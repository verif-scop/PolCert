(* *****************************************************************)
(*                                                                 *)
(*               Verified polyhedral AST generation                *)
(*                                                                 *)
(*                 Nathanaël Courant, Inria Paris                  *)
(*                                                                 *)
(*  Copyright Inria. All rights reserved. This file is distributed *)
(*  under the terms of the GNU Lesser General Public License as    *)
(*  published by the Free Software Foundation, either version 2.1  *)
(*  of the License, or (at your option) any later version.         *)
(*                                                                 *)
(* *****************************************************************)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Psatz.
Require Import Setoid Morphisms.

Require Import Linalg.
Require Import PolyLoop.
Require Import PolyLang.
Require Import Misc.
Require Import IterSemantics.
Require Import InstrTy.
Require Import VplInterface.
(* Require Import Result. *)
Require Import Canonizer.
Require Import Heuristics.
Require Import Projection.
Require Import PolyTest.
Require Import PolyOperations.

Require Import Vpl.Impure.
Require Import ImpureAlarmConfig.

Open Scope Z_scope.
Open Scope list_scope.

Require Import PolIRs.

Module ASTGen (PolIRs: POLIRS).

Module Instr := PolIRs.Instr.
Module PolyLang := PolIRs.PolyLang.
Module PolyLoop := PolIRs.PolyLoop.
Module Loop := PolIRs.Loop.

Fixpoint generate_loop (d : nat) (n : nat) (pi : PolyLang.PolyInstr) : imp PolyLoop.poly_stmt :=
  match d with
  | O => pure (PolyLoop.PInstr pi.(PolyLang.pi_instr) (map (fun t => (1%positive, t)) pi.(PolyLang.pi_transformation)))
  | S d1 =>
    BIND proj <- project ((n - d1)%nat, pi.(PolyLang.pi_poly)) -;
    BIND inner <- generate_loop d1 n pi -;
    pure (PolyLoop.PLoop (filter (fun c => negb (nth (n - d)%nat (fst c) 0 =? 0)) proj) inner)
  end.

Lemma env_scan_begin :
  forall polys env n p m, PolyLang.env_scan polys env n m p = true -> p =v= env ++ skipn (length env) p.
Proof.
  intros polys env n p m Hscan. unfold PolyLang.env_scan in Hscan. destruct (nth_error polys m); [|congruence].
  reflect. destruct Hscan as [[Heq1 Heq2] Heq3].
  apply same_length_eq in Heq1; [|rewrite resize_length; auto].
  rewrite Heq1 at 1.
  rewrite resize_skipn_eq; reflexivity.
Qed.
  
Lemma env_scan_single :
  forall polys env n p m, length env = n -> PolyLang.env_scan polys env n m p = true -> env =v= p.
Proof.
  intros polys env n p m Hlen Hscan.
  unfold PolyLang.env_scan in Hscan. destruct (nth_error polys m); [|congruence].
  reflect. destruct Hscan as [[Heq1 Heq2] Heq3]. rewrite Hlen in Heq1.
  rewrite Heq1. symmetry. auto.
Qed.

Lemma env_scan_split :
  forall polys env n p m, (length env < n)%nat -> PolyLang.env_scan polys env n m p = true <-> (exists x, PolyLang.env_scan polys (env ++ (x :: nil)) n m p = true).
Proof.
  intros polys env n p m Hlen.
  unfold PolyLang.env_scan. destruct (nth_error polys m); simpl; [|split; [intros; congruence|intros [x Hx]; auto]].
  split.
  - intros H. exists (nth (length env) p 0).
    reflect. destruct H as [[H1 H2] H3].
    split; [split|]; auto.
    rewrite app_length. simpl. rewrite <- resize_skipn_eq with (l := p) (d := length env) at 2.
    rewrite resize_app_le by (rewrite resize_length; lia).
    rewrite resize_length. rewrite <- is_eq_veq.
    rewrite is_eq_app by (rewrite resize_length; auto).
    reflect; split; auto.
    replace (length env + 1 - length env)%nat with 1%nat by lia.
    simpl. transitivity (nth 0 (skipn (length env) p) 0 :: nil).
    + rewrite nth_skipn. rewrite Nat.add_0_r. reflexivity.
    + destruct (skipn (length env) p); simpl; reflexivity.
  - intros [x Hx]. reflect. destruct Hx as [[H1 H2] H3].
    + split; [split|]; auto.
      rewrite app_length in H1. simpl in H1.
      rewrite <- is_eq_veq in H1. rewrite is_eq_app_left in H1.
      reflect; destruct H1 as [H1 H4]. rewrite resize_resize in H1 by lia. assumption.
Qed.

Lemma generate_loop_single_point :
  forall n pi env mem1 mem2,
    WHEN st <- generate_loop 0%nat n pi THEN
    PolyLoop.poly_loop_semantics st env mem1 mem2 ->
    length env = n ->
    in_poly (rev env) pi.(PolyLang.pi_poly) = true ->
    PolyLang.env_poly_lex_semantics (rev env) n (pi :: nil) mem1 mem2.
Proof.
  intros n pi env mem1 mem2 st Hgen Hsem Hlen Henvsat. simpl in *.
  apply mayReturn_pure in Hgen.
  unfold PolyLang.env_poly_lex_semantics.
  rewrite <- Hgen in Hsem. inversion_clear Hsem.
  eapply PolyLang.PolyLexProgress with (n := 0%nat) (p := rev env) (wcs:=wcs) (rcs:=rcs); [ |reflexivity| | | apply PolyLang.PolyLexDone].
  - unfold PolyLang.env_scan. simpl. reflect. split; [split|].
    + rewrite resize_eq; reflexivity.
    + rewrite resize_eq; [reflexivity | rewrite rev_length; lia].
    + auto.
  - intros n2 p2 Hcmp. apply not_true_iff_false; intros H'.
    apply env_scan_single in H'; [|rewrite rev_length; auto].
    rewrite H' in Hcmp. rewrite lex_compare_reflexive in Hcmp. congruence.
  - unfold affine_product in *. rewrite map_map in H.
    erewrite map_ext in H; [exact H|].
    intros; unfold PolyLoop.eval_affine_expr; simpl. apply Z.div_1_r.
  - intros n1 p1. unfold PolyLang.scanned.
    destruct n1 as [|n1]; [|destruct n1; simpl; auto]. simpl.
    apply not_true_iff_false; intros H'; reflect; destruct H' as [H1 H2].
    apply env_scan_single in H1; [|rewrite rev_length; lia].
    rewrite H1 in H2; rewrite is_eq_reflexive in H2.
    destruct H2; congruence.
Qed.

Lemma env_scan_extend :
  forall d n pi lb ub env m p,
    length env = n ->
    (n < d)%nat ->
    WHEN proj <- project (S n, pi.(PolyLang.pi_poly)) THEN
    (forall x, (forall c, In c proj -> nth n (fst c) 0 <> 0 -> satisfies_constraint (rev (x :: env)) c = true) <-> lb <= x < ub) ->
    PolyLang.env_scan (pi :: nil) (rev env) d m p =
      existsb (fun x : Z => PolyLang.env_scan (pi :: nil) (rev env ++ x :: nil) d m p) (Zrange lb ub).
Proof.
  intros d n pi lb ub env m p Hlen Hnd proj Hproj Hlbub.
  rewrite eq_iff_eq_true. rewrite existsb_exists.
  rewrite env_scan_split by (rewrite rev_length; lia).
  split.
  - intros [x Hscan]; exists x; split; [|auto].
    rewrite Zrange_in. unfold PolyLang.env_scan in Hscan. destruct m; [|destruct m; simpl in Hscan; try congruence].
    simpl in Hscan. reflect.
    destruct Hscan as [[Hscan1 Hscan2] Hscan3].
    assert (Hinproj : in_poly (rev env ++ x :: nil) proj = true).
    {
      rewrite Hscan1. eapply project_inclusion; [apply Hscan3|].
      rewrite app_length; rewrite rev_length; rewrite Hlen; unfold length.
      replace (n + 1)%nat with (S n) by lia. apply Hproj.
    }
    rewrite <- Hlbub by eauto.
    unfold in_poly in Hinproj. rewrite forallb_forall in Hinproj.
    intros; auto.
  - intros [x [H1 H2]]; exists x; assumption.
Qed.

Lemma env_scan_inj_nth :
  forall pis env1 env2 n m p s, length env1 = length env2 -> (s < length env1)%nat ->
                           PolyLang.env_scan pis env1 n m p = true -> PolyLang.env_scan pis env2 n m p = true -> nth s env1 0 = nth s env2 0.
Proof.
  intros pis env1 env2 n m p s Hleneq Hs Henv1 Henv2.
  unfold PolyLang.env_scan in Henv1, Henv2. destruct (nth_error pis m) as [pi|]; [|congruence].
  reflect. rewrite Hleneq in Henv1. destruct Henv1 as [[Henv1 ?] ?]; destruct Henv2 as [[Henv2 ?] ?].
  rewrite <- Henv2 in Henv1. apply nth_eq; auto.
Qed.

Lemma env_scan_inj_rev :
  forall pis env n m x1 x2 p, PolyLang.env_scan pis (rev (x1 :: env)) n m p = true -> PolyLang.env_scan pis (rev (x2 :: env)) n m p = true -> x1 = x2.
Proof.
  intros pis env n m x1 x2 p H1 H2.
  replace x1 with (nth (length env) (rev (x1 :: env)) 0) by (simpl; rewrite app_nth2, rev_length, Nat.sub_diag; reflexivity || rewrite rev_length; lia).
  replace x2 with (nth (length env) (rev (x2 :: env)) 0) by (simpl; rewrite app_nth2, rev_length, Nat.sub_diag; reflexivity || rewrite rev_length; lia).
  eapply env_scan_inj_nth; [| |exact H1|exact H2]; rewrite !rev_length; simpl; lia.
Qed.

Theorem generate_loop_preserves_sem :
  forall d n pi env mem1 mem2,
    (d <= n)%nat ->
    WHEN st <- generate_loop d n pi THEN
    PolyLoop.poly_loop_semantics st env mem1 mem2 ->
    length env = (n - d)%nat ->
    (forall c, In c pi.(PolyLang.pi_poly) -> fst c =v= resize n (fst c)) ->
    project_invariant (n - d)%nat pi.(PolyLang.pi_poly) (rev env) ->
    PolyLang.env_poly_lex_semantics (rev env) n (pi :: nil) mem1 mem2.
Proof.
  induction d.
  - intros n pi env mem1 mem2 Hnd st Hgen Hsem Hlen Hpilen Hinv.
    eapply generate_loop_single_point; eauto; try lia.
    eapply project_id; eauto.
    rewrite Nat.sub_0_r in Hinv. auto.
  - intros n pi env mem1 mem2 Hnd st Hgen Hsem Hlen Hpilen Hinv. simpl in *.
    bind_imp_destruct Hgen proj Hproj.
    bind_imp_destruct Hgen inner Hinner.
    apply mayReturn_pure in Hgen. rewrite <- Hgen in Hsem.
    apply PolyLoop.PLLoop_inv_sem in Hsem.
    destruct Hsem as [lb [ub [Hlbub Hsem]]].
    unfold PolyLang.env_poly_lex_semantics in *.
    eapply PolyLang.poly_lex_semantics_extensionality.
    + apply PolyLang.poly_lex_concat_seq with (to_scans := fun x => PolyLang.env_scan (pi :: nil) (rev (x :: env)) n).
      * eapply Instr.IterSem.iter_semantics_map; [|apply Hsem].
        intros x mem3 mem4 Hbounds Hloop. eapply IHd with (env := x :: env); simpl; eauto; try lia.
        replace (n - d)%nat with (S (n - S d))%nat in * by lia.
        eapply project_next_r_inclusion; [|exact Hproj|].
        -- rewrite project_invariant_resize, resize_app by (rewrite rev_length; auto).
           apply Hinv.
        -- intros c Hcin Hcnth. rewrite Zrange_in, <- Hlbub in Hbounds.
           unfold in_poly in Hbounds; rewrite forallb_forall in Hbounds. apply Hbounds.
           rewrite filter_In; reflect; auto.
      * intros x. apply PolyLang.env_scan_proper.
      * intros x1 k1 x2 k2 m p H1 H2 H3 H4. rewrite Zrange_nth_error in *.
        enough (lb + Z.of_nat k1 = lb + Z.of_nat k2) by lia.
        eapply env_scan_inj_rev; [destruct H3 as [? <-]; exact H1|destruct H4 as [? <-]; exact H2].
      * intros x1 n1 p1 k1 x2 n2 p2 k2 Hcmp H1 H2 H3 H4.
        rewrite Zrange_nth_error in *.
        apply env_scan_begin in H1; apply env_scan_begin in H2. simpl in *.
        rewrite H1, H2 in Hcmp.
        enough (lb + Z.of_nat k2 <= lb + Z.of_nat k1) by lia.
        eapply lex_app_not_gt.
        destruct H3 as [? <-]; destruct H4 as [? <-].
        rewrite Hcmp; congruence.
    + simpl. intros m p. rewrite env_scan_extend; eauto; try lia.
      * replace (S (n - S d)) with (n - d)%nat by lia. apply Hproj.
      * intros x; rewrite <- Hlbub. unfold in_poly; rewrite forallb_forall. apply forall_ext; intros c.
        split; intros H; intros; apply H; rewrite filter_In in *; reflect; tauto.
Qed.

Definition generate d n pi :=
  BIND st <- generate_loop d n pi -;
  BIND ctx <- project_invariant_export ((n - d)%nat, pi.(PolyLang.pi_poly)) -;
  pure (PolyLoop.PGuard ctx st).

Theorem generate_preserves_sem :
  forall d n pi env mem1 mem2,
    (d <= n)%nat ->
    WHEN st <- generate d n pi THEN
    PolyLoop.poly_loop_semantics st env mem1 mem2 ->
    length env = (n - d)%nat ->
    (forall c, In c pi.(PolyLang.pi_poly) -> fst c =v= resize n (fst c)) ->
    PolyLang.env_poly_lex_semantics (rev env) n (pi :: nil) mem1 mem2.
Proof.
  intros d n pi env mem1 mem2 Hd st Hgen Hloop Henv Hsize.
  bind_imp_destruct Hgen st1 H. bind_imp_destruct Hgen ctx Hctx.
  apply mayReturn_pure in Hgen.
  rewrite <- Hgen in *.
  apply PolyLoop.PLGuard_inv_sem in Hloop.
  destruct (in_poly (rev env) ctx) eqn:Htest.
  - eapply generate_loop_preserves_sem; eauto.
    rewrite <- (project_invariant_export_correct _ _ _ _ Hctx); eauto.
  - rewrite Hloop. apply PolyLang.PolyLexDone. intros n0 p. unfold PolyLang.env_scan.
    destruct n0; simpl in *; [|destruct n0]; auto. reflect.
    rewrite rev_length; rewrite Henv.
    destruct (is_eq (rev env) (resize (n - d)%nat p)) eqn:Hpenv; auto.
    destruct (in_poly p pi.(PolyLang.pi_poly)) eqn:Hpin; auto. exfalso.
    eapply project_invariant_inclusion in Hpin.
    rewrite <- (project_invariant_export_correct _ _ _ _ Hctx) in Hpin.
    reflect. rewrite <- Hpenv in Hpin. congruence.
Qed.


Definition update_poly pi pol :=
  {| PolyLang.pi_depth := pi.(PolyLang.pi_depth) ; PolyLang.pi_instr := pi.(PolyLang.pi_instr) ; PolyLang.pi_poly := pol ; PolyLang.pi_schedule := pi.(PolyLang.pi_schedule) ; PolyLang.pi_transformation := pi.(PolyLang.pi_transformation); PolyLang.pi_waccess := pi.(PolyLang.pi_waccess); PolyLang.pi_raccess := pi.(PolyLang.pi_raccess); |}.


Definition dummy_pi := PolyLang.dummy_pi.


Definition make_npis (pis: list PolyLang.PolyInstr) pol pl :=
  map (fun t => let pi := nth t pis dummy_pi in
             let npol := poly_inter_pure pi.(PolyLang.pi_poly) pol in
             update_poly pi npol) pl.

Definition make_npis_simplify pis pol pl :=
  mapM (fun t => let pi := nth t pis dummy_pi in
              BIND npol <- poly_inter pi.(PolyLang.pi_poly) pol -;
              pure (update_poly pi npol)) pl.

Definition pi_equiv pi1 pi2 :=
  (forall p, in_poly p pi1.(PolyLang.pi_poly) = in_poly p pi2.(PolyLang.pi_poly)) /\
  pi1.(PolyLang.pi_instr) = pi2.(PolyLang.pi_instr) /\
  pi1.(PolyLang.pi_transformation) = pi2.(PolyLang.pi_transformation).

Lemma make_npis_simplify_equiv :
  forall pis pol pl,
    WHEN npis <- make_npis_simplify pis pol pl THEN
         Forall2 pi_equiv (make_npis pis pol pl) npis.
Proof.
  intros pis pol pl npis Hnpis.
  apply mapM_mayReturn in Hnpis.
  unfold make_npis. rewrite Forall2_map_left.
  eapply Forall2_imp; [|exact Hnpis].
  intros t pi Hpi. simpl in *.
  bind_imp_destruct Hpi npol Hnpol; apply mayReturn_pure in Hpi.
  rewrite <- Hpi in *.
  unfold pi_equiv, update_poly; simpl.
  split; [|tauto].
  intros p. symmetry. apply poly_inter_def. auto.
Qed.

Fixpoint generate_loop_many (d : nat) (n : nat) (pis : list PolyLang.PolyInstr) : imp PolyLoop.poly_stmt :=
  match d with
  | O => pure (PolyLoop.make_seq (map (fun pi => PolyLoop.PGuard pi.(PolyLang.pi_poly) (PolyLoop.PInstr pi.(PolyLang.pi_instr) (map (fun t => (1%positive, t)) pi.(PolyLang.pi_transformation)))) pis))
  | S d1 =>
    BIND projs <- mapM (fun pi => project ((n - d1)%nat, pi.(PolyLang.pi_poly))) pis -;
    BIND projsep <- split_and_sort (n - d)%nat projs -;
    BIND inner <- mapM (fun '(pol, pl) =>
         BIND npis <- make_npis_simplify pis pol pl -;
         BIND inside <- generate_loop_many d1 n npis -;
         pure (PolyLoop.PLoop pol inside)) projsep -;
    pure (PolyLoop.make_seq inner)
  end.

(* Forall instance's, its index length <= n. (>n bit not contribute to semantics )*)
Definition pis_have_dimension pis n :=
  forallb (fun pi => (poly_nrl (pi.(PolyLang.pi_poly)) <=? n)%nat) pis = true.

Lemma make_npis_simplify_have_dimension :
  forall pis pol pl n,
    pis_have_dimension pis n ->
    (poly_nrl pol <= n)%nat ->
    WHEN npis <- make_npis_simplify pis pol pl THEN
         pis_have_dimension npis n.
Proof.
  intros pis pol pl n Hpis Hpol npis Hnpis.
  unfold pis_have_dimension in *; rewrite forallb_forall in *.
  intros npi Hnpi. eapply mapM_in_iff in Hnpi; [|exact Hnpis].
  destruct Hnpi as [t [Hnpi Htin]].
  bind_imp_destruct Hnpi npol Hnpol. apply mayReturn_pure in Hnpi.
  reflect.
  rewrite <- Hnpi; simpl.
  eapply poly_inter_nrl; [|exact Hpol|exact Hnpol].
  destruct (t <? length pis)%nat eqn:Ht; reflect.
  - specialize (Hpis (nth t pis dummy_pi)). reflect; apply Hpis.
    apply nth_In; auto.
  - rewrite nth_overflow by auto.
    simpl. unfold poly_nrl; simpl. lia.
Qed.

Definition generate_invariant (n : nat) (pis : list PolyLang.PolyInstr) (env : list Z) :=
  (* forall pi, In pi pis -> project_invariant n pi.(PolyLang.pi_poly) (rev env). *)
  True.

Lemma project_inclusion2 :
  forall (n : nat) (p : list Z) (pol : list (list Z * Z)),
    in_poly p pol = true -> WHEN proj <- project (n, pol) THEN in_poly p proj = true.
Proof.
  intros n p pol Hin proj Hproj.
  generalize (project_inclusion n p pol Hin proj Hproj); intros H.
  unfold in_poly in *; rewrite forallb_forall in *. intros c Hc; specialize (H c Hc).
  apply project_constraint_size with (c := c) in Hproj. specialize (Hproj Hc).
  rewrite <- H; unfold satisfies_constraint; f_equal.
  rewrite Hproj, <- dot_product_resize_left, resize_length.
  reflexivity.
Qed.

(* Useful to weaken an hypothesis in next proof *)
Lemma refl_scan :
  forall (scan1 scan2 : nat -> list Z -> bool), scan1 = scan2 -> (forall n p, scan1 n p = scan2 n p).
Proof.
  intros scan1 scan2 ->. reflexivity.
Qed.

Lemma poly_lex_semantics_subpis :
  forall pis pl to_scan mem1 mem2,
    (forall n p, to_scan n p = true -> In n pl) ->
    NoDup pl ->
    (forall n, In n pl -> (n < length pis)%nat) ->
    PolyLang.poly_lex_semantics to_scan pis mem1 mem2 <->
    PolyLang.poly_lex_semantics (fun n p => match nth_error pl n with Some m => to_scan m p | None => false end) (map (fun t => nth t pis dummy_pi) pl) mem1 mem2.
Proof.
  intros pis pl to_scan mem1 mem2 Hscan Hdup Hpl.
  split.
  - intros H; induction H as [to_scan prog mem Hdone|to_scan prog mem1 mem2 mem3 pi n p wcs rcs Hscanp Heqpi Hts Hsem1 Hsem2 IH].
    + apply PolyLang.PolyLexDone. intros n p; destruct (nth_error pl n); auto.
    + generalize (Hscan _ _ Hscanp); intros Hnpl. apply In_nth_error in Hnpl; destruct Hnpl as [k Hk].
      eapply PolyLang.PolyLexProgress; [| | |exact Hsem1|eapply PolyLang.poly_lex_semantics_extensionality; [apply IH|]].
      * rewrite Hk; auto.
      * erewrite map_nth_error; [|exact Hk]. f_equal.
        apply nth_error_nth; auto.
      * intros n2 p2 H; destruct (nth_error pl n2); auto.
      * intros n2 p2 H; eapply Hscan.
        unfold PolyLang.scanned in H; reflect; destruct H; eauto.
      * auto.
      * intros k2 p2. unfold PolyLang.scanned. simpl.
        destruct (nth_error pl k2) as [n2|] eqn:Hk2; simpl; [|reflexivity].
        f_equal. f_equal. f_equal.
        apply eq_iff_eq_true; reflect.
        split; [|congruence]. intros Hn. rewrite NoDup_nth_error in Hdup. apply Hdup; [|congruence].
        rewrite <- nth_error_Some. congruence.
  - match goal with [ |- PolyLang.poly_lex_semantics ?x ?y _ _ -> _] => remember x as to_scan1; remember y as pis1 end.
    generalize (refl_scan _ _ Heqto_scan1); clear Heqto_scan1; intros Heqto_scan1.
    intros H; generalize to_scan1 pis1 H to_scan Hscan Heqto_scan1 Heqpis1. clear Heqto_scan1 Heqpis1 Hscan to_scan H pis1 to_scan1.
    intros to_scan1 pis1 H.
    induction H as [to_scan1 prog mem Hdone|to_scan1 prog mem1 mem2 mem3 pi n p wcs rcs Hscanp Heqpi Hts Hsem1 Hsem2 IH].
    + intros; apply PolyLang.PolyLexDone.
      intros n p.
      apply not_true_is_false. intros Hscan2.
      destruct (In_nth_error _ _ (Hscan _ _ Hscan2)) as [k Hk].
      specialize (Heqto_scan1 k p). rewrite Hdone, Hk in Heqto_scan1. congruence.
    + intros to_scan Hscan Hscan1 Hprog; rewrite Hprog in *; rewrite Hscan1 in *.
      destruct (nth_error pl n) as [k|] eqn:Hk; [|congruence].
      eapply PolyLang.PolyLexProgress; [exact Hscanp| | |exact Hsem1|eapply PolyLang.poly_lex_semantics_extensionality; [apply (IH (PolyLang.scanned to_scan k p))|]].
      * erewrite map_nth_error in Heqpi; [|exact Hk].
        rewrite nth_error_nth_iff with (d := dummy_pi); [congruence|eauto].
      * intros n2 p2 Hts2. apply not_true_is_false. intros Hscan2.
        destruct (In_nth_error _ _ (Hscan _ _ Hscan2)) as [k2 Hk2].
        specialize (Hts k2 p2 Hts2); rewrite Hscan1, Hk2 in Hts. congruence.
      * intros n2 p2 H. unfold PolyLang.scanned in H. reflect. destruct H; eapply Hscan; eauto.
      * intros n2 p2. unfold PolyLang.scanned. simpl. rewrite Hscan1.
        destruct (nth_error pl n2) as [k2|] eqn:Hk2; simpl; [|reflexivity].
        f_equal. f_equal. f_equal.
        apply eq_iff_eq_true; reflect.
        split; [congruence|]. intros Hn. rewrite NoDup_nth_error in Hdup. apply Hdup; [|congruence].
        rewrite <- nth_error_Some. congruence.
      * reflexivity.
      * reflexivity.
Qed. 

Lemma env_scan_pi_equiv :
  forall env pis1 pis2 d n p,
    Forall2 pi_equiv pis1 pis2 ->
    PolyLang.env_scan pis1 env d n p = PolyLang.env_scan pis2 env d n p.
Proof.
  intros env pis1 pis2 d n p H.
  unfold PolyLang.env_scan. destruct (nth_error pis1 n) as [pi1|] eqn:Hpi1.
  - destruct (Forall2_nth_error _ _ _ _ _ _ _ H Hpi1) as [pi2 [-> Hpis]].
    f_equal. unfold pi_equiv in Hpis. destruct Hpis; auto.
  - erewrite nth_error_None, Forall2_length, <- nth_error_None in Hpi1 by (exact H).
    rewrite Hpi1; reflexivity.
Qed.

Lemma env_poly_lex_semantics_ext_pi_equiv :
  forall env n pis1 pis2 mem1 mem2,
    Forall2 pi_equiv pis1 pis2 ->
    PolyLang.env_poly_lex_semantics env n pis1 mem1 mem2 <-> PolyLang.env_poly_lex_semantics env n pis2 mem1 mem2.
Proof.
  intros env n pis1 pis2 mem1 mem2 H.
  unfold PolyLang.env_poly_lex_semantics.
  rewrite PolyLang.poly_lex_semantics_pis_ext_iff; [rewrite PolyLang.poly_lex_semantics_ext_iff; [reflexivity|]|].
  - intros m p. apply env_scan_pi_equiv. auto.
  - eapply Forall2_imp; [|exact H]. intros; unfold pi_equiv in *; tauto.
Qed.

Definition subscan pprog pol pl env d n p :=
  existsb (fun m => (m =? n)%nat) pl && in_poly p pol && PolyLang.env_scan pprog env d n p.

Lemma subscan_in :
  forall pis pol pl env d n p,
    subscan pis pol pl env d n p = true -> in_poly p pol = true.
Proof.
  intros pis pol pl env d n p Hsub.
  unfold subscan in Hsub.
  reflect; tauto.
Qed.

Lemma subscan_in_env :
  forall pis pol pl env d n p,
    (poly_nrl pol <= S (length env))%nat ->
    subscan pis pol pl env d n p = true ->
    in_poly (env ++ (nth (length env) p 0) :: nil) pol = true.
Proof.
  intros pos pol pl env d n p Hnrl Hsub.
  unfold subscan in Hsub. reflect. destruct Hsub as [[_ Hpin] Hscan].
  apply env_scan_begin in Hscan. rewrite Hscan in Hpin.
  erewrite <- in_poly_nrlength by (exact Hnrl).
  erewrite <- in_poly_nrlength in Hpin by (exact Hnrl).
  rewrite resize_app_le in * by lia.
  replace (S (length env) - length env)%nat with 1%nat in * by lia.
  rewrite resize_1 in *. simpl.
  rewrite nth_skipn, Nat.add_0_r in Hpin. auto.
Qed.

Instance subscan_proper pprog pol pl env d : Proper (eq ==> veq ==> eq) (subscan pprog pol pl env d).
Proof.
  intros n1 n2 Hn p1 p2 Hp. unfold subscan.
  (* destruct pprog as ((pis & varctxt) & vars). *)
  rewrite Hn, Hp; reflexivity.
  (* rewrite Hp at 1. rewrite Hp at 0. reflexivity. 
  eapply is_eq_proper in Hp.
  simpl.
  rewrite Hp. reflexivity. *)
Qed.

Lemma poly_lex_semantics_make_npis_subscan :
  forall pis pol pl n env mem1 mem2,
    NoDup pl ->
    (forall n, In n pl -> (n < length pis)%nat) ->
    PolyLang.poly_lex_semantics (subscan pis pol pl (rev env) n) pis mem1 mem2 <->
    PolyLang.env_poly_lex_semantics (rev env) n (make_npis pis pol pl) mem1 mem2.
Proof.
  intros pis pol pl n env mem1 mem2 Hdup Hind.
  unfold PolyLang.env_poly_lex_semantics, make_npis. 
  rewrite poly_lex_semantics_subpis with (pl := pl).
  - erewrite PolyLang.poly_lex_semantics_pis_ext_iff; [apply PolyLang.poly_lex_semantics_ext_iff|].
    + intros m p. destruct (nth_error pl m) as [k|] eqn:Hk.
      * assert (Hkin : In k pl) by (eapply nth_error_In; eauto).
        unfold subscan, PolyLang.env_scan. erewrite map_nth_error; [|exact Hk]. simpl.
        rewrite poly_inter_pure_def.
        destruct (nth_error pis k) as [pi|] eqn:Hpik; [|rewrite nth_error_None in Hpik; specialize (Hind _ Hkin); lia].
        erewrite nth_error_nth; [|exact Hpik].
        replace (existsb (fun k1 => (k1 =? k)%nat) pl) with true by (symmetry; rewrite existsb_exists; exists k; reflect; auto).
        ring.
      * rewrite nth_error_None in Hk. unfold PolyLang.env_scan.
        erewrite <- map_length, <- nth_error_None in Hk; rewrite Hk.
        reflexivity.
    + rewrite Forall2_map_left, Forall2_map_right. apply Forall2_R_refl.
      intros x; simpl; auto.
  - intros m p Hscan. unfold subscan in Hscan.
    destruct (existsb (fun m1 => (m1 =? m)%nat) pl) eqn:Hex; simpl in *; [|congruence].
    rewrite existsb_exists in Hex; destruct Hex as [m1 [Hm1 Hmeq]]. reflect.
    rewrite <- Hmeq; auto.
  - auto.
  - auto.
Qed.

Lemma env_scan_extend_many :
  forall d n pis lb ub env m p,
    length env = n ->
    (n < d)%nat ->
    (forall x, PolyLang.env_scan pis (rev env ++ x :: nil) d m p = true -> lb <= x < ub) ->
    PolyLang.env_scan pis (rev env) d m p =
      existsb (fun x : Z => PolyLang.env_scan pis (rev env ++ x :: nil) d m p) (Zrange lb ub).
Proof.
  intros d n pis lb ub env m p Hlen Hnd Hlbub.
  rewrite eq_iff_eq_true. rewrite existsb_exists.
  rewrite env_scan_split by (rewrite rev_length; lia).
  split.
  - intros [x Hscan]; exists x; split; [|auto].
    rewrite Zrange_in. auto.
  - intros [x [H1 H2]]; exists x; assumption.
Qed.

Lemma env_scan_make_npis_in :
  forall pis pol pl env n m p,
    PolyLang.env_scan (make_npis pis pol pl) env n m p = true -> in_poly p pol = true.
Proof.
  intros pis pol pl env n m p H.
  unfold make_npis, PolyLang.env_scan in H.
  destruct nth_error as [pi|] eqn:Hpi; [|congruence].
  rewrite nth_error_map_iff in Hpi. destruct Hpi as [t [Ht Hpi]].
  rewrite Hpi in H; simpl in H.
  rewrite poly_inter_pure_def in H. reflect; tauto.
Qed.

Theorem generate_loop_many_preserves_sem :
  forall d n pis env mem1 mem2,
    (d <= n)%nat ->
    WHEN st <- generate_loop_many d n pis THEN
    PolyLoop.poly_loop_semantics st env mem1 mem2 ->
    length env = (n - d)%nat ->
    pis_have_dimension pis n ->
    generate_invariant (n - d)%nat pis env ->
    PolyLang.env_poly_lex_semantics (rev env) n pis mem1 mem2.
Proof.
  induction d.
  - intros n pis env mem1 mem2 Hnd st Hgen Hsem Hlen Hpidim Hinv.
    simpl in *. apply mayReturn_pure in Hgen. rewrite <- Hgen in Hsem.
    apply PolyLoop.make_seq_semantics in Hsem.
    unfold PolyLang.env_poly_lex_semantics.
    rewrite Instr.IterSem.iter_semantics_mapl in Hsem.
    rewrite Instr.IterSem.iter_semantics_combine with (ys := n_range (length pis)) in Hsem by (rewrite n_range_length; auto).
    eapply PolyLang.poly_lex_semantics_extensionality;
      [eapply PolyLang.poly_lex_concat_seq with (to_scans := fun (arg : PolyLang.PolyInstr * nat) m p => (m =? snd arg)%nat && PolyLang.env_scan pis (rev env) n m p)|].
    + eapply Instr.IterSem.iter_semantics_map; [|exact Hsem].
      intros [pi x] mem3 mem4 Hinpixs Hloopseq. simpl in *.
      rewrite combine_n_range_in in Hinpixs.
      apply PolyLoop.PLGuard_inv_sem in Hloopseq.
      destruct (in_poly (rev env) (PolyLang.pi_poly pi)) eqn:Hinpi;
        [apply PolyLoop.PLInstr_inv_sem in Hloopseq; destruct Hloopseq as (wcs & rcs & Hloopseq); eapply PolyLang.PolyLexProgress with (p := rev env) (wcs:=wcs) (rcs:=rcs); [|exact Hinpixs| | |apply PolyLang.PolyLexDone]|].
      * unfold PolyLang.env_scan. rewrite Hinpixs. reflect. split; [auto|].
        split; [rewrite !resize_length_eq; [split; reflexivity| |]; rewrite !rev_length; lia|].
        exact Hinpi.
      * intros n2 p2 H. destruct (n2 =? x)%nat eqn:Hn2; reflect; [|auto].
        right. apply not_true_is_false; intros Hscan.
        apply env_scan_single in Hscan; [|rewrite rev_length; lia].
        rewrite Hscan in H. rewrite lex_compare_reflexive in H; congruence.
      * rewrite map_map in Hloopseq. unfold affine_product.
        erewrite map_ext; [exact Hloopseq|].
        intros c; unfold PolyLoop.eval_affine_expr; simpl. rewrite Z.div_1_r. reflexivity.
      * intros m p. unfold PolyLang.scanned.
        apply not_true_is_false. intros H; reflect.
        destruct H as [[Hmx Hscan] H].
        apply env_scan_single in Hscan; [|rewrite rev_length; lia].
        rewrite Hscan, is_eq_reflexive in H. destruct H; congruence.
      * rewrite Hloopseq; apply PolyLang.PolyLexDone. intros m p. apply not_true_is_false. intros H; reflect. destruct H as [Hmx Hscan].
        assert (H : rev env =v= p) by (apply env_scan_single in Hscan; [|rewrite rev_length; lia]; auto). rewrite H in Hinpi.
        unfold PolyLang.env_scan in Hscan; rewrite Hmx, Hinpixs, Hinpi in Hscan. reflect; destruct Hscan; congruence.
    + intros [i x] m1 m2 -> p1 p2 ->. reflexivity.
    + intros [i1 x1] k1 [i2 x2] k2 m p H1 H2 Hk1 Hk2.
      rewrite nth_error_combine in Hk1, Hk2. simpl in *; reflect.
      rewrite n_range_nth_error in Hk1, Hk2. destruct H1; destruct H2; destruct Hk1 as [? [? ?]]; destruct Hk2 as [? [? ?]]. congruence.
    + intros [i1 x1] n1 p1 k1 [i2 x2] n2 p2 k2 Hcmp H1 H2 Hk1 Hk2.
      reflect; simpl in *.
      rewrite nth_error_combine, n_range_nth_error in Hk1, Hk2.
      destruct H1 as [Hn1 H1]; destruct H2 as [Hn2 H2].
      apply env_scan_single in H1; apply env_scan_single in H2; try (rewrite rev_length; lia).
      rewrite <- H1, <- H2, lex_compare_reflexive in Hcmp. congruence.
    + intros m p. simpl. rewrite eq_iff_eq_true, existsb_exists.
      split; [intros [x Hx]; reflect; tauto|]. intros Hscan; rewrite Hscan.
      unfold PolyLang.env_scan in Hscan. destruct (nth_error pis m) as [pi|] eqn:Hpi; [|congruence].
      exists (pi, m). rewrite combine_n_range_in.
      simpl in *; reflect; auto.
  - intros n pis env mem1 mem2 Hnd st Hgen Hsem Hlen Hpidim Hinv. simpl in *.
    bind_imp_destruct Hgen projs Hprojs.
    bind_imp_destruct Hgen projsep Hprojsep.
    bind_imp_destruct Hgen inner Hinner.
    assert (Hprojnrl : forall ppl, In ppl projsep -> (poly_nrl (fst ppl) <= n - d)%nat).
    {
      eapply split_and_sort_nrl; [eauto|].
      intros pol Hpolin. eapply mapM_in_iff in Hpolin; [|eauto].
      destruct Hpolin as [pi [Hpol Hpiin]].
      rewrite <- poly_nrl_def. intros c; eapply project_constraint_size; eauto.
    }
    apply mayReturn_pure in Hgen. rewrite <- Hgen in Hsem; clear Hgen.
    rewrite PolyLoop.make_seq_semantics in Hsem.
    unfold PolyLang.env_poly_lex_semantics.
    eapply PolyLang.poly_lex_semantics_extensionality;
      [apply PolyLang.poly_lex_concat_seq with (to_scans := fun (arg : (polyhedron * list nat * PolyLoop.poly_stmt)) => subscan pis (fst (fst arg)) (snd (fst arg)) (rev env) n)|].
    +
      eapply Instr.IterSemImpure.iter_semantics_mapM_rev in Hsem; [|exact Hinner].
      eapply Instr.IterSem.iter_semantics_map; [|apply Hsem]. clear Hsem.
      intros [[pol pl] inner1] mem3 mem4 Hins [Hinner1 Hseminner1].
      apply in_combine_l in Hins.
      bind_imp_destruct Hinner1 npis Hnpis.
      bind_imp_destruct Hinner1 inside Hinside.
      apply mayReturn_pure in Hinner1; rewrite <- Hinner1 in *.
      simpl. rewrite poly_lex_semantics_make_npis_subscan; [|
        eapply split_and_sort_index_NoDup with (polpl := (pol, pl)); eauto |
        intros i Hi; erewrite mapM_length; [|exact Hprojs]; eapply split_and_sort_index_correct with (polpl := (pol, pl)); eauto
      ].
      erewrite env_poly_lex_semantics_ext_pi_equiv; [|apply make_npis_simplify_equiv; eauto].
      apply PolyLoop.PLLoop_inv_sem in Hseminner1.
      destruct Hseminner1 as [lb [ub [Hlbub Hsem]]].
      unfold PolyLang.env_poly_lex_semantics in *.
      eapply PolyLang.poly_lex_semantics_extensionality.
      apply PolyLang.poly_lex_concat_seq with (to_scans := fun x => PolyLang.env_scan npis (rev (x :: env)) n).
      * eapply Instr.IterSem.iter_semantics_map; [|apply Hsem].
        intros x mem5 mem6 Hbounds Hloop. eapply IHd with (env := x :: env); simpl; eauto; try lia.
        -- eapply make_npis_simplify_have_dimension; eauto.
           specialize (Hprojnrl _ Hins). simpl in Hprojnrl; lia.
        (* no longer needed: generate_invariant is [True] now.
        -- unfold generate_invariant in *. (* generate_invariant preservation *)
           intros npi Hnpi. eapply mapM_in_iff in Hnpi; [|eauto].
           destruct Hnpi as [t [Hnpi Ht]]. remember (nth t pis dummy_pi) as pi. simpl in Hnpi.
           assert (Hpi : In pi pis). {
             rewrite Heqpi; apply nth_In. erewrite mapM_length; eauto.
             eapply split_and_sort_index_correct; eauto.
           }
         *)
      * intros x; apply PolyLang.env_scan_proper.
      * intros x1 k1 x2 k2 m p H1 H2 H3 H4. rewrite Zrange_nth_error in *.
        enough (lb + Z.of_nat k1 = lb + Z.of_nat k2) by lia.
        eapply env_scan_inj_rev; [destruct H3 as [? <-]; exact H1|destruct H4 as [? <-]; exact H2].
      * intros x1 n1 p1 k1 x2 n2 p2 k2 Hcmp H1 H2 H3 H4.
        rewrite Zrange_nth_error in *.
        apply env_scan_begin in H1; apply env_scan_begin in H2. simpl in *.
        rewrite H1, H2 in Hcmp.
        enough (lb + Z.of_nat k2 <= lb + Z.of_nat k1) by lia.
        eapply lex_app_not_gt.
        destruct H3 as [? <-]; destruct H4 as [? <-].
        rewrite Hcmp; congruence.
      * simpl. intros m p.
        erewrite env_scan_extend_many; [reflexivity|exact Hlen|lia|].
        intros x Hscanx. apply Hlbub; simpl.
        erewrite <- env_scan_pi_equiv in Hscanx; [|apply make_npis_simplify_equiv; eauto].
        assert (Hpin : in_poly p pol = true) by (eapply env_scan_make_npis_in; eauto).
        rewrite env_scan_begin in Hpin by (exact Hscanx).
        erewrite <- in_poly_nrlength in Hpin; [|exact (Hprojnrl _ Hins)].
        rewrite resize_app in Hpin; [auto|].
        rewrite app_length, rev_length. simpl. lia.
    + intros. apply subscan_proper.
    + intros [[pol1 pl1] inner1] k1 [[pol2 pl2] inner2] k2 m p Hscan1 Hscan2 Hnth1 Hnth2.
      rewrite nth_error_combine in Hnth1, Hnth2. simpl in *.
      destruct Hnth1 as [Hnth1 _]; destruct Hnth2 as [Hnth2 _].
      apply subscan_in in Hscan1; apply subscan_in in Hscan2.
      eapply split_and_sort_disjoint; eauto.
    + intros [[pol1 pl1] inner1] m1 p1 k1 [[pol2 pl2] inner2] m2 p2 k2 Hcmp Hscan1 Hscan2 Hnth1 Hnth2.
      rewrite nth_error_combine in Hnth1, Hnth2. simpl in *.
      destruct Hnth1 as [Hnth1 _]; destruct Hnth2 as [Hnth2 _].
      rewrite env_scan_begin with (p := p1) in Hcmp by (unfold subscan in Hscan1; reflect; destruct Hscan1; eauto).
      rewrite env_scan_begin with (p := p2) in Hcmp by (unfold subscan in Hscan2; reflect; destruct Hscan2; eauto).
      apply subscan_in_env in Hscan1; [|rewrite rev_length; apply nth_error_In in Hnth1; specialize (Hprojnrl _ Hnth1); simpl in *; lia].
      apply subscan_in_env in Hscan2; [|rewrite rev_length; apply nth_error_In in Hnth2; specialize (Hprojnrl _ Hnth2); simpl in *; lia].
      rewrite lex_compare_app, lex_compare_reflexive in Hcmp by auto.
      destruct (k2 <=? k1)%nat eqn:Hprec; reflect; [auto|exfalso].
      eapply split_and_sort_sorted in Hprec; eauto. simpl in Hprec.
      unfold canPrecede in Hprec.
      specialize (Hprec _ (nth (length (rev env)) p2 0) Hscan1).
      rewrite assign_app_ge, app_nth2 in Hprec by (rewrite rev_length; lia).
      rewrite rev_length, Hlen, Nat.sub_diag in Hprec.
      rewrite rev_length, Hlen in Hscan1, Hscan2, Hcmp.
      specialize (Hprec Hscan2). simpl in Hprec.
      apply lex_compare_lt_head in Hcmp. rewrite !nth_skipn, !Nat.add_0_r in Hcmp.
      lia.
    + intros m p. simpl.
      apply eq_iff_eq_true. rewrite existsb_exists. split.
      * intros [[[pol pl] inner1] [Hin Hsubscan]].
        unfold subscan in Hsubscan. reflect. tauto.
      * intros Hscan.
        enough (exists x, In x projsep /\ subscan pis (fst x) (snd x) (rev env) n m p = true).
        {
          destruct H as [polpl [Hin Hsub]].
          eapply in_l_combine in Hin; [|eapply mapM_length; exact Hinner].
          destruct Hin as [inner1 Hin].
          exists (polpl, inner1); simpl; eauto.
        }
        unfold subscan.
        rewrite Hscan.
        unfold PolyLang.env_scan in Hscan. destruct (nth_error pis m) as [pi|] eqn:Hpi; [|congruence].
        reflect.
        destruct (mapM_nth_error2 _ _ _ _ _ _ Hpi _ Hprojs) as [pol [Hproj Hpol]].
        destruct Hscan as [[_ Hpresize] Hpin].
        generalize (project_inclusion2 _ _ _ Hpin _ Hproj). intros Hpin2.
        destruct (split_and_sort_cover _ _ _ Hprojsep _ _ _ Hpol Hpin2) as [ppl [Hpplin [Hppl1 Hppl2]]].
        exists ppl. split; [auto|].
        reflect; split; [|auto]; split; auto.
        rewrite existsb_exists; exists m; reflect; auto.
Qed.
End ASTGen.

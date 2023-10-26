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
Require Import Bool.
Require Import List.
Require Import Permutation.
Require Import Psatz.

Require Import Misc.
Require Import Linalg.
Require Import Canonizer.
Require Import Projection.
Require Import TopoSort.
Require Import PolyTest.
Require Import ImpureAlarmConfig.

(** * Polyhedral intersection *)
(** Include several polyhedral level operations: *)
(** 1. [normal operators] inter, diff *)
(** 2. split poly, build dependency matrix, separate polys, split and sort *) 
(** 3. context simplify (used in codegen polyloop simplication) *)
(** * Note that operations in Linalg.v are much more basic than those in this file. *)
(** * Operations in this files calls VPL lib, and its computation are always captured in the impure monad. *)

Definition poly_inter_pure (p1 p2 : polyhedron) : polyhedron := p1 ++ p2.
Lemma poly_inter_pure_def :
  forall p pol1 pol2, in_poly p (poly_inter_pure pol1 pol2) = in_poly p pol1 && in_poly p pol2.
Proof.
  intros p pol1 pol2; unfold poly_inter_pure, in_poly.
  rewrite forallb_app; reflexivity.
Qed.

Definition poly_inter p1 p2 :=
  Canon.canonize (poly_inter_pure p1 p2).
Lemma poly_inter_def :
  forall p pol1 pol2, WHEN pol <- poly_inter pol1 pol2 THEN in_poly p pol = in_poly p (poly_inter_pure pol1 pol2).
Proof.
  intros p pol1 pol2 pol Hinter.
  apply Canon.canonize_correct in Hinter.
  specialize (Hinter 1 p). rewrite !expand_poly_1 in Hinter.
  apply Hinter; lia.
Qed.

(* Print Canon.canonize. *)

Lemma poly_inter_pure_no_new_var :
  forall pol1 pol2 k, absent_var pol1 k -> absent_var pol2 k -> absent_var (poly_inter_pure pol1 pol2) k.
Proof.
  intros pol1 pol2 k H1 H2 c Hc.
  rewrite in_app_iff in Hc; destruct Hc; auto.
Qed.

Lemma poly_inter_no_new_var :
  forall pol1 pol2 k, absent_var pol1 k -> absent_var pol2 k ->
                 WHEN pol <- poly_inter pol1 pol2 THEN absent_var pol k.
Proof.
  intros pol1 pol2 k H1 H2 pol Hpol.
  apply Canon.canonize_no_new_var with (k := k) in Hpol; [auto|].
  apply poly_inter_pure_no_new_var; auto.
Qed.

Lemma poly_inter_nrl :
  forall pol1 pol2 n, (poly_nrl pol1 <= n)%nat -> (poly_nrl pol2 <= n)%nat ->
                 WHEN pol <- poly_inter pol1 pol2 THEN (poly_nrl pol <= n)%nat.
Proof.
  intros pol1 pol2 n H1 H2 pol Hpol.
  rewrite has_var_poly_nrl in *.
  intros k Hnk; eapply poly_inter_no_new_var; [| |exact Hpol]; eauto.
Qed.


(** * Polyhedral difference *)
Fixpoint poly_difference p1 p2 :=
  match p2 with
  | nil => pure nil  (** empty pol for p2 implies universe, so p1 - p2 = nil *)
  | c :: p2 =>
    BIND pl1 <- VplCanonizerZ.canonize (neg_constraint c :: p1) -;
    BIND diff <- poly_difference (c :: p1) p2 -;
    BIND b <- isBottom pl1 -;
    pure (if b then diff else (pl1 :: diff))
  end.

Lemma poly_difference_def :
  forall p2 p1 v, WHEN pl <- poly_difference p1 p2 THEN
                  existsb (in_poly v) pl = in_poly v p1 && negb (in_poly v p2).
Proof.
  induction p2.
  - intros p1 v pl Hpl. apply mayReturn_pure in Hpl; rewrite <- Hpl. simpl. destruct in_poly; auto.
  - intros p1 v pl Hpl. simpl in *.
    bind_imp_destruct Hpl pl1 Hpl1; bind_imp_destruct Hpl diff Hdiff; bind_imp_destruct Hpl empty Hempty; apply mayReturn_pure in Hpl; rewrite <- Hpl.
    transitivity (existsb (in_poly v) (pl1 :: diff)).
    { destruct empty; simpl; [|reflexivity]. eapply isBottom_correct_1 in Hempty; simpl in *; rewrite Hempty; reflexivity. }
    simpl. rewrite IHp2; [|eauto].
    rewrite VplCanonizerZ.canonize_correct; [|eauto]. simpl.
    rewrite neg_constraint_correct; unfold in_poly; simpl.
    destruct (satisfies_constraint v a); simpl.
    + reflexivity.
    + destruct forallb; reflexivity.
Qed.

Lemma poly_difference_no_new_var :
  forall p2 p1 k, absent_var p1 k -> absent_var p2 k ->
             WHEN pl <- poly_difference p1 p2 THEN forall p, In p pl -> absent_var p k.
Proof.
  induction p2.
  - intros p1 k Hp1 Hp2 pl Hpl p Hp. apply mayReturn_pure in Hpl; rewrite <- Hpl in *. simpl in *. tauto.
  - intros p1 k Hp1 Hp2 pl Hpl p Hp. simpl in *.
    bind_imp_destruct Hpl pl1 Hpl1; bind_imp_destruct Hpl diff Hdiff; bind_imp_destruct Hpl empty Hempty;
      apply mayReturn_pure in Hpl; rewrite <- Hpl in *.
    assert (Hin : In p (pl1 :: diff)) by (destruct empty; simpl in *; tauto).
    simpl in *. destruct Hin; [|eapply (IHp2 (a :: p1) k); eauto using absent_var_cons, absent_var_head, absent_var_tail].
    rewrite H in *.
    unfold absent_var. eapply VplCanonizerZ.canonize_no_new_var; [|eauto].
    apply absent_var_cons; [|auto].
    apply absent_var_head in Hp2; unfold neg_constraint; simpl; rewrite mult_nth.
    lia.
Qed.

Lemma poly_difference_nrl :
  forall p1 p2 n, (poly_nrl p1 <= n)%nat -> (poly_nrl p2 <= n)%nat ->
             WHEN pl <- poly_difference p1 p2 THEN (forall p, In p pl -> (poly_nrl p <= n)%nat).
Proof.
  intros p1 p2 n Hp1 Hp2 pl Hpl p Hp.
  rewrite has_var_poly_nrl in *.
  intros k Hk; eapply poly_difference_no_new_var; [| |exact Hpl|]; eauto.
Qed.

Lemma poly_difference_disjoint :
  forall p2 p1, WHEN pols <- poly_difference p1 p2 THEN all_disjoint pols.
Proof.
  induction p2.
  - intros p1 pols Hpols; simpl in *. apply mayReturn_pure in Hpols; rewrite <- Hpols.
    apply all_disjoint_nil.
  - intros p1 pols Hpols. simpl in *.
    bind_imp_destruct Hpols pl1 Hpl1; bind_imp_destruct Hpols diff Hdiff; bind_imp_destruct Hpols empty Hempty; apply mayReturn_pure in Hpols; rewrite <- Hpols.
    enough (all_disjoint (pl1 :: diff)) by (destruct empty; [eapply all_disjoint_cons_rev; eauto|auto]).
    apply all_disjoint_cons; [eapply IHp2; eauto|].
    intros p pol1 Hpolin Hinpl Hinpol1.
    rewrite VplCanonizerZ.canonize_correct in Hinpl; [|eauto].
    eapply poly_difference_def with (v := p) in Hdiff.
    unfold in_poly in *; simpl in *.
    rewrite neg_constraint_correct in Hinpl.
    destruct (satisfies_constraint p a) eqn:Hsat; simpl in *.
    + congruence.
    + rewrite existsb_forall in Hdiff; rewrite Hdiff in Hinpol1; [congruence|auto].
Qed.

(** * Separating a list of polyhedra *)
Definition separate_polys pol1 pol2 :=
  BIND inter <- poly_inter pol1 pol2 -;
  BIND empty <- isBottom inter -;
  if empty then pure (nil, pol2 :: nil) else
  BIND diff <- poly_difference pol2 pol1 -;
  pure (inter :: nil, diff).

(* Print bind.
Print pure.
Print ImpureConfig.Core.Base.imp. *)

Lemma separate_polys_nrl :
  forall pol1 pol2 n, (poly_nrl pol1 <= n)%nat -> (poly_nrl pol2 <= n)%nat ->
                 WHEN sep <- separate_polys pol1 pol2 THEN
                      forall pol, In pol (fst sep ++ snd sep) -> (poly_nrl pol <= n)%nat.
Proof.
  intros pol1 pol2 n H1 H2 sep Hsep pol Hpol.
  unfold separate_polys in Hsep.
  bind_imp_destruct Hsep inter Hinter; bind_imp_destruct Hsep empty Hempty. destruct empty.
  - apply mayReturn_pure in Hsep; rewrite <- Hsep in *; simpl in *.
    destruct Hpol as [<- | ?]; tauto.
  - bind_imp_destruct Hsep diff Hdiff; apply mayReturn_pure in Hsep; rewrite <- Hsep in *.
    simpl in *.
    destruct Hpol as [<- | Hpol]; [|eapply poly_difference_nrl; [| |exact Hdiff|]; eauto].
    eapply poly_inter_nrl in Hinter; eauto.
Qed.

Lemma separate_polys_cover :
  forall pol1 pol2, WHEN sep <- separate_polys pol1 pol2 THEN
                    forall p, in_poly p pol2 = true <-> exists pol, In pol (fst sep ++ snd sep) /\ in_poly p pol = true.
Proof.
  intros pol1 pol2 sep Hsep p.
  unfold separate_polys in Hsep.
  bind_imp_destruct Hsep inter Hinter; bind_imp_destruct Hsep empty Hempty. destruct empty.
  - apply mayReturn_pure in Hsep; rewrite <- Hsep in *; simpl in *.
    split; [intros H; exists pol2; auto|intros [pol [H1 H2]]; intuition congruence].
  - bind_imp_destruct Hsep diff Hdiff; apply mayReturn_pure in Hsep; rewrite <- Hsep in *.
    simpl in *.
    apply poly_difference_def with (v := p) in Hdiff.
    apply poly_inter_def with (p := p) in Hinter; rewrite poly_inter_pure_def in Hinter.
    destruct (in_poly p pol1); simpl in *; split.
    + intros H; exists inter; intuition congruence.
    + intros [pol [[H1 | H1] H2]]; [congruence|]. rewrite andb_false_r, existsb_forall in Hdiff.
      specialize (Hdiff pol H1); congruence.
    + intros H; rewrite H, existsb_exists in Hdiff. destruct Hdiff as [pol [H1 H2]]; eauto.
    + intros [pol [[H1 | H1] H2]]; [congruence|]. rewrite andb_true_r in Hdiff; rewrite <- Hdiff, existsb_exists.
      eauto. 
Qed.

Lemma separate_polys_separate :
  forall pol1 pol2, WHEN sep <- separate_polys pol1 pol2 THEN
                    forall p pol, In pol (snd sep) -> in_poly p pol = true -> in_poly p pol1 = false.
Proof.
  intros pol1 pol2 sep Hsep p pol Hpolin Hinpol.
  unfold separate_polys in Hsep.
  bind_imp_destruct Hsep inter Hinter; bind_imp_destruct Hsep empty Hempty. destruct empty.
  - apply mayReturn_pure in Hsep; rewrite <- Hsep in *; simpl in *.
    destruct Hpolin as [<- | ?]; [|tauto].
    apply isBottom_correct_1 in Hempty; simpl in *. specialize (Hempty p).
    rewrite poly_inter_def in Hempty; [|eauto]. rewrite poly_inter_pure_def in Hempty.
    destruct (in_poly p pol1); simpl in *; congruence.
  - bind_imp_destruct Hsep diff Hdiff; apply mayReturn_pure in Hsep; rewrite <- Hsep in *.
    simpl in *.
    apply poly_difference_def with (v := p) in Hdiff.
    apply not_true_is_false; intros H. rewrite H, andb_false_r, existsb_forall in Hdiff.
    specialize (Hdiff pol Hpolin); congruence.
Qed.

Lemma separate_polys_disjoint :
  forall pol1 pol2, WHEN sep <- separate_polys pol1 pol2 THEN all_disjoint (fst sep ++ snd sep).
Proof.
  intros pol1 pol2 sep Hsep.
  unfold separate_polys in Hsep.
  bind_imp_destruct Hsep inter Hinter; bind_imp_destruct Hsep empty Hempty. destruct empty.
  - apply mayReturn_pure in Hsep; rewrite <- Hsep in *; simpl in *.
    apply all_disjoint_cons; [apply all_disjoint_nil|]. intros; simpl in *; auto.
  - bind_imp_destruct Hsep diff Hdiff; apply mayReturn_pure in Hsep; rewrite <- Hsep in *.
    apply all_disjoint_app.
    + simpl. apply all_disjoint_cons; [apply all_disjoint_nil|].
      intros; simpl in *; auto.
    + simpl. eapply poly_difference_disjoint; eauto.
    + intros p p1 p2 H1 H2 Hp1 Hp2; simpl in *. destruct H1 as [H1 | H1]; [|auto].
      apply poly_difference_def with (v := p) in Hdiff.
      apply poly_inter_def with (p := p) in Hinter; rewrite poly_inter_pure_def, H1 in Hinter.
      rewrite Hinter in Hp1; reflect. destruct Hp1 as [Hpol1 Hpol2]; rewrite Hpol1, andb_false_r in Hdiff.
      rewrite existsb_forall in Hdiff; specialize (Hdiff p2 H2). congruence.
Qed.  

Fixpoint split_polys_rec (l : list polyhedron) (n : nat) : imp (list (polyhedron * list nat)) :=
  match l with
  | nil => pure ((nil, nil) :: nil)
  | p :: l =>
    BIND spl <- split_polys_rec l (S n) -;
    BIND spl1 <- mapM (fun '(pol, pl) =>
         BIND sep <- separate_polys p pol -;
         pure (map (fun pp => (pp, n :: pl)) (fst sep) ++ map (fun pp => (pp, pl)) (snd sep))
    ) spl -;
    pure (flatten spl1)
  end.

Lemma split_polys_rec_index_correct :
  forall pols n, WHEN out <- split_polys_rec pols n THEN forall polpl i, In polpl out -> In i (snd polpl) -> (n <= i < n + length pols)%nat.
Proof.
  induction pols.
  - intros n out Hout ppl i Hin Hiin.
    simpl in *. apply mayReturn_pure in Hout. rewrite <- Hout in Hin.
    simpl in Hin; destruct Hin as [Hin | Hin]; [|tauto]. rewrite <- Hin in Hiin; simpl in Hiin; tauto.
  - intros n out Hout ppl i Hin Hiin.
    simpl in *.
    bind_imp_destruct Hout spl Hspl; bind_imp_destruct Hout spl1 Hspl1; apply mayReturn_pure in Hout; rewrite <- Hout in *.
    rewrite flatten_In in Hin. destruct Hin as [u [Hppl Hu]].
    eapply mapM_in_iff in Hu; [|eauto].
    destruct Hu as [[pol pl] [Hu Hpolpl]].
    bind_imp_destruct Hu sep Hsep. apply mayReturn_pure in Hu; rewrite <- Hu in *.
    simpl in Hppl. rewrite in_app_iff, !in_map_iff in Hppl.
    specialize (IHpols _ _ Hspl (pol, pl)); simpl in IHpols.
    destruct Hppl as [[? [Heq _]] | [? [Heq _]]]; rewrite <- Heq in Hiin; simpl in Hiin; [destruct Hiin as [Hiin | Hiin]; [lia|]|];
      specialize (IHpols i Hpolpl Hiin); lia.
Qed.

Lemma split_polys_rec_index_NoDup :
  forall pols n, WHEN out <- split_polys_rec pols n THEN forall polpl, In polpl out -> NoDup (snd polpl).
Proof.
  induction pols.
  - intros n out Hout ppl Hin.
    simpl in *. apply mayReturn_pure in Hout. rewrite <- Hout in Hin.
    simpl in Hin; destruct Hin as [Hin | Hin]; [|tauto]. rewrite <- Hin; constructor.
  - intros n out Hout ppl Hin.
    simpl in *.
    bind_imp_destruct Hout spl Hspl; bind_imp_destruct Hout spl1 Hspl1; apply mayReturn_pure in Hout; rewrite <- Hout in *.
    rewrite flatten_In in Hin. destruct Hin as [u [Hppl Hu]].
    eapply mapM_in_iff in Hu; [|eauto].
    destruct Hu as [[pol pl] [Hu Hpolpl]].
    bind_imp_destruct Hu sep Hsep. apply mayReturn_pure in Hu; rewrite <- Hu in *.
    simpl in Hppl. rewrite in_app_iff, !in_map_iff in Hppl.
    specialize (IHpols _ _ Hspl (pol, pl)); simpl in IHpols.
    destruct Hppl as [[? [Heq _]] | [? [Heq _]]]; rewrite <- Heq; simpl; [|intuition].
    constructor; [|intuition].
    intros H; eapply (split_polys_rec_index_correct _ _ _ Hspl _ _ Hpolpl) in H.
    lia.
Qed.

Lemma split_polys_rec_nrl :
  forall pols n, WHEN out <- split_polys_rec pols n THEN
                 forall k, (forall pol, In pol pols -> (poly_nrl pol <= k)%nat) -> (forall ppl, In ppl out -> (poly_nrl (fst ppl) <= k)%nat).
Proof.
  induction pols.
  - intros n out Hout k Hpols ppl Hin.
    simpl in *. apply mayReturn_pure in Hout. rewrite <- Hout in Hin.
    simpl in Hin; destruct Hin as [Hin | Hin]; [|tauto]. rewrite <- Hin; unfold poly_nrl; simpl; lia.
  - intros n out Hout k Hpols ppl Hin.
    simpl in *.
    bind_imp_destruct Hout spl Hspl; bind_imp_destruct Hout spl1 Hspl1; apply mayReturn_pure in Hout; rewrite <- Hout in *.
    rewrite flatten_In in Hin. destruct Hin as [u [Hppl Hu]].
    eapply mapM_in_iff in Hu; [|eauto].
    destruct Hu as [[pol pl] [Hu Hpolpl]].
    bind_imp_destruct Hu sep Hsep. apply mayReturn_pure in Hu; rewrite <- Hu in *.
    eapply separate_polys_nrl in Hsep; [apply Hsep|apply Hpols; auto|eapply (IHpols _ _ Hspl _ _ (pol, pl)); eauto]. Unshelve. 2:eauto.
    apply in_map with (f := fst) in Hppl; simpl in Hppl; rewrite map_app, !map_map, !map_id in Hppl.
    exact Hppl.
Qed.

Lemma split_polys_rec_disjoint :
  forall pols n, WHEN out <- split_polys_rec pols n THEN all_disjoint (map fst out).
Proof.
    induction pols.
  - intros n out Hout p k1 k2 ppl1 ppl2 Hk1 Hk2 Hppl1 Hppl2.
    simpl in *. apply mayReturn_pure in Hout. rewrite <- Hout in *.
    destruct k1 as [|[|k1]]; destruct k2 as [|[|k2]]; simpl in *; congruence.
  - intros n out Hout.
    simpl in *.
    bind_imp_destruct Hout spl Hspl; bind_imp_destruct Hout spl1 Hspl1; apply mayReturn_pure in Hout; rewrite <- Hout in *.
    rewrite flatten_map. apply all_disjoint_flatten.
    + intros l1 Hl1.
      rewrite in_map_iff in Hl1. destruct Hl1 as [pll [Hpll Hin1]]; rewrite <- Hpll.
      eapply mapM_in_iff in Hin1; [|eauto]. destruct Hin1 as [[pol pl] [H1 H2]].
      bind_imp_destruct H1 sep Hsep; apply mayReturn_pure in H1; rewrite <- H1.
      simpl; rewrite map_app, !map_map, !map_id.
      eapply separate_polys_disjoint; eauto.
    + intros p k1 k2 l1 l2 pol1 pol2 Hk1 Hk2 Hl1 Hl2 Hin1 Hin2.
      rewrite nth_error_map_iff in Hk1, Hk2.
      destruct Hk1 as [pll1 [Hk1 Hll1]]; destruct Hk2 as [pll2 [Hk2 Hll2]]; rewrite Hll1, Hll2 in *.
      eapply mapM_nth_error1 in Hk1; [|exact Hspl1]. destruct Hk1 as [[pp1 pl1] [H1 Hk1]].
      eapply mapM_nth_error1 in Hk2; [|exact Hspl1]. destruct Hk2 as [[pp2 pl2] [H2 Hk2]].
      bind_imp_destruct H1 sep1 Hsep1; bind_imp_destruct H2 sep2 Hsep2.
      apply mayReturn_pure in H1; apply mayReturn_pure in H2. rewrite <- H1 in Hl1; rewrite <- H2 in Hl2.
      simpl in Hl1, Hl2; rewrite map_app, !map_map, !map_id in Hl1, Hl2.
      assert (Ht1 : in_poly p pp1 = true) by (erewrite (separate_polys_cover _ _ _ Hsep1 _); exists pol1; auto).
      assert (Ht2 : in_poly p pp2 = true) by (erewrite (separate_polys_cover _ _ _ Hsep2 _); exists pol2; auto).
      apply map_nth_error with (f := fst) in Hk1; apply map_nth_error with (f := fst) in Hk2.
      specialize (IHpols _ _ Hspl _ _ _ _ _ Hk1 Hk2 Ht1 Ht2). auto.
Qed.

Lemma split_polys_rec_cover_all :
  forall pols n, WHEN out <- split_polys_rec pols n THEN forall p, exists ppl, In ppl out /\ in_poly p (fst ppl) = true /\
                                                               (forall k pol, nth_error pols k = Some pol -> in_poly p pol = true -> In (n + k)%nat (snd ppl)).
Proof.
  induction pols.
  - intros n out Hout p.
    simpl in *. apply mayReturn_pure in Hout. exists (nil, nil). rewrite <- Hout.
    simpl; split; [|split]; auto. intros [|k]; simpl; congruence.
  - intros n out Hout p.
    simpl in *.
    bind_imp_destruct Hout spl Hspl; bind_imp_destruct Hout spl1 Hspl1; apply mayReturn_pure in Hout; rewrite <- Hout in *.
    destruct (IHpols _ _ Hspl p) as [[pol pl] [Hppl1 [Hin1 Hins1]]]; simpl in *.
    apply In_nth_error in Hppl1. destruct Hppl1 as [k1 Hk1].
    destruct (mapM_nth_error2 _ _ _ _ _ _ Hk1 _ Hspl1) as [lppl [Hlppl Hk2]].
    apply nth_error_In in Hk2.
    bind_imp_destruct Hlppl sep Hsep; apply mayReturn_pure in Hlppl.
    eapply separate_polys_cover in Hin1; [|eauto]. destruct Hin1 as [pol1 [Hpol1in Hinpol1]].
    rewrite in_app_iff in Hpol1in.
    destruct Hpol1in as [Hpol1in | Hpol1in]; [exists (pol1, n :: pl)|exists (pol1, pl)]; simpl; rewrite flatten_In.
    all: split; [exists lppl; split; [rewrite <- Hlppl; simpl|auto]|split; [auto|]].
    + rewrite in_app_iff; left. rewrite in_map_iff; exists pol1. auto.
    + intros [|k] pol2 Hk Hin2; simpl in *; [left; lia|right; rewrite Nat.add_succ_r; eapply Hins1; eauto].
    + rewrite in_app_iff; right. rewrite in_map_iff; exists pol1. auto.
    + intros [|k] pol2 Hk Hin2; simpl in *; [|rewrite Nat.add_succ_r; eapply Hins1; eauto].
      exfalso. eapply separate_polys_separate in Hinpol1; eauto. congruence.
Qed.

Definition split_polys pols :=
  BIND spl <- split_polys_rec pols 0%nat -;
  pure (filter (fun ppl => match snd ppl with nil => false | _ => true end) spl).

Lemma split_polys_index_correct :
  forall pols, WHEN out <- split_polys pols THEN forall polpl i, In polpl out -> In i (snd polpl) -> (i < length pols)%nat.
Proof.
  intros pols out Hout ppl i H1 H2.
  bind_imp_destruct Hout out1 Hout1. apply mayReturn_pure in Hout; rewrite <- Hout in *.
  rewrite filter_In in H1.
  generalize (split_polys_rec_index_correct pols 0%nat out1 Hout1 ppl i). intuition lia.
Qed.

Lemma split_polys_index_NoDup :
  forall pols, WHEN out <- split_polys pols THEN forall polpl, In polpl out -> NoDup (snd polpl).
Proof.
  intros pols out Hout ppl Hin.
  bind_imp_destruct Hout out1 Hout1. apply mayReturn_pure in Hout; rewrite <- Hout in *.
  rewrite filter_In in Hin; destruct Hin.
  eapply (split_polys_rec_index_NoDup pols 0%nat); eauto.
Qed.

Lemma split_polys_nrl :
  forall pols, WHEN out <- split_polys pols THEN forall k, (forall pol, In pol pols -> (poly_nrl pol <= k)%nat) -> (forall ppl, In ppl out -> (poly_nrl (fst ppl) <= k)%nat).
Proof.
  intros pols out Hout k H ppl Hin.
  bind_imp_destruct Hout out1 Hout1. apply mayReturn_pure in Hout; rewrite <- Hout in *.
  rewrite filter_In in Hin; destruct Hin.
  eapply (split_polys_rec_nrl pols 0%nat); eauto.
Qed.

Lemma split_polys_disjoint :
  forall pols, WHEN out <- split_polys pols THEN all_disjoint (map fst out).
Proof.
  intros pols out Hout.
  bind_imp_destruct Hout out1 Hout1. apply mayReturn_pure in Hout; rewrite <- Hout in *.
  apply split_polys_rec_disjoint in Hout1.
  apply all_disjoint_map_filter. auto.
Qed.

Lemma split_polys_cover :
  forall pols, WHEN out <- split_polys pols THEN
          forall p pol i, nth_error pols i = Some pol -> in_poly p pol = true -> exists ppl, In ppl out /\ In i (snd ppl) /\ in_poly p (fst ppl) = true.
Proof.
  intros pols out Hout p pol i Hi Hin.
  bind_imp_destruct Hout out1 Hout1. apply mayReturn_pure in Hout; rewrite <- Hout in *.
  destruct (split_polys_rec_cover_all _ _ _ Hout1 p) as [ppl Hppl].
  exists ppl. destruct Hppl as [H1 [H2 H3]]; specialize (H3 i pol).
  rewrite filter_In. split; [|auto]. split; [auto|]. destruct (snd ppl); [|auto].
  exfalso; apply H3; auto.
Qed.

(** * Building a dependency matrix for a list of polyhedra *)

Definition build_dependency_matrix n pols :=
  mapM (fun pol1 =>
          BIND proj1 <- Proj.project (n, pol1) -;
          mapM (fun pol2 => fmap negb (check_canPrecede n pol1 pol2 proj1)) pols) pols.

Lemma build_dependency_matrix_length :
  forall n pols, WHEN out <- build_dependency_matrix n pols THEN length out = length pols.
Proof.
  intros n pols out Hout.
  unfold build_dependency_matrix in Hout.
  symmetry; eapply mapM_length; eauto.
Qed.

Lemma build_dependency_matrix_canPrecede :
  forall n pols, WHEN out <- build_dependency_matrix n pols THEN
                 forall k1 k2 ppl1 ppl2, nth_error pols k1 = Some ppl1 -> nth_error pols k2 = Some ppl2 ->
                                    nth k2 (nth k1 out nil) true = false ->
                                    canPrecede n ppl1 ppl2.
Proof.
  intros n pols out Hout k1 k2 ppl1 ppl2 Hk1 Hk2 H.
  unfold build_dependency_matrix in Hout.
  eapply mapM_nth_error2 with (k := k1) in Hout; [|eauto].
  destruct Hout as [row [Hrow Hout]].
  bind_imp_destruct Hrow proj Hproj.
  eapply mapM_nth_error2 with (k := k2) in Hrow; [|eauto].
  destruct Hrow as [b [Hb Hrow]].
  erewrite nth_error_nth with (n := k1) in H; [|eauto].
  erewrite nth_error_nth in H; [|eauto]. rewrite H in Hb.
  unfold fmap in Hb. bind_imp_destruct Hb b1 Hb1; apply mayReturn_pure in Hb.
  destruct b1; simpl in *; [|congruence].
  eapply check_canPrecede_correct in Hb1; simpl in Hb1; [auto|].
  eapply Proj.project_in_iff; eauto.
Qed.

(** * Splitting and sorting a list of polyhedra *)

Definition split_and_sort n pols :=
  BIND spl <- split_polys pols -;
  BIND deps <- build_dependency_matrix n (map fst spl) -;
  BIND indices <- topo_sort deps -;
  pure (map (fun t => nth t spl (nil, nil)) indices).
(* Print split_and_sort. *)
(* Print nth.
Print map.
Print split_polys. *)
Lemma split_and_sort_index_NoDup :
  forall n pols, WHEN out <- split_and_sort n pols THEN forall polpl, In polpl out -> NoDup (snd polpl).
Proof.
  intros n pols out Hout polpl Hin.
  unfold split_and_sort in Hout.
  bind_imp_destruct Hout spl Hspl; bind_imp_destruct Hout deps Hdeps; bind_imp_destruct Hout indices Hindices; apply mayReturn_pure in Hout; rewrite <- Hout in *.
  rewrite in_map_iff in Hin. destruct Hin as [t [Hpolpl _]].
  destruct (t <? length spl)%nat eqn:Ht; reflect.
  - eapply nth_In in Ht; rewrite Hpolpl in Ht.
    eapply split_polys_index_NoDup in Ht; eauto.
  - eapply nth_overflow in Ht; rewrite Hpolpl in Ht.
    rewrite Ht; simpl. constructor.
Qed.

Lemma split_and_sort_index_correct :
  forall n pols, WHEN out <- split_and_sort n pols THEN forall polpl i, In polpl out -> In i (snd polpl) -> (i < length pols)%nat.
Proof.
  intros n pols out Hout polpl i Hin Hiin.
  unfold split_and_sort in Hout.
  bind_imp_destruct Hout spl Hspl; bind_imp_destruct Hout deps Hdeps; bind_imp_destruct Hout indices Hindices; apply mayReturn_pure in Hout; rewrite <- Hout in *.
  rewrite in_map_iff in Hin. destruct Hin as [t [Hpolpl _]].
  destruct (t <? length spl)%nat eqn:Ht; reflect.
  - eapply nth_In in Ht; rewrite Hpolpl in Ht.
    eapply split_polys_index_correct in Ht; eauto.
  - eapply nth_overflow in Ht; rewrite Hpolpl in Ht.
    rewrite Ht in Hiin; simpl in Hiin; tauto.
Qed.

Lemma split_and_sort_nrl :
  forall n pols, WHEN out <- split_and_sort n pols THEN forall k, (forall pol, In pol pols -> (poly_nrl pol <= k)%nat) -> (forall ppl, In ppl out -> (poly_nrl (fst ppl) <= k)%nat).
Proof.
  intros n pols out Hout k Hk ppl Hin.
  unfold split_and_sort in Hout.
  bind_imp_destruct Hout spl Hspl; bind_imp_destruct Hout deps Hdeps; bind_imp_destruct Hout indices Hindices; apply mayReturn_pure in Hout; rewrite <- Hout in *.
  rewrite in_map_iff in Hin. destruct Hin as [t [Hppl _]].
  destruct (t <? length spl)%nat eqn:Ht; reflect.
  - eapply nth_In in Ht; rewrite Hppl in Ht.
    eapply split_polys_nrl in Ht; eauto.
  - eapply nth_overflow in Ht; rewrite Hppl in Ht.
    rewrite Ht. unfold poly_nrl; simpl. lia.
Qed.

Lemma split_and_sort_disjoint :
  forall n pols, WHEN out <- split_and_sort n pols THEN
          forall p k1 k2 ppl1 ppl2, nth_error out k1 = Some ppl1 -> nth_error out k2 = Some ppl2 ->
                               in_poly p (fst ppl1) = true -> in_poly p (fst ppl2) = true -> k1 = k2.
Proof.
  intros n pols out Hout p k1 k2 ppl1 ppl2 Hk1 Hk2 Hp1 Hp2.
  unfold split_and_sort in Hout.
  bind_imp_destruct Hout spl Hspl; bind_imp_destruct Hout deps Hdeps; bind_imp_destruct Hout indices Hindices; apply mayReturn_pure in Hout; rewrite <- Hout in *.
  rewrite nth_error_map_iff in Hk1, Hk2.
  destruct Hk1 as [t1 [Hind1 Ht1]]; destruct Hk2 as [t2 [Hind2 Ht2]].
  symmetry in Ht1; rewrite <- nth_error_nth_iff in Ht1 by (
    erewrite <- map_length, <- build_dependency_matrix_length; [|eauto];
    eapply topo_sort_indices_correct; [eauto|]; apply nth_error_In in Hind1; eauto
  ).
  symmetry in Ht2; rewrite <- nth_error_nth_iff in Ht2 by (
    erewrite <- map_length, <- build_dependency_matrix_length; [|eauto];
    eapply topo_sort_indices_correct; [eauto|]; apply nth_error_In in Hind2; eauto
  ).
  assert (t1 = t2) by (eapply split_polys_disjoint; try (apply map_nth_error); eauto).
  eapply NoDup_nth_error; [|apply nth_error_Some; rewrite Hind1; congruence|congruence].
  eapply Permutation_NoDup; [apply topo_sort_permutation; eauto|apply n_range_NoDup].
Qed.  

Lemma split_and_sort_cover :
  forall n pols, WHEN out <- split_and_sort n pols THEN
            forall p pol i, nth_error pols i = Some pol -> in_poly p pol = true -> exists ppl, In ppl out /\ In i (snd ppl) /\ in_poly p (fst ppl) = true.
Proof.
  intros n pols out Hout p pol i Hi Hp.
  unfold split_and_sort in Hout.
  bind_imp_destruct Hout spl Hspl; bind_imp_destruct Hout deps Hdeps; bind_imp_destruct Hout indices Hindices; apply mayReturn_pure in Hout; rewrite <- Hout in *.
  eapply split_polys_cover in Hi; [|eauto]. specialize (Hi Hp).
  destruct Hi as [ppl [Hin [Hiin Hp1]]]. exists ppl.
  split; [|auto].
  apply In_nth_error in Hin; destruct Hin as [k Hk].
  rewrite in_map_iff. exists k. split; [erewrite nth_error_nth; eauto|].
  eapply Permutation_in; [eapply topo_sort_permutation; eauto|].
  erewrite build_dependency_matrix_length, map_length; [|eauto].
  rewrite n_range_in. apply nth_error_Some. congruence.
Qed.

Lemma split_and_sort_sorted :
  forall n pols, WHEN out <- split_and_sort n pols THEN
            forall k1 k2 ppl1 ppl2, nth_error out k1 = Some ppl1 -> nth_error out k2 = Some ppl2 ->
                               (k1 < k2)%nat -> canPrecede n (fst ppl1) (fst ppl2).
Proof.
  intros n pols out Hout k1 k2 ppl1 ppl2 Hk1 Hk2 Hcmp.
  bind_imp_destruct Hout spl Hspl; bind_imp_destruct Hout deps Hdeps; bind_imp_destruct Hout indices Hindices; apply mayReturn_pure in Hout; rewrite <- Hout in *.
  rewrite nth_error_map_iff in Hk1, Hk2.
  destruct Hk1 as [t1 [Hind1 Ht1]]; destruct Hk2 as [t2 [Hind2 Ht2]].
  symmetry in Ht1; rewrite <- nth_error_nth_iff in Ht1 by (
    erewrite <- map_length, <- build_dependency_matrix_length; [|eauto];
    eapply topo_sort_indices_correct; [eauto|]; apply nth_error_In in Hind1; eauto
  ).
  symmetry in Ht2; rewrite <- nth_error_nth_iff in Ht2 by (
    erewrite <- map_length, <- build_dependency_matrix_length; [|eauto];
    eapply topo_sort_indices_correct; [eauto|]; apply nth_error_In in Hind2; eauto
  ).
  assert (Hcmp2 : (k1 < k2 < length deps)%nat) by (split; [auto|]; rewrite <- topo_sort_length, <- nth_error_Some; [|eauto]; congruence).
  eapply topo_sort_sorted in Hcmp2; [|eauto].
  erewrite nth_error_nth with (n := k1) in Hcmp2; [|eauto].
  erewrite nth_error_nth with (n := k2) in Hcmp2; [|eauto].
  eapply build_dependency_matrix_canPrecede; [eauto| | |eauto]; erewrite map_nth_error; eauto.
Qed.

(** * Simplifying a polyhedron in a context *)

Fixpoint ctx_simplify pol ctx :=
  match pol with
  | nil => pure nil
  | c :: pol =>
    BIND simp1 <- ctx_simplify pol ctx -;
    BIND b <- isBottom (neg_constraint c :: simp1 ++ ctx) -;
    pure (if b then simp1 else c :: simp1)
  end.

Lemma ctx_simplify_correct :
  forall pol ctx, WHEN simp <- ctx_simplify pol ctx THEN (forall p, in_poly p ctx = true -> in_poly p pol = in_poly p simp).
Proof.
  induction pol; intros ctx simp Hsimp p Hpctx; simpl in *.
  - apply mayReturn_pure in Hsimp; rewrite <- Hsimp; reflexivity.
  - bind_imp_destruct Hsimp simp1 Hsimp1; bind_imp_destruct Hsimp b Hb; apply mayReturn_pure in Hsimp; rewrite <- Hsimp in *.
    transitivity (satisfies_constraint p a && in_poly p simp1); [f_equal; eapply IHpol; eauto|].
    destruct b; simpl; [|auto].
    apply isBottom_correct_1 in Hb; specialize (Hb p); simpl in *.
    rewrite neg_constraint_correct in Hb.
    destruct (satisfies_constraint p a); [auto|]. simpl in *.
    rewrite in_poly_app, Hpctx, andb_true_r in Hb. auto.
Qed.

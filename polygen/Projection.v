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

Require Import QArith.
Require Import QOrderedType.
Require Import ZArith.
Require Import List.
Require Import Psatz.

Require Import Misc.
Require Import Linalg.
Require Import Canonizer.
Require Import Heuristics.

Require Import Vpl.Impure.

Open Scope Z_scope.

(** * Projection of a polyhedron on a given variable *)

Definition isExactProjection n pol proj :=
  forall p s, 0 < s -> in_poly p (expand_poly s proj) = true <->
                 exists t k, 0 < t /\ in_poly (assign n k (mult_vector t p)) (expand_poly (s * t) pol) = true.

Definition isExactProjection1 n pol proj :=
  forall p, in_poly p proj = true <-> exists t k, 0 < t /\ in_poly (assign n k (mult_vector t p)) (expand_poly t pol) = true.

Lemma isExactProjection_weaken1 :
  forall n pol proj, isExactProjection n pol proj -> isExactProjection1 n pol proj.
Proof.
  intros n pol proj H p.
  specialize (H p 1). rewrite expand_poly_1 in H; rewrite H by lia. 
  split; intros [t [k Htk]]; exists t; exists k; rewrite Z.mul_1_l in *; auto.
Qed.

Lemma isExactProjection_assign :
  forall n p x t pol proj, 0 < t -> isExactProjection n pol proj -> in_poly p (expand_poly t pol) = true ->
                      in_poly (assign n x p) (expand_poly t proj) = true.
Proof.
  intros n p x t pol proj Ht Hproj Hpol.
  rewrite (Hproj _ t) by lia. exists 1. exists (nth n p 0). split; [lia|].
  rewrite <- Hpol. f_equiv; [|f_equal; lia].
  rewrite mult_vector_1. rewrite assign_assign.
  apply assign_id.
Qed.

Lemma isExactProjection_assign_1 :
  forall n p x pol proj, isExactProjection1 n pol proj -> in_poly p pol = true ->
                      in_poly (assign n x p) proj = true.
Proof.
  intros n p x pol proj Hproj Hpol.
  rewrite (Hproj _) by lia. exists 1. exists (nth n p 0). split; [lia|].
  rewrite <- Hpol. rewrite expand_poly_1. f_equiv.
  rewrite mult_vector_1. rewrite assign_assign.
  apply assign_id.
Qed.

Module Type ProjectOperator (Import Imp: FullImpureMonad).

  Parameter project : (nat * polyhedron) -> imp polyhedron.

  Parameter project_projected :
    forall n pol, WHEN proj <- project (n, pol) THEN absent_var proj n.

  Parameter project_no_new_var :
    forall n k pol, absent_var pol k -> WHEN proj <- project (n, pol) THEN absent_var proj k.

  Parameter project_in_iff :
    forall n pol, WHEN proj <- project (n, pol) THEN isExactProjection n pol proj.

End ProjectOperator.

Module FourierMotzkinProject (Import Imp: FullImpureMonad) <: ProjectOperator Imp.

  Definition merge_constraints n c1 c2 :=
    let '(g, (aa, bb)) := Z.ggcd (nth n (fst c1) 0) (nth n (fst c2) 0) in
    add_constraint (mult_constraint bb c1) (mult_constraint (-aa) c2).

  Lemma Q_exists_rec :
    forall (l1 l2 : list Q) (y1 : Q), ((exists x : Q, (forall y : Q, In y l1 -> (y <= x)%Q) /\ (forall z : Q, In z l2 -> (x <= z)%Q)) <->
                                  (forall y z : Q, In y l1 -> In z l2 -> (y <= z)%Q)) ->
                                 ((exists x : Q, (forall y : Q, In y (y1 :: l1) -> (y <= x)%Q) /\ (forall z : Q, In z l2 -> (x <= z)%Q)) <->
                                  (forall y z : Q, In y (y1 :: l1) -> In z l2 -> (y <= z)%Q)).
  Proof.
    intros l1 l2 y1 [Himp1 Himp2].
    split.
    - intros [x [Hxy Hxz]] y z Hiny Hinz.
      specialize (Hxy y Hiny). specialize (Hxz z Hinz). q_order.
    - intros H. destruct Himp2 as [x [Hxy Hxz]].
      + intros y z Hiny Hinz. apply H; simpl; auto.
      + destruct (Qlt_le_dec x y1).
        * exists y1. split.
          -- intros y [Hy1| Hiny]; [rewrite Hy1 | specialize (Hxy y Hiny)]; q_order.
          -- intros z Hinz. apply H; simpl; auto.
        * exists x. split.
          -- intros y [Hy1 | Hiny]; [rewrite Hy1 in *; q_order | apply Hxy; auto].
          -- auto.
  Qed.

  Lemma Q_exists_min :
    forall (l : list Q), exists x : Q, forall y : Q, In y l -> (x <= y)%Q.
  Proof.
    induction l as [|y1 l IH].
    - exists 0%Q; intros; simpl in *; tauto.
    - destruct IH as [x IH].
      destruct (Qlt_le_dec x y1).
      + exists x. intros y [Hy1 | Hiny]; [rewrite Hy1 in *; q_order | apply (IH y Hiny)].
      + exists y1. intros y [Hy1 | Hiny]; [rewrite Hy1 | specialize (IH y Hiny)]; q_order.
  Qed.


  Lemma Q_exists_between :
    forall (l1 l2 : list Q), (exists x : Q, (forall y : Q, In y l1 -> (y <= x)%Q) /\ (forall z : Q, In z l2 -> (x <= z)%Q)) <->
                        (forall y z : Q, In y l1 -> In z l2 -> (y <= z)%Q).
  Proof.
    induction l1 as [|y1 l1 IH1].
    - intros l2. split.
      + intros; simpl in *; tauto.
      + intros H; destruct (Q_exists_min l2) as [x Hx]; exists x.
        split; [intros; simpl in *; tauto | apply Hx].
    - intros l2; apply Q_exists_rec. apply IH1.
  Qed.

  Definition bound k c p :=
    (inject_Z (snd c - dot_product (assign k 0 p) (fst c))%Z / inject_Z (nth k (fst c) 0)%Z)%Q.

  Lemma assign_0_eq :
    forall k c p s, nth k (fst c) 0 = 0 -> satisfies_constraint (assign k s p) c = satisfies_constraint p c.
  Proof.
    intros k c p s H.
    unfold satisfies_constraint. f_equal. apply dot_product_assign_left_zero; auto.
  Qed.

  Lemma assign_pos_bound :
    forall k c p s t , 0 < nth k (fst c) 0 -> 0 < t ->
                  satisfies_constraint (assign k s (mult_vector t p)) (mult_constraint_cst t c) =
                  (Qle_bool (inject_Z s / inject_Z t) (bound k c p))%Q.
  Proof.
    intros k c p s t Hckpos Htpos. unfold bound.
    destruct t as [|tpos|tneg]; [lia| |lia].
    destruct (nth k (fst c) 0) as [|upos|uneg] eqn:Hu; [lia| |lia].
    unfold satisfies_constraint, Qle_bool, Qdiv, Qmult, Qinv, inject_Z; simpl.
    rewrite !dot_product_assign_left, dot_product_mult_left, mult_nth.
    rewrite eq_iff_eq_true; reflect. destruct (snd c); nia.
  Qed.

  Lemma assign_neg_bound :
    forall k c p s t , nth k (fst c) 0 < 0 -> 0 < t ->
                  satisfies_constraint (assign k s (mult_vector t p)) (mult_constraint_cst t c) =
                  (Qle_bool (bound k c p) (inject_Z s / inject_Z t))%Q.
  Proof.
    intros k c p s t Hckpos Htpos. unfold bound.
    destruct t as [|tpos|tneg]; [lia| |lia].
    destruct (nth k (fst c) 0) as [|upos|uneg] eqn:Hu; [lia|lia|].
    unfold satisfies_constraint, Qle_bool, Qdiv, Qmult, Qinv, inject_Z; simpl.
    rewrite !dot_product_assign_left, dot_product_mult_left, mult_nth.
    rewrite eq_iff_eq_true; reflect. destruct (snd c); nia.
  Qed.

  Lemma is_projected_separate :
    forall n pol p s, 0 < s ->
      (exists t k, 0 < t /\ in_poly (assign n k (mult_vector t p)) (expand_poly (s * t) pol) = true) <->
      (in_poly p (expand_poly s (filter (fun c => nth n (fst c) 0 =? 0) pol)) = true /\
       forall y z, In y (map (fun c => bound n (mult_constraint_cst s c) p) (filter (fun c => nth n (fst c) 0 <? 0) pol)) ->
              In z (map (fun c => bound n (mult_constraint_cst s c) p) (filter (fun c => nth n (fst c) 0 >? 0) pol)) ->
              (y <= z)%Q).
  Proof.
    intros n pol p s Hs.
    rewrite <- Q_exists_between.
    split.
    - intros [t [k [Ht Hin]]]. split.
      + unfold in_poly, expand_poly in *.
        rewrite forallb_map, forallb_forall in *. intros c Hinc.
        rewrite filter_In in Hinc. destruct Hinc as [Hinc Hnthc].
        specialize (Hin c Hinc). reflect.
        rewrite assign_0_eq, Z.mul_comm, <- mult_constraint_cst_comp, mult_constraint_cst_eq in Hin by (simpl; auto).
        exact Hin.
      + exists ((inject_Z k) / (inject_Z t))%Q. split.
        * intros y Hy. rewrite in_map_iff in Hy; destruct Hy as [c [Hy Hinc]].
          rewrite filter_In in Hinc; destruct Hinc as [Hinc Hnthc]. reflect.
          rewrite <- Hy. rewrite <- Qle_bool_iff, <- assign_neg_bound by auto.
          rewrite mult_constraint_cst_comp. unfold in_poly in Hin. rewrite forallb_forall in Hin.
          apply Hin. rewrite Z.mul_comm. unfold expand_poly. apply in_map. auto.
        * intros y Hy. rewrite in_map_iff in Hy; destruct Hy as [c [Hy Hinc]].
          rewrite filter_In in Hinc; destruct Hinc as [Hinc Hnthc]. reflect.
          rewrite <- Hy. rewrite <- Qle_bool_iff, <- assign_pos_bound by auto.
          rewrite mult_constraint_cst_comp. unfold in_poly in Hin. rewrite forallb_forall in Hin.
          apply Hin. rewrite Z.mul_comm. unfold expand_poly. apply in_map. auto.
    - intros [Hin0 [x [Hinneg Hinpos]]].
      exists (Zpos (Qden x)). exists (Qnum x).
      split; [lia|].
      unfold in_poly, expand_poly in *. rewrite forallb_map, forallb_forall in *.
      intros c Hinc.
      destruct (Z.compare_spec (nth n (fst c) 0) 0).
      + rewrite assign_0_eq, Z.mul_comm, <- mult_constraint_cst_comp, mult_constraint_cst_eq by (simpl; auto; lia).
        apply Hin0. rewrite filter_In. reflect; auto.
      + rewrite Z.mul_comm, <- mult_constraint_cst_comp, assign_neg_bound, Qle_bool_iff, <- Qmake_Qdiv by (auto; lia).
        apply Hinneg. rewrite in_map_iff; exists c; split; [auto|].
        rewrite filter_In; reflect; auto.
      + rewrite Z.mul_comm, <- mult_constraint_cst_comp, assign_pos_bound, Qle_bool_iff, <- Qmake_Qdiv by (auto; lia).
        apply Hinpos. rewrite in_map_iff; exists c; split; [auto|].
        rewrite filter_In; reflect; auto.
  Qed.

  Lemma merge_constraints_correct :
    forall n c1 c2 p, nth n (fst c1) 0 < 0 -> nth n (fst c2) 0 > 0 ->
                 satisfies_constraint p (merge_constraints n c1 c2) =
                 Qle_bool (bound n c1 p) (bound n c2 p).
  Proof.
    intros n c1 c2 p Hneg Hpos.
    unfold merge_constraints, bound.
    destruct (nth n (fst c1) 0) as [|a|a] eqn:Ha; [lia|lia|].
    destruct (nth n (fst c2) 0) as [|b|b] eqn:Hb; [lia| |lia].
    generalize (Z.ggcd_correct_divisors (Zneg a) (Zpos b)). generalize (Z.ggcd_gcd (Zneg a) (Zpos b)).
    destruct Z.ggcd as [g [aa bb]] eqn:Hggcd. simpl. intros Hg [Hag Hbg].
    unfold satisfies_constraint, Qle_bool, Qdiv, Qmult, Qinv, inject_Z. simpl.
    rewrite add_vector_dot_product_distr_right, !dot_product_mult_right.
    rewrite !dot_product_assign_left, Ha, Hb, eq_iff_eq_true; reflect.
    rewrite Z.mul_le_mono_pos_l with (p := g) by lia. nia.
  Qed.

  Lemma merge_constraints_mult_constraint_cst :
    forall n c1 c2 s, merge_constraints n (mult_constraint_cst s c1) (mult_constraint_cst s c2) =
                 mult_constraint_cst s (merge_constraints n c1 c2).
  Proof.
    intros n c1 c2 s; unfold merge_constraints, mult_constraint_cst, add_constraint, mult_constraint.
    simpl. destruct (Z.ggcd (nth n (fst c1) 0) (nth n (fst c2) 0)) as [g [aa bb]]. simpl.
    f_equal. nia.
  Qed.

  Definition pure_project n p :=
    let zero := filter (fun c => nth n (fst c) 0 =? 0) p in
    let pos := filter (fun c => nth n (fst c) 0 >? 0) p in
    let neg := filter (fun c => nth n (fst c) 0 <? 0) p in
    zero ++ flatten (map (fun nc => map (merge_constraints n nc) pos) neg).

  Definition project np := pure (pure_project (fst np) (snd np)).

  Theorem pure_project_in_iff :
    forall n pol, isExactProjection n pol (pure_project n pol).
  Proof.
    intros n pol p s Hs.
    rewrite is_projected_separate by auto.
    unfold pure_project. rewrite expand_poly_app, in_poly_app, andb_true_iff.
    f_equiv. unfold in_poly, expand_poly.
    rewrite forallb_map, <- flatten_forallb, forallb_map, forallb_forall.
    split.
    - intros H y z Hiny Hinz.
      rewrite in_map_iff in Hiny, Hinz; destruct Hiny as [cy [Hy Hiny]]; destruct Hinz as [cz [Hz Hinz]].
      specialize (H cy Hiny). rewrite forallb_map, forallb_forall in H. specialize (H cz Hinz).
      rewrite filter_In in Hiny, Hinz; reflect.
      rewrite <- Hy, <- Hz, <- Qle_bool_iff, <- merge_constraints_correct by (simpl; lia).
      rewrite merge_constraints_mult_constraint_cst; exact H.
    - intros H cy Hincy. rewrite forallb_map, forallb_forall. intros cz Hincz.
      rewrite <- merge_constraints_mult_constraint_cst, merge_constraints_correct by (rewrite filter_In in *; reflect; simpl; lia).
      rewrite Qle_bool_iff; apply H; rewrite in_map_iff; [exists cy | exists cz]; auto.
  Qed.

  Theorem project_in_iff :
    forall n pol, WHEN proj <- project (n, pol) THEN isExactProjection n pol proj.
  Proof.
    intros n pol proj Hproj.
    unfold project in Hproj. apply mayReturn_pure in Hproj. simpl in Hproj. rewrite <- Hproj.
    apply pure_project_in_iff; auto.
  Qed.

  Theorem merge_constraints_projected :
    forall n c1 c2, nth n (fst (merge_constraints n c1 c2)) 0 = 0.
  Proof.
    intros n c1 c2.
    unfold merge_constraints, add_constraint, mult_constraint.
    generalize (Z.ggcd_correct_divisors (nth n (fst c1) 0) (nth n (fst c2) 0)).
    destruct Z.ggcd as [g [aa bb]]. intros [H1 H2]. simpl.
    rewrite add_vector_nth, !mult_nth. nia.
  Qed.

  Lemma pure_project_constraint_in :
    forall n pol c, In c (pure_project n pol) ->
               ((In c pol /\ nth n (fst c) 0 = 0) \/
                (exists y z, In y pol /\ In z pol /\ nth n (fst y) 0 < 0 /\ 0 < nth n (fst z) 0 /\ c = merge_constraints n y z)).
  Proof.
    intros n pol c Hin. unfold pure_project in Hin.
    rewrite in_app_iff in Hin. destruct Hin as [Hin | Hin].
    - left; rewrite filter_In in Hin. reflect; tauto.
    - right; rewrite flatten_In in Hin. destruct Hin as [u [Hinu Huin]].
      rewrite in_map_iff in Huin; destruct Huin as [nc [Hu Hnc]].
      rewrite <- Hu, in_map_iff in Hinu. destruct Hinu as [pc [Hc Hpc]].
      rewrite <- Hc. exists nc; exists pc.
      rewrite filter_In in *; reflect; tauto.
  Qed.

  Theorem pure_project_projected :
    forall n pol c, In c (pure_project n pol) -> nth n (fst c) 0 = 0.
  Proof.
    intros n pol c Hin. apply pure_project_constraint_in in Hin.
    destruct Hin as [[Hcin Hcn] | [y [z [Hyin [Hzin [Hyn [Hzn Hc]]]]]]].
    - auto.
    - rewrite Hc. apply merge_constraints_projected.
  Qed.

  Theorem project_projected :
    forall n pol, WHEN proj <- project (n, pol) THEN forall c, In c proj -> nth n (fst c) 0 = 0.
  Proof.
    intros n pol proj Hproj c Hinproj.
    unfold project in Hproj; apply mayReturn_pure in Hproj; rewrite <- Hproj in *; simpl in *.
    eapply pure_project_projected; eauto.
  Qed.

  Theorem merge_constraints_no_new_var :
    forall n k c1 c2, nth k (fst c1) 0 = 0 -> nth k (fst c2) 0 = 0 -> nth k (fst (merge_constraints n c1 c2)) 0 = 0.
  Proof.
    intros n k c1 c2 Hc1 Hc2.
    unfold merge_constraints, add_constraint, mult_constraint.
    destruct Z.ggcd as [g [aa bb]]. simpl.
    rewrite add_vector_nth, !mult_nth. nia.
  Qed.

  Theorem pure_project_no_new_var :
    forall n k pol, (forall c, In c pol -> nth k (fst c) 0 = 0) -> (forall c, In c (pure_project n pol) -> nth k (fst c) 0 = 0).
  Proof.
    intros n k pol H c Hin.
    apply pure_project_constraint_in in Hin.
    destruct Hin as [[Hcin Hcn] | [y [z [Hyin [Hzin [Hyn [Hzn Hc]]]]]]].
    - auto.
    - rewrite Hc. apply merge_constraints_no_new_var; auto.
  Qed.

  Theorem project_no_new_var :
    forall n k pol, (forall c, In c pol -> nth k (fst c) 0 = 0) -> WHEN proj <- project (n, pol) THEN (forall c, In c proj -> nth k (fst c) 0 = 0).
  Proof.
    intros n k pol H proj Hproj.
    unfold project in Hproj; apply mayReturn_pure in Hproj; rewrite <- Hproj in *; simpl in *.
    eapply pure_project_no_new_var; eauto.
  Qed.

End FourierMotzkinProject.

(** * Polyhedral projection on the first [n] dimensions *)

Module Type PolyProject (Import Imp: FullImpureMonad).
  Parameter project : nat * polyhedron -> imp polyhedron.

  Parameter project_inclusion :
    forall n p pol, in_poly p pol = true -> WHEN proj <- project (n, pol) THEN in_poly (resize n p) proj = true.

  Parameter project_invariant : nat -> polyhedron -> list Z -> Prop.

  Parameter project_invariant_inclusion :
    forall n pol p, in_poly p pol = true -> project_invariant n pol (resize n p).

  Parameter project_id :
    forall n pol p, (forall c, In c pol -> fst c =v= resize n (fst c)) -> project_invariant n pol p -> in_poly p pol = true.

  Parameter project_next_r_inclusion :
    forall n pol p, project_invariant n pol p ->
               WHEN proj <- project (S n, pol) THEN
               (forall c, In c proj -> nth n (fst c) 0 <> 0 -> satisfies_constraint p c = true) ->
                 project_invariant (S n) pol p.

  Parameter project_invariant_resize :
    forall n pol p, project_invariant n pol p <-> project_invariant n pol (resize n p).

  Parameter project_invariant_export : nat * polyhedron -> imp polyhedron.

  Parameter project_invariant_export_correct :
    forall n p pol, WHEN res <- project_invariant_export (n, pol) THEN in_poly p res = true <-> project_invariant n pol p.

  Parameter project_constraint_size :
    forall n pol c, WHEN proj <- project (n, pol) THEN In c proj -> fst c =v= resize n (fst c).

End PolyProject.


Module PolyProjectImpl (Import Imp: FullImpureMonad) (Canon : PolyCanonizer Imp) (Proj : ProjectOperator Imp) <: PolyProject Imp.

  Ltac bind_imp_destruct H id1 id2 :=
  apply mayReturn_bind in H; destruct H as [id1 [id2 H]].

  Fixpoint do_project d k pol :=
    match k with
    | O => pure pol
    | S k1 =>
      BIND proj <- Proj.project ((d + k1)%nat, pol) -;
      BIND canon <- Canon.canonize proj -;
      do_project d k1 canon
    end.

  Lemma do_project_succ :
    forall k d pol, impeq (do_project d (S k) pol)
                     (BIND proj1 <- do_project (S d) k pol -; BIND proj <- Proj.project (d, proj1) -; Canon.canonize proj).
  Proof.
    induction k.
    - intros; simpl in *. rewrite Nat.add_0_r.
      rewrite impeq_bind_pure_l. f_equiv; intro proj1. rewrite impeq_bind_pure_r. reflexivity.
    - intros d pol; simpl in *.
      rewrite impeq_bind_assoc. rewrite Nat.add_succ_r. f_equiv; intro proj.
      rewrite impeq_bind_assoc. f_equiv; intro canon.
      rewrite IHk. reflexivity.
  Qed.

  Lemma do_project_in_iff :
    forall k s d p pol, 0 < s ->
                   WHEN proj <- do_project d k pol THEN
                        in_poly p (expand_poly s proj) = true <->
                   exists t m, length m = k /\ 0 < t /\
                          in_poly (resize d (mult_vector t p) ++ m ++ skipn (d + k)%nat (mult_vector t p))
                                  (expand_poly (s * t) pol) = true.
  Proof.
    induction k.
    - intros s d p pol Hs proj Hproj; simpl in *.
      apply mayReturn_pure in Hproj; rewrite Hproj.
      split.
      + intros Hin. exists 1. exists nil. simpl.
        split; [auto|split;[lia|]].
        rewrite !mult_vector_1, Nat.add_0_r, resize_skipn_eq, Z.mul_1_r.
        exact Hin.
      + intros [t [m [Hm [Ht Hin]]]].
        destruct m; simpl in *; [|congruence].
        rewrite Nat.add_0_r, resize_skipn_eq, Z.mul_comm, <- expand_poly_comp, expand_poly_eq in Hin by auto.
        exact Hin.
    - intros s d p pol Hs proj Hproj; simpl in *.
      bind_imp_destruct Hproj proja Hproja.
      bind_imp_destruct Hproj canon Hcanon.
      rewrite (IHk s d p canon Hs proj Hproj).
      split; intros [t [m [Hmlen [Ht Hin]]]]; assert (Hst : 0 < s * t) by nia.
      + rewrite (Canon.canonize_correct proja) in Hin by auto.
        rewrite (Proj.project_in_iff _ _ _ Hproja _ _ Hst) in Hin.
        destruct Hin as [r [u [Hr Hin]]].
        exists (t * r). exists (mult_vector r m ++ (u :: nil)).
        split; [rewrite app_length, mult_vector_length, Nat.add_1_r; auto|].
        split; [nia|].
        rewrite <- Hin, Z.mul_assoc. f_equiv.
        rewrite !mult_vector_app, <- !mult_vector_resize, <- !mult_vector_skipn, !mult_vector_comp.
        rewrite assign_app_ge; rewrite resize_length; [|lia].
        rewrite assign_app_ge; rewrite mult_vector_length, Hmlen; [|lia].
        replace (d + k - d - k)%nat with 0%nat by lia.
        rewrite <- app_assoc.
        f_equiv; [f_equal; f_equal; nia|].
        f_equiv. unfold assign. rewrite skipn_skipn. replace (1 + (d + k))%nat with (d + S k)%nat by lia.
        simpl. f_equiv. f_equiv. f_equal. nia.
      + exists t. exists (resize k m). split; [apply resize_length|].
        split; [auto|].
        rewrite (Canon.canonize_correct proja) by auto.
        rewrite (Proj.project_in_iff _ _ _ Hproja _ _ Hst).
        exists 1. exists (nth k m 0).
        split; [lia|].
        rewrite mult_vector_1. rewrite <- Hin.
        f_equiv; [|f_equal; lia].
        rewrite assign_app_ge; rewrite resize_length; [|lia].
        rewrite assign_app_ge; rewrite resize_length; [|lia].
        replace (d + k - d - k)%nat with 0%nat by lia.
        unfold assign.
        rewrite skipn_skipn. replace (1 + (d + k))%nat with (d + S k)%nat by lia.
        replace m with (resize k m ++ (nth k m 0 :: nil)) at 3 by (rewrite <- resize_succ; apply resize_length_eq; auto).
        rewrite <- app_assoc. reflexivity.
  Qed.

  Fixpoint simplify_poly (n : nat) (p : polyhedron) :=
    match n with
    | 0%nat => p
    | S n =>
      let nz := filter (fun c => negb (nth n (fst c) 0 =? 0)) p in
      let z := filter (fun c => nth n (fst c) 0 =? 0) p in
      match find_eq n nz with
      | None => nz ++ simplify_poly n z
      | Some c => c :: mult_constraint (-1) c ::
                   simplify_poly n (map (fun c1 => make_constraint_with_eq n c c1) nz ++ z)
      end
    end.

  Lemma simplify_poly_correct :
    forall n pol p t, 0 < t -> in_poly p (expand_poly t (simplify_poly n pol)) = in_poly p (expand_poly t pol).
  Proof.
    induction n.
    - intros; simpl; reflexivity.
    - intros pol p t Ht. simpl.
      set (nz := filter (fun c => negb (nth n (fst c) 0 =? 0)) pol).
      set (z := filter (fun c => nth n (fst c) 0 =? 0) pol).
      transitivity (in_poly p (expand_poly t nz) && in_poly p (expand_poly t z)).
      + destruct (find_eq n nz) as [c|] eqn:Hfindeq.
        * unfold in_poly in *. simpl. rewrite IHn; auto. rewrite andb_assoc.
          replace (satisfies_constraint p (mult_constraint_cst t c) &&
                   satisfies_constraint p (mult_constraint_cst t (mult_constraint (-1) c))) with
              (dot_product p (fst c) =? t * snd c)
            by (unfold satisfies_constraint, mult_constraint; simpl; rewrite eq_iff_eq_true, dot_product_mult_right; reflect; lia).
          assert (Hcnth : nth n (fst c) 0 <> 0) by (apply find_eq_nth in Hfindeq; lia).
          destruct (dot_product p (fst c) =? t * snd c) eqn:Heq; simpl; reflect.
          -- unfold expand_poly.
             rewrite map_app, forallb_app, map_map, !forallb_map. f_equal. apply forallb_ext.
             intros c1. rewrite make_constraint_with_eq_correct; auto.
          -- destruct (forallb (satisfies_constraint p) (expand_poly t nz)) eqn:Hin; simpl; [|reflexivity]. exfalso; apply Heq.
             unfold expand_poly in Hin. rewrite forallb_map, forallb_forall in Hin.
             eapply find_eq_correct; eauto.
        * rewrite expand_poly_app, in_poly_app. rewrite IHn by auto. reflexivity.
      + rewrite eq_iff_eq_true. reflect. unfold expand_poly, in_poly, nz, z; rewrite !forallb_map, !forallb_forall.
        split.
       * intros [H1 H2] c Hc; specialize (H1 c); specialize (H2 c).
         rewrite filter_In in H1, H2. destruct (nth n (fst c) 0 =? 0); auto.
       * intros H. split; intros c Hcin; rewrite filter_In in Hcin; apply H; tauto.
  Qed.


  Lemma simplify_poly_preserve_zeros :
    forall n m pol, (forall c, In c pol -> nth m (fst c) 0 = 0) -> (forall c, In c (simplify_poly n pol) -> nth m (fst c) 0 = 0).
  Proof.
    induction n.
    - intros; auto.
    - intros m pol H c Hc.
      simpl in Hc.
      set (nz := filter (fun c => negb (nth n (fst c) 0 =? 0)) pol) in *.
      set (z := filter (fun c => nth n (fst c) 0 =? 0) pol) in *.
      destruct (find_eq n nz) as [c1|] eqn:Hfindeq.
      + simpl in Hc.
        assert (Hc1 : nth m (fst c1) 0 = 0) by (apply find_eq_in in Hfindeq; apply H; unfold nz in Hfindeq; rewrite filter_In in Hfindeq; tauto).
        destruct Hc as [Hc | [Hc | Hc]];
          [rewrite <- Hc; auto | rewrite <- Hc; unfold mult_constraint; simpl; rewrite mult_nth; lia|].
        eapply IHn; [|apply Hc].
        intros c2 Hin2; rewrite in_app_iff, in_map_iff in Hin2.
        destruct Hin2 as [[c3 [Heq2 Hin3]] | Hin2]; [|apply H; unfold z in Hin2; rewrite filter_In in Hin2; tauto].
        rewrite <- Heq2, make_constraint_with_eq_preserve_zeros; auto. apply H.
        unfold nz in Hin3; rewrite filter_In in Hin3; tauto.
      + rewrite in_app_iff in Hc.
        destruct Hc as [Hc | Hc]; [apply H; unfold nz in Hc; rewrite filter_In in Hc; tauto|].
        eapply IHn; [|apply Hc]. intros c1 Hc1; apply H; unfold z in Hc1; rewrite filter_In in Hc1; tauto.
  Qed.

  Definition project (np : nat * polyhedron) : imp polyhedron :=
    let (n, p) := np in
    let k := poly_nrl p in
    BIND r <- do_project n (k - n)%nat p -; pure (simplify_poly n r).

  Lemma project_in_iff :
    forall s n p pol, 0 < s -> WHEN proj <- project (n, pol) THEN
                              in_poly p (expand_poly s proj) = true <->
                         exists t m, 0 < t /\ in_poly (resize n (mult_vector t p) ++ m) (expand_poly (s * t) pol) = true.
  Proof.
    intros s n p pol Hs proj Hproj.
    unfold project in Hproj.
    bind_imp_destruct Hproj r Hr; apply mayReturn_pure in Hproj; rewrite <- Hproj in *.
    rewrite simplify_poly_correct by auto.
    remember (poly_nrl pol) as u.
    rewrite (do_project_in_iff _ _ _ _ _ Hs _ Hr).
    split.
    - intros [t [m [Hmlen [Ht Hin]]]]; exists t. exists m. split; [auto|].
      rewrite <- in_poly_nrlength with (n := u) in Hin by (rewrite expand_poly_nrl; nia).
      rewrite <- in_poly_nrlength with (n := u) by (rewrite expand_poly_nrl; nia).
      rewrite app_assoc in Hin. rewrite resize_app_ge in Hin; [exact Hin|].
      rewrite app_length, resize_length, Hmlen. lia.
    - intros [t [m [Ht Hin]]]; exists t. exists (resize (u - n)%nat m).
      split; [apply resize_length|]. split; [auto|].
      rewrite <- in_poly_nrlength with (n := u) in Hin by (rewrite expand_poly_nrl; nia).
      rewrite <- in_poly_nrlength with (n := u) by (rewrite expand_poly_nrl; nia).
      rewrite app_assoc, resize_app_ge by (rewrite app_length, !resize_length; lia).
      destruct (u <=? n)%nat eqn:Hun; reflect.
      + rewrite resize_app_ge in * by (rewrite resize_length; lia). exact Hin.
      + rewrite resize_app_le in * by (rewrite resize_length; lia). rewrite !resize_length in *.
        rewrite resize_resize; [exact Hin|lia].
  Qed.

  Lemma project_in_iff1 :
    forall n p pol, WHEN proj <- project (n, pol) THEN
                    in_poly p proj = true <->
               exists t m, 0 < t /\ in_poly (resize n (mult_vector t p) ++ m) (expand_poly t pol) = true.
  Proof.
    intros n p pol proj Hproj.
    rewrite <- expand_poly_1 with (p := proj).
    assert (H01 : 0 < 1) by lia.
    rewrite (project_in_iff _ _ _ _ H01 _ Hproj). apply exists_ext. intros t.
    destruct t; reflexivity.
  Qed.

  Theorem project_inclusion :
    forall n p pol, in_poly p pol = true -> WHEN proj <- project (n, pol) THEN in_poly (resize n p) proj = true.
  Proof.
    intros n p pol Hp proj Hproj.
    rewrite (project_in_iff1 _ _ _ _ Hproj). exists 1. exists (skipn n p).
    split; [lia|].
    rewrite mult_vector_1, resize_resize, resize_skipn_eq, expand_poly_1 by lia.
    auto.
  Qed.

  Definition project_invariant n p v :=
    exists t m, 0 < t /\ in_poly (resize n (mult_vector t v) ++ m) (expand_poly t p) = true.

  Theorem project_invariant_inclusion :
    forall n pol p, in_poly p pol = true -> project_invariant n pol (resize n p).
  Proof.
    intros n pol p H.
    exists 1. exists (skipn n p).
    split; [lia|].
    rewrite mult_vector_1, resize_resize, resize_skipn_eq, expand_poly_1 by lia.
    auto.
  Qed.

  Theorem project_id :
    forall n pol p, (forall c, In c pol -> fst c =v= resize n (fst c)) -> project_invariant n pol p -> in_poly p pol = true.
  Proof.
    intros n pol p Hclen Hinv. rewrite poly_nrl_def in Hclen.
    destruct Hinv as [t [m [Ht Hinv]]].
    rewrite <- in_poly_nrlength with (n := n) in Hinv by (rewrite expand_poly_nrl; auto; lia).
    rewrite resize_app in Hinv by (apply resize_length).
    rewrite in_poly_nrlength in Hinv by (rewrite expand_poly_nrl; auto; lia).
    rewrite expand_poly_eq in Hinv; auto.
  Qed.

  Theorem project_invariant_resize :
    forall n pol p, project_invariant n pol p <-> project_invariant n pol (resize n p).
  Proof.
    intros n pol p. unfold project_invariant.
    apply exists_ext. intros t.
    rewrite <- mult_vector_resize. rewrite resize_resize by lia.
    reflexivity.
  Qed.

  Lemma do_project_no_new_var :
    forall k d pol n, (forall c, In c pol -> nth n (fst c) 0 = 0) -> WHEN proj <- do_project d k pol THEN (forall c, In c proj -> nth n (fst c) 0 = 0).
  Proof.
    induction k.
    - intros; simpl in *. xasimplify eauto.
    - intros; simpl in *. xasimplify eauto.
      generalize (Proj.project_no_new_var _ _ _ H _ Hexta). intros H1.
      generalize (Canon.canonize_no_new_var _ _ H1 _ Hexta0). intros H2.
      apply (IHk _ _ _ H2 _ Hexta1).
  Qed.

  Lemma do_project_constraints :
    forall k d pol n, (d <= n < d + k)%nat -> WHEN proj <- do_project d k pol THEN (forall c, In c proj -> nth n (fst c) 0 = 0).
  Proof.
    induction k.
    - intros; lia.
    - intros d pol n Hn proj Hproj.
      simpl in Hproj.
      bind_imp_destruct Hproj proja Hproja.
      bind_imp_destruct Hproj canon Hcanon.
      destruct (n =? d + k)%nat eqn:Heqn; reflect.
      + rewrite Heqn. generalize (Proj.project_projected _ _ _ Hproja). intros H1.
        generalize (Canon.canonize_no_new_var _ _ H1 _ Hcanon). intros H2.
        apply (do_project_no_new_var _ _ _ _ H2 _ Hproj).
      + assert (H : (d <= n < d + k)%nat) by lia.
        apply (IHk _ _ _ H _ Hproj).
  Qed.

  Theorem project_constraint_size :
    forall n pol c, WHEN proj <- project (n, pol) THEN In c proj -> fst c =v= resize n (fst c).
  Proof.
    intros n pol c proj Hproj Hin.
    apply vector_nth_veq.
    unfold project in Hproj.
    bind_imp_destruct Hproj r Hr; apply mayReturn_pure in Hproj; rewrite <- Hproj in *.
    intros k.
    rewrite nth_resize.
    destruct (k <? n)%nat eqn:Hkn; reflect; [reflexivity|].
    assert (Hcr : forall c1, In c1 r -> nth k (fst c1) 0 = 0).
    - intros c1 Hin1.
      destruct (k <? n + (poly_nrl pol - n))%nat eqn:Hkrl; reflect.
      + apply (do_project_constraints _ _ _ _ (conj Hkn Hkrl) _ Hr); auto.
      +  assert (Hnrl : (poly_nrl pol <= k)%nat) by lia.
         rewrite <- poly_nrl_def in Hnrl.
         assert (H : forall c, In c pol -> nth k (fst c) 0 = 0).
         * intros c2 Hin2; specialize (Hnrl c2 Hin2).
           apply nth_eq with (n := k) in Hnrl. rewrite nth_resize in Hnrl. destruct (k <? k)%nat eqn:Hkk; reflect; lia.
         * apply (do_project_no_new_var _ _ _ _  H _ Hr _ Hin1).
    - eapply simplify_poly_preserve_zeros; eauto.
  Qed.

  Theorem project_next_r_inclusion :
    forall n pol p, project_invariant n pol p ->
               WHEN proj <- project (S n, pol) THEN
               (forall c, In c proj -> nth n (fst c) 0 <> 0 -> satisfies_constraint p c = true) ->
               project_invariant (S n) pol p.
  Proof.
    intros n pol p Hinv proj Hproj Hsat.
    destruct Hinv as [t [m [Ht Hinv]]].
    apply (project_in_iff1 _ _ _ _ Hproj).
    unfold in_poly. rewrite forallb_forall. intros c Hinproj.
    destruct (nth n (fst c) 0 =? 0) eqn:Hzero; reflect; [|apply Hsat; auto].
    unfold project_invariant in Hinv.
    rewrite <- resize_skipn_eq with (d := 1%nat) (l := m) in Hinv.
    rewrite app_assoc in Hinv.
    assert (H : in_poly (resize n (mult_vector t p) ++ resize 1 m) (expand_poly t proj) = true).
    - rewrite (project_in_iff _ _ _ _ Ht _ Hproj). exists 1. exists (skipn 1%nat m).
      split; [lia|]. rewrite mult_vector_1. rewrite resize_length_eq by (rewrite app_length, !resize_length; lia).
      rewrite Z.mul_1_r; apply Hinv.
    - unfold in_poly in H. rewrite forallb_forall in H.
      rewrite <- mult_constraint_cst_eq with (k := t) by auto.
      specialize (H (mult_constraint_cst t c)).
      generalize (project_constraint_size _ _ _ _ Hproj Hinproj); intros Hsize.
      rewrite resize_succ, Hzero in Hsize.
      setoid_replace (0 :: nil) with (@nil Z) using relation veq in Hsize by (rewrite <- is_eq_veq; reflexivity).
      rewrite app_nil_r in Hsize. symmetry in Hsize; rewrite nrlength_def in Hsize.
      replace (fst c) with (fst (mult_constraint_cst t c)) in Hsize by reflexivity.
      rewrite <- satisfies_constraint_nrlength with (n := n) in H by auto.
      rewrite <- satisfies_constraint_nrlength with (n := n) by auto.
      rewrite resize_app in H by (apply resize_length). apply H.
      unfold expand_poly. apply in_map. auto.
  Qed.

  Definition project_invariant_export (np : nat * polyhedron) : imp polyhedron :=
    project np.

  Theorem project_invariant_export_correct :
    forall n p pol, WHEN res <- project_invariant_export (n, pol) THEN in_poly p res = true <-> project_invariant n pol p.
  Proof.
    intros n p pol proj Hproj.
    apply (project_in_iff1 _ _ _ _ Hproj).
  Qed.

End PolyProjectImpl.

Require Import ImpureAlarmConfig.
Module Proj := FourierMotzkinProject CoreAlarmed.
Module Export PPI := PolyProjectImpl CoreAlarmed Canon Proj.

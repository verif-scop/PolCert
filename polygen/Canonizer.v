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
Require Import Psatz.

Require Import Misc.
Require Import Linalg.
Require Import VplInterface.

Require Import Vpl.Impure.

Open Scope Z_scope.

Module Type PolyCanonizer (Import Imp: FullImpureMonad).

  Parameter canonize : polyhedron -> imp polyhedron.

  Parameter canonize_correct :
    forall p, WHEN r <- canonize p THEN (forall k v, 0 < k -> in_poly v (expand_poly k r) = in_poly v (expand_poly k p)).

  Parameter canonize_no_new_var :
    forall k p, absent_var p k -> WHEN r <- canonize p THEN absent_var r k.

End PolyCanonizer.

Module NaiveCanonizer(Import Imp: FullImpureMonad) <: PolyCanonizer Imp.

  Definition canonize (p : polyhedron) := pure p.

  Theorem canonize_correct :
    forall p, WHEN r <- canonize p THEN (forall k v, 0 < k -> in_poly v (expand_poly k r) = in_poly v (expand_poly k p)).
  Proof.
    intros p r Hcanon k v Hk. unfold canonize in Hcanon.
    apply mayReturn_pure in Hcanon. rewrite Hcanon. reflexivity.
  Qed.

  Theorem canonize_no_new_var :
    forall k p, absent_var p k -> WHEN r <- canonize p THEN absent_var r k.
  Proof.
    intros k p H r Hcanon. unfold canonize in Hcanon.
    apply mayReturn_pure in Hcanon. rewrite Hcanon in H. exact H.
  Qed.

End NaiveCanonizer.

Require Import ImpureAlarmConfig.

Module VplCanonizer <: PolyCanonizer CoreAlarmed.

  Definition check_not_new n (l1 l2 : polyhedron) :=
    (negb (forallb (fun c => nth n (fst c) 0 =? 0) l1)) || (forallb (fun c => nth n (fst c) 0 =? 0) l2).

  Lemma check_not_new_correct :
    forall n l1 l2, check_not_new n l1 l2 = true -> absent_var l1 n -> absent_var l2 n.
  Proof.
    intros n l1 l2 H1 H2 c Hc.
    unfold check_not_new in H1. reflect. destruct H1 as [H1 | H1].
    - exfalso. eapply eq_true_false_abs; [|exact H1].
      rewrite forallb_forall. intros c1; specialize (H2 c1). reflect; auto.
    - rewrite forallb_forall in H1. specialize (H1 c). reflect; auto.
  Qed.

  Definition check_no_new_vars l1 l2 :=
    let n := poly_nrl l2 in
    forallb (fun n => check_not_new n l1 l2) (n_range n).

  Lemma check_no_new_vars_correct :
    forall n l1 l2, check_no_new_vars l1 l2 = true -> absent_var l1 n -> absent_var l2 n.
  Proof.
    intros n l1 l2 H.
    destruct (n <? poly_nrl l2)%nat eqn:Hn; reflect.
    - apply check_not_new_correct.
      unfold check_no_new_vars in H. rewrite forallb_forall in H.
      apply H. rewrite n_range_in. auto.
    - intros H1 c Hc. rewrite <- poly_nrl_def in Hn. specialize (Hn c Hc).
      eapply nth_eq in Hn; rewrite Hn. rewrite nth_resize.
      destruct (n <? n)%nat eqn:Hn2; reflect; auto; lia.
  Qed.

  Definition canonize l :=
    BIND r <- lift (canonize_Cs (poly_to_Cs l)) -;
    pure match Cs_to_poly_Q r with
    | None => l
    | Some l2 =>
        if check_no_new_vars l l2 then l2 else l
  end.

  Lemma canonize_correct :
    forall p, WHEN r <- canonize p THEN (forall k v, 0 < k -> in_poly v (expand_poly k r) = in_poly v (expand_poly k p)).
  Proof.
    intros l l2 Hl2 k v Hk.
    unfold canonize in Hl2. bind_imp_destruct Hl2 r Hr.
    apply mayReturn_lift in Hr. apply mayReturn_pure in Hl2.
    destruct (Cs_to_poly_Q r) as [u|] eqn:Hu; [|congruence].
    destruct (check_no_new_vars l u); [|congruence].
    apply eq_iff_eq_true.
    rewrite <- poly_to_Cs_correct_Q with (p := l) by auto.
    rewrite (canonize_Cs_correct _ _ Hr _).
    rewrite (Cs_to_poly_Q_correct _ _ _ _ Hk Hu).
    rewrite Hl2. reflexivity.
  Qed.

  Lemma canonize_no_new_var :
    forall k p, absent_var p k -> WHEN r <- canonize p THEN absent_var r k.
  Proof.
    intros k l H l2 Hl2.
    unfold canonize in Hl2. bind_imp_destruct Hl2 r Hr. apply mayReturn_pure in Hl2.
    destruct (Cs_to_poly_Q r) as [u|]; [|rewrite <- Hl2; auto].
    destruct (check_no_new_vars l u) eqn:Hchk; [|rewrite <- Hl2; auto].
    rewrite <- Hl2. eapply check_no_new_vars_correct; eauto.
  Qed.

End VplCanonizer.

Module VplCanonizerZ.

  Definition canonize_constraint_Z (c : list Z * Z) :=
    let g := list_gcd (fst c) in
    if (g =? 0) then c
    else (map (fun x => x / g) (fst c), (snd c / g)).

  Lemma canonize_constraint_Z_correct :
    forall c p, satisfies_constraint p (canonize_constraint_Z c) = satisfies_constraint p c.
  Proof.
    intros c p. unfold canonize_constraint_Z.
    remember (list_gcd (fst c)) as g. destruct (g =? 0) eqn:Hg; auto.
    reflect. unfold satisfies_constraint; rewrite eq_iff_eq_true; reflect.
    assert (Hpos : 0 < g) by (generalize (list_gcd_nonneg (fst c)); lia).
    simpl.
    rewrite div_ge_iff by auto. f_equiv.
    rewrite <- Z.mul_comm, <- dot_product_mult_right. f_equal.
    unfold mult_vector. rewrite map_map.
    erewrite map_ext_in; [apply map_id|]. intros x Hx. simpl.
    symmetry; apply Znumtheory.Zdivide_Zdiv_eq; [auto|].
    rewrite Heqg; apply list_gcd_div. auto.
  Qed.

  Lemma canonize_constraint_Z_no_new_var :
    forall k c, nth k (fst c) 0 = 0 -> nth k (fst (canonize_constraint_Z c)) 0 = 0.
  Proof.
    intros k c H. unfold canonize_constraint_Z.
    destruct (list_gcd (fst c) =? 0); auto. simpl.
    transitivity (nth k (fst c) 0 / (list_gcd (fst c))).
    - rewrite <- map_nth with (f := fun x => x / list_gcd (fst c)). auto.
    - rewrite H. auto.
  Qed.

  Definition canonize l :=
    BIND r <- VplCanonizer.canonize (map canonize_constraint_Z l) -;
    pure (map canonize_constraint_Z r).

  Lemma canonize_correct :
    forall p, WHEN r <- canonize p THEN (forall v, in_poly v r = in_poly v p).
  Proof.
    intros l l2 Hl2 v.
    unfold canonize in Hl2. bind_imp_destruct Hl2 r Hr.
    apply mayReturn_pure in Hl2. apply VplCanonizer.canonize_correct in Hr.
    specialize (Hr 1 v). rewrite !expand_poly_1 in Hr.
    rewrite <- Hl2. unfold in_poly in *. rewrite forallb_map in *.
    erewrite forallb_ext; [|intros; rewrite canonize_constraint_Z_correct; reflexivity].
    rewrite Hr by lia.
    apply forallb_ext. intros; apply canonize_constraint_Z_correct.
  Qed.

  Lemma canonize_no_new_var :
    forall k p, absent_var p k -> WHEN r <- canonize p THEN absent_var r k.
  Proof.
    intros k l H l2 Hl2.
    unfold canonize in Hl2. bind_imp_destruct Hl2 r Hr. apply mayReturn_pure in Hl2.
    apply VplCanonizer.canonize_no_new_var with (k := k) in Hr.
    - intros c Hc. rewrite <- Hl2 in Hc. rewrite in_map_iff in Hc.
      destruct Hc as [c1 [Hc1 Hin1]]; rewrite <- Hc1; apply canonize_constraint_Z_no_new_var; auto.
    - intros c Hc; rewrite in_map_iff in Hc.
      destruct Hc as [c1 [Hc1 Hin1]]; rewrite <- Hc1; apply canonize_constraint_Z_no_new_var; auto.
  Qed.

End VplCanonizerZ.

Module Canon := VplCanonizer.
Module CanonZ := VplCanonizerZ.

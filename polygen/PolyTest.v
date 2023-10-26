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
Require Import Psatz.

Require Import Misc.
Require Import Linalg.
Require Import VplInterface.
Require Import Projection.
Require Import ImpureAlarmConfig.

Open Scope Z_scope.

Definition isBottom pol :=
  BIND p <- lift (ExactCs.fromCs_unchecked (poly_to_Cs pol)) -; lift (CstrDomain.isBottom p).

Lemma isBottom_correct :
  forall pol t, 0 < t -> If isBottom pol THEN forall p, in_poly p (expand_poly t pol) = false.
Proof.
  intros pol t Ht b Hbot.
  destruct b; simpl; [|auto]. intros p.
  unfold isBottom in Hbot.
  apply mayReturn_bind in Hbot; destruct Hbot as [p1 [Hp1 Hbot]].
  apply mayReturn_lift in Hp1; apply mayReturn_lift in Hbot.
  apply CstrDomain.isBottom_correct in Hbot; simpl in Hbot.
  apply ExactCs.fromCs_unchecked_correct in Hp1.
  apply not_true_is_false; intros Hin.
  rewrite <- poly_to_Cs_correct_Q in Hin by auto.
  eauto.
Qed.

Lemma isBottom_correct_1 :
  forall pol, If isBottom pol THEN forall p, in_poly p pol = false.
Proof.
  intros pol. generalize (isBottom_correct pol 1).
  rewrite expand_poly_1. intros H; apply H; lia.
Qed.

Definition isIncl pol1 pol2 :=
  BIND p1 <- lift (ExactCs.fromCs_unchecked (poly_to_Cs pol1)) -;
  BIND p2 <- lift (ExactCs.fromCs (poly_to_Cs pol2)) -;
  match p2 with Some p2 => lift (CstrDomain.isIncl p1 p2) | None => pure false end.

Lemma isIncl_correct :
  forall pol1 pol2 t, 0 < t -> If isIncl pol1 pol2 THEN forall p, in_poly p (expand_poly t pol1) = true -> in_poly p (expand_poly t pol2) = true.
Proof.
  intros pol1 pol2 t Ht b Hincl.
  destruct b; simpl; [|auto]. intros p Hin.
  unfold isIncl in Hincl.
  bind_imp_destruct Hincl p1 Hp1; bind_imp_destruct Hincl p2 Hp2.
  destruct p2 as [p2|]; [|apply mayReturn_pure in Hincl; congruence].
  apply mayReturn_lift in Hp1; apply mayReturn_lift in Hp2; apply mayReturn_lift in Hincl.
  apply CstrDomain.isIncl_correct in Hincl; simpl in Hincl.
  apply ExactCs.fromCs_unchecked_correct in Hp1.
  eapply ExactCs.fromCs_correct in Hp2.
  rewrite <- poly_to_Cs_correct_Q in Hin by auto.
  apply Hp1, Hincl in Hin. rewrite Hp2 in Hin.
  rewrite poly_to_Cs_correct_Q in Hin by auto.
  auto.
Qed.

Lemma isIncl_correct_1 :
  forall pol1 pol2, If isIncl pol1 pol2 THEN forall p, in_poly p pol1 = true -> in_poly p pol2 = true.
Proof.
  intros pol1 pol2. generalize (isIncl_correct pol1 pol2 1).
  rewrite !expand_poly_1. intros H; apply H; lia.
Qed.


Definition canPrecede n pol1 pol2 :=
  forall p1 x, in_poly p1 pol1 = true -> 
    in_poly (assign n x p1) pol2 = true -> nth n p1 0 < x.

Definition check_canPrecede n (pol1 pol2 proj1 : polyhedron) :=
  let g1 := filter (fun c => 0 <? nth n (fst c) 0) pol1 in
  isBottom (pol2 ++ proj1 ++ g1).

Lemma check_canPrecede_correct :
  forall n pol1 pol2 proj1,
    isExactProjection n pol1 proj1 ->
    If check_canPrecede n pol1 pol2 proj1 THEN canPrecede n pol1 pol2.
Proof.
  intros n pol1 pol2 proj1 Hproj1 b Hprec.
  destruct b; simpl; [|auto].
  intros p1 x Hp1 Hpx.
  unfold check_canPrecede in Hprec. apply isBottom_correct_1 in Hprec; simpl in Hprec.
  specialize (Hprec (assign n x p1)). rewrite !in_poly_app in Hprec. reflect.
  rewrite Hpx in Hprec.
  apply isExactProjection_weaken1 in Hproj1. eapply isExactProjection_assign_1 in Hproj1; [|exact Hp1].
  rewrite Hproj1 in Hprec.
  destruct Hprec as [? | [? | Hprec]]; try congruence.
  assert (Hin : in_poly p1 (filter (fun c => 0 <? nth n (fst c) 0) pol1) = true).
  - unfold in_poly in *; rewrite forallb_forall in *.
    intros c. rewrite filter_In. intros; apply Hp1; tauto.
  - rewrite <- Z.nle_gt. intros Hle.
    eapply eq_true_false_abs; [|exact Hprec].
    unfold in_poly in *; rewrite forallb_forall in *.
    intros c. rewrite filter_In. intros Hc.
    specialize (Hin c). rewrite filter_In in Hin. specialize (Hin Hc).
    destruct Hc as [Hcin Hc].
    unfold satisfies_constraint in *. reflect. rewrite dot_product_assign_left.
    nia.
Qed.

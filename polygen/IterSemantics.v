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

Require Import List.

Require Import Vpl.Impure.
Require Import Mymap.
Require Import ImpureOperations.

Require Import Misc.
Require Import StateTy.

Module IterSem (State: STATE).

(** * Iterating semantics on a list *)

Inductive iter_semantics {A : Type} (P : A -> State.t -> State.t -> Prop) : list A -> State.t -> State.t -> Prop :=
| IDone : forall st, iter_semantics P nil st st
| IProgress : forall x l st1 st2 st3,
    P x st1 st2 -> iter_semantics P l st2 st3 ->
    iter_semantics P (x :: l) st1 st3.

Lemma iter_semantics_map {A : Type} (P Q : A -> State.t -> State.t -> Prop) :
  forall l st1 st2,
    (forall x st1 st2, In x l -> P x st1 st2 -> Q x st1 st2) ->
    iter_semantics P l st1 st2 ->
    iter_semantics Q l st1 st2.
Proof.
  intros l st1 st2 Himp Hsem.
  induction Hsem; econstructor; eauto; [eapply Himp|eapply IHHsem]; eauto.
  - simpl; auto.
  - intros; apply Himp; simpl; auto.
Qed.

Lemma iter_semantics_mapl :
  forall (A B : Type) P (f : A -> B) (l : list A) st1 st2,
    iter_semantics P (map f l) st1 st2 <-> iter_semantics (fun x => P (f x)) l st1 st2.
Proof.
  intros A B P f. induction l.
  - intros; split; simpl; intros H; inversion_clear H; constructor.
  - intros; split; simpl; intros H; inversion_clear H; econstructor; eauto; rewrite IHl in *; auto.
Qed.

Lemma iter_semantics_combine :
  forall (A B : Type) P (xs : list A) (ys : list B) st1 st2,
    length xs = length ys -> iter_semantics P xs st1 st2 <-> iter_semantics (fun p => P (fst p)) (combine xs ys) st1 st2.
Proof.
  intros A B P xs ys st1 st2 H.
  replace xs with (map fst (combine xs ys)) at 1 by (apply map_combine; auto).
  rewrite iter_semantics_mapl; reflexivity.
Qed.


Module IterImpureSemantics (Import Imp: FullImpureMonad).

  (* Module IterSemantics := IterSem State. *)
  Module ImpOps := ImpureOps Imp.
  Import ImpOps.

  Lemma iter_semantics_sequence :
    forall (A : Type) P (xs : list (imp A)) (ys : list A) st1 st2,
      mayReturn (sequence xs) ys ->
      iter_semantics (fun x st3 st4 => WHEN y <- x THEN P y st3 st4) xs st1 st2 
      -> iter_semantics P ys st1 st2.
  Proof.
    intros A P. induction xs.
    - intros ys st1 st2 Hys Hsem; simpl in *. apply mayReturn_pure in Hys; rewrite <- Hys.
      inversion_clear Hsem; constructor.
    - intros ys st1 st2 Hys Hsem; simpl in *.
      bind_imp_destruct Hys y Hy.
      bind_imp_destruct Hys ys1 Hys1.
      apply mayReturn_pure in Hys; rewrite <- Hys in *.
      inversion_clear Hsem. 
      econstructor; [apply H; auto|].
      apply IHxs; auto.
  Qed.

  (* yet another unfortunately needed lemma because of mymap... *)
  Lemma iter_semantics_mymapl :
    forall (A B : Type) P (f : A -> B) (l : list A) st1 st2,
    iter_semantics P (mymap f l) st1 st2 <-> iter_semantics (fun x => P (f x)) l st1 st2.
  Proof.
    intros A B P f. induction l.
    - intros; split; simpl; intros H; inversion_clear H; constructor.
    - intros; split; simpl; intros H; inversion_clear H; econstructor; eauto; rewrite IHl in *; auto.
  Qed.

  Lemma iter_semantics_mapM :
    forall (A B : Type) f P (xs : list A) (ys : list B) st1 st2,
      mayReturn (mapM f xs) ys ->
      iter_semantics (fun x st3 st4 => WHEN y <- f x THEN P y st3 st4) xs st1 st2 -> iter_semantics P ys st1 st2.
  Proof.
    intros A B f P xs ys st1 st2 Hmap Hsem.
    eapply iter_semantics_sequence; [exact Hmap|].
    rewrite iter_semantics_mymapl. auto.
  Qed.

  Lemma iter_semantics_mapM_rev :
    forall (A B : Type) P f (xs : list A) (ys : list B) st1 st2,
      mayReturn (mapM f xs) ys ->
      iter_semantics P ys st1 st2 ->
      iter_semantics (fun '(x, y) st3 st4 => mayReturn (f x) y /\ P y st3 st4) (combine xs ys) st1 st2.
  Proof.
    intros A B P f. induction xs.
    - intros ys st1 st2 Hys Hsem; simpl in *. apply mayReturn_pure in Hys; rewrite <- Hys in Hsem.
      inversion_clear Hsem; constructor.
    - intros ys st1 st2 Hys Hsem; simpl in *.
      bind_imp_destruct Hys y Hy.
      bind_imp_destruct Hys ys1 Hys1.
      apply mayReturn_pure in Hys; rewrite <- Hys in *.
      inversion_clear Hsem.
      econstructor; [eauto|].
      apply IHxs; auto.
  Qed.

End IterImpureSemantics.

End IterSem.

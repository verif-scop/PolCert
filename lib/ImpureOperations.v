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

Require Import Mymap.
Require Import Misc.

Require Import Vpl.Impure.

Module ImpureOps (Import Imp: FullImpureMonad).

  Ltac bind_imp_destruct H id1 id2 :=
    apply mayReturn_bind in H; destruct H as [id1 [id2 H]].

  (** * Sequencing a number of monadic operations *)

  Fixpoint sequence {A : Type} (l : list (imp A)) : imp (list A) :=
    match l with
    | nil => pure nil
    | x :: l => BIND y <- x -; BIND l1 <- sequence l -; pure (y :: l1)
    end.

  Lemma sequence_mayReturn :
    forall (A : Type) (xs : list (imp A)) (ys : list A),
      mayReturn (sequence xs) ys -> Forall2 mayReturn xs ys.
  Proof.
    intros A. induction xs.
    - intros ys Hys; simpl in *. apply mayReturn_pure in Hys; rewrite <- Hys.
      constructor.
    - intros ys Hys; simpl in *.
      bind_imp_destruct Hys y Hy.
      bind_imp_destruct Hys ys1 Hys1.
      apply mayReturn_pure in Hys; rewrite <- Hys in *.
      constructor; auto.
  Qed.

  Lemma sequence_length :
    forall (A : Type) (xs : list (imp A)) (ys : list A), mayReturn (sequence xs) ys -> length xs = length ys.
  Proof.
    intros A xs ys H; apply sequence_mayReturn, Forall2_length in H. auto.
  Qed.

  (** * Mapping a pure function on a monadic value *)

  Definition fmap {A B : Type} (f : A -> B) (x : imp A) : imp B :=
    BIND y <- x -; pure (f y).

  (** * Mapping a monadic function on a list of values *)

  (* The use of mymap is due to a bug in Coq; see comment in Mymap.v *)
  Definition mapM {A B : Type} (f : A -> imp B) (l : list A) : imp (list B) := sequence (mymap f l).

  Lemma mapM_mayReturn :
    forall (A B : Type) (f : A -> imp B) (xs : list A) (ys : list B),
      mayReturn (mapM f xs) ys -> Forall2 (fun x y => mayReturn (f x) y) xs ys.
  Proof.
    intros A B f xs ys H.
    apply sequence_mayReturn in H. rewrite Forall2_mymap_left in H.
    exact H.
  Qed.

  Lemma mapM_length :
    forall (A B : Type) (f : A -> imp B) xs ys, mayReturn (mapM f xs) ys -> length xs = length ys.
  Proof.
    intros A B f xs ys H; apply sequence_length in H; rewrite mymap_length in H; auto.
  Qed.

  Lemma mapM_in_iff :
    forall (A B : Type) (f : A -> imp B) (xs : list A) (y : B),
      WHEN ys <- mapM f xs THEN In y ys -> exists x, mayReturn (f x) y /\ In x xs.
  Proof.
    intros A B f. unfold mapM. induction xs.
    - intros y ys Hys Hin. simpl in *. apply mayReturn_pure in Hys.
      rewrite <- Hys in Hin. simpl in *; tauto.
    - intros y ys Hys Hin. simpl in *.
      bind_imp_destruct Hys y1 Hy1; bind_imp_destruct Hys ys1 Hys1.
      apply mayReturn_pure in Hys; rewrite <- Hys in Hin.
      simpl in *.
      destruct Hin as [Hin | Hin].
      + exists a; intuition congruence.
      + specialize (IHxs y ys1 Hys1 Hin). firstorder.
  Qed.

  Lemma mapM_nth_error1 :
    forall (A B : Type) (f : A -> imp B) (k : nat) (xs : list A) (y : B),
      WHEN ys <- mapM f xs THEN nth_error ys k = Some y -> exists x, mayReturn (f x) y /\ nth_error xs k = Some x.
  Proof.
    intros A B f k. unfold mapM. induction k.
    - intros xs y [|y1 ys] Hys Hnth; simpl in *; [congruence|].
      destruct xs as [|x xs]; simpl in *; [apply mayReturn_pure in Hys; congruence|].
      bind_imp_destruct Hys y2 Hy2; bind_imp_destruct Hys ys2 Hys2.
      apply mayReturn_pure in Hys.
      exists x; split; congruence.
    - intros xs y [|y1 ys] Hys Hnth; simpl in *; [congruence|].
      destruct xs as [|x xs]; simpl in *; [apply mayReturn_pure in Hys; congruence|].
      bind_imp_destruct Hys y2 Hy2; bind_imp_destruct Hys ys2 Hys2.
      apply mayReturn_pure in Hys.
      replace ys2 with ys in * by congruence.
      apply (IHk _ _ _ Hys2 Hnth).
  Qed.

  Lemma mapM_nth_error2 :
    forall (A B : Type) (f : A -> imp B) (k : nat) (xs : list A) (x : A),
      nth_error xs k = Some x -> WHEN ys <- mapM f xs THEN exists y, mayReturn (f x) y /\ nth_error ys k = Some y.
  Proof.
    intros A B f k. unfold mapM. induction k.
    - intros [|x xs] x1 Hnth ys Hys; simpl in *; [congruence|].
      bind_imp_destruct Hys y1 Hy1; bind_imp_destruct Hys ys1 Hys1.
      apply mayReturn_pure in Hys; rewrite <- Hys in *.
      exists y1; split; congruence.
    - intros [|x xs] x1 Hnth ys Hys; simpl in *; [congruence|].
      bind_imp_destruct Hys y1 Hy1; bind_imp_destruct Hys ys1 Hys1.
      apply mayReturn_pure in Hys; rewrite <- Hys in *.
      apply (IHk _ _ Hnth _ Hys1).
  Qed.

End ImpureOps.
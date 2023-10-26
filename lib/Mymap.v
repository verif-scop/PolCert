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

(** This entire file is due to a bug in Coq: see https://github.com/coq/coq/issues/7875
    Once this bug is fixed, this file will no longer be relevant. *)

Require Import List.

Require Import Misc.

Fixpoint mymap {A B : Type} (f : A -> B) (l : list A) : list B :=
  match l with
  | nil => nil
  | x :: l => f x :: mymap f l
  end.

Lemma Forall2_mymap_left :
  forall (A B C : Type) (R : B -> C -> Prop) (f : A -> B) xs ys, Forall2 R (mymap f xs) ys <-> Forall2 (fun x y => R (f x) y) xs ys.
Proof.
  intros A B C R f xs ys. split.
  - intros H. remember (mymap f xs) as zs; generalize xs Heqzs; clear xs Heqzs. induction H.
    + intros xs; destruct xs; simpl in *; intros; [constructor|congruence].
    + intros xs; destruct xs; simpl in *; [congruence|].
      intros; constructor; [|apply IHForall2]; congruence.
  - intros H; induction H; simpl in *; econstructor; auto.
Qed.

Lemma Forall2_mymap_right :
  forall (A B C : Type) (R : A -> C -> Prop) (f : B -> C) xs ys, Forall2 R xs (mymap f ys) <-> Forall2 (fun x y => R x (f y)) xs ys.
Proof.
  intros A B C R f xs ys.
  rewrite Forall2_sym_iff, Forall2_mymap_left, Forall2_sym_iff.
  reflexivity.
Qed.

Lemma mymap_length :
  forall (A B : Type) (f : A -> B) xs, length (mymap f xs) = length xs.
Proof.
  induction xs; simpl in *; auto.
Qed.

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

Require Import String.

(** * Definition and properties of the [result] type *)
(** A result is the same as an option, but with an error message in case of failure *)

Inductive result (A : Type) :=
| Okk : A -> result A
| Err : string -> result A.

Arguments Okk {A}.
Arguments Err {A}.

Definition bind {A : Type} (a : result A) {B : Type} (f : A -> result B) :=
  match a with
  | Okk x => f x
  | Err s => Err s
  end.

Notation "a >>= f" := (bind a f) (at level 50, left associativity).
Notation "'do' a <- e ; c" := (e >>= (fun a => c)) (at level 60, right associativity).

Lemma Result_right_unit :
  forall A (a : result A), a = bind a (@Okk A).
Proof.
  intros; destruct a; auto.
Qed.

Lemma result_left_unit :
  forall A (a : A) B (f : A -> result B), f a = bind (Okk a) f.
Proof.
  intros; reflexivity.
Qed.

Lemma result_associativity :
  forall A (a : result A) B f C (g : B -> result C), bind a (fun x => bind (f x) g) = bind (bind a f) g.
Proof.
  intros; destruct a; reflexivity.
Qed.

Lemma bind_ok :
  forall A B a (f : A -> result B) x, a >>= f = Okk x -> exists y, a = Okk y /\ f y = Okk x.
Proof.
  intros; destruct a as [a|]; simpl in *; eauto; congruence.
Qed.

Ltac bind_ok_destruct H id1 id2 :=
  apply bind_ok in H; destruct H as [id1 [id2 H]].

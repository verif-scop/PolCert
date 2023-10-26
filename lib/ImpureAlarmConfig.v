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

Require Import Result.
Require Import Vpl.Impure Vpl.Debugging.
Require Import ImpureOperations.
Require Import IterSemantics.

Require Vpl.ImpureConfig.

Module CoreAlarmed := AlarmImpureMonad Vpl.ImpureConfig.Core.
Export CoreAlarmed.

Module Export ImpOps := ImpureOps CoreAlarmed.

Definition res_to_alarm {A : Type} (d : A) (x : result A) : imp A :=
  match x with
  | Okk a => pure a
  | Err s => alarm s (failwith INTERN s d)
  end.

Lemma res_to_alarm_correct :
  forall (A : Type) (d : A) (x : result A) (y : A),
    mayReturn (res_to_alarm d x) y -> x = Okk y.
Proof.
  intros A d x y. destruct x; simpl.
  - intros H. f_equal. apply mayReturn_pure. auto.
  - intros H. apply mayReturn_alarm in H. tauto.
Qed.

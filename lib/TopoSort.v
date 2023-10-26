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
Require Import Permutation.
Require Import Arith.
Require Import Misc.

Require Import Vpl.Impure.
Require Import Vpl.Debugging.

Require Import ImpureAlarmConfig.
Require Import String.
Require Import List.

Parameter topo_sort_untrusted : list (list bool) -> imp (list nat).

Definition check_toposort cstr out :=
  if Permutation_dec _ Nat.eq_dec (n_range (length cstr)) out then
    forallb (fun k2 => forallb (fun k1 => negb (nth (nth k2 out 0%nat) (nth (nth k1 out 0%nat) cstr nil) true)) (n_range k2)) (n_range (length cstr))
  else
    failwith CERT "topo_sort: not permutation"%string false.

(* Print check_toposort. *)
  
Lemma check_toposort_correct_permutation :
  forall cstr out, check_toposort cstr out = true -> Permutation (n_range (length cstr)) out.
Proof.
  intros cstr out H. unfold check_toposort in H.
  unfold Debugging.failwith in *.
  destruct Permutation_dec; [auto|congruence].
Qed.

Lemma check_toposort_correct_sorted :
  forall cstr out, check_toposort cstr out = true ->
              forall k1 k2, (k1 < k2 < length cstr)%nat -> nth (nth k2 out 0%nat) (nth (nth k1 out 0%nat) cstr nil) true = false.
Proof.
  intros cstr out H k1 k2 [Hk1 Hk2].
  unfold check_toposort, Debugging.failwith in H. destruct Permutation_dec; [|congruence].
  rewrite <- negb_true_iff. 
  rewrite forallb_forall in H. rewrite <- n_range_in in Hk2.
  specialize (H k2 Hk2); rewrite forallb_forall in H. rewrite <- n_range_in in Hk1.
  apply H; auto.
Qed.

Definition topo_sort cstr :=
  BIND out <- topo_sort_untrusted cstr -;
  if check_toposort cstr out then
    pure out
  else
    failwith CERT "topo_sort: not good sort" (alarm "topo_sort verification failed" out).

Lemma topo_sort_permutation :
  forall cstr, WHEN out <- topo_sort cstr THEN Permutation (n_range (length cstr)) out.
Proof.
  intros cstr out Hout.
  bind_imp_destruct Hout out1 Hout1.
  destruct (check_toposort cstr out1) eqn:Hcheck.
  - apply mayReturn_pure in Hout; rewrite Hout in *. apply check_toposort_correct_permutation; auto.
  - apply mayReturn_alarm in Hout; tauto.
Qed.

Lemma topo_sort_sorted :
  forall cstr, WHEN out <- topo_sort cstr THEN forall k1 k2, (k1 < k2 < length cstr)%nat ->
               nth (nth k2 out 0%nat) (nth (nth k1 out 0%nat) cstr nil) true = false.
Proof.
  intros cstr out Hout.
  bind_imp_destruct Hout out1 Hout1.
  destruct (check_toposort cstr out1) eqn:Hcheck.
  - apply mayReturn_pure in Hout; rewrite Hout in *. apply check_toposort_correct_sorted; auto.
  - apply mayReturn_alarm in Hout; tauto.
Qed.


Lemma topo_sort_indices_correct :
  forall cstr, WHEN out <- topo_sort cstr THEN forall i, In i out -> (i < length cstr)%nat.
Proof.
  intros cstr out Hout i Hin.
  rewrite <- n_range_in.
  eapply Permutation_in; [symmetry; apply topo_sort_permutation|]; eauto.
Qed.

Lemma topo_sort_length :
  forall cstr, WHEN out <- topo_sort cstr THEN length out = length cstr.
Proof.
  intros cstr out Hout.
  erewrite Permutation_length; [|symmetry; eapply topo_sort_permutation; eauto].
  rewrite n_range_length; eauto.
Qed.

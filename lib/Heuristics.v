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
Require Import Bool.
Require Import Psatz.

Require Import Misc.
Require Import Linalg.

Open Scope Z_scope.

Fixpoint minindex {A : Type} (f : A -> Z) (l : list A) : option A :=
  match l with
  | nil => None
  | x :: l => match minindex f l with None => Some x | Some y => if f x <? f y then Some x else Some y end
  end.

Lemma minindex_In :
  forall A f (l : list A) x, minindex f l = Some x -> In x l.
Proof.
  induction l.
  - intros; simpl in *; congruence.
  - intros x H; simpl in *. destruct (minindex f l) as [u|].
    + specialize (IHl u). destruct (f a <? f u); injection H; intros H1; rewrite <- H1; tauto.
    + injection H; intros; tauto.
Qed.

(** * Finding equalities: useful for reducing constraints on a given variable in a polyhedron *)
Definition find_eq (n : nat) (p : polyhedron) :=
  let l1 := filter (fun c => 0 <? nth n (fst c) 0) p in
  let l2 := filter (fun c => nth n (fst c) 0 <? 0) p in
  let l12 := list_prod l1 l2 in
  let flt := map fst (filter (fun c12 => is_eq (fst (fst c12)) (mult_vector (-1) (fst (snd c12))) && (snd (fst c12) =? -snd (snd c12))) l12) in
  minindex (fun c => nth n (fst c) 0) flt.

Theorem find_eq_in :
  forall n pol c, find_eq n pol = Some c -> In c pol.
Proof.
  intros n pol c Hfind. unfold find_eq in *.
  apply minindex_In in Hfind.
  rewrite in_map_iff in Hfind; destruct Hfind as [[c1 c2] [Heq Hfind1]].
  simpl in Heq; rewrite Heq in *.
  rewrite filter_In in Hfind1. destruct Hfind1 as [Hfind1 Heq1].
  rewrite in_prod_iff, !filter_In in Hfind1. tauto.
Qed.

Theorem find_eq_correct :
  forall n pol c p t, 0 < t -> find_eq n pol = Some c ->
                 (forall c, In c pol -> nth n (fst c) 0 <> 0 -> satisfies_constraint p (mult_constraint_cst t c) = true) -> dot_product p (fst c) = t * snd c.
Proof.
  intros n pol c p t Ht Hfind Hin.
  unfold find_eq, in_poly, satisfies_constraint in *.
  apply minindex_In in Hfind.
  rewrite in_map_iff in Hfind; destruct Hfind as [[c1 c2] [Heq Hfind1]].
  simpl in Heq; rewrite Heq in *.
  rewrite filter_In, in_prod_iff, !filter_In in Hfind1. reflect. destruct Hfind1 as [[[Hin1 ?] [Hin2 ?]] [Heql Heqr]].
  simpl in *; reflect.
  apply Hin in Hin1; apply Hin in Hin2; try lia; reflect.
  rewrite Heql, dot_product_mult_right in *. nia.
Qed.

Theorem find_eq_correct_1 :
  forall n pol c p, find_eq n pol = Some c -> (forall c, In c pol -> nth n (fst c) 0 <> 0 -> satisfies_constraint p c = true) -> dot_product p (fst c) = snd c.
Proof.
  intros n pol c p Hfind Hin.
  rewrite find_eq_correct with (t := 1) (n := n) (pol := pol); auto; try lia.
  intros c1. rewrite mult_constraint_cst_1. apply Hin.
Qed.

Theorem find_eq_nth :
  forall n pol c, find_eq n pol = Some c -> 0 < nth n (fst c) 0.
Proof.
  intros n pol c Hfind.
  unfold find_eq in *.
  apply minindex_In in Hfind.
  rewrite in_map_iff in Hfind; destruct Hfind as [[c1 c2] [Heq Hfind1]].
  simpl in Heq; rewrite Heq in *.
  rewrite filter_In, in_prod_iff, !filter_In in Hfind1. reflect. destruct Hfind1 as [[[? ?] [? ?]] ?].
  auto.
Qed.

Definition make_constraint_with_eq n c1 c2 :=
  let '(g, (aa, bb)) := Z.ggcd (nth n (fst c1) 0) (nth n (fst c2) 0) in
  add_constraint (mult_constraint (Z.sgn aa * -bb) c1) (mult_constraint (Z.abs aa) c2).

Lemma make_constraint_with_eq_correct :
  forall n c1 c2 p t, dot_product p (fst c1) = t * snd c1 -> nth n (fst c1) 0 <> 0 ->
                 satisfies_constraint p (mult_constraint_cst t (make_constraint_with_eq n c1 c2)) = satisfies_constraint p (mult_constraint_cst t c2).
Proof.
  intros n c1 c2 p t Hc1 Hcnz1. unfold make_constraint_with_eq.
  remember (nth n (fst c1) 0) as a. 
  remember (nth n (fst c2) 0) as b.
  generalize (Z.ggcd_correct_divisors a b). generalize (Z.ggcd_gcd a b).
  destruct Z.ggcd as [g [aa bb]] eqn:Hggcd. simpl. intros Hg [Haa Hbb].
  unfold satisfies_constraint, add_constraint, mult_constraint; simpl.
  rewrite add_vector_dot_product_distr_right, !dot_product_mult_right, eq_iff_eq_true; reflect.
  nia.
Qed.

Lemma make_constraint_with_eq_correct_1 :
  forall n c1 c2 p, dot_product p (fst c1) = snd c1 -> nth n (fst c1) 0 <> 0 ->
               satisfies_constraint p (make_constraint_with_eq n c1 c2) = satisfies_constraint p c2.
Proof.
  intros n c1 c2 p Hc1 Hcnz1.
  generalize (make_constraint_with_eq_correct n c1 c2 p 1).
  rewrite !mult_constraint_cst_1. intros H; apply H; lia.
Qed.

Lemma make_constraint_with_eq_nth :
  forall n c1 c2, nth n (fst c1) 0 <> 0 -> nth n (fst (make_constraint_with_eq n c1 c2)) 0 = 0.
Proof.
  intros n c1 c2 Hcnz1. unfold make_constraint_with_eq.
  remember (nth n (fst c1) 0) as a. 
  remember (nth n (fst c2) 0) as b.
  generalize (Z.ggcd_correct_divisors a b). generalize (Z.ggcd_gcd a b).
  destruct Z.ggcd as [g [aa bb]] eqn:Hggcd. simpl. intros Hg [Haa Hbb].
  unfold satisfies_constraint, add_constraint, mult_constraint; simpl.
  rewrite add_vector_nth, !mult_nth.
  nia.
Qed.

Lemma make_constraint_with_eq_preserve_zeros :
  forall n m c1 c2, nth n (fst c1) 0 = 0 -> nth n (fst c2) 0 = 0 -> nth n (fst (make_constraint_with_eq m c1 c2)) 0 = 0.
Proof.
  intros n m c1 c2 H1 H2. unfold make_constraint_with_eq.
  destruct Z.ggcd as [? [? ?]]. unfold add_constraint, mult_constraint. simpl.
  rewrite add_vector_nth, !mult_nth. nia.
Qed.

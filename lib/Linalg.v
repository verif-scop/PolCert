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
Require Import ListExt.
Require Import Bool.
Require Import Psatz.
Require Import Setoid Morphisms.
Require Import RelationPairs.
Require Import FunctionalExtensionality.

Require Import Misc.

Import List.ListNotations.

Require Import LibTactics.

Open Scope Z_scope.
Open Scope list_scope.
Open Scope vector_scope.


(** * Equality on vectors
    a series of lemmas for vector's equivalence.
*)

(** Two vectors are equal iff they are so up to trailing zeros. *)
(*** is_null: all elem in xs is 0. *)
Definition is_null xs := forallb (fun x => x =? 0) xs.
Transparent is_null.
Hint Unfold is_null.

(*** is_eq: two lists are equal, if they are equal up to trailing zeros. *)
Fixpoint is_eq (xs ys : list Z) :=
  match xs, ys with
  | nil, nil => true
  | nil, ys => is_null ys
  | xs, nil => is_null xs
  | x :: xs, y :: ys => (x =? y) && is_eq xs ys
  end.

Lemma veq_def xs ys : {P | P <-> is_eq xs ys = true}.
Proof.
  exists (is_eq xs ys = true). reflexivity.
Qed.

(* Definition veq xs ys := proj1_sig (veq_def xs ys). *)
(*** veq: two vector are equal. return a Prop. *)
Definition veq xs ys := is_eq xs ys = true.
Infix "=v=" := veq (at level 70) : vector_scope.

Lemma is_eq_veq :
  forall xs ys, is_eq xs ys = true <-> xs =v= ys.
Proof.
  intros. unfold veq. (* destruct (veq_def xs ys). simpl.
  symmetry. assumption. *) reflexivity.
Qed.
Hint Rewrite is_eq_veq : reflect.
Opaque veq.

Lemma is_eq_reflexive :
  forall xs, is_eq xs xs = true.
Proof.
  induction xs; simpl; auto.
  reflect. auto.
Qed.
Hint Immediate is_eq_reflexive.

Lemma veq_refl :
  forall xs, xs =v= xs.
Proof.
  intros. rewrite <- is_eq_veq. apply is_eq_reflexive.
Qed.

Lemma is_eq_commutative :
  forall xs ys, is_eq xs ys = is_eq ys xs.
Proof.
  induction xs.
  - destruct ys; auto.
  - destruct ys; simpl in *; auto.
    f_equal; [apply Z.eqb_sym | auto].
Qed.

Lemma veq_sym :
  forall xs ys, xs =v= ys -> ys =v= xs.
Proof.
  intros. rewrite <- is_eq_veq in *.
  rewrite is_eq_commutative. auto.
Qed.

Lemma is_eq_nil_left :
  forall xs, is_eq nil xs = is_null xs.
Proof.
  destruct xs; auto.
Qed.
Lemma is_eq_nil_right :
  forall xs, is_eq xs nil = is_null xs.
Proof.
  destruct xs; auto.
Qed.
Hint Immediate is_eq_nil_left is_eq_nil_right.
Hint Rewrite is_eq_nil_left is_eq_nil_right : vector.

Lemma is_null_eq_compat :
  forall xs ys, is_eq xs ys = true -> is_null xs = is_null ys.
Proof.
  induction xs.
  - destruct ys; auto.
  - destruct ys; auto. intro Heq. simpl in *.
    reflect; rewrite <- is_eq_veq in *. destruct Heq.
    f_equal; [congruence|auto].
Qed.

Lemma is_eq_is_null_left :
  forall xs ys, is_null xs = true -> is_eq xs ys = is_null ys.
Proof.
  induction xs.
  - destruct ys; auto.
  - destruct ys; auto. simpl. reflect. intros [Ha Heq].
    f_equal.
    + rewrite Ha. apply Z.eqb_sym.
    + auto.
Qed.

Lemma is_eq_is_null_right :
  forall xs ys, is_null ys = true -> is_eq xs ys = is_null xs.
Proof.
  intros. rewrite is_eq_commutative. apply is_eq_is_null_left. auto.
Qed.

Lemma is_eq_is_eq_left :
  forall xs ys zs, is_eq xs ys = true -> is_eq xs zs = is_eq ys zs.
Proof.
  induction xs.
  - intros ys zs Heq. rewrite is_eq_nil_left in *. rewrite is_eq_is_null_left; auto.
  - destruct ys; destruct zs; auto; autorewrite with vector.
    + intros. apply is_eq_is_null_left; auto.
    + intros. apply is_null_eq_compat; auto.
    + simpl in *. reflect. rewrite <- is_eq_veq in *. intros [Ha Heq]. f_equal; [congruence|auto].
Qed.

Lemma is_eq_is_eq_right :
  forall xs ys zs, is_eq ys zs = true -> is_eq xs ys = is_eq xs zs.
Proof.
  intros xs ys zs Heq.
  rewrite is_eq_commutative. erewrite is_eq_is_eq_left; [apply is_eq_commutative|]; auto.
Qed.

Lemma veq_transitive :
  forall xs ys zs, xs =v= ys -> ys =v= zs -> xs =v= zs.
Proof.
  intros xs ys zs H1 H2. rewrite <- is_eq_veq in *.
  erewrite is_eq_is_eq_left; eauto.
Qed.

Instance veq_Equiv : Equivalence veq.
Proof.
  split; [exact veq_refl | exact veq_sym | exact veq_transitive].
Qed.


Lemma veq_eq_dec: 
  forall xs ys, {veq xs ys} + {~ veq xs ys}.
Proof.
  intros. 
  Transparent veq.
  unfold veq. 
  destruct (is_eq xs ys); decide equality. 
  Opaque veq.
Qed.

Instance is_null_proper : Proper (veq ==> eq) is_null.
Proof.
  intros xs1 xs2 Hxs. rewrite <- is_eq_veq in Hxs.
  apply is_null_eq_compat; auto.
Qed.

Instance is_eq_proper : Proper (veq ==> veq ==> eq) is_eq.
Proof.
  intros xs1 xs2 H1 ys1 ys2 H2.
  erewrite is_eq_is_eq_left; [|rewrite is_eq_veq; exact H1].
  apply is_eq_is_eq_right; rewrite is_eq_veq; exact H2.
Qed.

Instance cons_proper : Proper (eq ==> veq ==> veq) cons.
Proof.
  intros x1 x2 Hx xs1 xs2 Hxs.
  rewrite <- is_eq_veq in *. simpl. rewrite Hx. rewrite Z.eqb_refl. auto.
Qed.

Lemma vector_nth_null :
  forall v, (forall n, nth n v 0 = 0) -> is_null v = true.
Proof.
  induction v.
  - intros; simpl; auto.
  - intros H; simpl; reflect; split.
    + exact (H 0%nat).
    + apply IHv; intros n; exact (H (S n)).
Qed.

Lemma vector_nth_eq :
  forall v1 v2, (forall n, nth n v1 0 = nth n v2 0) -> is_eq v1 v2 = true.
Proof.
  induction v1.
  - intros v2 H; simpl; destruct v2; try reflexivity; apply vector_nth_null.
    intros n; rewrite <- H; auto. destruct n; auto.
  - intros v2 H; destruct v2; simpl; rewrite andb_true_iff.
    + split; [reflect; exact (H 0%nat)|apply vector_nth_null; intros n; exact (H (S n))].
    + split; [reflect; exact (H 0%nat)|apply IHv1; intros n; exact (H (S n))].
Qed.

Lemma vector_nth_veq :
  forall v1 v2, (forall n, nth n v1 0 = nth n v2 0) -> v1 =v= v2.
Proof.
  intros v1 v2 H.
  rewrite <- is_eq_veq. apply vector_nth_eq; auto.
Qed.

Lemma is_eq_app :
  forall l1 l2 l3 l4, length l1 = length l3 -> is_eq (l1 ++ l2) (l3 ++ l4) = is_eq l1 l3 && is_eq l2 l4.
Proof.
  induction l1.
  - intros l2 l3 l4 H. destruct l3; simpl in *; auto; lia.
  - intros l2 l3 l4 H. destruct l3; simpl in *; try lia.
    rewrite IHl1; try lia. destruct (a =? z); auto.
Qed.

Lemma repeat_zero_is_null :
  forall n, is_null (repeat 0 n) = true.
Proof.
  induction n; auto.
Qed.

Lemma same_length_eq :
  forall xs ys, length xs = length ys -> xs =v= ys -> xs = ys.
Proof.
  induction xs.
  - intros ys Hlen Heq. rewrite <- is_eq_veq in Heq. destruct ys; simpl in *; congruence.
  - intros ys Hlen Heq. rewrite <- is_eq_veq in Heq. destruct ys; simpl in *; [congruence|].
    reflect. destruct Heq; f_equal; auto.
Qed.

Lemma veq_implies_rev_veq:
  forall v1 v2,
    v1 =v= v2 ->
    length v1 = length v2 ->
    List.rev v1 =v= List.rev v2.
Proof.
  induction v1.
  - intros. symmetry in H0.
    rewrite List.length_zero_iff_nil in H0. subst.
    trivial.
  - intros. simpls. destruct v2 eqn:Hv2; tryfalse.
    inversion H. inversion H0.
    rewrite andb_true_iff in H2.
    destruct H2.
    simpl.
    assert (rev v1 =v= rev l). {
      eapply IHv1; eauto.
    } 
    Transparent veq.
    unfold veq. rewrite is_eq_app.
    2: { do 2 rewrite List.rev_length; trivial. }
    rewrite andb_true_iff. split; trivial.
    inversion H. rewrite H6.
    rewrite andb_true_iff in H6. 
    destruct H6. eapply Z.eqb_eq in H5. subst. simpls.
    rewrite andb_true_iff. split; trivial.
Qed.

Instance app_proper : Proper (eq ==> veq ==> veq) (@app Z).
Proof.
  intros l1 l2 Hl r1 r2 Hr.
  rewrite Hl. rewrite <- is_eq_veq.
  rewrite is_eq_app by reflexivity. rewrite is_eq_reflexive; simpl.
  rewrite is_eq_veq; assumption.
Qed.

(** * Dot product 
    Some lemmas about dot product.
*)

Fixpoint dot_product (xs ys : list Z) :=
  match xs, ys with
  | _, nil | nil, _ => 0
  | x :: xs, y :: ys => x * y + dot_product xs ys
  end.

Lemma dot_product_nil_left : forall xs, dot_product nil xs = 0.
Proof.
  intros; destruct xs; auto.
Qed.
Lemma dot_product_nil_right : forall xs, dot_product xs nil = 0.
Proof.
  intros; destruct xs; auto.
Qed.
Hint Immediate dot_product_nil_left dot_product_nil_right.
Hint Rewrite dot_product_nil_left dot_product_nil_right : vector.

Lemma dot_product_commutative : forall xs ys, dot_product xs ys = dot_product ys xs.
Proof.
  induction xs.
  - intro ys; destruct ys; auto.
  - intro ys; destruct ys; [auto|simpl; rewrite IHxs; ring].
Qed.

Lemma dot_product_null_left :
  forall xs ys, is_null xs = true -> dot_product xs ys = 0.
Proof.
  induction xs; auto.
  intros ys Hnull; destruct ys; auto.
  simpl in *; reflect; destruct Hnull as [Hzero Hnull].
  rewrite IHxs; [nia | auto].
Qed.

Lemma dot_product_null_right :
  forall xs ys, is_null ys = true -> dot_product xs ys = 0.
Proof.
  intros xs ys Hnull; rewrite dot_product_commutative; auto using dot_product_null_left.
Qed.

Lemma dot_product_eq_compat_left :
  forall xs ys zs, is_eq xs ys = true -> dot_product xs zs = dot_product ys zs.
Proof.
  induction xs.
  - destruct ys; destruct zs; auto.
    intros. repeat (rewrite dot_product_null_left); auto.
  - destruct ys.
    + destruct zs; intros; repeat (rewrite dot_product_null_left); auto.
    + destruct zs; simpl; auto. reflect; rewrite <- is_eq_veq. intros [Ha Heq].
      f_equal; [congruence | auto].
Qed.

Lemma dot_product_eq_compat_right :
  forall xs ys zs, is_eq ys zs = true -> dot_product xs ys = dot_product xs zs.
Proof.
  intros xs ys zs Heq. rewrite dot_product_commutative.
  erewrite dot_product_eq_compat_left; eauto using dot_product_commutative.
Qed.

Instance dot_product_proper : Proper (veq ==> veq ==> eq) dot_product.
Proof.
  intros xs1 xs2 H1 ys1 ys2 H2.
  erewrite dot_product_eq_compat_left; [|rewrite is_eq_veq; exact H1].
  apply dot_product_eq_compat_right; rewrite is_eq_veq; exact H2.
Qed.

Lemma dot_product_repeat_zero_right :
  forall n l, dot_product l (repeat 0 n) = 0.
Proof.
  intros. apply dot_product_null_right. apply repeat_zero_is_null.
Qed.

Lemma dot_product_repeat_zero_left :
  forall n l, dot_product (repeat 0 n) l = 0.
Proof.
  intros. rewrite dot_product_commutative; apply dot_product_repeat_zero_right.
Qed.
Hint Rewrite dot_product_repeat_zero_left dot_product_repeat_zero_right : vector.

Lemma dot_product_app :
  forall l1 l2 l3 l4, length l1 = length l3 -> dot_product (l1 ++ l2) (l3 ++ l4) = dot_product l1 l3 + dot_product l2 l4.
Proof.
  induction l1.
  - intros l2 l3 l4 H. destruct l3; simpl in *; auto; lia.
  - intros l2 l3 l4 H. destruct l3; simpl in *; try lia. rewrite IHl1; lia.
Qed.

(** * Constraints and polyhedra *)

Definition constraint := (list Z * Z)%type.

Definition satisfies_constraint p c := dot_product p (fst c) <=? (snd c).
Transparent satisfies_constraint.
Hint Unfold satisfies_constraint.

(** constraint equal: vector equal (trailing zero) + Z.eq *)
Definition ceq := (veq * @eq Z)%signature.
Transparent ceq.
Infix "=c=" := ceq (at level 70) : vector_scope.

Instance satisfies_constraint_proper : Proper (veq ==> ceq ==> eq) satisfies_constraint.
Proof.
  intros p1 p2 H1 c1 c2 H2.
  unfold satisfies_constraint. rewrite H1. rewrite H2. reflexivity.
Qed.

Definition polyhedron := list constraint.

Definition in_poly p pol := forallb (satisfies_constraint p) pol.
Instance in_poly_proper : Proper (veq ==> eq ==> eq) in_poly.
Proof.
  intros p1 p2 H1 pol1 pol2 H2.
  rewrite H2. unfold in_poly.
  apply forallb_ext. intros. rewrite H1. reflexivity.
Qed.

Lemma in_poly_app :
  forall p pol1 pol2, in_poly p (pol1 ++ pol2) = in_poly p pol1 && in_poly p pol2.
Proof.
  intros. unfold in_poly. apply forallb_app.
Qed.

Definition empty_poly (pol : polyhedron) :=
  forall p, in_poly p pol = false.
Definition empty_constraint : constraint := (nil, -1).
Definition null_constraint : constraint := (nil, 0).
Transparent empty_poly empty_constraint null_constraint.
Hint Unfold empty_poly empty_constraint null_constraint.

Lemma empty_constraint_empty : forall p, satisfies_constraint p empty_constraint = false.
Proof.
  intros. autounfold; simpl; autorewrite with vector. auto.
Qed.
Lemma null_constraint_trivial : forall p, satisfies_constraint p null_constraint = true.
Proof.
  intros. autounfold; simpl; autorewrite with vector. auto.
Qed.





(** * Multiplying vectors and constraints by a constant *)

Definition mult_vector k xs := map (fun x => k * x) xs.
Definition mult_constraint (k : Z) (c : constraint) :=
  (mult_vector k (fst c), k * snd c).
Definition mult_constraint_cst k (c : (list Z * Z)) := (fst c, k * snd c).
Transparent mult_constraint mult_constraint_cst.
Hint Unfold mult_constraint mult_constraint_cst.

Lemma mult_vector_null :
  forall k xs, is_null xs = true -> is_null (mult_vector k xs) = true.
Proof.
  intros k. induction xs; auto.
  simpl. reflect.
  intros [Ha Hnull]. split; [nia | auto].
Qed.

Lemma mult_vector_eq_compat :
  forall k xs ys, is_eq xs ys = true -> is_eq (mult_vector k xs) (mult_vector k ys) = true.
Proof.
  intros k. induction xs.
  - intros ys Heq. rewrite is_eq_nil_left in *. apply mult_vector_null; auto.
  - destruct ys.
    + intros Heq. rewrite is_eq_nil_right in *. apply mult_vector_null; auto.
    + simpl. reflect. repeat (rewrite <- is_eq_veq in *).
      intros [Ha Heq]. split; [congruence | apply IHxs; auto].
Qed.

Instance mult_vector_proper : Proper (eq ==> veq ==> veq) mult_vector.
Proof.
  intros k1 k2 Hk xs1 xs2 Hx.
  rewrite Hk. rewrite <- is_eq_veq in *.
  apply mult_vector_eq_compat; auto.
Qed.

Instance mult_constraint_proper : Proper (eq ==> ceq ==> ceq) mult_constraint.
Proof.
  intros k1 k2 Hk c1 c2 Hc.
  rewrite Hk. unfold mult_constraint.
  rewrite Hc. reflexivity.
Qed.

Lemma dot_product_mult_left :
  forall k xs ys, dot_product (mult_vector k xs) ys = k * dot_product xs ys.
Proof.
  intros k. induction xs.
  - intro ys. repeat (rewrite dot_product_nil_left). ring.
  - intro ys. destruct ys.
    + repeat (rewrite dot_product_nil_right). ring.
    + simpl. rewrite IHxs. ring.
Qed.

Lemma dot_product_mult_right :
  forall k xs ys, dot_product xs (mult_vector k ys) = k * dot_product xs ys.
Proof.
  intros.
  rewrite dot_product_commutative.
  rewrite dot_product_mult_left.
  rewrite dot_product_commutative.
  auto.
Qed.

Lemma mult_nth :
  forall n k v, nth n (mult_vector k v) 0 = k * nth n v 0.
Proof.
  intros; unfold mult_vector.
  erewrite <- map_nth with (l := v). f_equal. lia.
Qed.

Lemma mult_vector_length :
  forall k v, length (mult_vector k v) = length v.
Proof.
  intros. apply map_length.
Qed.

Lemma mult_vector_1 :
  forall v, mult_vector 1 v = v.
Proof.
  induction v; simpl; auto; destruct a; f_equal; auto.
Qed.

Lemma mult_vector_comp :
  forall s t v, mult_vector s (mult_vector t v) = mult_vector (s * t) v.
Proof.
  intros s t v. unfold mult_vector. rewrite map_map; apply map_ext.
  intros; nia.
Qed.

Lemma mult_vector_app :
  forall s v1 v2, mult_vector s (v1 ++ v2) = mult_vector s v1 ++ mult_vector s v2.
Proof.
  intros s v1 v2. unfold mult_vector. apply map_app.
Qed.

Hint Rewrite dot_product_mult_left dot_product_mult_right : vector.

Lemma mult_constraint_eq :
  forall k c p, k > 0 -> satisfies_constraint p (mult_constraint k c) = satisfies_constraint p c.
Proof.
  intros k c p Hpos.
  destruct (satisfies_constraint p c) eqn:Heq; autounfold in *; simpl in *; rewrite dot_product_mult_right; reflect; nia.
Qed.

Lemma mult_constraint_zero :
  forall c p, satisfies_constraint p (mult_constraint 0 c) = true.
Proof.
  intros c p. autounfold; simpl; rewrite dot_product_mult_right.
  reflect; lia.
Qed.

Lemma mult_constraint_pos_satisfy :
  forall k c p, k >= 0 -> satisfies_constraint p c = true -> satisfies_constraint p (mult_constraint k c) = true.
Proof.
  intros k c p Hpos Hsat. destruct (Z.lt_total k 0) as [Hk | [Hk | Hk]].
  - lia.
  - rewrite Hk; apply mult_constraint_zero.
  - rewrite mult_constraint_eq; auto; lia.
Qed.

Lemma mult_constraint_1 :
  forall c, mult_constraint 1 c = c.
Proof.
  intros c; destruct c as [v x]; unfold mult_constraint.
  simpl in *; rewrite mult_vector_1.
  f_equal; destruct x; auto.
Qed.

Lemma mult_constraint_cst_1 :
  forall c, mult_constraint_cst 1 c = c.
Proof.
  intros c; destruct c as [v x]; destruct x; auto.
Qed.

Lemma mult_constraint_cst_eq :
  forall c k p, 0 < k -> satisfies_constraint (mult_vector k p) (mult_constraint_cst k c) = satisfies_constraint p c.
Proof.
  intros c k p Hk.
  unfold satisfies_constraint, mult_constraint_cst.
  rewrite dot_product_mult_left. simpl.
  apply eq_iff_eq_true. reflect.
  nia.
Qed.

Lemma mult_constraint_cst_comp :
  forall s t c, mult_constraint_cst s (mult_constraint_cst t c) = mult_constraint_cst (s * t) c.
Proof.
  intros. unfold mult_constraint_cst. simpl. f_equal.
  nia.
Qed.

(** * Constraint negation 
    a * p <= b 
    b + 1 <= a * p
*)
Definition neg_constraint c :=
  (mult_vector (-1) (fst c), -snd c - 1).
Lemma neg_constraint_correct :
  forall p c, satisfies_constraint p (neg_constraint c) = negb (satisfies_constraint p c).
Proof.
  intros p c. unfold satisfies_constraint.
  apply eq_iff_eq_true. reflect. unfold neg_constraint.
  simpl. rewrite dot_product_mult_right. lia.
Qed.


(** * Adding two vectors: ok with trailing zero *)

Fixpoint add_vector xs ys :=
  match xs, ys with
  | nil, nil => nil
  | nil, ys => ys
  | xs, nil => xs
  | x :: xs, y :: ys => (x + y) :: add_vector xs ys
  end.

Lemma add_vector_nil_left :
  forall xs, add_vector nil xs = xs.
Proof.
  intro xs; destruct xs; auto.
Qed.
Lemma add_vector_nil_right :
  forall xs, add_vector xs nil = xs.
Proof.
  intro xs; destruct xs; auto.
Qed.
Hint Immediate add_vector_nil_left add_vector_nil_right.
Hint Rewrite add_vector_nil_left add_vector_nil_right : vector.

Lemma add_vector_commutative :
  forall xs ys, add_vector xs ys = add_vector ys xs.
Proof.
  induction xs.
  - intro ys; destruct ys; auto.
  - intro ys; destruct ys; auto.
    simpl; f_equal; [ring | auto].
Qed.

Lemma add_vector_null_left :
  forall xs ys, is_null xs = true -> is_eq (add_vector xs ys) ys = true.
Proof.
  induction xs.
  - intros ys Heq. rewrite add_vector_nil_left. apply is_eq_reflexive.
  - intros ys Heq. destruct ys; auto.
    simpl in *; reflect; rewrite <- is_eq_veq in *.
    destruct Heq as [Ha Heq]; split; [lia | apply IHxs; auto].
Qed.

Lemma add_vector_null_right :
  forall xs ys, is_null ys = true -> is_eq (add_vector xs ys) xs = true.
Proof.
  intros xs ys Heq. rewrite add_vector_commutative. apply add_vector_null_left. auto.
Qed.

Lemma add_vector_eq_compat_left :
  forall xs ys zs, is_eq xs ys = true -> is_eq (add_vector xs zs) (add_vector ys zs) = true.
Proof.
  induction xs.
  - intros ys zs Heq. destruct ys; destruct zs; auto using is_eq_reflexive.
    rewrite add_vector_nil_left. rewrite is_eq_commutative. apply add_vector_null_left. auto.
  - intros ys zs Heq. destruct ys; destruct zs; auto.
    + rewrite add_vector_nil_left. apply add_vector_null_left. auto.
    + simpl in *; reflect; rewrite <- is_eq_veq in *.
      destruct Heq as [Ha Heq]; split; [lia | apply IHxs; auto].
Qed.

Lemma add_vector_eq_compat_right :
  forall xs ys zs, is_eq ys zs = true -> is_eq (add_vector xs ys) (add_vector xs zs) = true.
Proof.
  intros xs ys zs Heq. rewrite add_vector_commutative with (ys := ys).
  rewrite add_vector_commutative with (ys := zs). apply add_vector_eq_compat_left; auto.
Qed.

Instance add_vector_proper : Proper (veq ==> veq ==> veq) add_vector.
Proof.
  intros xs1 xs2 Hx ys1 ys2 Hy.
  transitivity (add_vector xs2 ys1).
  - rewrite <- is_eq_veq in *; erewrite add_vector_eq_compat_left; [reflexivity|exact Hx].
  - rewrite <- is_eq_veq in *; apply add_vector_eq_compat_right. exact Hy.
Qed.

Lemma add_vector_mult_distr :
  forall k xs ys, mult_vector k (add_vector xs ys) = add_vector (mult_vector k xs) (mult_vector k ys).
Proof.
  induction xs.
  - intro ys; destruct ys; auto.
  - intro ys; destruct ys; auto.
    simpl; f_equal; [ring | auto].
Qed.

Lemma add_vector_dot_product_distr_left :
  forall xs ys zs, dot_product (add_vector xs ys) zs = dot_product xs zs + dot_product ys zs.
Proof.
  induction xs.
  - intros ys zs; destruct ys; destruct zs; auto.
  - intros ys zs; destruct ys; destruct zs; simpl; try rewrite IHxs; ring.
Qed.

Lemma add_vector_dot_product_distr_right :
  forall xs ys zs, dot_product xs (add_vector ys zs) = dot_product xs ys + dot_product xs zs.
Proof.
  intros xs ys zs. rewrite dot_product_commutative. rewrite add_vector_dot_product_distr_left.
  f_equal; apply dot_product_commutative.
Qed.

Lemma add_vector_nth :
  forall n v1 v2, nth n (add_vector v1 v2) 0 = nth n v1 0 + nth n v2 0.
Proof.
  induction n.
  - intros; destruct v1; destruct v2; simpl; lia.
  - intros; destruct v1; destruct v2; simpl; try (rewrite IHn); lia.
Qed.


(** * Adding constraints *)

Definition add_constraint c1 c2 := (add_vector (fst c1) (fst c2), snd c1 + snd c2).
Transparent add_constraint.
Hint Unfold add_constraint.

Instance add_constraint_proper : Proper (ceq ==> ceq ==> ceq) add_constraint.
Proof.
  intros c1 c2 Hc d1 d2 Hd.
  unfold add_constraint.
  rewrite Hc. rewrite Hd. reflexivity.
Qed.

Lemma add_constraint_satisfy :
  forall p c1 c2, satisfies_constraint p c1 = true -> satisfies_constraint p c2 = true ->
             satisfies_constraint p (add_constraint c1 c2) = true.
Proof.
  intros p c1 c2 Hs1 Hs2.
  autounfold in *. simpl; reflect. rewrite add_vector_dot_product_distr_right. lia.
Qed.


(** * Certificates for polyhedral operations *)

Definition same_polyhedron pol1 pol2 := forall p, in_poly p pol1 = in_poly p pol2.

Fixpoint combine_constraints comb pol :=
  match comb, pol with
  | nil, _ | _, nil => null_constraint
  | c :: comb, p :: pol => add_constraint (mult_constraint c p) (combine_constraints comb pol)
  end.


Lemma combine_constraints_satisfy :
  forall p comb pol, forallb (fun w => 0 <=? w) comb = true -> forallb (satisfies_constraint p) pol = true ->
                satisfies_constraint p (combine_constraints comb pol) = true.
Proof.
  intros p. induction comb.
  - intros pol Hcomb Hsat. destruct pol; simpl; apply null_constraint_trivial.
  - intros pol Hcomb Hsat. destruct pol; simpl in *.
    + apply null_constraint_trivial.
    + reflect. destruct Hcomb as [Ha Hcomb]. destruct Hsat as [Hc Hsat].
      apply add_constraint_satisfy.
      * apply mult_constraint_pos_satisfy; [lia | auto].
      * apply IHcomb; auto.
Qed.

Definition constraint_entails (c1 c2 : constraint) := is_eq (fst c1) (fst c2) && (snd c1 <=? snd c2).
Hint Unfold constraint_entails.

Lemma constraint_entails_correct :
  forall c1 c2 p, constraint_entails c1 c2 = true -> satisfies_constraint p c1 = true -> satisfies_constraint p c2 = true.
Proof.
  intros c1 c2 p Hent Hsat.
  autounfold in *.
  reflect; destruct Hent as [Heq Hcmp].
  rewrite Heq in Hsat. lia.
Qed.

Definition witness := (list Z * Z)%type.

Definition is_redundant (wit : witness) (pol : polyhedron) (c : constraint) :=
  (0 <? snd wit) &&
    forallb (fun w => 0 <=? w) (fst wit) && 
    constraint_entails (combine_constraints (fst wit) pol) (mult_constraint (snd wit) c).
Transparent is_redundant.
Hint Unfold is_redundant.

Lemma is_redundant_correct :
  forall wit pol c p, is_redundant wit pol c = true -> forallb (satisfies_constraint p) pol = true ->
                 satisfies_constraint p c = true.
Proof.
  intros wit pol c p Hred Hinpoly.
  unfold is_redundant in Hred. reflect.
  destruct Hred as [[Hpos Hcpos] Hent].
  erewrite <- mult_constraint_eq.
  - eapply constraint_entails_correct; eauto.
    apply combine_constraints_satisfy; auto.
  - lia.
Qed.

Definition is_empty (wit : witness) (pol : polyhedron) := is_redundant wit pol empty_constraint.
Transparent is_empty.
Hint Unfold is_empty.

Lemma is_empty_correct :
  forall wit pol, is_empty wit pol = true -> empty_poly pol.
Proof.
  intros wit pol Hemp p.
  assert (~ (in_poly p pol = true)); [|destruct (in_poly p pol); congruence]. intro Hin.
  assert (satisfies_constraint p empty_constraint = true).
  - eapply is_redundant_correct; eauto.
  - rewrite empty_constraint_empty in *; congruence.
Qed.


(** * Lexicographical ordering of vectors *)

Fixpoint lex_compare_nil t :=
  match t with
  | nil => Eq
  | x :: t => match 0 ?= x with Eq => lex_compare_nil t | c => c end
  end.

Lemma lex_compare_nil_is_null :
  forall t, is_null t = true -> lex_compare_nil t = Eq.
Proof.
  induction t; auto.
  intros H; simpl in *. reflect. destruct H as [Ha Hn].
  rewrite Ha; auto.
Qed.

Lemma is_null_lex_compare_nil :
  forall t, lex_compare_nil t = Eq -> is_null t = true.
Proof.
  induction t; auto.
  intros H; simpl in *. reflect.
  destruct a; try discriminate.
  {
    eapply IHt in H.
    split; trivial.
  }
Qed.

Lemma lex_compare_nil_eq :
  forall t1 t2, is_eq t1 t2 = true -> lex_compare_nil t1 = lex_compare_nil t2.
Proof.
  induction t1.
  - intros t2 H. simpl. rewrite lex_compare_nil_is_null; auto. rewrite is_eq_nil_left in H; auto.
  - intros t2 H. destruct t2.
    + rewrite lex_compare_nil_is_null; auto.
    + simpl in H. reflect. rewrite <- is_eq_veq in *. destruct H as [Ha Hn]. rewrite Ha.
      simpl. destruct z; auto.
Qed.

Fixpoint lex_compare t1 t2 :=
  match t1, t2 with
  | nil, nil => Eq
  | _, nil => CompOpp (lex_compare_nil t1)
  | nil, _ => lex_compare_nil t2
  | x :: t1, y :: t2 => match x ?= y with Eq => lex_compare t1 t2 | c => c end
  end.

Lemma lex_compare_antisym :
  forall t1 t2, lex_compare t1 t2 = CompOpp (lex_compare t2 t1).
Proof.
  induction t1.
  - destruct t2; simpl; auto using CompOpp_involutive.
  - destruct t2; simpl; auto.
    rewrite Z.compare_antisym.
    rewrite IHt1. destruct (z ?= a); auto.
Qed.

Lemma lex_compare_null_left :
  forall t1 t2, is_null t1 = true -> lex_compare t1 t2 = lex_compare_nil t2.
Proof.
  induction t1.
  - intros; destruct t2; auto.
  - intros t2 H; destruct t2; simpl in *; reflect; destruct H as [Ha Hn]; rewrite Ha.
    + rewrite lex_compare_nil_is_null; auto.
    + rewrite IHt1; auto.
Qed.

Lemma lex_compare_nil_left :
  forall t, lex_compare nil t = lex_compare_nil t.
Proof.
  intros; destruct t; auto.
Qed.

Lemma lex_compare_nil_right :
  forall t, lex_compare t nil = CompOpp (lex_compare_nil t).
Proof.
  intros; destruct t; auto.
Qed.

Lemma lex_compare_left_eq :
  forall t1 t2 t3, is_eq t1 t2 = true -> lex_compare t1 t3 = lex_compare t2 t3.
Proof.
  induction t1.
  - intros t2 t3 H. rewrite lex_compare_nil_left. rewrite lex_compare_null_left; auto. rewrite is_eq_nil_left in H; auto.
  - intros t2 t3 H. destruct t2.
    + rewrite lex_compare_nil_left. rewrite lex_compare_null_left; auto. 
    + simpl in H. reflect. rewrite <- is_eq_veq in *. destruct H as [Ha Hn]. rewrite Ha.
      destruct t3.
      * simpl in *. erewrite lex_compare_nil_eq; eauto.
      * simpl. erewrite IHt1; auto.
Qed.

Lemma lex_compare_right_eq :
  forall t1 t2 t3, is_eq t2 t3 = true -> lex_compare t1 t2 = lex_compare t1 t3.
Proof.
  intros t1 t2 t3 H.
  rewrite lex_compare_antisym.
  erewrite lex_compare_left_eq; [|apply H]. rewrite <- lex_compare_antisym. auto.
Qed.

Instance lex_compare_proper : Proper (veq ==> veq ==> eq) lex_compare.
Proof.
  intros s1 s2 Hs t1 t2 Ht.
  transitivity (lex_compare s1 t2).
  - apply lex_compare_right_eq; rewrite is_eq_veq; exact Ht.
  - apply lex_compare_left_eq; rewrite is_eq_veq; exact Hs.
Qed.

Lemma lex_compare_app :
  forall t1 t2 t3 t4, length t1 = length t3 ->
                 lex_compare (t1 ++ t2) (t3 ++ t4) = match lex_compare t1 t3 with Eq => lex_compare t2 t4 | c => c end.
Proof.
  induction t1.
  - intros t2 t3 t4 H. destruct t3; simpl in *; auto; lia.
  - intros t2 t3 t4 H. destruct t3; simpl in *; auto; try lia.
    rewrite IHt1; try lia.
    destruct (a ?= z); auto.
Qed.

Lemma lex_compare_reflexive :
  forall t, lex_compare t t = Eq.
Proof.
  induction t; simpl; try rewrite Z.compare_refl; auto.
Qed.



(** * Product of an affine matrix with a vector *)

Definition affine_product mat p := map (fun t => dot_product (fst t) p + (snd t)) mat.

Lemma affine_product_nil_l_eq_nil: 
  forall p,
  affine_product [] p = [].
Proof.
  simpls; trivial.
Qed.

Instance affine_product_proper : Proper (eq ==> veq ==> eq) affine_product.
Proof.
  intros m1 m2 Hm x1 x2 Hx.
  unfold affine_product. rewrite Hm. apply map_ext. intros. rewrite Hx. reflexivity.
Qed.

Definition exact_listzzs_cols (cols: nat) (listzzs: list (list Z * Z)): Prop := 
  forall listz z listzz, 
    In listzz listzzs -> 
    listzz = (listz, z) ->
    length listz = cols.   
 
(* separate the main matrix and the contant col *)
Definition separate (mat: list (list Z * Z)): (list (list Z)) * list Z :=
  (map fst mat, map snd mat).

Definition matrix_product_pure (mat1 mat2: list (list Z)): list (list Z) := 
  let cols := if (length mat2 =? 0)%nat then 0%nat else (length (nth 0 mat2 [])) in
  let BT := transpose cols mat2 in 
  map (fun row => map (fun col => dot_product row col) BT) mat1.

Example test_matrix_product_pure:
  matrix_product_pure [[1;2];[3;4]] [[1;2];[3;4]] = [[7;10];[15;22]].
Proof. simpls. reflexivity. Qed.

Definition matrix_product (mat1 mat2: list (list Z * Z)): list (list Z * Z) := 
  let (A, a) := separate mat1 in 
  let (B, b) := separate mat2 in 
  let AB := matrix_product_pure A B in 
  let Aba := affine_product mat1 b in
  List.combine AB Aba.
(* Global Opaque matrix_product. *)

Definition sample_matrix_1 := [([1;2],3);([4;5],6);([7;8],9)].
Definition sample_matrix_2 := [([1],2);([3],4)].
Definition sample_vector := [6;9].

Example test_matrix_product:
  matrix_product sample_matrix_1 sample_matrix_2
    = [([7],13); ([19],34); ([31],55)].
Proof. 
  unfold matrix_product. 
  simpls. reflexivity. Qed.

Example test_matrix_product_assoc:
  affine_product sample_matrix_1 
    (affine_product sample_matrix_2 sample_vector) 
  = affine_product (matrix_product sample_matrix_1 sample_matrix_2) 
    sample_vector.
Proof. simpls. reflexivity. Qed. 

Lemma affine_product_eq_add_vector:
  forall mat p, 
  affine_product mat p 
    = add_vector (map (fun row => dot_product row p) (map fst mat)) (map snd mat).
Proof.
  induction mat.
  {
    intros; simpls. trivial.
  }
  {
    intros; simpls. rewrite IHmat. trivial.
  }
Qed.

Lemma map_to_zero_eq_repeat_length:
  forall A (l: list A) ,
  map (fun _ => 0) l = repeat 0 (length l).
Proof.
  induction l.
  simpls; trivial.
  simpls. f_equal. trivial.
Qed.

Lemma dot_product_zip_with:
  forall a M p z l,
  length a = length M ->
  dot_product 
  (map 
    (fun row => 
      match row with 
      | [] => 0
      | a0 :: row0 => z * a0 + dot_product l row0
      end)    
    (zipWith cons a M)
  ) p = 
  z * dot_product a p + 
    dot_product (map (fun row: list Z => dot_product l row) M) p.
Proof.
  (* a, M have to be of same length *)
  induction a.
  {
    intros. simpls.
    symmetry in H. rewrite length_zero_iff_nil in H. subst; simpls.
    destruct p; trivial; lia.
  }
  {
    intros. simpls.
    assert (exists M0 M', M = M0 :: M'). {
      destruct M. simpls. lia.
      do 2 eexists; eauto.
    }
    destruct H0 as (M0 & M' & H0). subst. simpl in H. inversion H. clear H.
    simpls. destruct p eqn:Hp; simpls; try lia.
    unfold zipWith in IHa.
    rewrite IHa; trivial.
    lia.
  }
Qed.

Lemma dot_product_aBp_assoc:
  forall B a p cols,
  (forall row, In row B -> length row = cols) ->
  dot_product (map (fun col => dot_product a col) (transpose cols B)) p  
    = dot_product a (map (fun row => dot_product row p) B).
Proof.
  induction B.
  {
    intros; simpls.
    rewrite map_repeat.
    rewrite dot_product_nil_right.
    rewrite dot_product_repeat_zero_left. trivial.
  }
  {
    intros until cols. 
    intros Hlen. rename a into b0. 
    simpls.
    destruct a0 eqn:Ha0.
    - subst; simpls.
      replace ((fun col : list Z => match col with
      | [] | _ => 0
      end)) with ((fun col: list Z => 0)). 2: {
        simpls.
        eapply functional_extensionality.
        intro. destruct x; trivial.
      }
      rewrite map_to_zero_eq_repeat_length.
      rewrite dot_product_repeat_zero_left.
      trivial. 
    - (* b0 = z :: l *)
      subst; simpls.
      rewrite <- IHB with (cols:=cols).
      eapply dot_product_zip_with.
      + 
        rewrite transpose_length.
        -- pose proof Hlen b0. eapply H. left; trivial. 
        -- intros. pose proof Hlen t. 
          assert (length t = cols). {eapply H0. right; trivial. }
          lia.
      + 
        intros.
        pose proof Hlen row. eapply H0. right; trivial.
  }
Qed.

Lemma map_fst_in:
  forall A B (l: list (A * B)) a,
  In a (map fst l) ->
  exists b, In (a, b) l.
Proof.
  induction l.
  {
    intros. simpls. tryfalse.
  }
  {
    intros. simpls.
    destruct H.
    subst; simpls.
    destruct a eqn:Ha. 
    - eexists; left; eauto.
    - eapply IHl in H. destruct H as (b & H).
      exists b; right; eauto.
  }
Qed.

Lemma matrix_product_assoc:
  forall m1 m2 p k2, 
  exact_listzzs_cols k2 m2 ->
  affine_product (matrix_product m1 m2) p = affine_product m1 (affine_product m2 p).
Proof. 
  induction m1.
  {
    intros. simpls. trivial.
  }
  {
    intros until k2. intros Hcolsm2. simpls. 
    pose proof IHm1 m2 p.
    unfold matrix_product in H. simpl in H.
    rewrite H with (k2:=k2); trivial.
    simpls.
    destruct (length (map fst m2) =? 0)%nat eqn:Hm2len.
    {
      eapply Nat.eqb_eq in Hm2len.
      eapply length_zero_iff_nil in Hm2len. 
      eapply map_eq_nil in Hm2len. subst; simpls; trivial.
      destruct p; simpls; trivial.
    }
    {
      eapply Nat.eqb_neq in Hm2len.
      f_equal.
      simpls.
      rewrite Z.add_assoc.
      eapply Z.add_cancel_r.
      rewrite affine_product_eq_add_vector.
      rewrite add_vector_dot_product_distr_right.
      eapply Z.add_cancel_r.
      assert (length (nth 0 (map fst m2) []) = k2). {
        clear - Hm2len Hcolsm2.
        destruct (map fst m2) eqn:Hm2; simpls; tryfalse.
        unfold exact_listzzs_cols in Hcolsm2. 
        assert (In l (map fst m2)). {
          rewrite Hm2. eapply in_eq.
        }
        eapply map_fst_in in H; eauto.
        destruct H as (b & H).
        eapply Hcolsm2; eauto.
      }
      rewrite H0.
      rewrite dot_product_aBp_assoc; trivial.
      clear - Hcolsm2.
      intros. unfold exact_listzzs_cols in Hcolsm2.
      intros.
      eapply map_fst_in in H.
      destruct H as (b & H).
      eapply Hcolsm2 in H; eauto.
    }
  }
Qed.

Lemma matrix_product_pure_cols:
  forall m1 m2 m3 k2,
    (length m2 > 0)%nat ->
    (forall row2, In row2 m2 -> length row2 = k2) ->
    matrix_product_pure m1 m2 = m3 ->
    (forall row3, In row3 m3 -> length row3 = k2).
Proof.
  intros until k2. intros Hlenm2 H Hprod.
  pose proof Hprod as Gprod.
  unfold matrix_product_pure in Hprod.
  intros row3 Hin3. 
  (* intros row3 Hin3.  *)
  pose proof Hin3 as Gin3.
  rewrite <- Hprod in Hin3. 
  rewrite in_map_iff in Hin3.
  destruct Hin3 as (row & H1 & Hrow).
  rewrite <- H1.
  rewrite map_length.
  destruct (length m2 =? 0)%nat eqn:Hchecklenm2; simpls.
  - eapply Nat.eqb_eq in Hchecklenm2. 
    eapply length_zero_iff_nil in Hchecklenm2. 
    subst; simpls. lia.
  -
    rewrite H; simpls.
    2: {
      destruct m2 eqn:Hm2; tryfalse; simpls. left; trivial.
    }
    pose proof @transpose_length Z k2 m2.
    eapply H0; eauto. 
    intros. eapply H in H2. lia.
Qed.

Lemma matrix_product_cols_0:
  forall m1, 
  exact_listzzs_cols 0 (matrix_product m1 []).
Proof.
  induction m1.
  {
    intros. unfold matrix_product. simpls. unfold exact_listzzs_cols.
    intros; tryfalse.
  }
  {
    unfold matrix_product. simpls. unfold exact_listzzs_cols.
    intros. inversion H; simpls; eauto; tryfalse. subst. inversion H1.
    trivial.
  }
Qed.

Lemma matrix_product_cols:
  forall m1 m2 k2, 
  (length m2 > 0)%nat ->
  exact_listzzs_cols k2 m2 -> 
  exact_listzzs_cols (k2) (matrix_product m1 m2).
Proof.
  intros.
  unfold matrix_product.
  simpls. unfolds exact_listzzs_cols.
  intros until listzz. intros Hin Hlistzz.  
  rewrite Hlistzz in Hin.
  eapply in_combine_l in Hin.
  eapply matrix_product_pure_cols 
    with (m2:=(map fst m2)) in Hin; eauto.
  - rewrite map_length; trivial.
  -  
    intros.  
    rewrite in_map_iff in H1. destruct H1 as [v [H1 H2]].
    destruct v eqn:Hv. simpls. subst. 
    eapply H0; eauto. 
Qed.

(** * Resizing a vector to a fixed size *)
Fixpoint resize (d : nat) (l : list Z) :=
  match d with
  | O => nil
  | S d => match l with nil => 0 :: resize d nil | x :: l => x :: resize d l end
  end.

Theorem resize_length :
  forall d l, length (resize d l) = d.
Proof.
  induction d; destruct l; simpl; auto.
Qed.
Hint Immediate resize_length.
Hint Rewrite resize_length : vector.

Theorem resize_nil_null :
  forall d, is_null (resize d nil) = true.
Proof.
  induction d; auto.
Qed.
Hint Immediate resize_nil_null.
Hint Rewrite resize_nil_null : vector.

Theorem resize_eq :
  forall d l, (length l <= d)%nat -> resize d l =v= l.
Proof.
  induction d.
  - intros l H; destruct l; simpl in *; [reflexivity | lia].
  - intros l H; destruct l; simpl in *.
    + rewrite <- is_eq_veq. apply resize_nil_null.
    + rewrite IHd; [reflexivity | lia].
Qed.

Theorem resize_skipn_eq :
  forall d l, resize d l ++ skipn d l =v= l.
Proof.
  induction d.
  - intros l; reflexivity.
  - intros l; destruct l; simpl in *.
    + rewrite app_nil_r; rewrite <- is_eq_veq; apply resize_nil_null.
    + rewrite IHd. reflexivity.
Qed.

Lemma resize_app :
  forall n p q, length p = n -> resize n (p ++ q) = p.
Proof.
  induction n.
  - intros; destruct p; simpl in *; auto; lia.
  - intros p q Hlength; destruct p; simpl in *.
    + lia.
    + rewrite IHn; auto.
Qed.

Lemma resize_app_le :
  forall n p q, (length p <= n)%nat -> resize n (p ++ q) = p ++ resize (n - length p)%nat q.
Proof.
  induction n.
  - intros p q H. destruct p; simpl in *; [auto | lia].
  - intros p q H. destruct p; simpl in *; [|rewrite IHn by lia]; reflexivity.
Qed.

Lemma resize_app_ge :
  forall n v1 v2, (n <= length v1)%nat -> resize n (v1 ++ v2) = resize n v1.
Proof.
  induction n.
  - intros; simpl in *; auto.
  - intros; destruct v1; simpl in *; [|rewrite IHn]; auto; lia.
Qed.

Lemma resize_null_repeat :
  forall n l, is_null l = true -> resize n l = repeat 0 n.
Proof.
  induction n.
  - intros; simpl; auto.
  - intros l H; destruct l; simpl in *.
    + rewrite IHn; auto.
    + reflect. destruct H.
      rewrite IHn; [congruence | auto].
Qed.

Lemma resize_eq_compat :
  forall n l1 l2, is_eq l1 l2 = true -> resize n l1 = resize n l2.
Proof.
  induction n.
  - intros; simpl; auto.
  - intros l1 l2 H.
    destruct l1; destruct l2; simpl in *; reflect; auto; destruct H as [H1 H2]; rewrite <- ?is_eq_veq in H2; 
      f_equal; auto; apply IHn; [rewrite is_eq_nil_left | rewrite is_eq_nil_right]; auto.
Qed.

Instance resize_proper : Proper (eq ==> veq ==> eq) resize.
Proof.
  intros n1 n2 Hn l1 l2 Hl. rewrite Hn. apply resize_eq_compat. rewrite is_eq_veq. auto.
Qed.

Lemma resize_resize :
  forall n m l, (n <= m)%nat -> resize n (resize m l) = resize n l.
Proof.
  induction n.
  - intros m l H. reflexivity.
  - intros m l H. destruct m as [|m]; [lia|].
    destruct l; simpl; rewrite IHn by lia; reflexivity.
Qed.

Lemma resize_length_eq :
  forall n l, length l = n -> resize n l = l.
Proof.
  induction n; intros; destruct l; simpl in *; f_equal; auto; lia.
Qed.

Lemma nth_resize :
  forall n k v, nth k (resize n v) 0 = if (k <? n)%nat then nth k v 0 else 0.
Proof.
  induction n.
  - intros k v; destruct k; auto.
  - intros k v; destruct k; destruct v; simpl; auto;
      replace (S k <? S n)%nat with (k <? n)%nat by (rewrite eq_iff_eq_true; reflect; lia); rewrite IHn; destruct k; reflexivity.
Qed.

Lemma resize_1 :
  forall v, resize 1 v = nth 0 v 0 :: nil.
Proof.
  intros v; destruct v; auto.
Qed.


(** * Alternative formulation of previous results that used [++] on both sides *)

Lemma dot_product_app_left :
  forall l1 l2 l3, dot_product (l1 ++ l2) l3 = dot_product l1 (resize (length l1) l3) + dot_product l2 (skipn (length l1) l3).
Proof.
  intros.
  erewrite <- resize_skipn_eq with (l := l3) at 1.
  rewrite dot_product_app; [reflexivity|rewrite resize_length; auto].
Qed.

Lemma dot_product_app_right :
  forall l1 l2 l3, dot_product l1 (l2 ++ l3) = dot_product (resize (length l2) l1) l2 + dot_product (skipn (length l2) l1) l3.
Proof.
  intros. rewrite dot_product_commutative. rewrite dot_product_app_left.
  f_equal; apply dot_product_commutative.
Qed.

Lemma is_eq_app_left :
  forall l1 l2 l3, is_eq (l1 ++ l2) l3 = is_eq l1 (resize (length l1) l3) && is_eq l2 (skipn (length l1) l3).
Proof.
  intros.
  erewrite <- resize_skipn_eq with (l := l3) at 1.
  rewrite is_eq_app; [reflexivity|rewrite resize_length; auto].
Qed.

Lemma is_eq_app_right :
  forall l1 l2 l3, is_eq l1 (l2 ++ l3) = is_eq (resize (length l2) l1) l2 && is_eq (skipn (length l2) l1) l3.
Proof.
  intros. rewrite is_eq_commutative. rewrite is_eq_app_left.
  f_equal; apply is_eq_commutative.
Qed.

(** * More results on dot product *)

Lemma dot_product_resize_left :
  forall t1 t2, dot_product (resize (length t2) t1) t2 = dot_product t1 t2.
Proof.
  intros t1 t2. rewrite <- app_nil_r with (l := t2) at 3. rewrite dot_product_app_right.
  rewrite dot_product_nil_right; lia.
Qed.

Lemma dot_product_resize_right :
  forall t1 t2, dot_product t1 (resize (length t1) t2) = dot_product t1 t2.
Proof.
  intros. rewrite dot_product_commutative. rewrite dot_product_resize_left.
  rewrite dot_product_commutative. auto.
Qed.

(** * Misc results *)

Lemma resize_succ :
  forall n l, resize (S n) l = resize n l ++ nth n l 0 :: nil.
Proof.
  induction n.
  - intros; destruct l; simpl; auto.
  - intros; destruct l; simpl in *; f_equal.
    + rewrite (IHn nil). destruct n; auto.
    + apply IHn.
Qed.

Theorem nth_eq :
  forall n l1 l2, l1 =v= l2 -> nth n l1 0 = nth n l2 0.
Proof.
  induction n.
  - intros l1 l2 H. rewrite <- is_eq_veq in H.
    destruct l1; destruct l2; simpl in *; reflect; auto; destruct H; auto.
  - intros l1 l2 H. rewrite <- is_eq_veq in H.
    destruct l1; destruct l2; simpl in *; reflect; auto; destruct H; auto.
    + specialize (IHn nil l2). rewrite <- is_eq_veq in IHn. rewrite <- IHn by (destruct l2; auto). destruct n; auto.
    + specialize (IHn l1 nil). rewrite <- is_eq_veq in IHn. rewrite IHn by (destruct l1; auto). destruct n; auto.
Qed.

Lemma mult_vector_resize :
  forall n k v, resize n (mult_vector k v) = mult_vector k (resize n v).
Proof.
  induction n.
  - intros; simpl in *; auto.
  - intros; simpl in *.
    destruct v; simpl in *; rewrite <- IHn; f_equal.
    lia.
Qed.

Lemma mult_vector_skipn :
  forall n k v, skipn n (mult_vector k v) = mult_vector k (skipn n v).
Proof.
  induction n.
  - intros; simpl in *; auto.
  - intros; destruct v; simpl in *; auto.
Qed.

Lemma lex_app_not_gt :
  forall env x1 x2 l1 l2, lex_compare ((env ++ (x1 :: nil)) ++ l1) ((env ++ (x2 :: nil)) ++ l2) <> Gt -> x1 <= x2.
Proof.
  intros env x1 x2 l1 l2 H.
  rewrite !lex_compare_app, lex_compare_reflexive in H by (rewrite ?app_length; reflexivity).
  simpl in H. destruct (x1 ?= x2) eqn:H12; simpl; congruence.
Qed.

Lemma lex_compare_lt_head :
  forall v1 v2, lex_compare v1 v2 = Lt -> nth 0 v1 0 <= nth 0 v2 0.
Proof.
  intros v1 v2 H.
  rewrite <- resize_skipn_eq with (d := 1%nat) (l := v1) in H.
  rewrite <- resize_skipn_eq with (d := 1%nat) (l := v2) in H.
  rewrite !resize_1 in H.
  simpl in H. destruct (nth 0 v1 0 ?= nth 0 v2 0) eqn:Hcmp; congruence.
Qed.


(** * Setting a component of a vector to a fixed value *)

Definition assign n x v :=
  resize n v ++ (x :: (skipn (S n) v)).

Lemma assign_id :
  forall k v, assign k (nth k v 0) v =v= v.
Proof.
  intros k v. unfold assign.
  rewrite <- resize_skipn_eq with (d := S k) (l := v) at 4.
  rewrite resize_succ, <- app_assoc; reflexivity.
Qed.

Lemma dot_product_assign_right :
  forall k s v1 v2, dot_product v1 (assign k s v2) = dot_product v1 v2 + nth k v1 0 * (s - nth k v2 0).
Proof.
  intros k s v1 v2.
  rewrite <- assign_id with (k := k) (v := v1) at 1 2.
  rewrite <- assign_id with (k := k) (v := v2) at 2.
  unfold assign.
  rewrite !dot_product_app by (rewrite !resize_length; reflexivity).
  simpl. nia.
Qed.

Lemma dot_product_assign_left :
  forall k s v1 v2, dot_product (assign k s v1) v2 = dot_product v1 v2 + nth k v2 0 * (s - nth k v1 0).
Proof.
  intros.
  rewrite dot_product_commutative, dot_product_assign_right, dot_product_commutative.
  reflexivity.
Qed.

Lemma dot_product_assign_right_zero :
  forall k s v1 v2, nth k v1 0 = 0 -> dot_product v1 (assign k s v2) = dot_product v1 v2.
Proof.
  intros; rewrite dot_product_assign_right; nia.
Qed.

Lemma dot_product_assign_left_zero :
  forall k s v1 v2, nth k v2 0 = 0 -> dot_product (assign k s v1) v2 = dot_product v1 v2.
Proof.
  intros; rewrite dot_product_assign_left; nia.
Qed.

Lemma assign_app_lt :
  forall n k v1 v2, (n < length v1)%nat -> assign n k (v1 ++ v2) = assign n k v1 ++ v2.
Proof.
  intros n k v1 v2 H. unfold assign.
  rewrite <- app_assoc. rewrite skipn_app_ge by lia. rewrite resize_app_ge by lia.
  reflexivity.
Qed.

Lemma assign_app_ge :
  forall n k v1 v2, (length v1 <= n)%nat -> assign n k (v1 ++ v2) = v1 ++ assign (n - length v1) k v2.
Proof.
  intros n k v1 v2 H. unfold assign.
  rewrite resize_app_le by lia. rewrite skipn_app_le by lia. rewrite <- app_assoc.
  f_equal. f_equal. f_equal. f_equal. lia.
Qed.

Lemma assign_assign :
  forall n x y v, assign n x (assign n y v) = assign n x v.
Proof.
  intros n x y v. unfold assign.
  rewrite resize_app by (apply resize_length).
  rewrite skipn_app_le by (rewrite resize_length; lia).
  rewrite resize_length. replace (S n - n)%nat with 1%nat by lia.
  reflexivity.
Qed.


(** * Expanding polyhedra *)

Definition expand_poly k pol := map (mult_constraint_cst k) pol.

Lemma expand_poly_1 :
  forall p, expand_poly 1 p = p.
Proof.
  intros p.
  unfold expand_poly. erewrite map_ext; [apply map_id|].
  apply mult_constraint_cst_1.
Qed.

Lemma expand_poly_eq :
  forall p k v, 0 < k -> in_poly (mult_vector k v) (expand_poly k p) = in_poly v p.
Proof.
  intros p k v Hk.
  unfold in_poly, expand_poly. rewrite forallb_map. apply forallb_ext.
  intros; apply mult_constraint_cst_eq; auto.
Qed.

Lemma expand_poly_comp :
  forall s t p, expand_poly s (expand_poly t p) = expand_poly (s * t) p.
Proof.
  intros. unfold expand_poly.
  rewrite map_map. apply map_ext.
  apply mult_constraint_cst_comp.
Qed.

Lemma expand_poly_app :
  forall s p1 p2, expand_poly s (p1 ++ p2) = expand_poly s p1 ++ expand_poly s p2.
Proof.
  intros s p1 p2. unfold expand_poly. rewrite map_app. reflexivity.
Qed.


(** * Size at which a vector can be truncated without change *)
(** length not counting trailing zeros *)
Fixpoint nrlength l :=
  match l with
  | nil => 0%nat
  | x :: l => let n := nrlength l in if (x =? 0) && (n =? 0)%nat then 0%nat else S n
  end.
  
Lemma nrlength_zero_null :
  forall l, nrlength l = 0%nat -> is_null l = true.
Proof.
  induction l.
  - simpl in *; auto.
  - intros H; simpl in *.
    destruct (a =? 0); simpl in *; [|congruence].
    destruct (nrlength l); simpl in *; [auto|congruence].
Qed.

Lemma nrlength_null_zero :
  forall l, is_null l = true -> nrlength l = 0%nat.
Proof.
  induction l.
  - simpl; auto.
  - intros H; simpl in *; reflect; destruct H as [H1 H2]; rewrite IHl by auto; rewrite H1; reflexivity.
Qed.

Lemma nrlength_zero_null_iff :
  forall l, nrlength l = 0%nat <-> is_null l = true.
Proof.
  intros l; split; [apply nrlength_zero_null | apply nrlength_null_zero].
Qed.

Lemma nrlength_le_length:
  forall l,
    Nat.le (nrlength l) (length l).
Proof.
  induction l.
  - simpls. lia.
  - simpls. destruct a; simpls; try lia.
    destruct (nrlength l) eqn:Hnr; simpls; try lia.
Qed.

Lemma nrlength_def :
  forall l n, resize n l =v= l <-> (nrlength l <= n)%nat.
Proof.
  induction l.
  - intros n; simpl in *. split; intros; [lia|].
    rewrite <- is_eq_veq. rewrite is_eq_nil_right. apply resize_nil_null.
  - intros n. rewrite <- is_eq_veq. destruct n.
    + simpl in *. destruct (a =? 0); simpl; [|split; intros; [congruence|lia]].
      rewrite <- nrlength_zero_null_iff.
      destruct (nrlength l); simpl in *; split; intros; lia.
    + simpl. rewrite Z.eqb_refl. simpl. rewrite is_eq_veq. rewrite IHl.
      case_if eq H; reflect; lia.
Qed.

Lemma nrlength_eq :
  forall l, resize (nrlength l) l =v= l.
Proof.
  intros; rewrite nrlength_def; lia.
Qed.

Lemma nrlength_def_impl :
  forall l n, (nrlength l <= n)%nat -> resize n l =v= l.
Proof.
  intros; rewrite nrlength_def; auto.
Qed.

Lemma firstn_eq_implies_resize_n_eq:
  forall n l1 l',
    firstn n l1 = l' ->
    is_eq (resize n l1) l' = true.
Proof.
  induction n.
  - intros; simpl in H. rewrite <- H. trivial.
  - intros; simpl in *. 
    destruct l1 eqn:Hl1; simpl in *; subst; try discriminate.
    eapply resize_nil_null.
    rewrite andb_true_iff. split; try lia.
    eapply IHn; trivial.
Qed.


Instance nrlength_proper: Proper (veq ==> eq) nrlength.
Proof.
  Transparent veq.
  intros p1 p2. revert p1 p2. 
  induction p1. 
  - intros. unfold veq in H. rewrite is_eq_nil_left in H. 
    eapply nrlength_null_zero in H. simpls. rewrite H; trivial.
  - intros. simpls.
    destruct p2 eqn:Hp2.
    + 
      unfold veq in H. rewrite is_eq_nil_right in H. simpls.
      rewrite andb_true_iff in H. destruct H.
      rewrite H.
      rewrite andb_true_l. eapply nrlength_null_zero in H0. rewrite H0. simpl; trivial.
    + 
      simpls. rename a into a1; rename z into a2; rename p1 into p1'; rename l into p2'.
      unfold veq in H. simpls. 
      rewrite andb_true_iff in H. destruct H.
      eapply Z.eqb_eq in H. subst. eapply IHp1 in H0. rewrite H0.
      destruct ((a2 =? 0)%Z && (nrlength p2' =? 0)%nat) eqn:Hcond; trivial.
  Opaque veq.
Qed.

Lemma dot_product_nrlength_right :
  forall v1 v2 n, (nrlength v1 <= n)%nat -> dot_product v1 (resize n v2) = dot_product v1 v2.
Proof.
  intros v1 v2 n H. rewrite <- (nrlength_def_impl v1 n) by auto.
  rewrite <- dot_product_resize_right with (t2 := v2). rewrite resize_length. reflexivity.
Qed.

Lemma dot_product_nrlength_left :
  forall v1 v2 n, (nrlength v2 <= n)%nat -> dot_product (resize n v1) v2 = dot_product v1 v2.
Proof.
  intros v1 v2 n H. rewrite dot_product_commutative. rewrite dot_product_nrlength_right by auto.
  apply dot_product_commutative.
Qed.

Lemma satisfies_constraint_nrlength :
  forall p c n, (nrlength (fst c) <= n)%nat -> satisfies_constraint (resize n p) c = satisfies_constraint p c.
Proof.
  intros p c n H. unfold satisfies_constraint.
  rewrite dot_product_nrlength_left; auto.
Qed.

Lemma nrlength_mult :
  forall k v, k <> 0 -> nrlength (mult_vector k v) = nrlength v.
Proof.
  intros k. induction v.
  - simpl; auto.
  - intros; simpl. rewrite IHv by auto.
    replace (k * a =? 0) with (a =? 0); [reflexivity|].
    rewrite eq_iff_eq_true; reflect; nia.
Qed.

Lemma nrlength_skipn :
  forall n p, nrlength (skipn n p) = (nrlength p - n)%nat.
Proof.
  induction n.
  - intros; simpl; lia.
  - intros [|x p]; simpl; [reflexivity|]. rewrite IHn.
    case_if eq H; reflect; lia.
Qed.

Lemma nrlength_cons :
  forall x p, (nrlength (x :: p) <= S (nrlength p))%nat.
Proof.
  intros; simpl. case_if; lia.
Qed.

Lemma nrlength_app :
  forall p q, (nrlength (p ++ q) <= length p + nrlength q)%nat.
Proof.
  induction p.
  - intros; simpl; auto.
  - intros; simpl; specialize (IHp q). case_if; lia.
Qed.

(** * Size at which a polyhedron can be truncated without change *)

Definition poly_nrl (pol : polyhedron) := list_max (map (fun c => nrlength (fst c)) pol).

Lemma in_poly_nrlength :
  forall p pol n, (poly_nrl pol <= n)%nat -> in_poly (resize n p) pol = in_poly p pol.
Proof.
  intros p pol n H.
  unfold in_poly. rewrite eq_iff_eq_true, !forallb_forall. apply forall_ext.
  intros c.
  enough (In c pol -> satisfies_constraint (resize n p) c = satisfies_constraint p c) by (intuition congruence).
  intros Hin. apply satisfies_constraint_nrlength.
  eapply list_max_le; [exact H|]. rewrite in_map_iff. exists c. auto.
Qed.

Lemma expand_poly_nrl :
  forall k p, k <> 0 -> poly_nrl (expand_poly k p) = poly_nrl p.
Proof.
  intros k p H. unfold poly_nrl, expand_poly.
  rewrite map_map. f_equal.
Qed.

Lemma poly_nrl_def :
  forall n pol, (forall c, In c pol -> fst c =v= resize n (fst c)) <-> (poly_nrl pol <= n)%nat.
Proof.
  intros n pol. unfold poly_nrl. rewrite list_max_le_iff. split.
  - intros H x Hin. rewrite in_map_iff in Hin. destruct Hin as [c [Hlen Hin]].
    rewrite <- Hlen, <- nrlength_def. symmetry; auto.
  - intros H c Hin. symmetry; rewrite nrlength_def. apply H.
    rewrite in_map_iff; exists c; auto.
Qed.

Lemma poly_nrl_app :
  forall p q, poly_nrl (p ++ q) = Nat.max (poly_nrl p) (poly_nrl q).
Proof.
  intros p q. unfold poly_nrl.
  rewrite map_app, list_max_app. reflexivity.
Qed.

(** * Whether a variable is absent in a given polyhedron *)
(*** constraint all zero at col n *)
Definition absent_var (p : polyhedron) k :=
  forall c, In c p -> nth k (fst c) 0 = 0.

Lemma has_var_poly_nrl :
  forall n p, (poly_nrl p <= n)%nat <-> (forall k, (n <= k)%nat -> absent_var p k).
Proof.
  intros n p.
  rewrite <- poly_nrl_def. split.
  - intros H k Hnk c Hc.
    specialize (H c Hc).
    erewrite nth_eq; [|exact H].
    rewrite nth_overflow; [reflexivity|].
    rewrite resize_length; auto.
  - intros H c Hc.
    apply vector_nth_veq; intros k.
    rewrite nth_resize.
    destruct (k <? n)%nat eqn:Hnk; reflect; [reflexivity|].
    rewrite H; auto.
Qed.

Lemma absent_var_cons :
  forall k c p, nth k (fst c) 0 = 0 -> absent_var p k -> absent_var (c :: p) k.
Proof.
  intros k c p H1 H2 c1 [-> | Hc1]; auto.
Qed.

Lemma absent_var_head :
  forall k c p, absent_var (c :: p) k -> nth k (fst c) 0 = 0.
Proof.
  intros k c p H; apply H; simpl; auto.
Qed.

Lemma absent_var_tail :
  forall k c p, absent_var (c :: p) k -> absent_var p k.
Proof.
  intros k c p H c1 Hc1; apply H; simpl; auto.
Qed.


(** * Applying [resize] on all constraints of a polyhedron. *)

Definition resize_poly n (p : polyhedron) := map (fun c => (resize n (fst c), snd c)) p.
Lemma resize_poly_in :
  forall p pol n, length p = n -> in_poly p (resize_poly n pol) = in_poly p pol.
Proof.
  intros p pol n H; unfold in_poly, resize_poly.
  rewrite forallb_map. apply forallb_ext.
  intros c; unfold satisfies_constraint; f_equal. simpl.
  rewrite <- H, dot_product_resize_right. reflexivity.
Qed.

Lemma resize_poly_nrl :
  forall pol n, (poly_nrl (resize_poly n pol) <= n)%nat.
Proof.
  intros pol n. unfold poly_nrl, resize_poly. rewrite map_map. apply list_le_max.
  intros k Hk. rewrite in_map_iff in Hk; destruct Hk as [c [Hc ?]]. simpl in Hc.
  rewrite <- Hc, <- nrlength_def. rewrite resize_resize; auto. reflexivity.
Qed.

(** * Predicate testing whether all polyhedra in a list are disjoint *)

Definition all_disjoint pl :=
  forall p k1 k2 pol1 pol2,
    nth_error pl k1 = Some pol1 -> nth_error pl k2 = Some pol2 ->
    in_poly p pol1 = true -> in_poly p pol2 = true -> k1 = k2.

Lemma all_disjoint_nil :
  all_disjoint nil.
Proof.
  intros p [|k1] [|k2] ? ? ? ? ? ?; simpl in *; congruence.
Qed.

Lemma all_disjoint_cons :
  forall pol pl, all_disjoint pl -> (forall p pol1, In pol1 pl -> in_poly p pol = true -> in_poly p pol1 = true -> False) -> all_disjoint (pol :: pl).
Proof.
  intros pol pl Hdisj H p k1 k2 pol1 pol2 Hk1 Hk2 Hpol1 Hpol2.
  destruct k1 as [|k1]; destruct k2 as [|k2]; [auto| | |erewrite (Hdisj p k1 k2); eauto]; simpl in *; exfalso;
    [apply nth_error_In in Hk2|apply nth_error_In in Hk1]; eapply (H p); try congruence; eauto.
Qed.

Lemma all_disjoint_cons_rev :
  forall pol pl, all_disjoint (pol :: pl) -> all_disjoint pl /\ (forall p pol1, In pol1 pl -> in_poly p pol = true -> in_poly p pol1 = true -> False).
Proof.
  intros pol pl Hdisj.
  split.
  - intros p k1 k2 ? ? ? ? ? ?. assert (S k1 = S k2) by (eapply (Hdisj p (S k1) (S k2)); eauto). congruence.
  - intros p pol1 Hin H1 H2.
    apply In_nth_error in Hin. destruct Hin as [k Hk].
    specialize (Hdisj p 0%nat (S k) pol pol1).
    enough (0%nat = S k) by congruence.
    apply Hdisj; auto.
Qed.

Lemma all_disjoint_app :
  forall pl1 pl2, all_disjoint pl1 -> all_disjoint pl2 -> (forall p pol1 pol2, In pol1 pl1 -> In pol2 pl2 -> in_poly p pol1 = true -> in_poly p pol2 = true -> False) ->
             all_disjoint (pl1 ++ pl2).
Proof.
  induction pl1.
  - intros; simpl; auto.
  - intros pl2 H1 H2 H. simpl.
    apply all_disjoint_cons_rev in H1. simpl in H.
    apply all_disjoint_cons; [apply IHpl1; try tauto|].
    + intros; eapply H; eauto.
    + intros p pol1 Hin. rewrite in_app_iff in Hin; destruct Hin; [|eapply H; eauto].
      destruct H1 as [_ H1]; eapply H1; eauto.
Qed.

Lemma all_disjoint_flatten :
  forall pll, (forall l1, In l1 pll -> all_disjoint l1) ->
         (forall p k1 k2 l1 l2 pol1 pol2, nth_error pll k1 = Some l1 -> nth_error pll k2 = Some l2 -> In pol1 l1 -> In pol2 l2 ->
                                     in_poly p pol1 = true -> in_poly p pol2 = true -> k1 = k2) -> all_disjoint (flatten pll).
Proof.
  induction pll.
  - intros; apply all_disjoint_nil.
  - intros Hdisj Hdisj2. simpl.
    apply all_disjoint_app; [apply Hdisj; simpl; auto|apply IHpll|].
    + intros; apply Hdisj; simpl; auto.
    + intros p k1 k2 ? ? ? ? ? ? ? ? ? ?. enough (S k1 = S k2) by congruence. eapply Hdisj2; simpl in *; eauto.
    + intros p pol1 pol2 Ha Hfl Hin1 Hin2.
      rewrite flatten_In in Hfl. destruct Hfl as [u [Hinu Huin]].
      apply In_nth_error in Huin. destruct Huin as [k Hk].
      enough (0%nat = S k) by congruence. eapply Hdisj2; simpl in *; eauto.
Qed.

Lemma all_disjoint_map_filter :
  forall (A : Type) (f : A -> polyhedron) (P : A -> bool) (l : list A), all_disjoint (map f l) -> all_disjoint (map f (filter P l)).
Proof.
  intros A f P. induction l.
  - intros H; simpl in *; auto.
  - intros H; simpl in *.
    apply all_disjoint_cons_rev in H. destruct H as [H1 H2].
    destruct (P a).
    + simpl. apply all_disjoint_cons; [auto|].
      intros p pol1 H3 H4 H5; eapply H2; eauto.
      rewrite in_map_iff; rewrite in_map_iff in H3. destruct H3 as [x H3]; exists x; rewrite filter_In in H3; tauto.
    + auto.
Qed.

(** checking an matrix, every rows have length dim *)
Definition check_listzzs_cols (listzzs: list (list Z * Z)) (dim: nat) := 
  negb 
    (existsb (fun (listzz: list Z * Z) => 
      let (listz, z):= listzz in 
      negb (Nat.eqb dim (length listz))
      ) listzzs).

Lemma check_listzzs_cols_correct: 
  forall listzzs cols,
    check_listzzs_cols listzzs cols = true -> 
    exact_listzzs_cols cols listzzs.
Proof.
  intros.
  unfold check_listzzs_cols in H.
  unfold check_listzzs_cols in H.
  unfold exact_listzzs_cols.
  intros.
  eapply negb_true_iff in H.
  eapply Misc.existsb_forall with (x:=listzz) in H; eauto.
  rewrite H1 in H.
  eapply negb_false_iff in H.
  eapply Nat.eqb_eq in H.
  lia.
Qed.
    
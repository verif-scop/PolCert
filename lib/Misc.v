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
Require Import Setoid.
Require Import Permutation.

Import List.ListNotations.

Open Scope Z_scope.

(** * More properties of lists that are missing from the Coq library *)

Lemma forallb_map :
  forall A B f (g : A -> B) l, forallb f (map g l) = forallb (fun x => f (g x)) l.
Proof.
  intros. induction l; simpl; auto; congruence.
Qed.

Lemma forallb_ext :
  forall A f g (l : list A), (forall x, f x = g x) -> forallb f l = forallb g l.
Proof.
  intros. induction l; simpl; auto; congruence.
Qed.

Lemma forallb_exists :
  forall A f (l : list A), forallb f l = false <-> exists x, In x l /\ f x = false.
Proof.
  intros A f. induction l.
  - intros; simpl. split; [congruence | intros [x Hx]; tauto].
  - simpl. rewrite andb_false_iff, IHl.
    destruct (f a) eqn:Hfa; firstorder congruence.
Qed.

Lemma existsb_forall :
  forall A f (l : list A), existsb f l = false <-> forall x, In x l -> f x = false.
Proof.
  intros A f. induction l.
  - simpl; tauto.
  - simpl. rewrite orb_false_iff, IHl.
    destruct (bool_dec (f a) false); firstorder congruence. 
Qed.

Lemma skipn_skipn :
  forall A n m (l : list A), skipn n (skipn m l) = skipn (n + m)%nat l.
Proof.
  induction m.
  - simpl. rewrite Nat.add_0_r; auto.
  - rewrite Nat.add_succ_r. destruct l; simpl.
    + destruct n; auto.
    + auto.
Qed.

Lemma skipn_app :
  forall A n (p q : list A), length p = n -> skipn n (p ++ q) = q.
Proof.
  induction n.
  - intros; destruct p; simpl in *; auto; lia.
  - intros; destruct p; simpl in *; auto; lia.
Qed.

Lemma skipn_app_le :
  forall (A : Type) n (v1 v2 : list A), (length v1 <= n)%nat -> skipn n (v1 ++ v2) = skipn (n - length v1) v2.
Proof.
  intros A n; induction n.
  - intros; simpl in *.
    destruct v1; simpl in *; auto; lia.
  - intros v1 v2 H; destruct v1.
    + reflexivity.
    + simpl in *; apply IHn; lia.
Qed.

Lemma skipn_app_ge :
  forall (A : Type) n (v1 v2 : list A), (n <= length v1)%nat -> skipn n (v1 ++ v2) = skipn n v1 ++ v2.
Proof.
  intros A n; induction n.
  - intros; simpl; auto.
  - intros; destruct v1; simpl in *; [|apply IHn]; lia.
Qed.

Lemma firstn_nth_app :
  forall A n (l : list A) d, (length l >= S n)%nat -> firstn (S n) l = firstn n l ++ (nth n l d :: nil).
Proof.
  intros A. induction n.
  - intros l d H; destruct l; simpl in *; [lia | auto].
  - intros l d H; destruct l; simpl in *; [lia |].
    erewrite IHn by lia. reflexivity.
Qed.

Lemma map_nth_error_none :
  forall A B n (f : A -> B) l, nth_error l n = None -> nth_error (map f l) n = None.
Proof.
  intros; rewrite nth_error_None in *; rewrite map_length; auto.
Qed.

Lemma nth_repeat:
  forall A (a:A) (n m:nat),
  nth n (repeat a m) a = a.
Proof.
  intros.
  revert n. induction m as [|m IHm].
  - now intros [|n].
  - intros [|n]; [reflexivity|exact (IHm n)].
Qed.

Lemma nth_error_repeat:
  forall A a (n m:nat),
  (n < m)%nat -> @nth_error A (repeat a m) n = Some a.
Proof.
  intros until m. intro Hnm. rewrite (nth_error_nth' _ a).
  - now rewrite nth_repeat.
  - now rewrite repeat_length.
Qed.

Lemma nth_error_map_iff :
  forall A B (f : A -> B) n l x, nth_error (map f l) n = Some x <-> (exists y, nth_error l n = Some y /\ x = f y).
Proof.
  intros A B f. induction n.
  - intros [|y l] x; simpl.
    + split; [congruence|firstorder congruence].
    + split; intros; [exists y|]; firstorder congruence.
  - intros [|y l] x; simpl.
    + split; [|intros [y Hy]]; intuition congruence.
    + apply IHn.
Qed.

Lemma nth_error_nth :
  forall (A : Type) n (l : list A) d x, nth_error l n = Some x -> nth n l d = x.
Proof.
  intros A; induction n.
  - intros l d x; destruct l; simpl in *; congruence.
  - intros l d x; destruct l; simpl in *; [congruence | apply IHn].
Qed.

Lemma nth_error_nth_iff :
  forall (A : Type) n (l : list A) d x, (n < length l)%nat -> nth_error l n = Some x <-> nth n l d = x.
Proof.
  intros A; induction n.
  - intros l d x Hn; destruct l; simpl in *; [lia | split; congruence].
  - intros l d x Hn; destruct l; simpl in *; [|apply IHn]; lia.
Qed.

Lemma nth_skipn :
  forall A n m (l : list A) d, nth n (skipn m l) d = nth (m + n) l d.
Proof.
  induction m.
  - intros. simpl. reflexivity.
  - intros. simpl.
    destruct l; simpl.
    + destruct n; reflexivity.
    + apply IHm.
Qed.

Theorem nth_error_combine :
  forall (A B : Type) (n : nat) (l : list A) (l' : list B) x y,
    nth_error (combine l l') n = Some (x, y) <-> nth_error l n = Some x /\ nth_error l' n = Some y.
Proof.
  induction n.
  - intros l l' x y; destruct l; destruct l'; simpl in *; split; (intros [H1 H2] || (intros H; split)); congruence.
  - intros l l' x y; destruct l; destruct l'; simpl in *; split; (intros [H1 H2] || (intros H; split)); try congruence.
    + rewrite IHn in H; destruct H; auto.
    + rewrite IHn in H; destruct H; auto.
    + rewrite IHn; auto.
Qed.

Theorem in_l_combine :
  forall (A B : Type) (l : list A) (l': list B) x,
    length l = length l' -> In x l -> (exists y, In (x, y) (combine l l')).
Proof.
  intros A B l l' x Hlen Hin. apply In_nth_error in Hin.
  destruct Hin as [n Hin].
  destruct (nth_error l' n) as [y|] eqn:Heq.
  - exists y. apply nth_error_In with (n := n). rewrite nth_error_combine. auto.
  - rewrite nth_error_None in Heq.
    assert (n < length l)%nat by (rewrite <- nth_error_Some; congruence).
    lia.
Qed.

Lemma combine_map_r :
  forall (A B C : Type) (f : B -> C) (xs : list A) (ys : list B),
    combine xs (map f ys) = map (fun u => (fst u, f (snd u))) (combine xs ys).
Proof.
  intros A B C f. induction xs.
  - intros [|y ys]; simpl; auto.
  - intros [|y ys]; simpl; f_equal; auto.
Qed.

Lemma map_combine :
  forall (A B : Type) (xs : list A) (ys : list B),
    length xs = length ys -> map fst (combine xs ys) = xs.
Proof.
  intros A B. induction xs.
  - intros [|y ys] H; simpl in *; auto.
  - intros [|y ys] H; simpl in *; [|rewrite IHxs]; congruence.
Qed.

Fixpoint flatten {A : Type} (l : list (list A)) :=
  match l with
  | nil => nil
  | a :: l => a ++ (flatten l)
  end.

Lemma flatten_app_singleton:
  forall A ll l,
    @flatten A (ll ++ [l]) = flatten ll ++ l.
Proof.
  induction ll.
  {
    intros; simpl. eapply app_nil_r.
  }
  {
    intros; simpl.
    rewrite IHll.
    simpl; eapply app_assoc.
  }
Qed.

Lemma flatten_forallb :
  forall (A : Type) (l : list (list A)) (P : A -> bool),
    forallb (forallb P) l = forallb P (flatten l).
Proof.
  induction l.
  - intros; simpl; auto.
  - intros; simpl. rewrite IHl. rewrite forallb_app. reflexivity.
Qed.

Lemma flatten_In :
  forall (A : Type) (x : A) l, In x (flatten l) <-> exists u, In x u /\ In u l.
Proof.
  intros A x l. induction l.
  - simpl; firstorder.
  - simpl. rewrite in_app_iff.
    split.
    + intros [H | H]; [exists a; auto|]. rewrite IHl in H; destruct H as [u Hu]; exists u; tauto.
    + intros [u [Hxu [Hau | Hul]]]; [left; congruence|]. right; rewrite IHl; exists u; tauto.
Qed.

Lemma flatten_map :
  forall (A B : Type) (f : A -> B) l, map f (flatten l) = flatten (map (map f) l).
Proof.
  intros A B f. induction l; simpl; auto.
  rewrite map_app, IHl; reflexivity.
Qed.

(** * Results on [Forall2] *)

Lemma Forall2_nth_error :
  forall (A B : Type) (R : A -> B -> Prop) n xs ys x, Forall2 R xs ys -> nth_error xs n = Some x -> exists y, nth_error ys n = Some y /\ R x y.
Proof.
  intros A B R. induction n.
  - intros xs ys x Hforall Hnth; destruct Hforall; simpl in *; [|exists y; split]; try congruence.
  - intros xs ys x Hforall Hnth; destruct Hforall; simpl in *; [congruence|].
    eapply IHn; eauto.
Qed.

Lemma Forall2_sym :
  forall (A B : Type) (R : A -> B -> Prop) xs ys, Forall2 R xs ys -> Forall2 (fun y x => R x y) ys xs.
Proof.
  intros A B R xs ys Hforall. induction Hforall; constructor; auto.
Qed.

Lemma Forall2_imp :
  forall (A B : Type) (R R' : A -> B -> Prop) xs ys, (forall x y, R x y -> R' x y) -> Forall2 R xs ys -> Forall2 R' xs ys.
Proof.
  intros A B R R' xs ys H Hforall. induction Hforall; constructor; auto.
Qed.

Lemma Forall2_sym_iff :
  forall (A B : Type) (R : A -> B -> Prop) xs ys, Forall2 R xs ys <-> Forall2 (fun y x => R x y) ys xs.
Proof.
  intros A B R xs ys. split.
  - apply Forall2_sym.
  - intros H; apply Forall2_sym in H. eapply Forall2_imp; eauto.
Qed.

Lemma Forall2_map_left :
  forall (A B C : Type) (R : B -> C -> Prop) (f : A -> B) xs ys, Forall2 R (map f xs) ys <-> Forall2 (fun x y => R (f x) y) xs ys.
Proof.
  intros A B C R f xs ys. split.
  - intros H. remember (map f xs) as zs; generalize xs Heqzs; clear xs Heqzs. induction H.
    + intros xs; destruct xs; simpl in *; intros; [constructor|congruence].
    + intros xs; destruct xs; simpl in *; [congruence|].
      intros; constructor; [|apply IHForall2]; congruence.
  - intros H; induction H; simpl in *; econstructor; auto.
Qed.

Lemma Forall2_map_right :
  forall (A B C : Type) (R : A -> C -> Prop) (f : B -> C) xs ys, Forall2 R xs (map f ys) <-> Forall2 (fun x y => R x (f y)) xs ys.
Proof.
  intros A B C R f xs ys.
  rewrite Forall2_sym_iff, Forall2_map_left, Forall2_sym_iff.
  reflexivity.
Qed.

Lemma Forall2_R_refl :
  forall (A : Type) (R : A -> A -> Prop) xs, (forall x, R x x) -> Forall2 R xs xs.
Proof.
  intros A R; induction xs.
  - intros; constructor.
  - intros; constructor; auto.
Qed.

Lemma Forall2_length :
  forall (A B : Type) (R : A -> B -> Prop) (xs : list A) (ys : list B), Forall2 R xs ys -> length xs = length ys.
Proof.
  intros A B R xs ys H. induction H; simpl; auto.
Qed.


(** * Tactics for rewriting under binders *)

Definition helper_lemma : forall P Q, P -> Q -> Q :=
  fun P Q _ Q_proof => Q_proof.

Ltac under_binder vartype tacr tac :=
  let f := fresh "f" in
  let H := fresh "H" in
  let var := fresh "x" in
  evar (f : vartype -> Prop);
  tacr f; [|intro var; tac var; match goal with |- ?P <-> ?Q => apply (helper_lemma (Q -> P)) end; [intro H; pattern var; exact H|]; reflexivity];
  unfold f in *;
  clear f.

Lemma forall_ext :
  forall (A : Type) (P Q : A -> Prop), (forall x, P x <-> Q x) -> (forall x, P x) <-> (forall x, Q x).
Proof.
  intros A P Q H; split; intros; [rewrite <- H|rewrite H]; auto.
Qed.

Lemma exists_ext :
  forall (A : Type) (P Q : A -> Prop), (forall x, P x <-> Q x) -> (exists x, P x) <-> (exists x, Q x).
Proof.
  intros A P Q H; split; intros [x Hx]; exists x; [rewrite <- H|rewrite H]; auto.
Qed.

Ltac under_forall vartype tac :=
  under_binder vartype ltac:(fun f => rewrite forall_ext with (Q := f)) tac.
Ltac under_exists vartype tac :=
  under_binder vartype ltac:(fun f => rewrite exists_ext with (Q := f)) tac.
Ltac under_forall_in H vartype tac :=
  under_binder vartype ltac:(fun f => rewrite forall_ext with (Q := f) in H) tac.
Ltac under_exists_in H vartype tac :=
  under_binder vartype ltac:(fun f => rewrite exists_ext with (Q := f) in H) tac.


(** * The [reflect] tactic *)

Hint Rewrite andb_true_iff andb_false_iff orb_true_iff orb_false_iff negb_true_iff negb_false_iff: reflect.
Hint Rewrite Z.eqb_eq Z.leb_le Z.eqb_neq Z.leb_gt Z.ltb_lt Z.ltb_ge Z.gtb_ltb Z.geb_leb Z.compare_eq_iff Z.compare_lt_iff Z.compare_gt_iff : reflect.
Hint Rewrite Nat.eqb_eq Nat.leb_le Nat.eqb_neq Nat.leb_gt Nat.ltb_lt Nat.ltb_ge : reflect.

Ltac reflect := autorewrite with reflect in *.
Ltac reflect_binders :=
  repeat (
      autorewrite with reflect in *;
      try match goal with
          | [ |- context [forallb ?f1 ?l1 = true] ] =>
            (rewrite forallb_forall with (f := f1) (l := l1);
             let typ := match (type of f1) with (?A -> bool) => A end in
             under_forall typ ltac:(fun _ => reflect_binders)
            )
          | [ H : context [forallb ?f1 ?l1 = true] |- _] =>
            (rewrite forallb_forall with (f := f1) (l := l1) in H;
             let typ := match (type of f1) with (?A -> bool) => A end in
             under_forall_in H typ ltac:(fun _ => reflect_binders)
            )
          | [ |- context [existsb ?f1 ?l1 = true] ] =>
            (rewrite existsb_exists with (f := f1) (l := l1);
             let typ := match (type of f1) with (?A -> bool) => A end in
             under_exists typ ltac:(fun _ => reflect_binders)
            )
          | [ H : context [existsb ?f1 ?l1 = true] |- _] =>
            (rewrite existsb_exists with (f := f1) (l := l1) in H;
             let typ := match (type of f1) with (?A -> bool) => A end in
             under_exists_in H typ ltac:(fun _ => reflect_binders)
            )
          end
    ).


Lemma test1:
  forall l, (forallb (fun x => x =? 0) l = true <-> (forall x, In x l -> x = 0)).
Proof.
  intros l.
  reflect_binders.
  reflexivity.
Qed.

Lemma test2:
  (forall (x y : Z), (x =? y) = true) <-> (forall (x y : Z), x = y).
Proof.
  under_forall Z ltac:(fun _ => under_forall Z ltac:(fun _ => reflect)).
  reflexivity.
Qed.

Lemma test3:
  forall l1 l2, forallb (fun x => existsb (fun y => x =? y) l1) l2 = true <->
           forall x, In x l2 -> exists y, In y l1 /\ x = y.
Proof.
  intros l1 l2.
  reflect_binders. reflexivity.
Qed.

(** * Handlings [if]s *)

Tactic Notation "case_if" "in" hyp(H) :=
  lazymatch goal with
    | [ H : context[if ?X then _ else _] |- _ ] => destruct X
  end.

Tactic Notation "case_if" "in" hyp(H) "as" simple_intropattern(Has) :=
  lazymatch goal with
    | [ H : context[if ?X then _ else _] |- _ ] => destruct X as Has
  end.

Tactic Notation "case_if" "in" hyp(H) "eq" ident(Heq) :=
  lazymatch goal with
    | [ H : context[if ?X then _ else _] |- _ ] => destruct X eqn:Heq
  end.

Tactic Notation "case_if" "in" hyp(H) "as" simple_intropattern(Has) "eq" ident(Heq) :=
  lazymatch goal with
    | [ H : context[if ?X then _ else _] |- _ ] => destruct X as Has eqn:Heq
  end.

Tactic Notation "case_if" :=
  lazymatch goal with
    | [ |- context[if ?X then _ else _] ] => destruct X
  end.

Tactic Notation "case_if" "as" simple_intropattern(Has) :=
  lazymatch goal with
    | [ |- context[if ?X then _ else _] ] => destruct X as Has
  end.

Tactic Notation "case_if" "eq" ident(Heq) :=
  lazymatch goal with
    | [ |- context[if ?X then _ else _] ] => destruct X eqn:Heq
  end.

Tactic Notation "case_if" "as" simple_intropattern(Has) "eq" ident(Heq) :=
  lazymatch goal with
    | [ |- context[if ?X then _ else _] ] => destruct X as Has eqn:Heq
  end.

(** * Integer ranges *)

Fixpoint n_range (n : nat) :=
  match n with
  | O => nil
  | S n => (n_range n) ++ (n :: nil)
  end.

Lemma n_range_in :
  forall n m, In m (n_range n) <-> (m < n)%nat.
Proof.
  induction n.
  - intros. simpl in *. split; [intro; exfalso; auto | apply Nat.nlt_0_r].
  - intros m. simpl in *. split.
    + intros H. apply in_app_or in H. destruct H as [H | H].
      * rewrite IHn in H. lia.
      * simpl in H. destruct H; [lia | exfalso; auto].
    + intros H. apply in_or_app. destruct (Nat.eq_dec n m).
      * right; simpl; auto.
      * left; rewrite IHn; lia.
Qed.

Lemma n_range_begin :
  forall n, n_range (S n) = 0%nat :: (map S (n_range n)).
Proof.
  induction n.
  - simpl in *. auto.
  - simpl in *. rewrite IHn at 1. simpl.
    f_equal. rewrite map_app. simpl. reflexivity.
Qed.

Lemma n_range_length :
  forall n, length (n_range n) = n.
Proof.
  induction n.
  - simpl; auto.
  - simpl; rewrite app_length, IHn; simpl; lia.
Qed.

Lemma n_range_nth_error :
  forall n m x, nth_error (n_range n) m = Some x <-> ((m < n)%nat /\ x = m).
Proof.
  induction n.
  - intros; simpl. destruct m; simpl; split; (congruence || lia).
  - intros m x; simpl.
    destruct ((m <? n)%nat) eqn:Hnm; reflect.
    + rewrite nth_error_app1 by (rewrite n_range_length; lia). rewrite IHn; lia.
    + rewrite nth_error_app2 by (rewrite n_range_length; lia). rewrite n_range_length.
      destruct (m - n)%nat as [|u] eqn:Hmn; simpl.
      * replace m with n by lia. intuition (congruence || lia).
      * destruct u; simpl; intuition (congruence || lia).
Qed.

Lemma combine_n_range_in :
  forall (A : Type) (k : nat) (l : list A) (x : A),
    In (x, k) (combine l (n_range (length l))) <-> nth_error l k = Some x.
Proof.
  intros A. induction k.
  - intros [|y l] x.
    + simpl. split; intros; [tauto | congruence].
    + replace (length (y :: l)) with (S (length l)) by reflexivity.
      rewrite n_range_begin. simpl.
      split; [|intros; left; congruence].
      intros [H | H]; [congruence|]. exfalso.
      apply in_combine_r in H. rewrite in_map_iff in H. destruct H as [? [? _]]; congruence.
  - intros [|y l] x.
    + simpl. split; intros; [tauto | congruence].
    + replace (length (y :: l)) with (S (length l)) by reflexivity.
      rewrite n_range_begin. simpl.
      rewrite <- IHk, combine_map_r, in_map_iff. split.
      * intros [H | [[x1 k1] [Hxk Hin]]]; [congruence|].
        simpl in *. congruence.
      * intros H; right; exists (x, k); auto.
Qed.

Lemma n_range_NoDup :
  forall n, NoDup (n_range n).
Proof.
  induction n.
  - constructor.
  - simpl. rewrite NoDup_Add; [|apply Add_app].
    rewrite app_nil_r. split; [auto|].
    rewrite n_range_in. lia.
Qed.

Definition Zrange lb ub := map (fun n => lb + Z.of_nat n) (n_range (Z.to_nat (ub - lb))).

Lemma Zrange_empty :
  forall lb ub, lb >= ub -> Zrange lb ub = nil.
Proof.
  intros lb ub H. unfold Zrange.
  assert (H1 : Z.to_nat (ub - lb) = 0%nat).
  { destruct (ub - lb) eqn:Hdiff; (reflexivity || lia). }
  rewrite H1. reflexivity.
Qed.

Lemma Zrange_begin :
  forall lb ub, lb < ub -> Zrange lb ub = lb :: Zrange (lb + 1) ub.
Proof.
  intros lb ub H. unfold Zrange.
  assert (H1 : Z.to_nat (ub - lb) = S (Z.to_nat (ub - (lb + 1)))).
  { rewrite <- Z2Nat.inj_succ by lia. f_equal. lia. }
  rewrite H1. rewrite n_range_begin. simpl. f_equal.
  - lia.
  - rewrite map_map; apply map_ext. intro; lia.
Qed.

Lemma Zrange_end :
  forall lb ub, lb < ub -> Zrange lb ub = Zrange lb (ub - 1) ++ ((ub - 1) :: nil).
Proof.
  intros lb ub H. unfold Zrange.
  assert (H1 : Z.to_nat (ub - lb) = S (Z.to_nat (ub - (lb + 1)))).
  { rewrite <- Z2Nat.inj_succ by lia. f_equal. lia. }
  rewrite H1. simpl. rewrite map_app. simpl. f_equal.
  - f_equal. f_equal. f_equal. lia.
  - f_equal. rewrite Z2Nat.id; lia.
Qed.

Lemma Zrange_in :
  forall lb ub n, In n (Zrange lb ub) <-> lb <= n < ub.
Proof.
  intros lb ub n.
  unfold Zrange. rewrite in_map_iff. split.
  - intros [x [Hx1 Hx2]]; rewrite n_range_in in Hx2.
    apply Nat2Z.inj_lt in Hx2.
    rewrite Z2Nat.id in Hx2; [lia|].
    destruct (ub - lb); simpl in *; lia.
  - intros H. exists (Z.to_nat (n - lb)). split.
    + rewrite Z2Nat.id; lia.
    + rewrite n_range_in. apply Z2Nat.inj_lt; lia.
Qed.

Lemma Zrange_nth_error :
  forall n x lb ub, nth_error (Zrange lb ub) n = Some x <-> (lb <= x < ub /\ x = lb + Z.of_nat n).
Proof.
  intros n x lb ub. unfold Zrange.
  rewrite nth_error_map_iff.
  under_exists nat ltac:(fun _ => rewrite n_range_nth_error).
  setoid_replace (n < Z.to_nat (ub - lb))%nat with (Z.of_nat n < ub - lb) using relation iff; [firstorder lia|].
  destruct (ub - lb); simpl; lia.
Qed.

Lemma Zrange_single :
  forall x, Zrange x (x + 1) = (x :: nil).
Proof.
  intros x. unfold Zrange.
  replace (x + 1 - x) with 1 by lia. simpl.
  f_equal. lia.
Qed.

(** * Results on integer division *)

Lemma div_lt_iff :
  forall x y z, 0 < y -> x / y < z <-> x < y * z.
Proof.
  intros x y z Hy; split; intro H.
  - apply Z.nle_gt; intro H2. apply Z.div_le_lower_bound in H2; lia.
  - apply Z.div_lt_upper_bound; auto.
Qed.

Lemma div_le_iff :
  forall x y z, 0 < y -> x / y <= z <-> x <= y * z + y - 1.
Proof.
  intros x y z Hy. rewrite <- Z.lt_succ_r. rewrite div_lt_iff by lia. nia.
Qed.

Lemma div_ge_iff :
  forall x y z, 0 < z -> x <= y / z <-> x * z <= y.
Proof.
  intros x y z Hz. rewrite <- !Z.nlt_ge. apply not_iff_compat. rewrite div_lt_iff by lia. nia.
Qed.

Lemma div_gt_iff :
  forall x y z, 0 < z -> x < y / z <-> x * z + z - 1 < y.
Proof.
  intros x y z Hz. rewrite <- !Z.nle_gt. apply not_iff_compat. rewrite div_le_iff by lia. nia.
Qed.

(** * Maximum of lists of [nat] *)

Fixpoint list_max l :=
  match l with
  | nil => 0%nat
  | x :: l => Nat.max x (list_max l)
  end.

Theorem list_max_le :
  forall l n, (list_max l <= n -> (forall x, In x l -> x <= n))%nat.
Proof.
  induction l; simpl in *.
  - intros; exfalso; auto.
  - intros n H x [Ha | Hl].
    + lia.
    + apply IHl; auto; lia.
Qed.

Theorem list_le_max :
  forall l n, (forall x, In x l -> x <= n)%nat -> (list_max l <= n)%nat.
Proof.
  induction l; simpl in *.
  - intros; lia.
  - intros n H. apply Nat.max_lub.
    + apply H; auto.
    + apply IHl; intros; apply H; auto.
Qed.

Theorem list_max_le_iff :
  forall l n, (list_max l <= n <-> (forall x, In x l -> x <= n))%nat.
Proof.
  intros l n; split; [apply list_max_le | apply list_le_max].
Qed.

Lemma list_max_ge :
  forall l x, In x l -> (x <= list_max l)%nat.
Proof.
  induction l.
  - intros; simpl in *; tauto.
  - intros x H; simpl in *; destruct H as [H | H]; [|specialize (IHl x H)]; lia.
Qed.

Lemma list_max_app :
  forall p q, list_max (p ++ q) = Nat.max (list_max p) (list_max q).
Proof.
  induction p; intros; simpl in *; [reflexivity|rewrite IHp]; lia.
Qed.

(** * Extra results on [gcd] on [positive] *)

Definition flip_ggcd (gg : positive * (positive * positive)) := (fst gg, (snd (snd gg), fst (snd gg))).

Lemma ggcdn_comm :
  forall n a b, Pos.ggcdn n b a = flip_ggcd (Pos.ggcdn n a b).
Proof.
  induction n.
  - intros; simpl; auto.
  - intros; destruct a; destruct b; simpl; try reflexivity;
      [rewrite Pos.compare_antisym; destruct (a ?= b)%positive eqn:Hab| | |];
      try (rewrite IHn; simpl; destruct Pos.ggcdn as (g,(u,v)); simpl; reflexivity).
    simpl.
    apply Pos.compare_eq in Hab; rewrite Hab; reflexivity.
Qed.

Lemma ggcd_comm :
  forall a b, Pos.ggcd b a = flip_ggcd (Pos.ggcd a b).
Proof.
  intros a b. unfold Pos.ggcd. rewrite <- ggcdn_comm.
  f_equal. lia.
Qed.

Lemma divide_mul_cancel_l p q r : (p * q | p * r)%positive -> (q | r)%positive.
Proof.
  intros [x H]. exists x. nia.
Qed.

Lemma divide_mul2_l p q r : (q | r)%positive -> (p * q | p * r)%positive.
Proof.
  intros [x H]. exists x. nia.
Qed.

Lemma divide_mul_cancel_r p q r : (q * p | r * p)%positive -> (q | r)%positive.
Proof.
  intros [x H]. exists x. nia.
Qed.

Lemma divide_mul2_r p q r : (q | r)%positive -> (q * p | r * p)%positive.
Proof.
  intros [x H]. exists x. nia.
Qed.

Lemma divide_mul_cancel_l_iff p q r : (p * q | p * r)%positive <-> (q | r)%positive.
Proof.
  split; [apply divide_mul_cancel_l | apply divide_mul2_l].
Qed.

Lemma divide_mul_cancel_r_iff p q r : (q * p | r * p)%positive <-> (q | r)%positive.
Proof.
  split; [apply divide_mul_cancel_r | apply divide_mul2_r].
Qed.

Lemma divide_antisym p q : (p | q)%positive -> (q | p)%positive -> p = q.
Proof.
  intros [a Ha] [b Hb]. nia.
Qed.

Lemma divide_refl p : (p | p)%positive.
Proof.
  exists 1%positive. lia.
Qed.

Lemma divide_trans p q r : (p | q)%positive -> (q | r)%positive -> (p | r)%positive.
Proof.
  intros [x Hx] [y Hy]; exists (x * y)%positive; nia.
Qed.

Lemma gcd_spec a b p : (forall q, ((q | a)%positive /\ (q | b)%positive) <-> (q | p)%positive) <-> p = Pos.gcd a b.
Proof.
  split.
  - intros Hg. 
    apply divide_antisym.
    + generalize (divide_refl p). intros H; rewrite <- Hg in H; destruct H. apply Pos.gcd_greatest; auto.
    + apply Hg; split; [apply Pos.gcd_divide_l | apply Pos.gcd_divide_r].
  - intros Hp; rewrite Hp. intros q. split.
    + intros [Ha Hb]; apply Pos.gcd_greatest; auto.
    + intros Hd; split; eapply divide_trans; [exact Hd | apply Pos.gcd_divide_l | exact Hd | apply Pos.gcd_divide_r].
Qed.

Lemma gcd_mul_k k a b : (Pos.gcd (k * a) (k * b) = k * Pos.gcd a b)%positive.
Proof.
  generalize (Pos.gcd_greatest (k * a) (k * b) k)%positive. intros H; destruct H.
  - exists a; nia.
  - exists b; nia.
  - rewrite H; rewrite Pos.mul_comm. f_equal.
    symmetry in H. rewrite Pos.mul_comm in H. rewrite <- gcd_spec in H.
    rewrite <- gcd_spec. intros q. specialize (H (k * q)%positive).
    rewrite !divide_mul_cancel_l_iff in H. auto.
Qed.

Lemma gcd_greatest_mul a b k p : (p | k * a)%positive -> (p | k * b)%positive -> (p | k * Pos.gcd a b)%positive.
Proof.
  rewrite <- gcd_mul_k.
  apply Pos.gcd_greatest.
Qed.

Definition lcm a b := let '(g, (aa, bb)) := Pos.ggcd a b in (aa * b)%positive.

Lemma lcm_comm a b : lcm a b = lcm b a.
Proof.
  unfold lcm.
  generalize (Pos.ggcd_correct_divisors a b).
  rewrite ggcd_comm with (a := a) (b := b); destruct Pos.ggcd as (g, (u, v)).
  simpl. nia.
Qed.

Lemma divide_lcm_r a b : (b | lcm a b)%positive.
Proof.
  unfold lcm.
  remember (Pos.ggcd a b) as u.
  destruct u as [g [aa bb]].
  exists aa. reflexivity.
Qed.

Lemma divide_lcm_l a b : (a | lcm a b)%positive.
Proof.
  rewrite lcm_comm. apply divide_lcm_r.
Qed.

Lemma lcm_gcd_mul a b : (lcm a b * Pos.gcd a b = a * b)%positive.
Proof.
  unfold lcm.
  generalize (Pos.ggcd_correct_divisors a b).
  rewrite <- Pos.ggcd_gcd.
  destruct Pos.ggcd as (g, (u, v)); intros [Hu Hv]. simpl.
  nia.
Qed.

Lemma lcm_smallest : forall a b p, (a | p)%positive -> (b | p)%positive -> (lcm a b | p)%positive.
Proof.
  intros a b p [x Hx] [y Hy].
  apply divide_mul_cancel_r with (p := Pos.gcd a b).
  rewrite lcm_gcd_mul.
  apply gcd_greatest_mul; [exists y; rewrite Hy | exists x; rewrite Hx]; nia.
Qed.

Lemma lcm_one : forall a, lcm 1%positive a = a.
Proof.
  intros a. unfold lcm. reflexivity.
Qed.


(** * gcd of lists of [Z] *)

Fixpoint list_gcd l :=
  match l with
  | nil => 0
  | x :: l => Z.gcd x (list_gcd l)
  end.

Lemma list_gcd_nonneg :
  forall l, 0 <= list_gcd l.
Proof.
  destruct l.
  - simpl; lia.
  - simpl. apply Z.gcd_nonneg.
Qed.

Lemma list_gcd_div :
  forall l x, In x l -> (list_gcd l | x).
Proof.
  induction l.
  - intros; simpl in *; tauto.
  - intros x [Ha | Hx].
    + rewrite <- Ha. simpl. apply Z.gcd_divide_l.
    + transitivity (list_gcd l).
      * simpl; apply Z.gcd_divide_r.
      * auto.
Qed.

(** * lcm of lists of [positive] *)

Fixpoint list_lcm l :=
  match l with
  | nil => 1%positive
  | x :: l => lcm x (list_lcm l)
  end.

Lemma list_lcm_correct :
  forall x l, In x l -> (x | list_lcm l)%positive.
Proof.
  intros x l. induction l.
  - intros; simpl in *; tauto.
  - intros [Ha | Hl]; simpl in *.
    + rewrite Ha. apply divide_lcm_l.
    + eapply divide_trans; [apply IHl; auto|apply divide_lcm_r].
Qed.

(** * Decidability of [Permutation] *)

Section PermutationDec.
  Variable A : Type.
  Variable dec : forall (x y : A), {x = y} + {x <> y}.

  Fixpoint removeone (a : A) (l : list A) : option (list A) :=
    match l with
    | nil => None
    | b :: l => if dec b a then Some l else match removeone a l with None => None | Some l1 => Some (b :: l1) end
    end.

  Lemma removeone_In :
    forall a l, In a l -> exists l1 l2, removeone a l = Some (l1 ++ l2) /\ l = l1 ++ (a :: l2).
  Proof.
    induction l as [|b l IHl].
    - intros; simpl in *; tauto.
    - intros; simpl in *. destruct dec; [exists nil; exists l; simpl; split; f_equal; auto|].
      destruct IHl as [l1 [l2 [H1 H2]]]; [destruct H; congruence|].
      exists (b :: l1); exists l2; rewrite H1, H2. simpl; auto.
  Qed.

  Lemma removeone_notIn :
    forall a l, ~(In a l) -> removeone a l = None.
  Proof.
    induction l as [|b l IHl].
    - intros; simpl in *; auto.
    - intros; simpl in *; rewrite IHl; auto.
      destruct dec; intuition.
  Qed.

  Lemma removeone_None :
    forall a l, removeone a l = None -> ~(In a l).
  Proof.
    intros a l H1 H2; apply removeone_In in H2.
    destruct H2 as [? [? [? ?]]]; congruence.
  Qed.

  Lemma removeone_Some :
    forall a l1 l2, removeone a l1 = Some l2 -> exists l3 l4, l2 = l3 ++ l4 /\ l1 = l3 ++ (a :: l4).
  Proof.
    intros a l1 l2 H.
    destruct (In_dec dec a l1) as [Hin | Hin]; [apply removeone_In in Hin|apply removeone_notIn in Hin; congruence].
    destruct Hin as [l3 [l4 [H1 H2]]]; exists l3; exists l4; split; congruence.
  Qed.

  Lemma removeone_Permutation :
    forall a l1 l2, removeone a l1 = Some l2 -> Permutation (a :: l2) l1.
  Proof.
    intros a l1 l2 H.
    destruct (removeone_Some a l1 l2 H) as [l3 [l4 [-> ->]]].
    apply Permutation_cons_app; reflexivity.
  Qed.

  Lemma Permutation_dec : forall (l1 l2 : list A), {Permutation l1 l2} + {~(Permutation l1 l2)}.
  Proof.
    induction l1 as [|x l1 IH].
    - intros [|x l2].
      + left; auto.
      + right; apply Permutation_nil_cons.
    - intros l2.
      destruct (removeone x l2) as [l3|] eqn:Hrem.
      + apply removeone_Permutation in Hrem.
        destruct (IH l3) as [Hperm | Hperm].
        * left. rewrite <- Hrem. apply Permutation_cons; auto.
        * right. rewrite <- Hrem. intros H; apply Hperm. eapply Permutation_cons_inv; eauto.
      + right. apply removeone_None in Hrem.
        intros H; apply Hrem. eapply Permutation_in; [exact H|]. simpl; auto.
  Defined.

End PermutationDec.

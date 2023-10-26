Require Import Ring_polynom_AddOnQ.
Require Import NArith.
Require Import QArith.
Require Import OrderedType.
Require Import Lia.
Local Open Scope list_scope.
Import List.ListNotations.
Open Scope nat_scope.
Require Qcanon.

Module Type Num.
  Parameter t : Type.
  Parameter le : t -> t -> Prop.
  Parameter lt : t -> t -> Prop.
  Parameter z : t.
  Parameter lt_not_eq : forall x y : t, lt x y -> ~ (x = y).
  Parameter eq_dec : forall n m : t, {n = m} + {n <> m}.
  Parameter lt_eq_dec : forall n m : t, {lt n m} + {n = m} + {lt m n}.
  Parameter lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
End Num.

Module Index (N : Num).
  
  (*
  Notation "x '<' y" := (N.lt x y).
  Notation "x '<=' y" := (N.le x y).
  Notation "x '=' y" := (N.eq x y).
  *)
  Definition t: Type := list N.t.

  Definition eq (l1 l2 : t): Prop := 
    length l1 = length l2 /\ 
    forall i:nat, forall d:N.t, (i < length l1 -> nth i l1 d = nth i l2 d).

  Definition lt (l1 l2 : t) : Prop := 
  forall d:N.t,
  (length l1 < length l2 /\ forall i:nat, i < length l1 -> nth i l1 d = nth i l2 d)
  \/ (exists k:nat, k < length l1 /\ k < length l2 /\ N.lt (nth k l1 d) (nth k l2 d) /\ forall i:nat, i < k -> nth i l1 d = nth i l2 d).
  

  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof.
    intros.
    unfold eq in *.
    split.
    elim H.
    elim H0.
    intros.
    lia.
    induction i.
    - elim H.
      elim H0.
      intros.
      elim (H2 0 d).
      apply H4.
      assumption.
      lia.
    - intros.
    elim H.
    elim H0.
    intros.
    elim (H3 (S i) d).
    apply H5.
    assumption.
    lia.
  Qed.

  Lemma eq_refl : forall x : t, eq x x.
  Proof.
    intros.
    unfold eq.
    intros.
    split.
    reflexivity.
    induction i;
    reflexivity.
  Qed. 

  Lemma eq_sym : forall x y : t, eq x y -> eq y x.
  Proof.
    intros.
    unfold eq in *.
    intros.
    split.
    - elim H;lia.
    - induction i.
      elim H.
      intros.
      assert (Hsym : nth 0 x d = nth 0 y d). 
      apply H. 
      rewrite <- H0 in H2. assumption.
      rewrite Hsym;reflexivity.
     
      intros.
      elim H.
      intros.
      assert (Hsym : nth (S i) x d = nth (S i) y d). 
      apply H. 
      rewrite <- H1 in H0. assumption.
      rewrite Hsym;reflexivity.
  Qed.
  
  Lemma lt_empty : forall x y : t, lt x y -> [] <> y.
  Proof.
    intros x y LT.
    unfold lt in LT.
    pose proof (LT N.z) as LT'. clear LT.
    elim LT'. clear LT'.
    intros OR.
    elim OR.
    - intros. 
      intuition.
      assert (length y = 0) by (apply length_zero_iff_nil; auto).
      lia.
    - intro H. elim H. clear H.
      intros k AND. clear LT'.
      intuition.
      assert (POS : 0 <= k) by apply le_0_n.
      assert (0 < length y) by lia.
      assert (y = []) by auto.
      assert (length y = 0) by (apply length_zero_iff_nil ; assumption).
      lia.
  Qed.
  
  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    intros x y z LTxy LTyz.
    unfold lt in *.
    intros d. 
    Ltac break_and :=
      repeat match goal with
      | [H: ?x /\ ?y |- _] => elim H; clear H ; let X:= fresh "LT" in let Y:= fresh "H" in intros X Y
   end.

    elim (LTxy d); elim (LTyz d);intros.
    - left.
      split.
      lia.
      intros i LEQ.
      cutrewrite (nth i x d = nth i y d).
      apply H. lia.
      apply H0. assumption.
    - elim H. clear H.
      intros k LTk.
      assert (DEC : {length x <= k} + {k < length x}) by apply le_lt_dec.
      elim DEC.
      -- intro LT.
        left.
        split. lia.
        intros i LTi.
        cutrewrite (nth i x d = nth i y d).
        apply LTk. lia.
        apply H0. lia.
      -- intro LEQ.
        right.
        exists k.
        split. lia.
        split. lia.
        split. 
        + cutrewrite (nth k x d = nth k y d).
          apply LTk.
          apply H0. lia.
        + intros i LEk.
          cutrewrite (nth i x d = nth i y d).
          apply LTk. assumption.
          apply H0. lia.
    - elim H0. clear H0.
      intros k LTk.
      assert (DEC : {length z <= k} + {k < length z}) by apply le_lt_dec.
      elim DEC.
      -- intro LT.
        left.
        split. lia.
        intros i LTi.
        cutrewrite (nth i x d = nth i y d).
        apply H. lia.
        apply LTk. lia.
      -- intro LEQ.
        right.
        exists k.
        split. lia.
        split. lia.
        split. 
        + cutrewrite <- (nth k y d = nth k z d).
          apply LTk.
          apply H. lia.
        + intros i LEk.
          cutrewrite <- (nth i y d = nth i z d).
          apply LTk. assumption.
          apply H. lia.
    - elim H. clear H.
      intros k2 LTk2.
      elim H0. clear H0.
      intros k1 LTk1. 
      assert (DEC : {k1 < k2} + {k1 = k2} + {k2 < k1}) by apply lt_eq_lt_dec.
      elim DEC; clear DEC.
      -- intro DEC.
        elim DEC ; clear DEC.
        --- right. 
          exists k1.
          split. lia.
          split. lia.
          split.
          + cutrewrite <- (nth k1 y d = nth k1 z d).
            apply LTk1. 
            apply LTk2. assumption.
          + intros i LEi. 
            cutrewrite (nth i x d = nth i y d).
            apply LTk2. lia. 
            apply LTk1. lia.
        --- intro EQ.
          right.
          exists k1.  
          rewrite EQ in *.
          split. lia.
          split. lia.
          split.
          + apply (N.lt_trans (nth k2 x d) (nth k2 y d)).
            apply LTk1. 
            apply LTk2.
          + intros i LEi. 
            cutrewrite (nth i x d = nth i y d).
            apply LTk2. lia. 
            apply LTk1. lia. 
      -- intro LT.
        right.
        exists k2.
        split. lia.
        split. lia.
        split.
        + cutrewrite (nth k2 x d = nth k2 y d).
          apply LTk2.
          apply LTk1. lia.
        + intros i LEi. 
          cutrewrite (nth i x d = nth i y d).
          apply LTk2. assumption.
          apply LTk1. lia.
  Qed.
      
  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    intros x y LTxy.
    intuition.
    unfold lt in LTxy.
    unfold eq in H.
    pose proof (LTxy N.z) as LTxy_z. clear LTxy.
    elim (LTxy_z); clear LTxy_z.
    - intuition. 
    - intuition.
      elim H0.
      intros k LTk. 
      break_and.
      assert (DEC : {1 <= k} + {k < 1}) by apply le_lt_dec.
      elim DEC ; clear DEC.
      + intro LEQ.
        assert (EQ : nth (k-1) x N.z = nth (k-1) y N.z).
        apply H.
        lia.
        assert (~ (nth k x N.z = nth k y N.z)) 
          by (apply N.lt_not_eq;assumption).
      auto.
      + intros.
        assert (EQ0 : k = 0) by lia.
        rewrite EQ0 in *.
        assert (nth 0 x N.z = nth 0 y N.z) 
          by (apply H2 ; assumption).
        assert (~ (nth 0 x N.z = nth 0 y N.z)) 
          by (apply N.lt_not_eq;assumption).
        auto.
  Qed.

  Open Scope bool_scope.

  (* Lemmas used for eq_dec *)
  Lemma eq_compat : forall x y: t, x = y -> eq x y.
  Proof.
    intros.
    unfold eq.
    constructor.
    subst. reflexivity.
    subst. reflexivity.
  Qed.

  Lemma cons_app_compat : forall x :t, forall n:N.t, n::x = (n::[])++x.
  Proof.
    intros.
    auto.
  Qed.

  Lemma nth_cons : forall x:t, forall n d :N.t, forall i : nat,
  nth i x d = nth (S i) (n :: x) d.
  Proof.
    intros.
    induction i.
    - auto.
    - auto.
  Qed.

  Lemma length_cons : forall x:t, forall n:N.t, length (n :: x) = S (length x).
  Proof.
    intros.
    auto.
  Qed.

  Lemma eq_cons (x y : t) (n:N.t) : eq (n::x) (n::y) -> eq x y.
  Proof.
    intros.
    unfold eq in *.
    break_and.
    split.
    auto.
    intros.
    assert (nth (S i) (n :: x) d = nth (S i) (n :: y) d).
    apply H.
    rewrite length_cons.
    lia.
    rewrite (nth_cons x n d i).
    rewrite (nth_cons y n d i).
    assumption.
  Qed.

  Lemma pf_ind : forall x y:t, forall n1 n2 : N.t, 
  (eq x y -> x = y) -> n1 = n2 -> eq (n1 :: x) (n2 :: y) -> (n1 :: x) = (n2 :: y).
  Proof.
    intros.
    assert (x = y).
    apply H.
    apply (eq_cons x y n1).
    rewrite <- H0 in H1.
    assumption.
    subst. reflexivity.
  Qed.

  Lemma eq_compat2 : forall x y: t, eq x y -> x = y.
  Proof.
    refine (fix F x y {struct x} := match x,y 
    return eq x y -> x = y with
      | [],[] => _ (*fun pf_nil => _*)
      | [],_ => _ (*fun pf_nill => _*)
      | _,[] => _ (*fun pf_nilr => _*)
      | a::x1, b::y1 => match N.eq_dec a b with
        | left _ => fun pf_cons => let pf_cons' := F x1 y1 _ in _
        | right _ => _
        end
      end).
    - intro;reflexivity.
    - intros. inversion H. 
      simpl in H0. 
      inversion H0.
    - intros. inversion H. 
      simpl in H0. 
      inversion H0. 
    - apply pf_ind.
      apply F.
      assumption.
      assumption.
    - intros. 
      unfold eq in H.
      inversion H.
      assert (forall d, nth 0 (a :: x1) d = nth 0 (b :: y1) d).
      intro. apply H1.
      simpl.
      lia.
      simpl in H2.
      contradiction (H2 N.z).
   
    Unshelve.
    rewrite e in pf_cons.
    apply (eq_cons x1 y1 b).
    assumption.
  Qed.

  Definition eq_dec (x y : t) : {eq x y} + {~ eq x y}.
  Proof.
    assert ({x = y} + {x <> y}).
    apply list_eq_dec.
    exact N.eq_dec.
    elim H.
    - intro.
      left;apply eq_compat;assumption.

    - intro. 
    right.
    intro.
    apply b.
    apply eq_compat2.
    assumption.
  Qed.
  
  Ltac len_pos := 
  match goal with
  | [ |- 0 < length (?a :: ?x)] => cutrewrite (a :: x = [a] ++ x) ; [ | auto] ; 
    rewrite app_length ; simpl ; intuition
  end.

  Lemma lt_cons : forall x y : t, forall a : N.t, lt x y -> lt (a :: x) (a :: y).
    intros x y a LT.
    unfold lt in *.
    intro d.
    pose proof (LT d) as LTk. clear LT.
    elim LTk. clear LTk.
    - intro AND. 
      left.
      split.
      -- simpl. lia.
      -- intros i LT.
        simpl in LT.
        cutrewrite (a :: x = [a] ++ x) ; [ | auto].
        cutrewrite (a :: y = [a] ++ y) ; [ | auto].
        assert (DEC : {length [a] <= i} + {i < length [a]}) by apply le_lt_dec.
        elim DEC; clear DEC.
        + intro LEQ.
          assert(DEC : {1 <= i} + {i < 1}) by apply le_lt_dec.
          elim DEC; clear DEC.
          ++ intros. 
            rewrite app_nth2 ; [ | lia].
            rewrite app_nth2 ; [ | lia].
            simpl.
            apply AND.
            lia. 
          ++ intros.
            cutrewrite (i = 0) ; [ | lia].
            simpl ; auto.
        + intro LT2.
          rewrite app_nth1 ; [ | lia].
          rewrite app_nth1 ; [ | lia].
          simpl in LT2.
          cutrewrite (i = 0) ; [ | lia].
          simpl. auto.
   - intro PROP.
     right.
     elim PROP. clear PROP.
     intros k LT.
     exists (k+1).
     split. simpl. lia.
     split. simpl. lia.
     split.
     -- cutrewrite (a :: x = [a] ++ x) ; [ | auto].
       cutrewrite (a :: y = [a] ++ y) ; [ | auto].
       rewrite app_nth2 ; [ | simpl ; lia].
       rewrite app_nth2 ; [ | simpl ; lia].
       simpl.
       cutrewrite (k + 1 - 1 = k) ; [ | lia].
       apply LT.
    -- intros i LEQ.
      cutrewrite (a :: x = [a] ++ x) ; [ | auto].
      cutrewrite (a :: y = [a] ++ y) ; [ | auto]. 
      assert(DEC : {1 <= i} + {i < 1}) by apply le_lt_dec.
      elim DEC; clear DEC.
      ++ intros. 
        rewrite app_nth2 ; [ | simpl ; lia].
        rewrite app_nth2 ; [ | simpl ; lia].
        simpl.
        apply LT.
        lia. 
      ++ intros.
        cutrewrite (i = 0) ; [ | lia].
        simpl ; auto.
  Qed.

  Lemma lt_cons2 : forall x y : t, forall a b : N.t, N.lt a b -> lt (a::x) (b::y).
  Proof.
    intros.
    unfold lt.
    right.
    exists 0.
    intuition.
   - cutrewrite (a :: x = [a] ++ x) ; [ | auto].
    rewrite app_length.
    simpl.
    intuition.
  - cutrewrite (b :: y = [b] ++ y) ; [ | auto].
    rewrite app_length.
    simpl.
    intuition.
  - absurd (i < 0).
    intuition. 
    assumption.
  Qed.

  Lemma compare : forall x y : t, Compare lt eq x y.
  Proof.
    refine (fix F x y {struct x} := match x,y 
    return Compare lt eq x y with
      | [],[] => _ 
      | [],_ => _ 
      | _,[] => _
      | a::x1, b::y1 => match N.eq_dec a b with
        | left _ => let pf_cons' := F x1 y1 in _
        | right _ => _
        end
      end).
  - constructor 2.
    apply eq_refl.
  - constructor 1.
    unfold lt.
    intro d. 
    left. 
    split.
      -- simpl. intuition.
      -- intros i LE. simpl in LE. assert (0 <= i) by apply le_0_n.
        lia.
  - constructor 3.
    unfold lt.
    intro d.
    left. 
    split.
      -- simpl. intuition.
      -- intros i LE. simpl in LE. assert (0 <= i) by apply le_0_n.
        lia.
  - rewrite e. inversion pf_cons'. 
    -- constructor 1.
      apply lt_cons ; assumption.
    -- constructor 2.
      cutrewrite (x1 = y1) ; [ | apply eq_compat2 ; assumption].
      apply eq_refl. 
    -- constructor 3.
      apply lt_cons ; assumption.
  - assert (DEC : {N.lt a b} + {a = b} + {N.lt b a}) by apply N.lt_eq_dec.
    elim DEC.
    + intro DEC2.
      elim DEC2.
      ++ intro LT.
        constructor 1.
        apply lt_cons2 ; assumption.
      ++ intro EQ. 
        absurd (a = b) ; assumption.
    + intro LT.
      constructor 3.
      apply lt_cons2. assumption.
  Qed.

End Index.

Module NatNum <: Num.
  Definition t := nat.
 
  Definition le := Nat.le.
  Definition lt := Nat.lt.
  Definition z := 0%nat.
  Lemma lt_not_eq : forall x y : t, x < y -> ~ (x = y).
  Proof. intuition. Qed. 
   
  Lemma eq_dec : forall n m : nat, {n = m} + {n <> m}.
  Proof. apply Nat.eq_dec. Qed.
  
  Lemma lt_eq_dec : forall n m : t, {lt n m} + {n = m} + {lt m n}.
  Proof. apply lt_eq_lt_dec. Qed.
 
  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof. apply lt_trans. Qed.
End NatNum. 

Module QcNum <: Num.
  Local Open Scope Q_scope.
  Import Qcanon.
  Definition t := Qc.
 
  Definition le := Qcle.
  Definition lt := Qclt.
  Definition z := 0%Qc.
  Lemma lt_not_eq : forall x y : t, x < y -> x <> y.
  Proof.
    intros x y LT.
    intuition.
    rewrite H in LT.
    unfold Qclt in LT.
    unfold Qlt in LT.
    lia.
  Qed.
  
  Lemma eq_dec : forall n m : t, {n = m} + {n <> m}.
  Proof. apply Qc_eq_dec. Qed.
  
  Lemma lt_eq_dec : forall x y : t, {lt x y} + {x = y} + {lt y x}.
  Proof.    
    intros x y.
    assert ({x < y} + {y < x} + {x = y}) by apply Qc_dec.
    intuition.
  Qed.
 
  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof. apply Qclt_trans. Qed.
End QcNum.

Module NatIndex := Index(NatNum).

Module QcIndex := Index(QcNum).

Require Import QArith.
Require Import NumC.
Require Import QArith_base.
Require Datatypes.

Module QOp.
  Open Scope Q_scope.

  Lemma to_PExpr_compat_pos : forall q:Q,
  Qcanon.Qcle (Qcanon.Q2Qc 0%Q) (Qcanon.Q2Qc q) <-> 0 <= q.
  Proof.
    intuition. 
    - assert (cmp : Qcompare 0 q = Qcompare (Qred 0) (Qred q)) by apply Qred_compare.
      unfold Qcanon.Qcle in H.
      simpl in H.
      simpl in cmp.
      assert (NGt : 0 ?= Qred q <> Gt).
      rewrite <- (Qle_alt 0 (Qred q));assumption.
      rewrite (Qle_alt 0 q).
      rewrite <- cmp in NGt.
      assumption.
    - unfold Qcanon.Qcle.
      simpl.
      assert (cmp : Qcompare 0 q = Qcompare (Qred 0) (Qred q)) by apply Qred_compare.
      assert (NGt : 0 ?= q <> Gt).
      rewrite <- (Qle_alt 0 q);assumption.
      rewrite cmp in NGt.
      assumption.
  Qed.

  Import Datatypes.
  Lemma to_PExpr_compat_pos_strict : forall q:Q,
  Qcanon.Qclt (Qcanon.Q2Qc 0%Q) (Qcanon.Q2Qc q) <-> 0 < q.
  Proof.
    intuition. 
    - assert (cmp : Qcompare 0 q = Qcompare (Qred 0) (Qred q)) by apply Qred_compare.
      unfold Qcanon.Qclt in H.
      simpl in H.
      simpl in cmp.
      assert (NGt : 0 ?= Qred q = Lt).
      rewrite <- (Qlt_alt 0 (Qred q));assumption.
      rewrite (Qlt_alt 0 q).
      rewrite <- cmp in NGt.
      assumption.
    - unfold Qcanon.Qcle.
      simpl.
      assert (cmp : Qcompare 0 q = Qcompare (Qred 0) (Qred q)) by apply Qred_compare.
      assert (NGt : 0 ?= q = Lt).
      rewrite <- (Qlt_alt 0 q);assumption.
      rewrite cmp in NGt.
      assumption.
  Qed.

  Lemma QNum_to_Q_le_compat : forall q1 q2 : QNum.t, 
  QNum.Le q1 q2 <-> Qle (QNum.to_Q q1) (QNum.to_Q q2).
  Proof. intuition. Qed.
  
  Lemma QNum_to_Q_lt_compat : forall q1 q2 : QNum.t, 
  QNum.Lt q1 q2 -> Qle (QNum.to_Q q1) (QNum.to_Q q2).
  Proof. intuition. Qed.

    Lemma Qred_opp_compat : forall x:Q,
    Qred x = x -> Qred (-x) = -x.
    Proof.
      intros x red.
      rewrite Qred_opp.
      rewrite red.
      reflexivity.
    Qed.

    Lemma Qred_canon_compat : forall x:Q,
    Qred (x) = x -> Qcanon.this (Qcanon.Q2Qc (x)) = x.
    Proof.
      intros x red.
      simpl.
      assumption.
    Qed.

  Lemma Qcanon_opp_compat : forall q:QNum.t, 
  Qcanon.this (Qcanon.Qcopp q) = - Qcanon.this q.
  Proof.
    intro q.
    unfold Qcanon.Qcopp.
    destruct q as [x pf].
    simpl (Qcanon.this {| Qcanon.this := x; Qcanon.canon := pf |}).
    apply Qred_canon_compat.
    apply Qred_opp_compat.
    assumption.
  Qed.
  
  Lemma Qcanon_add_Q2Qc : forall x y : Q,
  Qcanon.Q2Qc (x + y) =
  Qcanon.Qcplus (Qcanon.Q2Qc x) (Qcanon.Q2Qc y).
  Proof.
    intros x y.
    apply Qcanon.Qc_is_canon.
    unfold Qcanon.Qcplus.
    simpl (Qcanon.this (Qcanon.Q2Qc x)).
    simpl (Qcanon.this (Qcanon.Q2Qc y)).
    assert (Hred : Qred(x + y)==(x + y)) by apply Qplus'_correct.
    rewrite Hred.
    assert (Hredx : Qred x == x) by apply Qred_correct.
    assert (Hredy : Qred y == y) by apply Qred_correct.
    assert (Hredxy : Qred x + Qred y == x + y) by(rewrite Hredx, Hredy; reflexivity).
    assert (Hredred : Qred (Qred x + Qred y) == Qred x + Qred y) by apply Qred_correct.
    rewrite Hredred. rewrite Hredxy. reflexivity.
  Qed.      

  Lemma Qcanon_minus_Q2Qc : forall x y : Q,
  Qcanon.Q2Qc (x - y) = Qcanon.Qcminus (Qcanon.Q2Qc x) (Qcanon.Q2Qc y).
  Proof.
    intros x y.
    apply Qcanon.Qc_is_canon.
    unfold Qcanon.Qcminus.
    unfold Qcanon.Qcplus.
    rewrite Qcanon_opp_compat.
    simpl (Qcanon.this (Qcanon.Q2Qc x)).
    simpl (Qcanon.this (Qcanon.Q2Qc y)).
    assert (red : Qred(x - y)==(x + -y)) by apply Qplus'_correct.
    rewrite red.
    assert (redx : Qred x == x) by apply Qred_correct.
    assert (redy : Qred y == y) by apply Qred_correct.
    assert (redxy : Qred x +- Qred y == x +- y) by (rewrite redx, redy; reflexivity).
    assert (redred : Qred (Qred x +- Qred y) == Qred x +- Qred y) by apply Qred_correct.
    rewrite redred.
    rewrite redxy.
    reflexivity.
  Qed.
  
  Lemma Qcanon_mult_Q2Qc : forall x y : Q,
  Qcanon.Q2Qc (x * y) =
  Qcanon.Qcmult (Qcanon.Q2Qc x) (Qcanon.Q2Qc y).
  Proof.
    intros x y.
    apply Qcanon.Qc_is_canon.
    unfold Qcanon.Qcmult.
    simpl (Qcanon.this (Qcanon.Q2Qc x)).
    simpl (Qcanon.this (Qcanon.Q2Qc y)).
    assert (Hred : Qred(x * y)==(x * y)) by apply Qmult'_correct.
    rewrite Hred.
    assert (Hredx : Qred x == x) by apply Qred_correct.
    assert (Hredy : Qred y == y) by apply Qred_correct.
    assert (Hredxy : Qred x * Qred y == x * y) by(rewrite Hredx, Hredy; reflexivity).
    assert (Hredred : Qred (Qred x * Qred y) == Qred x * Qred y) by apply Qred_correct.
    rewrite Hredred. rewrite Hredxy. reflexivity.
  Qed.
  
  Lemma Qcanon_Q_compat_1 : forall q1 q2 : QNum.t, forall q3 : Q,
  Qcanon.Q2Qc (QNum.to_Q q1 * QNum.to_Q q2 + q3) = 
  QNum.add (QNum.mul (Qcanon.Q2Qc (QNum.to_Q q1)) (Qcanon.Q2Qc (QNum.to_Q q2))) (Qcanon.Q2Qc q3).
  Proof.
    intros q1 q2 q3.
    destruct q1 as [x canonx], q2 as [y canony].
    simpl.
    unfold QNum.mul, QNum.add, Qcanon.Qcmult.
    simpl.
    rewrite canonx, canony.
    rewrite Qcanon_add_Q2Qc. reflexivity.
  Qed.
  
  Lemma Q2Qc_this_eq : forall q:QNum.t,
  Qcanon.Q2Qc (Qcanon.this q) = q.
  Proof.
    intro q.
    apply Qcanon.Qc_is_canon. simpl. apply Qred_correct.
  Qed.
     
  Lemma Qcanon_distrib_Q2Qc : forall q1 q2 : QNum.t, forall q3 : Q,
  Qcanon.Q2Qc (QNum.to_Q q1 * QNum.to_Q q2 + q3) = QNum.add (Qcanon.Q2Qc q3) (QNum.mul q2 q1).
  Proof.
    intros q1 q2 q3.
    rewrite Qcanon_Q_compat_1.
    unfold QNum.to_Q.
    
    rewrite Q2Qc_this_eq.
    rewrite Q2Qc_this_eq.
    unfold QNum.add.
    unfold QNum.mul.
    rewrite Qcanon.Qcmult_comm.
    apply Qcanon.Qcplus_comm.
  Qed.

  Lemma Qred_Q2Qc_compat : forall q:Q, Qcanon.Q2Qc (Qred q) = Qcanon.Q2Qc q.
  Proof.
    intro q.
    apply Qcanon.Qc_is_canon.
    simpl.
    apply Qred_correct.
  Qed.
  
  Lemma Qcanon_opp : forall q:Q, Qcanon.Q2Qc (-q) = Qcanon.Qcopp (Qcanon.Q2Qc q).
  Proof.
    intro q.
    unfold Qcanon.Qcopp.
    apply Qcanon.Qc_is_canon.
    simpl (Qcanon.this (Qcanon.Q2Qc q)).
    rewrite <- Qred_opp.
    rewrite Qred_Q2Qc_compat.
    reflexivity.
  Qed.
  
  Local Open Scope Z_scope.
  Lemma mul_pos_compat (num : Z) (den : positive) : 0 <= num * Zpos den <-> 0 <= num .
  Proof.
    intuition.
  Qed.
  Local Close Scope Z_scope.
  
  Lemma pos_compat (p q : Q) : 0 <= p -> p == q -> 0 <= q.
  Proof.
    Local Open Scope Z_scope.
    intros POS EQ.
    case p as (p_num,p_den).
    case q as (q_num,q_den).
    unfold Qle in *.  
    unfold Qeq in EQ.
    simpl in *.
    rewrite Z.mul_1_r in *.
    rewrite <- (mul_pos_compat p_num q_den) in POS.
    rewrite EQ in POS.
    rewrite mul_pos_compat in POS.
    assumption.
  Qed.
  Local Close Scope Z_scope.
  
  Local Open Scope Z_scope.
  Lemma mul_pos_compat_strict (num : Z) (den : positive) : 
    0 < num * Zpos den <-> 0 < num .
  Proof.
    intuition.
  Qed.

  Local Close Scope Z_scope.
  Lemma pos_compat_strict (p q : Q) : 0 < p -> p == q -> 0 < q.
  Proof.
    Local Open Scope Z_scope.
    intros POS EQ.
    case p as (p_num,p_den).
    case q as (q_num,q_den).
    unfold Qlt in *.  
    unfold Qeq in EQ.
    simpl in *.
    rewrite Z.mul_1_r in *.
    rewrite <- (mul_pos_compat_strict p_num q_den) in POS.
    rewrite EQ in POS.
    rewrite mul_pos_compat_strict in POS.
    assumption.
  Qed.
  Local Close Scope Z_scope.
End QOp.

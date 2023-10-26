(** We provide here some arithmetic on [ZN.t = option Z] 

  - Here [Some z] represents an integer z.
  - And [None] represents an unknow integer.

  This "number" is used to encode intervals.
  When [None] is involved in comparisons (e.g. [<=]),
  it can thus be considered as a kind of infinite.

  Authors: Alexandre Maréchal et Sylvain Boulmé

 *) 

Require Export Sumbool.
Require Export ZArith.
Require Export BinInt.
Require Export OptionMonad.
Require Export Lia.
Open Scope Z_scope.
Open Scope option_scope.

Program Definition Z_isZero (z: Z) : { z=0 } + { z <> 0 } :=
  match z with
  | Z0 => left _
  | _ => right _
  end.

Program Definition Z_isNat (z: Z) : { 0 <= z } + { ~(0 <= z) } :=
  match z with
  | Z0 => left _
  | Zpos _ => left _
  | Zneg _ => right _
  end.

Program Definition Z_isNegNat (z: Z) : { z <= 0 } + { ~(z <= 0) } :=
  match z with
  | Z0 => left _
  | Zpos _ => right _
  | Zneg _ => left _
  end.


(* A naive tactics to eliminate Z.min/Z.max in proofs *)
Hint Resolve Z.le_trans Z.le_max_l Z.le_max_r Z.le_min_l Z.le_min_r: zarith.

Lemma Zle_max_rew_r x y z: x <= (Z.max y z) <-> (x <= y \/ x <= z).
Proof.
  intros; constructor 1.
  apply Z.max_case_strong; intuition.
  intuition eauto with zarith.
Qed.

Lemma Zle_max_rew_l: forall x y z, (Z.max y z) <= x <-> (y <= x /\ z <= x).
Proof.
  intros; apply Z.max_case_strong; intuition eauto with zarith.
Qed.

Lemma Zle_min_rew_r x y z: x <= (Z.min y z) <-> (x <= y /\ x <= z).
Proof.
  intros; apply Z.min_case_strong; intuition eauto with zarith.
Qed.

Lemma Zle_min_rew_l x y z: (Z.min y z) <= x <-> (y <= x \/ z <= x).
Proof.
  intros; split.
  apply Z.min_case_strong; intuition.
  intuition;
    (eapply Zle_trans; [ idtac | eauto ]; eauto with zarith).
Qed.


Ltac Zminmax_simplify :=
  repeat (rewrite ! Z.max_id, Z.min_id in * |- * 
          || rewrite Zle_max_rew_l 
          || rewrite Zle_max_rew_r
          || rewrite Zle_min_rew_l
          || rewrite Zle_min_rew_r); 
  intuition (lia || auto with zarith).

(* A basis of compatibility lemmas of Z multiplication *)

Hint Resolve Z.mul_le_mono_nonpos_l Z.mul_le_mono_nonpos_r: zarith.

Lemma Z_le_trans_r n m p: m <= p -> n <= m -> n <= p.
Proof.
  lia. 
Qed.

Lemma Z_not_negnat_isnat z: ~(z <= 0) -> 0 <= z.
Proof.
  lia.
Qed.

Create HintDb zle_compat discriminated.
Hint Resolve Z.mul_le_mono_nonpos_l Z.mul_le_mono_nonneg_l Z.mul_le_mono_nonpos_r Z.mul_le_mono_nonneg_r Z.le_trans Z_le_trans_r
     Z_not_negnat_isnat: zle_compat.

Delimit Scope ZN_scope with ZN.

Module ZN.

  Definition t : Type := option Z. 

  Bind Scope ZN_scope with t.
  Open Scope ZN.

  Create HintDb zn discriminated.
  Create HintDb xzn discriminated.

  Definition leZ (z1:Z) (zn2: t): Prop :=
    WHEN z2 <- zn2 THEN z1 <= z2.

  Definition le (zn1 zn2: t): Prop :=
    WHEN z1 <- zn1 THEN leZ z1 zn2.

  Definition add (zn1 zn2:t) : t :=
    SOME z1 <- zn1 -;
    SOME z2 <- zn2 -;
    Some(z1 + z2).
  Extraction Inline add.

  (** NB: z is required to be not zero !
   It is a precondition for precision !
   (e.g. not verified in Coq)
   *)
  Definition mulZ1 (z: Z) (zn:t) : t :=
    SOME z2 <- zn -;
    Some(z * z2).
  Extraction Inline mulZ1.

  Definition mulZ (z: Z) (zn:t) : t :=
    if Z_isZero z then
      Some 0
    else
      mulZ1 z zn.
  Extraction Inline mulZ.

  Definition opp (zn:t) : t :=
    SOME z <- zn -;
    Some(-z).
  Extraction Inline opp.

  Notation "x + y" := (add x y) : ZN_scope.
  Notation "x <= y" := (le x y) : ZN_scope.
  Notation "x <= y <= z" := (le x y /\ le y z) : ZN_scope.

  Open Scope ZN_scope.


  (* ARITHMETIC LEMMAS *)

  Lemma leZ_le z1 (zn2:t):
    leZ z1 zn2 <-> (Some z1) <= zn2.
  Proof. 
    unfold le; simpl; intuition.
  Qed.

  Lemma mulZ1_Some a b:
    mulZ1 a (Some b)=(Some (a*b)%Z).
  Proof.
    auto.
  Qed.

  Lemma mulZ_Some a b:
    mulZ a (Some b)=(Some (a*b)%Z).
  Proof.
    unfold mulZ.
    destruct (Z_isZero a); intros; try subst; auto.
  Qed.

  Lemma mulZ_mulZ1 a b:
    a <> 0 -> mulZ a b=mulZ1 a b.
  Proof.
    unfold mulZ.
    destruct (Z_isZero a); intros; try subst; auto.
    lia.
  Qed.

  (* Remark not used in the following ! *)
  Remark notLe zn1 zn2:
    ~(zn1 <= zn2) <-> EXISTS z1 <- zn1 SUCH EXISTS z2 <- zn2 SUCH (z2 < z1)%Z.
  Proof.
    destruct zn1, zn2; simpl; intuition try lia.
  Qed.
  Hint Resolve notLe: xzn.

  Ltac simpl_arith :=
    xsimplify ltac:(intuition eauto with xzn); 
    intros;
    try (rewrite ! mulZ_Some in * |- *); 
    repeat (rewrite mulZ_mulZ1 in * |- *; [ idtac | lia || (auto with zarith; fail) ]); 
    simpl in * |- * ;
    try (rewrite ! leZ_le in * |- *); 
    try (apply f_equal); lia || auto with zn zarith.

  Lemma le_None x: x <= None.
  Proof.
    destruct x; simpl; auto.
  Qed.
  Hint Resolve le_None: zn.

  Program Definition isZero zn: { zn= (Some 0) } + { zn <> (Some 0) } := 
    match zn with
    | None => right _ 
    | Some z => if Z_isZero z then left _ else right _
    end.
  Extraction Inline isZero.


  Program Definition le_dec zn1 zn2 : {zn1 <= zn2} + {~ zn1 <= zn2} :=
    match zn1 with
    | None => left _
    | Some z1 =>
        match zn2 with
        | None => left _ 
        | Some z2 => if Z_le_dec z1 z2 then left _ else right _
        end
    end.
  Extraction Inline le_dec.

  Definition leb (x y:t) := if le_dec x y then true else false. 

  Notation "x <=? y" := (leb x y) : ZN_scope.
  Coercion Is_true: bool >-> Sortclass.

  Lemma le_bool_le x y: x <=? y <-> x <= y.
  Proof.
    unfold leb; destruct (le_dec x y); simpl; intuition; lia || auto.
  Qed.

  Program Definition eq_dec x y : {x=y} + {x<>y} :=
    match x with
    | None =>
         match y with
         | None => left _ _
         | Some zy => right _ _
         end
    | Some zx =>
         match y with
         | None => right _ _
         | Some zy => if Z.eq_dec zx zy then left _ else right _ 
         end
    end.


  Lemma Some_eq (z1 z2:Z):
    Some z1 = Some z2 <-> z1 = z2.
  Proof.
    intuition congruence.
  Qed.
  Hint Rewrite Some_eq: zn.

  Lemma add_le_compat (a b c d : t) :
    a <= b -> c <= d -> a + c <= b + d.
  Proof.
    unfold add; simpl_arith.
  Qed.

  Lemma opp_le_compat (a b: t) :
    a <= b  -> opp b <= opp a.
  Proof.
    unfold opp; simpl_arith.
  Qed.

  Lemma le_refl a : a <= a.
  Proof.
    unfold le; simpl_arith.
  Qed.

  Hint Resolve le_refl add_le_compat opp_le_compat: zn. 

  Lemma le_trans b (a c : t): 
    a <= Some b -> Some b <= c -> a <= c.
  Proof.
    unfold le, leZ; simpl_arith.
  Qed.

  (* Lemmas on multiplications *)
  Lemma mulZ1_le_compat_pos_l a b c :
    (0 <= a)%Z -> b <= c -> (mulZ1 a b) <= (mulZ1 a c).
  Proof.
    unfold mulZ1; simpl_arith.
  Qed.
  Hint Resolve mulZ1_le_compat_pos_l: zn.

  Lemma mulZ_le_compat_pos_l a b c :
    (0 <= a)%Z -> b <= c -> (mulZ a b) <= (mulZ a c).
  Proof.
    unfold mulZ; destruct (Z_isZero a); auto with zn.
  Qed.
  Hint Resolve mulZ_le_compat_pos_l: zn.

  Lemma mulZ1_le_compat_opp_l a b c :
    ~(0 <= a)%Z -> b <= c -> (mulZ1 a c) <= (mulZ1 a b).
  Proof.
    unfold mulZ1; simpl_arith.
  Qed.
  Hint Resolve mulZ1_le_compat_opp_l: zn.

  Lemma mulZ_le_compat_opp_l a b c :
    ~(0 <= a)%Z -> b <= c -> (mulZ a c) <= (mulZ a b).
  Proof.
    unfold mulZ; destruct (Z_isZero a); auto with zn.
  Qed.
  Hint Resolve mulZ_le_compat_opp_l: zn.

  (* LATTICE STRUCTURE *)
  Definition join (zn1 zn2: t): t :=
    SOME z1 <- zn1 -;
    SOME z2 <- zn2 -;
    Some (Z.max z1 z2).

  Lemma join_lowest x y z: x <= z -> y <= z ->  join x y <= z.
  Proof.
    unfold join; destruct z; simpl_arith; Zminmax_simplify.
  Qed.

  Lemma join_le_l x y z:
    z <= x -> z <= join x y.
  Proof.
    unfold join; destruct z; simpl_arith; Zminmax_simplify.
  Qed.

  Lemma join_le_r x y z:
    z <= y -> z <= join x y.
  Proof.
    unfold join; destruct z; simpl_arith; Zminmax_simplify.
  Qed.


  Definition meet (zn1 zn2: t): t :=
    SOME z1 <- zn1 -;
    SOME z2 <- zn2 -;
    Some (Z.min z1 z2).

  Lemma meet_le_l x y z: x <= z -> meet x y <= z.
  Proof.
    unfold meet; destruct z; simpl_arith; Zminmax_simplify.
  Qed.

  Lemma meet_le_r x y z: y <= z -> meet x y <= z.
  Proof.
    unfold meet; destruct z; simpl_arith; Zminmax_simplify.
  Qed.

  Lemma meet_greatest x y z: z <= x -> z <= y ->  z <= meet x y.
  Proof.
    unfold meet; destruct z; simpl_arith; Zminmax_simplify.
  Qed.
  Hint Resolve join_le_l join_le_r join_lowest meet_le_l meet_le_r meet_greatest: zn.


  Close Scope ZN_scope.

End ZN.

Close Scope option_scope.
Close Scope Z_scope.

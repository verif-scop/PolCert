Require Import Bool.
Require Import Base.
Require Import Linalg.
Require Import LinalgExt.
Require Import ZArith.
Require Import List.
Require Import MSets.
Require Import Coq.MSets.MSetProperties.
Require Import AST.
Require Import ImpureAlarmConfig.
Require Import PolyOperations.
Require Import Lia.
Require Import Classical.
Require Import LibTactics.
Require Import sflib.
Import ListNotations.

Scheme Equality for list.

Definition free_ident (u: unit) : ident := 99999%positive.

(** Domain: Constraints for valid instances' index. *)
Definition Domain := polyhedron.


Module NP.
  Definition t: Type := nat * list Z.
  Definition eq (d1 d2: t): Prop := 
    match d1, d2 with 
    | (n1, p1), (n2, p2) => 
       n1 = n2 /\ p1 =v= p2
    end.
  Lemma eq_refl: 
    forall d, eq d d.
  Proof.
    destruct d as (n, p).
    simpls. splits; trivial. eapply veq_refl.
  Qed.
  Lemma eq_equiv: 
    Equivalence eq.
  Proof.
    split.
    {
      intros d. apply eq_refl.
    }
    {
      intros d1 d2 E. 
      unfold eq in E.
      destruct d1 as (n1 & p1). 
      destruct d2 as (n2 & p2).
      destruct E.
      splits; eauto. eapply veq_sym; trivial.
    }
    {
      intros d1 d2 d3 E12 E23. 
      destruct d1 as (n1 & p1). 
      destruct d2 as (n2 & p2).
      destruct d3 as (n3 & p3).
      simpls. 
      destruct E12; destruct E23.
      splits; subst; eauto.
      eapply veq_transitive; eauto.
    }
  Qed.
  Lemma eq_dec: 
    forall d1 d2: t, {eq d1 d2} + {~ eq d1 d2}.
  Proof.
    destruct d1, d2; simpls; try (left; reflexivity); try (right; congruence).
    destruct (Nat.eq_dec n n0); subst.
    {
      destruct (veq_eq_dec l l0); subst.
      {
        left. splits; eauto.
      }
      {
        right. intro E. destruct E. congruence.
      }
    }
    {
      right. intro E. destruct E. congruence.
    }
  Qed.
End NP.

Module NPSet := MSetWeakList.Make NP.
Module NPSetProp := WPropertiesOn NP NPSet.

Definition listzz_strict_eqb (c1 c2: list Z * Z): bool := 
    let (v1, c1) := c1 in 
    let (v2, c2) := c2 in 
    Z.eqb c1 c2 && list_beq Z.t Z.eqb v1 v2. 

(* Compute (constraint_strict_eqb ([Z.one;Z.two], Z.one) ([Z.one;Z.two], Z.zero)). *)

Lemma listzz_strict_eqb_eq:
  forall cstr1 cstr2, 
    listzz_strict_eqb cstr1 cstr2 = true -> 
    cstr1 = cstr2.
Proof.
  intros.
  unfold listzz_strict_eqb in H.
  destruct cstr1 as (v1&c1).
  destruct cstr2 as (v2&c2).
  eapply andb_true_iff in H.
  destruct H.
  eapply Z.eqb_eq in H.
  eapply internal_list_dec_bl in H0; eauto.
  eapply Z.eqb_eq.
Qed.

Lemma listzz_strict_eq_eqb:
  forall cstr1 cstr2, 
    cstr1 = cstr2 -> 
    listzz_strict_eqb cstr1 cstr2 = true.
Proof.
  intros.
  unfold listzz_strict_eqb.
  destruct cstr1 as (v1&c1).
  destruct cstr2 as (v2&c2).
  inv H.
  eapply andb_true_iff. splits. 
  eapply Z.eqb_eq; trivial.
  eapply internal_list_dec_lb; eauto.
  eapply Z.eqb_eq.
Qed.

Definition listzzs_strict_eqb: Domain -> Domain -> bool := 
    list_beq constraint listzz_strict_eqb.

Lemma listzzs_strict_eqb_eq: 
  forall dom1 dom2, 
    listzzs_strict_eqb dom1 dom2 = true -> 
    dom1 = dom2.  
Proof.
  intros.
  unfold listzzs_strict_eqb in H.
  eapply internal_list_dec_bl in H; eauto.
  eapply listzz_strict_eqb_eq.
Qed.

Lemma listzzs_strict_eq_eqb:
  forall dom1 dom2, 
    dom1 = dom2 -> 
    listzzs_strict_eqb dom1 dom2 = true.
Proof.
  intros.
  unfold listzzs_strict_eqb.
  subst. eapply internal_list_dec_lb; eauto.
  eapply listzz_strict_eq_eqb.
Qed.

(** AffineFunction: calculate ax + b. *)
Definition AffineFunction := list (list Z * Z) %type.  (** ax + b *)
(** strict *)

Definition Schedule :=  AffineFunction.
Definition Transformation := AffineFunction.
Definition AccessFunction := (ident * AffineFunction) %type.
Definition aff_func_dummy:AccessFunction := (1%positive, nil).

Definition listzzs_eqb (l1 l2: list (list Z * Z)): bool := 
  Nat.eqb (length l1) (length l2) &&
  forallb (fun (l1l2: (list Z * Z) * (list Z * Z)) => 
    let (l1, l2) := l1l2 in 
    let (v1, c1) := l1 in
    let (v2, c2) := l2 in
    is_eq v1 v2 && Z.eqb c1 c2
  ) (combine l1 l2).

Definition access_eqb (a1 a2: AccessFunction) :=
  let (id1, aff_func1) := a1 in 
  let (id2, aff_func2) := a2 in 
  Pos.eqb id1 id2 && listzzs_eqb aff_func1 aff_func2.

(* Definition opt_access_eqb (a1 a2: option AccessFunction) :=
  match a1, a2 with
  | Some a1, Some a2 => access_eqb a1 a2
  | None, None => true
  | _, _ => false
  end. *)

Definition opt_access_subset (al1 al2: option (list AccessFunction)) :=
  match al1, al2 with
  | Some al1, Some al2 => forallb (fun a1 => existsb (fun a2 => access_eqb a1 a2) al2) al1
  | None, None => true
  | _, _ => false
  end.

Definition access_strict_eqb (a1 a2: AccessFunction) := 
  let (id1, aff_func1) := a1 in 
  let (id2, aff_func2) := a2 in 
  Pos.eqb id1 id2 && listzzs_strict_eqb aff_func1 aff_func2.

Lemma access_strict_eqb_eq: 
  forall a1 a2,
    access_strict_eqb a1 a2 = true -> 
    a1 = a2.
Proof.
  intros.
  unfold access_strict_eqb in H.
  destruct a1 as (id1, listzzs1).
  destruct a2 as (id2, listzzs2).
  eapply andb_true_iff in H.
  destruct H.
  eapply Pos.eqb_eq in H.
  eapply listzzs_strict_eqb_eq in H0.
  f_equal; trivial.
Qed.

Lemma access_strict_eq_eqb: 
  forall a1 a2,
    a1 = a2 ->
    access_strict_eqb a1 a2 = true. 
Proof.
  intros.
  unfold access_strict_eqb in H.
  destruct a1 as (id1, listzzs1).
  destruct a2 as (id2, listzzs2).
  eapply andb_true_iff.
  inv H.
  rewrite Pos.eqb_eq. split; trivial.
  eapply listzzs_strict_eq_eqb. trivial.
Qed.

Definition access_list_strict_eqb := 
    list_beq AccessFunction access_strict_eqb.
  
Lemma access_list_strict_eqb_eq:
  forall al1 al2,
    access_list_strict_eqb al1 al2 -> 
    al1 = al2.
Proof.
  intros.
  unfold access_list_strict_eqb in H.
  eapply internal_list_dec_bl in H; trivial.
  eapply access_strict_eqb_eq.
Qed.

Lemma access_list_strict_eq_eqb:
  forall al1 al2,
    al1 = al2 ->
    access_list_strict_eqb al1 al2 = true.
Proof.
  induction al1.
  - intros. subst. simpls. trivial. 
  - intros. destruct al2 eqn:Hal2; tryfalse. inv H. simpl.
    rewrite IHal1; trivial. rewrite andb_true_iff. split; trivial.
    eapply access_strict_eq_eqb. trivial.
Qed.

Definition DomIndex := list Z.

Record MemCell := { 
  arr_id: ident; 
  arr_index: list Z;
}. 

Definition exact_cell (a: AccessFunction) (p: DomIndex): MemCell := 
  let (id, func) := a in 
  {|
    arr_id := id;
    arr_index := affine_product func p;
  |}.

Definition cell_eq (c1 c2: MemCell): Prop := 
  arr_id c1 = arr_id c2 /\ veq (arr_index c1) (arr_index c2).
  
Definition cell_neq (c1 c2: MemCell): Prop := 
  arr_id c1 <> arr_id c2 \/ ~ veq (arr_index c1) (arr_index c2).

Instance cell_eq_proper: Proper ((cell_eq ==> cell_eq ==> iff)) cell_eq.
Proof.
  intros c1 c2 Heq c3 c4 Heq'. 
  unfolds cell_eq. split; intro.
  - firstorder; try lia. 
    eapply veq_transitive; eauto. eapply veq_transitive; eauto. 
    eapply veq_sym; trivial.   
  - firstorder; try lia.
    eapply veq_transitive; eauto. eapply veq_transitive; eauto. 
    eapply veq_sym; trivial.   
Qed.

Instance cell_neq_proper: Proper ((cell_eq ==> cell_eq ==> iff)) cell_neq.
Proof.
  intros c1 c2 Heq c3 c4 Heq'. 
  unfolds cell_neq. unfolds cell_eq. split; intro.
  - firstorder; try lia.
    right. intro. apply H. 
    eapply veq_transitive; eauto. eapply veq_transitive; eauto. 
    eapply veq_sym; trivial.   
  - firstorder; try lia.
    right. intro. apply H. 
    eapply veq_transitive; eauto. eapply veq_transitive; eauto. 
    eapply veq_sym; trivial.
Qed.

Instance cell_eq_symm: Symmetric cell_eq.
Proof. 
  intros c1 c2 Heq. unfolds cell_eq. split; firstorder. eapply veq_sym; trivial.
Qed.

Lemma cell_neq_symm: 
  forall c1 c2, 
    cell_neq c1 c2 <-> cell_neq c2 c1.
Proof.
  intros. unfolds cell_neq. split; intro.
  destruct H; eauto.
  right. intro. apply H.
  eapply veq_sym; eauto.
  destruct H; eauto.
  right. intro. apply H.
  eapply veq_sym; eauto.
Qed.

Definition valid_access_cells (p: DomIndex) (cells: list MemCell) (al: list AccessFunction): Prop :=
    forall c,
      In c cells ->
      exists a,
        In a al /\ cell_eq (exact_cell a p) c.

Definition TimeStamp := list Z.

Definition V0 (n: nat): list Z := repeat 0%Z n.

Definition Vopp (v: list Z) : list Z := List.map (Z.opp) v.
Notation "-- v" := (Vopp v) (at level 35, right associativity).

Lemma opp_app: 
  forall v1 v2, 
    -- (v1 ++ v2) = (-- v1) ++ (-- v2).
Proof.
  induction v1.
  {
    intros; simpls; trivial.
  }
  {
    intros. simpls. rewrite IHv1; trivial.
  }
Qed.

Lemma opp_opp: 
  forall v, 
    -- (-- v) = v.
Proof.
  induction v. 
  {
    intros; simpls; trivial.
  }
  {
    intros; simpls. rewrite IHv; trivial.
    rewrite Z.opp_involutive; trivial.
  }
Qed.

Lemma opp_v0_v0: 
  forall n, 
    -- (V0 n) = V0 n.
Proof.
  induction n; simpls; trivial.
  unfold V0. 
  unfold repeat. eapply f_equal. eapply IHn.
Qed.

Lemma v0_n_app_1_dot_product_p_is_nth_p:
forall n p v,
  nth_error p n = Some v ->
  dot_product (V0 n ++ [1%Z]) p = v.
Proof. 
induction n.
- intros. simpls. destruct p; tryfalse. 
  inv H. destruct p; try lia.
- intros. simpls. destruct p eqn:Hp; tryfalse.
  eapply IHn in H. trivial. 
Qed.

Lemma dot_product_opp_l: 
  forall v1 v2, 
    dot_product (-- v1) v2 = Z.opp (dot_product v1 v2).
Proof.
  induction v1.
  {
    intros; simpls.
    destruct v2; trivial.
  }
  {
    intros; simpls. 
    destruct v2 eqn:Hv2; simpls; trivial.
    rewrite IHv1.
    lia.
  }
Qed.

Lemma dot_product_opp_r: 
  forall v1 v2, 
    dot_product v1 (-- v2) = Z.opp (dot_product v1 v2).
Proof. 
  induction v1.
  {
    intros; simpls.
    destruct v2; trivial.
  }
  {
    intros; simpls. 
    destruct v2 eqn:Hv2; simpls; trivial.
    rewrite IHv1.
    lia.
  }
Qed.

(*********************)

Definition make_constr_lt0_l (aff: (list Z * Z)) (dim2: nat): (list Z * Z) := 
  let (v1, c1) := aff in 
  let v := v1 ++ (V0 dim2) in
  (v, (-c1-1)%Z).

Lemma make_constr_lt0_l_correct: 
  forall dim2 v1 c1 p1 p2, 
    length p1 = length v1 ->
    (dot_product v1 p1 + c1 < 0)%Z <->
    satisfies_constraint (p1++p2) (make_constr_lt0_l (v1, c1) dim2) = true.
Proof. 
  intros. unfold make_constr_lt0_l.
  unfold satisfies_constraint.
  simpl. rewrite dot_product_app; trivial.
  rewrite dot_product_commutative.
  unfold V0. rewrite dot_product_repeat_zero_right.
  simpls; lia. 
Qed. 

Definition make_constr_lt0_r (dim1: nat) (aff: (list Z * Z)): (list Z * Z) := 
  let (v2, c2) := aff in 
  let v := (V0 dim1) ++ v2 in
  (v, (-c2-1)%Z).

Lemma make_constr_lt0_r_correct: 
  forall dim1 v2 c2 p1 p2, 
    length p1 = dim1 ->
    (dot_product v2 p2 + c2 < 0)%Z <->
    satisfies_constraint (p1++p2) (make_constr_lt0_r dim1 (v2, c2)) = true.
Proof. 
  intros. unfold make_constr_lt0_r.
  unfold satisfies_constraint.
  simpl. rewrite dot_product_app. 
  2: {unfold V0. rewrite repeat_length. trivial. }
  rewrite dot_product_commutative.
  unfold V0. rewrite dot_product_repeat_zero_right. 
  lia.
Qed.

Definition make_constrs_eq0_l (aff: (list Z * Z)) (dim2: nat): polyhedron :=
  let (v1, c1) := aff in 
  let v := v1 ++ (V0 dim2) in
  ((v, (-c1)%Z) :: ((-- v, c1%Z) :: nil)).

Lemma make_constrs_eq0_l_correct: 
  forall dim2 v1 c1 p1 p2, 
    length p1 = length v1 ->
    (dot_product v1 p1 + c1 = 0)%Z <->
    in_poly (p1++p2) (make_constrs_eq0_l (v1, c1) dim2) = true.
Proof.
  intros.
  unfold make_constrs_eq0_l.
  unfold in_poly. unfold forallb.
  do 2 rewrite andb_true_iff. split; intro.
  {
    unfold satisfies_constraint.
    simpl. rewrite dot_product_app; trivial. 
    rewrite dot_product_commutative in H0.
    unfold V0. rewrite dot_product_repeat_zero_right. 
    rewrite opp_app. rewrite opp_v0_v0. rewrite dot_product_app.
    2: {unfold "--". rewrite map_length. trivial. }
    unfold V0. rewrite dot_product_repeat_zero_right.
    simpls. rewrite dot_product_opp_r.
    splits; trivial; try lia.  
  }
  {
    unfolds satisfies_constraint.
    destruct H0 as (LT & GT & _).
    simpls. rewrite dot_product_app in LT; trivial. 
    rewrite dot_product_commutative.
    unfold V0 in LT. rewrite dot_product_repeat_zero_right in LT. simpls.
    rewrite opp_app in GT. rewrite opp_v0_v0 in GT. rewrite dot_product_app in GT.
    2: {unfold "--". rewrite map_length. trivial. }
    unfold V0 in GT. rewrite dot_product_repeat_zero_right in GT. 
    rewrite dot_product_opp_r in GT.
    lia.
  }
Qed.

Definition make_constrs_eq0_r (dim1: nat) (aff: (list Z * Z)): polyhedron :=
  let (v2, c2) := aff in 
  let v := (V0 dim1) ++ v2 in
  ((v, (-c2)%Z) :: ((-- v, c2%Z) :: nil)).

Lemma make_constrs_eq0_r_correct: 
  forall dim1 v2 c2 p1 p2, 
    length p1 = dim1 ->
    (dot_product v2 p2 + c2 = 0)%Z <->
    in_poly (p1++p2) (make_constrs_eq0_r dim1 (v2, c2)) = true.
Proof.
  intros. unfold make_constrs_eq0_r.
  unfold in_poly. unfold forallb.
  do 2 rewrite andb_true_iff. split; intro.
  {
    unfold satisfies_constraint.
    simpl. rewrite dot_product_app. 
    2: {unfold V0. rewrite repeat_length. trivial. }
    rewrite dot_product_commutative.
    unfold V0. rewrite dot_product_repeat_zero_left. 
    rewrite opp_app. rewrite opp_v0_v0. rewrite dot_product_app.
    2: {unfold V0. rewrite repeat_length. trivial. }
    unfold V0. rewrite dot_product_repeat_zero_right.
    simpls. rewrite dot_product_opp_r.
    rewrite dot_product_commutative in H0.
    splits; trivial; try lia. 
  }
  {
    unfolds satisfies_constraint.
    destruct H0 as (LT & GT & _).
    simpls. rewrite dot_product_app in LT. 
    2: {unfold V0. rewrite repeat_length. trivial. }
    rewrite dot_product_commutative.
    unfold V0 in LT. rewrite dot_product_repeat_zero_right in LT. simpls.
    rewrite opp_app in GT. rewrite opp_v0_v0 in GT. rewrite dot_product_app in GT.
    2: {unfold V0. rewrite repeat_length. trivial. }
    unfold V0 in GT. rewrite dot_product_repeat_zero_right in GT. simpls.
    rewrite dot_product_opp_r in GT.
    lia.
  }
Qed.

Fixpoint make_poly_lt0_l
(sched1: Schedule) (dim2: nat)
(pol: polyhedron) :=
match sched1 with
  | [] => []
  | aff :: sched1' => 
    ((make_constr_lt0_l aff dim2) :: pol) ::
    (make_poly_lt0_l sched1' dim2 ((make_constrs_eq0_l aff dim2) ++ pol)) (** *)
end.

Lemma make_poly_lt0_l_correct: 
  forall sched1 p1 p2 dim2 pol, 
    exact_listzzs_cols (length p1) sched1 ->
    (in_poly (p1 ++ p2) pol = true /\
    lex_compare [] (affine_product sched1 p1) = Gt) <-> 
    Exists (fun pol => in_poly (p1 ++ p2) pol = true) (make_poly_lt0_l sched1 dim2 pol).
Proof. 
  induction sched1.
  {
    intros until pol. intros Hlen.
    simpls. split; intro.
    {
      destruct H; tryfalse.
    }
    {
      inv H; tryfalse.
    }
  }
  {
    intros until pol. intros Hlen.
    destruct a as (v1, c1) eqn:Hconstr1. 
    unfold affine_product. 
    split; intro.
    {
      eapply Exists_cons.
      destruct H.
      simpl in H0. 
      destruct (dot_product v1 p1 + c1)%Z eqn:Hprod; tryfalse; try lia.
      {
        (* equal 0 *)
        right.
        eapply IHsched1; eauto. 
        {
          clear - Hlen. 
          firstorder.
        }
        split.
        {
          rewrite in_poly_app. rewrite andb_true_iff. split; trivial.
          unfold in_poly. unfold forallb.
          eapply make_constrs_eq0_l_correct; eauto.
          {
            clear - Hlen. unfold exact_listzzs_cols in Hlen. 
            symmetry.
            eapply Hlen; eauto. eapply in_eq.
          }
        }
        {
          simpl. 
          destruct (affine_product sched1 p1) eqn:Hts1.
          {
            unfold affine_product in Hts1.
            rewrite Hts1 in H0.
            simpl; tryfalse.
          } 
          {
            rewrite <- Hts1. trivial. 
          }
        }
      }
      {
        (* 0 < *)
        left.
        unfold in_poly. unfold forallb. rewrite andb_true_iff. 
        split; trivial.
        eapply make_constr_lt0_l_correct; trivial.
        {
          clear - Hlen.
          symmetry. eapply Hlen; eauto. eapply in_eq.
        }
        rewrite Hprod; lia.      
      }
    }
    {
        eapply Exists_cons in H. 
        destruct H as [Hin | Hexists].
        {
          simpl in Hin. rewrite andb_true_iff in Hin.
          destruct Hin; trivial.
          simpls. 
          eapply make_constr_lt0_l_correct in H; trivial. split; trivial.
          destruct (dot_product v1 p1 + c1)%Z eqn:Hd; tryfalse; trivial.
          {
            clear - Hlen.
            symmetry. eapply Hlen; eauto. eapply in_eq.
          }
        }
        {
          eapply IHsched1 in Hexists; trivial.
          destruct Hexists as (Hpol & Hgt).
          rewrite in_poly_app in Hpol. rewrite andb_true_iff in Hpol. destruct Hpol.
          splits; trivial.
          eapply make_constrs_eq0_l_correct in H; trivial.
          simpl. rewrite H.
          simpl in Hgt.
          destruct (affine_product sched1 p1) eqn:Hts1; tryfalse.
          rewrite <- Hts1 in Hgt. trivial.
          {
            clear - Hlen. symmetry. eapply Hlen; eauto. eapply in_eq. 
          }
          {
            clear - Hlen; firstorder.
          }
        }
    }
  }
Qed.

Fixpoint make_poly_lt0_r
(dim1: nat) (sched2: Schedule)
(pol: polyhedron) :=
match sched2 with
 | [] => []
 | aff2 :: sched2' =>
   ((make_constr_lt0_r dim1 aff2) :: pol) ::
   (make_poly_lt0_r dim1 sched2' (make_constrs_eq0_r dim1 aff2 ++ pol))
end.

Lemma make_poly_lt0_r_correct: 
  forall sched2 p1 p2 dim1 pol, 
    length p1 = dim1 ->
    (in_poly (p1 ++ p2) pol = true /\
    lex_compare [] (affine_product sched2 p2) = Gt) <-> 
    Exists (fun pol => in_poly (p1 ++ p2) pol = true) (make_poly_lt0_r dim1 sched2 pol).
Proof. 
  induction sched2.
  {
    intros until pol. intros Hlen.
    simpls. split; intro.
    {
      destruct H; tryfalse.
    }
    {
      inv H; tryfalse.
    }
  }
  {
    intros until pol. intros Hlen.
    destruct a as (v2, c2) eqn:Hconstr2. 
    unfold affine_product. 
    split; intro.
    {
      eapply Exists_cons.
      destruct H.
      simpl in H0. 
      destruct (dot_product v2 p2 + c2)%Z eqn:Hprod; tryfalse; try lia.
      {
        (* equal 0 *)
        right.
        eapply IHsched2; eauto. split.
        {
          rewrite in_poly_app. rewrite andb_true_iff. split; trivial.
          unfold in_poly. unfold forallb.
          eapply make_constrs_eq0_r_correct; eauto.
        }
        {
          simpl. 
          destruct (affine_product sched2 p2) eqn:Hts2.
          {
            unfold affine_product in Hts2.
            rewrite Hts2 in H0.
            simpl; tryfalse.
          } 
          {
            rewrite <- Hts2. trivial. 
          }
        }
      }
      {
        (* 0 < *)
        left.
        unfold in_poly. unfold forallb. rewrite andb_true_iff. 
        split; trivial.
        eapply make_constr_lt0_r_correct; trivial.
        rewrite Hprod. 
        lia.      
      }
    }
    {
       eapply Exists_cons in H. 
       destruct H as [Hin | Hexists].
       {
        simpl in Hin. rewrite andb_true_iff in Hin.
        destruct Hin; trivial.
        simpls. eapply make_constr_lt0_r_correct in H; trivial. split; trivial.
        destruct (dot_product v2 p2 + c2)%Z eqn:Hd; tryfalse; trivial.
       }
       {
         eapply IHsched2 in Hexists; trivial.
         destruct Hexists as (Hpol & Hgt).
         rewrite in_poly_app in Hpol. rewrite andb_true_iff in Hpol. destruct Hpol.
         splits; trivial.
         eapply make_constrs_eq0_r_correct in H; trivial.
         simpl. rewrite H.
         simpl in Hgt.
         destruct (affine_product sched2 p2) eqn:Hts2; tryfalse.
         rewrite <- Hts2 in Hgt. trivial.
       }
    }
  }
Qed.

Definition make_constr_gt0_l (aff: (list Z * Z)) (dim2: nat): (list Z * Z) := 
  let (v1, c1) := aff in 
  let v := --v1 ++ (V0 dim2) in
  (v, (c1-1)%Z).

Lemma make_constr_gt0_l_correct: 
  forall dim2 v1 c1 p1 p2, 
    length p1 = length v1 ->
    (dot_product v1 p1 + c1 > 0)%Z <->
    satisfies_constraint (p1++p2) (make_constr_gt0_l (v1, c1) dim2) = true.
Proof.
  intros. unfold make_constr_gt0_l.
  unfold satisfies_constraint.
  simpl. rewrite dot_product_app; trivial.
  rewrite dot_product_commutative.
  unfold V0. rewrite dot_product_repeat_zero_right.
  rewrite dot_product_opp_r.
  simpls; lia. 
  { 
    unfold "--". rewrite map_length. trivial.
  } 
Qed.

Definition make_constr_gt0_r (dim1: nat) (aff: (list Z * Z)): (list Z * Z) := 
  let (v2, c2) := aff in 
  let v := (V0 dim1) ++ (--v2) in
  (v, (c2-1)%Z).

Lemma make_constr_gt0_r_correct: 
  forall dim1 v2 c2 p1 p2, 
    length p1 = dim1 ->
    (dot_product v2 p2 + c2 > 0)%Z <->
    satisfies_constraint (p1++p2) (make_constr_gt0_r dim1 (v2, c2)) = true.
Proof.
  intros. unfold make_constr_gt0_r.
  unfold satisfies_constraint.
  simpl. rewrite dot_product_app; trivial.
  rewrite dot_product_commutative.
  unfold V0. rewrite dot_product_repeat_zero_right.
  rewrite dot_product_opp_r.
  simpls; lia. 
  { 
    unfold V0. rewrite repeat_length. trivial.
  } 
Qed.

Fixpoint make_poly_gt0_l
(sched1: Schedule) (dim2: nat)
(pol: polyhedron)
: list polyhedron:=
match sched1 with
  | [] => []
  | aff1 :: sched1' =>
    (make_constr_gt0_l aff1 dim2 :: pol) ::
    (make_poly_gt0_l sched1' dim2 (make_constrs_eq0_l aff1 dim2 ++ pol))
end.

Lemma make_poly_gt0_l_correct: 
  forall sched1 p1 p2 dim2 pol, 
    exact_listzzs_cols (length p1) sched1 ->
    (in_poly (p1 ++ p2) pol = true /\
    lex_compare (affine_product sched1 p1) [] = Gt) <-> 
    Exists (fun pol => in_poly (p1 ++ p2) pol = true) (make_poly_gt0_l sched1 dim2 pol).
Proof. 
  induction sched1.
  {
    intros until pol. intros Hlen.
    simpls. split; intro.
    {
      destruct H; tryfalse.
    }
    {
      inv H; tryfalse.
    }
  }
  {
    intros until pol. intros Hlen.
    destruct a as (v1, c1) eqn:Hconstr1. 
    unfold affine_product. 
    split; intro.
    {
      eapply Exists_cons.
      destruct H.
      simpl in H0. 
      destruct (dot_product v1 p1 + c1)%Z eqn:Hprod; tryfalse; try lia.
      {
        (* equal 0 *)
        right.
        eapply IHsched1; eauto. 
        {
          clear - Hlen; firstorder.
        }
        split.
        {
          rewrite in_poly_app. rewrite andb_true_iff. split; trivial.
          (* unfold in_poly. unfold forallb. *)
          eapply make_constrs_eq0_l_correct; eauto.
          {
            clear - Hlen. unfold exact_listzzs_cols in Hlen. 
            symmetry.
            eapply Hlen; eauto. eapply in_eq.
          }
        }
        {
          simpl. 
          destruct (affine_product sched1 p1) eqn:Hts1.
          {
            unfold affine_product in Hts1.
            rewrite Hts1 in H0.
            simpl; tryfalse.
          } 
          {
            rewrite <- Hts1. 
            rewrite lex_compare_nil_right. unfold affine_product; trivial.  
          }
        }
      }
      {
        (* 0 < *)
        left.
        unfold in_poly. unfold forallb. rewrite andb_true_iff. 
        split; trivial.
        eapply make_constr_gt0_l_correct; try lia.
        {
          clear - Hlen.
          symmetry. eapply Hlen; eauto. eapply in_eq.
        }
      }
    }
    {
      eapply Exists_cons in H. 
      destruct H as [Hin | Hexists].
      {
        simpl in Hin. rewrite andb_true_iff in Hin.
        destruct Hin; trivial.
        simpls. eapply make_constr_gt0_l_correct in H; trivial. split; trivial.
        destruct (dot_product v1 p1 + c1)%Z eqn:Hd; tryfalse; trivial.
        {
          clear - Hlen.
          symmetry. eapply Hlen; eauto. eapply in_eq.
        }
      }
      {
        eapply IHsched1 in Hexists; trivial.
        2: {clear - Hlen; firstorder. }
        destruct Hexists as (Hpol & Hgt).
        rewrite in_poly_app in Hpol. rewrite andb_true_iff in Hpol. destruct Hpol.
        splits; trivial.
        eapply make_constrs_eq0_l_correct in H; trivial.
        2: {clear - Hlen. symmetry. eapply Hlen; eauto. eapply in_eq. }
        simpl. rewrite H.
        
        rewrite lex_compare_nil_right in Hgt. 
        unfold affine_product in Hgt. trivial.
      }
    }
  }
Qed.

Fixpoint make_poly_gt0_r
(dim1: nat) (sched2: Schedule)
(pol: polyhedron)
: list (polyhedron):=
match sched2 with
  | [] => []
  | aff2 :: sched2' =>
    (make_constr_gt0_r dim1 aff2 :: pol) ::
    (make_poly_gt0_r dim1 sched2' (make_constrs_eq0_r dim1 aff2 ++ pol))
end.

Lemma make_poly_gt0_r_correct: 
  forall sched2 p1 p2 dim1 pol, 
    length p1 = dim1 ->
    (in_poly (p1 ++ p2) pol = true /\
    lex_compare (affine_product sched2 p2) [] = Gt) <-> 
    Exists (fun pol => in_poly (p1 ++ p2) pol = true) (make_poly_gt0_r dim1 sched2 pol).
Proof. 
  induction sched2.
  {
    intros until pol. intros Hlen.
    simpls. split; intro.
    {
      destruct H; tryfalse.
    }
    {
      inv H; tryfalse.
    }
  }
  {
    intros until pol. intros Hlen.
    destruct a as (v2, c2) eqn:Hconstr2. 
    unfold affine_product. 
    split; intro.
    {
      eapply Exists_cons.
      destruct H.
      simpl in H0. 
      destruct (dot_product v2 p2 + c2)%Z eqn:Hprod; tryfalse; try lia.
      {
        (* equal 0 *)
        right.
        eapply IHsched2; eauto. 
        split.
        {
          rewrite in_poly_app. rewrite andb_true_iff. split; trivial.
          (* unfold in_poly. unfold forallb. *)
          eapply make_constrs_eq0_r_correct; eauto.
        }
        {
          simpl. 
          destruct (affine_product sched2 p2) eqn:Hts2.
          {
            unfold affine_product in Hts2.
            rewrite Hts2 in H0.
            simpl; tryfalse.
          } 
          {
            rewrite <- Hts2. 
            rewrite lex_compare_nil_right. unfold affine_product; trivial.  
          }
        }
      }
      {
        (* 0 < *)
        left.
        unfold in_poly. unfold forallb. rewrite andb_true_iff. 
        split; trivial.
        eapply make_constr_gt0_r_correct; try lia.
      }
    }
    {
      eapply Exists_cons in H. 
      destruct H as [Hin | Hexists].
      {
        simpl in Hin. rewrite andb_true_iff in Hin.
        destruct Hin; trivial.
        simpls. 
        eapply make_constr_gt0_r_correct in H; trivial. split; trivial.
        destruct (dot_product v2 p2 + c2)%Z eqn:Hd; tryfalse; trivial.
      }
      {
        eapply IHsched2 in Hexists; trivial.
        destruct Hexists as (Hpol & Hgt).
        rewrite in_poly_app in Hpol. rewrite andb_true_iff in Hpol. destruct Hpol.
        splits; trivial.
        eapply make_constrs_eq0_r_correct in H; trivial.
        simpl. rewrite H.
        
        rewrite lex_compare_nil_right in Hgt. 
        unfold affine_product in Hgt. trivial.
      }
    }
  }
Qed.
(* Fixpoint make_poly_gt0_r
(dim1: nat) (sched2: Schedule)
(pol: polyhedron)
: list (polyhedron):=
match sched2 with
  | [] => []
  | aff2 :: sched2' =>
    let (v2, c2) := aff2 in
    let v := (V0 dim1) ++ (-- v2) in
    ((v, (1+c2)%Z) :: pol) ::
    (make_poly_gt0_r dim1 sched2' ((v, c2%Z) :: ((-- v, (-c2)%Z) :: pol)))
end. *)

Definition make_constr_lt (aff1 aff2: (list Z * Z)): (list Z * Z) :=
  let (v1, c1) := aff1 in 
  let (v2, c2) := aff2 in 
  (v1 ++ (-- v2), (-c1+c2-1)%Z).

Lemma make_constr_lt_correct: 
  forall p1 p2 v1 v2 c1 c2,
  length p1 = length v1 ->
  satisfies_constraint (p1 ++ p2) (make_constr_lt (v1, c1) (v2, c2)) = true <->
  (dot_product v1 p1 + c1 < dot_product v2 p2 + c2)%Z.
Proof.
  intros. unfolds satisfies_constraint.
  simpls. 
  rewrite dot_product_app; trivial.
  rewrite dot_product_opp_r.
  rewrite dot_product_commutative.
  replace (dot_product v2 p2) with (dot_product p2 v2). 2: {
    eapply dot_product_commutative.
  }
  lia.
Qed.

Definition make_constrs_eq (aff1 aff2: (list Z * Z)): polyhedron :=
  let (v1, c1) := aff1 in 
  let (v2, c2) := aff2 in 
  let v := ( v1 ++ (-- v2)) in
  (v, (c2-c1)%Z) :: (-- v, (c1-c2)%Z) :: nil.

Lemma make_constrs_eq_correct: 
  forall p1 p2 v1 v2 c1 c2,
  length p1 = length v1 ->
  in_poly (p1 ++ p2) (make_constrs_eq (v1, c1) (v2, c2)) = true <->
  (dot_product v1 p1 + c1)%Z = (dot_product v2 p2 + c2)%Z.
Proof. 
  intros. split; intro. 
  {
    simpls. unfolds satisfies_constraint; simpls.
    rewrite opp_app in H0. rewrite opp_opp in H0.
    rewrite dot_product_app in H0; trivial.
    rewrite dot_product_opp_r in H0.
    do 2 rewrite andb_true_iff in H0.
    destruct H0 as (Hlt & Hgt & _).
    assert ((dot_product v1 p1 + c1 <=? dot_product v2 p2 + c2)%Z = true). 
    {
      rewrite dot_product_commutative in Hlt. 
      replace (dot_product v2 p2) with (dot_product p2 v2). 2: {
        eapply dot_product_commutative.
      }
      lia.
    }
    assert ((dot_product v2 p2 + c2 <=? dot_product v1 p1 + c1)%Z = true). {
      rewrite dot_product_app in Hgt; trivial.
      2: {
        unfold "--". rewrite map_length. subst; trivial.
      }
      rewrite dot_product_opp_r in Hgt. 
      rewrite dot_product_commutative in Hgt.
      rewrite dot_product_commutative.
      lia. 
    }
    lia.
  }
  {
    simpls. unfolds satisfies_constraint; simpls.
    rewrite opp_app. rewrite opp_opp.
    rewrite dot_product_app; trivial.
    rewrite dot_product_app; trivial.
    do 2 rewrite dot_product_opp_r. 
    do 2 rewrite andb_true_iff.
    rewrite dot_product_commutative in H0.
    replace (dot_product v2 p2) with (dot_product p2 v2) in H0. 2: {
      eapply dot_product_commutative.
    }
    splits; trivial; try lia.
    {
      unfold "--". rewrite map_length. trivial.
    }
  }
Qed.

(** define a list of polyhedron testing two instances p1 & p2 schedule having sched1(p1) < sched2(p2);
    each polyhedron test specific dimension `n`, asserting firstn (n-1) p1 = firstn (n-1) p2 and nth n p1 < nth n p2.   
    dim1 is just length of (sched1[0])
    dim2 is just length of (sched2[0]);
    a list of polyhedron that test lex order. generate test poly for one dim at one time.
*)

Fixpoint make_poly_lt 
(sched1: Schedule) (sched2: Schedule) (dim1 dim2: nat)
(pol: polyhedron)
: list polyhedron:=
  match sched1, sched2 with
    | [], [] => []
    | aff1 :: sched1', aff2 :: sched2' =>
      (make_constr_lt aff1 aff2 :: pol) :: (** v1 <= v2; timestamp1 <= timestamp2*)
      (make_poly_lt sched1' sched2' dim1 dim2 (make_constrs_eq aff1 aff2 ++ pol))  (** ts1 = ts2 *)
    | v1 :: sched1', [] =>
      make_poly_lt0_l sched1 dim2 pol 
    | [], v2 :: sched2' =>
      make_poly_gt0_r dim1 sched2 pol
  end.

Lemma make_poly_lt_correct':
  forall sched1 sched2 p1 p2 dim1 dim2 pol ,
    length p1 = dim1 ->
    length p2 = dim2 ->
    exact_listzzs_cols dim1 sched1 ->
    (in_poly (p1 ++ p2) pol = true /\
    lex_compare (affine_product sched1 p1) (affine_product sched2 p2) = Lt) <->
    Exists 
    (fun pol => 
      in_poly (p1 ++ p2) pol = true
    )
    (make_poly_lt sched1 sched2 dim1 dim2 pol).
Proof.
  induction sched1.
  {
    intros until pol. intros Hlen1 Hlen2 Hwf1.
    split; intro.
    {
      destruct H as (Hin & Hlt).
      destruct sched2 eqn:Hsched2.
      {
        simpls; trivial; tryfalse.
      }
      {
        rewrite affine_product_nil_l_eq_nil in Hlt.
        unfold make_poly_lt. 
        eapply make_poly_gt0_r_correct; eauto.
        split; trivial.
        rewrite lex_compare_antisym.
        rewrite Hlt. trivial.
      }
    }
    {
      split.
      {
        unfold make_poly_lt in H. 
        destruct sched2 eqn:Hsched2.
        {
          inv H; tryfalse.
        }
        {
          eapply make_poly_gt0_r_correct in H; trivial.
          destruct H; trivial.
        }
      }
      {
        unfold make_poly_lt in H. 
        destruct sched2 eqn:Hsched2.
        {
          inv H; tryfalse.
        }
        {
          eapply make_poly_gt0_r_correct in H; trivial.
          destruct H; trivial.
          rewrite affine_product_nil_l_eq_nil.
          rewrite lex_compare_antisym.
          rewrite H0. trivial.
        }
      } 
    }
  }
  {
    intros until pol. intros Hlen1 Hlen2 Hwf1.
    split; intro. 
    {
      destruct H as (Hin & Hlt).
      destruct sched2 eqn:Hsched2.
      {
        subst. 
        unfold make_poly_lt.
        rewrite affine_product_nil_l_eq_nil in Hlt; trivial.
        eapply make_poly_lt0_l_correct; eauto.
        split; trivial.
        rewrite lex_compare_antisym.
        rewrite Hlt. trivial.
      }
      (* case: sched1 & sched2 not nil *)
      rename a into constr1; rename p into constr2.
      simpls.

      rewrite Exists_cons.
      destruct constr1 as (v1, c1) eqn:Hconstr1.
      destruct constr2 as (v2, c2) eqn:Hconstr2.
      destruct (dot_product v1 p1 + c1 ?= dot_product v2 p2 + c2)%Z eqn:Hhd.
      {
        (* case: head eq *)
        right.
        {
          eapply IHsched1; trivial.
          {
            clear - Hwf1.
            firstorder.
          }
          {
            simpl in Hlt; rewrite Hhd in Hlt; trivial.
            rewrite in_poly_app.
            rewrite andb_true_iff. split; trivial. split; trivial.
            eapply make_constrs_eq_correct. 
            {
              clear - Hwf1 Hlen1. subst.
              unfold exact_listzzs_cols in Hwf1. symmetry.
              eapply Hwf1.
              subst; firstorder. eexists.
            }
            eapply Z.compare_eq in Hhd; trivial.
          }
        }
      }
      {
        (* case: head gt. *)
        assert (length p1 = length v1). {
          clear - Hwf1 Hlen1.
          unfold exact_listzzs_cols in Hwf1. subst. symmetry. eapply Hwf1; eauto. eapply in_eq.
        }
        left. 
        simpl in Hlt. rewrite Hhd in Hlt.
        replace (make_constr_lt (v1, c1) (v2, c2) :: pol) with ([make_constr_lt (v1, c1) (v2, c2)] ++ pol).
        2: {simpl; trivial. }
        rewrite in_poly_app. rewrite andb_true_iff. split; trivial. 
        simpl. rewrite andb_true_iff; split; trivial. 
        eapply make_constr_lt_correct; eauto.
      }
      {
        (* case: head lt *)
        simpl in Hlt. rewrite Hhd in Hlt. tryfalse. 
      }
    }
    {
      destruct sched2 eqn:Hsched2.
      {
        subst. 
        unfold make_poly_lt in H.
        rewrite affine_product_nil_l_eq_nil; trivial.
        eapply make_poly_lt0_l_correct in H; eauto.
        destruct H as (Hpol & Hlt).
        split; trivial.
        rewrite lex_compare_antisym.
        rewrite Hlt. trivial.
      }
      (* case: sched1 & sched2 not nil *)
      rename a into constr1; rename p into constr2.
      destruct constr1 as (v1, c1) eqn:Hconstr1.
      destruct constr2 as (v2, c2) eqn:Hconstr2. rename l into sched2'.
      eapply Exists_cons in H. destruct H as [Hin | Hpol].
      {
        replace (make_constr_lt (v1, c1) (v2, c2) :: pol) with ([make_constr_lt (v1, c1) (v2, c2)] ++ pol) in Hin. 
        2: {simpl. trivial. }
        rewrite in_poly_app in Hin. rewrite andb_true_iff in Hin. destruct Hin.
        split; trivial.
        simpls.
        rewrite andb_true_iff in H. destruct H as (H & _).
        assert (length p1 = length v1). {
            clear - Hwf1 Hlen1.
            unfold exact_listzzs_cols in Hwf1. subst. symmetry. eapply Hwf1; eauto. eapply in_eq.
        }
        eapply make_constr_lt_correct in H; trivial. rewrite H. trivial.
      }
      {
        eapply IHsched1 in Hpol; trivial.
        {
          destruct Hpol as (Hpol & Hgt).
          rewrite in_poly_app in Hpol.
          rewrite andb_true_iff in Hpol.
          destruct Hpol as (Hpol1 & Hpol2). split; trivial.
          simpl. rewrite Hgt. 
          eapply make_constrs_eq_correct in Hpol1. rewrite Hpol1.
          rewrite Z.compare_refl; trivial.
          {
            clear - Hwf1 Hlen1. subst.
            unfold exact_listzzs_cols in Hwf1. symmetry.
            eapply Hwf1.
            subst; firstorder. eexists.
          }
        }
        {
          clear - Hwf1.
          firstorder.
        }
      }
    }
  }
Qed.

Lemma make_poly_lt_correct: 
  forall sched1 p1 sched2 p2 dim1 dim2,
    length p1 = dim1 ->
    length p2 = dim2 ->
    exact_listzzs_cols dim1 sched1 ->
    lex_compare (affine_product sched1 p1) (affine_product sched2 p2) = Lt <->
    Exists 
    (fun pol => 
      in_poly (p1 ++ p2) pol = true
    )
    (make_poly_lt sched1 sched2 dim1 dim2 []).
Proof.
  intros.
  eapply make_poly_lt_correct' with (pol:=[]) (sched2:=sched2) in H1; eauto.
  rewrite <- H1. unfold in_poly. unfold forallb. 
  firstorder.
Qed.

(* Fixpoint make_poly_lt 
(sched1: Schedule) (sched2: Schedule) (dim1 dim2: nat)
(pol: polyhedron)
: list polyhedron:=
  match sched1, sched2 with
    | [], [] => []
    | aff1 :: sched1', aff2 :: sched2' =>
      let (v1, c1) := aff1 in 
      let (v2, c2) := aff2 in  
      let v := v1 ++ (-- v2) in
      ((v, (1-c1+c2)%Z) :: pol) :: (** v1 <= v2; timestamp1 <= timestamp2*)
      (make_poly_lt sched1' sched2' dim1 dim2 ((v, (c2-c1)%Z) :: ((-- v, (c1-c2)%Z) :: pol)))  (** ts1 = ts2 *)
    | v1 :: sched1', [] =>
      make_poly_lt0_l sched1 dim2 pol 
    | [], v2 :: sched2' =>
      make_poly_gt0_r dim1 sched2 pol
  end. *)

Definition make_constr_gt (aff1 aff2: (list Z * Z)): (list Z * Z) :=
  let (v1, c1) := aff1 in 
  let (v2, c2) := aff2 in 
  (--v1 ++ v2, (c1-c2-1)%Z).

Lemma make_constr_gt_correct: 
  forall p1 p2 v1 v2 c1 c2,
  length p1 = length v1 ->
  satisfies_constraint (p1 ++ p2) (make_constr_gt (v1, c1) (v2, c2)) = true <->
  Z.gt (dot_product v1 p1 + c1)%Z  (dot_product v2 p2 + c2)%Z.
Proof.
  intros until c2. intros Hlen. unfold make_constr_gt. split; intro.
  {
    unfold satisfies_constraint in H. 
    simpl in H. 
    rewrite dot_product_app in H. rewrite dot_product_opp_r in H.
    2: {
      unfold "--". rewrite map_length. trivial. 
    }
    rewrite Z.leb_le in H. 
    rewrite dot_product_commutative in H.  
    replace (dot_product p2 v2) with (dot_product v2 p2) in H. 2: {eapply dot_product_commutative. }
    lia.
  }
  {
    unfold satisfies_constraint.
    simpl. rewrite dot_product_app. 
    2: {
      unfold "--". rewrite map_length. trivial.
    }
    rewrite dot_product_opp_r. 
    rewrite dot_product_commutative. 
    replace (dot_product p2 v2) with (dot_product v2 p2). 2: {eapply dot_product_commutative. }
    lia.
  }
Qed.

Fixpoint make_poly_gt 
(sched1: Schedule) (sched2: Schedule)
(dim1 dim2: nat)
(pol: polyhedron)
: list polyhedron:=
match sched1, sched2 with
  | [], [] => []
  | aff1 :: sched1', aff2 :: sched2' =>
    (make_constr_gt aff1 aff2 :: pol) ::
    (make_poly_gt sched1' sched2' dim1 dim2 (make_constrs_eq aff1 aff2 ++ pol))
  | v1 :: sched1', nil =>
    make_poly_gt0_l sched1 dim2 pol 
  | [], v2 :: sched2' =>
    make_poly_lt0_r dim1 sched2 pol
end.



(* Lemma affine_product_nil_r_eq_nil: 
  forall sched, 
  affine_product sched [] = [].
Proof. 
  intros. unfold affine_product. *)

(* Fixpoint lex_compare_n t1 t2 n := 
  match t1, t2, n with

  | nil, nil => Eq
  | _, nil => CompOpp (lex_compare_nil t1)
  | nil, _ => lex_compare_nil t2
  | x :: t1, y :: t2 => match x ?= y with Eq => lex_compare t1 t2 | c => c end
  end. *)

(* Only soundness. If completeness is needed, more premises are needed, *)
(* To clarify the semantics of parameter `pol` *)
Lemma make_poly_gt_correct':
  forall sched1 sched2 p1 p2 dim1 dim2 pol ,
    length p1 = dim1 ->
    length p2 = dim2 ->
    exact_listzzs_cols dim1 sched1 ->
    (in_poly (p1 ++ p2) pol = true /\
    lex_compare (affine_product sched1 p1) (affine_product sched2 p2) = Gt) <->
    Exists 
    (fun pol => 
      in_poly (p1 ++ p2) pol = true
    )
    (make_poly_gt sched1 sched2 dim1 dim2 pol).
Proof.
  induction sched1.
  {
    intros until pol. intros Hlen1 Hlen2 Hwf1.
    split; intro.
    {
      destruct H as (Hin & Hgt).
      destruct sched2 eqn:Hsched2.
      {
        simpls; trivial; tryfalse.
      }
      {
        rewrite affine_product_nil_l_eq_nil in Hgt.
        unfold make_poly_gt. 
        eapply make_poly_lt0_r_correct; eauto.
      }
    }
    {
      split.
      {
        unfold make_poly_gt in H. 
        destruct sched2 eqn:Hsched2.
        {
          inv H; tryfalse.
        }
        {
          eapply make_poly_lt0_r_correct in H; trivial.
          destruct H; trivial.
        }
      }
      {
        unfold make_poly_gt in H. 
        destruct sched2 eqn:Hsched2.
        {
          inv H; tryfalse.
        }
        {
          eapply make_poly_lt0_r_correct in H; trivial.
          destruct H; trivial.
        }
      } 
    }
  }
  {
    intros until pol. intros Hlen1 Hlen2 Hwf1.
    split; intro. 
    {
      destruct H as (Hin & Hgt).
      destruct sched2 eqn:Hsched2.
      {
        subst. 
        unfold make_poly_gt.
        rewrite affine_product_nil_l_eq_nil in Hgt; trivial.
        eapply make_poly_gt0_l_correct; eauto.
      }
      (* case: sched1 & sched2 not nil *)
      rename a into constr1; rename p into constr2.
      simpls.

      rewrite Exists_cons.
      destruct constr1 as (v1, c1) eqn:Hconstr1.
      destruct constr2 as (v2, c2) eqn:Hconstr2.
      destruct (dot_product v1 p1 + c1 ?= dot_product v2 p2 + c2)%Z eqn:Hhd.
      {
        (* case: head eq *)
        right.
        {
          eapply IHsched1; trivial.
          {
            clear - Hwf1.
            firstorder.
          }
          {
            simpl in Hgt; rewrite Hhd in Hgt; trivial.
            rewrite in_poly_app.
            rewrite andb_true_iff. split; trivial. split; trivial.
            eapply make_constrs_eq_correct. 
            {
              clear - Hwf1 Hlen1. subst.
              unfold exact_listzzs_cols in Hwf1. symmetry.
              eapply Hwf1.
              subst; firstorder. eexists.
            }
            eapply Z.compare_eq in Hhd; trivial.
          }
        }
      }
      {
        (* case: head lt *)
        simpl in Hgt. rewrite Hhd in Hgt. tryfalse. 
      }
      {
        (* case: head gt. *)
        assert (length p1 = length v1). {
          clear - Hwf1 Hlen1.
          unfold exact_listzzs_cols in Hwf1. subst. symmetry. eapply Hwf1; eauto. eapply in_eq.
        }
        left. 
        simpl in Hgt. rewrite Hhd in Hgt.
        replace (make_constr_gt (v1, c1) (v2, c2) :: pol) with ([make_constr_gt (v1, c1) (v2, c2)] ++ pol).
        2: {simpl; trivial. }
        rewrite in_poly_app. rewrite andb_true_iff. split; trivial. 
        simpl. rewrite andb_true_iff; split; trivial. 
        eapply make_constr_gt_correct; eauto.
      }
    }
    {
      destruct sched2 eqn:Hsched2.
      {
        subst. 
        unfold make_poly_gt in H.
        rewrite affine_product_nil_l_eq_nil; trivial.
        eapply make_poly_gt0_l_correct in H; eauto.
      }
      (* case: sched1 & sched2 not nil *)
      rename a into constr1; rename p into constr2.
      destruct constr1 as (v1, c1) eqn:Hconstr1.
      destruct constr2 as (v2, c2) eqn:Hconstr2. rename l into sched2'.
      eapply Exists_cons in H. destruct H as [Hin | Hpol].
      {
        replace (make_constr_gt (v1, c1) (v2, c2) :: pol) with ([make_constr_gt (v1, c1) (v2, c2)] ++ pol) in Hin. 
        2: {simpl. trivial. }
        rewrite in_poly_app in Hin. rewrite andb_true_iff in Hin. destruct Hin.
        split; trivial.
        simpls.
        rewrite andb_true_iff in H. destruct H as (H & _).
        assert (length p1 = length v1). {
            clear - Hwf1 Hlen1.
            unfold exact_listzzs_cols in Hwf1. subst. symmetry. eapply Hwf1; eauto. eapply in_eq.
        }
        eapply make_constr_gt_correct in H; trivial. rewrite H. trivial.
      }
      {
        eapply IHsched1 in Hpol; trivial.
        {
          destruct Hpol as (Hpol & Hgt).
          rewrite in_poly_app in Hpol.
          rewrite andb_true_iff in Hpol.
          destruct Hpol as (Hpol1 & Hpol2). split; trivial.
          simpl. rewrite Hgt. 
          eapply make_constrs_eq_correct in Hpol1. rewrite Hpol1.
          rewrite Z.compare_refl; trivial.
          {
            clear - Hwf1 Hlen1. subst.
            unfold exact_listzzs_cols in Hwf1. symmetry.
            eapply Hwf1.
            subst; firstorder. eexists.
          }
        }
        {
          clear - Hwf1.
          firstorder.
        }
      }
    }
  }
Qed.


Lemma make_poly_gt_correct: 
  forall sched1 p1 sched2 p2 dim1 dim2,
    length p1 = dim1 ->
    length p2 = dim2 ->
    exact_listzzs_cols dim1 sched1 ->
    lex_compare (affine_product sched1 p1) (affine_product sched2 p2) = Gt ->
    Exists 
    (fun pol => 
      in_poly (p1 ++ p2) pol = true
    )
    (make_poly_gt sched1 sched2 dim1 dim2 []).
Proof.
  intros.
  eapply make_poly_gt_correct'; eauto.
Qed.


(* Fixpoint make_poly_gt 
  (sched1: Schedule) (sched2: Schedule)
  (dim1 dim2: nat)
  (pol: polyhedron)
  : list polyhedron:=
  match sched1, sched2 with
    | [], [] => []
    | aff1 :: sched1', aff2 :: sched2' =>
      let (v1, c1) := aff1 in 
      let (v2, c2) := aff2 in  
      let v := (-- v1) ++ v2 in
      ((v, (1-c1+c2)%Z) :: pol) ::
      (make_poly_gt sched1' sched2' dim1 dim2 ((v, (c2-c1)%Z) :: ((-- v, (c1-c2)%Z) :: pol)))
    | v1 :: sched1', nil =>
      make_poly_gt0_l sched1 dim2 pol 
    | [], v2 :: sched2' =>
      make_poly_lt0_r dim1 sched2 pol
  end. *)

(* make poly, asserting all sched1*p1 + c1 should be equal to zero *)
Fixpoint make_poly_all0_l
  (sched1: Schedule) (dim2: nat)
  (pol: polyhedron) : polyhedron:=
  match sched1 with
    | [] => pol
    | aff1 :: sched1' =>
      let (v1, c1) := aff1 in 
      let v := (-- v1) ++ (V0 dim2) in
      (* 0 <= v1*p1 + c1 *) (* v1*p1 + c1 <= 0 *)
      (v, c1) :: ((-- v, Z.opp c1) :: 
      (make_poly_all0_l sched1' dim2 pol))
  end.  

Lemma make_poly_all0_l_correct: 
  forall sched1 dim2 pol p1 p2,
    make_poly_all0_l sched1 dim2 [] = pol -> 
    exact_listzzs_cols (length p1) sched1 -> 
    (in_poly (p1 ++ p2) pol = true <-> 
    is_null (affine_product sched1 p1) = true).
Proof.
  induction sched1; intros; subst; simpls.
  {
    firstorder.
  }
  {
    destruct a as [v1 c1].
    simpls.
    split; intro. 
    {
      do 2 rewrite andb_true_iff in H.
      rewrite andb_true_iff.
      destruct H as (G & L & H).
      split.
      {
        assert ((dot_product v1 p1 + c1 <=? 0)%Z = true). {
          clear - L H0.
          unfolds satisfies_constraint. simpls.
          rewrite opp_app in L. 
          rewrite opp_opp in L. 
          rewrite dot_product_app in L.
          2: {
            clear - H0.
            symmetry.
            unfolds exact_listzzs_cols. 
            eapply H0; eauto. eapply in_eq.
          }
          rewrite opp_v0_v0 in L.
          unfold V0.
          rewrite dot_product_repeat_zero_right in L. 
          rewrite Z.leb_le in L. rewrite Z.leb_le. 
          rewrite dot_product_commutative.
          lia.
        }
        assert ((0 <=? dot_product v1 p1 + c1)%Z = true). {
          clear - G H0.
          unfolds satisfies_constraint; simpls.
          rewrite dot_product_app in G. 
          2: {
            unfold "--". 
            rewrite map_length. 
            symmetry.
            eapply H0; eauto. eapply in_eq.
          }
          rewrite dot_product_opp_r in G.
          unfold V0 in G. rewrite dot_product_repeat_zero_right in G.
          rewrite Z.leb_le in G. rewrite Z.leb_le. 
          rewrite dot_product_commutative.
          lia.
        }
        lia.
      }
      {
        eapply IHsched1; eauto.
        clear - H0. firstorder.
      }
    }
    {
      do 2 rewrite andb_true_iff.
      rewrite andb_true_iff in H.
      destruct H.
      splits.
      {
        unfold satisfies_constraint; simpls.
        rewrite dot_product_app. 
        2: {
          clear - H0.
          unfold "--". rewrite map_length.
          symmetry. eapply H0; eauto. eapply in_eq.
        }
        rewrite dot_product_opp_r. 
        unfold V0. rewrite dot_product_repeat_zero_right. 
        rewrite Z.leb_le.
        rewrite Z.eqb_eq in H.
        symmetry in H.
        eapply Z.eq_le_incl in H. 
        rewrite dot_product_commutative. lia. 
      }
      {
        unfold satisfies_constraint; simpls.
        rewrite opp_app. rewrite opp_opp. rewrite opp_v0_v0. 
        rewrite dot_product_app. 
        2: {
          clear - H0.
          symmetry. eapply H0; eauto. eapply in_eq.
        }
        unfold V0. rewrite dot_product_repeat_zero_right. 
        rewrite Z.leb_le.
        rewrite Z.eqb_eq in H.
        eapply Z.eq_le_incl in H. 
        rewrite dot_product_commutative. lia. 
      }
      {
        eapply IHsched1; eauto.
        clear - H0. firstorder.
      }
    }
  }
Qed.

Fixpoint make_poly_all0_r
  (dim1: nat) (sched2: Schedule)
  (pol: polyhedron) : polyhedron:=
  match sched2 with
    | [] => pol
    | aff2 :: sched2' =>
      let (v2, c2) := aff2 in 
      let v := (-- (V0 dim1)) ++ v2 in
      (* v2*p2 + c2 <= 0 *) (* 0 <= v2*p2 + c2 *)
      (v, Z.opp c2) :: ((-- v, c2) :: 
      (make_poly_all0_r dim1 sched2' pol))
  end.

Lemma make_poly_all0_r_correct:
  forall sched2 dim1 pol p1 p2,
    make_poly_all0_r dim1 sched2 [] = pol -> 
    length p1 = dim1 ->
    (in_poly (p1 ++ p2) pol = true <-> 
    is_null (affine_product sched2 p2) = true).
Proof.
  induction sched2; intros; simpls.
  {
    subst; firstorder.
  }
  {
    destruct a as [v2 c2].
    simpls.
    split; intro. 
    {
      rewrite <- H in H1; simpls.
      do 2 rewrite andb_true_iff in H1.
      rewrite andb_true_iff.
      simpls.
      destruct H1 as (G & L & H1).
      split.
      {
        assert ((dot_product v2 p2 + c2 <=? 0)%Z = true). {
          clear - G H0.
          unfolds satisfies_constraint; simpls.
          rewrite dot_product_app in G. 
          2: {
            unfold V0. unfold "--". 
            rewrite map_length.
            rewrite repeat_length. trivial.
          }
          rewrite dot_product_opp_r in G.
          unfold V0 in G. rewrite dot_product_repeat_zero_right in G.
          rewrite Z.leb_le in G. rewrite Z.leb_le. 
          rewrite dot_product_commutative.
          lia.
        }
        assert ((0 <=? dot_product v2 p2 + c2)%Z = true). {
          clear - L H1 H0.
          unfolds satisfies_constraint. simpls.
          rewrite opp_app in L. 
          rewrite opp_opp in L. 
          rewrite dot_product_app in L.
          2: {
            unfold V0. rewrite repeat_length. trivial.
          }
          unfold V0 in L. rewrite dot_product_repeat_zero_right in L. 
          rewrite dot_product_opp_r in L. 
          rewrite Z.leb_le in L. rewrite Z.leb_le. 
          rewrite dot_product_commutative. lia.
        }
        lia.
      }
      {
        eapply IHsched2; eauto.
      }
    }
    {
      rewrite <- H; simpls.
      do 2 rewrite andb_true_iff.
      rewrite andb_true_iff in H1.
      destruct H1.
      splits.
      {
        unfold satisfies_constraint; simpls.
        rewrite dot_product_app. 
        2: {
          clear - H0.
          unfold V0. unfold "--".
          rewrite map_length.
          rewrite repeat_length. trivial.
        }
        rewrite opp_v0_v0.
        unfold V0. 
        rewrite dot_product_repeat_zero_right. 
        rewrite Z.leb_le.
        rewrite Z.eqb_eq in H1.
        eapply Z.eq_le_incl in H1. 
        rewrite dot_product_commutative. lia. 
      }
      {
        unfold satisfies_constraint; simpls.
        rewrite opp_app. rewrite opp_opp. 
        rewrite dot_product_app. 
        2: {
          unfold V0.
          rewrite repeat_length. trivial.
        }
        rewrite dot_product_opp_r. 
        unfold V0. rewrite dot_product_repeat_zero_right. 
        rewrite Z.leb_le.
        rewrite Z.eqb_eq in H1.
        symmetry in H1.
        eapply Z.eq_le_incl in H1. 
        rewrite dot_product_commutative. lia. 
      }
      {
        eapply IHsched2; eauto.
      }
    }
  }
Qed.

(** sched1, sched2 can be any affine function. *)
Fixpoint make_poly_eq 
  (sched1: AffineFunction) (sched2: AffineFunction)
  (dim1 dim2: nat)
  (pol: polyhedron) : polyhedron :=
  match sched1, sched2 with
    | [], [] => pol
    | aff1 :: sched1', aff2 :: sched2' =>
      (* let (v1, c1) := aff1 in 
      let (v2, c2) := aff2 in 
      let v := (-- v1) ++ v2 in *)
      (* -v1*p1 + v2*p2 <= c1 - c2 -- v1*p1 + c1 >=  v2*p2 + c2*)
      (* v1*p1 - v2*p2 <= c2 - c1 -- v1*p1 + c1 <=  v2*p2 + c2*)      
      (* (v, (c1-c2)%Z) :: ((-- v, (c2-c1)%Z) ::  *)
      (make_constrs_eq aff1 aff2) ++ 
      (make_poly_eq sched1' sched2' dim1 dim2 pol)
    | v1 :: sched1', nil =>
      make_poly_all0_l sched1 dim2 pol 
    | [], v2 :: sched2' =>
      make_poly_all0_r dim1 sched2 pol
  end.

Lemma make_poly_eq_correct_true: 
  forall func1 func2 dim1 dim2 p1 p2,
    length p1 = dim1 -> 
    length p2 = dim2 -> 
    exact_listzzs_cols dim1 func1 ->
    in_poly (p1 ++ p2)
     (make_poly_eq func1 func2 dim1 dim2 []) = true
    <-> (veq (affine_product func1 p1) (affine_product func2 p2)). (* <- should also correct *)
Proof.
  induction func1; intros.
  {
    destruct func2 eqn:Hf2. 
    {
      simpls; firstorder.
    }
    rename p into constr; rename a into constrs.
    destruct constr as (v, c). 
    unfold make_poly_eq.
    eapply make_poly_all0_r_correct; eauto.
  }
  {
    destruct a as (v, c).
    unfold make_poly_eq.
    destruct func2 eqn:Hf2. 
    {
      rewrite <- H in H1.
      split; intro.
      eapply veq_sym. eapply make_poly_all0_l_correct; eauto.
      eapply veq_sym in H2. eapply make_poly_all0_l_correct; eauto.
    }
    rewrite in_poly_app.
    rewrite andb_true_iff. 
    destruct p as (v2, c2). rename a into func2'. rename v into v1. rename c into c1.
    split; intro.  
    {
        inv H2.
        eapply make_constrs_eq_correct in H3; eauto. simpls. rewrite H3. unfold veq; simpl.
        rewrite andb_true_iff. split; try lia. 
        eapply IHfunc1; eauto. 
        {
          clear - H1. firstorder.
        }
        {
          clear - H1. unfold exact_listzzs_cols in H1. symmetry. eapply H1; eauto. eapply in_eq.
        } 
    }
    {
      inversion H2. 
      rewrite andb_true_iff in H4.
      destruct H4.
      rewrite H3.
      eapply Z.eqb_eq in H3.
      eapply make_constrs_eq_correct in H3.
      rewrite H3. rewrite H4. splits; simpls; trivial.  
      eapply IHfunc1; eauto.
      {
        clear - H H1. firstorder.
      }
      {
        clear - H H1. 
        unfold exact_listzzs_cols in H1. symmetry. subst. eapply H1; eauto. eapply in_eq.
      }
  } 
  }
Qed.

Lemma make_poly_eq_correct_false: 
  forall func1 func2 dim1 dim2 p1 p2,
    length p1 = dim1 -> 
    length p2 = dim2 -> 
    exact_listzzs_cols dim1 func1 ->
    in_poly (p1 ++ p2)
     (make_poly_eq func1 func2 dim1 dim2 []) = false
    <-> ~veq (affine_product func1 p1) (affine_product func2 p2). 
Proof.
  intros. split; intro.
  {
    intro. eapply make_poly_eq_correct_true in H3; eauto. tryfalse.
  }
  {
    assert (~(in_poly (p1++p2) (make_poly_eq func1 func2 dim1 dim2 []) = true) -> 
      (in_poly (p1++p2) (make_poly_eq func1 func2 dim1 dim2 []) = false)
    ). {
      intro.
      destruct (in_poly (p1++p2) (make_poly_eq func1 func2 dim1 dim2 [])); tryfalse; trivial.
    }
    eapply H3.
    intro. eapply make_poly_eq_correct_true in H4; eauto.
  }
Qed.


Definition make_poly_ge
(sched1: Schedule) (sched2: Schedule)
(dim1 dim2: nat)
(pol: polyhedron)
: list (polyhedron):=
  (make_poly_eq sched1 sched2 dim1 dim2 pol) :: make_poly_gt sched1 sched2 dim1 dim2 pol.

(** TODO: completeness *)
Lemma make_poly_ge_correct: 
  forall sched1 p1 sched2 p2 dim1 dim2,
    length p1 = dim1 ->
    length p2 = dim2 ->
    exact_listzzs_cols dim1 sched1 ->
    (lex_compare (affine_product sched1 p1) (affine_product sched2 p2) = Eq \/ 
    lex_compare (affine_product sched1 p1) (affine_product sched2 p2) = Gt)
    ->
    Exists 
    (fun pol => 
      in_poly (p1 ++ p2) pol = true
    )
    (make_poly_ge sched1 sched2 dim1 dim2 []).
Proof. 
  intros. 
  {
    destruct H2 as [EQ | GT].
    {
      unfold make_poly_ge.
      eapply Exists_cons_hd.
      eapply is_eq_iff_cmp_eq in EQ.
      eapply make_poly_eq_correct_true in EQ; eauto.
    }
    {
      unfold make_poly_ge.
      eapply Exists_cons; right.
      eapply make_poly_gt_correct in GT; eauto.
    }
  }
  (* {
    unfold make_poly_ge in H2.
    eapply Exists_cons in H2. 
    destruct H2 as [EQ | GT].
    {
      eapply make_poly_eq_correct_true in EQ; eauto.
      left. eapply is_eq_iff_cmp_eq; eauto.
    }
    {      
      eapply make_poly_gt_correct in GT; eauto.
    }
  } *)
Qed.


Definition constr_transl_l (dim: nat) (constr: constraint) := 
  let (v, c) := constr in 
  let v' := v ++ V0 dim in 
  (v', c).

Lemma constr_transl_l_correct:
  forall p p' dim v c,
    length p = length v ->
    (satisfies_constraint (p++p') (constr_transl_l dim (v, c)) = true
    <-> satisfies_constraint p (v, c) = true).
Proof.
  induction p.
  {
    intros; simpls. 
    assert (v = []). {eapply length_zero_iff_nil; lia. }
    subst. simpls. 
    split; intro.
    { 
      unfolds satisfies_constraint. simpls.
      unfold V0 in H0.
      rewrite dot_product_repeat_zero_right in H0. trivial.
    }
    {
      unfolds satisfies_constraint; simpls.
      unfold V0.
      rewrite dot_product_repeat_zero_right. trivial.
    }
  }
  {
    intros; simpls.
    unfolds satisfies_constraint; simpls.
    destruct v eqn:Hv; tryfalse. simpls. inv H.
    eapply IHp with (p':=p') (dim:=dim) (c:=(c-a*z)%Z) in H1.
    split; intro; try lia.
  }
Qed.

Lemma map_constr_transl_l_correct: 
  forall constrs dim p p',
    exact_listzzs_cols (length p) constrs ->
    in_poly (p++p') (map (constr_transl_l dim) constrs) = true
    <-> in_poly p constrs = true.
Proof.
  induction constrs.
  {
    intros; simpls; firstorder.
  }
  {
    intros; simpls.
    split; intro.
    {
      rewrite andb_true_iff in H0.
      rewrite andb_true_iff.
      inv H0; split.
      {
        eapply constr_transl_l_correct with (p':=p') (dim:=dim); trivial.
        {
          destruct a as (v, c). simpls.
          unfold exact_listzzs_cols in H.
          pose proof (H v c (v, c)).
          rewrite H0; trivial. eapply in_eq.
        }
        {
          destruct a as (v, c); simpls. trivial.
        }
        
      }
      {
        eapply IHconstrs; eauto.
        clear - H; firstorder.
      }
    }
    {
      rewrite andb_true_iff in H0.
      rewrite andb_true_iff.
      inv H0; split.
      {
        eapply constr_transl_l_correct with (p':=p') (dim:=dim) in H1. simpls; trivial. 
        {
          destruct a as (v, c). simpls; trivial.
        }
        {
          destruct a as (v, c); simpls. 
          unfold exact_listzzs_cols in H.
          pose proof (H v c (v, c)).
          rewrite H3; trivial. eapply in_eq.
        }
      }
      {
        eapply IHconstrs; eauto.
        clear - H; firstorder.
      }
    }
  }
Qed.

Definition constr_transl_r (dim: nat) (constr: constraint) := 
  let (v, c) := constr in 
  let v' := V0 dim ++ v in 
  (v', c).

Lemma constr_transl_r_correct:
  forall p p' dim constr,
    length p = dim -> 
    satisfies_constraint (p++p') (constr_transl_r dim constr) = true
    <-> satisfies_constraint p' constr = true.
Proof.
  induction p.
  {
    intros; simpls.
    subst.
    unfold constr_transl_r. simpls. 
    destruct constr; trivial. firstorder.
  }
  {
    intros; simpls.
    subst. unfold constr_transl_r. simpls.
    destruct constr as (v, c) eqn:Hconstr.
    split.
    {
      intro.
      simpls.
      eapply IHp with (dim:=length p); trivial. 
      unfolds satisfies_constraint; simpls.
      unfold V0. lia.
    }
    {
      intro.
      eapply IHp with (dim:=length p) in H; trivial.
      unfolds satisfies_constraint; simpls.
      unfold V0 in H. lia.
    }
  }
Qed.

Lemma map_constr_transl_r_correct: 
  forall constrs dim p p',
    length p = dim -> 
    in_poly (p++p') (map (constr_transl_r dim) constrs) = true
    <-> in_poly (p') constrs = true.
Proof.
  induction constrs.
  {
    intros; simpls. firstorder.
  }
  {
    intros; simpls.
    do 2 rewrite andb_true_iff.
    split; intro.
    {

      inv H0.
      split.
      {
        eapply constr_transl_r_correct with (p':=p') (dim:=(length p)) in H1; trivial.
      }
      {
        eapply IHconstrs; eauto.
      } 
    }
    {
      inv H0.
      split.
      {
        eapply constr_transl_r_correct with (p':=p') (dim:=(length p)) in H1; eauto.
      }
      {
        eapply IHconstrs; eauto.
      }
    }
  }
Qed.

(** 
    [ pol1 ] ( 0 )  | c1
    ( 0 )  [ pol2 ] | c2
*)
Definition poly_product (pol1 pol2: polyhedron) (dim1 dim2: nat) := 
  poly_inter (map (constr_transl_l dim2) pol1) (map (constr_transl_r dim1) pol2)
  .

Lemma poly_product_correct:
  forall pol1 pol2 dim1 dim2 p1 p2,
    WHEN pol' <- poly_product pol1 pol2 dim1 dim2 THEN
    length p1 = dim1 -> 
    length p2 = dim2 -> 
    exact_listzzs_cols (length p1) pol1 ->
    (in_poly (p1 ++ p2) pol' = true
    <-> in_poly p1 pol1 = true /\ in_poly p2 pol2 = true).
Proof. 
  intros. intros pol' Hprod Hlen1 Hlen2.
  unfold poly_product in Hprod.
  eapply poly_inter_def with (p:=p1++p2) in Hprod.
  rewrite poly_inter_pure_def in Hprod.
  split.
  {
    intros Hin.
    rewrite Hprod in Hin. 
    rewrite Bool.andb_true_iff in Hin.
    destruct Hin.
    split. 
    eapply map_constr_transl_l_correct; eauto.
    eapply map_constr_transl_r_correct with (p:=p1) (dim:=dim1); trivial.
  }
  {
    intros [Hin1 Hin2].
    rewrite Hprod. 
    rewrite Bool.andb_true_iff.
    split.
    eapply map_constr_transl_l_correct; eauto.
    eapply map_constr_transl_r_correct with (p:=p1) (dim:=dim1); trivial.
  }
Qed.

Fixpoint sequence_lesser len : list nat :=
  match len with
    | O => []
    | S len' => len' :: sequence_lesser len'
  end.

Fixpoint make_poly_env_eq' (env_dim: nat) (iters_dim1 iters_dim2: nat) (n: nat): polyhedron := 
  match n with 
  | O => []
  | S n' => 
    ((assign (env_dim + iters_dim1 + n') (1%Z) (assign n' (-1%Z) (V0 (env_dim + iters_dim1 + env_dim + iters_dim2)))), 0%Z) ::
    ((assign (env_dim + iters_dim1 + n') (-1%Z) (assign n' (1%Z) (V0 (env_dim + iters_dim1 + env_dim + iters_dim2))), 0%Z) :: (make_poly_env_eq' env_dim iters_dim1 iters_dim2 n'))
  end. 

Definition make_poly_env_eq (env_dim: nat) (iters_dim1 iters_dim2: nat): polyhedron := 
  make_poly_env_eq' env_dim iters_dim1 iters_dim2 env_dim.

Lemma nth_repeat_default: 
  forall {A: Type} (n n': nat) (d: A),
    nth n (repeat d n') d = d.
Proof.
  induction n.
  {
    intros; simpls; destruct n'; trivial. 
  }
  {
    intros. simpls.
    destruct n'; simpls; trivial.
  }
Qed.
  
Lemma nth_assign_different: 
  forall (l: list Z) (n n': nat) (d: Z) (v: Z),
    n <> n' ->
    n' < length l ->
    nth n (assign n' v l) 0%Z = nth n l 0%Z.
Proof.
  unfold assign.
  intros; simpls.
  destruct l eqn:Hl; destruct n eqn:Hn; destruct n' eqn:Hn'; simpls; tryfalse; trivial.
  {
    destruct n0; trivial.
  }
  {
    lia.
  }
  {
    pose proof (classic (n0 < n1)).
    destruct H1.
    {
      rewrite app_nth1.
      rewrite nth_resize.
      eapply Nat.ltb_lt in H1.
      rewrite H1; trivial.
      rewrite resize_length; trivial.
    }
    {
      assert (exists c, n0 = n1 + c).
      {
        exists (n0 - n1).
        lia.
      }
      destruct H2 as (c & N).
      rewrite N. 
      replace n1 with (length (resize n1 l0)) at 1. 2: {rewrite resize_length; trivial. }
      rewrite app_nth2_plus.
      destruct c eqn:Hc; try lia.
      simpls. 
      destruct l0 eqn:Hl0; simpls; try lia.
      rewrite Misc.nth_skipn.
      destruct (n1 + S n2) eqn:Hn0; try lia.
      assert (n1 + n2 = n3). {lia. }
      subst; trivial.
    }  
  }
Qed.


Lemma firstn_eq_implies_nth_eq: 
forall A n' n p1 p2 d, 
          @firstn A n p1 = firstn n p2 -> 
          n' < n ->
          nth n' p1 d = nth n' p2 d. 
Proof. 
    induction n'.
    {
      intros. simpls. destruct n; try lia.
      simpls. destruct p1; destruct p2; simpls; tryfalse; trivial.
      inv H; econs.
    }
    {
      intros.
      destruct p1 eqn:Hp1; destruct p2 eqn:Hp2; simpls; tryfalse; trivial.
      {
        rewrite firstn_nil in H. 
        destruct n; tryfalse; try lia.
      }
      {
        rewrite firstn_nil in H.
        destruct n; tryfalse; try lia.
      }
      {
        destruct n eqn:Hn; tryfalse; try lia.
        do 2 rewrite firstn_cons in H.
        eapply IHn' with (n:=n0); trivial; try lia. 
        inv H; trivial.
      } 
    }
Qed.

Lemma firstn_ge_implies_firstn:  
        forall n n' A l l', 
          @firstn A n l = firstn n l' -> 
          n' <= n ->
          firstn n' l = firstn n' l'. 
Proof.
  induction n. 
  {
    intros; simpls. 
    assert (n' = 0). lia. subst; trivial.
  }
  {
    intros; simpls. 
    destruct l eqn:Hl; destruct l' eqn:Hl'; subst; trivial; tryfalse.
    inv H.
    destruct n' eqn:Hn'; simpls; tryfalse; try lia; trivial.
    eapply IHn with (n':=n0) in H3; try lia.
    rewrite H3; trivial.
  }
Qed.


Lemma make_poly_env_eq'_correct: 
  forall n len1 len2 len3 p1 p2,
    firstn n (firstn len1 p1) = firstn n (firstn len1 p2) ->
    n <= len1 ->
    length p1 = len1 + len2 ->
    length p2 = len1 + len3 ->
    in_poly (p1 ++ p2) (make_poly_env_eq' len1 len2 len3 n) = true.
Proof.
  induction n.
  {
    intros; simpls; trivial.
  }
  {
    intros.
    destruct p1 eqn:Hp1; destruct p2 eqn:Hp2; simpls; try lia.
    rename z into z1; rename l into l1; rename z0 into z2; rename l0 into l2.
    assert (exists len1', len1 = S len1'). {
      destruct len1 eqn:Hlen1; simpls; try lia.
      eexists; eauto. 
    }
    destruct H3 as [len1' Hlen1'].
    rewrite Hlen1' in *; simpls. inversion H1. inversion H2. 
    do 2 rewrite andb_true_iff.
    splits.
    { 
      (* *)
      unfolds satisfies_constraint.
      replace (z1 ::l1 ++ z2 :: l2) with ((z1 :: l1) ++ (z2 :: l2)); trivial.
      rewrite <- Hp1. rewrite <- Hp2. simpls.

      replace (S (length l1 + S len1' + len3)) with ((S (length l1)) + (S (length l2))); try lia.

      rewrite dot_product_assign_right.
      rewrite dot_product_assign_right.
      rewrite dot_product_repeat_zero_right.
      assert (nth n (p1 ++ p2) 0%Z = nth (S (length l1 + n)) (p1 ++ p2) 0%Z). {
        do 2 rewrite firstn_firstn in H.
        replace (Init.Nat.min n len1') with n in H; try lia.
        do 2 rewrite <- firstn_cons in H.
        rewrite <- Hp1 in H; rewrite <- Hp2 in H.

        replace (S (length l1 + n)) with ((S (length l1)) + n); try lia.
        replace (S (length l1)) with (length p1). 2: {rewrite H4. rewrite Hp1. trivial. }

        rewrite app_nth2_plus.
        rewrite app_nth1. 2: { rewrite Hp1. simpl. rewrite H4. lia. }
        clear - H.
        eapply firstn_eq_implies_nth_eq with (n:=(S n)) (n':=n); eauto.
      }
      repeat rewrite <- H3.
      assert (nth n (V0 (S (length l1) + S (length l2))) 0%Z = 0%Z). {
        unfold V0.
        eapply nth_repeat_default; eauto.
      }
      rewrite H6.
      assert (nth (S (length l1 + n)) (assign n (-1) (V0 (S (length l1) + S (length l2)))) 0%Z = 0%Z). {
        rewrite nth_assign_different; try lia; eauto. 
        eapply nth_repeat_default; eauto.
        unfold V0; rewrite repeat_length.
        lia.
      }
      rewrite H7.
      lia.
    }
    { (* copy paste *)
      unfolds satisfies_constraint.
      replace (z1 ::l1 ++ z2 :: l2) with ((z1 :: l1) ++ (z2 :: l2)); trivial.
      rewrite <- Hp1. rewrite <- Hp2. simpls.

      replace (S (length l1 + S len1' + len3)) with ((S (length l1)) + (S (length l2))); try lia.

      rewrite dot_product_assign_right.
      rewrite dot_product_assign_right.
      rewrite dot_product_repeat_zero_right.
      assert (nth n (p1 ++ p2) 0%Z = nth (S (length l1 + n)) (p1 ++ p2) 0%Z). {
        do 2 rewrite firstn_firstn in H.
        replace (Init.Nat.min n len1') with n in H; try lia.
        do 2 rewrite <- firstn_cons in H.
        rewrite <- Hp1 in H; rewrite <- Hp2 in H.

        replace (S (length l1 + n)) with ((S (length l1)) + n); try lia.
        replace (S (length l1)) with (length p1). 2: {rewrite H4. rewrite Hp1. trivial. }

        rewrite app_nth2_plus.
        rewrite app_nth1. 2: { rewrite Hp1. simpl. rewrite H4. lia. }
        clear - H.
        eapply firstn_eq_implies_nth_eq with (n:=(S n)) (n':=n); eauto.
      }
      repeat rewrite <- H3.
      assert (nth n (V0 (S (length l1) + S (length l2))) 0%Z = 0%Z). {
        unfold V0.
        eapply nth_repeat_default; eauto.
      }
      rewrite H6.
      assert (nth (S (length l1 + n)) (assign n (1) (V0 (S (length l1) + S (length l2)))) 0%Z = 0%Z). {
        rewrite nth_assign_different; try lia; eauto. 
        eapply nth_repeat_default; eauto.
        unfold V0; rewrite repeat_length.
        lia.
      }
      rewrite H7.
      lia.
    }
    {
       
      replace (z1 :: l1 ++ z2 :: l2) with ((z1 :: l1) ++ (z2 :: l2)). 2: {trivial. }
      eapply IHn with (len1:=S len1'); trivial. 2: {try lia. }
      (* replace (S len1' -n) with (S (len1' - n)); try lia. *)
      replace (firstn (S len1') (z1 :: l1)) with (z1 :: (firstn len1' l1)); trivial.
      replace (firstn (S len1') (z2 :: l2)) with (z2 :: (firstn len1' l2)); trivial.
      inv H.
      destruct n eqn:Hn; simpl; trivial.
      clear - H7.
      eapply firstn_ge_implies_firstn in H7; eauto.
    }  
  }
Qed.

(** make_poly_env_eq is used for validate_two_accesses, which only works on the 
  hypothesis that two instances' env are equal. (Guarantee that all instances of poly's semantics is considered under validate_two_accesses) 
  So it acts as a "premise". 
  Therefore we only needs "implication" but not "<-" for it.
*)
Lemma make_poly_env_eq_correct: 
  forall len1 len2 len3 p1 p2,
    firstn len1 p1 = firstn len1 p2 ->
    length p1 = len1 + len2 -> 
    length p2 = len1 + len3 ->
    in_poly (p1 ++ p2) (make_poly_env_eq len1 len2 len3) = true.
Proof.
  intros.
  assert (firstn len1 (firstn len1 p1) = firstn len1 (firstn len1 p2)). {
    rewrite H. trivial.
  }
  eapply make_poly_env_eq'_correct; eauto.
Qed.

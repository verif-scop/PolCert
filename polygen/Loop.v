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

Require Import InstrTy.
Require Import Misc.
Require Import IterSemantics.
Require Import AST.

Open Scope Z_scope.
Open Scope list_scope.

(** * The semantics of the Loop language *)

Module Loop(IInstr: INSTR).

Definition ident := IInstr.ident.
Definition instr:=IInstr.t.
Definition mem:=IInstr.State.t.
Module Ty:=IInstr.Ty.
Definition instr_semantics:=IInstr.instr_semantics.

Inductive expr :=
| Constant : Z -> expr
| Sum : expr -> expr -> expr
| Mult : Z -> expr -> expr
| Div : expr -> Z -> expr
| Mod : expr -> Z -> expr
| Var : nat -> expr
| Max : expr -> expr -> expr
| Min : expr -> expr -> expr.

Fixpoint eval_expr (env : list Z) (e : expr) :=
  match e with
  | Constant c => c
  | Sum e1 e2 => eval_expr env e1 + eval_expr env e2
  | Mult k e => k * eval_expr env e
  | Div e k => eval_expr env e / k
  | Mod e k => (eval_expr env e) mod k
  | Var n => nth n env 0
  | Max e1 e2 => Z.max (eval_expr env e1) (eval_expr env e2)
  | Min e1 e2 => Z.min (eval_expr env e1) (eval_expr env e2)
  end.

Ltac destruct_match :=
  match goal with
  | [ |- context[match ?X with _ => _ end] ] => destruct X
  end.

Definition make_sum e1 e2 :=
  match e1, e2 with
  | Constant n, Constant m => Constant (n + m)
  | Constant 0, e2 => e2
  | e1, Constant 0 => e1
  | e1, e2 => Sum e1 e2
  end.

Definition make_mult n e :=
  match n, e with
  | _, Constant m => Constant (n * m)
  | 0, _ => Constant 0
  | 1, e => e
  | n, e => Mult n e
  end.

Definition make_div e n :=
  match e, n with
  | Constant m, _ => Constant (m / n)
  | e, 1 => e
  | e, -1 => make_mult (-1) e
  | e, n => Div e n
  end.

Definition make_mod e n :=
  match e, n with
  | Constant m, _ => Constant (m mod n)
  | e, 1 => Constant 0
  | e, (-1) => Constant 0
  | e, n => Mod e n
  end.

Definition make_max e1 e2 :=
  match e1, e2 with
  | Constant m, Constant n => Constant (Z.max m n)
  | e1, e2 => Max e1 e2
  end.

Definition make_min e1 e2 :=
  match e1, e2 with
  | Constant m, Constant n => Constant (Z.min m n)
  | e1, e2 => Min e1 e2
  end.

Inductive test :=
| LE : expr -> expr -> test
| EQ : expr -> expr -> test
| And : test -> test -> test
| Or : test -> test -> test
| Not : test -> test
| TConstantTest : bool -> test.

Fixpoint eval_test (env : list Z) (t : test) :=
  match t with
  | LE e1 e2 => eval_expr env e1 <=? eval_expr env e2
  | EQ e1 e2 => eval_expr env e1 =? eval_expr env e2
  | And t1 t2 => eval_test env t1 && eval_test env t2
  | Or t1 t2 => eval_test env t1 || eval_test env t2
  | Not t => negb (eval_test env t)
  | TConstantTest b => b
  end.

Definition make_le e1 e2 :=
  match e1, e2 with
  | Constant n, Constant m => TConstantTest (n <=? m)
  | e1, e2 => LE e1 e2
  end.

Definition make_eq e1 e2 :=
  match e1, e2 with
  | Constant n, Constant m => TConstantTest (n =? m)
  | e1, e2 => EQ e1 e2
  end.

Definition make_and t1 t2 :=
  match t1, t2 with
  | TConstantTest true, t | t, TConstantTest true => t
  | TConstantTest false, _ | _, TConstantTest false => TConstantTest false
  | t1, t2 => And t1 t2
  end.

Definition make_or t1 t2 :=
  match t1, t2 with
  | TConstantTest false, t | t, TConstantTest false => t
  | TConstantTest true, _ | _, TConstantTest true => TConstantTest true
  | t1, t2 => Or t1 t2
  end.

Definition make_not t :=
  match t with
  | TConstantTest b => TConstantTest (negb b)
  | t => Not t
  end.

Fixpoint and_all l :=
  match l with
  | nil => TConstantTest true
  | x :: l => make_and x (and_all l)
  end.

Inductive stmt :=
| Loop : expr -> expr -> stmt -> stmt
| Instr : instr -> list expr -> stmt (** list expr relates to iterators.  *)
| Seq : stmt_list -> stmt
| Guard : test -> stmt -> stmt
with stmt_list := 
| SNil : stmt_list
| SCons : stmt -> stmt_list -> stmt_list
.

Definition t := (stmt * (list ident) * (list (ident*Ty.t))) % type.

Definition dummy_stmt := Instr (IInstr.dummy_instr) nil.
Definition dummy: t := (dummy_stmt, nil, nil).

(* FUTURE: for extractor. not used now. *)
Definition wf (stmt_ext: t) := 
  forall stmt varctxt vars, 
    stmt_ext = (stmt, varctxt, vars) -> 
    True.

Inductive loop_semantics : stmt -> list Z -> mem -> mem -> Prop :=
| LInstr : forall i es env mem1 mem2 wcs rcs,
    instr_semantics i (map (eval_expr env) es) wcs rcs mem1 mem2 ->
    loop_semantics (Instr i es) env mem1 mem2
| LSeqEmpty : forall env mem, loop_semantics (Seq SNil) env mem mem
| LSeq : forall env st sts mem1 mem2 mem3,
    loop_semantics st env mem1 mem2 ->
    loop_semantics (Seq sts) env mem2 mem3 ->
    loop_semantics (Seq (SCons st sts)) env mem1 mem3
| LGuardTrue : forall env t st mem1 mem2,
    loop_semantics st env mem1 mem2 ->
    eval_test env t = true ->
    loop_semantics (Guard t st) env mem1 mem2
| LGuardFalse : forall env t st mem,
    eval_test env t = false -> loop_semantics (Guard t st) env mem mem
| LLoop : forall env lb ub st mem1 mem2,
    IInstr.IterSem.iter_semantics (fun x => loop_semantics st (x :: env)) (Zrange (eval_expr env lb) (eval_expr env ub)) mem1 mem2 ->
    loop_semantics (Loop lb ub st) env mem1 mem2.

(** A wrapped semantics for loop semantics *)
Inductive semantics: t -> mem -> mem -> Prop := 
| LSemaIntro: forall loop_ext loop ctxt vars env mem1 mem2,
    loop_ext = (loop, ctxt, vars) -> 
    IInstr.Compat vars mem1 ->
    IInstr.NonAlias mem1 -> 
    IInstr.InitEnv ctxt (rev env) mem1 ->
    loop_semantics loop env mem1 mem2 -> 
    semantics loop_ext mem1 mem2.
    
Definition make_guard test inner :=
  match test with
  | TConstantTest true => inner
  | TConstantTest false => Seq SNil
  | test => Guard test inner
  end.


Definition make_let value inner :=
  Loop value (Sum value (Constant 1)) inner.


Lemma make_sum_correct :
  forall env e1 e2, eval_expr env (make_sum e1 e2) = eval_expr env e1 + eval_expr env e2.
Proof.
  intros env e1 e2; unfold make_sum; repeat destruct_match; simpl; try reflexivity; lia.
Qed.

Lemma make_mult_correct :
  forall env n e, eval_expr env (make_mult n e) = n * eval_expr env e.
Proof.
  intros env n e; unfold make_mult; repeat (destruct_match; simpl); try reflexivity; lia.
Qed.


Lemma make_div_correct :
  forall env e n, eval_expr env (make_div e n) = eval_expr env e / n.
Proof.
  intros env e n; unfold make_div; repeat (destruct_match; simpl); try reflexivity; rewrite ?Z.div_1_r; try reflexivity.
  all: 
  try solve [rewrite <- Z.div_opp_opp, Z.div_1_r by try lia; try reflexivity].
  replace (eval_expr env e / z / -1) with (-(eval_expr env e / z) /1). 
  rewrite Z.div_1_r; lia.
  rewrite <- Z.div_opp_opp; simpl; try lia.
  rewrite Z.opp_involutive; trivial.
Qed.


Lemma make_mod_correct :
  forall env e n, eval_expr env (make_mod e n) = eval_expr env e mod n.
Proof.
  intros env e n; unfold make_mod; repeat (destruct_match; simpl); try reflexivity; rewrite ?Z.mod_1_r; try reflexivity;
    replace (-1) with (-(1)) by reflexivity; rewrite Z.mod_opp_r_z; rewrite ?Z.mod_1_r; lia.
Qed.

Lemma make_max_correct :
  forall env e1 e2, eval_expr env (make_max e1 e2) = Z.max (eval_expr env e1) (eval_expr env e2).
Proof.
  intros env e1 e2; unfold make_max; repeat (destruct_match; simpl); reflexivity.
Qed.

Lemma make_min_correct :
  forall env e1 e2, eval_expr env (make_min e1 e2) = Z.min (eval_expr env e1) (eval_expr env e2).
Proof.
  intros env e1 e2; unfold make_min; repeat (destruct_match; simpl); reflexivity.
Qed.

Lemma make_le_correct :
  forall env e1 e2, eval_test env (make_le e1 e2) = (eval_expr env e1 <=? eval_expr env e2).
Proof.
  intros env e1 e2; unfold make_le; repeat (destruct_match; simpl); reflexivity.
Qed.

Lemma make_eq_correct :
  forall env e1 e2, eval_test env (make_eq e1 e2) = (eval_expr env e1 =? eval_expr env e2).
Proof.
  intros env e1 e2; unfold make_eq; repeat (destruct_match; simpl); reflexivity.
Qed.

Lemma make_and_correct :
  forall env t1 t2, eval_test env (make_and t1 t2) = eval_test env t1 && eval_test env t2.
Proof.
  intros env t1 t2; unfold make_and; repeat (destruct_match; simpl); try reflexivity;
    repeat (match goal with [ |- context[?X && ?Y]] => destruct X; simpl end); auto.
Qed.

Lemma make_or_correct :
  forall env t1 t2, eval_test env (make_or t1 t2) = eval_test env t1 || eval_test env t2.
Proof.
  intros env t1 t2; unfold make_or; repeat (destruct_match; simpl); try reflexivity;
    repeat (match goal with [ |- context[?X || ?Y]] => destruct X; simpl end); auto.
Qed.

Lemma make_not_correct :
  forall env t, eval_test env (make_not t) = negb (eval_test env t).
Proof.
  intros env t; unfold make_not; repeat (destruct_match; simpl); reflexivity.
Qed.


Theorem and_all_correct :
  forall l env, eval_test env (and_all l) = forallb (eval_test env) l.
Proof.
  induction l; simpl in *; [auto|].
  intros; rewrite make_and_correct, IHl; auto.
Qed.

Lemma make_let_correct :
  forall value inner env mem1 mem2,
    loop_semantics (make_let value inner) env mem1 mem2 <-> loop_semantics inner (eval_expr env value :: env) mem1 mem2.
Proof.
  intros value inner env mem1 mem2.
  split.
  - unfold make_let. intros H; inversion_clear H.
    simpl in H0. rewrite Zrange_single in H0.
    inversion_clear H0. inversion H1. congruence.
  - intros H. unfold make_let. constructor.
    rewrite Zrange_single.
    econstructor; [|econstructor]. auto.
Qed.

Lemma make_guard_correct :
  forall test inner env mem1 mem2,
    loop_semantics (make_guard test inner) env mem1 mem2 <->
    (if eval_test env test then loop_semantics inner env mem1 mem2 else mem1 = mem2).
Proof.
  intros test inner env mem1 mem2.
  split.
  - destruct (eval_test env test) eqn:Htest.
    + unfold make_guard; intros H; destruct test; simpl;
        try (inversion_clear H; congruence).
      simpl in *. rewrite Htest in H. auto.
    + unfold make_guard; intros H; destruct test; simpl;
        try (inversion_clear H; congruence).
      simpl in *. rewrite Htest in H. inversion_clear H; auto.
  - destruct (eval_test env test) eqn:Htest.
    + unfold make_guard; intros H; destruct test; simpl;
        try (apply LGuardTrue; auto).
      simpl in Htest; rewrite Htest; auto.
    + unfold make_guard; intros H; destruct test; simpl; rewrite H;
        try (apply LGuardFalse; auto).
      simpl in Htest; rewrite Htest; auto.
      constructor; auto.
Qed.

End Loop.

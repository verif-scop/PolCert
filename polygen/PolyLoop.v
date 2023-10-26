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

Require Import Linalg.
Require Import Misc.
Require Import IterSemantics.
Require Import InstrTy.

Require Import PolyTest.
Require Import PolyOperations.
Require Import ImpureAlarmConfig.

Open Scope Z_scope.

Module PolyLoop (Instr: INSTR).


Definition instr := Instr.t.
Definition instr_semantics := Instr.instr_semantics.
Definition mem := Instr.State.t.

Notation affine_expr := (positive * (list Z * Z))%type.
Definition eval_affine_expr env (e : affine_expr) :=
  (dot_product (fst (snd e)) (rev env) + snd (snd e)) / (Zpos (fst e)).
Definition affine_expr_ok env (e : affine_expr) :=
  ((dot_product (fst (snd e)) (rev env) + snd (snd e)) mod (Zpos (fst e)) =? 0).

Inductive poly_stmt :=
| PLoop : polyhedron -> poly_stmt -> poly_stmt
| PInstr : instr -> list affine_expr -> poly_stmt
| PSkip : poly_stmt
| PSeq : poly_stmt -> poly_stmt -> poly_stmt
| PGuard : polyhedron -> poly_stmt -> poly_stmt.
(* | PStrideGuard : list affine_expr -> poly_stmt -> poly_stmt. *)

Inductive poly_loop_semantics : poly_stmt -> list Z -> mem -> mem -> Prop :=
| PLInstr : forall i es env mem1 mem2 wcs rcs,
(*    forallb (affine_expr_ok env) es = true -> *)
    instr_semantics i (map (eval_affine_expr env) es) wcs rcs mem1 mem2 ->
    poly_loop_semantics (PInstr i es) env mem1 mem2
| PLSkip : forall env mem, poly_loop_semantics PSkip env mem mem
| PLSeq : forall env st1 st2 mem1 mem2 mem3,
    poly_loop_semantics st1 env mem1 mem2 ->
    poly_loop_semantics st2 env mem2 mem3 ->
    poly_loop_semantics (PSeq st1 st2) env mem1 mem3
| PLGuardTrue : forall env t st mem1 mem2,
    poly_loop_semantics st env mem1 mem2 ->
    in_poly (rev env) t = true ->
    poly_loop_semantics (PGuard t st) env mem1 mem2
| PLGuardFalse : forall env t st mem,
    in_poly (rev env) t = false -> poly_loop_semantics (PGuard t st) env mem mem
| PLLoop : forall env p lb ub st mem1 mem2,
    (forall x, in_poly (rev (x :: env)) p = true <-> lb <= x < ub) ->
    Instr.IterSem.iter_semantics (fun x => poly_loop_semantics st (x :: env)) (Zrange lb ub) mem1 mem2 ->
    poly_loop_semantics (PLoop p st) env mem1 mem2.

Lemma PLInstr_inv_sem :
  forall i es env mem1 mem2,
    poly_loop_semantics (PInstr i es) env mem1 mem2 ->
    exists wcs rcs,
    instr_semantics i (map (eval_affine_expr env) es) wcs rcs mem1 mem2.
Proof.
  intros i es env mem1 mem2 Hsem. inversion_clear Hsem. do 2 eexists; eauto.
Qed.

Lemma PLLoop_inv_sem :
  forall env p st mem1 mem2,
    poly_loop_semantics (PLoop p st) env mem1 mem2 ->
    exists lb ub, (forall x, in_poly (rev (x :: env)) p = true <-> lb <= x < ub) /\ Instr.IterSem.iter_semantics (fun x => poly_loop_semantics st (x :: env)) (Zrange lb ub) mem1 mem2.
Proof.
  intros env p st mem1 mem2 H. inversion_clear H.
  eexists; eexists; eauto.
Qed.

Lemma PLGuard_inv_sem :
  forall env p st mem1 mem2,
    poly_loop_semantics (PGuard p st) env mem1 mem2 ->
    if in_poly (rev env) p then poly_loop_semantics st env mem1 mem2 else mem1 = mem2.
Proof.
  intros env p st mem1 mem2 H.
  inversion_clear H.
  - rewrite H1; simpl; auto.
  - rewrite H0; simpl; auto.
Qed.

Lemma PLSeq_inv_sem :
  forall env st1 st2 mem1 mem3,
    poly_loop_semantics (PSeq st1 st2) env mem1 mem3 ->
    exists mem2, poly_loop_semantics st1 env mem1 mem2 /\ poly_loop_semantics st2 env mem2 mem3.
Proof.
  intros env p st mem1 mem3 H.
  inversion_clear H. exists mem2; auto.
Qed.

Lemma PLSkip_inv_sem :
  forall env mem1 mem2, poly_loop_semantics PSkip env mem1 mem2 -> mem1 = mem2.
Proof.
  intros env mem1 mem2 H; inversion H; congruence.
Qed.

Fixpoint make_seq l :=
  match l with
  | nil => PSkip
  | x :: l => PSeq x (make_seq l)
  end.

Lemma make_seq_semantics :
  forall l env mem1 mem2, poly_loop_semantics (make_seq l) env mem1 mem2 <->
    Instr.IterSem.iter_semantics (fun s => poly_loop_semantics s env) l mem1 mem2.
Proof.
  induction l.
  - intros; split; intros H; inversion_clear H; constructor.
  - intros; split; simpl; intros H; inversion_clear H; econstructor; eauto; rewrite IHl in *; eauto.
Qed.

Fixpoint flatten_seq_rec stmt atend :=
  match stmt with
  | PSeq st1 st2 => flatten_seq_rec st1 (flatten_seq_rec st2 atend)
  | PSkip => atend
  | stmt => PSeq stmt atend
  end.

Lemma flatten_seq_rec_semantics :
  forall s atend env mem1 mem2, poly_loop_semantics (flatten_seq_rec s atend) env mem1 mem2 <-> poly_loop_semantics (PSeq s atend) env mem1 mem2.
Proof.
  induction s; intros atend env mem1 mem2; simpl in *; try reflexivity.
  - split.
    + intros H; econstructor; [constructor|auto].
    + intros H; apply PLSeq_inv_sem in H; destruct H as [mem3 [H1 H2]]; apply PLSkip_inv_sem in H1; congruence.
  - rewrite IHs1. split.
    + intros H.
      apply PLSeq_inv_sem in H; destruct H as [mem3 [H1 H2]]; rewrite IHs2 in H2.
      apply PLSeq_inv_sem in H2; destruct H2 as [mem4 [H2 H3]]. 
      econstructor; [econstructor|]; eauto.
    + intros H.
      apply PLSeq_inv_sem in H; destruct H as [mem3 [H1 H2]].
      apply PLSeq_inv_sem in H1; destruct H1 as [mem4 [H1 H3]].
      econstructor; [eauto|].
      rewrite IHs2; econstructor; eauto.
Qed.

Definition flatten_seq stmt := flatten_seq_rec stmt PSkip.

Lemma flatten_seq_semantics :
  forall s env mem1 mem2, poly_loop_semantics (flatten_seq s) env mem1 mem2 <-> poly_loop_semantics s env mem1 mem2.
Proof.
  intros s env mem1 mem2; unfold flatten_seq; rewrite flatten_seq_rec_semantics.
  split.
  - intros H; apply PLSeq_inv_sem in H; destruct H as [mem3 [H1 H2]]; apply PLSkip_inv_sem in H2. congruence.
  - intros H; econstructor; [|constructor]; eauto.
Qed.

End PolyLoop.

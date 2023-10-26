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
Require Import Psatz.


Require Import Linalg.
Require Import ImpureAlarmConfig.

Require Import PolyLang.
Require Import ASTGen.
(* Require Import PolyLoop. *)
Require Import PolyLoopSimpl.
Require Import LoopGen.
(* Require Import Loop. *)
Require Import Misc.

Open Scope Z_scope.

Require Import InstrTy.
Require Import PolIRs.

Require Import LibTactics.

Module CodeGen (PolIRs: POLIRS).

(* Module Instr := PolIRs.BaseInstr. *)
Module PolyLang := PolIRs.PolyLang.
Module PolyLoop := PolIRs.PolyLoop.
Module Loop := PolIRs.Loop.

Module ASTGen := ASTGen(PolIRs).
Module PolyLoopSimplifier := PolyLoopSimplify(PolIRs).
Module LoopGen := LoopGen(PolIRs).

Definition complete_generate d n pi :=
  BIND polyloop <- ASTGen.generate d n pi -;
  LoopGen.polyloop_to_loop (n - d)%nat polyloop.

Theorem complete_generate_preserve_sem :
  forall d n pi env mem1 mem2,
    (d <= n)%nat ->
    WHEN st <- complete_generate d n pi THEN
    Loop.loop_semantics st env mem1 mem2 ->
    length env = (n - d)%nat ->
    (forall c, In c pi.(PolyLang.pi_poly) -> fst c =v= resize n (fst c)) ->
    PolyLang.env_poly_lex_semantics (rev env) n (pi :: nil) mem1 mem2.
Proof.
  intros d n pi env mem1 mem2 Hdn st Hst Hloop Henv Hsize.
  unfold complete_generate in Hst.
  bind_imp_destruct Hst polyloop Hpolyloop.
  eapply ASTGen.generate_preserves_sem; eauto.
  eapply LoopGen.polyloop_to_loop_correct; eauto.
Qed.


(** after elimination, each instance prefixs its timestamp, which should be less than `k`. here d = n + k - es,  *)
(** meaning: timestamp length + domain index length - one shared env size *)
Definition complete_generate_lex_many d n pis :=
  BIND polyloop <- ASTGen.generate_loop_many d n pis -;
  BIND simp <- PolyLoopSimplifier.polyloop_simplify polyloop (n - d)%nat nil -;
  LoopGen.polyloop_to_loop (n - d)%nat simp.

Theorem complete_generate_lex_many_preserve_sem :
  forall d n pis env mem1 mem2,
    (d <= n)%nat ->
    WHEN st <- complete_generate_lex_many d n pis THEN
    Loop.loop_semantics st env mem1 mem2 ->
    length env = (n - d)%nat ->
    ASTGen.pis_have_dimension pis n ->
    PolyLang.env_poly_lex_semantics (rev env) n pis mem1 mem2.
Proof.
  intros d n pis env mem1 mem2 Hdn st Hst Hloop Henv Hpis.
  unfold complete_generate_lex_many in Hst.
  bind_imp_destruct Hst polyloop Hpolyloop; bind_imp_destruct Hst simp Hsimp.
  eapply ASTGen.generate_loop_many_preserves_sem; eauto; [|unfold ASTGen.generate_invariant; auto].
  eapply PolyLoopSimplifier.polyloop_simplify_correct; [|exact Hsimp| | |]; auto; [unfold poly_nrl; simpl; lia|].
  eapply LoopGen.polyloop_to_loop_correct; eauto.
Qed.

Definition complete_generate_many es n pis :=
  let k := list_max (map (fun pi => length pi.(PolyLang.pi_schedule)) pis) in
  let epis := PolyLang.elim_schedule k es pis in
  complete_generate_lex_many (n + k - es)%nat (n + k)%nat epis.

Theorem complete_generate_many_preserve_sem :
  forall es n pis env mem1 mem2,
    (es <= n)%nat ->
    WHEN st <- complete_generate_many es n pis THEN
    Loop.loop_semantics st env mem1 mem2 ->
    length env = es ->
    ASTGen.pis_have_dimension pis n ->
    (forall pi, In pi pis -> (poly_nrl pi.(PolyLang.pi_schedule) <= n)%nat) ->
    PolyLang.env_poly_semantics (rev env) n pis mem1 mem2.
Proof.
  intros es n pis env mem1 mem2 Hes st Hst Hloop Henv Hpis Hpis2.
  unfold complete_generate_many in Hst.
  eapply complete_generate_lex_many_preserve_sem in Hst; [|lia].
  eapply PolyLang.poly_elim_schedule_semantics_env_preserve; [| |apply Hst|]; auto; try lia.
  - rewrite rev_length; auto.
  - unfold ASTGen.pis_have_dimension, PolyLang.elim_schedule in *. rewrite forallb_map, forallb_forall in *.
    intros pi Hpi; specialize (Hpis pi Hpi). reflect.
    rewrite PolyLang.pi_elim_schedule_nrl by (apply list_max_ge; rewrite in_map_iff; exists pi; auto).
    specialize (Hpis2 pi Hpi); lia.
  - intros k pi Hpi. apply nth_error_In in Hpi. apply list_max_ge. rewrite in_map_iff; exists pi; auto.
Qed.

Definition codegen (pol: PolIRs.PolyLang.t): imp Loop.t :=
  let '(pis, varctxt, vars) := pol in 
  BIND loop <- complete_generate_many (length varctxt) (length vars) pis -; 
  pure (loop, varctxt, vars).

Lemma wf_pprog_implies_pis_have_dimension: 
  forall pis ctxt vars,
    PolIRs.PolyLang.wf_pprog (pis, ctxt, vars) ->
    ASTGen.pis_have_dimension (pis) (length vars).
Proof.
  intros pis ctxt vars Hwf.
  unfold PolIRs.PolyLang.wf_pprog in Hwf.
  unfold ASTGen.pis_have_dimension.
  destruct Hwf as (Hwf1 & Hwf3).
  eapply forallb_forall. intros pi Hin. 
  pose proof (Hwf3 pi Hin) as Hwfpi.
  unfold PolIRs.PolyLang.wf_pinstr in Hwfpi. 
  destruct Hwfpi as (_ & G & _). eapply Nat.leb_le; trivial.
Qed.

Lemma wf_pprog_implies_pis_sched_valid_dimension: 
  forall pis ctxt vars,
    PolIRs.PolyLang.wf_pprog (pis, ctxt, vars) ->
    (forall pi, In pi pis -> poly_nrl (PolyLang.pi_schedule pi) <= length vars).
Proof. 
  intros pis ctxt vars Hwf.
  unfold PolIRs.PolyLang.wf_pprog in Hwf.
  unfold ASTGen.pis_have_dimension.
  destruct Hwf as (Hwf1 & Hwf3).
  intros pi Hin. 
  pose proof (Hwf3 pi Hin) as Hwfpi.
  unfold PolIRs.PolyLang.wf_pinstr in Hwfpi. 
  destruct Hwfpi as (_ & _ & G & _). trivial. 
Qed.

(* currently, Loop.wf is a trivial placeholder *)
Lemma codegen_preserve_wf: 
  forall pol,
    WHEN loop <- codegen pol THEN 
    PolIRs.PolyLang.wf_pprog pol ->
    PolIRs.Loop.wf loop.
Proof.
  intros pol loop Hcodegen Hwf1.
  unfold PolIRs.Loop.wf. intros; trivial.
Qed.


Theorem codegen_correct: 
  forall pol st st', 
    WHEN loop <- codegen pol THEN
    PolIRs.PolyLang.wf_pprog pol ->
    PolIRs.Loop.semantics loop st st' -> 
    PolIRs.PolyLang.semantics pol st st'.
Proof.
  intros. intros loop Hcodegen Hwf Hsemt.
  inversion Hsemt. rename env into envv.
  unfold codegen in Hcodegen. 
  destruct pol as ((pis & varctxt_s) & vars_s).
  bind_imp_destruct Hcodegen loop' Hgen.
  eapply mayReturn_pure in Hcodegen. subst. inversion H; subst.
  eapply complete_generate_many_preserve_sem 
    with (env:= envv) (mem1:=st) (mem2:=st') in Hgen; eauto.
  eapply PolIRs.PolyLang.PSemaIntro with (envv:=rev envv); eauto.
  2: { clear - Hwf. firstorder.  }
  eapply Hgen; eauto.
  {
    symmetry; eapply PolIRs.Instr.init_env_samelen with (envv:=rev envv) in H2.
    rewrite rev_length in H2; trivial.
  }
  {
    eapply wf_pprog_implies_pis_have_dimension; eauto.
  }
  {
    (* wf pinstr *)
    eapply wf_pprog_implies_pis_sched_valid_dimension; eauto.
  }
Qed.

End CodeGen.

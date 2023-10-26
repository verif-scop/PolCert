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
Require Import PolyLoop.
Require Import PolyOperations.
Require Import ImpureAlarmConfig.

Require Import StateTy.
Require Import InstrTy.
Open Scope Z_scope.

Require Import PolIRs.

Module PolyLoopSimplify (PolIRs: POLIRS).

Module Instr := PolIRs.Instr.
Module PolyLang := PolIRs.PolyLang.
Module PolyLoop := PolIRs.PolyLoop.
Module Loop := PolIRs.Loop.

Fixpoint polyloop_simplify stmt n ctx :=
  match stmt with
  | PolyLoop.PSkip => pure PolyLoop.PSkip
  | PolyLoop.PSeq st1 st2 => BIND s1 <- polyloop_simplify st1 n ctx -; BIND s2 <- polyloop_simplify st2 n ctx -; pure (PolyLoop.PSeq s1 s2)
  | (PolyLoop.PGuard) pol st =>
    let pol := resize_poly n pol in
    BIND npol <- ctx_simplify pol ctx -;
    BIND nctx <- poly_inter pol ctx -;
    BIND nst <- polyloop_simplify st n nctx -;
    pure (PolyLoop.PGuard npol nst)
  | PolyLoop.PLoop pol st =>
    let pol := resize_poly (S n) pol in
    BIND npol <- ctx_simplify pol ctx -;
    BIND nctx <- poly_inter pol ctx -;
    BIND nst <- polyloop_simplify st (S n) nctx -;
    pure (PolyLoop.PLoop npol nst)
  | PolyLoop.PInstr i es => pure (PolyLoop.PInstr i es)
  end.

Lemma polyloop_simplify_correct :
  forall stmt n ctx,
    (poly_nrl ctx <= n)%nat ->
    WHEN nst <- polyloop_simplify stmt n ctx THEN
         forall env mem1 mem2, length env = n -> in_poly (rev env) ctx = true ->
                          PolyLoop.poly_loop_semantics nst env mem1 mem2 ->
                          PolyLoop.poly_loop_semantics stmt env mem1 mem2.
Proof.
  induction stmt; intros n ctx Hctx nst Hnst env mem1 mem2 Henvlen Henvctx Hsem; simpl in *.
  - bind_imp_destruct Hnst npol Hnpol; bind_imp_destruct Hnst nctx Hnctx.
    bind_imp_destruct Hnst nst1 Hnst1; apply mayReturn_pure in Hnst; rewrite <- Hnst in *.
    apply PolyLoop.PLLoop_inv_sem in Hsem.
    assert (Hinctx : forall x, in_poly (rev (x :: env)) ctx = true) by
        (intros x; rewrite <- in_poly_nrlength with (n := n); [|auto]; simpl; rewrite resize_app by (rewrite rev_length; auto); auto).
    assert (Heq : forall x, in_poly (rev (x :: env)) npol = in_poly (rev (x :: env)) p) by
        (intros x; erewrite <- (ctx_simplify_correct _ _ _ Hnpol); [rewrite resize_poly_in; [|rewrite rev_length]; simpl; auto|auto]).
    destruct Hsem as [lb [ub [Hlbub Hsem]]].
    apply PolyLoop.PLLoop with (lb := lb) (ub := ub); [intros x; rewrite <- Heq; apply Hlbub|].
    eapply Instr.IterSem.iter_semantics_map; [|exact Hsem].
    intros x mem3 mem4 Hx Hsem1. simpl in *.
    rewrite Zrange_in, <- Hlbub, Heq in Hx.
    assert (Hnctxnrl : (poly_nrl nctx <= S n)%nat) by (eapply poly_inter_nrl; [apply resize_poly_nrl| |exact Hnctx]; lia).
    eapply IHstmt; [exact Hnctxnrl|exact Hnst1|simpl; auto| |exact Hsem1].
    erewrite poly_inter_def, poly_inter_pure_def, resize_poly_in; [|rewrite rev_length|exact Hnctx]; [|simpl; auto]; reflect; simpl; auto.
  - apply mayReturn_pure in Hnst; rewrite <- Hnst in *; auto.
  - apply mayReturn_pure in Hnst; rewrite <- Hnst in *; auto.
  - bind_imp_destruct Hnst s1 Hs1; bind_imp_destruct Hnst s2 Hs2; apply mayReturn_pure in Hnst; rewrite <- Hnst in *.
    apply PolyLoop.PLSeq_inv_sem in Hsem; destruct Hsem as [mem3 [Hsem1 Hsem2]].
    apply PolyLoop.PLSeq with (mem2 := mem3); [eapply IHstmt1 | eapply IHstmt2]; eauto.
  - bind_imp_destruct Hnst npol Hnpol; bind_imp_destruct Hnst nctx Hnctx.
    bind_imp_destruct Hnst nst1 Hnst1; apply mayReturn_pure in Hnst; rewrite <- Hnst in *.
    apply PolyLoop.PLGuard_inv_sem in Hsem.
    replace (in_poly (rev env) npol) with (in_poly (rev env) p) in *.
    + destruct (in_poly (rev env) p) eqn:Hin.
      * apply PolyLoop.PLGuardTrue; [|auto].
        assert (Henvnctx : in_poly (rev env) nctx = true) by
            (erewrite poly_inter_def, poly_inter_pure_def; [|exact Hnctx]; reflect; rewrite resize_poly_in; auto; rewrite rev_length; auto).
        assert (Hnctxnrl : (poly_nrl nctx <= n)%nat) by (eapply poly_inter_nrl; [apply resize_poly_nrl|exact Hctx|exact Hnctx]).
        eapply IHstmt with (n := n) (ctx := nctx); eauto.
      * rewrite Hsem. apply PolyLoop.PLGuardFalse; auto.
    + erewrite <- (ctx_simplify_correct _ _ _ Hnpol); auto.
      rewrite resize_poly_in; [|rewrite rev_length]; auto.
Qed.

Fixpoint polyloop_find_loopseq stmt :=
  match stmt with
  | PolyLoop.PSkip => Some nil
  | PolyLoop.PSeq (PolyLoop.PLoop pol st) stmt => match polyloop_find_loopseq stmt with None => None | Some l => Some ((pol, st) :: l) end
  | _ => None
  end.

Lemma polyloop_find_loopseq_eq :
  forall stmt res, polyloop_find_loopseq stmt = Some res ->
              stmt = PolyLoop.make_seq (map (fun z => PolyLoop.PLoop (fst z) (snd z)) res).
Proof.
  induction stmt; intros res Hres; simpl in *; try congruence.
  - assert (H : res = nil) by congruence; rewrite H. reflexivity.
  - destruct stmt1; try congruence.
    destruct (polyloop_find_loopseq stmt2) as [l|] eqn:Heq; [|congruence].
    injection Hres as Hres. rewrite <- Hres; simpl.
    f_equal. apply IHstmt2; reflexivity.
Qed.
End PolyLoopSimplify.

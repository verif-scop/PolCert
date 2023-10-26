Require Import List.
Require Import InstrTy.
Require Import IterSemantics.
Require Import ImpureAlarmConfig.
Require Import ZArith.
Require Import StateTy.
Require Import TyTy.
Require Import Base.
Require Import PolyBase.
Require Import AST.
Require Import OpenScop.
Require Import Coqlib.
Require Import Linalg.
Import List.ListNotations.

Module Ty <: TY.
  Definition t := unit.
  Definition dummy := tt.
  Definition eqb (t1 t2: t) := true.
  Lemma eqb_eq : forall t1 t2, eqb t1 t2 = true <-> t1 = t2.
  Proof. intros. firstorder. destruct t1; destruct t2; trivial. Qed.
End Ty.

Module State <: STATE.
  Definition t := unit.
  Definition non_alias (st: t) := True.
  Definition eq := @eq t.
  Definition eq_refl := @eq_refl t. 
  Definition eq_trans := @eq_trans t.
  Definition eq_sym := @eq_sym t.
  Definition dummy_state := tt.
End State.

Module TInstr <: INSTR.
  Module State := State.
  Module Ty := Ty.
  Module IterSem := IterSem State.
  Module IterSemImpure := IterSem.IterImpureSemantics(CoreAlarmed).
  
  Definition ident := AST.ident.
  Definition ident_eqb := Pos.eqb.
  Definition ident_eqb_eq := Pos.eqb_eq.
  Definition ident_to_openscop_ident (id: ident) := id.
  Definition openscop_ident_to_ident (id: ident) := id.

  Definition ident_to_varname := AST.ident_to_varname.
  Definition varname_to_ident := AST.varname_to_ident.
  Definition bind_ident_varname := AST.bind_ident_varname.
  Definition iterator_to_varname := AST.iterator_to_varname.

  Inductive lang := 
  | Tunknown (wl: list AccessFunction) (rl: list AccessFunction)
  .

  Definition t:=lang.

  Definition dummy_instr := Tunknown nil nil.
  
  Inductive sema: t -> list Z -> list MemCell -> list MemCell -> State.t -> State.t -> Prop := .
  Definition instr_semantics := sema.

  Definition eqb (i1 i2: t) := 
    match i1, i2 with
    | Tunknown wl rl, Tunknown wl' rl' => 
      access_list_strict_eqb wl wl' && access_list_strict_eqb rl rl'
    end.

  Lemma eqb_eq : forall i1 i2, eqb i1 i2 = true <-> i1 = i2.
  Proof.
    intros i1 i2. split; intros H.
    - destruct i1; destruct i2; try reflexivity; try inversion H.
      apply andb_true_iff in H1. destruct H1.
      apply access_list_strict_eqb_eq in H0.
      apply access_list_strict_eqb_eq in H1.
      subst. reflexivity.
    - rewrite H.
      unfold eqb. destruct i2; try reflexivity.
      apply andb_true_iff. split.
      eapply access_list_strict_eq_eqb; trivial.
      eapply access_list_strict_eq_eqb; trivial.
  Qed.

  Definition NonAlias (st: State.t) : Prop := True.

  Lemma sema_prsv_nonalias:
    forall i p wcells rcells st st',
    NonAlias st ->
    instr_semantics i p wcells rcells st st' ->
    NonAlias st'.
  Proof. intros. firstorder. Qed.

  Lemma instr_semantics_stable_under_state_eq:
    forall i p wcs rcs st1 st2 st1' st2',
    State.eq st1 st1' ->
    State.eq st2 st2' ->
    instr_semantics i p wcs rcs st1 st2 ->
    instr_semantics i p wcs rcs st1' st2'.
  Proof. intros. firstorder. Qed.

  Definition InitEnv  (env: list ident) (envv: list Z) (st: State.t): Prop := 
    length env = length envv.
  Definition Compat (vars: list (ident * Ty.t)) (st: State.t): Prop := True.

  Lemma init_env_samelen : forall env envv st, InitEnv env envv st -> length env = length envv.
  Proof. intros env envv st H. trivial. Qed.

  Definition waccess (i: t): option (list AccessFunction) := None.
  Definition raccess (i: t): option (list AccessFunction) := None.

  Definition valid_access_function (wl rl: list AccessFunction) (i: t): Prop := 
    forall p st st' wcells rcells,
    (* State.compat st p -> *)
    instr_semantics i p wcells rcells st st' ->
    valid_access_cells p wcells wl /\ valid_access_cells p rcells rl.

  Definition access_function_checker (wl rl: list AccessFunction) (i: t) := true.

  Definition check_never_written (ctxt: list ident) (i: t) := true.

  Lemma access_function_checker_correct: 
        forall wl rl i, 
            access_function_checker wl rl i = true -> valid_access_function wl rl i. 
  Proof. firstorder. Qed.

  Lemma bc_condition_implie_permutbility:
  forall i1 p1 wcs1 rcs1 st1 st2 st3 i2 p2 wcs2 rcs2,
      NonAlias st1 ->
      (instr_semantics i1 p1 wcs1 rcs1 st1 st2 /\ instr_semantics i2 p2 wcs2 rcs2 st2 st3) ->
      (
      Forall (fun wc2 => 
          Forall (fun wc1 => cell_neq wc1 wc2) wcs1
      ) wcs2
      )
      /\
      (
          Forall (fun rc2 => 
              Forall (fun wc1 => cell_neq wc1 rc2) wcs1
          ) rcs2
      )
      /\
      (
          Forall (fun wc2 => 
              Forall (fun rc1 => cell_neq rc1 wc2 ) rcs1
          ) wcs2
      )
      ->
  (exists st2' st3', instr_semantics i2 p2 wcs2 rcs2 st1 st2' /\ instr_semantics i1 p1 wcs1 rcs1 st2' st3' /\ State.eq st3 st3').
  Proof. intros. destruct H0. inv H0. Qed.

  Definition to_openscop (cinstr: t) (names: list varname): option OpenScop.ArrayStmt := Some OpenScop.ArrSkip. 
End TInstr.


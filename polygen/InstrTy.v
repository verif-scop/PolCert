Require Import ZArith.
Require Import List.
Require Import StateTy.
Require Import TyTy.
Require Import IterSemantics.
Require Import ImpureAlarmConfig.
Require Import Base.
Require Import PolyBase.
(* Require Import AST. *)
Require Import OpenScop.

(** The interface for base instruction, parameterizing the validator. *)
(** User should give its syntax, semantics, and proves its properties (Bernstein's Conditions). *)

Module Type INSTR.
    Declare Module State: STATE.
    Declare Module Ty: TY.
    Module IterSem := IterSem(State).
    Module IterSemImpure := IterSem.IterImpureSemantics(CoreAlarmed).
    Parameter t : Type.
    Parameter dummy_instr : t.
    Parameter ident: Type.
    Parameter ident_eqb: ident -> ident -> bool.
    Parameter ident_eqb_eq: forall i1 i2, ident_eqb i1 i2 = true <-> i1 = i2.


    (** auxiliary definitions for file exchange *)
    Parameter ident_to_varname: ident -> varname.
    Parameter ident_to_openscop_ident: ident -> AST.ident.
    Parameter openscop_ident_to_ident: AST.ident -> ident.
    Parameter varname_to_ident : varname -> ident.
    Parameter bind_ident_varname : list (ident * varname) -> list ident.
    Parameter iterator_to_varname: nat -> varname.

    (* the semantics expose write/read cells(footprint) for it *)
    Parameter instr_semantics : t -> list Z -> list MemCell -> list MemCell -> State.t -> State.t -> Prop.

    Parameter instr_semantics_stable_under_state_eq:
        forall i p wcs rcs st1 st2 st1' st2',
            State.eq st1 st1' ->
            State.eq st2 st2' ->
            instr_semantics i p wcs rcs st1 st2 ->
            instr_semantics i p wcs rcs st1' st2'.
    
    Parameter eqb : t -> t -> bool.
    Parameter eqb_eq: forall i1 i2, eqb i1 i2 = true <-> i1 = i2.
    
    (* Parameter NonAlias: (list ident) -> State.t -> Prop. *)
    Parameter NonAlias: State.t -> Prop.
    Parameter InitEnv: (list ident) -> (list Z) -> State.t -> Prop.
    Parameter Compat: (list (ident * Ty.t)) -> State.t -> Prop.

    Parameter init_env_samelen: 
        forall env envv st,
            InitEnv env envv st ->
            length env = length envv.

    Parameter to_openscop: t -> list varname -> option OpenScop.ArrayStmt.

    (** Used by extractor. could just return None when unnecessary. *)
    Parameter waccess: t -> option (list AccessFunction).
    Parameter raccess: t -> option (list AccessFunction).

    (** Valid access functions should overapproximate memory footprint in dynamic semantics *)
    Definition valid_access_function (wl rl: list AccessFunction) (i: t): Prop := 
        forall p st st' wcells rcells,
        instr_semantics i p wcells rcells st st' ->
        valid_access_cells p wcells wl /\ valid_access_cells p rcells rl.

    (** Check that all constant context are indeed not written by its instruction. *)
    Parameter check_never_written: (list ident) -> t -> bool.

    (** Check all access functions are valid. *)
    Parameter access_function_checker: list AccessFunction -> list AccessFunction -> t -> bool.
    Parameter access_function_checker_correct: 
        forall wl rl i, 
            access_function_checker wl rl i = true -> valid_access_function wl rl i. 

    Parameter sema_prsv_nonalias:
        forall i p wcs rcs st1 st2,
            NonAlias st1 ->
            instr_semantics i p wcs rcs st1 st2 ->
            NonAlias st2.

    Parameter bc_condition_implie_permutbility:
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

End INSTR.

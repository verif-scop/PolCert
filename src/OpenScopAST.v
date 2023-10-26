Require Import Base.
Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import String.
Require Import Linalg.
Require Import OpenScop.
Require Import AST.
Require Import InstrTy.
(** Use for parsing purpose *)
(** Will be convert into OpenScop<C> *)

(** OpenscopAST may be parameterized with Language (for stmt/expr/identifier) and memory model *)

(* OCaml's string type. *)
(* Parameter string : Type. *)
(* OCaml's int type. *)
Parameter location: Type.

(** FIXME *)
Record intInfo := {
  II_source: string;
  II_isNegative: bool;
  II_integer: string;
}.

Record floatInfo := {
  isHex_FI:bool;
  integer_FI:option string;
  fraction_FI:option string;
  exponent_FI:option string;
  suffix_FI:option string
}.

(** Move to another file *)


(* Definition openscop_constraint_loc := (openscop_constraint)%type. *)

Definition RelTypeLoc := (OpenScop.RelType * location)%type.

Definition RelMetaLoc := (list Z * location)%type.

Record RelationLoc := {
    rel_type_loc: RelTypeLoc; 
    meta_loc: RelMetaLoc;
    constrs_loc: ((list (list Z)) * location);
}.

Record ContextLoc := {
    lang_loc: string;
    param_domain_loc: RelationLoc;
    params_loc: option (list OpenScop.varname);
}.

Definition StmtExtLoc := (OpenScop.StmtExt * location)%type.

Record StmtExtsLoc := {
    stmt_exts_loc: list StmtExtLoc;
}.

Record StatementLoc := {
    domain_loc: RelationLoc; 
    scattering_loc: RelationLoc; 
    accesses_loc: list RelationLoc; 
    stmt_exts_opt_loc: option StmtExtsLoc;
}.

Definition GlbExtLoc := (OpenScop.GlbExt * location)%type.

Definition GlbExtsLoc := list GlbExtLoc.

Record OpenScopAST := {
    context_loc: ContextLoc;
    statements_loc: list StatementLoc;  (** len>0 *)
    glb_exts_loc: GlbExtsLoc; 
}.

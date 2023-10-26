Require Import Base.
Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import String.
Require Import Linalg.
Require Import AST.
Require Import Floats.
(** The OpenScop Representation, textual representation for polyhedral model. *)

Definition varname:= string.

(* Parameter ident_to_varname : ident -> varname.
Parameter varname_to_ident : varname -> ident.
Parameter bind_ident_varname : list (ident * varname) -> list ident.
Parameter iterator_to_varname: nat -> varname. *)

(* TODO: atom only for array expr; affine expr no float *)
Inductive Atom := 
| AInt: Z -> Atom
| AVar: string -> Atom
| AFloat: float -> Atom
.

(* AfAtom *)

Inductive AffineExpr := 
| AfInt: Z -> AffineExpr
| AfVar: string -> AffineExpr
| AfAdd: AffineExpr -> AffineExpr -> AffineExpr
| AfMinus: AffineExpr -> AffineExpr -> AffineExpr
| AfMulti: AffineExpr -> AffineExpr -> AffineExpr
| AfDiv: AffineExpr -> AffineExpr -> AffineExpr
.

Inductive ArrayAccess :=
| ArrAccess: string -> list AffineExpr -> ArrayAccess.

Inductive ArrayExpr := 
| ArrAtom : Atom -> ArrayExpr
(* for array expr, variable is counted as single-dim access, so there should be variable atom *)
| ArrAccessAtom: ArrayAccess -> ArrayExpr
| ArrAdd: ArrayExpr -> ArrayExpr -> ArrayExpr
| ArrMinus: ArrayExpr -> ArrayExpr -> ArrayExpr
| ArrMulti: ArrayExpr -> ArrayExpr -> ArrayExpr
| ArrDiv: ArrayExpr -> ArrayExpr -> ArrayExpr

| ArrLt: ArrayExpr -> ArrayExpr -> ArrayExpr
| ArrLe: ArrayExpr -> ArrayExpr -> ArrayExpr
| ArrCond: ArrayExpr (*bool*) -> ArrayExpr -> ArrayExpr -> ArrayExpr

| ArrCall: varname -> list ArrayExpr -> ArrayExpr
(* | ArrExprUnknown: ArrayExpr   *)
(* note that, this is specially for semantically unsupported features, like :? and function call *)
.

Inductive ArrayStmt := 
| ArrAssign: ArrayAccess -> ArrayExpr -> ArrayStmt
| ArrSkip: ArrayStmt 
.


Inductive RelType := 
| CtxtTy: RelType 
| DomTy: RelType    
| ScttTy: RelType
| ReadTy: RelType
| WriteTy: RelType
| MayWriteTy: RelType
. 

Record RelMeta := {
    row_nb: nat; 
    col_nb: nat; 
    out_dim_nb: nat; 
    in_dim_nb: nat;
    local_dim_nb: nat;
    param_nb: nat;
}.

(** length should always larger than 1 + len(context.vars)*)
Definition openscop_constraint := (list Z)%type.
(** e/i + real constraint *)
Record Relation := {
    rel_type: RelType; 
    meta: RelMeta;
    constrs: list (bool * openscop_constraint);
}.


Record ContextScop := {  (** Context for OpenScop specification *)
    lang: string;
    param_domain: Relation; 
    params: option (list varname); 
}.

Inductive StmtExt := 
| StmtBody: (list string) -> ArrayStmt -> StmtExt
.  

Definition StmtExts := list StmtExt.
   (** TODO: should be unique; should be only one extensions... *)

Record Statement := {
    domain: Relation; 
    scattering: Relation; 
    access: list Relation; 
    stmt_exts_opt: option StmtExts;
}.

(* OpenScop itself use Pos to annotated each varaible name *)
Inductive GlbExt := 
| ArrayExt: list (ident * string) -> GlbExt
  (* list of (array id, array name) pair, mandatory *)
| CommentExt: string -> GlbExt
  (* comment string *)
| ScatNamesExt: list string -> GlbExt
  (* gives a name to each scattering dimension *)
| CoordExt: option string -> (nat * nat) -> (nat * nat) -> nat -> GlbExt 
  (* File name, starting line & column, ending line & column, indentation *)
.

Definition GlbExts := list GlbExt.

Record OpenScop := {
    context: ContextScop;
    statements: list Statement;  (** len>0 *)
    glb_exts: GlbExts; 
}.

Definition dummy_ctxt_rel := {|
  rel_type:= CtxtTy;
  meta:= {| row_nb:=0; col_nb:=0; out_dim_nb:=0; in_dim_nb:=0; local_dim_nb:=0; param_nb:=0; |};
  constrs:= nil;
|}.

Definition dummy_ctxt_scop := {|
  lang:= "C";
  param_domain:= dummy_ctxt_rel; 
  params:=None;
|}.

Definition dummy_scop := {|
  context := dummy_ctxt_scop;
  statements := nil;
  glb_exts := nil;
|}.

%{
    open Camlcoq 
    open Exceptions
    open Printf
    open Floats
    open C2C
%}
%token <string * OpenScopAST.location> INT
%token <(string option)*(string option)* OpenScopAST.location> FLOAT
%token <string * OpenScopAST.location> IDENT
%token NULLFILE
%token <OpenScopAST.location> OPENSCOP OPENSCOPEND
%token <OpenScopAST.location> CONTEXT DOMAIN SCATTERING READ WRITE MAYWRITE
%token <OpenScopAST.location> STRINGS STRINGSEND
%token <OpenScopAST.location> BODY BODYEND
%token <OpenScopAST.location> ARRAYS ARRAYSEND
%token <OpenScopAST.location> COORD COORDEND
%token <OpenScopAST.location> SCATNAMES SCATNAMESEND
%token <OpenScopAST.location> COMMENT COMMENTEND
%token <OpenScopAST.location> LOOP LOOPEND
// %token C

%token <OpenScopAST.location> NEWLINE
%token EOF
%token <string> LINE
%token LBRACK RBRACK LPAREN RPAREN EQUAL PLUS MINUS MULTI DIV SEMI
%token LT LE QUESTION COLON COMMA
%token ADDASSIGN SUBASSIGN DIVASSIGN MULTIASSIGN

// %left MINUS
%left PLUS MINUS
%left MULTI DIV

%start <OpenScopAST.coq_OpenScopAST> openscop

// %type <unit> any_token
// %type <unit> any_token_except_ident
// %type <unit> unknown_stmt
%type <OpenScop.coq_ArrayExpr> array_expr
%type <OpenScop.coq_AffineExpr> affine_expr array_bracket
%type <OpenScop.coq_ArrayAccess> array_access
%type < Camlcoq.P.t * char list> array_pair
%type <OpenScop.coq_ArrayStmt> array_stmt
%type <OpenScopAST.coq_GlbExtLoc> arrays_extension comment_extension coord_extension scatnames_extension global_extension
%type <OpenScop.coq_Atom> atom
%type <Camlcoq.Z.t> int
(* defaultly use 64-bit float *)
%type <Floats.float> float
%type <OpenScopAST.coq_GlbExtLoc list> global_extensions list(global_extension)
%type <OpenScopAST.coq_ContextLoc> context
%type <char list list> ctxt_param
%type <Camlcoq.Z.t list> int_list
%type <Camlcoq.Z.t list list> int_list_list
%type <unit> linebreaks
%type <(string * OpenScopAST.location) list> list(IDENT)
%type <OpenScopAST.location list> list(NEWLINE)
%type <OpenScop.coq_AffineExpr list> list(array_bracket)
%type <(Camlcoq.P.t * char list) list> list(array_pair)
%type <OpenScopAST.coq_StatementLoc> statement
%type <OpenScopAST.coq_StatementLoc list> list(statement) statements
%type <OpenScopAST.coq_StmtExtLoc> statement_extension statement_body_extension
%type <OpenScopAST.coq_StmtExtLoc list> list(statement_extension) statement_extensions
%type <OpenScopAST.coq_RelationLoc> relation domain_relation scattering_relation
%type <OpenScopAST.coq_RelationLoc list> relations

(* unambiguity should be cleared! *)
(* because newline is here to sperate different int/ list of matrix *)
(* it ruins the grammar, and rules are typed with look-aheads in mind *)
(* especially for possible empty domain/scattering function (noloop.c) *)
(* empty domain means instruction not in loop. empty sctt maps instance to timestamp all 0 vectors*)

(* Attention that current parser's behavoir rely on arbitrary conflict solutions *)
%%

openscop: 
    linebreaks; OPENSCOP; linebreaks;
    ctxt=context; linebreaks;
    stmts=statements; linebreaks;
    glb_exts=global_extensions; linebreaks; 
    OPENSCOPEND; linebreaks; EOF
    { 
        {OpenScopAST.context_loc=ctxt; OpenScopAST.statements_loc=stmts; OpenScopAST.glb_exts_loc=glb_exts}
    };; 

context: 
| langloc=IDENT; linebreaks; 
        ctxtrel=relation; NEWLINE; linebreaks; ctxtparams=ctxt_param {
    let (lang, loc) = langloc in
    {
        OpenScopAST.lang_loc = (coqstring_of_camlstring lang);
        OpenScopAST.param_domain_loc = ctxtrel;
        OpenScopAST.params_loc = Some ctxtparams;
    }
} 
(** FIXME *)
// | langloc=IDENT; linebreaks; ctxtrel=relation {
//     let (lang, loc) = langloc in
//     {
//         lang_loc = lang;
//         param_domain_loc = ctxtrel;
//         params_loc = None;
//     }
// }
;;
(** FIXME: nb is not number, only a flag for ident's existences *)
ctxt_param: 
| nb=int; linebreaks; STRINGS; linebreaks; idlist=list(IDENT); linebreaks; STRINGSEND {
    let n = Z.of_sint (List.length(idlist)) in 
    if (nb = Z.zero && n > Z.zero)  || (nb = Z.one && n = Z.zero) then  
        comp_error None "context parameter count mismatch, %s\n" ""
    else List.map (fun (str, _) -> coqstring_of_camlstring str) idlist
}
| nb=int; linebreaks {
    if nb = Z.zero then [] else comp_error None "context parameter count mismatch, %s\n" ""
}
;;

(* ad-hoc modification, adpating explicit look-aheads in the rule... *)
domain_relation:
| loc=DOMAIN; NEWLINE; il=int_list; NEWLINE; linebreaks; ill=int_list_list; linebreaks
{
    {
        OpenScopAST.rel_type_loc = (OpenScop.DomTy, loc);
        OpenScopAST.meta_loc = (il, loc);
        OpenScopAST.constrs_loc = (ill, loc);         
    }
}
| loc=DOMAIN; NEWLINE; il=int_list; NEWLINE; linebreaks
{
    {
        OpenScopAST.rel_type_loc = (OpenScop.DomTy, loc);
        OpenScopAST.meta_loc = (il, loc);
        OpenScopAST.constrs_loc = ([], loc);         
    }
}
;;

(* sctt is also possible two be empty, especially for no-loop *)
(* as NEWLINE contribute to semantics, we introduce explicit look-ahead  *)
scattering_relation:
| loc=SCATTERING; NEWLINE; il=int_list; NEWLINE; linebreaks; ill=int_list_list; linebreaks
{
    {
        OpenScopAST.rel_type_loc = (OpenScop.ScttTy, loc);
        OpenScopAST.meta_loc = (il, loc);
        OpenScopAST.constrs_loc = (ill, loc);         
    }
}
| loc=SCATTERING; NEWLINE; il=int_list; NEWLINE; linebreaks
{
    {
        OpenScopAST.rel_type_loc = (OpenScop.ScttTy, loc);
        OpenScopAST.meta_loc = (il, loc);
        OpenScopAST.constrs_loc = ([], loc);         
    }
}
;;

relation: 
(* currently, context's relation is ignored semantically *)
| loc=CONTEXT; NEWLINE; il=int_list; NEWLINE
{
(*    List.iter (fun l -> List.iter (fun n -> printf "%s\t" (Z.to_string n)) l; printf "\n") ill; *)
    {
        OpenScopAST.rel_type_loc = (OpenScop.CtxtTy, loc);
        OpenScopAST.meta_loc = (il, loc);
        OpenScopAST.constrs_loc = ([], loc);         
    }

}
| loc=READ; NEWLINE; il=int_list; NEWLINE;  linebreaks; ill=int_list_list
{
    {
        OpenScopAST.rel_type_loc = (OpenScop.ReadTy, loc);
        OpenScopAST.meta_loc = (il, loc);
        OpenScopAST.constrs_loc = (ill, loc);         
    }
}
| loc=WRITE; NEWLINE; il=int_list; NEWLINE; linebreaks;  ill=int_list_list
{
    {
        OpenScopAST.rel_type_loc = (OpenScop.WriteTy, loc);
        OpenScopAST.meta_loc = (il, loc);
        OpenScopAST.constrs_loc = (ill, loc);         
    }
}
| loc=MAYWRITE; NEWLINE; il=int_list; NEWLINE;  linebreaks; ill=int_list_list
{
    {
        OpenScopAST.rel_type_loc = (OpenScop.MayWriteTy, loc);
        OpenScopAST.meta_loc = (il, loc);
        OpenScopAST.constrs_loc = (ill, loc);         
    }
}
;; 

int_list_list: 
| il=int_list; NEWLINE { il::[] }
| il=int_list; NEWLINE; ill=int_list_list  {
      il::ill};;

int_list: 
| c=int {c::[]} 
| c=int; il=int_list {c::il};;


statements: nb=int; linebreaks; stmts=list(statement) {
    let n = Z.of_sint (List.length(stmts)) in 
    if nb <> n then  
        comp_error None "stmt count mismatch, %s\n" ""
    else stmts
} ;;

statement: 
| nb=int; linebreaks; domrel=domain_relation; 
// NEWLINE; linebreaks; 
scttrel=scattering_relation; accrels=relations; linebreaks; sexts=statement_extensions 
{
    let n = (Z.of_sint (List.length(accrels))) in 
    if nb <> (Z.add n Z.two) then  
    comp_error None "stmt rel counts mismatch, %s\n" ""
    else 
    (*
    let domrel = List.nth rels 0 in
    let scttrel = List.nth rels 1 in 
    let accrels = List.tl (List.tl rels) in
    *)
    {
        OpenScopAST.domain_loc = domrel;
        OpenScopAST.scattering_loc = scttrel;
        OpenScopAST.accesses_loc = accrels;
        OpenScopAST.stmt_exts_opt_loc = 
            if List.length(sexts) > 0 then Some sexts else None;
    }
} 
;;

relations: 
| rel=relation; linebreaks {rel::[]}
| rel=relation; NEWLINE; linebreaks; rellist=relations  {    
rel::rellist};;

statement_extensions: nb=int; linebreaks; exts=list(statement_extension); linebreaks {
    let n = Z.of_sint (List.length(exts)) in 
    if nb <> n then  
    comp_error None "stmt extension length mismatch, %s\n" ""
    else 
    exts
};;

statement_extension: 
| ext=statement_body_extension {ext};;

statement_body_extension: 
| loc=BODY; linebreaks; (*iter count*) nb=int; linebreaks; (*iter names*) idlist=list(IDENT); linebreaks; st=array_stmt; linebreaks; BODYEND  {
    let n = Z.of_sint (List.length(idlist)) in 
    if nb <> n then 
    comp_error (Some loc) "stmt body iteration count mismatch, %s\n" ""
    else 
    ( 
        OpenScop.StmtBody ( 
            List.map (fun (id, _) -> coqstring_of_camlstring id) idlist,
            st
            (* coqstring_of_camlstring "<placeholder>" *) 
            (* FIXME: with array expr. Parameterize Openscop with (language = memory model) *)
        )
    , loc)
}
| loc=BODY; linebreaks; (*iter count*) nb=int; linebreaks; st=array_stmt; linebreaks; BODYEND  {
    if nb <> Z.zero then 
    comp_error (Some loc) "stmt body iteration count mismatch, %s\n" ""
    else 
    ( 
        OpenScop.StmtBody ( 
           [],
            st
        )
    , loc)
}
;;

global_extensions: ge=list(global_extension) {ge};;

global_extension: 
| se=scatnames_extension; linebreaks  {se}
| ae=arrays_extension; linebreaks  {ae}
| ce=coord_extension; linebreaks  {ce}
| ce=comment_extension ; linebreaks {ce}
;;

scatnames_extension: loc=SCATNAMES; linebreaks; sl=list(IDENT); linebreaks; SCATNAMESEND
{
    ( 
        OpenScop.ScatNamesExt (List.map (fun (id, loc) -> coqstring_of_camlstring id) sl) 
    , loc)
};;

arrays_extension: loc=ARRAYS; linebreaks; nb=int; linebreaks ; apl=list(array_pair); linebreaks ; ARRAYSEND {
    let n2 = Z.of_sint (List.length(apl)) in 
    if nb <> n2 then  
    comp_error (Some loc) "array list length mismatch, %s\n" ""
    else 
    ( 
    OpenScop.ArrayExt (apl)
    , loc)
};;

array_pair: aid=int; aname_loc=IDENT; loc=NEWLINE {
    let (aname, loc) = aname_loc in
    (P.of_int64 (Z.to_int64 aid), coqstring_of_camlstring aname)
};;

coord_extension: 
| loc=COORD; linebreaks; NULLFILE; linebreaks; a1=int; a2=int; NEWLINE; linebreaks; b1=int; b2=int; NEWLINE; linebreaks; c=int; NEWLINE; linebreaks; COORDEND {
    ( 
        OpenScop.CoordExt (None, 
        (Nat.of_int64 (Z.to_int64 a1), Nat.of_int64 (Z.to_int64 a2)), 
        (Nat.of_int64 (Z.to_int64 b1), Nat.of_int64 (Z.to_int64 b2)), 
        Nat.of_int64 (Z.to_int64 c)
        ), 
    loc)
}
| loc=COORD; linebreaks; idloc=IDENT; NEWLINE; a1=int; a2=int; NEWLINE; b1=int; b2=int; NEWLINE; c=int; NEWLINE; COORDEND {
    let (id, _) = idloc in
     ( 
        OpenScop.CoordExt (Some (coqstring_of_camlstring id), 
            (Nat.of_int64 (Z.to_int64 a1), Nat.of_int64 (Z.to_int64 a2)), 
            (Nat.of_int64 (Z.to_int64 b1), Nat.of_int64 (Z.to_int64 b2)), 
            Nat.of_int64 (Z.to_int64 c)), 
    loc)
};;

comment_extension: 
| loc=COMMENT; cmt=LINE; linebreaks; COMMENTEND {
    ( OpenScop.CommentExt (coqstring_of_camlstring cmt), loc) };; (** FIXME: useless *)

array_stmt: 
| arr_acc=array_access; EQUAL; ae=array_expr; SEMI {OpenScop.ArrAssign (arr_acc, ae)}
| arr_acc=array_access; ADDASSIGN; ae=array_expr; SEMI {OpenScop.ArrAssign (arr_acc, OpenScop.ArrAdd(OpenScop.ArrAccessAtom (arr_acc), ae))}
| arr_acc=array_access; SUBASSIGN; ae=array_expr; SEMI {OpenScop.ArrAssign (arr_acc, OpenScop.ArrMinus(OpenScop.ArrAccessAtom (arr_acc), ae))}
| arr_acc=array_access; MULTIASSIGN; ae=array_expr; SEMI {OpenScop.ArrAssign (arr_acc, OpenScop.ArrMulti(OpenScop.ArrAccessAtom (arr_acc), ae))}
| arr_acc=array_access; DIVASSIGN; ae=array_expr; SEMI {OpenScop.ArrAssign (arr_acc, OpenScop.ArrDiv(OpenScop.ArrAccessAtom (arr_acc), ae))}
// | unknown_stmt { OpenScop.ArrSkip } 
;;

// any_token_except_ident:
// | INT {()} 
// | LBRACK {()} 
// | RBRACK {()} 
// | LBRACE {()}
// | RBRACE {()}
// | EQUAL {()} 
// | PLUS {()} 
// | MINUS {()} 
// | MULTI {()} 
// | DIV {()} 
// ;;

// unknown_stmt:
// | SEMI {()}
// | any_token_except_ident; unknown_stmt {()}
// | any_token_except_ident; IDENT; unknown_stmt {()}
// | IDENT; any_token_except_ident; unknown_stmt {()}
// ;;

array_access:
| idloc=IDENT; {
    let (id, loc) = idloc in
    OpenScop.ArrAccess ((coqstring_of_camlstring id), [])
}
| idloc=IDENT; hd=array_bracket; tail=list(array_bracket); {
    let (id, loc) = idloc in
    OpenScop.ArrAccess ((coqstring_of_camlstring id), (hd::tail))};;

array_bracket: 
LBRACK; ae=affine_expr; RBRACK {ae};;

(* TODO: we have no ability to distinguish constant variable or mutable variable in parser *)
(* need another pass to change contxt access out of array access *)
(* could fix this in OpenScopAST2OpenScop.ml. though this does not affect current result *)
array_expr:
| c=int {
    OpenScop.ArrAtom (OpenScop.AInt c) 
}
| c=float {
    OpenScop.ArrAtom (OpenScop.AFloat c)
}
| aa=array_access { OpenScop.ArrAccessAtom aa }
| LPAREN; ae=array_expr; RPAREN {ae} 
| ae1=array_expr; PLUS; ae2=array_expr {OpenScop.ArrAdd (ae1, ae2)}
| ae1=array_expr; MINUS; ae2=array_expr {OpenScop.ArrMinus (ae1, ae2)}
| ae1=array_expr; MULTI; ae2=array_expr {OpenScop.ArrMulti (ae1, ae2)}
| ae1=array_expr; DIV; ae2=array_expr {OpenScop.ArrDiv (ae1, ae2)}
| ae1=array_expr; LT; ae2=array_expr {OpenScop.ArrLt (ae1, ae2)}
| ae1=array_expr; LE; ae2=array_expr {OpenScop.ArrLe (ae1, ae2)} 
| cond=array_expr; QUESTION; ae1=array_expr; COLON; ae2=array_expr 
    {OpenScop.ArrCond (cond, ae1, ae2)}
| idloc=IDENT; LPAREN; RPAREN {
    let (id, loc) = idloc in OpenScop.ArrCall (coqstring_of_camlstring id, [])}
| idloc=IDENT; LPAREN; ael=array_expr_list; RPAREN {
    let (id, loc) = idloc in OpenScop.ArrCall (coqstring_of_camlstring id, ael)}
(* TODO: should be list of expr *)
;;

array_expr_list:
| ae=array_expr {ae::[]}
| ae=array_expr; COMMA; ael=array_expr_list {ae::ael}
;;  

int: 
| cloc=INT { 
    let (c, loc) = cloc in 
    let cInfo = 
    { 
              OpenScopAST.coq_II_source = (coqstring_of_camlstring c);
              OpenScopAST.coq_II_isNegative = false;
              OpenScopAST.coq_II_integer = (coqstring_of_camlstring c);
    } in 
    (Z.of_sint64 (elab_int_constant cInfo loc))
}
| MINUS cloc=INT {
    let (c, loc) = cloc in 
    let cInfo = 
    { 
              OpenScopAST.coq_II_source = (coqstring_of_camlstring c);
              OpenScopAST.coq_II_isNegative = true;
              OpenScopAST.coq_II_integer = (coqstring_of_camlstring c);
    } in 
    (Z.of_sint64 (elab_int_constant cInfo loc))
}
;;

(* TODO: done in lexer part should be better *)
(* TODO: all parser-related definition should move to ocaml, not coq *)
float:
| cloc=FLOAT { 
    let (intpart, frac, loc) = cloc in 
    let cInfo = 
    { 
        OpenScopAST.isHex_FI = false;
        OpenScopAST.integer_FI = (Option.map (fun x -> coqstring_of_camlstring x) intpart);
        OpenScopAST.fraction_FI = (Option.map (fun x -> coqstring_of_camlstring x) frac);
        OpenScopAST.exponent_FI = None;
        OpenScopAST.suffix_FI = None
    }
    in 
    let (v, ty) = (elab_float_constant cInfo loc) in
    (convertFloatPure v ty)
}
| MINUS cloc=FLOAT {
    let (intpart, frac, loc) = cloc in 
    let cInfo = 
    { 
        OpenScopAST.isHex_FI = false;
        OpenScopAST.integer_FI = (Option.map (fun x -> coqstring_of_camlstring x) intpart);
        OpenScopAST.fraction_FI = (Option.map (fun x -> coqstring_of_camlstring x) frac);
        OpenScopAST.exponent_FI = None;
        OpenScopAST.suffix_FI = None
    }
    in 
    let (v, ty) = (elab_float_constant cInfo loc) in
    (Float.neg (convertFloatPure v ty))
}
;;

atom: 
| idloc=IDENT {let (id, loc) = idloc in OpenScop.AVar (coqstring_of_camlstring id)} 
| c=int {
    OpenScop.AInt c 
}
| c=float {
    OpenScop.AFloat c
}
;; 

affine_expr: 
| idloc=IDENT {let (id, loc) = idloc in OpenScop.AfVar (coqstring_of_camlstring id)} 
| c=int {
    OpenScop.AfInt c 
}
| LPAREN; e=affine_expr; RPAREN {e} 
| e1=affine_expr; PLUS; e2=affine_expr { OpenScop.AfAdd (e1, e2) }
| e1=affine_expr; MINUS; e2=affine_expr { OpenScop.AfMinus (e1, e2) }
| e1=affine_expr; MULTI; e2=affine_expr { OpenScop.AfMulti (e1, e2) }
| e1=affine_expr; DIV; e2=affine_expr { OpenScop.AfDiv (e1, e2)}
;;

linebreaks: list(NEWLINE) {()};;

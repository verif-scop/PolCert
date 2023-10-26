(** type check AST & transform AST to OpenScop *)

open OpenScopAST
open OpenScop
open Camlcoq
(* open Top *)
open Exceptions
open Printf 

let supported_lang = ["C"; "Java"];; 

let type_check_relation (rel: coq_RelationLoc): unit = 
  let (relTy, relLoc) = rel.rel_type_loc in
  let (meta, metaLoc) = rel.meta_loc in 
  let (constrs, loc) = rel.constrs_loc in
    if List.length meta <> 6 
    then type_error (Some metaLoc) "relation meta should have 6 elements%s\n" "";
  if List.exists (fun x -> (Z.lt x Z.zero)) meta 
    then type_error (Some metaLoc) "relation meta should be non negative%s\n" "";
  let row_nb = List.nth meta 0 in 
  let col_nb = List.nth meta 1 in 
  let out_dim_nb = List.nth meta 2 in 
  let in_dim_nb = List.nth meta 3 in 
  let local_dim_nb = List.nth meta 4 in 
  let param_nb = List.nth meta 5 in 
  (* rel => meta constraint *)
  match relTy with
  | CtxtTy ->
      if out_dim_nb <> Z.zero (* out_dim should be 0 *)
        then type_error (Some metaLoc) "context relation should have 0 out dim%s\n" ""; 
      if in_dim_nb <> Z.zero (* in_dim should be 0 *)
        then type_error (Some metaLoc) "context relation should have 0 in dim%s\n" ""; ()
  | DomTy -> if in_dim_nb <> Z.zero (* in_dim should be 0 *)
    then type_error (Some metaLoc) "domain relation should have 0 in-dim%s\n" ""; ()
    (* TODO: loop iterators correspond to out dim? *)
  | ScttTy -> ()
    (* TODO: output dimensions correspond to scattering dimensions *)
    (* TODO: loop iterators correspond to input dimensions.*)
  | ReadTy -> ()
    (* TODO: output dimensions correspond to the array identifier and dimensions *)
    (* TODO: the first output dimension corresponds to the array identifier *)
    (* TODO: the (i+1)th output dimension corresponds to the ith array dimension (i>1) *)
    (* TODO: loop iterators correspond to input dimensions.*)
  | WriteTy -> ()
  | MayWriteTy -> ()
  ;
  (* check each constr first elem is 0/1*)
  List.iter (fun constr -> 
    if (List.nth constr 0) <> Z.zero || (List.nth constr 0) <> Z.one 
    then type_error (Some loc) "first elem of each constraint should be 0/1%s\n"  "" 
  ) constrs;
  (* meta => constr constraint*)
  (* 1. row_nb *)
  (* List.iter (fun l -> List.iter (fun n -> printf "%s\t" (Z.to_string n)) l; printf "\n") constrs; *)
  
  if List.length constrs <> Z.to_int row_nb
    then type_error (Some loc) "relation constrs should have %s rows\n" (Z.to_string row_nb);
  (* 2. col_nb *)
  if List.exists (fun x -> List.length x <> Z.to_int col_nb) constrs
    then type_error (Some loc) "relation constrs should have %s cols\n" (Z.to_string col_nb);
  (* 3. col_nb = 1 + out + in + loc + param + 1 *)
  if col_nb <> Z.add (Z.add (Z.add (Z.add out_dim_nb in_dim_nb) local_dim_nb) param_nb) (Z.of_sint 2)
    then type_error (Some loc) "relation constrs cols not consistent%s\n" ""
  (* 4. ... param_nb consistency should be check globally *)
  ;()  
;;

let type_check_context (ctxt: coq_ContextLoc): unit = 
  if not (List.mem (camlstring_of_coqstring ctxt.lang_loc) supported_lang) 
    then type_error None "lang not supported%s\n" "";
  let (relTy, relLoc) = ctxt.param_domain_loc.rel_type_loc in
  if relTy <> OpenScop.CtxtTy 
    then type_error (Some relLoc) "should be context relation%s\n" "";
  type_check_relation ctxt.param_domain_loc;
  (* can move to global check *)
  match ctxt.params_loc with 
  | None -> ()
  | Some params -> 
    let (meta, _) = ctxt.param_domain_loc.meta_loc in
    let param_nb = List.nth meta 5 in 
    if param_nb <> Z.of_sint (List.length params)
      then type_error (Some relLoc) "context params count does not meet context parameters%s\n" "";
    ()
;;

(** literally, no check for stmt ext currently; may further check iterators/body are consistent with array extensions and context in global check. TODO *)
let type_check_stmt_ext (stmtExtLoc: coq_StmtExtLoc): unit = 
  let (stmtExt, loc) = stmtExtLoc in
  match stmtExt with 
  | StmtBody (iterators, body) -> () 
;; 

(** Assert ordered relations: domain; sctt; access... *)
let type_check_stmts (stmts: coq_StatementLoc list): unit = 
  List.iter (fun stmt -> 
    let domainRel = stmt.OpenScopAST.domain_loc in 
    let scttRel = stmt.scattering_loc in 
    let accessRels = stmt.accesses_loc in 
    let (relTy, relLoc) = domainRel.rel_type_loc in
    if relTy <> OpenScop.DomTy 
      then type_error (Some relLoc) "should be domain relation%s" "";
    type_check_relation domainRel;
    let (relTy, relLoc) = scttRel.rel_type_loc in
    if relTy <> OpenScop.ScttTy 
      then type_error (Some relLoc) "should be scattering relation%s" "";
    type_check_relation scttRel;
    List.iter (fun accRel -> 
      let (relTy, relLoc) = accRel.OpenScopAST.rel_type_loc in
      if relTy <> OpenScop.ReadTy && relTy <> OpenScop.WriteTy && relTy <> OpenScop.MayWriteTy
        then type_error (Some relLoc) "should be access relation%s" "";
      type_check_relation accRel;
    ) accessRels;
    let stmtExts = stmt.stmt_exts_opt_loc in 
    match stmtExts with 
    | None -> ()
    | Some exts -> List.iter type_check_stmt_ext exts; ()
  ) stmts; ()
;;

let type_check_glb_ext (extLoc: OpenScopAST.coq_GlbExtLoc): unit = 
  let (ext, loc) = extLoc in 
    match ext with 
    | ArrayExt arrPairs -> () (* TODO: check glb consistency: all array name/id across stmts are used correctly *)
    | CommentExt cmt -> ()
    | ScatNamesExt scttnames -> () (* TODO: may check glb consistency *) 
    | CoordExt (ofile, (sl, sc), (el, ec), ident) -> () 
  ; ()
;;

let type_check_glb_exts (glb_exts: OpenScopAST.coq_GlbExtsLoc): unit = 
  List.iter type_check_glb_ext glb_exts; ();;


let type_check_glb (ast: OpenScopAST.coq_OpenScopAST): unit = 
  (* 1. check param count *)
  let (meta, _) = ast.context_loc.param_domain_loc.meta_loc in 
  let param_nb = List.nth meta 5 in 
  (* check all relation meta have exact param_nb *)
  List.iter (fun stmt -> 
    let domainRel = stmt.OpenScopAST.domain_loc in 
    let scttRel = stmt.scattering_loc in 
    let accessRels = stmt.accesses_loc in 
    let check_rel_param_nb relation  = 
      let (meta, loc) = relation.OpenScopAST.meta_loc in 
      let param_nb' = List.nth meta 5 in 
      if param_nb' <> param_nb 
        then type_error (Some loc) "relation param_nb not consistent%s\n" ""
    in
    check_rel_param_nb domainRel;
    check_rel_param_nb scttRel;
    List.iter (fun accRel -> 
      check_rel_param_nb accRel;
    ) accessRels; ()
  ) ast.statements_loc; ()
  (* 2. check array/sctt/... TODO *)
;;

let type_check (ast: OpenScopAST.coq_OpenScopAST): unit = 
  type_check_context ast.context_loc;
  type_check_stmts ast.statements_loc;
  type_check_glb_exts ast.glb_exts_loc;
  type_check_glb ast
;;

let convert_rel (rel: OpenScopAST.coq_RelationLoc): OpenScop.coq_Relation =
  let (relTy, _) = rel.rel_type_loc in
  let (meta', _) = rel.meta_loc in
  let (constrs, _) = rel.constrs_loc in
  {
    rel_type = relTy;
    meta = {
      row_nb = Nat.of_int64 (Z.to_int64 (List.nth meta' 0)); 
      col_nb = Nat.of_int64 (Z.to_int64 (List.nth meta' 1)); 
      out_dim_nb = Nat.of_int64 (Z.to_int64 (List.nth meta' 2)); 
      in_dim_nb = Nat.of_int64 (Z.to_int64 (List.nth meta' 3));
      local_dim_nb = Nat.of_int64 (Z.to_int64 (List.nth meta' 4));
      param_nb = Nat.of_int64 (Z.to_int64 (List.nth meta' 5));
    };
    constrs = List.map (
      fun constr -> 
        let ei = List.nth constr 0 in 
        let real_constr = List.tl constr in 
        (if ei = Z.zero then (false, real_constr) else (true, real_constr))
    ) constrs;
  }
;;

let convert_ctxt (ctxt: OpenScopAST.coq_ContextLoc): OpenScop.coq_ContextScop = 
  {
    lang = ctxt.lang_loc;
    param_domain = convert_rel ctxt.param_domain_loc;
    params = ctxt.params_loc;
  }
;; 
 
let convert_stmt (stmt: OpenScopAST.coq_StatementLoc): OpenScop.coq_Statement = 
  {
    domain = convert_rel stmt.domain_loc;
    scattering = convert_rel stmt.scattering_loc;
    access = List.map convert_rel stmt.accesses_loc;
    stmt_exts_opt = if stmt.stmt_exts_opt_loc <> None then 
      (match stmt.stmt_exts_opt_loc with 
      | Some exts -> Some (List.map (fun (ext, _) -> ext) exts))
       else None; 
    (* convert_stmt_ext stmt.stmt_exts_opt_loc;     *)
  }
;; 

let convert_ast (ast: OpenScopAST.coq_OpenScopAST): OpenScop.coq_OpenScop = 
  {
    context = convert_ctxt ast.context_loc; 
    statements = List.map convert_stmt ast.statements_loc;
    glb_exts = List.map (fun (ext, _) -> ext) ast.glb_exts_loc; 
  }
;;

let convert (ast: OpenScopAST.coq_OpenScopAST) =
  type_check ast; 
  convert_ast ast
;; 
  
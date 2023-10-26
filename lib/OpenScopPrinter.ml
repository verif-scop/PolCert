(* open Top *)
open OpenScop
(* open Format *)
open Printf
open List
(* open String *)
(* open Buffer *)
(* open Camlcoq *)

(** Printer for OpenScop *)

(*** TODO: implement as a functor, maybe later *)

let version = "0.1"

(** TODO: maybe fix this implementation.. 
    safe-string restriction *)
(* let camlstring_of_coqstring (chars: char list) =
  let buf = Buffer.create 1024 in
  List.iter (Buffer.add_char buf) chars;
  Buffer.contents buf *)

  (* let n = List.length l in
  let s = Bytes.create n in
  let rec iter i = function
    | [] -> ()
    | c :: l -> Bytes.set s i c; iter (i + 1) l
  in iter 0 l; Bytes.to_string s *)

let relmeta_printer out meta = 
  fprintf out "%d %d %d %d %d %d\n" 
    (Camlcoq.Nat.to_int meta.OpenScop.row_nb) 
    (Camlcoq.Nat.to_int meta.col_nb) 
    (Camlcoq.Nat.to_int meta.out_dim_nb) 
    (Camlcoq.Nat.to_int meta.in_dim_nb) 
    (Camlcoq.Nat.to_int meta.local_dim_nb) 
    (Camlcoq.Nat.to_int meta.param_nb)

let relconstr_printer out constr = 
  let (ei, real_constr) = constr in 
  let rec real_constr_printer out real_constr =
      match real_constr with 
      | [] -> fprintf out "\n"
      | n::constr' -> fprintf out "\t%d" (Camlcoq.Z.to_int n); real_constr_printer out constr'
  in
  fprintf out "\t%d" (if ei then 1 else 0);
  real_constr_printer out real_constr


let rec relconstrs_printer out constrs = 
  match constrs with 
  | [] -> fprintf out "\n"
  | constr :: constrs' -> 
      relconstr_printer out constr;
      relconstrs_printer out constrs'  
    

let relation_printer out relation = 
  (
  match relation.OpenScop.rel_type with
  | CtxtTy -> fprintf out "CONTEXT\n"; 
  | DomTy -> fprintf out "DOMAIN\n"; 
  | ScttTy -> fprintf out "SCATTERING\n"; 
  | ReadTy -> fprintf out "READ\n"; 
  | WriteTy -> fprintf out "WRITE\n"; 
  | MayWriteTy -> fprintf out "MAYWRITE\n"; 
  )
  ; 
  relmeta_printer out relation.meta 
  ;
  relconstrs_printer out relation.constrs

let ctxt_params_printer out params =
  match params with 
  | None -> fprintf out "# Empty param information...\n"
  | Some params -> 
      fprintf out "# Parameter names are provided ...\n";
      fprintf out "%d\n" (if (List.length params) > 0 then 1 else 0);
      fprintf out "# Parameter names ...\n";
      fprintf out "<strings>\n";
      List.iter (fun name -> fprintf out "%s " (Camlcoq.camlstring_of_coqstring name)) params;
      fprintf out "\n</strings>\n\n"

let context_printer out context = 
  fprintf out "# =============================================== Global\n";
  fprintf out "# Language\n";
  fprintf out "%s\n\n" (Camlcoq.camlstring_of_coqstring context.OpenScop.lang);
  fprintf out "# Context\n";
  relation_printer out context.param_domain;
  ctxt_params_printer out context.params

let rec aff_expr_str aff_expr = 
  match aff_expr with 
  | OpenScop.AfInt z -> Camlcoq.Z.to_string z
  | OpenScop.AfVar id -> Camlcoq.camlstring_of_coqstring id
  | OpenScop.AfAdd (aff_expr1, aff_expr2) -> 
      (aff_expr_str aff_expr1) ^ " + " ^ (aff_expr_str aff_expr2)
  | OpenScop.AfMinus (aff_expr1, aff_expr2) -> 
    (aff_expr_str aff_expr1) ^ " - " ^ (aff_expr_str aff_expr2)
  | OpenScop.AfMulti (aff_expr1, aff_expr2) -> 
    (aff_expr_str aff_expr1) ^ " * " ^ (aff_expr_str aff_expr2)
  | OpenScop.AfDiv (aff_expr1, aff_expr2) -> 
    (aff_expr_str aff_expr1) ^ " / " ^ (aff_expr_str aff_expr2)
  

let arr_access_str arr_access = 
match arr_access with 
| OpenScop.ArrAccess (id, aff_exprs) -> 
  (* let id_str = extern_atom id in  *)
  let id_str = id in 
  let affs_str = (List.fold_left (fun str aff_expr -> str ^ "[" ^ (aff_expr_str aff_expr) ^ "]") "" aff_exprs) in 
   Camlcoq.camlstring_of_coqstring id_str ^ affs_str


let rec arr_expr_str arr_expr = 
  match arr_expr with 
  | OpenScop.ArrAtom atom -> 
    (
      match atom with 
      | OpenScop.AInt z -> Camlcoq.Z.to_string z
      | OpenScop.AVar id -> Camlcoq.camlstring_of_coqstring id
      | OpenScop.AFloat f -> Float.to_string (Camlcoq.camlfloat_of_coqfloat f)
    )  
  | OpenScop.ArrAccessAtom (arr_access) -> 
      arr_access_str arr_access 
  | OpenScop.ArrAdd (arr_expr1, arr_expr2) -> 
    (arr_expr_str arr_expr1) ^ " + " ^ (arr_expr_str arr_expr2)
  | OpenScop.ArrMinus (arr_expr1, arr_expr2) -> 
    (arr_expr_str arr_expr1) ^ " - " ^ (arr_expr_str arr_expr2)
  | OpenScop.ArrMulti (arr_expr1, arr_expr2) -> 
    (arr_expr_str arr_expr1) ^ " * " ^ (arr_expr_str arr_expr2)
  | OpenScop.ArrDiv (arr_expr1, arr_expr2) -> 
    (arr_expr_str arr_expr1) ^ " / " ^ (arr_expr_str arr_expr2)
  | OpenScop.ArrLt (arr_expr1, arr_expr2) -> 
    (arr_expr_str arr_expr1) ^ " < " ^ (arr_expr_str arr_expr2)
  | OpenScop.ArrLe (arr_expr1, arr_expr2) -> 
    (arr_expr_str arr_expr1) ^ " <= " ^ (arr_expr_str arr_expr2)
  | OpenScop.ArrCond (arr_expr1, arr_expr2, arr_expr3) -> 
    (arr_expr_str arr_expr1) ^ " ? " ^ (arr_expr_str arr_expr2) ^ " : " ^ (arr_expr_str arr_expr3)
  | OpenScop.ArrCall (id, arr_exprs) -> 
    let id_str = Camlcoq.camlstring_of_coqstring id in 
    if List.length arr_exprs = 0 then id_str ^ "()" else
    let arrs_str = (List.fold_left (fun str arr_expr -> str ^ "," ^ (arr_expr_str arr_expr)) "" (List.tl arr_exprs)) in 
    id_str ^ "(" ^ (arr_expr_str (List.hd arr_exprs)) ^ arrs_str ^ ")" 
  (* TODO: condition expression *)

let arr_instr_string arr_instr = 
  match arr_instr with 
  | OpenScop.ArrAssign (arr_access, arr_expr) -> 
    let lstr = arr_access_str arr_access in
    let rstr = arr_expr_str arr_expr in 
    let final_str = lstr ^ " = " ^ rstr ^ ";" in
    final_str
  | OpenScop.ArrSkip -> "$placeholder = 0;"

let stmt_ext_printer out ext = 
  match ext with 
  | OpenScop.StmtBody (iters, e) -> 
    let iterators_str' = (List.fold_left (fun str iter -> str ^ " " ^ (Camlcoq.camlstring_of_coqstring iter)) "" iters) in
    let strlen = String.length iterators_str' in
    let iterators_str = if strlen = 0 then iterators_str' else (String.sub iterators_str' 1 (strlen - 1)) in
    fprintf out 
"<body>\n# Number of original iterators\n%d\n# List of original iterators\n%s\n# Statement body expression\n%s\n</body>\n\n"
        (List.length iters) 
        iterators_str
        (arr_instr_string e) (** TODO: should serialize the instr's AST. FIXME *) 
        (* (camlstring_of_coqstring e) *)

let stmt_printer out idx stmt = 
  fprintf out "# ----------------------------------------------  %d.%d Domain\n" idx 1;
  relation_printer out stmt.OpenScop.domain;
  fprintf out "# ----------------------------------------------  %d.%d Scattering\n" idx 2;
  relation_printer out stmt.scattering;  
  fprintf out "# ----------------------------------------------  %d.%d Access\n" idx 3;
  List.iter (fun access_rel -> relation_printer out access_rel) stmt.access;  
  match stmt.stmt_exts_opt with  
  | Some stmt_exts ->
    (
      fprintf out "# ----------------------------------------------  %d.%d Statement Extensions\n" idx 4;
      fprintf out "# Number of Statement Extensions\n%d\n" (List.length (stmt_exts));
      List.iter (fun ext -> stmt_ext_printer out ext) stmt_exts
    )
  | None -> ()

let stmts_printer out stmts = 
  fprintf out "# =============================================== Statements\n";
  fprintf out "# Number of statements:\n%d\n" (List.length stmts);
  List.iteri (fun idx stmt -> 
    fprintf out "# =============================================== Statement %d\n" (idx+1);
    fprintf out "# Number of relations describing the statement:\n%d\n\n" (2 + (List.length stmt.OpenScop.access));
    stmt_printer out (idx+1) stmt
  ) stmts
  
let glb_exts_printer out glb_exts = 
  fprintf out "# =============================================== Extensions\n";
  List.iter (fun ext -> 
    match ext with 
    | OpenScop.CommentExt cmt -> fprintf out 
        "<comment>\n%s\n</comment>\n\n" 
        (Camlcoq.camlstring_of_coqstring cmt)
    | ArrayExt arr_list -> 
      fprintf out "<arrays>\n";
      fprintf out "# Number of arrays\n%d\n# Mapping array-identifiers/array-names\n" (List.length arr_list);
      List.iter (fun (id, name)-> 
          fprintf out "%d %s\n" 
            (Camlcoq.P.to_int id)
            (Camlcoq.camlstring_of_coqstring name) 
        ) arr_list;
        fprintf out "</arrays>\n\n"
    | ScatNamesExt scat_name_list -> 
      let name_list_str = (List.fold_left (fun str name -> str ^ " " ^ (Camlcoq.camlstring_of_coqstring name)) "" scat_name_list) in
      let strlen = String.length name_list_str in
      fprintf out "<scatnames>\n%s\n</scatnames>\n\n" 
        (if strlen = 0 then name_list_str else (String.sub name_list_str 1 ((String.length name_list_str) - 1))) ;
    | CoordExt (ofile, (sl, sc), (el, ec), idents) ->
      fprintf out 
"<coordinates>\n# File name\n%s\n# Starting line and column\n%d %d\n# Ending line and column\n%d %d\n# Indentation\n%d\n</coordinates>\n\n"
        (match ofile with 
        | None -> "(null)"
        | Some str -> Camlcoq.camlstring_of_coqstring str
        )
        (Camlcoq.Nat.to_int sl)
        (Camlcoq.Nat.to_int sc) 
        (Camlcoq.Nat.to_int el) 
        (Camlcoq.Nat.to_int ec) 
        (Camlcoq.Nat.to_int idents)
  ) glb_exts

let openscop_printer' out (scop: OpenScop.coq_OpenScop) = 
  Printf.fprintf out "# [File generated by coq-openscop %s]\n\n" version;
  Printf.fprintf out "<OpenScop>\n\n";
  context_printer out (scop.context);
  stmts_printer out (scop.statements);
  glb_exts_printer out (scop.glb_exts);
  Printf.fprintf out "</OpenScop>\n"

let openscop_printer filename scop = 
  let out = open_out filename in
  openscop_printer' out scop;
  close_out out
;;

(* let () = 
  let out = open_out ("out" ^ ".scop") in
  openscop_printer out sample_scop;
  close_out out
;; *)

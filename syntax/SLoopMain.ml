open Diagnostics
open Result
open SLoopCommon
open SLoopCli
open SLoopDispatch
open SLoopProfile

let tool_name = "Syntax-Frontend Polyhedral Optimizer"

module ParallelCodegenCore = ParallelCodegen.ParallelCodegen(SPolIRs.SPolIRs)
module ParallelLoopIR = ParallelCodegenCore.ParallelLoop
module ParallelBaseLoop = ParallelLoopIR.BaseLoop
module ParallelInstr = SPolIRs.SPolIRs.Instr
module VerifiedSequentialCompiler = SVerifiedCompilerConfig
module VerifiedParallelCompiler = SVerifiedParallelCompilerConfig

let pluto_tiling_mode second_level =
  if second_level
  then PlutoTilingValidator.SecondLevel
  else PlutoTilingValidator.Ordinary

let diamond_midpoint_label full =
  if full then "mid_full_diamond" else "mid_diamond"

let usage = SLoopCli.usage
let parse_args = SLoopCli.parse_args
let validate_flag_model = SLoopCli.validate_flag_model
let configure_scheduler_modes = SLoopCli.configure_scheduler_modes

let route_has_tiling route = SLoopRoute.has_tiling route

let route_is_identity route = SLoopRoute.identity_schedule route

let route_has_iss route = SLoopRoute.iss_enabled route

let route_is_second_level route =
  match route.SLoopRoute.tiling_family with
  | SLoopRoute.Tiled { levels = SLoopRoute.TwoLevels; _ } -> true
  | SLoopRoute.NoTiling
  | SLoopRoute.Tiled { levels = SLoopRoute.OneLevel; _ } -> false

let route_is_diamond route =
  match route.SLoopRoute.tiling_family with
  | SLoopRoute.Tiled { shape = SLoopRoute.Diamond _; _ } -> true
  | SLoopRoute.NoTiling
  | SLoopRoute.Tiled { shape = SLoopRoute.Rectangular; _ } -> false

let route_has_intra_tile route =
  route.SLoopRoute.intra_tile_policy = SLoopRoute.IntraTileEnabled

let route_uses_post_tiling_affine route =
  route_is_diamond route
  || route_has_intra_tile route

let route_tiling_explicitly_requested route =
  SLoopRoute.tiling_explicitly_requested route

let read_openscop_or_fail path =
  match OpenScopReader.read path with
  | Some scop -> scop
  | None -> frontend_failf "cannot read OpenScop file %s" path

let print_section title body =
  print_endline ("== " ^ title ^ " ==");
  print_string body;
  if body = "" || body.[String.length body - 1] <> '\n' then print_newline ();
  print_newline ()

let max_int a b = if a >= b then a else b

let string_of_z z = string_of_int (Camlcoq.Z.to_int z)

let string_of_aff (zs, c) =
  let coeffs = String.concat "," (List.map string_of_z zs) in
  Printf.sprintf "[%s | %s]" coeffs (string_of_z c)

let string_of_aff_list affs =
  "[" ^ String.concat "; " (List.map string_of_aff affs) ^ "]"

let string_of_access acc =
  let (arr, affs) = acc in
  Printf.sprintf "(%s,%s)" (string_of_int (Camlcoq.P.to_int arr)) (string_of_aff_list affs)

let string_of_access_list accs =
  "[" ^ String.concat "; " (List.map string_of_access accs) ^ "]"

let nth_or xs n default =
  try List.nth xs n with _ -> default

let name_of_ident id = Camlcoq.extern_atom id
let name_of_nat n = string_of_int (Camlcoq.Nat.to_int n)

let rec string_of_parallel_loop_expr_raw env = function
  | ParallelBaseLoop.Constant z -> string_of_z z
  | ParallelBaseLoop.Var n -> nth_or env (Camlcoq.Nat.to_int n) ("v" ^ name_of_nat n)
  | ParallelBaseLoop.Sum (a, b) ->
      Printf.sprintf "(%s + %s)"
        (string_of_parallel_loop_expr_raw env a)
        (string_of_parallel_loop_expr_raw env b)
  | ParallelBaseLoop.Mult (k, e) ->
      Printf.sprintf "(%s * %s)" (string_of_z k) (string_of_parallel_loop_expr_raw env e)
  | ParallelBaseLoop.Div (e, k) ->
      Printf.sprintf "(%s / %s)" (string_of_parallel_loop_expr_raw env e) (string_of_z k)
  | ParallelBaseLoop.Mod (e, k) ->
      Printf.sprintf "(%s %% %s)" (string_of_parallel_loop_expr_raw env e) (string_of_z k)
  | ParallelBaseLoop.Max (a, b) ->
      Printf.sprintf "max(%s, %s)"
        (string_of_parallel_loop_expr_raw env a)
        (string_of_parallel_loop_expr_raw env b)
  | ParallelBaseLoop.Min (a, b) ->
      Printf.sprintf "min(%s, %s)"
        (string_of_parallel_loop_expr_raw env a)
        (string_of_parallel_loop_expr_raw env b)

let string_of_parallel_loop_expr env e =
  string_of_parallel_loop_expr_raw env e

let parallel_slot_expr slots n =
  nth_or slots (Camlcoq.Nat.to_int n) (ParallelBaseLoop.Constant (Camlcoq.Z.of_sint 0))

let loop_slots_of_parallel slots =
  List.map ParallelCodegenCore.erase_expr slots

let string_of_parallel_affine env slots aff =
  string_of_parallel_loop_expr env
    (ParallelCodegenCore.tag_expr
       (SLoopSymbolicSimpl.display_affine_expr
          (loop_slots_of_parallel slots)
          aff))

let string_of_parallel_access env slots = function
  | ParallelInstr.AcVar id -> name_of_ident id
  | ParallelInstr.AcArr (id, idxs) ->
      let base = name_of_ident id in
      List.fold_left
        (fun acc idx -> acc ^ "[" ^ string_of_parallel_affine env slots idx ^ "]")
        base idxs

let string_of_parallel_instr_expr env slots expr =
  let rec go = function
    | expr ->
        begin match
          SLoopSymbolicSimpl.display_instr_expr
            (loop_slots_of_parallel slots)
            expr
        with
        | Some e ->
            string_of_parallel_loop_expr env (ParallelCodegenCore.tag_expr e)
        | None -> go_raw expr
        end
  and go_raw = function
    | ParallelInstr.ExConst z -> string_of_z z
    | ParallelInstr.ExFloat lit -> Camlcoq.camlstring_of_coqstring lit
    | ParallelInstr.ExVar n -> string_of_parallel_loop_expr env (parallel_slot_expr slots n)
    | ParallelInstr.ExAccess a -> string_of_parallel_access env slots a
    | ParallelInstr.ExAdd (a, b) -> Printf.sprintf "(%s + %s)" (go a) (go b)
    | ParallelInstr.ExSub (a, b) -> Printf.sprintf "(%s - %s)" (go a) (go b)
    | ParallelInstr.ExMul (a, b) -> Printf.sprintf "(%s * %s)" (go a) (go b)
    | ParallelInstr.ExDiv (a, b) -> Printf.sprintf "(%s / %s)" (go a) (go b)
    | ParallelInstr.ExLe (a, b) -> Printf.sprintf "(%s <= %s)" (go a) (go b)
    | ParallelInstr.ExEq (a, b) -> Printf.sprintf "(%s == %s)" (go a) (go b)
    | ParallelInstr.ExAnd (a, b) -> Printf.sprintf "(%s && %s)" (go a) (go b)
    | ParallelInstr.ExCall (fn, args) ->
        let fn = Camlcoq.camlstring_of_coqstring fn in
        let args =
          match List.map go args with
          | [] -> ""
          | hd :: tl -> List.fold_left (fun acc s -> acc ^ ", " ^ s) hd tl
        in
        Printf.sprintf "%s(%s)" fn args
    | ParallelInstr.ExCond (c, t, f) ->
        Printf.sprintf "(%s ? %s : %s)" (go c) (go t) (go f)
  in
  go expr

let string_of_parallel_test env tst =
  let rec go = function
    | ParallelBaseLoop.LE (a, b) ->
        Printf.sprintf "%s <= %s"
          (string_of_parallel_loop_expr env a)
          (string_of_parallel_loop_expr env b)
    | ParallelBaseLoop.EQ (a, b) ->
        Printf.sprintf "%s == %s"
          (string_of_parallel_loop_expr env a)
          (string_of_parallel_loop_expr env b)
    | ParallelBaseLoop.And (a, b) -> Printf.sprintf "(%s && %s)" (go a) (go b)
    | ParallelBaseLoop.Or (a, b) -> Printf.sprintf "(%s || %s)" (go a) (go b)
    | ParallelBaseLoop.Not t -> Printf.sprintf "!(%s)" (go t)
    | ParallelBaseLoop.TConstantTest true -> "true"
    | ParallelBaseLoop.TConstantTest false -> "false"
  in
  go tst

let rec parallel_stmt_list_to_list = function
  | ParallelLoopIR.SNil -> []
  | ParallelLoopIR.SCons (st, tl) -> st :: parallel_stmt_list_to_list tl

let parallel_indent n = String.make (2 * n) ' '

let fresh_parallel_loop_name env depth =
  let rec pick n =
    let cand = Printf.sprintf "i%d" (depth + n) in
    if List.mem cand env then pick (n + 1) else cand
  in
  pick 0

let rec lines_of_parallel_stmt env depth lvl = function
  | ParallelLoopIR.Loop (mode, _, lb, ub, body) ->
      let v = fresh_parallel_loop_name env depth in
      let loop_kw =
        match mode with
        | ParallelLoopIR.SeqMode -> "for"
        | ParallelLoopIR.ParMode -> "parallel for"
        | ParallelLoopIR.VecMode -> "vector for"
      in
      let header =
        Printf.sprintf "%s%s %s in range(%s, %s) {"
          (parallel_indent lvl)
          loop_kw
          v
          (string_of_parallel_loop_expr env lb)
          (string_of_parallel_loop_expr env ub)
      in
      let body_lines = lines_of_parallel_stmt (v :: env) (depth + 1) (lvl + 1) body in
      header :: body_lines @ [parallel_indent lvl ^ "}"]
  | ParallelLoopIR.Instr (instr, slots) ->
      begin match instr with
      | ParallelInstr.SSkip -> [parallel_indent lvl ^ "skip;"]
      | ParallelInstr.SAssign (lhs, rhs) ->
          [parallel_indent lvl
           ^ string_of_parallel_access env slots lhs
           ^ " = "
           ^ string_of_parallel_instr_expr env slots rhs
           ^ ";"]
      end
  | ParallelLoopIR.Seq stmts ->
      List.concat (List.map (lines_of_parallel_stmt env depth lvl) (parallel_stmt_list_to_list stmts))
  | ParallelLoopIR.Guard (tst, body) ->
      let header =
        Printf.sprintf "%sif (%s) {" (parallel_indent lvl) (string_of_parallel_test env tst)
      in
      let body_lines = lines_of_parallel_stmt env depth (lvl + 1) body in
      header :: body_lines @ [parallel_indent lvl ^ "}"]

let string_of_parallel_loop (((stmt, varctxt), _vars) : ParallelLoopIR.t) =
  let ctxt_names = List.map name_of_ident varctxt in
  let header =
    match ctxt_names with
    | [] -> []
    | _ -> ["context(" ^ String.concat ", " ctxt_names ^ ");"; ""]
  in
  String.concat "\n" (header @ lines_of_parallel_stmt (List.rev ctxt_names) 0 0 stmt) ^ "\n"

let dump_poly_payload label pp =
  let module PL = SPolIRs.SPolIRs.PolyLang in
  let ((pis, varctxt), vars) = pp in
  Printf.eprintf
    "[debug] %s payload: pis=%d varctxt=%d vars=%d
"
    label (List.length pis) (List.length varctxt) (List.length vars);
  List.iteri
    (fun idx pi ->
      Printf.eprintf
        "[debug]   pi[%d]: depth=%d poly_rows=%d sched_rows=%d tf_rows=%d w=%d r=%d
"
        idx
        (int_of_nat (PL.pi_depth pi))
        (List.length (PL.pi_poly pi))
        (List.length (PL.pi_schedule pi))
        (List.length (PL.pi_transformation pi))
        (List.length (PL.pi_waccess pi))
        (List.length (PL.pi_raccess pi));
      Printf.eprintf
        "[debug]     schedule=%s
"
        (string_of_aff_list (PL.pi_schedule pi));
      Printf.eprintf
        "[debug]     transformation=%s
"
        (string_of_aff_list (PL.pi_transformation pi));
      Printf.eprintf
        "[debug]     waccess=%s
"
        (string_of_access_list (PL.pi_waccess pi));
      Printf.eprintf
        "[debug]     raccess=%s
"
        (string_of_access_list (PL.pi_raccess pi)))
    pis

let debug_env_enabled name =
  match Sys.getenv_opt name with
  | Some ("1" | "true" | "TRUE" | "yes" | "YES") -> true
  | _ -> false

let dump_poly_payload_if name label pp =
  if debug_env_enabled name then dump_poly_payload label pp

let dump_bandaffine_payload label env_size pil_ext =
  let module BA = STilingBandSched.CoreBandSched.BandAffine in
  Printf.eprintf
    "[debug] %s band-payload: env=%d pis=%d\n"
    label env_size (List.length pil_ext);
  List.iteri
    (fun idx pi ->
      Printf.eprintf
        "[debug]   ext[%d]: depth=%d sched1=%s sched2=%s tf=%s w=%s r=%s\n"
        idx
        (int_of_nat (BA.PolyLang.pi_depth_ext pi))
        (string_of_aff_list (BA.PolyLang.pi_schedule1_ext pi))
        (string_of_aff_list (BA.PolyLang.pi_schedule2_ext pi))
        (string_of_aff_list (BA.PolyLang.pi_transformation_ext pi))
        (string_of_access_list (BA.PolyLang.pi_waccess_ext pi))
        (string_of_access_list (BA.PolyLang.pi_raccess_ext pi)))
    pil_ext

let debug_bandaffine_pair_checks label env_size pil_ext =
  let module BA = STilingBandSched.CoreBandSched.BandAffine in
  let valid_access = BA.check_valid_access pil_ext in
  Printf.eprintf
    "[debug] %s valid_access=%b env=%d\n"
    label valid_access (int_of_nat env_size);
  let rec debug_self i = function
    | [] -> ()
    | pi :: rest ->
        let (res, ok) = BA.validate_two_instrs pi pi env_size in
        Printf.eprintf
          "[debug] %s self[%d]=%b(ok=%b)\n"
          label i res ok;
        debug_self (i + 1) rest
  in
  let rec debug_pairs i = function
    | [] -> ()
    | pi :: rest ->
        let rec debug_with j = function
          | [] -> ()
          | pj :: rest' ->
              let (fwd, ok_fwd) = BA.validate_two_instrs pi pj env_size in
              let (rev, ok_rev) = BA.validate_two_instrs pj pi env_size in
              Printf.eprintf
                "[debug] %s pair[%d,%d] fwd=%b(ok=%b) rev=%b(ok=%b)\n"
                label i j fwd ok_fwd rev ok_rev;
              debug_with (j + 1) rest'
        in
        debug_with (i + 1) rest;
        debug_pairs (i + 1) rest
  in
  debug_self 0 pil_ext;
  debug_pairs 0 pil_ext

let extract_poly loop =
  match SPolOpt.CoreOpt.Extractor.extractor loop with
  | Err msg -> frontend_failf "extractor failed: %s" (string_of_coq_err msg)
  | Okk pol -> pol

let poly_to_openscop pol =
  match SPolOpt.to_source_openscop pol with
  | None -> frontend_failf "cannot convert extracted polyhedral model to OpenScop"
  | Some scop -> scop

let validate_components pp1 pp2 =
  let ((pil1, varctxt1), _) = pp1 in
  let ((pil2, _), _) = pp2 in
  let (wf1, wf1_ok) = SPolOpt.CoreOpt.check_wf_polyprog pp1 in
  let (wf2, wf2_ok) = SPolOpt.CoreOpt.check_wf_polyprog pp2 in
  let (eqdom, eqdom_ok) = SPolOpt.CoreOpt.coq_EqDom pp1 pp2 in
  let env_dim = nat_of_int (List.length varctxt1) in
  let pil_ext = SPolIRs.SPolIRs.PolyLang.compose_pinstrs_ext pil1 pil2 in
  let valid_access = SPolOpt.CoreOpt.check_valid_access pil_ext in
  let (res, res_ok) = SPolOpt.CoreOpt.validate_instr_list (List.rev pil_ext) env_dim in
  ((wf1, wf1_ok), (wf2, wf2_ok), (eqdom, eqdom_ok), (valid_access, true), (res, res_ok))

let print_validate_components label pp1 pp2 =
  let ((wf1, wf1_ok), (wf2, wf2_ok), (eqdom, eqdom_ok), (valid_access, _), (res, res_ok)) =
    validate_components pp1 pp2
  in
  Printf.eprintf
    "[debug] %s components: wf1=%b(ok=%b) wf2=%b(ok=%b) eqdom=%b(ok=%b) valid_access=%b res=%b(ok=%b)\n"
    label wf1 wf1_ok wf2 wf2_ok eqdom eqdom_ok valid_access res res_ok

let extract_to_openscop loop =
  poly_to_openscop (extract_poly loop)

let schedule_poly pol =
  match SPolIRs.SPolIRs.scheduler pol with
  | Err msg -> frontend_failf "scheduler failed: %s" (string_of_coq_err msg)
  | Okk pol' -> pol'

let debug_scheduler loop =
  let pol0 = extract_poly loop in
  dump_poly_payload "extracted" pol0;
  let pol = SPolOpt.CoreOpt.Strengthen.strengthen_pprog pol0 in
  dump_poly_payload "strengthened" pol;
  let inscop = poly_to_openscop pol in
  let (self_valid, self_ok) = SPolOpt.CoreOpt.validate pol pol in
  print_validate_components "validate(strengthened, strengthened)" pol pol;
  Printf.eprintf
    "[debug] validate(strengthened, strengthened) = %b (ok=%b, alarm=%b)\n"
    self_valid self_ok (not self_ok);
  let pol_roundtrip =
    match SPolIRs.SPolIRs.PolyLang.from_openscop_like_source pol inscop with
    | Okk pol' -> pol'
    | Err msg -> frontend_failf "self round-trip failed: %s" (string_of_coq_err msg)
  in
  let pol_complete_before =
    match SPolIRs.SPolIRs.PolyLang.from_openscop_complete inscop with
    | Okk pol' -> pol'
    | Err _ -> SPolIRs.SPolIRs.PolyLang.dummy
  in
  dump_poly_payload "roundtrip-before" pol_roundtrip;
  dump_poly_payload "complete-before" pol_complete_before;
  let (roundtrip_valid, roundtrip_ok) = SPolOpt.CoreOpt.validate pol pol_roundtrip in
  print_validate_components "validate(strengthened, roundtrip-before)" pol pol_roundtrip;
  let (complete_before_valid, complete_before_ok) = SPolOpt.CoreOpt.validate pol pol_complete_before in
  print_validate_components "validate(strengthened, complete-before)" pol pol_complete_before;
  print_endline "== Debug Extracted OpenScop ==";
  OpenScopPrinter.openscop_printer' stdout inscop;
  print_newline ();
  print_endline "== Debug Roundtrip-Before OpenScop ==";
  OpenScopPrinter.openscop_printer' stdout (poly_to_openscop pol_roundtrip);
  print_newline ();
  Printf.eprintf
    "[debug] validate(strengthened, roundtrip-before) = %b (ok=%b, alarm=%b)\n"
    roundtrip_valid roundtrip_ok (not roundtrip_ok);
  let pol_sched = schedule_poly pol in
  dump_poly_payload "scheduled" pol_sched;
  let pol_complete_after =
    match SPolIRs.SPolIRs.scop_scheduler inscop with
    | Okk outscop ->
        begin match SPolIRs.SPolIRs.PolyLang.from_openscop_complete outscop with
        | Okk pol' -> pol'
        | Err _ -> SPolIRs.SPolIRs.PolyLang.dummy
        end
    | Err _ -> SPolIRs.SPolIRs.PolyLang.dummy
  in
  dump_poly_payload "complete-after" pol_complete_after;
  let (sched_valid, sched_ok) = SPolOpt.CoreOpt.validate pol pol_sched in
  print_validate_components "validate(strengthened, scheduled)" pol pol_sched;
  let (old_complete_sched_valid, old_complete_sched_ok) = SPolOpt.CoreOpt.validate pol_complete_before pol_sched in
  print_validate_components "validate(complete-before, scheduled)" pol_complete_before pol_sched;
  let (new_complete_sched_valid, new_complete_sched_ok) = SPolOpt.CoreOpt.validate pol pol_complete_after in
  print_validate_components "validate(strengthened, complete-after)" pol pol_complete_after;
  let (complete_sched_valid, complete_sched_ok) = SPolOpt.CoreOpt.validate pol_complete_before pol_complete_after in
  print_validate_components "validate(complete-before, complete-after)" pol_complete_before pol_complete_after;
  print_endline "== Debug Scheduled OpenScop ==";
  OpenScopPrinter.openscop_printer' stdout (poly_to_openscop pol_sched);
  print_newline ();
  Printf.eprintf
    "[debug] validate(strengthened, scheduled) = %b (ok=%b, alarm=%b)\n"
    sched_valid sched_ok (not sched_ok)

let dump_extracted_openscop loop =
  print_endline "== Extracted OpenScop ==";
  OpenScopPrinter.openscop_printer' stdout (extract_to_openscop loop);
  print_newline ()

let import_complete_spol_or_fail label scop =
  match SPolIRs.SPolIRs.PolyLang.from_openscop_complete scop with
  | Okk pol -> pol
  | Err msg ->
      frontend_failf
        "cannot import %s into syntax polyhedral IR: %s"
        label
        (string_of_coq_err msg)

let import_faithful_spol_or_fail label base scop =
  match SPolIRs.SPolIRs.PolyLang.from_openscop base scop with
  | Okk pol -> pol
  | Err msg ->
      frontend_failf
        "cannot import %s faithfully into syntax IR: %s"
        label
        (string_of_coq_err msg)

let import_schedule_only_spol_or_fail label base scop =
  match SPolIRs.SPolIRs.PolyLang.from_openscop_schedule_only base scop with
  | Okk pol -> pol
  | Err msg ->
      frontend_failf
        "cannot import %s as schedule-only syntax IR: %s"
        label
        (string_of_coq_err msg)

let import_complete_tpol_or_fail label scop =
  match TPolIRs.TPolIRs.PolyLang.from_openscop_complete scop with
  | Okk pol -> pol
  | Err msg ->
      frontend_failf
        "cannot import %s into validator polyhedral IR: %s"
        label
        (string_of_coq_err msg)

let import_complete_tiling_or_fail label scop =
  match TPolOpt.Tiling.PL.from_openscop_complete scop with
  | Okk pol -> pol
  | Err msg ->
      frontend_failf
        "cannot import %s into tiling validator IR: %s"
        label
        (string_of_coq_err msg)

let required_vars_for_tiling_pinstr env_size pi =
  max_int
    (env_size + Camlcoq.Nat.to_int (TPolOpt.Tiling.PL.pi_depth pi))
    (max_int
       (List.length (TPolOpt.Tiling.PL.pi_poly pi))
       (List.length (TPolOpt.Tiling.PL.pi_schedule pi)))

let required_vars_for_tiling_pprog pp =
  let ((pis, ctxt), vars) = pp in
  let env_size = List.length ctxt in
  List.fold_left
    (fun acc pi -> max_int acc (required_vars_for_tiling_pinstr env_size pi))
    (List.length vars)
    pis

let pad_tiling_vars_to required ((pis, ctxt), vars) =
  let current = List.length vars in
  if current >= required then
    ((pis, ctxt), vars)
  else
    let rec add idx n acc =
      if n <= 0 then List.rev acc
      else
        let ident =
          Camlcoq.intern_string (Printf.sprintf "__tiling_pad_%d" idx)
        in
        add (idx + 1) (n - 1) ((ident, TPolIRs.TPolIRs.Ty.dummy) :: acc)
    in
    ((pis, ctxt), vars @ add current (required - current) [])

let normalize_tiling_validator_inputs before_pol after_pol =
  let required =
    max_int
      (required_vars_for_tiling_pprog before_pol)
      (required_vars_for_tiling_pprog after_pol)
  in
  (pad_tiling_vars_to required before_pol, pad_tiling_vars_to required after_pol)

let build_canonical_tiled_after before_pol ws =
  let ((before_pis, before_ctxt), before_vars) = before_pol in
  let env_size = nat_of_int (List.length before_ctxt) in
  let after_pis =
    List.map2
      (fun before_pi w ->
        let cw = TPolOpt.Tiling.compiled_pinstr_tiling_witness w in
        {
          TPolOpt.Tiling.PL.pi_depth =
            nat_of_int
              (Camlcoq.Nat.to_int (TPolOpt.Tiling.PL.pi_depth before_pi)
               + List.length w.stw_links);
          pi_instr = TPolOpt.Tiling.PL.pi_instr before_pi;
          pi_poly =
            (TPolOpt.Tiling.ptw_link_domain cw)
            @
            (TPolOpt.Tiling.lifted_base_domain_after_env
               env_size
               cw
               (TPolOpt.Tiling.PL.pi_poly before_pi));
          pi_schedule =
            TPolOpt.Tiling.lift_schedule_after_env
              (TPolOpt.Tiling.ptw_added_dims cw)
              env_size
              (TPolOpt.Tiling.PL.pi_schedule before_pi);
          pi_point_witness = PointWitness.PSWTiling w;
          pi_transformation = TPolOpt.Tiling.PL.pi_transformation before_pi;
          pi_access_transformation =
            TPolOpt.Tiling.PL.pi_access_transformation before_pi;
          pi_waccess = TPolOpt.Tiling.PL.pi_waccess before_pi;
          pi_raccess = TPolOpt.Tiling.PL.pi_raccess before_pi;
        })
      before_pis
      ws
  in
  ((after_pis, before_ctxt), before_vars)

let build_canonical_tiled_after_spol before_pol ws =
  let ((before_pis, before_ctxt), before_vars) = before_pol in
  let env_size = nat_of_int (List.length before_ctxt) in
  let after_pis =
    List.map2
      (fun before_pi w ->
        let cw = TPolOpt.Tiling.compiled_pinstr_tiling_witness w in
        let added_dims = TPolOpt.Tiling.ptw_added_dims cw in
        {
          SPolIRs.SPolIRs.PolyLang.pi_depth =
            nat_of_int
              (Camlcoq.Nat.to_int (SPolIRs.SPolIRs.PolyLang.pi_depth before_pi)
               + List.length w.stw_links);
          pi_instr = SPolIRs.SPolIRs.PolyLang.pi_instr before_pi;
          pi_poly =
            (TPolOpt.Tiling.ptw_link_domain cw)
            @
            (TPolOpt.Tiling.lifted_base_domain_after_env
               env_size
               cw
               (SPolIRs.SPolIRs.PolyLang.pi_poly before_pi));
          pi_schedule =
            TPolOpt.Tiling.lift_schedule_after_env
              added_dims
              env_size
              (SPolIRs.SPolIRs.PolyLang.pi_schedule before_pi);
          pi_point_witness = PointWitness.PSWTiling w;
          pi_transformation = SPolIRs.SPolIRs.PolyLang.pi_transformation before_pi;
          pi_access_transformation =
            SPolIRs.SPolIRs.PolyLang.pi_access_transformation before_pi;
          pi_waccess = SPolIRs.SPolIRs.PolyLang.pi_waccess before_pi;
          pi_raccess = SPolIRs.SPolIRs.PolyLang.pi_raccess before_pi;
        })
      before_pis
      ws
  in
  ((after_pis, before_ctxt), before_vars)

let required_vars_for_spol_pinstr env_size pi =
  let module PL = SPolIRs.SPolIRs.PolyLang in
  let access_width accs =
    List.fold_left
      (fun acc (_, affs) ->
        List.fold_left
          (fun acc' (zs, _) -> max_int acc' (List.length zs))
          acc
          affs)
      0
      accs
  in
  max_int
    (env_size + Camlcoq.Nat.to_int (PL.pi_depth pi))
    (max_int
       (List.fold_left
          (fun acc (zs, _) -> max_int acc (List.length zs))
          0
          (PL.pi_poly pi))
       (max_int
          (List.fold_left
             (fun acc (zs, _) -> max_int acc (List.length zs))
             0
             (PL.pi_schedule pi))
          (max_int
             (List.fold_left
                (fun acc (zs, _) -> max_int acc (List.length zs))
                0
                (PL.pi_transformation pi))
             (max_int
                (access_width (PL.pi_waccess pi))
                (access_width (PL.pi_raccess pi))))))

let required_vars_for_spol_pprog pp =
  let ((pis, ctxt), vars) = pp in
  let env_size = List.length ctxt in
  List.fold_left
    (fun acc pi -> max_int acc (required_vars_for_spol_pinstr env_size pi))
    (List.length vars)
    pis

let pad_spol_vars_to required ((pis, ctxt), vars) =
  let current = List.length vars in
  if current >= required then
    ((pis, ctxt), vars)
  else
    let rec add idx n acc =
      if n <= 0 then List.rev acc
      else
        let ident =
          Camlcoq.intern_string (Printf.sprintf "__tiling_codegen_pad_%d" idx)
        in
        add (idx + 1) (n - 1) ((ident, SPolIRs.SPolIRs.Ty.dummy) :: acc)
    in
    ((pis, ctxt), vars @ add current (required - current) [])

let normalize_spol_codegen_input pp =
  pad_spol_vars_to (required_vars_for_spol_pprog pp) pp

let count_spol_domain_rows ((pis, _ctxt), _vars) =
  List.fold_left
    (fun acc pi -> acc + List.length (SPolIRs.SPolIRs.PolyLang.pi_poly pi))
    0
    pis

let dedup_spol_codegen_domains ((pis, ctxt), vars) =
  let module PL = SPolIRs.SPolIRs.PolyLang in
  let dedup_pi (pi : PL.coq_PolyInstr) =
    { pi with pi_poly = PL.dedup_domain_rows (PL.pi_poly pi) }
  in
  ((List.map dedup_pi pis, ctxt), vars)

let maybe_dedup_spol_codegen_domains timings metrics pol =
  add_metric metrics "codegen_input.pis" (let ((pis, _), _) = pol in List.length pis);
  add_metric metrics "codegen_input.domain_rows" (count_spol_domain_rows pol);
  if debug_env_enabled "POLCERT_PROFILE_DEDUP_CODEGEN_DOMAINS" then
    let deduped =
      time_stage timings "dedup_codegen_domains" (fun () ->
        dedup_spol_codegen_domains pol)
    in
    add_metric metrics "codegen_dedup.pis" (let ((pis, _), _) = deduped in List.length pis);
    add_metric metrics "codegen_dedup.domain_rows" (count_spol_domain_rows deduped);
    deduped
  else
    pol

let normalize_stiling_validator_inputs before_pol after_pol =
  let required =
    max_int
      (required_vars_for_spol_pprog before_pol)
      (required_vars_for_spol_pprog after_pol)
  in
  (pad_spol_vars_to required before_pol, pad_spol_vars_to required after_pol)

let check_tiling_after_wf after_pol =
  let (wf_after, wf_after_ok) =
    SPolOpt.CoreOpt.check_wf_polyprog_general after_pol
  in
  if not wf_after_ok then
    (false, false)
  else
    (wf_after, true)

let classify_tiling_band_route after_pol route route_ok =
  let accept_if_wf route_name =
    let (wf_after, wf_after_ok) =
      check_tiling_after_wf after_pol
    in
    if not wf_after_ok then
      (false, false, "alarm")
    else if not wf_after then
      (false, true, "rejected")
    else
      (true, true, route_name)
  in
  if not route_ok then
    (false, false, "alarm")
  else
    match route with
    | STilingBandSched.CoreBandRuntime.Rejected ->
        (false, true, "rejected")
    | STilingBandSched.CoreBandRuntime.DirectBandAccepted ->
        accept_if_wf "permutable-band"
    | STilingBandSched.CoreBandRuntime.GeneralScheduleAccepted ->
        accept_if_wf "actual-schedule"

let checked_tiling_validate_with_band_route before_pol after_pol ws =
  let (route, route_ok) =
    STilingBandSched.checked_tiling_schedule_sourceb_first_runtime_validate_route
      before_pol after_pol ws
  in
  classify_tiling_band_route after_pol route route_ok

let checked_tiling_validate_with_bands before_pol after_pol ws =
  let (res, ok, _) =
    checked_tiling_validate_with_band_route before_pol after_pol ws
  in
  (res, ok)

let checked_tiling_validate_direct before_pol after_pol ws =
  let (res, ok, route) =
    checked_tiling_validate_with_band_route before_pol after_pol ws
  in
  TilingValidationRoute.record route;
  (res, ok)

let tiling_artifact_from_scops_or_fail
    ~second_level
    ~before_label
    ~after_label
    before_scop
    after_scop =
  let tiling_mode = pluto_tiling_mode second_level in
  try
    PlutoTilingValidator.extract_phase_artifact_from_scops
      ~tiling_mode
      ~before_path:before_label
      ~after_path:after_label
      before_scop
      after_scop
  with
  | PlutoTilingValidator.ValidationError msg ->
      frontend_failf
        "cannot extract tiling witness/artifact for %s -> %s: %s"
        before_label
        after_label
        msg

let canonicalize_tiled_after before_label after_label before_pol after_scop ws =
  let canonical_after = build_canonical_tiled_after before_pol ws in
  match TPolOpt.Tiling.PL.from_openscop_schedule_only canonical_after after_scop with
  | Okk pol -> pol
  | Err msg ->
      frontend_failf
        "cannot import %s as a schedule over the canonical tiled skeleton for %s: %s"
        after_label
        before_label
        (string_of_coq_err msg)

let affine_forward_scops before_label after_label before_scop after_scop =
  let before_pol = import_complete_tpol_or_fail before_label before_scop in
  let after_pol = import_complete_tpol_or_fail after_label after_scop in
  TPolValidator.validate before_pol after_pol

let run_affine_validator before_file after_file =
  let before_scop = read_openscop_or_fail before_file in
  let after_scop = read_openscop_or_fail after_file in
  let (res, ok) =
    affine_forward_scops before_file after_file before_scop after_scop
  in
  Printf.printf "before: %s\n" before_file;
  Printf.printf "after:  %s\n" after_file;
  Printf.printf
    "contract: schedule refinement under supplied domains and trusted access summaries; statement bodies are not checked\n";
  Printf.printf "overall: %s\n" (if ok && res then "PASS" else "FAIL");
  if ok && res then 0 else 2

let tiling_forward_scops ~second_level ~before_label ~after_label before_scop after_scop =
  let before_pol = import_complete_spol_or_fail before_label before_scop in
  let artifact =
    tiling_artifact_from_scops_or_fail
      ~second_level
      ~before_label
      ~after_label
      before_scop
      after_scop
  in
  let ws = PhaseTiling.convert_witness artifact.artifact_witness in
  let after_pol =
    let canonical_after = build_canonical_tiled_after_spol before_pol ws in
    match SPolIRs.SPolIRs.PolyLang.from_openscop_schedule_only canonical_after artifact.artifact_after_scop with
    | Okk pol -> pol
    | Err msg ->
        frontend_failf
          "cannot import %s as a schedule over the canonical tiled skeleton for %s: %s"
          after_label
          before_label
          (string_of_coq_err msg)
  in
  let (before_pol, after_pol) =
    normalize_stiling_validator_inputs before_pol after_pol
  in
  checked_tiling_validate_direct before_pol after_pol ws

let extract_strengthened_poly loop =
  let pol0 = extract_poly loop in
  SPolOpt.CoreOpt.Strengthen.strengthen_pprog pol0

let tag_loop_for_parallel_pretty loop =
  ParallelCodegenCore.tag_loop loop

let hint_dims hints =
  List.map (fun hint -> hint.Scheduler.hint_current_dim) hints

let max_current_depth_spol_pprog pp =
  let ((pis, _ctxt), _vars) = pp in
  List.fold_left
    (fun acc pi -> max_int acc (int_of_nat (SPolIRs.SPolIRs.PolyLang.pi_depth pi)))
    0
    pis

let rec int_range lo hi =
  if lo >= hi then [] else lo :: int_range (lo + 1) hi

let unique_ints xs =
  let rec go seen acc = function
    | [] -> List.rev acc
    | x :: rest ->
        if List.mem x seen then go seen acc rest
        else go (x :: seen) (x :: acc) rest
  in
  go [] [] xs

let checked_affine_schedule_or_fail pol =
  let (pol', ok) = SPolOpt.CoreOpt.checked_affine_schedule pol in
  if not ok then
    frontend_failf "affine scheduling raised an extracted alarm before parallel codegen";
  pol'

type 'a phase_pipeline_artifacts = {
  phase_mid_scop : 'a;
  phase_tiling_scop : 'a;
  phase_after_scop : 'a;
  phase_has_final_affine : bool;
}

let current_midpoint_label () =
  if Scheduler.diamond_tiling_enabled () then
    diamond_midpoint_label
      (Scheduler.full_dimensional_diamond_start_enabled ())
  else if Scheduler.identity_schedule_enabled () then
    "mid_identity"
  else
    "mid_affine"

let current_tiling_label () =
  if Scheduler.diamond_tiling_enabled () then
    "posttile_diamond"
  else if Scheduler.intra_tile_enabled () then
    "posttile_rectangular"
  else if Scheduler.identity_schedule_enabled () then
    "identity_tiled"
  else
    "after_tiled"

let current_final_after_label () =
  if Scheduler.diamond_tiling_enabled () then
    "after_rescheduled"
  else if Scheduler.intra_tile_enabled () then
    "after_intratile"
  else if Scheduler.identity_schedule_enabled () then
    "identity_tiled"
  else
    "after_tiled"

let phase_pipeline_artifacts_or_fail before_scop =
  if Scheduler.post_tiling_affine_enabled () then
    match Scheduler.run_pluto_post_tiling_affine_pipeline before_scop with
    | Err msg ->
        frontend_failf
          "post-tiling affine Pluto pipeline failed: %s"
          (string_of_coq_err msg)
    | Okk (mid_scop, posttile_scop, after_scop) ->
        {
          phase_mid_scop = mid_scop;
          phase_tiling_scop = posttile_scop;
          phase_after_scop = after_scop;
          phase_has_final_affine = true;
        }
  else
    match Scheduler.run_pluto_phase_pipeline before_scop with
    | Err msg ->
        frontend_failf
          "phase-aligned Pluto pipeline failed: %s"
          (string_of_coq_err msg)
    | Okk (mid_scop, after_scop) ->
        {
          phase_mid_scop = mid_scop;
          phase_tiling_scop = after_scop;
          phase_after_scop = after_scop;
          phase_has_final_affine = false;
        }

let debug_band_tiling_runtime route loop =
  let pol0 = extract_poly loop in
  let pol = SPolOpt.CoreOpt.Strengthen.strengthen_pprog pol0 in
  let before_scop = poly_to_openscop pol in
  let identity_tiled =
    route_is_identity route
    && route_has_tiling route
    && not (Scheduler.diamond_tiling_enabled ())
  in
  let identity_pair_pipeline =
    identity_tiled && not (Scheduler.post_tiling_affine_enabled ())
  in
  let midpoint_label =
    if identity_tiled then "identity_before" else current_midpoint_label ()
  in
  let tiling_label =
    if identity_tiled then "identity_tiled" else current_tiling_label ()
  in
  let artifacts =
    if identity_pair_pipeline then
      match Scheduler.run_pluto_identity_tiling_pipeline before_scop with
      | Err msg ->
          frontend_failf
            "identity Pluto tiling pipeline failed: %s"
            (string_of_coq_err msg)
      | Okk (mid_scop, after_scop) ->
          {
            phase_mid_scop = mid_scop;
            phase_tiling_scop = after_scop;
            phase_after_scop = after_scop;
            phase_has_final_affine = false;
          }
    else
      phase_pipeline_artifacts_or_fail before_scop
  in
  let mid_scop = artifacts.phase_mid_scop in
  let tiling_scop = artifacts.phase_tiling_scop in
  let midpoint_importer =
    if identity_tiled then
      SPolIRs.SPolIRs.PolyLang.from_openscop_like_source
    else
      SPolIRs.SPolIRs.PolyLang.from_openscop_schedule_only
  in
  let midpoint_importer_label =
    if identity_tiled then "source-like" else "schedule-only"
  in
  let pol_mid =
    match midpoint_importer pol mid_scop with
    | Okk pol' -> pol'
    | Err msg ->
        frontend_failf
          "cannot import %s with the verified pipeline importer: %s"
          midpoint_label
          (string_of_coq_err msg)
  in
  let artifact =
    tiling_artifact_from_scops_or_fail
      ~second_level:(Scheduler.second_level_tiling_enabled ())
      ~before_label:midpoint_label
      ~after_label:tiling_label
      mid_scop
      tiling_scop
  in
  if debug_env_enabled "POLCERT_DEBUG_BAND_TILING" then
    Printf.eprintf
      "[debug-band-tiling] witness:\n%s\n"
      (PlutoTilingValidator.render_witness artifact.artifact_witness);
  let ws = PhaseTiling.convert_witness artifact.artifact_witness in
  let pol_after =
    let canonical_after = build_canonical_tiled_after_spol pol_mid ws in
    match
      SPolIRs.SPolIRs.PolyLang.from_openscop_schedule_only
        canonical_after
        artifact.artifact_after_scop
    with
    | Okk pol' -> pol'
    | Err msg ->
        frontend_failf "cannot import after_tiled over canonical skeleton: %s"
          (string_of_coq_err msg)
  in
  let (accepted, route_ok, route_name) =
    checked_tiling_validate_with_band_route pol_mid pol_after ws
  in
  Printf.eprintf
    "[debug-band-tiling] accepted=%b(ok=%b) route=%s\n"
    accepted route_ok route_name;
  dump_poly_payload
    (Printf.sprintf "band-mid(%s)" midpoint_importer_label)
    pol_mid;
  dump_poly_payload "band-after(canonical-schedule-only)" pol_after

let run_tiling_validator ~second_level before_file after_file =
  let report =
    PlutoTilingValidator.validate_files
      ~tiling_mode:(pluto_tiling_mode second_level)
      before_file
      after_file
  in
  print_endline (PlutoTilingValidator.render_report report);
  if not report.ok then
    2
  else
    let before_scop = read_openscop_or_fail before_file in
    let after_scop = read_openscop_or_fail after_file in
    let ((formal_res, formal_ok), route) =
      TilingValidationRoute.capture (fun () ->
        tiling_forward_scops
          ~second_level
          ~before_label:before_file
          ~after_label:after_file
          before_scop
          after_scop)
    in
    TilingValidationRoute.report route;
    Printf.printf "formal: %s\n"
      (if formal_ok && formal_res then "PASS" else "FAIL");
    if formal_ok && formal_res then 0 else 2

let run_tiling_witness_extractor ~second_level before_file after_file =
  let witness =
    PlutoTilingValidator.extract_witness_from_files
      ~tiling_mode:(pluto_tiling_mode second_level)
      before_file
      after_file
  in
  print_endline (PlutoTilingValidator.render_witness witness);
  0

let nth_or_fail ctx xs n =
  try List.nth xs n
  with Failure _ ->
    frontend_failf "%s index %d is out of bounds" ctx n

let apply_iss_bridge_to_spol_or_fail
    label
    before_pol
    (bridge : SLoopIss.parsed_iss_bridge) =
  let module PL = SPolIRs.SPolIRs.PolyLang in
  let ((before_pis, ctxt), vars) = before_pol in
  let stmt_ws = bridge.pib_witness.ISSWitness.iw_stmt_witnesses in
  if List.length before_pis <> List.length bridge.pib_before_domains then
    frontend_failf
      "%s: before stmt count mismatch between source polyhedral model (%d) and ISS bridge (%d)"
      label
      (List.length before_pis)
      (List.length bridge.pib_before_domains);
  if List.length stmt_ws <> List.length bridge.pib_after_domains then
    frontend_failf
      "%s: after stmt count mismatch between ISS witness (%d) and ISS bridge domains (%d)"
      label
      (List.length stmt_ws)
      (List.length bridge.pib_after_domains);
  let after_pis =
    List.map2
      (fun _dump_domain w ->
        let parent = int_of_nat w.ISSWitness.isw_parent_stmt in
        let source = nth_or_fail "ISS parent stmt" before_pis parent in
        let domain =
          source.PL.pi_poly
          @ PhaseISS.signed_piece_constraints
              bridge.pib_witness.ISSWitness.iw_cuts
              w.ISSWitness.isw_piece_signs
        in
        { source with PL.pi_poly = domain })
      bridge.pib_after_domains
      stmt_ws
  in
  let after_pol = ((after_pis, ctxt), vars) in
  let ok =
    SPolOpt.CoreOpt.ValidatorCore.checked_iss_complete_cut_shape_validate
      before_pol
      after_pol
      bridge.pib_witness
  in
  if ok then
    after_pol
  else
    frontend_failf
      "%s: extracted ISS complete-cut-shape checker rejected reconstructed split program"
      label

let iss_bridge_from_scop_opt before_scop =
  match Scheduler.iss_identity_bridge_from_scop before_scop with
  | Okk text -> SLoopIss.parse_iss_bridge_text_opt text
  | Err msg ->
      frontend_failf "ISS bridge export failed: %s" (string_of_coq_err msg)

let run_iss_bridge_validator = SLoopIss.run_iss_bridge_validator
let run_iss_dump_validator = SLoopIss.run_iss_dump_validator
let run_iss_pluto_suite = SLoopIss.run_iss_pluto_suite
let run_iss_pluto_live_suite = SLoopIss.run_iss_pluto_live_suite

let scheduler_value_or_fail label = function
  | Okk value -> value
  | Err msg ->
      frontend_failf "%s failed: %s" label (string_of_coq_err msg)

let identity_schedule_input_scop route pol before_scop =
  if route_has_iss route then
    match iss_bridge_from_scop_opt before_scop with
    | None -> before_scop
    | Some bridge ->
        apply_iss_bridge_to_spol_or_fail
          "iss-identity-schedule"
          pol
          bridge
        |> poly_to_openscop
  else
    before_scop

let scheduled_scop_of_route route loop =
  let pol = extract_strengthened_poly loop in
  let before_scop = poly_to_openscop pol in
  (* Match the verified pipeline: first check ISS, then schedule its output.
     The local route prevents the proposal helpers from applying ISS again. *)
  let before_scop = identity_schedule_input_scop route pol before_scop in
  let route = { route with SLoopRoute.structural_extension = SLoopRoute.Plain } in
  if route_uses_post_tiling_affine route then
    let (_, _, after_scop) =
      if route_has_iss route then
        scheduler_value_or_fail
          "ISS post-tiling affine Pluto pipeline"
          (Scheduler.run_pluto_post_tiling_affine_pipeline_with_iss before_scop)
      else
        scheduler_value_or_fail
          "post-tiling affine Pluto pipeline"
          (Scheduler.run_pluto_post_tiling_affine_pipeline before_scop)
    in
    after_scop
  else
    match route.SLoopRoute.schedule_family,
          route.SLoopRoute.structural_extension,
          route.SLoopRoute.tiling_family with
    | SLoopRoute.IdentitySchedule, _, SLoopRoute.NoTiling ->
        identity_schedule_input_scop route pol before_scop
    | SLoopRoute.AffineSchedule, SLoopRoute.Plain, SLoopRoute.NoTiling ->
        scheduler_value_or_fail
          "affine-only Pluto scheduling"
          (Scheduler.affine_only_scop_scheduler before_scop)
    | SLoopRoute.AffineSchedule, SLoopRoute.ISS, SLoopRoute.NoTiling ->
        scheduler_value_or_fail
          "ISS affine-only Pluto scheduling"
          (Scheduler.affine_only_scop_scheduler_with_iss before_scop)
    | SLoopRoute.IdentitySchedule, _, SLoopRoute.Tiled _ ->
        let tiling_input = identity_schedule_input_scop route pol before_scop in
        let (_, after_scop) =
          scheduler_value_or_fail
            "identity Pluto tiling pipeline"
            (Scheduler.run_pluto_identity_tiling_pipeline tiling_input)
        in
        after_scop
    | SLoopRoute.AffineSchedule, SLoopRoute.Plain, SLoopRoute.Tiled _ ->
        let (_, after_scop) =
          scheduler_value_or_fail
            "phase-aligned Pluto pipeline"
            (Scheduler.run_pluto_phase_pipeline before_scop)
        in
        after_scop
    | SLoopRoute.AffineSchedule, SLoopRoute.ISS, SLoopRoute.Tiled _ ->
        let (_, after_scop) =
          scheduler_value_or_fail
            "ISS phase-aligned Pluto pipeline"
            (Scheduler.run_pluto_phase_pipeline_with_iss before_scop)
        in
        after_scop

type hinted_schedule =
  | ParallelSchedule
  | VectorSchedule

let hinted_schedule_name = function
  | ParallelSchedule -> "parallel"
  | VectorSchedule -> "vector"

let scheduled_scop_and_hints_of_route kind route loop =
  let pol = extract_strengthened_poly loop in
  let before_scop = poly_to_openscop pol in
  let before_scop = identity_schedule_input_scop route pol before_scop in
  let route = { route with SLoopRoute.structural_extension = SLoopRoute.Plain } in
  let result =
    if route_uses_post_tiling_affine route then
      match kind, route_has_iss route with
      | ParallelSchedule, false ->
          Scheduler.post_tiling_affine_scop_scheduler_with_parallel_hint before_scop
      | ParallelSchedule, true ->
          Scheduler.post_tiling_affine_scop_scheduler_with_parallel_hint_with_iss before_scop
      | VectorSchedule, false ->
          Scheduler.post_tiling_affine_scop_scheduler_with_vector_hint before_scop
      | VectorSchedule, true ->
          Scheduler.post_tiling_affine_scop_scheduler_with_vector_hint_with_iss before_scop
    else
      match route.SLoopRoute.schedule_family,
            route.SLoopRoute.structural_extension,
            route.SLoopRoute.tiling_family,
            kind with
      | SLoopRoute.IdentitySchedule, _, SLoopRoute.NoTiling, _ ->
          frontend_failf
            "internal error: hinted %s execution requires identity tiling"
            (hinted_schedule_name kind)
      | SLoopRoute.IdentitySchedule, _, SLoopRoute.Tiled _, ParallelSchedule ->
          let input_scop = identity_schedule_input_scop route pol before_scop in
          Scheduler.tile_only_scop_scheduler_with_parallel_hint input_scop
      | SLoopRoute.IdentitySchedule, _, SLoopRoute.Tiled _, VectorSchedule ->
          let input_scop = identity_schedule_input_scop route pol before_scop in
          Scheduler.tile_only_scop_scheduler_with_vector_hint input_scop
      | SLoopRoute.AffineSchedule, SLoopRoute.Plain, SLoopRoute.NoTiling,
          ParallelSchedule ->
          Scheduler.affine_only_scop_scheduler_with_parallel_hint before_scop
      | SLoopRoute.AffineSchedule, SLoopRoute.ISS, SLoopRoute.NoTiling,
          ParallelSchedule ->
          Scheduler.affine_only_scop_scheduler_with_iss_with_parallel_hint before_scop
      | SLoopRoute.AffineSchedule, SLoopRoute.Plain, SLoopRoute.NoTiling,
          VectorSchedule ->
          Scheduler.affine_only_scop_scheduler_with_vector_hint before_scop
      | SLoopRoute.AffineSchedule, SLoopRoute.ISS, SLoopRoute.NoTiling,
          VectorSchedule ->
          Scheduler.affine_only_scop_scheduler_with_iss_with_vector_hint before_scop
      | SLoopRoute.AffineSchedule, SLoopRoute.Plain, SLoopRoute.Tiled _,
          ParallelSchedule ->
          begin match Scheduler.run_pluto_phase_pipeline_with_parallel_hint before_scop with
          | Err msg -> Err msg
          | Okk (_, after_scop, hints) -> Okk (after_scop, hints)
          end
      | SLoopRoute.AffineSchedule, SLoopRoute.ISS, SLoopRoute.Tiled _,
          ParallelSchedule ->
          begin match Scheduler.run_pluto_phase_pipeline_with_iss_with_parallel_hint before_scop with
          | Err msg -> Err msg
          | Okk (_, after_scop, hints) -> Okk (after_scop, hints)
          end
      | SLoopRoute.AffineSchedule, SLoopRoute.Plain, SLoopRoute.Tiled _,
          VectorSchedule ->
          begin match Scheduler.run_pluto_phase_pipeline_with_vector_hint before_scop with
          | Err msg -> Err msg
          | Okk (_, after_scop, hints) -> Okk (after_scop, hints)
          end
      | SLoopRoute.AffineSchedule, SLoopRoute.ISS, SLoopRoute.Tiled _,
          VectorSchedule ->
          begin match Scheduler.run_pluto_phase_pipeline_with_iss_with_vector_hint before_scop with
          | Err msg -> Err msg
          | Okk (_, after_scop, hints) -> Okk (after_scop, hints)
          end
  in
  scheduler_value_or_fail
    ((hinted_schedule_name kind) ^ " Pluto scheduling")
    result

let print_scheduled_scop scop =
  print_endline "== Scheduled OpenScop ==";
  OpenScopPrinter.openscop_printer' stdout scop;
  print_newline ()

let dump_scheduled_openscop route loop =
  print_scheduled_scop (scheduled_scop_of_route route loop)

let dump_scheduled_openscop_with_parallel route loop =
  let (scop, _) =
    scheduled_scop_and_hints_of_route ParallelSchedule route loop
  in
  print_scheduled_scop scop

let dump_scheduled_openscop_with_vector route loop =
  let (scop, _) = scheduled_scop_and_hints_of_route VectorSchedule route loop in
  print_scheduled_scop scop

let profile_codegen_pipeline timings metrics pol =
  let ((pis, varctxt), vars) = pol in
  let es = List.length varctxt in
  let es_nat = nat_of_int es in
  let n = SPolOpt.CoreOpt.CodeGen.codegen_target_dim pol in
  let n_int = int_of_nat n in
  let k =
    List.fold_left
      max
      0
      (List.map
         (fun pi -> List.length (SPolIRs.SPolIRs.PolyLang.pi_schedule pi))
         pis)
  in
  let k_nat = nat_of_int k in
  let epis =
    time_stage timings "codegen_elim_schedule" (fun () ->
      SPolOpt.CoreOpt.CodeGen.PolyLang.elim_schedule k_nat es_nat pis)
  in
  let (polyloop, ok_generate) =
    time_stage timings "codegen_ast_generate" (fun () ->
      SPolOpt.CoreOpt.CodeGen.ASTGen.generate_loop_many
        (nat_of_int (n_int + k - es))
        (nat_of_int (n_int + k))
        epis)
  in
  let polyloop_stats = polyloop_stats_of_stmt polyloop in
  add_metric metrics "polyloop_raw.nodes" polyloop_stats.pl_nodes;
  add_metric metrics "polyloop_raw.loops" polyloop_stats.pl_loops;
  add_metric metrics "polyloop_raw.guards" polyloop_stats.pl_guards;
  add_metric metrics "polyloop_raw.instrs" polyloop_stats.pl_instrs;
  add_metric metrics "polyloop_raw.seqs" polyloop_stats.pl_seqs;
  add_metric metrics "polyloop_raw.constraints" polyloop_stats.pl_constraints;
  let (simp, ok_simplify) =
    time_stage timings "codegen_polyloop_simpl" (fun () ->
      SPolOpt.CoreOpt.CodeGen.PolyLoopSimplifier.polyloop_simplify polyloop es_nat [])
  in
  let simp_stats = polyloop_stats_of_stmt simp in
  add_metric metrics "polyloop_simpl.nodes" simp_stats.pl_nodes;
  add_metric metrics "polyloop_simpl.loops" simp_stats.pl_loops;
  add_metric metrics "polyloop_simpl.guards" simp_stats.pl_guards;
  add_metric metrics "polyloop_simpl.instrs" simp_stats.pl_instrs;
  add_metric metrics "polyloop_simpl.seqs" simp_stats.pl_seqs;
  add_metric metrics "polyloop_simpl.constraints" simp_stats.pl_constraints;
  let (loop_raw, ok_loopgen) =
    time_stage timings "codegen_loopgen" (fun () ->
      SPolOpt.CoreOpt.CodeGen.LoopGen.polyloop_to_loop es_nat simp)
  in
  let loop_stats = loop_stmt_stats loop_raw in
  add_metric metrics "loop_raw.nodes" loop_stats.loop_nodes;
  add_metric metrics "loop_raw.loops" loop_stats.loop_loops;
  add_metric metrics "loop_raw.guards" loop_stats.loop_guards;
  add_metric metrics "loop_raw.instrs" loop_stats.loop_instrs;
  add_metric metrics "loop_raw.seqs" loop_stats.loop_seqs;
  let loop_with_ctxt = ((loop_raw, varctxt), vars) in
  let loop_clean =
    time_stage timings "cleanup" (fun () ->
      SPolOpt.CoreOpt.Prepare.Cleanup.cleanup loop_with_ctxt)
  in
  (loop_clean, ok_generate && ok_simplify && ok_loopgen)

let profile_identity_only loop =
  let timings = ref [] in
  let metrics = ref [] in
  let pol0 = time_stage timings "extract" (fun () -> extract_poly loop) in
  let pol =
    time_stage timings "strengthen" (fun () ->
      SPolOpt.CoreOpt.Strengthen.strengthen_pprog pol0)
  in
  let pol_norm =
    time_stage timings "normalize_codegen" (fun () ->
      normalize_spol_codegen_input pol)
  in
  let pol_prep =
    time_stage timings "prepare_codegen" (fun () ->
      SPolOpt.CoreOpt.Prepare.prepare_codegen pol_norm)
  in
  let pol_codegen = maybe_dedup_spol_codegen_domains timings metrics pol_prep in
  let (loop_clean, ok_codegen) = profile_codegen_pipeline timings metrics pol_codegen in
  print_stage_timings !timings;
  print_profile_metrics !metrics;
  (loop_clean, ok_codegen)

let profile_affine_only loop =
  let timings = ref [] in
  let metrics = ref [] in
  let pol0 = time_stage timings "extract" (fun () -> extract_poly loop) in
  let pol =
    time_stage timings "strengthen" (fun () ->
      SPolOpt.CoreOpt.Strengthen.strengthen_pprog pol0)
  in
  let pol_mid = time_stage timings "affine_schedule" (fun () -> checked_affine_schedule_or_fail pol) in
  let pol_norm =
    time_stage timings "normalize_codegen" (fun () ->
      normalize_spol_codegen_input pol_mid)
  in
  let pol_prep =
    time_stage timings "prepare_codegen" (fun () ->
      SPolOpt.CoreOpt.Prepare.prepare_codegen pol_norm)
  in
  let pol_codegen = maybe_dedup_spol_codegen_domains timings metrics pol_prep in
  let (loop_clean, ok_codegen) = profile_codegen_pipeline timings metrics pol_codegen in
  print_stage_timings !timings;
  print_profile_metrics !metrics;
  (loop_clean, ok_codegen)

let profile_default_tiled loop =
  let timings = ref [] in
  let metrics = ref [] in
  let pol0 = time_stage timings "extract" (fun () -> extract_poly loop) in
  let pol =
    time_stage timings "strengthen" (fun () ->
      SPolOpt.CoreOpt.Strengthen.strengthen_pprog pol0)
  in
  let before_scop =
    time_stage timings "export_before_scop" (fun () -> poly_to_openscop pol)
  in
  let midpoint_label = current_midpoint_label () in
  let tiling_label = current_tiling_label () in
  let final_after_label = current_final_after_label () in
  let artifacts =
    time_stage timings "pluto_phase_pipeline" (fun () ->
      phase_pipeline_artifacts_or_fail before_scop)
  in
  let mid_scop = artifacts.phase_mid_scop in
  let tiling_scop = artifacts.phase_tiling_scop in
  let after_scop = artifacts.phase_after_scop in
  let pol_mid =
    time_stage timings "import_mid_affine" (fun () ->
      import_schedule_only_spol_or_fail midpoint_label pol mid_scop)
  in
  let (affine_res, affine_ok) =
    time_stage timings "affine_validate" (fun () ->
      affine_forward_scops "before" midpoint_label before_scop mid_scop)
  in
  if not (affine_ok && affine_res) then begin
    print_stage_timings !timings;
    print_profile_metrics !metrics;
    (loop, false)
  end else
    let artifact =
      time_stage timings "extract_tiling_artifact" (fun () ->
        tiling_artifact_from_scops_or_fail
          ~second_level:(Scheduler.second_level_tiling_enabled ())
          ~before_label:midpoint_label
          ~after_label:tiling_label
          mid_scop
          tiling_scop)
    in
    let ws =
      time_stage timings "convert_tiling_witness" (fun () ->
        PhaseTiling.convert_witness artifact.artifact_witness)
    in
    let canonical_after =
      time_stage timings "build_canonical_after" (fun () ->
        build_canonical_tiled_after_spol pol_mid ws)
    in
    let pol_tiling_sched =
      time_stage timings "import_after_schedule" (fun () ->
        import_schedule_only_spol_or_fail
          tiling_label
          canonical_after
          artifact.artifact_after_scop)
    in
    let final_affine_ok =
      if artifacts.phase_has_final_affine then
        let (res, ok) =
          time_stage timings "affine_validate_reschedule" (fun () ->
            affine_forward_scops tiling_label final_after_label tiling_scop after_scop)
        in
        ok && res
      else
        true
    in
    if not final_affine_ok then begin
      print_stage_timings !timings;
      print_profile_metrics !metrics;
      (loop, false)
    end else
    let pol_after_sched =
      if artifacts.phase_has_final_affine then
        time_stage timings "import_after_reschedule" (fun () ->
          import_schedule_only_spol_or_fail
            final_after_label
            pol_tiling_sched
            after_scop)
      else
        pol_tiling_sched
    in
    let (pol_mid_val, pol_tiling_val) =
      time_stage timings "normalize_tiling_inputs" (fun () ->
        normalize_stiling_validator_inputs pol_mid pol_tiling_sched)
    in
    let (res, ok) =
      time_stage timings "checked_tiling_validate" (fun () ->
        checked_tiling_validate_direct pol_mid_val pol_tiling_val ws)
    in
    if not (ok && res) then begin
      print_stage_timings !timings;
      print_profile_metrics !metrics;
      (loop, false)
    end else
      let pol_after_codegen =
        time_stage timings "current_view" (fun () ->
          SPolIRs.SPolIRs.PolyLang.current_view_pprog pol_after_sched)
      in
      let pol_codegen =
        time_stage timings "normalize_codegen" (fun () ->
          normalize_spol_codegen_input pol_after_codegen)
      in
      let pol_prep =
        time_stage timings "prepare_codegen" (fun () ->
          SPolOpt.CoreOpt.Prepare.prepare_codegen pol_codegen)
      in
      let pol_codegen =
        maybe_dedup_spol_codegen_domains timings metrics pol_prep
      in
      let (loop_clean, ok_codegen) =
        profile_codegen_pipeline timings metrics pol_codegen
      in
      print_stage_timings !timings;
      print_profile_metrics !metrics;
      (loop_clean, ok_codegen)

let source_loop_count loop =
  let ((stmt, _), _) = loop in
  (loop_stmt_stats stmt).loop_loops

let profile_selected_optimization route loop =
  begin match route.SLoopRoute.execution_family with
  | SLoopRoute.Sequential -> ()
  | SLoopRoute.PlutoParallelHint _ | SLoopRoute.ParallelCurrent _ ->
      frontend_failf "--profile-stages does not support parallel routes yet"
  | SLoopRoute.PlutoVectorHint _ | SLoopRoute.VectorCurrent _ ->
      frontend_failf "--profile-stages does not support vector routes yet"
  end;
  if route_has_iss route then
    frontend_failf "--profile-stages currently supports the default no-ISS routes only";
  if route_is_second_level route then
    frontend_failf "--profile-stages does not support --second-level-tile yet";
  if route_is_identity route && not (route_has_tiling route) then
    profile_identity_only loop
  else if not (route_has_tiling route) then
    profile_affine_only loop
  else if
    source_loop_count loop = 0
  then
    profile_identity_only loop
  else
    profile_default_tiled loop

let standalone_handlers = {
  sa_run_affine_validator = run_affine_validator;
  sa_run_tiling_witness_extractor = run_tiling_witness_extractor;
  sa_run_tiling_validator = run_tiling_validator;
  sa_run_iss_dump_validator = run_iss_dump_validator;
  sa_run_iss_bridge_validator = run_iss_bridge_validator;
  sa_run_iss_pluto_suite = run_iss_pluto_suite;
  sa_run_iss_pluto_live_suite = run_iss_pluto_live_suite;
}

let verified_sequential_config_of_route route =
  let open VerifiedSequentialCompiler in
  (* This shape-independent route checks affine scheduling, tiling, and a final
     affine schedule.  It covers both rectangular intra-tile rescheduling and
     diamond rescheduling. *)
  if route_uses_post_tiling_affine route then
    if route_has_iss route then RawPostTilingAffineISS else RawPostTilingAffine
  else
  match route.SLoopRoute.schedule_family,
        route.SLoopRoute.structural_extension,
        route.SLoopRoute.tiling_family with
  | SLoopRoute.IdentitySchedule, SLoopRoute.Plain, SLoopRoute.NoTiling ->
      RawIdentity
  | SLoopRoute.AffineSchedule, SLoopRoute.Plain, SLoopRoute.NoTiling ->
      RawAffine
  | SLoopRoute.AffineSchedule, SLoopRoute.ISS, SLoopRoute.NoTiling ->
      RawAffineISS
  | SLoopRoute.IdentitySchedule, SLoopRoute.Plain,
      SLoopRoute.Tiled { levels = SLoopRoute.OneLevel; _ } ->
      RawIdentityBand
  | SLoopRoute.IdentitySchedule, SLoopRoute.Plain,
      SLoopRoute.Tiled { levels = SLoopRoute.TwoLevels; _ } ->
      RawIdentitySecondLevel
  | SLoopRoute.IdentitySchedule, SLoopRoute.ISS,
      SLoopRoute.Tiled { levels = SLoopRoute.OneLevel; _ } ->
      RawIdentityBandISS
  | SLoopRoute.IdentitySchedule, SLoopRoute.ISS,
      SLoopRoute.Tiled { levels = SLoopRoute.TwoLevels; _ } ->
      RawIdentitySecondLevelISS
  | SLoopRoute.AffineSchedule, SLoopRoute.Plain,
      SLoopRoute.Tiled { levels = SLoopRoute.OneLevel; _ } ->
      RawDefaultBand
  | SLoopRoute.AffineSchedule, SLoopRoute.Plain,
      SLoopRoute.Tiled { levels = SLoopRoute.TwoLevels; _ } ->
      RawSecondLevel
  | SLoopRoute.AffineSchedule, SLoopRoute.ISS,
      SLoopRoute.Tiled { levels = SLoopRoute.OneLevel; _ } ->
      RawISS
  | SLoopRoute.AffineSchedule, SLoopRoute.ISS,
      SLoopRoute.Tiled { levels = SLoopRoute.TwoLevels; _ } ->
      RawSecondLevelISS
  | SLoopRoute.IdentitySchedule, SLoopRoute.ISS, SLoopRoute.NoTiling ->
      RawUnsupported

let run_selected_sequential_loop_compiler route compile loop =
  let selected = verified_sequential_config_of_route route in
  if
    source_loop_count loop = 0
    && selected = VerifiedSequentialCompiler.RawDefaultBand
    && not (route_tiling_explicitly_requested route)
  then begin
    prerr_endline
      "[tiling-validation] status=not-applicable reason=no-loop";
    compile VerifiedSequentialCompiler.RawIdentity loop
  end
  else
    let ((optimized, ok), route) =
      TilingValidationRoute.capture (fun () ->
        compile selected loop)
    in
    TilingValidationRoute.report route;
    let tiling_ok =
      not (List.exists (String.equal "rejected") route)
    in
    (optimized, ok && tiling_ok)

let run_selected_sequential_loop_optimization route postpass loop =
  run_selected_sequential_loop_compiler route
    (fun selected loop ->
       VerifiedSequentialCompiler.compile_with_postpass
         selected postpass loop)
    loop

let verified_parallel_current_config_of_route route dim =
  let d = nat_of_int dim in
  let open VerifiedParallelCompiler in
  if route_uses_post_tiling_affine route then
    if route_has_iss route then RawParallelCurrentPostTilingAffineISS d
    else RawParallelCurrentPostTilingAffine d
  else if route_is_identity route && route_has_tiling route then
    if route_has_iss route then RawParallelCurrentIdentityTiledISS d
    else RawParallelCurrentIdentityTiled d
  else if route_has_iss route then
    if route_is_identity route then
      RawParallelCurrentIdentityISS d
    else if not (route_has_tiling route) then
      RawParallelCurrentAffineISS d
    else
      RawParallelCurrentDefaultISS d
  else if route_is_identity route then
    RawParallelCurrentIdentity d
  else if not (route_has_tiling route) then
    RawParallelCurrentAffine d
  else
    RawParallelCurrentDefault d

let verified_parallel_current_many_config_of_route route dims =
  let dims = List.map nat_of_int (unique_ints dims) in
  let open VerifiedParallelCompiler in
  if route_uses_post_tiling_affine route then
    if route_has_iss route then RawParallelCurrentManyPostTilingAffineISS dims
    else RawParallelCurrentManyPostTilingAffine dims
  else if route_is_identity route && route_has_tiling route then
    if route_has_iss route then RawParallelCurrentManyIdentityTiledISS dims
    else RawParallelCurrentManyIdentityTiled dims
  else if route_has_iss route then
    if route_is_identity route then
      RawParallelCurrentManyIdentityISS dims
    else if not (route_has_tiling route) then
      RawParallelCurrentManyAffineISS dims
    else
      RawParallelCurrentManyDefaultISS dims
  else if route_is_identity route then
    RawParallelCurrentManyIdentity dims
  else if not (route_has_tiling route) then
    RawParallelCurrentManyAffine dims
  else
    RawParallelCurrentManyDefault dims

let verified_vector_current_config_of_route route dim =
  let d = nat_of_int dim in
  let open VerifiedParallelCompiler in
  if route_uses_post_tiling_affine route then
    if route_has_iss route then RawVectorCurrentPostTilingAffineISS d
    else RawVectorCurrentPostTilingAffine d
  else if route_is_identity route && route_has_tiling route then
    if route_has_iss route then RawVectorCurrentIdentityTiledISS d
    else RawVectorCurrentIdentityTiled d
  else if route_has_iss route then
    if route_is_identity route then
      RawVectorCurrentIdentityISS d
    else if not (route_has_tiling route) then
      RawVectorCurrentAffineISS d
    else
      RawVectorCurrentDefaultISS d
  else if route_is_identity route then
    RawVectorCurrentIdentity d
  else if not (route_has_tiling route) then
    RawVectorCurrentAffine d
  else
    RawVectorCurrentDefault d

let valid_parallel_hint_scopes scop hints =
  let count = List.length (OpenScop.statements scop) in
  List.for_all (fun hint ->
    hint.Scheduler.hint_stmt_ids <> [] &&
    List.for_all (fun id -> id > 0 && id <= count)
      hint.Scheduler.hint_stmt_ids) hints

let parallel_scop_and_hint_dims_of_route ?hint_snapshot route loop =
  try
    let (after_scop, hints) =
      match hint_snapshot with
      | Some snapshot -> snapshot
      | None -> scheduled_scop_and_hints_of_route ParallelSchedule route loop
    in
    if valid_parallel_hint_scopes after_scop hints then
      (Some after_scop, hint_dims hints)
    else (None, [])
  with _ -> (None, [])

let max_hint_dim_exclusive dims =
  List.fold_left
    (fun acc dim -> if dim < 0 then acc else max_int acc (dim + 1))
    0
    dims

let max_scop_scattering_out_dim scop =
  List.fold_left
    (fun acc stmt ->
      max_int
        acc
        (int_of_nat
           (OpenScop.out_dim_nb
              (OpenScop.meta (OpenScop.scattering stmt)))))
    0
    (OpenScop.statements scop)

let parallel_candidate_hi_of_scop after_scop hinted_dims =
  let with_hints hi = max_int hi (max_hint_dim_exclusive hinted_dims) in
  let default_hi = with_hints 16 in
  match after_scop with
  | None -> default_hi
  | Some scop ->
      let raw_width = max_scop_scattering_out_dim scop in
      with_hints
        (int_of_nat
           (OpenScop.kept_scattering_rows_before scop (nat_of_int raw_width)))

let parallel_candidate_dims_of_scop after_scop hinted_dims =
  unique_ints
    (hinted_dims
     @ int_range 0 (parallel_candidate_hi_of_scop after_scop hinted_dims))

let vector_hint_dims_of_route route loop =
  try
    let (_, hints) =
      scheduled_scop_and_hints_of_route VectorSchedule route loop
    in
    hint_dims hints
  with _ -> []

let report_parallel_validation details =
  prerr_endline ("[parallel-validation] " ^ details)

let verified_sequential_after_parallel_skip route loop =
  report_parallel_validation
    "status=skipped source=pluto-hint reason=no-certifiable-dimension";
  let (optimized, ok) =
    run_selected_sequential_loop_optimization
      route VerifiedSequentialCompiler.no_postpass loop
  in
  (tag_loop_for_parallel_pretty optimized, ok)

let is_consumer_candidate_failure = function
  | CertcheckerConfig.CertCheckerFailure (_, msg) ->
      String.equal msg "Parallel validation failed"
      || String.equal
           msg
           "Annotated parallel codegen produced non-affine instruction trace loop"
      || String.equal
           msg
           "Annotated vector codegen produced a non-affine trace, a non-innermost vector loop, or no vector loop"
  | _ -> false

let verified_candidate_or_raise = function
  | Ok ((pl, ok), routes) ->
      let tiling_ok =
        not (List.exists (String.equal "rejected") routes)
      in
      if ok && tiling_ok then Some (pl, routes) else None
  | Error ((CertcheckerConfig.CertCheckerFailure _ as exn), routes) ->
      if is_consumer_candidate_failure exn then
        None
      else begin
        TilingValidationRoute.report routes;
        raise exn
      end
  | Error (exn, _) -> raise exn

let try_verified_parallel_current_compile route loop dim =
  verified_candidate_or_raise
    (TilingValidationRoute.capture_result (fun () ->
        VerifiedParallelCompiler.compile
          (verified_parallel_current_config_of_route route dim)
          loop))

let try_verified_parallel_current_many_compile route loop dims =
  let dims = unique_ints dims in
  if dims = [] then
    None
  else
    verified_candidate_or_raise
      (TilingValidationRoute.capture_result (fun () ->
          VerifiedParallelCompiler.compile
            (verified_parallel_current_many_config_of_route route dims)
            loop))

let try_verified_vector_current_compile route loop dim =
  verified_candidate_or_raise
    (TilingValidationRoute.capture_result (fun () ->
        VerifiedParallelCompiler.compile
          (verified_vector_current_config_of_route route dim)
          loop))

(* Profitability only: every candidate reaching this predicate has already
   passed the verified compiler.  Unknown bounds remain eligible; the search
   skips only candidates whose parallel loops are all demonstrably trivial. *)
let rec constant_parallel_bound = function
  | ParallelBaseLoop.Constant z -> Some z
  | ParallelBaseLoop.Var _ -> None
  | ParallelBaseLoop.Sum (a, b) ->
      constant_parallel_bounds Camlcoq.Z.add a b
  | ParallelBaseLoop.Mult (k, e) ->
      Option.map (Camlcoq.Z.mul k) (constant_parallel_bound e)
  | ParallelBaseLoop.Div (e, k) ->
      if Camlcoq.Z.eq k Camlcoq.Z.zero then None
      else Option.map (fun z -> Camlcoq.Z.div z k) (constant_parallel_bound e)
  | ParallelBaseLoop.Mod (e, k) ->
      if Camlcoq.Z.eq k Camlcoq.Z.zero then None
      else Option.map (fun z -> Camlcoq.Z.modulo z k) (constant_parallel_bound e)
  | ParallelBaseLoop.Max (a, b) ->
      constant_parallel_bounds (fun x y -> if Camlcoq.Z.le x y then y else x) a b
  | ParallelBaseLoop.Min (a, b) ->
      constant_parallel_bounds (fun x y -> if Camlcoq.Z.le x y then x else y) a b
and constant_parallel_bounds f a b =
  match constant_parallel_bound a, constant_parallel_bound b with
  | Some x, Some y -> Some (f x y)
  | _ -> None

let parallel_trip_count lb ub =
  let rec additive_terms = function
    | ParallelBaseLoop.Constant z -> ([], z)
    | ParallelBaseLoop.Sum (a, b) ->
        let (ta, ca) = additive_terms a in
        let (tb, cb) = additive_terms b in
        (ta @ tb, Camlcoq.Z.add ca cb)
    | e ->
        match constant_parallel_bound e with
        | Some z -> ([], z)
        | None -> ([e], Camlcoq.Z.zero)
  in
  let (lower_terms, lower_const) = additive_terms lb in
  let (upper_terms, upper_const) = additive_terms ub in
  if List.sort compare lower_terms = List.sort compare upper_terms then
    Some (Camlcoq.Z.sub upper_const lower_const)
  else None

let rec has_potential_parallel_iterations = function
  | ParallelLoopIR.Loop (mode, _, lb, ub, body) ->
      let nontrivial =
        match parallel_trip_count lb ub with
        | Some count -> Camlcoq.Z.gt count Camlcoq.Z.one
        | _ -> true
      in
      (mode = ParallelLoopIR.ParMode && nontrivial)
      || has_potential_parallel_iterations body
  | ParallelLoopIR.Instr _ -> false
  | ParallelLoopIR.Seq stmts ->
      List.exists has_potential_parallel_iterations (parallel_stmt_list_to_list stmts)
  | ParallelLoopIR.Guard (_, body) -> has_potential_parallel_iterations body

let parallel_candidate_is_potentially_nontrivial (((stmt, _), _) : ParallelLoopIR.t) =
  has_potential_parallel_iterations stmt

exception No_parallel_scope_candidate

let parallel_candidate_debug message =
  if Sys.getenv_opt "POLCERT_PARALLEL_DEBUG" = Some "1" then
    report_parallel_validation message

let same_parallel_instance_space (a : OpenScop.coq_OpenScop) (b : OpenScop.coq_OpenScop) =
  let arrays scop = List.filter (function OpenScop.ArrayExt _ -> true | _ -> false) scop.OpenScop.glb_exts in
  a.context = b.context && arrays a = arrays b
  && List.length a.statements = List.length b.statements
  && List.for_all2
       (fun x y -> x.OpenScop.domain = y.OpenScop.domain
           && x.OpenScop.access = y.OpenScop.access
           && x.OpenScop.stmt_exts_opt = y.OpenScop.stmt_exts_opt)
       a.statements b.statements

let normalize_parallel_tiled_scop route mid scop =
  if route_is_second_level route then
    try
      (PlutoTilingValidator.extract_phase_artifact_from_scops
        ~tiling_mode:PlutoTilingValidator.SecondLevel
        ~before_path:"parallel_mid" ~after_path:"parallel_tiled"
        mid scop).artifact_after_scop
    with PlutoTilingValidator.ValidationError _ ->
      raise No_parallel_scope_candidate
  else scop

(* Statement numbers in the OpenScop loop extension are one-based.  The
   extracted lowering uses positions in the imported statement list.  The
   resulting schedule is still an untrusted affine proposal. *)
let propose_scoped_parallel_schedule hints scop =
  let module P = SPolIRs.SPolIRs.PolyLang in
  let module V = SParallelPolOpt.ValidatorCore.ParallelCore in
  let ((pis, env), _) =
    P.canonicalize_schedule_pprog
      (P.current_view_pprog (import_complete_spol_or_fail "parallel scope" scop))
  in
  let count = List.length pis in
  let width = List.fold_left (fun w pi -> max w (List.length pi.P.pi_schedule)) 0 pis in
  if hints = [] || count = 0 then raise No_parallel_scope_candidate;
  let plans = List.map (fun hint ->
    let dim = hint.Scheduler.hint_current_dim in
    let ids = List.sort_uniq compare hint.Scheduler.hint_stmt_ids in
    if dim < 0 || dim >= width || ids = []
       || List.exists (fun id -> id <= 0 || id > count) ids
    then raise No_parallel_scope_candidate;
    { V.scoped_dim = nat_of_int dim;
      scoped_statements = List.map (fun id -> nat_of_int (id - 1)) ids }) hints
  in
  let statements = List.mapi (fun index stmt ->
    let pi = List.nth pis index in
    let zero = (List.init (List.length env + int_of_nat pi.P.pi_depth)
      (fun _ -> Camlcoq.Z.zero), Camlcoq.Z.zero) in
    let padded = pi.P.pi_schedule @
      List.init (width - List.length pi.P.pi_schedule) (fun _ -> zero) in
    let rows = SParallelPolOpt.scoped_parallel_rows plans (nat_of_int index)
      (nat_of_int 0) zero padded in
    let n = List.length rows in
    let scattering = {
      OpenScop.rel_type = OpenScop.ScttTy;
      OpenScop.meta = {
        OpenScop.row_nb = nat_of_int n;
        OpenScop.col_nb = nat_of_int (n + int_of_nat pi.P.pi_depth + List.length env + 2);
        OpenScop.out_dim_nb = nat_of_int n;
        OpenScop.in_dim_nb = pi.P.pi_depth;
        OpenScop.local_dim_nb = nat_of_int 0;
        OpenScop.param_nb = nat_of_int (List.length env);
      };
      OpenScop.constrs = P.affine_rows_to_sctt_constrs rows
        (nat_of_int (List.length env)) pi.P.pi_depth (nat_of_int n);
    } in
    { stmt with OpenScop.scattering = scattering }) (OpenScop.statements scop)
  in
  let proposed = { scop with OpenScop.statements = statements } in
  let dims = unique_ints (List.map (fun hint ->
    match OpenScop.raw_to_canonical_schedule_dim proposed
      (nat_of_int (2 * hint.Scheduler.hint_current_dim + 1)) with
    | Some dim -> int_of_nat dim
    | None -> raise No_parallel_scope_candidate) hints) in
  if dims = [] then raise No_parallel_scope_candidate;
  proposed, dims

let try_verified_scoped_hints ?hint_snapshot route loop =
  try
    let module P = SPolIRs.SPolIRs.PolyLang in
    let module V = SParallelPolOpt.ValidatorCore in
    let proposed, hints = match hint_snapshot with
      | Some snapshot -> snapshot
      | None -> scheduled_scop_and_hints_of_route ParallelSchedule route loop in
    let count = List.length (OpenScop.statements proposed) in
    if not (valid_parallel_hint_scopes proposed hints) then
      raise No_parallel_scope_candidate;
    (* Global hints keep their existing path and incur no extra validation. *)
    if not (List.exists (fun hint ->
      List.length (List.sort_uniq compare hint.Scheduler.hint_stmt_ids) < count) hints)
    then None else
    let after, dims = propose_scoped_parallel_schedule hints proposed in
    parallel_candidate_debug (Printf.sprintf
      "proposal=scoped phase=precheck hints=%s coordinates=%s"
      (String.concat ";" (List.map (fun h -> Printf.sprintf "%d:[%s]"
        h.Scheduler.hint_current_dim
        (String.concat "," (List.map string_of_int h.Scheduler.hint_stmt_ids))) hints))
      (String.concat "," (List.map string_of_int dims)));
    (* The ordinary many-dimension endpoint permits partial success.  A local
       hint proposal instead has to certify every requested coordinate. *)
    let check_parallel_coordinates after =
      let after_pol = P.canonicalize_schedule_pprog
        (P.current_view_pprog
          (import_complete_spol_or_fail "parallel scoped proposal" after)) in
      if not (List.for_all (fun dim ->
        let accepted, valid = V.check_pprog_parallel_currentb after_pol (nat_of_int dim) in
        parallel_candidate_debug (Printf.sprintf
          "proposal=scoped phase=precheck coordinate=%d accepted=%b valid=%b"
          dim accepted valid);
        accepted && valid) dims) then raise No_parallel_scope_candidate
    in
    let check_original_proposal before proposed =
      let old_pol = P.current_view_pprog
        (import_complete_spol_or_fail "parallel proposal source" before) in
      match P.from_openscop_schedule_only old_pol proposed with
      | Err _ -> raise No_parallel_scope_candidate
      | Okk proposed_pol ->
          let accepted, valid = V.validate_general old_pol proposed_pol in
          if not (accepted && valid) then begin
            parallel_candidate_debug "proposal=scoped reason=producer-affine-rejected";
            raise No_parallel_scope_candidate
          end
    in
    let candidate before_scop =
      let phases =
        if route_uses_post_tiling_affine route then
          Scheduler.run_pluto_post_tiling_affine_pipeline before_scop
        else
          let pair = if route_is_identity route then
            Scheduler.run_pluto_identity_tiling_pipeline before_scop
          else Scheduler.run_pluto_phase_pipeline before_scop in
          match pair with
          | Err msg -> Err msg
          | Okk (mid, tiled) -> Okk (mid, tiled, tiled)
      in
      match phases with
      | Err msg -> Err msg
      | Okk (mid, tiled, _) ->
          let tiled = normalize_parallel_tiled_scop route mid tiled in
          let proposed, after =
            if route_is_second_level route then
              let proposed = normalize_parallel_tiled_scop route mid proposed in
              let after, mapped_dims = propose_scoped_parallel_schedule hints proposed in
              if mapped_dims <> dims then raise No_parallel_scope_candidate;
              proposed, after
            else proposed, after
          in
          if not (same_parallel_instance_space tiled proposed) then begin
            parallel_candidate_debug "proposal=scoped reason=instance-space-mismatch";
            raise No_parallel_scope_candidate;
          end;
          check_original_proposal tiled proposed;
          check_parallel_coordinates after;
          Okk (mid, (tiled, after))
    in
    let config = if route_has_iss route then
      VerifiedParallelCompiler.RawParallelCurrentManyPostTilingAffineISS (List.map nat_of_int dims)
    else VerifiedParallelCompiler.RawParallelCurrentManyPostTilingAffine (List.map nat_of_int dims) in
    let result =
      if route_has_tiling route then
        Scheduler.with_post_tiling_affine_candidate candidate (fun () ->
          verified_candidate_or_raise (TilingValidationRoute.capture_result (fun () ->
            VerifiedParallelCompiler.compile config loop)))
      else
        Scheduler.with_affine_candidate (fun before ->
          check_original_proposal before proposed;
          check_parallel_coordinates after;
          Okk after) (fun () ->
          try_verified_parallel_current_many_compile route loop dims)
    in
    parallel_candidate_debug (Printf.sprintf
      "proposal=scoped hints=%d coordinates=%s accepted=%b"
      (List.length hints) (String.concat "," (List.map string_of_int dims))
      (Option.is_some result));
    result
  with
  | No_parallel_scope_candidate -> None
  | CertcheckerConfig.CertCheckerFailure (_, "Post-tiling affine validation failed.") ->
      parallel_candidate_debug "proposal=scoped reason=affine-rejected";
      None
  | CertcheckerConfig.CertCheckerFailure (_, "Scheduler validation failed.") ->
      parallel_candidate_debug "proposal=scoped reason=affine-rejected";
      None

let accept_scoped_parallel_result (pl, routes) =
  TilingValidationRoute.report routes;
  report_parallel_validation "status=accepted source=pluto-hint path=scoped-proposal";
  pl, true

let try_verified_proposed_parallel_compile route loop proposed_opt dim =
  if not (route_has_tiling route) || proposed_opt = None then None else
  let proposed = Option.get proposed_opt in
  let candidate before_scop =
    let phases =
      if route_uses_post_tiling_affine route then
        Scheduler.run_pluto_post_tiling_affine_pipeline before_scop
      else
        let pair =
          if route_is_identity route then
            Scheduler.run_pluto_identity_tiling_pipeline before_scop
          else Scheduler.run_pluto_phase_pipeline before_scop
        in
        match pair with
        | Err msg -> Err msg
        | Okk (mid, after) -> Okk (mid, after, after)
    in
    match phases with
    | Err msg -> Err msg
    | Okk (mid, tiled, _) ->
        let tiled = normalize_parallel_tiled_scop route mid tiled in
        let proposed = normalize_parallel_tiled_scop route mid proposed in
        if not (same_parallel_instance_space tiled proposed) then begin
          parallel_candidate_debug "proposal=actual reason=instance-space-mismatch";
          raise No_parallel_scope_candidate
        end;
        (* The hint refers to [proposed], not to the sequential tiling rerun.
           The affine validator checks this last schedule change before the
           global parallel certificate is checked. *)
        Okk (mid, (tiled, proposed))
  in
  let config =
    if route_has_iss route then
      VerifiedParallelCompiler.RawParallelCurrentPostTilingAffineISS (nat_of_int dim)
    else VerifiedParallelCompiler.RawParallelCurrentPostTilingAffine (nat_of_int dim)
  in
  try
    let result = Scheduler.with_post_tiling_affine_candidate candidate (fun () ->
      match TilingValidationRoute.capture_result (fun () ->
              VerifiedParallelCompiler.compile config loop) with
      | Error (CertcheckerConfig.CertCheckerFailure (_, "Post-tiling affine validation failed."), _) ->
          parallel_candidate_debug "scope=phase reason=affine-rejected";
          None
      | captured -> verified_candidate_or_raise captured) in
    parallel_candidate_debug
      (Printf.sprintf "proposal=%s coordinate=%d accepted=%b nontrivial=%b"
         "actual" dim
         (Option.is_some result)
         (match result with Some (pl, _) -> parallel_candidate_is_potentially_nontrivial pl | None -> false));
    result
  with
  | No_parallel_scope_candidate ->
      parallel_candidate_debug "proposal=actual reason=no-compatible-candidate";
      None
  | CertcheckerConfig.CertCheckerFailure (_, "Post-tiling affine validation failed.") ->
      parallel_candidate_debug "scope=phase reason=affine-rejected";
      None

let run_verified_hinted_parallel_optimization_with
    ?hint_snapshot
    ?proposal_compile
    ?(scope_compile = fun _ _ _ _ -> None)
    try_compile sequential_fallback route loop =
  let (after_scop, hinted_dims) =
    parallel_scop_and_hint_dims_of_route ?hint_snapshot route loop
  in
  let hinted_dims = unique_ints hinted_dims in
  let strict =
    match route.SLoopRoute.execution_family with
    | SLoopRoute.PlutoParallelHint { strict; _ } -> strict
    | _ -> false
  in
  let candidates =
    if strict then
      hinted_dims
    else
      parallel_candidate_dims_of_scop after_scop hinted_dims
  in
  let accept ((pl, routes), path, dim) =
    if Option.is_some proposal_compile then
      report_parallel_validation
        (Printf.sprintf "status=accepted source=pluto-hint path=%s coordinate=%d"
           path dim);
    TilingValidationRoute.report routes;
    (pl, true)
  in
  let rec go singleton_fallback = function
    | [] ->
        if strict then begin
          report_parallel_validation
            "status=rejected source=pluto-hint reason=no-certifiable-dimension";
          (tag_loop_for_parallel_pretty loop, false)
        end else begin
          match singleton_fallback with
          | Some result -> accept result
          | None -> sequential_fallback route loop
        end
    | dim :: rest ->
        let uses_proposal =
          Option.is_some proposal_compile
          && route_has_tiling route && List.mem dim hinted_dims
        in
        let reference () =
          Option.map (fun result -> (result, "checked-reference", dim))
            (try_compile route loop dim)
        in
        let compiled =
          match proposal_compile with
          | Some compile when uses_proposal ->
              begin match compile route loop after_scop dim with
              | Some accepted -> Some (accepted, "actual-proposal", dim)
              | None when strict -> None
              | None ->
                  begin match scope_compile route loop after_scop dim with
                  | Some ((pl, _) as accepted)
                    when parallel_candidate_is_potentially_nontrivial pl ->
                      Some (accepted, "phase-scoped-proposal", dim)
                  | _ -> reference ()
                  end
              end
          | _ -> reference ()
        in
        begin match compiled with
        | Some (((pl, _), _, _) as result) ->
            if strict || parallel_candidate_is_potentially_nontrivial pl then
              accept result
            else
              let fallback =
                match singleton_fallback with
                | Some _ -> singleton_fallback
                | None -> Some result
              in
              go fallback rest
        | None ->
            let scoped =
              if not strict && List.mem dim hinted_dims && not uses_proposal then
                scope_compile route loop after_scop dim
              else None
            in
            begin match scoped with
            | Some ((pl, _) as result) when parallel_candidate_is_potentially_nontrivial pl ->
                accept (result, "phase-scoped-proposal", dim)
            | _ -> go singleton_fallback rest
            end
        end
  in
  go None candidates

let run_verified_hinted_parallel_optimization route loop =
  Scheduler.with_checked_parallel_proposal (fun () ->
    let hint_snapshot =
      try Some (scheduled_scop_and_hints_of_route ParallelSchedule route loop)
      with _ -> None in
    match Option.bind hint_snapshot (fun snapshot ->
      try_verified_scoped_hints ~hint_snapshot:snapshot route loop) with
    | Some ((pl, _) as result) when parallel_candidate_is_potentially_nontrivial pl ->
        accept_scoped_parallel_result result
    | _ -> run_verified_hinted_parallel_optimization_with
      ?hint_snapshot
      ~proposal_compile:try_verified_proposed_parallel_compile
      try_verified_parallel_current_compile
      verified_sequential_after_parallel_skip
      route loop)

let run_verified_hinted_multipar_parallel_optimization_with
    ?hint_snapshot
    try_compile sequential_fallback route loop =
  let (after_scop, hinted_dims) =
    parallel_scop_and_hint_dims_of_route ?hint_snapshot route loop
  in
  let hinted_dims = unique_ints hinted_dims in
  let strict =
    match route.SLoopRoute.execution_family with
    | SLoopRoute.PlutoParallelHint { strict; _ } -> strict
    | _ -> false
  in
  let candidates =
    if strict then
      hinted_dims
    else
      parallel_candidate_dims_of_scop after_scop hinted_dims
  in
  let hinted_result =
    match hinted_dims with
    | [] -> None
    | _ -> try_compile route loop hinted_dims
  in
  let hinted_accepted =
    match hinted_result with
    | Some _ -> true
    | None -> false
  in
  let selected =
    match try_compile route loop candidates with
    | Some (pl, routes) -> Some (pl, routes, hinted_accepted)
    | None ->
        begin match hinted_result with
        | Some (pl, routes) -> Some (pl, routes, true)
        | None -> None
        end
  in
  match selected with
  | Some (pl, routes, _accepted_hint) ->
      TilingValidationRoute.report routes;
      (pl, true)
  | None ->
      if strict then begin
        report_parallel_validation
          "status=rejected source=pluto-hint reason=no-certifiable-dimension";
        (tag_loop_for_parallel_pretty loop, false)
      end else
        sequential_fallback route loop

let run_verified_hinted_multipar_parallel_optimization route loop =
  Scheduler.with_checked_parallel_proposal (fun () ->
    let hint_snapshot =
      try Some (scheduled_scop_and_hints_of_route ParallelSchedule route loop)
      with _ -> None in
    match Option.bind hint_snapshot (fun snapshot ->
      try_verified_scoped_hints ~hint_snapshot:snapshot route loop) with
    | Some ((pl, _) as result) when parallel_candidate_is_potentially_nontrivial pl ->
        accept_scoped_parallel_result result
    | _ -> run_verified_hinted_multipar_parallel_optimization_with
        ?hint_snapshot
        try_verified_parallel_current_many_compile
        verified_sequential_after_parallel_skip
        route loop)

let run_selected_parallel_optimization route loop =
  match route.SLoopRoute.execution_family with
  | SLoopRoute.PlutoParallelHint { multiple = true; _ } ->
      run_verified_hinted_multipar_parallel_optimization route loop
  | SLoopRoute.PlutoParallelHint { multiple = false; _ } ->
      run_verified_hinted_parallel_optimization route loop
  | _ ->
      frontend_failf "internal error: non-hinted route reached parallel hint dispatch"

let report_vector_validation details =
  prerr_endline ("[vector-validation] " ^ details)

let verified_sequential_after_vector_skip route loop reason =
  report_vector_validation ("status=skipped reason=" ^ reason);
  let (optimized, ok) =
    run_selected_sequential_loop_optimization
      route VerifiedSequentialCompiler.no_postpass loop
  in
  (tag_loop_for_parallel_pretty optimized, ok)

let run_selected_vector_optimization route loop =
  let hinted_dims = unique_ints (vector_hint_dims_of_route route loop) in
  (* Vectorization follows Pluto's innermost-loop hints.  The checked codegen
     independently rejects any annotation that is not structurally innermost. *)
  let candidates = hinted_dims in
  let rec go = function
    | [] ->
        let reason =
          if hinted_dims = [] then "no-hint"
          else "hint-not-certifiable-or-non-innermost"
        in
        verified_sequential_after_vector_skip route loop reason
    | dim :: rest ->
        begin match try_verified_vector_current_compile route loop dim with
        | Some (pl, routes) ->
            TilingValidationRoute.report routes;
            report_vector_validation
              "status=applied source=pluto-hint scope=innermost";
            (pl, true)
        | None -> go rest
        end
  in
  go candidates

let report_explicit_current_failure exn routes report_consumer =
  if is_consumer_candidate_failure exn then
    report_consumer ()
  else
    TilingValidationRoute.report routes

let run_selected_parallel_current_optimization route loop dim =
  match
    TilingValidationRoute.capture_result (fun () ->
        VerifiedParallelCompiler.compile
          (verified_parallel_current_config_of_route route dim)
          loop)
  with
  | Ok ((optimized, ok), route) ->
    let ok =
      ok && not (List.exists (String.equal "rejected") route)
    in
    if ok then
      TilingValidationRoute.report route
    else
      report_parallel_validation
        "status=rejected source=explicit-current reason=not-certifiable-or-out-of-range";
    (optimized, ok)
  | Error ((CertcheckerConfig.CertCheckerFailure _ as exn), routes) ->
      report_explicit_current_failure exn routes (fun () ->
        report_parallel_validation
          "status=rejected source=explicit-current reason=not-certifiable-or-out-of-range");
      raise exn
  | Error (exn, _) -> raise exn

let run_selected_vector_current_optimization route loop dim =
  match
    TilingValidationRoute.capture_result (fun () ->
        VerifiedParallelCompiler.compile
          (verified_vector_current_config_of_route route dim)
          loop)
  with
  | Ok ((optimized, ok), routes) ->
    let ok =
      ok && not (List.exists (String.equal "rejected") routes)
    in
    if ok then begin
      TilingValidationRoute.report routes;
      report_vector_validation
        "status=applied source=explicit-current scope=innermost";
      (optimized, true)
    end else begin
      report_vector_validation
        "status=rejected source=explicit-current reason=not-certifiable-or-non-innermost";
      frontend_failf "explicit vector-current validation failed"
    end
  | Error ((CertcheckerConfig.CertCheckerFailure _ as exn), routes) ->
      report_explicit_current_failure exn routes (fun () ->
        report_vector_validation
          "status=rejected source=explicit-current reason=not-certifiable-or-non-innermost");
      raise exn
  | Error (exn, _) -> raise exn

let pluto_unroll_factor cfg =
  match pluto_extra_value "--ufactor=" cfg with
  | Some value ->
      begin
        try max 1 (int_of_string value)
        with Failure _ -> 8
      end
  | None -> 8

module UnrollJamLoop = SPolIRs.SPolIRs.Loop
module UnrollJamInstr = SPolIRs.SPolIRs.Instr

let unrolljam_policy_name () =
  match Sys.getenv_opt "POLCERT_UNROLLJAM_POLICY" with
  | Some "none" -> "none"
  | Some "checked-all-depths" -> "checked-all-depths"
  | Some "pluto-profitability" -> "pluto-profitability"
  | Some value ->
      frontend_failf
        "unknown POLCERT_UNROLLJAM_POLICY=%s; expected none, checked-all-depths, or pluto-profitability"
        value
  | None -> "pluto-profitability"

let unrolljam_register_budget = 32

let unrolljam_debug_enabled () =
  match Sys.getenv_opt "POLCERT_UNROLLJAM_DEBUG" with
  | Some "1" | Some "true" | Some "yes" -> true
  | _ -> false

let unrolljam_loop_depths loop =
  let rec insert_depth depth depths =
    if List.mem depth depths then depths else depth :: depths
  in
  let rec stmt depth depths = function
    | UnrollJamLoop.Loop (_, _, body) ->
        stmt (depth + 1) (insert_depth depth depths) body
    | UnrollJamLoop.Instr (_, _) -> depths
    | UnrollJamLoop.Seq sts -> stmt_list depth depths sts
    | UnrollJamLoop.Guard (_, body) -> stmt depth depths body
  and stmt_list depth depths = function
    | UnrollJamLoop.SNil -> depths
    | UnrollJamLoop.SCons (st, rest) ->
        stmt_list depth (stmt depth depths st) rest
  in
  let ((st, _ctxt), _vars) = loop in
  List.sort compare (stmt 0 [] st)

let unrolljam_plan_of_depths depths =
  List.map
    (fun depth -> SLoopJamLower.make_unrolljam_candidate (nat_of_int depth))
    depths

let unrolljam_plan_of_depth_paths candidates =
  List.map
    (fun (depth, path) ->
       SLoopJamLower.make_unrolljam_candidate_at_path
         (nat_of_int depth)
         (List.map nat_of_int path))
    candidates

let string_of_unrolljam_path path =
  "[" ^ String.concat "," (List.map string_of_int path) ^ "]"

type unrolljam_loop_env_entry = {
  loop_depth : int;
  loop_deps : int list;
}

let unique_ints xs =
  List.fold_left
    (fun acc x -> if List.mem x acc then acc else x :: acc)
    []
    xs

let loop_env_lookup env n =
  nth_or env (Camlcoq.Nat.to_int n) None

let rec loop_expr_depths env = function
  | UnrollJamLoop.Constant _ -> []
  | UnrollJamLoop.Var n ->
      begin match loop_env_lookup env n with
      | Some entry -> entry.loop_deps
      | None -> []
      end
  | UnrollJamLoop.Sum (a, b)
  | UnrollJamLoop.Max (a, b)
  | UnrollJamLoop.Min (a, b) ->
      unique_ints (loop_expr_depths env a @ loop_expr_depths env b)
  | UnrollJamLoop.Mult (_, e)
  | UnrollJamLoop.Div (e, _)
  | UnrollJamLoop.Mod (e, _) ->
      loop_expr_depths env e

let loop_env_extend env depth lb ub =
  let deps =
    unique_ints (depth :: loop_expr_depths env lb @ loop_expr_depths env ub)
  in
  Some { loop_depth = depth; loop_deps = deps } :: env

let rec loop_expr_uses_depth env depth = function
  | UnrollJamLoop.Constant _ -> false
  | UnrollJamLoop.Var n ->
      begin match loop_env_lookup env n with
      | Some entry -> List.mem depth entry.loop_deps
      | None -> false
      end
  | UnrollJamLoop.Sum (a, b)
  | UnrollJamLoop.Max (a, b)
  | UnrollJamLoop.Min (a, b) ->
      loop_expr_uses_depth env depth a || loop_expr_uses_depth env depth b
  | UnrollJamLoop.Mult (_, e)
  | UnrollJamLoop.Div (e, _)
  | UnrollJamLoop.Mod (e, _) ->
      loop_expr_uses_depth env depth e

let rec loop_expr_key env = function
  | UnrollJamLoop.Constant z -> "c:" ^ string_of_z z
  | UnrollJamLoop.Var n ->
      begin match loop_env_lookup env n with
      | Some entry -> Printf.sprintf "l:%d" entry.loop_depth
      | None -> Printf.sprintf "p:%d" (Camlcoq.Nat.to_int n)
      end
  | UnrollJamLoop.Sum (a, b) ->
      "sum(" ^ loop_expr_key env a ^ "," ^ loop_expr_key env b ^ ")"
  | UnrollJamLoop.Mult (k, e) ->
      "mul(" ^ string_of_z k ^ "," ^ loop_expr_key env e ^ ")"
  | UnrollJamLoop.Div (e, k) ->
      "div(" ^ loop_expr_key env e ^ "," ^ string_of_z k ^ ")"
  | UnrollJamLoop.Mod (e, k) ->
      "mod(" ^ loop_expr_key env e ^ "," ^ string_of_z k ^ ")"
  | UnrollJamLoop.Max (a, b) ->
      "max(" ^ loop_expr_key env a ^ "," ^ loop_expr_key env b ^ ")"
  | UnrollJamLoop.Min (a, b) ->
      "min(" ^ loop_expr_key env a ^ "," ^ loop_expr_key env b ^ ")"

let affine_slot slots n =
  nth_or slots (Camlcoq.Nat.to_int n) (UnrollJamLoop.Constant (Camlcoq.Z.of_sint 0))

let rec affine_uses_depth env slots depth = function
  | UnrollJamInstr.AeConst _ -> false
  | UnrollJamInstr.AeVar n ->
      loop_expr_uses_depth env depth (affine_slot slots n)
  | UnrollJamInstr.AeAdd (a, b)
  | UnrollJamInstr.AeSub (a, b) ->
      affine_uses_depth env slots depth a || affine_uses_depth env slots depth b
  | UnrollJamInstr.AeMul (_, e) ->
      affine_uses_depth env slots depth e

let rec affine_key env slots = function
  | UnrollJamInstr.AeConst z -> "ac:" ^ string_of_z z
  | UnrollJamInstr.AeVar n -> "av:" ^ loop_expr_key env (affine_slot slots n)
  | UnrollJamInstr.AeAdd (a, b) ->
      "aa(" ^ affine_key env slots a ^ "," ^ affine_key env slots b ^ ")"
  | UnrollJamInstr.AeSub (a, b) ->
      "as(" ^ affine_key env slots a ^ "," ^ affine_key env slots b ^ ")"
  | UnrollJamInstr.AeMul (k, e) ->
      "am(" ^ string_of_z k ^ "," ^ affine_key env slots e ^ ")"

let access_uses_depth env slots depth = function
  | UnrollJamInstr.AcVar _ -> false
  | UnrollJamInstr.AcArr (_, idxs) ->
      List.exists (affine_uses_depth env slots depth) idxs

let access_key env slots = function
  | UnrollJamInstr.AcVar id -> "v:" ^ name_of_ident id
  | UnrollJamInstr.AcArr (id, idxs) ->
      "a:" ^ name_of_ident id ^ "[" ^
      String.concat "," (List.map (affine_key env slots) idxs) ^
      "]"

let unique_strings xs =
  List.fold_left
    (fun acc x -> if List.mem x acc then acc else x :: acc)
    []
    xs

let rec read_accesses_expr = function
  | UnrollJamInstr.ExConst _
  | UnrollJamInstr.ExFloat _
  | UnrollJamInstr.ExVar _ -> []
  | UnrollJamInstr.ExAccess acc -> [acc]
  | UnrollJamInstr.ExAdd (a, b)
  | UnrollJamInstr.ExSub (a, b)
  | UnrollJamInstr.ExMul (a, b)
  | UnrollJamInstr.ExDiv (a, b)
  | UnrollJamInstr.ExLe (a, b)
  | UnrollJamInstr.ExEq (a, b)
  | UnrollJamInstr.ExAnd (a, b) ->
      read_accesses_expr a @ read_accesses_expr b
  | UnrollJamInstr.ExCall (_, args) ->
      List.concat (List.map read_accesses_expr args)
  | UnrollJamInstr.ExCond (c, t, f) ->
      read_accesses_expr c @ read_accesses_expr t @ read_accesses_expr f

let instr_accesses = function
  | UnrollJamInstr.SSkip -> []
  | UnrollJamInstr.SAssign (lhs, rhs) -> lhs :: read_accesses_expr rhs

let rec loop_contains_loop = function
  | UnrollJamLoop.Loop _ -> true
  | UnrollJamLoop.Instr _ -> false
  | UnrollJamLoop.Seq sts -> stmt_list_contains_loop sts
  | UnrollJamLoop.Guard (_, body) -> loop_contains_loop body
and stmt_list_contains_loop = function
  | UnrollJamLoop.SNil -> false
  | UnrollJamLoop.SCons (st, rest) ->
      loop_contains_loop st || stmt_list_contains_loop rest

let rec collect_access_keys env depth = function
  | UnrollJamLoop.Loop (lb, ub, body) ->
      collect_access_keys (loop_env_extend env depth lb ub) (depth + 1) body
  | UnrollJamLoop.Instr (instr, slots) ->
      List.map (access_key env slots) (instr_accesses instr)
  | UnrollJamLoop.Seq sts -> collect_access_keys_list env depth sts
  | UnrollJamLoop.Guard (_, body) -> collect_access_keys env depth body
and collect_access_keys_list env depth = function
  | UnrollJamLoop.SNil -> []
  | UnrollJamLoop.SCons (st, rest) ->
      collect_access_keys env depth st @ collect_access_keys_list env depth rest

let rec collect_innermost_access_groups env depth = function
  | UnrollJamLoop.Loop (lb, ub, body) ->
      let env' = loop_env_extend env depth lb ub in
      if loop_contains_loop body then
        collect_innermost_access_groups env' (depth + 1) body
      else
        [collect_access_keys env' (depth + 1) body]
  | UnrollJamLoop.Instr _ -> []
  | UnrollJamLoop.Seq sts -> collect_innermost_access_groups_list env depth sts
  | UnrollJamLoop.Guard (_, body) -> collect_innermost_access_groups env depth body
and collect_innermost_access_groups_list env depth = function
  | UnrollJamLoop.SNil -> []
  | UnrollJamLoop.SCons (st, rest) ->
      collect_innermost_access_groups env depth st @
      collect_innermost_access_groups_list env depth rest

let rec collect_invariant_access_keys env slots depth acc =
  if access_uses_depth env slots depth acc then [] else [access_key env slots acc]

let rec collect_invariant_keys_stmt env next_depth candidate_depth = function
  | UnrollJamLoop.Loop (lb, ub, body) ->
      collect_invariant_keys_stmt
        (loop_env_extend env next_depth lb ub)
        (next_depth + 1)
        candidate_depth
        body
  | UnrollJamLoop.Instr (instr, slots) ->
      List.concat
        (List.map
           (collect_invariant_access_keys env slots candidate_depth)
           (instr_accesses instr))
  | UnrollJamLoop.Seq sts -> collect_invariant_keys_list env next_depth candidate_depth sts
  | UnrollJamLoop.Guard (_, body) ->
      collect_invariant_keys_stmt env next_depth candidate_depth body
and collect_invariant_keys_list env next_depth candidate_depth = function
  | UnrollJamLoop.SNil -> []
  | UnrollJamLoop.SCons (st, rest) ->
      collect_invariant_keys_stmt env next_depth candidate_depth st @
      collect_invariant_keys_list env next_depth candidate_depth rest

let rec collect_innermost_invariant_groups env depth candidate_depth = function
  | UnrollJamLoop.Loop (lb, ub, body) ->
      let env' = loop_env_extend env depth lb ub in
      if loop_contains_loop body then
        collect_innermost_invariant_groups env' (depth + 1) candidate_depth body
      else
        [collect_invariant_keys_stmt env' (depth + 1) candidate_depth body]
  | UnrollJamLoop.Instr _ -> []
  | UnrollJamLoop.Seq sts -> collect_innermost_invariant_groups_list env depth candidate_depth sts
  | UnrollJamLoop.Guard (_, body) ->
      collect_innermost_invariant_groups env depth candidate_depth body
and collect_innermost_invariant_groups_list env depth candidate_depth = function
  | UnrollJamLoop.SNil -> []
  | UnrollJamLoop.SCons (st, rest) ->
      collect_innermost_invariant_groups env depth candidate_depth st @
      collect_innermost_invariant_groups_list env depth candidate_depth rest

let max_unique_count groups =
  List.fold_left
    (fun acc group -> max acc (List.length (unique_strings group)))
    0
    groups

let unrolljam_profitability_stats factor env depth lb ub body =
  if not (loop_contains_loop body) then
    None
  else
    let candidate_env = loop_env_extend env depth lb ub in
    let access_groups =
      collect_innermost_access_groups candidate_env (depth + 1) body
    in
    let invariant_groups =
      collect_innermost_invariant_groups candidate_env (depth + 1) depth body
    in
    let total_unique = max_unique_count access_groups in
    let invariant_unique = max_unique_count invariant_groups in
    let regs =
      (total_unique * factor) - (invariant_unique * (factor - 1))
    in
    Some (total_unique, invariant_unique, regs)

let unrolljam_profitable_at_depth factor env depth lb ub body =
  match unrolljam_profitability_stats factor env depth lb ub body with
  | None -> false
  | Some (total_unique, invariant_unique, regs) ->
      invariant_unique > 0 &&
      invariant_unique < total_unique &&
      unrolljam_register_budget - regs >= 0

let pluto_profitability_candidates factor loop =
  let ((stmt, varctxt), _vars) = loop in
  let initial_env = List.map (fun _ -> None) varctxt in
  let rec insert_candidate cand candidates =
    if List.mem cand candidates then candidates else cand :: candidates
  in
  let rec stmt_candidates env depth path candidates = function
    | UnrollJamLoop.Loop (lb, ub, body) ->
        if unrolljam_debug_enabled () then begin
          match unrolljam_profitability_stats factor env depth lb ub body with
          | None ->
              Printf.eprintf
                "[polcert-unrolljam] depth=%d path=%s profitable=false reason=no-inner-loop\n%!"
                depth (string_of_unrolljam_path path)
          | Some (total_unique, invariant_unique, regs) ->
              Printf.eprintf
                "[polcert-unrolljam] depth=%d path=%s total=%d invariant=%d regs=%d cost=%d profitable=%b\n%!"
                depth (string_of_unrolljam_path path)
                total_unique invariant_unique regs
                (unrolljam_register_budget - regs)
                (unrolljam_profitable_at_depth factor env depth lb ub body)
        end;
        let candidates =
          if unrolljam_profitable_at_depth factor env depth lb ub body
          then insert_candidate (depth, path) candidates
          else candidates
        in
        stmt_candidates
          (loop_env_extend env depth lb ub)
          (depth + 1)
          (path @ [0])
          candidates
          body
    | UnrollJamLoop.Instr _ -> candidates
    | UnrollJamLoop.Seq sts -> stmt_list_candidates env depth path 0 candidates sts
    | UnrollJamLoop.Guard (_, body) ->
        stmt_candidates env depth (path @ [0]) candidates body
  and stmt_list_candidates env depth path index candidates = function
    | UnrollJamLoop.SNil -> candidates
    | UnrollJamLoop.SCons (st, rest) ->
        let candidates =
          stmt_candidates env depth (path @ [index]) candidates st
        in
        stmt_list_candidates env depth path (index + 1) candidates rest
  in
  List.sort compare (stmt_candidates initial_env 0 [] [] stmt)

let select_unrolljam_plan cfg loop =
  (* This is the untrusted policy hook. It only selects candidate positions;
     the extracted Coq pass still checks every selected transformation. *)
  match unrolljam_policy_name () with
  | "none" -> []
  | "checked-all-depths" ->
      unrolljam_plan_of_depths (unrolljam_loop_depths loop)
  | "pluto-profitability" ->
      unrolljam_plan_of_depth_paths
        (pluto_profitability_candidates (pluto_unroll_factor cfg) loop)
  | _ -> assert false

let run_requested_sequential_loop_optimization cfg route postpass loop =
  if cfg.pluto_unrolljam_seen then
    let const_first =
      String.equal (unrolljam_policy_name ()) "checked-all-depths"
    in
    let factor = nat_of_int (pluto_unroll_factor cfg) in
    run_selected_sequential_loop_compiler route
      (fun selected loop ->
         VerifiedSequentialCompiler.compile_with_unrolljam
           selected
           const_first
           (select_unrolljam_plan cfg)
           factor
           loop)
      loop
  else
    run_selected_sequential_loop_optimization route postpass loop

let parallel_unrolljam_const_first () =
  (* Full constant unrolling can remove every loop before the fresh parallel
     validation.  Parallel combinations retain block loops and let the checked
     unroll-jam pass transform them instead. *)
  false

let try_verified_parallel_current_unrolljam_compile cfg route loop dim =
  verified_candidate_or_raise
    (TilingValidationRoute.capture_result (fun () ->
       VerifiedParallelCompiler.compile_parallel_after_unrolljam
         (verified_sequential_config_of_route route)
         (parallel_unrolljam_const_first ())
         (select_unrolljam_plan cfg)
         (nat_of_int (pluto_unroll_factor cfg))
         (nat_of_int dim)
         loop))

let try_verified_parallel_current_many_unrolljam_compile cfg route loop dims =
  let dims = unique_ints dims in
  if dims = [] then
    None
  else
    verified_candidate_or_raise
      (TilingValidationRoute.capture_result (fun () ->
         VerifiedParallelCompiler.compile_parallel_many_after_unrolljam
           (verified_sequential_config_of_route route)
           (parallel_unrolljam_const_first ())
           (select_unrolljam_plan cfg)
           (nat_of_int (pluto_unroll_factor cfg))
           (List.map nat_of_int dims)
           loop))

let verified_sequential_after_parallel_unrolljam_skip cfg route loop =
  report_parallel_validation
    "status=skipped source=pluto-hint reason=no-certifiable-dimension-after-unrolljam";
  let (optimized, ok) =
    run_requested_sequential_loop_optimization
      cfg route VerifiedSequentialCompiler.no_postpass loop
  in
  (tag_loop_for_parallel_pretty optimized, ok)

let run_requested_hinted_parallel_unrolljam_optimization cfg route loop =
  match route.SLoopRoute.execution_family with
  | SLoopRoute.PlutoParallelHint { multiple = true; _ } ->
      run_verified_hinted_multipar_parallel_optimization_with
        (try_verified_parallel_current_many_unrolljam_compile cfg)
        (verified_sequential_after_parallel_unrolljam_skip cfg)
        route loop
  | SLoopRoute.PlutoParallelHint { multiple = false; _ } ->
      run_verified_hinted_parallel_optimization_with
        (try_verified_parallel_current_unrolljam_compile cfg)
        (verified_sequential_after_parallel_unrolljam_skip cfg)
        route loop
  | _ ->
      frontend_failf
        "internal error: non-hinted route reached parallel unroll-jam dispatch"

let require_checked_success ok =
  if not ok then begin
    prerr_endline "[alarm] requested checked optimization was rejected";
    exit 1
  end

let run_requested_parallel_const_unroll cfg (optimized, ok) =
  if ok && cfg.force_const_unroll then
    let (unrolled, unroll_ok) =
      VerifiedParallelCompiler.checked_const_unroll optimized
    in
    (unrolled, unroll_ok)
  else
    (optimized, ok)

let () =
  try
    Gc.set { (Gc.get()) with
               Gc.minor_heap_size = 524288;
               Gc.major_heap_increment = 4194304 };
    let cfg = parse_args () in
    let selection = validate_flag_model Sys.argv.(0) cfg in
    if cfg.pluto_compat_dry_run then exit 0;
    configure_scheduler_modes selection cfg;
    match SLoopDispatch.run_standalone_action selection standalone_handlers with
    | ExitCode code ->
        exit code
    | ContinueToLoop ->
      let route =
        match selection with
        | SLoopRoute.Optimize route -> route
        | SLoopRoute.Standalone _ ->
            frontend_failf "internal error: standalone route reached optimizer dispatch"
      in
      begin match cfg.input with
      | None ->
        print_endline (usage Sys.argv.(0));
        exit 2
      | Some file ->
        let prog = SLoopParse.parse_file file in
        let loop = SLoopElab.elaborate prog in
        let postpass =
          if cfg.force_const_unroll && not cfg.pluto_unrolljam_seen then
            VerifiedSequentialCompiler.const_unroll_postpass
          else
            VerifiedSequentialCompiler.no_postpass
        in
        if cfg.dump_input then print_section "Input Loop" (SLoopPretty.string_of_loop loop);
        if route.SLoopRoute.extract_only then begin
          let scop =
            if cfg.extract_strengthened_only then
              poly_to_openscop (extract_strengthened_poly loop)
            else extract_to_openscop loop
          in
          OpenScopPrinter.openscop_printer' stdout scop;
          print_newline ();
          exit 0
        end;
        if route.SLoopRoute.profile_stages then begin
          let (_profiled, profile_ok) = profile_selected_optimization route loop in
          TilingValidationRoute.clear ();
          let (optimized, verified_ok) =
            run_requested_sequential_loop_optimization
              cfg route postpass loop
          in
          let ok = profile_ok && verified_ok in
          require_checked_success ok;
          print_section "Optimized Loop" (SLoopPretty.string_of_loop optimized);
          exit 0
        end;
        if cfg.dump_extracted_openscop then dump_extracted_openscop loop;
        if cfg.dump_scheduled_openscop then
          begin match route.SLoopRoute.execution_family with
          | SLoopRoute.PlutoVectorHint _ ->
              dump_scheduled_openscop_with_vector route loop
          | SLoopRoute.PlutoParallelHint _ ->
              dump_scheduled_openscop_with_parallel route loop
          | SLoopRoute.Sequential
          | SLoopRoute.ParallelCurrent _
          | SLoopRoute.VectorCurrent _ ->
              dump_scheduled_openscop route loop
          end;
        if cfg.debug_scheduler then debug_scheduler loop;
        if debug_env_enabled "POLCERT_DEBUG_BAND_TILING" then
          debug_band_tiling_runtime route loop;
        begin match route.SLoopRoute.execution_family with
        | SLoopRoute.VectorCurrent dim ->
            let (optimized, ok) =
              run_selected_vector_current_optimization route loop dim
            in
            require_checked_success ok;
            print_section "Optimized Loop" (string_of_parallel_loop optimized)
        | SLoopRoute.ParallelCurrent dim ->
            let (optimized, ok) =
              run_selected_parallel_current_optimization route loop dim
              |> run_requested_parallel_const_unroll cfg
            in
            require_checked_success ok;
            print_section "Optimized Loop" (string_of_parallel_loop optimized)
        | SLoopRoute.PlutoVectorHint _ ->
            let (optimized, ok) = run_selected_vector_optimization route loop in
            require_checked_success ok;
            print_section "Optimized Loop" (string_of_parallel_loop optimized)
        | SLoopRoute.PlutoParallelHint _ ->
            let (optimized, ok) =
              (if cfg.pluto_unrolljam_seen then
                 run_requested_hinted_parallel_unrolljam_optimization cfg route loop
               else
                 run_selected_parallel_optimization route loop)
              |> run_requested_parallel_const_unroll cfg
            in
            require_checked_success ok;
            print_section "Optimized Loop" (string_of_parallel_loop optimized)
        | SLoopRoute.Sequential ->
            let (optimized, ok) =
              run_requested_sequential_loop_optimization
                cfg route postpass loop
            in
            require_checked_success ok;
            print_section "Optimized Loop" (SLoopPretty.string_of_loop optimized)
        end
      end
  with
  | Sys_error msg -> error no_loc "%s" msg; exit 2
  | SLoopParse.Error (pos, msg) -> error no_loc "parse error at byte %d: %s" pos msg; exit 2
  | SLoopElab.Error msg -> error no_loc "elaboration error: %s" msg; exit 2
  | FrontendFailure msg -> error no_loc "%s" msg; exit 2
  | PlutoTilingValidator.ValidationError msg -> error no_loc "%s" msg; exit 2
  | CertcheckerConfig.CertCheckerFailure (_, msg) ->
      prerr_endline "[alarm] requested checked optimization was rejected";
      error no_loc "optimization failed inside extracted runtime: %s" msg; exit 2
  | e -> crash e

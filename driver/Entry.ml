open Diagnostics
open Result
open TPolValidator
open TPolOpt
open TilingWitness

module TBandSched = TilingBandDirectRuntime.TilingBandDirectRuntime(TPolIRs.TPolIRs)

let tool_name = "Verified Validator for Affine Scheduling and Tiling"

type validation_kind =
  | Kind_auto
  | Kind_affine
  | Kind_tiling

type file_mode =
  | Pair_mode of string * string
  | Phase_mode of string * string * string
  | Diamond_phase_mode of string * string * string * string
  | Iss_bridge_mode of string
  | Iss_dump_mode of string * string

let pluto_tiling_mode second_level =
  if second_level
  then PlutoTilingValidator.SecondLevel
  else PlutoTilingValidator.Ordinary

let usage prog =
  Printf.sprintf
    "Usage:\n  %s [--kind auto|affine|tiling] [--second-level-tile] <before.scop> <after.scop>\n  %s [--kind auto|affine|tiling] [--second-level-tile] <before.scop> <mid.scop> <after.scop>\n  %s [--kind auto|affine|tiling] [--second-level-tile] <before.scop> <mid.scop> <posttile.scop> <after.scop>\n  %s --iss-bridge <bridge.txt>\n  %s --iss-debug-dumps <before.txt> <after.txt>\n\nAliases:\n  --auto      : same as --kind auto\n  --affine    : same as --kind affine\n  --tiling    : same as --kind tiling\n\nTwo-input mode:\n  auto   : try affine validation first, then tiling validation\n  affine : run affine validation on before/after\n  tiling : run tiling validation on before/after\n\nThree-input mode:\n  auto   : run affine(before, mid), then tiling(mid, after)\n  affine : run affine(before, mid) only\n  tiling : run tiling(mid, after) only\n\nFour-input mode:\n  auto   : run affine(before, mid), tiling(mid, posttile), affine(posttile, after)\n  affine : run affine(before, mid) and affine(posttile, after)\n  tiling : run tiling(mid, posttile) only\n\nOptions:\n  --second-level-tile : enable dependency-aware witness canonicalization and\n                        raw-order to canonical-order import alignment for tiling modes\n\nISS modes:\n  --iss-bridge      : delegate to polopt --validate-iss-bridge\n  --iss-debug-dumps : delegate to polopt --validate-iss-debug-dumps\n"
    prog prog prog prog prog

let string_of_coq_err msg = Camlcoq.camlstring_of_coqstring msg

let rec nat_of_int n =
  if n <= 0 then Datatypes.O else Datatypes.S (nat_of_int (n - 1))

let kind_of_string = function
  | "auto" -> Kind_auto
  | "affine" -> Kind_affine
  | "tiling" -> Kind_tiling
  | s -> invalid_arg ("unknown validation kind: " ^ s)

let resolve_tool_or_fail name =
  let exe_dir =
    try Filename.dirname (Unix.readlink (Printf.sprintf "/proc/%d/exe" (Unix.getpid ())))
    with _ -> Filename.dirname Sys.argv.(0)
  in
  let candidates =
    [ Filename.concat exe_dir name;
      Filename.concat (Sys.getcwd ()) name;
      Filename.concat "/polcert" name ]
  in
  match List.find_opt Sys.file_exists candidates with
  | Some path -> path
  | None -> failwith ("cannot locate helper executable " ^ name)

let run_polopt_passthrough args =
  let polopt = resolve_tool_or_fail "polopt" in
  let cmd =
    String.concat " "
      (Filename.quote polopt :: List.map Filename.quote args)
  in
  Sys.command cmd

let read_scop_or_fail path =
  match OpenScopReader.read path with
  | Some scop -> scop
  | None -> failwith ("cannot read OpenScop file " ^ path)

let import_complete_or_fail path scop =
  match TPolIRs.TPolIRs.PolyLang.from_openscop_complete scop with
  | Okk pol -> pol
  | Err msg ->
      failwith
        (Printf.sprintf
           "cannot import %s as a complete polyhedral model: %s"
           path
           (string_of_coq_err msg))

let import_complete_tiling_or_fail path scop =
  match TPolIRs.TPolIRs.PolyLang.from_openscop_complete scop with
  | Okk pol -> pol
  | Err msg ->
      failwith
        (Printf.sprintf
          "cannot import %s as a tiling polyhedral model: %s"
           path
           (string_of_coq_err msg))

let affine_relation before_path after_path =
  let scop1 = read_scop_or_fail before_path in
  let scop2 = read_scop_or_fail after_path in
  let pol1 = import_complete_or_fail before_path scop1 in
  let pol2 = import_complete_or_fail after_path scop2 in
  let (res1, ok1) = validate pol1 pol2 in
  let (res2, ok2) = validate pol2 pol1 in
  (ok1, res1, ok2, res2)

let affine_forward before_path after_path =
  let scop1 = read_scop_or_fail before_path in
  let scop2 = read_scop_or_fail after_path in
  let pol1 = import_complete_or_fail before_path scop1 in
  let pol2 = import_complete_or_fail after_path scop2 in
  let (res, ok) = validate pol1 pol2 in
  (ok, res)

let max_int a b = if a >= b then a else b

let required_vars_for_pinstr env_size pi =
  let module PL = TPolIRs.TPolIRs.PolyLang in
  max_int
    (env_size + Camlcoq.Nat.to_int (PL.pi_depth pi))
    (max_int
       (List.length (PL.pi_poly pi))
       (List.length (PL.pi_schedule pi)))

let required_vars_for_pprog pp =
  let ((pis, ctxt), vars) = pp in
  let env_size = List.length ctxt in
  List.fold_left
    (fun acc pi -> max_int acc (required_vars_for_pinstr env_size pi))
    (List.length vars)
    pis

let pad_vars_to required ((pis, ctxt), vars) =
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
      (required_vars_for_pprog before_pol)
      (required_vars_for_pprog after_pol)
  in
  (pad_vars_to required before_pol, pad_vars_to required after_pol)

let build_canonical_tiled_after before_pol ws =
  let ((before_pis, before_ctxt), before_vars) = before_pol in
  let env_size = nat_of_int (List.length before_ctxt) in
  let after_pis =
    List.map2
      (fun before_pi w ->
        let cw = Tiling.compiled_pinstr_tiling_witness w in
        {
          TPolIRs.TPolIRs.PolyLang.pi_depth =
            nat_of_int
              (Camlcoq.Nat.to_int (TPolIRs.TPolIRs.PolyLang.pi_depth before_pi)
               + List.length w.stw_links);
          pi_instr = TPolIRs.TPolIRs.PolyLang.pi_instr before_pi;
          pi_poly =
            (Tiling.ptw_link_domain cw)
            @
            (Tiling.lifted_base_domain_after_env
               env_size
               cw
               (TPolIRs.TPolIRs.PolyLang.pi_poly before_pi));
          pi_schedule =
            Tiling.lift_schedule_after_env
              (Tiling.ptw_added_dims cw)
              env_size
              (TPolIRs.TPolIRs.PolyLang.pi_schedule before_pi);
          pi_point_witness = PointWitness.PSWTiling w;
          pi_transformation = TPolIRs.TPolIRs.PolyLang.pi_transformation before_pi;
          pi_access_transformation =
            TPolIRs.TPolIRs.PolyLang.pi_access_transformation before_pi;
          pi_waccess = TPolIRs.TPolIRs.PolyLang.pi_waccess before_pi;
          pi_raccess = TPolIRs.TPolIRs.PolyLang.pi_raccess before_pi;
        })
      before_pis
      ws
  in
  ((after_pis, before_ctxt), before_vars)

let canonicalize_tiled_after before_pol after_path after_scop ws =
  let canonical_after = build_canonical_tiled_after before_pol ws in
  match TPolIRs.TPolIRs.PolyLang.from_openscop_schedule_only canonical_after after_scop with
  | Okk pol -> pol
  | Err msg ->
      failwith
        (Printf.sprintf
           "cannot import %s as a schedule over the canonical tiled skeleton: %s"
           after_path
           (string_of_coq_err msg))

let tiling_artifact_from_files_or_fail ~second_level before_path after_path =
  PlutoTilingValidator.extract_phase_artifact_from_files
    ~tiling_mode:(pluto_tiling_mode second_level)
    before_path
    after_path

let check_tiling_after_wf after_pol =
  let (wf_after, wf_after_ok) =
    TPolValidator.check_wf_polyprog_general after_pol
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
    | TBandSched.Rejected ->
        (false, true, "rejected")
    | TBandSched.DirectBandAccepted ->
        accept_if_wf "permutable-band"
    | TBandSched.GeneralScheduleAccepted ->
        accept_if_wf "actual-schedule"

let checked_tiling_validate_with_bands before_pol after_pol ws =
  let (route, route_ok) =
    TBandSched.checked_tiling_schedule_sourceb_first_runtime_validate_route
      before_pol after_pol ws
  in
  classify_tiling_band_route after_pol route route_ok

let run_tiling_pair ~second_level before_path after_path =
  let before_scop = read_scop_or_fail before_path in
  let before_pol = import_complete_tiling_or_fail before_path before_scop in
  let artifact = tiling_artifact_from_files_or_fail ~second_level before_path after_path in
  let ws = PhaseTiling.convert_witness artifact.artifact_witness in
  let after_pol =
    canonicalize_tiled_after
      before_pol
      after_path
      artifact.artifact_after_scop
      ws
  in
  let (before_pol, after_pol) =
    normalize_tiling_validator_inputs before_pol after_pol
  in
  let (res, ok, route) =
    checked_tiling_validate_with_bands before_pol after_pol ws
  in
  (ok, res, route)

let print_affine_relation before_path after_path =
  let (ok1, res1, ok2, res2) = affine_relation before_path after_path in
  if ok1 && res1 && ok2 && res2 then begin
    Printf.printf
      "[EQ] The supplied schedules (%s, %s) refine each other under their trusted domain/access summaries; statement bodies are not checked.\n"
      before_path after_path;
    true
  end else if ok1 && res1 then begin
    Printf.printf
      "[GT] Schedule %s refines %s under the supplied trusted domain/access summaries.\n"
      after_path before_path;
    true
  end else if ok2 && res2 then begin
    Printf.printf
      "[LT] Schedule %s refines %s under the supplied trusted domain/access summaries.\n"
      before_path after_path;
    true
  end else begin
    Printf.printf
      "[NE] Cannot establish schedule refinement between %s and %s under the supplied domain/access summaries.\n"
      before_path after_path;
    false
  end

let print_tiling_result ~second_level before_path after_path =
  let (ok, res, route) = run_tiling_pair ~second_level before_path after_path in
  if ok && res then begin
    Printf.printf
      "[TILING-OK] %s validates %s as a tiling-derived refinement (route=%s).\n"
      after_path before_path route;
    true
  end else begin
    Printf.printf
      "[TILING-FAIL] %s does not validate %s as a tiling-derived refinement (route=%s).\n"
      after_path before_path route;
    false
  end

let run_iss_bridge bridge =
  run_polopt_passthrough ["--validate-iss-bridge"; bridge]

let run_iss_dumps before_file after_file =
  run_polopt_passthrough
    ["--validate-iss-debug-dumps"; before_file; after_file]

let parse_args () =
  let kind = ref Kind_auto in
  let second_level = ref false in
  let files = ref [] in
  let iss_bridge = ref None in
  let iss_dumps = ref None in
  let rec go i =
    if i >= Array.length Sys.argv then ()
    else
      match Sys.argv.(i) with
      | "--kind" ->
          if i + 1 >= Array.length Sys.argv then begin
            prerr_endline "option --kind expects a value";
            prerr_endline (usage Sys.argv.(0));
            exit 2
          end;
          kind := kind_of_string Sys.argv.(i + 1);
          go (i + 2)
      | "--auto" ->
          kind := Kind_auto;
          go (i + 1)
      | "--affine" ->
          kind := Kind_affine;
          go (i + 1)
      | "--tiling" ->
          kind := Kind_tiling;
          go (i + 1)
      | "--second-level-tile" ->
          second_level := true;
          go (i + 1)
      | "--iss-bridge" ->
          if i + 1 >= Array.length Sys.argv then begin
            prerr_endline "option --iss-bridge expects one file path";
            prerr_endline (usage Sys.argv.(0));
            exit 2
          end;
          iss_bridge := Some Sys.argv.(i + 1);
          go (i + 2)
      | "--iss-debug-dumps" ->
          if i + 2 >= Array.length Sys.argv then begin
            prerr_endline "option --iss-debug-dumps expects two file paths";
            prerr_endline (usage Sys.argv.(0));
            exit 2
          end;
          iss_dumps := Some (Sys.argv.(i + 1), Sys.argv.(i + 2));
          go (i + 3)
      | "--help" | "-h" ->
          print_string (usage Sys.argv.(0));
          exit 0
      | s when String.length s > 0 && s.[0] = '-' ->
          prerr_endline ("unknown option: " ^ s);
          prerr_endline (usage Sys.argv.(0));
          exit 2
      | path ->
          files := !files @ [path];
          go (i + 1)
  in
  go 1;
  let mode =
    match !iss_bridge, !iss_dumps, !files with
    | Some bridge, None, [] -> Iss_bridge_mode bridge
    | None, Some (before_file, after_file), [] ->
        Iss_dump_mode (before_file, after_file)
    | None, None, [before_path; after_path] ->
        Pair_mode (before_path, after_path)
    | None, None, [before_path; mid_path; after_path] ->
        Phase_mode (before_path, mid_path, after_path)
    | None, None, [before_path; mid_path; posttile_path; after_path] ->
        Diamond_phase_mode (before_path, mid_path, posttile_path, after_path)
    | _ ->
        prerr_endline (usage Sys.argv.(0));
        exit 2
  in
  (!kind, !second_level, mode)

let run_pair kind second_level before_path after_path =
  match kind with
  | Kind_affine ->
      print_affine_relation before_path after_path
  | Kind_tiling ->
      print_tiling_result ~second_level before_path after_path
  | Kind_auto ->
      let (ok1, res1, ok2, res2) = affine_relation before_path after_path in
      if (ok1 && res1) || (ok2 && res2) then
        print_affine_relation before_path after_path
      else
        print_tiling_result ~second_level before_path after_path

let run_phase kind second_level before_path mid_path after_path =
  match kind with
  | Kind_affine ->
      let (ok, res) = affine_forward before_path mid_path in
      if ok && res then begin
        Printf.printf "[AFFINE-OK] %s validates %s as an affine refinement.\n"
          mid_path before_path;
        true
      end else begin
        Printf.printf "[AFFINE-FAIL] %s does not validate %s as an affine refinement.\n"
          mid_path before_path;
        false
      end
  | Kind_tiling ->
      print_tiling_result ~second_level mid_path after_path
  | Kind_auto ->
      let (ok_affine, res_affine) = affine_forward before_path mid_path in
      let (ok_tiling, res_tiling, tiling_route) =
        run_tiling_pair ~second_level mid_path after_path
      in
      Printf.printf "[PHASE] affine(before, mid): %s\n"
        (if ok_affine && res_affine then "OK" else "FAIL");
      Printf.printf "[PHASE] tiling(mid, after): %s route=%s\n"
        (if ok_tiling && res_tiling then "OK" else "FAIL") tiling_route;
      if ok_affine && res_affine && ok_tiling && res_tiling then begin
        Printf.printf
          "[OK] Phase-aligned validation succeeded for (%s -> %s -> %s).\n"
          before_path mid_path after_path;
        true
      end else begin
        Printf.printf
          "[FAIL] Phase-aligned validation failed for (%s -> %s -> %s).\n"
          before_path mid_path after_path;
        false
      end

let run_diamond_phase kind second_level before_path mid_path posttile_path after_path =
  match kind with
  | Kind_affine ->
      let (ok_affine1, res_affine1) = affine_forward before_path mid_path in
      let (ok_affine2, res_affine2) = affine_forward posttile_path after_path in
      Printf.printf "[PHASE] affine(before, mid): %s\n"
        (if ok_affine1 && res_affine1 then "OK" else "FAIL");
      Printf.printf "[PHASE] affine(posttile, after): %s\n"
        (if ok_affine2 && res_affine2 then "OK" else "FAIL");
      if ok_affine1 && res_affine1 && ok_affine2 && res_affine2 then begin
        Printf.printf
          "[OK] Diamond affine validation succeeded for (%s -> %s -> %s -> %s).\n"
          before_path mid_path posttile_path after_path;
        true
      end else begin
        Printf.printf
          "[FAIL] Diamond affine validation failed for (%s -> %s -> %s -> %s).\n"
          before_path mid_path posttile_path after_path;
        false
      end
  | Kind_tiling ->
      let (ok_tiling, res_tiling, tiling_route) =
        run_tiling_pair ~second_level mid_path posttile_path
      in
      Printf.printf "[PHASE] tiling(mid, posttile): %s route=%s\n"
        (if ok_tiling && res_tiling then "OK" else "FAIL") tiling_route;
      if ok_tiling && res_tiling then begin
        Printf.printf
          "[OK] Diamond tiling validation succeeded for (%s -> %s).\n"
          mid_path posttile_path;
        true
      end else begin
        Printf.printf
          "[FAIL] Diamond tiling validation failed for (%s -> %s).\n"
          mid_path posttile_path;
        false
      end
  | Kind_auto ->
      let (ok_affine1, res_affine1) = affine_forward before_path mid_path in
      let (ok_tiling, res_tiling, tiling_route) =
        run_tiling_pair ~second_level mid_path posttile_path
      in
      let (ok_affine2, res_affine2) = affine_forward posttile_path after_path in
      Printf.printf "[PHASE] affine(before, mid): %s\n"
        (if ok_affine1 && res_affine1 then "OK" else "FAIL");
      Printf.printf "[PHASE] tiling(mid, posttile): %s route=%s\n"
        (if ok_tiling && res_tiling then "OK" else "FAIL") tiling_route;
      Printf.printf "[PHASE] affine(posttile, after): %s\n"
        (if ok_affine2 && res_affine2 then "OK" else "FAIL");
      if ok_affine1 && res_affine1 && ok_tiling && res_tiling && ok_affine2 && res_affine2 then begin
        Printf.printf
          "[OK] Diamond phase-aligned validation succeeded for (%s -> %s -> %s -> %s).\n"
          before_path mid_path posttile_path after_path;
        true
      end else begin
        Printf.printf
          "[FAIL] Diamond phase-aligned validation failed for (%s -> %s -> %s -> %s).\n"
          before_path mid_path posttile_path after_path;
        false
      end

let _ =
  try
    Gc.set
      {
        (Gc.get ()) with
        Gc.minor_heap_size = 524288;
        Gc.major_heap_increment = 4194304;
      };
    let (kind, second_level, mode) = parse_args () in
    begin
      match mode with
      | Iss_bridge_mode _ | Iss_dump_mode _ when second_level ->
          prerr_endline "--second-level-tile only applies to tiling validation modes";
          prerr_endline (usage Sys.argv.(0));
          exit 2
      | _ -> ()
    end;
    if second_level && kind = Kind_affine then begin
      prerr_endline "--second-level-tile cannot be combined with --kind affine";
      prerr_endline (usage Sys.argv.(0));
      exit 2
    end;
    let success =
      match mode with
      | Iss_bridge_mode bridge ->
          exit (run_iss_bridge bridge)
      | Iss_dump_mode (before_file, after_file) ->
          exit (run_iss_dumps before_file after_file)
      | Pair_mode (before_path, after_path) ->
          run_pair kind second_level before_path after_path
      | Phase_mode (before_path, mid_path, after_path) ->
          run_phase kind second_level before_path mid_path after_path
      | Diamond_phase_mode (before_path, mid_path, posttile_path, after_path) ->
          run_diamond_phase kind second_level before_path mid_path posttile_path after_path
    in
    if not success then exit 1
  with
  | Invalid_argument msg ->
      error no_loc "%s" msg;
      exit 2
  | Failure msg ->
      error no_loc "%s" msg;
      exit 2
  | PlutoTilingValidator.ValidationError msg ->
      error no_loc "%s" msg;
      exit 2
  | CertcheckerConfig.CertCheckerFailure (_, msg) ->
      error no_loc "validation failed inside extracted runtime: %s" msg;
      exit 2
  | Sys_error msg ->
      error no_loc "%s" msg;
      exit 2
  | e -> crash e

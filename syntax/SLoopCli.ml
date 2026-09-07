type config = SLoopConfig.config = {
  mutable dump_input : bool;
  mutable dump_extracted_openscop : bool;
  mutable dump_scheduled_openscop : bool;
  mutable debug_scheduler : bool;
  mutable extract_only : bool;
  mutable extract_strengthened_only : bool;
  mutable profile_stages : bool;
  mutable force_identity : bool;
  mutable force_notile : bool;
  mutable force_iss : bool;
  mutable force_second_level_tile : bool;
  mutable force_diamond_tile : bool;
  mutable force_full_diamond_tile : bool;
  mutable force_band_tiling_experiment : bool;
  mutable force_legacy_generic_tiling : bool;
  mutable force_const_unroll : bool;
  mutable force_parallel : bool;
  mutable force_parallel_strict : bool;
  mutable force_multipar : bool;
  mutable parallel_current_dim : int option;
  mutable force_vector : bool;
  mutable force_vector_strict : bool;
  mutable vector_current_dim : int option;
  mutable pluto_compat_mode : bool;
  mutable pluto_compat_explain : bool;
  mutable pluto_compat_dry_run : bool;
  mutable pluto_tile_seen : bool;
  mutable pluto_notile_seen : bool;
  mutable pluto_diamond_seen : bool;
  mutable pluto_nodiamond_seen : bool;
  mutable pluto_parallel_seen : bool;
  mutable pluto_no_parallel_seen : bool;
  mutable pluto_isldep_seen : bool;
  mutable pluto_candldep_seen : bool;
  mutable pluto_intratileopt_seen : bool;
  mutable pluto_no_intratileopt_seen : bool;
  mutable pluto_prevector_seen : bool;
  mutable pluto_no_prevector_seen : bool;
  mutable pluto_unrolljam_seen : bool;
  mutable pluto_no_unrolljam_seen : bool;
  mutable pluto_extra_flags : string list;
  mutable pluto_control_files : (string * string) list;
  mutable pluto_compat_notes : string list;
  mutable validate_affine_openscop : (string * string) option;
  mutable extract_tiling_witness_openscop : (string * string) option;
  mutable validate_tiling_openscop : (string * string) option;
  mutable validate_iss_debug_dumps : (string * string) option;
  mutable validate_iss_bridge : string option;
  mutable validate_iss_pluto_suite : bool;
  mutable validate_iss_pluto_live_suite : bool;
  mutable input : string option;
}

let usage prog =
  String.concat ""
    [
      Printf.sprintf
        "Usage: %s [--dump-input] [--dump-extracted-openscop] [--dump-scheduled-openscop] [--debug-scheduler] [--extract-only|--extract-strengthened-only] [--profile-stages] [--identity] [--identity-tiled] [--notile] [--iss] [--second-level-tile] [--diamond-tile] [--full-diamond-tile] [--intratileopt|--nointratileopt] [--rar] [--const-unroll] [--parallel] [--parallel-strict] [--parallel-current <dim>] [--vector] [--vector-strict] [--vector-current <dim>] <file.loop>\n"
        prog;
      Printf.sprintf
        "       %s --pluto-compat [--explain] [--dry-run] <Pluto-like optimizer flags> <file.loop>\n"
        prog;
      Printf.sprintf
        "       %s --validate-affine-openscop <before.scop> <after.scop>\n"
        prog;
      "         checks schedule refinement under supplied domains and trusted access summaries;\n";
      "         it does not check OpenScop statement bodies against those summaries\n";
      Printf.sprintf
        "       %s [--second-level-tile] --extract-tiling-witness-openscop <before.scop> <after.scop>\n"
        prog;
      Printf.sprintf
        "       %s [--second-level-tile] --validate-tiling-openscop <before.scop> <after.scop>\n"
        prog;
      Printf.sprintf "       %s --validate-iss-debug-dumps <before.txt> <after.txt>\n" prog;
      Printf.sprintf "       %s --validate-iss-bridge <bridge.txt>\n" prog;
      Printf.sprintf "       %s --validate-iss-pluto-suite\n" prog;
      Printf.sprintf "       %s --validate-iss-pluto-live-suite\n" prog;
      "\nDefault optimization path:\n";
      "  extracted theorem-aligned affine+tiling pipeline with band-aware ordinary tiling (`SBandTilingOpt.opt`)\n";
      "\nExplicit phase controls:\n";
      "  --extract-strengthened-only : export the strengthened source OpenScop, without invoking Pluto\n";
      "  --profile-stages  : print OCaml-side stage timings for the default no-parallel\n";
      "                      theorem-aligned routes (`--identity`, `--notile`, or default)\n";
      "  --identity        : no Pluto phase, just checked extraction/strengthen/codegen\n";
      "  --identity-tiled  : native theorem-facing identity schedule plus checked Pluto\n";
      "                      tile-only route; can compose with --parallel-current\n";
      "  --notile          : stop after affine scheduling validation\n";
      "  --iss             : switch to the extracted theorem-aligned ISS+affine+tiling pipeline\n";
      "                       (`SBandTilingOpt.opt_with_iss`); identity+ISS requires --tile\n";
      "  --second-level-tile : checked nested tiling producer for tiled optimization routes\n";
      "                        and tiling witness/validation actions\n";
      "  --diamond-tile    : checked diamond midpoint + tiling route; composes with ISS,\n";
      "                      second-level tiling, and checked parallel/vector consumers\n";
      "  --full-diamond-tile : stronger diamond producer mode over the same checked route;\n";
      "                        supported on non-ISS/ISS and ordinary/second-level tiled paths\n";
      "  --intratileopt    : let Pluto reorder loops within each tile; validate tiling\n";
      "                       and the final affine rescheduling separately; requires tiling\n";
      "  --nointratileopt  : preserve the preselected intra-tile loop order (default)\n";
      "  --rar             : include Pluto read-after-read relations in the scheduling\n";
      "                      objective (disabled by default); valid on native and\n";
      "                      Pluto-compatible checked routes\n";
      "  --band-tiling-experiment : compatibility alias for the default band-aware\n";
      "                             ordinary tiling route; only valid on the default\n";
      "                             non-ISS full tiled path\n";
      "  --legacy-generic-tiling : deprecated compatibility alias; tiled routes still use\n";
      "                            the direct permutable-band checker and otherwise reject\n";
      "  --const-unroll    : checked post pass that fully unrolls statically constant\n";
      "                       sequential loops; parallel annotations are preserved\n";
      "  --parallel        : experimental verified `parallel for` route driven by Pluto `--parallel`\n";
      "                       loop hints; supported on both the default and `--iss` pipelines,\n";
      "                       with or without `--notile`\n";
      "                       In Pluto-compatible mode, --multipar enables checked\n";
      "                       schedule coordinates when the validator accepts them\n";
      "  --parallel-strict : with `--parallel`, require the certified parallel loop to be the\n";
      "                       Pluto-hinted dimension; reject if that dimension is not certifiable\n";
      "  --parallel-current d : theorem-aligned verified `parallel for` on padded\n";
      "                         schedule coordinate d (legacy option name); supported on identity, affine-only, and full\n";
      "                         tiled paths, including their `--iss` variants and the\n";
      "                         non-ISS and ISS diamond routes\n";
      "  --vector          : experimental checked `vector for` route driven by Pluto\n";
      "                       `--prevector` loop hints; only a certified structurally\n";
      "                       innermost hinted loop is annotated, otherwise the verified\n";
      "                       sequential producer is retained\n";
      "  --vector-strict   : compatibility spelling for explicit hint-only vector intent;\n";
      "                       the current vector route is already innermost-hint-only\n";
      "  --vector-current d : theorem-aligned checked `vector for` on padded schedule\n";
      "                         coordinate d (legacy option name), requiring doall and innermost checks\n";
      "  --pluto-compat    : parse Pluto-style optimizer flags in this OCaml driver,\n";
      "                      reject unsupported Pluto defaults/features with explicit\n";
      "                      reasons, then run the matching checked polopt route\n";
      "\nExamples:\n";
      Printf.sprintf "  %s file.loop                        # default theorem-aligned band-aware affine+tiling path\n" prog;
      Printf.sprintf "  %s --profile-stages file.loop       # print per-stage timings for the default route\n" prog;
      Printf.sprintf "  %s --second-level-tile file.loop    # full tiled checked path with second-level tiling enabled\n" prog;
      Printf.sprintf "  %s --diamond-tile file.loop         # sequential checked diamond midpoint + tiling route\n" prog;
      Printf.sprintf "  %s --iss --diamond-tile file.loop   # ISS split plus checked diamond route\n" prog;
      Printf.sprintf "  %s --full-diamond-tile file.loop    # stronger diamond producer mode over the same checked route\n" prog;
      Printf.sprintf "  %s --intratileopt file.loop         # checked tiling plus intra-tile loop reordering\n" prog;
      Printf.sprintf "  %s --parallel file.loop             # Pluto-hinted verified parallel path\n" prog;
      Printf.sprintf "  %s --parallel --parallel-strict file.loop\n" prog;
      Printf.sprintf "  %s --parallel-current 0 file.loop   # theorem-aligned explicit schedule-coordinate parallel path\n" prog;
      Printf.sprintf "  %s --vector-current 0 file.loop     # theorem-aligned explicit schedule-coordinate vector path\n" prog;
      Printf.sprintf "  %s --diamond-tile --parallel-current 0 file.loop\n" prog;
      Printf.sprintf "  %s --iss --parallel-current 0 file.loop\n" prog;
      Printf.sprintf "  %s --notile file.loop               # affine-only checked path\n" prog;
      Printf.sprintf "  %s --identity file.loop             # identity/no-schedule path\n" prog;
      Printf.sprintf "  %s --identity-tiled --parallel-current 1 file.loop\n" prog;
      Printf.sprintf "  %s --validate-affine-openscop before.scop mid.scop\n" prog;
      Printf.sprintf "  %s --validate-tiling-openscop mid.scop after.scop\n" prog;
      Printf.sprintf "  %s --second-level-tile --validate-tiling-openscop mid.scop after.scop\n" prog;
      Printf.sprintf "  %s --identity --tile --iss file.loop # checked ISS plus identity-tiling path\n" prog;
      Printf.sprintf "  %s --pluto-compat --tile --smartfuse --nointratileopt --prevector --nounrolljam --rar --nodiamond-tile --noparallel file.loop\n" prog;
    ]

let usage_error prog msg =
  prerr_endline msg;
  prerr_endline (usage prog);
  exit 2

let pluto_reject prog msg =
  ignore prog;
  prerr_endline ("[pluto-compat] reject: " ^ msg);
  exit 2

let enable_pluto_compat cfg =
  cfg.pluto_compat_mode <- true

let add_pluto_note cfg msg =
  cfg.pluto_compat_notes <- cfg.pluto_compat_notes @ [msg]

let add_pluto_extra_flag cfg flag =
  cfg.pluto_extra_flags <- cfg.pluto_extra_flags @ [flag]

let add_pluto_control_file prog cfg target path note =
  enable_pluto_compat cfg;
  if not (Sys.file_exists path) then
    pluto_reject prog (Printf.sprintf "%s: no such file" path);
  cfg.pluto_control_files <- cfg.pluto_control_files @ [(target, path)];
  add_pluto_note cfg note

let starts_with s prefix =
  let len_s = String.length s in
  let len_p = String.length prefix in
  len_s >= len_p && String.sub s 0 len_p = prefix

let contains s needle =
  try
    ignore (Str.search_forward (Str.regexp_string needle) s 0);
    true
  with Not_found -> false

let pluto_executable_for_probe () =
  match Sys.getenv_opt "POLCERT_PLUTO" with
  | Some path when String.trim path <> "" -> path
  | _ ->
      let container_pluto = "/pluto/tool/pluto" in
      if Sys.file_exists container_pluto then
        container_pluto
      else
        "pluto"

let pluto_help_cache = ref None

let pluto_help_text () =
  match !pluto_help_cache with
  | Some text -> text
  | None ->
      let cmd = Filename.quote (pluto_executable_for_probe ()) ^ " --help 2>&1" in
      let ic = Unix.open_process_in cmd in
      let buf = Buffer.create 4096 in
      begin
        try
          while true do
            Buffer.add_string buf (input_line ic);
            Buffer.add_char buf '\n'
          done
        with End_of_file -> ()
      end;
      ignore (Unix.close_process_in ic);
      let text = Buffer.contents buf in
      pluto_help_cache := Some text;
      text

let pluto_supports_option flag =
  contains (pluto_help_text ()) flag

let pluto_has_lp_solver_support () =
  pluto_supports_option "--glpk" || pluto_supports_option "--gurobi"

let pluto_candldep_probe_cache = ref None

let pluto_has_working_candldep () =
  match !pluto_candldep_probe_cache with
  | Some ok -> ok
  | None ->
      let src = Filename.temp_file "polcert-candldep-probe" ".c" in
      let out = Filename.temp_file "polcert-candldep-probe-out" ".c" in
      let oc = open_out src in
      output_string oc
        "void candl_probe(int N, int A[]) {\n\
         int i;\n\
         #pragma scop\n\
         for (i = 1; i < N; i++) {\n\
           A[i] = A[i - 1] + 1;\n\
         }\n\
         #pragma endscop\n\
         }\n";
      close_out oc;
      let cmd =
        String.concat " "
          [
            Filename.quote (pluto_executable_for_probe ());
            "--candldep --notile --noprevector --nounrolljam --nodiamond-tile --noparallel";
            "-o";
            Filename.quote out;
            Filename.quote src;
            ">/dev/null 2>/dev/null";
          ]
      in
      let ok = Sys.command cmd = 0 in
      begin try Sys.remove src with Sys_error _ -> () end;
      begin try Sys.remove out with Sys_error _ -> () end;
      pluto_candldep_probe_cache := Some ok;
      ok

let split_eq_flag s =
  match String.index_opt s '=' with
  | None -> None
  | Some idx ->
      Some
        (String.sub s 0 idx,
         String.sub s (idx + 1) (String.length s - idx - 1))

let value_options = [
  "--cache-size";
  "--cloogf";
  "--cloogl";
  "--codegen-context";
  "--coeff-bound";
  "--data-element-size";
  "--ft";
  "--lt";
  "--ufactor";
  "-o";
]

let output_value_options = [
  "--cloogf";
  "--cloogl";
  "--codegen-context";
  "-o";
]

let tile_size_value_options = [
  "--cache-size";
  "--data-element-size";
  "--ufactor";
]

let tile_size_value_prefixes =
  List.map (fun flag -> flag ^ "=") tile_size_value_options

let positive_oracle_value_options = [
  "--cache-size";
  "--coeff-bound";
  "--data-element-size";
  "--ufactor";
]

let nonnegative_oracle_value_options = [
  "--forceparallel";
  "--ft";
  "--lt";
]

let known_rejection_reason = function
  | "--pet" -> Some "frontend is polopt's verified loop extractor, not Pluto/PET"
  | "--readscop" -> Some "frontend is polopt's verified loop extractor, not Pluto OpenScop input"
  | "--dumpscop" -> Some "Pluto OpenScop dumps are an oracle-debug interface, not a polopt input/output mode"
  | "--version" -> Some "CLI version reporting is outside the optimizer-compatibility surface"
  | "--bee" -> Some "Bee pragmas are Pluto codegen output, while polopt uses its own codegen"
  | "--cloogsh" -> Some "Cloog codegen tuning is outside the polopt checked route"
  | "--indent" -> Some "formatting is outside the optimizer-validation route"
  | "--dump-iss-bridge" -> Some "this flag is not accepted by the current Pluto binary"
  | "--lbtile" -> Some "this flag appears in stale scripts but is not accepted by the current Pluto binary"
  | "--multipipe" -> Some "this flag appears in stale scripts but is not accepted by the current Pluto binary"
  | "--output" -> Some "the current Pluto binary uses -o, not --output"
  | "--sched" -> Some "this flag appears in stale scripts but is not accepted by the current Pluto binary"
  | "--variables_not_global" -> Some "this flag appears in stale scripts but is not accepted by the current Pluto binary"
  | _ -> None

let reject_value_option prog flag value =
  if List.mem flag output_value_options then
    pluto_reject prog (flag ^ ": output/codegen shaping is outside the polopt checked route")
  else
    pluto_reject prog (Printf.sprintf "%s: value %S is not exposed through the checked polopt route" flag value)

let parse_positive_int_value prog flag value =
  try
    let n = int_of_string value in
    if n <= 0 then
      pluto_reject prog (flag ^ ": value must be a positive integer");
    value
  with Failure _ ->
    pluto_reject prog (flag ^ ": value must be a positive integer")

let parse_nonnegative_int_value prog flag value =
  try
    let n = int_of_string value in
    if n < 0 then
      pluto_reject prog (flag ^ ": value must be a non-negative integer");
    value
  with Failure _ ->
    pluto_reject prog (flag ^ ": value must be a non-negative integer")

let add_pluto_value_flag prog cfg flag value =
  let value = parse_positive_int_value prog flag value in
  add_pluto_extra_flag cfg (flag ^ "=" ^ value);
  if String.equal flag "--ufactor" then
    add_pluto_note cfg
      (flag ^ "=" ^ value
       ^ " accepted as Pluto's unroll/tile factor; it is passed to the scheduler oracle only with --determine-tile-size")
  else
    add_pluto_note cfg (flag ^ "=" ^ value ^ " passed through to Pluto's checked scheduler oracle")

let add_pluto_nonnegative_value_flag prog cfg flag value =
  let value = parse_nonnegative_int_value prog flag value in
  add_pluto_extra_flag cfg (flag ^ "=" ^ value);
  add_pluto_note cfg (flag ^ "=" ^ value ^ " passed through to Pluto's checked scheduler oracle")

let add_lp_solver_flag prog cfg flag =
  if not (pluto_supports_option flag) then
    pluto_reject prog (flag ^ ": current Pluto binary does not advertise this LP/DFP option");
  if
    List.mem flag ["--typedfuse"; "--hybridfuse"; "--delayedcut"]
    && not (pluto_has_lp_solver_support ())
  then
    pluto_reject prog (flag ^ ": requires a GLPK- or Gurobi-enabled Pluto binary");
  add_pluto_extra_flag cfg flag;
  add_pluto_note cfg (flag ^ " passed through to Pluto's checked scheduler oracle")

let pluto_extra_has flag cfg =
  List.exists (String.equal flag) cfg.pluto_extra_flags

let pluto_extra_has_prefix prefix cfg =
  List.exists (fun flag -> starts_with flag prefix) cfg.pluto_extra_flags

let pluto_extra_has_any_prefix prefixes cfg =
  List.exists (fun prefix -> pluto_extra_has_prefix prefix cfg) prefixes

let pluto_ufactor_prefix = "--ufactor="

let pluto_scheduler_extra_flags cfg =
  if cfg.pluto_unrolljam_seen
     && not (pluto_extra_has "--determine-tile-size" cfg)
  then
    List.filter
      (fun flag -> not (starts_with flag pluto_ufactor_prefix))
      cfg.pluto_extra_flags
  else
    cfg.pluto_extra_flags

let rec find_map f = function
  | [] -> None
  | x :: xs ->
      begin match f x with
      | None -> find_map f xs
      | some -> some
      end

let pluto_extra_value prefix cfg =
  find_map
    (fun flag ->
       if starts_with flag prefix then
         Some (String.sub flag (String.length prefix) (String.length flag - String.length prefix))
       else
         None)
    cfg.pluto_extra_flags

let pluto_polopt_args cfg =
  let args = ref [] in
  if cfg.force_iss then args := !args @ ["--iss"];
  if cfg.force_identity then
    begin
      args := !args @ (if cfg.pluto_tile_seen then ["--identity"; "--tile"] else ["--identity"]);
      if cfg.force_second_level_tile then args := !args @ ["--second-level-tile"]
    end
  else begin
    if cfg.force_notile then args := !args @ ["--notile"];
    if cfg.force_second_level_tile then args := !args @ ["--second-level-tile"];
    if cfg.force_full_diamond_tile then args := !args @ ["--full-diamond-tile"]
    else if cfg.force_diamond_tile then args := !args @ ["--diamond-tile"]
  end;
  if cfg.force_parallel then args := !args @ ["--parallel"];
  if cfg.force_parallel_strict then args := !args @ ["--parallel-strict"];
  if cfg.force_vector then args := !args @ ["--vector"];
  if cfg.force_vector_strict then args := !args @ ["--vector-strict"];
  if cfg.force_const_unroll then args := !args @ ["--const-unroll"];
  if cfg.pluto_unrolljam_seen then args := !args @ ["--unrolljam"];
  !args

let print_pluto_explain cfg =
  let args = pluto_polopt_args cfg in
  let scheduler_flags =
    pluto_scheduler_extra_flags cfg
    @ if cfg.pluto_intratileopt_seen then ["--intratileopt"] else []
  in
  let post_flags =
    if cfg.pluto_unrolljam_seen
       && not (pluto_extra_has "--determine-tile-size" cfg)
    then
      List.filter (fun flag -> starts_with flag pluto_ufactor_prefix) cfg.pluto_extra_flags
    else
      []
  in
  print_endline "[pluto-compat] accepted";
  print_endline
    ("[pluto-compat] polopt args: "
     ^ (match args with [] -> "<default>" | _ -> String.concat " " args));
  if scheduler_flags <> [] then
    print_endline
      ("[pluto-compat] pluto oracle flags: "
       ^ String.concat " " scheduler_flags);
  if post_flags <> [] then
    print_endline
      ("[pluto-compat] checked post flags: "
       ^ String.concat " " post_flags);
  if cfg.pluto_control_files <> [] then
    print_endline
      ("[pluto-compat] pluto control files: "
       ^ String.concat " "
           (List.map
              (fun (target, source) -> target ^ "<=" ^ source)
              cfg.pluto_control_files));
  List.iter
    (fun note -> print_endline ("[pluto-compat] note: " ^ note))
    cfg.pluto_compat_notes

let validate_pluto_compat prog cfg =
  if cfg.pluto_compat_mode then begin
    if cfg.pluto_tile_seen && cfg.pluto_notile_seen then
      pluto_reject prog "--tile and --notile are both present; this driver rejects contradictory phase controls";
    if cfg.parallel_current_dim <> None then
      pluto_reject prog "--parallel-current: not a Pluto flag; use native polopt mode for explicit schedule-coordinate parallel certification";
    if cfg.vector_current_dim <> None then
      pluto_reject prog "--vector-current: not a Pluto flag; use native polopt mode for explicit schedule-coordinate vector certification";
    if cfg.pluto_parallel_seen && cfg.pluto_no_parallel_seen then
      pluto_reject prog "--parallel and --noparallel are both present; this driver rejects contradictory phase controls";
    if cfg.pluto_diamond_seen && cfg.pluto_nodiamond_seen then
      pluto_reject prog "--diamond-tile/--full-diamond-tile and --nodiamond-tile are both present; this driver rejects contradictory phase controls";
    if cfg.pluto_intratileopt_seen && cfg.pluto_no_intratileopt_seen then
      pluto_reject prog "--intratileopt and --nointratileopt are both present; this driver rejects contradictory tile-schedule controls";
    if cfg.pluto_prevector_seen && cfg.pluto_no_prevector_seen then
      pluto_reject prog "--prevector and --noprevector are both present; this driver rejects contradictory vector controls";
    if cfg.pluto_unrolljam_seen && cfg.pluto_no_unrolljam_seen then
      pluto_reject prog "--unrolljam and --nounrolljam are both present; this driver rejects contradictory unroll controls";
    if (pluto_extra_has "--lastwriter" cfg) && (pluto_extra_has "--nolastwriter" cfg) then
      pluto_reject prog "--lastwriter and --nolastwriter are both present; this driver rejects contradictory dependence controls";
    if cfg.pluto_isldep_seen && cfg.pluto_candldep_seen then
      pluto_reject prog "--isldep and --candldep are both present; Pluto accepts only one dependence tester";
    if (pluto_extra_has "--scalpriv" cfg) && not cfg.pluto_candldep_seen then
      pluto_reject prog "--scalpriv requires --candldep in the checked polopt subset";
    if (pluto_extra_has "--lastwriter" cfg) && cfg.pluto_candldep_seen then
      pluto_reject prog "--lastwriter is only supported with Pluto's ISL dependence tester, not --candldep";
    if not (cfg.pluto_intratileopt_seen || cfg.pluto_no_intratileopt_seen) then
      pluto_reject prog "Pluto enables --intratileopt by default; pass --nointratileopt or --intratileopt explicitly";
    if not cfg.pluto_no_prevector_seen then begin
      cfg.force_vector <- true;
      add_pluto_note cfg
        "Pluto --prevector consumes only a mapped innermost hint and checks both doall and structural innermostness"
    end;
    if not (cfg.pluto_no_unrolljam_seen || cfg.pluto_unrolljam_seen) then
      pluto_reject prog "Pluto enables --unrolljam by default; pass --nounrolljam or explicit --unrolljam";
    if (not cfg.force_parallel) && not cfg.pluto_no_parallel_seen then
      pluto_reject prog "Pluto enables --parallel by default; pass --noparallel or --parallel explicitly";
    if cfg.force_vector && cfg.force_parallel then
      pluto_reject prog "--prevector/--vector cannot be combined with --parallel in the current checked annotation surface";
    if cfg.pluto_unrolljam_seen
       && (cfg.force_vector || cfg.vector_current_dim <> None)
    then
      pluto_reject prog
        "--unrolljam cannot currently be combined with vector execution; parallel combinations revalidate annotations after the checked Loop postpass";
    if cfg.force_const_unroll
       && not cfg.pluto_unrolljam_seen
       && (cfg.force_vector || cfg.vector_current_dim <> None)
    then
      pluto_reject prog
        "--const-unroll cannot currently be combined with vector execution; parallel output preserves its annotations and unfolds only sequential loops";
    if (not cfg.force_diamond_tile) && not cfg.pluto_nodiamond_seen then
      pluto_reject prog "Pluto enables --diamond-tile by default; pass --nodiamond-tile or --diamond-tile explicitly";
    if cfg.force_identity && cfg.force_parallel && not cfg.pluto_tile_seen then
      pluto_reject prog "--parallel with --identity requires --tile so the checked identity-tiling route has a Pluto loop hint";
    if cfg.force_identity && cfg.force_vector && not cfg.pluto_tile_seen then
      pluto_reject prog "--prevector with --identity requires --tile so the checked identity-tiling route has a Pluto loop hint";
    if cfg.force_identity && cfg.force_second_level_tile && not cfg.pluto_tile_seen then
      pluto_reject prog "--second-level-tile with --identity requires --tile";
    if cfg.force_identity && cfg.force_diamond_tile then
      pluto_reject prog "--diamond-tile requires a Pluto tiling phase and cannot be combined with --identity";
    if cfg.force_identity && cfg.pluto_tile_seen then
      add_pluto_note cfg
        (if cfg.force_iss && cfg.force_second_level_tile then
           "--identity --tile --iss --second-level-tile uses the checked ISS plus direct permutable-band identity-tiling route"
         else if cfg.force_second_level_tile then
           "--identity --tile --second-level-tile uses the checked direct permutable-band identity-tiling route"
         else if cfg.force_iss then
           "--identity --tile --iss uses the checked ISS plus identity-tiling route"
         else
           "--identity --tile uses the checked identity-tiling route");
    if cfg.force_identity && (not cfg.pluto_notile_seen) && (not cfg.pluto_tile_seen) then
      pluto_reject prog "--identity: current Pluto keeps tiling enabled by default; use --identity --notile for polopt's no-tiling identity route";
    if cfg.force_second_level_tile && cfg.force_notile then
      pluto_reject prog "--second-level-tile requires tiling and cannot be combined with --notile";
    if cfg.force_second_level_tile && cfg.force_identity && not cfg.pluto_tile_seen then
      pluto_reject prog "--second-level-tile with --identity requires --tile";
    let has_cache_or_data_size =
      pluto_extra_has_prefix "--cache-size=" cfg
      || pluto_extra_has_prefix "--data-element-size=" cfg
    in
    let has_ufactor = pluto_extra_has_prefix pluto_ufactor_prefix cfg in
    let has_determine_tile_size = pluto_extra_has "--determine-tile-size" cfg in
    if has_cache_or_data_size && not has_determine_tile_size then
      pluto_reject prog "--cache-size/--data-element-size require --determine-tile-size in the checked polopt subset";
    if has_ufactor && not has_determine_tile_size
       && not cfg.pluto_unrolljam_seen
    then
      pluto_reject prog "--ufactor without --determine-tile-size requires --unrolljam in the checked polopt subset";
    if
      (has_cache_or_data_size || (has_ufactor && has_determine_tile_size))
      && (cfg.force_notile || cfg.force_identity)
    then
      pluto_reject prog "--cache-size/--data-element-size/--ufactor require a tiled route when used for Pluto tile-size modeling";
    if has_ufactor && not has_determine_tile_size && cfg.pluto_unrolljam_seen then
      add_pluto_note cfg
        "--ufactor is not passed to Pluto's scheduler oracle here; --unrolljam uses proved block unrolling followed by locally validated jam attempts";
    if
      (pluto_extra_has_prefix "--ft=" cfg)
      <> (pluto_extra_has_prefix "--lt=" cfg)
    then
      pluto_reject prog "--ft and --lt must be supplied together in the checked polopt subset";
    begin match pluto_extra_value "--ft=" cfg, pluto_extra_value "--lt=" cfg with
    | Some ft, Some lt ->
        let ft = int_of_string ft in
        let lt = int_of_string lt in
        if ft > lt then
          pluto_reject prog "--ft must be less than or equal to --lt";
        if cfg.force_notile || cfg.force_identity then
          pluto_reject prog "--ft/--lt require a tiled route in the checked polopt subset"
    | _ -> ()
    end;
    if cfg.force_diamond_tile then begin
      if cfg.force_notile then
        pluto_reject prog "--diamond-tile requires tiling and cannot be combined with --notile";
      if cfg.force_identity then
        pluto_reject prog "--diamond-tile requires a Pluto tiling phase and cannot be combined with --identity";
      ()
    end
  end

let parse_args () : config =
  let cfg : config =
    {
      dump_input = false;
      dump_extracted_openscop = false;
      dump_scheduled_openscop = false;
      debug_scheduler = false;
      extract_only = false;
      extract_strengthened_only = false;
      profile_stages = false;
      force_identity = false;
      force_notile = false;
      force_iss = false;
      force_second_level_tile = false;
      force_diamond_tile = false;
      force_full_diamond_tile = false;
      force_band_tiling_experiment = false;
      force_legacy_generic_tiling = false;
      force_const_unroll = false;
      force_parallel = false;
      force_parallel_strict = false;
      force_multipar = false;
      parallel_current_dim = None;
      force_vector = false;
      force_vector_strict = false;
      vector_current_dim = None;
      pluto_compat_mode = false;
      pluto_compat_explain = false;
      pluto_compat_dry_run = false;
      pluto_tile_seen = false;
      pluto_notile_seen = false;
      pluto_diamond_seen = false;
      pluto_nodiamond_seen = false;
      pluto_parallel_seen = false;
      pluto_no_parallel_seen = false;
      pluto_isldep_seen = false;
      pluto_candldep_seen = false;
      pluto_intratileopt_seen = false;
      pluto_no_intratileopt_seen = false;
      pluto_prevector_seen = false;
      pluto_no_prevector_seen = false;
      pluto_unrolljam_seen = false;
      pluto_no_unrolljam_seen = false;
      pluto_extra_flags = [];
      pluto_control_files = [];
      pluto_compat_notes = [];
      validate_affine_openscop = None;
      extract_tiling_witness_openscop = None;
      validate_tiling_openscop = None;
      validate_iss_debug_dumps = None;
      validate_iss_bridge = None;
      validate_iss_pluto_suite = false;
      validate_iss_pluto_live_suite = false;
      input = None;
    }
  in
  let invalid_non_negative_int prog =
    usage_error prog "option --parallel-current expects a non-negative integer"
  in
  let invalid_vector_non_negative_int prog =
    usage_error prog "option --vector-current expects a non-negative integer"
  in
  let rec go i =
    if i >= Array.length Sys.argv then cfg
    else begin
      match Sys.argv.(i) with
      | "--pluto-compat" -> enable_pluto_compat cfg; go (i + 1)
      | "--explain" ->
          enable_pluto_compat cfg;
          cfg.pluto_compat_explain <- true;
          go (i + 1)
      | "--dry-run" ->
          enable_pluto_compat cfg;
          cfg.pluto_compat_dry_run <- true;
          go (i + 1)
      | "--dump-input" -> cfg.dump_input <- true; go (i + 1)
      | "--dump-extracted-openscop" -> cfg.dump_extracted_openscop <- true; go (i + 1)
      | "--dump-scheduled-openscop" -> cfg.dump_scheduled_openscop <- true; go (i + 1)
      | "--debug-scheduler" -> cfg.debug_scheduler <- true; go (i + 1)
      | "--extract-only" ->
          if cfg.extract_strengthened_only then
            usage_error Sys.argv.(0) "choose only one extraction output mode";
          cfg.extract_only <- true; go (i + 1)
      | "--extract-strengthened-only" ->
          if cfg.extract_only && not cfg.extract_strengthened_only then
            usage_error Sys.argv.(0) "choose only one extraction output mode";
          cfg.extract_only <- true;
          cfg.extract_strengthened_only <- true;
          go (i + 1)
      | "--profile-stages" -> cfg.profile_stages <- true; go (i + 1)
      | "--identity" -> cfg.force_identity <- true; go (i + 1)
      | "--identity-tiled" ->
          cfg.force_identity <- true;
          cfg.pluto_tile_seen <- true;
          cfg.force_notile <- false;
          go (i + 1)
      | "--tile" ->
          enable_pluto_compat cfg;
          cfg.pluto_tile_seen <- true;
          cfg.force_notile <- false;
          go (i + 1)
      | "--notile" ->
          cfg.force_notile <- true;
          cfg.pluto_notile_seen <- true;
          go (i + 1)
      | "--affine-only" -> cfg.force_notile <- true; go (i + 1)
      | "--iss" -> cfg.force_iss <- true; go (i + 1)
      | "--second-level-tile" -> cfg.force_second_level_tile <- true; go (i + 1)
      | "--diamond-tile" ->
          cfg.force_diamond_tile <- true;
          cfg.pluto_diamond_seen <- true;
          go (i + 1)
      | "--nodiamond-tile" ->
          enable_pluto_compat cfg;
          cfg.force_diamond_tile <- false;
          cfg.force_full_diamond_tile <- false;
          cfg.pluto_nodiamond_seen <- true;
          go (i + 1)
      | "--full-diamond-tile" ->
          cfg.force_diamond_tile <- true;
          cfg.force_full_diamond_tile <- true;
          cfg.pluto_diamond_seen <- true;
          go (i + 1)
      | "--band-tiling-experiment" -> cfg.force_band_tiling_experiment <- true; go (i + 1)
      | "--legacy-generic-tiling" -> cfg.force_legacy_generic_tiling <- true; go (i + 1)
      | "--const-unroll" ->
          cfg.force_const_unroll <- true;
          go (i + 1)
      | "--parallel" | "--parallelize" ->
          cfg.force_parallel <- true;
          cfg.pluto_parallel_seen <- true;
          go (i + 1)
      | "--multipar" ->
          enable_pluto_compat cfg;
          cfg.force_parallel <- true;
          cfg.force_multipar <- true;
          cfg.pluto_parallel_seen <- true;
          add_pluto_extra_flag cfg "--multipar";
          add_pluto_note cfg "--multipar enables checked parallel dimensions when available";
          go (i + 1)
      | "--noparallel" ->
          enable_pluto_compat cfg;
          cfg.force_parallel <- false;
          cfg.pluto_no_parallel_seen <- true;
          go (i + 1)
      | "--innerpar" ->
          enable_pluto_compat cfg;
          add_pluto_extra_flag cfg "--innerpar";
          add_pluto_note cfg "--innerpar passed to Pluto's checked tile-schedule oracle; the resulting parallel hint is independently certified";
          go (i + 1)
      | "--parallel-strict" -> cfg.force_parallel_strict <- true; go (i + 1)
      | "--vector" | "--vectorize" ->
          cfg.force_vector <- true;
          cfg.pluto_prevector_seen <- true;
          go (i + 1)
      | "--vector-strict" -> cfg.force_vector_strict <- true; go (i + 1)
      | "--tile-sizes-file" ->
          if i + 1 >= Array.length Sys.argv then
            pluto_reject Sys.argv.(0) "--tile-sizes-file requires a file path";
          add_pluto_control_file Sys.argv.(0) cfg "tile.sizes" Sys.argv.(i + 1)
            "--tile-sizes-file installs an explicit Pluto tile.sizes file for the checked oracle run";
          go (i + 2)
      | "--fusion-structure" | "--fst-file" ->
          if i + 1 >= Array.length Sys.argv then
            pluto_reject Sys.argv.(0) (Sys.argv.(i) ^ " requires a file path");
          add_pluto_control_file Sys.argv.(0) cfg ".fst" Sys.argv.(i + 1)
            (Sys.argv.(i) ^ " installs an explicit Pluto .fst file for the checked oracle run");
          go (i + 2)
      | "--precut" | "--precut-file" ->
          if i + 1 >= Array.length Sys.argv then
            pluto_reject Sys.argv.(0) (Sys.argv.(i) ^ " requires a file path");
          add_pluto_control_file Sys.argv.(0) cfg ".precut" Sys.argv.(i + 1)
            (Sys.argv.(i) ^ " installs an explicit Pluto .precut file for the checked oracle run");
          go (i + 2)
      | s when starts_with s "--tile-sizes-file=" ->
          begin match split_eq_flag s with
          | Some (_, path) ->
              add_pluto_control_file Sys.argv.(0) cfg "tile.sizes" path
                "--tile-sizes-file installs an explicit Pluto tile.sizes file for the checked oracle run";
              go (i + 1)
          | None -> assert false
          end
      | s when starts_with s "--fusion-structure=" || starts_with s "--fst-file=" ->
          begin match split_eq_flag s with
          | Some (flag, path) ->
              add_pluto_control_file Sys.argv.(0) cfg ".fst" path
                (flag ^ " installs an explicit Pluto .fst file for the checked oracle run");
              go (i + 1)
          | None -> assert false
          end
      | s when starts_with s "--precut=" || starts_with s "--precut-file=" ->
          begin match split_eq_flag s with
          | Some (flag, path) ->
              add_pluto_control_file Sys.argv.(0) cfg ".precut" path
                (flag ^ " installs an explicit Pluto .precut file for the checked oracle run");
              go (i + 1)
          | None -> assert false
          end
      | "--nointratileopt" ->
          cfg.pluto_no_intratileopt_seen <- true;
          add_pluto_note cfg "--nointratileopt selects the stable intra-tile loop order";
          go (i + 1)
      | "--intratileopt" ->
          cfg.pluto_intratileopt_seen <- true;
          add_pluto_note cfg "--intratileopt selects checked intra-tile loop reordering";
          go (i + 1)
      | "--noprevector" ->
          enable_pluto_compat cfg;
          cfg.pluto_no_prevector_seen <- true;
          add_pluto_note cfg "--noprevector accepted; no checked vector annotation is requested";
          go (i + 1)
      | "--prevector" ->
          enable_pluto_compat cfg;
          cfg.pluto_prevector_seen <- true;
          cfg.force_vector <- true;
          add_pluto_note cfg "--prevector selects the innermost-hint-only checked vector annotation route";
          go (i + 1)
      | "--nounrolljam" ->
          enable_pluto_compat cfg;
          cfg.pluto_no_unrolljam_seen <- true;
          add_pluto_note cfg "--nounrolljam accepted; no checked unroll post pass is requested";
          go (i + 1)
      | "--unrolljam" ->
          enable_pluto_compat cfg;
          cfg.pluto_unrolljam_seen <- true;
          add_pluto_note cfg "--unrolljam selects checked block unrolling, local jam validation, and cleanup; parallel routes obtain a fresh annotation certificate afterward";
          go (i + 1)
      | (("--smartfuse" | "--nofuse" | "--maxfuse" | "--nodepbound"
         | "--per-cc-obj" | "--flic" | "--fast-lin-ind-check"
         | "--determine-tile-size" | "--lastwriter" | "--nolastwriter"
         | "--isldepaccesswise" | "--isldepstmtwise" | "--isldepcoalesce"
         | "--pipsolve") as flag) ->
          enable_pluto_compat cfg;
          add_pluto_extra_flag cfg flag;
          add_pluto_note cfg (flag ^ " passed through to Pluto's checked scheduler oracle");
          go (i + 1)
      | "--candldep" ->
          enable_pluto_compat cfg;
          if not (pluto_has_working_candldep ()) then
            pluto_reject Sys.argv.(0) "--candldep: selected Pluto Candl importer aborts on a dependent probe; requires the Candl dependence-type import fix";
          cfg.pluto_candldep_seen <- true;
          add_pluto_extra_flag cfg "--candldep";
          add_pluto_note cfg "--candldep passed through to Pluto's checked scheduler oracle";
          go (i + 1)
      | "--scalpriv" ->
          enable_pluto_compat cfg;
          if not (pluto_has_working_candldep ()) then
            pluto_reject Sys.argv.(0) "--scalpriv: selected Pluto Candl importer aborts on a dependent probe; requires the Candl dependence-type import fix";
          add_pluto_extra_flag cfg "--scalpriv";
          add_pluto_note cfg "--scalpriv passed through only with --candldep; PolOpt still validates the output schedule under the original scalar storage semantics";
          go (i + 1)
      | (("--glpk" | "--gurobi" | "--lp" | "--dfp" | "--ilp" | "--lpcolor"
         | "--clusterscc" | "--typedfuse" | "--hybridfuse" | "--delayedcut") as flag) ->
          enable_pluto_compat cfg;
          add_lp_solver_flag Sys.argv.(0) cfg flag;
          go (i + 1)
      | "--isldep" ->
          enable_pluto_compat cfg;
          cfg.pluto_isldep_seen <- true;
          add_pluto_note cfg "--isldep accepted as Pluto's default dependence tester for the checked polopt route";
          go (i + 1)
      | "--rar" ->
          add_pluto_extra_flag cfg "--rar";
          add_pluto_note cfg "--rar passed through to Pluto's checked scheduler oracle";
          go (i + 1)
      | (("--debug" | "--moredebug" | "--silent") as flag) ->
          enable_pluto_compat cfg;
          add_pluto_note cfg (flag ^ " accepted as a logging-only no-op for the checked polopt route");
          go (i + 1)
      | "--nocloogbacktrack" ->
          enable_pluto_compat cfg;
          add_pluto_note cfg "--nocloogbacktrack accepted as a no-op because PolOpt does not use Pluto's CLooG code generator";
          go (i + 1)
      | "--islsolve" ->
          enable_pluto_compat cfg;
          add_pluto_note cfg "--islsolve accepted as Pluto's default scheduler solver; --pipsolve or an LP solver still overrides it as in Pluto";
          go (i + 1)
      | "--unroll" ->
          pluto_reject Sys.argv.(0) "--unroll: use explicit --unrolljam for polopt's checked constant-bound unroll subset"
      | "--parallel-current" ->
          if i + 1 >= Array.length Sys.argv then invalid_non_negative_int Sys.argv.(0);
          let dim =
            try int_of_string Sys.argv.(i + 1)
            with Failure _ -> invalid_non_negative_int Sys.argv.(0)
          in
          if dim < 0 then invalid_non_negative_int Sys.argv.(0);
          cfg.parallel_current_dim <- Some dim;
          go (i + 2)
      | "--vector-current" ->
          if i + 1 >= Array.length Sys.argv then invalid_vector_non_negative_int Sys.argv.(0);
          let dim =
            try int_of_string Sys.argv.(i + 1)
            with Failure _ -> invalid_vector_non_negative_int Sys.argv.(0)
          in
          if dim < 0 then invalid_vector_non_negative_int Sys.argv.(0);
          cfg.vector_current_dim <- Some dim;
          go (i + 2)
      | "--help" | "-h" ->
          print_endline (usage Sys.argv.(0));
          exit 0
      | "--validate-affine-openscop" ->
          if i + 2 >= Array.length Sys.argv then
            usage_error Sys.argv.(0) "option --validate-affine-openscop expects two file paths";
          cfg.validate_affine_openscop <- Some (Sys.argv.(i + 1), Sys.argv.(i + 2));
          go (i + 3)
      | "--extract-tiling-witness-openscop" ->
          if i + 2 >= Array.length Sys.argv then
            usage_error Sys.argv.(0) "option --extract-tiling-witness-openscop expects two file paths";
          cfg.extract_tiling_witness_openscop <- Some (Sys.argv.(i + 1), Sys.argv.(i + 2));
          go (i + 3)
      | "--validate-tiling-openscop" ->
          if i + 2 >= Array.length Sys.argv then
            usage_error Sys.argv.(0) "option --validate-tiling-openscop expects two file paths";
          cfg.validate_tiling_openscop <- Some (Sys.argv.(i + 1), Sys.argv.(i + 2));
          go (i + 3)
      | "--validate-iss-debug-dumps" ->
          if i + 2 >= Array.length Sys.argv then
            usage_error Sys.argv.(0) "option --validate-iss-debug-dumps expects two file paths";
          cfg.validate_iss_debug_dumps <- Some (Sys.argv.(i + 1), Sys.argv.(i + 2));
          go (i + 3)
      | "--validate-iss-bridge" ->
          if i + 1 >= Array.length Sys.argv then
            usage_error Sys.argv.(0) "option --validate-iss-bridge expects one file path";
          cfg.validate_iss_bridge <- Some Sys.argv.(i + 1);
          go (i + 2)
      | "--validate-iss-pluto-suite" ->
          cfg.validate_iss_pluto_suite <- true;
          go (i + 1)
      | "--validate-iss-pluto-live-suite" ->
          cfg.validate_iss_pluto_live_suite <- true;
          go (i + 1)
      | s when List.mem s positive_oracle_value_options ->
          enable_pluto_compat cfg;
          if i + 1 >= Array.length Sys.argv then
            pluto_reject Sys.argv.(0) (s ^ " requires a value");
          add_pluto_value_flag Sys.argv.(0) cfg s Sys.argv.(i + 1);
          go (i + 2)
      | s when
          begin match split_eq_flag s with
          | Some (flag, _) -> List.mem flag positive_oracle_value_options
          | None -> false
          end ->
          enable_pluto_compat cfg;
          begin match split_eq_flag s with
          | Some (flag, value) ->
              add_pluto_value_flag Sys.argv.(0) cfg flag value;
              go (i + 1)
          | None -> assert false
          end
      | s when List.mem s nonnegative_oracle_value_options ->
          enable_pluto_compat cfg;
          if i + 1 >= Array.length Sys.argv then
            pluto_reject Sys.argv.(0) (s ^ " requires a value");
          add_pluto_nonnegative_value_flag Sys.argv.(0) cfg s Sys.argv.(i + 1);
          go (i + 2)
      | s when
          begin match split_eq_flag s with
          | Some (flag, _) -> List.mem flag nonnegative_oracle_value_options
          | None -> false
          end ->
          enable_pluto_compat cfg;
          begin match split_eq_flag s with
          | Some (flag, value) ->
              add_pluto_nonnegative_value_flag Sys.argv.(0) cfg flag value;
              go (i + 1)
          | None -> assert false
          end
      | s when List.mem s value_options ->
          enable_pluto_compat cfg;
          if i + 1 >= Array.length Sys.argv then
            pluto_reject Sys.argv.(0) (s ^ " requires a value");
          reject_value_option Sys.argv.(0) s Sys.argv.(i + 1)
      | s when
          begin match split_eq_flag s with
          | Some (flag, _) -> List.mem flag value_options
          | None -> false
          end ->
          enable_pluto_compat cfg;
          begin match split_eq_flag s with
          | Some (flag, value) -> reject_value_option Sys.argv.(0) flag value
          | None -> assert false
          end
      | s when
          begin match known_rejection_reason s with
          | Some reason -> pluto_reject Sys.argv.(0) (s ^ ": " ^ reason)
          | None -> false
          end ->
          assert false
      | s when starts_with s "--" ->
          if cfg.pluto_compat_mode then
            pluto_reject Sys.argv.(0) (s ^ ": not in the current Pluto-compatible checked subset")
          else
            usage_error Sys.argv.(0) ("unknown option: " ^ s)
      | s when String.length s > 0 && s.[0] = '-' ->
          usage_error Sys.argv.(0) ("unknown option: " ^ s)
      | file ->
          begin match cfg.input with
          | None -> cfg.input <- Some file; go (i + 1)
          | Some _ -> usage_error Sys.argv.(0) "only one input file is supported"
          end
    end
  in
  go 1

let validate_flag_model prog (cfg : config) =
  validate_pluto_compat prog cfg;
  match SLoopRoute.normalize cfg with
  | Ok selection ->
      if cfg.pluto_compat_mode && cfg.pluto_compat_explain then
        print_pluto_explain cfg;
      selection
  | Error msg -> usage_error prog msg

let phase_pipeline_mode_of_selection = function
  | SLoopRoute.Optimize {
      schedule_family = SLoopRoute.AffineSchedule;
      structural_extension = SLoopRoute.Plain;
      tiling_family = SLoopRoute.Tiled { shape = SLoopRoute.Rectangular; _ };
      execution_family = SLoopRoute.Sequential;
      intra_tile_policy = SLoopRoute.IntraTileDisabled;
      _
    } -> Scheduler.SingleInvocationPhases
  | _ -> Scheduler.StagedPhases

let configure_scheduler_modes selection (cfg : config) =
  let schedule_mode, tiling_mode, diamond_mode, intra_tile_mode =
    match selection with
    | SLoopRoute.Standalone
        (SLoopRoute.ExtractTilingWitness { second_level; _ }
        | SLoopRoute.ValidateTiling { second_level; _ }) ->
        ( Scheduler.AffineSchedule,
          (if second_level then Scheduler.SecondLevelTiling else Scheduler.OrdinaryTiling),
          Scheduler.NoDiamondTiling,
          Scheduler.DisableIntraTile )
    | SLoopRoute.Standalone _ ->
        ( Scheduler.AffineSchedule,
          Scheduler.OrdinaryTiling,
          Scheduler.NoDiamondTiling,
          Scheduler.DisableIntraTile )
    | SLoopRoute.Optimize route ->
        let schedule_mode =
          match route.SLoopRoute.schedule_family with
          | SLoopRoute.AffineSchedule -> Scheduler.AffineSchedule
          | SLoopRoute.IdentitySchedule -> Scheduler.IdentitySchedule
        in
        let tiling_mode =
          match route.SLoopRoute.tiling_family with
          | SLoopRoute.Tiled { levels = SLoopRoute.TwoLevels; _ } ->
              Scheduler.SecondLevelTiling
          | SLoopRoute.NoTiling
          | SLoopRoute.Tiled { levels = SLoopRoute.OneLevel; _ } ->
              Scheduler.OrdinaryTiling
        in
        let diamond_mode =
          match route.SLoopRoute.tiling_family with
          | SLoopRoute.Tiled {
              shape = SLoopRoute.Diamond SLoopRoute.FullDimensionalStart; _
            } -> Scheduler.DiamondFullDimensionalStart
          | SLoopRoute.Tiled {
              shape = SLoopRoute.Diamond SLoopRoute.OneDimensionalStart; _
            } -> Scheduler.DiamondOneDimensionalStart
          | SLoopRoute.NoTiling
          | SLoopRoute.Tiled { shape = SLoopRoute.Rectangular; _ } ->
              Scheduler.NoDiamondTiling
        in
        let intra_tile_mode =
          match route.SLoopRoute.intra_tile_policy with
          | SLoopRoute.IntraTileDisabled -> Scheduler.DisableIntraTile
          | SLoopRoute.IntraTileEnabled -> Scheduler.EnableIntraTile
        in
        (schedule_mode, tiling_mode, diamond_mode, intra_tile_mode)
  in
  Scheduler.set_schedule_mode schedule_mode;
  Scheduler.set_tiling_mode
    tiling_mode;
  Scheduler.set_diamond_mode diamond_mode;
  Scheduler.set_intra_tile_mode intra_tile_mode;
  Scheduler.set_phase_pipeline_mode (phase_pipeline_mode_of_selection selection);
  Scheduler.set_pluto_extra_flags (pluto_scheduler_extra_flags cfg);
  Scheduler.set_pluto_control_files cfg.pluto_control_files

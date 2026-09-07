let fail case expected actual =
  Printf.eprintf
    "[parallel-hint-mapping] FAIL case=%s expected=%s actual=%s\n%!"
    case expected actual;
  exit 1

let pass case details =
  Printf.printf "[parallel-hint-mapping] PASS case=%s %s\n%!" case details

let read_file path =
  let channel = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in channel)
    (fun () -> really_input_string channel (in_channel_length channel))

let write_file path contents =
  let channel = open_out_bin path in
  Fun.protect
    ~finally:(fun () -> close_out channel)
    (fun () -> output_string channel contents)

let replace_once ~case ~needle ~replacement text =
  let replaced =
    Str.replace_first (Str.regexp_string needle) replacement text
  in
  if String.equal replaced text then
    fail case "fixture marker present" "fixture marker absent";
  replaced

let loop_extension =
  "<loop>\n\
   1\n\
   t3\n\
   2\n\
   1\n\
   2\n\
   none\n\
   1\n\
   </loop>\n\n"

let with_t3_parallel_hint ~case text =
  replace_once
    ~case
    ~needle:"</OpenScop>"
    ~replacement:(loop_extension ^ "</OpenScop>")
    text

let parse_scop case path =
  match OpenScopReader.read path with
  | Some scop -> scop
  | None -> fail case "parseable OpenScop" "reader returned None"

let mapped_hints case path =
  let scop = parse_scop case path in
  let raw = Scheduler.extract_parallel_hints_from_outscop path in
  match Scheduler.map_parallel_hints_to_canonical_dims scop raw with
  | [hint] -> hint
  | hints ->
      fail case "one mapped hint" (Printf.sprintf "%d mapped hints" (List.length hints))

let assert_hint case hint ~raw ~canonical =
  let actual_raw = hint.Scheduler.hint_raw_dim in
  let actual_canonical = hint.Scheduler.hint_current_dim in
  if actual_raw <> raw || actual_canonical <> canonical then
    fail
      case
      (Printf.sprintf "raw=%d canonical=%d" raw canonical)
      (Printf.sprintf "raw=%d canonical=%d" actual_raw actual_canonical);
  if hint.Scheduler.hint_iterator <> "t3"
     || hint.Scheduler.hint_stmt_ids <> [1; 2]
  then
    fail case "iterator=t3 statements=[1,2]" "hint metadata changed";
  pass
    case
    (Printf.sprintf "raw=%d canonical=%d" actual_raw actual_canonical)

let with_temp_scop contents f =
  let path = Filename.temp_file "polcert-parallel-hint-" ".scop" in
  Fun.protect
    ~finally:(fun () -> if Sys.file_exists path then Sys.remove path)
    (fun () ->
       write_file path contents;
       f path)

let test_nonzero_scalar_row fixture =
  let text = read_file fixture |> with_t3_parallel_hint ~case:"nonzero-scalar-row" in
  with_temp_scop text (fun path ->
    let hint = mapped_hints "nonzero-scalar-row" path in
    assert_hint "nonzero-scalar-row" hint ~raw:2 ~canonical:2)

let test_globally_zero_row fixture =
  let nonzero_row =
    "   0    0   -1    0    0    0    0    1    ## c2 == 1"
  in
  let zero_row =
    "   0    0   -1    0    0    0    0    0    ## c2 == 0"
  in
  let text =
    read_file fixture
    |> replace_once
         ~case:"globally-zero-row"
         ~needle:nonzero_row
         ~replacement:zero_row
    |> with_t3_parallel_hint ~case:"globally-zero-row"
  in
  with_temp_scop text (fun path ->
    let hint = mapped_hints "globally-zero-row" path in
    assert_hint "globally-zero-row" hint ~raw:2 ~canonical:1)

let test_pluto_c_independence fixture =
  let text = read_file fixture |> with_t3_parallel_hint ~case:"pluto-c-independent" in
  with_temp_scop text (fun path ->
    let before = mapped_hints "pluto-c-independent" path in
    let sidecar = path ^ ".pluto.c" in
    Fun.protect
      ~finally:(fun () -> if Sys.file_exists sidecar then Sys.remove sidecar)
      (fun () ->
         write_file sidecar "for (t3 = 0; t3 < 1; ++t3) S1();\n";
         let compact = mapped_hints "pluto-c-independent" path in
         write_file sidecar "arbitrary formatting that is not C\n";
         let malformed = mapped_hints "pluto-c-independent" path in
         if before.Scheduler.hint_current_dim
              <> compact.Scheduler.hint_current_dim
            || before.Scheduler.hint_current_dim
              <> malformed.Scheduler.hint_current_dim
         then
           fail "pluto-c-independent" "unchanged canonical dimension"
             "sidecar changed mapping";
         pass "pluto-c-independent" "missing/reformatted sidecar ignored"))

let test_phase_schedule_passthrough fixture =
  let case = "phase-schedule-passthrough" in
  let original = parse_scop case fixture in
  let producer = Filename.temp_file "polcert-phase-producer-" ".sh" in
  let previous = Sys.getenv_opt "POLCERT_PLUTO" in
  Fun.protect
    ~finally:(fun () ->
      Unix.putenv "POLCERT_PLUTO" (Option.value previous ~default:"");
      if Sys.file_exists producer then Sys.remove producer)
    (fun () ->
      write_file producer
        "#!/bin/sh\nfor input do :; done\n\
         for stage in midtransform posttile afterscheduling; do\n\
           cp -- \"$input\" \"$input.$stage.scop\" || exit 1\n\
         done\n";
      Unix.chmod producer 0o700;
      Unix.putenv "POLCERT_PLUTO" producer;
      match Scheduler.run_pluto_scop_with_phase_dumps [] original with
      | Result.Okk (mid, tiled, final) ->
          if mid <> tiled || tiled <> final then
            fail case "producer phase schedules unchanged"
              "adapter inserted or changed a schedule coordinate";
          pass case "final schedule is the producer output; no statement rank"
      | Result.Err _ -> fail case "mock phase producer succeeds" "scheduler error")

let test_candidate_scope_restoration () =
  let case = "candidate-scope-restoration" in
  let previous = !(Scheduler.post_tiling_affine_candidate) in
  let candidate scop = Result.Okk (scop, (scop, scop)) in
  let caught = ref false in
  (try
     Scheduler.with_post_tiling_affine_candidate candidate (fun () ->
       match !(Scheduler.post_tiling_affine_candidate) with
       | Some active when active == candidate -> raise Exit
       | _ -> fail case "candidate active within scope" "candidate missing")
   with Exit -> caught := true);
  if not !caught then
    fail case "test exception propagated" "exception swallowed";
  if !(Scheduler.post_tiling_affine_candidate) != previous then
    fail case "previous proposal restored after failure" "proposal leaked";
  pass case "failed proposal cannot affect a later compilation"

let test_parallel_proposal_flag_scope () =
  let case = "parallel-proposal-flag-scope" in
  let previous_flags = !(Scheduler.current_pluto_extra_flags) in
  let previous_mode = !(Scheduler.current_checked_parallel_proposal) in
  Fun.protect
    ~finally:(fun () -> Scheduler.set_pluto_extra_flags previous_flags)
    (fun () ->
      Scheduler.set_pluto_extra_flags [];
      (try
         Scheduler.with_checked_parallel_proposal (fun () ->
           if List.mem "--innerpar" (Scheduler.tile_only_parallel_flags ()) then
             fail case "no implicit innerpar in actual proposal" "flag forced";
           Scheduler.set_pluto_extra_flags ["--innerpar"];
           if not (List.mem "--innerpar"
                     (Scheduler.with_pluto_extra_flags (Scheduler.tile_only_parallel_flags ()))) then
             fail case "explicit innerpar preserved" "explicit flag lost";
           raise Exit)
       with Exit -> ());
      if !(Scheduler.current_checked_parallel_proposal) <> previous_mode then
        fail case "mode restored after exception" "mode leaked");
  pass case "default proposal uses wavefront; explicit and legacy requests preserved"

(* Exercise the public vector dispatch, not just the shared mapping helper.
   The C sidecar deliberately disagrees with the scattering coordinates. *)
let test_vector_dispatch fixture =
  let source = read_file fixture in
  let zero_source = replace_once ~case:"vector-global-zero"
    ~needle:"   0    0   -1    0    0    0    0    1    ## c2 == 1"
    ~replacement:"   0    0   -1    0    0    0    0    0    ## c2 == 0" source in
  List.iter (fun (label, source, expected) ->
    let hinted = with_t3_parallel_hint ~case:label source
      |> replace_once ~case:label ~needle:"none\n1\n</loop>"
           ~replacement:"none\n4\n</loop>" in
    with_temp_scop hinted (fun proposal ->
      List.iter (fun (variant, sidecar) ->
        let case = label ^ "-" ^ variant in
        let producer = Filename.temp_file "polcert-vector-hint-producer-" ".sh" in
        let cfile = Filename.temp_file "polcert-vector-hint-sidecar-" ".c" in
        let previous = Sys.getenv_opt "POLCERT_PLUTO" in
        Fun.protect ~finally:(fun () ->
          Unix.putenv "POLCERT_PLUTO" (Option.value previous ~default:"");
          Sys.remove producer; Sys.remove cfile) (fun () ->
          Option.iter (write_file cfile) sidecar;
          let copy_c = match sidecar with None -> "" | Some _ ->
            "cp -- " ^ Filename.quote cfile ^ " \"$input.pluto.c\"\n" in
          write_file producer ("#!/bin/sh\nfor input do :; done\ncp -- " ^
            Filename.quote proposal ^ " \"$input.afterscheduling.scop\" || exit 1\n" ^ copy_c);
          Unix.chmod producer 0o700;
          Unix.putenv "POLCERT_PLUTO" producer;
          match Scheduler.run_pluto_scop_with_vector_hint [] (parse_scop case proposal) with
          | Result.Okk (_, [hint]) -> assert_hint case hint ~raw:2 ~canonical:expected
          | Result.Okk (_, hints) -> fail case "one canonical vector hint"
              (Printf.sprintf "%d hints" (List.length hints))
          | Result.Err _ -> fail case "mock vector producer succeeds" "scheduler error"))
        ["missing-c", None;
         "malformed-c", Some "not C and no indentation\n";
         "misleading-depth", Some "for (t1 = 0; t1 < 8; ++t1) {\n  for (t3 = 0; t3 < 8; ++t3) {\n    S1();\n    S2();\n  }\n}\n"]))
    ["vector-nonzero-scalar", source, 2; "vector-global-zero", zero_source, 1]

let () =
  let fixture =
    "tools/tiling_routes/fixtures/fusion5-scalar-interleaved.midtransform.scop"
  in
  test_nonzero_scalar_row fixture;
  test_globally_zero_row fixture;
  test_pluto_c_independence fixture;
  test_phase_schedule_passthrough fixture;
  test_candidate_scope_restoration ();
  test_parallel_proposal_flag_scope ();
  test_vector_dispatch fixture

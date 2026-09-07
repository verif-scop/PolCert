open SLoopRoute

let checks = ref 0
let check label condition =
  if not condition then failwith label;
  incr checks

let read path =
  let channel = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in channel)
    (fun () -> really_input_string channel (in_channel_length channel))

let write path text =
  let channel = open_out_bin path in
  Fun.protect ~finally:(fun () -> close_out channel)
    (fun () -> output_string channel text)

let parse path =
  match OpenScopReader.read path with
  | Some scop -> scop
  | None -> failwith ("cannot parse " ^ path)

let base = {
  schedule_family = AffineSchedule;
  structural_extension = Plain;
  tiling_family = Tiled { shape = Rectangular; levels = OneLevel; explicitly_requested = false };
  execution_family = Sequential;
  intra_tile_policy = IntraTileDisabled;
  extract_only = false;
  profile_stages = false;
}

let test_route_selection () =
  let cfg = SLoopCli.parse_args () in
  let tile shape levels = Tiled { shape; levels; explicitly_requested = true } in
  List.iter (fun schedule_family ->
    List.iter (fun structural_extension ->
      List.iter (fun tiling_family ->
        List.iter (fun execution_family ->
          List.iter (fun intra_tile_policy ->
            let route = { base with schedule_family; structural_extension;
              tiling_family; execution_family; intra_tile_policy } in
            let applicable =
              schedule_family = AffineSchedule && structural_extension = Plain
              && execution_family = Sequential && intra_tile_policy = IntraTileDisabled
              && (match tiling_family with Tiled { shape = Rectangular; _ } -> true | _ -> false)
            in
            let expected = if applicable then Scheduler.SingleInvocationPhases else Scheduler.StagedPhases in
            SLoopCli.configure_scheduler_modes (Optimize route) cfg;
            check "CLI resets phase acquisition for every route"
              (!(Scheduler.current_phase_pipeline_mode) = expected))
            [IntraTileDisabled; IntraTileEnabled])
          [Sequential; PlutoParallelHint { strict = false; multiple = false };
           ParallelCurrent 2; PlutoVectorHint { strict = false }; VectorCurrent 2])
        [NoTiling; tile Rectangular OneLevel; tile Rectangular TwoLevels;
         tile (Diamond OneDimensionalStart) OneLevel;
         tile (Diamond FullDimensionalStart) TwoLevels])
      [Plain; ISS]) [AffineSchedule; IdentitySchedule];
  SLoopCli.configure_scheduler_modes (Optimize base) cfg;
  check "ordinary sequential mode enabled"
    (!(Scheduler.current_phase_pipeline_mode) = Scheduler.SingleInvocationPhases);
  SLoopCli.configure_scheduler_modes (Standalone (ValidateAffine ("a", "b"))) cfg;
  check "standalone clears previous single-invocation mode"
    (!(Scheduler.current_phase_pipeline_mode) = Scheduler.StagedPhases)

let with_directory action =
  let directory = Filename.temp_file "polcert-phase-test-" "" in
  Sys.remove directory;
  Unix.mkdir directory 0o700;
  let previous = Sys.getcwd () in
  Fun.protect ~finally:(fun () ->
    Sys.chdir previous;
    Array.iter (fun file -> Sys.remove (Filename.concat directory file)) (Sys.readdir directory);
    Unix.rmdir directory)
    (fun () -> Sys.chdir directory; action directory)

let with_producer ?(missing_mid=false) ?different_final ?(sidecar=false)
    ?(check_tiles=false) action =
  with_directory (fun directory ->
    let producer = Filename.concat directory "producer.sh" in
    let log = Filename.concat directory "calls.txt" in
    let copy_mid = if missing_mid then "" else "cp -- \"$input\" \"$input.midtransform.scop\"\n" in
    let copy_final = match different_final with
      | None -> "cp -- \"$input\" \"$input.afterscheduling.scop\"\n"
      | Some path -> "cp -- " ^ Filename.quote path ^ " \"$input.afterscheduling.scop\"\n"
    in
    write producer ("#!/bin/sh\nset -eu\nprintf '%s\\n' \"$*\" >> " ^ Filename.quote log ^
      "\nfor input do :; done\n" ^
      (if check_tiles then "test \"$(cat tile.sizes)\" = '16 16'\n" else "") ^
      copy_mid ^ "cp -- \"$input\" \"$input.posttile.scop\"\n" ^ copy_final ^
      (if sidecar then "printf 'not C and not a schedule\\n' > \"$input.pluto.c\"\n" else ""));
    Unix.chmod producer 0o700;
    let previous = Sys.getenv_opt "POLCERT_PLUTO" in
    Fun.protect ~finally:(fun () -> Unix.putenv "POLCERT_PLUTO" (Option.value previous ~default:""))
      (fun () -> Unix.putenv "POLCERT_PLUTO" producer;
        action (fun () ->
          if not (Sys.file_exists log) then [] else
            String.split_on_char '\n' (read log) |> List.filter ((<>) ""))))

let configure mode =
  Scheduler.set_schedule_mode Scheduler.AffineSchedule;
  Scheduler.set_tiling_mode Scheduler.OrdinaryTiling;
  Scheduler.set_diamond_mode Scheduler.NoDiamondTiling;
  Scheduler.set_intra_tile_mode Scheduler.DisableIntraTile;
  Scheduler.set_phase_pipeline_mode mode;
  Scheduler.set_pluto_extra_flags [];
  Scheduler.set_pluto_control_files []

let expect_pair label original = function
  | Result.Okk (mid, tiled) -> check label (mid = original && tiled = original)
  | Result.Err _ -> failwith (label ^ ": rejected")

let test_acquisition fixture =
  let original = parse fixture in
  List.iter (fun sidecar ->
    configure Scheduler.SingleInvocationPhases;
    with_producer ~sidecar (fun calls ->
      expect_pair "both phases are actual producer output" original
        (Scheduler.run_pluto_phase_pipeline original);
      check "single invocation ignores missing/misleading C" (List.length (calls ()) = 1);
      check "single invocation does not rerun identity scheduling"
        (not (List.mem "--identity" (String.split_on_char ' ' (List.hd (calls ()))))))) [false; true];
  configure Scheduler.StagedPhases;
  with_producer (fun calls ->
    expect_pair "excluded route preserves staged phases" original
      (Scheduler.run_pluto_phase_pipeline original);
    check "excluded route still invokes both stages" (List.length (calls ()) = 2));
  configure Scheduler.SingleInvocationPhases;
  let called = ref 0 in
  let candidate scop = incr called; Result.Okk scop in
  with_producer (fun calls ->
    Scheduler.with_affine_candidate candidate (fun () ->
      expect_pair "custom midpoint is retained" original (Scheduler.run_pluto_phase_pipeline original));
    check "affine candidate was actually called exactly once" (!called = 1);
    check "only tiling invokes Pluto when a candidate is installed" (List.length (calls ()) = 1);
    check "candidate path preserves identity tiling"
      (List.mem "--identity" (String.split_on_char ' ' (List.hd (calls ())))));
  let previous = !(Scheduler.affine_candidate) in
  let propagated = ref false in
  (try Scheduler.with_affine_candidate (fun _ -> raise Exit)
         (fun () -> ignore (Scheduler.run_pluto_phase_pipeline original))
   with Exit -> propagated := true);
  check "candidate exception propagates" !propagated;
  check "candidate restored after exception" (!(Scheduler.affine_candidate) == previous);
  with_producer ~missing_mid:true (fun calls ->
    check "missing midpoint is rejected, not silently recomputed"
      (match Scheduler.run_pluto_phase_pipeline original with Result.Err _ -> true | _ -> false);
    check "missing midpoint triggers no staged retry" (List.length (calls ()) = 1));
  let different = Filename.temp_file "polcert-phase-different-" ".scop" in
  Fun.protect ~finally:(fun () -> Sys.remove different) (fun () ->
    let changed = Str.replace_first (Str.regexp_string "## c1 == $i0+1") "## changed" (read fixture) in
    let changed = Str.replace_first (Str.regexp_string "   0   -1    0    0    1    0    0    1")
      "   0   -1    0    0    1    0    0    2" changed in
    write different changed;
    check "final-schedule negative is a real AST change" (parse different <> original);
    with_producer ~different_final:different (fun calls ->
      check "post-tile change cannot be silently omitted"
        (match Scheduler.run_pluto_phase_pipeline original with Result.Err _ -> true | _ -> false);
      check "post-tile change triggers no hidden retry" (List.length (calls ()) = 1)))

let test_flags_and_controls fixture =
  configure Scheduler.SingleInvocationPhases;
  let original = parse fixture in
  let sizes = Filename.temp_file "polcert-phase-sizes-" ".txt" in
  Fun.protect ~finally:(fun () -> Sys.remove sizes; Scheduler.set_pluto_control_files []) (fun () ->
    write sizes "16 16\n";
    Scheduler.set_pluto_extra_flags ["--nofuse"; "--rar"];
    Scheduler.set_pluto_control_files ["tile.sizes", sizes];
    with_producer ~check_tiles:true (fun calls ->
      expect_pair "explicit tile sizes available to the same invocation" original
        (Scheduler.run_pluto_phase_pipeline original);
      check "one producer with explicit flags" (List.length (calls ()) = 1);
      let flags = String.split_on_char ' ' (List.hd (calls ())) in
      List.iter (fun flag -> check ("forwarded " ^ flag) (List.mem flag flags))
        ["--nofuse"; "--rar"; "--tile"; "--nointratileopt"; "--noprevector"; "--noparallel"];
      check "explicit control cleaned up" (not (Sys.file_exists "tile.sizes"))));
  Scheduler.set_tiling_mode Scheduler.SecondLevelTiling;
  check "two-level flag retained"
    (List.mem "--second-level-tile" (Scheduler.single_invocation_tiling_flags ()));
  Scheduler.set_tiling_mode Scheduler.OrdinaryTiling;
  check "two-level flag does not leak"
    (not (List.mem "--second-level-tile" (Scheduler.single_invocation_tiling_flags ())))

let () =
  try
    let fixture = Filename.concat (Sys.getcwd ())
      "tools/tiling_routes/fixtures/fusion5-scalar-interleaved.midtransform.scop" in
    test_route_selection ();
    test_acquisition fixture;
    test_flags_and_controls fixture;
    Printf.printf "[phase-pipeline] PASS %d assertions\n%!" !checks
  with exn -> Printf.eprintf "[phase-pipeline] FAIL %s\n%!" (Printexc.to_string exn); exit 1

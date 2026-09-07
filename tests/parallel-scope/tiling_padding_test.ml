open Result

module P = SPolIRs.SPolIRs.PolyLang
module V = SParallelPolOpt.ValidatorCore
module R = STilingBandSched.CoreBandRuntime
module C = R.Legacy
module Q = C.Tiling.PL

let n = Camlcoq.Nat.of_int
let ni = Camlcoq.Nat.to_int
let z = Camlcoq.Z.of_sint
let failures = ref 0
let checks = ref 0

let expect name condition =
  incr checks;
  if condition then Printf.printf "[tiling-padding] PASS %s\n%!" name
  else begin
    incr failures;
    Printf.eprintf "[tiling-padding] FAIL %s\n%!" name
  end

let get = function
  | Okk value -> value
  | Err message -> failwith (Camlcoq.camlstring_of_coqstring message)

let some name = function
  | Some value -> value
  | None -> failwith ("tiling-padding: missing " ^ name)

let checked name (value, alarm_ok) =
  expect (name ^ ": no alarm") alarm_ok;
  value

let replace_at index value =
  List.mapi (fun current old -> if index = current then value else old)

let zero_row rows =
  let columns = match rows with
    | (coefficients, _) :: _ -> List.length coefficients
    | [] -> failwith "tiling-padding: unexpected empty schedule" in
  List.init columns (fun _ -> z 0), z 0

let check_entries name expected_length before after ws =
  let ((before_pis, env), _) = C.Base.outer_to_tiling_pprog before in
  let ((after_pis, _), _) = C.Base.outer_to_tiling_pprog after in
  let env_size = n (List.length env) in
  List.iteri (fun index ((old_pi, new_pi), witness) ->
    if witness.TilingWitness.stw_links <> [] then begin
      let label = Printf.sprintf "%s S%d" name (index + 1) in
      let layout = some "two-level layout"
        (C.infer_scalar_aware_second_level_band_layout env_size old_pi witness) in
      let recipe = some "two-level recipe"
        (C.second_level_band_recipe_of_witness witness) in
      let expected = some "expected two-level schedule"
        (C.scalar_aware_second_level_target_schedule env_size old_pi witness layout recipe) in
      let actual = new_pi.Q.pi_schedule in
      let shape rows = C.check_scalar_aware_second_level_entry_shapeb
        env_size layout old_pi {new_pi with Q.pi_schedule = rows} witness in
      expect (label ^ ": fixture retains its original expected row count")
        (List.length expected = expected_length);
      expect (label ^ ": producer schedule has four rows, with no added test padding")
        (List.length actual = 4);
      expect (label ^ ": unmodified producer schedule matches the local shape")
        (shape actual);
      expect (label ^ ": exact expected schedule matches the local shape")
        (shape expected);
      expect (label ^ ": adding trailing zero rows is allowed")
        (shape (actual @ [zero_row actual; zero_row actual]));
      expect (label ^ ": trailing-zero equivalence is symmetric")
        (C.check_schedule_with_symmetric_trailing_zero_paddingb expected actual &&
         C.check_schedule_with_symmetric_trailing_zero_paddingb actual expected);
      let coefficients, _ = zero_row actual in
      expect (label ^ ": a nonzero trailing row is rejected")
        (not (shape (actual @ [coefficients, z 1])));
      let root = List.nth actual 1 in
      let child = List.nth actual 2 in
      expect (label ^ ": exchanging the two tile coordinates is rejected")
        (not (shape (replace_at 2 root (replace_at 1 child actual))));
      let tile_coefficients, tile_constant = root in
      expect (label ^ ": shifting a tile coordinate is rejected")
        (not (shape (replace_at 1
          (tile_coefficients, Camlcoq.Z.add tile_constant (z 1)) actual)));
      let point_coefficients, point_constant = List.nth actual 3 in
      expect (label ^ ": reversing the point coordinate is rejected")
        (not (shape (replace_at 3
          (List.map Camlcoq.Z.neg point_coefficients, point_constant) actual)));
      expect (label ^ ": deleting a nonzero point row is rejected")
        (not (shape (List.filteri (fun position _ -> position <> 3) actual)));
      expect (label ^ ": deleting a leading phase row is not trailing-zero erasure")
        (not (shape (List.tl actual)))
    end)
    (List.combine (List.combine before_pis after_pis) ws)

let check_route name before after ws =
  let before_t = C.Base.outer_to_tiling_pprog before in
  let after_t = C.Base.outer_to_tiling_pprog after in
  expect (name ^ ": source/witness correspondence is unchanged")
    (C.TilingCheck.check_pprog_tiling_sourceb before_t after_t ws);
  expect (name ^ ": phase-scalar direct checker accepts")
    (checked (name ^ " phase-scalar")
      (R.PhaseScalar.checked_tiling_sourceb_phase_scalar_extended_direct before_t after_t ws));
  let route = checked (name ^ " runtime route")
    (R.checked_tiling_schedule_sourceb_first_runtime_validate_route before after ws) in
  expect (name ^ ": runtime selects the direct band route, not actual-schedule")
    (route = R.DirectBandAccepted)

let () =
  (* Byte-identical output of the fixed Pluto d414 producer on the existing
     mixed-phase.loop with --identity --tile --second-level-tile --nofuse
     --nodiamond-tile --nointratileopt --noprevector --nounrolljam --noparallel.
     Fixture SHA256: f89d68e28eb1a71ee6ff5b1ca9471564dc9e3cae2f6514e5ffac8995d821a154.
     The regression must use this output unchanged, not append a zero row to
     make the old one-directional shape test accept it. *)
  let loop = SLoopElab.elaborate (SLoopParse.parse_file
    "tools/parallel_current/fixtures/mixed-phase.loop") in
  let source = SPolOpt.CoreOpt.Strengthen.strengthen_pprog
    (get (SPolOpt.CoreOpt.Extractor.extractor loop)) in
  let source_scop = some "source OpenScop" (SPolOpt.to_source_openscop source) in
  let raw_after = some "captured identity tiling" (OpenScopReader.read
    "tests/parallel-scope/mixed-phase-identity-two-level.scop") in
  let artifact = PlutoTilingValidator.extract_phase_artifact_from_scops
    ~tiling_mode:PlutoTilingValidator.SecondLevel
    ~before_path:"mixed-phase.loop" ~after_path:"mixed-phase-identity-two-level.scop"
    source_scop raw_after in
  let ws = PhaseTiling.convert_witness artifact.artifact_witness in
  expect "fixture tiles exactly the first and last phase"
    (List.map (fun w -> List.length w.TilingWitness.stw_links) ws = [2;0;0;0;2]);
  List.iter (fun (name, expected_length, importer) ->
    let before = get (importer source source_scop) in
    let after = get (V.import_canonical_tiled_after_poly
      before artifact.artifact_after_scop ws) in
    check_entries name expected_length before after ws;
    check_route name before after ws)
    ["source-like", 4, P.from_openscop_like_source;
     "schedule-only", 5, P.from_openscop_schedule_only];
  Printf.printf "[tiling-padding] checks=%d failures=%d\n%!" !checks !failures;
  if !failures <> 0 then exit 1

open Datatypes

module CLoop = CTypedLoopSamples.Loop
module CBand = PolOptBandTiling.PolOptBandTiling (CPolIRs.CPolIRs)
module CParallel = ParallelPolOpt.ParallelPolOpt (CPolIRs.CPolIRs)
module PLoop = CParallel.ParallelCodegenCore.ParallelLoop

type stats = {
  loops : int;
  divs : int;
  mods : int;
  guards : int;
  instrs : int;
  coupled_exprs : int;
}

let zero_stats =
  { loops = 0; divs = 0; mods = 0; guards = 0; instrs = 0;
    coupled_exprs = 0 }

let add a b =
  { loops = a.loops + b.loops;
    divs = a.divs + b.divs;
    mods = a.mods + b.mods;
    guards = a.guards + b.guards;
    instrs = a.instrs + b.instrs;
    coupled_exprs = a.coupled_exprs + b.coupled_exprs }

let bump_loop s = { s with loops = s.loops + 1 }
let bump_guard s = { s with guards = s.guards + 1 }
let bump_instr s = { s with instrs = s.instrs + 1 }

let rec nat_to_int = function O -> 0 | S n -> 1 + nat_to_int n

let rec vars_of_expr = function
  | CLoop.Constant _ -> []
  | CLoop.Sum (a, b) | CLoop.Max (a, b) | CLoop.Min (a, b) ->
      vars_of_expr a @ vars_of_expr b
  | CLoop.Mult (_, e) | CLoop.Div (e, _) | CLoop.Mod (e, _) ->
      vars_of_expr e
  | CLoop.Var n -> [nat_to_int n]

let has_coupled_vars e =
  match List.sort_uniq Int.compare (vars_of_expr e) with
  | _ :: _ :: _ -> true
  | _ -> false

let rec expr_stats = function
  | CLoop.Constant _ | CLoop.Var _ -> zero_stats
  | (CLoop.Sum (a, b) | CLoop.Max (a, b) | CLoop.Min (a, b)) as e ->
      let s = add (expr_stats a) (expr_stats b) in
      if has_coupled_vars e then { s with coupled_exprs = s.coupled_exprs + 1 }
      else s
  | CLoop.Mult (_, e) as whole ->
      let s = expr_stats e in
      if has_coupled_vars whole then
        { s with coupled_exprs = s.coupled_exprs + 1 }
      else s
  | CLoop.Div (e, _) as whole ->
      let s = expr_stats e in
      { s with
        divs = s.divs + 1;
        coupled_exprs = s.coupled_exprs + if has_coupled_vars whole then 1 else 0 }
  | CLoop.Mod (e, _) as whole ->
      let s = expr_stats e in
      { s with
        mods = s.mods + 1;
        coupled_exprs = s.coupled_exprs + if has_coupled_vars whole then 1 else 0 }

let rec test_stats = function
  | CLoop.LE (a, b) | CLoop.EQ (a, b) -> add (expr_stats a) (expr_stats b)
  | CLoop.And (a, b) | CLoop.Or (a, b) -> add (test_stats a) (test_stats b)
  | CLoop.Not t -> test_stats t
  | CLoop.TConstantTest _ -> zero_stats

let rec stmt_stats = function
  | CLoop.Loop (lb, ub, body) ->
      bump_loop (add (expr_stats lb) (add (expr_stats ub) (stmt_stats body)))
  | CLoop.Instr (_, args) ->
      bump_instr (List.fold_left (fun s e -> add s (expr_stats e)) zero_stats args)
  | CLoop.Seq stmts -> stmt_list_stats stmts
  | CLoop.Guard (test, body) -> bump_guard (add (test_stats test) (stmt_stats body))
and stmt_list_stats = function
  | CLoop.SNil -> zero_stats
  | CLoop.SCons (stmt, rest) -> add (stmt_stats stmt) (stmt_list_stats rest)

let loop_stats (((stmt, _), _) : CLoop.t) = stmt_stats stmt

let rec pexpr_stats = function
  | PLoop.BaseLoop.Constant _ | PLoop.BaseLoop.Var _ -> zero_stats
  | PLoop.BaseLoop.Sum (a, b)
  | PLoop.BaseLoop.Max (a, b)
  | PLoop.BaseLoop.Min (a, b) -> add (pexpr_stats a) (pexpr_stats b)
  | PLoop.BaseLoop.Mult (_, e) -> pexpr_stats e
  | PLoop.BaseLoop.Div (e, _) ->
      let s = pexpr_stats e in { s with divs = s.divs + 1 }
  | PLoop.BaseLoop.Mod (e, _) ->
      let s = pexpr_stats e in { s with mods = s.mods + 1 }

let rec ptest_stats = function
  | PLoop.BaseLoop.LE (a, b) | PLoop.BaseLoop.EQ (a, b) ->
      add (pexpr_stats a) (pexpr_stats b)
  | PLoop.BaseLoop.And (a, b) | PLoop.BaseLoop.Or (a, b) ->
      add (ptest_stats a) (ptest_stats b)
  | PLoop.BaseLoop.Not t -> ptest_stats t
  | PLoop.BaseLoop.TConstantTest _ -> zero_stats

let requested_concurrency_dim = S (S (S O))

type mode_counts = {
  seq : int;
  par : int;
  vec : int;
  par_requested : int;
  vec_requested : int;
  vec_noninnermost : int;
}

let zero_modes =
  { seq = 0; par = 0; vec = 0; par_requested = 0; vec_requested = 0;
    vec_noninnermost = 0 }

let add_modes a b =
  { seq = a.seq + b.seq;
    par = a.par + b.par;
    vec = a.vec + b.vec;
    par_requested = a.par_requested + b.par_requested;
    vec_requested = a.vec_requested + b.vec_requested;
    vec_noninnermost = a.vec_noninnermost + b.vec_noninnermost }

let rec pstmt_stats = function
  | PLoop.Loop (mode, origin, lb, ub, body) ->
      let body_stats, modes = pstmt_stats body in
      let stats = bump_loop (add (pexpr_stats lb) (add (pexpr_stats ub) body_stats)) in
      let modes = match mode with
        | PLoop.SeqMode -> { modes with seq = modes.seq + 1 }
        | PLoop.ParMode ->
            { modes with
              par = modes.par + 1;
              par_requested = modes.par_requested
                + if origin = Some requested_concurrency_dim then 1 else 0 }
        | PLoop.VecMode ->
            { modes with
              vec = modes.vec + 1;
              vec_requested = modes.vec_requested
                + if origin = Some requested_concurrency_dim then 1 else 0;
              vec_noninnermost = modes.vec_noninnermost
                + if body_stats.loops > 0 then 1 else 0 }
      in
      stats, modes
  | PLoop.Instr (_, args) ->
      (bump_instr (List.fold_left (fun s e -> add s (pexpr_stats e)) zero_stats args),
       zero_modes)
  | PLoop.Seq stmts -> pstmt_list_stats stmts
  | PLoop.Guard (test, body) ->
      let stats, modes = pstmt_stats body in
      bump_guard (add (ptest_stats test) stats), modes
and pstmt_list_stats = function
  | PLoop.SNil -> zero_stats, zero_modes
  | PLoop.SCons (stmt, rest) ->
      let stats, modes = pstmt_stats stmt in
      let rest_stats, rest_modes = pstmt_list_stats rest in
      add stats rest_stats, add_modes modes rest_modes

let parallel_stats (((stmt, _), _) : PLoop.t) = pstmt_stats stmt

let configure ?(tiling=Scheduler.OrdinaryTiling)
    ?(schedule=Scheduler.AffineSchedule)
    ?(diamond=Scheduler.NoDiamondTiling) () =
  Scheduler.set_schedule_mode schedule;
  Scheduler.set_tiling_mode tiling;
  Scheduler.set_diamond_mode diamond;
  Scheduler.set_intra_tile_mode Scheduler.DisableIntraTile;
  Scheduler.set_pluto_extra_flags [];
  Scheduler.set_pluto_control_files []

let describe s =
  Printf.sprintf "loops:%d,divs:%d,mods:%d,guards:%d,instrs:%d,coupled:%d"
    s.loops s.divs s.mods s.guards s.instrs s.coupled_exprs

let fail case expected actual interpretation =
  Printf.eprintf
    "[typed-c-pipeline] FAIL case=%s expected=%s actual=%s interpretation=%s\n%!"
    case expected actual interpretation;
  exit 1

let pass case expected actual interpretation =
  Printf.printf
    "[typed-c-pipeline] PASS case=%s expected=%s actual=%s interpretation=%s\n%!"
    case expected actual interpretation

let run case f =
  try
    let value, ok = f () in
    if ok then value
    else
      fail case "verified-pipeline-acceptance:true" "acceptance:false"
        "extracted-fail-closed-route-rejected"
  with
  | CertcheckerConfig.CertCheckerFailure (_, msg) ->
      fail case "verified-pipeline-acceptance" "validator-rejection"
        msg
  | exn ->
      fail case "verified-pipeline-acceptance" (Printexc.to_string exn)
        "unexpected-runtime-failure"

let assert_typed_context case (((_, _), vars) : CLoop.t) =
  if vars = [] || not (List.exists (fun (_, bounds) -> bounds <> []) vars) then
    fail case "nonempty-C-type-environment-with-array-bounds"
      "missing-or-scalar-only-type-environment" "typed-input-was-not-preserved"

let bind_c_names names =
  let name s = Camlcoq.coqstring_of_camlstring s in
  ignore (Camlcoq.bind_ident_varname
    (List.map (fun (id, c_name) -> id, name c_name) names))

let register_pointwise_names () =
  bind_c_names
    [ CTypedLoopSamples.pw_N, "N";
      CTypedLoopSamples.pw_M, "M";
      CTypedLoopSamples.pw_A, "A";
      CTypedLoopSamples.pw_B, "B" ]

let register_matmul_names () =
  bind_c_names
    [ CTypedLoopSamples.mm_M, "M";
      CTypedLoopSamples.mm_N, "N";
      CTypedLoopSamples.mm_K, "K";
      CTypedLoopSamples.mm_C, "C";
      CTypedLoopSamples.mm_A, "A";
      CTypedLoopSamples.mm_B, "B" ]

let register_reverse_names () =
  bind_c_names
    [ CTypedLoopSamples.ri_N, "RI_N";
      CTypedLoopSamples.ri_A, "RI_A" ]

let register_diamond_names () =
  bind_c_names
    [ CTypedLoopSamples.ds_T, "T";
      CTypedLoopSamples.ds_N, "N";
      CTypedLoopSamples.ds_A, "A" ]

(* This is an untrusted oracle artifact reconstructed from Pluto's reverse-ISS
   debug dump.  The extracted ISS validator below, rather than this text or its
   parser, is the acceptance boundary. *)
let reverse_iss_bridge = {|VAR_ORDER 2
VAR RI_N
VAR i
BEFORE_STMTS 1
BEFORE_DOMAIN 3
ROW 0,-1|0
ROW -1,1|-1
ROW -1,0|-1
AFTER_STMTS 2
AFTER_DOMAIN 4
ROW 0,-1|0
ROW -1,1|-1
ROW -1,0|-1
ROW -1,2|-1
AFTER_DOMAIN 4
ROW 0,-1|0
ROW -1,1|-1
ROW -1,0|-1
ROW 1,-2|0
CUTS 1
CUT -1,2|0
STMT_WITNESSES 2
STMT_WITNESS 0 lt
STMT_WITNESS 0 ge
END|}

let extract_strengthened case source =
  match CBand.BaseOpt.Extractor.extractor source with
  | Result.Okk pol -> CBand.BaseOpt.Strengthen.strengthen_pprog pol
  | Result.Err _ ->
      fail case "typed-C-extraction:success" "typed-C-extraction:rejection"
        "C-instruction-access-extraction-failed"

let poly_stmt_count ((pis, _), _) = List.length pis

let ordinary_tiling () =
  let case = "ordinary-tiling-pointwise" in
  let source = CTypedLoopSamples.c_loop_pointwise_2d in
  register_pointwise_names ();
  assert_typed_context case source;
  configure ();
  let output = run case (fun () -> CBand.coq_Opt_band source) in
  let before = loop_stats source and after = loop_stats output in
  if output = source || after.loops <= before.loops || after.divs = 0 then
    fail case "changed:true,loops-increase:true,tiling-divs:positive"
      (Printf.sprintf "changed:%B,before={%s},after={%s}"
         (output <> source) (describe before) (describe after))
      "ordinary-tiling-effect-missing";
  pass case "typed-C-input,verified-ordinary-tiling,structural-effect"
    (Printf.sprintf "before={%s},after={%s}" (describe before) (describe after))
    "validated-band-tiling-added-tile-and-point-loops"

let two_level_tiling () =
  let case = "two-level-tiling-matmul" in
  let source = CTypedLoopSamples.c_loop_matmul in
  register_matmul_names ();
  assert_typed_context case source;
  configure ();
  let ordinary = run case (fun () -> CBand.coq_Opt_band source) in
  configure ~tiling:Scheduler.SecondLevelTiling ();
  let output = run case (fun () -> CBand.coq_Opt_band source) in
  let one = loop_stats ordinary and two = loop_stats output in
  if output = ordinary || two.loops <= one.loops || two.divs <= one.divs then
    fail case "different-from-one-level:true,loops-and-divs-increase:true"
      (Printf.sprintf "different:%B,one={%s},two={%s}"
         (output <> ordinary) (describe one) (describe two))
      "second-tiling-level-effect-missing";
  pass case "typed-matmul,verified-two-level-tiling,additional-level"
    (Printf.sprintf "one-level={%s},two-level={%s}" (describe one) (describe two))
    "second-level-validator-accepted-an-additional-tile-hierarchy"

let iss_split_codegen () =
  let case = "iss-reverse-index" in
  let source = CTypedLoopSamples.c_loop_reverse_iss in
  register_reverse_names ();
  assert_typed_context case source;
  configure ();
  let source_pol = extract_strengthened case source in
  let bridge = PhaseISS.parse_iss_bridge_text reverse_iss_bridge in
  let (source_pis, ctxt), vars = source_pol in
  let split_pis =
    PhaseISS.reconstruct_after_pis bridge.PhaseISS.pib_after_domains
      bridge.PhaseISS.pib_witness.ISSWitness.iw_cuts
      bridge.PhaseISS.pib_witness.ISSWitness.iw_stmt_witnesses
      source_pis
      (fun source -> source.CBand.PolyLang.pi_poly)
      (fun source domain -> { source with CBand.PolyLang.pi_poly = domain })
  in
  let split_pol = ((split_pis, ctxt), vars) in
  let witness = bridge.PhaseISS.pib_witness in
  let source_stmts = poly_stmt_count source_pol in
  let split_stmts = poly_stmt_count split_pol in
  if not (CBand.ValidatorCore.checked_iss_complete_cut_shape_validate
            source_pol split_pol witness)
  then
    fail case "ISS-validator:accept" "ISS-validator:reject"
      "untrusted-reverse-split-witness-was-rejected";
  if source_stmts <> 1 || split_stmts <> 2 then
    fail case "source-statements:1,split-statements:2"
      (Printf.sprintf "source-statements:%d,split-statements:%d"
         source_stmts split_stmts)
      "ISS-split-effect-missing";
  let split_wf =
    run case (fun () -> CBand.ValidatorCore.check_wf_polyprog_general split_pol)
  in
  if not split_wf then
    fail case "validated-split-well-formed:true" "well-formed:false"
      "ISS-output-could-not-enter-verified-codegen";
  let output =
    run case (fun () ->
      CBand.PrepareCore.prepared_codegen
        (CBand.PolyLang.current_view_pprog split_pol))
  in
  let before = loop_stats source and after = loop_stats output in
  if output = source || after.instrs <= before.instrs then
    fail case "changed:true,generated-pieces:at-least-2"
      (Printf.sprintf "changed:%B,before={%s},after={%s}"
         (output <> source) (describe before) (describe after))
      "verified-ISS-codegen-effect-missing";
  pass case "typed-reverse-access,ISS-statements:1-to-2,verified-codegen"
    (Printf.sprintf "source-statements:%d,split-statements:%d,before={%s},after={%s}"
       source_stmts split_stmts (describe before) (describe after))
    "ISS-validator-well-formedness-checker-and-codegen-all-accepted"

let diamond_tiling () =
  let case = "diamond-stencil" in
  let source = CTypedLoopSamples.c_loop_diamond_stencil in
  register_diamond_names ();
  assert_typed_context case source;
  configure ();
  let no_diamond =
    run case (fun () -> CBand.coq_Opt_post_tiling_affine_band source)
  in
  configure ~diamond:Scheduler.DiamondOneDimensionalStart ();
  let output = run case (fun () -> CBand.coq_Opt_post_tiling_affine_band source) in
  let before = loop_stats source in
  let rectangular = loop_stats no_diamond and diamond = loop_stats output in
  if output = source || output = no_diamond
     || diamond.loops <= before.loops || diamond.divs = 0
     || diamond.coupled_exprs <= before.coupled_exprs
  then
    fail case "changed-from-source-and-no-diamond:true,loops-and-divs-increase:true,coupled-wavefront:true"
      (Printf.sprintf "source-change:%B,diamond-change:%B,before={%s},no-diamond={%s},diamond={%s}"
         (output <> source) (output <> no_diamond) (describe before)
         (describe rectangular) (describe diamond))
      "diamond-wavefront-effect-missing";
  pass case "typed-stencil,verified-diamond-plus-post-affine,coupled-wavefront"
    (Printf.sprintf "before={%s},no-diamond={%s},diamond={%s}"
       (describe before) (describe rectangular) (describe diamond))
    "diamond-tiling-and-post-tiling-affine-validation-both-accepted"

let parallelize () =
  let case = "parallel-pointwise" in
  let source = CTypedLoopSamples.c_loop_pointwise_2d in
  register_pointwise_names ();
  assert_typed_context case source;
  configure ();
  let output =
    run case (fun () ->
      CParallel.coq_Opt_parallel_current source requested_concurrency_dim)
  in
  let stats, modes = parallel_stats output in
  if modes.par <> 1 || modes.par_requested <> 1 || modes.vec <> 0 then
    fail case "par-mode:1,requested-origin:1,vec-mode:0"
      (Printf.sprintf "stats={%s},seq:%d,par:%d,par-requested:%d,vec:%d"
         (describe stats) modes.seq modes.par modes.par_requested modes.vec)
      "validated-parallel-annotation-missing";
  pass case "typed-pointwise,verified-tiling-and-parallel-dimension"
    (Printf.sprintf "stats={%s},seq:%d,par:%d,par-requested:%d,vec:%d"
       (describe stats) modes.seq modes.par modes.par_requested modes.vec)
    "dependence-free-schedule-coordinate-was-marked-parallel"

let vectorize () =
  let case = "vector-pointwise" in
  let source = CTypedLoopSamples.c_loop_pointwise_2d in
  register_pointwise_names ();
  assert_typed_context case source;
  configure ();
  let output =
    run case (fun () ->
      CParallel.coq_Opt_vector_current source requested_concurrency_dim)
  in
  let stats, modes = parallel_stats output in
  if modes.vec <> 1 || modes.vec_requested <> 1
     || modes.vec_noninnermost <> 0 || modes.par <> 0
  then
    fail case "vec-mode:1,requested-origin:1,noninnermost:0,par-mode:0"
      (Printf.sprintf "stats={%s},seq:%d,par:%d,vec:%d,vec-requested:%d,noninnermost:%d"
         (describe stats) modes.seq modes.par modes.vec modes.vec_requested
         modes.vec_noninnermost)
      "validated-vector-annotation-missing";
  pass case "typed-pointwise,verified-restricted-inner-concurrency"
    (Printf.sprintf "stats={%s},seq:%d,par:%d,vec:%d,vec-requested:%d,noninnermost:%d"
       (describe stats) modes.seq modes.par modes.vec modes.vec_requested
       modes.vec_noninnermost)
    "dependence-free-innermost-schedule-coordinate-was-marked-vector"

let () =
  ordinary_tiling ();
  two_level_tiling ();
  iss_split_codegen ();
  diamond_tiling ();
  parallelize ();
  vectorize ();
  Printf.printf
    "[typed-c-pipeline] PASS expected=6 actual=6 interpretation=all-typed-C-verified-route-and-component-effects-observed\n%!"

module PL = SPolIRs.SPolIRs.PolyLang
module Check = ISSValidator.ISSValidator(SPolIRs.SPolIRs)
module I = SInstr.SInstr

let z = Camlcoq.Z.of_sint
let nat = PhaseISS.nat_of_int
let constraint_ coeffs rhs = (List.map z coeffs, z rhs)
let require label result =
  if not result then failwith label;
  Printf.printf "PASS %s\n%!" label

let before =
  SLoopIss.build_iss_debug_pprog ["N"; "i"]
    [[constraint_ [0; -1] 0; constraint_ [-1; 1] (-1)]]

let piece sign =
  { ISSWitness.isw_parent_stmt = nat 0;
    isw_piece_signs = [sign] }

let witness =
  { ISSWitness.iw_cuts = [constraint_ [-1; 2] 0];
    iw_stmt_witnesses =
      [piece ISSWitness.ISSCutGeZero; piece ISSWitness.ISSCutLtZero] }

let bridge =
  { PhaseISS.pib_var_order = ["N"; "i"];
    pib_before_domains = [[]];
    pib_after_domains = [[]; [constraint_ [0; 0] (-1)]];
    pib_witness = witness }

let accepts after w = Check.checked_iss_complete_cut_shape_validate before after w
let candidate b =
  let ((rows, ctxt), vars) = before in
  let w = b.PhaseISS.pib_witness in
  let rows = PhaseISS.reconstruct_after_pis
    b.PhaseISS.pib_after_domains w.ISSWitness.iw_cuts
    w.ISSWitness.iw_stmt_witnesses rows
    (fun pi -> pi.PL.pi_poly) (fun pi domain -> {pi with PL.pi_poly=domain}) in
  (((rows, ctxt), vars), w)

let () =
  let after, w = candidate bridge in
  require "canonical complete partition accepted" (accepts after w);
  let ((source :: _, _), _) = before in
  let ((rows, ctxt), vars) = after in
  require "raw universe/empty domains are not adopted"
    (List.for_all (fun pi ->
       pi.PL.pi_poly <> [] && pi.PL.pi_poly <> [constraint_ [0; 0] (-1)]) rows);
  require "source payload retained"
    (List.for_all (fun pi -> pi.PL.pi_instr = source.PL.pi_instr &&
                            pi.PL.pi_raccess = source.PL.pi_raccess &&
                            pi.PL.pi_waccess = source.PL.pi_waccess) rows);
  let forged = ((List.map2 (fun pi domain -> {pi with PL.pi_poly = domain})
                   rows bridge.PhaseISS.pib_after_domains, ctxt), vars) in
  require "forged raw domains rejected directly" (not (accepts forged w));
  let changed_cut = {w with ISSWitness.iw_cuts = [constraint_ [-1; 2] 7]} in
  require "cut changed without matching candidate rejected" (not (accepts after changed_cut));
  let changed_after, changed_w = candidate {bridge with PhaseISS.pib_witness = changed_cut} in
  require "different complete cut remains a valid proposal" (accepts changed_after changed_w);
  let missing = {w with ISSWitness.iw_stmt_witnesses = [piece ISSWitness.ISSCutGeZero]} in
  let missing_after, missing_w = candidate {bridge with PhaseISS.pib_after_domains=[[]];pib_witness=missing} in
  require "missing sign region rejected" (not (accepts missing_after missing_w));
  let duplicated = {w with ISSWitness.iw_stmt_witnesses = [piece ISSWitness.ISSCutGeZero;piece ISSWitness.ISSCutGeZero]} in
  let duplicate_after, duplicate_w = candidate {bridge with PhaseISS.pib_witness=duplicated} in
  require "duplicate sign region rejected" (not (accepts duplicate_after duplicate_w));
  let bad_instr = I.SAssign (I.AcVar (Camlcoq.intern_string "changed"), I.ExConst (z 1)) in
  let changed_payload = ((List.map (fun pi -> {pi with PL.pi_instr=bad_instr}) rows,ctxt),vars) in
  require "changed instruction rejected" (not (accepts changed_payload w));
  let changed_access = ((List.map (fun pi -> {pi with PL.pi_waccess=[(Camlcoq.intern_string "changed",[])]}) rows,ctxt),vars) in
  require "changed memory access rejected" (not (accepts changed_access w));
  let malformed =
    try ignore (PhaseISS.signed_piece_constraints w.ISSWitness.iw_cuts []);false
    with PhaseISS.PhaseISSFailure _ -> true in
  require "cut/sign arity mismatch rejected" malformed

(* These tests exercise the native source-coordinate adapter, not the
   dump-only debug model used by the low-level checker tests above. *)
let source_scop params iterators =
  let strings = List.map Camlcoq.coqstring_of_camlstring in
  let relation depth =
    { OpenScop.dummy_ctxt_rel with
      OpenScop.rel_type = OpenScop.DomTy;
      meta = { OpenScop.dummy_ctxt_rel.OpenScop.meta with
        OpenScop.out_dim_nb = nat depth;
        param_nb = nat (List.length params) } } in
  { OpenScop.dummy_scop with
    OpenScop.context = { OpenScop.dummy_ctxt_scop with
      OpenScop.params = Some (strings params);
      param_domain = relation 0 };
    statements = List.map (fun iters ->
      { OpenScop.domain = relation (List.length iters);
        scattering = OpenScop.dummy_ctxt_rel;
        access = [];
        stmt_exts_opt = Some [OpenScop.StmtBody (strings iters, OpenScop.ArrSkip)] })
      iterators }

let one_piece parent =
  { ISSWitness.isw_parent_stmt = nat parent;
    isw_piece_signs = [ISSWitness.ISSCutGeZero] }

let named_bridge order cut domains =
  { PhaseISS.pib_var_order = order;
    pib_before_domains = domains;
    pib_after_domains = domains;
    pib_witness = { ISSWitness.iw_cuts = [cut];
      iw_stmt_witnesses = List.mapi (fun parent _ -> one_piece parent) domains } }

let rejects label f =
  require label (try ignore (f ()); false with PhaseISS.PhaseISSFailure _ -> true)

let () =
  let iters = List.init 11 (fun i -> "$i" ^ string_of_int i) in
  let source = source_scop ["Z"; "A"; "Unused"] [iters] in
  let semantic = ["Z"; "A"; "Unused"] @ iters in
  let present = List.filter (fun name -> name <> "Unused" && name <> "$i5") semantic in
  let wire = List.sort String.compare present in
  let values = List.mapi (fun index name -> name, index + 1) semantic in
  let coeffs = List.map (fun name -> List.assoc name values) wire in
  let row = constraint_ coeffs 17 in
  let parsed = named_bridge wire row [[row]] in
  let aligned = PhaseISS.align_bridge_to_source source parsed in
  let expected = constraint_
      (List.map (fun name -> if List.mem name present then List.assoc name values else 0) semantic) 17 in
  require "eleven-dimensional lexical wire order is not source order" (wire <> semantic);
  require "eleven-dimensional cut follows explicit source coordinates"
    (aligned.PhaseISS.aib_witness.ISSWitness.iw_cuts = [expected]);
  require "before-domain coefficients follow source coordinates"
    (aligned.PhaseISS.aib_before_domains = [[expected]]);
  require "after-domain coefficients follow parent source coordinates"
    (aligned.PhaseISS.aib_after_domains = [[expected]]);
  require "unused parameter and iterator retain zero-valued coordinate slots"
    (List.nth (fst expected) 2 = z 0 && List.nth (fst expected) 8 = z 0);
  let reversed_wire = List.rev wire in
  let reversed = named_bridge reversed_wire
      (constraint_ (List.rev coeffs) 17) [[constraint_ (List.rev coeffs) 17]] in
  require "wire permutation preserves the same named cut"
    (PhaseISS.align_bridge_to_source source reversed = aligned);
  let mixed = source_scop ["N"; "M"] [["i"; "j"]; ["i"]] in
  let cut = constraint_ [0; 2; -1; 0] 0 in
  (* Wire is j,i,N,M; source coordinates are N,M,i[,j]. *)
  let mixed_bridge = named_bridge ["j"; "i"; "N"; "M"] cut
      [[constraint_ [1; 0; 0; 0] 9]; [constraint_ [0; 1; 0; 0] 7]] in
  rejects "mixed-depth nonempty global cut rejects the existing uniform-width limitation" (fun () ->
    PhaseISS.align_bridge_to_source mixed mixed_bridge);
  let no_cut_bridge = { mixed_bridge with PhaseISS.pib_witness =
      { ISSWitness.iw_cuts = []; iw_stmt_witnesses = List.map (fun w ->
          { w with ISSWitness.isw_piece_signs = [] }) mixed_bridge.PhaseISS.pib_witness.ISSWitness.iw_stmt_witnesses } } in
  let mixed_aligned = PhaseISS.align_bridge_to_source mixed no_cut_bridge in
  require "mixed-depth domains use each statement's own depth"
    (mixed_aligned.PhaseISS.aib_before_domains =
      [[constraint_ [0; 0; 0; 1] 9]; [constraint_ [0; 0; 1] 7]]);
  let reordered_children = { no_cut_bridge with
    PhaseISS.pib_after_domains = List.rev mixed_bridge.PhaseISS.pib_after_domains;
    pib_witness = { no_cut_bridge.PhaseISS.pib_witness with
      ISSWitness.iw_stmt_witnesses = List.rev no_cut_bridge.PhaseISS.pib_witness.ISSWitness.iw_stmt_witnesses } } in
  require "child order does not determine parent coordinate order"
    ((PhaseISS.align_bridge_to_source mixed reordered_children).PhaseISS.aib_after_domains =
      List.rev mixed_aligned.PhaseISS.aib_after_domains);
  let scalar_only = source_scop ["N"] [[]; ["i"]] in
  rejects "parameter-only cut cannot bypass mixed-depth exact row widths" (fun () ->
    PhaseISS.align_bridge_to_source scalar_only
      (named_bridge ["i"; "N"] (constraint_ [0; 1] 2) [[]; []]));
  require "unused trailing iterator retains required full cut width"
    ((PhaseISS.align_bridge_to_source (source_scop ["N"] [["i"; "j"]])
      (named_bridge ["i"; "N"] (constraint_ [2; -1] 0) [[]])).PhaseISS.aib_witness.ISSWitness.iw_cuts
      = [constraint_ [-1; 2; 0] 0]);
  rejects "nonzero coordinate absent from shallow statement rejected" (fun () ->
    PhaseISS.align_bridge_to_source mixed
      { mixed_bridge with PhaseISS.pib_witness =
        { mixed_bridge.PhaseISS.pib_witness with ISSWitness.iw_cuts = [constraint_ [1; 0; 0; 0] 0] } });
  rejects "different positional meanings of a global cut rejected" (fun () ->
    PhaseISS.align_bridge_to_source (source_scop [] [["i"; "j"]; ["j"; "i"]])
      (named_bridge ["i"; "j"] (constraint_ [1; 0] 0) [[]; []]));
  rejects "unknown nonzero bridge variable rejected" (fun () ->
    PhaseISS.align_bridge_to_source (source_scop [] [["i"]])
      (named_bridge ["unknown"] (constraint_ [1] 0) [[]]));
  rejects "unknown nonzero raw-domain variable rejected" (fun () ->
    PhaseISS.align_bridge_to_source (source_scop [] [["i"]])
      (named_bridge ["unknown"] (constraint_ [0] 0) [[constraint_ [1] 0]]));
  rejects "duplicate bridge names rejected" (fun () ->
    PhaseISS.align_bridge_to_source source { parsed with PhaseISS.pib_var_order = "A" :: wire });
  rejects "missing bridge coefficients rejected" (fun () ->
    PhaseISS.align_bridge_to_source source
      { parsed with PhaseISS.pib_before_domains = [[constraint_ [] 0]] });
  rejects "duplicate source iterator names rejected" (fun () ->
    PhaseISS.align_bridge_to_source (source_scop [] [["i"; "i"]])
      (named_bridge ["i"] (constraint_ [1] 0) [[]]));
  rejects "source parameter-iterator collision rejected" (fun () ->
    PhaseISS.align_bridge_to_source (source_scop ["i"] [["i"]])
      (named_bridge ["i"] (constraint_ [1] 0) [[]]));
  rejects "invalid parent index rejected" (fun () ->
    PhaseISS.align_bridge_to_source source
      { parsed with PhaseISS.pib_witness =
        { parsed.PhaseISS.pib_witness with ISSWitness.iw_stmt_witnesses = [one_piece 5] } });
  let nameless = { source with OpenScop.context =
      { source.OpenScop.context with OpenScop.params = None } } in
  rejects "missing explicit source parameter names rejected" (fun () ->
    PhaseISS.align_bridge_to_source nameless parsed);
  let s = List.hd source.OpenScop.statements in
  let bad_depth = { s with OpenScop.domain = { s.OpenScop.domain with
      OpenScop.meta = { s.OpenScop.domain.OpenScop.meta with OpenScop.out_dim_nb = nat 12 } } } in
  rejects "source iterator metadata mismatch rejected" (fun () ->
    PhaseISS.align_bridge_to_source { source with OpenScop.statements = [bad_depth] } parsed);
  rejects "negative bridge header count rejected" (fun () ->
    PhaseISS.parse_iss_bridge_text "VAR_ORDER -1\nEND\n");
  let formal_before = SLoopIss.build_iss_debug_pprog semantic [[expected]] in
  let full_bridge = { parsed with PhaseISS.pib_after_domains = [[]; []];
      pib_witness = { parsed.PhaseISS.pib_witness with
        ISSWitness.iw_stmt_witnesses = [piece ISSWitness.ISSCutGeZero; piece ISSWitness.ISSCutLtZero] } } in
  let aligned = PhaseISS.align_bridge_to_source source full_bridge in
  let formal_w = aligned.PhaseISS.aib_witness in
  let ((before_pis, ctxt), vars) = formal_before in
  let after_pis = PhaseISS.reconstruct_after_pis aligned.PhaseISS.aib_after_domains
      formal_w.ISSWitness.iw_cuts formal_w.ISSWitness.iw_stmt_witnesses before_pis
      (fun pi -> pi.PL.pi_poly) (fun pi domain -> {pi with PL.pi_poly = domain}) in
  let formal_after = ((after_pis, ctxt), vars) in
  require "aligned eleven-dimensional proposal passes unchanged verified partition checker"
    (Check.checked_iss_complete_cut_shape_validate formal_before formal_after formal_w)

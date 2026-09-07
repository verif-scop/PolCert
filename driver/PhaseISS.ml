open Result

exception PhaseISSFailure of string

let failf fmt = Printf.ksprintf (fun s -> raise (PhaseISSFailure s)) fmt

let rec nat_of_int n =
  if n <= 0 then Datatypes.O else Datatypes.S (nat_of_int (n - 1))

let rec int_of_nat = function
  | Datatypes.O -> 0
  | Datatypes.S n -> 1 + int_of_nat n

let split_on_char ch s =
  let rec go i j acc =
    if j = String.length s then
      List.rev (String.sub s i (j - i) :: acc)
    else if s.[j] = ch then
      go (j + 1) (j + 1) (String.sub s i (j - i) :: acc)
    else
      go i (j + 1) acc
  in
  go 0 0 []

let int_of_string_or_fail ctx s =
  try int_of_string s
  with Failure _ -> failf "cannot parse integer in %s: %S" ctx s

let count_of_string_or_fail ctx s =
  let n = int_of_string_or_fail ctx s in
  if n < 0 then failf "negative count in %s: %d" ctx n;
  n

let z_of_string s =
  Camlcoq.Z.of_sint (int_of_string_or_fail "ISS bridge" s)

let parse_row_line line =
  match String.split_on_char ' ' line with
  | ["ROW"; payload] ->
      begin match split_on_char '|' payload with
      | [coeffs_s; const_s] ->
          let coeffs =
            if coeffs_s = "" then []
            else List.map z_of_string (split_on_char ',' coeffs_s)
          in
          (coeffs, z_of_string const_s)
      | _ ->
          failf "bad ISS bridge ROW payload: %S" payload
      end
  | _ ->
      failf "bad ISS bridge ROW line: %S" line

let iss_sign_of_string = function
  | "ge" -> ISSWitness.ISSCutGeZero
  | "lt" -> ISSWitness.ISSCutLtZero
  | s -> failf "unknown ISS halfspace sign %S in bridge" s

type parsed_iss_bridge = {
  pib_var_order : string list;
  pib_before_domains : (BinNums.coq_Z list * BinNums.coq_Z) list list;
  pib_after_domains : (BinNums.coq_Z list * BinNums.coq_Z) list list;
  pib_witness : ISSWitness.iss_witness;
}

let iss_bridge_text_present text =
  String.split_on_char '\n' text
  |> List.exists
       (fun line ->
         let line = String.trim line in
         String.length line >= 9 && String.sub line 0 9 = "VAR_ORDER")

let parse_iss_bridge_text text =
  let lines0 =
    String.split_on_char '\n' text
    |> List.filter (fun s -> String.trim s <> "")
  in
  let rec drop_preamble = function
    | [] -> failf "missing ISS bridge VAR_ORDER"
    | line :: rest as lines ->
        if String.length line >= 9 && String.sub line 0 9 = "VAR_ORDER"
        then lines
        else drop_preamble rest
  in
  let lines = drop_preamble lines0 in
  let rec take_rows n acc = function
    | [] -> failf "unexpected end of ISS bridge while reading %d rows" n
    | line :: rest ->
        if n = 0 then (List.rev acc, line :: rest)
        else take_rows (n - 1) (parse_row_line line :: acc) rest
  in
  let rec take_vars n acc = function
    | [] -> failf "unexpected end of ISS bridge while reading %d vars" n
    | line :: rest ->
        if n = 0 then (List.rev acc, line :: rest)
        else
          begin match String.split_on_char ' ' line with
          | ["VAR"; name] -> take_vars (n - 1) (name :: acc) rest
          | _ -> failf "bad ISS bridge VAR line: %S" line
          end
  in
  let rec take_domains tag n acc lines =
    if n = 0 then (List.rev acc, lines) else
    match lines with
    | [] -> failf "unexpected end of ISS bridge while reading %s domains" tag
    | line :: rest ->
        begin match String.split_on_char ' ' line with
        | [hdr; row_count_s] when hdr = tag ->
            let row_count =
              count_of_string_or_fail "ISS bridge domain row count" row_count_s
            in
            let (rows, rest') = take_rows row_count [] rest in
            take_domains tag (n - 1) (rows :: acc) rest'
        | _ ->
            failf "bad ISS bridge %s line: %S" tag line
        end
  in
  let rec take_cuts n acc lines =
    if n = 0 then (List.rev acc, lines) else
    match lines with
    | [] -> failf "unexpected end of ISS bridge while reading cuts"
    | line :: rest ->
        begin match String.split_on_char ' ' line with
        | ["CUT"; payload] ->
            let row = parse_row_line ("ROW " ^ payload) in
            take_cuts (n - 1) (row :: acc) rest
        | _ -> failf "bad ISS bridge CUT line: %S" line
        end
  in
  let rec take_stmt_witnesses n acc lines =
    if n = 0 then (List.rev acc, lines) else
    match lines with
    | [] ->
        failf "unexpected end of ISS bridge while reading stmt witnesses"
    | line :: rest ->
        begin match String.split_on_char ' ' line with
        | ["STMT_WITNESS"; parent_s; signs_s] ->
            let signs =
              if signs_s = "" then []
              else List.map iss_sign_of_string (split_on_char ',' signs_s)
            in
            let w =
              {
                ISSWitness.isw_parent_stmt =
                  nat_of_int (count_of_string_or_fail "ISS bridge parent" parent_s);
                isw_piece_signs = signs;
              }
            in
            take_stmt_witnesses (n - 1) (w :: acc) rest
        | _ -> failf "bad ISS bridge STMT_WITNESS line: %S" line
        end
  in
  let var_order, rest1 =
    match lines with
    | line :: rest ->
        begin match String.split_on_char ' ' line with
        | ["VAR_ORDER"; n_s] ->
            take_vars (count_of_string_or_fail "ISS bridge var count" n_s) [] rest
        | _ -> failf "bad ISS bridge header: %S" line
        end
    | [] -> failf "empty ISS bridge output"
  in
  let before_domains, rest2 =
    match rest1 with
    | line :: rest ->
        begin match String.split_on_char ' ' line with
        | ["BEFORE_STMTS"; n_s] ->
            take_domains
              "BEFORE_DOMAIN"
              (count_of_string_or_fail "ISS bridge before stmt count" n_s)
              [] rest
        | _ -> failf "bad ISS bridge BEFORE_STMTS line: %S" line
        end
    | [] -> failf "missing ISS bridge BEFORE_STMTS"
  in
  let after_domains, rest3 =
    match rest2 with
    | line :: rest ->
        begin match String.split_on_char ' ' line with
        | ["AFTER_STMTS"; n_s] ->
            take_domains
              "AFTER_DOMAIN"
              (count_of_string_or_fail "ISS bridge after stmt count" n_s)
              [] rest
        | _ -> failf "bad ISS bridge AFTER_STMTS line: %S" line
        end
    | [] -> failf "missing ISS bridge AFTER_STMTS"
  in
  let cuts, rest4 =
    match rest3 with
    | line :: rest ->
        begin match String.split_on_char ' ' line with
        | ["CUTS"; n_s] ->
            take_cuts (count_of_string_or_fail "ISS bridge cut count" n_s) [] rest
        | _ -> failf "bad ISS bridge CUTS line: %S" line
        end
    | [] -> failf "missing ISS bridge CUTS"
  in
  let stmt_witnesses, rest5 =
    match rest4 with
    | line :: rest ->
        begin match String.split_on_char ' ' line with
        | ["STMT_WITNESSES"; n_s] ->
            take_stmt_witnesses
              (count_of_string_or_fail "ISS bridge stmt witness count" n_s)
              [] rest
        | _ -> failf "bad ISS bridge STMT_WITNESSES line: %S" line
        end
    | [] -> failf "missing ISS bridge STMT_WITNESSES"
  in
  begin match rest5 with
  | ["END"] -> ()
  | line :: _ -> failf "unexpected trailing ISS bridge line: %S" line
  | [] -> failf "missing ISS bridge END"
  end;
  let witness =
    {
      ISSWitness.iw_cuts = cuts;
      iw_stmt_witnesses = stmt_witnesses;
    }
  in
  {
    pib_var_order = var_order;
    pib_before_domains = before_domains;
    pib_after_domains = after_domains;
    pib_witness = witness;
  }

let parse_iss_bridge_text_opt text =
  if iss_bridge_text_present text then
    Some (parse_iss_bridge_text text)
  else
    None

let nth_or_fail ctx xs n =
  try List.nth xs n
  with Failure _ ->
    failf "%s index %d is out of bounds" ctx n

module SPolyLang = PolyLang.PolyLang(SInstr.SInstr)
module TPolyLang = PolyLang.PolyLang(TInstr.TInstr)
module CPolyLang = PolyLang.PolyLang(CInstr.CInstr)

(* VAR_ORDER describes the named dump's serialization basis, not PolyLang's
   coordinate order.  Only the source OpenScop specifies the latter: ordered
   parameters followed by that statement's ordered iterators. *)
type aligned_iss_bridge = {
  aib_before_domains : (BinNums.coq_Z list * BinNums.coq_Z) list list;
  aib_after_domains : (BinNums.coq_Z list * BinNums.coq_Z) list list;
  aib_witness : ISSWitness.iss_witness;
}

let check_unique_names ctx names =
  let rec loop seen = function
    | [] -> ()
    | name :: rest ->
        if name = "" || List.mem name seen then
          failf "%s has an empty or duplicate name: %S" ctx name;
        loop (name :: seen) rest
  in
  loop [] names

let source_coordinate_names scop =
  let ctxt = scop.OpenScop.context in
  let param_count = int_of_nat ctxt.OpenScop.param_domain.OpenScop.meta.OpenScop.param_nb in
  let params =
    match ctxt.OpenScop.params with
    | Some names -> List.map Camlcoq.camlstring_of_coqstring names
    | None when param_count = 0 -> []
    | None -> failf "ISS source OpenScop has no explicit parameter names"
  in
  check_unique_names "ISS source parameters" params;
  if List.length params <> param_count then
    failf "ISS source parameter name/count mismatch";
  List.mapi
    (fun index stmt ->
      let meta = stmt.OpenScop.domain.OpenScop.meta in
      if int_of_nat meta.OpenScop.param_nb <> param_count ||
         int_of_nat meta.OpenScop.in_dim_nb <> 0 ||
         int_of_nat meta.OpenScop.local_dim_nb <> 0 then
        failf "ISS source statement %d has unsupported domain dimensions" index;
      let iters =
        match stmt.OpenScop.stmt_exts_opt with
        | Some [OpenScop.StmtBody (names, _)] ->
            List.map Camlcoq.camlstring_of_coqstring names
        | _ -> failf "ISS source statement %d needs one explicit iterator list" index
      in
      if List.length iters <> int_of_nat meta.OpenScop.out_dim_nb then
        failf "ISS source statement %d iterator name/count mismatch" index;
      let names = params @ iters in
      check_unique_names (Printf.sprintf "ISS source statement %d coordinates" index) names;
      names)
    scop.OpenScop.statements

let align_named_row var_order source_names (coeffs, constant) =
  if List.length coeffs <> List.length var_order then
    failf "ISS bridge row width does not match VAR_ORDER";
  let named = List.combine var_order coeffs in
  List.iter
    (fun (name, coeff) ->
      if coeff <> BinNums.Z0 && not (List.mem name source_names) then
        failf "ISS bridge uses nonzero variable %S absent from source statement" name)
    named;
  (List.map
     (fun name -> try List.assoc name named with Not_found -> BinNums.Z0)
     source_names, constant)

let trim_zero_coefficients (coeffs, constant) =
  let rec drop = function BinNums.Z0 :: rest -> drop rest | rest -> rest in
  (List.rev (drop (List.rev coeffs)), constant)

let align_bridge_to_source before_scop bridge =
  check_unique_names "ISS bridge VAR_ORDER" bridge.pib_var_order;
  let coordinates = source_coordinate_names before_scop in
  if List.length coordinates <> List.length bridge.pib_before_domains then
    failf "ISS bridge/source statement count mismatch";
  if List.length bridge.pib_after_domains <>
     List.length bridge.pib_witness.ISSWitness.iw_stmt_witnesses then
    failf "ISS bridge after-domain/witness count mismatch";
  let align names row = align_named_row bridge.pib_var_order names row in
  let before_domains = List.map2 (fun names rows -> List.map (align names) rows)
      coordinates bridge.pib_before_domains in
  let after_domains = List.map2
      (fun w rows ->
        let names = nth_or_fail "ISS parent stmt" coordinates
            (int_of_nat w.ISSWitness.isw_parent_stmt) in
        List.map (align names) rows)
      bridge.pib_witness.ISSWitness.iw_stmt_witnesses bridge.pib_after_domains in
  let cuts_by_statement = List.map
      (fun names -> List.map (align names)
          bridge.pib_witness.ISSWitness.iw_cuts)
      coordinates in
  (* The verified witness uses one positional cut list for all statements.
     Compare names/positions modulo zero tails, but retain full source width:
     the subsequent well-formedness check requires exactly that many columns
     in every constraint.  A nonempty global cut cannot satisfy this existing
     interface at two different statement depths, even with zero tails. *)
  let cuts = match cuts_by_statement with
    | [] -> failf "ISS source contains no statements"
    | cuts :: rest ->
        let canonical = List.map trim_zero_coefficients cuts in
        if not (List.for_all (fun rows -> List.map trim_zero_coefficients rows = canonical) rest) then
          failf "ISS named cuts have incompatible source coordinates across statements";
        if not (List.for_all ((=) cuts) rest) then
          failf "ISS global-cut witness requires equal source coordinate widths across statements";
        cuts
  in
  { aib_before_domains = before_domains;
    aib_after_domains = after_domains;
    aib_witness = { bridge.pib_witness with ISSWitness.iw_cuts = cuts } }

(* The Python bridge checks that each raw piece is its pre-ISS dump domain
   plus exactly these signed cuts.  Pluto may simplify/reorder the source
   constraints before that dump.  Reusing the source domain preserves its
   representation for the verified exact-shape checker; it does not select
   new cuts.  The caller checks the complete partition and well-formedness
   against [before_pol].  This is not a separate equality check between the
   pre-ISS dump domain and the original source domain. *)
let signed_piece_constraints cuts signs =
  if List.length cuts <> List.length signs then
    failf "ISS cut/sign count mismatch";
  List.map2
    (fun (coeffs, constant) sign ->
      match sign with
      | ISSWitness.ISSCutLtZero ->
          (coeffs, Camlcoq.Z.sub (Camlcoq.Z.neg constant) Camlcoq.Z.one)
      | ISSWitness.ISSCutGeZero ->
          (List.map Camlcoq.Z.neg coeffs, constant))
    cuts signs

let reconstruct_after_pis after_domains cuts stmt_ws before_pis get_domain set_domain =
  if List.length stmt_ws <> List.length after_domains then
    failf
      "ISS bridge after stmt count mismatch between witness (%d) and domains (%d)"
      (List.length stmt_ws)
      (List.length after_domains);
  List.map
    (fun w ->
      let parent = int_of_nat w.ISSWitness.isw_parent_stmt in
      let source = nth_or_fail "ISS parent stmt" before_pis parent in
      let domain =
        get_domain source
        @ signed_piece_constraints cuts w.ISSWitness.isw_piece_signs
      in
      set_domain source domain)
    stmt_ws

let apply_bridge_to_spol_source before_pol bridge =
  let ((before_pis, ctxt), vars) = before_pol in
  if List.length before_pis <> List.length bridge.aib_before_domains then
    failf
      "ISS bridge before stmt count mismatch between source polyhedral model (%d) and bridge (%d)"
      (List.length before_pis)
      (List.length bridge.aib_before_domains);
  let after_pis =
    reconstruct_after_pis
      bridge.aib_after_domains
      bridge.aib_witness.ISSWitness.iw_cuts
      bridge.aib_witness.ISSWitness.iw_stmt_witnesses
      before_pis
      (fun source -> source.SPolyLang.pi_poly)
      (fun source domain -> { source with SPolyLang.pi_poly = domain })
  in
  (((after_pis, ctxt), vars), bridge.aib_witness)

let apply_bridge_to_tpol_source before_pol bridge =
  let ((before_pis, ctxt), vars) = before_pol in
  if List.length before_pis <> List.length bridge.aib_before_domains then
    failf
      "ISS bridge before stmt count mismatch between source polyhedral model (%d) and bridge (%d)"
      (List.length before_pis)
      (List.length bridge.aib_before_domains);
  let after_pis =
    reconstruct_after_pis
      bridge.aib_after_domains
      bridge.aib_witness.ISSWitness.iw_cuts
      bridge.aib_witness.ISSWitness.iw_stmt_witnesses
      before_pis
      (fun source -> source.TPolyLang.pi_poly)
      (fun source domain -> { source with TPolyLang.pi_poly = domain })
  in
  (((after_pis, ctxt), vars), bridge.aib_witness)

let apply_bridge_to_cpol_source before_pol bridge =
  let ((before_pis, ctxt), vars) = before_pol in
  if List.length before_pis <> List.length bridge.aib_before_domains then
    failf
      "ISS bridge before stmt count mismatch between source polyhedral model (%d) and bridge (%d)"
      (List.length before_pis)
      (List.length bridge.aib_before_domains);
  let after_pis =
    reconstruct_after_pis
      bridge.aib_after_domains
      bridge.aib_witness.ISSWitness.iw_cuts
      bridge.aib_witness.ISSWitness.iw_stmt_witnesses
      before_pis
      (fun source -> source.CPolyLang.pi_poly)
      (fun source domain -> { source with CPolyLang.pi_poly = domain })
  in
  (((after_pis, ctxt), vars), bridge.aib_witness)

let infer_from_source_scop apply_bridge before_pol before_scop =
  match Scheduler.iss_identity_bridge_from_scop before_scop with
  | Err _ as err -> err
  | Okk text ->
      begin
        try match parse_iss_bridge_text_opt text with
        | None -> Okk None
        | Some bridge ->
              let bridge = align_bridge_to_source before_scop bridge in
              let (after_pol, witness) = apply_bridge before_pol bridge in
              Okk (Some (after_pol, witness))
            with
            | PhaseISSFailure msg ->
                Err (Camlcoq.coqstring_of_camlstring msg)
            | Invalid_argument msg ->
                Err (Camlcoq.coqstring_of_camlstring msg)
      end

let spol_infer_iss_from_source_scop before_pol before_scop =
  infer_from_source_scop apply_bridge_to_spol_source before_pol before_scop

let tpol_infer_iss_from_source_scop before_pol before_scop =
  infer_from_source_scop apply_bridge_to_tpol_source before_pol before_scop

let cpol_infer_iss_from_source_scop before_pol before_scop =
  infer_from_source_scop apply_bridge_to_cpol_source before_pol before_scop

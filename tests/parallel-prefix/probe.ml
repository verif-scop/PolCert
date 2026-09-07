open Result
module P = SPolIRs.SPolIRs.PolyLang
module V = Validator.Validator(SPolIRs.SPolIRs)
let unalarm (value, valid) = if valid then value else failwith "validator alarm"

let take n xs = List.filteri (fun i _ -> i < n) xs
let drop n xs = List.filteri (fun i _ -> i >= n) xs
let phase_key d pi =
  let rows = take d pi.P.pi_schedule in
  if List.length rows = d
     && List.for_all (fun (a, _) -> List.for_all (Camlcoq.Z.eq Camlcoq.Z.zero) a) rows
  then Some (List.map snd rows) else None

let () =
  let scop = Option.get (OpenScopReader.read Sys.argv.(1)) in
  let pol = match P.from_openscop_complete scop with
    | Okk p -> P.current_view_pprog p
    | Err msg -> failwith (Camlcoq.camlstring_of_coqstring msg)
  in
  let d = int_of_string Sys.argv.(2) in
  let plan = Camlcoq.Nat.of_int d in
  let check p = unalarm (V.check_pprog_parallel_currentb p plan) in
  let ((pis, env), vars) = pol in
  Printf.printf "global_before=%b statements=%d\n%!" (check pol) (List.length pis);
  let keys = List.sort_uniq compare (List.filter_map (phase_key d) pis) in
  let checked = List.map (fun key ->
    let group = List.filter (fun pi -> phase_key d pi = Some key) pis in
    let ok = check ((group, env), vars) in
    Printf.printf "phase=%s count=%d parallel=%b\n%!"
      (String.concat "," (List.map (fun z -> string_of_int (Camlcoq.Z.to_int z)) key))
      (List.length group) ok;
    (key, ok)) keys in
  let width = List.fold_left (fun w pi -> max w (List.length pi.P.pi_schedule)) 0 pis in
  let pis' = List.map (fun pi ->
    let zero = (List.init (List.length env + Camlcoq.Nat.to_int pi.P.pi_depth)
      (fun _ -> Camlcoq.Z.zero), Camlcoq.Z.zero) in
    let sched = pi.P.pi_schedule @ List.init (width - List.length pi.P.pi_schedule) (fun _ -> zero) in
    let keep = match phase_key d pi with
      | None -> true
      | Some key -> List.assoc key checked in
    let schedule = if keep then sched @ [zero]
      else take d sched @ [zero] @ drop d sched in
    { pi with P.pi_schedule = schedule }) pis in
  let proposal = ((pis', env), vars) in
  Printf.printf "schedule_validation=%b\n%!" (unalarm (V.validate_general pol proposal));
  Printf.printf "wf_proposal=%b\n%!" (unalarm (V.check_wf_polyprog_general proposal));
  Printf.printf "global_after=%b\n%!" (check proposal)

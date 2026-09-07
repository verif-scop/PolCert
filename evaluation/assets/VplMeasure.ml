(* Measurement-only module. All recorded intervals use CLOCK_MONOTONIC.
   Regions are synchronous; exclusive time subtracts immediate child intervals. *)
external now : unit -> float = "polcert_monotonic_clock"
let skip_debug = try Sys.getenv "VPLMEASURE_SKIP_DEBUG" = "1" with Not_found -> false

type aggregate = { mutable calls : int; mutable inclusive : float;
                   mutable exclusive : float }
type frame = { key : string; label : string; started : float; mutable children : float }
let active_stage = ref ""
let stack : frame list ref = ref []
let totals : (string, aggregate) Hashtbl.t = Hashtbl.create 128
let counters : (string, int) Hashtbl.t = Hashtbl.create 128

let bump name value =
  if !active_stage <> "" then begin
    let key = !active_stage ^ "|" ^ name in
    let old = try Hashtbl.find counters key with Not_found -> 0 in
    Hashtbl.replace counters key (old + value)
  end

let maximum name value =
  if !active_stage <> "" then begin
    let key = !active_stage ^ "|" ^ name in
    let old = try Hashtbl.find counters key with Not_found -> 0 in
    Hashtbl.replace counters key (max old value)
  end

let poly name rows =
  if !active_stage <> "" then begin
    let constraints = List.length rows in
    let dimensions = List.fold_left (fun m (coeffs, _) -> max m (List.length coeffs)) 0 rows in
    bump (name ^ ".calls") 1;
    bump (name ^ ".constraints_sum") constraints;
    maximum (name ^ ".constraints_max") constraints;
    bump (name ^ ".dimensions_sum") dimensions;
    maximum (name ^ ".dimensions_max") dimensions
  end

let region name f =
  if !active_stage = "" then f () else begin
    let path = List.rev_map (fun frame -> frame.label) !stack @ [name] in
    let frame = {key = !active_stage ^ "|" ^ String.concat "/" path;
                 label = name; started = now (); children = 0.0} in
    stack := frame :: !stack;
    let finish () =
      let elapsed = now () -. frame.started in
      (match !stack with
       | head :: tail when head == frame -> stack := tail
       | _ -> failwith "VplMeasure: unbalanced region stack");
      (match !stack with parent :: _ -> parent.children <- parent.children +. elapsed | [] -> ());
      let aggregate = try Hashtbl.find totals frame.key with Not_found ->
        let row = {calls = 0; inclusive = 0.0; exclusive = 0.0} in
        Hashtbl.add totals frame.key row; row in
      aggregate.calls <- aggregate.calls + 1;
      aggregate.inclusive <- aggregate.inclusive +. elapsed;
      aggregate.exclusive <- aggregate.exclusive +. (elapsed -. frame.children)
    in
    match f () with value -> finish (); value
    | exception error -> finish (); raise error
  end

let stage name f =
  if !active_stage <> "" then failwith "VplMeasure: nested stage";
  active_stage := name;
  match region "stage_other" f with
  | value -> active_stage := ""; value
  | exception error -> active_stage := ""; raise error

let print () =
  if !stack <> [] then failwith "VplMeasure: unfinished regions";
  let names = Hashtbl.fold (fun name _ acc -> name :: acc) totals [] |> List.sort String.compare in
  List.iter (fun name -> let row = Hashtbl.find totals name in
    Printf.eprintf "[vpl-profile] region %s %d %.9f %.9f\n" name row.calls row.inclusive row.exclusive) names;
  let names = Hashtbl.fold (fun name _ acc -> name :: acc) counters [] |> List.sort String.compare in
  List.iter (fun name -> Printf.eprintf "[vpl-profile] metric %s %d\n" name (Hashtbl.find counters name)) names

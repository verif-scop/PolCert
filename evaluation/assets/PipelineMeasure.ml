(* Isolated measurement overlay: the original driver and checks are unchanged.
   The outermost classified region owns nested work. In particular, the affine
   checker invoked by parallel/tiling validation is not charged a second time. *)
external now : unit -> float = "polcert_monotonic_clock"

type aggregate = { mutable calls : int; mutable seconds : float }
let started : float option ref = ref None
let owner : string option ref = ref None
let totals : (string, aggregate) Hashtbl.t = Hashtbl.create 16
let entries : (string, int) Hashtbl.t = Hashtbl.create 32
let excluded_io = ref 0.0
let proposal_count = ref 0
(* A separate VPL-details build can attach nested operation attribution to each
   outermost stage. The ordinary pipeline profiler uses the identity hook. *)
type stage_hook = { measure : 'a. string -> (unit -> 'a) -> 'a }
let stage_hook = ref { measure = (fun _ f -> f ()) }

let measurement_io f =
  let before = now () in
  match f () with
  | value -> excluded_io := !excluded_io +. now () -. before; value
  | exception error -> excluded_io := !excluded_io +. now () -. before; raise error

let capture_begin name flags write_input =
  match Sys.getenv_opt "POLCERT_PROFILE_CAPTURE" with
  | None -> None
  | Some root -> measurement_io (fun () ->
      incr proposal_count;
      let base = Printf.sprintf "%s/%04d-%s" root !proposal_count name in
      let out = open_out (base ^ ".flags.json") in
      Printf.fprintf out "[%s]\n"
        (String.concat "," (List.map (Printf.sprintf "%S") flags));
      close_out out;
      write_input (base ^ ".input.scop");
      Some base)

let capture_result base write_result = match base with
  | None -> ()
  | Some path -> measurement_io (fun () -> write_result path)

let region name f =
  match !started with
  | None -> f ()
  | Some _ ->
      let count = try Hashtbl.find entries name with Not_found -> 0 in
      Hashtbl.replace entries name (count + 1);
      let trace_calls = Sys.getenv_opt "POLCERT_PROFILE_CALLS" = Some "1" in
      let enclosing = match !owner with None -> "none" | Some label -> label in
      let trace_start = if trace_calls then now () else 0.0 in
      if trace_calls then
        Printf.eprintf "[pipeline-call] enter %s %d owner=%s\n%!"
          name (count + 1) enclosing;
      let trace_finish () =
        if trace_calls then
          Printf.eprintf "[pipeline-call] exit %s %d owner=%s seconds=%.9f\n%!"
            name (count + 1) enclosing (now () -. trace_start)
      in
      match !owner with
      | Some _ ->
          (match f () with
           | value -> trace_finish (); value
           | exception error -> trace_finish (); raise error)
      | None ->
          owner := Some name;
          let before = now () in
          let io_before = !excluded_io in
          let finish () =
            let elapsed = now () -. before -. (!excluded_io -. io_before) in
            owner := None;
            let row = try Hashtbl.find totals name with Not_found ->
              let row = {calls = 0; seconds = 0.0} in
              Hashtbl.add totals name row; row in
            row.calls <- row.calls + 1;
            row.seconds <- row.seconds +. elapsed;
            trace_finish ()
          in
          match (!stage_hook).measure name f with
          | value -> finish (); value
          | exception error -> finish (); raise error

let print () =
  match !started with
  | None -> ()
  | Some before ->
      let elapsed = now () -. before -. !excluded_io in
      (match !owner with
       | Some name -> Printf.eprintf "[pipeline-profile] unfinished %s\n" name
       | None -> ());
      let names = Hashtbl.fold (fun name _ xs -> name :: xs) totals []
        |> List.sort String.compare in
      List.iter (fun name -> let row = Hashtbl.find totals name in
        Printf.eprintf "[pipeline-profile] region %s %d %.9f\n"
          name row.calls row.seconds) names;
      let classified = Hashtbl.fold (fun _ row sum -> sum +. row.seconds) totals 0.0 in
      Printf.eprintf "[pipeline-profile] region others 1 %.9f\n" (elapsed -. classified);
      Printf.eprintf "[pipeline-profile] total %.9f\n" elapsed;
      Printf.eprintf "[pipeline-profile] excluded_capture_io %.9f\n" !excluded_io;
      Hashtbl.fold (fun name count xs -> (name, count) :: xs) entries []
      |> List.sort compare
      |> List.iter (fun (name, count) ->
           Printf.eprintf "[pipeline-profile] entries %s %d\n" name count)

let start () =
  if !started <> None then failwith "PipelineMeasure.start called twice";
  started := Some (now ());
  at_exit print

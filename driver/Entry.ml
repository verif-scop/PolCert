open Diagnostics
open Result
open TPolValidator

let tool_name = "Verified Validator for Affine Polyhedral Scheduling"

let _ =
  try
    Gc.set { (Gc.get()) with
                Gc.minor_heap_size = 524288; (* 512k *)
                Gc.major_heap_increment = 4194304 (* 4M *)
            };
  if Array.length Sys.argv < 3 then 
    Printf.printf "Usage: %s <pol1> <pol2>\n" Sys.argv.(0)
  else
  let scopfile1 = Sys.argv.(1) in
  let scopfile2 = Sys.argv.(2) in 
  match OpenScopReader.read scopfile1, OpenScopReader.read scopfile2 with
  | Some scop1, Some scop2 ->
    (match TPolIRs.TPolIRs.PolyLang.from_openscop_complete scop1,
          TPolIRs.TPolIRs.PolyLang.from_openscop_complete scop2 with
    | Okk pol1, Okk pol2 ->
        let (res1, ok1) = TVal.validate pol1 pol2 in
        let (res2, ok2) = TVal.validate pol2 pol1 in
        (if ok1 && res1 && ok2 && res2 then
          Printf.printf "[EQ] The two polyhedral models (%s, %s) are equivalent.\n" scopfile1 scopfile2
        else if ok1 && res1 then
          Printf.printf ("[GT] Polyhedral model %s refines %s.\n") scopfile2 scopfile1
        else if ok2 && res2 then
          Printf.printf ("[LT] Polyhedral model %s refines %s.\n") scopfile1 scopfile2 
        else
          Printf.printf ("[NE] Cannot determine refinement relations between the two polyhedral models (%s, %s).\n") scopfile1 scopfile2
        )
    | _, _ ->
      Printf.printf "Error: cannot convert openscop to polyhedron.\n"
    )
  | _, _ -> 
    Printf.printf "Error: cannot read the input openscop files (s).\n"
  with
  | Sys_error msg -> error no_loc "%s" msg; exit 2
  | e -> crash e

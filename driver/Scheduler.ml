

(* let scheduler  *)
open Result
open Driveraux
(* open CPolIRs *)
open Camlcoq
open Filename
open Str  (* Required for regular expressions *)

(** scop to scop *)

(** TODO: specify dump scop file name in pluto*)
let scheduler' inscop = 
  let inscop_file = tmp_file ".scop" in
  let outscop_file = inscop_file ^ ".afterscheduling.scop" in 
  OpenScopPrinter.openscop_printer inscop_file inscop;
  let cmd = List.concat [
    ["pluto";
    "--dumpscop";
    (* "--nointratileopt"; *)
    (* "--nodiamond-tile";      *)
    "--noprevector";
    "--smartfuse";     
    "--nounrolljam";
    "--noparallel";
    "--notile";
    "--rar";
    "--readscop"];
    [inscop_file]
  ] in
  (* print_string ((String.concat " " cmd) ^ "\n"); *)
  let stdout =  (tmp_file (".stdout")) in
  let exc = command ?stdout:(Some stdout) cmd in
  if exc <> 0 then (
    safe_remove outscop_file;
    command_error "scheduler" exc;)
  else 
    (* print_string ("Reading " ^ (basename outscop_file) ^ " ...\n"); *)
    match OpenScopReader.read outscop_file with 
    | Some outscop -> Okk outscop
    | None -> Err (coqstring_of_camlstring ("scheduler failed")) 


let find_and_extract_time filename =
  let ic = open_in filename in
  let rec process_lines () =
    try
      let line = input_line ic in
      let regex = regexp "\\[pluto\\] Auto-transformation time: \\([0-9.]+\\)s" in
      if string_match regex line 0 then begin
        let time_str = matched_group 1 line in
        let time_float = float_of_string time_str in
        close_in ic;
        time_float
      end else
        process_lines ()
    with
      End_of_file -> close_in ic; max_float
  in
  process_lines ()


(* also return the autoscheduling time, in pluto's stdout, "Auto-transformation time" *)
let invoke_pluto testname =
  let inscop_file = testname ^ ".beforescheduling.scop" in
  let outscop_file = testname ^ ".afterscheduling.scop" in
  let cmd = List.concat [
    ["pluto";
    "--dumpscop";
    (* "--nointratileopt"; *)
    (* "--nodiamond-tile";      *)
    "--noprevector";
    "--smartfuse";     
    "--nounrolljam";
    "--noparallel";
    "--notile";
    "--rar"];
    [testname ^ ".c"]
  ] in
  let stdout =  (tmp_file ("." ^ testname ^ ".stdout")) in
  print_string ("\027[90mInfo\027[0m: Executing \"" ^ (String.concat " " cmd) ^ "\"\n");
  let exc = command ?stdout:(Some stdout) cmd in
  if exc <> 0 then (
    command_error "invoke pluto failed" exc;)
  else 
    (* [pluto] Auto-transformation time: 0.001530s *)
    let runtime = find_and_extract_time stdout in
    Printf.printf "\027[90mInfo\027[0m: Invoke pluto succeed, with auto-transformation time %fs\n" runtime;
    print_string ("\027[90mInfo\027[0m: Reading " ^ (inscop_file) ^ " ...\n");
    match OpenScopReader.read inscop_file with 
    | Some inscop -> 
      print_string ("\027[90mInfo\027[0m: Read " ^ (inscop_file) ^ " successfully\n");
      (match OpenScopReader.read outscop_file with 
      | Some outscop ->
        print_string ("\027[90mInfo\027[0m: Read " ^ (outscop_file) ^ " successfully\n");
        Okk (inscop, outscop, runtime)
      | None -> Err (coqstring_of_camlstring ("invoke pluto failed"))
      )
    | None -> Err (coqstring_of_camlstring ("invoke pluto failed")) 
    
  (* match OpenScopReader.read inscop_file with
  | Some outscop -> Okk outscop
  | None -> Err (coqstring_of_camlstring ("cannot read " ^ inscop_file ^ "\n")) *)

(* let scheduler' cpol =
  let inscop = CPolIRs.PolyLang.to_openscop cpol in
  let inscop_file = tmp_file ".scop" in
  let outscop_file = tmp_file ".scop" in 
  OpenScopPrinter.openscop_printer inscop_file inscop;
  match OpenScopReader.read inscop_file with
  | Some outscop -> CPolIRs.PolyLang.from_openscop cpol outscop
  | None -> Err (coqstring_of_camlstring ("Error: cannot read " ^ inscop_file ^ "\n")) *)

let scop_scheduler inscop = scheduler' inscop;;

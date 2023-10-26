open Unix
open TPolIRs
open TPolValidator
open PolPrinter

let tests = [| 
    (** below is examples/ in pluto, that is compilable by candl frontend. *)
    "covcol"; "dsyr2k"; "fdtd-2d"; "gemver"; "lu"; "mvt"; "ssymm"; "tce";                 
    "adi"; "corcol"; "dct"; "dsyrk"; "floyd"; 
    "jacobi-1d-imper";
    "matmul-init"; "pca"; "strmm"; "tmm";                 
    "advect3d"; "corcol3"; "doitgen"; "fdtd-1d"; 
     "jacobi-2d-imper"; 
    "matmul"; "seidel"; "strsm"; "trisolv";
    (** below are in pluto's tests/  (they are truly tested in test.sh.in), and is compilable by candl frontend *)
    (** some of tests are also examples *)
    "1dloop-invar"; "costfunc"; 
    "fusion1"; "fusion2"; "fusion3"; "fusion4"; "fusion5";  
    "fusion6"; "fusion7"; "fusion8"; "fusion9"; "fusion10";  
    "intratileopt1"; "intratileopt2"; "intratileopt3"; "intratileopt4"; 
    "matmul-seq"; "matmul-seq3"; "multi-loop-param"; "multi-stmt-stencil-seq";
    "mxv"; "mxv-seq"; "mxv-seq3"; "negparam"; "nodep"; "noloop";
    "polynomial"; "seq"; "shift"; "spatial"; 
    "tricky1"; "tricky2"; "tricky3"; "tricky4"; "wavefront"
    |]

(* let tests = [| "3d7pt"; "apop"; "covcol"; "dsyr2k"; "fdtd-2d"; "gemver"; "heat-3d"; "lbm_fpc_d2q9"; "lbm_ldc_d3q27"; "lu"; "mvt"; "ssymm"; "tce";
                    "adi"; "corcol"; "dct"; "dsyrk"; "floyd"; "heat-1d"; "jacobi-1d-imper"; "lbm_ldc_d2q9"; "lbm_mrt_d2q9"; "matmul-init"; "pca"; "strmm"; "tmm";
                    "advect3d"; "corcol3"; "doitgen"; "fdtd-1d"; "game-of-life"; "heat-2d"; "jacobi-2d-imper"; "lbm_ldc_d3q19"; "lbm_poiseuille_d2q9"; "matmul"; "seidel"; "strsm"; "trisolv" |] *)


let example_tests = [| "noloop" |]

let folder_exists folder_path =
  Sys.file_exists folder_path && Sys.is_directory folder_path

(* let print_colored_text color_code text =
  Printf.printf "\027[%sm%s\027[0m" color_code text

let print_warning_message message =
  print_colored_text "33" message 33 is the ANSI code for yellow *)

let eval_result = ref []

let test_single idx test_name =
  if not (folder_exists test_name) then
    Printf.printf "\027[31mFAIL\027[0m: Test folder %s does not exists, skipped\n" test_name
  else
  Printf.printf "\027[90mInfo\027[0m: Testing [[[ %d: %s ]]]... \n" (idx+1) test_name;
  try
    Unix.chdir test_name;
    (* Printf.printf "Info: chdir to: %s\n" test_name; *)
    (match Scheduler.invoke_pluto test_name with
    | Okk (inscop, outscop, runtime) ->
        (* Printf.printf "Info: pluto success.\n"; *)
        (
        match TPolIRs.PolyLang.from_openscop_complete inscop, TPolIRs.PolyLang.from_openscop_complete outscop with
        | Okk inpol, Okk outpol -> 
            (
              (match TPolIRs.PolyLang.to_openscop inpol with
              | Some inscop -> OpenScopPrinter.openscop_printer "in.scop" inscop
              | None -> Printf.printf "\027[31mFAIL\027[0m: inpol to openscop failed\n")
              ; 
              (match TPolIRs.PolyLang.to_openscop outpol with
              | Some inscop -> OpenScopPrinter.openscop_printer "out.scop" inscop
              | None -> Printf.printf "\027[31mFAIL\027[0m:: outpol to openscop failed\n")
              ; 
            );
            (Printf.printf "\027[90mInfo\027[0m: poly transformation success\n";
            let t0 = Sys.time() in
            let (res1, ok1) = TVal.validate inpol outpol in
            let tv1 = Sys.time() -. t0 in
            let t0 = Sys.time() in
            let (res2, ok2) = TVal.validate outpol inpol in
            let tv2 = Sys.time() -. t0 in
            (if ok1 && res1 then
              Printf.printf "\027[32mSUCCEED\027[0m: (orig -> opt). Running time %fs.\n" tv1
            else
              Printf.printf "\027[31mFAIL\027[0m: (orig -> opt). (ok:%B, res:%B).\n" ok1 res1
            );
            (if ok2 && res2 then
                Printf.printf "\027[32mSUCCEED\027[0m: (opt -> orig). Running time %fs.\n" tv2
              else 
                Printf.printf "\027[31mFAIL\027[0m: (opt -> orig). (ok:%B, res:%B).\n" ok2 res2);
            let result = (if res1 && res2 then "EQ" else if res1 then "GT" else if res2 then "LT" else "NEQ") in 
            eval_result := List.append !eval_result [(test_name, Float.mul 1000.0 runtime, Float.mul 1000.0 tv1, Float.mul 1000.0 tv2, result)]);  (* ms *)
            Printf.printf "<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<\n%!"
        | _, _ -> 
            Printf.printf "\027[31mFAIL\027[0m: poly transformation failed\n%!"
        )
    | Err (err) ->
        Printf.printf "\027[31mFAIL\027[0m: pluto failed\n");
      Unix.chdir ".."
  with Unix_error (err, func, arg) ->
    Printf.printf "\027[31mFAIL\027[0m: %s\n" (Unix.error_message err)

let print_result filename =
  let oc = open_out filename in
  Printf.fprintf oc "Test ToP ToB ToF Result\n";
  let lst = !eval_result in  (* Dereference the ref to access the list *)
  List.iter (fun (str, f1, f2, f3, str2) ->
    Printf.fprintf oc "%s %.2f %.2f %.2f %s\n" str f1 f2 f3 str2
  ) lst;
  close_out oc
;;

(* Main function *)
let () =
  (* Loop through each folder name in the array and test it *)
  Array.iteri test_single tests;
  print_result "../../result.txt"
  (* Array.iter test_single tests *)

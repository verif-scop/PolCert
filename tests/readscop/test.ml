open Printf 
open OpenScopReader
open OpenScopPrinter

let loop filename = 
  let outfilename = filename ^ ".output" in
  (match read_and_print filename outfilename with
   | Some p ->
      printf "\027[32mSUCCEED\027[0m: Parsing openscop file %s.\n" filename
   | None -> printf "\027[31mFAIL\027[0m: Parsing openscop file %s .\n" filename)

(** test both printer and reader *)
let () = 
  for i = 1 to Array.length Sys.argv - 1 do
    loop Sys.argv.(i); 
    loop (Sys.argv.(i) ^ ".output")
  done
;;

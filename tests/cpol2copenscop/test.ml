open Printf 
open OpenScopReader
open OpenScopPrinter
open Pol2OpenScop
open PolPrinter
open CPolIRs

let run () = 
  cpol_printer "1_cpol.output" sample_cpol;
  let ocopenscop = CPolIRs.PolyLang.to_openscop sample_cpol in
  match ocopenscop with
  | Some copenscop -> 
    (openscop_printer "2_sample_copenscop.output" copenscop;
    let ocpol' = CPolIRs.PolyLang.from_openscop sample_cpol copenscop in (** ocpol' should be equal to cpol *)
    match ocpol' with
    | Okk cpol' -> cpol_printer "3_cpol.output" cpol'; printf "\027[32mSUCCEED\027[0m: Convert Pol to and from Openscop (for CInstr)\n"
    | Err msg -> printf "\027[31mFAIL\027[0m: %s\n" (Camlcoq.camlstring_of_coqstring msg))
  | None -> 
      printf "\027[31mFAIL\027[0m: %s\n" ("Convert Pol to and from Openscop (for CInstr)")
;;

(** test both printer and reader *)
let () = 
  run ()
;;

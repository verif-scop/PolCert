(** test pluto works in ocaml *)
open Printf 
open Top
open PolPrinter
open Camlcoq
open CPolIRs


let () =
  let cpol_orig = CSample1.sample_cpol in
  cpol_printer "./orig.cpol" cpol_orig;
  match CPolIRs.scheduler cpol_orig with
  | Okk cpol_opt -> 
      cpol_printer "./opt.cpol" cpol_opt;
      printf "\027[32mSUCCEED\027[0m: Invoke pluto.\n"
  | Err msg -> 
      printf "\027[31mFAIL\027[0m: Invoke pluto, %s\n" (camlstring_of_coqstring msg)
;;

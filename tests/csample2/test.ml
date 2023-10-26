open Printf 
open Top
open PolPrinter
open Camlcoq
open CPolIRs
open CPolOpt
open CSample2

let () =
  (* printf "Testing validation using pluto for csample2...\n"; *)
  let cpol_orig = CSample2.sample_cpol in
  cpol_printer "./orig.cpol" cpol_orig;
  match CPolIRs.scheduler cpol_orig with
  | Okk cpol_opt -> 
      cpol_printer "./opt.cpol" cpol_opt;
      let (res, ok) = CPolOpt.Validator.validate cpol_orig cpol_opt in
      (* printf "%b\n" res; *)
      (if ok && res then printf "\027[32mSUCCEED\027[0m: (orig -> opt).\n"
      else printf "\027[31mFAIL\027[0m: (orig -> opt).\n");
      let (res, ok) = CPolOpt.Validator.validate cpol_opt cpol_orig  in
      (* printf "%b\n" res; *)
      (if ok && res then printf "\027[32mSUCCEED\027[0m: (opt -> orig).\n"
      else printf "\027[31mFAIL\027[0m: (opt -> orig).\n");
  | Err msg -> 
      printf "\027[31mFAIL\027[0m: %s\n" (camlstring_of_coqstring msg)
;;
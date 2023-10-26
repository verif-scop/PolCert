Require Import ImpureConfig.
Require Import DemoPLVerifier.
Require Import ExtrOcamlString.
Import Debugging.

Set Extraction AccessOpaque.

(** Debugging 
in order to debug, you need to:
  - comment the normal "mode"
  - decomment the debugging "mode" 
*)
(* begin: normal mode *) 
(* Extraction Inline failwith. *)
(* Extraction Inline trace. *)
(* end: normal mode *)

(* begin: debugging code *)
Extract Inlined Constant failwith =>
  "(fun st mesg _ -> raise (CertcheckerConfig.CertCheckerFailure (st, (CoqPr.charListTr mesg))))".

(* If needed, change the global mode below in the first arg of [trace_cmp]. *)
Extract Inlined Constant trace =>
   "(fun mode l a -> if (Debugging.traceCmp INFO mode) then (print_string (CoqPr.charListTr l); print_newline()); a)".
(* end: debugging code *)


Extract Inlined Constant CoqAddOn.posPr => "CoqPr.posPr'".
Extract Inlined Constant CoqAddOn.posPrRaw => "CoqPr.posPrRaw'".
Extract Inlined Constant CoqAddOn.zPr => "CoqPr.zPr'".
Extract Inlined Constant CoqAddOn.zPrRaw => "CoqPr.zPrRaw'".

(* TODO A VIRER ? *)
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive unit => "unit" [ "()" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)" [ "(,)" ].

Extraction Blacklist List String Nat.

Extraction Inline value error.

Cd "extraction".

Separate Extraction Debugging DemoPLVerifier
 (* for compatibility with vpl/lib: *) ProgVar LinTerm PedraQ PedraQBackend DomainFunctors(* Itv *).

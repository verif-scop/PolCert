(** Functions to help debugging of VPL code.

 + a function [failwith] to track internal errors. 
   => Context: most of the times, internal errors of the VPL (bugs in the "non-certified" part of the code) are "masked" 
      using a default value.
        Such a style is both simple for proofs and efficient at runtime 
        (and is necessary to match Verasco interfaces).
   => Purpose: here, we propose to "mark" in the code where are inserted these default values with a "failwith" function.
      Hence, we have thus two modes of the failwith function at extraction:
        - the "normal" mode that propagates the default value.
        - the "debugging" mode that provoques a runtime-failure in Caml, and thus help to track internal errors.

 + trace: use the same principle than "failwith" in order to have traces from the extracted code.

WARNING ON USAGE:
 in
  [failwith "toto" expr]
 or 
  [trace INFO "toto" expr]
 evaluation of [expr] happens before the side-effect (error-raising or printing)

Hence, in order to avoid surprise, [expr] must be a value.

==> The extraction modes for trace and failwith are defined in PedraExtract.v.
(Thus, it is not necessary to recompile all coq!)

*)

Require Import String.

Inductive failureStatus : Set := 
 | CERT   (* invalid certificates from PedraQOracles *)
 | DEMO   (* a failure in DemoPL checker *)
 | NYI    (* "not yet implemented" error *)
 | INTERN (* other cases                 *)
 .

(* NB: in "production" mode, failure are ignored and a default value is returned instead *)
Definition failwith {A: Type} (st: failureStatus) (mesg: string) (a:A) := a.

Inductive traceStatus : Set := 
 | OFF   (* trace never printed *) 
 | INFO  (* trace printed when global mode is INFO or DEBUG *)
 | DEBUG (* trace only printed when global mode is DEBUG *)
 .
(* NB: the global mode is a constant in PedraExtract *)

Definition traceCmp (global local: traceStatus) : bool :=
  match global, local with
  | OFF, _ => false
  | _, OFF => false
  | INFO, DEBUG => false
  | _, _ => true
  end.

Definition trace {A: Type} (local:traceStatus) (s: string) (a:A) := a.

(* 
  If needed, use this tactic to remove debug "annotation" in proofs.
  (However, most of times, the "annotation" is automatically removed by Coq evaluation).
*)
Ltac unfoldDebug := unfold failwith, trace.

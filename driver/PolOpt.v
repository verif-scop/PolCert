Require Import Bool.
Require Import List.
Require Import String.
Import ListNotations.
(* Require Import Errors. *)
Require Import Result.
Require Import Base.
Require Import PolyBase.  
Require Import PolyLang.
Require Import AST.
Require Import BinPos.
Require Import PolyTest.
Require Import Linalg.
Require Import PolyOperations.

Require Import Loop. 
Require Import ZArith.
Require Import Permutation.
Require Import Sorting.Sorted.
Require Import SelectionSort.

Require Import Extractor.
Require Import CodeGen. 

Require Import Validator.
Require Import LibTactics.
Require Import sflib.


Require Import Convert.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Definition apply_total (A B: Type) (x: imp A) (f: A -> B) : imp B :=
   BIND x' <- x -;
   pure (f x').

Definition apply_partial (A B: Type)
                         (x: imp A) (f: A -> imp B) : imp B :=
   BIND x' <- x -;
   f x'.

Definition apply_partial_res (A B: Type)
                           (x: imp A) (f: A -> result B) (d: B): imp B := 
   BIND x' <- x -;
   res_to_alarm d (f x').

Declare Scope opt_scop.
                         
Notation "a @@ b" :=
   (apply_total _ _ a b) (at level 50, left associativity): opt_scop.

Notation "a @@@ b" :=
   (apply_partial _ _ a b) (at level 50, left associativity): opt_scop.

Notation "a @@@[ d ] b" :=
   (apply_partial_res _ _ a b d) (at level 50, left associativity): opt_scop.

Definition print {A: Type} (printer: A -> unit) (prog: A) : A :=
    let unused := printer prog in prog.
  
Local Open Scope string_scope.

Local Open Scope opt_scop.

Local Open Scope impure_scope.
Definition time {A B: Type} (name: string) (f: A -> B) : A -> B := f.


(** Pretty-printers (defined in Caml). *)
Parameter print_CompCertC_stmt: Csyntax.statement -> unit.
(* Parameter print_Loop: Loop.t -> unit.
Parameter print_Pol: PolyLang.t -> unit. *)

Require Import StateTy.
Require Import InstrTy.

Require Import PolIRs.
Require Import CInstr.
Module PolOpt (PolIRs: POLIRS).

(** loop -> pol -> pol -> loop *)
(* Module Loop := PolIRs.Loop.
Module Pol := PolIRs.PolyLang. *)

(* Parameter scheduler: (Pol.t -> result Pol.t). *)
Definition scheduler := PolIRs.scheduler.

Module Extractor := Extractor PolIRs.
Module CodeGen := CodeGen PolIRs.
Module Validator := Validator PolIRs.
(* Definition codegen (pol: Pol.t): result Loop.t := 
   Okk Loop.dummy. *)

(* Definition validate_cpol (pol1 pol2: PolIRs.PolyLang.t)  *)
  (* :=  *)
  
  (* . * FIXME *)
  
Definition scheduler' (pol: PolIRs.PolyLang.t): imp PolIRs.PolyLang.t := 
   match scheduler pol with 
   | Okk pol' => 
      BIND res <- (Validator.validate pol pol') -;
      if res then pure (pol') 
      else res_to_alarm pol (Err "Scheduler validation failed.")
   | Err msg => res_to_alarm pol (Err msg)
   end.



Definition Opt (loop: PolIRs.Loop.t): imp PolIRs.Loop.t := 
   pure loop
   @@@[PolIRs.PolyLang.dummy] time "PolOpt.Extractor" Extractor.extractor
   (* @@ print (print_CPol) *)
   @@@ time "PolOpt.Scheduler" scheduler'
   (* @@ print (print_CPol) *)
   (* @@@[cloop_ty_dummy] time "PolOpt.Codegen" CodeGen.codegen *)
   @@@ time "PolOpt.Codegen" CodeGen.codegen.
   (* @@ print (print_CLoop). *)

Close Scope impure_scope.
Close Scope opt_scop.

End PolOpt.

(* Require Import CState.
Require Import PolyLoop.
Require Import Loop. *)

(** Instantiate all IRs PolOpt use *)
(* Module CPolIRs <: POLIRS with Module Instr := CInstr.
   Module Instr := CInstr.
   Module State := State.
   Module PolyLang := PolyLang CInstr.
   Module PolyLoop := PolyLoop CInstr.
   Module Loop := Loop CInstr.
End CPolIRs. *)

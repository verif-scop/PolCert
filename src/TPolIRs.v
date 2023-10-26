Require Import PolIRs.
Require Import TInstr.
Require Import PolyLang. 
Require Import PolyLoop.
Require Import Loop.
Require Import Result.
Require Import OpenScop.
Require Import String.

Local Open Scope string_scope.

Module TPolIRs <: POLIRS with Module Instr := TInstr.
   Module Instr := TInstr.
   Module State := State.
   Module Ty := Ty.
   Module PolyLang := PolyLang TInstr.
   Module PolyLoop := PolyLoop TInstr.
   Module Loop := Loop TInstr.
   Definition scop_scheduler (scop: OpenScop): result OpenScop := Err "invalid". 
   Definition scheduler (cpol: PolyLang.t): result PolyLang.t := Err "invalid".
End TPolIRs.

Require Import PolIRs.
Require Import CInstr.
Require Import PolyLang. 
Require Import PolyLoop.
Require Import Loop.
Require Import CState.
Require Import Result.
Require Import OpenScop.
Require Import String.
Require Import CTy.
Local Open Scope string_scope.

Module CPolIRs <: POLIRS with Module Instr := CInstr.
   Module Instr := CInstr.
   Module State := CState.
   Module Ty := CTy.
   Module PolyLang := PolyLang CInstr.
   Module PolyLoop := PolyLoop CInstr.
   Module Loop := Loop CInstr.
   Parameter scop_scheduler: OpenScop -> result OpenScop.

   Definition scheduler cpol := 
      match PolyLang.to_openscop cpol with
      | Some inscop => 
         match scop_scheduler inscop with 
         | Okk outscop => PolyLang.from_openscop cpol outscop
         | Err msg => Err msg
         end
      | None => Err "Transform pol to openscop failed"
      end
   .
End CPolIRs.

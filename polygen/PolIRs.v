Require Import InstrTy.
Require Import PolyLang.
Require Import PolyLoop.
Require Import Loop.
Require Import Result.

Module Type POLIRS.

Declare Module Instr : INSTR.
Module State := Instr.State.
Module Ty := Instr.Ty.
Module PolyLang := PolyLang Instr.
Module PolyLoop := PolyLoop Instr.
Module Loop := Loop Instr.

Parameter scheduler: PolyLang.t -> result PolyLang.t.


End POLIRS.

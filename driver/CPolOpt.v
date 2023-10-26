Require Import CPolIRs.
Require Import PolOpt.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

(** The final polyhedral optimizer for CInstr*)
Module CPolOpt := PolOpt CPolIRs.

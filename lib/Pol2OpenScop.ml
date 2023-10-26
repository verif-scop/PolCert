(* open CPol *)
open OpenScop
open Camlcoq
open Top
open Exceptions
open Printf 
open CPolIRs
open CSample1

let sample_openscop = sample_scop;;
let sample_openscop' = sample_scop;; (** act as optimized openscop *)
let sample_cpol = CSample1.sample_cpol;;

let cpol_to_openscop cpol = sample_scop;;
    
let openscop_to_cpol cpol_old copenscop = sample_cpol;;



(* Require Import CPol.
Require Import COpenScop.
Require Import Result.
Require Import String.

Definition cpol_to_openscop (cpol: CPol): result COpenScop.OpenScop := 
    Err "Not implemented yet"%string.

Definition openscop_to_cpol (cpol_old: CPol) (copenscop: COpenScop.OpenScop): result CPol := 
    Err "Not implemented yet"%string. *)

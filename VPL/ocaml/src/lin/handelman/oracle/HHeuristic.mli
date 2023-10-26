(** This module defines heuristics use in the Handelman oracle. 
A heuristic aim at finding one or several products able to cancel a given monomial.
*)

open HOtypes
open HPattern
	
type t = Pneuma.t -> HPattern.t -> Pneuma.t

module AllUnderMaxDegree : sig
(** This heuristic returns every index leading to a polynomial that has a smaller degree than the input polynomial. *)
	val allUnderMaxDegree : t
end

(** The heuristic applied when every others do not match.
It is currently defined as {!val:allUnderMaxDegree}. *)
val default : t

(** This heuristic can be applied on a monomial where each variable has a degree <= 1.
It uses a linear program to determine a product of variable bounds able to cancel the monomial. *)
val powerLTOne : t

val extractEvenPowers : t

val linearMonomial : t
		
val of_pattern : t


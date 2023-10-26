(** This module defines a function per heuristic, to determine when they must be applied. *)

open HOtypes

type t = 
| Default of Poly.t
| AllUnderMaxDegree of Poly.t
| ExtractEvenPowers of Poly.Monomial.t * Index.Int.t
| LinearMonomial of Poly.Monomial.t
| Random of Poly.t
| PowerLTOne of Poly.Monomial.t
| AlreadyIn of Poly.Monomial.t

type matcher

(** matchers *)
val default : matcher
val alreadyIn : matcher
val linearMonomial : matcher
val extractEvenPowers : matcher
val powerLTOne : matcher

(** [matching_order] is a list defining the order according to which heuristics must be applied.*)
val matching_order : matcher list

(** [matching_order_nl] is a list defining the order according to which heuristics must be applied.
It must not contain matcher {!val:linearMonomial}.*)
val matching_order_nl : matcher list

(** [matching_custom m pn] returns which heuristic must be applied on the given pneuma.
It tries matchers according to the order defined in [m] and returns the first one to match. *)
val matching_custom : Pneuma.t -> matcher list -> t

(** Same as {!function:matching_rec}, where [m] is [matching_order]. *)
val matching : Pneuma.t -> t


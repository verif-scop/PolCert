(** This module contains function to call the handelman oracle.
Given an input polynomial [g] and an input polyhedron [P], the oracle computes a set of products of constraints of [p] able to cancel the nonlinear monomials of [g]. 
*)

open HOtypes

(** [oracle_custom p ph matchers] returns a couple [(l,mapP)] where:
{ul {- [l] is the list of products able to cancel nonlinear monomials of [p]}
{- [mapP] contains the mapping from elements of [l] (which are indexes) to polynomials.}}  *)
val oracle_custom: Poly.t -> 'c HPol.t -> HPattern.matcher list -> Hi.t list * MapIndexP.t

(** [oracle p ph] returns a couple [(l,mapP)] where:
{ul {- [l] is the list of products able to cancel nonlinear monomials of [p]}
{- [mapP] contains the mapping from elements of [l] (which are indexes) to polynomials.}}
It uses the default matching order of {!module:HPattern}.  *)
val oracle: Poly.t -> 'c HPol.t -> Hi.t list * MapIndexP.t

(** [oracle_hi p ph matchers] returns a list of products able to cancel nonlinear monomials of [p]. *)
val oracle_hi_custom: Poly.t -> 'c HPol.t -> HPattern.matcher list -> Hi.t list * Poly.t list

(** [oracle_hi p ph] returns a list of products able to cancel nonlinear monomials of [p]. 
	 It uses the default matching order of {!module:HPattern}. *)
val oracle_hi: Poly.t -> 'c HPol.t -> Hi.t list * Poly.t list



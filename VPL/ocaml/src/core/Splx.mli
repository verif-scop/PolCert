(** This module implements a feasibility-only simplex algorithm.
The basis for the algorithm comes from the article "Integrating simplex with DPLL(T)"
published by Bruno Dutertre and Leonardo de Moura in 2006 as
an SRI International technical report.
The interface of this module needs a fair amount of user-friendliness. 

{e Remarks}. This module works only with variables of {!module:Var.Positive}. 
Its implementation directly depends on the data structure {!module:Rtree}. *)

(**
data type for the description of bound

The [id] field records which input constraint the bound is the result of.
The [scale] field is used to generate correct certificates in case the
input constraint was of the form [2.x <= 2].
The [bv] field is the actual value of the bound of the variable.
*)
type bnd_t
= {id: int; scale: Scalar.Rat.t; bv: Scalar.Symbolic.t}

module Cs = Cstr.Rat.Positive
module Vec = Cs.Vec
module V = Vec.V

(** accessor for the [id] field of a value of type [bnd_t] *)
val get_id : bnd_t -> int

(** accessor for the [scale] field of a value of type [bnd_t] *)
val get_scale : bnd_t -> Scalar.Rat.t

(** accessor for the [bv] field of a value of type [bnd_t] *)
val get_bv : bnd_t -> Scalar.Symbolic.t

(** equality test on values of type [bnd_t]. *)
val bnd_equal : bnd_t -> bnd_t -> bool

(** equality test on values of type [bnd_t option]. *)
val obnd_equal : bnd_t option -> bnd_t option -> bool

type state_t = { v: Scalar.Symbolic.t; low: bnd_t option; up: bnd_t option }
val get_v : state_t -> Scalar.Symbolic.t
val get_low : state_t -> bnd_t option
val get_up : state_t -> bnd_t option

(** equality test on values of type [state_t]. *)
val state_equal : state_t -> state_t -> bool

module Defs : sig
(** Record definitions for the variables eliminated during preprocessing. *)

    type t
    val empty : t
    val add : V.t -> Vec.t -> t -> t
    val rm : V.t -> t -> t
    val getVars : t -> V.Set.t
    val getDef : t -> V.t -> Vec.t option
    val fold : ('a -> V.t * Vec.t -> 'a) -> 'a -> t -> 'a
    val rewrite : t -> Vec.t -> Vec.t
    val to_string : (V.t -> string) -> t -> string

end

(** The type of a simplex tableau. *)
type t = {
	mat: (Vec.t option) Rtree.t;
	state: state_t Rtree.t;
	vars : V.Set.t;
	defs : Defs.t;
	nxt: V.t
}

val get_mat : t ->  (Vec.t option) Rtree.t
val get_state: t -> state_t Rtree.t
val getVars : t -> V.Set.t
val get_nxt: t -> V.t

module Witness : sig
	(*	The type of a contradiction witness.  This is the list of the non-zero
	coefficients to apply to the linear constraints of the instance, identified
	by an index number starting from zero and incremented for each newly added
	contraint.
	It describes a linear combination of the constraints of the problem yielding a
	trivially contradictory constraint.*)
	type t = (int * Scalar.Rat.t) list
	
	(** Pretty-print a value of type [t]. *)
	val to_string : t -> string
	
	val equal : t -> t -> bool
end

type witness_t = Witness.t

type 'a mayUnsatT
= IsOk of 'a | IsUnsat of witness_t

(**
[add s (id, c)] adds contraints [c], identified by [id],
to the simplex problem [s].

[add] assumes, but does not check, that [id] uniquely identifies [c].
If the addition of [c] to the simplex problem makes it unsatisfiable,
[add] may or may not return [IsUnsat w], where [w] describes a linear
combination of the input constraints yielding a contradiction,
otherwise, the updated problem is returned.

In the current implementation, [IsUnsat] is only returned when
specifying incompatible bounds on single variables, e.g. [x < 1] and
[x > 1].
*)
val add: t -> int * Cs.t -> t mayUnsatT

(**
[addAcc] is a convenience wrapper around [add] which propagates
[IsUnsat] or performs the addition using [add] as necessary.
*)
val addAcc : t mayUnsatT -> int * Cs.t -> t mayUnsatT

(**
[mk lim l] builds a new simplex problem, composed of the constraints in [l].

Variable [lim] specifies a frame beyond which fresh variables can be
allocated, using [V.next]. Note that [lim] itself may be used as a
fresh variable. There is no possibility to change the frame after a
simplex data structure has been created using [mk]: all the constraints
ever added to the result of [mk] should have their variables "smaller"
than [lim].

[mk] is implemented in terms of [add] and has the same behaviour
regarding [IsUnsat] return values.
*)
val mk: V.t -> (int * Cs.t) list -> t mayUnsatT

(** Look for an assignment of the variables of the problem which satisfies
all the constraints.  If such an assignment is found, the last simplex
tableau is returned.  If no such assignment exist, an unsatifiability witness
is returned which describes a linear combination of the input constraints
yielding a contradiction. *)
val check : t -> t mayUnsatT

(**
convenience wrapper around [check] which propagate unsatifiability
or checks satisfiability as required
*)
val checkFromAdd : t mayUnsatT -> t mayUnsatT

(** Get an assignment of the variables which satisfies the input constraints.
Calling [getAsg] is only meaningful on a value of type [t] returned by
[check] or [checkFromAdd]. *)
val getAsg : t -> Vector.Symbolic.Positive.t

val insertBack : V.t -> t -> t

(*	Complement the bound with given integer identifier.
	If multiple bounds have this identifier, one is arbitrarily chosen.
	Assumes the current point satisfies all constraints and bounds.
*)
val compl: t -> int -> t

(*	Make the bound with given integer identifier strict. *)
val stricten: t -> int -> t mayUnsatT

(*	Remove the bound with the given integer identifier.
	If this is the only bound on the corresponding variable, project said
	variable from the constraints.
*)
val forget: t -> int -> t

(** Pretty-print an element of type [t].
The function [pr] wraps functions [prMat] and [prState]. *)
val pr: (V.t -> string) -> t -> string

(** [prMat s] pretty-prints the constraint matrix (field [mat]) of [s]. *)
val prMat: (V.t -> string) -> Vec.t option Rtree.t -> string

(** [prState s] pretty-prints the bounds and values on variables (field [state]) of [s]. *)
val prState: (V.t -> string) -> state_t Rtree.t -> string

(** Pretty-print an element of type [bnd_t option]. *)
val prBnd: bnd_t option -> string

(** Pretty-print an element of type [state_t]. *)
val prSt: state_t -> string


(**/**)
(*	The following types and functions are private, hence the leading ``_''.
	They are used for diagnostic purposes.
*)

type bck_t =
| Ok
| KoL of Scalar.Symbolic.t
| KoU of Scalar.Symbolic.t

type whatnext_t = NonBasic of V.t | UnsatSplx of witness_t

(** [mergeB st1 st2] computes the intersection of the bounds described by [st1] and [st2].
The [v] field of the result is equal to [st1.v].
If the interval resulting from the intersection is empty,
exception [Unsat w] is raised with [w] describing the offending bounds. *)

val mergeB: state_t -> state_t -> state_t

(** [setSymbolic ve st] computes the amount by which the value of one of the variables involved in [ve]
(assuming it has a unit coefficient) should be increased so that the state [st] satisfies the constraint [ve]. *)
val setSymbolic: Vec.t -> state_t Rtree.t -> Scalar.Symbolic.t

(** [fitBnd st = (d, st')] adjusts the value of the variable which state is described by [st], so that it fits its bounds.
It is assumed (but not enforced), that there is at least one possible value which fits the bounds.
The [fitBnd] function returns the new state [st'] with updated value and [d] = [st'.v - st.v]. *)

type fitBndT
= FitBnd of Scalar.Symbolic.t * state_t | BndUnsat of witness_t

val fitBnd: state_t -> fitBndT

(** [incrupdate v x m st] adjusts the value of the basic variables in [st] so that
the constraints [m] are still satisfied after a change [d] on the value of the non-basic variable [x] (new value is [x] + [d]). *)
val incrupdate: Scalar.Symbolic.t -> V.t -> (Vec.t option) Rtree.t -> state_t Rtree.t -> state_t Rtree.t

(** [pivot m xB xN] transforms that contraint matrix [m] so that
the basic variable [xB] becomes non-basic and
the non-basic variable [xN] becomes basic.
The handling of variable values to preserve the invariant is left to the caller. *)
val pivot: Vec.t option Rtree.t -> V.t -> V.t -> Vec.t option Rtree.t

val _in_bound: state_t -> bck_t

val check_loop : t -> t mayUnsatT

type choiceT
= {var : V.t; vec : Vec.t; st : state_t}

type strategyT
= Bland | Steep

type chgDirT
= HasToIncr | HasToDecr

module type Strategy
= sig

	val pickBasic : t -> choiceT option

	val pickNBasic : t -> chgDirT -> Vec.t -> whatnext_t

end

module Bland : Strategy
module Steep : Strategy

type stepT
= StepCont of t | StepSat of t | StepUnsat of witness_t

val step : strategyT -> t -> stepT

module Preprocessing : sig

    (** Compute the set of variables of the constraints input by the user
which have neither syntactic upper bound nor lower bound. *)
    val getUnboundedVars : t -> V.Set.t

    (** [findOccurence x sx] returns the basic variable of one row on which [x]
occurs with a non-null coefficient, if one exists. *)
    val findOccurence : V.t -> t -> V.t option

    (** [elim x xb sx] eliminates [x] from the tableau using the constraint which
has [xb] as a basic variable.  Note that the problem which [elim] returns is not
equivalent to [sx]. *)
    val elim : V.t -> V.t -> t -> t

    (** [presimpl sx] eliminates from [sx] the variables which are not
syntactically bounded. *)
    val presimpl : t -> t

end

val getAsgOpt : V.t -> (int * Cs.t) list -> Scalar.Symbolic.t Rtree.t option

val getPointInside_cone : Cs.Vec.V.t -> Cs.t list -> Scalar.Symbolic.t Rtree.t option

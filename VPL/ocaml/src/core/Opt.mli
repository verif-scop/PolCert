(** This module builds on {! Splx} to offer an optimizing simplex. *)

(** A value of type [progressT] describes the change that can be operated on a given quantity.
The change does not specify whether this is an increase or a decrease.
In the case of [UpTo d], the change [d] is always positive. *)
type progressT = Unbnd | UpTo of Scalar.Symbolic.t | NoChange

(** Describe the direction of a value change: increasing or decreasing. *)
type dirT = Incr | Decr

(** During the optimization, a value of type [actionT] decribes the choice on the course of actions,
based on the contents of the objective line.
[Done] means that the optimal value for the objective function is reached.
[Move (v, d, p)] means that adjusting the value of the variable [v], in direction [d],
will increase the value of the objective function.
In the latter case, the bounds on [v] limit its change according to [p]. *)
type actionT = Done | Move of (Splx.V.t * dirT * progressT)

(** At the end of each pivoting step, decide whether the optimum is reached or
progress still needs to be made. *)
type nextT = OptFinite of Scalar.Symbolic.t | OptUnbnd | GoOn of Splx.t

(** This is the result type of the optimization. *)
type optT =
  | Finite of (Splx.t * Scalar.Rat.t * Splx.witness_t) (** The optimized form can take values up to and including the given value. *)
  | Sup of (Splx.t * Scalar.Rat.t * Splx.witness_t) (** The optimized form can take values up to and excluding the given value. *)
  | Infty (** The optimized form is unbounded. *)

(**
	maximize a linear form under a set of constraints

	[max] returns either a description of the optimum for the given
	linear form or an unsatifiability witness if the constraint system
	is not satisfiable.

	The simplex tableau may be built using functions [add] or [mk], but
	[check] must not be called on it prior to calling [max] as [check]
	performs simplifications possible for satifiability checking, but not
	for optimization.
 *)
val max: Splx.t -> Splx.Vec.t -> optT Splx.mayUnsatT

(**
	convenience wrapper around [max] for direct use on the result of
	functions [add] or [mk]
 *)
val max' : Splx.t Splx.mayUnsatT -> Splx.Vec.t -> optT Splx.mayUnsatT

(** Pretty-print a value of type [progressT]. *)
val prProgress: progressT -> string

(** Pretty-print a value of type [dirT]. *)
val prDir: dirT -> string

(** Pretty-print a value of type [actionT].
The provided basis must be the one in which the non-basic variable is defined. *)
val prAction: (Splx.V.t -> string) -> actionT -> string

(** Pretty-print a value of type [nextT]. *)
val prNext: (Splx.V.t -> string) -> nextT -> string

(** Pretty-print a value of type [optT]. *)
val prOpt: optT -> string

(** The following function are internal functions which are exported for testing purposes only.
They maintain the invariant on the simplex structure,
which is that the value of all the variables should satisfy both their bounds and the constraints. *)

(** [pickNBasic z s] observes the objective line of the simplex tableau,
represented by the contraint of basic variable [z]
and decides what should be done. *)
val pickNBasic: Splx.V.t -> Splx.t -> actionT

(** [pickBasic s xN xNBnd dir] looks for the basic variable with which to pivot [xN].
The selected basic variable [xB] is the one which constrains the most the change of the value of [xN] in direction [dir].
The constraint on this change, [xNBnd1] is returned along with [xB].
The [xNBnd] argument is the constraint set on the change of the value of [xN] by the bounds of [xN].
If [xNBnd] is the most restrictive of all of the constraints imposed on the value of [xN], then [xB] = [xN]. *)
val pickBasic: Splx.t -> Splx.V.t -> progressT -> dirT -> Splx.V.t * progressT

(** [step z s] does one optimization step:
it chooses a non-basic variable which can be used to increase the value of the goal,
it chooses a basic variable with which to pivot and finally pivots.
It notices that the optimum is reached only if it is reached in [s]. *)
val step: Splx.V.t -> Splx.t -> nextT

(** [setObj s obj] sets [obj] as the linear form to optimize in [s] and
returns the corresponding problem,
along with the basic variable associated with [obj]. *)
val setObj: Splx.t -> Splx.Vec.t -> Splx.V.t * Splx.t

(** We maximize epsilon such that epsilon <= 1 and for all constraint Ci, Ci >= epsilon. *)
val getAsg : Cstr.Rat.Positive.Vec.V.t -> (int * Cstr.Rat.Positive.t) list -> Scalar.Symbolic.t Rtree.t option

val getAsg_and_value : Cstr.Rat.Positive.Vec.V.t -> (int * Cstr.Rat.Positive.t) list
    -> (Vector.Symbolic.Positive.t * Scalar.Rat.t option) option

val getAsg_raw : Cstr.Rat.Positive.t list -> Vector.Symbolic.Positive.t option

val getAsg_and_value_raw : Cstr.Rat.Positive.t list -> (Vector.Symbolic.Positive.t * Scalar.Rat.t option) option

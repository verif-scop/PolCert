
(** This is the main module of the VPL.
It defines what a polyhedron is and what operations can be done on it.
Not that there is no handling of the empty polyhedron (i.e. the bottom value):
a value of type [t] is assumed to be non-bottom and operators that may yield
an empty polyhedron have an [option] type as return value. *)

module EqSet = IneqSet.EqSet
module Cons = IneqSet.Cons
module Cert = Cons.Cert
module Cs = EqSet.Cs
module Vec = Cs.Vec
module Var = Vec.V

module Debug : DebugTypes.Type

(** The type of an abstract value.
The internal representation splits the linear constraints
into a set of equalities and a set of inequalities *)
type 'c t = {
	eqs: 'c EqSet.t;
	ineqs: 'c IneqSet.t;}

(** The polyhedron with no constraints. *)
val top: 'c t

val get_eqs : 'c t -> 'c EqSet.t
val get_ineqs : 'c t -> 'c IneqSet.t

(** The return type of the inclusion test {!incl}.
If inclusion holds, the certificate can be checked using function [check]. *)
type 'c rel_t =
| NoIncl
| Incl of 'c list

type bndT =
	| Infty
	| Open of Scalar.Rat.t
	| Closed of Scalar.Rat.t

type itvT = { low: bndT; up: bndT }

val bnd_to_string : bndT -> string

val get_low: itvT -> bndT
val get_up: itvT -> bndT

type cstT = S of Scalar.Rat.t | I of itvT

(** The description of an assignment operation.
[var] is given the value [lin] + [cst]. *)
type assign_t = {
	var: Var.t;
	lin: (Scalar.Rat.t * Var.t) list;
	cst: cstT }

val getVar: assign_t -> Var.t
val getLin: assign_t -> (Scalar.Rat.t * Var.t) list
val getCst: assign_t -> cstT


(** [equalSyn p1 p2] returns true if [p1] and [p2] are made of exactly the same constraints.
The comparison is sensitive to insertion order for equalities, but not for inequalities. *)
val equalSyn: 'c1 t -> 'c2 t -> bool

(** [mk l] builds the polyhedron representing the conjunction of constraints in [l].
If the resulting polyhedron is empty (i.e. the conjunction is unsatisfiable),
[None] is returned. *)
val mk: 'c Cert.t -> 'c Cons.t list -> 'c t option
val mkSub: 'c Cert.t -> Var.t -> 'c Cons.t list -> 'c t option

(** A value of type [meetT] represents the result of an intersection of two
sets of constraints [s1] and [s2]. Either this intersection is empty, or it is
some new set of constraints [s]. The constructor [Contrad] represents the former
possibility, where the certificate gives a proof of the intersection being empty.
A value [Added (s, (fwd, bwd))] states that [fwd] is the proof of the intersection
of [s1] and [s2] being included in [s], while [bwd] is a proof of [s] being
included in the intersection of [s1] and [s2]. *)
type 'c meetT =
	| Added of 'c t
	| Contrad of 'c

(** Pretty-printer for values of type meetPr. *)
val meetPr: 'c Cert.t -> (Var.t -> string) -> 'c meetT -> string

(** Equality t*est for values of type meetT.
Certificate equality is tested using [Cert.isEq] and
polyhedron equality is test with [isEqSyn]. *)
val meetEq: 'c meetT -> 'c meetT -> bool

(** Intersect a polyhedron with a new constraint. *)
val add: 'c Cert.t -> 'c t -> 'c Cons.t -> 'c meetT
val addSub: 'c Cert.t -> Var.t -> 'c t -> 'c Cons.t -> 'c meetT

(** Intersect a polyhedron with a list of new constraints. *)
val addM: 'c Cert.t -> 'c t -> 'c Cons.t list -> 'c meetT
val addMSub: 'c Cert.t -> Var.t -> 'c t -> 'c Cons.t list -> 'c meetT

(** Compute the intersection of two polyhedra. *)
val meet: 'c Cert.t -> 'c t -> 'c t -> 'c meetT
val meetSub: 'c Cert.t -> Var.t -> 'c t -> 'c t -> 'c meetT

(** Forget all information about a given variable [v] in a polyhedron [p].
The certificate proves that the result includes the geometric projection of the [p] with respect to [v].
The certificate can be checked using function [check]. *)
val project: 'c Cert.t -> 'c t -> Var.t -> 'c t
val projectSub: 'c Cert.t -> Var.t -> 'c t -> Var.t -> 'c t

(** Forget all information about a set of variables.
Although the result is identical to projecting the variables one by one,
heuristic choices on the projection order make [projectM] more efficient. *)
val projectM: 'c Cert.t -> 'c t -> Var.t list -> 'c t
val projectMSub: 'c Cert.t -> Var.t -> 'c t -> Var.t list -> 'c t

(** [join p1 p2] computes the convex hull [p] of [p1] and [p2].
The certificate provides the necessary arguments to show inclusion of [p1] and [p2] in [p]. *)
val join: 'c1 Cert.t -> 'c2 Cert.t -> 'c1 t -> 'c2 t -> 'c1 t * 'c2 t
val joinSub: 'c1 Cert.t -> 'c2 Cert.t -> Var.t -> 'c1 t -> 'c2 t -> 'c1 t * 'c2 t

(** [minkowski p1 p2] computes the minkowski sum [p] of [p1] and [p2]. *)
val minkowski: 'c1 Cert.t -> 'c2 Cert.t -> 'c1 t -> 'c2 t -> 'c1 t * 'c2 t
val minkowskiSub: 'c1 Cert.t -> 'c2 Cert.t -> Var.t -> 'c1 t -> 'c2 t -> 'c1 t * 'c2 t

(** Widening operator.
The result includes the two operands, although no certificate is created.
Note that [widen p1 p2] relies on [p1] being included in [p2]. *)
val widen: 'c Cert.t -> 'c t -> 'c t -> 'c t

(** [incl factory p1 p2] checks the (geometrical) inclusion of [p1] in [p2]. *)
val incl: 'c1 Cert.t -> 'c1 t -> 'c2 t -> 'c1 rel_t
val inclSub: 'c1 Cert.t -> Var.t -> 'c1 t -> 'c2 t -> 'c1 rel_t

(** [let (itv, lProof, uProof) = itvize p v] computes the bounds imposed on the linear form [v]
by the constraints of the polyhedron [p].
For each bound (upper and lower), an inclusion certificate is returned if it is finite,
allowing the prove that the returned interval is indeed correct.
[lProof] and [uProof] are the certificates for the lower and upper bounds, respectively. *)
val itvize: 'c Cert.t -> 'c t -> Vec.t -> itvT * 'c option * 'c option
val itvizeSub: 'c Cert.t -> Var.t -> 'c t -> Vec.t -> itvT * 'c option * 'c option

(** [getUpperBound p v] computes the upper bound on the linear form [v]
implied by polyhedron [p].  If the bound is finite, a certificate is
provided. *)
val getUpperBound : 'c Cert.t -> 'c t -> Vec.t -> bndT * 'c option
val getUpperBoundSub : 'c Cert.t -> Var.t -> 'c t -> Vec.t -> bndT * 'c option

(** [getLowerBound p v] computes the lower bound on the linear form [v]
implied by polyhedron [p].  If the bound is finite, a certificate is
provided. *)
val getLowerBound : 'c Cert.t -> 'c t -> Vec.t -> bndT * 'c option
val getLowerBoundSub : 'c Cert.t -> Var.t -> 'c t -> Vec.t -> bndT * 'c option

(** [rename x y p] renames variable [x] to variable [y] in polyhedron [p].
[y] must be fresh in [p]. *)
val rename: 'c Cert.t -> Var.t -> Var.t -> 'c t -> 'c t

(** This function checks that the given polyhedron satisfies the following
invariants. It returns [(true, "")] if it does and [(false, reason)] if not,
where [reason] lists the checks that have failed.
- there is no trivial constraint
- the polyhedron is not empty
- there is no redundant constraint
- invariants on the set of equalities {ul
 {- a defined variable appears with unit coefficient}
 {- a defined variable does not appear in the equalities before it}}
- invariants on the set of inequalities {ul
 {- none of the variables defined by an equality appears in an inequality}} *)
val invChk: 'c Cert.t -> 'c t -> bool * string

(** Pretty-printer for a polyhedron. *)
val to_string: (Var.t -> string) -> 'c t -> string
val to_string_ext: 'c Cert.t -> (Var.t -> string) -> 'c t -> string
val to_string_itv: (Var.t -> string) -> Vec.t -> itvT -> string
val to_string_raw: 'c t -> string
val to_string_ext_raw: 'c Cert.t -> 'c t -> string
val to_string_itv_raw: Vec.t -> itvT -> string

(** For Sage plot. *)
val plot : 'c t -> string
val plot_opt : 'c t option -> string
(*
(**/**)
type discr_t

val joinSetup: Var.t -> t -> t -> Var.t * (int -> discr_t) * t * Var.t list
*)
(* XXX: get the set of variables bound by a polyhedron *)
val varSet : 'c t -> Var.Set.t

val get_cons : 'c t -> 'c Cons.t list
val get_cstr : 'c t -> Cs.t list
val get_cstr_ineqs : 'c t -> Cs.t list
(*
val inter : 'c t -> 'c t -> 'c t option
*)
val equal : 'c1 Cert.t -> 'c2 Cert.t -> 'c1 t -> 'c2 t -> bool

val to_unit : 'c t -> unit t

(** Returns the partition into regions of the given polyhedron, according to the given normalization point.
    Certificates are lost during the process: frontiers of regions have no certificate.
*)
val get_regions_from_point : 'c Cert.t -> 'c t -> Vec.t -> unit t list

(** Returns the partition into regions of the given polyhedron.
    The normalization point is chosen using {!val:Opt.get_asg}.
    Certificates are lost during the process: frontiers of regions have no certificate.
*)
val get_regions : 'c Cert.t -> 'c t -> unit t list

(** Returns an estimation of the size of the polyhedron. *)
val size : 'c t -> Scalar.Rat.t option

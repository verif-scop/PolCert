module Debug : DebugTypes.Type
(** This module defines the type of Schweighofer products. *)

(** This is the type of Handelman indices.
For instance, [cIndex (1, 0, 3)] represents C_1^1 * C_2^0 * C_3^3. *)
type cIndex = Index.Int.t

(** This type of indices represents a product of variables.
For instance, [varIndex (1, 0, 3)] represents x_1^1 * x_2^0 * x_3^3. *)
type varIndex = Index.Int.t

(** This type defines the Farkas decomposition of a constraint.
For instance, [boundIndex (1, 0, 3)] represents 1*C_1 + 0*C_2 + 3*C_3. *)
type boundIndex = Index.Rat.t

(** Defines the type of Schweighofer products as either :
	- a Handelman product using type {!type:cIndex}
	- a product of variables bounds (each of them is represented by its Farkas decomposition using type {!type:boundIndex}) multiplied by a monomial of type {!type:varIndex}
	- a Handelman product (type {!type:cIndex}) multiplied by a monomial of type {!type:varIndex} *)
type t =
| Ci of cIndex
| VarBounds of varIndex * (boundIndex list)
| VarCi of varIndex * cIndex

val to_string : t -> string

val eq : t -> t -> bool

val is_linear : t -> bool

module Eval : sig

	val eval_Hi : t -> CstrPoly.Positive.Poly.t list -> CstrPoly.Positive.Poly.V.t list -> Q.t list -> Q.t
	val eval_poly : CstrPoly.Positive.Poly.t -> CstrPoly.Positive.Poly.V.t list -> Q.t list -> Q.t

end

module Cert : sig

	type squares = (CstrPoly.Positive.Poly.V.t * int) list

	type schweighofer = Scalar.Rat.t * (cIndex * squares * boundIndex list)

	(** [hi_to_cert n_cstrs vars coeff hi] *)
	val hi_to_cert : int -> CstrPoly.Positive.Poly.V.t list -> Scalar.Rat.t -> t -> schweighofer

    val to_string : schweighofer list -> string
end

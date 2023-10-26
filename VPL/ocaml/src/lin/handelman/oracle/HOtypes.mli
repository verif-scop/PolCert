(** This module defines datatypes used by the oracle that generates Schweighofer products used in Handelman linearization. 
*)

module CP = CstrPoly.Positive
module Poly = CP.Poly
module V = Poly.V

module Debug : DebugTypes.Type

(*
(** This module handles trace generation and printing for the oracle. *)
module HTrace : sig

	(** [enable] enables oracle trace generation, stocking them as a string list. *)
	val enable : unit -> unit
	
	(** [print_enable] enables oracle trace printing on the fly. *)
	val print_enable : unit -> unit
	
	(** [color_enable] enables the use of colors in traces IF they are printed on the fly. *)
	val color_enable : unit -> unit
	 
	(** [enable_default] enables oracle trace printing on the fly, with colors. *)
	val enable_default : unit -> unit
	
	(** If printing on the fly is enabled, [log_title s] prints the given lazy string [s] in boldface.
	Otherwise, [log_title s] stacks the string in a variable, accessible with [get]. *)
	val log_title : string Lazy.t -> unit
	   
	(** If printing on the fly is enabled, [log s] prints the given lazy string [s].
	Otherwise, [log s] stacks the string in a variable, accessible with [get]. *)
	val log : string Lazy.t -> unit
	
	(** [get] returns the current stacked traces and empties the stack. *)
	val get : unit -> string list
	
end
*)

(** This map binds things to elements of type {!type:Poly.t}. *)
module MapP : Map.S with type key = Poly.t

(** This module associates in a map a list of {!type:Hi.t} to a polynomial. It is used to remember what products were used to cancel a given polynomial. *)
module MapPolyHi : sig
	
	type t = Hi.t list MapP.t
	
	val to_string : t -> string

	(** [memMonom m map] returns [true] if [map] contains a binding to a polynomial that contains monomial [m]. *)
	val memMonom : Poly.MonomialBasis.t -> t -> bool
	
	(** [memMonomSigned m map] returns [true] if [map] contains a binding to a polynomial that contains monomial [m] and a coefficient of the same sign. *)
	val memMonomSigned : Poly.Monomial.t -> t -> bool
	
	val merge : t -> t -> t
end

(** This map binds things to elements of type {!type:Index.Int.t}. *)
module MapI = IndexBuild.MapI

(** This module associates in a map a polynomial to a Handelman index. *)
module MapIndexP : sig

	type t
	
	(** [of_polyhedron l] creates an empty map and fill it with constraints of the polyhedron given as a list of polynomials. *)
	val of_polyhedron : Poly.t list -> t
	
	val to_string : t -> string

	(** [poly_to_deg_max p l] returns an index [ind] whose ith component is the maximum power in [p] of the ith variable in [l]. 
	For instance, {ul 
		{- [poly_to_deg_max (x^2y - 2x^3 + y^2 + xz^2) [x;z] = (3,2)]}
		{- [poly_to_dex_max (x^2z - z^3) [x;y;z] = (2,0,3)]}} *)
	val poly_to_deg_max : Poly.t -> Poly.V.t list -> Index.Int.t
	
	(** *)
	val gen_mono : (Poly.V.t * int) list -> Poly.MonomialBasis.t list
	
	(** [poly_to_deg p ml] returns an index where the ith value is equal to 1 if [ml(i)] is a monomial of polynomial [p]. *)		
	val poly_to_deg : Poly.t -> Poly.MonomialBasis.t list -> Index.Int.t
	
	(** [to_deg ind map ml] returns the index of the polynomial [map(ind)] as defined in {!poly_to_deg}.
	@raise Not_found if [ind] has no binding in [map] *)
	val to_deg : Index.Int.t -> t -> Poly.MonomialBasis.t list -> Index.Int.t
	
	(** [get ind mapIP mapI] returns the polynomial corresponding to index [ind] in map [mapIP].
	If [ind] has no binding in [mapIP], maps are updated. *)
	val get : Index.Int.t -> t -> IndexBuild.Map.t -> (Poly.t * t * IndexBuild.Map.t)
end

(** This map binds things to elements of type {!type:Poly.V.t}. *)
module MapV : Map.S with type key = Poly.V.t

(** This module defines the maps used in {!module:HLP}. They gather information about variable bounds. *)
module LPMaps : sig
	
	type t = Upper | Lower
	
	(** It associates a variable [v] to a pair of option booleans [(b1,b2)]. 
	[b1] = [Some true] (resp. [b2] = [Some true]) means that [v] has a lower (resp. upper) bound.
	[b1] = [Some false] (resp. [b2] = [Some false]) means that [v] has no lower (resp. upper) bound.
	[b1] = [None] (resp. [b2] = [None]) means that we don't have information on [v]'s lower (resp. upper) bound. *)
	type mapDetBound = (bool option * bool option) MapV.t
	
	(** It associates a variable to a pair of option {!type:Hi.boundIndex}. *)
	type mapBound = (Hi.boundIndex option * Hi.boundIndex option)  MapV.t
	
	type bounds = {mapDB : mapDetBound ; mapB : mapBound}
	
	(** [init pl vl] initializes maps with bounds that appear syntactically in [pl]. *)
	val init : Poly.t list -> Poly.V.t list -> bounds
	
	(** [hasSup v mapDB] returns 0 if [v] has no upper bound in [mapDB], 1 otherwise. *)
	val hasSup : Poly.V.t -> mapDetBound -> Q.t
	
	(** [hasInf v mapDB] returns 0 if [v] has no lower bound in [mapDB], 1 otherwise. *)
	val hasInf : Poly.V.t -> mapDetBound -> Q.t
	
	(** [detSup v mapDB] returns 1 if [v] has an upper bound in [mapDB], 0 otherwise. *)
	val detSup : Poly.V.t -> mapDetBound -> Q.t
	
	(** [detInf v mapDB] returns 1 if [v] has a lower bound in [mapDB], 0 otherwise. *)
	val detInf : Poly.V.t -> mapDetBound -> Q.t
	
	val mapDB_to_string : mapDetBound -> string

	val mapB_to_string : mapBound -> string
	
	(** [updateMapDB mapDB v value bound] binds in [mapDB] the upper bound of variable [v] to [value] if [upper] = [true].
	Otherwise, it binds the lower bound of variable [v] to [value]. *)
	val updateMapDB : mapDetBound -> Poly.V.t -> bool -> t -> mapDetBound

	(** [updateMapB mapB v value bound] binds in [mapB] the upper bound of variable [v] to [value] if [upper] = [true].
	Otherwise, it binds the lower bound of variable [v] to [value]. *)
	val updateMapB : mapBound -> Poly.V.t -> Hi.boundIndex -> t -> mapBound
	
end

(** This module defines the main functions used by the Handelman oracle.
The sacred pneuma is the exhalation emerging from the cleft where the Pythia was sitting. *)
module Pneuma : sig
	
	type t = {
	p : Poly.t; (** polynomial to linearize*)
	vl : Poly.V.t list; (** variables appearing in p and ph *)
	mapP : MapPolyHi.t; 
	mapIP : MapIndexP.t;
	mapI : IndexBuild.Map.t;
	ph : Poly.t list; (** constraints of the input polyhedron, represented as polynomials.
		Polynomial [p] represented constraint [p >= 0]. *)
	sx : Splx.t;
	lp : LPMaps.bounds}
	
	val to_string : t -> string
	
	val neg_poly : CstrPoly.Positive.t -> Poly.t list
	
	(** [init p ph] initializes a {!type Pneuma.t} with polynomial [p], and a polyhedron [ph]. *)
	val init : Poly.t -> 'c HPol.t -> t
	
	(** [len pn] returns the number of constraints of the input polyhedron. *)
	val n_cstrs : t -> int
	
	(** [compute ind vl] returns [vl(0)^(ind(0)) * ... * vl(n)^(ind(n))]. *)
	val computeVarIndex : Index.Int.t -> Poly.V.t list -> Poly.t
	
	(** [hi_to_poly hi pn]  returns the polynomial equal to [hi] and updates maps in [pn]. *)
	val hi_to_poly : Hi.t -> t -> Poly.t * MapIndexP.t * IndexBuild.Map.t
end

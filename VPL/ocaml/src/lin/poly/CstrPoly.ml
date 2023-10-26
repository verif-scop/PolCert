type cmpT = Cstr.cmpT

module type Type = sig
	module Cs : Cstr.Rat.Type
	module Poly : Poly.Type with module Vec = Cs.Vec

	(** Represents polynomial expression [p typ 0]. *)
	type t = {
		typ : cmpT; (** the comparison operator *)
		p: Poly.t; (** the polynomial *)
	}
	
	val to_string : t -> string
	
	(** [mk typ poly] builds the linear constraint [p typ 0]. *)
	val mk: cmpT -> Poly.t -> t
	
	(** [eq p] builds the equality [p = 0] *)
	val eq: Poly.t -> t

	(** [le p] builds the equality [p <= 0] *)
	val le: Poly.t -> t
	
	(** [lt p] builds the equality [p < 0] *)
	val lt: Poly.t -> t
	
	val compl : t -> t
		
	(** [empty] represents 0 = 0*)
	val empty : t
	 
	(** [equal c1 c2] checks that the two polynomials within constraints are syntactically equal. *)
	val equal: t -> t -> bool
	
	(** syntaxic comparison *)
	val cmp : t -> t -> int
	val compare : t -> t -> int
	
	val toCstr : t -> Cs.t
	
	val ofCstr : Cs.t -> t
	
	(** Separates the affine constraints from the given list of polynomial constraints. *)
	val partition_affine : t list -> (Cs.t list * t list)
end

module CstrPoly (Cs : Cstr.Rat.Type) = struct
	module Cs = Cs
	module Poly = Poly.Poly(Cs.Vec)
	type t = {
		typ : cmpT;
		p: Poly.t;
	}
	
	let to_string : t -> string
		= fun cp ->
		Printf.sprintf "%s %s 0"
			(Poly.to_string cp.p) 
			(match cp.typ with
			| Cstr.Eq -> " = "
			| Cstr.Le -> " <= "
			| Cstr.Lt -> " < ")
	
	let mk : cmpT -> Poly.t -> t
		= fun typ p -> 
		{p = p ; typ = typ}
	
	let eq : Poly.t -> t
		= fun p ->
		{p = p ; typ = Cstr.Eq}
		
	let le : Poly.t -> t
		= fun p ->
		{p = p ; typ = Cstr.Le}
	
	let lt : Poly.t -> t
		= fun p ->
		{p = p ; typ = Cstr.Lt}
	
	let compl : t -> t
		= fun c ->
		match c.typ with
		| Cstr.Eq -> invalid_arg "CstrPoly.compl"
		| Cstr.Le -> { typ = Cstr.Lt; p = Poly.neg c.p }
		| Cstr.Lt -> { typ = Cstr.Le; p = Poly.neg c.p }
		
	let empty : t 
		= eq Poly.z 
		
	let equal: t -> t -> bool
		= fun cp1 cp2 ->
		cp1.typ = cp2.typ && Poly.equal cp1.p cp2.p
		
	let cmp : t -> t -> int
		= fun cp1 cp2 ->
		match (cp1.typ,cp2.typ) with
		| (Cstr.Eq,Cstr.Le) | (Cstr.Le,Cstr.Lt) | (Cstr.Eq,Cstr.Lt) -> -1
		| (Cstr.Le,Cstr.Eq) | (Cstr.Lt,Cstr.Le) | (Cstr.Lt,Cstr.Eq) -> 1
		| (_,_) -> Poly.compare cp1.p cp2.p
	
	let compare = cmp
	
	let toCstr : t -> Cs.t
		= fun cp ->
		let (vec,cste) = Poly.toCstr cp.p in
		Cs.mk2 cp.typ vec (Scalar.Rat.neg cste)
	
	let ofCstr : Cs.t -> t
		= fun c ->
		let p = Poly.ofCstr c.Cs.v (Scalar.Rat.neg c.Cs.c) in
		mk c.Cs.typ p
	
	let partition_affine : t list -> (Cs.t list * t list)
		= fun polys ->
		let (affs, ps) = List.partition (fun p -> Poly.is_affine p.p) polys in
		(List.map toCstr affs, ps)
end

module Positive = CstrPoly(Pol.Cs)

module String = CstrPoly(Cstr.Rat.String)

module type Type = sig
	module Cs : Cstr.Rat.Type
	module Poly : Poly.Rat.Type
	
	type t
	  = {lin : Tableau.Vector.t; cst : Scalar.Rat.t}
	
	val empty : t
	
	(** Get the linear part of the parametric coefficient *)
	val getLin : t -> Tableau.Vector.t

	(** Get the constant part of the parametric coefficient *)
	val getCst : t -> Scalar.Rat.t

	(** Equality predicate for two parametric coefficients *)
	val equal : t -> t -> bool

	(** Tests if the given parametric coefficient is null. *)
	val is_zero : t -> bool
	
	(** [pr paramPr c] pretty-prints parametric coefficient [c]
	using [paramPr] to get a string representation of the parameters. *)
	val pr : (int -> string) -> t -> string

	(** default pretty-printer for parameters *)
	val paramDfltPr : int -> string

	(** pretty-printer for [t] with default pretty-printing for parameters *)
	val to_string : t -> string

	(** [mk l a] builds a parametric coefficient.
	[l] is the list of coefficients of the parameters, in order.
	[a] is the constant part of the parametric coefficient. *)
	val mk : Scalar.Rat.t list -> Scalar.Rat.t -> t

	(** [mkSparse n l a] builds a parametric coefficient from a sparse representation.
	[n] is the number of parameters, numbered from [0] to [n - 1],
	[l] is the list of coefficients of the parameters and
	[a] is the constant part of the parametric coefficients.
	Parameters for which there is no coefficient in [l] have zero coefficient. *)
	val mkSparse : int -> (int * Scalar.Rat.t) list -> Scalar.Rat.t -> t

	(** [mkCst a] is a short-hand for [mkSparse 0 [] a]. *)
	val mkCst : Scalar.Rat.t -> t

	(** [ofPoly tr n p] builds a parametric coefficient out of a polynomial.
	[tr] handles the mapping between variables and parameter indices.
	If [p] is not an affine expression, [Invalid_arg] is raised. *)
	val ofPoly : (Cs.Vec.V.t -> int) -> int -> Poly.t -> t

	(** [toPoly tr c] builds a value of type [PolyQ.t] from a parametric coefficient.
	[tr] is the mapping functions from the indices of the parameters to variables. *)
	val toPoly : (int -> Cs.Vec.V.t) -> t -> Poly.t

	type signT
	  = LT0 | LE0 | GT0 | GE0 | EQ0

	val to_cstr : (int -> Cs.Vec.V.t) -> signT -> t -> Cs.t

	(** Add two parametric coefficients.
	[add] raises [Invalid_argument] if the two coefficients don't have the same size. *)
	val add : t -> t -> t

	(** Multiply a parametric coefficient by a scalar. *)
	val mul : Scalar.Rat.t -> t -> t

	(** [is_constant c] returns true is [c] does not depend on any parameter. *)
	val is_constant : t -> bool

	(** [is_constant c] returns true is [c] has value zero for all parameters value. *)
	val is_zero : t -> bool

	(** [nParams c] returns the number of parameters appearing in [c]. *)
	val nParams : t -> int

	(** [eval c f] computes the value of the coefficient [c] when the value for
	the parameters are chosen according to [f]. *)
	val eval : t -> (int -> Q.t) -> Q.t

	(** [eval2 c f] computes the value of the coefficient [c] when the value for
	the parameters are chosen according to [f]. *)
	val eval2 : t -> (int -> Scalar.Symbolic.t) -> Scalar.Symbolic.t
end

module ParamCoeff (Cs : Cstr.Rat.Type) = struct
	module Cs = Cs
	module Poly = Poly.Rat.Poly(Cs.Vec)
	
	type t
	  = {lin : Tableau.Vector.t; cst : Scalar.Rat.t}
	
	let empty : t
		= {lin = [] ; cst = Scalar.Rat.z}
	
	let getLin : t -> Tableau.Vector.t
	  = fun c -> c.lin

	let getCst : t -> Scalar.Rat.t
	  = fun c -> c.cst

	let equal : t -> t -> bool
	  = fun c c' ->
	  if not (Scalar.Rat.equal c.cst c'.cst) then false
	  else if List.length c.lin <> List.length c'.lin then false
	  else List.for_all2 Scalar.Rat.equal c.lin c'.lin

	let pr : (int -> string) -> t -> string
	  = fun paramPr c ->
	  let s =
		 List.mapi (fun i a -> (i, a)) c.lin
		 |> List.filter (fun (_, a) -> not(Scalar.Rat.isZ a))
		 |> List.map (fun (i, a) -> Printf.sprintf "%s * %s" (Scalar.Rat.to_string a) (paramPr i))
		 |> String.concat " + "
	  in
	  if not (Scalar.Rat.well_formed c.cst) then
		 if s = "" then "0"
		 else s
	  else
		 let cs = Scalar.Rat.to_string c.cst in
		 if s = "" then cs
		 else Printf.sprintf "%s + %s" s cs

	let paramDfltPr : int -> string
	  = fun i -> "p" ^ Stdlib.string_of_int i

	let to_string : t -> string
	  = fun c -> pr paramDfltPr c

	let mk : Scalar.Rat.t list -> Scalar.Rat.t -> t
	  = fun l b -> {lin = l; cst = b}

	let mkSparse : int -> (int * Scalar.Rat.t) list -> Scalar.Rat.t -> t
	  = let rec fill : int -> int -> (int * Scalar.Rat.t) list -> Tableau.Vector.t
		   = fun n i ->
		   function
		   | [] -> if i < n then Scalar.Rat.z :: fill n (i + 1) [] else []
		   | ((x, a) :: l') as l ->
		 if n <= i || x < i then Stdlib.invalid_arg "Tableau.ParamCoeff.mk"
		 else if x = i then a :: fill n (i + 1) l'
		 else Scalar.Rat.z :: fill n (i + 1) l
		 in
		 fun n l a ->
		 {lin = List.sort (fun (i, _) (i', _) -> Stdlib.compare i i') l |> fill n 0;
		  cst = a
		 }

	let mkCst : Scalar.Rat.t -> t
	  = fun a -> mkSparse 0 [] a

	let ofPoly : (Cs.Vec.V.t -> int) -> int -> Poly.t -> t
	  = fun tr n p ->
	  let (cst, lin) = List.partition
			(function (m, _) when Poly.MonomialBasis.equal m Poly.MonomialBasis.null -> true
			| _ -> false)
			(List.map Poly.Monomial.data (Poly.data p))
	  in
	  let lin' = List.map
			    (function 
			    	 (m, a) when Poly.MonomialBasis.data m |> List.length = 1 -> 
			    	 	let x = Poly.MonomialBasis.data m |> List.hd in (tr x, a)
				    (*| (_ :: _ :: _, _)
				    | ([], _) -> Stdlib.invalid_arg "Tableau.ParamCoeff.ofPolyQ")*)
				    | (_ , _) -> Stdlib.invalid_arg "Tableau.ParamCoeff.ofPolyQ")
			    lin
	  in
	  match cst with
	  | _ :: _ :: _ -> Stdlib.failwith "Tableau.ParamCoeff.ofPolyQ"
	  | [] -> mkSparse n lin' Scalar.Rat.z
	  | [_, cst'] -> mkSparse n lin' cst'

	let toPoly : (int -> Cs.Vec.V.t) -> t -> Poly.t
	  = fun tr c -> Poly.mk_cste (List.mapi (fun i a -> ([tr i],a)) c.lin |> Poly.mk2) c.cst

	type signT
	  = LT0 | LE0 | GT0 | GE0 | EQ0

	let to_cstr : (int -> Cs.Vec.V.t) -> signT -> t -> Cs.t
		= fun to_vpl sign c ->
		let lin = List.mapi (fun i a -> (a,to_vpl i)) c.lin in
		let cst = c.cst in
		match sign with
		| LT0 -> Cs.lt lin (Cs.Vec.Coeff.neg cst)
		| LE0 -> Cs.le lin (Cs.Vec.Coeff.neg cst)
		| GT0 -> Cs.lt (List.map (fun (a, x) -> (Cs.Vec.Coeff.neg a, x)) lin) cst
		| GE0 -> Cs.le (List.map (fun (a, x) -> (Cs.Vec.Coeff.neg a, x)) lin) cst
		| EQ0 -> Cs.eq lin (Cs.Vec.Coeff.neg cst)


	let add : t -> t -> t
	  = fun c c' ->
	  try
		 {lin = List.map2 Scalar.Rat.add c.lin c'.lin; cst = Scalar.Rat.add c.cst c'.cst}
	  with Invalid_argument _ -> Stdlib.invalid_arg "Tableau.ParamCoeff.add"

	let mul : Scalar.Rat.t -> t -> t
	  = fun a c ->
	  {lin = List.map (Scalar.Rat.mul a) c.lin; cst = Scalar.Rat.mul a c.cst}

	let is_constant : t -> bool
	  = fun c -> List.for_all (Scalar.Rat.equal Scalar.Rat.z) c.lin

	let is_zero : t -> bool
	  = fun c -> is_constant c && Scalar.Rat.equal Scalar.Rat.z c.cst

	let nParams : t -> int
	  = fun c -> List.length c.lin

	let eval : t -> (int -> Scalar.Rat.t) -> Scalar.Rat.t
	=	fun c f ->
		List.fold_left (fun (i, v) c -> (i + 1, Scalar.Rat.add v (Scalar.Rat.mul c (f i))))
			(0, c.cst) c.lin
		|> Stdlib.snd

	let eval2 : t -> (int -> Scalar.Symbolic.t) -> Scalar.Symbolic.t
	=	fun c f ->
		List.fold_left (fun (i, v) c -> (i + 1, Scalar.Symbolic.add v (Scalar.Symbolic.mulr c (f i))))
			(0, c.cst |> Scalar.Symbolic.ofRat) c.lin
		|> Stdlib.snd
end

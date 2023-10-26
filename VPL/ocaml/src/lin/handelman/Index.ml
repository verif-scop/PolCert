(** This module type defines the type of indexes depending on a type of values. 
An index is a list of nonnegative elements. *)

module type Type = sig
	
	type coeff
	type t
	
	(** [init n] returns an index of length [n] filled with zeros. *)
	val init : int -> t
	
	(** [len ind] returns the length of index [ind]. *)
	val len : t -> int
	
	(** [is_nonnegative ind] returns true if every element of index [ind] is nonnegative. *)
	val is_nonnegative : t -> bool
	
	(** [well_formed ind] returns [true] if ind is well formed, [false] otherwise. *)
	val well_formed : t -> bool
	
	(** [mk l] builds an index from the coefficient list [l].
	@raise Invalid_argument if [l] contains negative elements. *)
	val mk : coeff list -> t
	
	(** [unitary i len] returns an index of length [len], whose value is 1 at index [i] and 0 otherwise. *)	
	val unitary : int -> int -> t
	
	(** [is_pred ind1 ind2] returns [true] if [ind1(j)] <= [ind2(j)] for all 0 <= j <= len(ind1). 
	@raise Invalid_argument if [ind1] and [ind2] have different length. *)
	val is_pred : t -> t -> bool
	
	(** [data ind] returns [ind]'s coefficients. *)
	val data : t -> coeff list
	
	(** [sum ind] returns the sum of all elements of [ind]. *)
	val sum : t -> coeff
	
	(** [set ind i c] returns an index equal to [ind], with the [i]th coefficient equals to [c]. *)
	val set : t -> int -> coeff -> t
	
	(** [get ind i] returns the [i]th coefficient of index [ind]. *)
	val get : t -> int -> coeff
	
	(** [incr ind i] returns and index equal to [ind] such that [i]th coefficient equals to [ind(i)]+1. *)
	val incr : t -> int -> t
	
	(** [decr ind i] returns and index equal to [ind] such that [i]th coefficient equals to [ind(i)]-1. *)
	val decr : t -> int -> t
	
	(** [add ind1 ind2] returns an index such that the ith coefficient equals to [ind1(i)] + [ind2(i)]. *)
	val add : t -> t -> t

	(** [sumI il] computes the sum of all elements in [il].
		@raise Invalid_argument if [l] is empty. *)
	val sumI : t list -> t
		
	(** [sub ind1 ind2] returns an index such that the ith coefficient equals to [ind1(i)] - [ind2(i)]. *)	
	val sub : t -> t -> t
	
	(** [equal ind1 ind2] returns [true] if for all i [ind1(i)] = [ind2(i)], [false] otherwise. *)
	val equal : t -> t -> bool
	
	(** [is_null ind] returns [true] if for all i [ind(i)] = 0, [false] otherwise. *)
	val is_null : t -> bool
	
	(** [first_positive ind] returns the place of the first strictly positive coefficient. 
	@raise Not_found if there is no such coefficient. *)	
	val first_positive : t -> int

	val to_string : t -> string

	(** [compare ind1 ind2] returns a positive integer if [ind1] > [ind2] ({i w.r.t.} lexicographic order), a negative one if [ind1] < [ind2], 0 otherwise. *)	
	val compare : t -> t -> int
	
	(** [le ind1 ind2] returns [true] if [ind1] <= [ind2] ({i w.r.t} elementwise order), [false] otherwise. *)
	val le : t -> t -> bool
	
	(** [le_nl ind1 ind2] returns [true] if [ind1] <= [ind2] ({i w.r.t} elementwise order), [false] otherwise.
	It ignores coefficients that are equal to one. *)
	val le_nl : t -> t -> bool
	
	(** [is_unitary ind] returns [true] if [ind] contains a single one, and every other coefficient is null, [false] otherwise. *)						
	val is_unitary : t -> bool
	 
	(** [one_coeff_nn ind] returns [true] if [ind] contains a single nonnull coefficient, [false] otherwise. *)		
	val one_coeff_nn : t -> bool
		
end

(** This module defines the type of Scalar used as coefficients in Indexes *)
module type Scalar = sig
	type t
	val z : t
	val u : t
	val negU: t
	val add : t -> t -> t
	val mul: t -> t -> t
	val to_string: t -> string
	val of_string: string -> t
	val le : t -> t -> bool
	val lt : t -> t -> bool
	val equal: t -> t -> bool
end

module Index (Coeff : Scalar) = 
	struct
	
	type coeff = Coeff.t
	type t = coeff list
	
	let (init : int -> t)
		= fun len ->
		List.map (fun i -> Coeff.z) (Misc.range 0 len)
	
	let (len : t -> int)
		= fun i ->
		List.length i
	
	let (is_nonnegative : t -> bool)
		= fun i ->
		List.for_all (fun j -> Coeff.le Coeff.z j) i
	
	let (well_formed : t -> bool)
		= fun i -> is_nonnegative i
	
	let (mk : coeff list -> t)
		= fun l -> 
		if is_nonnegative l then l
		else Stdlib.invalid_arg "IndexC.mk : coefficients are not nonnegative"
		
	let (unitary : int -> int -> t)
		= fun i len ->
		List.map (fun j -> if i = j then Coeff.u else Coeff.z) (Misc.range 0 len)
		
	let (is_pred : t -> t -> bool)
		= fun i1 i2 ->
		List.for_all2 (fun j1 j2 -> Coeff.le j1 j2) i1 i2
	
	let (data : t -> coeff list)
		= fun ind -> ind
	
	let (sum : t -> Coeff.t)
		= fun i -> List.fold_left (fun r j -> Coeff.add r j) Coeff.z i
	
	let (set : t -> int -> Coeff.t -> t)
		= fun ind j c ->
		List.mapi (fun i v -> if i = j then c else v) ind
		
	let (get : t -> int -> Coeff.t)
		= fun i j ->
		List.nth i j
		
	let (incr : t -> int -> t)
		= fun i j -> 
		List.mapi (fun k v -> if k = j then Coeff.add v Coeff.u else v) i
	
	let (decr : t -> int -> t)
		= fun i j -> 
		List.mapi (fun k v -> if k = j then Coeff.add v Coeff.negU else v) i
		
	let (add : t -> t -> t)
		= fun i1 i2 -> 
		List.map2 (fun j1 j2 -> Coeff.add j1 j2) i1 i2
	
	let (sumI : t list -> t)
		= fun il ->
		try 
			let dim = len (List.hd il) in
			List.fold_left
				(fun res i -> add res i)
				(init dim)
				il
		with _ -> Stdlib.invalid_arg "Index.sum : empty input list" 		
				
	let (sub : t -> t -> t)
		= fun i1 i2 -> 
		List.map2 (fun j1 j2 -> Coeff.add j1 (Coeff.mul j2 Coeff.negU)) i1 i2
	
	let (equal : t -> t -> bool)
		= fun i1 i2 ->
		List.for_all2 (fun j1 j2 -> Coeff.equal j1 j2 ) i1 i2
	
	let (is_null : t -> bool)
		= fun i ->
		List.for_all (fun j -> Coeff.equal j Coeff.z) i
		
	let (first_positive : t -> int)
		= fun id ->
		Misc.findi (fun i -> Coeff.lt Coeff.z (get id i)) (Misc.range 0 (len id))
		
	let (to_string : t -> string)
		= fun i ->
		Printf.sprintf "(%s)" (String.concat ";" (List.map (fun j -> Coeff.to_string j) i))
	
	let rec (compare : t -> t -> int)
		= fun i1 i2 -> 
		match (i1,i2) with
			| ([],[]) -> 0
			| (_,[]) -> 1
			| ([],_) -> -1
			| (j1::tl1, j2::tl2) -> let x = Stdlib.compare j1 j2 in
			match x with
				| 0 -> compare tl1 tl2
				| _ -> x

	let (le : t -> t -> bool)
		= fun i1 i2 -> 
		List.for_all2 (fun j1 j2 -> Coeff.le j1 j2) i1 i2

	let (le_nl : t -> t -> bool)
		= fun i1 i2 -> 
		List.for_all2 (fun j1 j2 -> Coeff.le j1 Coeff.u || Coeff.le j1 j2) i1 i2
							
	let (is_unitary : t -> bool)
		= fun i ->
		let l = List.filter (fun j -> not(Coeff.equal j Coeff.z)) i in
		List.length l = 1 && List.find (fun j -> not( Coeff.equal j Coeff.z)) i = Coeff.u
	
	let (one_coeff_nn : t -> bool)
		= fun i ->
		let l = List.filter (fun j -> not(Coeff.equal j Coeff.z)) i in
		List.length l = 1
		
end

(** Type of integers scalars. *)
module ScalarInt = struct
	type t = int
	let z = 0
	let u = 1
	let negU = -1
	let add = (+)
	let mul = ( * )
	let le = ( <= )
	let lt = ( < )
	let to_string = string_of_int
	let of_string = int_of_string
	let equal = ( = )
end

(** Type of indexes where coefficient type is {!type:ScalarInt.t}. *)
module Int = struct
	include Index (ScalarInt)
	
	(** [value ind] returns the euclidian norm of index [ind]. *)
	let (value : t -> float)
		= fun i -> sqrt (List.fold_left (fun f j -> f +. float_of_int (j*j)) 0.0 i)
end

(** Type of indexes where coefficient type is {!type:SxPoly.ScalarQ.t}. *)
module Rat = struct
	include Index (struct include Scalar.Rat let of_string = Q.of_string end)
end
	
	

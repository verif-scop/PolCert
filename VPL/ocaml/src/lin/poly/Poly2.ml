(** This module defines the type of polynomials used in the Handelman linearization *)


(** This module type defines the type of polynomials depending on the type of coefficients and variables*)
module type Type = sig
	module Vec : Vector.Type
   module Coeff = Vec.Coeff
	module V = Vec.V
	
	(** MonomialBasis represents the list of variables of a monomial *)
	module MonomialBasis : sig 
		type t
		
		(** [to_string_param m s] returns monomialBasis [m] as a string where variables (which are integers) are prefixed by [s] *)
		val to_string_param : t -> string -> string
		
		(** [to_string m] returns monomialBasis [m] as a string where variables (which are integers) are prefixed by "x" *)
		val to_string : t -> string
		
		(** [compare m1 m2] uses lexicographic order to return 0 if [m1] = [m2], a negative integer if [m1] < [m2] and a positive one otherwise *)
		val compare : t -> t -> int
		
		(** [equal m1 m2] returns [true] if [m1] = [m2], [false] otherwise *)
		val equal : t -> t -> bool
		
		(** [rename m x y] renames each occurency of [x] in [m] by [y]*)
		val rename : t -> V.t -> V.t -> t
		
		(** [eval m v] evaluates monomialBasis [m], replacing each variable with its value in function [v] *)
		val eval : t -> (V.t -> Coeff.t) -> Coeff.t
		
		val mk : (V.t * int) list -> t
		
		val data : t -> (V.t * int) list
		
		val mk_list : V.t list -> t
		
		val data_list : t -> V.t list
		
		val null : t
	end
	
	(** Monomial represents a monomial as a couple of a monomialBasis and a coefficient *)
	module Monomial : sig
		type t

		val to_string : t -> string
		
		(** [compare x y] returns 0 if [x] is equal to [y], a negative integer if [x] is smaller than [y]
		Use this function to sort the monomials in a polynomial
		This function do NOT compare the monomial coefficients *)
		val compare : t -> t -> int
		
		(** [monomial_equal (m1,c1) (m2,c2)] returns true if monomials [(m1,c1)] and [(m2,c2)] are equal *)
		val equal : t -> t -> bool		

		(** [mk m c] builds a monomial from monomialBasis [m] and coefficient [c] *)
		val mk : MonomialBasis.t -> Coeff.t -> t
		
		(** [mk2 m c] builds a monomial from a list of variables * exposant and coefficient [c] *)
		val mk2 : (V.t * int) list -> Coeff.t -> t
		
		(** [mk2 m c] builds a monomial from V.t list [m] and coefficient [c] *)
		val mk_list : V.t list -> Coeff.t -> t
		
		val data : t -> MonomialBasis.t * Coeff.t
		
		(** [mul m1 m2] returns the monomial equal to [m1 * m2] *)
		val mul : t -> t -> t

		(** [isLinear m] returns true if the degree of [m] is at most one.
		[isLinear] assumes [m] is in canonical form. *)
		val isLinear : t -> bool
		
		(** [eval m v] returns a coefficient which is the evaluation of monomial [m], where each variable is replaced by its value in function [v] *)
		val eval : t -> (V.t -> Coeff.t) -> Coeff.t
		
		(** [eval_partial m v] returns a monomial, which is the evaluation of monomial [m] where each variable is replaced by its value in function [v]. If a variable has no value in [v], it remains in the result. *)
		val eval_partial : t -> (V.t -> Coeff.t option) -> t
	end
	
	type t
	
	(** [compare x y] returns 0 if [x] is equal to [y], a negative integer if [x] is smaller than [y], a positive on otherwise *)
	val compare : t -> t -> int
			
	val to_string : t -> string
	
	(** [mk l] builds a polynomial from the {!type:Monomial.t} list [l] *)
	val mk : Monomial.t list -> t 
	
	(** [mk2 l] builds a polynomial from the list of V.t * Coeff.t [l] *)
	val mk2 : ((V.t * int) list * Coeff.t) list -> t
	
	(** [mk_list l] builds a polynomial from the list of V.t * Coeff.t [l] *)
	val mk_list : (V.t list * Coeff.t) list -> t
	
	val mk_cste : t -> Coeff.t -> t
	
	(** [mk2_cste l c] adds coefficient [c] to the list of V.t * Coeff.t [l] *)
	val mk2_cste : ((V.t * int) list * Coeff.t) list -> Coeff.t -> t

	(** [mk2_cste_list l c] adds coefficient [c] to the list of V.t * Coeff.t [l] *)
	val mk_cste_list : (V.t list * Coeff.t) list -> Coeff.t -> t
	
	(** [data p] returns the polynomial [p] as a {!type:Monomial.t} list *)
	val data : t -> Monomial.t list
	 
	(** [data2 p] returns the polynomial [p] as a list of V.t * Coeff.t *)
	val data2 : t -> ((V.t * int) list * Coeff.t) list
	
	(** [data_list p] returns the polynomial [p] as a list of V.t * Coeff.t *)
	val data_list : t -> (V.t list * Coeff.t) list
	
	(** [cste c] returns the constant polynomial [c] *)
	val cste : Coeff.t -> t
	
	(** [z] is the null polynomial *)
	val z : t
	
	(** [u] is the constant polynomial equal to one *)
	val u : t
	
	(** [negU] is the constant polynomial equal to minus_one *)
	val negU : t
	
	(** [is_constant p] returns true if [p] is constant *)
	val is_constant : t -> bool
	
	(** [isZ p] returns true if [p] is null *)
	val isZ : t -> bool

	(** [is_affine p] returns true if [p] is an affine expression.
	[is_affine] assumes that [p] is in canonical form. *)
	val is_affine : t -> bool
	
	(** [equal p1 p2] returns [true] is [p1 = p2], [false] otherwise *)
	val equal : t -> t -> bool
	
	(** [add p1 p2] returns the polynomial equal to [p1 + p2] *)
	val add : t -> t -> t

	(** [mul p1 p2] returns the polynomial equal to [p1 * p2] *)
	val mul : t -> t -> t
	
	(** [mul p1 c] returns the polynomial equal to [p1 * c] *)
	val mulc : t -> Coeff.t -> t
	
	(** [neg p] returns the polynomial equal to [-1*p] *)
	val neg : t -> t
	
	(** [sub p1 p2] returns the polynomial equal to [p1 - p2] *)
	val sub : t -> t -> t
	
	(** [sum l] returns the sum of every polynomial in the list [l] *)
	val sum : t list -> t
	
	(** [prod l] returns the product of every polynomial in the list [l] *)
	val prod : t list -> t
	
	(** [pow p i] returns the polynomial equal to [p ^ i] *)
	val pow : t -> int -> t
	
	(** [rename p x y] renames each occurency of [x] in [p] by [y] *)
	val rename : t -> V.t -> V.t -> t
	
	(** [monomial_coefficient p m] returns the scalar coefficient of the monomialBasis [m] in [p] *)
	val monomial_coefficient : t -> MonomialBasis.t -> Coeff.t
	(*
	(** [monomial_coefficient_poly p m] returns the polynomial coefficient of monomialBasis [m] in [p].
	For instance, [monomial_coefficient_poly 3x1x2x3 - 2x2x3 {ul [x2;x3]}] = [3x1 - 2]*)
	val monomial_coefficient_poly : t -> MonomialBasis.t -> t
	
	(** [get_constant p] returns the constant coefficient of polynomial [p] *)
	val get_constant : t -> Coeff.t
	
	(** [get_affine_part p] returns the affine part of polynomial [p] *)
	val get_affine_part : t -> V.t list -> t
	
	(** [get_vars p] returns the list of variables that appear in polynomial [p] *)
	val get_vars : t -> V.t list
	
	(** [eval p v] returns a coefficient which is the evaluation of polynomial [p], where each variable is replaced by its value in function [v] *) 
	val eval : t -> (V.t -> Coeff.t) -> Coeff.t
	
	(** [eval_partial p v] returns a polynomial, which is the evaluation of polynomial [p] where each variable is replaced by its value in function [v]. If a variable has no value in [v], it remains in the result. *)
	val eval_partial : t -> (V.t -> Coeff.t option) -> t
	
	(** [ofCstr names vec coeff] builds the polynomial [vec + coeff]. *)
	val ofCstr : Vec.t -> Coeff.t -> t
	
	(** [toCstr p] returns the linear part and the coefficient of [p].
	@raise Invalid_argument if [p] is not affine. *)
	val toCstr : t -> (Vec.t * Coeff.t)
	*)
end

module Poly (Vec : Vector.Type) = struct
	module Vec = Vec
	module Coeff = Vec.Coeff
	module V = Vec.V
	
	type exp = int (* >= 0*)
	
	module MonomialBasis = 
		struct 
		(* monomial_basis represents a MONIC monomial (i.e. leading coeff = 1) *)
		type t = (V.t * exp) list
		
		let to_string_param : t -> string -> string
			= fun m s ->
			String.concat ""
				(List.map
					(fun (v,e) -> 
					match e with 
					| 0 | 1 -> V.to_string' s v
					| _ -> Printf.sprintf "%s^%i" (V.to_string' s v) e)
					m)
		
		let rec(to_string : t -> string)
			= fun m ->
			to_string_param m "x"
	
		let rec (compare : t -> t -> int)
			= fun m1 m2 ->
			match m1, m2 with
			| [], [] -> 0
			| [], _ :: _ -> -1
 		 	| _ :: _, [] -> 1
 		 	| (x1,e1) :: m1', (x2,e2) :: m2' ->
 		   	let i = V.cmp x1 x2 in
 		    	if i = 0 
 		    	then 
 		    		let j = Stdlib.compare e1 e2 in
 		    		if j = 0
		     		then compare m1' m2'
		     		else j
		     	else i
		
		let (equal : t -> t -> bool)
			= fun m1 m2 ->
			compare m1 m2 = 0
			
		let (rename : t -> V.t -> V.t -> t)
			= fun m v v' ->
			List.map (fun (var,e) -> if V.equal var v then (v',e) else (var,e)) m
		
		let (eval : t -> (V.t -> Coeff.t) -> Coeff.t)
			= fun m f_eval ->
			List.fold_left 
				(fun c (v,e) -> Coeff.mul c (Coeff.pow (f_eval v) e))
				Coeff.u m
		
		let (well_formed : t -> bool)
			= fun m ->
			List.for_all (fun (v,e) -> V.cmp v V.u >= 0 && e >= 0) m
		
		let (mk : (V.t * exp) list -> t)
			= fun l -> 
			if well_formed l then List.fast_sort (fun (v1,_) (v2,_) -> V.cmp v1 v2) l
			else Stdlib.invalid_arg ("SxPoly.Poly.Monomial.mk")
			
		let (mk_list : V.t list -> t)
			= fun l -> 
			List.fast_sort V.cmp l
			|> List.fold_left 	
				(fun res v -> 
					let (v',e') = List.hd res in
					if V.equal v v'
					then (v',e'+1) :: List.tl res
					else (v,1)::res)
				[]
			|> List.rev
			|> fun l -> if well_formed l
				then l
				else Stdlib.invalid_arg ("SxPoly.Poly.Monomial.mk")
			
		let (data : t -> (V.t * exp) list)
			= fun m -> m
		
		let (data_list : t -> V.t list)
			= fun m -> 
			List.fold_left
				(fun res (v,e) ->
					res
					@
					List.map
						(fun _ -> v)
						(Misc.range 0 e))
				[] m
			
		let null : t = []
		
	end

	module Monomial = 
		struct

		type t = (MonomialBasis.t * Coeff.t)

		let (to_string : t -> string)
			= fun m -> let (vlist, c) = m in 
			match vlist with
			| [] -> Coeff.to_string c
			| _ -> if Coeff.equal c (Coeff.mk1 1)
				then MonomialBasis.to_string vlist
				else if Coeff.lt c (Coeff.mk1 0) 
					then String.concat "" ["(";Coeff.to_string c;")*";MonomialBasis.to_string vlist]
					else String.concat "" [Coeff.to_string c ; "*" ; MonomialBasis.to_string vlist]
		
		let (compare : t -> t -> int)
			= fun (m1,_) (m2,_) ->
			MonomialBasis.compare m1 m2
		
		let (equal : t -> t -> bool)
			= fun (m1,c1) (m2,c2) ->
			MonomialBasis.compare m1 m2 = 0 && Coeff.equal c1 c2				

		let canonO : t -> t option	
			= fun (m, a) ->
  			if not (Coeff.well_formed_nonnull a)
  			then None
 			else Some (MonomialBasis.mk m, a)
	
		let canon : t -> t
		  = fun m ->
		  match canonO m with
		  | Some m' -> m'
		  | None -> Stdlib.invalid_arg ("SxPoly.SxPoly.Monomial.canon : " ^ (to_string m))

		let mk : MonomialBasis.t -> Coeff.t -> t
	  		= fun m a -> canon (m, a)
		
		let mk2 : (V.t * exp) list -> Coeff.t -> t
	  		= fun m a -> canon (MonomialBasis.mk m, a)
	  	
	  	let mk_list : V.t list -> Coeff.t -> t
	  		= fun m a -> canon (MonomialBasis.mk_list m, a)
	  		
		let data : t -> MonomialBasis.t * Coeff.t
			= fun (m,c) -> (m,c)
		
		let data_list : t -> V.t list * Coeff.t
			= fun (m,c) ->
			(MonomialBasis.data_list m, c)
		
		let rec(mul : t -> t -> t)
			= let merge : MonomialBasis.t -> MonomialBasis.t
				= fun l ->
				List.fold_left 
					(fun res (v,e) ->
						let (v',e') = List.hd res in
						if V.equal v v'
						then (v, e+e') :: List.tl res
						else (v,e)::res)
					[] l
				|> List.rev
			in
			fun (m1,c1) (m2,c2) -> 
			if Coeff.equal (Coeff.mul c1 c2) Coeff.z 
			then ([],Coeff.z)
			else
			let new_m = match (m1,m2) with
			| ([],_) -> m2
			| (_,[]) -> m1
			| _ -> m1 @ m2
			|> List.sort (fun (v1,_) (v2,_) -> V.cmp v1 v2)
			|> merge
			in 
			(new_m, Coeff.mul c1 c2)
	
		let isConstant : t -> bool
		  = fun (m,_) -> MonomialBasis.compare m MonomialBasis.null = 0 
		  
		let isLinear : t -> bool
		  = fun (m,c) -> List.length m = 1
		  
		let (eval : t -> (V.t -> Coeff.t) -> Coeff.t)
			= fun (m,c) e ->
			if MonomialBasis.compare m [] = 0
			then c
			else Coeff.mul (MonomialBasis.eval m e) c
			
		let (eval_partial : t -> (V.t -> Coeff.t option) -> t)
			= fun (m,c) f_eval ->
			List.fold_left 
				(fun (m',c') (v,e) -> match (f_eval v) with 
					| Some c2 -> mul (m',c') (MonomialBasis.null, c2)
					| None -> mul (m',c') ([v,e], Coeff.u))
				([], c) m
		
	end
	
	type t = Monomial.t list

	let (compare : t -> t -> int)
		= fun p1 p2 ->
			match (p1,p2) with
			| ([],[]) -> 0
			| (_,[]) -> 1
			| ([],_) -> -1
			| (m1::tl1, m2::tl2) -> let x = Monomial.compare m1 m2 in 
			match x with
				| 0 -> compare tl1 tl2
				| _ -> x
			
	let to_string : t -> string
	  = fun p ->
	  List.map Monomial.to_string p
	  |> String.concat " + "
	  |> fun s -> if String.length s = 0 then "0" else s
	
	let canon : t -> t
  		= let rec (collapseDups : t -> t)
      		= function
      			| [] | _ :: [] as p -> p
      			| m :: (m' :: p' as p) ->
	 			if Monomial.compare m m' = 0
	 			then collapseDups ((Stdlib.fst m, Coeff.add (Stdlib.snd m) (Stdlib.snd m')) :: p')
	 			else m :: collapseDups p
    		in
    		let fixConstant
     		 = fun p ->
      			let (cst, m) = List.partition (fun (m, _) -> MonomialBasis.compare m MonomialBasis.null = 0) p in
     	 			([], List.fold_left (fun n (_, a) -> Coeff.add n a) Coeff.z cst) :: m
    		in
    		fun p ->
    		fixConstant p
    		|> List.filter (fun (_, a) -> Coeff.well_formed_nonnull a)
    		|> List.map Monomial.canonO
    		|> List.map
				(function Some m -> m
				| None ->
					to_string p
					|> Printf.sprintf "SxPoly.canon: Monomial.canon on %s"
					|> Stdlib.failwith)
    		|> List.sort Monomial.compare
    		|> collapseDups
    		|> List.filter (fun (_, a) ->
				if Coeff.equal a Coeff.z 
				then false
				else if Coeff.well_formed_nonnull a 
					then true
					else
						to_string p
						|> Printf.sprintf "SxPoly.canon: Coeff.well_formed_nonnull on %s"
						|> Stdlib.failwith)
			|> function _ :: _ as p' -> p' | [] -> [[], Coeff.z]

	
	let mk : Monomial.t list -> t
		= fun l -> canon l
	
	let mk2 : ((V.t * exp) list * Coeff.t) list -> t
		= fun l -> canon l
	
	let mk_list : (V.t list * Coeff.t) list -> t
		= fun l -> 
		List.map 
			(fun (vars,c) -> Monomial.mk_list vars c)
			l
		|> canon
	
	let mk_cste : t -> Coeff.t -> t
		= fun p cst -> (MonomialBasis.null, cst) :: p |> canon 
		
	let mk2_cste : ((V.t * exp) list * Coeff.t) list -> Coeff.t -> t
		= fun l cst -> (MonomialBasis.null, cst) :: l |> canon 
	
	let mk2_cste_list : (V.t list * Coeff.t) list -> Coeff.t -> t
		= fun l cst -> 
		(MonomialBasis.null, cst)
		::
		List.map 
			(fun (vars,c) -> Monomial.mk_list vars c)
			l
		|> canon 
		
	let data : t -> Monomial.t list
		= fun p -> p
	
	let data2 : t -> ((V.t * exp) list * Coeff.t) list
		= fun p -> p
		 
	let data_list : t -> (V.t list * Coeff.t) list
		= fun p -> 
		List.map Monomial.data_list p
		
	let (cste : Coeff.t -> t)
		= fun i ->
		[(MonomialBasis.null,i)] |> canon
	
	let (z : t)
		= cste Coeff.z
	
	let (u : t)
		= cste Coeff.u
		
	let (negU : t) = cste Coeff.negU
	
	let rec(is_constant : t -> bool)
		= fun p ->
		match p with
		| [] -> true
		| [(m,coeff)] -> MonomialBasis.compare m MonomialBasis.null = 0
		| (m,coeff) :: tail -> false

	let rec(isZ : t -> bool)
		= fun p ->
		if p = [] then true (* nécessaire? *)
		else if List.length p = 1 
			then let (mono,coeff) = List.hd p in
				MonomialBasis.compare mono MonomialBasis.null = 0 && Coeff.equal coeff Coeff.z
			else false
	
	(* [is_affine] assumes that [p] is in canonical form. *)
	let is_affine : t -> bool
	  = fun p -> List.for_all (fun m -> Monomial.isConstant m || Monomial.isLinear m) p

	let rec(add : t -> t -> t)
		= let rec(add_rec : t -> t -> t)
			= fun p1 p2 ->
			match (p1,p2) with
			| ([],poly2) -> poly2
			| (poly1,[]) -> poly1
			| ((m1,c1) :: tail1, (m2,c2) :: tail2) -> 
				let comp = MonomialBasis.compare m1 m2 in 
				if comp = 0
				then if Coeff.equal (Coeff.add c1 c2) Coeff.z 
					then add_rec tail1 tail2
					else (m1,Coeff.add c1 c2)::(add_rec tail1 tail2)
				else if comp < 0 (*m1 < m2*) 
					then (m1,c1)::(add_rec tail1 ((m2,c2)::tail2))
					else (m2,c2)::(add_rec ((m1,c1)::tail1) tail2)
		in fun p1 p2 ->
		add_rec p1 p2 |> canon

	let rec(mul : t -> t -> t) 
		= let rec(mul_rec : t -> t -> t)
			= fun p1 p2 ->
			match (p1,p2) with
			| ([],_) -> []
			| (m::tail1,p2) -> List.fold_left 
				add (mul_rec tail1 p2) (List.map (fun m2 -> [Monomial.mul m m2]) p2)
		in fun p1 p2 -> 
		mul_rec p1 p2 |> canon
	
	(* XXX: naïve implem*)
	let (mulc : t -> Coeff.t -> t) 
		= fun p c ->
		mul p (cste c)
	
	let (neg : t -> t)
		= fun p ->
		mulc p Coeff.negU 
	
	(* XXX: naïve implem *)
	let (sub : t -> t -> t)
		= fun p1 p2 ->
		add p1 (mul negU p2)
	
	let (sum : t list -> t)
		= fun l ->
		List.fold_left (fun r p -> add r p) z l 
	
	let (prod : t list -> t)
		= fun l ->
		List.fold_left (fun r p -> mul r p) u l 
	
	let (pow : t -> int -> t)
		= fun p i ->
		List.map (fun _ -> p) (Misc.range 0 i) |> prod 
	
	let (equal : t -> t -> bool)
		= fun p1 p2 ->
		List.length p1 <> List.length p2
		&&
		List.for_all2 Monomial.equal p1 p2
	
	let (rename : t -> V.t -> V.t -> t)
		= fun p v v'->
		List.map (fun (m,c) -> (MonomialBasis.rename m v v',c)) p
		|> canon

	let rec(monomial_coefficient : t -> MonomialBasis.t -> Coeff.t)
		= fun p m ->
		match (p,m) with
		| ([],_) -> Coeff.z
		| ((m1,c)::tail, m2) -> if MonomialBasis.compare m1 m2 = 0
			then c
			else if MonomialBasis.compare m1 m2 < 0
				then monomial_coefficient tail m
				else Coeff.z
	
	let rec(sub_monomial : MonomialBasis.t -> MonomialBasis.t -> (MonomialBasis.t * bool))
	= fun m1 m2 ->
	match (m1,m2) with
	| (_,[]) -> (m1,true)
	| ([],_) -> ([],false)
	| (v1::tail1,v2::tail2) -> if V.cmp v1 v2 = 0
		then sub_monomial tail1 tail2
		else let (l,b) = sub_monomial tail1 m2 in (v1::l,b)
	(*
	let (monomial_coefficient_poly : t -> MonomialBasis.t -> t)
		= let rec(monomial_coefficient_poly_rec : t -> MonomialBasis.t -> t)
			= fun p m ->
			match (p,m) with
			| ([],_) -> []
			| ((m1,c)::tail, m2) -> if List.length m1 >= List.length m2 && MonomialBasis.compare (Misc.sublist m1 0 (List.length m2)) m2 > 0 (* m1 > m2 *)
				then []
				else let (l,b) = sub_monomial m1 m in if b
					then add [(l,c)] (monomial_coefficient_poly_rec tail m2)
					else monomial_coefficient_poly_rec tail m2
		in fun p m -> 
		monomial_coefficient_poly_rec p m |> canon

	let (get_constant : t -> Coeff.t)
		= fun p ->
		monomial_coefficient p MonomialBasis.null

	let rec(get_affine_part : t -> V.t list -> t)
		= fun p variables ->
		let res = match p with
			| [] -> []
			| (vlist,coeff) :: tail -> let q = get_affine_part tail variables in 
				let vlist2 = List.filter (fun x -> List.mem x variables) vlist in 
					if List.length vlist2 <= 1 
						then add [(vlist,coeff)] q
						else q
		in canon res
				
	let (get_vars : t -> V.t list)
		= fun p ->
		List.map (fun (m,c) -> Misc.rem_dupl V.equal m) p
		|> List.concat 
		|> Misc.rem_dupl V.equal
	
	let (eval : t -> (V.t -> Coeff.t) -> Coeff.t)
			= fun p e ->
			List.fold_left 
			(fun c m -> Coeff.add c (Monomial.eval m e))
			Coeff.z p
	
	let (eval_partial : t -> (V.t -> Coeff.t option) -> t)
			= fun p e ->
			List.fold_left 
			(fun p m -> add p [(Monomial.eval_partial m e)])
			[] p
	
	let toCstr : t -> (Vec.t * Coeff.t)
		= fun p ->
		if is_affine p 
		then 
			let vec = (List.fold_left 
				(fun l (m,c) -> 
					if MonomialBasis.compare m MonomialBasis.null <> 0 
					then (c, List.nth (MonomialBasis.data m) 0) :: l
					else l)
				[] (List.map Monomial.data (data p)))
				|> Vec.mk
			and cste = get_constant p 
			in
			(vec,cste)
		else Stdlib.invalid_arg "handelman.polyToCstr: not affine polynomial"

	let ofCstr : Vec.t -> Coeff.t -> t
		= fun vec cste ->
		let l = vec
		|> Vec.toList 
			|> List.map (fun (x,n) -> Monomial.mk2 [x] n)
			|> mk 
		in
		mk_cste l cste
	
	let of_string : string -> t
   	= fun s ->
    	PolyParser.one_poly PolyLexer.token (Lexing.from_string s) 
    	|> List.map (fun (vl,q) -> (List.map V.fromPos vl, Coeff.ofQ q))
    	|> canon
    	
	module Invariant
 		= struct
  	(** This module contains an executable specification of what it means to be
	a well-formed polynomial. *)

  		let rec helper_sorted : ('a -> 'a -> bool) -> 'a list -> bool
	    = fun f ->
    	function
   		| [] | _ :: [] -> true
   		| x :: ((x' :: _) as l') -> f x x' && helper_sorted f l'

  		module Monom
    	= struct

    		let check_sorted : Monomial.t -> bool
      		= fun (l, _) -> helper_sorted (fun x x' -> V.cmp x x' <= 0) l

    		let check : Monomial.t -> bool
      		= fun (vlist,c) -> Coeff.well_formed_nonnull c && check_sorted (vlist,c)
  		end

  		(* strict negativity enforces no duplicates *)
		let check_sorted : t -> bool
    	= helper_sorted (fun m m' -> Monomial.compare m m' < 0)
      
  		let check : t -> bool
    		= fun p ->
    		match p with
    		| [] -> false
    		| [[], a] when Coeff.equal a Coeff.z -> true
    		| _ -> List.for_all Monom.check p && check_sorted p

  		let checkOrFail : t -> unit
    		= fun p ->
    		if not (check p)
    		then p
	 		|> to_string
	 		|> Printf.sprintf "SxPoly.Invariant.checkOrFail: %s"
	 		|> Stdlib.failwith
	end
	*)
end

module RelInt = Poly(Vector.RelInt.Int)


(** Module of vectors, which associate variables from {!modtype:Var.Type} to values from {!modtype:Scalar.Type}.
A vector is either a {!type:Rtree.t} with variables {!type:Var.Positive.t} or a {!type:VarMap.t} with variables {!type:Var.Int.t}. 
*)

module type Type = sig
	module M : VarMap.Type
	module V = M.V
	module Coeff : Scalar.Type
	type t = Coeff.t M.t
	
	val name : string
	
	(** A vector with coefficients all set to zero. *)
	val nil: t
	
	val to_string : (V.t -> string) -> t -> string
	
	val mk : (Coeff.t * V.t) list -> t 
	
	val toList : t -> (V.t * Coeff.t) list
	
	(** [get vec v] returns the coefficient of variable [v] in vec. Returns {!val:Coeff.z} if [v] is not present in [vec]. *)
	val get: t -> V.t -> Coeff.t
	
	(** [set vec v n] sets the coefficient of variable [v] to [n] in vector [vec]. *)
	val set: t -> V.t -> Coeff.t -> t
	
	(** [getvars l] returns the set of variables that appear in the list of vectors [l]. *)
	val getVars: t list -> V.Set.t
	
	(** [neg vec] multiplies each coefficient in [vec] by -1. *)	
	val neg : t -> t
	

	val add : t -> t -> t
	val sub : t -> t -> t
	
	(** Computes the multiplication componentwise.*)
	val mul_t : t -> t -> t
	
	(** Multiplication by a scalar. *)
	val mulc : Coeff.t -> t -> t 
	
	(** Division by a scalar. *)
	val divc : t -> Coeff.t -> t 
	
	(** Multiplication by a Rational. *)
	val mulr : Scalar.Rat.t -> t -> t 
	
	(** Division by a Rational. *)
	val divr : t -> Scalar.Rat.t -> t 
	
	(** [middle x y] returns the middle point of the segment [xy]. *)	
	val middle : t -> t -> t
		
	(** Syntaxic comparison *)
	val cmp : t -> t -> int
	
	(** Syntaxic equality *)
	val equal : t -> t -> bool
	
	val dot_product : t -> t -> Coeff.t
	
	(** Same as {!val:dot_product}, where the first vector has rational coefficients. *)
	val dot_productr : Scalar.Rat.t M.t -> t -> Coeff.t
	
	(** [isomorph v1 v2] returns [Some r] if [v1] is equal to [mult r v2].
	If there is no such [r], [None] is returned. *)
	val isomorph: t -> t -> Coeff.t option
	
	(** [elim x v1 v2] eliminates the [x] from [v2] using [v1].
	If [v2] has coefficient zero for variable [x], it is returned untouched.
	Otherwise, if variable [x] has coefficient zero in [v1], [Invalid_argument "Vec.elim"] is raised. *)
	val elim: V.t -> t -> t -> t

	(**/**)
	val shift: V.t -> t -> V.t option M.t -> V.t * t * V.t option M.t 
	(**/**)
	
	val ofSymbolic : Scalar.Symbolic.t -> Coeff.t
	
	val toRat : t -> Scalar.Rat.t M.t 
	val ofRat : Scalar.Rat.t M.t -> t
end

module VectorRtree (Coeff : Scalar.Type) = struct
	module M = Rtree
	module V = Var.Positive
	type t = Coeff.t Rtree.t
	
	let name : string = "Rtree with coeff type : " ^ (Coeff.name)
	
	let cut : t -> Coeff.t -> t -> t 
			= fun l n r ->
		if Coeff.cmp Coeff.z n = 0 && l = M.Nil && r = Rtree.Nil then
			Rtree.Nil
		else
			Rtree.Sub (l, n, r)

	let set ve0 va0 n0 =
		let z = (Coeff.cmp Coeff.z n0 = 0) in
		let rec _set ve va =
			match ve, va with
			| Rtree.Nil, V.XH when z -> Rtree.Nil
			| Rtree.Nil, V.XH -> Rtree.Sub (Rtree.Nil, n0, Rtree.Nil)

			| Rtree.Sub (Rtree.Nil, _, Rtree.Nil), V.XH when z -> Rtree.Nil
			| Rtree.Sub (l, _, r), V.XH -> Rtree.Sub (l, n0, r)

			| Rtree.Nil, V.XO t -> cut (_set Rtree.Nil t) Coeff.z Rtree.Nil
			| Rtree.Nil, V.XI t -> cut Rtree.Nil Coeff.z (_set Rtree.Nil t)

			| Rtree.Sub (l, n, r), V.XO t -> cut (_set l t) n r
			| Rtree.Sub (l, n, r), V.XI t -> cut l n (_set r t)
		in
		_set ve0 va0	

	let mk (i: (Coeff.t * V.t) list) =
		List.fold_left (fun v (n, var) -> set v var n) Rtree.Nil i

	let rec mul_t : t -> t -> t
		= fun v1 v2 ->
		match (v1, v2) with
		| (Rtree.Nil, Rtree.Nil) -> Rtree.Nil
		| (Rtree.Sub _, Rtree.Nil) -> Rtree.Nil
		| (Rtree.Nil, Rtree.Sub _) -> Rtree.Nil
		| (Rtree.Sub (l1, n1, r1), Rtree.Sub (l2, n2, r2)) ->
			cut (mul_t l1 l2) (Coeff.mul n1 n2) (mul_t r1 r2)

	let rec add : t -> t -> t
		= fun v1 v2 ->
		match (v1, v2) with
		| (Rtree.Nil, Rtree.Nil) -> Rtree.Nil
		| (Rtree.Sub _, Rtree.Nil) -> v1
		| (Rtree.Nil, Rtree.Sub _) -> v2
		| (Rtree.Sub (l1, n1, r1), Rtree.Sub (l2, n2, r2)) ->
			cut (add l1 l2) (Coeff.add n1 n2) (add r1 r2)

	let map f v0 =
		let rec _map v =
			match v with
			| Rtree.Nil -> Rtree.Nil
			| Rtree.Sub (l, n, r) -> cut (_map l) (f n) (_map r)
		in
		_map v0
	
	let mulc n v = map (fun v' -> Coeff.mul n v') v

	let divc v c = map (fun n -> Coeff.div n c) v

	let mulr n v = map (fun v' -> Coeff.mulr n v') v

	let divr v q = map (fun n -> Coeff.divr n q) v

	let toList : t -> (V.t * Coeff.t) list
		=	let rmZeroes : (V.t * Coeff.t) list -> (V.t * Coeff.t) list
			= fun l -> List.filter (fun (_,n) -> Coeff.cmp Coeff.z n <> 0) l
			in
			fun v -> rmZeroes (Rtree.toList v)

	let get : t -> V.t -> Coeff.t
		= fun x v ->
		Rtree.get Coeff.z x v

	let neg : t -> t
		= fun x -> 
		map (fun c -> Coeff.mul Coeff.negU c) x
	
	let sub : t -> t -> t 
		= fun v1 v2 ->
		add v1 (neg v2)

	let middle : t -> t -> t 
		= fun x x' ->
		add x x' 
		|> mulc (Coeff.mk 2 1)
	
	let rec equal : t -> t -> bool
		= fun p1 p2 ->
		match (p1,p2) with
		| (Rtree.Nil, Rtree.Nil) -> true
		| (Rtree.Sub _, Rtree.Nil) -> false
		| (Rtree.Nil, Rtree.Sub _) -> false
		| (Rtree.Sub (l1, n1, r1), Rtree.Sub (l2, n2, r2)) ->
			if Coeff.cmp n1 n2 = 0 then
				equal l1 l2 && equal r1 r2
			else
				false

	let rec dot_product : t -> t -> Coeff.t
		= fun v1 v2 ->
		match (v1, v2) with
		| (Rtree.Nil, Rtree.Nil) -> Coeff.z
		| (Rtree.Sub _, Rtree.Nil) -> Coeff.z
		| (Rtree.Nil, Rtree.Sub _) -> Coeff.z
		| (Rtree.Sub (l1, n1, r1), Rtree.Sub (l2, n2, r2)) ->
			Coeff.add 
				(Coeff.mul n1 n2) 
				(Coeff.add (dot_product l1 l2) (dot_product r1 r2))	
			
	let isomorph : t -> t -> Coeff.t option
		= fun v1 v2 ->
		let rec _iso optr v1 v2 =
			match v1, v2 with
			| Rtree.Nil, Rtree.Nil -> (optr, true)
			| Rtree.Nil, _ | _, Rtree.Nil -> (None, false)
			| Rtree.Sub (l1, n1, r1), Rtree.Sub (l2, n2, r2) ->
				match Coeff.cmpz n1, Coeff.cmpz n2 with
				| 0, 0 ->
					let (optr1, res1) = _iso optr l1 l2 in
					if res1 then
						_iso optr1 r1 r2
					else
						(None, false)
				| 0,_ | _,0 -> (None, false)
				| _,_ ->
					let (res, r) =
						let ratio = Coeff.div n1 n2 in
						match optr with
						| None -> (true, Some ratio)
						| Some r -> (Coeff.cmp r ratio = 0, optr)
					in
					if res then
						let (_, res1) = _iso r l1 l2 in
						if res1 then
							_iso r r1 r2
						else
							(None, false)
					else
						(None, false)
		in
		let (ratio, _) = _iso None v1 v2 in ratio
	
	let nil = Rtree.Nil

	let getVars: t list -> V.Set.t
		= fun l -> Rtree.mskBuild (fun n -> Coeff.cmpz n <> 0) l |> Rtree.pathsGet
	
	let rec cmp : t -> t -> int
		= fun v1 v2 ->
		match (v1,v2) with
		| (Rtree.Nil, Rtree.Nil) -> 0
		| (Rtree.Nil, Rtree.Sub (_, n, _)) -> -1
		| (Rtree.Sub (_, n, _), Rtree.Nil) -> 1
		| (Rtree.Sub (l1, n1, r1),Rtree.Sub (l2, n2, r2)) -> 
			match Coeff.cmp n1 n2 with
			| 0 -> begin
				match cmp l1 l2 with
				| 0 -> cmp r1 r2
				| r -> r
				end
			| r -> r

	let to_string: (V.t -> string) -> t -> string
		= fun varPr v ->
			let nodePr a x =
				if Coeff.cmpz a = 0 then
					""
				else
					(Coeff.to_string a) ^ "." ^ x
			in
			let s = Rtree.to_string " + " nodePr varPr v in
			if String.compare s "" = 0
			then "0"
			else s 
		
	let elim (v: V.t) (using: t) (from: t): t =
		let n1 = get from v in
		match Coeff.cmpz n1 with
		| 0 -> from
		| _ ->
			let n2 = get using v in
			match Coeff.cmpz n2 with
			| 0 -> invalid_arg "Vec.elim"
			| _ -> add (mulc (Coeff.neg n1) using) (mulc n2 from)

	let shift: V.t -> t -> V.t option Rtree.t -> V.t * t * V.t option Rtree.t
		= fun nxt0 vec0 relocTbl0 ->
		let rec _shift nxt wip ve relocTbl =
			match ve, relocTbl with
			| Rtree.Nil, _ -> (nxt, wip, relocTbl)
			| Rtree.Sub (l, n, r), Rtree.Nil ->
				let (nxt1, wip1, reloc) =
					if Coeff.cmpz n = 0 then
						(nxt, wip, None)
					else
						(V.next nxt, set wip nxt n, Some nxt)
				in
				let (nxt2, wip2, lReloc) = _shift nxt1 wip1 l Rtree.Nil in
				let (nxt3, wip3, rReloc) = _shift nxt2 wip2 r Rtree.Nil in
				(nxt3, wip3, Rtree.Sub (lReloc, reloc, rReloc))
			| Rtree.Sub (l, n, r), Rtree.Sub (lReloc, reloc, rReloc) ->
				let (nxt1, wip1, reloc1) =
					if Coeff.cmpz n = 0 then
						(nxt, wip, reloc)
					else
						match reloc with
						| Some x -> (nxt, set wip x n, reloc)
						| None -> (V.next nxt, set wip nxt n, Some nxt)
				in
				let (nxt2, wip2, lReloc1) = _shift nxt1 wip1 l lReloc in
				let (nxt3, wip3, rReloc1) = _shift nxt2 wip2 r rReloc in
				(nxt3, wip3, Rtree.Sub (lReloc1, reloc1, rReloc1))
		in
		_shift nxt0 Rtree.Nil vec0 relocTbl0
	
	let toRat : t -> Scalar.Rat.t Rtree.t
		= fun v ->
		Rtree.map Coeff.toQ v
	
	let ofRat : Scalar.Rat.t Rtree.t -> t
		= fun v ->
		Rtree.map Coeff.ofQ v
		
	let ofSymbolic : Scalar.Symbolic.t -> Coeff.t
		= fun v ->
		Stdlib.failwith "Vector.ofSymbolic : not implemented" 
		
	let rec dot_productr : Scalar.Rat.t Rtree.t -> t -> Coeff.t
		= fun q v ->
		match (q, v) with
		| (Rtree.Nil, Rtree.Nil) 
		| (Rtree.Sub _, Rtree.Nil)
		| (Rtree.Nil, Rtree.Sub _) -> Coeff.z
		| (Rtree.Sub (l1, n1, r1), Rtree.Sub (l2, n2, r2)) ->
			Coeff.add 
				(Coeff.mulr n1 n2) 
				(Coeff.add (dot_productr l1 l2) (dot_productr r1 r2))
end

module VectorMap (Coeff : Scalar.Type)(V : Var.Type) = struct
	module M = VarMap.VarMap(V)
	module V = M.V (*Var.Int*)
	type t = Coeff.t M.t

	let name : string = "IntMap with coeff type : " ^ (Coeff.name)
	
	let set vec var value =
		if Coeff.isZ value
		then M.remove var vec
		else M.set2 vec var value
		
	let mk (i: (Coeff.t * V.t) list) =
		List.fold_left (fun v (n,var) -> set v var n) M.empty i

	let rec mul_t : t -> t -> t
		= fun v1 v2 ->
		M.merge 
			(fun _ c1opt c2opt ->
				match c1opt,c2opt with
				| None,_ | _,None -> None
				| Some c1, Some c2 -> let c' = Coeff.mul c1 c2 in
					if Coeff.isZ c'
					then None
					else Some c')
			v1 v2

	let rec add : t -> t -> t
		= fun v1 v2 ->
		M.merge 
			(fun _ c1opt c2opt ->
				match c1opt,c2opt with
				| None, None -> None
				| None, Some c | Some c, None -> Some c
				| Some c1, Some c2 -> let c' = Coeff.add c1 c2 in
					if Coeff.isZ c'
					then None
					else Some c')
			v1 v2
	
	let map (*: (Coeff.t -> Coeff.t) -> t -> t*)
		= fun f vec ->
		M.fold
			(fun var map c -> 
				let c' = f c in
				if Coeff.isZ c'
				then M.remove var map
				else M.set2 map var c')
			M.empty 
			vec

	
	let mulc n v = map (fun v' -> Coeff.mul n v') v

	let divc v c = map (fun n -> Coeff.div n c) v

	let mulr n v = map (fun v' -> Coeff.mulr n v') v

	let divr v q = map (fun n -> Coeff.divr n q) v
	
	(* XXX: besoin de supprimer les 0 comme dans la version Rtree?*)
	let toList : t -> (V.t * Coeff.t) list
		= fun v -> (M.toList v)

	let get : t -> V.t -> Coeff.t
		= fun x v ->
		M.get Coeff.z x v

	let neg : t -> t
		= fun x -> 
		map (fun c -> Coeff.mul Coeff.negU c) x
	
	let sub : t -> t -> t 
		= fun v1 v2 ->
		add v1 (neg v2)

	let middle : t -> t -> t 
		= fun x x' ->
		add x x' 
		|> mulc (Coeff.mk 2 1)
	
	let rec equal : t -> t -> bool
		= fun p1 p2 ->
		M.equal Coeff.equal p1 p2

	let rec dot_product : t -> t -> Coeff.t
		= fun v1 v2 ->
		M.fold2
			(fun _ res n m ->
				Coeff.add res (Coeff.mul n m))
			Coeff.z
			v1 v2
	
	let nil = M.empty
	
	let isomorph : t -> t -> Coeff.t option
		= fun v1 v2 ->
		try
			let (res,b) = M.fold2_strict
				(fun (res,b) c1 c2 -> 
					if not b 
					then (res,b)
					else match Coeff.cmpz c1, Coeff.cmpz c2 with
						| 0, 0 -> (res,b)
						| _,0 | 0,_ -> (None,false)
						| _,_ -> let c = Coeff.div c1 c2 in
							match res with
							| None -> (Some c, true)
							| Some c' -> if Coeff.equal c c'
								then (Some c, true)
								else (None, false)
				)
				(None, true)
				v1 v2
			in
			if b then res else None
		with Invalid_argument _ -> None
		
	let getVars: t list -> V.Set.t
		= fun l -> M.mskBuild (fun n -> Coeff.cmpz n <> 0) l |> M.pathsGet
		
	let rec cmp : t -> t -> int
		= fun v1 v2 ->
		M.fold2
			(fun _ res c1 c2 ->
				if res = 0 
				then Coeff.cmp c1 c2
				else res)
			0
			v1 v2	
	
	let to_string: (V.t -> string) -> t -> string
		= fun varPr v ->
			let nodePr a x =
				if Coeff.cmpz a = 0 then
					""
				else
					(Coeff.to_string a) ^ "." ^ x
			in
			if equal v nil
			then "0"
			else M.to_string " + " nodePr varPr v
		
	let elim (v: V.t) (using: t) (from: t): t =
		let n1 = get from v in
		match Coeff.cmpz n1 with
		| 0 -> from
		| _ ->
			let n2 = get using v in
			match Coeff.cmpz n2 with
			| 0 -> invalid_arg "Vec.elim"
			| _ -> add (mulc (Coeff.neg n1) using) (mulc n2 from)

	module VectorRtree = VectorRtree(Coeff)
	
	let shift: V.t -> t -> V.t option M.t -> V.t * t * V.t option M.t
		= let toRtree_vec : t -> VectorRtree.t
			= fun t ->
			M.toList t
			(* TODO: changer cette traduction?*)
			|> List.map (fun (v,x) -> V.toInt v |> VectorRtree.V.fromInt, x)
			|> VectorRtree.M.mk Coeff.z 
			
		in 
		let ofRtree_vec : VectorRtree.t -> t
			= fun t ->
			VectorRtree.M.toList t
			|> List.map (fun (v,x) -> VectorRtree.V.toInt v |> V.fromInt, x)
			|> M.mk2
		in 
		
		let toRtree2 : V.t option M.t -> VectorRtree.V.t option VectorRtree.M.t
			= fun t ->
			M.toList t
			|> List.map (fun (v,x) -> V.toInt v |> VectorRtree.V.fromInt, 
				match x with
				| None -> None
				| Some x -> Some (V.toInt x |> VectorRtree.V.fromInt))
			|> VectorRtree.M.mk None 
			
		in 
		let ofRtree2 : VectorRtree.V.t option VectorRtree.M.t-> V.t option M.t
			= fun t ->
			VectorRtree.M.toList t
			|> List.map (fun (v,x) -> VectorRtree.V.toInt v |> V.fromInt, 
				match x with
				| None -> None
				| Some x -> Some (VectorRtree.V.toInt x |> V.fromInt))
			|> M.mk2
		in 
		fun nxt0 vec0 relocTbl0 ->
		let (v,vec,r) = VectorRtree.shift (V.toInt nxt0 |> VectorRtree.V.fromInt) (toRtree_vec vec0) (toRtree2 relocTbl0)
		in
		(VectorRtree.V.toInt v |> V.fromInt,
		 ofRtree_vec vec,
		 ofRtree2 r)
		
	let toRat : t -> Scalar.Rat.t M.t
		= fun v ->
		M.map Coeff.toQ v
	
	let ofRat : Scalar.Rat.t M.t -> t
		= fun v ->
		M.map Coeff.ofQ v
		
	let ofSymbolic : Scalar.Symbolic.t -> Coeff.t
		= fun v ->
		Stdlib.failwith "Vector.ofSymbolic : not implemented" 
		
	let rec dot_productr : Scalar.Rat.t M.t -> t -> Coeff.t
		= fun q v ->
		M.fold2
			(fun _ res n m ->
				Coeff.add res (Coeff.mulr n m))
			Coeff.z
			q v
end

module Rat = struct	

	module type Type = sig
		include Type with module Coeff = Scalar.Rat
		
		(** Compute the greatest common divisor of the coefficients of a vector. *)
		val gcd : t -> Scalar.Rat.t
	end
	
	module Positive = struct
		module Coeff = Scalar.Rat
		include VectorRtree (Coeff)
		
		let ofSymbolic : Scalar.Symbolic.t -> Scalar.Rat.t
			= fun v ->
			if Scalar.Symbolic.hasDelta v
			then Scalar.Rat.add 
					(Scalar.Symbolic.get_v v)
					(Scalar.Rat.mul Scalar.Rat.delta (Scalar.Symbolic.get_d v))
			else Scalar.Symbolic.get_v v 
		
	
		let gcd v =
			let gcd = Rtree.fold (fun _ g a ->
				if Scalar.Rat.cmpz a = 0 then
					g
				else
					let sofRat = Scalar.Rat.ofRat in
					match g with
					| None -> Some (Scalar.Rat.toZ (Scalar.Rat.abs a |> sofRat))
					| Some g -> Some (Scalar.Rat.gcd g a)) None v
			in
			match gcd with
			| None -> Scalar.Rat.u
			| Some (nGcd, dGcd) -> Scalar.Rat.ofZ dGcd nGcd |> Scalar.Rat.toRat
	end
	
	module Int  = struct
		module Coeff = Scalar.Rat
		include VectorMap (Coeff)(Var.Int)
		
		let ofSymbolic : Scalar.Symbolic.t -> Scalar.Rat.t
			= fun v ->
			if Scalar.Symbolic.hasDelta v
			then Scalar.Rat.add 
					(Scalar.Symbolic.get_v v)
					(Scalar.Rat.mul Scalar.Rat.delta (Scalar.Symbolic.get_d v))
			else Scalar.Symbolic.get_v v 
		
		let gcd v =
			let gcd = M.fold (fun _ g a ->
				if Scalar.Rat.cmpz a = 0 then
					g
				else
					let sofRat = Scalar.Rat.ofRat in
					match g with
					| None -> Some (Scalar.Rat.toZ (Scalar.Rat.abs a |> sofRat))
					| Some g -> Some (Scalar.Rat.gcd g a)) None v
			in
			match gcd with
			| None -> Scalar.Rat.u
			| Some (nGcd, dGcd) -> Scalar.Rat.ofZ dGcd nGcd |> Scalar.Rat.toRat
	end
	
	module String  = struct
		module Coeff = Scalar.Rat
		include VectorMap (Coeff)(Var.String)
		
		let ofSymbolic : Scalar.Symbolic.t -> Scalar.Rat.t
			= fun v ->
			if Scalar.Symbolic.hasDelta v
			then Scalar.Rat.add 
					(Scalar.Symbolic.get_v v)
					(Scalar.Rat.mul Scalar.Rat.delta (Scalar.Symbolic.get_d v))
			else Scalar.Symbolic.get_v v 
		
		let gcd v =
			let gcd = M.fold (fun _ g a ->
				if Scalar.Rat.cmpz a = 0 then
					g
				else
					let sofRat = Scalar.Rat.ofRat in
					match g with
					| None -> Some (Scalar.Rat.toZ (Scalar.Rat.abs a |> sofRat))
					| Some g -> Some (Scalar.Rat.gcd g a)) None v
			in
			match gcd with
			| None -> Scalar.Rat.u
			| Some (nGcd, dGcd) -> Scalar.Rat.ofZ dGcd nGcd |> Scalar.Rat.toRat
	end
	
end

module Float = struct
	module Positive = struct
		module Coeff = Scalar.Float
		include VectorRtree(Coeff)	
	
		let ofSymbolic : Scalar.Symbolic.t -> Scalar.Float.t
			= fun v ->
			if Scalar.Symbolic.hasDelta v
			then Scalar.Float.add 
					(Scalar.Symbolic.get_v v |> Scalar.Float.ofQ)
					(Scalar.Float.mul Scalar.Float.delta (Scalar.Symbolic.get_d v |> Scalar.Float.ofQ))
			else Scalar.Symbolic.get_v v |> Scalar.Float.ofQ 
	end
	
	module Int = struct
		module Coeff = Scalar.Float
		include VectorMap(Coeff)(Var.Int)	
	
		let ofSymbolic : Scalar.Symbolic.t -> Scalar.Float.t
			= fun v ->
			if Scalar.Symbolic.hasDelta v
			then Scalar.Float.add 
					(Scalar.Symbolic.get_v v |> Scalar.Float.ofQ)
					(Scalar.Float.mul Scalar.Float.delta (Scalar.Symbolic.get_d v |> Scalar.Float.ofQ))
			else Scalar.Symbolic.get_v v |> Scalar.Float.ofQ 
	end
end


module Symbolic = struct
	module Positive = struct
		module Coeff = Scalar.Symbolic
		include VectorRtree(Scalar.Symbolic)
	
		let ofSymbolic v = v
	end
	
	module Int = struct
		module Coeff = Scalar.Symbolic
		include VectorMap(Scalar.Symbolic)(Var.Int)
	
		let ofSymbolic v = v
	end
end

module RelInt = struct
	module Positive = struct
		module Coeff = Scalar.RelInt
		include VectorRtree(Coeff)	
	
		let ofSymbolic : Scalar.Symbolic.t -> Scalar.RelInt.t
			= fun v ->
			Stdlib.failwith "Vector.RelInt.Positive.ofSymbolic"
	end
	
	module Int = struct
		module Coeff = Scalar.RelInt
		include VectorMap(Coeff)(Var.Int)	
	
		let ofSymbolic : Scalar.Symbolic.t -> Scalar.RelInt.t
			= fun v ->
			Stdlib.failwith "Vector.RelInt.Int.ofSymbolic"
	end
end

module MachineInt = struct
	module Positive = struct
		module Coeff = Scalar.MachineInt
		include VectorRtree(Coeff)	
	
		let ofSymbolic : Scalar.Symbolic.t -> Scalar.MachineInt.t
			= fun v ->
			Stdlib.failwith "Vector.MachineInt.Positive.ofSymbolic"
	end
	
	module Int = struct
		module Coeff = Scalar.MachineInt
		include VectorMap(Coeff)(Var.Int)	
	
		let ofSymbolic : Scalar.Symbolic.t -> Scalar.MachineInt.t
			= fun v ->
			Stdlib.failwith "Vector.MachineInt.Int.ofSymbolic"
	end
end

module Debug = DebugTypes.Debug(struct let name = "Handelman" end)

(* cIndex (1, 0, 3) représente C_1^1 * C_2^0 * C_3^3 *)
type cIndex = Index.Int.t
(* varIndex (1, 0, 3) représente x_1^1 * x_2^0 * x_3^3 *)
type varIndex = Index.Int.t
(* boundIndex (1, 0, 3) représente 1xC_1 + 0xC_2 + 3xC_3 *)
type boundIndex = Index.Rat.t

type t =
| Ci of cIndex
| VarBounds of varIndex * (boundIndex list)
| VarCi of varIndex * cIndex

let (to_string : t -> string)
	= fun h ->
	match h with
	| Ci i -> "Ci(" ^ (Index.Int.to_string i) ^ ")"
	| VarBounds (i,j) -> "VB(" ^ (Index.Int.to_string i) ^ ", " ^ (Misc.list_to_string Index.Rat.to_string j " ; ") ^ ")"
	| VarCi (i,j) -> "VC(" ^ (Index.Int.to_string i) ^ ", " ^ (Index.Int.to_string j) ^ ")"

let (eq : t -> t -> bool)
	= fun h1 h2 ->
	match (h1,h2) with
	| (Ci i1, Ci i2) -> Index.Int.equal i1 i2
	| (VarBounds (i1,j1), VarBounds (i2,j2)) -> Index.Int.equal i1 i2
		&& List.length j1 = List.length j2
		&& (List.for_all2 (fun k1 k2 -> Index.Rat.equal k1 k2) j1 j2)
	| (VarCi (i1,j1), VarCi (i2,j2)) -> Index.Int.equal i1 i2 && Index.Int.equal j1 j2
	| (_,_) -> false

let is_linear : t -> bool
	= function
	| Ci id -> Index.Int.is_unitary id
	| VarBounds(vI,bIs) ->
		((Index.Int.is_null vI) && (List.length bIs = 1))
	  ||
		((Index.Int.is_unitary vI) && (List.length bIs = 0))
	| VarCi (vI,cI) ->
		((Index.Int.is_null vI) && (Index.Int.is_unitary cI))
	  ||
		((Index.Int.is_unitary vI) && (Index.Int.is_null cI))

module Eval = struct

	(** [pow q i] returns [q^i]*)
	let (pow : Q.t -> int -> Q.t)
		= fun q i ->
		List.fold_left
			(fun c _ -> Q.mul c q)
			Q.one
			(Misc.range 0 i)

	(** [eval_f vl l] returns a function associating [vl[i]] to [l[i]] *)
	let (evalf : CstrPoly.Positive.Poly.V.t list -> 'a list -> CstrPoly.Positive.Poly.V.t -> 'a)
			= fun vl l v ->
			try let i = Misc.findi (fun x -> CstrPoly.Positive.Poly.V.equal x v) vl in
				List.nth l i
			with
			| Not_found -> Stdlib.failwith "HOtypes.Hi.Eval.evalf : Not_found"
			| Invalid_argument _ -> Stdlib.failwith "HOtypes.Hi.Eval.evalf : Invalid_argument"

	let (eval_cIndex : cIndex -> CstrPoly.Positive.Poly.t list -> (CstrPoly.Positive.Poly.V.t -> Q.t) -> Q.t)
		= fun id pl eval  ->
			List.fold_left2
			(fun c i p -> Q.add c (if i = 0 then Q.zero else (pow (CstrPoly.Positive.Poly.eval p eval) i)))
			Q.zero
			(Index.Int.data id) pl

	let (eval_varIndex : varIndex -> CstrPoly.Positive.Poly.V.t list -> (CstrPoly.Positive.Poly.V.t -> Q.t) -> Q.t)
		= fun id vl eval ->
			List.fold_left2
			(fun c i v -> let p = CstrPoly.Positive.Poly.mk2 [([v],Q.one)] in
				Q.mul c (pow (CstrPoly.Positive.Poly.eval p eval) i))
			Q.one
			(Index.Int.data id) vl

	let (eval_boundIndex : boundIndex -> CstrPoly.Positive.Poly.t list ->  (CstrPoly.Positive.Poly.V.t -> Q.t) -> Q.t)
		= fun id pl eval  ->
			List.fold_left2
			(fun c i p -> Q.add c (if Q.equal i Q.zero then Q.zero else (Q.mul i (CstrPoly.Positive.Poly.eval p eval))))
			Q.zero
			(Index.Rat.data id) pl

	let (eval_Hi : t -> CstrPoly.Positive.Poly.t list -> CstrPoly.Positive.Poly.V.t list -> Q.t list -> Q.t)
		= fun hi pl vl ci ->
			let eval = evalf vl ci in
			match hi with
			| Ci c_id -> eval_cIndex c_id pl eval
			| VarBounds (v_id, b_ids) -> List.fold_left (fun res b_id -> Q.add res (eval_boundIndex b_id pl eval)) Q.zero b_ids
				|> Q.mul (eval_varIndex v_id vl eval)
			| VarCi (v_id, c_id) -> Q.mul (eval_varIndex v_id vl eval) (eval_cIndex c_id pl eval)

	let (eval_poly : CstrPoly.Positive.Poly.t -> CstrPoly.Positive.Poly.V.t list -> Q.t list -> Q.t)
		= fun p vl ci ->
		CstrPoly.Positive.Poly.eval p (evalf vl ci)
end

module Cert = struct
	module Poly = CstrPoly.Positive.Poly
	module V = Poly.V

	type squares = (V.t * int) list

    let squares_to_string : squares -> string
        = fun sq ->
        Misc.list_to_string
            (fun (v,i) -> Printf.sprintf "%s^%i" (V.to_string v) i)
            sq "."

	type schweighofer = Scalar.Rat.t * (cIndex * squares * boundIndex list)

    let schweighofer_to_string : schweighofer -> string
        = fun (coeff, (cI, sq, bIs)) ->
        Printf.sprintf "%s.(%s * %s * %s)"
            (Scalar.Rat.to_string coeff)
            (Index.Int.to_string cI)
            (squares_to_string sq)
            (Misc.list_to_string Index.Rat.to_string bIs "*")

    let to_string : schweighofer list -> string
        = fun ss ->
        Misc.list_to_string schweighofer_to_string ss " ; "
        
	let varIndex_to_squares : V.t list -> varIndex -> squares
		= fun vars id ->
		Index.Int.data id
		|> List.map (fun i -> i/2) (* divided by 2 because of the Coq type *)
		|> List.combine vars
		|> List.filter
			(fun (_,exp) -> exp > 0)

	(** [hi_to_cert n_cstrs vars coeff hi] *)
	let hi_to_cert : int -> V.t list -> Scalar.Rat.t -> t -> schweighofer
		= fun n_cstrs vars coeff -> function
		| Ci cId -> (coeff, (cId, [], []))
		| VarBounds (varId, bIs) -> (coeff, (Index.Int.init n_cstrs, varIndex_to_squares vars varId, bIs))
		| VarCi (varId , cId) -> (coeff, (cId, varIndex_to_squares vars varId, []))

end

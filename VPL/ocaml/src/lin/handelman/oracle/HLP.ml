(** This module builds and solve the linear programming problem associated to the heuristic powerLTOne.
Within this heuristic, we must choose one bound (either the upper or lower) per variable x_i. As some bounds may not exist if the input polyhedron is unbouded, we handle this using a {!type HOtypes.LPMaps.mapDetBound}.
Decision variables are called lpvars, and lpvars_i = 1 if we choose the upper bound of x_i.
*)
module Debug = HOtypes.Debug

open HOtypes

module Build = struct

	(** There is only one equality in the lp, used to produce a product with the good sign.
	It is done by counting the number of negative bounds that we have chosen, which is the number of nonnull lpvars_i
	The equality produced is sum_i y_i = k + (1 or 0 depending on the sign of the monomial to cancel)
	*)
	let build_equalities :  V.t list -> bool -> V.t -> CP.t list
		= fun vars pos k ->
		let coeff = (Poly.add
				(Poly.mk2 [([k],Q.of_int 2)])
				(Poly.cste (if pos then Q.one else Q.zero)))
		in
		let p = List.map (fun v -> ([v],Q.one)) vars
			|> Poly.mk2
		in
		let eq = Poly.sub p coeff
			|> CP.mk Cstr.Eq
		in [eq]

	(** These inequalities encode that lpvars_i = 1 if the upper bound if x_i is chosen, 0 otherwise. *)
	let build_inequalities : V.t list -> LPMaps.mapDetBound -> CP.t list
		= fun vars mapDB ->
		List.fold_left
			(fun ineqs v ->
					(CP.mk
						Cstr.Le
						(Poly.mk2_cste [([v],Scalar.Rat.u)] (Scalar.Rat.neg (LPMaps.hasSup v mapDB)))
					)
				::
					(CP.mk
						Cstr.Le
						(Poly.mk2_cste [([v],Scalar.Rat.negU)] (Scalar.Rat.sub Scalar.Rat.u (LPMaps.hasInf v mapDB)))
					)
				::
					ineqs)
			[] vars

	(** The objective function minimizes the use of unknown bounds. *)
	let build_obj : V.t list -> LPMaps.mapDetBound -> Poly.Vec.t
		= fun vars mapDB ->
		List.map
			(fun v -> let coeff = Scalar.Rat.sub
					(LPMaps.detSup v mapDB)
					(LPMaps.detInf v mapDB)
				in (coeff,v))
			vars
		|> Poly.Vec.mk

	(** Builds the positivity constraints for each decision variable. *)
	let positivity_cstrs : V.t list -> CP.t list
		= fun vars ->
	 	List.map
	 		(fun v -> CP.mk
	 			Cstr.Le
	 			(Poly.mk2 [([v],Scalar.Rat.negU)]))
	 		vars

	(** Builds the satisfiability problem. *)
	let build : V.t list -> bool -> LPMaps.mapDetBound -> Splx.t Splx.mayUnsatT
		= fun vars pos mapDB ->
		HOtypes.Debug.log DebugTypes.Detail
			(lazy(Printf.sprintf "LP.build vars = %s\nInit mapDB = %s\n"
			(Poly.MonomialBasis.to_string (Poly.MonomialBasis.mk vars))
			(LPMaps.mapDB_to_string mapDB)));

		(* la variable max+1 correspond à k et sert à fixer la parité *)
		let k = V.next (Misc.max V.cmp vars) in
		let lpvars = vars @ [k] in
		let lp_eq = build_equalities vars pos k in
		let lp_ineqs = build_inequalities vars mapDB in
		let var_pos = positivity_cstrs lpvars in
		let ineqs = List.mapi
			(fun i cstr -> (i, CP.toCstr cstr))
			(var_pos @ lp_ineqs @ lp_eq)
		in
		(Splx.mk (V.next k) ineqs)

end

module Bound = struct

	(** [get vars typ v sx] returns a witness allowing to compute the tightest (upper or lower depending on [typ] bound of [v] in  the polyhedron represented by [sx].
	It returns [None] if such bound does not exists ({i i.e.} is the polyhedron is unbounded in that direction). *)
	let (getWitness : V.t list -> LPMaps.t -> V.t -> Splx.t -> Splx.witness_t option)
		= fun vars typ v sxPh ->
		let coeff = match typ with
			| LPMaps.Upper -> Scalar.Rat.u
			| LPMaps.Lower -> Scalar.Rat.negU
		in
		let obj = Poly.Vec.mk [(coeff, v)]
		in
		match Opt.max sxPh obj with
		| Splx.IsOk (Opt.Finite (sxPh, value, wit) | Opt.Sup (sxPh, value, wit)) -> Some wit
		| Splx.IsOk (Opt.Infty) | Splx.IsUnsat _ -> None

	(** [getBoundIndex wit ph] returns the {!type Hi.boundIndex} corresponding to [wit], which depends on the order of the constraints in [ph]. *)
	let getBoundIndex : Splx.witness_t -> Poly.t list -> Hi.boundIndex
		= fun wit ph ->
		List.mapi
			(fun i _ ->
				try
					let (_,q) = List.find (fun (j,_) -> i = j) wit in q
				with
					Not_found -> Scalar.Rat.z)
			ph
		|> Index.Rat.mk

	let get : V.t list -> LPMaps.t -> V.t -> Splx.t -> Poly.t list -> Hi.boundIndex option
		= fun vars typ v sxPh ph ->
		match getWitness vars typ v sxPh with
		| None -> None
		| Some wit -> Some (getBoundIndex wit ph)

	let updateMaps : V.t list -> (V.t * LPMaps.t) list -> Splx.t -> LPMaps.mapDetBound -> LPMaps.mapBound
		-> Poly.t list -> (LPMaps.mapDetBound * LPMaps.mapBound * (Hi.boundIndex list option))
		= let addOption : 'a -> 'a list option -> 'a list option
			= fun e es ->
			match es with
			| None -> None
			| Some l -> Some (e::l)
		in
		fun vars model sxPh mapDB mapB ph ->
		List.fold_left
			(fun (mapDB, mapB, bIs) (v,typ) ->
				match typ with
				| LPMaps.Upper ->
					begin
					match MapV.find v mapB with
					| (_,Some bI) -> (mapDB, mapB, addOption bI bIs)
					| (_,None) -> match get vars typ v sxPh ph with
						| None -> (LPMaps.updateMapDB mapDB v false typ, mapB, None)
						| Some bI -> (LPMaps.updateMapDB mapDB v true typ, LPMaps.updateMapB mapB v bI typ, addOption bI bIs)
					end
				| LPMaps.Lower ->
					begin
					match MapV.find v mapB with
					| (Some bI,_) -> (mapDB, mapB, addOption bI bIs)
					| (None,_) -> match get vars typ v sxPh ph with
						| None -> (LPMaps.updateMapDB mapDB v false typ, mapB, None)
						| Some bI -> (LPMaps.updateMapDB mapDB v true typ, LPMaps.updateMapB mapB v bI typ, addOption bI bIs)
					end
			)
			(mapDB, mapB, Some [])
			model
end

module Solve = struct

	let getModel : V.t list -> Vector.Symbolic.Positive.t -> (V.t * LPMaps.t) list
		= fun vars vec ->
		Debug.log DebugTypes.Detail (lazy (Printf.sprintf "Model: %s"
			(Vector.Symbolic.Positive.to_string Vector.Symbolic.Positive.V.to_string vec)));
		List.map
			(fun v ->
			if Scalar.Symbolic.isZ (Vector.Symbolic.Positive.get vec v)
			then (v, LPMaps.Lower)
			else (v, LPMaps.Upper))
			vars

	(** Returns a model that satisfies the LP. *)
	let solve : Splx.t Splx.mayUnsatT -> V.t list -> LPMaps.mapDetBound
		-> (V.t * LPMaps.t) list option Splx.mayUnsatT
		= fun sx vars mapDB ->
		match sx with
		| Splx.IsOk sx ->
			begin
			let obj = Build.build_obj vars mapDB in
			match Opt.max sx obj with
			| Splx.IsOk (Opt.Finite (sx, value, wit) | Opt.Sup (sx, value, wit)) ->
				begin
				let vec = Splx.getAsg sx
					|> getModel vars
				in
				Splx.IsOk (Some vec)
				end
			| Splx.IsOk (Opt.Infty) -> Splx.IsOk (None)
			| Splx.IsUnsat wit -> Splx.IsUnsat wit
			end
		| Splx.IsUnsat wit -> Splx.IsUnsat wit

	let rec exec : LPMaps.bounds -> Poly.t list -> Splx.t -> V.t list -> V.t list -> Scalar.Rat.t
		-> Hi.boundIndex list option * LPMaps.bounds
		= fun bounds ph sxPh vars varsMon coeffMon ->
		let pos = (Scalar.Rat.le Scalar.Rat.z coeffMon) in
		let mapDB = bounds.LPMaps.mapDB and mapB = bounds.LPMaps.mapB in
		let sxBool = Build.build varsMon pos mapDB in
		match solve sxBool varsMon mapDB with
		| Splx.IsOk(None) | Splx.IsUnsat _ -> (None, bounds)
		| Splx.IsOk (Some model) ->
			let (mapDB,mapB,bIs) = Bound.updateMaps varsMon model sxPh mapDB mapB ph in
			let bounds' = {LPMaps.mapDB = mapDB ; LPMaps.mapB = mapB} in
			match bIs with
			| None -> exec bounds' ph sxPh vars varsMon coeffMon
			| Some bIs -> (Some bIs, bounds')
end

let run : LPMaps.bounds -> Poly.t list -> Splx.t -> V.t list -> Poly.Monomial.t
	-> Hi.boundIndex list option * LPMaps.bounds
	= fun bounds ph sxPh vars mon ->
	let (mB,coeffMon) = Poly.Monomial.data mon in
	let varsMon = Poly.MonomialBasis.data mB in
	Solve.exec bounds ph sxPh vars varsMon coeffMon

open HOtypes
open HPattern

type t = Pneuma.t -> HPattern.t -> Pneuma.t

(* XXX: devrait updater les maps? *)
let exposantDegree : Pneuma.t -> Poly.t -> Pneuma.t
	= fun pn p ->
	let n_cstrs = Pneuma.n_cstrs pn in
	let deg_max = Index.Int.sum (MapIndexP.poly_to_deg_max pn.Pneuma.p pn.Pneuma.vl) in
	let il = IndexBuild.Liste.le n_cstrs deg_max in
	let il' = List.map (fun x -> Hi.Ci(x)) il in
	{pn with Pneuma.p = Poly.sub pn.Pneuma.p p ; Pneuma.mapP = MapP.add p il' pn.Pneuma.mapP}

module AllUnderMaxDegree = struct
	(** [check_degree f_deg vl] returns a function that test if the polynomial corresponding to an index has a degree smaller than f_deg *)
	let check_degree : Index.Int.t -> V.t list -> (Poly.t -> bool)
		= fun f_deg vl ->
		fun poly -> Index.Int.le_nl (MapIndexP.poly_to_deg_max poly vl) f_deg

	(** [tryAdd (il,mapIP,mapI) check il' ind cons] computes [ind' =  cons + ind], and adds [ind'] to [il] if the following conditions hold:
	{ul
		{-item [ind] is not already in [il]}
		{-item [ind] is not in [il']}
		{-item [check ind = true]}
	}*)
	let tryAdd : (IndexBuild.Liste.t * MapIndexP.t * IndexBuild.Map.t) -> (Poly.t -> bool) -> IndexBuild.Liste.t -> Index.Int.t -> Index.Int.t
		-> (IndexBuild.Liste.t * MapIndexP.t * IndexBuild.Map.t)
		= fun (il,mapIP,mapI) check il' ind cons ->
		let ind' = Index.Int.add ind cons in
		if List.mem ind' il || List.mem ind' il'
		then (il,mapIP,mapI)
		else
			let (p1,mapIP1,mapI1) = (MapIndexP.get ind mapIP mapI) in
			let (p2,mapIP2,mapI2) = (MapIndexP.get cons mapIP1 mapI1) in
			let (p3,mapIP3,mapI3) = (MapIndexP.get ind' mapIP2 mapI2) in
			if check p3
			then (ind' :: il, mapIP3, mapI3)
			else (il, mapIP3, mapI3)

	let get_next_constraints : Pneuma.t -> IndexBuild.Liste.t -> (IndexBuild.Liste.t * MapIndexP.t * IndexBuild.Map.t)
		= let rec (get_next_constraints : IndexBuild.Liste.t -> IndexBuild.Liste.t -> (Poly.t -> bool) -> MapIndexP.t -> IndexBuild.Map.t
			-> (IndexBuild.Liste.t * MapIndexP.t * IndexBuild.Map.t))
			= fun constraints il check mapIP mapI ->
			let (l,mapIP,mapI) =
				List.fold_left
					(fun (l,mapIP,mapI) cons ->
						List.fold_left
							(fun (l',mapIP,mapI) ind -> tryAdd (l',mapIP,mapI) check l ind cons)
							(l,mapIP,mapI)	il
						)
				([], mapIP, mapI)	constraints
			in
			match l with
			| [] -> ([],mapIP,mapI)
			| l -> let (l',mapIP',mapI') = get_next_constraints constraints l check mapIP mapI
				in
				(l @ l',mapIP',mapI')
		in
		fun pn constraints ->
		let f_deg = MapIndexP.poly_to_deg_max pn.Pneuma.p pn.Pneuma.vl in
		let check = check_degree f_deg pn.Pneuma.vl in
		get_next_constraints constraints constraints check pn.Pneuma.mapIP pn.Pneuma.mapI

	let (allUnderMaxDegree : t)
		= fun pn pat ->
		match pat with
		| HPattern.AllUnderMaxDegree p ->
			HOtypes.Debug.log DebugTypes.Detail
				(lazy(Printf.sprintf "AllUnderMaxDegree : %s" (Poly.to_string p)));
			let n_cstrs = Pneuma.n_cstrs pn in
			let constraints = List.map (fun i -> Index.Int.unitary i n_cstrs) (Misc.range 0 n_cstrs) in
			let (l,mapIP,mapI) = get_next_constraints pn constraints in
			let l' = List.map (fun x -> Hi.Ci(x)) (constraints @ l) in
			{pn with Pneuma.p = Poly.sub pn.Pneuma.p p ; Pneuma.mapP = MapP.add p l' pn.Pneuma.mapP}
		| _ -> Stdlib.failwith "Heuristic.allUnderMaxDegree"
end

let rec (default : t)
	= fun pn pat->
	match pat with
	| HPattern.Default p -> (*AllUnderMaxDegree.allUnderMaxDegree pn (HPattern.AllUnderMaxDegree p)*)
		exposantDegree pn p
	| _ -> Stdlib.failwith "Heuristic.default"

	and (powerLTOne : t)
		= fun pn pat ->
		match pat with
		| PowerLTOne mon ->
			(try
				HOtypes.Debug.log DebugTypes.Detail
					(lazy(Printf.sprintf "powerLTOne : %s" (Poly.Monomial.to_string mon)));
				let get_coeff : Poly.t -> Poly.Monomial.t -> Q.t
						= fun p mon ->
						let (m,c) = Poly.Monomial.data mon in
						let (_,c') = List.find (fun m' -> Poly.Monomial.compare m' mon = 0) (Poly.data p) |> Poly.Monomial.data
						in Q.mul Q.minus_one (Q.div c c') in
				let (bI,bounds) = (match HLP.run pn.Pneuma.lp pn.Pneuma.ph pn.Pneuma.sx pn.Pneuma.vl mon with
					| (Some bI,bounds) -> HOtypes.Debug.exec HOtypes.Debug.(bI,bounds)
						DebugTypes.Detail (lazy("extractEvenPowers : LP succeed"))
					| (None,bounds) -> Stdlib.raise Not_found) in
				HOtypes.Debug.log DebugTypes.Detail
					(lazy("Result LP = " ^ (Misc.list_to_string Index.Rat.to_string bI " ; ")));
				let id = Index.Int.init (pn.Pneuma.vl |> List.length) in
				let newHi = Hi.VarBounds(id,bI) in
				HOtypes.Debug.log DebugTypes.Detail
					(lazy("new Hi= " ^ (Hi.to_string newHi)));
				let (p',mapIP',mapI') = Pneuma.hi_to_poly newHi pn in
				let mapP' = MapP.add (Poly.mk [mon]) [newHi] pn.Pneuma.mapP in (* MULTIPLIER PAR -1 *)
				let p' = Poly.add pn.Pneuma.p (Poly.mul (get_coeff p' mon |> Poly.cste) p') in
				HOtypes.Debug.log DebugTypes.Detail
					(lazy("next p'= " ^ (Poly.to_string p')));
				{pn with Pneuma.p = p'; Pneuma.mapP = mapP' ; Pneuma.mapIP = mapIP' ; Pneuma.mapI = mapI' ; Pneuma.lp = bounds}
			with Not_found -> default pn (HPattern.Default (Poly.mk [mon])))
		| _ -> Stdlib.failwith "Heuristic.powerLTOne"

	and (extractEvenPowers : t)
		(* extract even powers of an index *)
		= let extract : Index.Int.t -> (Index.Int.t * Index.Int.t)
			= fun id ->
			let (id1,id2) = List.map
				(fun i -> ((i/2)*2, i mod 2))
				(Index.Int.data id)
			|> List.split
			|> fun (i1,i2) -> (Index.Int.mk i1, Index.Int.mk i2)
			in if Index.Int.is_null id2
			then let j = Index.Int.first_positive id1 in
				let id1' = Index.Int.set id1 j ((Index.Int.get id1 j)-2) in
				let id2' = Index.Int.set id2 j 2 in
				(id1',id2')
			else (id1,id2)
		in
		(* computes the polynomial that will be returned to the oracle *)
		let compute_new_poly : Poly.t list -> Poly.t -> Poly.Monomial.t -> Scalar.Rat.t -> Poly.t
			= fun pl poly mon coeff ->
			let pl = List.fold_left
				(fun l p -> try
						let (m',c') = List.find
							(fun m' -> Poly.Monomial.compare m' mon = 0)
							(Poly.data p)
						|> Poly.Monomial.data
						in
						(p,c') :: l
					with Not_found -> l)
				[] pl
			in
			let n = List.length pl in
			Poly.sub
				poly
				(Poly.sum
					(List.map
						(fun (p,c') -> Poly.mul p (Q.div coeff (Q.mul (Q.of_int n) c') |> Poly.cste))
						pl)
				)
		in
		let rec (updateHi : Hi.t list -> Index.Int.t -> Hi.t list)
			= fun hil id ->
			if Index.Int.is_null id
			then hil
			else
				match hil with
				| [] -> []
				| Hi.VarBounds (vI,bIl) :: l -> Hi.VarBounds(Index.Int.add vI id, bIl) :: (updateHi l id)
				| Hi.Ci (ci) :: l -> Hi.VarCi(id,ci) :: (updateHi l id)
				| _ -> Stdlib.failwith "HHeuristic.extractEvenPowers.updateHi"
		in
		fun pn pat ->
		match pat with
		| ExtractEvenPowers (mon,id) ->
			let (m,c) = Poly.Monomial.data mon in
			HOtypes.Debug.log DebugTypes.Normal
				(lazy(Printf.sprintf "extractEvenPowers : %s, %s"
				(Poly.Monomial.to_string mon)
				(Index.Int.to_string id)));
			let (id,idm') = extract id in
			let m' = List.fold_left2
				(fun r i v -> r @ (List.map (fun _ -> v) (Misc.range 0 i)))
				[]
				(Index.Int.data idm') pn.Pneuma.vl
				|> Poly.MonomialBasis.mk
			in
			let p' = Poly.mk [Poly.Monomial.mk m' c] in
			let pn' = {pn with Pneuma.p = p'} in
			let pn' = of_pattern pn' (matching_custom pn' matching_order_nl) in
			let hil = updateHi (MapP.find p' pn'.Pneuma.mapP) id in
			HOtypes.Debug.log DebugTypes.Detail
				(lazy("new Hi= " ^ (Misc.list_to_string Hi.to_string hil " ; ")));
			let (hi_p,mapIP',mapI') = List.fold_left
				(fun (l,mapIP,mapI) hi ->
					let (p,mapIP',mapI') = Pneuma.hi_to_poly hi {pn' with Pneuma.mapIP = mapIP ; Pneuma.mapI = mapI}
					in
					(p :: l,mapIP',mapI'))
				([],pn.Pneuma.mapIP, pn.Pneuma.mapI) hil
			in
			let p' = compute_new_poly hi_p pn.Pneuma.p mon c in
			(*let mapP' = MapP.add pn.Pneuma.p hil pn.Pneuma.mapP in*)
			let mapP' = MapP.add (Poly.mk [mon]) hil (MapPolyHi.merge pn.Pneuma.mapP pn'.Pneuma.mapP) in
			{pn' with Pneuma.p = p'; Pneuma.mapP = mapP' ; Pneuma.mapIP = mapIP' ; Pneuma.mapI = mapI'}
		| _ -> Stdlib.failwith "Heuristic.extractEvenPowers"

	and (linearMonomial : t)
		= fun pn pat ->
		match pat with
		| LinearMonomial m -> {pn with Pneuma.p = Poly.sub pn.Pneuma.p (Poly.mk [m])}
		| _ -> Stdlib.failwith "Heuristic.linearMonomial"

	and (alreadyIn : t)
		= fun pn pat ->
		match pat with
		| AlreadyIn m -> {pn with Pneuma.p = Poly.sub pn.Pneuma.p (Poly.mk [m])}
		| _ -> Stdlib.failwith "Heuristic.AlreadyIn"

	and (of_pattern : t)
		= fun pn pat ->
		HOtypes.Debug.log DebugTypes.Normal (lazy "Heuristic used : ");
		match pat with
		| HPattern.Default _ -> HOtypes.Debug.exec (default pn pat) DebugTypes.Normal (lazy "Default\n")
		| HPattern.AlreadyIn m -> HOtypes.Debug.exec (alreadyIn pn pat) DebugTypes.Normal (lazy "AlreadyIn\n")
		| HPattern.LinearMonomial m -> HOtypes.Debug.exec (linearMonomial pn pat) DebugTypes.Normal  (lazy "LinearMonomial\n")
		| HPattern.ExtractEvenPowers(p,id) -> HOtypes.Debug.exec (extractEvenPowers pn pat) DebugTypes.Normal (lazy "ExtractEvenPowers\n")
		| HPattern.PowerLTOne m -> HOtypes.Debug.exec (powerLTOne pn pat) DebugTypes.Normal (lazy("PowerLTOne\n"))
		| _ -> HOtypes.Debug.exec (default pn (HPattern.Default pn.Pneuma.p)) DebugTypes.Normal (lazy("Unexpected pattern matched, calling default"))

open HOtypes

let (oracle_stop : Pneuma.t -> bool)
	= fun pn ->
	List.length (MapP.bindings pn.Pneuma.mapP) >= 500

let rec (oracle_rec : HPattern.matcher list -> Pneuma.t -> Pneuma.t)
	= fun matchers pn ->
	if Poly.isZ pn.Pneuma.p || (oracle_stop pn)
	then pn
	else let pn' = HPattern.matching pn |> HHeuristic.of_pattern pn in
		HOtypes.Debug.log DebugTypes.Detail
			(lazy (Printf.sprintf "Oracle - Actual State :\n%s" (Pneuma.to_string pn')));
		oracle_rec matchers pn'

let (oracle_custom : Poly.t -> 'c HPol.t -> HPattern.matcher list -> Hi.t list * MapIndexP.t)
	= fun p ph matchers->
	let pn = oracle_rec matchers (Pneuma.init p ph) in
	(MapP.bindings pn.Pneuma.mapP
	|> List.map (fun (_,i) -> i)
	|> List.concat,
	pn.Pneuma.mapIP)

let (oracle: Poly.t -> 'c HPol.t -> Hi.t list * MapIndexP.t)
	= fun p ph->
	oracle_custom p ph HPattern.matching_order

let (check_hi: Poly.t -> Poly.t list -> Hi.t -> bool)
	= fun h ci hi ->
	match hi with
	| Hi.Ci ind ->
	Poly.equal h (List.fold_left
		(fun p i -> let p' = List.nth ci i in
		Poly.add p
			(List.fold_left
			(fun p _ -> Poly.mul p p')
			Poly.u
			(Misc.range 0 i)))
		Poly.z
		(Index.Int.data ind))
	| _ -> true

(*
let (remove_doubles : Hi.t list -> Hi.t list)
	= fun hil ->
	List.fold_left
		(fun l hi -> if List.mem hi l then l else hi :: l)
		[] hil
	*)
let (oracle_hi_custom: Poly.t -> 'c HPol.t -> HPattern.matcher list -> Hi.t list * Poly.t list)
	= fun p ph matching_order ->
	let pn = oracle_rec matching_order (Pneuma.init p ph) in
	let his = MapP.bindings pn.Pneuma.mapP
		|> List.map (fun (_,i) -> i)
		|> List.concat
		|> Misc.rem_dupl Hi.eq
		|> List.filter (fun hi -> Hi.is_linear hi |> not)
		(*|> fun l -> Misc.sublist l 0 100*)
	in
	let polys = List.map (fun hi -> let (p,_,_) = Pneuma.hi_to_poly hi pn in p) his
(*		|> fun l -> Misc.sublist l 0 100*)
	in (his,polys)

let (oracle_hi: Poly.t -> 'c HPol.t -> Hi.t list * Poly.t list)
	= fun p ph ->
	HOtypes.Debug.log DebugTypes.Title (lazy "Linearization Oracle");
	HOtypes.Debug.log DebugTypes.MInput
		(lazy (Printf.sprintf "Polynomial %s\nPolyhedron %s"
		(Poly.to_string p)
		(ph#to_string)));
	let (his,polys) = oracle_hi_custom p ph HPattern.matching_order in
	HOtypes.Debug.exec (his,polys)
		DebugTypes.MOutput (lazy (Printf.sprintf "His = %s\nPolys associated = %s"
			(Misc.list_to_string Hi.to_string his " ; ")
			(Misc.list_to_string Poly.to_string polys " ; ")))

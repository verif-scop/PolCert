open HOtypes

type t = 
| Default of Poly.t
| AllUnderMaxDegree of Poly.t
| ExtractEvenPowers of Poly.Monomial.t * Index.Int.t
| LinearMonomial of Poly.Monomial.t
| Random of Poly.t
| PowerLTOne of Poly.Monomial.t
| AlreadyIn of Poly.Monomial.t

type matcher = Pneuma.t -> t option

let default : matcher
	= fun pn ->
	Some (Default pn.Pneuma.p)

let alreadyIn : matcher
	= fun pn ->
	try 
		Some (AlreadyIn (List.find (fun m -> MapPolyHi.memMonomSigned m pn.Pneuma.mapP) (Poly.data pn.Pneuma.p)))
	with 
	Not_found -> None

let linearMonomial : matcher
	= fun pn ->
	try 
		Some (LinearMonomial (List.find (fun m -> Poly.Monomial.isLinear m || Poly.Monomial.isConstant m) (Poly.data pn.Pneuma.p)))
	with 
	Not_found -> None

let extractEvenPowers : matcher
	= let rec (extractEvenPowersRec : Pneuma.t -> (Poly.MonomialBasis.t * Scalar.Rat.t) list -> V.t list -> t option)
		= fun pn p vl ->
		match p with
		| [] -> None
		| (m,c) :: tl when (MapPolyHi.memMonom m pn.Pneuma.mapP |> not) -> 
			let id = (MapIndexP.poly_to_deg_max (Poly.mk [Poly.Monomial.mk m c]) vl) in
			if Misc.max Stdlib.compare (Index.Int.data id) > 1 
			then Some (ExtractEvenPowers (Poly.Monomial.mk m c,id))
			else extractEvenPowersRec pn tl vl
		| _ -> None
		in fun pn -> 
		extractEvenPowersRec pn (List.map Poly.Monomial.data (Poly.data pn.Pneuma.p)) pn.Pneuma.vl
		
let powerLTOne : matcher
	= fun pn ->
	let one = List.map (fun _ -> 1) pn.Pneuma.vl |> Index.Int.mk in
	try 
		let m = List.find 
			(fun m -> let id = MapIndexP.poly_to_deg_max (Poly.mk [m]) pn.Pneuma.vl in Index.Int.le id one) 
			(Poly.data pn.Pneuma.p) in
			Some (PowerLTOne m)
	with Not_found -> None

let matching_order : matcher list = [alreadyIn ; extractEvenPowers ; linearMonomial ; powerLTOne ; default]

let matching_order_nl : matcher list = [alreadyIn ; powerLTOne ; default]

let rec(matching_custom : Pneuma.t -> matcher list -> t)
		= fun pn l ->
		match l with
		| [] -> Stdlib.failwith "HPattern.matcing_rec"
		| matcher :: tl -> match matcher pn with
			| Some pat -> pat
			| None -> matching_custom pn tl

let (matching : Pneuma.t -> t)
	= fun pn -> 
	matching_custom pn matching_order


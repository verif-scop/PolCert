module Cs = Cstr.Rat.Positive
module V = Cs.Vec.V
module Cons = PLP.Cons
module Cert = Cons.Cert

module Debug = DebugTypes.Debug(struct let name = "CHullBuild" end)

module type Type = sig
	module Min : Min.Type
	module PLP : PLP.Type

	type ('c1,'c2) certT =
		| C1 of 'c1
		| C2 of 'c2

	val build_map : 'c1 Cert.t -> 'c2 Cert.t -> 'c1 Cons.t list -> 'c2 Cons.t list -> V.t list -> PLP.Naming.t -> (('c1,'c2) certT) PLP.mapVar_t

	val build_params : PLP.Naming.t -> 'c1 Cons.t list -> 'c2 Cons.t list -> V.t list * PLP.Naming.t

	val build_vars : 'c1 Cons.t list -> 'c2 Cons.t list -> V.t list * PLP.Naming.t

	val build_constraint : V.t option -> 'c1 Cons.t list -> 'c2 Cons.t list -> Tableau.Vector.t

	val build_constraints : V.t option -> Cs.Vec.t -> V.t list -> 'c1 Cons.t list -> 'c2 Cons.t list -> Tableau.Vector.t list

	val build_obj : V.t list -> 'c1 Cons.t list -> 'c2 Cons.t list -> PLP.PSplx.Objective.t

	val get_init_point : V.t list -> 'c1 Cons.t list -> 'c2 Cons.t list -> Cs.Vec.t

	val build : 'c1 Cert.t -> 'c2 Cert.t -> V.t option -> Cs.Vec.t -> 'c1 Cons.t list -> 'c2 Cons.t list
		-> PLP.PSplx.t * (('c1,'c2) certT) PLP.mapVar_t

	val filter_trivial : (PLP.Region.t * (('c1,'c2) certT) Cons.t) list option -> (PLP.Region.t * (('c1,'c2) certT) Cons.t) list option

	val rem_dupl : (PLP.Region.t * (('c1,'c2) certT) Cons.t) list option -> (PLP.Region.t * (('c1,'c2) certT) Cons.t) list option

	val get_join_cert : 'c1 Cert.t -> 'c2 Cert.t -> 'c1 Cons.t list -> 'c2 Cons.t list
		-> (('c1,'c2) certT) PLP.mapVar_t -> (PLP.Region.t * (('c1,'c2) certT) Cons.t) list option
		-> 'c1 Cons.t list * 'c2 Cons.t list

	val extract_solution : (PLP.Region.t * (('c1,'c2) certT) Cons.t) list option -> (('c1,'c2) certT) Cons.t list

	val print_sxs : (PLP.Region.t * (('c1,'c2) certT) Cons.t) list option -> unit

	val get_no_cert : 'c1 Cert.t -> 'c2 Cert.t -> PLP.PSplx.t -> ('c1, 'c2) certT

	val join : 'c1 Cert.t -> 'c2 Cert.t -> V.t option -> 'c1 Cons.t list -> 'c2 Cons.t list -> 'c1 Cons.t list * 'c2 Cons.t list

end

module Build (Min : Min.Type) = struct
	module Min = Min
	module PLP = PLP.PLP(Min)
	module PSplx = PLP.PSplx
	module Naming = PLP.Naming

	type ('c1,'c2) certT =
		| C1 of 'c1
		| C2 of 'c2

	let build_map : 'c1 Cert.t -> 'c2 Cert.t -> 'c1 Cons.t list -> 'c2 Cons.t list -> V.t list -> Naming.t -> (('c1,'c2) certT) PLP.mapVar_t
		= fun factory1 factory2 p1 p2 vars names ->
		let to_index = Naming.to_index names Naming.Var in
		let trivial_cstr1 = Cons.mkTriv factory1 Cstr.Le Scalar.Rat.u in
		let trivial_cstr2 = Cons.mkTriv factory2 Cstr.Le Scalar.Rat.u in
		let p1_cons = List.map (fun (c,cert) -> c, C1 cert) (p1 @ [trivial_cstr1])
		and p2_cons = List.map (fun (c,cert) -> c, C2 cert) (p2 @ [trivial_cstr2])
		in
		List.fold_left2
			(fun map cons var -> PLP.MapV.add (to_index var) cons map)
			PLP.MapV.empty
			(p1_cons @ p2_cons)
			vars

	let build_params : Naming.t -> 'c1 Cons.t list -> 'c2 Cons.t list -> V.t list * Naming.t
		= fun names p1 p2 ->
		let params = V.Set.union (Cs.getVars (List.map Cons.get_c p1))
				(Cs.getVars (List.map Cons.get_c p2))
			|> V.Set.elements
		in
		(params, Naming.mkParam params names)

	let build_vars : 'c1 Cons.t list -> 'c2 Cons.t list -> V.t list * Naming.t
		= fun p1 p2 ->
		let offset = (List.length p1) + 1 in
		let lambdas_p1 = List.mapi (fun i _ -> V.fromInt (i+1)) p1
		and lambda_add_p1 = V.fromInt offset
		and lambdas_p2 = List.mapi (fun i _ -> V.fromInt (i + 1 + offset)) p2
		and lambda_add_p2 = V.fromInt ((List.length p2) + offset + 1)
		in
		let vars = lambdas_p1 @ [lambda_add_p1] @ lambdas_p2 @ [lambda_add_p2] in
		(vars, Naming.mkVar vars Naming.empty)

	(* if param = None, it is about constant*)
	let build_constraint : V.t option -> 'c1 Cons.t list -> 'c2 Cons.t list -> Tableau.Vector.t
		= fun param p1 p2 ->
		(List.map
			(fun cons ->
				match param with
				| None -> Cons.get_c cons |> Cs.get_c |> Scalar.Rat.neg
				| Some param -> Cons.get_c cons |> Cs.get_v |> fun vec -> Cs.Vec.get vec param)
			p1)
		@
		(* Si la contrainte concerne les constantes : -1, sinon 0*)
		(match param with
		| Some param -> [Scalar.Rat.z]
		| None -> [Scalar.Rat.negU])
		@
		(List.map
			(fun cons ->
				match param with
				| None -> Cons.get_c cons |> Cs.get_c
				| Some param -> Cons.get_c cons |> Cs.get_v |> fun vec -> Cs.Vec.get vec param |> Scalar.Rat.neg)
			p2)
		@
		(* Si la contrainte concerne les constantes : 1, sinon 0*)
		(match param with
		| Some param -> [Scalar.Rat.z]
		| None -> [Scalar.Rat.u])
		@
		[Scalar.Rat.z] (* constante de l'égalité*)

	let build_norm_from_point : Cs.Vec.t -> 'c1 Cons.t list -> 'c2 Cons.t list -> Tableau.Vector.t
		= fun init_point p1 p2 ->
		List.map
			(fun cons ->
				Scalar.Rat.sub
					(Cons.get_c cons |> Cs.get_c)
					(Cs.Vec.dot_product
						init_point
						(Cons.get_c cons |> Cs.get_v))
			)
			p1
		@ [Scalar.Rat.u] (* Coeff of lambda_p1*)
		@ List.map (fun _ -> Scalar.Rat.z) p2
		@ [Scalar.Rat.z] (* Coeff of lambda_p2*)
		@ [Scalar.Rat.u] (* Normalization constant *)

	let build_constraints : V.t option -> Cs.Vec.t -> V.t list -> 'c1 Cons.t list -> 'c2 Cons.t list -> Tableau.Vector.t list
		= fun epsilon_opt init_point params p1 p2 ->
		let params = match epsilon_opt with
		| Some epsilon -> Misc.pop V.equal params epsilon
		| None -> params
		in
		(build_norm_from_point init_point p1 p2)
		:: (build_constraint None p1 p2)
		:: (List.map (fun param -> build_constraint (Some param) p1 p2) params)

	let build_paramCoeff : V.t list -> 'c1 Cons.t -> PLP.ParamCoeff.t
		= fun params cons ->
		let vec = List.map
			(fun param ->
					Cons.get_c cons |> Cs.get_v |> Cs.Vec.neg |> fun vec -> Cs.Vec.get vec param)
			params
		in
		PLP.ParamCoeff.mk vec (Cons.get_c cons |> Cs.get_c)

	let build_obj : V.t list -> 'c1 Cons.t list -> 'c2 Cons.t list -> PLP.Objective.t
		= fun params p1 p2 ->
		let null_paramCoeff = PLP.ParamCoeff.mk (List.map (fun _ -> Scalar.Rat.z) params) Scalar.Rat.z in
		let coeffs = List.map (build_paramCoeff params) p1
			@ [PLP.ParamCoeff.mk (List.map (fun _ -> Scalar.Rat.z) params) Scalar.Rat.u]
			@ List.map (fun _ -> null_paramCoeff) p2
			@ [null_paramCoeff]
		and cste = null_paramCoeff in
		PLP.Objective.mk coeffs cste

	let get_init_point : V.t list -> 'c1 Cons.t list -> 'c2 Cons.t list -> Cs.Vec.t
		= fun params p1 p2 ->
		let horizon = Misc.max V.cmp params
			|> V.next
		in
		match Splx.getPointInside_cone horizon (List.map Cons.get_c p1) with
		| Some point -> Rtree.map Cs.Vec.ofSymbolic point
		| None -> begin
			match Splx.getPointInside_cone horizon (List.map Cons.get_c p2) with
			| Some point -> Rtree.map Cs.Vec.ofSymbolic point
			| None -> let x1 =
				match Opt.getAsg horizon (List.mapi (fun i cons -> i, Cons.get_c cons) p1) with
				| None -> failwith "Unexpected empty polyhedron"
				| Some point -> Rtree.map Cs.Vec.ofSymbolic point
			and x2 =
				match Opt.getAsg horizon (List.mapi (fun i cons -> i, Cons.get_c cons) p2) with
				| None -> failwith "Unexpected empty polyhedron"
				| Some point -> Rtree.map Cs.Vec.ofSymbolic point
			in
			Cs.Vec.divc (Cs.Vec.add x1 x2) (Scalar.Rat.of_float 2.)
			end

	let build : 'c1 Cert.t -> 'c2 Cert.t -> V.t option -> Cs.Vec.t -> 'c1 Cons.t list -> 'c2 Cons.t list
		-> PSplx.t * (('c1,'c2) certT) PLP.mapVar_t
		= fun factory1 factory2 epsilon_opt init_point p1 p2 ->
		let (vars, names) = build_vars p1 p2 in
		let (params, names) = build_params names p1 p2 in
		Debug.log DebugTypes.Detail
			(lazy (Printf.sprintf "init point chosen : %s" (Cs.Vec.to_string Cs.Vec.V.to_string init_point)));
		let mat = build_constraints epsilon_opt init_point params p1 p2 in
		let obj = build_obj params p1 p2 in
		let map = build_map factory1 factory2 p1 p2 vars names in
		{PSplx.obj = obj ; PSplx.mat = mat ; PSplx.basis = [] ; PSplx.names = names},
		map

	(*
	let rewrite_cons : V.t -> 'c Cons.t list -> 'c Cons.t list
		= fun param_const ->
		List.map
			(fun cons ->
				let c = Cons.get_c cons in
				let vec = Cs.Vec.set (Cs.get_v c) param_const (Cs.get_c c |> Cs.Coeff.neg) in
				let cstr = {c with Cs.v = vec ; Cs.c = Scalar.Rat.z} in
				{cons with Cons.c = cstr})
	*)
	let filter_trivial : (PLP.Region.t * (('c1,'c2) certT) Cons.t) list option -> (PLP.Region.t * (('c1,'c2) certT) Cons.t) list option
		= function
		| None -> None
		| Some sols -> Some (List.filter
			(fun (_,cons) ->
				Cs.tellProp (Cons.get_c cons) <> Cs.Trivial
				&& not(Cs.Vec.equal (Cons.get_c cons |> Cs.get_v) Cs.Vec.nil))
			sols)

	let rem_dupl : (PLP.Region.t * (('c1,'c2) certT) Cons.t) list option -> (PLP.Region.t * (('c1,'c2) certT) Cons.t) list option
		= function
		| None -> None
		| Some sols -> Some (Misc.rem_dupl
			(fun (_,cons1) (_,cons2) -> Cs.equal (Cons.get_c cons1) (Cons.get_c cons2))
			sols)

	let get_join_cert : 'c1 Cert.t -> 'c2 Cert.t -> 'c1 Cons.t list -> 'c2 Cons.t list
		-> (('c1,'c2) certT) PLP.mapVar_t -> (PLP.Region.t * (('c1,'c2) certT) Cons.t) list option
		-> 'c1 Cons.t list * 'c2 Cons.t list
		= let get_cert_p1 : 'c1 Cert.t -> (int * Q.t) list -> (('c1,'c2) certT) PLP.mapVar_t -> 'c1
			= fun factory1 basisValue map ->
			List.fold_left
				(fun r_cert (col,q) -> try
					match PLP.MapV.find col map with
					| (c, C1 cert) -> factory1.Cert.add r_cert (factory1.Cert.mul q cert)
					| (_,_) -> Stdlib.failwith "Join.get_join_cert.get_cert_p1"
					with Not_found -> r_cert)
				factory1.Cert.top
				basisValue
		in
		let get_cert_p2 : 'c2 Cert.t -> (int * Q.t) list -> (('c1,'c2) certT) PLP.mapVar_t -> 'c2
			= fun factory2 basisValue map ->
			List.fold_left
				(fun r_cert (col,q) -> try
					match PLP.MapV.find col map with
					| (c, C2 cert) -> factory2.Cert.add r_cert (factory2.Cert.mul q cert)
					| (_,_) -> Stdlib.failwith "Join.get_join_cert.get_cert_p1"
					with Not_found -> r_cert)
				factory2.Cert.top
				basisValue
		in
		let is_strict : (int * Q.t) list -> (('c1,'c2) certT) PLP.mapVar_t -> bool
			= fun basisValue map ->
			List.exists
				(fun (col,_) -> try
					let (c,_) = PLP.MapV.find col map in
					Cs.get_typ c = Cstr.Lt
					with Not_found -> false)
				basisValue
		in
		fun factory1 factory2 p1 p2 map ->
		function
		| None -> [],[]
		| Some sols ->
			(* Colonnes correspondant au premier polyèdre*)
			let p1_col_min = 0 and p1_col_max = List.length p1
			(* Colonnes correspondant au second polyèdre*)
			and p2_col_min = (List.length p1) + 1 and p2_col_max = (List.length p1) + 1 + (List.length p2)
			in
			List.map
				(fun (reg, cons) ->
					(*let cstr = Cs.mulc Scalar.Rat.negU (Cons.get_c cons) in*)
					let cstr = Cons.get_c cons in
					match reg.PLP.Region.sx with
					| None -> Stdlib.failwith "Join.get_join_cert"
					| Some sx ->
						let basisValue = PSplx.getCurVal sx in
						let arg1 = List.filter (fun (i,q) -> p1_col_min <= i && i <= p1_col_max && Scalar.Rat.cmpz q < 0) basisValue
						and arg2 = List.filter (fun (i,q) -> p2_col_min <= i && i <= p2_col_max && Scalar.Rat.cmpz q < 0) basisValue
						in
						if is_strict arg1 map && is_strict arg2 map
						then let cstr' = {cstr with Cs.typ = Cstr.Lt} in
							((cstr', get_cert_p1 factory1 arg1 map),
						 	 (cstr', get_cert_p2 factory2 arg2 map))
						else (* TODO: dans ce cas, il faut élargir les deux certificats*)
							((cstr, get_cert_p1 factory1 arg1 map |> factory1.Cert.to_le),
						 	 (cstr, get_cert_p2 factory2 arg2 map |> factory2.Cert.to_le)))
				sols
			|> List.split

	let extract_solution : (PLP.Region.t * (('c1,'c2) certT) Cons.t) list option -> (('c1,'c2) certT) Cons.t list
		= function
		| None -> []
		| Some sols -> List.map
			(fun (_,(c,cert)) -> {(Cs.compl c) with Cs.typ = c.Cs.typ}, cert)
			sols

	let plot_result : V.t list -> (PLP.Region.t * (('c1,'c2) certT) Cons.t) list option -> unit
		= fun params ->
		function
		| None -> ()
		| Some sols -> PLP.Plot.plot' "/home/amarecha/verasco/vpl2/exp/logs/plot.sage"
			params (List.length params)
			(List.filter (fun (_,cons) -> Cs.tellProp (Cons.get_c cons) <> Cs.Trivial) sols)

	let print_sxs : (PLP.Region.t * (('c1,'c2) certT) Cons.t) list option -> unit
		= function
		| None -> ()
		| Some sols ->
			print_endline (Misc.list_to_string
				(fun (reg, cons) -> Printf.sprintf "Solutions %s : \n%s\n"
					(let c = Cons.get_c cons in Cs.to_string Cs.Vec.V.to_string {(Cs.compl c) with Cs.typ = c.Cs.typ})
					(match reg.PLP.Region.sx with | None -> "none" | Some sx -> PSplx.to_string sx))
				sols "\n")

	let get_no_cert : 'c1 Cert.t -> 'c2 Cert.t -> PSplx.t -> ('c1, 'c2) certT
		= fun factory1 _ _ ->
		C1 factory1.Cert.top

	let join' : 'c1 Cert.t -> 'c2 Cert.t -> V.t option -> 'c1 Cons.t list -> 'c2 Cons.t list
		-> 'c1 Cons.t list * 'c2 Cons.t list
		= fun factory1 factory2 epsilon_opt p1 p2 ->
		let cs = List.map Cons.get_c p1 @ List.map Cons.get_c p2 in
		let params_set = Cs.getVars cs in
		let params = V.Set.elements params_set in
		let init_point = get_init_point params p1 p2	in
		let (sx,map) = build factory1 factory2 epsilon_opt init_point p1 p2 in
		let regs = PLP.run_classic sx (get_no_cert factory1 factory2) in
		let regs_filtered = filter_trivial regs
			|> rem_dupl in
		get_join_cert factory1 factory2 p1 p2 map regs_filtered

	(** Returns the convex hull of the given inequalities (no equality should be given), and the next identifer. *)
	let join : 'c1 Cert.t -> 'c2 Cert.t -> V.t option -> 'c1 Cons.t list -> 'c2 Cons.t list -> 'c1 Cons.t list * 'c2 Cons.t list
		= fun factory1 factory2 epsilon_opt p1 p2 ->
		Debug.log DebugTypes.Title
			(lazy "Convex hull");
		Debug.log DebugTypes.MInput
			(lazy (Printf.sprintf "First polyhedron : %s\nSecond Polyhedron : %s"
				(Misc.list_to_string (Cons.to_string Cs.Vec.V.to_string) p1 "\n")
				(Misc.list_to_string (Cons.to_string Cs.Vec.V.to_string) p2 "\n")));
		let (conss1, conss2) = join' factory1 factory2 epsilon_opt p1 p2 in
		Debug.log DebugTypes.MOutput
			(lazy (Printf.sprintf "Polyhedron1 : %s\nPolyhedron2 : %s"
				(Misc.list_to_string (Cons.to_string_ext factory1 Cs.Vec.V.to_string) conss1 "\n")
				(Misc.list_to_string (Cons.to_string_ext factory2 Cs.Vec.V.to_string) conss2 "\n")));
		(conss1, conss2)

end

module Classic = struct
	module Rat = Build(Min.Classic(Vector.Rat.Positive))

	module Symbolic = Build(Min.Classic(Vector.Symbolic.Positive))

	module Float = Build(Min.Classic(Vector.Float.Positive))
end

module Raytracing = struct
	module Glpk = struct
		module Rat = Build(Min.Glpk(Vector.Rat.Positive))

		module Float = Build(Min.Glpk(Vector.Float.Positive))

		module Symbolic = Build(Min.Glpk(Vector.Symbolic.Positive))
	end
	module Splx = struct
		module Rat = Build(Min.Splx(Vector.Rat.Positive))

		module Float = Build(Min.Splx(Vector.Float.Positive))

		module Symbolic = Build(Min.Splx(Vector.Symbolic.Positive))
	end
end

module Heuristic = struct
	module Rat = Build(Min.Heuristic(Vector.Rat.Positive))

	module Symbolic = Build(Min.Heuristic(Vector.Symbolic.Positive))

	module Float = Build(Min.Heuristic(Vector.Float.Positive))
end

let join : Flags.scalar -> 'c1 Cert.t -> 'c2 Cert.t -> V.t option -> 'c1 Cons.t list -> 'c2 Cons.t list
	-> 'c1 Cons.t list * 'c2 Cons.t list
	= fun scalar factory1 factory2 epsilon_opt p1 p2 ->
	Debug.log DebugTypes.Title (lazy "Building Convex Hull");
	match !Flags.min with
	| Flags.Raytracing Flags.Glpk ->	begin
		match scalar with
  		| Flags.Symbolic -> Raytracing.Glpk.Symbolic.join factory1 factory2 epsilon_opt p1 p2
		| Flags.Float -> Raytracing.Glpk.Float.join factory1 factory2 epsilon_opt p1 p2
		| Flags.Rat -> Raytracing.Glpk.Rat.join factory1 factory2 epsilon_opt p1 p2
		end
	| Flags.Raytracing Flags.Splx -> begin
		match scalar with
  		| Flags.Symbolic -> Raytracing.Splx.Symbolic.join factory1 factory2 epsilon_opt p1 p2
		| Flags.Float -> Raytracing.Splx.Float.join factory1 factory2 epsilon_opt p1 p2
		| Flags.Rat -> Raytracing.Splx.Rat.join factory1 factory2 epsilon_opt p1 p2
		end
	| Flags.Classic -> begin
		match scalar with
  		| Flags.Symbolic -> Classic.Symbolic.join factory1 factory2 epsilon_opt p1 p2
		| Flags.Float -> Classic.Float.join factory1 factory2 epsilon_opt p1 p2
		| Flags.Rat -> Classic.Rat.join factory1 factory2 epsilon_opt p1 p2
		end
	| Flags.MHeuristic -> begin
		match scalar with
  		| Flags.Symbolic -> Heuristic.Symbolic.join factory1 factory2 epsilon_opt p1 p2
		| Flags.Float -> Heuristic.Float.join factory1 factory2 epsilon_opt p1 p2
		| Flags.Rat -> Heuristic.Rat.join factory1 factory2 epsilon_opt p1 p2
		end
	| _ -> Stdlib.failwith "Join.join"

module Debug = DebugTypes.Debug(struct let name = "Proj" end)
module Cs = Cstr.Rat.Positive
module EqSet = PLP.EqSet
module Cons = PLP.Cons
module Cert = Cons.Cert
module V = Cs.Vec.V

(* x+1 car les identifiants commencent à 0 *)
let varEncode : int -> Cs.Vec.V.t
  = fun x -> Cs.Vec.V.fromInt (x+1)

module Proj (Min : Min.Type) = struct

	module PLP = PLP.PLP(Min)

	module Build = struct

		let getCoeffs : V.t option -> Cstr.Rat.Positive.t list -> Scalar.Rat.t list
		  = let get : V.t option -> Cstr.Rat.Positive.t -> Scalar.Rat.t
				= function
				| None -> Cstr.Rat.Positive.get_c
				| Some x -> fun c -> Cs.Vec.get (Cstr.Rat.Positive.get_v c) x
			 in
			 fun x l -> List.map (get x) l

		module Norm = struct

			let translateAlphas : V.Set.t -> Cstr.Rat.Positive.t list -> (Scalar.Rat.t * V.t option) list -> Q.t list
				= fun xs cs l ->
				List.filter (function (_, None) -> true | (_, Some x) -> not (V.Set.mem x xs)) l
				|> List.map (fun (n, x) -> getCoeffs x cs |> List.map (fun n' -> Scalar.Rat.mul n n'))
				|> function
					| [] -> Stdlib.failwith "Build.Norm.translateAlphas"
					| h :: t -> List.fold_left (List.map2 Q.add) h t

			let build : V.Set.t -> Cstr.Rat.Positive.t list -> Tableau.Vector.t
				= let findNormCoeffs : Cstr.Rat.Positive.t list -> (Scalar.Rat.t * V.t option) list
					= let buildCons : V.t -> Cstr.Rat.Positive.t -> Cstr.Rat.Positive.t
						= fun eps c -> {c with Cstr.Rat.Positive.v = Cs.Vec.set (Cstr.Rat.Positive.get_v c) eps Scalar.Rat.u}
				 	in
					let extract : V.t list -> Splx.t -> (Scalar.Rat.t * V.t option) list
						= fun xs sx ->
						let asg =
					Splx.getAsg sx
					|> Rtree.map
					  (fun n ->
						if Scalar.Symbolic.hasDelta n
						then Scalar.Symbolic.toQ n
							(* XXX: tenter de sélectionner un point à l'intérieur *)
							(*Stdlib.failwith "Build.Norm.buildInterior: extract"*)
						else Scalar.Symbolic.get_v n)
					in
					(Scalar.Rat.negU, None) :: List.map (fun x -> (Cs.Vec.get asg x, Some x)) xs
				in
				fun l ->
				let xs = Cstr.Rat.Positive.getVars l in
				let xl = V.Set.elements xs in
				let eps = V.horizon xs in
				Cstr.Rat.Positive.le [Scalar.Rat.negU, eps] Scalar.Rat.z ::
					Cstr.Rat.Positive.le [Scalar.Rat.u, eps] Scalar.Rat.u ::
					List.map (buildCons eps) l
					 |> List.fold_left (fun (i, l') c -> (i + 1, (i, c) :: l')) (0, [])
					 |> Stdlib.snd
					 |> Splx.mk (V.next eps)
					 |> Splx.checkFromAdd
					 |> (fun sx -> Opt.max' sx (Cs.Vec.mk [Scalar.Rat.u, eps]))
					 |> function
						| Splx.IsUnsat _ -> Stdlib.failwith "Build.Norm.buildInterior: unsat"
						| Splx.IsOk Opt.Infty -> Stdlib.failwith "Build.Norm.buildInterior: unbounded"
						| Splx.IsOk (Opt.Sup _) -> Stdlib.failwith "Build.Norm.buildInterior: sup"
						| Splx.IsOk (Opt.Finite (sx', o, _)) ->
				 if Scalar.Rat.isZ o then Stdlib.failwith "Build.Norm.buildInterior: zero"
				 else extract xl sx'
			in
			fun xs l ->
			findNormCoeffs l
			|> translateAlphas xs l
			|> fun v -> v @ [Q.minus_one]

		end

		(** [buildProjCons xs l] builds a list a constraints to be inserted in the
		simplex tableau.  The variables in [xs] must be bounded by the constraints in [l]. *)
		let buildProjCons : V.t list -> Cstr.Rat.Positive.t list -> Tableau.Vector.t list
		  = fun xs cs ->
		  List.map (fun x ->
				 getCoeffs (Some x) cs
				 |> List.map Scalar.Rat.toQ
				 |> fun v -> v @ [Q.zero])
				xs

		let buildObj : bool -> V.t list -> Cstr.Rat.Positive.t list -> PLP.Objective.t
		  = let buildCoeff : bool -> V.t list -> Cstr.Rat.Positive.t -> PLP.ParamCoeff.t
				= fun withConst params c ->
				let v = Cstr.Rat.Positive.get_v c in
				PLP.ParamCoeff.mk (List.map (fun x -> Cs.Vec.get v x |> Scalar.Rat.neg) params)
					 (if withConst then Cstr.Rat.Positive.get_c c else Q.zero)
			 in
			 fun withConst params cs ->
			 PLP.Objective.mk
				(List.map (buildCoeff withConst params) cs)
				(PLP.ParamCoeff.mkSparse (List.length params) [] Q.zero)

		let buildLambdaSum : 'a list -> Tableau.Vector.t
			= fun cstrs -> List.map (fun _ -> Q.one) cstrs @ [Q.one]
	end

	module PSplx = PLP.PSplx
	module Naming = PLP.Naming
	(*
	let rec removeTrivAndDups : (Cs.t * Cons.Cert.frag_t) list -> (Cs.t * Cons.Cert.frag_t) list
	  = function
	  | [] -> []
	  | (c, f) :: l ->
		  match Cs.tellProp c with
		  | Cs.Contrad -> Stdlib.failwith "Sxproj.removeTrivAndDups"
		  | Cs.Trivial -> removeTrivAndDups l
		  | Cs.Nothing ->
		if List.exists (fun (c', _) -> Cs.equal c c') l
		then removeTrivAndDups l
		else (c, f) :: removeTrivAndDups l
	*)
	type projFlagsT
	  = {
		 withCst : bool;
		 withTrivial : bool;
		 nBasicStrat : PLP.Objective.pivotStrgyT;
		 scalar : Flags.scalar
	  }

	let projFlags_to_string : projFlagsT -> string
	  = fun flags ->
	  Printf.sprintf
			"{withCst = %B; withTrivial = %B; sum_lambda = %B; scalar = %s}"
			 flags.withCst flags.withTrivial !Flags.sum_lambda_1
			 (match flags.scalar with
			 | Flags.Symbolic -> "Symbolic"
			 | Flags.Float -> "Float"
			 | Flags.Rat -> "Rat")

	let projFlagsDflt : projFlagsT
	  = {
		 withCst = true;
		 withTrivial = true;
		 nBasicStrat = PLP.Objective.Bland;
		 scalar = Flags.Float;
	  }

	(* XXX: Is it necessary to add the trivial constraint at the end? *)
	let projToTab : 'c Cert.t -> projFlagsT -> Cs.Vec.V.t list -> 'c Cons.t list -> PSplx.t
		= fun factory flags xs l ->
		if !Flags.sum_lambda_1 
		then print_endline "Caution : sum_lambda = true in the projection by PLP";
		let cstrs = List.map Stdlib.fst l in
		let bndSet = Cs.getVars cstrs in
		let projSet = Cs.Vec.V.Set.inter (Cs.Vec.V.Set.of_list xs) bndSet in
		let params = Cs.Vec.V.Set.diff bndSet projSet |> Cs.Vec.V.Set.elements in
		if flags.withTrivial
		then
			let l' = l @ [(Cs.le [] Scalar.Rat.u, factory.Cert.triv Cstr.Le Scalar.Rat.u)] in
			let cstrs' = cstrs @ [Cs.le [] Scalar.Rat.u] in
			 {
				PSplx.obj = Build.buildObj flags.withCst params cstrs';
				PSplx.mat = (if !Flags.sum_lambda_1
					then Build.buildLambdaSum cstrs'
					else Build.Norm.build projSet cstrs')
					::
					Build.buildProjCons (Cs.Vec.V.Set.elements projSet) cstrs';
				PSplx.basis = [];
				PSplx.names =
				Naming.mkParam params Naming.empty
				|> Naming.mkVar (List.mapi (fun i _ -> varEncode i) l')
			 }
		else
			{
				PSplx.obj = Build.buildObj flags.withCst params cstrs;
				PSplx.mat = (if !Flags.sum_lambda_1
					then Build.buildLambdaSum cstrs
					else Build.Norm.build projSet cstrs)
					::
					Build.buildProjCons (Cs.Vec.V.Set.elements projSet) cstrs;
				PSplx.basis = [];
				PSplx.names =
			Naming.mkParam params Naming.empty
				|> Naming.mkVar (List.mapi (fun i _ -> varEncode i) l)
			}

	module type Type = sig
		val proj : 'c Cert.t -> projFlagsT -> Cs.Vec.V.t list -> 'c Cons.t list -> 'c Cons.t list * (Cs.t list * 'c Cons.t) list
	end

	let exec : 'c Cert.t -> projFlagsT -> Cs.Vec.V.t list -> 'c Cons.t list -> 'c Cons.t list * (Cs.t list * 'c Cons.t) list
	  = let rec rmTrivAndDups : 'c Cons.t list -> 'c Cons.t list
			= function
			| [] -> []
			| (c,cert) :: l ->
			 	match Cs.tellProp c with
			 	| Cs.Contrad -> Stdlib.failwith "Sxproj.projectDicho:rmTrivAndDups"
			 	| Cs.Trivial -> rmTrivAndDups l
			 	| Cs.Nothing ->
					if List.exists (fun (c',_) -> Cs.equal c c') l
				 	then rmTrivAndDups l
				 	else (c,cert) :: rmTrivAndDups l
		 in
		 let regsToCs : (PLP.Region.t * 'c Cons.t) list -> 'c Cons.t list * (Cs.t list * 'c Cons.t) list
			= fun regs ->
			Debug.log DebugTypes.MOutput
				(lazy (Printf.sprintf "Regions: \n%s\n"
					(Misc.list_to_string
						(fun (reg,sol) -> Printf.sprintf "%s --> %s"
							(Cons.to_string Cs.V.to_string sol)
							(PLP.Region.to_string reg)) regs "\n")));
			Debug.log DebugTypes.Title (lazy "Building result from regions");
			let sols = rmTrivAndDups (List.split regs |> Stdlib.snd) in
			let regions = List.map
				(fun (reg,sol) -> (PLP.Region.get_cstrs reg, sol))
				regs in
			Debug.log DebugTypes.Title (lazy "Result has been built from regions");
			(sols, regions)
		in
		let explore : 'c Cert.t -> projFlagsT -> PLP.Objective.pivotStrgyT -> PSplx.t -> 'c PLP.mapVar_t -> 'c Cons.t list * (Cs.t list * 'c Cons.t) list
			= fun factory flags strgy tab map ->
			let config = {PLP.std_config with
				PLP.reg_t = (if !Flags.sum_lambda_1 then PLP.NCone else PLP.Cone);
				stgy = strgy;}
			in
			match PLP.run config tab (PLP.get_cert_default factory map) with
			| None -> ([],[])(*XXX: faut il lever une exception?  Stdlib.failwith "Sxproj.projectDicho" *)
			| Some regs -> regsToCs regs
		in
		let init_map : 'c Cons.t list -> PSplx.t -> 'c PLP.mapVar_t
			= fun conss sx ->
			Debug.log DebugTypes.Normal (lazy "Init map");
			let nm = sx.PSplx.names in
			Misc.fold_left_i
				(fun i map cons ->
					let col = Naming.to_index nm Naming.Var (varEncode i) in
					PLP.MapV.add col cons map)
			 	(PLP.MapV.empty) conss
		in
		 fun factory flags xs cs ->
		 if not flags.withCst then Stdlib.failwith "Sxproj.projectDicho: !withCst is unsupported"
		 else
		 	Debug.log DebugTypes.Title (lazy "Building Simplex Tableau");
			let tab = projToTab factory flags xs cs in
			Debug.log DebugTypes.Title (lazy "Reporting Projection");
			let (l,regs) = explore factory flags flags.nBasicStrat tab (init_map cs tab) in
  			(*check cs l (tab.PSplx.names);*)
  			(l,regs)

	let proj : 'c Cert.t -> projFlagsT -> Cs.Vec.V.t list -> 'c Cons.t list -> 'c Cons.t list * (Cs.t list * 'c Cons.t) list
  		= fun factory flags xs ineqs ->
  		Debug.log DebugTypes.Title (lazy "Building Projection");
  		exec factory flags xs ineqs

  	let projDefault : 'c Cert.t -> Cs.Vec.V.t list -> 'c Cons.t list -> 'c Cons.t list * (Cs.t list * 'c Cons.t) list
  		= fun factory xs ineqs ->
  		Debug.log DebugTypes.Title (lazy "Building Default Projection");
  		exec factory projFlagsDflt xs ineqs
end

module Classic = struct
	module Rat = Proj(Min.Classic(Vector.Rat.Positive))

	module Symbolic = Proj(Min.Classic(Vector.Symbolic.Positive))

	module Float = Proj(Min.Classic(Vector.Float.Positive))
end

module Raytracing = struct
	module Glpk = struct
		module Rat = struct
			module Min = Min.Glpk(Vector.Rat.Positive)
			include Proj(Min)
		end

		module Float = struct
			module Min = Min.Glpk(Vector.Float.Positive)
			include Proj(Min)
		end

		module Symbolic = struct
			module Min = Min.Glpk(Vector.Symbolic.Positive)
			include Proj(Min)
		end
	end
	module Splx = struct
		module Rat = struct
			module Min = Min.Splx(Vector.Rat.Positive)
			include Proj(Min)
		end

		module Float = struct
			module Min = Min.Splx(Vector.Float.Positive)
			include Proj(Min)
		end

		module Symbolic = struct
			module Min = Min.Splx(Vector.Symbolic.Positive)
			include Proj(Min)
		end
	end
end

module Heuristic = struct
	module Rat = Proj(Min.Heuristic(Vector.Rat.Positive))

	module Symbolic = Proj(Min.Heuristic(Vector.Symbolic.Positive))

	module Float = Proj(Min.Heuristic(Vector.Float.Positive))
end

let proj : 'c Cert.t -> Flags.scalar -> Cs.Vec.V.t list -> 'c Cons.t list -> 'c Cons.t list * (Cs.t list * 'c Cons.t) list
  		= fun factory scalar xs ineqs ->
  		Debug.log DebugTypes.Title (lazy "Building Projection");
  		match !Flags.min with
  		| Flags.Raytracing Flags.Glpk ->	begin
  			match scalar with
	  		| Flags.Symbolic -> Raytracing.Glpk.Symbolic.projDefault factory xs ineqs
  			| Flags.Float -> Raytracing.Glpk.Float.projDefault factory xs ineqs
  			| Flags.Rat -> Raytracing.Glpk.Rat.projDefault factory xs ineqs
  			end
  		| Flags.Raytracing Flags.Splx -> begin
			match scalar with
	  		| Flags.Symbolic -> Raytracing.Splx.Symbolic.projDefault factory xs ineqs
  			| Flags.Float -> Raytracing.Splx.Float.projDefault factory xs ineqs
  			| Flags.Rat -> Raytracing.Splx.Rat.projDefault factory xs ineqs
  			end
  		| Flags.Classic -> begin
  			match scalar with
	  		| Flags.Symbolic -> Classic.Symbolic.projDefault factory xs ineqs
  			| Flags.Float -> Classic.Float.projDefault factory xs ineqs
  			| Flags.Rat -> Classic.Rat.projDefault factory xs ineqs
  			end
  		| Flags.MHeuristic -> begin
  			match scalar with
	  		| Flags.Symbolic -> Heuristic.Symbolic.projDefault factory xs ineqs
  			| Flags.Float -> Heuristic.Float.projDefault factory xs ineqs
  			| Flags.Rat -> Heuristic.Rat.projDefault factory xs ineqs
  			end
  		| _ -> Stdlib.failwith "Proj.proj"

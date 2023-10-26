module Debug = Hi.Debug

module Cs = PLP.Cs
module CP = CstrPoly.Positive
module Cert = HPol.Cert

let factory : unit Cert.t = {
	Cert.name = "Unit";
	Cert.top = ();
	Cert.triv = (fun _ _ -> ());
	Cert.add = (fun _ _ -> ());
	Cert.mul = (fun _ _ -> ());
	Cert.to_le = (fun _ -> ());
	Cert.merge = (fun _ _ -> ());
	Cert.to_string = (fun _ -> "unit");
	Cert.rename = (fun _ _ _ -> ());
}

module Handelman (Minimization : Min.Type) = struct

	module PLP = PLP.PLP(Minimization)
	module Obj = PLP.PSplx.Objective
	module Poly = Obj.ParamCoeff.Poly
	module Naming = PLP.Naming

	module PLP_MODIF = struct
		open PLP

		let choose_init_point : PSplx.t -> config -> Vec.t * config
			= fun sx config ->
			if config.points = []
			then
				let point = PSplx.getParams sx
					|> List.map (fun p -> (Vec.Coeff.mk1 (Random.int 100),p))
			  		|> Vec.mk
			  	in
			  	(point, {config with points = [ExplorationPoint.Point point]})
			else
				let v = match List.hd config.points with
				| ExplorationPoint.Point v -> v
				| ExplorationPoint.Direction(_,(_,v)) -> v
				in
				(v,config)

		let choose_init_point : 'c HPol.t -> config -> Vec.t * config
			= fun ph config ->
			if config.points = []
			then
				let horizon = ph#horizon() in
				match Region.getPointInside config.reg_t horizon (ph#get_ineqs()) with
				| None -> Stdlib.failwith "Handelman.PLP.init : unexpected empty input polyhedron"
				| Some point ->
					(point, {config with points = [ExplorationPoint.Point point]})
			else
				let v = match List.hd config.points with
				| ExplorationPoint.Point v -> v
				| ExplorationPoint.Direction(_,(_,v)) -> v
				in
				(v,config)

		let init_and_exec : 'c HPol.t ->  config -> PSplx.t -> (PSplx.t -> 'c) -> t option
			= fun ph config sx get_cert ->
			let (point,config) = choose_init_point ph config in
			if InitSx.init point config sx
			then
				let plp = {
				regs = init_regions config;
				todo = config.points
				} in
				Some (exec config plp)
			else None

		let run : 'c HPol.t -> config -> PSplx.t -> (PSplx.t -> 'c) -> (Region.t * 'c PLPCore.Cons.t) list option
			= fun ph config sx get_cert ->
			PLPCore.Stat.reset();
			Random.init 0;
			Debug.log DebugTypes.Title
				(lazy("PLP solver with scalar_type = " ^ (Vec.Coeff.name)));
			Debug.log DebugTypes.MInput
				(lazy (Printf.sprintf "Exploration points provided : %s\n%s"
					(Misc.list_to_string ExplorationPoint.to_string config.points " ; ")
					(PSplx.to_string sx)));
			Debug.log DebugTypes.MInput
				(lazy (Printf.sprintf "Regions provided : %s\n"
					(Misc.list_to_string Region.to_string config.regions " ; ")));
			match init_and_exec ph config sx get_cert with
			| None -> None
			| Some plp -> begin
				let res = get_results plp get_cert in
				if PLPCore.Debug.is_enabled DebugTypes.Sage
				then begin
					match res with
					| None -> ()
					| Some regs -> Plot.plot regs
				end;
				res
			end

		let init_region : 'c HPol.t -> region_t -> Region.t list
			= fun ph region_type ->
			let horizon = ph#horizon() in
			List.mapi
				(fun id ineq ->
					match Region.getPointInside region_type horizon [ineq], Region.getPointInside region_type horizon [Cs.compl ineq] with
					| None,_ | _,None -> Stdlib.failwith "Handelman.PLP.init_region : unexpected empty region"
					| Some pInside, Some pOutside -> let boundary = (Cs.compl ineq, pInside) in
						{  id = id;
							Region.r = [boundary, None];
							Region.point = pOutside;
							Region.sx = None})
				(ph#get_ineqs())

		let run_plp : 'c HPol.t -> Obj.pivotStrgyT -> PSplx.t -> bool -> (Region.t * 'c PLPCore.Cons.t) list option
			= fun ph st sx is_normalized ->
			let region_type = if is_normalized then Cone else NCone in
			let config' = {std_config with
				reg_t = region_type;
				stgy = st;
				regions = init_region ph region_type;
				} in
			run ph config' sx (get_no_cert factory)
	end

	module Build = struct

		let obj_buildOfPoly : Poly.t list -> Poly.t -> Obj.t * Naming.t
		  = let module VSet = Set.Make (struct type varT = Poly.V.t type t = varT let compare = Poly.V.cmp end) in
			 let gatherParams1 : Poly.t -> VSet.t
				= fun p ->
				Poly.data2 p
				|> List.map Stdlib.fst
				|> List.concat
				|> List.fold_left (fun s x -> VSet.add x s) VSet.empty
				(*|> VSet.remove Poly.V.null*)
			 in
			 let gatherParams : Poly.t list -> (int * Poly.V.t) list
				= fun l ->
				List.map gatherParams1 l
				|> List.fold_left VSet.union VSet.empty
				|> VSet.elements
				|> List.mapi (fun i x -> (i, x))
			 in
			 fun lin cst ->
			 if not (List.for_all Poly.is_affine lin && Poly.is_affine cst)
			 then Stdlib.invalid_arg "Obj._buildOfPoly"
			 else
				let l = gatherParams (cst :: lin) in
				let nm =
			List.fold_left (fun nm' (i, x) -> Naming.allocAt Naming.Param x i nm')
						 Naming.empty
						 l
				in
				let lin' = List.map (Obj.ParamCoeff.ofPoly (Naming.to_index nm Naming.Param) (List.length l)) lin in
				let cst' = Obj.ParamCoeff.ofPoly (Naming.to_index nm Naming.Param) (List.length l) cst in
				(Obj.mk lin' cst', nm)

		let obj_of_polyList : Poly.t list -> Obj.t * Naming.t
		  = fun l ->
		  if List.length l < 1 then Stdlib.invalid_arg "Obj.of_polyList"
		  else
			 let l' = List.rev l in
			 obj_buildOfPoly (List.tl l' |> List.rev) (List.hd l')

		let obj_of_polySparseList : int -> (int * Poly.t) list -> Poly.t -> Obj.t * Naming.t
		  = let rec fill : int -> int -> (int * Poly.t) list -> Poly.t list
				= fun n i ->
				function
				| [] -> if i < n then Poly.z :: fill n (i + 1) [] else []
				| ((x, a) :: l') as l ->
			 if n <= i || x < i then Stdlib.invalid_arg "Obj.of_polySparseList"
			 else if x = i then a :: fill n (i + 1) l'
			 else Poly.z :: fill n (i + 1) l
			 in
			 fun n l a ->
			 obj_buildOfPoly (List.sort (fun (i, _) (i', _) -> Stdlib.compare i i') l |> fill n 0) a

		let rec obj_of_poly : Poly.t -> Poly.V.t list -> Obj.t * Naming.t
		  = fun p l ->
		  let lin = List.map (fun x -> Poly.monomial_coefficient_poly p (Poly.MonomialBasis.mk [x])) l in
		  let cst = Poly.sub p
			(List.fold_left
				(fun p1 x -> Poly.add
					p1
					(Poly.mul
						(Poly.monomial_coefficient_poly p (Poly.MonomialBasis.mk [x]))
						(Poly.mk2 [([x], Scalar.Rat.u)])))
			Poly.z l)
		  |> Poly.mul Poly.negU in
		  obj_buildOfPoly lin cst

		(* data/mk à améliorer *)
		(** row_from_constraint p mb converts the Poly.t p into a row*)
		let rec (row_from_constraint : Poly.t -> Poly.V.t list -> Tableau.Vector.t)
		  = fun p vars ->
		  match vars with
		  | [] -> [Scalar.Rat.mul (Scalar.Rat.negU) (Poly.monomial_coefficient p Poly.MonomialBasis.null)]
		  | var :: tail -> let coeff = Poly.monomial_coefficient p (Poly.MonomialBasis.mk [var]) in
					coeff::(row_from_constraint p tail);;

		let from_poly : Poly.V.t list -> Poly.t list -> Poly.t list -> Poly.t -> Poly.t option -> PLP.PSplx.t
		  = fun vars ineqs eqs obj normalization ->
		  if List.length vars + List.length ineqs < List.length ineqs + List.length eqs
		  then Stdlib.invalid_arg "PSplx.Build.from_poly: variables"
		  else
			 if List.exists Poly.isZ ineqs || List.exists Poly.isZ eqs
			 then Stdlib.invalid_arg "PSplx.Build.from_poly: constraints"
			 else
				let (o, nm) = obj_of_poly obj vars in
				{
			PLP.PSplx.obj = o;
			PLP.PSplx.mat = List.map
				(fun r -> row_from_constraint r vars)
				((match normalization with Some n -> [n] | None -> []) @ (ineqs @ eqs));
			PLP.PSplx.basis = [];
			PLP.PSplx.names = Naming.mkVar vars nm
				}
				|> PLP.PSplx.addSlacks (List.length ineqs)

		let polyToParamCoeff : PLP.PSplx.t -> Poly.t -> Obj.ParamCoeff.t
		  = fun sx p ->
		  Obj.ParamCoeff.ofPoly (Naming.to_index sx.PLP.PSplx.names Naming.Param)
				  (PLP.PSplx.nParams sx) p
	end

	let (get_non_linear_monomials : Poly.t -> Poly.V.t list -> Poly.MonomialBasis.t list)
		= let rec(get_non_linear_monomials_rec : (Poly.V.t list * Q.t) list -> Poly.V.t list -> Poly.MonomialBasis.t list)
			= fun p variables ->
			match p with
			| [] -> []
			| (vlist,coeff) :: tail -> let mlist = get_non_linear_monomials_rec tail variables in
				let vlist2 = List.filter (fun x -> List.mem x variables) vlist in
					if not (List.mem (Poly.MonomialBasis.mk vlist2) mlist) && List.length vlist2 > 1
						then (Poly.MonomialBasis.mk vlist2) :: mlist
						else mlist
		in fun p variables ->
		get_non_linear_monomials_rec (Poly.data2 p) variables

	let (get_non_linear_coeffs: Poly.t -> Poly.V.t list -> Poly.t list)
		= fun p variables ->
		let mlist = get_non_linear_monomials p variables in
		List.map
		(fun vlist -> Poly.monomial_coefficient_poly p vlist)
		mlist

	module Norm = struct

		(** Projects the given point on the given subspace. *)
		let project_point : Poly.V.t list -> Poly.Vec.t -> Poly.Vec.t
			= fun params point ->
			let vec = List.map (fun param -> (Poly.Vec.Coeff.u, param)) params
				|> Poly.Vec.mk
			in
			Poly.Vec.mul_t vec point

		(** Returns a point (as a function) within the polyhedron to project.
		If the answer is [None], it means that the polyhedron is empty! *)
		let getPointInside : Cs.t list -> Poly.V.t list -> (Poly.V.t -> Scalar.Rat.t option) option
			= fun cstrs params ->
			match Opt.getAsg_raw cstrs with
			| None -> None
			| Some point -> begin
				let vec = Rtree.map (Vector.Rat.Positive.ofSymbolic) point
				|> project_point params in
				Debug.log DebugTypes.Detail (lazy(Printf.sprintf "normalization point : %s"
					(Poly.Vec.to_string Poly.V.to_string vec)));
				Some (fun v ->
				if List.mem v params
				then Some (Poly.Vec.get vec v)
				else None)
				end

		(** Returns the normalization constraint and a point (as a function) within the polyhedron to project.
		If the answer is [None], it means that the polyhedron is empty!
		TODO : adapt the normalization constant to the polynomial. *)
		let get : 'c HPol.t -> Poly.t list -> Poly.t -> Poly.t -> (Poly.t * (Poly.V.t -> Scalar.Rat.t option)) option
			= fun ph his_p objective f ->
			let variables = List.map Poly.get_vars (f :: his_p)
				|> List.concat
				|> Misc.rem_dupl Poly.V.equal
			in
			let non_linear_monomials = List.map
				(fun p ->
					Poly.sub p (Poly.get_affine_part p variables)
					|> Poly.data
					|> List.map Poly.Monomial.data
					|> List.map Stdlib.fst)
				(f :: his_p)
				|> List.concat
				|> Misc.rem_dupl Poly.MonomialBasis.equal
			in
			Debug.log DebugTypes.Detail (lazy(Printf.sprintf "Non linear monomials : %s"
				(Misc.list_to_string Poly.MonomialBasis.to_string non_linear_monomials " ; ")))
			;
			let horizon = Poly.horizon (f :: his_p) in
			let change_of_vars = List.fold_left
				(fun (f,horizon) m ->
					let m_h = Poly.MonomialBasis.mk [horizon] in
					((fun m' ->	if Poly.MonomialBasis.equal m m' then Some m_h else f m'),
					 Poly.V.next horizon))
				((fun _ -> None), horizon)
				non_linear_monomials
				|> Stdlib.fst
			in
			let his_p' = List.map (Poly.change_variable change_of_vars) (f :: his_p) in
			Debug.log DebugTypes.Detail (lazy(Printf.sprintf "Change_of_var : %s"
				(Misc.list_to_string Poly.to_string his_p' " ; ")))
			;
			let his_p'_cstr = List.map (CP.mk Cstr.Le) his_p'
				|> List.map (fun p -> CP.compl p |> CP.toCstr)
			in
			let ineqs = List.map (fun c -> {c with Cs.typ = Cstr.Lt}) (ph#get_ineqs() @ his_p'_cstr)
			in
			Debug.log DebugTypes.Detail
				(lazy (Printf.sprintf "get : ineqs = %s" (Cs.list_to_string ineqs)));
			Debug.log DebugTypes.Detail
				(lazy (Printf.sprintf "Projecting polyhedron of monomials : \n%s"
					(let vars_to_project = List.filter
						(fun v -> not (List.exists
							(fun v' -> Cs.Vec.V.equal v v') variables))
							(Cs.getVars ineqs |> Cs.Vec.V.Set.elements)
					in
					Proj.proj Factory.Unit.factory Flags.Float vars_to_project
						(List.map Factory.Unit.mk ineqs)
					|> Stdlib.fst
					|> List.map Stdlib.fst
					|> List.map Cs.canon
					|> Cs.list_to_string)))
			;
			match getPointInside ineqs (ph#get_vars) with
			| None -> None
			| Some pointInside ->
				match !Flags.handelman_normalize with
				| None -> None
				| Some constant ->
					let res = Poly.sub
						(Poly.eval_partial objective pointInside)
						(Poly.cste constant)
					in
					Some (res, pointInside)
	end

	let handelman : Obj.pivotStrgyT -> 'c HPol.t -> Poly.t list -> Poly.t
		-> (PLP.Region.t * 'c Pol.Cons.t) list option
		= fun st ph his_p f ->
		let variables = ph#get_vars in
		let nb_h = (List.length his_p) in
		let n = Var.Positive.next (Misc.max Poly.V.cmp variables) |> Var.Positive.toInt in
		let lpvars = List.map
			(fun i -> Var.Positive.fromInt i)
			(Misc.range n (nb_h + n))
		in
		(* le ième Hi est associé à la variable numéro i*)
		let flin = 	(List.fold_right
				(fun i p -> Poly.add
					(Poly.mul
						(Poly.mk2 [([List.nth lpvars i], Scalar.Rat.u)])
						(List.nth his_p i))
					p)
				(Misc.range 0 nb_h) (* le premier indice est associé à la contrainte triviale*)
				f)
		in
		let simplex_equalities = get_non_linear_coeffs flin variables in
		let simplex_inequalities = [] in
		let objective = Poly.get_affine_part flin variables in
		Debug.log DebugTypes.Normal
			(lazy("Objective = " ^ (Poly.to_string objective)));
		let normalization = match Norm.get ph his_p objective f with
		| Some (n, _) -> begin
			Debug.log DebugTypes.Normal
				(lazy ("Normalization : " ^ (Poly.to_string n)));
			Some n
			end
		| None -> None
		in
		try
		begin
			let sx = Build.from_poly lpvars simplex_inequalities simplex_equalities objective normalization in
			Debug.log DebugTypes.Detail (lazy("Simplex tableau : \n" ^ (PLP.PSplx.to_string sx)));
(*			Debug.log DebugTypes.Detail (lazy("Basis : " ^ (Misc.list_to_string PLP.PSplx.to_string sx)));*)
			try PLP_MODIF.run_plp ph st sx (normalization <> None)
			with Failure s ->
				Debug.exec None DebugTypes.Detail (lazy("Handelman Exception: " ^ s))
		end
		with
			Invalid_argument s -> Debug.exec None DebugTypes.Detail (lazy("Handelman : invalid_argument -> " ^ s))

	(** It puts strict inequalities when possible (gathering this information from the certificate). *)
	let adjustCmp : Cs.t list -> Hi.t list -> (int * Scalar.Rat.t) list -> Cstr.cmpT
		= let cICmp : Cs.t list -> Hi.cIndex -> Cstr.cmpT
			= fun cstrs cI ->
			List.fold_left2
			(fun cmp cstr i -> if i <> 0
				then Cs.cmpAdd cmp (cstr.Cs.typ)
				else cmp)
			Cstr.Le
			cstrs (Index.Int.data cI)
			in
		let hiCmp : Cs.t list -> Hi.t -> Cstr.cmpT
			= fun cstrs hi ->
			let cICmp_ins = cICmp cstrs in
			match hi with
			| Hi.Ci cI | Hi.VarCi (_,cI) -> cICmp_ins cI
			| Hi.VarBounds (_,_) -> Cstr.Le
		in
		let iCmp : Cs.t list -> Hi.t list -> int -> Cstr.cmpT
			= fun cstrs his i ->
			hiCmp cstrs (List.nth his i)
		in
		fun cstrs his cert ->
		let iCmp_ins = iCmp cstrs his in
		List.fold_left
			(fun cmp (i,q) -> Cs.cmpAdd cmp (iCmp_ins i))
			Cstr.Le
			cert

	let compute_certs : Hi.t list -> int -> Poly.V.t list -> (PLP.Region.t * 'c PLPCore.Cons.t) list
		-> (CP.t * Hi.Cert.schweighofer list) list
		= fun his n_cstrs vars regs ->
			let compute_cert : (int * Scalar.Rat.t) list -> Hi.Cert.schweighofer list
				= fun l ->
				List.filter (fun (_,q) -> not (Scalar.Rat.isZ q)) l
				|> List.map
					(fun (i,q) ->
						List.nth his i
						|> Hi.Cert.hi_to_cert n_cstrs vars q)
			in
			List.map
				(fun (reg, cons) ->
					let cstr = PLPCore.Cons.get_c cons in
					let cp = CP.ofCstr cstr in
					match reg.PLP.Region.sx with
					| Some sx ->
						let value = PLP.PSplx.getCurVal sx in
						let cert = compute_cert value in
						(cp, cert)
					| None -> Stdlib.failwith "Handelman.compute_certs")
			regs

	let run : 'c HPol.t -> Hi.t list -> Poly.t list -> Poly.t -> (CP.t * Hi.Cert.schweighofer list) list option
		= fun ph his his_poly g ->
		Debug.log DebugTypes.Title (lazy "Handelman");
		Debug.log DebugTypes.MInput
			(lazy(Printf.sprintf "His = %s\n His_poly = %s\ng = %s\n"
			(Misc.list_to_string Hi.to_string his " ; ")
			(Misc.list_to_string Poly.to_string his_poly " ; ")
			(Poly.to_string g)));
		(* XXX: faut il ajuster les comparaisons avec -1* les contraintes? *)
		match handelman Obj.Bland ph his_poly g with
		| None -> None
		| Some regs -> begin
			let vars = ph#get_vars in
			let n_cstrs = List.length ph#get_poly_rep in
			let res = compute_certs his n_cstrs vars regs in
			Debug.log DebugTypes.MOutput
				(lazy(Misc.list_to_string CP.to_string (List.map Stdlib.fst res) "\n "))
            ;
			Debug.log DebugTypes.MOutput
				(lazy(Printf.sprintf "Handelman certificates : %s"
                    (Misc.list_to_string
                            (fun (cp, cert) -> Printf.sprintf "%s -> %s"
                                (CP.to_string cp)
                                (Hi.Cert.to_string cert)
                            )
                            res "\n"
                            )))
			;
			Some res
			end
			(*let adjustCmp_ins = adjustCmp (ph#get_cstr()) his in
			let res = compute_certs his regs in
			let l =
			List.map
				(fun (csP,cert) -> let csP' = {csP with CP.typ = adjustCmp_ins cert}
					in (csP',cert))
				res
			in
			Some l*)

	exception Timeout

	module type Type = sig
		type t = {
			ph : unit HPol.t ;
			g : Poly.t;
		}

		val mkHPol : 'c Pol.t -> unit HPol.t

		(** Used for Coq only *)
		val run_oracle : 'c Pol.t -> CP.t -> (CP.t * Hi.Cert.schweighofer list) list option

		val run : 'c Pol.t -> CP.t list -> t
	end

	module Pb : Type = struct

	  	let running_time : float Stdlib.ref
	  		= Stdlib.ref 0.0

		type t =
			{ph : unit HPol.t ;
			 g : Poly.t}

		let (is_empty : t -> bool)
	  		= fun pb ->
	  		pb.ph#is_empty

		let empty : t = {ph = new HPol.t ; g = Poly.z}

		let current_result : t list ref = ref []

		let (run_one : t -> t)
			= fun pb ->
			let (his,his_poly) = HOracle.oracle_hi pb.g pb.ph in
			match run pb.ph his his_poly pb.g with
			| None -> pb
			| Some result ->
				let p = result
					|> List.split
					|> Stdlib.fst
					|> List.map (fun cp -> (cp, factory.Cert.top))
				in
				let ph' = pb.ph#addM factory p in
				{pb with ph = ph'}

		let (poly_equal : t -> t -> bool)
			= fun pb1 pb2 ->
			pb1.ph#equal factory factory pb2.ph

		let (poly_equal_opt : t -> t option -> bool)
			= fun pb1 pb2 ->
			match pb2 with
			| Some pb2 -> poly_equal pb1 pb2
			| None -> false

		let rec (run_rec : t -> Poly.t list -> t list)
			= fun pb pl ->
			match pl with
			| [] -> [pb]
			| g::tl -> if pb.ph#is_empty
				then [pb]
				else let pb = run_one {pb with g = g} in
					pb :: (run_rec pb tl)

		let rec (run_loop_rec : t -> Poly.t list -> Poly.t list -> t option -> unit)
			= fun pb pl pl_cpy pb_prev ->
			match pl with
			| [] -> if pb.ph#is_empty
				then current_result := !current_result @ [pb]
				else if poly_equal_opt pb pb_prev
					then current_result := !current_result @ [pb]
					else begin
						current_result := !current_result @ [pb];
						run_loop_rec pb pl_cpy pl_cpy (Some pb)
						end
			| g::tl -> if pb.ph#is_empty
				then current_result := !current_result @ [empty]
				else let pb = run_one {pb with g = g} in
					current_result := !current_result @ [pb];
					run_loop_rec pb tl pl_cpy pb_prev

		let (run_loop : t -> Poly.t list -> t list)
			= fun pb pl ->
			current_result := [];
			try
				run_loop_rec pb pl pl None;
				!current_result
			with
			| Timeout -> !current_result

		let rewrite_polynomials : 'c Pol.t -> CP.t list -> CP.t list
			(* returns the polynomial equal to v in Cons *)
			= let get_eq : Cs.Vec.V.t -> 'c Pol.Cons.t -> Cs.t
				= fun v cons ->
				let cstr = Pol.Cons.get_c cons in
				let vec = Cs.get_v cstr in
				let coeff = Cs.Vec.get vec v in
				Cs.add
					cstr
					(Cs.mk (Cs.get_typ cstr) [Scalar.Rat.neg coeff,v] Scalar.Rat.z)
				|> Cs.mulc (Scalar.Rat.inv (Scalar.Rat.neg coeff))
			in
			let rewrite_var : Poly.V.t -> Poly.t -> Poly.t -> Poly.t
				= fun v p p' ->
				List.map
					(fun mon -> let (mb,c) = Poly.Monomial.data mon in
						let vs = Poly.MonomialBasis.data mb in
						let (eq_v,vs') = List.partition (fun var -> Poly.V.equal var v) vs in
						let product = Poly.pow p' (List.length eq_v) in
						Poly.mk [Poly.Monomial.mk (Poly.MonomialBasis.mk vs') c]
						|> Poly.mul product
					)
					(Poly.data p)
				|> Poly.sum
			in
			let rewrite_poly : 'c Pol.EqSet.t -> CP.t -> CP.t
				= fun eqs p ->
				let p' =
				List.fold_left
					(fun p (v,cons) ->
						print_endline (Printf.sprintf "%s -> %s" (Cs.Vec.V.to_string v) (Pol.Cons.to_string Cs.Vec.V.to_string cons));
						let cstr = get_eq v cons in
						let p' = Poly.ofCstr (Cs.get_v cstr) (Cs.get_c cstr) in
						rewrite_var v p p'
					)
					(p.CP.p)
					eqs
				in
				{p with CP.p = p'}
			in
			fun ph pl ->
			let eqs = Pol.get_eqs ph in
			let rewrite = rewrite_poly eqs in
			List.map rewrite pl

		let timeout : int -> unit
			= fun i -> match i with
			| j when j = Sys.sigalrm -> Stdlib.raise Timeout
			| _ -> ()

		let remove_timeout : _ -> unit
			= fun _ -> ()

		let mkHPol : 'c Pol.t -> unit HPol.t
			= fun phPol ->
			let phPol_unit = Pol.to_unit phPol in
			let ph = new HPol.t in
			ph#mkPol phPol_unit;
			ph

		(** Used for Coq only *)
		let run_oracle : 'c Pol.t -> CP.t -> (CP.t * Hi.Cert.schweighofer list) list option
			= fun phPol poly ->
			Debug.log DebugTypes.Title (lazy "Handelman.Pb");
			Debug.log DebugTypes.MInput
				(lazy (Printf.sprintf "Polyhedron %s and polynomial constraint %s"
				(Pol.to_string Cs.Vec.V.to_string phPol)
				(CP.to_string poly)));
			let ph = mkHPol phPol in
			let pl' = rewrite_polynomials phPol [poly] (* rewritting w.r.t equalities in phPol *)
				|> List.fold_left
					(fun res cp -> (HOtypes.Pneuma.neg_poly cp) @ res) []
				(* Putting the polynomial on the form p >= 0*)
			in
			Debug.log DebugTypes.Detail
				(lazy (Printf.sprintf "Rewritted polynomials in nonnegative form using equalities into %s"
				(Misc.list_to_string Poly.to_string pl' " ; ")));
			match pl' with
			| [g] -> let (his,his_poly) = HOracle.oracle_hi g ph in
				run ph his his_poly g
			| _ -> Stdlib.failwith "Handelman.pb.run_oracle"

		let (run : 'c Pol.t -> CP.t list -> t)
			= fun phPol pl ->
			Debug.log DebugTypes.Title (lazy "Handelman.Pb");
			Debug.log DebugTypes.MInput
				(lazy (Printf.sprintf "Polyhedron %s and polynomial constraints %s"
				(Pol.to_string Cs.Vec.V.to_string phPol)
				(Misc.list_to_string CP.to_string pl " ; ")));
			let ph = mkHPol phPol in
			let pl' = rewrite_polynomials phPol pl (* rewritting w.r.t equalities in phPol *)
				|> List.fold_left
					(fun res cp -> (HOtypes.Pneuma.neg_poly cp) @ res) []
				(* Putting the polynomial on the form p >= 0*)
			in
			Debug.log DebugTypes.Detail
				(lazy (Printf.sprintf "Rewritted polynomials in nonnegative form using equalities into %s"
				(Misc.list_to_string Poly.to_string pl' " ; ")));
			let pb = {ph = ph ; g = Poly.z} in
			begin
			match !Flags.handelman_timeout with
			| Some i ->
				Sys.set_signal Sys.sigalrm (Sys.Signal_handle timeout);
				let _ = Unix.alarm i in
				()
			| None -> ()
			end;
			let res =
				if !Flags.handelman_loop
				then run_loop pb pl'
				else run_rec pb pl'
			in
			Sys.set_signal Sys.sigalrm (Sys.Signal_handle remove_timeout);
			match res with
			| [] -> Stdlib.failwith "Handelman.run: no output produced"
			| _ -> List.nth res ((List.length res)-1)

		end

end


module Rat = Handelman(Min.Classic(Vector.Rat.Positive))

module Symbolic = Handelman(Min.Classic(Vector.Symbolic.Positive))

module Float = Handelman(Min.Classic(Vector.Float.Positive))


(*
	let init_map : 'c Cert.t -> int -> 'c Cons.t PLP.MapV.t
		= fun factory nb_his ->
		let trivial_cstr = Cs.mk Cstr.Le [] Scalar.Rat.u in
		List.fold_left
			(fun map i -> PLP.MapV.add i (Pol.Cons.triv factory) map)
			PLP.MapV.empty
			(Misc.range 0 nb_his)
	*)
	(*
	module Norm = struct
		let getPointInside : Cs.t list -> Poly.V.t list -> Poly.V.t -> Scalar.Rat.t option
			= fun cstrs params v ->
			let horizon = Cs.getVars cstrs
				|> Cs.Vec.V.horizon
			in
			match Splx.getAsgOpt horizon (List.mapi (fun i c -> (i,c)) cstrs) with
			| None -> Stdlib.failwith "getPointInside : empty polyhedron"
			| Some point ->
				let vec = Rtree.map (Vector.Rat.Positive.ofSymbolic) point in
				if List.mem v params
				then Some (Vector.Rat.Positive.get vec v)
				else None

		let get : 'c HPol.t -> Poly.t -> Poly.t * (Poly.V.t -> Scalar.Rat.t option)
			= fun ph objective ->
			let ineqs = List.map (fun c -> {c with Cs.typ = Cstr.Lt}) (ph#get_ineqs()) in
			Debug.log DebugTypes.Detail
				(lazy (Printf.sprintf "get : ineqs = %s" (Cs.list_to_string ineqs)));
			(*List.map (Cs.mulc Scalar.Rat.negU) (ph#get_ineqs())*) (* XXX: mais purkwa? *)
			let pointInside = getPointInside ineqs (ph#get_vars) in
			let res = Poly.sub
				(Poly.eval_partial objective pointInside)
				(Poly.cste Scalar.Rat.u) (* This is the normalization constraint constant *)
		(*	|> fun res -> Poly.mulc res Scalar.Rat.negU*)
			in
			(res, pointInside)
	end
	*)

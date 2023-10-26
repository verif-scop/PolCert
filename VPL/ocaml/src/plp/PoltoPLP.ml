module Cons = PLP.Cons
module Cert = Cons.Cert
module Cs = Cstr.Rat.Positive
module Vec = Cs.Vec
module V = Cs.Vec.V

module MinFloat = Min.Classic(Vec)
module B = Join.Build(MinFloat)
include B

	(*
	(* À priori inutile *)
	(** [computePoints x0 cstrs x'] takes the result of a minimization and the inner point on which it was done.
	It attaches to each constraint a new point within the polyhedron. *)
	let computePoints : Vec.t -> (Cs.t * Vec.t) list -> Vec.t -> (Cs.t * Vec.t) list
		= fun x0 cstrs x' ->
		let conv = MinFloat.vecInput_Vec in
		let convCs = MinFloat.float_of_cstr in
		List.map
			(fun (cstr,x) ->
			let (direction,value) =
				let direction = MinFloat.TwoPoints (conv x, conv x0) in
				let value = MinFloat.Sort.value direction (convCs cstr) in
				(direction,value)
				(*if Vec.Coeff.well_formed_nonnull value
				then (direction,value)
				else begin
					let normal = MinFloat.Sort.normal cstr in
					let direction = MinFloat.Normal(x0,normal) in
					let value = MinFloat.Sort.value direction cstr in
					(direction,value)
				end*)
			in
			(* intersection between [x,x0) and cstr: *)
			let x_inter = MinFloat.Sort.getPoint' (direction, value) in
			let x_output = Vec.divc (Vec.add x_inter x') (Scalar.Rat.mk1 2) in
			(cstr, x_output)
			)
			cstrs
	*)

module BuildSx = struct

	let build_paramCoeff : Cs.Vec.V.t list -> Cs.t -> PLP.PSplx.ParamCoeff.t
		= fun params cstr ->
		let vec = List.map
			(fun param ->
				 Cs.get_v cstr |> fun vec -> Cs.Vec.get vec param)
			params
		in
		PLP.PSplx.ParamCoeff.mk vec (Cs.get_c cstr |> Cs.Coeff.neg)

	let objective : Cs.Vec.V.t list -> Cs.t list -> PLP.PSplx.Objective.t
		= fun params cstrs ->
		let null_paramCoeff = PLP.PSplx.ParamCoeff.mk (List.map (fun _ -> Scalar.Rat.z) params) Scalar.Rat.z in
		let coeffs = List.map (fun cstr -> build_paramCoeff params (Cs.compl cstr)) cstrs in
		PLP.PSplx.Objective.mk coeffs null_paramCoeff

	let build_norm_from_point : Vec.t -> Cs.t list -> Tableau.Vector.t
		= fun init_point cstrs ->
		List.map
			(fun cstr ->
				Scalar.Rat.sub
					(Cs.Vec.dot_product
						init_point
						(Cs.get_v cstr))
					(Cs.get_c cstr)
			)
			cstrs
		@ [Scalar.Rat.negU] (* Normalization constant *)

	let build_params : PLP.Naming.t -> Cs.t list -> Vec.V.t list * PLP.Naming.t
		= fun names cstrs ->
		let params = Cs.getVars cstrs
			|> Vec.V.Set.elements
		in
		(params, PLP.Naming.mkParam params names)

	let build_vars : Cs.t list -> Vec.V.t list * PLP.Naming.t
		= fun cstrs ->
		let vars = List.mapi (fun i _ -> Vec.V.fromInt (i+1)) cstrs in
		(vars, PLP.Naming.mkVar vars PLP.Naming.empty)

	let build : Vec.t -> Cs.t list -> PLP.PSplx.t
		= fun init_point cstrs ->
		let (_, names) = build_vars cstrs in
		let (params, names) = build_params names cstrs in
		let obj = objective params cstrs
		and mat = [build_norm_from_point init_point cstrs] in
		PLP.({PSplx.obj = obj ; PSplx.mat = mat ; PSplx.basis = [] ; PSplx.names = names})
end

type 'c regionsT = {
	mapping : (PLP.Region.t * 'c Cons.t) list;
	interior_point : Vec.t ;
}

let regions_to_string' : (PLP.Region.t * 'c Cons.t) list -> string
	= fun regs ->
	Printf.sprintf "\tRegions : \n%s"
		(Misc.list_to_string
			(fun (reg,cons) -> Printf.sprintf "%s\n%s\n"
				(PLP.Region.to_string reg)
				(Cons.to_string Vec.V.to_string cons))
			regs "\n")

let regions_to_string : 'c regionsT -> string
	= fun regs ->
	regions_to_string' regs.mapping

let to_plp : 'c Cert.t -> Vec.t -> ('c Cons.t * Vec.t) list -> 'c regionsT
	= let build_map : 'c Cons.t list -> 'c PLP.mapVar_t
		= fun conss ->
		Misc.fold_left_i (fun i map cons -> PLP.MapV.add i cons map)
			PLP.MapV.empty
			conss
	in
	fun factory x0 conss_points ->
	(*Misc.list_to_string
		(fun (c,v) -> Printf.sprintf "%s -> %s"
			(Cs.to_string Cs.Vec.V.to_string c)
			(Vec.to_string Vec.V.to_string v))
		cstrs " ; "
		|> print_endline;*)
	let (conss,points) = List.split conss_points in
	let config = PLP.std_config (*{PLP.std_config with
		PLP.points = (List.map (fun v -> PLP.ExplorationPoint.Point v) points);
		(*PLP.add_region = PLP.standard_test;*)
	} *)in
	let mapVar = build_map conss in
	let get_cert = PLP.get_cert_default factory mapVar in
	let sx = BuildSx.build x0 (List.map Cons.get_c conss) in
	match PLP.run config sx get_cert with
	| None -> Stdlib.failwith "PoltoPLP.to_plp"
	| Some regs -> {mapping = regs ; interior_point = x0}

let minimize_and_plp : 'c Cert.t -> Vec.t -> 'c Cons.t list -> 'c regionsT
	= fun factory init_point conss ->
	(* TODO: ces étapes devraient être évitée, la minimization devrait pouvoir gérer des Cons.t directement*)
	MinFloat.minimize init_point (List.map Cons.get_c conss)
	|> List.map (fun (cstr,point) ->
		let cons = List.find (fun cons -> Cs.equalSyn (Cons.get_c cons) cstr) conss in
		(cons,point))
	|> to_plp factory init_point

module ReNormalize = struct

	(** Computes the denominantor of lambda from the new point (homogenized) and the polyhedron face. *)
	let compute_denominator : Vec.t -> Vec.t -> Vec.Coeff.t
		= fun polyhedron_face new_point ->
		Vec.dot_product polyhedron_face new_point
		|> Vec.Coeff.neg

	let compute_numerator : Vec.t -> Vec.t -> Vec.Coeff.t
		= fun vec_to_normalize new_point ->
		Vec.dot_product vec_to_normalize new_point

	let homogenize_point : Vec.t -> Vec.V.t -> Vec.t
		= fun point additional_var ->
		Vec.set point additional_var Vec.Coeff.u

	let homogenize_cstr : Vec.V.t -> Cs.t -> Vec.t
		= fun additional_var cstr ->
		[cstr.Cs.c , additional_var]
			|> Vec.mk
			|> Vec.sub cstr.Cs.v

	let remove_additional_var : Vec.V.t -> Vec.t -> Vec.t
		= fun additional_var point ->
		Vec.set point additional_var Vec.Coeff.z
		(*
		Vec.get point additional_var
		|> Vec.divr point
		|> fun point -> Vec.set point additional_var Vec.Coeff.z
		*)
		(* TODO faut il diviser tous les coefficients par le coefficient de la variable additionnelle? *)

	let renormalize_vec : Vec.Coeff.t -> Vec.V.t -> Vec.t -> Vec.t -> Vec.t -> Vec.t
		= fun denominator additional_var new_point polyhedron_face vec ->
		let lambda = Vec.Coeff.div (compute_numerator vec new_point) denominator in
		Vec.add vec (Vec.mulc lambda polyhedron_face)

	let renormalize_boundary : Vec.Coeff.t -> Vec.V.t -> Vec.t -> Vec.t -> PLP.Boundary.t -> PLP.Boundary.t
		= fun denominator additional_var new_point polyhedron_face (cstr,point_other_side) ->
		let renormalize_vec = renormalize_vec denominator additional_var new_point polyhedron_face in
		let vec' = homogenize_cstr additional_var cstr
			|> renormalize_vec
		and point_other_side' = homogenize_point point_other_side additional_var
			|> renormalize_vec
			|> remove_additional_var additional_var
		in
		let cstr' = Cs.mk2 (Cs.get_typ cstr)
			(Vec.set vec' additional_var Vec.Coeff.z)
			(Vec.get vec' additional_var |> Vec.Coeff.neg) in
		(cstr',point_other_side')

	let renormalize_region : Vec.V.t -> Vec.t -> (PLP.Region.t * 'c Cons.t) -> (PLP.Region.t * 'c Cons.t)
		= fun additional_var new_point (reg,cons) ->
		let polyhedron_face = Cons.get_c cons
			|> homogenize_cstr additional_var in
		let new_point = homogenize_point new_point additional_var in
		let denominator = compute_denominator polyhedron_face new_point in
		let renormalize_boundary = renormalize_boundary denominator additional_var new_point polyhedron_face in
		let boundaries = List.map
			(fun (boundary,i) -> renormalize_boundary boundary, i)
			reg.PLP.Region.r
		in
		let point' = homogenize_point reg.PLP.Region.point additional_var
			|> renormalize_vec denominator additional_var new_point polyhedron_face
			|> remove_additional_var additional_var
		in
		({reg with PLP.Region.r = boundaries ; PLP.Region.point = point'},
		 cons)

	let renormalize : 'c regionsT -> Vec.t -> 'c regionsT
		= fun regs new_point ->
		let additional_var = List.map (fun (_,cons) -> Cons.get_c cons) regs.mapping
			|> Cs.getVars
			|> Cs.Vec.V.horizon
		in
		let mapping' = List.map (renormalize_region additional_var new_point) regs.mapping
		in
		{mapping = mapping' ; interior_point = new_point}

end

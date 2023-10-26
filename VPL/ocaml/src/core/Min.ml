module type Type = sig
	module Vec : Vector.Type with module M = Cstr.Rat.Positive.Vec.M

	(** [minimize x cstrs] removes the redundancies in the list of constraints [cstrs].
		@param x is a point that should lie in the interior of the polyhedron defined by [cstrs].
		This function attach to each returned constraint [cstr] a point that violates only [cstr].
		When possible, this point does not saturate the completentary of [cstr]. *)
	val minimize : Vec.t -> Cstr.Rat.Positive.t list -> (Cstr.Rat.Positive.t * Vec.t) list

	val minimize_cone : Vec.t -> Cstr.Rat.Positive.t list -> (Cstr.Rat.Positive.t * Vec.t) list

	val name : string
end

module Debug = DebugTypes.Debug(struct let name = "Min" end)

module Check = struct
	let enabled : bool Stdlib.ref = Stdlib.ref false

	let enable : unit -> unit = fun () -> enabled := true

	let disable : unit -> unit = fun () -> enabled := false

	let check : bool Lazy.t -> string Lazy.t-> unit
		= fun test s ->
		if !enabled
		then if not (Lazy.force test)
			then Stdlib.failwith ("Check error : " ^ (Lazy.force s))
end

module Classic (Vec : Vector.Type with module M = Cstr.Rat.Positive.Vec.M) = struct
	module Cs = Cstr.Rat.Positive
	module Vec = Vec

	let name = "Classic"

	let (strict_comp : Cs.t -> Cs.t)
		= fun cstr ->
		{(Cs.compl cstr) with Cs.typ = Cstr.Lt}


	let ofSymbolic : Vector.Symbolic.Positive.t -> Vec.t
		= fun v ->
		Rtree.map Vec.ofSymbolic v

	let init : Vec.V.t -> (int * Cs.t) -> (int * Cs.t) list -> Vec.t option
		= fun horizon (i0,cstr0) cstrs ->
		let cstrs' = Misc.pop (fun (i1,_) (i2,_) -> i1 = i2) cstrs (i0,cstr0) in
		let sx = Splx.mk horizon ((i0, Cs.compl cstr0) :: cstrs')
			|> Splx.checkFromAdd
		in
		match sx with
		| Splx.IsUnsat _ -> None
		| Splx.IsOk sx ->
			(* On vérifie si le point obtenu va saturer cstr0 *)
			if Cs.get_typ cstr0 = Cstr.Le
			then Some (ofSymbolic (Splx.getAsg sx))
			else
				let max_id = Misc.max (fun (i1,_) (i2,_) -> Stdlib.compare i1 i2) cstrs
					|> Stdlib.fst
				in
				match Splx.add sx (max_id + 1, strict_comp cstr0)
					|> Splx.checkFromAdd
				with
				| Splx.IsUnsat _ -> Some (ofSymbolic (Splx.getAsg sx))
				| Splx.IsOk sx' -> Some (ofSymbolic (Splx.getAsg sx'))

	(* XXX: pas optimal, peut-on réutiliser les simplexes précédents? *)
	let correct_point : Vec.V.t -> ((int * Cs.t) * Vec.t) -> (int * Cs.t) list -> (Cs.t * Vec.t)
		= fun horizon ((i0,cstr0),point) cstrs ->
		match Splx.mk horizon ((i0, strict_comp cstr0) :: cstrs)
			|> Splx.checkFromAdd
		with
		| Splx.IsUnsat _ -> (cstr0, point)
		| Splx.IsOk sx -> (cstr0, ofSymbolic (Splx.getAsg sx))

	let correct_points : Vec.V.t -> ((int * Cs.t) * Vec.t) list -> (Cs.t * Vec.t) list
		= fun horizon cstrs ->
		List.map
			(fun cstr ->
				let cstrs = Misc.pop (fun ((i1,_),_) ((i2,_),_) -> i1 = i2) cstrs cstr in
				correct_point horizon cstr (List.split cstrs |> Stdlib.fst))
			cstrs

	let minimize' : Cs.t list -> (Cs.t * Vec.t) list
		= fun cstrs ->
		let horizon = Cs.getVars cstrs
			|> Vec.V.horizon in
		let cstrs = List.mapi (fun i cstr -> (i,cstr)) cstrs in
		List.fold_left
			(fun (res,cstrs) (i0,cstr0) ->
				match init horizon (i0,cstr0) cstrs with
				| None -> (res, Misc.pop (fun (i1,_) (i2,_) -> i1 = i2) cstrs (i0,cstr0))
				| Some point -> (((i0,cstr0),point)::res, cstrs))
			([],cstrs)
			cstrs
		|> Stdlib.fst
		|> correct_points horizon

	let minimize : Vec.t -> Cs.t list -> (Cs.t * Vec.t) list
		= fun _ cstrs ->
		Debug.log DebugTypes.Title (lazy ("Minimization : Classic with vector type = " ^ (Vec.name)));
		Debug.log DebugTypes.MInput (lazy (Printf.sprintf "Constraints : %s"
			(Cs.list_to_string cstrs)));
		let res = minimize' cstrs in
		Debug.log DebugTypes.MOutput (lazy (Misc.list_to_string
			(fun (c,v) -> Printf.sprintf "(%s, %s)"
				(Cs.to_string Cs.Vec.V.to_string c)
				(Vec.to_string Vec.V.to_string v))
			res " ; "));
		res

	let init_cone : Vec.V.t -> (int * Cs.t) -> (int * Cs.t) list -> Vec.t option
		= fun horizon (i0,cstr0) cstrs ->
		let cstrs' = Misc.pop (fun (i1,_) (i2,_) -> i1 = i2) cstrs (i0,cstr0) in
		let cstrs'' = List.map
			(fun (i,cstr) -> i, {cstr with
				Cs.c = Cs.Vec.Coeff.sub cstr.Cs.c Cs.Vec.Coeff.u;
				Cs.typ = Cstr.Le})
			((i0, Cs.compl cstr0) :: cstrs')
		in
		let sx = Splx.mk horizon cstrs''
			|> Splx.checkFromAdd
		in
		match sx with
		| Splx.IsUnsat _ -> None
		| Splx.IsOk sx ->  Some (ofSymbolic (Splx.getAsg sx))

	let minimize_cone' : Cs.t list -> (Cs.t * Vec.t) list
		= fun cstrs ->
		let horizon = Cs.getVars cstrs
			|> Vec.V.horizon in
		let cstrs = List.mapi (fun i cstr -> (i,cstr)) cstrs in
		List.fold_left
			(fun (res,cstrs) (i0,cstr0) ->
				match init_cone horizon (i0,cstr0) cstrs with
				| None -> (res, Misc.pop (fun (i1,_) (i2,_) -> i1 = i2) cstrs (i0,cstr0))
				| Some point -> ((cstr0,point)::res, cstrs))
			([],cstrs)
			cstrs
		|> Stdlib.fst

	let minimize_cone : Vec.t -> Cs.t list -> (Cs.t * Vec.t) list
		= fun _ cstrs ->
		Debug.log DebugTypes.Title (lazy ("Minimization Cone : Classic with vector type = " ^ (Vec.name)));
		Debug.log DebugTypes.MInput (lazy (Printf.sprintf "Constraints : %s"
			(Cs.list_to_string cstrs)));
		let res = minimize_cone' cstrs in
		Debug.log DebugTypes.MOutput (lazy (Misc.list_to_string
			(fun (c,v) -> Printf.sprintf "(%s, %s)"
				(Cs.to_string Cs.Vec.V.to_string c)
				(Vec.to_string Vec.V.to_string v))
			res " ; "));
		res
end

module Classic_ = Classic (Cstr.Rat.Positive.Vec)

module Min (VecInput : Vector.Type)(Vec : Vector.Type)(CsInput : Cstr.Type)(LP : MinLP.Type)  = struct

	module Cs = LP.CsUser

	type direction_type  =
	| Normal of Vec.t * Cs.Vec.t (** x' = x0 + t * normal *)
	| TwoPoints of Vec.t * Vec.t (** x' = x0 + t * (x1 - x0) *)

	type direction = direction_type * Cs.Vec.Coeff.t

	type conversion =
	{
		vec_CsVec : Vec.t -> Cs.Vec.t;
		csVec_Vec : Cs.Vec.t -> Vec.t;
		csCoeff_Coeff : Cs.Vec.Coeff.t -> Vec.Coeff.t;
		csInput_Cs : CsInput.t -> Cs.t;
		vecInput_Vec : VecInput.t -> Vec.t;
		vec_VecInput : Vec.t -> VecInput.t
		}

	let empty : conversion
		= {
		vec_CsVec = (fun _ -> Cs.Vec.nil);
		csVec_Vec = (fun _ -> Vec.nil);
		csCoeff_Coeff = (fun _ -> Vec.Coeff.z);
		csInput_Cs = (fun _ -> Cs.eq [] Cs.Vec.Coeff.z);
		vecInput_Vec = (fun _ -> Vec.nil);
		vec_VecInput = (fun _ -> VecInput.nil);
		}

	let conv : conversion ref
		= ref empty

	(** Two lists: {ul
		{- constraints that must be added to the lp}
		{- constraints that are already in the lp}
		}
	*)
	type map_t = (Cs.t list * Cs.t list) LP.MapC.t

	(** Map to store the lp done to determine the redundancy of some constraints. *)
	type mapLP_t = LP.t LP.MapC.t
	let mapLP : mapLP_t ref = ref LP.MapC.empty

	type frontier = Cs.t * VecInput.t

	let is_frontier : Cs.t -> frontier list -> bool
		= fun cstr fs ->
		List.exists
			(fun (f,_) -> Cs.equalSyn f cstr)
			fs

	(** This module evaluates each constraints in some directions (either contraints normal vectors, or defined with two points), and sort the result. The first constraint of each list is thus a true frontier. *)
	module Sort = struct

		(** Returns the normal vector of the given constraint. *)
		let normal : Cs.t -> Cs.Vec.t
			= fun c ->
			Cs.get_v c

		(** Evaluates the given constraint in the given direction. *)
		let value : direction_type -> Cs.t -> Cs.Vec.Coeff.t
			= fun dirType cstr ->
			let a = normal cstr in
			match dirType with
			| Normal (point, normal) -> begin
				let num = Cs.Vec.Coeff.sub
					(Cs.get_c cstr)
					(Cs.Vec.dot_product
						a
						(!conv.vec_CsVec point))
				in
				let den = Cs.Vec.dot_product a normal in
				Cs.Vec.Coeff.div num den
				end

			(* D : x' = x0 + t(x1 - x0)
				C : <a,x> = b
				t = (b - <a,x0>) / <a,x1-x0> *)
			| TwoPoints (x0, x1) -> begin
				let num = Cs.Vec.Coeff.sub
					(Cs.get_c cstr)
					(Cs.Vec.dot_product
						a
						(!conv.vec_CsVec x0))
				in
				let den = Cs.Vec.dot_product a (Vec.sub x1 x0 |> !conv.vec_CsVec)
				in
				Cs.Vec.Coeff.div num den
				end

		(** Computes the value of the intersection between the direction and the constraints. *)
		let getPoint' : direction -> VecInput.t
			= fun (dirType,v) ->
			match dirType with
			| Normal (point, normal) -> Vec.add
				point
				(Cs.Vec.mulc v normal |> !conv.csVec_Vec)
				|> !conv.vec_VecInput
			| TwoPoints	(x0,x1) -> Vec.add
				x0
				(Vec.mulc
					(!conv.csCoeff_Coeff v)
					(Vec.sub x1 x0))
				|> !conv.vec_VecInput

		(** Returns the value of the intersection between the direction and the constraints.
		If the direction type is [TwoPoints], it checks that the new point still statisfies the lp associated to [cstr]. *)
		let getPoint : Cs.t -> direction -> VecInput.t
			= fun cstr (dirType,v) ->
			match dirType with
			| Normal _ as d -> getPoint' (d,v)
			| TwoPoints (x0,_) as d ->
				let x' = getPoint' (d,v) in
				let x'' = !conv.vecInput_Vec x' |> !conv.vec_CsVec in
				try
					let lp = LP.MapC.find cstr !mapLP in
					let x_lp = LP.get_solution lp in
					let eval'' = Cs.eval' cstr x''
					and eval_lp = Cs.eval' cstr x_lp in
					if Cs.Vec.Coeff.cmp (Cs.Vec.Coeff.abs eval_lp) (Cs.Vec.Coeff.abs eval'') < 0
					then !conv.csVec_Vec x_lp |> !conv.vec_VecInput
					else x'
				with Not_found -> x'


		(** Sorts the evaluations. *)
		let sort : ('a * direction) list -> ('a * direction) list
			= fun dirs ->
				dirs
			|> List.filter (fun (_,(dir,v)) -> Cs.Vec.Coeff.well_formed v && Cs.Vec.Coeff.le Cs.Vec.Coeff.z v) (* XXX: le ou lt?*)
			|> List.sort (fun (_,(dir1,v1)) (_,(dir2,v2)) -> Cs.Vec.Coeff.cmp v1 v2)

		(** Resulting type of a sorting. *)
		type eval = (Cs.t * direction) list list

		(** Stacks ({i i.e.} put in the same sublist) two evaluations that are two close, {i w.r.t.} {!val:Cs.Vec.Coeff.equalApprox}. *)
		let rec stack : ('a * direction) list -> ('a * direction) list list
			= function
			| [] -> []
			| [x] -> [[x]]
			| (c,(dir1,v1)) :: tl ->
				let l = stack tl in
				let l1 = List.hd l in
				let (_,(dir2,v2)) = List.hd l1 in
				if Cs.Vec.Coeff.equalApprox v1 v2 (* XXX: attention equalApprox?*)
				then ((c,(dir1,v1)) :: l1) :: (List.tl l)
				else [(c,(dir1,v1))] :: l

		(** Extract true boundaries from a value of type {!type:eval}.
		The first element of each list is a true boundary, if it is a singleton. *)
		let getTrue : eval -> frontier option
			= function
			| [] -> Stdlib.failwith "Min.getTrue : unexpected empty list"
			| []::_ -> Stdlib.failwith "Min.getTrue : unexpected empty element"
			| [(cstr,(dir,v))] :: [] ->
				let v' = Cs.Vec.Coeff.mul (Cs.Vec.Coeff.of_float 2.) v in
				let x = getPoint cstr (dir,v') in
				Some (cstr,x)
			| (x1 :: x2 ::_) :: tl -> None
			| [(cstr,(dir1,v1))] :: tl ->
				let l = List.hd tl in
				let (_,(_,v2)) = List.hd l in
				let v' = Cs.Vec.Coeff.div
					(Cs.Vec.Coeff.add v1 v2)
					(Cs.Vec.Coeff.of_float 2.)
				in
				let x = getPoint cstr (dir1,v') in
				Some (cstr,x)

		(** [update_one cstr cstr' map] updates [map], adding [cstr'] to the the first list binded to [cstr].
		See {!type:map_t} for more informations. *)
		let updateOne : Cs.t -> Cs.t -> map_t -> map_t
			= fun cstr cstrToAdd map ->
			try
				let (l1,l2) = LP.MapC.find cstr map in
				if List.mem cstrToAdd l1 || List.mem cstrToAdd l2
				then map
				else LP.MapC.add cstr ((cstrToAdd :: l1),l2) map
			with
			Not_found -> LP.MapC.add cstr ([cstrToAdd],[]) map

		let updateMap'_v1 : map_t -> Cs.t -> eval -> map_t
			= fun map cstr l ->
			List.fold_left
				(fun map (cstr_to_add,_) ->
					if Cs.equalSyn cstr_to_add cstr
					then map
					else updateOne cstr cstr_to_add map)
				map (List.concat l)

		(* on prend tous les prédecesseurs dans la liste*)
		let updateMap_v1 : map_t -> frontier list -> (Cs.t * eval) list -> map_t
			= fun map frontiers evals ->
			List.fold_left
				(fun map (cstr, eval) ->
					if is_frontier cstr frontiers
					then map
					else updateMap'_v1 map cstr eval)
				map evals

		let updateMap'_v2 : map_t -> Cs.t -> eval -> map_t
			= fun map cstr l ->
			let cstrs_to_add = List.hd l in
			List.fold_left
				(fun map (cstr_to_add,_) ->
					if Cs.equalSyn cstr_to_add cstr
					then map
					else updateOne cstr cstr_to_add map)
				map cstrs_to_add

		(* ne prend que les vraies frontières de la liste (plusieurs s'il y a égalité)*)
		let updateMap_v2 : map_t -> frontier list -> (Cs.t * eval) list -> map_t
			= fun map frontiers evals ->
			List.fold_left
				(fun map (cstr, eval) ->
					if is_frontier cstr frontiers
					then map
					else updateMap'_v2 map cstr eval)
				map evals

		let rec heuristique_zarbi : (Cs.t * 'a) list list -> (Cs.t * 'a) list -> Cs.t -> (Cs.t * 'a) list list
			-> (Cs.t * 'a) list list
			= fun pred paquet cstr others ->
			let length_pred = 2 in
			let length_succ = 1 in
			let add paquet pred =
				if List.length pred >= length_pred
				then paquet :: Misc.sublist pred 0 length_pred
				else paquet :: pred
			in
			if List.exists (fun (c,_) -> Cs.equalSyn c cstr) paquet
			then pred @ Misc.sublist others 0 length_succ
			else match others with
				| [] -> Stdlib.failwith "Min.heuristique_zarbi"
				| paquet' :: others' -> heuristique_zarbi (add paquet pred) paquet' cstr others'

		let updateMap'_v3 : map_t -> Cs.t -> eval -> map_t
			= fun map cstr l ->
			let cstrs_to_add = heuristique_zarbi [] (List.hd l) cstr (List.tl l)
				@ [List.hd l]
				|> List.concat
			in
			List.fold_left
				(fun map (cstr_to_add,_) ->
					if Cs.equalSyn cstr_to_add cstr
					then map
					else updateOne cstr cstr_to_add map)
				map cstrs_to_add

		(* heuristique zarbi de Michaël *)
		let updateMap_v3 : map_t -> frontier list -> (Cs.t * eval) list -> map_t
			= fun map frontiers evals ->
			List.fold_left
				(fun map (cstr, eval) ->
					if is_frontier cstr frontiers
					then map
					else updateMap'_v3 map cstr eval)
				map evals


		let updateMap'_desespoir : map_t -> Cs.t -> eval -> map_t
			= fun map cstr l ->
			let cstrs_to_add = List.concat l
			in
			List.fold_left
				(fun map (cstr_to_add,_) ->
					if Cs.equalSyn cstr_to_add cstr
					then map
					else updateOne cstr cstr_to_add map)
				map cstrs_to_add

		(* heuristique du desespoir *)
		let updateMap_desespoir : map_t -> frontier list -> (Cs.t * eval) list -> map_t
			= fun map frontiers evals ->
			List.fold_left
				(fun map (cstr, eval) ->
					if is_frontier cstr frontiers
					then map
					else updateMap'_desespoir map cstr eval)
				map evals

		let updateMap : map_t -> frontier list -> (Cs.t * eval) list -> map_t
			= if String.compare LP.name "Glpk" = 0
			 then updateMap_v2
			 else if String.compare LP.name "Splx" = 0
			 	then updateMap_v2
			 	else Stdlib.invalid_arg "Min.updateMap: name"

		(* Evalue chaque contrainte dans la direction de la normale de cstr.
			Trie les résultats et accumule les égalités. *)
		let init_one : Vec.t -> Cs.t list -> Cs.t -> eval
			= fun x0 cstrs cstr ->
			let normal = normal cstr in
			let dir_type = Normal (x0,normal) in
			List.map
				(fun cstr -> let v = value dir_type cstr in
					(cstr,(dir_type,v)))
				cstrs
			|> fun l -> (Debug.log DebugTypes.Detail (lazy(Printf.sprintf "Evals before post-processing : %s -> \n%s"
				(Cs.to_string Cs.Vec.V.to_string cstr)
				(Misc.list_to_string (fun (c,(_,v)) -> (Cs.to_string Cs.Vec.V.to_string c) ^ " -> " ^ (Cs.Vec.Coeff.to_string v)) l " ; "))));
				l
			|> sort
			|> stack

		let direction_to_string : direction -> string
			= fun (dir_type,c) ->
			match dir_type with
			| Normal (x0,normal) -> Printf.sprintf "Normal %s in direction %s, with coeff %s"
				(Vec.to_string Vec.V.to_string x0)
				(Cs.Vec.to_string Cs.Vec.V.to_string normal)
				(Cs.Vec.Coeff.to_string c)
			| TwoPoints (x,x') ->Printf.sprintf "TwoPoint %s -> %s, with coeff %s"
				(Vec.to_string Vec.V.to_string x)
				(Vec.to_string Vec.V.to_string x')
				(Cs.Vec.Coeff.to_string c)

		let eval_to_string : eval -> string
			= fun l ->
			Misc.list_to_string
				(fun l -> Misc.list_to_string
					(fun (c,dir) -> (Cs.to_string Cs.Vec.V.to_string c) ^ ", " ^ (direction_to_string dir)) l ";")
				l " ; "

		let eval_to_string2 : eval -> string
			= fun l ->
			Misc.list_to_string
				(fun l -> Misc.list_to_string
					(fun (c,_) -> Cs.to_string Cs.Vec.V.to_string c) l ";")
				l " ; "

		let getFrontiers : (Cs.t * eval) list -> frontier list
			= fun evals ->
			List.fold_left
				(fun frontiers (_,eval) ->
					match getTrue eval with
					| Some (c,p) when not (is_frontier c frontiers) -> (c,p) :: frontiers
					| _ -> frontiers)
				[] evals

		let init : Vec.t -> Cs.t list -> frontier list * map_t
			= fun x0 cstrs ->
			if cstrs = []
			then Stdlib.failwith "omg"
			else
			let evals = List.map
				(fun cstr -> (cstr,init_one x0 cstrs cstr))
				cstrs
			in
			Debug.log DebugTypes.Detail (lazy(Printf.sprintf "evals = %s"
				(Misc.list_to_string (fun (cs,eval) -> Printf.sprintf "%s -> %s"
					(Cs.to_string Cs.Vec.V.to_string cs)
					(eval_to_string2 eval))
					evals "\n")));
			let frontiers = getFrontiers evals in
			Debug.log DebugTypes.Detail (lazy(Printf.sprintf "frontiers = %s"
				(Misc.list_to_string (fun (c,_) -> Cs.to_string Cs.Vec.V.to_string c) frontiers " ; ")));
			let map = updateMap LP.MapC.empty frontiers evals
			(*List.fold_left
				(fun map (cstr, eval) ->
					if is_frontier cstr frontiers
					then map
					else updateMap map cstr eval)
				LP.MapC.empty evals*)
			in
			(frontiers,map)
	end

	let (strict_comp : Cs.t -> Cs.t)
		= fun cstr ->
		{(Cs.compl cstr) with Cs.typ = Cstr.Lt}

	let init_lp : LP.t option -> Cs.t -> Cs.Vec.V.t list -> LP.t
		= fun lp cstr vars ->
		match lp with
		| Some lp -> lp
		| None -> match LP.mk [Cs.compl cstr] vars with
			| LP.IsOk lp -> lp
			| LP.IsUnsat -> Stdlib.failwith "Min.init_lp"
	(*
	(** [runlp vars cstr cstrs lp] runs a LP to find a point that violates [cstr] and satisfies each constraint of [cstrs].
		It starts from the LP [lp] if it exists. *)
	let runlp : Cs.Vec.V.t list -> Cs.t -> Cs.t list -> LP.t option -> (Vec.t * LP.t) option
		= fun vars cstr cstrs lp ->
		let lp = init_lp lp cstr vars in
		match LP.add_cstrs cstrs lp with
		| LP.IsOk lp -> begin
			if Cs.get_typ cstr = Cstr.Le
			then let sol = LP.get_solution lp
				|> !conv.csVec_Vec in
				Some (sol, lp)
			else
				match LP.add_cstrs [strict_comp cstr] lp with
				| LP.IsUnsat -> let sol = LP.get_solution lp
					|> !conv.csVec_Vec in
					Some (sol, lp)
				| LP.IsOk lp' -> let sol = LP.get_solution lp'
					|> !conv.csVec_Vec in
					Some (sol, lp')
						(* XXX: potentiellement ajouté plusieurs fois : à optimiser *)
					(* XXX: faut il renvoyer lp pour ne pas rendre unsat des problèmes sat? *)
			end
		| LP.IsUnsat -> None
	*)

	(** [runlp vars cstr cstrs lp] runs a LP to find a point that violates [cstr] and satisfies each constraint of [cstrs].
	It starts from the LP [lp] if it exists. *)
	let runlp_not_cone : Cs.Vec.V.t list -> Cs.t -> Cs.t list -> LP.t option -> (Vec.t * LP.t) option
		= fun vars cstr cstrs lp ->
		let lp = init_lp lp cstr vars in
		match LP.add_cstrs cstrs lp with
		| LP.IsOk lp ->
			let sol = LP.get_solution lp
				|> !conv.csVec_Vec in
			Some (sol, lp)
		| LP.IsUnsat -> None

	let init_lp_cone : LP.t option -> Cs.t -> Cs.Vec.V.t list -> LP.t
		= fun lp cstr vars ->
		match lp with
		| Some lp -> lp
		| None ->
			let cstr' = {(Cs.compl cstr) with
				Cs.c = Cs.Vec.Coeff.sub (Cs.compl cstr).Cs.c Cs.Vec.Coeff.u;
				Cs.typ = Cstr.Le}
			in
			match LP.mk [cstr'] vars with
			| LP.IsOk lp -> lp
			| LP.IsUnsat -> Stdlib.failwith "Min.init_lp"

	(** [runlp vars cstr cstrs lp] runs a LP to find a point that violates [cstr] and satisfies each constraint of [cstrs].
	It starts from the LP [lp] if it exists. *)
	let runlp_cone : Cs.Vec.V.t list -> Cs.t -> Cs.t list -> LP.t option -> (Vec.t * LP.t) option
		= fun vars cstr cstrs lp ->
		let lp = init_lp_cone lp cstr vars in
		let cstrs' = List.map
			(fun cstr -> {cstr with
				Cs.c = Cs.Vec.Coeff.sub cstr.Cs.c Cs.Vec.Coeff.u;
				Cs.typ = Cstr.Le})
			cstrs
		in
		match LP.add_cstrs cstrs' lp with
		| LP.IsOk lp ->
			let sol = LP.get_solution lp
				|> !conv.csVec_Vec in
			Some (sol, lp)
		| LP.IsUnsat -> None

	type typT = Cone | NCone

	(** [runlp vars cstr cstrs lp] runs a LP to find a point that violates [cstr] and satisfies each constraint of [cstrs].
	It starts from the LP [lp] if it exists. *)
	let runlp : typT -> Cs.Vec.V.t list -> Cs.t -> Cs.t list -> LP.t option -> (Vec.t * LP.t) option
		= function
		| Cone -> runlp_cone
		| NCone -> runlp_not_cone

	(** Removes all occurrences of the given constraint from the list. *)
	let removeCstr : Cs.t -> (Cs.t * Cs.t list) list -> (Cs.t * Cs.t list) list
		= fun cstr l ->
		List.fold_left
			(fun res (cstr',l') ->
				if Cs.equalSyn cstr cstr'
				then res
				else (cstr', Misc.popAll Cs.equalSyn l' cstr) :: res)
			[]
			l

	(* Returns a list of constraints with a point showing their nonredundancy (w.r.t. the given constraints). It updates mapLP. *)
	let rec run_rec : typT -> (Cs.t * Cs.t list) list -> Cs.Vec.V.t list -> (Cs.t * Vec.t) list
		= fun typ l vars ->
		Debug.log DebugTypes.Detail (lazy (Printf.sprintf "run_rec with l = %s"
			(Misc.list_to_string (fun (c,l) -> Printf.sprintf "%s -> %s"
				(Cs.to_string Cs.Vec.V.to_string c)
				(Misc.list_to_string (Cs.to_string Cs.Vec.V.to_string) l " ; "))
				 l " ; ")));
		match l with
		| [] -> []
		| (cstr,l') :: tl ->
(*			(if l' = [] then Stdlib.failwith "run_rec : empty list");*)
			let lpOpt = try
				Some (LP.MapC.find cstr !mapLP)
			with
				Not_found -> None
			in
			Debug.log DebugTypes.Normal (lazy "Launching LP");
			match runlp typ vars cstr l' lpOpt with
			| None ->
				Debug.log DebugTypes.Detail (lazy "LP Unsat");
				let tl' = removeCstr cstr tl in
				run_rec typ tl' vars
			| Some (x,lp) ->
				Debug.log DebugTypes.Detail (lazy "LP Sat");
				mapLP := LP.MapC.add cstr lp !mapLP;
				(cstr,x) :: (run_rec typ tl vars)

	let map_to_string : map_t -> string
		= fun map ->
		Misc.list_to_string
			(fun (c,(l1,l2)) -> Printf.sprintf "%s -> (%s,%s)"
				(Cs.to_string Cs.Vec.V.to_string c)
				(Misc.list_to_string (Cs.to_string Cs.Vec.V.to_string) l1 ";")
				(Misc.list_to_string (Cs.to_string Cs.Vec.V.to_string) l2 ";")
			)
		(LP.MapC.bindings map)
		"\n"

	(** It returns a list of triples, where:
	{ul
	{- the first element is a constraint [c] that may be a true frontier}
	{- the second element is a list [l] of constraints that are in [c]'s lp}
	{- the third element is the current point showing that [c] is not redundant {i w.r.t} all elements of [l]}
	}
	@param map binds [(l1,l2)] to a {!type:Cs.t} [c], where [l1] is the list of constraints that must be added in [c]'s lp, and [l2] is the list of constraints that are already in [c]'s lp.
	*)
	let run : typT -> map_t -> Cs.Vec.V.t list -> (Cs.t * Cs.t list * Vec.t) list
		= fun typ map vars ->
		Debug.log DebugTypes.Normal (lazy (Printf.sprintf "Run : map = %s"
			(map_to_string map)));
		let l = List.map
			(fun (c,(l1,l2)) -> (c,l1))
			(LP.MapC.bindings map)
		in
		run_rec typ l vars
		|>	List.map
			(fun (cstr,x) ->
				let (l1,l2) = LP.MapC.find cstr map in
				(cstr, l1 @ l2, x))

	let reinit_map : (Cs.t * Cs.t list * Vec.t) list -> frontier list -> map_t
		= fun l frontiers ->
		List.fold_left
			(fun map (cstr,cstrs,_) ->
				if is_frontier cstr frontiers
				then map
				else LP.MapC.add cstr ([],cstrs) map)
			LP.MapC.empty l

	let init_one : (Cs.t * Cs.t list * Vec.t) -> Vec.t -> Cs.t list -> Cs.t * Sort.eval
		= fun (cstr, alreadyIn, x') x0 cstrs ->
		Debug.log DebugTypes.Detail (lazy(Printf.sprintf "Init_one (%s,%s)"
			(Vec.to_string Vec.V.to_string x0)
			(Vec.to_string Vec.V.to_string x')));
		let dir_type = TwoPoints (x0,x') in
		let res =
		List.fold_left
			(fun evals cstr ->
				if List.exists (Cs.equalSyn cstr) alreadyIn
				then evals
				else let v = Sort.value dir_type cstr in
					(cstr,(dir_type,v)):: evals)
			[] cstrs
		|> fun l -> (Debug.log DebugTypes.Detail (lazy(Printf.sprintf "Evals before post-processing : %s"
				(Misc.list_to_string (fun (c,(_,v)) -> (Cs.to_string Cs.Vec.V.to_string c) ^ " -> " ^ (Cs.Vec.Coeff.to_string v)) l " ; "))));
				l
		|> Sort.sort
		|> Sort.stack
		in
		(cstr,res)

	let init : frontier list -> Vec.t -> Cs.t list -> (Cs.t * Cs.t list * Vec.t) list -> frontier list * map_t
		= fun previous_frontiers x0 cstrs l ->
		Debug.log DebugTypes.Detail (lazy(Printf.sprintf "init with l = %s"
				(Misc.list_to_string
					(fun (c, alreadyIn,_) -> Printf.sprintf "%s, alreadyIn : %s"
						(Cs.to_string Cs.Vec.V.to_string c)
						(Cs.list_to_string alreadyIn))
				l " ; " )));
		let evals = List.map
			(fun l' -> init_one l' x0 cstrs)
			l
		in
		Debug.log DebugTypes.Detail (lazy(Printf.sprintf "evals = %s"
				(Misc.list_to_string Sort.eval_to_string (List.split evals |> Stdlib.snd) "\n")));
		let frontiers =
			previous_frontiers
			@ (Sort.getFrontiers evals)
		in
		let init_map = reinit_map l frontiers in
		let map = Sort.updateMap init_map frontiers evals
		(*let map = List.fold_left
			(fun map (cstr,eval) ->
				if is_frontier cstr frontiers
				then map
				else Sort.updateMap1 map cstr eval)
			init_map evals*)
		in
		(frontiers,map)

	let map_to_string : map_t -> string
		= fun map ->
		Misc.list_to_string
			(fun (c,(l1,l2)) -> Printf.sprintf "%s -> (%s,%s)"
				(Cs.to_string Cs.Vec.V.to_string c)
				(Misc.list_to_string (Cs.to_string Cs.Vec.V.to_string) l1 ";")
				(Misc.list_to_string (Cs.to_string Cs.Vec.V.to_string) l2 ";")
			)
		(LP.MapC.bindings map)
		"\n"

	let rec minimize_rec : typT -> Cs.Vec.V.t list -> frontier list -> Vec.t -> Cs.t list -> map_t -> frontier list
		= fun typ vars frontiers x0 cstrs map ->
		Debug.log DebugTypes.Detail (lazy(Printf.sprintf "Map : %s" (map_to_string map)));
		let l = run typ map vars in
		if List.length l = 0
		then frontiers
		else let (frontiers,map') = init frontiers x0 cstrs l in
			minimize_rec typ vars frontiers x0 cstrs map'

	let minimize' : typT -> conversion -> VecInput.t -> CsInput.t list -> (CsInput.t * VecInput.t) list
		= fun typ conversion x0 cstrs ->
		(* Variable initialization *)
		if cstrs = []
		then []
		else begin
			conv := conversion;
			mapLP := LP.MapC.empty;
			let cstrs = Misc.rem_dupl CsInput.equalSyn cstrs in (* XXX: faire une autre fonction sans ça? *)
			let vars = CsInput.getVars cstrs
				|> CsInput.Vec.V.Set.elements
				|> List.map (fun v -> CsInput.Vec.V.toPos v |> Cs.Vec.V.fromPos)
			in
			(* map_binding contient une conversion des cstrs (en CsInput) en Cs *)
			let (map_bindings, cstrs') =
			List.fold_left
				(fun (map,l) c -> let c' = !conv.csInput_Cs c in
					(LP.MapC.add c' c map, c' :: l))
				(LP.MapC.empty,[]) cstrs
			in
			let x0' = !conv.vecInput_Vec x0 in
			let (frontiers, map) = Sort.init x0' cstrs' in
			let frontiers' = minimize_rec typ vars frontiers x0' cstrs' map in
			List.map
				(fun (cstr,p) -> let cstr' = LP.MapC.find cstr map_bindings in
					(cstr',p))
				frontiers' (* frontiers' contient frontiers*)
		end

	let minimize : conversion -> VecInput.t -> CsInput.t list -> (CsInput.t * VecInput.t) list
		= fun conversion point cstrs ->
		Debug.log DebugTypes.Title (lazy ("Minimization : Raytracing with vector type = " ^ (VecInput.name)));
		Debug.log DebugTypes.MInput (lazy (Printf.sprintf "Interior Point : %s\nConstraints : %s"
			(VecInput.to_string VecInput.V.to_string point)
			(CsInput.list_to_string cstrs)));
		let res = minimize' NCone conversion point cstrs in
		Debug.log DebugTypes.MOutput (lazy (Misc.list_to_string
			(fun (c,v) -> Printf.sprintf "(%s, %s)"
				(CsInput.to_string CsInput.Vec.V.to_string c)
				(VecInput.to_string VecInput.V.to_string v))
			res " ; "));
		res

	let minimize_cone : conversion -> VecInput.t -> CsInput.t list -> (CsInput.t * VecInput.t) list
		= fun conversion point cstrs ->
		Debug.log DebugTypes.Title (lazy ("Minimization : Raytracing with vector type = " ^ (VecInput.name)));
		Debug.log DebugTypes.MInput (lazy (Printf.sprintf "Interior Point : %s\nConstraints : %s"
			(VecInput.to_string VecInput.V.to_string point)
			(CsInput.list_to_string cstrs)));
		let res = minimize' Cone conversion point cstrs in
		Debug.log DebugTypes.MOutput (lazy (Misc.list_to_string
			(fun (c,v) -> Printf.sprintf "(%s, %s)"
				(CsInput.to_string CsInput.Vec.V.to_string c)
				(VecInput.to_string VecInput.V.to_string v))
			res " ; "));
		res

end

module Splx(Vec : Vector.Type with module M = Cstr.Rat.Positive.Vec.M) = struct
	let name = "Raytracing:Splx:" ^ (Vec.Coeff.name)
	module Vec = Vec
	module LP = MinLP.Splx(Cstr.Float.Positive)
	include Min(Vec)(Cstr.Float.Positive.Vec)(Cstr.Rat.Positive)(LP)

	let id : 'a -> 'a = fun x -> x
	let csCoeff_Coeff x = x
	let vecInput_Vec x = Rtree.map (fun v -> Vec.Coeff.to_float v |> Cstr.Float.Positive.Vec.Coeff.of_float) x
	let vec_VecInput x = Rtree.map (fun v -> Cstr.Float.Positive.Vec.Coeff.to_float v |> Vec.Coeff.of_float) x
	let float_of_cstr : Cstr.Rat.Positive.t -> Cstr.Float.Positive.t
		= fun cstr ->
		let v = Rtree.map (fun x -> Cstr.Rat.Positive.Coeff.to_float x |> Cstr.Float.Positive.Vec.Coeff.of_float) cstr.Cstr.Rat.Positive.v in
		let c = Cstr.Rat.Positive.Coeff.to_float cstr.Cstr.Rat.Positive.c |> Cstr.Float.Positive.Vec.Coeff.of_float in
		Cstr.Float.Positive.mk2 cstr.Cstr.Rat.Positive.typ v c

	let conversion_default = {
		csInput_Cs = float_of_cstr;
		vec_CsVec = id;
		csVec_Vec = id;
		csCoeff_Coeff = csCoeff_Coeff;
		vecInput_Vec = vecInput_Vec;
		vec_VecInput = vec_VecInput
	}

	let minimize = minimize conversion_default

	let minimize_cone = minimize_cone conversion_default
end

module Glpk(Vec : Vector.Type with module M = Cstr.Rat.Positive.Vec.M) = struct
	let name = "Glpk"

	module Cs = Cstr.Rat.Positive
	module Vec = Vec

	let set_coeffs : Wrapper.polyhedron -> Cs.Vec.V.t list -> int -> Cs.t -> unit
  		= fun poly vars i_cstr cstr ->
		List.iter
			(fun (var,coeff) ->
				let i_var = Misc.findi (Cs.Vec.V.equal var) vars in
				Wrapper.set_coeff poly i_cstr i_var (Cs.Vec.Coeff.to_float coeff))
			(Cs.Vec.toList cstr.Cs.v) 

	let get_witness : Wrapper.polyhedron -> Vec.V.t list -> int -> Vec.t
		= fun poly vars id_cstr ->
		List.mapi
			(fun id_var var ->
				let coeff = Wrapper.get_witness_coeff poly id_cstr id_var
					|> Vec.Coeff.of_float
				in
				(coeff,var))
			vars
		|> Vec.mk

  let set_central_point : Wrapper.polyhedron -> Vec.V.t list -> Vec.t -> unit
      = fun poly vars point ->
        List.iteri
          (fun i v ->
            let coeff = Vec.get point v
                        |> Vec.Coeff.to_float in
            Wrapper.set_central_point_coeff poly i coeff
          )
          vars
          
	(* XXX: must check polyhedron emptiness?*)
	let minimize_witness': Vec.t -> Cs.t list -> (Cs.t * Vec.t) list
		= fun point cstrs ->
		let vars = Cs.getVars cstrs
			|> Cs.Vec.V.Set.elements
		in
		let poly = Wrapper.mk (List.length cstrs) (List.length vars) in
    List.iteri (set_coeffs poly vars) cstrs;
    set_central_point poly vars point;
		if Wrapper.is_empty(poly)
		then [] (* XXX: que faire dans ce cas?*)
		else begin
			Wrapper.minimize poly;
			let cstrs' = Misc.fold_right_i
				(fun i cstr res ->
					if Wrapper.is_true poly i
					then cstr :: res
					else res)
				cstrs []
			|> List.mapi
				(fun i cstr ->
				let witness = get_witness poly vars i in
				(cstr,witness))
			in
			Wrapper.rm poly;
			cstrs'
		end

	let minimize_witness : Vec.t -> Cs.t list -> (Cs.t * Vec.t) list
		= fun point cstrs ->
		Debug.log DebugTypes.Title (lazy ("Minimization : Raytracing with vector type = " ^ (Vec.name)));
		Debug.log DebugTypes.MInput (lazy (Printf.sprintf "Constraints : %s"
			(Cs.list_to_string cstrs)));
		let res = minimize_witness' point cstrs in
		Debug.log DebugTypes.MOutput (lazy (Misc.list_to_string
			(fun (c,v) -> Printf.sprintf "(%s, %s)"
				(Cs.to_string Cs.Vec.V.to_string c)
				(Vec.to_string Vec.V.to_string v))
			res " ; "));
		res

	let minimize point constraints = minimize_witness point constraints

	let minimize_cone point constraints = minimize_witness point constraints
end

module Rat_Splx = Splx(Cstr.Rat.Positive.Vec)

module Rat_Glpk = Glpk(Cstr.Rat.Positive.Vec)

module Heuristic(Vec : Vector.Type with module M = Cstr.Rat.Positive.Vec.M) = struct
	let name = "Heuristic"
	module Vec = Vec

	module Glpk = Glpk(Vec)
	module Splx = Splx(Vec)
	module Classic = Classic(Vec)

	let minimize point constraints =
		match Heuristic.min constraints with
		| Flags.Raytracing (Flags.Glpk) -> Glpk.minimize point constraints
		| Flags.Raytracing (Flags.Splx) -> Splx.minimize point constraints
		| Flags.Classic -> Classic.minimize point constraints
		| _ -> Stdlib.invalid_arg "Min.Heuristic.minimize"

	let minimize_cone point constraints =
		match Heuristic.min constraints with
		| Flags.Raytracing (Flags.Glpk) -> Glpk.minimize_cone point constraints
		| Flags.Raytracing (Flags.Splx) -> Splx.minimize_cone point constraints
		| Flags.Classic -> Classic.minimize_cone point constraints
		| _ -> Stdlib.invalid_arg "Min.Heuristic.minimize_cone"
end

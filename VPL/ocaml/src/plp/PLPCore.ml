module Cs = Cstr.Rat.Positive
module EqSet = EqSet.EqSet(Cs)
module Cons = EqSet.Cons

module Debug = DebugTypes.Debug(struct let name = "PLPCore" end)
module Profile = Profile.Profile(struct let name = "PLPCore" end)

module Stat = struct
	let nb_regions : int ref = ref 0

	let incr_nb_regions : unit -> unit
		= fun () ->
		nb_regions := !nb_regions + 1

	(** (nb_redundancies, nb_true_bounds) *)
	let ratio_redundancy : (int * int) ref = ref (0,0)

	let incr_redundancy : int -> int -> unit
		= fun i j ->
		ratio_redundancy :=
			((Stdlib.fst !ratio_redundancy) + i,
			 (Stdlib.snd !ratio_redundancy) + j)

	(** (nb_subdivisions, nb_regions) *)
	let ratio_subdivisions : (int * int) ref = ref (0,0)

	let incr_subdivisions : int -> int -> unit
		= fun i j ->
		ratio_subdivisions :=
			((Stdlib.fst !ratio_subdivisions) + i,
			 (Stdlib.snd !ratio_subdivisions) + j)

	let nb_corrections : int ref = ref 0

	let incr_nb_corrections : unit -> unit
		= fun () ->
		nb_corrections := !nb_corrections + 1

	let reset : unit -> unit
		= fun () ->
		begin
		nb_regions := 0;
		ratio_redundancy := (0,0);
		nb_corrections := 0;
		ratio_subdivisions := (0,0);
		end

	let to_string : unit -> string
		= fun () ->
		Printf.sprintf ("PLP stats : \n\tnb_regions = %i
			\n\tnumber of redundancies (in region representations) = %i
			\n\tnumber of true boundaries = %i
			\n\t -> redundancy ratio = %f
			\n\tnumber of corrections = %i
			\n\ratio of subdivisions = %f")
			!nb_regions
			(Stdlib.fst !ratio_redundancy)
			(Stdlib.snd !ratio_redundancy)
			((Stdlib.fst !ratio_redundancy |> float_of_int) /. (Stdlib.snd !ratio_redundancy |> float_of_int))
			!nb_corrections
			((Stdlib.fst !ratio_subdivisions |> float_of_int) /. (Stdlib.snd !ratio_subdivisions |> float_of_int))
end

module PLP(Minimization : Min.Type) = struct
	module Vec = Minimization.Vec
	module PSplx_ = PSplx.PSplx(Cs)
	module PSplx = PSplx_.PSplx(Vec)

	module Explore = PSplx.Explore

	module Objective = PSplx.Objective
	module ParamCoeff = PSplx.ParamCoeff
	module Pivot = PSplx.Pivot
	module Naming = PSplx.Naming

	module V = Vec.V
	module Coeff = Vec.Coeff

	module MapV = Map.Make(struct type t = int let compare = Stdlib.compare end)

	(** This map is used for the certificate generation.
	Is associates to each simplex column an element of {!type:Cons.t}. *)
	type 'c mapVar_t = ('c Cons.t) MapV.t

	type region_t = Cone | NCone

	module Boundary = struct
		type t = Cs.t * Vec.t

		let equal : t -> t -> bool
			= fun (c1,_) (c2,_) ->
			Cs.equalSyn c1 c2

		let get_cstr : t -> Cs.t
			= fun (c,_) ->
			c

		let get_cstrs : t list -> Cs.t list
			= fun bs ->
			List.map get_cstr bs

		let to_string : t -> string
			= fun (c,p) ->
			"Boundary : " ^ (Cs.to_string V.to_string c)
			^ " - point_other_side : " ^ (Vec.to_string V.to_string p)

        let canon : t -> t
            = fun (c,v) ->
            (Cs.canon c, v)
	end

	let (strict_comp : Cs.t -> Cs.t)
		= fun cstr ->
		let cstr_comp = Cs.compl cstr in
		(match Cs.get_typ cstr_comp with
			| Cstr.Le -> {cstr_comp with Cs.typ = Cstr.Lt}
			| _ -> cstr_comp)

	let (cstr_eq : Cs.t -> Cs.t)
		= fun cstr ->
		{cstr with Cs.typ = Cstr.Eq}

	let is_trivial : Cs.t -> bool
			= fun c ->
			(Cs.Vec.equal (Cs.get_v c) Cs.Vec.nil)

	module ExplorationPoint = struct

		type t =
			| Direction of int * Boundary.t (** (id of origin region, boundary) *)
			| Point of Vec.t

		let to_string : t -> string
			= function
			| Direction (id,(c,x)) ->
				Printf.sprintf "(%s, %s, %s)"
				(string_of_int id)
				(Cs.to_string Cs.Vec.V.to_string c)
				(Vec.to_string Vec.V.to_string x)
			| Point v ->
				Vec.to_string Vec.V.to_string v

		let equal : t -> t -> bool
			= fun p1 p2 ->
			match (p1,p2) with
			| Direction(id1, (cstr1, pointToExplore1)), Direction (id2, (cstr2, pointToExplore2)) ->
					id1 = id2
					&& Cs.equalSyn cstr1 cstr2
					&& Vec.equal pointToExplore1 pointToExplore2
			| Point v1, Point v2 -> Vec.equal v1 v2
			| _,_ -> false
	end

	module Region = struct

		type t = {
			id : int;
			r : (Boundary.t * int option) list;
			point : Vec.t; (* Un point dans la région *)
			sx : PSplx.t option (* Tableau de simplexe dont l'objectif a donné cette région *)
		}

		let mk : int -> Boundary.t list -> Vec.t -> PSplx.t -> t
			= fun id bounds point sx ->
			{id = id;
			 r = List.map (fun b -> (b,None)) bounds;
			 point = point;
			 sx = Some sx
			}

        let canon : t -> t
            = fun reg ->
            {reg with
                r = List.map (fun (bnd, i) -> (Boundary.canon bnd, i)) reg.r;
            }

		let get_cstrs : t -> Cs.t list
			= fun reg ->
			List.map (fun (b,_) -> Boundary.get_cstr b) reg.r

		let to_string : t -> string
			= fun r ->
			let cstrs = get_cstrs r in
			let vars = Cs.getVars cstrs |> V.Set.elements in
			(Printf.sprintf "Region %i : \n\tBoundaries : %s\n\t Point : %s\n\t\n\n\tPlot : %s"
				r.id
				(Misc.list_to_string
					(fun (b,i) -> Printf.sprintf "%s -> %s"
						(Boundary.to_string b)
						(match i with None -> "unknown" | Some i -> string_of_int i))
					r.r "\n\t\t")
				(Vec.to_string V.to_string r.point)
				("P = Polyhedron(ieqs = " ^ (Misc.list_to_string
					(fun c -> Cs.plot vars c)
					cstrs ",") ^ ")"))
			^
			(if Debug.is_enabled DebugTypes.Detail
			then Printf.sprintf "\n\tTableau : \n%s" (match r.sx with None -> "None" | Some sx -> PSplx.to_string sx)
			else "")

		module Extract = struct

			(** Returns the list of rows associated to a null basic variable. *)
			let get_null_basic_variables : PSplx.t -> int list
				= fun sx ->
				Misc.fold_left_i
					(fun i res (col_number, value) ->
						if Scalar.Rat.isZ value
						then i :: res
						else res)
					[]
					(PSplx.getCurVal sx)

			(** [scan_column sx rows col] returns the list of rows (taken in [rows]) with which column [col] can pivot. *)
			let scan_column : Tableau.Matrix.t -> int list -> int -> int list
				= fun mat rows_id col ->
				Misc.fold_left_i
					(fun i res row ->
						if List.mem i rows_id && Q.sign (Tableau.Vector.get col row) > 0
						then i :: res
						else res)
					[]
					mat

			(** Pivots have the form ((row_of_leaving var, leaving var), column of leaving var).
			There is no need to store the name of the entering variable because its name is its column. *)
			type pivot = (int * int) * int

			let pivot_to_string : pivot -> string
				= fun ((_,leaving_var), entering_var) ->
				Printf.sprintf "%i -> %i" leaving_var entering_var

			module Basis = struct
				type t = int list

				let make : int list -> t
					= List.fast_sort (fun i j -> if i < j then 1 else -1)

				let pivot : t -> pivot -> t
				= fun basis ((_,leaving_var), entering_var) ->
				entering_var :: (Misc.pop (=) basis leaving_var)
				|> make

				let rec equal : t -> t -> bool
					= fun b1 b2 ->
					match b1,b2 with
					| [],[] -> true
					| [],_ | _,[] -> false
					| i1 :: b1', i2 :: b2' -> i1 = i2 && equal b1' b2'

			end

			(** Returns a list of potential true frontiers and a list of pivots to perform.*)
			let extract' : PSplx.t -> Cs.t list * pivot list
				= fun sx ->
				let null_rows = get_null_basic_variables sx in
				let scan_col = scan_column sx.PSplx.mat null_rows in
				let naming = Naming.to_vpl sx.PSplx.names in
				Misc.fold_left_i
					(fun col (frontiers, pivots) paramCoeff ->
						if not (ParamCoeff.is_zero paramCoeff)
						then begin(* the variable associated with the column is nonbasic *)
							let pivot_rows = scan_col col in
							if pivot_rows = []
							then let new_frontier = (ParamCoeff.to_cstr naming ParamCoeff.GT0 paramCoeff) in
								((new_frontier :: frontiers), pivots)
							else let new_pivots =
								List.map
									(fun row -> ((row, List.nth sx.PSplx.basis row), col))
									pivot_rows
								in
								(frontiers, (pivots @ new_pivots))
							end
						else (frontiers, pivots)
						)
					([], [])
					sx.PSplx.obj.Objective.lin

			let do_pivot : Basis.t -> Basis.t list -> bool
				= fun b basiss ->
				List.exists (Basis.equal b) basiss
				|> not


			let rec extract_rec : PSplx.t -> Basis.t list -> Cs.t list * Basis.t list
				= fun sx basiss ->
				Debug.log DebugTypes.Detail
					(lazy(Printf.sprintf "Extraction of region in tableau \n%s\n basis : %s "
					(PSplx.to_string sx)
					(*(Misc.list_to_string pivot_to_string previous_pivots " ; ")));*)
					(Misc.list_to_string string_of_int (List.sort Stdlib.compare sx.PSplx.basis) ";" )));
				let (frontiers, pivots) = extract' sx in
				List.fold_left
					(fun (frontiers,basiss) pivot ->
						let b = Basis.pivot sx.PSplx.basis pivot in
						if do_pivot b basiss
						then
							let ((leaving_var_row, leaving_var), entering_var) = pivot in
							Debug.log DebugTypes.Detail
								(lazy(Printf.sprintf "Pivoting on %s" (pivot_to_string pivot)));
							let sx' = PSplx.pivot sx leaving_var_row entering_var in
							let (frontiers', basiss') = extract_rec sx' (b :: basiss) in
							(frontiers @ frontiers', basiss')
						else (frontiers,basiss))
					(frontiers, basiss)
					pivots

			let extract : PSplx.t -> Cs.t list
				= fun sx ->
				Debug.log DebugTypes.Detail (lazy("Extracting region from simplex tableau"));
				let frontiers = extract_rec sx [Basis.make sx.PSplx.basis]
					|> Stdlib.fst
					|> Misc.rem_dupl (fun c c' -> Cs.equal c c')
		  			|> List.filter (fun c -> not (is_trivial c))
		  		in
		  		Debug.exec frontiers DebugTypes.Detail (lazy("Extraction done"));
		end
		(* VERSION ORIGINALE *)

		let extract : PSplx.t -> Cs.t list
		  	= fun sx ->
		  	Objective.foldi
			 	(fun i c l ->
			  		(ParamCoeff.to_cstr
					(Naming.to_vpl sx.PSplx.names)
					ParamCoeff.GT0 c)
			  		:: l)
			 	sx.PSplx.obj
			 	[]
			(* XXX: ça serait bien d'avoir une forme canonique des contraintes pour pourvoir remplacer equal par equalSyn*)
		  	|> Misc.rem_dupl (fun c c' -> Cs.equal c c')
		  	|> List.filter (fun c -> is_trivial c |> not)

		(* VERSION TEST *)
		(*
		let extract : PSplx.t -> Cs.t list
			= fun sx ->
			Profile.start "Extract.region";
			let res = Extract.extract sx in
			Profile.stop "Extract.region";
			res
		*)

		(** Returns a point in the regions' interior. The chosen point is a 1 from each boundary if possible. *)
		let getPointInside : region_t -> Cs.Vec.V.t -> Cs.t list -> Vec.t option
			= let getPointInside_cone : Cs.Vec.V.t -> Cs.t list -> Vec.t option
				= fun horizon cstrs ->
				match Splx.getPointInside_cone horizon cstrs with
				| None -> None
				| Some pl -> Some (Vec.M.map Vec.ofSymbolic pl)
			and getPointInside_not_cone : Cs.Vec.V.t -> Cs.t list -> Vec.t option
				= fun horizon cstrs ->
				let cstrs' = List.mapi
					(fun i cstr -> i, cstr)
					cstrs
				in
				match Opt.getAsg horizon cstrs' with
				| None -> None
				| Some pl -> Some (Vec.M.map Vec.ofSymbolic pl)
			in
			function
			| Cone -> getPointInside_cone
			| NCone -> getPointInside_not_cone

		(** Returns true if the given point lies in the given region. *)
		let (contains : t -> Vec.t -> bool)
			= fun reg p ->
			List.for_all
				(fun ((c,_),_) -> Cs.satisfy (Vec.toRat p) c)
				reg.r

		(** Returns true if the given point lies in the given region. *)
		let (contains' : Cs.t list -> Vec.t -> bool)
			= fun cstrs p ->
			List.for_all
				(fun c -> Cs.satisfy (Vec.toRat p) c)
				cstrs

		(** Returns true if the given point lies in the given relaxed ({i i.e.} non-strict) region. *)
		let (contains_large : t -> Vec.t -> bool)
			= fun reg p ->
			List.for_all
				(fun ((c,_),_) -> Cs.satisfy (Vec.toRat p) {c with Cs.typ = Cstr.Le})
				reg.r

		(** Returns true if the given point lies in the given relaxed ({i i.e.} non-strict) region. *)
		let (contains'_large : Cs.t list -> Vec.t -> bool)
			= fun cstrs p ->
			List.for_all
				(fun c -> Cs.satisfy (Vec.toRat p) {c with Cs.typ = Cstr.Le})
				cstrs

		let contains_ep : t -> ExplorationPoint.t -> bool
			= fun reg ->
			function
			| ExplorationPoint.Direction (_,(_,point)) ->
				contains reg point
			| ExplorationPoint.Point point ->
				contains reg point

		let contains_large_ep : t -> ExplorationPoint.t -> bool
			= fun reg ->
			function
			| ExplorationPoint.Direction (_,(_,point)) ->
				contains_large reg point
			| ExplorationPoint.Point point ->
				contains_large reg point

		let (equalSyn : t -> t -> bool)
			= fun reg1 reg2 ->
			List.for_all2 Cs.equalSyn (get_cstrs reg1) (get_cstrs reg2)

		let (equal : t -> t -> bool)
			= fun reg1 reg2 ->
			Misc.list_eq (fun c cstrs -> List.exists (fun c' -> Cs.equal c c') cstrs)
				(get_cstrs reg1) (get_cstrs reg2)

		let eval_obj : t -> Cs.Vec.t -> Cs.Vec.Coeff.t option
			= fun reg p ->
			match reg.sx with
			| None -> None
			| Some sx ->
				let cstr = PSplx.obj_value' sx in
				Some (Cs.eval' cstr p)
	end

	type mapRegs_t = Region.t MapV.t

	(*let next_id : int ref = ref 0*)

	type t = {
		regs : mapRegs_t;
		todo: ExplorationPoint.t list
	}

	let empty : t
		= {regs = MapV.empty ; todo = []}

	let to_string : t -> string
		= fun plp ->
		let regs = MapV.bindings plp.regs
			|> List.split
			|> Stdlib.snd
		in
		Printf.sprintf "Regions = %s\nTodo list : \n%s"
			(Misc.list_to_string Region.to_string regs "\n")
			(Misc.list_to_string ExplorationPoint.to_string plp.todo " ; ")

	(** Module that checks results on the fly.
		It is based on {!module:Debug.Check}, thus these verifications cost almost nothing if checking is disabled. *)
	module Check = struct

		let satisfy : Vec.t -> Cs.t -> bool
				= fun v c ->
				let v' = Vec.toRat v in
				Cs.satisfy v' c

		let check_boundary : Boundary.t -> unit
			= fun (cstr,point) ->
			Debug.Check.check
				(lazy (not (satisfy point cstr)))
				(lazy(Printf.sprintf "Point %s satisfies its boundary %s"
					(Vec.to_string Vec.V.to_string point)
					(Cs.to_string Cs.Vec.V.to_string cstr)))

		let check_region : Region.t -> unit
			= fun r ->
			begin
				Debug.Check.check (lazy(Region.contains r r.Region.point))
					(lazy(Printf.sprintf "point not in region %s"
					(Region.to_string r)));
				List.iter (fun (b,_) -> check_boundary b) r.Region.r
			end

		let check_result : t -> unit
			= fun plp ->
			MapV.iter (fun _ -> check_region) plp.regs
	end

	module Adjacency = struct

		(** Returns true if [reg1] and [reg2] are adjacent through [cstr1] and [cstr2].
		@param cstr1 must belong to [reg1]
		@param cstr2 must belong to [reg2] *)
		let adjacent_cstr_lp : Region.t -> Region.t -> Cs.t -> Cs.t -> bool
			= fun reg1 reg2 cstr1 cstr2->

				let cstrs_reg1 = {cstr1 with Cs.typ = Cstr.Le}
					:: (Misc.popAll Cs.equalSyn (Region.get_cstrs reg1) cstr1)
				and cstrs_reg2 = {cstr2 with Cs.typ = Cstr.Le}
					:: (Misc.popAll Cs.equal (Region.get_cstrs reg2) cstr2)
				in
				let cstrs = cstrs_reg1 @ cstrs_reg2 in
				let horizon = Cs.getVars cstrs
					|> Vec.V.horizon
				in
				let cstrs = List.mapi (fun i c -> (i,c)) cstrs in
				match Splx.mk horizon cstrs |> Splx.checkFromAdd with
				| Splx.IsUnsat _ -> false
				| Splx.IsOk _ -> true

		(** Returns true if [reg1] and [reg2] are adjacent through [cstr1] and [cstr2].
		@param cstr1 must belong to [reg1]
		@param cstr2 must belong to [reg2] *)
		let adjacent_cstr : Region.t -> Region.t -> Cs.t -> Cs.t -> bool
			= fun reg1 reg2 cstr1 cstr2 ->
				match reg1.Region.sx, reg2.Region.sx with
				| Some sx1, Some sx2 ->
					let p = Cs.get_saturating_point cstr1 in
					let obj1 = PSplx.obj_value' sx1
					and obj2 = PSplx.obj_value' sx2
					in
					Cs.Vec.Coeff.equal (Cs.eval' obj1 p) (Cs.eval' obj2 p)
				| _,_ -> adjacent_cstr_lp reg1 reg2 cstr1 cstr2

		let adjacent' : int -> Cs.t -> ((int * Cs.t) * 'a) list -> mapRegs_t -> int option
			= fun id_init cstr l regMap ->
			let reg = MapV.find id_init regMap in
			try
				let ((id',_),_) = List.find
					(fun ((id', cstr'), _) ->
						id_init <> id'
					  &&
					  	(adjacent_cstr reg (MapV.find id' regMap) cstr cstr'))
					l
				in
				Some id'
			with Not_found -> None

		(** returns [Some i] with [i] the index of the adjacent region if it exists, [None] otherwise. *)
		let adjacent : int -> Cs.t -> ((int * Cs.t) * 'a) list -> mapRegs_t -> int option
			= fun id_init cstr l regMap ->
			Profile.start "adjacent";
			let res = adjacent' id_init cstr l regMap in
			Profile.stop "adjacent";
			res
	end


	(** Several methods to choose the next point to explore. *)
	module Next_Point = struct

		module Min = Min.Min(Vec)(Vec)(Cs)(MinLP.Splx(Cs))

		let conv : Min.conversion
			= Min.({vec_CsVec = (fun x -> Vec.toRat x);
				csVec_Vec  = (fun x -> Vec.ofRat x) ;
				csCoeff_Coeff = (fun x -> Vec.Coeff.ofQ x) ;
				csInput_Cs = (fun x -> x) ;
				vecInput_Vec = (fun x -> x) ;
				vec_VecInput = (fun x -> x)
			})

		module Point_in_Region = struct
			(** Returns the index of the region in which the given point is minimal w.r.t objective functions. *)
			let eval_regions : ExplorationPoint.t -> t -> (int * Region.t) option
				= fun p plp ->
				try
					match p with
					| ExplorationPoint.Point point -> begin
						let point' = conv.Min.vec_CsVec point in
						MapV.fold
							(fun id reg value_opt ->
								match Region.eval_obj reg point', value_opt with
								| Some v, None -> Some ((id,reg),v)
								| Some v, Some (_,v') -> if Cs.Vec.Coeff.lt v' v
									then Some ((id,reg),v)
									else value_opt
								| None, _ -> value_opt)
							plp.regs
							None
						|> function
							| None -> None
							| Some (i,_) -> Some i
					end

					| ExplorationPoint.Direction (id, (_, point)) ->
						let point' = conv.Min.vec_CsVec point in
						MapV.fold
							(fun id' reg value_opt ->
								if id = id'
								then value_opt
								else match Region.eval_obj reg point', value_opt with
									| Some v, None -> Some ((id,reg),v)
									| Some v, Some (_, v') -> if Cs.Vec.Coeff.lt v' v
										then Some ((id,reg),v)
										else value_opt
									| None, _ -> value_opt)
							plp.regs
							None
						|> function
							| None -> None
							| Some (i,_) -> Some i
				with Invalid_argument _ -> None

			let in_region' : ExplorationPoint.t -> t -> (int * Region.t) option
				= fun p plp ->
				match eval_regions p plp with
				| Some (i,reg) ->
					if Region.contains_large_ep reg p
					then Some (i,reg)
					else None
				| None -> None
			(** Returns a region containing the given point, if it exists. *)

			let in_region : ExplorationPoint.t -> t -> (int * Region.t) option
				= fun p plp ->
				Profile.start "in_region";
				let res = in_region' p plp in
				Profile.stop "in_region";
				res
		end

		(** Module that chooses the next point to explore by raytracing. *)
		module RayTracing = struct

			let eval' : (int * Region.t) list -> Min.direction_type -> ((int * Cs.t) * Min.direction) list
				= fun regs dir_type ->
				List.fold_left
					(fun res (id,reg) ->
						List.fold_left
						(fun res ((cstr',_),_) ->
							let v = Min.Sort.value dir_type cstr' in
							((id, cstr'), (dir_type, v)) :: res)
						res reg.Region.r)
					[] regs

			let eval : (int * Region.t) list -> Min.direction_type -> ((int * Cs.t) * Min.direction) list
				= fun regs dir_type ->
				Profile.start "raytracing";
				let res = eval' regs dir_type in
				Profile.stop "raytracing";
				res

			(*
			(** Removes the initial region [reg] (identified by [id]) and those that are on the same side of [cstr] that [reg]. *)
			let filter_regions : int -> Cs.t -> mapRegs_t -> (int * Region.t) list
				= fun id cstr regMap ->
				MapV.fold
					(fun id' reg res ->
						if id = id' || (List.exists (fun ((cstr',_),_) -> Cs.equal cstr' cstr) reg.Region.r)
						then res
						else (id',reg) :: res )
					regMap
					[]
			*)
			(** Removes the initial region [reg] (identified by [id]) and those that are on the same side of [cstr] that [reg].
				TODO: use LP.*)
			let filter_regions : int -> Cs.t -> mapRegs_t -> (int * Region.t) list
				= fun id cstr regMap ->
				MapV.fold
					(fun id' reg res ->
						if id = id' || (List.exists (fun ((cstr',_),_) -> Cs.equal cstr' cstr) reg.Region.r)
						then res
						else (id',reg) :: res )
					regMap
					[]

			let debug_evals
				= fun l ->
				Debug.exec l DebugTypes.Detail
					(lazy(Printf.sprintf "Evals before post-processing : \n%s"
							(Misc.list_to_string
								(fun ((id,c),(_,v)) -> Printf.sprintf "id %i, %s -> %s"
									id
									(Cs.to_string Cs.Vec.V.to_string c)
									(Cs.Vec.Coeff.to_float v |> string_of_float))
								l "\n")))

			let compute_next_point : Cs.t -> ('a * Min.direction) list list ->  Cs.Vec.Coeff.t option
				= fun cstr evals ->
				let i = Misc.findi (List.exists (fun ((_,cstr'),_) -> Cs.equalSyn cstr cstr')) evals
				in
				let eval_i = List.filter
					(fun ((_,cstr'),_) -> not (Cs.equal cstr cstr')
						&& not (Cs.equal (strict_comp cstr) cstr'))
					(List.nth evals i)
				in
				match eval_i with
				| [] ->
					if List.length evals = (i+1) (* il n'y a pas d'élément après cstr dans la liste*)
					then None
					else let (_,(_,v2)) = List.nth evals (i+1) |> List.hd in
					Some v2
				| (_,(_,v2))  :: _ -> Some v2

			let eval_to_string : ('a * Min.direction) list list -> string
				= fun l ->
				Misc.list_to_string
					(fun l -> Misc.list_to_string
						(fun ((_,c),(_,v)) ->
							(Cs.to_string Cs.Vec.V.to_string c) ^ ", " ^ (Cs.Vec.Coeff.to_float v|>string_of_float)) l " ; ")
					l "\n"

			exception Adjacent of int

			let adjust'' : region_t -> (int * Boundary.t) -> mapRegs_t -> (int * Region.t) list -> ExplorationPoint.t
				= fun reg_t (id, (cstr, pointOtherSide)) regMap regions_to_eval ->
				Min.conv := conv;
				let x0 = (MapV.find id regMap).Region.point in
				let dir_type = Min.TwoPoints (x0,pointOtherSide) in
				let v1 = Min.Sort.value dir_type cstr in
				let evals = ((id,cstr), (dir_type, v1))
					:: (eval regions_to_eval dir_type)
					|> Min.Sort.sort
					|> Min.Sort.stack
				in
				Debug.log DebugTypes.Detail (lazy(Printf.sprintf "evals = %s"
					(eval_to_string evals)));
				try
					(* XXX: que se passe t-il si i n'est pas 0? *)
					let i = Misc.findi (List.exists (fun ((_,cstr'),_) -> Cs.equal cstr cstr')) evals in
					let evals =
						if List.length (List.nth evals i) > 1
						then (* On a trouvé des candidat adjacents, il faut vérifier qu'ils sont bien adjacents *)
							match Adjacency.adjacent id cstr (List.nth evals i) regMap with
							| None -> begin match reg_t with
								| Cone -> (Misc.sublist evals 0 i) @ [[(id,cstr), (dir_type, v1)]] @ (Misc.sublist evals (i+1) (List.length evals))
								| NCone -> evals
							end
							| Some id_adj -> Stdlib.raise (Adjacent id_adj) (* un des candidats était bien adjacent *)
						else evals
					in
					match compute_next_point cstr evals with
					| None -> ExplorationPoint.Direction(id, (cstr, pointOtherSide))
					| Some v2 ->
						let v' = Cs.Vec.Coeff.div
							(Cs.Vec.Coeff.add v1 v2)
							(Cs.Vec.Coeff.of_float 2.)
						in
						Debug.log DebugTypes.Detail
							(lazy (Printf.sprintf "computing middle of %s and %s : %s"
							(Cs.Vec.Coeff.to_string v1)
							(Cs.Vec.Coeff.to_string v2)
							(Cs.Vec.Coeff.to_string v')));
						let x = Min.Sort.getPoint cstr (dir_type,v') in
							Debug.log DebugTypes.Detail
							(lazy (Printf.sprintf "The next exploration point will be %s"
								(Vec.to_string Vec.V.to_string x)));
						ExplorationPoint.Direction(id, (cstr, x))
				with Not_found -> Stdlib.failwith "PLP.adjust"

			let adjust' : region_t -> (int * Boundary.t) -> mapRegs_t -> ExplorationPoint.t
				= fun reg_t (id, (cstr, pointOtherSide)) regMap ->
				let regions_to_eval = filter_regions id cstr regMap in
				adjust'' reg_t (id, (cstr, pointOtherSide)) regMap regions_to_eval

			let adjust : region_t -> (int * Boundary.t) -> mapRegs_t -> ExplorationPoint.t
				= fun reg_t (id, (cstr, pointOtherSide)) regMap ->
				Debug.log DebugTypes.Detail
					(lazy (Printf.sprintf "Adjusting exploration point (%s, %s, %s)"
						(Vec.to_string Vec.V.to_string((MapV.find id regMap).Region.point))
						(Cs.to_string Cs.Vec.V.to_string cstr)
						(Vec.to_string Vec.V.to_string pointOtherSide)));
				adjust' reg_t (id, (cstr, pointOtherSide)) regMap

			let apply_adjacency : t -> int -> Boundary.t -> int -> t
				= fun plp id_init boundary id_adj ->
				(* Updating the region map*)
				let (cstr,_) = boundary in
				let cstr_adj =  strict_comp cstr in
				let reg = MapV.find id_init plp.regs
				and reg_adj = MapV.find id_adj plp.regs in
				let reg = {reg with
					Region.r = List.map (fun (b,i) ->
						if Boundary.equal b boundary
						then (b,Some id_adj)
						else (b,i))
					 	reg.Region.r
				}
				and reg_adj = {reg_adj with
					Region.r = List.map (fun ((cstr',v),i) ->
						if Cs.equal cstr' cstr_adj(* XXX: equal?*)
						then ((cstr',v), Some id_init)
						else ((cstr',v),i))
					 	reg_adj.Region.r
				} in
				let map' = MapV.add id_init reg plp.regs
					|> MapV.add id_adj reg_adj in
				(* Updating the exploration point list*)
				let todo' = List.fold_left
					(fun res -> function
						| ExplorationPoint.Point v as x -> x :: res
						| ExplorationPoint.Direction (id,(cstr,b)) as x ->
							if id = id_adj && (Cs.equal cstr cstr_adj)(* XXX: equal?*)
							then res
							else x :: res)
					[] plp.todo in
				{regs = map' ; todo = todo'}


			(** The PLP state [t] is modified if an adjacency is found. *)
			let rec get_next_point_rec : region_t -> t -> t
				= fun reg_t plp ->
				match plp.todo with
				| [] -> plp
				| (ExplorationPoint.Direction (id,b)) :: tl -> begin
					try
						let p = adjust reg_t (id,b) plp.regs in
						{plp with todo = p :: tl}
					with Adjacent id_adjacent ->
						apply_adjacency {plp with todo = tl} id b id_adjacent
						|> get_next_point_rec reg_t
					end
				| (ExplorationPoint.Point vec) :: tl ->
					if MapV.exists (fun _ reg -> Region.contains reg vec) plp.regs
					then (Debug.log DebugTypes.Detail
							(lazy (Printf.sprintf "Exploration point %s lies within an already discovered region"
							(Vec.to_string Vec.V.to_string vec)));
						get_next_point_rec reg_t {plp with todo = tl})
					else {plp with todo = (ExplorationPoint.Point vec) :: tl}

			(** Returns the next point to explore, or [None] if there is none.
			The returned point is the first element of [plp.todo]. *)
			let get_next_point : region_t -> t -> ExplorationPoint.t option * t
				= fun reg_t plp ->
				let plp = get_next_point_rec reg_t plp in
				if plp.todo = []
				then (None, plp)
				else (Some (List.hd plp.todo),plp)
		end

		(** Other algorithm to find new exploration points *)
		module RayTracing_min = struct


			let eval : (int * Region.t) list -> Min.direction_type -> ((int * Cs.t) * Min.direction) list
				= fun regs dir_type ->
				List.fold_left
					(fun res (id,reg) ->
						List.fold_left
						(fun res ((cstr',_),_) ->
							let v = Min.Sort.value dir_type cstr' in
							((id, cstr'), (dir_type, v)) :: res)
						res reg.Region.r)
					[] regs

			let debug_evals
				= fun l ->
				Debug.exec l DebugTypes.Detail
					(lazy(Printf.sprintf "Evals before post-processing : \n%s"
							(Misc.list_to_string
								(fun ((id,c),(_,v)) -> Printf.sprintf "id %i, %s -> %s"
									id
									(Cs.to_string Cs.Vec.V.to_string c)
									(Cs.Vec.Coeff.to_float v |> string_of_float))
								l "\n")))

			let compute_next_point : Cs.t -> ('a * Min.direction) list list ->  Cs.Vec.Coeff.t option
				= fun cstr evals ->
				let i = Misc.findi (List.exists (fun ((_,cstr'),_) -> Cs.equalSyn cstr cstr')) evals
				in
				let eval_i = List.filter
					(fun ((_,cstr'),_) -> not (Cs.equal cstr cstr')
						&& not (Cs.equal (strict_comp cstr) cstr'))
					(List.nth evals i)
				in
				match eval_i with
				| [] ->
					if List.length evals = (i+1) (* il n'y a pas d'élément après cstr dans la liste*)
					then None
					else let (_,(_,v2)) = List.nth evals (i+1) |> List.hd in
					Some v2
				| (_,(_,v2))  :: _ -> Some v2

			let eval_to_string : ('a * Min.direction) list list -> string
				= fun l ->
				Misc.list_to_string
					(fun l -> Misc.list_to_string
						(fun ((_,c),(_,v)) ->
							(Cs.to_string Cs.Vec.V.to_string c) ^ ", " ^ (Cs.Vec.Coeff.to_float v|>string_of_float)) l " ; ")
					l "\n"

			exception Adjacent of int

			let adjust : region_t -> mapRegs_t -> (int * Boundary.t) -> (int * Region.t) -> ExplorationPoint.t
				= fun reg_t regMap (id, (cstr, pointOtherSide)) reg ->
				Min.conv := conv;
				let x0 = (MapV.find id regMap).Region.point in
				let dir_type = Min.TwoPoints (x0,pointOtherSide) in
				let v1 = Min.Sort.value dir_type cstr in
				let evals = ((id,cstr), (dir_type, v1))
					:: (eval [reg] dir_type)
					|> debug_evals
					|> Min.Sort.sort
					|> Min.Sort.stack
				in
				Debug.log DebugTypes.Detail (lazy(Printf.sprintf "evals = %s"
					(eval_to_string evals)));
				try
					(* XXX: que se passe t-il si i n'est pas 0? *)
					let i = Misc.findi (List.exists (fun ((_,cstr'),_) -> Cs.equal cstr cstr')) evals in
					let evals =
						if List.length (List.nth evals i) > 1
						then (* On a trouvé des candidat adjacents, il faut vérifier qu'ils sont bien adjacents *)
							match Adjacency.adjacent id cstr (List.nth evals i) regMap with
							| None -> begin match reg_t with
								| Cone -> (Misc.sublist evals 0 i) @ [[(id,cstr), (dir_type, v1)]] @ (Misc.sublist evals (i+1) (List.length evals))
								| NCone -> evals
							end
							| Some id_adj -> Stdlib.raise (Adjacent id_adj) (* un des candidats était bien adjacent *)
						else evals
					in
					match compute_next_point cstr evals with
					| None -> ExplorationPoint.Direction(id, (cstr, pointOtherSide))
					| Some v2 ->
						let v' = Cs.Vec.Coeff.div
							(Cs.Vec.Coeff.add v1 v2)
							(Cs.Vec.Coeff.of_float 2.)
						in
						Debug.log DebugTypes.Detail
							(lazy (Printf.sprintf "computing middle of %s and %s : %s"
							(Cs.Vec.Coeff.to_string v1)
							(Cs.Vec.Coeff.to_string v2)
							(Cs.Vec.Coeff.to_string v')));
						let x = Min.Sort.getPoint cstr (dir_type,v') in
							Debug.log DebugTypes.Detail
							(lazy (Printf.sprintf "The next exploration point will be %s"
								(Vec.to_string Vec.V.to_string x)));
						ExplorationPoint.Direction(id, (cstr, x))
				with Not_found -> Stdlib.failwith "PLP.adjust"

			let apply_adjacency : t -> int -> Boundary.t -> int -> t
				= fun plp id_init boundary id_adj ->
				(* Updating the region map*)
				let (cstr,_) = boundary in
				let cstr_adj =  strict_comp cstr in
				let reg = MapV.find id_init plp.regs
				and reg_adj = MapV.find id_adj plp.regs in
				let reg = {reg with
					Region.r = List.map (fun (b,i) ->
						if Boundary.equal b boundary
						then (b,Some id_adj)
						else (b,i))
					 	reg.Region.r
				}
				and reg_adj = {reg_adj with
					Region.r = List.map (fun ((cstr',v),i) ->
						if Cs.equal cstr' cstr_adj(* XXX: equal?*)
						then ((cstr',v), Some id_init)
						else ((cstr',v),i))
					 	reg_adj.Region.r
				} in
				let map' = MapV.add id_init reg plp.regs
					|> MapV.add id_adj reg_adj in
				(* Updating the exploration point list*)
				let todo' = List.fold_left
					(fun res -> function
						| ExplorationPoint.Point v as x -> x :: res
						| ExplorationPoint.Direction (id,(cstr,b)) as x ->
							if id = id_adj && (Cs.equal cstr cstr_adj)(* XXX: equal?*)
							then res
							else x :: res)
					[] plp.todo in
				{regs = map' ; todo = todo'}

			(** The PLP state [t] is modified if an adjacency is found. *)
			let rec get_next_point_rec : region_t -> t -> t
				= fun reg_t plp ->
				match plp.todo with
				| [] -> plp
				| ((ExplorationPoint.Direction (id,b)) as ep):: tl -> begin
					match Point_in_Region.in_region ep plp with
					| None -> {plp with todo = ep :: tl}
					| Some (i,reg) ->
					try
						let p = adjust reg_t plp.regs (id,b) (i,reg) in
						 get_next_point_rec reg_t {plp with todo = p :: tl}
					with Adjacent id_adjacent ->
						apply_adjacency {plp with todo = tl} id b id_adjacent
						|> get_next_point_rec reg_t
					end
				| ((ExplorationPoint.Point vec) as ep) :: tl ->
					match Point_in_Region.in_region ep plp with
					| None -> {plp with todo = ep :: tl}
					| Some reg -> begin
						(Debug.log DebugTypes.Detail
						(lazy (Printf.sprintf "Exploration point %s lies within an already discovered region"
						(Vec.to_string Vec.V.to_string vec)));
						get_next_point_rec reg_t {plp with todo = tl})
					end

			(** Returns the next point to explore, or [None] if there is none.
				The returned point is the first element of [plp.todo]. *)
			let get_next_point : region_t -> t -> ExplorationPoint.t option * t
				= fun reg_t plp ->
				let plp = get_next_point_rec reg_t plp in
				if plp.todo = []
				then (None, plp)
				else (Some (List.hd plp.todo),plp)
		end

		module Greedy = struct

			let get_next : t -> int * Boundary.t -> ExplorationPoint.t option
				= fun plp (reg_id, (cstr,point)) ->
				let ipoint = (MapV.find reg_id plp.regs).Region.point in
				let dir = Min.TwoPoints (ipoint, point) in
				let t = Min.Sort.value dir cstr in
				let vec = Min.Sort.getPoint' (dir, Cs.Vec.Coeff.add t (Cs.Vec.Coeff.of_float 0.1)) in
				match Point_in_Region.in_region (ExplorationPoint.Point vec) plp with
				| None -> Some (ExplorationPoint.Point vec)
				| _ ->  None


			let rec get_next_point_rec : region_t -> t -> t
				= fun reg_t plp ->
				match plp.todo with
				| [] -> plp
				| (ExplorationPoint.Direction (id,b)) :: tl -> begin
					match get_next plp (id,b) with
					| Some ep -> {plp with todo = ep :: tl}
					| None -> get_next_point_rec reg_t {plp with todo = tl}
					end
				| (ExplorationPoint.Point vec) :: tl ->
					if MapV.exists (fun _ reg -> Region.contains reg vec) plp.regs
					then (Debug.log DebugTypes.Detail
							(lazy (Printf.sprintf "Exploration point %s lies within an already discovered region"
							(Vec.to_string Vec.V.to_string vec)));
						get_next_point_rec reg_t {plp with todo = tl})
					else {plp with todo = (ExplorationPoint.Point vec) :: tl}

			(** Returns the next point to explore, or [None] if there is none.
				The returned point is the first element of [plp.todo]. *)
			let get_next_point : region_t -> t -> ExplorationPoint.t option * t
				= fun reg_t plp ->
				Min.conv := conv;
				let plp = get_next_point_rec reg_t plp in
				if plp.todo = []
				then (None, plp)
				else (Some (List.hd plp.todo),plp)
		end
	end

	let get_next_point
		= fun reg_t plp ->
		Profile.start "get_next_point";
		let res = match !Flags.plp with
			| Flags.Greedy -> Next_Point.Greedy.get_next_point reg_t plp
			| Flags.Adj_Raytracing -> Next_Point.RayTracing.get_next_point reg_t plp
			| Flags.Adj_Raytracing_min -> Next_Point.RayTracing_min.get_next_point reg_t plp
		in
		Profile.stop "get_next_point";
		res

	let reg_id : int ref = ref 0

	(** Returns a fresh id for a new region. *)
	let get_fresh_id : unit -> int
		= fun () ->
		let id = !reg_id in
		reg_id := id + 1;
		id

	(** Module that runs one exploration *)
	module Exec = struct

		(*
		(** [correct_point names cstrs point] returns a point that lies in [cstrs]'s interior.
			If [point] fulfills this criterion, if is returned.
			If no such point exists, [None] is returned.
		*)
		let correct_point : Naming.t -> Cs.t list -> Vec.t -> Vec.t option
			= fun names cstrs point ->
			Debug.log DebugTypes.Detail (lazy("Correcting region"));
			if Region.contains' cstrs point
			then Debug.exec (Some point) DebugTypes.Detail (lazy "Point unchanged")
			else match Region.getPointInside (Naming.vpl_max names) cstrs with
				| None -> Debug.exec None DebugTypes.Detail (lazy "Region has empty interior")
				| Some p -> begin
					Debug.log DebugTypes.Detail (lazy(Printf.sprintf "Changing point %s to %s"
						(Vec.to_string V.to_string point)
						(Vec.to_string V.to_string p)));
					Some p
				end
		*)

		(* XXX: faut-il remettre la version ci-dessus pour les floats? *)

		(** [correct_point names cstrs point] returns a point that lies in [cstrs]'s interior.
			If no such point exists, [None] is returned.
			It uses {!val:Region.getPointInside}.
		*)
		let correct_point : region_t -> Naming.t -> Cs.t list -> Vec.t -> Vec.t option
			= fun reg_t names cstrs point ->
			Debug.log DebugTypes.Normal (lazy("Correcting region"));
			match Region.getPointInside reg_t (Naming.vpl_max names) cstrs with
			| None -> Debug.exec None DebugTypes.Normal
				(lazy (Printf.sprintf "Region has empty interior:\n%s"
					(Cs.list_to_string cstrs)))
			| Some p when Region.contains' cstrs p -> begin
				Debug.log DebugTypes.Normal (lazy(Printf.sprintf "Changing point %s to %s"
					(Vec.to_string V.to_string point)
					(Vec.to_string V.to_string p)));
				Some p
				end
			| Some p -> Stdlib.failwith
				(Printf.sprintf "Point correction returned %s, which is not in region %s"
					(Vec.to_string Vec.V.to_string p)
					(Cs.list_to_string cstrs))

		(** [get_boundaries cstrs point] returns the list of boundaries by minimizing [cstrs].
			@param point must be a point in the interior of [cstrs]. *)
		let (get_boundaries : region_t -> Cs.t list -> Vec.t -> Boundary.t list)
			= fun reg_t cstrs point ->
			Debug.log DebugTypes.Detail (lazy("Looking for true boundaries in new region"));
			let res = match reg_t with
				| Cone -> Minimization.minimize_cone point cstrs
				| NCone -> Minimization.minimize point cstrs in
			let len = List.length cstrs
			and len_res = List.length res in
			Stat.incr_redundancy (len - len_res) len_res;
			res

		let exec' : region_t -> Objective.pivotStrgyT -> PSplx.t -> Vec.t -> Region.t option
		  	= fun reg_t st sx pointToExplore ->
		  	Debug.log DebugTypes.Normal
		  		(lazy("Exec on the point " ^ (Vec.to_string V.to_string pointToExplore)));
		  	Profile.start "LP" ;
		 	let sx' = Explore.push st pointToExplore sx in
		 	Profile.stop "LP" ;
		 	Debug.log DebugTypes.Normal
		  		(lazy("Found solution " ^ (PSplx.obj_value sx' |> PSplx.ParamCoeff.to_string)));
		 	let cstrs = Region.extract sx' in
		 	match correct_point reg_t sx'.PSplx.names cstrs pointToExplore with
		 	| None -> None
		 	| Some point ->
		 		let bounds = get_boundaries reg_t cstrs point in
		 		let id = get_fresh_id() in
		 		let reg = Region.mk id bounds point sx' in
		 		Check.check_region reg;
		 		Some reg

		 (** [exec strat sx map exp] returns the region resulting from the exploration of [exp].
			If this region has empty interior, it returns [None]. *)
		let exec : region_t -> Objective.pivotStrgyT -> PSplx.t -> Vec.t -> Region.t option
		  	= fun reg_t st sx pointToExplore ->
		  	Profile.start "exec";
		  	let res = exec' reg_t st sx pointToExplore in
		  	Profile.stop "exec";
		  	res
	end

	let extract_points : Region.t -> int -> ExplorationPoint.t list
		= fun reg reg_id->
		List.map
			(fun (b,_) -> ExplorationPoint.Direction (reg_id, b))
			reg.Region.r

	(** Initialized simplex tableau *)
	let sx_glob : PSplx.t ref = ref PSplx.empty

	let get_sx : Region.t -> PSplx.t
		= fun reg ->
		match reg.Region.sx with
		| Some sx -> sx
		| None -> !sx_glob

	type config = {
		add_region : Region.t option -> Region.t -> ExplorationPoint.t -> t -> t;
		reg_t : region_t;
		points : ExplorationPoint.t list;
		stgy : Objective.pivotStrgyT;
		regions : Region.t list;
		}

	(* TODO : tirer parti des égalités! *)
	module Add_Region = struct

		(** [should_explore_again reg1 cstr reg2] checks whether the point that has been explored should be explored again.
		@param reg1 is the provenance region.
		@param cstr is constraint that has been crossed in the previous region.
		@param reg2 is the new discovered region.*)
		let should_explore_again : Region.t -> Cs.t -> Region.t -> bool
			= fun reg1 cstr reg2 ->
			let cstr_comp = strict_comp cstr in
			Adjacency.adjacent_cstr reg1 reg2 cstr cstr_comp
			|> not

		(* TODO: better equality test? *)
		(** [region_already_known reg plp] checks whether [reg] is already present in [plp]. *)
		let region_already_known : Region.t -> t -> bool
			= fun reg plp ->
			MapV.exists
				(fun _ reg' -> Region.equal reg reg')
				plp.regs

		(** Return a witness if the region has no interior, [None] otherwise. *)
		let has_interior : Region.t -> bool
			= fun reg ->
			let cstrs = Region.get_cstrs reg in
			let nvar = Cs.getVars cstrs |> Cs.Vec.V.horizon in
			let cstrs' = List.mapi (fun i c -> (i,c)) cstrs in
			match Splx.checkFromAdd (Splx.mk nvar cstrs') with
			| Splx.IsOk _ -> true
			| Splx.IsUnsat _ -> false (*match w with
				| [i,_] -> Some (List.assoc i cstrs')
				| _ -> Stdlib.failwith "PLP.has_interior"*)

		let remove_point : ExplorationPoint.t -> ExplorationPoint.t list -> ExplorationPoint.t list
			= fun point points ->
			Misc.pop ExplorationPoint.equal points point

		let do_not_add : Region.t -> ExplorationPoint.t -> t -> t
			= fun reg explorationPoint plp ->
			Debug.log DebugTypes.Normal (lazy "Region not added");
			{plp with todo = (remove_point explorationPoint plp.todo)}

		let add : config -> Region.t option -> Region.t -> ExplorationPoint.t -> t -> t
			= fun config reg_origin new_reg explorationPoint plp ->
			if region_already_known new_reg plp
			then do_not_add new_reg explorationPoint plp
			else if has_interior new_reg
				then config.add_region reg_origin new_reg explorationPoint plp
				else do_not_add new_reg explorationPoint plp
	end

	module InitSx = struct
		(** Leads to a feasible parametric simplex tableau. *)
		let init_sx : Objective.pivotStrgyT -> PSplx.t -> Vec.t -> PSplx.t option
			= fun st sx point ->
			Debug.log DebugTypes.Normal
				(lazy(Printf.sprintf "PLP initialization with point = %s"
					(Vec.to_string Vec.V.to_string point)));
		  	match Explore.Init.findFeasibleBasis sx point with
		  	| None -> Debug.exec None DebugTypes.Normal (lazy "Problem Unsat")
		  	| Some sx as r -> Debug.exec r DebugTypes.Normal (lazy "Problem Sat")

		(** Returns true if the input simplex tableau is feasible, and initializes variable sx with it.*)
		let init : Vec.t -> config -> PSplx.t -> bool
			= fun point config sx ->
			match init_sx config.stgy sx point with
		  	| None -> false
		  	| Some sx' -> begin
		  		Debug.log DebugTypes.Detail (lazy (Printf.sprintf "Initialized simplex tableau : \n%s"
		  			(PSplx.to_string sx')));
		  		sx_glob := sx';
		  		true
		  		end

	end

	(** This function is used when an execution (ran on point [p]) led to a region with empty interior.
	It returns the middle between the initial region's point and [p]. *)
	let find_new_point : Vec.t -> Vec.t -> Vec.t
		= fun init_point explored_point ->
		Vec.middle init_point explored_point

	let rec exec : config -> t -> t
		= fun config plp ->
		Debug.log DebugTypes.Normal
			(lazy (Printf.sprintf "Current exploration list : \n%s"
				(Misc.list_to_string ExplorationPoint.to_string plp.todo " ; ")));
		match get_next_point config.reg_t plp with
		| (None, plp') -> plp'
		| (Some explorationPoint, plp') ->
			match explorationPoint with
			| ExplorationPoint.Direction (id, (cstr, pointToExplore)) -> begin
				Debug.log DebugTypes.Detail
					(lazy (Printf.sprintf "Exec on constraint %s and point %s"
						(Cs.to_string Cs.Vec.V.to_string cstr)
						(Vec.to_string Vec.V.to_string pointToExplore)));
				let reg = MapV.find id plp'.regs in
				match Exec.exec config.reg_t config.stgy (get_sx reg) pointToExplore with
				| None ->
					let newPointToExplore = find_new_point reg.Region.point pointToExplore in
					let newExplorationPoint = ExplorationPoint.Direction(id, (cstr, newPointToExplore)) in
					(* on remplace l'ancien ExplorationPoint.t de todo par le nouveau *)
					exec config {plp' with todo = List.tl plp'.todo @ [newExplorationPoint]}
				| Some reg' -> exec config (Add_Region.add config (Some reg) reg' explorationPoint plp')
				end
			| ExplorationPoint.Point pointToExplore ->
				match Exec.exec config.reg_t config.stgy !sx_glob pointToExplore with
				| None -> exec config {plp' with todo = (Add_Region.remove_point explorationPoint plp'.todo)}
				| Some reg' -> exec config (Add_Region.add config None reg' explorationPoint plp')

	(** [extract_sol sx map] returns the output constraint corresponding to the objective value of [sx].
	This constraint is of type {!type:Cons.t}, which certificate is computed thanks to [map]. *)
	let extract_sol : PSplx.t -> (PSplx.t -> 'c) -> 'c Cons.t
		= fun sx get_cert ->
		let cstr = PSplx.obj_value' sx |> Cs.canon
		and cert = get_cert sx in
		(cstr, cert)

	let result_to_string : (Region.t * 'c Cons.t) list option -> string
		= fun res ->
		match res with
		| None -> "None"
		| Some res ->
			Printf.sprintf "Regions = %s\n"
				(Misc.list_to_string
					(fun (reg, (c,_)) ->
						(Region.to_string reg)
						^ "\nSolution = "
						^ (Cs.to_string Cs.Vec.V.to_string c))
					res "\n")

	(* Under construction, for testing purpose *)
	(*
	let check_redundancies : (Region.t * 'c Cons.t) list -> unit
		= let is_orthogonal : 'c Cons.t -> Cs.t -> bool
			= fun (cstr,_) cstr' ->
			Cs.Vec.dot_product cstr.Cs.v cstr'.Cs.v
			|> Cs.Vec.Coeff.isZ
		in
		(*let find_common_constraint : Region.t list -> Cs.t
			= fun *)
		fun res ->
		let reg_list = List.map
			(fun (_, cons) ->
				let regs = List.filter (fun (_,cons') -> Cons.equal cons cons') res
					|> List.split
					|> Stdlib.fst
				in
				(regs,cons))
			res
			(* only take regions that are subdivided*)
			|> List.filter (fun (regs,_) -> List.length regs > 1)
		in
		List.iter
			(fun (regs,cons) -> Stat.incr_subdivisions (List.length regs) 1)
			reg_list
		;
		(*
		List.iter
			(fun (regs,cons) ->
				Printf.sprintf "%s -> \n%s\n\n"
					(Cons.to_string Cs.Vec.V.to_string cons)
					(Misc.list_to_string Region.to_string regs "\n")
				|> print_endline)
			reg_list
		*)
		()
	*)

	(** Careful: if a region has no simplex tableau (because it was given in input), it does not appear in the result. *)
	let get_results : t -> (PSplx.t -> 'c) -> (Region.t * 'c Cons.t) list option
		= let extract_sols : (PSplx.t -> 'c) -> Region.t list -> (Region.t * 'c Cons.t) list
			= fun get_cert regs ->
			List.fold_left
				(fun res reg -> match reg.Region.sx with
					| None -> res
					| Some sx -> (reg, extract_sol sx get_cert) :: res)
				[] regs
		in
		fun plp get_cert ->
		let regs = MapV.bindings plp.regs
			|> List.split
			|> Stdlib.snd
            |> List.map Region.canon
		in
		Stat.nb_regions := List.length regs;
		let results = extract_sols get_cert regs in
		Debug.log DebugTypes.MOutput
			(lazy(result_to_string (Some results)));
		(*check_redundancies results;*) (* XXX: pour tests seulement! *)
		Some results

	(* also initializes the fresh region id *)
	let init_regions : config -> mapRegs_t
		= fun config ->
		reg_id := 0;
		List.fold_left
			(fun map reg ->
				if !reg_id <= reg.Region.id
				then reg_id := reg.Region.id + 1;
				MapV.add reg.Region.id {reg with Region.sx = None} map)
			MapV.empty config.regions

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

	let init_and_exec : config -> PSplx.t -> (PSplx.t -> 'c) -> t option
		= fun config sx get_cert ->
		let (point,config) = choose_init_point sx config in
		if InitSx.init point config sx
		then
			let plp = {
			regs = init_regions config;
			todo = config.points
			} in
			Some (exec config plp)
		else None

	let run : config -> PSplx.t -> (PSplx.t -> 'c) -> (Region.t * 'c Cons.t) list option
		= fun config sx get_cert ->
		Stat.reset();
		Random.init 0;
		Debug.log DebugTypes.Title
			(lazy("PLP solver with scalar_type = " ^ (Vec.Coeff.name)));
		Debug.log DebugTypes.MInput
			(lazy (Printf.sprintf "Exploration points provided : %s\n%s"
				(Misc.list_to_string ExplorationPoint.to_string config.points " ; ")
				(PSplx.to_string sx)));
		Profile.start "run";
		let res = match init_and_exec config sx get_cert with
		| None -> None
		| Some plp -> get_results plp get_cert
		in
		Profile.stop "run";
		res

end

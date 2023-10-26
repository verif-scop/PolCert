module Cs = PLPCore.Cs
module EqSet = PLPCore.EqSet
module Cons = PLPCore.Cons
module Cert = Cons.Cert

module Debug = DebugTypes.Debug(struct let name = "PLP" end)

module type Type = sig
	module Minimization : Min.Type
	module MapV : Map.S with type key = int
	module PSplx : PSplx.Type
	module Naming : Naming.Type

	(** This map is used for the certificate generation.
	Is associates to each simplex column an element of {!type:Cons.t}. *)
	type 'c mapVar_t = ('c Cons.t) MapV.t

	module Boundary : sig
		type t
	end

	module Region : sig
		type t = {
			id : int;
			r : (Boundary.t * int option) list;
			point : Minimization.Vec.t; (* Un point dans la région *)
			sx : PSplx.t option(* Tableau de simplexe dont l'objectif a donné cette région *)
		}
	end

	type region_t = Cone | NCone

	module ExplorationPoint : sig
		type t =
			| Direction of int * Boundary.t (** (id of origin region, boundary*)
			| Point of Minimization.Vec.t
	end

	type t

	type get_next_point_t = region_t -> t -> ExplorationPoint.t option * t

	module RayTracing : sig
		val get_next_point : get_next_point_t
	end

	module RegionTesting : sig
		val get_next_point : get_next_point_t
	end

	val get_cert_default : 'c Cert.t -> 'c mapVar_t -> PSplx.t -> 'c

	val get_no_cert : 'c Cert.t -> PSplx.t -> 'c

	type config = {
		get_next_point : get_next_point_t;
		reg_t : region_t;
		points : ExplorationPoint.t list;
		stgy : PSplx.Objective.pivotStrgyT;
		regions : Region.t list;
		}

	val std_config : config

	val run : config -> PSplx.t -> (PSplx.t -> 'c) -> (Region.t * 'c Cons.t) list option

	(** Same as {!val:run} where regions are cones. *)
	val run_classic : PSplx.t -> (PSplx.t -> 'c) -> (Region.t * 'c Cons.t) list option
end

module PLP(Minimization : Min.Type) = struct

	module Minimization = Minimization
	include PLPDistrib.PLP(Minimization)

	let get_cert_default : 'c Cert.t -> 'c mapVar_t -> PSplx.t -> 'c
		= fun factory map sx ->
		let basisValue = PSplx.getCurVal sx in
		List.fold_left
			(fun l (col,q) ->
				if Q.equal q Q.zero
				then l
				else
					try let (_,cert) = MapV.find col map in
						(cert, q) :: l
					with Not_found -> l)
			[]
			basisValue
		|> Cert.linear_combination factory

	let get_no_cert : 'c Cert.t -> PSplx.t -> 'c
		= fun factory _ ->
		factory.Cert.top

	(*
	(** We test if exploration points belong to already discovered regions. *)
	module RegionTesting = struct

		let rec get_next_point_rec : region_t -> ExplorationPoint.t list -> mapRegs_t -> ExplorationPoint.t list
			= fun reg_t todo regMap ->
			match todo with
			| [] -> []
			| (ExplorationPoint.Point v) :: tl -> begin
				if MapV.exists (fun _ reg -> Region.contains reg v) regMap
				then get_next_point_rec reg_t tl regMap
				else (ExplorationPoint.Point v) :: tl
				end
			| _ -> Stdlib.failwith "PLP.RegionTesting.get_next_point_rec"

		let get_next_point : get_next_point_t
			= fun reg_t plp ->
			let plp = {plp with todo = get_next_point_rec reg_t plp.todo plp.regs} in
			if plp.todo = []
			then (None, plp)
			else
				(Some (List.hd plp.todo), plp)
	end
	*)
	let standard : Region.t option -> Region.t -> ExplorationPoint.t -> t -> t
			= fun origin_reg reg point plp ->
			Debug.log DebugTypes.Normal (lazy "Adding new region to plp");
			let id = reg.Region.id in
			let regs = MapV.add id reg plp.regs in
			let new_points = extract_points reg id in
			match point with
			| ExplorationPoint.Point vec ->
				let todo = new_points @ (Add_Region.remove_point point plp.todo) in
				{regs = regs ; todo = todo}
			| ExplorationPoint.Direction (id, (cstr, pointToExplore)) as point ->
				let todo = match origin_reg with
					| Some origin_reg ->
						if Add_Region.should_explore_again origin_reg cstr reg
						then new_points @ plp.todo
						else new_points @ (Add_Region.remove_point point plp.todo)
					| None -> new_points @ plp.todo
				in
				{regs = regs ; todo = todo}

	let standard_test : Region.t option -> Region.t -> ExplorationPoint.t -> t -> t
			= fun _ reg point plp ->
			Debug.log DebugTypes.Normal (lazy "Adding new region to plp");
			let regs = MapV.add reg.Region.id reg plp.regs in
			let todo = Add_Region.remove_point point plp.todo in
			{regs = regs ; todo = todo}

	let std_config = {
		add_region = standard;
		reg_t = Cone;
		points = [];
		stgy = Objective.Bland;
		regions = [];
	}

	(* Checks if each basis can move to another one with only one pivot.
	First version *)
	let check_basis : (Region.t * 'c Cons.t) list option -> bool
		= let rec differences : int list -> int list -> int
			= fun b1 b2 ->
			match b1,b2 with
			| [],[] -> 0
			| [],_ | _,[] -> Stdlib.invalid_arg "check_basis"
			| x1 :: tl1, x2 :: tl2 when x1 = x2 -> differences tl1 tl2
			| _ :: tl1, _ :: tl2 -> 1 + (differences tl1 tl2)
		in
		fun sols ->
		match sols with
		| None -> true
		| Some sols -> begin
			let bases = List.fold_left
				(fun bases (reg, _) -> match reg.Region.sx with
					| None -> bases
					| Some sx -> PSplx.get_basis sx :: bases
				)
				[] sols
			in
			List.for_all
				(fun basis -> List.exists
					(fun basis' -> differences basis basis' = 1)
					bases)
				bases
		end

	(* Checks if each basis can move to another one with only one pivot.
	Second version *)
	let check_basis : (Region.t * 'c Cons.t) list option -> bool
		= let rec differences : int list -> int list -> int
			= fun b1 b2 ->
			match b1,b2 with
			| [],[] -> 0
			| [],_ | _,[] -> Stdlib.invalid_arg "check_basis:1"
			| x1 :: tl1, x2 :: tl2 when x1 = x2 -> differences tl1 tl2
			| _ :: tl1, _ :: tl2 -> 1 + (differences tl1 tl2)
		in
		let reachable_in_one_pivot : Region.t -> Region.t -> bool
			= fun reg1 reg2 ->
			match reg1.Region.sx, reg2.Region.sx with
			| None,_ | _,None -> Stdlib.invalid_arg "check_basis:2"
			| Some sx1, Some sx2 -> differences sx1.PSplx.basis sx2.PSplx.basis = 1
		in
		let rec get_adjacent_region : (Region.t * 'c Cons.t) list -> Region.t -> Cs.t -> Region.t option
			= fun sols reg cstr ->
			match sols with
			| [] -> None
			| (reg',_) :: sols  ->
				if Adjacency.adjacent_cstr reg reg' cstr (strict_comp cstr)
				then Some reg'
				else get_adjacent_region sols reg cstr
		in
		fun sols ->
		match sols with
		| None -> true
		| Some sols -> begin
			List.for_all
				(fun (reg,cons) ->
					List.for_all
						(fun ((cstr,_), _) ->
							match get_adjacent_region (Misc.pop (=) sols (reg,cons)) reg cstr with
							| None -> Stdlib.failwith "check_basis:2"
							| Some reg' -> begin
								Debug.log DebugTypes.Detail
									(lazy (Printf.sprintf "Adjacency between \n%s\nAND\n%s"
									(Region.to_string reg)
									(Region.to_string reg')));
								if reachable_in_one_pivot reg reg'
								then true
								else (Debug.log DebugTypes.Detail (lazy " -> ko");false)
								end
						)
					reg.Region.r
				)
				sols
		end

	let run: config -> PSplx.t -> (PSplx.t -> 'c) -> (Region.t * 'c Cons.t) list option
		= fun config sx get_cert ->
		let res =
			if PSplx.nParams sx = 0 || !Flags.distributed_plp = None || !Flags.distributed_plp = Some 0
			then run config sx get_cert
			else Stdlib.failwith "Distributed PLP not implemented" (*Distributed.run config.stgy sx get_cert*)
		in begin
			if PLPCore.Debug.is_enabled DebugTypes.Sage
			then match res with
				| None -> ()
				| Some regs -> Plot.plot regs
		end;
		if PLPCore.Debug.is_enabled DebugTypes.Detail
		then begin if check_basis res
			then print_endline "ok"
			else print_endline "ko"
		end;
		res

	let run_classic : PSplx.t -> (PSplx.t -> 'c) -> (Region.t * 'c Cons.t) list option
		= fun sx get_cert ->
		run std_config sx get_cert

end

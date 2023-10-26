exception Glpk_not_installed

module type Type = sig
	
	module CsUser : Cstr.Type

	type t
	
	module MapC : Map.S with type key = CsUser.t
	
	val name : string
	
	type mayUnsatT
		= IsOk of t | IsUnsat
	
	val to_string : t -> string
		
	val mk : CsUser.t list -> CsUser.Vec.V.t list -> mayUnsatT

	val get_solution : t -> CsUser.Vec.t
			
	val add_cstrs : CsUser.t list -> t -> mayUnsatT
			
	val add_cstr : CsUser.t -> t -> mayUnsatT
end

module Debug = DebugTypes.Debug(struct let name = "MinLP" end)

module Stat = struct	
	let enabled : bool ref = ref false
	
	let enable : unit -> unit
		= fun _b ->
		enabled := true
		
	let disable : unit -> unit
		= fun _b ->
		enabled := false
	
	let n_lp : int ref = ref 0
	
	let size_lp : int ref = ref 0
	
	let reset : unit -> unit
		= fun () ->
		n_lp := 0;
		size_lp := 0
	
	
	let incr_size : int -> unit
		= fun size ->
		if !enabled
		then size_lp := !size_lp + size 
	
	let incr : unit -> unit
		= fun () ->
		if !enabled
		then n_lp := !n_lp + 1
end

module Splx (CsUser : Cstr.Type) = struct
	
	module CsPriv = Cstr.Rat.Positive
	module CsUser = struct
		include CsUser
		let compare = cmp
	end
	
	module V = CsPriv.Vec.V
	
	module MapC = Map.Make(CsUser)
	
	module Integer = struct
		type t = int
		let compare = Stdlib.compare
	end
	
	module MapI = Map.Make(Integer)
	type mapInt_t = CsUser.t MapI.t
	
	let name = "Splx"
	
	type t = {
		mapInt : mapInt_t;
		vars : V.t list ; 
		sx : Splx.t}
	
	let userToPriv : CsUser.t -> CsPriv.t
		= fun c_user ->
		{	
			CsPriv.typ = c_user.CsUser.typ
			; 
			CsPriv.c = CsUser.Vec.Coeff.toQ c_user.CsUser.c
			;
			CsPriv.v = 
				CsUser.Vec.toList c_user.CsUser.v
				|> List.map
					(fun (v,c) -> 
						(CsUser.Vec.Coeff.toQ c,
						CsUser.Vec.V.toPos v |> Var.Positive.fromPos))
				|> CsPriv.Vec.mk
		}
		
	type mayUnsatT
		= IsOk of t | IsUnsat
	
	let to_string : t -> string
		= fun x -> 
		Splx.pr Splx.V.to_string x.sx
				
	let mk' : CsUser.t list -> V.t list -> mayUnsatT
		= fun cstrs vars ->
		let horizon = V.max vars |> V.next 
		in  
		let (mapI,cstrs,_) = List.fold_left
			(fun (map,l,i) c -> 
				let c' = userToPriv c in
				(MapI.add i c map, 
				 (i,c') :: l, 
				 i+1)
			)
			(MapI.empty, [], 0)
			cstrs
		in
		match	Splx.mk horizon cstrs with
		| Splx.IsOk sx -> IsOk
			{mapInt = mapI;
			 vars = vars;
			 sx = sx}
		| Splx.IsUnsat _ -> IsUnsat
	
	let mk : CsUser.t list -> V.t list -> mayUnsatT
		= fun cstrs vars ->
		Stat.incr ();
		Stat.incr_size (List.length cstrs);
		Debug.log DebugTypes.Title
			(lazy(Printf.sprintf "LP using Splx"));
		Debug.log DebugTypes.MInput 
			(lazy(Printf.sprintf "Constraints : %s\nVariables : %s"
				(CsUser.list_to_string cstrs)
				(Misc.list_to_string V.to_string vars " ; ")));
		mk' cstrs vars
		
	let get_solution : t -> CsUser.Vec.t
		= fun lp ->
		Splx.getAsg lp.sx
		|> Rtree.toList
		|> List.map (fun (v,c) -> 
			(CsUser.Vec.ofSymbolic c,
			Var.Positive.toPos v |> CsUser.Vec.V.fromPos))
		|> CsUser.Vec.mk
		
	let add_cstrs : CsUser.t list -> t -> mayUnsatT
		= fun cstrs lp ->
		Stat.incr_size (List.length cstrs);
		if cstrs = []
		then IsOk lp
		else begin
			Debug.log DebugTypes.Normal 
				(lazy (Printf.sprintf "Adding constraints %s"
				(CsUser.list_to_string cstrs)));
			let (mapI,cstrs,_) = List.fold_left
				(fun (map,l,i) c -> 
					let c' = userToPriv c in
					(MapI.add i c map, 
					 (i,c') :: l, 
					 i+1)
				)
				(lp.mapInt, [], MapI.cardinal lp.mapInt)
				cstrs
			in
			let res = List.fold_left
				(fun res (i,c) -> Splx.addAcc res (i,c))
				(Splx.add lp.sx (List.hd cstrs))
				(List.tl cstrs)
				|> Splx.checkFromAdd
			in 
			match	res with
			| Splx.IsOk sx -> begin
				Debug.log DebugTypes.Normal
				(lazy (Printf.sprintf "-> Problem is Sat"));
				IsOk {lp with mapInt = mapI ; sx = sx}
				end
			| Splx.IsUnsat _ -> begin
				Debug.log DebugTypes.MOutput
				(lazy (Printf.sprintf "Problem is UnSat"));
				IsUnsat
				end
		end
		
	let add_cstr : CsUser.t -> t -> mayUnsatT
		= fun cstr lp ->
		add_cstrs [cstr] lp
	
end


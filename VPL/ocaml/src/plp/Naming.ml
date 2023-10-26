module type Type = sig
	module Vec : Vector.Type
	module V = Vec.V
	
	type typT = Param | Var | Slack

	module Usr : sig
		type t = typT * V.t
		
		val equal : t -> t -> bool
	end
	
	type t

	val empty : t

	(** [equal m m'] returns true if [m] and [m'] are syntactically equal. *)
	val equal : t -> t -> bool

	(** [alloc t x m] allocates [x] in the next available slot. *)
	val alloc : typT -> V.t -> t -> t
	
	(** [allocAt t x i m] states that [x] is to be found at column
	[i] in [m].  If [x] is already allocated or if there is already
	something at this column, then [Invalid_argument] is raised.
	If there is a gap between the last allocated index and [i],
	[Invalid_argument] is raised as well. *)
	val allocAt : typT -> V.t -> int -> t -> t
	
	(** [mkVar l m] treats all the elements of [l] as variables.
	They are allocated in [m] consecutively and starting from 0.
	If variables have already been allocated in [m], the function
	raises an [Invalid_argument] exception. *)
	val mkVar : V.t list -> t -> t

	(** [mkParam l m] treats all the elements of [l] as parameters.
	They are allocated in [m] consecutively and starting from 0.
	If parameters have already been allocated in [m], the function
	raises an [Invalid_argument] exception.
	The allocation of VPL variables coincidentally happens to match
	that performed by [Context]. *)
	val mkParam : V.t list -> t -> t
	
	(** [to_index m t x] returns the column which has been assigned
	to variable or parameter (depending on [t]) [x].  If [x] is
	not assigned to anything, then [Invalid_argument] is raised. *)
	val to_index : t -> typT -> V.t -> int
	
	(** [to_user m t i] returns the user-provided variable, slack or
	parameter (depending on [t]) of the given index. *)
	val to_user : t -> typT -> int -> V.t * typT
	
	(** [to_vpl m i] returns the VPL representation of the
	parameter at index [i]. *)
	val to_vpl : t -> int -> V.t
	
	(** [vpl_max m] returns a [V.t] such that all parameters
	are assigned strictly smaller [V.t]'s. *)
	val vpl_max : t -> V.t
	
	(** [allocSlackShift x m] allocates [x] at index [0], shifting
	all the variables and slack accordingly.  If [x] is already allocated,
	[Invalid_argument] is raised. *)
	val allocSlackShift : V.t -> t -> t

	(** [freeSlackShift x m] removes slack [x] from [m] and shifts
	variables as needed.  If [x] isn't already allocated, then
	[Invalid_argument] is raised. *)
	val freeSlackShift : V.t -> t -> t
	
end

module Naming (Vec : Vector.Type) = struct
	module Vec = Vec
	module V = Vec.V
	
	type typT = Param | Var | Slack
	
	module Usr = struct
		type t = typT * V.t
		
		let compareTyp : typT -> typT -> int
			= fun t1 t2 ->
			match (t1,t2) with
			| Var, Var -> 0
			| Param, Param -> 0
			| Slack, Slack -> 0
			| Var, _ -> 1
			| Param, Var -> -1
			| Param, Slack -> 1
			| Slack, Var -> -1 
			| Slack, Param -> -1 
			
		let compare : t -> t -> int
			= fun (t1,v1) (t2,v2) ->
			let r = V.cmp v1 v2 in
			if r = 0
			then compareTyp t1 t2
			else r
			
		let equal : t -> t -> bool
			= fun (t1,u1) (t2,u2) -> u1 = u2 && t1 = t2
	
	end
	
	module UserMap = Map.Make (Usr)
	
	module PrivMap = Map.Make (struct type t = int let compare = Stdlib.compare end)
	
	type paramT = V.t
	type varT = V.t
	type slackT = V.t
	
	type t = {
		nxtIdVar : int;
		nxtIdParam : int;
		nxtParam : V.t;
	  	nxtVar : V.t;
	  	nxtSlack : V.t;
	  	usrMap : int UserMap.t;
	  	varMap : Usr.t PrivMap.t;
	  	paramMap : Usr.t PrivMap.t;
	}

	let empty : t
	  = {
	  nxtIdVar = 0;
	  nxtIdParam = 0;
	  nxtParam = V.u;
	  nxtVar = V.u;
	  nxtSlack = V.u;
	  usrMap = UserMap.empty;
	  varMap = PrivMap.empty;
	  paramMap = PrivMap.empty;
	}
	
	let equal : t -> t -> bool
		= fun m m' ->
	  	UserMap.equal (=) m.usrMap m'.usrMap
	  	&& PrivMap.equal Usr.equal m.varMap m'.varMap
	  	&& PrivMap.equal Usr.equal m.paramMap m'.paramMap
	  	&& m.nxtIdVar = m'.nxtIdVar
	 	&& m.nxtIdParam = m'.nxtIdParam
	  	&& V.equal m.nxtParam m'.nxtParam
	  	&& V.equal m.nxtVar m'.nxtVar
		&& V.equal m.nxtSlack m'.nxtSlack
	
	let new_max : V.t -> V.t -> V.t
		= fun v1 v2 ->
		if V.cmp v1 v2 > 0
		then V.next v1
		else V.next v2
	
	let alloc : typT -> V.t -> t -> t
		= let allocParam : V.t -> t -> t
			= fun x m ->
		   let id = m.nxtIdParam in
		   {m with
			usrMap = UserMap.add (Param,x) id m.usrMap;
			paramMap = PrivMap.add id (Param,x) m.paramMap;
			nxtIdParam = id+1;
			nxtParam = new_max m.nxtParam x
		   }
		in
		let allocV : V.t -> t -> t
		   = fun x m ->
		   let id = m.nxtIdVar in
		   {m with
			usrMap = UserMap.add (Var,x) id m.usrMap;
			varMap = PrivMap.add id (Var,x) m.varMap;
			nxtIdVar = id+1;
			nxtVar = new_max m.nxtVar x
		   }
		in
		let allocSlack : V.t -> t -> t
		   = fun x m ->
		   let id = m.nxtIdVar in
		   {m with
			usrMap = UserMap.add (Slack,x) id m.usrMap;
			varMap = PrivMap.add id (Slack,x) m.varMap;
			nxtIdVar = id+1;
			nxtSlack = new_max m.nxtSlack x
		   }
		in
		fun t x m -> 
		if UserMap.mem (t,x) m.usrMap
		then Stdlib.invalid_arg "Naming.alloc"
		else
		   match t with
		   | Param -> allocParam x m
		   | Var -> allocV x m
			| Slack -> allocSlack x m
	
	let allocAt : typT -> V.t -> int -> t -> t
		= fun t x i m ->
	  	if UserMap.mem (t,x) m.usrMap 
	  	 ||
			(t = Var && (PrivMap.mem i m.varMap) )
		 ||
			(t = Param && (PrivMap.mem i m.paramMap))
		 ||
			(t = Slack && (PrivMap.mem i m.varMap))
	  then Stdlib.invalid_arg "Naming.allocAt"
	  else alloc t x m

	(* il s'agit de la variable d'ajout, qui fait parti des slacks*)
	let allocSlackShift : V.t -> t -> t
		= fun x m ->
		if UserMap.mem (Slack,x) m.usrMap
		then Stdlib.invalid_arg "Naming.allocSlackShift"
		else
			{m with
		   usrMap = UserMap.mapi 
		   	(fun (t,v) i -> if t = Var || t = Slack
		   		then i+1
		   		else i)
		   	m.usrMap
				|> UserMap.add (Slack,x) 0
			;
			varMap = PrivMap.fold 
				(fun i x' -> PrivMap.add (i + 1) x') 
				m.varMap
				(PrivMap.singleton 0 (Slack,x))
			;
			nxtIdVar = m.nxtIdVar + 1
		}

	let freeSlackShift : V.t -> t -> t
		= fun x m ->
		if not (UserMap.mem (Slack,x) m.usrMap)
		then Stdlib.invalid_arg "Naming.free: does not exist"
	  	else
			let id = UserMap.find (Slack,x) m.usrMap in
			{m with
			usrMap = UserMap.mapi
				(fun (t,v) id' -> if t = Var || t = Slack && id' > id 
					then id' - 1 
					else id') 
				m.usrMap
	  			|> UserMap.remove (Slack,x)
	  		;	
			varMap = PrivMap.fold
		 		(fun i x m' ->
		 		if i = id then m'
		  		else
				if i > id then PrivMap.add (i - 1) x m'
				else PrivMap.add i x m')
		 		m.varMap PrivMap.empty
		 	;
			nxtIdVar = m.nxtIdVar - 1;
	   }
	
	let mkVar : V.t list -> t -> t
  		= fun l m ->
  		if V.cmp m.nxtVar V.u <> 0
  		then Stdlib.invalid_arg "Naming.mkVar"
  		else List.fold_left (fun m x -> alloc Var x m) m l
	
	let mkParam : V.t list -> t -> t
  		= fun l m ->
  		if V.cmp m.nxtParam V.u <> 0
  		then Stdlib.invalid_arg "Naming.mkParam"
  		else List.fold_left (fun m x -> alloc Param x m) m l

	let to_user : t -> typT -> int -> V.t * typT
  		= fun m t i ->(*
  		Printf.sprintf "to_user " ^ (match t with |Param -> "Param " |Var -> "Var ") ^ (string_of_int i)
  			|> print_endline;*)
  		match t with
  		| Var | Slack ->
     		if PrivMap.mem i m.varMap
     		then let (t,v) = PrivMap.find i m.varMap in
     			if t = Var || t = Slack then (v,t)
     			else Stdlib.failwith "Naming.to_user:var"
     		else Stdlib.invalid_arg "Naming.to_user"
  		| Param ->
     		if PrivMap.mem i m.paramMap
     		then let (t,v) = PrivMap.find i m.paramMap in
     			if t = Param then (v,t)
     			else Stdlib.failwith "Naming.to_user:param"
     		else Stdlib.invalid_arg "Naming.to_user"
     		
	let user_to_string: typT -> V.t -> string
  		= fun t u ->
  		(match t with Param -> "p" | Var -> "d" | Slack -> "s") ^ V.to_string u

	let to_string: t -> typT -> int -> string
  		= fun m t i ->
  		try 
  			let (v,t) = to_user m t i 
  			in user_to_string t v
  		with Invalid_argument _ -> "??"

	let to_index: t -> typT -> V.t -> int
  		= fun m t x ->
  		try 
  			UserMap.find (t,x) m.usrMap
  		with Not_found -> 
  			Stdlib.failwith "Naming.to_index"

(*
	let vpl_to_index : t -> V.t -> int
  		= fun m x ->
  		PrivMap.fold
    		(fun i p r ->
     		match r with
     		| Some _ as r' -> r'
     		| None -> if V.cmp x p = 0 then Some i else None)
    		m.paramMap None
  		|> function
    		| None -> Stdlib.invalid_arg "Naming.vpl_to_index"
    		| Some i -> i

	let vpl_to_user : t -> V.t -> V.t
  		= fun m x ->  PrivMap.find (vpl_to_index m x) m.paramMap

	let vpl_to_string : t -> V.t -> string
  		= fun m x -> vpl_to_user m x |> user_to_string Param
*)
	let to_vpl : t -> int -> V.t
  		= fun m i ->
  		try
  			PrivMap.find i m.paramMap
  			|> Stdlib.snd
  		with Not_found -> 
  			Stdlib.failwith "Naming.to_index" 

	let vpl_max : t -> V.t
  		= fun m -> m.nxtParam

  	let slack_max : t -> V.t
  		= fun m -> m.nxtSlack

end

(** Interface for the maps associating variables to values. *)

module type Type = sig
	type 'n t 
	
	module V : Var.Type
	
	(** Empty map. *)
	val empty : 'n t
	
	(** Returns true if the map is empty. *)
	val is_empty : 'n t -> bool
	
	(** [get z map v] returns the value associated to [v] in [map]. If there is no such binding, it returns [z]. *)
	val get: 'n -> 'n t -> V.t -> 'n
	
	(** [set z map var value] returns [map], with a binding from [var] to [value]. 
	If the implemented map is {!module:Rtree}, value [z] is placed on each intermediate node.
	This is not the case for {!module:IntMap}. *)
	val set: 'n -> 'n t -> V.t -> 'n -> 'n t
	
	(** [mk z l] builds a map from the list of association [l]. 
		Is uses {!val:set} that needs a value [z] for the implementation {!module:Rtree}. *)
	val mk: 'n -> (V.t * 'n) list -> 'n t
	
	(** [map f m] applies function [f] for each binding in [m]. *)
	val map: ('n -> 'm) -> 'n t -> 'm t
	
	val fold: (V.t -> 'a -> 'n -> 'a) -> 'a -> 'n t -> 'a
	
	(** Same as {!val:fold}, but with two maps.
	Function identity is applied when a binding is missing in one map. *)
	val fold2: (V.t -> 'a -> 'n -> 'm -> 'a) -> 'a -> 'n t -> 'm t -> 'a
	
	(** Same as {!val:fold2}, but the function uses option types. *)
	val fold2_opt: (V.t -> 'a -> 'n option -> 'm option -> 'a) -> 'a -> 'n t -> 'm t -> 'a
	
	(** [find f rt] looks for a node [n] of [rt] for which [f] returns [Some b].
	If such a node is found, the path to [n] in [rt] is returned along with the [b] returned by [f].
	If [f] returns [None] for all the nodes of [rt], the function [find] returns [None].
	The order in which [find] walks through [rt] is not specified. *)
	val find: ('a -> 'b option) -> 'a t -> (V.t * 'b) option
	
	(** Same as {!val:find} with two maps. *)
	val find2: (V.t -> 'm -> 'n -> 'b option) -> 'm t -> 'n t -> (V.t * 'b) option
	
	(** Same as {!val:find} where the given function is a predicate. *)
	val findPred: ('a -> bool) -> 'a t -> (V.t * 'a) option
	
	(** Same as {!val:find2} where the given function is a predicate. *)
	val findPred2: ('a -> 'b -> bool) -> 'a t -> 'b t -> (V.t * 'a * 'b) option
	
	val toList: 'a t -> (V.t * 'a) list
	val to_string: string -> ('a -> string -> string) -> (V.t -> string) -> 'a t -> string
			   
	(** [mskBuild pred l] builds a mask tree where a node is true
	if [pred] has returned [true] for at least one tree in [l] for that [node]. *)
	val mskBuild: ('a -> bool) -> 'a t list -> bool t
	
	(** [pathsGet m] returns the set of variables which value is [true] in map [m]. *)
	val pathsGet: bool t -> V.Set.t
	
	(** [basisBuild isNil pr l] builds a [string t] where a path leads to its associated string (provided by [pr])
if there is at least a tree in [l] which associates a non-nil coefficient (determined by [isNil]) to this path. *)
	val basisBuild: ('a -> bool) -> (V.t -> string) -> 'a t list -> string t
	
	val merge : (V.t -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t

	val merge3 : (V.t -> 'a option -> 'b option -> 'c option -> 'res option) -> 'a t -> 'b t -> 'c t -> 'res t
	
	val for_all2 : ('m option -> 'n option -> bool) -> 'm t -> 'n t -> bool
	
	(** [equal cmp m1 m2] tests whether the maps [m1] and [m2] are equal, that is, contain equal keys and associate them with equal data. @param cmp is the equality predicate used to compare the data associated with the keys. *)
	val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
	
end

module VarMap (V : Var.Type) = struct
	
	module V = V
	module M = Map.Make(struct type t = V.t let compare = V.cmp end)

	type 'n t = 'n M.t

	let empty = M.empty

	let is_empty = M.is_empty

	let equal = M.equal 

	(* XXX: est-ce mieux de faire map.mem puis map.find ou bien map.find en catchant l'exception? *)
	let get: 'n -> 'n t -> V.t -> 'n
		= fun z map v ->
		if M.mem v map
		then M.find v map
		else z

	(* To fit with Rtree's set function.*)
	let set: 'n -> 'n t -> V.t -> 'n -> 'n t
		= fun _ map v x ->
		M.add v x map

	(* To avoid the first parameter in set .*)
	let set2: 'n t -> V.t -> 'n -> 'n t
		= fun map v x ->
		M.add v x map

	let remove : V.t -> 'n t -> 'n t
		= fun v map ->
		M.remove v map
	
	let mk: 'n -> (V.t * 'n) list -> 'n t
		= fun z l ->
		List.fold_left (fun a (x, n) -> set z a x n) empty l

	let mk2: (V.t * 'n) list -> 'n t
		= fun l ->
		List.fold_left (fun a (x, n) -> set2 a x n) empty l
	
	let map: ('n -> 'm) -> 'n t -> 'm t
		= fun f map ->
		M.map f map

	let toList: 'a t -> (V.t * 'a) list
		= fun map ->
		M.bindings map
	
	let fold: (V.t -> 'a -> 'n -> 'a) -> 'a -> 'n t -> 'a
		= fun f base map ->
		M.fold (fun key elt res -> f key res elt) map base
	
	(* XXX: tester l'existence avant toList?*)
	let find: ('a -> 'b option) -> 'a t -> (V.t * 'b) option
		= fun f map ->
		try
			let (v,a) = List.find
			(fun (v,a) -> match f a with
				| None -> false
				| _ -> true)
			(toList map)
			in 
			match f a with
			| Some b -> Some (v,b)
			| None -> None
		with Not_found -> None

	let merge : (V.t -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t
		= fun f map nap ->
		M.merge f map nap
	
	(* nap et map doivent comporter les mêmes bindings*)
	let fold2_strict: ('a -> 'n -> 'm -> 'a) -> 'a -> 'n t -> 'm t -> 'a
		= fun f base nap map ->
		List.fold_left2
			(fun res (v1,n) (v2,m) ->
				if V.cmp v1 v2 <> 0
				then Stdlib.invalid_arg "M.fold2"
				else f res n m)
			base
			(toList nap) (toList map)

	let fold2: (V.t -> 'a -> 'm -> 'n -> 'a) -> 'a -> 'm t -> 'n t -> 'a
		= fun f base map nap ->
		merge
			(fun _ mopt nopt -> Some (mopt,nopt))
			map nap
		|>
		fold	
			(fun v res opt ->
				match opt with
				| (None, _) | (_, None) -> res
				| (Some m, Some n) -> f v res m n)
			base

	(* XXX: à implémenter? *)
	let fold2_opt: (V.t -> 'a -> 'm option -> 'n option -> 'a) -> 'a -> 'm t -> 'n t -> 'a
		= fun f base map nap ->
		merge
			(fun _ mopt nopt -> Some (mopt,nopt))
			map nap
		|>
		fold	
			(fun v res (mopt, nopt) -> f v res mopt nopt)
			base

	(* XXX: à corriger -> prendre en compte f_left et f_right?*)

	(*let find2 : ('m -> 'n -> 'b option) -> ('b option -> 'b option) -> ('b option -> 'b option) -> 'm t -> 'n t -> 'b option 
		= fun f f_left f_right map nap ->
		try
			let l = merge 
				(fun _ mopt nopt ->
					match mopt,nopt with
					| None,_ | _,None -> None
					| Some m, Some n -> Some (m,n))
				map nap
				|> toList
			in
			let (_,(m,n)) = List.find
				(fun (v,(m,n)) -> match f m n with
					| None -> false
					| _ -> true)
				l
			in
			match f m n with
			| Some b -> Some b
			| None -> None
		with Not_found -> None
	*)
	let find2 : (V.t -> 'm -> 'n -> 'b option) -> 'm t -> 'n t -> (V.t * 'b) option
		= fun f map nap ->
		try
			let l = merge 
				(fun _ mopt nopt ->
					match mopt,nopt with
					| None,_ | _,None -> None
					| Some m, Some n -> Some (m,n))
				map nap
				|> toList
			in
			let (v,(m,n)) = List.find
				(fun (v,(m,n)) -> match f v m n with
					| None -> false
					| _ -> true)
				l
			in
			match f v m n with
			| Some b -> Some (v,b)
			| None -> None
		
		with Not_found -> None
	
	let findPred: ('a -> bool) -> 'a t -> (V.t * 'a) option
		= fun f map ->
		try
			let (v,a) = List.find
			(fun (v,a) -> f a)
			(toList map)
			in Some (v,a)
		with Not_found -> None 


	let findPred2: ('a -> 'b -> bool) -> 'a t -> 'b t -> (V.t * 'a * 'b) option
		= fun f map nap ->
		try
			let l = merge 
				(fun _ mopt nopt ->
					match mopt,nopt with
					| None,_ | _,None -> None
					| Some m, Some n -> Some (m,n))
				map nap
				|> toList
			in
			let (v,(m,n)) = List.find
				(fun (v,(m,n)) -> f m n)
				l
			in Some (v,m,n)
		with Not_found -> None

	let to_string: string -> ('a -> string -> string) -> (V.t -> string) -> 'a t -> string
		= fun sep nodePr pathPr tree ->
		let nodeList = List.map (fun (p, a) -> nodePr a (pathPr p)) (toList tree) in
		String.concat sep (List.filter (fun s -> String.length s <> 0) nodeList)

	let mskBuild1 : ('a -> bool) -> bool t -> 'a t -> bool t
		= fun pred map_b map ->
		merge
			(fun _ bopt xopt ->
				match bopt,xopt with
				| Some true, _ -> Some true
				| _, Some x when pred x-> Some true
				| _, Some x -> Some false
				| _,_ -> None)
			map_b map

	(* XXX: GC? *)
	let mskBuild: ('a -> bool) -> 'a t list -> bool t
	= fun pred l -> List.fold_left (mskBuild1 pred) empty l

	let pathsGet: bool t -> V.Set.t
		= fun mapb ->
		M.filter (fun _ b -> b) mapb
		|> toList
		|> List.split
		|> Stdlib.fst
		|> V.Set.of_list


	let basisBuild: ('a -> bool) -> (V.t -> string) -> 'a t list -> string t
		= fun isNil pr l ->
	  let nodes = mskBuild (fun n -> not (isNil n)) l |> pathsGet in
	  V.Set.fold (fun p t -> set "#inval" t p (pr p)) nodes empty

	let equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
		= fun cmp m n ->
		M.equal cmp m n
	
	let rec for_all2 : ('m option -> 'n option -> bool) -> 'm t -> 'n t -> bool
		= fun f m n ->
		merge
			(fun _ mopt nopt -> Some (mopt, nopt))
			m n
		|>
		M.for_all (fun _ (m,n) -> f m n)
	
	(* XXX: à implémenter*)
	let merge3 : (V.t -> 'a option -> 'b option -> 'c option -> 'res option) -> 'a t -> 'b t -> 'c t -> 'res t
		= fun f r1 r2 r3 ->
		M.empty
end

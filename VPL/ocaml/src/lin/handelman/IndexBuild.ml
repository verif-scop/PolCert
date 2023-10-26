module Liste = struct

	type t = Index.Int.t list

	let (check_len : t -> bool)
		= fun il ->
		try let len = Index.Int.len (List.hd il) in
			List.for_all (fun i -> Index.Int.len i = len) il
		with Failure _ -> true

	let (to_string : t -> string)
		= fun il ->
		Misc.list_to_string Index.Int.to_string il " ; "

	let (equal : t -> t -> bool)
		= fun il1 il2 ->
		List.for_all (fun i -> List.exists (fun j -> Index.Int.compare i j = 0) il2) il1 &&
		List.for_all (fun i -> List.exists (fun j -> Index.Int.compare i j = 0) il1) il2

	(** [max il] takes a list of {!(Index.Int.t * float) option} and returns the greatest element of this list {i w.r.t} their second component. *)
	let rec (max : ((Index.Int.t * float) option) list -> (Index.Int.t * float) option)
		= fun il ->
		match il with
		| [] -> Stdlib.failwith "max : empty list"
		| [x] -> x
		| None :: tl -> max tl
		| (Some (i,f)) :: tl -> match max tl with
			| Some (i',f') -> if f < f' then Some (i',f') else Some (i,f)
			| None -> Some (i,f)

	(** [get_min dim il] returns an index [ind] such that [ind(i)] = min_j il(j)(i). *)
	let (get_min : int -> t -> Index.Int.t)
		= fun dim il ->
		List.map
			(fun i -> Misc.min Stdlib.compare (List.map (fun j -> Index.Int.get j i) il))
			(Misc.range 0 dim)
		|> Index.Int.mk

	(* Hypothesis : il <> [] *)
	let (get_next : int -> t -> Index.Int.t)
		= let rec(get_next_rec : t -> int -> Index.Int.t -> int -> (Index.Int.t * float) option)
			= fun il dim ind min_size ->
			let il' = List.filter (fun i -> Index.Int.is_pred ind i) il in
			if List.length il' < min_size
			then None
			else let ind = get_min dim il' in
				if List.length il' = min_size
				then Some (ind, Index.Int.value ind)
				else let max_ind =
					List.map
						(fun j -> get_next_rec il' dim (Index.Int.incr ind j) min_size)
						(Misc.range 0 dim)
					|> max
				in
				match max_ind with
					| None -> Some (ind, Index.Int.value ind)
					| Some (i,f) -> Some (i,f)
		in
		fun dim il ->
		if List.length il = 1
		then Index.Int.init dim
		else
		let ind = Index.Int.init dim in
			match get_next_rec il dim ind (Stdlib.max 2 ((List.length il)/2)) with
			| Some (i,f) -> i
			| None -> Stdlib.failwith "List.get_next : no next element"

    (*
	let (components : Index.Int.t -> t)
		= fun ind ->
		let dim = Index.Int.len ind in
		let (_,_,res) =
		List.fold_left
			(fun (i,init,res) v ->
				(i+1,
				 init,
				 (if v <> 0
				  then (Index.Int.set init i v) :: res
				  else res)))
			(0, Index.Int.init dim, [])
			(Index.Int.data ind)
		in
		res
        *)

    let (components : Index.Int.t -> t)
		= fun ind ->
		let dim = Index.Int.len ind in
        let init = Index.Int.init dim in
		Misc.fold_left_i
			(fun i res v ->
                if v <> 0
                then let id = Index.Int.set init i 1 in
                (List.map (fun _ -> id) (Misc.range 0 v)) @ res
                else res
            )
			[] (Index.Int.data ind)

	(** computes the list of indexes that are strictly smaller than a given one {i w.r.t} element-wise comparison *)
	let get_preds : Index.Int.t -> t
		= let rec get_preds_rec : Index.Int.t -> int -> t
			= fun ind col ->
			ind ::
			(List.concat
				(List.mapi
					(fun i _ -> if Index.Int.get ind i = 0
						then []
						else get_preds_rec (Index.Int.decr ind i) i)
					(Misc.sublist (Index.Int.data ind) 0 (col+1))
				)
			)
		in
		fun ind ->
		get_preds_rec ind (Index.Int.len ind)
		|> fun l -> Misc.pop Index.Int.equal l ind
		|> List.filter (fun i -> not (Index.Int.is_null i))

	(** [le dim max] computes the list of indexes of dimension dim whose sum of elements is <= max *)
	let (le : int -> int -> t)
		= let rec le : Index.Int.t -> int -> int -> int -> t
			= fun ind col valeur val_max->
			ind ::
			(List.concat
				(List.mapi
					(fun i _ -> if valeur = val_max
						then []
						else le (Index.Int.incr ind i) i (valeur+1) val_max)
					(Misc.sublist (Index.Int.data ind) 0 (col+1))
				)
			)
		in
		fun dim val_max ->
		le (Index.Int.init dim) dim 0 val_max
		|> List.filter (fun i -> not (Index.Int.is_null i))

end


module MapI = struct
	include Map.Make(Index.Int)
		(*
	let addList : key list -> 'a list -> 'a t -> 'a t
		= fun keys elements map ->
		List.fold_left2
			(fun map key e -> add key e map)
			map
			keys elements
	*)
	(** [addMap f keys map] adds to [map] bindings from [k] to f[k] for all [k] in [keys]. *)
	let addMap : (key -> 'a) -> key list -> 'a t -> 'a t
		= fun f keys map ->
		List.fold_left
			(fun map key -> add key (f key) map)
			map
			keys

	(** [addMapCond cond f keys map] adds to [map] bindings from [k] to f[k] for all [k] in [keys] that satisfy [cond]. *)
	let addMapCond : (key -> bool) -> (key -> 'a) -> key list -> 'a t -> 'a t
		= fun cond f keys map ->
		List.fold_left
			(fun map key -> if cond key
				then add key (f key) map
				else map)
			map
			keys

	let addMapCond' : (key -> 'a t -> bool) -> (key -> 'a) -> key list -> 'a t -> 'a t
		= fun cond f keys map ->
		List.fold_left
			(fun map key -> if cond key map
				then add key (f key) map
				else map)
			map
			keys

	let addMapCond2 : (key -> 'b -> bool) -> (key -> 'b -> 'a) -> key list -> 'b list -> 'a t -> 'a t
		= fun cond f keys elems map ->
		List.fold_left2
			(fun map key elem -> if cond key elem
				then add key (f key elem) map
				else map)
			map
			keys
			elems

	let addMapCond2' : (key -> 'a t -> bool) -> (key -> 'b -> 'a) -> key list -> 'b list -> 'a t -> 'a t
		= fun cond f keys elems map ->
		List.fold_left2
			(fun map key elem -> if cond key map
				then add key (f key elem) map
				else map)
			map
			keys
			elems
end

module Map =
	struct

	type t = Liste.t MapI.t

	let (to_string : t -> string)
		= let (to_string2 : Index.Int.t * Liste.t -> string)
			= fun (i,il) ->
			Printf.sprintf "%s -> %s" (Index.Int.to_string i) (Liste.to_string il) in
		fun m ->
		Misc.list_to_string to_string2(MapI.bindings m) "\n"

	(* Hypothesis : il <> [] *)
	let rec (compute_rec : int -> Liste.t -> t)
		= fun dim il ->
		let next_ind = Liste.get_next dim il in
		if Index.Int.is_null next_ind
		then MapI.addMapCond
			(fun i -> not (Index.Int.is_unitary i))
			Liste.components
			il MapI.empty
		else begin
			(* rem : indexes for which next_ind is a predecessor
			   keep : others *)
			let (rem,keep) = List.partition (Index.Int.is_pred next_ind) il in
			let subs = List.map (fun j -> Index.Int.sub j next_ind) rem in (* différences de rem avec next_ind*)
			let keep' =
				(if Index.Int.is_unitary next_ind then [] else [next_ind])
			  @
				(List.filter (fun i -> not (Index.Int.is_null i)) subs)
			  @
			  	keep
			in
			let map = (compute_rec dim keep') in
			MapI.addMapCond2
				(fun i sub -> not (Index.Int.is_unitary i || Index.Int.is_null sub))
				(fun _ sub -> [next_ind ; sub])
				rem subs map
		end

	let (compute : Liste.t -> t)
		= fun il ->
		if List.length il = 0
		then Stdlib.invalid_arg "IndexBuild.Map.compute : empty input list"
		else

            let dim = Index.Int.len (List.hd il) in
            Misc.rem_dupl Index.Int.equal il
            |> compute_rec dim

	(* Hypothesis : il <> [] *)
	let rec (compute_list_from_map_rec : int -> Liste.t -> t -> t)
		= fun dim il map ->
		let next_ind = Liste.get_next dim il in
		if Index.Int.is_null next_ind
		then MapI.addMapCond'
			(fun i m -> not (MapI.mem i m || Index.Int.one_coeff_nn i))
			Liste.components
			il map
		else begin
			(* rem : indexes for which next_ind is a predecessor
			   keep : others *)
			let (rem,keep) = List.partition (fun x -> Index.Int.is_pred next_ind x) il in
			let subs = (List.map (fun j -> Index.Int.sub j next_ind) rem) in
			let keep' =
				(if Index.Int.one_coeff_nn next_ind then [] else [next_ind])
			  @
			  	(List.filter (fun i -> not (Index.Int.is_null i)) subs)
			  @
			  	keep
			in
			let map' = (compute_list_from_map_rec dim keep' map) in
			MapI.addMapCond2'
				(fun i m -> not (Index.Int.one_coeff_nn i || MapI.mem i m))
				(fun _ sub -> next_ind ::
					(if Index.Int.is_null sub
					 then []
					 else [sub]))
				rem subs map'
		end

	let (compute_list_from_map : Liste.t -> t -> t)
		= fun il map ->
		if List.length il = 0
		then Stdlib.invalid_arg "IndexBuild.Map.compute_list_from_map : empty input list"
		else let dim = Index.Int.len (List.hd il) in
			compute_list_from_map_rec dim il map


	let rec (get_next : Index.Int.t -> t -> Index.Int.t)
		= fun i map ->
		let init = Index.Int.init (Index.Int.len i) in
			 (MapI.bindings map)
			|> List.map Stdlib.fst
			|> List.map (fun j -> Index.Int.sub i j)
			|> List.filter (fun j -> Index.Int.is_nonnegative j)
			|> List.map (fun j -> (j, Index.Int.value j))
			|> fun l -> if List.length l = 0
				then init
				else Misc.max (fun (j1,v1) (j2,v2) -> if v1 > v2 then -1 else 1) l (* on cherche le min des valeurs*)
				|> Stdlib.fst

	let rec (compute_from_map : Index.Int.t -> t -> (Liste.t * t))
		= fun i map ->
		try
			(MapI.find i map, map)
		with Not_found ->
			if Index.Int.one_coeff_nn i
			then ([], map)
			else
				let ind = get_next i map in
				if Index.Int.is_null ind
				then let il = Liste.components i in
					(il, MapI.add i il map)
				else let i' = Index.Int.sub i ind in
					let (_,map') = (compute_from_map ind map) in
					let il' = ind :: (if Index.Int.is_null i' then [] else [i']) in
					(il', MapI.add i il' map')

end

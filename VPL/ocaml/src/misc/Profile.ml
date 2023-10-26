(**
	This module implements a simple hand-made profiling tool.
	To use it, simply instantiate the fonctor Profile with a module D that contains a name. Example :
	module MyProfile = Profile(struct let name = "MyModuleName" end)

	The "name" variable is used to prefix the name of functions in the report.
*)

module type Type = sig
	module D : sig val name : string end

	(** Reset the whole map. *)
	val reset : unit -> unit

	(** Starts the timer for the given function name.
		@raise Already_started if that timer was already launched. *)
	val start : string -> unit

	(** Stops the timer for the given function name.
		@raise Not_started if that timer was not launched. *)
	val stop : string -> unit

	val enable : unit -> unit

	val disable : unit -> unit
end

module MapPro = Map.Make(struct type t = string let compare = String.compare end)

type element = {
	start : float option;
	time : float;
}

let e0 = {
	start = None;
	time = 0.;
}

let map : element MapPro.t ref = ref MapPro.empty

let enabled : bool ref = ref false

let enable : unit -> unit
	= fun () ->
	enabled := true

let disable : unit -> unit
	= fun () ->
	enabled := false

let reset : unit -> unit
	= fun () ->
	map := MapPro.empty

let print_map : unit -> unit
	= fun () ->
	print_endline "";
	MapPro.iter
		(fun name e -> Printf.sprintf "%s -> (%s,%s)"
			name
			(if e.start = None then "None" else "Active")
			(string_of_float e.time)
			|> print_endline)
		!map;
	print_endline ""

exception Already_started of string
exception Not_started of string

module Profile (D : sig val name : string end) = struct
	module D = D

	let enable : unit -> unit
		= fun () ->
		enabled := true

	let disable : unit -> unit
		= fun () ->
		enabled := false

	let reset : unit -> unit
		= fun () ->
		map := MapPro.empty

	(* get prefix, avoids the given name s *)
	let get_prefix : string -> string
		= fun s ->
		let (max_name, max) = MapPro.fold
			(fun name e (max_name, max) ->
				if e.start <> None && not (Misc.string_equal name s)
				then match e.start, max.start with
					| None,_ | _,None -> Stdlib.failwith "Profile.get_prefix"
					| Some e_start, Some max_start ->
						if e_start >= max_start
						then (name, e)
						else (max_name, max)
				else (max_name, max))
			!map ("", {e0 with start = Some 0.})
		in
		max_name

	let get_name_start : string -> string
		= fun name ->
		let prefix = get_prefix "" in
		if Misc.string_equal prefix ""
		then String.concat ":" [D.name ; name]
		else String.concat ":" [prefix ; D.name ; name]

	(* This is a trick to avoid putting its own name as prefix*)
	let get_name_stop : string -> string
		= fun name ->
		let prefix = get_prefix "" in
		let prefix = get_prefix prefix in
		if Misc.string_equal prefix ""
		then String.concat ":" [D.name ; name]
		else String.concat ":" [prefix ; D.name ; name]

	let start : string -> unit
		= fun name ->
		if !enabled
		then begin
			let name = get_name_start name in
			try
				let e = MapPro.find name !map in
				if e.start = None
				then
					let start_time =  Unix.gettimeofday() in
					map := MapPro.add name {e with start = Some start_time} !map
				else Stdlib.raise (Already_started name)
			with Not_found ->
				let start_time =  Unix.gettimeofday() in
				map := MapPro.add name {e0 with start = Some start_time} !map
		end

	let stop : string -> unit
		= fun name ->
		if !enabled
		then begin
			let name = get_name_stop name in
			try
				let e = MapPro.find name !map in
				match e.start with
				| None -> Stdlib.raise (Not_started name)
				| Some start_time ->
					let time' = Unix.gettimeofday() -. start_time in
					map := MapPro.add name {start = None ; time = time'+.  e.time} !map
			with Not_found -> Stdlib.raise (Not_started name)
		end

end

module Report = struct

	type result = string * float
	type t = result list

	let get_results : unit -> t
		= fun () ->
		List.map (fun (name,e) -> (name, e.time))
			(MapPro.bindings !map)

	let is_son_of : string -> string -> bool
		= fun s father ->
		let len_father = String.length father in
		String.length s >= len_father && Misc.string_equal father (String.sub s 0 len_father)

	let sort_name : t -> t
		= fun l ->
		let compare (s1,_) (s2,_) = String.compare s1 s2 in
		List.fast_sort compare l

	type tree = Node of result * tree list

	let time_to_string : float -> string
		= fun t0 ->
		string_of_float t0

	let remove_prefix : string -> string
		= fun s ->
		 let last_dot = String.rindex s ':' in
		 try
		 	let before_last_dot = String.rindex_from s (last_dot-1) ':' in
		 	Misc.substring s (before_last_dot + 1)
		 with Not_found -> s

	let result_to_string : result -> result -> string
		= fun (father_name, father_time) (name,time) ->
		Printf.sprintf "%s -> %s, %f %c"
			(remove_prefix name)
			(time_to_string time)
			(time *. 100. /. father_time) '%'

	let rec tree_to_string_rec : result -> tree -> string
		= fun father -> function
		| Node (res, t) ->
			Printf.sprintf "%s\n%s"
			(result_to_string father res)
			(String.concat "\n" (List.map (tree_to_string_rec res) t) |> Misc.add_tab 1 )

	let tree_to_string : tree -> string
		= function
		| Node (res, t) -> Printf.sprintf "%s"
			(String.concat "\n" (List.map (tree_to_string_rec res) t))

	let rec add : result -> tree -> tree * bool
		= fun (s, time) -> function
		| Node ((root,time_root), trees) as tree ->
			if is_son_of s root
			then
				let (trees', b) = List.fold_left
					(fun (trees,b) tree ->
						if b then (tree :: trees, b)
						else
							let (t',b') = add (s, time) tree in
							(t' :: trees, b || b'))
					([], false) trees
				in
				if b
				then (Node ((root,time_root), trees'), true)
				else
					let tree_son = Node ((s, time),[]) in
					(Node ((root,time_root), tree_son :: trees), true)
			else (tree, false)

	let init_tree : unit -> tree
		= fun () ->
		Node (("", 0.), [])

	let build_tree : t -> tree
		= fun l ->
		List.fold_left
			(fun tree e ->
				let (tree',b) = add e tree in
				if b then tree'
				else Stdlib.failwith "build")
			(init_tree()) l

	let sort_tree_list : tree list -> tree list
		= List.fast_sort
			(fun (Node((_,t1),_)) (Node((_,t2),_)) -> Stdlib.compare t1 t2)

	let rec sort_tree : tree -> tree
		= function
		| Node (res, trees) ->
			let trees' = List.map sort_tree trees
			|> sort_tree_list in
			Node (res, trees')

	let report : unit -> string
		= fun () ->
		get_results()
		|> sort_name
		|> build_tree
		|> sort_tree
		|> tree_to_string
end

let report = Report.report

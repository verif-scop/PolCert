let nb_message_sent : int ref = ref 0

(* TODO: mettre à jour pour les nouveaux ExplorationPoint.t *)

module Slave (Minimization : Min.Type) = struct

	include PLP.PLP(Minimization)
	
	let res_slave : t ref = ref empty
	
	let print : unit -> unit
		= fun () ->
		Printf.sprintf "current_result :\ntodo = %s"
			(Misc.list_to_string (fun (id,(_,p)) -> Vec.to_string Vec.V.to_string p) !res_slave.todo " ; ")
		|> prerr_endline
	
	let adjust_points : explorationPoint list -> explorationPoint list
		= fun points ->
		List.fold_left
			(fun res point -> match RayTracing.adjust Cone point !res_slave.regs with
				| None -> res
				| Some point -> point :: res)
			[]
			points 
	
	module Write = struct
		
		let work_to_string : unit -> string
			= fun () ->
			Printf.sprintf "todo %i"
				(List.length !res_slave.todo)
		
		(** format : 
		region
		explorationsPoints
		remaining_work*)
		let send : int -> explorationPoint list -> unit
			= fun id points ->
			nb_message_sent := !nb_message_sent + 1;
			let reg = MapV.find id !res_slave.regs in
			let params = PSplx.getParams reg.Region.sx in
			let s = Printf.sprintf "problem\nregion %i\n%s%s\n%s\n"
				id
				(Distributed.Print.region reg)
				(Distributed.Print.explorationPoints params points)
				(work_to_string())
			in
			Printf.sprintf "\nSLAVE WRITING \n%s\n\n" s
				|>	prerr_endline;
			print_string s;
			print_endline "w"
		
		let ask_for_work : unit -> unit
			= fun () ->
			prerr_endline "slave asking for work";
			print_endline "Done";
			print_endline "w"
		
	end	
	
	module FirstStep = struct
				
		let random_point : Vec.V.t list -> Vec.t
			= fun params ->
			List.map (fun v -> Scalar.Rat.mk (Random.int(1000)) (Random.int(1000)+1) |> Vec.Coeff.ofQ
				, v) 
				params
				|> Vec.mk
		
		let init : Objective.pivotStrgyT -> PSplx.t -> (explorationPoint list * Distributed.local_region_idT) option
			= fun st sx ->
			let point = random_point (PSplx.getParams sx) in
		  	match Exec.exec Cone st sx point with
		 	| None -> None
		  	| Some reg -> begin
		  		(* taken from add_region*)
		  		let id = get_id() in
				let regs = MapV.add id reg MapV.empty in
				(* XXX:  vérifier les points rendus! (voir addRegion)*)
				let todo = extract_points reg id in
				res_slave := {!res_slave with regs = regs};
				let todo' = adjust_points todo in
				Some (todo', id)
		  	end
		
		let run : string -> unit
			= fun s ->
			let sx = Distributed.Parse.sx s
				|> Distributed.Parse.to_sx
			in
			match init Objective.Bland sx with
			| None -> ()
			| Some (points, id) -> Write.send id points
	end
	
	module Read = struct
		
		let region_already_known : Region.t -> int option
			= fun reg ->
			let i = ref 0 in
			let b = MapV.exists (fun id reg' -> if Region.equal reg reg' 
				then (i := id ; true)
				else false) 
			(!res_slave.regs)
			in
			if b 
			then Some !i
			else None
		
		let replace_id : Distributed.global_region_idT -> Distributed.local_region_idT -> unit
			= fun glob_id loc_id ->
			if loc_id <> glob_id
			then begin
				let map = MapV.add glob_id (MapV.find loc_id !res_slave.regs) !res_slave.regs
				and todo = List.map 
					(fun (id,p) -> if id = loc_id
						then (glob_id,p)
						else (id,p))
					!res_slave.todo
				in				
				res_slave := {regs = map ; todo = todo}
			end
		
		let parse_problem : string -> unit
			= fun s ->
			let (_, glob_id, reg, points) = PLPParser.problem PLPLexer.token (Lexing.from_string s) 
				|> Distributed.Parse.slave
			in 
			begin
			match region_already_known reg with
			| Some loc_id -> replace_id glob_id loc_id
			| None -> ()
			end;
			let regs = MapV.add glob_id reg !res_slave.regs in
			let todo = points @ !res_slave.todo in
			res_slave := {regs = regs ; todo = todo}
		
		let parse_points : string -> unit
			= fun s -> 
			let points = PLPParser.points PLPLexer.token (Lexing.from_string s) 
			|> List.map (fun (loc_reg_id, cstr, point) -> 
				let names = (MapV.find loc_reg_id !res_slave.regs).Region.sx.PSplx.names in
				Distributed.Parse.explorationPoint names (loc_reg_id, cstr, point))
			in 
			let todo = points @ !res_slave.todo in
			res_slave := {!res_slave with todo = todo}
			
		let run : string -> unit
			= fun s ->
			if String.compare (String.sub s 0 7) "problem" = 0
			then parse_problem s
			else if String.compare (String.sub s 0 6) "points" = 0
				then parse_points s
				else failwith "PLPSlave.Read.run"
	end
	
	module Steps = struct
	
		let step : unit -> (explorationPoint list * Distributed.local_region_idT) option
			= fun () -> 
			match !res_slave.todo with
			| [] -> None
			| (id_region, (cstr, point)) :: tl ->	
				let sx = (MapV.find id_region !res_slave.regs).Region.sx in
				match Exec.exec Cone Objective.Bland sx point with
			 	| None -> None
			  	| Some reg -> begin
			  		(* taken from add_region*)
			  		let id = get_id() in
					let regs = MapV.add id reg !res_slave.regs in
					res_slave := {regs = regs ; todo = List.tl !res_slave.todo};
					let todo = 
						(if Add_Region.should_explore_again cstr reg
						then [(id_region, (cstr, point))]
						else []) 
					@ (extract_points reg id)
					in
					let todo' = adjust_points todo in
					Some (todo', id)
			  	end 
			  	
		let run : unit -> unit
			= fun () -> 
			match step() with
			| None -> ()
			| Some (points, loc_id) -> Write.send loc_id points
			
	end
	
end

module SlaveRat = struct
	include Slave (Min.Classic(Vector.Rat.Positive))	
end

(** Waits for something to be readable in stdin. *)
let read_wait : unit -> string
	= fun () ->
	(* -1 means no timeout *)
	let (_,_,_) = Unix.select [Unix.stdin] [] [] (-1.0) in
	let s = ref "" in
	try
  		while true; do
  			let s' = Stdlib.read_line() in
  			try let _ = String.index s' 'w' in
  				Stdlib.raise End_of_file
  			with Not_found -> 
  				s := !s ^ s' ^ "\n"
  		done;!s
	with End_of_file ->
		!s
;;

(** If there is something to read in stdin, read it. Otherwise, returns None. *)
let read : unit -> string option
	= fun () ->
	let (in_ch,_,_) = Unix.select [Unix.stdin] [] [] 0.00001 in
	match in_ch with 
	| [] -> None
	| _ :: _ -> begin
		let s = ref "" in
		try
	  		while true; do
	  			let s' = Stdlib.read_line() in
	  			try let _ = String.index s' 'w' in
	  				Stdlib.raise End_of_file
	  			with Not_found -> 
	  				s := !s ^ s' ^ "\n"
	  		done; Some !s
		with End_of_file -> Some !s
	end
;;

let rec more_whip : unit -> unit
	= fun () ->
	SlaveRat.print() ; 
	Printf.sprintf "nb_message_sent = %i" !nb_message_sent
		|> prerr_endline;
	match !SlaveRat.res_slave.SlaveRat.todo with
	| [] -> begin (* Plus de point à traiter. *)
		SlaveRat.Write.ask_for_work();
		let s = read_wait() in
		SlaveRat.Read.run s;
		more_whip()
		end
	| _ :: _ -> begin
		match read() with
		| None -> begin (* Rien à lire *)
			SlaveRat.Steps.run();
			more_whip()
			end
		| Some s -> begin
			SlaveRat.Read.run s;
			more_whip()
			end
		end
;;
	
let first_whip : unit -> unit
	= fun () ->
	let s = read_wait() in
	SlaveRat.FirstStep.run s;
	let s = read_wait() in
	SlaveRat.Read.run s;
	more_whip()
;;
	
first_whip();;


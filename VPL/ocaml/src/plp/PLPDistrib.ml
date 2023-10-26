module Cs = PLPCore.Cs
module EqSet = PLPCore.EqSet
module Cons = PLPCore.Cons

module Debug = DebugTypes.Debug(struct let name = "PLPDistrib" end)

module PLP(Minimization : Min.Type) = struct
	
	include PLPPlot.Plot(Minimization)
	
	type explorationPoint = int * Boundary.t
	
	(*XXX : le parsing ne fonctionne pas quand il n'y a pas de paramètres *)
	module Distributed = struct
		(*
		(** index of the process in the list of processes.*)
		type process_idT = int
		type global_region_idT = int
		type local_region_idT = int
		
		module MapId = Map.Make(struct type t = int let compare = Stdlib.compare end)
		
		(** Associates a local region id to a global region id (key). *)
		type map_process_regionT = local_region_idT MapId.t
	
		(** Associates a map_process_regionT to a process id(key). *)
		type mapIdT = map_process_regionT MapId.t
		
		(** Associates to a processus id the number of points it has left to explore. *)
		type mapWorkT = int MapId.t
		
		type t = {
			regs : mapRegs_t; (** associates global region id to regions. *)
			mapId : mapIdT;
			mapWork : mapWorkT;
			todo : explorationPoint list;
		}
		
		let empty = {
			regs = MapV.empty;
			mapId = MapId.empty;
			mapWork = MapId.empty;
			todo = []
		}
		(*
		let to_string : unit () -> string
			= fun () ->
			Printf.sprintf "Current result : \n\t%s\n\t%s\n\t%s\n\t%s"
			()
		*)
		let result : t ref = ref empty 
		
		let set_work : process_idT -> int -> unit
			= fun pr_id work ->
			result := {!result with mapWork = MapId.add pr_id work !result.mapWork}
		
		let get_work : process_idT -> int
			= fun pr_id ->
			try MapId.find pr_id !result.mapWork
			with Not_found -> 0	
			
		let add_work : process_idT -> int -> unit
			= fun pr_id work ->
			let prev_work = get_work pr_id in
			result := {!result with mapWork = MapId.add pr_id (work + prev_work) !result.mapWork}
		
		let mapWork_to_string : unit -> string
			= fun () ->
			Misc.list_to_string 
				(fun (process_id,work) -> Printf.sprintf "(%i -> %i)" process_id work) 
				(MapId.bindings !result.mapWork) " ; "
						
		(** Returns the local id of the region identified globally as [glob_id] in processus [pr_id]. *)
		let get_region_id : process_idT -> global_region_idT -> local_region_idT 
			= fun pr_id glob_id ->
			try
				let map = MapId.find pr_id !result.mapId in
				try
					MapId.find glob_id map
				with Not_found -> Stdlib.failwith "PLP.get_id : region not found"
			with Not_found -> Stdlib.failwith "PLP.get_id : process not found"
		
		(** Set the local id of the region identified globally as [glob_id] in processus [pr_id] as [loc_id]. *)
		let set_region_id : process_idT -> global_region_idT -> local_region_idT -> unit
			= fun pr_id glob_id loc_id ->
			let map = MapId.add glob_id loc_id 
				(try MapId.find pr_id !result.mapId
				with Not_found -> MapId.empty)
			in
			result := {!result with mapId = MapId.add pr_id map !result.mapId}	
			
		module Print = struct
		
			let vector : Vec.V.t list -> Vec.t -> string
				= fun params vec -> 
				String.concat " "
				(List.map 
					(fun param ->
						Vec.get vec param |> Vec.Coeff.plp_print)
				params)
		
			let paramCoeff : int -> ParamCoeff.t -> string
				= fun nParams p ->
				let lin_str = 
					if nParams = 0
					then "0"
					else String.concat " " (List.map Q.to_string p.ParamCoeff.lin)
				in 
				Printf.sprintf "%s %s"
					lin_str
					(Q.to_string p.ParamCoeff.cst)
		
			let obj : int -> Objective.t -> string
				= fun nParams obj ->
				Printf.sprintf "%s\n%s"
					(String.concat "\n" (List.map (paramCoeff nParams) obj.Objective.lin))
					((paramCoeff nParams) obj.Objective.cst)
		
			(** Format : 
			s n_vars n_params
			basis
			variables
			parameters
			obj
			m
			matrix
			*)
			let sx : PSplx.t -> string
			= fun sx ->
			let vars = List.map (fun i -> Naming.to_user sx.PSplx.names Naming.Var i |> fst)
				(Misc.range 0 (PSplx.nVars sx))
			and params = List.map (fun i -> Naming.to_user sx.PSplx.names Naming.Param i |> fst)
				(Misc.range 0 (PSplx.nParams sx) )
			in
			Printf.sprintf "simplex %i %i\n%s\n%s\n%s\n%s\nmatrix\n%s\n"
				(PSplx.nVars sx)
				(PSplx.nParams sx)
				(String.concat " " (List.map string_of_int sx.PSplx.basis))
				(String.concat " " (List.map Vec.V.plp_print vars))
				(String.concat " " (List.map Vec.V.plp_print params))
				((obj (PSplx.nParams sx)) sx.PSplx.obj)
				(String.concat "\n" (List.map 
					(fun v -> String.concat " " (List.map Q.to_string v))
					sx.PSplx.mat))
		
			let cstr : Vec.V.t list -> Cs.t -> string
				= fun params cstr ->
				let vec = Cs.get_v cstr in
				Printf.sprintf "%s %s"
				(String.concat " "
						(List.map (fun v -> Cs.Vec.get vec v |> Scalar.Rat.to_string)
							params))
				(Cs.get_c cstr |> Scalar.Rat.to_string)
			
			let boundary : Vec.V.t list -> Boundary.t -> string
				= fun params (c,point) ->
				Printf.sprintf "%s\n%s"
					(cstr params c)
					(vector params point)

			let region : Region.t -> string
				= fun reg ->
				let params = PSplx.getParams reg.Region.sx in
				match reg.Region.r with
				| [] -> Printf.sprintf "%s\n%sno boundaries\n"
					(vector params reg.Region.point)
					(sx reg.Region.sx)
				| _ :: _ -> Printf.sprintf "%s\n%sboundaries\n%s\n"
					(vector params reg.Region.point)
					(sx reg.Region.sx)
					(String.concat "\n" (List.map (boundary params) reg.Region.r))
		
			(** format : 
			p id_region
			cstr
			pointOtherSide *)
			let explorationPoint : Vec.V.t list -> explorationPoint -> string
				= fun params (id, (c, pointOtherSide)) ->
				Printf.sprintf "exp %i\n%s\n%s"
					id
					(cstr params c)
					(vector params pointOtherSide)
			
			let explorationPoints : Vec.V.t list -> explorationPoint list -> string
				= fun params points ->
				match points with
				| [] -> "no point"
				| _ :: _ ->  String.concat "\n" (List.map (explorationPoint params) points)
		end
	
		module Parse = struct
	
			let paramCoeff : Q.t list -> int -> ParamCoeff.t 
				= fun coeffs dimParam ->
				ParamCoeff.mk 
					(Misc.sublist coeffs 0 dimParam)
					(List.nth coeffs dimParam)
	
			let obj : Q.t list list -> int -> int -> Objective.t
				= fun coeffs dimVar dimParam ->
				Objective.mk
					(List.map (fun x -> paramCoeff x dimParam) (Misc.sublist coeffs 0 dimVar))
					(paramCoeff (List.nth coeffs dimVar) dimParam)
		
			
			let point :  Naming.t -> (Q.t * Q.t) list -> Vec.t
				= fun names coeffs ->
				List.mapi
					(fun i (a,b) -> let v = Vec.Coeff.add
						(Vec.Coeff.ofQ a)
						(Vec.Coeff.mulr b (Vec.Coeff.delta))
						in
						(v, Naming.to_vpl names i))
					coeffs
					|> Vec.mk
							
			let to_sx : PLPBuild.DescSx.t -> PSplx.t
				= fun d ->
				let rangeVar = Misc.range 0 d.PLPBuild.DescSx.dimVar in
				let rangeParam = Misc.range 0 d.PLPBuild.DescSx.dimParam in
				let obj = obj d.PLPBuild.DescSx.obj d.PLPBuild.DescSx.dimVar d.PLPBuild.DescSx.dimParam in
				let names = List.fold_left
					(fun names i -> 
						let v = List.nth d.PLPBuild.DescSx.vars i |> Vec.V.fromInt in
						Naming.allocAt Naming.Var v i names)
					Naming.empty
					rangeVar
				in
				let names = List.fold_left
					(fun names i -> 
						let v = List.nth d.PLPBuild.DescSx.params i |> Vec.V.fromInt in
						Naming.allocAt Naming.Param v i names)
					names
					rangeParam
				in
				{PSplx.obj=obj ; PSplx.mat = d.PLPBuild.DescSx.mat ; PSplx.basis = d.PLPBuild.DescSx.basis ; PSplx.names = names}
		
			let sx : string -> PLPBuild.DescSx.t
				= fun s ->
				try
				PLPParser.one_sx PLPLexer.token (Lexing.from_string s)
				with _ -> begin
					prerr_endline ("parsing error from string\n" ^ s);
				 	failwith "Parsing error"
					end
			
					
			let cstr : Naming.t -> Q.t list -> Cs.t
				= fun names coeffs ->
				let vec = List.map
					(fun i -> (List.nth coeffs i,	Naming.to_vpl names i))
					(Misc.range 0 ((List.length coeffs)-1)) 
				in
				let cst = List.nth coeffs ((List.length coeffs)-1)
				in
				Cs.lt vec cst
		
			let region : PLPBuild.DescReg.t -> Region.t * int
				= fun reg ->
				let sx = to_sx reg.PLPBuild.DescReg.sx in
				let pointInside = point sx.PSplx.names reg.PLPBuild.DescReg.point in
				let bnds = List.map
					(fun (cstr_coeffs,point_coeffs) -> 
						let cstr = cstr sx.PSplx.names cstr_coeffs in
						let point = point sx.PSplx.names point_coeffs in
						(cstr,point))
					reg.PLPBuild.DescReg.bnds
				in
				({Region.sx = sx ; Region.point = pointInside ; Region.r = bnds}, reg.PLPBuild.DescReg.id)
			
			let explorationPoint : Naming.t -> int * Q.t list * (Q.t * Q.t) list -> explorationPoint
				= fun names (id,c,p)  ->
				let c = cstr names c in
				let p = point names p in
				(id,(c,p)) 
				
			let slave : PLPBuild.DescSlave.t -> int * int * Region.t * explorationPoint list
				= fun slave ->
				let (reg,id) = region slave.PLPBuild.DescSlave.reg in
				let names = reg.Region.sx.PSplx.names in
				let explorationPoints = List.map (explorationPoint names) slave.PLPBuild.DescSlave.pointsToExplore in
				(slave.PLPBuild.DescSlave.remaining_work, id, reg, explorationPoints)
		end
		
		module Processes = struct
		
			type com = {
				pid : int;
				in_ch : Stdlib.in_channel;
				in_fd : Unix.file_descr;
				out_ch : Stdlib.out_channel;
				p1_exit : Unix.file_descr;
				p2_ent : Unix.file_descr} 
		
			let pipes : com list ref
				= ref []
				
			let print : unit -> unit
				= fun () ->
				Debug.log DebugTypes.Detail
					(lazy (Printf.sprintf "Processes : \n%s"
						(String.concat " ; "
							(List.map (fun com -> string_of_int com.pid) !pipes) 
						)))
			
			let close : unit -> unit
				= fun () ->
				List.iter
					(fun com -> 
						Debug.log DebugTypes.Normal
							(lazy ("Fermeture du processus " ^ (string_of_int com.pid)));
						Unix.kill com.pid Sys.sigkill;
						Stdlib.close_in com.in_ch;
						Stdlib.close_out com.out_ch;
						Unix.close com.p1_exit;
						Unix.close com.p2_ent)
					!pipes;
				pipes := []
		
		
			let obj_path : string Stdlib.ref 
				= Stdlib.ref "/home/amarecha/verasco/vpl2/"
		
			let n_processes : int Stdlib.ref
				= Stdlib.ref 1
		
			let create_process : unit -> unit
				= fun () ->
				begin
					let (p1_exit,p1_ent) = Unix.pipe() and (p2_exit,p2_ent) = Unix.pipe() in
					let in_ch = Unix.in_channel_of_descr p2_exit in
					Stdlib.set_binary_mode_in in_ch false;
					let out_ch = Unix.out_channel_of_descr p1_ent in
					Stdlib.set_binary_mode_out out_ch false;
					let pid = Unix.create_process 
						(!obj_path ^ "PLPSlave.native") 
						[|(!obj_path ^ "PLPSLave.native")|] 
						p1_exit p2_ent Unix.stderr in
					Debug.log DebugTypes.Normal
						(lazy ("Création du processus " ^ (string_of_int pid)));
					pipes := !pipes @ 
						[{pid=pid ; 
						  in_ch=in_ch ; 
						  in_fd = p2_exit; 
						  out_ch=out_ch ; 
						  p1_exit=p1_exit ; 
						  p2_ent = p2_ent}]
				end
					
			let create : unit -> unit
				= fun () -> 
				List.iter (fun _ -> create_process()) (Misc.range 0 !n_processes)
			
			let write : com -> string -> unit
				= fun com s ->
				(* écriture dans le pipe *)
				Debug.log DebugTypes.Detail
					(lazy (Printf.sprintf "Writing for slave %i message\n%s"
						com.pid s));
				(* marque de fin de communication : 'w' *)
				output_string com.out_ch (s ^ "w\n");
				Stdlib.flush com.out_ch
		
		(*
			let read : com -> string
				= fun com ->
				begin
				let s = ref "" in
				try
				  	while true; do
				  		let s' = (input_line com.in_ch) in
				  		try let _ = String.index s' 'w' in
				  			Stdlib.raise End_of_file
				  		with Not_found -> 
				  			s := !s ^ s' ^ "\n"
				  	done;!s
				with End_of_file -> begin
					let len = String.length !s in
					let truc = Stdlib.pos_in com.in_ch in
					Printf.sprintf "number of char read : %i, position : %i" len truc
						|> print_endline;
					!s
					end
				end 
			*)
			
			let read_char : Unix.file_descr -> char
				= fun fd -> 
				let by = Bytes.create 1 in
				let _ = Unix.read fd by 0 1 in
				String.get (Bytes.to_string by) 0
			
			let read : com -> string
				= fun com ->
				begin
				let s = ref "" in
				try
				  	while true; do
				  		let c = read_char com.in_fd in
				  		if c = 'w'
				  		then begin
				  			let _ = read_char com.in_fd in (* on saute le \n qui suit*)
				  			Stdlib.raise End_of_file
				  		end
				  		else s := !s ^ (String.make 1 c)
				  	done;!s
				with End_of_file -> !s
				end 
			
			let nb_message_read : int ref = ref 0
			
			type resT = 
				| AskForWork of process_idT 
				| NewRegion of process_idT * (int * local_region_idT * Region.t * explorationPoint list)
			
			let is_reading : process_idT ref = ref (-1)
			
			let treat_string  : string -> process_idT -> resT
				= fun s process_id ->
				if String.compare s "Done\n" = 0
				then begin
					Debug.log DebugTypes.Detail
						(lazy (Printf.sprintf "process %i is asking for work" process_id));
					AskForWork process_id
				end 
				else begin
					Debug.log DebugTypes.Detail
						(lazy (Printf.sprintf "received from process %i region :\n%s" process_id s));
					NewRegion 
						(process_id, 
						 PLPParser.problem PLPLexer.token (Lexing.from_string s)
						 	|> Parse.slave)
				end
				
			(* problème avec select : lorsqu'on lit sur le input_channel, comme il est bufferisé, on peut lire plus que souhaité. *)
			let rec wait_res : unit -> resT
				= fun () ->
				if !is_reading >= 0
				then begin(* was reading some input channel*)
					Debug.log DebugTypes.Detail (lazy ("Reading again from " ^ (string_of_int !is_reading)));
					let com = List.nth !pipes !is_reading in
					let s = read com in
					Debug.log DebugTypes.Detail (lazy ("Read " ^ s));
					if String.compare s "" = 0
					then begin
						is_reading := -1;
						wait_res()
					end 
					else treat_string s !is_reading
				end
				else begin	
					(* Waits for something to be readable in any input channel.
					-1 means no timeout *)
					Debug.log DebugTypes.Detail (lazy "Selecting");
					let (readables,_,_) = Unix.select 
						(List.map (fun com -> com.in_fd) !pipes)
						[] [] (-1.) in
		
					nb_message_read := !nb_message_read + 1;
				
					let readable = List.hd readables in
					let process_id = Misc.findi (fun com -> com.in_fd = readable) !pipes in
					(*is_reading := process_id;*)
					let com = List.nth !pipes process_id in
					let s = read com in
					treat_string s process_id
				end
				(*
				let process_id = 0 in
				let com = List.hd !pipes in
				let s = read com in
				*)
				
		end
		
		(** Returns a fresh id for a new region.
		Ids given by master are negative. *)
		let get_id : unit -> int
			= fun () ->
			let id = !reg_id in
			reg_id := id - 1;
			id
		
		let region_already_known : Region.t -> bool
			= fun reg ->
			MapV.exists (fun _ reg' -> Region.equal reg reg') (!result.regs)

		let add_region : process_idT -> (int * local_region_idT * Region.t * explorationPoint list) 
			-> (global_region_idT * explorationPoint list) option
			(* explorationPoints talk about the new region. Put the global id instead of the local one. *)
			= let update_explorationPoints : global_region_idT -> explorationPoint list -> explorationPoint list 
				= fun glob_id points ->
				List.map (fun (_,p) -> (glob_id, p)) points
			in
			fun sender_process_id (_, loc_id, reg, explorationPoints) ->
			let glob_id = get_id() in
			if region_already_known reg
			then begin
				Debug.log DebugTypes.Normal (lazy "Region already known");
				None
			end
			else begin
				result := {!result with regs = MapV.add glob_id reg !result.regs};
				(* Setting region ids*)
				List.iteri 
					(fun i com -> 
						if i = sender_process_id
						then set_region_id i glob_id loc_id
						else set_region_id i glob_id glob_id)
					!Processes.pipes;
				Some (glob_id, update_explorationPoints glob_id explorationPoints)
			end	 
		
		let set_explorationPoint : process_idT -> explorationPoint -> explorationPoint
			= fun process_id (glob_id, p) ->
			(get_region_id process_id glob_id, p)
		
		(** Gives the first point of todo to the process. *)
		let giveWork : process_idT -> Processes.com -> unit
			= fun pr_id com ->
			if get_work pr_id = 0 && !result.todo <> []
			then begin
				let (glob_id, p) = List.hd !result.todo in
				result := {!result with todo = List.tl !result.todo};
				set_work pr_id 1;
				let params = PSplx.getParams (MapV.find glob_id !result.regs).Region.sx in
				Printf.sprintf "points\n%s\n"
				(Print.explorationPoint params (set_explorationPoint pr_id (glob_id, p)))
				|> Processes.write com
			end 
				
		let saveWork : global_region_idT -> explorationPoint list -> unit
			= fun glob_id points ->
			result := {!result with 
				todo = !result.todo @ 
				(List.map
					(fun (loc_id, p) -> glob_id, p) 
					points)
			}
			
		(** Propagate the new region (glob_id) to every process, except the sender. *)
		let propagateRegion : global_region_idT -> process_idT -> unit
			= fun glob_id sender_process ->
			let reg = MapV.find glob_id !result.regs in
			let str : process_idT -> string
				= fun pr_id ->
				let loc_id = get_region_id pr_id glob_id in
				Printf.sprintf "problem\nregion %i\n%sno point\ntodo 0\n" (* 0 est le nombre de travail restant (inutile dans cette communication) *)
				loc_id
				(Print.region reg)
			in
			List.iteri (fun process_id' com -> 
				if process_id' <> sender_process
				then Processes.write com (str process_id'))
				!Processes.pipes
		
		let init : PSplx.t -> unit
			= fun sx ->
			let s = Print.sx sx in
			Debug.log DebugTypes.Normal
				(lazy (Printf.sprintf "Initializing with string\n%s" s));
			List.iter (fun com -> Processes.write com s) !Processes.pipes 
		
		let stop : unit -> bool
			= fun () ->
			print_endline (mapWork_to_string());
			!result.todo = []
			&&	(MapId.for_all (fun _ work -> work = 0) !result.mapWork)
			
		let distrib_work : unit -> unit
			= fun () ->
			List.iteri giveWork !Processes.pipes
		
		let asking_for_work : process_idT -> unit
			= fun process_id ->
			set_work process_id 0
				
		(* must be done at least once after initialization *)
		let rec steps : (PSplx.t -> 'c) -> (Region.t * 'c Cons.t) list option
			= fun get_cert ->
			Debug.log DebugTypes.Normal (lazy "Steps");
			begin
				match Processes.wait_res() with
				| Processes.NewRegion (process_id, slave_result) -> begin
					match add_region process_id slave_result with
					| None -> ()
					| Some (glob_id, points) -> begin
						propagateRegion glob_id process_id;
						saveWork glob_id points;
						distrib_work()
						end
					end
				| Processes.AskForWork process_id -> begin
					asking_for_work process_id;
					giveWork process_id (List.nth !Processes.pipes process_id) 
					end
			end;
			if stop()
			then get_results {regs = !result.regs ; todo = []} get_cert
			else steps get_cert
		
		let init_state : unit -> unit
			= fun () ->
			(Processes.n_processes := match !Flags.distributed_plp with
				| Some n when n > 0 -> n
				| _ -> Stdlib.invalid_arg "PLP.Distributed.init_state : incorrect number of processes");
			reg_id := -1;
			result := empty;
			Processes.nb_message_read := 0;
			Processes.close();
			Processes.is_reading := -1
		
		let run : Objective.pivotStrgyT -> PSplx.t -> (PSplx.t -> 'c) -> (Region.t * 'c Cons.t) list option
			= fun st sx get_cert ->
			init_state();
			let point = Vec.nil in
			match Init.init_sx st sx point with
			| None -> None
			| Some sx -> begin
				Processes.create();
				init sx
			end;
			let res = steps get_cert in
			Processes.close();
			Printf.sprintf "nb_message_read = %i" !Processes.nb_message_read
				|> print_endline;
			res
		*)
	end
end

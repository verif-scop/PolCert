type levelT = Title | Normal | Detail | MInput | MOutput | Sage

type color = Black | Red | Green | Yellow | Blue | Magenta | Cyan | White 

let default : unit -> unit
	= fun () ->
	let _ = Unix.system "setterm -term linux -default" in
	()

let str_color : color -> string
	= function
	| Black -> "black"
	| Red -> "red"
	| Green -> "green"
	| Yellow -> "yellow"
	| Blue -> "blue"
	| Magenta -> "magenta" 
	| Cyan -> "cyan"
	| White -> "white" 

module type Type = sig
	module D : sig val name : string end
	
	val enable : levelT list -> unit

	val print_enable : unit -> unit
	
	val print_disable : unit -> unit
	
	val disable : unit -> unit
	
	val log : levelT -> string Lazy.t -> unit
	
	val is_enabled : levelT -> bool
	
	val set_color : color -> unit
	
	val exec : 'a -> levelT -> string Lazy.t -> 'a
end

let trace : string list Stdlib.ref
  = Stdlib.ref []
	  
module Debug (D : sig val name : string end) = struct
	module D = D
	
	let color : color option ref = ref None
	
	let nb_tab : int ref = ref 0
	
	let set_color : color -> unit
		= fun c ->
		color := Some c
	
	let enabled : (levelT -> bool) Stdlib.ref
	  = Stdlib.ref (function _ -> false)

	let print_on_fly : bool Stdlib.ref
	  = Stdlib.ref false

	let is_enabled : levelT -> bool
	  = fun lvl -> !enabled lvl 

	let enable : levelT list -> unit
		= fun lvls ->
		enabled := (function 
	  	| lvl when List.mem lvl lvls -> true
	  	| _ -> false)

	let print_enable : unit -> unit
	  = fun () -> print_on_fly := true
	  
	let disable : unit -> unit
		= fun lvl ->
		enabled := (function _ -> false) 

	let print_disable : unit -> unit
	  = fun () -> print_on_fly := false
	
	let get_str_color : unit -> string
		= fun () ->
		match !color with
		| Some c -> "-fore " ^ (str_color c)
		| None -> ""
	
	let (log_normal : string Lazy.t -> unit)
		= fun s -> 
		let s' = Misc.add_tab (1 + !nb_tab) (Lazy.force s) in
		if !print_on_fly
		then begin
			let _ = Unix.system ("setterm -term linux " ^ (get_str_color())) in
			Stdlib.prerr_endline s';
			default()
		end
		else trace := s' :: !trace
		
	let (log_detail : string Lazy.t -> unit)
		= fun s -> 
		let s' = Misc.add_tab (2 + !nb_tab) (Lazy.force s) in
		if !print_on_fly
		then begin
			let _ = Unix.system ("setterm -term linux " ^ (get_str_color())) in
			Stdlib.prerr_endline s';
			default()
		end
		else trace := s' :: !trace
	
	let (log_minput : string Lazy.t -> unit)
		= fun s -> 
		nb_tab := !nb_tab + 1;
		let s' = (Lazy.force s) ^ "\n" in
		if !print_on_fly
		then begin
			let _ = Unix.system ("setterm -term linux " ^ (get_str_color()) ^ " -bold on") in
			Stdlib.prerr_endline "Module Input :";
			let _ = Unix.system ("setterm -term linux -bold off") in
			Stdlib.prerr_endline s';
			default()
		end
		else trace := ("Module Input : \n" ^ s') :: !trace
	
	let (log_moutput : string Lazy.t -> unit)
		= fun s -> 
		nb_tab := max (!nb_tab - 1) 0;
		let s' = (Lazy.force s) in
		if !print_on_fly
		then begin
			let _ = Unix.system ("setterm -term linux " ^ (get_str_color()) ^ " -bold on") in
			Stdlib.prerr_endline "\nModule Output :";
			let _ = Unix.system ("setterm -term linux -bold off") in
			Stdlib.prerr_endline (s' ^ "\n");
			default()
		end
		else trace := ("\nModule Output : \n" ^ s') :: !trace
	
	let set_title : string -> string
		= fun s ->
		let n = String.length s in
		let len = 26 in
		Printf.sprintf "\n%s\n%s %s %s\n%s"
			(String.make (n + len) '%')
			(String.make ((len/2) - 1) '%')
			s 
			(String.make ((len/2) - 1) '%')
			(String.make (n + len) '%')
			
	let (log_title : string Lazy.t -> unit)
		= fun s -> 
		let s' = set_title (Lazy.force s) in
		if !print_on_fly
		then begin
			let _ = Unix.system ("setterm -term linux " ^ (get_str_color()) ^ " -bold on") in
			Stdlib.prerr_endline s';
			default()
		end 
		else trace := s' :: !trace	
	
	let log : levelT -> string Lazy.t -> unit
		= fun lvl s -> 
		if is_enabled lvl
		then 
			match lvl with
		  	| Title -> log_title s
		  	| Normal -> log_normal s
		  	| Detail -> log_detail s
			| MInput -> log_minput s
			| MOutput -> log_moutput s
			| Sage -> log_detail s
			
	let get_trace : unit -> string list
	  = fun () -> List.rev !trace

	let reset_trace : unit -> unit
	  = fun () -> 
	  print_endline "report";
	  trace := []
	
	let exec : 'a -> levelT -> string Lazy.t -> 'a
		= fun e lvl s ->
		log lvl s;
		e
	
	let exec2 : 'a -> levelT -> ('a -> string Lazy.t) -> 'a
		= fun e lvl s ->
		log lvl (s e);
		e
		
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
end

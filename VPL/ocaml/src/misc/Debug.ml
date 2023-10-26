open DebugTypes

type t = {
	print_enable : unit -> unit;
	print_disable : unit -> unit;
	levels : levelT list;
	color : color;
	set_color : color -> unit;
	enable : levelT list -> unit;
	disable : unit -> unit;
}

let min = {
	print_enable = Min.Debug.print_enable;
	print_disable = Min.Debug.print_disable;
	levels = [Title ; MInput ; MOutput];
	color = Cyan;
	set_color = Min.Debug.set_color;
	enable = Min.Debug.enable;
	disable = Min.Debug.disable;
}

let join = {
	print_enable = Join.Debug.print_enable;
	print_disable = Join.Debug.print_disable;
	levels = [Title ; MInput ; MOutput];
	color = Magenta;
	set_color = Join.Debug.set_color;
	enable = Join.Debug.enable;
	disable = Join.Debug.disable;
}

let proj = {
	print_enable = Proj.Debug.print_enable;
	print_disable = Proj.Debug.print_disable;
	levels = [Title ; MInput ; MOutput];
	color = Magenta;
	set_color = Proj.Debug.set_color;
	enable = Proj.Debug.enable;
	disable = Proj.Debug.disable;
}

let plp = {
	print_enable = PLPCore.Debug.print_enable;
	print_disable = PLPCore.Debug.print_disable;
	levels = [Title ; MInput ; MOutput];
	color = Red;
	set_color = PLPCore.Debug.set_color;
	enable = PLPCore.Debug.enable;
	disable = PLPCore.Debug.disable;
}

let minLP = {
	print_enable = MinLP.Debug.print_enable;
	print_disable = MinLP.Debug.print_disable;
	levels = [Title ; MInput ; MOutput];
	color = Green;
	set_color = MinLP.Debug.set_color;
	enable = MinLP.Debug.enable;
	disable = MinLP.Debug.disable;
}

let handelman = {
	print_enable = Handelman.Debug.print_enable;
	print_disable = Handelman.Debug.print_disable;
	levels = [Title ; MInput ; MOutput];
	color = Magenta;
	set_color = Handelman.Debug.set_color;
	enable = Handelman.Debug.enable;
	disable = Handelman.Debug.disable;
}

let hOracles = {
	print_enable = HOtypes.Debug.print_enable;
	print_disable = HOtypes.Debug.print_disable;
	levels = [Title ; MInput ; MOutput];
	color = White;
	set_color = HOtypes.Debug.set_color;
	enable = HOtypes.Debug.enable;
	disable = HOtypes.Debug.disable;
}

let pol = {
	print_enable = Pol.Debug.print_enable;
	print_disable = Pol.Debug.print_disable;
	levels = [Title ; MInput ; MOutput];
	color = Blue;
	set_color = Pol.Debug.set_color;
	enable = Pol.Debug.enable;
	disable = Pol.Debug.disable;
}

let pSplx = {
	print_enable = PSplx.Debug.print_enable;
	print_disable = PSplx.Debug.print_disable;
	levels = [Title ; MInput ; MOutput];
	color = Yellow;
	set_color = PSplx.Debug.set_color;
	enable = PSplx.Debug.enable;
	disable = PSplx.Debug.disable;
}

let modules : t list = [min ; proj ; join ; handelman ; minLP ; hOracles ; plp ; pol ; pSplx]

let print_enable : unit -> unit
	= fun () ->
	List.iter (fun m -> m.print_enable()) modules

let print_disable : unit -> unit
	= fun () ->
	List.iter (fun m -> m.print_disable()) modules

let set_colors : unit -> unit
	= fun () ->
	List.iter (fun m -> m.set_color m.color) modules

let enable : unit -> unit
	= fun () ->
	List.iter (fun m -> m.enable m.levels) modules

let disable : unit -> unit
 = fun () ->
 	List.iter (fun m -> m.disable()) modules

let get_trace : unit -> string list
  = fun () -> List.rev !DebugTypes.trace

let reset_trace : unit -> unit
  = fun () -> DebugTypes.trace := []

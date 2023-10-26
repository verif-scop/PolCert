module DescSx= struct

		type t = {dimVar : int ;
		dimParam : int;
		basis : int list ; 
		vars : int list ;
		params : int list ;
		obj : Q.t list list;
		mat : Q.t list list}

	  let isValid : t -> bool
		 = fun d ->
		 List.length d.obj = d.dimVar + 1
		 &&
		 List.for_all (fun l -> List.length l = d.dimParam + 1) d.obj
		 &&
		 List.for_all (fun l -> List.length l = d.dimVar + 1) d.mat

	  let mkRaw : Z.t -> Z.t -> Z.t list -> Z.t list -> Z.t list -> Q.t list list -> Q.t list list -> t
		 = fun dimVar dimParam basis vars params obj mat -> 
		 {dimVar = Z.to_int dimVar; 
		 dimParam = Z.to_int dimParam;
		 basis = List.map Z.to_int basis;
		 vars = List.map Z.to_int vars;
		 params = List.map Z.to_int params;
		 obj = obj;
		 mat = mat}

	let mk : Z.t -> Z.t -> Z.t list -> Z.t list -> Z.t list -> Q.t list list -> Q.t list list -> t
		= fun dimVar dimParam basis vars params obj mat -> 
		let r = mkRaw dimVar dimParam basis vars params obj mat in
		if isValid r then r
		else Stdlib.invalid_arg "sxBuild.DescSx.mk"
end

module DescReg = struct
	
	type t = {
		id : int;
		sx : DescSx.t;
		point : (Q.t * Q.t) list;
		bnds : (Q.t list * (Q.t * Q.t) list) list
		}
	
	let isValid : t -> bool
		= fun d ->
		DescSx.isValid d.sx
		&& 
		List.for_all 
			(fun (cstr,point) -> List.length cstr = d.sx.DescSx.dimParam + 1 
				&& 
				List.length point = d.sx.DescSx.dimParam) d.bnds
		&&
		List.length d.point = d.sx.DescSx.dimParam
				
	let mkRaw : int -> (Q.t * Q.t) list -> DescSx.t -> (Q.t list * (Q.t * Q.t) list) list -> t
		= fun id point sx bnds -> 
		{id = id ; sx = sx; bnds = bnds ; point = point}

	let mk : int -> (Q.t * Q.t) list -> DescSx.t -> (Q.t list * (Q.t * Q.t) list) list -> t
		= fun id point sx bnds -> 
		let reg = mkRaw id point sx bnds in
		if isValid reg then reg
		else Stdlib.invalid_arg "sxBuild.DescReg.mk"
		
end

module DescPoints = struct
	type t = (int * Q.t list * (Q.t * Q.t) list) list
end

module DescSlave = struct
	type t = {
		reg : DescReg.t;
		pointsToExplore : (int * Q.t list * (Q.t * Q.t) list) list;
		remaining_work : int}
		
	let mk : DescReg.t -> (int * Q.t list * (Q.t * Q.t) list) list -> int -> t
		= fun reg points i ->
		{reg = reg;
		pointsToExplore = points;
		remaining_work = i} 
end

(*
module type Type = sig
	module CP = CstrPoly.Positive
	module Poly = CP.Poly

	class ['c] t : 
		object 
	
		method to_string : string
	
		method get_poly_rep : CP.t list
	
		method get_noneq_poly : CP.t list
	
		method get_vars : Poly.V.t list
	
		method get_vpl_rep : 'c Pol.t option

		method get_cstr : unit -> CP.Cs.t list
	
		method get_ineqs : unit -> CP.Cs.t list
		
		method horizon : unit -> Poly.V.t
		
		(** [is_empty] returns true iff the polyhedron is empty *)
		method is_empty : bool
	
		method mk : 'c Pol.t -> CP.t list -> Poly.V.t list -> unit
	
		method mkPol : 'c Pol.t -> unit
	
		method init : unit -> unit 
	(*
		method addM : CP.t list -> t
	*)
		method equal : 'c2 t -> bool 
	
		method isInside : Poly.Vec.t -> bool
	
		(** Syntactic check*)
		method cstrInPol : CP.Cs.t -> bool
	end
end
*)

module CP = CstrPoly.Positive
module Poly = CP.Poly
module Cert = Proj.EqSet.Cons.Cert

let get_vars : CP.t list -> Poly.V.t list
	= fun l ->
	List.map (fun cp -> Poly.get_vars cp.CP.p) l
	|> List.concat
	|> Misc.rem_dupl Poly.V.equal 

(** [add_vars vl l] returns the list of variable appearing in [vl] and in polynomial cosntraints [l]. *)	
let add_vars : Poly.V.t list -> CP.t list -> Poly.V.t list
	= fun vl l ->
	(List.map (fun cp -> Poly.get_vars cp.CP.p) l)
	|> List.concat
	|> fun l -> l @ vl
	|> Misc.rem_dupl Poly.V.equal 
	
class ['c] t = 
	object (self)
	val mutable poly_rep : CP.t list = []
	val mutable vpl_rep : 'c Pol.t option = None
	val mutable vars : Poly.V.t list = []
	
	method to_string : string
		= Misc.list_to_string CP.to_string poly_rep " ; "
		
	method get_poly_rep : CP.t list
		= poly_rep
		 
	method get_noneq_poly : CP.t list
		= List.filter (fun cp -> cp.CP.typ <> Cstr.Eq) poly_rep
	
	method get_vars : Poly.V.t list
		= vars
	
	method get_vpl_rep : 'c Pol.t option
		= vpl_rep

	method get_cstr : unit -> CP.Cs.t list
		= fun () ->
		match vpl_rep with
		| None -> []
		| Some p -> Pol.get_cstr p

	method get_ineqs : unit -> CP.Cs.t list
		= fun () ->
		match vpl_rep with
		| None -> []
		| Some p -> Pol.get_cstr_ineqs p
	
	method horizon : unit -> Poly.V.t
		= fun () ->
		Misc.max Poly.V.cmp vars
			|> Poly.V.next
			
	method is_empty : bool
		= match vpl_rep with
		| None -> true
		| _ -> false
	
	method private update : unit -> unit 
		= fun () -> 
		if self#is_empty
		then poly_rep <- [];
			vars <- [];
			
	method init : unit -> unit 
		= fun () ->
		vpl_rep <- None;
		self#update()
		
	method mkPol : 'c Pol.t -> unit
		= fun p -> 
		if self#is_empty
		then let cstrs = Pol.get_cstr p in
			vpl_rep <- Some p;
			poly_rep <- List.map CP.ofCstr cstrs;
			vars <- get_vars poly_rep

	method mk : 'c Pol.t -> CP.t list -> Poly.V.t list -> unit
		= fun vpl cl variables ->
		vpl_rep <- Some vpl;
		poly_rep <- cl;
		vars <- variables
	
	method addM : 'c Cert.t -> (CP.t * 'c) list -> 'c t
		= fun factory l ->
		let ph' = new t in
		begin
			match vpl_rep with
			| None -> ()
			| Some p ->
				let variables = add_vars vars (List.map Stdlib.fst l) in 
				let conss = List.map (fun (cp,cert) -> (CP.toCstr cp, cert)) l in
			match Pol.addM factory p conss with
				| Pol.Contrad _ -> ph'#init()
				| Pol.Added p' -> 
					let cstrs = Pol.get_cstr p'
						|> List.map CP.ofCstr in
					ph'#mk p' cstrs variables
		end; 
		ph'
	
	method equal : 'c Cert.t -> 'c2 Cert.t -> 'c2 t -> bool 
		= fun factory1 factory2 p' -> 
		match (vpl_rep,p'#get_vpl_rep) with
		| (None,None) -> true
		| (Some p1, Some p2) ->	(match (Pol.incl factory1 p1 p2, Pol.incl factory2 p2 p1) with
			| (Pol.Incl _, Pol.Incl _) -> true 
		| (_,_) -> false)
		| (_,_) -> false
	
	method isInside : Poly.Vec.t -> bool
		= fun point ->
		List.for_all 
			(fun cstr -> CP.Cs.satisfy point cstr)
			(self#get_ineqs())
		
	method cstrInPol : CP.Cs.t -> bool
		= fun cstr ->
		List.exists
			(CP.Cs.equal cstr)
			(self#get_cstr())
end

	

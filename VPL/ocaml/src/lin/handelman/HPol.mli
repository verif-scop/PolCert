module CP = CstrPoly.Positive
module Poly = CP.Poly
module Cert = Proj.EqSet.Cons.Cert

class ['c] t : object
	val mutable poly_rep : CP.t list
	val mutable vars : Poly.V.t list
	val mutable vpl_rep : 'c Pol.t option
	method addM : 'c Cert.t -> (CP.t * 'c) list -> 'c t
	method cstrInPol : CP.Cs.t -> bool
	method equal : 'c Cert.t -> 'c Cert.t -> 'c t -> bool
	method get_cstr : unit -> CP.Cs.t list
	method get_ineqs : unit -> CP.Cs.t list
	method get_noneq_poly : CP.t list
	method get_poly_rep : CP.t list
	method get_vars : Poly.V.t list
	method get_vpl_rep : 'c Pol.t option
	method horizon : unit -> Poly.V.t
	method init : unit -> unit
	method isInside : Poly.Vec.t -> bool
	method is_empty : bool
	method mk : 'c Pol.t -> CP.t list -> Poly.V.t list -> unit
	method mkPol : 'c Pol.t -> unit
	method to_string : string
	method private update : unit -> unit
end


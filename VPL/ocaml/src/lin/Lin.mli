module CP = CstrPoly.Positive

val addPolyM : 'a Pol.Cert.t -> 'a Pol.t -> CP.t list -> Factory.Unit.t Pol.t option

val addPoly : 'a Pol.Cert.t -> 'a Pol.t -> CP.t -> Factory.Unit.t Pol.t option
	

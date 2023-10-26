module CP = CstrPoly.Positive

let addPolyM' : 'a Pol.Cert.t -> 'a Pol.t -> CP.t list -> Factory.Unit.t Pol.t option
	= fun factory phPol pl ->
	if Pol.equal factory factory Pol.top phPol
	then Some (Pol.to_unit phPol)
	else match !Flags.proj with
		| Flags.Proj_PLP(Flags.Rat) -> (Handelman.Rat.Pb.run phPol pl).Handelman.Rat.Pb.ph#get_vpl_rep
		| Flags.Proj_PLP(Flags.Symbolic)-> (Handelman.Symbolic.Pb.run phPol pl).Handelman.Symbolic.Pb.ph#get_vpl_rep
		| Flags.Proj_PLP(Flags.Float) -> (Handelman.Float.Pb.run phPol pl).Handelman.Float.Pb.ph#get_vpl_rep
		| Flags.FM -> (Handelman.Rat.Pb.run phPol pl).Handelman.Rat.Pb.ph#get_vpl_rep
		| Flags.PHeuristic -> Stdlib.failwith "Lin.addPolyM"
	
	
let addPolyM : 'a Pol.Cert.t -> 'a Pol.t -> CP.t list -> Factory.Unit.t Pol.t option
	= fun factory p ->
	Heuristic.apply_proj 
		(List.map Pol.Cons.get_c (Pol.get_ineqs p)) 
		(addPolyM' factory p)

let addPoly : 'a Pol.Cert.t -> 'a Pol.t -> CP.t -> Factory.Unit.t Pol.t option
	= fun factory phPol p ->
	addPolyM factory phPol [p]
	

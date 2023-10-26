module Cs = Cstr.Rat.Positive
module Vec = Cs.Vec
module Var = Vec.V
module CP = CstrPoly.Positive
module Polynomial = CP.Poly
module Coeff = Scalar.Rat

module type Type = sig
	type t

	val factory : t Pol.Cert.t

	val mk : Pol.Cs.t -> t Pol.Cons.t

    val convert : 'c Pol.t -> t Pol.t

	val check : t Pol.t -> bool

	val equal : Pol.Cs.t -> t -> bool

    val to_string : t -> string
end

module Cstr = struct

	type t = Pol.Cs.t

	module Cert = Pol.Cert

	let factory : t Cert.t = {
		Cert.name = "Cstr";
		Cert.top = (Cs.mk Cstr.Eq [] Scalar.Rat.z);
		Cert.triv = (fun cmp n -> if
			match cmp with
			| Cstr.Le -> Scalar.Rat.le Scalar.Rat.z n
			| Cstr.Lt -> Scalar.Rat.lt Scalar.Rat.z n
			| Cstr.Eq -> Scalar.Rat.equal n Scalar.Rat.z
			then ()
			else (Printf.sprintf "triv %s %s 0"
			 	(Cstr.(match cmp with | Le -> "<=" | Lt -> "<" | Eq -> "="))
				(Scalar.Rat.to_string n)
				|> print_endline;
				Stdlib.failwith "Factory.Cstr.triv")
			;
			Cs.mk cmp [] n);
		Cert.add = Cs.add;
		Cert.mul = Cs.mulc;
		Cert.to_le = (fun c -> {c with Cs.typ = Cstr.Le});
		Cert.merge = (fun c1 c2 ->
			let c1' = {c1 with Cs.typ = Cstr.Eq}
			and c2' = {c2 with Cs.typ = Cstr.Eq} in
			if Cs.equal c1' c2'
			then c1'
			else failwith "merge");
		Cert.to_string = Cs.to_string Cs.Vec.V.to_string;
		Cert.rename = Cs.rename;
	}

	let mk : Pol.Cs.t -> t Pol.Cons.t
		= fun cs -> (cs,cs)

    let convert : 'c Pol.t -> t Pol.t
        = fun p -> {
            Pol.eqs = List.map (fun (v,(cstr,_)) -> (v,mk cstr)) p.Pol.eqs;
            Pol.ineqs = List.map (fun (cstr,_) -> mk cstr) p.Pol.ineqs;
        }

	let check : t Pol.t -> bool
		= fun p ->
		List.for_all
			(fun (c,cert) -> Cs.equal c cert)
			(Pol.get_cons p)

	let equal : Pol.Cs.t -> t -> bool
		= fun cs cert ->
		Cs.equalSyn cs cert

    let to_string = Pol.Cs.to_string Pol.Var.to_string
end

module Unit = struct

	type t = unit

	module Cert = Pol.Cert

	let factory : t Cert.t = {
		Cert.name = "Unit";
		Cert.top = ();
		Cert.triv = (fun _ _ -> ());
		Cert.add = (fun _ _ -> ());
		Cert.mul = (fun _ _ -> ());
		Cert.to_le = (fun _ -> ());
		Cert.merge = (fun _ _ -> ());
		Cert.to_string = (fun _ -> "unit");
		Cert.rename = (fun _ _ _ -> ());
	}

	let mk : Pol.Cs.t -> t Pol.Cons.t
		= fun cs -> (cs,())

    let convert : 'c Pol.t -> t Pol.t
        = fun p -> {
            Pol.eqs = List.map (fun (v,(cstr,_)) -> (v,mk cstr)) p.Pol.eqs;
            Pol.ineqs = List.map (fun (cstr,_) -> mk cstr) p.Pol.ineqs;
        }

	let check : t Pol.t -> bool
		= fun _ -> true

	let equal : Pol.Cs.t -> t -> bool
		= fun _ _ -> true

    let to_string _ = "unit"
end

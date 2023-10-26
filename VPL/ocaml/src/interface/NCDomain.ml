type cmpT = Cstr.cmpT_extended

module Cs = Cstr.Rat.Positive
module Vec = Cs.Vec
module Var = Vec.V
module CP = CstrPoly.Positive
module Polynomial = CP.Poly
module Coeff = Scalar.Rat

module CW = CWrappers

module Polyhedron (F : Factory.Type) = struct

	type t =
		| NonBot of F.t Pol.t
		| Bottom

	exception Wrong_Certificate of string

	let top = NonBot Pol.top

	let bottom = Bottom

	let is_bottom p = p = Bottom

	let to_string : (Var.t -> string) -> t -> string
		= fun varPr -> function
		| Bottom -> "bottom"
		| NonBot p ->
			if p = Pol.top then
				"top"
			else
				Pol.to_string varPr p

	let check : t -> t
		= function
		| Bottom -> Bottom
		| NonBot p as ph -> if F.check p
			then ph
			else Stdlib.failwith (Printf.sprintf "VPL has failed: wrong certificate in polyhedron %s"
				(to_string Var.to_string ph))

	let addM : t -> Cs.t list -> t
		= fun p cs ->
		match p with
		| Bottom -> p
		| NonBot p ->
			let cs' = List.map F.mk cs in
			match Pol.addM F.factory p cs' with
			| Pol.Added pol -> check (NonBot pol)
			| Pol.Contrad _ -> Bottom

	let addNLM : t -> CP.t list -> t
		= fun _ _ ->
		Stdlib.failwith "VPL.addNLM: unimplemented"

	let meet : t -> t -> t
		= fun p1 p2 ->
		match p1,p2 with
		| Bottom, _ | _, Bottom -> Bottom
		| NonBot p1', NonBot p2' ->
			match Pol.meet F.factory p1' p2' with
			| Pol.Added pol -> check (NonBot pol)
			| Pol.Contrad _ -> Bottom

	(* TODO: need Factory.equal! *)
	let join : t -> t -> t
		= fun p1 p2 ->
		match p1, p2 with
		| Bottom, Bottom -> Bottom
		| Bottom, NonBot _ -> p2
		| NonBot _, Bottom -> p1
		| NonBot p1', NonBot p2' ->
			let p' = Pol.join F.factory F.factory p1' p2'
				|> Stdlib.fst
			in
			check (NonBot p')

	(* TODO: need Factory.equal! *)
	let minkowski : t -> t -> t
		= fun p1 p2 ->
		match p1, p2 with
		| Bottom, Bottom -> Bottom
		| Bottom, NonBot _ -> p2
		| NonBot _, Bottom -> p1
		| NonBot p1', NonBot p2' ->
			let p' = Pol.minkowski F.factory F.factory p1' p2'
				|> Stdlib.fst
			in
			check (NonBot p')

	let project : t -> Var.t list -> t
		= fun p vars ->
		match p with
		| Bottom -> Bottom
		| NonBot p' ->
			let p' = Pol.projectM F.factory p' vars in
			check (NonBot p')

	let projectM = project

	let widen: t -> t -> t
		= fun p1 p2 ->
		match p1, p2 with
		| Bottom, Bottom -> Bottom
		| Bottom, NonBot _ -> p2
		| NonBot _, Bottom -> top
		| NonBot p1', NonBot p2' ->
			let p' = Pol.widen F.factory p1' p2' in
			check (NonBot p')

	(* TODO: lever une exception spécifique*)
	let check_incl : F.t list -> t -> unit
		= fun rel -> function
		| Bottom -> ()
		| NonBot p ->
			if not (Misc.list_eq2 F.equal (Pol.get_cstr p) rel)
			then Stdlib.failwith "VPL has failed: wrong certificate in inclusion"

	let incl : t -> t -> bool
		= fun p1 p2 ->
		match p1,p2 with
		| Bottom, Bottom | Bottom, NonBot _ -> true
		| NonBot _, Bottom -> false
		| NonBot p1', NonBot p2' ->
			match Pol.incl F.factory p1' p2' with
			| Pol.Incl cert -> (check_incl cert (NonBot p2');true)
			| Pol.NoIncl -> false

	let check_bound : bool -> Vec.t -> Pol.bndT * F.t option -> Pol.bndT
		= fun upper obj (bnd,cert) ->
        let error_string = if upper
            then "check_upper_bound"
            else "check_lower_bound"
        in
		match (bnd,cert) with
		| (Pol.Infty, None) -> Pol.Infty
		| (_, None)
		| (Pol.Infty, Some _) -> Stdlib.raise (Wrong_Certificate error_string)
		| (Pol.Open v, Some cert) ->
            let expected_cert = if upper
                then (Cs.mk2 Cstr.Lt obj v)
                else (Cs.mk2 Cstr.Lt (Vec.neg obj) (Scalar.Rat.neg v))
            in
			if F.equal expected_cert cert
			then Pol.Open v
			else Stdlib.raise (Wrong_Certificate
                (Printf.sprintf "%s -> cstr: %s; expected %s, got: %s"
                    error_string
                    (Pol.bnd_to_string bnd)
                    (Cs.to_string Cs.Vec.V.to_string expected_cert)
                    (F.to_string cert)))
		| (Pol.Closed v, Some cert) ->
			let expected_cert = if upper
                then (Cs.mk2 Cstr.Le obj v)
                else (Cs.mk2 Cstr.Le (Vec.neg obj) (Scalar.Rat.neg v))
            in
			if F.equal expected_cert cert
			then Pol.Closed v
			else Stdlib.raise (Wrong_Certificate
                (Printf.sprintf "%s -> cstr: %s; expected %s, got: %s"
                    error_string
                    (Pol.bnd_to_string bnd)
                    (Cs.to_string Cs.Vec.V.to_string expected_cert)
                    (F.to_string cert)))

	let getUpperBound : t -> Vec.t -> Pol.bndT option
		= fun p vec ->
		match p with
		| Bottom -> None
		| NonBot p' -> Some (Pol.getUpperBound F.factory p' vec |> check_bound true vec)

	let getLowerBound : t -> Vec.t -> Pol.bndT option
		= fun p vec ->
		match p with
		| Bottom -> None
		| NonBot p' -> Some (Pol.getLowerBound F.factory p' vec |> check_bound false vec)

	let itvize : t -> Vec.t -> Pol.itvT
		= fun p vec ->
		match p with
		| Bottom -> {Pol.low = Pol.Closed Scalar.Rat.u ; Pol.up = Pol.Closed Scalar.Rat.z}
		| NonBot p' ->
			let (itv, certLower, certUpper) = Pol.itvize F.factory p' vec in
			let itvLower = check_bound false vec (itv.Pol.low, certLower)
			and itvUpper = check_bound true vec (itv.Pol.up, certUpper) in
			{Pol.low = itvLower ; Pol.up = itvUpper}

	let get_cstr = function
		| Bottom -> []
		| NonBot p -> Pol.get_cstr p

	let rename : Var.t -> Var.t -> t -> t
		= fun fromX toY -> function
		| Bottom -> Bottom
		| NonBot p ->
			NonBot (Pol.rename F.factory fromX toY p)

	type rep = unit Pol.t

  	let backend_rep : t -> rep option
  		= fun p ->
  		match p with
  		| Bottom -> None
  		| NonBot p ->
  			let eqs = List.map (fun (v, (c,_)) -> (v, (c,()))) p.Pol.eqs
  			and ineqs = List.map (fun (c,_) -> (c,())) p.Pol.ineqs
  			in Some {Pol.eqs = eqs ; Pol.ineqs = ineqs}

	let mapi : bool -> (int -> Pol.Cs.t -> Pol.Cs.t) -> (int -> Pol.Cs.t -> Pol.Cs.t) -> t -> t
		= fun _ f1 f2 ->
		function
		| Bottom -> Bottom
		| NonBot pol ->
			let eqs = Pol.get_eqs pol
			and ineqs = Pol.get_ineqs pol in
			NonBot {
				Pol.eqs = List.mapi (fun i (v,(cstr,_)) -> (v, F.mk (f1 i cstr))) eqs;
				Pol.ineqs = List.mapi (fun i (cstr,_) -> F.mk (f2 i cstr)) ineqs
			}
end

let translate_cstr : Cs.t -> Vec.t -> Cs.t
	= fun cstr vec ->
	let v = Cs.get_v cstr in
	let l = Vec.toList v in
	let (var,coeff) = List.hd l in
	let m = Scalar.Rat.div (Cs.get_c cstr) coeff
		|> Vec.set Vec.nil var
	in
	let m' = Vec.add vec m in
	let cste = Vec.dot_product m' v in
	{cstr with Cs.c = cste}

(** High level domain with ocaml verification of certificates. *)
module NCVPL_Cstr = struct
	module P = struct
		include Polyhedron (Factory.Cstr)

		let translate : t -> Vec.t -> t
			= fun pol vec ->
			match pol with
			| Bottom -> Bottom
			| NonBot pol ->
				let eqs = Pol.get_eqs pol in
				let ineqs = Pol.get_ineqs pol in
				NonBot {
					Pol.eqs = List.map
						(fun (v,(cstr, cert)) -> (v, (translate_cstr cstr vec, translate_cstr cert vec)))
						eqs;
					Pol.ineqs = List.map
						(fun (cstr, cert) -> (translate_cstr cstr vec, translate_cstr cert vec))
						ineqs;
				}

		(** Careful : addNLM is UNcertified. *)
		let addNLM : t -> CP.t list -> t
			= fun p cps ->
			match p with
			| Bottom -> Bottom
			| NonBot pol -> match Lin.addPolyM Factory.Cstr.factory pol cps with
				| None -> Bottom
				| Some pol' -> NonBot {
					Pol.eqs = List.map
						(fun (var, (cstr, _)) -> (var, Factory.Cstr.mk cstr))
						(Pol.get_eqs pol');
					Pol.ineqs = List.map
						(fun (cstr, _) -> Factory.Cstr.mk cstr)
						(Pol.get_ineqs pol');
					}

	end
	module I = NCInterface.Interface (P)
	module I_Q = I.QInterface
	module Q = CW.MakeHighLevel (I_Q)

	module I_Z = I.ZInterface
	module Z = CW.MakeZ (I_Z)
end

(** High level domain with NO certificates. *)
module NCVPL_Unit = struct
	module P = struct
		include Polyhedron (Factory.Unit)

		let translate : t -> Vec.t -> t
			= fun pol vec ->
			match pol with
			| Bottom -> Bottom
			| NonBot pol ->
				NonBot {
					Pol.eqs = List.map
						(fun (v,(cstr, cert)) -> (v, (translate_cstr cstr vec, cert)))
						(Pol.get_eqs pol);
					Pol.ineqs = List.map
						(fun (cstr, cert) -> (translate_cstr cstr vec, cert))
						(Pol.get_ineqs pol);
				}

		let addNLM : t -> CP.t list -> t
			= fun p cps ->
			match p with
			| Bottom -> Bottom
			| NonBot pol -> match Lin.addPolyM Factory.Unit.factory pol cps with
				| None -> Bottom
				| Some pol' -> NonBot pol'

	end
	module I = NCInterface.Interface (P)
	module I_Q = I.QInterface
	module Q = CW.MakeHighLevel (I_Q)

	module I_Z = I.ZInterface
	module Z = CW.MakeZ (I_Z)
end

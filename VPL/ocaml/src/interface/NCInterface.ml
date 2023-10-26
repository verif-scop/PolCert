type cmpT = Cstr.cmpT_extended

module Cs = Cstr.Rat.Positive
module Vec = Cs.Vec
module Var = Vec.V
module CP = CstrPoly.Positive
module Polynomial = CP.Poly

module CW = CWrappers

module type Polyhedron_Type = sig

	type t

	exception Wrong_Certificate of string

	val top : t
	val bottom : t
	val is_bottom : t -> bool
	val addM : t -> Cs.t list -> t
	val addNLM : t -> CP.t list -> t
	val meet : t -> t -> t
	val join : t -> t -> t
	val minkowski : t -> t -> t
	val project : t -> Var.t list -> t
	val projectM : t -> Var.t list -> t
	val widen : t -> t -> t
	val incl : t -> t -> bool
	val to_string : (Var.t -> string) -> t -> string
	val getUpperBound : t -> Vec.t -> Pol.bndT option
	val getLowerBound : t -> Vec.t -> Pol.bndT option
	val itvize : t -> Vec.t -> Pol.itvT

   type rep = unit Pol.t
	val backend_rep : t -> rep option
	val rename : Var.t -> Var.t -> t -> t

	(* Non certifed functions: *)
	val translate : t -> Vec.t -> t
	val mapi : bool -> (int -> Pol.Cs.t -> Pol.Cs.t) -> (int -> Pol.Cs.t -> Pol.Cs.t) -> t -> t
end

module Interface (P : Polyhedron_Type)  = struct

	module Interface (Term: CW.TermType) = struct
		module Interval = struct

			type bndT = Pol.bndT

			type t = Pol.itvT

			let top = {Pol.low = Pol.Infty ; Pol.up = Pol.Infty}

			let is_top : t -> bool
				= fun itv ->
				match itv.Pol.low, itv.Pol.up with
				| Pol.Infty, Pol.Infty -> true
				| _,_ -> false

			let mk : bndT -> bndT -> t
				= fun low up ->
				{Pol.low = low ; Pol.up = up}
		end

		include P

		let project: Var.t list -> t -> t
			= fun vars p ->
			P.project p vars

		let projectM: Var.t list -> t -> t
			= fun vars p ->
			P.projectM p vars

		let partition_affine : (cmpT * Term.t) list -> Cs.t list * CP.t list
			= fun l ->
			List.map Term.to_cp l
			|> CP.partition_affine

		let assume: (cmpT * Term.t) list -> t -> t
			= fun cstrs p ->
			let (affs, polys) = partition_affine cstrs
			in
			let p' = P.addM p affs in
			if is_bottom p'
			then p'
			else if polys = []
				then p'
				else P.addNLM p' polys

		let to_string : (Var.t -> string) -> t -> string
			= fun varPr p ->
			if p = P.top
			then "top"
			else P.to_string varPr p

		let leq : t -> t -> bool = P.incl

		let extract_vec : Term.t -> Vec.t option
			= fun term ->
			let p = Term.to_poly term in
			if Polynomial.is_affine p
			then Some (Polynomial.toCstr p
				|> Stdlib.fst)
			else None

		let getUpperBound : t -> Term.t -> Pol.bndT option
			= fun pol term ->
			match extract_vec term with
			| None -> Stdlib.invalid_arg "getUpperBound : nonlinear expression"
			| Some vec -> P.getUpperBound pol vec

		let getLowerBound : t -> Term.t -> Pol.bndT option
			= fun pol term ->
			match extract_vec term with
			| None -> Stdlib.invalid_arg "getLowerBound : nonlinear expression"
			| Some vec -> P.getLowerBound pol vec

		let itvize : t -> Term.t -> Pol.itvT
			= fun pol term ->
			match extract_vec term with
			| None -> Stdlib.invalid_arg "itvize : nonlinear expression"
			| Some vec -> P.itvize pol vec

		let backend_rep : t -> (rep * ((ProgVar.PVar.t -> ProgVar.PVar.t) * (ProgVar.PVar.t -> ProgVar.PVar.t))) option
  			= fun p ->
  			match P.backend_rep p with
  			| Some p -> Some (p, ((fun x -> x), (fun x -> x)))
  			| None -> None
	end

	module QInterface = struct
		module Term = CW.QInterface.Term

		include Interface(Term)
	end

	module ZInterface = struct
		module Term = CW.QAffTerm

		include Interface(Term)
	end
end

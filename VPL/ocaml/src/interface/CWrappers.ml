(** This file provides wrappers of the coq certified domains
    as interfaces of "VPLInterface2"
*)

(* NB: ci-dessous, je = Sylvain !

Je ne vois pas bien comment rentrer dans le moule de "VPLInterface2".

J'essaie de proposer qqchose d'analogue, en modifiant ce qui me gène.
But: lifter les modules "FullDom"
        de "src/coq/extract/PedraQ"
     et de "src/coq/extract/PedraZ"
*)

module Var = Var.Positive
  (* type des variables: pour l'utilisateur du "int" serait plus simple ? *)

module Annot = struct
    (* type des annotations possibles: à compléter ! *)
  	type t =
	| Old (* used in assign / guassign *)
	| Unused (* a default unused case representing future annotations *)

	let to_string : t -> string
  		= function
  		| Old -> "Old"
  		| Unused -> "Unused"
end

type cmpT = Cstr.cmpT_extended

type binl = AND | OR

let binl_to_string = function
	| AND -> Symbols.s_and
	| OR -> Symbols.s_or

module CP = CstrPoly.Positive
module Polynomial = CP.Poly

module type TermType = sig
  type t

  val to_string : (Var.t -> string) -> t -> string

  val to_poly : t -> Polynomial.t

  val to_cp : cmpT * t -> CP.t
end

module type LowLevelDomain = sig

  module Term : TermType

  type t

  val top: t

  val bottom: t

  val is_bottom: t -> bool

  (* atomic assume *)
  val assume: (cmpT * Term.t) list -> t -> t

  val meet : t -> t -> t

  val join: t -> t -> t

  val minkowski : t -> t -> t

  val project: Var.t list -> t -> t

  val widen: t -> t -> t

  val rename: Var.t -> Var.t -> t -> t

  (** Test the inclusion of two polyhedra. *)
  val leq: t -> t -> bool

  val to_string: (Var.t -> string) -> t -> string

  val getUpperBound : t -> Term.t -> Pol.bndT option

  val getLowerBound : t -> Term.t -> Pol.bndT option

  val itvize : t -> Term.t -> Pol.itvT

  type rep = PedraQOracles.t
  val backend_rep : t -> (rep * ((ProgVar.PVar.t -> ProgVar.PVar.t) * (ProgVar.PVar.t -> ProgVar.PVar.t))) option

  (** Uncertified functions : *)
  (** [translate pol dir] translates polyhedron [pol] in direction [dir]. *)
  val translate : t -> Pol.Cs.Vec.t -> t

  (** [mapi b f1 f2 pol] applies function [f1] to each equation and [f2] to each inequation of [pol].
  Boolean [b] has no effect here. It is used in the high-level version of [mapi]. *)
  val mapi : bool -> (int -> Pol.Cs.t -> Pol.Cs.t) -> (int -> Pol.Cs.t -> Pol.Cs.t) -> t -> t

  (** Projection of several variables at the same time. *)
  val projectM: Var.t list -> t -> t
end

module Interface (Coeff: Scalar.Type) = struct

	module Term = struct
	(* copié de VPLInterface2 *)

		type t =
		| Var of Var.t
		| Cte of Coeff.t
		| Add of t * t
		| Sum of t list
		| Opp of t
		| Mul of t * t
		| Prod of t list
		(* | Poly of Polynomial.t *)
		| Annot of Annot.t * t

		let rec to_poly : t -> Polynomial.t
			= function
			| Var x -> Polynomial.fromVar x
			| Cte c -> Polynomial.cste (Coeff.toQ c)
			| Add  (p1,p2) -> Polynomial.add (to_poly p1) (to_poly p2)
			| Sum l -> Polynomial.sum (List.map to_poly l)
			| Opp p -> Polynomial.neg (to_poly p)
			| Mul (p1,p2) -> Polynomial.mul (to_poly p1) (to_poly p2)
			| Prod l -> Polynomial.prod (List.map to_poly l)
			(*| Poly p -> p*)
			| Annot (_,p) -> to_poly p

		let to_cp : cmpT * t -> CP.t
			= fun (cmp,t) ->
			let p = to_poly t in
			let (cmp',p') =
			Cstr.(match cmp with
			| EQ -> (Eq, p)
			| LE -> (Le, Polynomial.neg p)
			| LT -> (Lt, Polynomial.neg p)
			| GE -> (Le, p)
			| GT -> (Lt, p)
			| NEQ -> Stdlib.failwith "VPLInterface.Term.to_cp: NEQ unimplemented")
			in
			CP.mk cmp' p'

		let rec to_string : (Var.t -> string) -> t -> string
			= fun varPr -> function
			| Var v -> varPr v
			| Cte c -> Coeff.to_string c
			| Add (t1,t2) -> Printf.sprintf "%s + %s" (to_string varPr t1) (to_string varPr t2)
			| Sum l -> String.concat " + " (List.map (to_string varPr) l)
			| Opp t -> Printf.sprintf "-(%s)" (to_string varPr t)
			| Mul (t1,t2) ->  Printf.sprintf "(%s) * (%s)" (to_string varPr t1) (to_string varPr t2)
			| Prod l -> String.concat " * " (List.map (fun t -> Printf.sprintf "(%s)" (to_string varPr t)) l)
			| Annot (annot,t) -> Printf.sprintf "%s (%s)" (Annot.to_string annot) (to_string varPr t)

		let of_cstr : Pol.Cs.t -> t
			= fun cstr ->
			let l = Pol.Cs.get_v cstr
				|> Pol.Cs.Vec.toList
				|> List.map (fun (var,coeff) -> Mul (Var var, Cte (Coeff.ofQ coeff)))
			and c = Pol.Cs.get_c cstr |> Pol.Cs.Vec.Coeff.neg |> fun c -> Cte (Coeff.ofQ c)
			in
			Sum (c::l)
	end

  module Cond =
  struct

    type t =
      | Basic of bool
      | Atom of Term.t * cmpT * Term.t
      | BinL of t * binl * t
      | Not of t

    let rec to_string : (Var.t -> string) -> t -> string
    	= fun varPr -> function
      | Basic b -> string_of_bool b
      | Atom (t1,cmp,t2) -> Printf.sprintf "%s %s %s"
      	(Term.to_string varPr t1) (Cstr.cmpT_extended_to_string cmp) (Term.to_string varPr t2)
      | BinL (c1, bin, c2) -> Printf.sprintf "(%s %s %s)"
      	(to_string varPr c1) (binl_to_string bin) (to_string varPr c2)
      | Not c -> Printf.sprintf "%s (%s)" Symbols.s_not (to_string varPr c)

    let of_cstrs : Pol.Cs.t list -> t
		= fun cstrs ->
		List.map Term.of_cstr cstrs
		|> List.fold_left
			(fun cond term -> let atom = Atom (term, Cstr.LE, Term.Cte Coeff.z) in
				BinL (cond, AND, atom))
			(Basic true)
  end

  (* je coupe "Type" en 2 (avec renommage en Domain) *)

  module type LowLevelDomain = LowLevelDomain with module Term = Term

  module type HighLevelDomain =
  sig

    include LowLevelDomain

    val assume: Cond.t -> t -> t

    val asserts: Cond.t -> t -> bool

    val assign: (Var.t * Term.t) list -> t -> t

    val guassign: (Var.t list) -> Cond.t -> t -> t

  end

end

(* translation of basic datatypes *)
let import_certvar: Var.t -> ProgVar.PVar.t
= PedraQOracles.varToProgVar
let export_certvar: ProgVar.PVar.t -> Var.t
= PedraQOracles.progVarToVar

module CQNum = NumC.QNum
module CZNum = NumC.ZNum

let import_Q: Scalar.Rat.t -> CQNum.t
= PedraQOracles.nToNumC

let import_Z: Scalar.RelInt.t -> CZNum.t
= PedraQOracles.zToCoqZ

let export_Q: CQNum.t -> Scalar.Rat.t
= PedraQOracles.nToNb

let export_Z_as_Q: CZNum.t -> Scalar.Rat.t
= fun z -> Scalar.RelInt.toQ (PedraQOracles.coqZToZ z)

module CAnnot = ASTerm.TopLevelAnnot

let import_annot: Annot.t -> CAnnot.t option
  = function
  | Annot.Old -> Some (CAnnot.OLD)
  | _ -> None

let export_annot: CAnnot.t -> Annot.t option
  = function
  | CAnnot.OLD -> Some (Annot.Old)
  | _ -> None

module QItv = Itv.QItv

let import_QbndT: Pol.bndT -> QItv.bndT =
  function
  | Pol.Infty -> QItv.Infty
  | Pol.Open b -> QItv.Open (import_Q b)
  | Pol.Closed b -> QItv.Closed (import_Q b)

let export_QbndT: QItv.bndT -> Pol.bndT =
  function
  | QItv.Infty -> Pol.Infty
  | QItv.Open b -> Pol.Open (export_Q b)
  | QItv.Closed b -> Pol.Closed (export_Q b)

module ZItv = ZNoneItv.ZNItv
module Zbnd = ZNone.ZN

let export_ZbndT: Zbnd.t -> Pol.bndT =
  function
  | None -> Pol.Infty
  | Some b -> Pol.Closed (export_Z_as_Q b)

(* translation of a sequence of a binary assocative operation
   into a well-balanced tree (with minimal height)
*)
let rec balance_bin_assoc (zero: 'a) (bin: 'a -> 'a -> 'a) (l: 'a list) (acc: 'a list): 'a
    = match l with
    | [] ->
       (match acc with
       | [] -> zero
       | [x] -> x
       | x::y::l -> balance_bin_assoc zero bin l [bin x y])
    | [x] -> balance_bin_assoc zero bin [] (x::acc)
    | x::y::l -> balance_bin_assoc zero bin l ((bin x y)::acc)

let import_bin_assoc (f: 'a -> 'b) (zero: 'b) (bin: 'b -> 'b -> 'b) (l: 'a list): 'b
   = balance_bin_assoc zero bin (List.map f l) []

(* translation of cmpT *)
let import_cmpT (f: 'a -> 'b) (t1: 'a) (c:cmpT) (t2:'a): 'b * NumC.cmpG * 'b
  = let t1 = f t1 in
    let t2 = f t2 in
    match c with
    | Cstr.EQ -> (t1, NumC.Eq, t2)
    | Cstr.NEQ -> (t1, NumC.Neq, t2)
    | Cstr.LE -> (t1, NumC.Le, t2)
    | Cstr.LT -> (t1, NumC.Lt, t2)
    | Cstr.GE -> (t2, NumC.Le, t1)
    | Cstr.GT -> (t2, NumC.Lt, t1)

let export_cmpT (c: NumC.cmpG): cmpT
  = match c with
    | NumC.Eq -> Cstr.EQ
    | NumC.Neq -> Cstr.NEQ
    | NumC.Le -> Cstr.LE
    | NumC.Lt -> Cstr.LT

let export_s_cmpT (c: NumC.cmpT): cmpT
  = match c with
    | NumC.EqT -> Cstr.EQ
    | NumC.LeT -> Cstr.LE
    | NumC.LtT -> Cstr.LT

(********************)
(* translation on Q *)
(********************)

module QInterface = Interface(Scalar.Rat)
module QTerm = QInterface.Term
module QCond = QInterface.Cond
module CQCond = ASCond.QCond
module CQTerm = CQCond.Term

let rec import_QTerm: QTerm.t -> CQTerm.t
  = function
  | QTerm.Var x -> CQTerm.Var (import_certvar x)
  | QTerm.Cte c -> CQTerm.Cte (import_Q c)
  | QTerm.Add (t1, t2) -> CQTerm.Add (import_QTerm t1, import_QTerm t2)
  | QTerm.Sum l -> import_bin_assoc import_QTerm (CQTerm.Cte CQNum.z) (fun t1 t2 -> CQTerm.Add (t1,t2)) l
  | QTerm.Opp t -> CQTerm.Opp (import_QTerm t)
  | QTerm.Mul (t1, t2) -> CQTerm.Mul (import_QTerm t1, import_QTerm t2)
  | QTerm.Prod l -> import_bin_assoc import_QTerm (CQTerm.Cte CQNum.u) (fun t1 t2 -> CQTerm.Mul (t1,t2)) l
  | QTerm.Annot (a, t) ->
     (match import_annot a with
     | Some a -> CQTerm.Annot (a, import_QTerm t)
     | None -> (* Skip annotation *) import_QTerm t)

let rec export_QTerm: CQTerm.t -> QTerm.t
  = function
  | CQTerm.Var x -> QTerm.Var (export_certvar x)
  | CQTerm.Cte c -> QTerm.Cte (export_Q c)
  | CQTerm.Add (t1, t2) -> QTerm.Add (export_QTerm t1, export_QTerm t2)
  | CQTerm.Opp t -> QTerm.Opp (export_QTerm t)
  | CQTerm.Mul (t1, t2) -> QTerm.Mul (export_QTerm t1, export_QTerm t2)
  | CQTerm.Annot (a, t) ->
     (match export_annot a with
     | Some a -> QTerm.Annot (a, export_QTerm t)
     | None -> (* Skip annotation *) export_QTerm t)

let rec import_QCond: QCond.t -> CQCond.t
  = function
  | QCond.Basic b -> CQCond.Basic b
  | QCond.Atom (t1,c,t2) -> let (t1,c,t2) = import_cmpT import_QTerm t1 c t2 in
                            CQCond.Atom (c, t1, t2)
  | QCond.BinL (c1, AND, c2) -> CQCond.BinL (ASCond.AND, import_QCond c1, import_QCond c2)
  | QCond.BinL (c1, OR, c2) -> CQCond.BinL (ASCond.OR, import_QCond c1, import_QCond c2)
  | QCond.Not c -> CQCond.Not (import_QCond c)


(*************************************************************)
(*                  LowLevel -> HighLevel                    *)
(*************************************************************)
module MakeHighLevel (LHD: QInterface.LowLevelDomain) : QInterface.HighLevelDomain with type rep = LHD.rep = struct

  open DomainInterfaces

  module QAtomicCond = ASAtomicCond.QAtomicCond

  module AtomicD = struct

    include LHD

    let isBottom = is_bottom

    let isIncl = leq

    let project p x =  project [export_certvar x] p

    let assume c = assume [export_cmpT c.QAtomicCond.cmpOp, export_QTerm c.QAtomicCond.right]

	let getItvMode mo t p =
		match mo with
		| BOTH ->
			let itv = itvize p (export_QTerm t) in
			{ QItv.lower = import_QbndT itv.Pol.low ;
			QItv.upper = import_QbndT itv.Pol.up }
		| UP -> begin
			match getUpperBound p (export_QTerm t) with
			| Some bound -> {
				QItv.lower = QItv.Infty ;
				QItv.upper = import_QbndT bound}
			| None -> failwith "empty"
			end
		| LOW -> begin
			match getLowerBound p (export_QTerm t) with
			| Some bound -> {
				QItv.lower = import_QbndT bound  ;
				QItv.upper = QItv.Infty}
			| None -> failwith "empty"
 			end

    let rename x y = rename (export_certvar x) (export_certvar y)

    let pr p = CoqPr.stringTr (to_string Var.to_string p)

    let to_string f p = CoqPr.stringTr (to_string (fun x -> CoqPr.charListTr (f (import_certvar x))) p)

  end

  module FullDom = DomainFunctors.MakeFull(CQNum)(CQCond)(QItv)(QAtomicCond)(AtomicD)(AtomicD)(AtomicD)(AtomicD)(AtomicD)

    (* BELOW = a copy-paste from PedraQWrapper *)
  let not_yet_implemented s =
    raise (CertcheckerConfig.CertCheckerFailure (Debugging.NYI, s ^ " on Q"))

  include FullDom

  module Term = QInterface.Term

  let auto_lifting : (LHD.t -> LHD.t) -> t -> t
    = fun f poly ->
    {poly with pol = f poly.pol}

  let minkowski p1 p2 =
    {p1 with pol = LHD.minkowski p1.pol p2.pol}

  let translate pol vec =
  match backend_rep pol with
  | None -> Stdlib.failwith "translate"
  | Some (p,(ofVar,toVar)) ->
    let (_,ofVar',_) = PedraQOracles.export_backend_rep (p,(ofVar,toVar)) in
    let vec' = Vector.Rat.Positive.toList vec
      |> List.map (fun (v,c) -> c, (ofVar' v))
      |> Vector.Rat.Positive.mk
    in
    auto_lifting (fun p -> LHD.translate p vec') pol

  let projectM vars pol =
  match backend_rep pol with
  | None -> Stdlib.failwith "translate"
  | Some (p,(ofVar,toVar)) ->
    let (_,ofVar',_) = PedraQOracles.export_backend_rep (p,(ofVar,toVar)) in
    let vars' = List.map ofVar' vars in
  	{pol with pol = LHD.projectM vars' pol.pol}

  let mapi b f1 f2 pol =
  match backend_rep pol with
  | None -> Stdlib.failwith "map"
  | Some (p,(ofVar,toVar)) ->
  	 if b
  	 then let (_,ofVar',toVar') = PedraQOracles.export_backend_rep (p,(ofVar,toVar)) in
		 let f' : (int -> Pol.Cs.t -> Pol.Cs.t) -> int -> Pol.Cs.t -> Pol.Cs.t
		 	= fun f i cstr ->
		 	Pol.Cs.rename_f toVar' cstr
		 	|> f i
		 	|> Pol.Cs.rename_f ofVar'
		 in
    	 auto_lifting (fun p -> LHD.mapi false (f' f1) (f' f2) p) pol
    else
    	 auto_lifting (fun p -> LHD.mapi false f1 f2 p) pol

  let is_bottom = isBottom

  let assume c p =
    assume (import_QCond c) p

  let asserts c p =
    coq_assert (import_QCond c) p

  let rename x y = rename (import_certvar x) (import_certvar y)

  let assign l p =
    match l with
    | [] -> p
    | [(x, t)] -> FullDom.assign (import_certvar x) (import_QTerm t) p
    | _ -> not_yet_implemented "assign"

  let guassign l c p =
    match l with
    | [] -> p
    | [x] -> FullDom.guassign (import_certvar x) (import_QCond c) p
    | _ -> not_yet_implemented "guassign"

  let rec project l p =
    match l with
    | [] -> p
    | x::l -> project l (FullDom.project p (import_certvar x))

  let leq = isIncl

    (* REALLY INEFFICIENT. TO CHANGE ? *)
  let to_string f p =
    CoqPr.charListTr (to_string (fun x -> CoqPr.stringTr (f (export_certvar x))) p)

  let itvize p t =
    let itv = getItvMode BOTH (import_QTerm t) p in
    { Pol.low = export_QbndT itv.QItv.lower ; Pol.up = export_QbndT itv.QItv.upper }

  let getUpperBound p t =
    try Some (export_QbndT (getItvMode UP (import_QTerm t) p).QItv.upper)
    with Failure s when String.compare s "empty" = 0 -> None

  let getLowerBound p t =
    try Some (export_QbndT (getItvMode LOW (import_QTerm t) p).QItv.lower)
	 with Failure s when String.compare s "empty" = 0 -> None

end








(***********************************************************)
(* translation on Z: mostly a copy-paste from the one of Q *)
(***********************************************************)

module ZInterface = Interface(Scalar.RelInt)
module ZTerm = ZInterface.Term
module ZCond = ZInterface.Cond
module CZCond = ASCond.ZCond
module CZTerm = CZCond.Term


let rec import_ZTerm: ZTerm.t -> CZTerm.t
  = function
  | ZTerm.Var x -> CZTerm.Var (import_certvar x)
  | ZTerm.Cte c -> CZTerm.Cte (import_Z c)
  | ZTerm.Add (t1, t2) -> CZTerm.Add (import_ZTerm t1, import_ZTerm t2)
  | ZTerm.Sum l -> import_bin_assoc import_ZTerm (CZTerm.Cte CZNum.z) (fun t1 t2 -> CZTerm.Add (t1,t2)) l
  | ZTerm.Opp t -> CZTerm.Opp (import_ZTerm t)
  | ZTerm.Mul (t1, t2) -> CZTerm.Mul (import_ZTerm t1, import_ZTerm t2)
  | ZTerm.Prod l -> import_bin_assoc import_ZTerm (CZTerm.Cte CZNum.u) (fun t1 t2 -> CZTerm.Mul (t1,t2)) l
  | ZTerm.Annot (a, t) ->
     (match import_annot a with
     | Some a -> CZTerm.Annot (a, import_ZTerm t)
     | None -> (* Skip annotation *) import_ZTerm t)

let rec import_ZCond: ZCond.t -> CZCond.t
  = function
  | ZCond.Basic b -> CZCond.Basic b
  | ZCond.Atom (t1,c,t2) -> let (t1,c,t2) = import_cmpT import_ZTerm t1 c t2 in
                            CZCond.Atom (c, t1, t2)
  | ZCond.BinL (c1, AND, c2) -> CZCond.BinL (ASCond.AND, import_ZCond c1, import_ZCond c2)
  | ZCond.BinL (c1, OR, c2) -> CZCond.BinL (ASCond.OR, import_ZCond c1, import_ZCond c2)
  | ZCond.Not c -> CZCond.Not (import_ZCond c)




module Vec = Vector.Rat.Positive


module QAffTerm = struct
   type t = Vec.t * Scalar.Rat.t

   let to_string : (Var.t -> string) -> t -> string
   	= fun varPr (v,cste) ->
   	Printf.sprintf "%s + %s"
   		(Vec.to_string varPr v)
   		(Scalar.Rat.to_string cste)

   let to_poly : t -> Polynomial.t
   	= fun (vec,cste) ->
   	Polynomial.ofCstr vec cste

   let to_cp : cmpT * t -> CP.t
		= fun (cmp,t) ->
		let p = to_poly t in
		let (cmp',p') =
		Cstr.(match cmp with
		| EQ -> (Eq, p)
		| LE -> (Le, Polynomial.neg p)
		| LT -> (Lt, Polynomial.neg p)
		| GE -> (Le, p)
		| GT -> (Lt, p)
		| NEQ -> Stdlib.failwith "VPLInterface.Term.to_cp: NEQ unimplemented")
		in
		CP.mk cmp' p'
end


module CQAffTerm = LinTerm.QAffTerm

let export_QAffTerm: CQAffTerm.t -> QAffTerm.t =
  fun t -> (PedraQOracles.ltToVec t.CQAffTerm.lin, export_Q t.CQAffTerm.cte)

module type QLowLevelDomain = LowLevelDomain with module Term = QAffTerm

module CQCstr = CstrC.Cstr

(*************************************************************)
(*            LowLevel on Q -> HighLevel on Z                 *)
(*************************************************************)

module MakeZ (LHD: QLowLevelDomain) : ZInterface.HighLevelDomain with type rep = LHD.rep = struct

  open DomainInterfaces

  module DW = struct

    include LHD

    let isBottom = is_bottom

    let isIncl = leq

    let project p x =  project [export_certvar x] p

    let assume c = assume [(export_s_cmpT c.CQCstr.typ,
                            (PedraQOracles.ltToVec (LinTerm.LinQ.opp c.CQCstr.coefs),
                             export_Q c.CQCstr.cst))]

	let getItvMode mo t p =
		match mo with
		| BOTH ->
			let itv = itvize p (export_QAffTerm t) in
			{ QItv.lower = import_QbndT itv.Pol.low ;
			QItv.upper = import_QbndT itv.Pol.up }
		| UP -> begin
			match getUpperBound p (export_QAffTerm t) with
			| Some bound -> {
				QItv.lower = QItv.Infty ;
				QItv.upper = import_QbndT bound }
			| None -> failwith "empty"
			end
		| LOW -> begin
			match getLowerBound p (export_QAffTerm t) with
			| Some bound -> {
				QItv.lower = import_QbndT bound  ;
				QItv.upper = QItv.Infty }
			| None -> failwith "empty"
			end

    let rename x y = rename (export_certvar x) (export_certvar y)

    let pr p = CoqPr.stringTr (to_string Var.to_string p)

    let to_string f p = CoqPr.stringTr (to_string (fun x -> CoqPr.charListTr (f (import_certvar x))) p)

  end

  module FullDom = DomainFunctors.MakeZ(DW)(DW)(DW)(DW)(DW)

  include FullDom

  let not_yet_implemented s =
    raise (CertcheckerConfig.CertCheckerFailure (Debugging.NYI, "makeZ " ^ s ^ " on Z"))

  module Term = ZInterface.Term

  let is_bottom = FullDom.isBottom

  let assume c p =
    assume (import_ZCond c) p

  let asserts c p =
    coq_assert (import_ZCond c) p

  let rename x y = rename (import_certvar x) (import_certvar y)

  let join = FullDom.join

  let assign l p =
    match l with
    | [] -> p
    | [(x, t)] -> FullDom.assign (import_certvar x) (import_ZTerm t) p
    | _ -> not_yet_implemented "assign"

  let guassign l c p =
    match l with
    | [] -> p
    | [x] -> FullDom.guassign (import_certvar x) (import_ZCond c) p
    | _ -> not_yet_implemented "guassign"


  let rec project l p =
    match l with
    | [] -> p
    | x::l -> project l (FullDom.project p (import_certvar x))

  let leq = FullDom.isIncl

    (* REALLY INEFFICIENT. TO CHANGE ? *)
  let to_string f p =
    CoqPr.charListTr (FullDom.to_string (fun x -> CoqPr.stringTr (f (export_certvar x))) p)

  let itvize p t =
    let itv = getItvMode BOTH (import_ZTerm t) p in
    { Pol.low = export_ZbndT itv.ZItv.low ; Pol.up = export_ZbndT itv.ZItv.up }

  let getUpperBound p t =
  	try Some (export_ZbndT (getItvMode UP (import_ZTerm t) p).ZItv.up)
  	with Failure s when String.compare s "empty" = 0 -> None

  let getLowerBound p t =
  	try Some (export_ZbndT (getItvMode LOW (import_ZTerm t) p).ZItv.low)
  	with Failure s when String.compare s "empty" = 0 -> None

  let translate _ _ = not_yet_implemented "translate"

  let mapi _ _ _ _ = not_yet_implemented "mapi"

  let minkowski _ _ = not_yet_implemented "minkowski"

  let projectM vars pol =
  match backend_rep pol with
  | None -> Stdlib.failwith "translate"
  | Some (p,(ofVar,toVar)) ->
    let (_,ofVar',_) = PedraQOracles.export_backend_rep (p,(ofVar,toVar)) in
    let vars' = List.map ofVar' vars in
  	{pol with pol = LHD.projectM vars' pol.pol}
end

module EqSet = IneqSet.EqSet
module Cons = IneqSet.Cons
module Cert = Cons.Cert
module Cs = EqSet.Cs
module Vec = Cs.Vec
module Var = Vec.V

module Debug = IneqSet.Debug
module Profile = Profile.Profile(struct let name = "Pol" end)

type 'c t = {
	eqs: 'c EqSet.t;
	ineqs: 'c IneqSet.t;}

let top: 'c t
= {
	eqs = EqSet.nil;
	ineqs = IneqSet.nil;
}

let get_eqs (x : 'c t) = x.eqs
let get_ineqs (x : 'c t) = x.ineqs

let to_string: (Var.t -> string) -> 'c t -> string
	= fun varPr p ->
	if EqSet.isTop p.eqs && IneqSet.isTop p.ineqs
	then "top"
	else (EqSet.to_string varPr p.eqs) ^ (IneqSet.to_string varPr p.ineqs)

let to_string_raw: 'c t -> string
	= fun p -> to_string Var.to_string  p

let to_string_ext: 'c Cert.t -> (Var.t -> string) -> 'c t -> string
	= fun factory varPr p ->
	let estr =
		if EqSet.isTop p.eqs
		then " top"
		else "\n" ^ (EqSet.to_string_ext factory varPr p.eqs)
	in
	let istr =
		if IneqSet.isTop p.ineqs
		then " top"
		else "\n" ^ (IneqSet.to_string_ext factory varPr p.ineqs)
	in
	Printf.sprintf "{\n\teqs =%s;\n\tineqs =%s\n}" estr istr

let to_string_ext_raw: 'c Cert.t -> 'c t -> string
	= fun factory p -> to_string_ext factory Var.to_string  p

type 'c rel_t =
| NoIncl
| Incl of 'c list

type bndT =
	| Infty
	| Open of Scalar.Rat.t
	| Closed of Scalar.Rat.t

type itvT = { low: bndT; up: bndT }

let bnd_to_string : bndT -> string
    = function
    | Infty -> "infty"
	| Open r -> Printf.sprintf "Open(%s)" (Scalar.Rat.to_string r)
	| Closed r ->  Printf.sprintf "Closed (%s)" (Scalar.Rat.to_string r)

let get_up (i: itvT) = i.up
let get_low (i: itvT) = i.low

type cstT = S of Scalar.Rat.t | I of itvT

(** The description of an assignment operation.
[var] is given the value [lin] + [cst]. *)
type assign_t = {
	var: Var.t;
	lin: (Scalar.Rat.t * Var.t) list;
	cst: cstT }

let getVar: assign_t -> Var.t
= fun a -> a.var

let getLin: assign_t -> (Scalar.Rat.t * Var.t) list
= fun a -> a.lin

let getCst: assign_t -> cstT
= fun a -> a.cst

let get_cons p : 'c Cons.t list =
	EqSet.list p.eqs @ IneqSet.list p.ineqs

let get_cstr p : Cs.t list =
  (List.map (fun (_,c) -> Cons.get_c c) (get_eqs p)) @
  (List.map Cons.get_c (get_ineqs p))

let get_cstr_ineqs p : Cs.t list =
  (List.map Cons.get_c (get_ineqs p))

let to_string_itv: (Var.t -> string) -> Vec.t -> itvT -> string
= fun varPr v itv ->
	let prLow = function
		| Infty -> "-infty < "
		| Open n -> (Scalar.Rat.to_string n) ^ " < "
		| Closed n -> (Scalar.Rat.to_string n) ^ " <= "
	in
	let prUp = function
		| Infty -> " < +infty"
		| Open n -> " < " ^ (Scalar.Rat.to_string n)
		| Closed n -> " <= " ^ (Scalar.Rat.to_string n)
	in
	(prLow itv.low) ^ (Vec.to_string varPr v) ^ (prUp itv.up)

let to_string_itv_raw: Vec.t -> itvT -> string
= fun v itv -> to_string_itv Var.to_string  v itv

let equalSyn p1 p2: bool =
	let incl l1 l2 = List.for_all
		(fun c2 -> List.exists
			(fun c1 -> Cs.inclSyn (Cons.get_c c1) (Cons.get_c c2)) l1) l2
	in
	let eq l1 l2 = incl l1 l2 && incl l2 l1 in
	EqSet.equal p1.eqs p2.eqs && eq p1.ineqs p2.ineqs

type 'c ependingT =
	| EMin of 'c EqSet.t
	| EAdd of 'c Cons.t list * 'c ependingT

type 'c ipendingT =
	| IMin of 'c IneqSet.t
	| IAdd of 'c Cons.t list * 'c ipendingT
	| IAddRw of 'c Cons.t list * 'c ipendingT
	| IRed of 'c IneqSet.t
	| IRw of 'c IneqSet.t

let rec needsRewrite: 'c ipendingT -> 'c ipendingT
= function
	| IMin iset -> IRw iset
	| IAdd (l, ip) -> IAddRw (l, needsRewrite ip)
	| IAddRw (l, ip) -> IAddRw (l, needsRewrite ip)
	| IRed iset -> IRw iset
	| IRw _ as ip -> ip

type 'c rewriteT =
	| Rewritten of 'c IneqSet.t
	| RewriteBot of 'c

(** [rewriteIneqs es s] projects from [s] all variables defined in [es].
The produced certificates prove that the result [s'] is implied by [s].
No redundancy elimination is performed on [s']. *)
let rewriteIneqs: 'c Cert.t -> 'c EqSet.t -> 'c IneqSet.t -> 'c rewriteT
=	let rewrite: 'c Cert.t -> 'c EqSet.t -> 'c rewriteT -> 'c Cons.t -> 'c rewriteT
	= fun factory es -> function
		| RewriteBot _ as r -> fun _ -> r
		| Rewritten s -> fun c ->
			let c' = EqSet.filter factory es c in
			match Cs.tellProp (Cons.get_c c') with
			| Cs.Trivial -> Rewritten s
			| Cs.Contrad -> RewriteBot (Cons.get_cert c')
			| Cs.Nothing ->
				Rewritten (c'::s)
	in
	fun factory es s ->
		List.fold_left (rewrite factory es) (Rewritten []) s

type 'c rewriteBisT =
	| Rewritten' of 'c Cons.t list
	| RewriteBot' of 'c

let listRw: 'c Cert.t -> 'c EqSet.t -> 'c Cons.t list -> 'c rewriteBisT
=	let rw1: 'c Cert.t -> 'c EqSet.t -> 'c rewriteBisT -> 'c Cons.t -> 'c rewriteBisT
	= fun factory eset -> function
		| RewriteBot' _ as rw -> fun _ -> rw
		| Rewritten' ilist -> fun cons ->
			let (cstr',cert') = EqSet.filter factory eset cons in
			match Cs.tellProp cstr' with
			| Cs.Contrad -> RewriteBot' cert'
			| Cs.Trivial ->
				Rewritten' ilist
			| Cs.Nothing ->
				Rewritten' ((cstr',cert')::ilist)
	in
	fun factory eset ilist ->
		let rwZ = Rewritten' [] in
		List.fold_left (rw1 factory eset) rwZ ilist

type 'c logT = {
	eset: 'c ependingT;
	iset: 'c ipendingT}

let rec epending_to_string : 'c ependingT -> string
	= function
	| EMin eset -> Printf.sprintf "EMin (%s)" (EqSet.to_string Var.to_string eset)
	| EAdd (l, epending) -> Printf.sprintf "EAdd (%s, %s)"
		(Misc.list_to_string (fun (_,c) -> Cs.to_string Var.to_string c) l " ; ")
		(epending_to_string epending)

let rec ipending_to_string : 'c ipendingT -> string
	= function
	| IMin iset -> Printf.sprintf "IMin (%s)" (IneqSet.to_string Var.to_string iset)
	| IAdd (l, ipending) -> Printf.sprintf "IAdd (%s, %s)"
		(Misc.list_to_string (fun (_,c) -> Cs.to_string Var.to_string c) l " ; ")
		(ipending_to_string ipending)
	| IAddRw (l, ipending) -> Printf.sprintf "IAddRw (%s, %s)"
		(Misc.list_to_string (fun (_,c) -> Cs.to_string Var.to_string c) l " ; ")
		(ipending_to_string ipending)
	| IRed iset -> Printf.sprintf "IRed (%s)" (IneqSet.to_string Var.to_string iset)
	| IRw iset -> Printf.sprintf "IRw (%s)" (IneqSet.to_string Var.to_string iset)

let log_to_string : 'c logT -> string
	= fun log ->
	Printf.sprintf "eset =\n%s\n---\niset =\n%s\n"
	(epending_to_string log.eset)
	(ipending_to_string log.iset)

let logEset: 'c logT -> 'c ependingT -> 'c logT
	= fun lp eset ->
	{  eset = eset;
		iset = needsRewrite lp.iset;
	}

let logIset: 'c logT -> 'c ipendingT -> 'c logT
	= fun lp iset ->
	{lp with iset = iset;}

type 'c meetT =
	| Added of 'c t
	| Contrad of 'c

let meetPr: 'c Cert.t -> (Var.t -> string) -> 'c meetT -> string
= fun factory varPr -> function
	| Contrad ce -> Printf.sprintf "Contrad ce, with ce:\n%s" (factory.Cert.to_string ce)
	| Added p -> Printf.sprintf
		"Added p with p:\n%s"
		(to_string_ext factory varPr p)

let meetEq: 'c meetT -> 'c meetT -> bool
= fun m1 m2 ->
	match m1, m2 with
	| Contrad ce1, Contrad ce2 -> ce1 = ce2
	| Added p1, Added p2 -> equalSyn p1 p2
	| Contrad _, Added _
	| Added _ , Contrad _ -> false

type ('a,'c) mayBotT
	= Ok of 'a | Bot of 'c

let logOut: ('c logT, 'c) mayBotT -> 'c meetT
	= function
	| Bot ce -> Contrad ce
	| Ok lp ->
		match lp.iset with
		| IRed _ | IRw _ | IAdd (_, _) | IAddRw (_, _) -> assert false
		| IMin iset ->
			match lp.eset with
			| EAdd _ -> assert false
			| EMin eset ->
				let p = {
						eqs = eset;
						ineqs = iset
					} in
					Added p

let logAddEqs: 'c logT -> 'c Cons.t list -> 'c logT
	= fun p l ->
	if List.length l = 0
	then p
	else logEset p (EAdd (l, p.eset))

let logEqSetAddM: 'c Cert.t -> 'c logT -> ('c logT, 'c) mayBotT
	= fun factory lp1 ->
	let rec flatten: 'c Cons.t list -> 'c ependingT -> ('c logT, 'c) mayBotT
		= fun l -> function
		| EAdd (l', lp) -> flatten (l @ l') lp
		| EMin eset as ep ->
			if List.length l = 0
			then Ok {lp1 with eset = ep}
			else
				match EqSet.addM factory eset l with
				| EqSet.Bot c -> Bot c
				| EqSet.Added eset' -> Ok (logEset lp1 (EMin eset'))
	in
	flatten [] lp1.eset

(* XXX: If there is nothing to rewrite, the log should not be changed. *)
let logrewriteIneqs: 'c Cert.t -> 'c logT -> ('c logT, 'c) mayBotT
	= fun factory lp ->
	let rec rw: 'c logT -> 'c EqSet.t -> 'c ipendingT -> ('c ipendingT, 'c) mayBotT
		= fun lp eset ip ->
			match ip with
			| IAdd (l, ip1) -> begin
				match rw lp eset ip1 with
				| Bot _ as r -> r
				| Ok ip2 -> Ok (IAdd (l, ip2))
				end
			| IAddRw (l, ip1) -> begin
				match listRw factory eset l with
				| RewriteBot' f -> Bot f
				| Rewritten' l' ->
					match rw lp eset ip1 with
					| Bot _ as r -> r
					| Ok ip2 ->
						if List.length l' = 0
						then Ok ip2
						else Ok (IAdd (l', ip2))
				end
			| IMin iset | IRed iset ->	Ok ip
			| IRw iset ->
				match rewriteIneqs factory eset iset with
				| RewriteBot f -> Bot f
				| Rewritten iset' ->  Ok (IRed iset')
	in
	match lp.eset with
	| EAdd (_, _) -> assert false
	| EMin eset ->
		match rw lp eset lp.iset with
		| Bot ce -> Bot ce
		| Ok ip -> Ok (logIset lp ip)

let logIneqSetAddM: Var.t -> Scalar.Symbolic.t Rtree.t -> 'c logT -> ('c logT, 'c) mayBotT
	= let doAdd: Var.t -> 'c logT -> 'c Cons.t list -> 'c IneqSet.t -> Scalar.Symbolic.t Rtree.t -> ('c logT, 'c) mayBotT
		= fun nvar lp l iset point ->
		let iset' = IneqSet.addM nvar iset l point in
		Ok (logIset lp (IMin iset'))
	in
	fun nvar point lp ->
		let rec flatten: 'c Cons.t list -> 'c ipendingT -> ('c logT, 'c) mayBotT
		= fun l -> function
			| IRw _
			| IAddRw (_, _) -> assert false
			| IAdd (l', ip) -> flatten (l @ l') ip
			| IRed iset -> doAdd nvar lp l iset point
			| IMin iset as ip ->
				if List.length l = 0
				then Ok {lp with iset = ip}
				else doAdd nvar lp l iset point
	in
	flatten [] lp.iset

type satChkT = Sat of Splx.t | Unsat of (int * Cs.Vec.Coeff.t) list

(** [chkFeasibility nvar s] checks whether [s] is satisfiable and returns a
simplex object with a satisfied state if it is. If it is not satisfiable, then
a linear combination of the input constraints is returned. [nvar] is used for
fresh variable generation. *)
let chkFeasibility: Var.t -> (int * Cs.t) list -> satChkT
	= let chkFeasibility: Var.t -> (int * Cs.t) list -> satChkT
		= fun nvar cs ->
		match Splx.checkFromAdd (Splx.mk nvar cs) with
		| Splx.IsOk sx -> Sat sx
		| Splx.IsUnsat w -> Unsat w
	in fun nvar cs ->
	Profile.start "chkFeasibility";
	let res = chkFeasibility nvar cs in
	Profile.stop "chkFeasibility";
	res

let rec extract_implicit_eqs' : 'c Cert.t -> Var.t -> 'c logT -> (('c logT, 'c) mayBotT) * (Scalar.Symbolic.t Rtree.t) option
	= fun factory nvar lp ->
	(* TODO: peut-on factoriser le calcul des Is et Js?*)
	let compute_Is : 'c Cons.t list -> (int * Cs.Vec.Coeff.t) list -> (int * 'c Cons.t) list
		= fun conss wit ->
		let (i0, coeff0) = List.hd wit in
		List.fold_left
			(fun res (i, coeff) ->
				let cons = Cons.mul factory coeff (List.nth conss i)
					|> Cons.add factory (List.hd res |> Stdlib.snd)
				in
				(i,cons) :: res)
			[(i0, Cons.mul factory coeff0 (List.nth conss i0))]
			(Misc.sublist wit 1 ((List.length wit)-1))
	in
	let compute_Js : 'c Cons.t list -> (int * Cs.Vec.Coeff.t) list -> (int * 'c) list
		= fun conss wit ->
		let compute_index : int -> int
			= fun i ->
			let n = Misc.findi (fun (j,_) -> i = j) wit in
			List.nth wit (n-1)
			|> Stdlib.fst
		in
		let len = (List.length wit)-1 in
		let (i_n, coeff_n) = List.nth wit len in
		List.fold_right
			(fun (i, coeff) res ->
				let cert = factory.Cert.mul coeff (List.nth conss i |> Cons.get_cert)
					|> factory.Cert.add (List.hd res |> Stdlib.snd)
				in
				(compute_index i,cert) :: res)
			(Misc.sublist wit 1 len)
			[(compute_index i_n,factory.Cert.mul coeff_n (List.nth conss i_n |> Cons.get_cert))]
		|> List.rev
	in
	(* Remove trivial constraints from a given list of constraints. *)
	let rmTriv: 'c Cons.t list -> 'c Cons.t list
		= let isTriv: Cs.t -> bool
			= fun c ->
			Cs.tellProp c = Cs.Trivial
		in
		fun l ->
		List.filter (fun (c,_) -> not (isTriv c)) l
	in
	let rec get_ineqs :'c ipendingT -> 'c Cons.t list
		= fun iset ->
		match iset with
		| IMin iset | IRed iset | IRw iset -> iset
		| IAdd (iset,tail) | IAddRw (iset,tail) -> iset @ (get_ineqs tail)
	in
	let conss = get_ineqs lp.iset
		|> rmTriv
	in
	let ilist = List.mapi (fun i (c,_) -> (i,c)) conss in
	match chkFeasibility nvar ilist with
	| Unsat wit ->
		let cert = Cons.linear_combination_cert factory conss wit in
		(Bot cert, None)
	| Sat _ ->
		let ilist_stricten = List.map (fun (i,c) -> i, {c with Cs.typ = Cstr.Lt}) ilist in
		match chkFeasibility nvar ilist_stricten with
		| Sat sx_strict -> Ok lp, Some (Splx.getAsg sx_strict)
		| Unsat wit ->
			let is = compute_Is conss wit
			and js = compute_Js conss wit
			in
			let ijs = List.map2
				(fun (i,(cstr,lower_bound)) (j,upper_bound) ->
					assert (i = j);
					(i, ({cstr with Cs.typ = Cstr.Eq}, factory.Cert.merge lower_bound upper_bound))
					) is js
			in
			let elist =
				List.fold_left
				(fun res (i,_) ->
					if List.mem_assoc i ijs
					then List.assoc i ijs :: res
					else res)
				[] ilist
			in
			let lp' = logAddEqs lp elist in
			match logEqSetAddM factory lp' with
			| Bot _ as b -> b, None
			| Ok lp ->
				match logrewriteIneqs factory lp with
				| Bot _ as b -> b, None
				| Ok lp -> extract_implicit_eqs' factory nvar lp

let extract_implicit_eqs : 'c Cert.t -> Var.t -> 'c logT -> (('c logT, 'c) mayBotT) * (Scalar.Symbolic.t Rtree.t) option
	= fun factory nvar lp ->
	Profile.start "extract_implicit_eqs";
	let res = extract_implicit_eqs' factory nvar lp in
	Profile.stop "extract_implicit_eqs";
	res

let logInit: 'c t -> 'c Cons.t list -> ('c logT, 'c) mayBotT
	= let split: 'c Cons.t list -> 'c Cons.t list * 'c Cons.t list
		= fun l -> List.partition (fun (c, _) -> Cs.get_typ c = Cstr.Eq) l
	in
	fun p l ->
		let (elist, ilist) = split l in
		Ok {
			eset = if elist = []
				then EMin p.eqs
				else EAdd (elist, EMin p.eqs);
			iset = if ilist = []
				then if elist = []
					then IMin p.ineqs
					else IRw p.ineqs
				else IAddRw (ilist, IMin p.ineqs)
		}

let logBind: ('c logT, 'c) mayBotT -> ('c logT -> ('c logT, 'c) mayBotT) -> ('c logT, 'c) mayBotT
= fun mlp f ->
	match mlp with
	| Bot _ as b -> b
	| Ok lp -> f lp

let (<*>) = logBind

(* XXX: it is a bit awkward that [p.nxt] is supposed to take into account
the identifiers used in [l]. *)
let addAux': 'c Cert.t -> Var.t -> 'c t -> 'c Cons.t list -> 'c meetT
	= fun factory nvar p l ->
	logOut
	(logInit p l
	<*> (fun lp -> logEqSetAddM factory lp) (* Removing syntactic equalities *)
	<*> (fun lp -> logrewriteIneqs factory lp)
	|> function
		| Bot _ as b -> b
		| Ok lp ->
			match extract_implicit_eqs factory nvar lp with
			| Bot f, _ -> Bot f
			| Ok _, None -> Stdlib.failwith "Pol.addAux"
			| Ok lp, Some point -> logIneqSetAddM nvar point lp)

let addAux: 'c Cert.t -> Var.t -> 'c t -> 'c Cons.t list -> 'c meetT
	= fun factory nvar p conss ->
	Profile.start "addAux" ;
	let res = addAux' factory nvar p conss in
	Profile.stop "addAux";
	res

let addMSub: 'c Cert.t -> Var.t -> 'c t -> 'c Cons.t list -> 'c meetT
	= fun factory nvar p conss -> addAux factory nvar p conss

let addSub: 'c Cert.t -> Var.t -> 'c t -> 'c Cons.t -> 'c meetT
	= fun factory nvar p c -> addAux factory nvar p [c]

let meetSub: 'c Cert.t -> Var.t -> 'c t -> 'c t -> 'c meetT
	= fun factory nvar p1 p2 ->
	addAux factory nvar p1 (EqSet.list p2.eqs @ IneqSet.list p2.ineqs)

let mkSub: 'c Cert.t -> Var.t -> 'c Cons.t list -> 'c t option
	= fun factory nvar l ->
	match addMSub factory nvar top l with
	| Added p -> Some p
	| Contrad _ -> None

let projectSub: 'c Cert.t -> Var.t -> 'c t -> Var.t -> 'c t
	= fun factory nxtVar p x ->
	let (opte, eqs) = EqSet.trySubst factory x p.eqs in
	let ineqs =
		match opte with
		| Some e -> IneqSet.subst factory nxtVar eqs x e p.ineqs
		| None -> match !Flags.proj with
			| Flags.FM -> IneqSet.fmElim factory nxtVar eqs x p.ineqs
			| Flags.Proj_PLP scalar_type -> IneqSet.pProj factory x p.ineqs scalar_type
			| Flags.PHeuristic -> match Heuristic.proj (List.map Cons.get_c p.ineqs) with
				| Flags.FM -> IneqSet.fmElim factory nxtVar eqs x p.ineqs
				| Flags.Proj_PLP scalar_type -> IneqSet.pProj factory x p.ineqs scalar_type
				| Flags.PHeuristic -> Stdlib.invalid_arg "Pol.projectSub"
	in
	{ineqs = ineqs; eqs = eqs;}

let projectMSubFM: 'c Cert.t -> Var.t -> 'c t -> Var.t list -> 'c t
	= fun factory nxtVar p l ->
	let msk =
		List.fold_left (fun m x -> Rtree.set None m x (Some x)) Rtree.Nil l
	in
	let rec project1 : 'c EqSet.t -> 'c IneqSet.t -> 'c t
	= fun eqs ineqs ->
		let (opte, eqs1) = EqSet.trySubstM factory msk eqs in
		match opte with
		| Some (e, x) ->
			let ineqs1 = IneqSet.subst factory nxtVar eqs1 x e ineqs in
			project1 eqs1 ineqs1
		| None ->
			let ineqs1 = IneqSet.fmElimM factory nxtVar eqs1 msk ineqs
			in
			{ineqs = ineqs1; eqs = eqs1}
	in
	project1 p.eqs p.ineqs

let projectMSubPLP: 'c Cert.t -> Var.t -> 'c t -> Var.t list -> Flags.scalar -> 'c t
	= fun factory nxtVar p l scalar_type ->
	let msk =
		List.fold_left (fun m x -> Rtree.set None m x (Some x)) Rtree.Nil l
	in
	let rec findEq : Var.t list -> 'c EqSet.t -> 'c IneqSet.t -> ('c EqSet.t * 'c IneqSet.t)
		= fun vars eqs ineqs ->
		match vars with
		| [] -> (eqs,ineqs)
		| v :: tl ->
			let (opte, eqs1) = EqSet.trySubstM factory msk eqs in
			match opte with
			| Some (e, x) ->
				let ineqs1 = IneqSet.subst factory nxtVar eqs1 x e ineqs in
				findEq tl eqs1 ineqs1
			| None -> findEq tl eqs1 ineqs
	in
	let (eqs1, ineqs1) = findEq l p.eqs p.ineqs in
	(* XXX: Comment actualiser les variables à projeter après réécriture des égalités?*)
	let ineqs2 = IneqSet.pProjM factory l ineqs1 scalar_type in
	{ineqs = ineqs2;eqs = eqs1}


let projectMSub: 'c Cert.t -> Var.t -> 'c t -> Var.t list -> 'c t
	= fun factory nxt p l ->
	match !Flags.proj with
	| Flags.Proj_PLP scalar_type -> projectMSubPLP factory nxt p l scalar_type
	| Flags.FM -> projectMSubFM factory nxt p l
	| Flags.PHeuristic -> match Heuristic.proj (List.map Cons.get_c p.ineqs) with
		| Flags.Proj_PLP scalar_type -> projectMSubPLP factory nxt p l scalar_type
		| Flags.FM -> projectMSubFM factory nxt p l
		| Flags.PHeuristic -> Stdlib.invalid_arg "Pol.projectMSub"
(*
type discr_t = Op1 of int | Op2 of int | Other
*)
(* note: x = y1 + y2 and alpha1 + alpha2 = 1 are substituted on the fly *)
let joinSetup: 'c1 Cert.t -> 'c2 Cert.t -> Var.t -> 'c1 t -> 'c2 t
	-> Var.t * (('c1,'c2) Cons.discr_t) t * Var.t list * ('c1,'c2) Cons.discr_cert
	= fun factory1 factory2 varNxt p1 p2 ->
	Debug.log DebugTypes.Detail (lazy "Entering joinSetup");
	let factory = Cons.discr_factory factory1 factory2 in
	let alpha = varNxt in
	let aIneqs = Cert.([
		(Cs.mk Cstr.Le [Scalar.Rat.u, alpha] Scalar.Rat.u,
			(factory1.triv Cstr.Le Cs.Vec.Coeff.z, factory2.triv Cstr.Le Cs.Vec.Coeff.u));
		(Cs.mk Cstr.Le [Scalar.Rat.negU, alpha] Scalar.Rat.z,
			(factory1.triv Cstr.Le Cs.Vec.Coeff.u, factory2.triv Cstr.Le Cs.Vec.Coeff.z))
		])
	in
	let (varNxt1, r, eqs1) = EqSet.joinSetup_1 factory2 (Var.next varNxt) Rtree.Nil alpha p1.eqs in
	Debug.log DebugTypes.Detail (lazy (Printf.sprintf "Equalities of P1 handled: \n%s"
		(EqSet.to_string_ext factory Var.to_string eqs1)));
	let (varNxt2, r, eqs2) = EqSet.joinSetup_2 factory1 varNxt1 r alpha p2.eqs in
	Debug.log DebugTypes.Detail (lazy (Printf.sprintf "Equalities of P2 handled: \n%s"
		(EqSet.to_string_ext factory Var.to_string eqs2)));
	let (varNxt3, r, ineqs1) = IneqSet.joinSetup_1 factory2 varNxt2 r alpha p1.ineqs in
	Debug.log DebugTypes.Detail (lazy (Printf.sprintf "Inequalities of P1 handled: \n%s"
		(IneqSet.to_string_ext factory Var.to_string ineqs1)));
	let (varNxt4, r, ineqs2) = IneqSet.joinSetup_2 factory1 varNxt3 r alpha p2.ineqs in
	Debug.log DebugTypes.Detail (lazy (Printf.sprintf "Inequalities of P2 handled: \n%s"
		(IneqSet.to_string_ext factory Var.to_string ineqs2)));
	let eqs = List.append eqs1 eqs2 in
	let ineqs = List.concat [ineqs1; ineqs2; aIneqs] in
	let vars =
		Rtree.fold (fun _ a -> function None -> a | Some x -> x::a) [alpha] r
	in
	(varNxt4, {ineqs = ineqs; eqs = eqs}, vars, factory)

let correct_cmp: 'c Cert.t -> 'c Cons.t -> 'c Cons.t
	= fun fac (c,cert) ->
	if (Cs.get_typ c) = Cstr.Le
	then (c, fac.Cert.to_le cert)
	else (c,cert)

let split_certificates : 'c1 Cert.t -> 'c2 Cert.t -> (('c1,'c2) Cons.discr_t) t -> 'c1 t * 'c2 t
	= fun factory1 factory2 p ->
	let (ineqs1,ineqs2) =
	List.fold_left
		(fun (ineqs1,ineqs2) (c, (cert1,cert2)) ->
			((correct_cmp factory1 (c, cert1))::ineqs1),
			((correct_cmp factory2 (c, cert2))::ineqs2))
		([],[]) p.ineqs
	and (eqs1,eqs2) =
	List.fold_left
		(fun (eqs1,eqs2) (v, (c, (cert1,cert2))) -> (v, (c, cert1))::eqs1, (v, (c, cert2))::eqs2)
		([],[]) p.eqs
	in
	{eqs = eqs1 ; ineqs = ineqs1}, {eqs = eqs2 ; ineqs = ineqs2}

let joinSub_classic: 'c1 Cert.t -> 'c2 Cert.t -> Var.t -> 'c1 t -> 'c2 t -> 'c1 t * 'c2 t
	= fun factory1 factory2 nxtVar p1 p2 ->
	(*
	let postProcess p =
(* XXX: This whole function is an ugly hackish quickfix for an issue with strict inequality support.
See notClosed0 in the join test suite. *)
		let ltList: t -> int list
		= fun p ->
			let ltCons = List.filter (fun c -> Cs.get_typ (Cons.get_c c) = Cstr.Lt) (IneqSet.list p.ineqs) in
			List.map Cons.get_id ltCons
		in
		let isLt: int list -> int -> bool
		= fun l i0 -> List.exists (fun i -> i = i0) l
		in
		let hasLt: int list -> Cert.cstr_t -> bool
		= fun l -> function
			| Cert.SplitEq _ -> failwith "Pol.join"
			| Cert.Direct f -> List.exists (fun (i, _) -> isLt l i) f
		in
		let ltP = ltList p in
		let ltP1 = ltList p1 in
		let ltP2 = ltList p2 in
		let elect j =
			if isLt ltP (Cert.getId j) then
				if hasLt ltP1 (Cert.getArg1 j) && hasLt ltP2 (Cert.getArg2 j) then
					false
				else
					true
			else
				false
		in
		let promote: t -> int list -> t
		= fun p les ->
			let promote1 c =
				if List.exists (fun i -> i = Cons.get_id c) les then
					{c with Cons.c = {(Cons.get_c c) with Cs.typ = Cstr.Le }}
				else
					c
			in
			{p with ineqs = List.map promote1 p.ineqs}
		in
		(promote p (List.map Cert.getId (List.filter elect cert)), cert)
	in
	*)
	let (nxtVar1, p0, vars, factory) = joinSetup factory1 factory2 nxtVar p1 p2 in
	let p = projectMSub factory nxtVar1 p0 vars in
	split_certificates factory1 factory2 p
	(*match cert with
	| Cert.Empty _ | Cert.Bind _ -> failwith "Pol.join"
	| Cert.Implies l ->
		let l0 = List.map split l in
		let l1 = List.map (fun (i, a1, a2) -> {Cert.id = i; Cert.arg1 = a1; Cert.arg2 = a2}) l0 in
		postProcess (p, l1)*)

module Join_PLP = struct

	let split_eq : 'c Cert.t -> 'c t -> 'c Cons.t list
		= fun factory p ->
		List.fold_left
			(fun res (_,cons) ->
				let (c1,c2) = Cons.split factory cons in
				c1::c2::res)
			[]
			p.eqs

	(* Version spéciale pour extract_implicit_eq*)
	let logOut: ('c logT, 'c) mayBotT -> 'c t
		= function
			| Bot ce -> Stdlib.failwith "Pol.join:extract_implicit_eq"
			| Ok lp -> begin
				match lp.iset with
				| IRed _ | IRw _ | IAdd (_, _) | IAddRw (_, _) -> assert false
				| IMin iset ->
					match lp.eset with
					| EAdd _ -> assert false
					| EMin eset -> {eqs = eset; ineqs = iset}
			end

	let extract_implicit_eq : 'c Cert.t -> Var.t -> 'c t -> 'c t
		= fun factory nxtVar p ->
		logOut
		(logInit p []
		|> function
			| Bot _ as b -> b
			| Ok lp ->
				match extract_implicit_eqs factory nxtVar lp with
				| Bot f, _ -> Bot f
				| Ok _, None -> Stdlib.failwith "Pol.join:extract_implicit_eq"
				| Ok lp, Some point -> logIneqSetAddM nxtVar point lp)

	let filter_trivial : 'c Cons.t list -> 'c Cons.t list
		= fun l ->
			List.filter
				(fun cons ->
					Cs.tellProp (Cons.get_c cons) <> Cs.Trivial
					&& not(Cs.Vec.equal (Cons.get_c cons |> Cs.get_v) Cs.Vec.nil))
				l

	let add_epsilon : Var.t -> 'c Cons.t list -> 'c Cons.t list
		= fun epsilon l ->
		List.map
			(fun cons ->
				({(Cons.get_c cons) with Cs.v = Cs.Vec.set (Cons.get_c cons |> Cs.get_v) epsilon Cs.Vec.Coeff.negU},
				 Cons.get_cert cons))
			l

	let remove_epsilon : Var.t -> 'c Cons.t list -> 'c Cons.t list
		= fun epsilon l ->
		List.map
			(fun cons ->
				({(Cons.get_c cons) with Cs.v = Cs.Vec.set (Cons.get_c cons |> Cs.get_v) epsilon Cs.Vec.Coeff.z},
				 Cons.get_cert cons))
			l

	let joinSub_epsilon: Flags.scalar -> 'c1 Cert.t -> 'c2 Cert.t -> Var.t -> 'c1 t -> 'c2 t -> 'c1 t * 'c2 t
		= fun scalar_type factory1 factory2 nxtVar p1 p2 ->
		let epsilon = nxtVar in
		let p1_eqs = split_eq factory1 p1
		and p2_eqs = split_eq factory2 p2 in
		let (p1_cons, p2_cons) =
			if p1_eqs <> [] || p2_eqs <> []
			then ((add_epsilon epsilon p1_eqs) @ p1.ineqs, (add_epsilon epsilon p2_eqs) @ p2.ineqs)
			else (p1.ineqs, p2.ineqs)
		in
		let (p1',p2') =
			let eps_opt = if p1_eqs <> [] || p2_eqs <> []
				then Some epsilon
				else None in
			match !Flags.join with
			| Flags.Join_PLP _ -> Join.join scalar_type factory1 factory2 eps_opt p1_cons p2_cons
			| Flags.Join_fromRegions -> Join_RR.join factory1 factory2 eps_opt p1_cons p2_cons
			| _ -> Stdlib.failwith "Pol.joinSub_epsilon"
		in
		let p1'_ineqs = remove_epsilon epsilon p1' |> filter_trivial
		and p2'_ineqs = remove_epsilon epsilon p2' |> filter_trivial
		in
		(extract_implicit_eq factory1 nxtVar {ineqs = p1'_ineqs ; eqs = []},
		 extract_implicit_eq factory2 nxtVar {ineqs = p2'_ineqs ; eqs = []})

end

let inclSub: 'c1 Cert.t -> Var.t -> 'c1 t -> 'c2 t -> 'c1 rel_t
	= fun factory nxtVar p1 p2 ->
	Debug.log DebugTypes.Normal (lazy (Printf.sprintf "Checking inclusion %s ⊂ %s"
		(to_string_ext factory Var.to_string p1)
		(to_string Var.to_string p2)))
	;
	match EqSet.incl factory p1.eqs p2.eqs with
	| EqSet.NoIncl -> NoIncl
	| EqSet.Incl certE -> begin
		Debug.log DebugTypes.Detail (lazy (Printf.sprintf "Inclusion holds for equalities: %s"
			(Misc.list_to_string factory.to_string certE "\n")));
		match IneqSet.incl factory nxtVar p1.eqs p1.ineqs p2.ineqs with
		| IneqSet.NoIncl -> NoIncl
		| IneqSet.Incl certI -> begin
			Debug.log DebugTypes.Detail (lazy (Printf.sprintf "Inclusion holds for inequalities: %s"
			(Misc.list_to_string factory.to_string certI "\n")));
			Incl (List.append certI certE)
			end
		end

let joinSub: 'c1 Cert.t -> 'c2 Cert.t -> Var.t -> 'c1 t -> 'c2 t -> 'c1 t * 'c2 t
	= let check_incl
		= fun factory nxtVar p1 p2 ->
		match inclSub factory nxtVar p1 p2 with
		| Incl p2_from_p1 ->
			let ineqs = get_ineqs p2 |> List.rev
			and eqs = get_eqs p2 in
			let len_ineqs = List.length ineqs in
			Some {
				ineqs = List.map2
					(fun (cstr,_) cert -> (cstr,cert))
					ineqs (Misc.sublist p2_from_p1 0 len_ineqs);
				eqs = List.map2
					(fun (v, (cstr,_)) cert -> (v, (cstr,cert)))
					eqs (Misc.sublist p2_from_p1 len_ineqs (List.length p2_from_p1));
			}
		| NoIncl -> None
	in
	fun factory1 factory2 nxtVar p1 p2 ->
	match check_incl factory1 nxtVar p1 p2 with
	| Some p1' -> (p1',p2)
	| None -> match check_incl factory2 nxtVar p2 p1 with
	| Some p2' -> (p1,p2')
	| None -> begin
		Debug.log DebugTypes.Normal (lazy "No inclusion found. Computing convex hull. ");
		match !Flags.join with
			| Flags.Baryc -> joinSub_classic factory1 factory2 nxtVar p1 p2
			| Flags.Join_PLP scalar_type -> Join_PLP.joinSub_epsilon scalar_type factory1 factory2 nxtVar p1 p2
			| Flags.Join_fromRegions -> Join_PLP.joinSub_epsilon Flags.Float factory1 factory2 nxtVar p1 p2
			| Flags.JHeuristic -> match Heuristic.join (get_cstr p1) (get_cstr p2) with
				| Flags.Baryc -> joinSub_classic factory1 factory2 nxtVar p1 p2
				| Flags.Join_PLP scalar_type -> Join_PLP.joinSub_epsilon scalar_type factory1 factory2 nxtVar p1 p2
				| Flags.Join_fromRegions -> Join_PLP.joinSub_epsilon Flags.Float factory1 factory2 nxtVar p1 p2
				| Flags.JHeuristic -> Stdlib.invalid_arg "Pol.joinSub"
		end
type relVarT = OldSt of Var.t | NewSt of Var.t
type relLinT = (Scalar.Rat.t * relVarT) list
type relCstrT = {cmpSign: Cstr.cmpT; linear: relLinT; constant: Scalar.Rat.t}

let widen : 'c Cert.t -> 'c t -> 'c t -> 'c t
	= fun factory p1 p2 ->
	let elect s c =
		let c1 = EqSet.filter factory p1.eqs c in
		match Cs.tellProp (Cons.get_c c1) with
		| Cs.Trivial -> c::s (* XXX: c shouldn't get in, right? *)
		| Cs.Nothing ->
			if List.exists (fun c2 -> Cons.equal c2 c1) p1.ineqs then
				c::s
			else
				s

		| Cs.Contrad -> failwith "Pol.widen"
	in
	{ p2 with ineqs = List.fold_left elect [] p2.ineqs }

let mkplist p =
	let e = EqSet.list p.eqs in
	let i = IneqSet.list p.ineqs in
	List.map (fun c -> (Cons.get_c c)) (List.append e i)

let opt2itv: (Scalar.Rat.t -> Scalar.Rat.t) -> 'c Cert.t -> 'c Cons.t list -> Opt.optT -> bndT * 'c option
	= fun f factory conss ->
	function
	| Opt.Finite (_, n, w) ->
		let cert = Cons.linear_combination_cert factory conss w
			|> factory.Cert.add (factory.Cert.triv Cstr.Le Scalar.Rat.z)
		in
		(Closed (f n), Some cert)
	| Opt.Sup (_, n, w) ->
		let cert = Cons.linear_combination_cert factory conss w
			|> factory.Cert.add (factory.Cert.triv Cstr.Le Scalar.Rat.z)
		in
		(Open (f n), Some cert)
  | Opt.Infty -> (Infty, None)

let getUpperBoundImpl : 'c Cert.t -> 'c Cons.t list -> Vec.t -> Splx.t Splx.mayUnsatT -> bndT * 'c option
  = fun factory conss v sx ->
  match Opt.max' sx v with
  | Splx.IsUnsat _ -> Stdlib.failwith "Pol.getUpperBoundSub"
  | Splx.IsOk u -> opt2itv (fun n -> n) factory conss u

let getUpperBoundSub : 'c Cert.t -> Var.t -> 'c t -> Vec.t -> bndT * 'c option
  = fun factory x p v ->
  let conss = EqSet.list p.eqs @ IneqSet.list p.ineqs in
  let i_cstr = List.mapi (fun i cons -> (i, Cons.get_c cons)) conss in
  Splx.mk x i_cstr
    |> getUpperBoundImpl factory conss v

let getLowerBoundImpl : 'c Cert.t -> 'c Cons.t list -> Vec.t -> Splx.t Splx.mayUnsatT -> bndT * 'c option
  = fun factory conss v sx ->
  match Opt.max' sx (Vec.neg v) with
  | Splx.IsUnsat _ -> Stdlib.failwith "Pol.getLowerBoundSub"
  | Splx.IsOk l -> opt2itv Scalar.Rat.neg factory conss l

let getLowerBoundSub : 'c Cert.t -> Var.t -> 'c t -> Vec.t -> bndT * 'c option
  = fun factory x p v ->
  let conss = EqSet.list p.eqs @ IneqSet.list p.ineqs in
  let i_cstr = List.mapi (fun i cons -> (i, Cons.get_c cons)) conss in
  Splx.mk x i_cstr
    |> getLowerBoundImpl factory conss v

let itvizeSub: 'c Cert.t -> Var.t -> 'c t -> Vec.t -> itvT * 'c option * 'c option
	= fun factory nxtVar p v ->
	let conss = EqSet.list p.eqs @ IneqSet.list p.ineqs in
	let i_cstr = List.mapi (fun i cons -> (i, Cons.get_c cons)) conss in
	let sx = Splx.mk nxtVar i_cstr in
	let (up, upf) = getUpperBoundImpl factory conss v sx in
	let (low, lpf) = getLowerBoundImpl factory conss v sx in
	{low = low; up = up}, lpf, upf

let varSet: 'c t -> Var.Set.t
	= fun p -> Cs.getVars (mkplist p)

let add: 'c Cert.t -> 'c t -> 'c Cons.t -> 'c meetT
	= fun factory p c ->
	Debug.log DebugTypes.Title (lazy "Building add");
	Debug.log DebugTypes.MInput (lazy (Printf.sprintf "c = %s\nP = %s"
			(Cons.to_string_ext factory Var.to_string c)
			(to_string_raw p)))
	;
	let nxt = Var.Set.union (varSet p) (Cs.getVars [Cons.get_c c]) |> Var.horizon in
	let res = addSub factory nxt p c in
	Debug.log DebugTypes.MOutput (lazy (Printf.sprintf "%s"
			(match res with
			| Added p -> to_string_raw p
			| Contrad cert -> "Contrad " ^ (factory.to_string cert))))
	;
	res

let addM: 'c Cert.t -> 'c t -> 'c Cons.t list -> 'c meetT
= fun factory p l ->
	Debug.log DebugTypes.Title (lazy "Building add");
	Debug.log DebugTypes.MInput (lazy (Printf.sprintf "c = %s\nP = %s"
			(Misc.list_to_string (Cons.to_string_ext factory Var.to_string) l " ; ")
			(to_string_raw p)))
	;
	let nxt = Var.Set.union (varSet p) (Cs.getVars (List.map Cons.get_c l)) |> Var.horizon in
	let res = addMSub factory nxt p l in
	Debug.log DebugTypes.MOutput (lazy (Printf.sprintf "%s"
			(match res with
			| Added p -> to_string_raw p
			| Contrad cert -> "Contrad " ^ (factory.to_string cert))))
	;
	res

let meet: 'c Cert.t -> 'c t -> 'c t -> 'c meetT
	= fun factory p1 p2 ->
	let nxt = Var.Set.union (varSet p1) (varSet p2) |> Var.horizon in
	meetSub factory nxt p1 p2

let mk: 'c Cert.t -> 'c Cons.t list -> 'c t option
	= fun factory l ->
	mkSub factory (List.map Stdlib.fst l |> Cs.getVars |> Var.horizon) l

let project: 'c Cert.t -> 'c t -> Var.t -> 'c t
	= fun factory p x ->
	Debug.log DebugTypes.Title (lazy "Building Projection");
	Debug.log DebugTypes.MInput (lazy (Printf.sprintf "v = %s\nP = %s"
			(Var.to_string x)
			(to_string_raw p)))
	;
	let res = projectSub factory (Var.Set.add x (varSet p) |> Var.horizon) p x in
	Debug.log DebugTypes.MOutput (lazy (Printf.sprintf "%s"
			(to_string_raw res)))
	;
	res

let projectM: 'c Cert.t -> 'c t -> Var.t list -> 'c t
	= fun factory p l ->
	Debug.log DebugTypes.Title (lazy "Building Projection");
	Debug.log DebugTypes.MInput (lazy (Printf.sprintf "v = %s\nP = %s"
			(Misc.list_to_string Var.to_string l ";")
			(to_string_raw p)))
	;
	let res = projectMSub factory (Var.Set.union (Var.Set.of_list l) (varSet p) |> Var.horizon) p l in
	Debug.log DebugTypes.MOutput (lazy (Printf.sprintf "%s"
			(to_string_raw res)))
	;
	res

let join: 'c1 Cert.t -> 'c2 Cert.t -> 'c1 t -> 'c2 t -> 'c1 t * 'c2 t
	= fun factory1 factory2 p1 p2 ->
	Debug.log DebugTypes.Title (lazy "Building Join");
	Debug.log DebugTypes.MInput (lazy (Printf.sprintf "P1 = %s\nP2 = %s\n"
			(to_string_raw p1)
			(to_string_raw p2)))
	;
	let nxt = Var.Set.union (varSet p1) (varSet p2) |> Var.horizon in
	let res = joinSub factory1 factory2 nxt p1 p2 in
	Debug.log DebugTypes.MOutput (lazy (Printf.sprintf "%s"
			(to_string_raw (fst res))))
	;
	res

let incl: 'c1 Cert.t -> 'c1 t -> 'c2 t -> 'c1 rel_t
	= fun factory p1 p2 ->
	let nxt = Var.Set.union (varSet p1) (varSet p2) |> Var.horizon in
	inclSub factory nxt p1 p2

let itvize: 'c Cert.t -> 'c t -> Vec.t -> itvT * 'c option * 'c option
	= fun factory p v ->
	let nxt = Var.Set.union (Vec.getVars [v]) (varSet p) |> Var.horizon in
	itvizeSub factory nxt p v

let getUpperBound : 'c Cert.t -> 'c t -> Vec.t -> bndT * 'c option
	= fun factory p v ->
	let nxt = Var.Set.union (Vec.getVars [v]) (varSet p) |> Var.horizon in
	getUpperBoundSub factory nxt p v

let getLowerBound : 'c Cert.t -> 'c t -> Vec.t -> bndT * 'c option
	= fun factory p v ->
	let nxt = Var.Set.union (Vec.getVars [v]) (varSet p) |> Var.horizon in
	getLowerBoundSub factory nxt p v

let rename: 'c Cert.t -> Var.t -> Var.t -> 'c t -> 'c t
	= fun factory x y p -> {
	eqs = EqSet.rename factory p.eqs x y;
	ineqs = IneqSet.rename factory p.ineqs x y}

(*
let inter factory p1 p2 =
  mk factory ((get_cstr p1) @ (get_cstr p2))
*)
let invChk: 'c Cert.t -> 'c t -> bool * string
	= fun factory p ->
	let chkTriv: 'c t -> bool
		= let chk1: 'c Cons.t -> bool
			= fun c -> Cs.tellProp (Cons.get_c c) = Cs.Nothing
		in
		fun p ->
			List.for_all chk1 p.ineqs && List.for_all (fun (_, c) -> chk1 c) p.eqs
	in
	let chkDefU: 'c t -> bool
		= let chk1: Var.t * 'c Cons.t -> bool
			= fun (x, c) ->
			let lin = Cs.get_v (Cons.get_c c) in
			Scalar.Rat.cmp Scalar.Rat.u (Vec.get lin x) = 0
		in
		fun p -> List.for_all chk1 p.eqs
	in
	let chkDefE: 'c t -> bool
		= let chk1: Var.t * 'c Cons.t -> Var.t list * bool -> Var.t list * bool
			= fun (x, c) (l, r) ->
			let lin = Cs.get_v (Cons.get_c c) in
			(x::l, r && List.for_all (fun x' -> Scalar.Rat.cmpz (Vec.get lin x') = 0) l)
		in
		fun p -> snd (List.fold_right chk1 p.eqs ([], true))
	in
	let chkDefI: 'c t -> bool
		= let chk1: Var.t list -> 'c Cons.t -> bool
			= fun l c ->
			let lin = Cs.get_v (Cons.get_c c) in
			List.for_all (fun x -> Scalar.Rat.cmpz (Vec.get lin x) = 0) l
		in
		fun p -> List.for_all (chk1 (List.map fst p.eqs)) p.ineqs
	in
	let chkBot: 'c t -> bool
		= let cs: 'c t -> (int * Cs.t) list
			= fun p ->
			List.mapi (fun i c -> (i, Cons.get_c c))
				(List.append p.ineqs (List.map snd p.eqs))
		in
		fun p ->
			let h = varSet p |> Var.horizon in
			match Splx.checkFromAdd (Splx.mk h (cs p)) with
			| Splx.IsOk _ -> true
			| Splx.IsUnsat _ -> false
	in
	let chkRed: 'c t -> bool
		= let chkE: 'c EqSet.t -> bool
			= let add: 'c EqSet.t option -> Var.t * 'c Cons.t -> 'c EqSet.t option
				= function
				| None -> fun _ -> None
				| Some es -> fun (_, c) ->
					match EqSet.addM factory es [c] with
					| EqSet.Added es' -> Some es'
					| EqSet.Bot _ -> None
			in
			fun es ->
				match List.fold_left add (Some EqSet.nil) es with
				| None -> false
				| Some es' -> List.length es = List.length es'
		in
		let chkI: 'c t -> bool
			= fun p ->
			let nxt = varSet p |> Var.horizon in
			match IneqSet.simpl factory nxt p.eqs p.ineqs with
			| IneqSet.SimplBot _ -> false
			| IneqSet.SimplMin is -> List.length is = List.length p.ineqs
		in
		fun p -> chkI p && chkE p.eqs
	in
	let tr: bool -> string -> bool * string
		= fun r m -> (r, if r then "" else m)
	in
	let log = [
		tr (chkTriv p) "some constraints are trivial or contradictory";
		tr (chkDefU p) "non-unit coefficient for a defined variable";
		tr (chkDefE p) "a defined variable appears in an equality";
		tr (chkDefI p) "a defined variable appears in an inequality";
		tr (chkBot p) "the polyhedron is empty";
		tr (chkRed p) "there are redundant constraints"
	] in
	(List.for_all (fun (r, _) -> r) log,
		let errs = List.map snd log in
		String.concat "\n" (List.filter (fun s -> String.length s > 0) errs))

let equal : 'c1 Cert.t -> 'c2 Cert.t -> 'c1 t -> 'c2 t -> bool
	= fun fac1 fac2 p1 p2 ->
	match (incl fac1 p1 p2, incl fac2 p2 p1) with
	| (Incl _, Incl _) -> true
	| (_,_) -> false

let plot : 'c t -> string
	= fun p ->
	let (eqs, ineqs) = List.partition (fun c -> c.Cs.typ = Cstr.Eq) (get_cstr p)
	in
	let vars = Cs.getVars (eqs @ ineqs)
		|> Var.Set.elements
	in
	Printf.sprintf "P = Polyhedron(eqns = %s, ieqs = %s)\n"
		(Misc.list_to_string (Cs.plot vars) eqs ", ")
		(Misc.list_to_string (Cs.plot vars) ineqs ", ")

let plot_opt : 'c t option -> string
	= function
	| None -> "P = Polyhedron(eqns = [1,0])"
	| Some p -> plot p

let to_unit : 'c t -> unit t
	= fun ph ->
	{
		eqs = List.map
			(fun (var, (cstr, _)) -> (var, (cstr,())))
			(get_eqs ph);
		ineqs = List.map
			(fun (cstr, _) -> (cstr,()))
			(get_ineqs ph);
	}


let minkowskiSetup : 'c1 Cert.t -> 'c2 Cert.t -> Var.t -> 'c1 t -> 'c2 t
-> Var.t * (('c1,'c2) Cons.discr_t) t * Var.t list * ('c1,'c2) Cons.discr_cert
	= fun factory1 factory2 nxt p1 p2 ->
	let factory = Cons.discr_factory factory1 factory2 in
	let (varNxt1, r, eqs1) = EqSet.minkowskiSetup_1 factory2 (Var.next nxt) Rtree.Nil p1.eqs in
	let (varNxt2, r, eqs2) = EqSet.minkowskiSetup_2 factory1 (Var.next nxt) Rtree.Nil p2.eqs in
	let (varNxt3, r, ineqs1) = IneqSet.minkowskiSetup_1 factory2 varNxt2 r p1.ineqs in
	let (varNxt4, r, ineqs2) = IneqSet.minkowskiSetup_2 factory1 varNxt3 r p2.ineqs in
	let eqs = List.append eqs1 eqs2 in
	let ineqs = List.concat [ineqs1; ineqs2] in
	let vars =
		Rtree.fold (fun _ a -> function None -> a | Some x -> x::a) [] r
	in
	(varNxt4, {ineqs = ineqs; eqs = eqs}, vars, factory)

let minkowskiSub: 'c1 Cert.t -> 'c2 Cert.t -> Var.t -> 'c1 t -> 'c2 t -> 'c1 t * 'c2 t
	= fun factory1 factory2 nxtVar p1 p2 ->
	let (nxtVar1, p0, vars, factory) = minkowskiSetup factory1 factory2 nxtVar p1 p2 in
	let p = projectMSub factory nxtVar1 p0 vars in
	split_certificates factory1 factory2 p

let minkowski : 'c1 Cert.t -> 'c2 Cert.t -> 'c1 t -> 'c2 t -> 'c1 t * 'c2 t
	= fun factory1 factory2 p1 p2 ->
	let nxt = Var.Set.union (varSet p1) (varSet p2)
		|> Var.horizon
	in
	minkowskiSub factory1 factory2 nxt p1 p2

let get_regions_from_point : 'c Cert.t -> 'c t -> Vec.t -> unit t list
    = fun factory p point ->
    let regions = IneqSet.get_regions_from_point factory p.ineqs point
    and eqs = List.map (fun (var, (cstr,_)) -> (var, (cstr, ()))) p.eqs
    in
    List.map (fun reg -> {eqs = eqs ; ineqs = reg}) regions

let get_regions : 'c Cert.t -> 'c t -> unit t list
    = fun factory p ->
	Debug.log DebugTypes.Title (lazy "Getting regions");
	Debug.log DebugTypes.MInput (lazy (Printf.sprintf "P = %s"
			(to_string_raw p)))
	;
    Profile.start "get_regions";
    let point = match Opt.getAsg_raw (List.map Cons.get_c p.ineqs) with
        | None -> Stdlib.failwith "Pol.get_regions"
        | Some pl -> (Vec.M.map Vec.ofSymbolic pl)
    in
    let regions = IneqSet.get_regions_from_point factory p.ineqs point
    and eqs = List.map (fun (var, (cstr,_)) -> (var, (cstr, ()))) p.eqs
    in
    let res = List.map (fun reg -> {eqs = eqs ; ineqs = reg}) regions in
    Profile.stop "get_regions";
    res

let size : 'c t -> Scalar.Rat.t option
    = fun p ->
    Debug.log DebugTypes.Title (lazy "Size");
	Debug.log DebugTypes.MInput (lazy (Printf.sprintf "P = %s"
    	(to_string_raw p)));
    let res = match Opt.getAsg_and_value_raw (List.map Cons.get_c p.ineqs) with
    | Some (_, None) -> None
    | None -> None
    | Some (_, Some value) -> Some value
    in
    Debug.log DebugTypes.MOutput (lazy
        (match res with
            | None -> "none"
            | Some r -> Printf.sprintf "%s: %f" (Scalar.Rat.to_string r) (Scalar.Rat.to_float r)));
    res

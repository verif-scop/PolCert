module Cs = Cstr.Rat.Positive
module Vec = Cs.Vec
module V = Vec.V

module Defs
  = struct

(** Order matters: the variable defined by the last element of the list
does not appears in the definitions before it, but the variable
defined by the head of the list can appear in the definitions after it. *)
    type t = (V.t * Vec.t) list

    let empty : t
      = []

    let add : V.t -> Vec.t -> t -> t
      = fun x v d ->
      let v' =
	List.fold_right (fun (x', xdef') v' -> Vec.elim x' xdef' v') d v
      in
      if Vec.equal Vec.nil v'
      then Stdlib.failwith "Splx.Defs.add"
      else (x, v') :: d

    let rm : V.t -> t -> t
      = fun x l -> List.filter (fun (x', _) -> V.cmp x x' <> 0) l

    let getVars : t -> V.Set.t
      = fun d -> List.map Stdlib.fst d |> V.Set.of_list

    let getDef : t -> V.t -> Vec.t option
      = fun d x ->
      List.fold_right
	(fun (x', xdef') ->
	 function
	 | None -> if V.cmp x x' = 0 then Some xdef' else None
	 | Some def -> Some (Vec.elim x' xdef' def)
	)
	d None

    let fold : ('a -> V.t * Vec.t -> 'a) -> 'a -> t -> 'a
      = List.fold_left

    let rewrite : t -> Vec.t -> Vec.t
      = List.fold_right (fun (x, xdef) v' -> Vec.elim x xdef v')

    let to_string : (V.t -> string) -> t -> string
      = fun varPr d ->
      List.rev_map (fun (x, d) -> Printf.sprintf "%s: %s = 0" (varPr x) (Vec.to_string varPr d)) d
      |> String.concat "\n"

end

type bnd_t = { id: int; scale: Cs.Vec.Coeff.t; bv: Scalar.Symbolic.t }
let get_id x = x.id
let get_scale x = x.scale
let get_bv x = x.bv

let bnd_equal : bnd_t -> bnd_t -> bool
  = fun b1 b2 ->
  b1.id = b2.id &&
    Cs.Vec.Coeff.cmp b1.scale b2.scale = 0 &&
      Scalar.Symbolic.cmp b1.bv b2.bv = 0

let obnd_equal : bnd_t option -> bnd_t option -> bool
  = fun ob1 ob2 ->
  match ob1, ob2 with
  | None, None -> true
  | Some _, None
  | None, Some _ -> false
  | Some b1, Some b2 -> bnd_equal b1 b2

type state_t = { v: Scalar.Symbolic.t; low: bnd_t option; up: bnd_t option }
let get_low x = x.low
let get_up x = x.up
let get_v x = x.v

let state_equal : state_t -> state_t -> bool
  = fun st1 st2 ->
  Scalar.Symbolic.cmp st1.v st2.v = 0 &&
    obnd_equal st1.low st2.low &&
      obnd_equal st1.up st2.up

type bck_t =
| Ok
| KoL of Scalar.Symbolic.t
| KoU of Scalar.Symbolic.t

module Witness = struct
	type t = (int * Cs.Vec.Coeff.t) list
	
	let to_string : t -> string
		= function
		| [] -> "empty"
		| _::_ as l ->
			let pr (i, n) = Printf.sprintf "%s*(%i)" (Cs.Vec.Coeff.to_string n) i in
			String.concat " + " (List.map pr l)
	
	let cmp (i1,_) (i2,_) =
		match Stdlib.compare i1 i2 with
		| 0 -> invalid_arg "Cert.cmp"
		| n -> n

	let sort a = List.sort cmp a
	
	let equal : t -> t -> bool
		= fun f1 f2  ->
		List.length f1 = List.length f2 &&
		List.for_all2 (fun (i1, n1) (i2, n2) -> i1 = i2 && Cs.Vec.Coeff.cmp n1 n2 = 0)
			(sort f1) (sort f2)
end

type witness_t = Witness.t

type whatnext_t = NonBasic of V.t | UnsatSplx of witness_t

type 'a mayUnsatT
= IsOk of 'a | IsUnsat of witness_t

type t = {
	mat: (Vec.t option) Rtree.t;
	state: state_t Rtree.t;
	vars : V.Set.t;
	defs : Defs.t;
	nxt: V.t
}

let get_mat x = x.mat
let get_state x = x.state
let getVars = fun x -> x.vars
let get_nxt x = x.nxt

let prBnd = function
	| None -> "None"
	| Some b -> Printf.sprintf "Some {id = %i; scale = %s; bv = %s}" b.id (Cs.Vec.Coeff.to_string b.scale) (Scalar.Symbolic.to_string b.bv)

let prSt st = Printf.sprintf "{v = %s; low = %s; up = %s}" (Scalar.Symbolic.to_string st.v) (prBnd st.low) (prBnd st.up)

let prState: (V.t -> string) -> state_t Rtree.t -> string
= fun varPr state ->
	let pr st x = Printf.sprintf "%s: %s" x (prSt st) in
	Rtree.to_string "\n" pr varPr state

let prMat: (V.t -> string) -> Vec.t option Rtree.t -> string
= fun varPr mat ->
	let pr c x =
		match c with
		| None -> ""
		| Some v -> Printf.sprintf "%s: %s = 0" x (Vec.to_string varPr v)
	in
	Rtree.to_string "\n" pr varPr mat

let pr: (V.t -> string) -> t -> string
= fun varPr s ->
  Printf.sprintf "matrix:\n%s\ndefinitions:\n%s\nstate:\n%s\n"
		 (prMat varPr s.mat)
		 (Defs.to_string varPr s.defs)
		 (prState varPr s.state)

(** [computeSymbolic st x v] computes the value of the variable [x],
considering it is defined by the constraint [v] and that the variables
have the values given in [st]. *)
let computeSymbolic : state_t Rtree.t -> V.t -> Vec.t -> Scalar.Symbolic.t
  = let dot : state_t Rtree.t -> Vec.t -> Scalar.Symbolic.t
      = let rec tmul : state_t Rtree.t -> Vec.t -> Scalar.Symbolic.t Rtree.t
	  = fun t v ->
	  match t, v with
	  | Rtree.Nil, _
	  | _, Rtree.Nil -> Rtree.Nil
	  | Rtree.Sub (tl, tn, tr), Rtree.Sub (vl, vn, vr) ->
	     Rtree.Sub (tmul tl vl, Scalar.Symbolic.mulr vn tn.v, tmul tr vr)
	in
	fun t v -> Rtree.fold (fun _ -> Scalar.Symbolic.add) Scalar.Symbolic.z (tmul t v)
    in
    fun st x v -> Vec.set v x Cs.Vec.Coeff.z |> Vec.neg |> dot st

let elimBasicVars : t -> Vec.t -> Vec.t
  = let getBasicVars : t -> V.Set.t
      = fun sx ->
      Rtree.mskBuild (function None -> false | Some _ -> true) [sx.mat]
      |> Rtree.pathsGet
    in
    fun sx v ->
    V.Set.fold
      (fun x v' ->
       match Rtree.get None sx.mat x with
       | None -> Stdlib.failwith "Splx.elimBasicVars"
       | Some vx -> Vec.elim x vx v'
      )
      (getBasicVars sx) v

let insertBack : V.t -> t -> t
  = fun x sx ->
  match Defs.getDef sx.defs x with
  | None -> sx
  | Some v ->
     let v' = elimBasicVars sx v in
     {sx with
       mat = Rtree.set None sx.mat x (Some v');
       defs = Defs.rm x sx.defs;
       state =
	 let s = Rtree.get {v = Scalar.Symbolic.z; low = None; up = None} sx.state x in
	 Rtree.set {v = Scalar.Symbolic.z; low = None; up = None}
		   sx.state x {s with v = computeSymbolic sx.state x v'}
     }

let bndMax : bnd_t -> bnd_t -> bnd_t
= fun b b' -> if Scalar.Symbolic.cmp b.bv b'.bv < 0 then b' else b

let bndMin : bnd_t -> bnd_t -> bnd_t
= fun b b' -> if Scalar.Symbolic.cmp b.bv b'.bv > 0 then b' else b

let mergeB : state_t -> state_t -> state_t
= fun st1 st2 ->
	let l =
		match st1.low, st2.low with
		| l, None | None, l -> l
		| Some l1, Some l2 -> Some (bndMax l1 l2)
	in
	let u =
		match st1.up, st2.up with
		| u, None | None, u -> u
		| Some u1, Some u2 -> Some (bndMin u1 u2)
	in
	{st1 with low = l; up = u}

let setSymbolic ve st =
	let rec acc a = function
		| Rtree.Nil, _ | _, Rtree.Nil -> a
		| Rtree.Sub (l1, n1, r1), Rtree.Sub (l2, st2, r2) ->
			let a1 = Scalar.Symbolic.sub a (Scalar.Symbolic.mulr n1 st2.v) in
			acc (acc a1 (l1, l2)) (r1, r2)
	in
	acc Scalar.Symbolic.z (ve, st)

type fitBndT
= FitBnd of Scalar.Symbolic.t * state_t | BndUnsat of witness_t

let fitBnd : state_t -> fitBndT
= fun st ->
	match st.low, st.up with
	| None, None -> FitBnd (Scalar.Symbolic.z, st)
	| Some l, None ->
		if Scalar.Symbolic.cmp st.v l.bv < 0
		then FitBnd (Scalar.Symbolic.sub l.bv st.v, {st with v = l.bv})
		else FitBnd (Scalar.Symbolic.z, st)
	| None, Some u ->
		if Scalar.Symbolic.cmp u.bv st.v < 0
		then FitBnd (Scalar.Symbolic.sub u.bv st.v, {st with v = u.bv})
		else FitBnd (Scalar.Symbolic.z, st)
	| Some l, Some u ->
		if Scalar.Symbolic.cmp l.bv u.bv > 0
		then BndUnsat [l.id, l.scale; u.id, u.scale]
		else
			if Scalar.Symbolic.cmp st.v l.bv < 0
			then FitBnd (Scalar.Symbolic.sub l.bv st.v, {st with v = l.bv})
			else
				if Scalar.Symbolic.cmp u.bv st.v < 0
				then FitBnd (Scalar.Symbolic.sub u.bv st.v, {st with v = u.bv})
				else FitBnd (Scalar.Symbolic.z, st)

let rec incrupdate: Scalar.Symbolic.t -> V.t -> Vec.t option Rtree.t -> state_t Rtree.t -> state_t Rtree.t
  = fun d xN m st ->
  match m, st with
  | Rtree.Nil, rt -> rt
  | Rtree.Sub _, Rtree.Nil -> failwith "Splx.incrupdate"
  | Rtree.Sub (l1, n1, r1), Rtree.Sub (l2, n2, r2) ->
     let n =
       match n1 with
       | None -> n2
       | Some cons ->
	  let n = Vec.get cons xN in
	  {n2 with v = Scalar.Symbolic.sub n2.v (Scalar.Symbolic.mulr n d)}
     in
     Rtree.Sub (incrupdate d xN l1 l2, n, incrupdate d xN r1 r2)

let mkBnd id (c: Cs.t) (a: Cs.Vec.Coeff.t): state_t =
	let b: Cs.Vec.Coeff.t = Cs.Vec.Coeff.div (Cs.get_c c) a in
	let aZ = Cs.Vec.Coeff.cmpz a in
	if aZ = 0 then
		invalid_arg "Splx.mkBnd"
	else
		match Cs.get_typ c with
		| Cstr.Eq ->
			let l = {id = id; scale = Cs.Vec.Coeff.inv (Cs.Vec.Coeff.neg a); bv = Scalar.Symbolic.ofRat b} in
			let u = {id = id; scale = Cs.Vec.Coeff.inv a; bv = Scalar.Symbolic.ofRat b} in
			{v = Scalar.Symbolic.z; low = Some l; up = Some u}
		| Cstr.Le ->
			if aZ < 0 then
				let u = {id = id; scale = Cs.Vec.Coeff.inv a; bv = Scalar.Symbolic.ofRat b} in
				{v = Scalar.Symbolic.z; low = None; up = Some u}
			else
				let l = {id = id; scale = Cs.Vec.Coeff.inv (Cs.Vec.Coeff.neg a); bv = Scalar.Symbolic.ofRat b} in
				{v = Scalar.Symbolic.z; low = Some l; up = None}
		| Cstr.Lt ->
			if aZ < 0 then
				let u = {id = id; scale = Cs.Vec.Coeff.inv a; bv = Scalar.Symbolic.ndelta b} in
				{v = Scalar.Symbolic.z; low = None; up = Some u}
			else
				let l = {id = id; scale = Cs.Vec.Coeff.inv (Cs.Vec.Coeff.neg a); bv = Scalar.Symbolic.pdelta b} in
				{v = Scalar.Symbolic.z; low = Some l; up = None}

let add : t -> int * Cs.t -> t mayUnsatT
=	let boundVar : t -> int -> Cs.t -> V.t -> t mayUnsatT
	= fun sx id c x ->
		let a = Vec.get (Cs.get_v c) x in
		let oBnd = Rtree.get {v = Scalar.Symbolic.z; low = None; up = None} sx.state x in
		match fitBnd (mergeB oBnd (mkBnd id c a)) with
		| BndUnsat w -> IsUnsat w
		| FitBnd (delta, bnd') ->
			let st =
			  Rtree.set {v = Scalar.Symbolic.z; low = None; up = None} sx.state x bnd'
			  |> incrupdate delta x sx.mat
			in
			IsOk (insertBack x {sx with state = st})
	in
	let constrain : t -> int -> Cs.t -> t
	= fun s id c ->
		let nCons =
		  Vec.set (Vec.neg (Cs.get_v c)) s.nxt Cs.Vec.Coeff.u
		  |> Defs.rewrite s.defs
		  |> elimBasicVars s
		in
		let nVState = {(mkBnd id c Cs.Vec.Coeff.u) with v = setSymbolic nCons s.state} in
		let nMat = Rtree.set None s.mat s.nxt (Some nCons) in
		let nState: state_t Rtree.t
		=	let stNil: state_t = {v = Scalar.Symbolic.z; low = None; up = None} in
			(* XXX: check how the state is handled, sparse or not *)
			let rec fill: state_t Rtree.t -> Vec.t -> state_t Rtree.t
			= fun st v ->
				match v, st with
				| Rtree.Nil, (_ as st') -> st'
				| Rtree.Sub (l, _, r), Rtree.Nil ->
					Rtree.Sub (fill Rtree.Nil l, stNil, fill Rtree.Nil r)
				| Rtree.Sub (lv, _, rv), Rtree.Sub (ls, ns, rs) ->
					Rtree.Sub (fill ls lv, ns, fill rs rv)
			in
			fill (Rtree.set stNil s.state s.nxt nVState) (Cs.get_v c)
		in
		{s with
		  mat = nMat;
		  state = nState;
		  nxt = V.next s.nxt
		}
	in
	let handleTriv : int -> Cs.t -> t -> t mayUnsatT
	= fun i c sx ->
		match Cs.tellProp c with
		| Cs.Trivial -> IsOk sx
		| Cs.Contrad -> IsUnsat [i, Cs.Vec.Coeff.u]
		| Cs.Nothing -> Stdlib.failwith "Splx.add"
	in
	fun s (id, c) ->
	let xs = Cs.getVars [c] in
	let s' = {s with vars = V.Set.union s.vars xs} in
	match V.Set.cardinal xs with
	| 0 -> handleTriv id c s'
	| 1 -> V.Set.choose xs |> boundVar s' id c
	| _ -> IsOk (constrain s' id c)

let addAcc : t mayUnsatT -> int * Cs.t -> t mayUnsatT
= function
	| IsOk sx -> add sx
	| IsUnsat _ as r -> fun _ -> r

let mk: V.t -> (int * Cs.t) list -> t mayUnsatT
= fun lim l ->
	let empty = {
	    mat = Rtree.Nil;
	    state = Rtree.Nil;
	    vars = V.Set.empty;
	    defs = Defs.empty;
	    nxt = lim
	  }
	in
	List.fold_left (fun s c -> addAcc s c) (IsOk empty) l

let pivot m xB xN =
	let xNCons =
		let xBCons =
			match Rtree.get None m xB with
			| None -> invalid_arg "Splx.pivot"
			| Some cons -> cons
		in
		Vec.divc xBCons (Vec.get xBCons xN)
	in
	let elim = function
		| None -> None
		| Some cons -> Some (Vec.elim xN xNCons cons)
	in
	let m1 = Rtree.map elim (Rtree.set None m xB None) in
	Rtree.set None m1 xN (Some xNCons)

let _in_bound (b: state_t): bck_t =
	match b.low with
	| Some l when Scalar.Symbolic.cmp l.bv b.v > 0 -> KoL l.bv
	| Some _ | None ->
		match b.up with
		| Some u when Scalar.Symbolic.cmp b.v u.bv > 0 -> KoU u.bv
		| Some _ | None -> Ok

type chgDirT = HasToIncr | HasToDecr

type choiceT
= {var : V.t; vec : Vec.t; st : state_t}

let fromLeft : choiceT option -> choiceT option
= function None -> None | Some c -> Some {c with var = V.XO c.var}

let fromRight : choiceT option -> choiceT option
= function None -> None | Some c -> Some {c with var = V.XI c.var}

module type Strategy
= sig

	val pickBasic : t -> choiceT option

	val pickNBasic : t -> chgDirT -> Vec.t -> whatnext_t

end

module Bland : Strategy
= struct

	let pickBasic : t -> choiceT option
	= fun s ->
		let elect : Vec.t option -> state_t -> choiceT option
		= fun mc st ->
			match mc with
			| None -> None
			| Some c ->
				match _in_bound st with
				| Ok -> None
				| KoL _
				| KoU _ -> Some {var = V.XH; vec = c; st = st}
		in
		let rec find : Vec.t option Rtree.t -> state_t Rtree.t -> choiceT option
		= fun m stree ->
			match m, stree with
			| Rtree.Nil, _
			| _, Rtree.Nil -> None
			| Rtree.Sub (l1, mc, r1), Rtree.Sub (l2, st, r2) ->
				match elect mc st with
				| Some _ as r -> r
				| None ->
					match find l1 l2 with
					| Some _ as r -> fromLeft r
					| None -> fromRight (find r1 r2)
		in
		find s.mat s.state

	let pickNBasic s d xiv =
		let tryincr w a st =
			match st.up with
			| None -> NonBasic V.XH
			| Some u when Scalar.Symbolic.cmp u.bv st.v > 0 -> NonBasic V.XH
			| Some u -> UnsatSplx ((u.id, Cs.Vec.Coeff.mul u.scale a)::w)
		in
		let trydecr w a st =
			match st.low with
			| None -> NonBasic V.XH
			| Some l when Scalar.Symbolic.cmp l.bv st.v < 0 -> NonBasic V.XH
			| Some l -> UnsatSplx ((l.id, Cs.Vec.Coeff.mul l.scale a)::w)
		in
		let (fpos, fneg) =
			match d with
			| HasToDecr -> (tryincr, trydecr)
			| HasToIncr -> (trydecr, tryincr)
		in
		let f w a st =
			match Cs.Vec.Coeff.cmpz a with
			| 0 -> UnsatSplx w
			| n when n < 0 -> fpos w a st
			| _ -> fneg w (Cs.Vec.Coeff.neg a) st
		in
		let rec find a0 ve st =
			match ve, st with
			| Rtree.Nil, _ -> UnsatSplx a0
			| Rtree.Sub _, Rtree.Nil -> NonBasic V.XH
			| Rtree.Sub (l1, n1, r1), Rtree.Sub (l2, n2, r2) ->
				match f a0 n1 n2 with
				| NonBasic _ as r -> r
				| UnsatSplx a1 ->
					match find a1 l1 l2 with
					| NonBasic v -> NonBasic (V.XO v)
					| UnsatSplx a2 ->
						match find a2 r1 r2 with
						| NonBasic v -> NonBasic (V.XI v)
						| UnsatSplx _ as r -> r
		in
		find [] xiv s.state

end

module Steep : Strategy
= struct

	type indepChoiceT
	= Bounded of V.t * Scalar.Symbolic.t | Unbounded of V.t

	let pickBasic : t -> choiceT option
	= fun s ->
		let candidate : Vec.t option -> state_t -> choiceT option
		= function
			| None -> fun _ -> None
			| Some ve -> fun st ->
				match _in_bound st with
				| Ok -> None
				| KoL _ | KoU _ -> Some {var = V.XH; vec = ve; st = st}
		in
		let score: choiceT -> Scalar.Symbolic.t
		= fun c ->
			match _in_bound c.st with
			| KoL l -> Scalar.Symbolic.sub l c.st.v
			| KoU u -> Scalar.Symbolic.sub c.st.v u
			| Ok -> Stdlib.failwith "Splx.pickbasic_steep.score"
		in
		let choose : choiceT option -> choiceT option -> choiceT option
		= function
			| None -> fun oc -> oc
			| Some c as oc -> function
				| None -> oc
				| Some c' as oc'-> if Scalar.Symbolic.cmp (score c) (score c') < 0 then oc' else oc
		in
		let rec find: Vec.t option Rtree.t -> state_t Rtree.t -> choiceT option
		= fun m st ->
			match m, st with
			| Rtree.Nil, _ | _, Rtree.Nil -> None
			| Rtree.Sub (l1, n1, r1), Rtree.Sub (l2, n2, r2) ->
				let ocl = fromLeft (find l1 l2) in
				let ocr = fromRight (find r1 r2) in
				choose (choose ocl ocr) (candidate n1 n2)
		in
		find s.mat s.state

	let pickNBasic : t -> chgDirT -> Vec.t -> whatnext_t
	=	let choose : indepChoiceT option -> indepChoiceT option -> indepChoiceT option
		= function
			| None -> fun c -> c
			| Some (Unbounded _) as oc -> fun _ -> oc
			| Some (Bounded (_, sc)) as oc -> function
				| None -> oc
				| Some (Unbounded _) as oc' -> oc'
				| Some (Bounded (_, sc')) as oc' ->
					if Scalar.Symbolic.cmp sc sc' < 0 then oc' else oc
		in
		let tryDecr : state_t -> indepChoiceT option
		= fun st ->
			match st.low with
			| None -> Some (Unbounded V.XH)
			| Some l ->
				if Scalar.Symbolic.cmp l.bv st.v < 0
				then Some (Bounded (V.XH, Scalar.Symbolic.sub st.v l.bv)) (* XXX: coefficient *)
				else None
		in
		let tryIncr : state_t -> indepChoiceT option
		= fun st ->
			match st.up with
			| None -> Some (Unbounded V.XH)
			| Some u ->
				if Scalar.Symbolic.cmp st.v u.bv < 0
				then Some (Bounded (V.XH, Scalar.Symbolic.sub u.bv st.v)) (* XXX: coefficient *)
				else None
		in
		let candidate : chgDirT -> Cs.Vec.Coeff.t -> state_t -> indepChoiceT option
		= function
			| HasToIncr -> fun a st ->
				let asign = Cs.Vec.Coeff.cmpz a in
				if asign = 0 then None
				else
					if asign < 0 then tryDecr st
					else tryIncr st
			| HasToDecr -> fun a st ->
				let asign = Cs.Vec.Coeff.cmpz a in
				if asign = 0 then None
				else
					if asign < 0 then tryIncr st
					else tryDecr st
		in
		let fromLeft : indepChoiceT option -> indepChoiceT option
		= function
			| None -> None
			| Some (Unbounded x) -> Some (Unbounded (V.XO x))
			| Some (Bounded (x, sc)) -> Some (Bounded (V.XO x, sc))
		in
		let fromRight : indepChoiceT option -> indepChoiceT option
		= function
			| None -> None
			| Some (Unbounded x) -> Some (Unbounded (V.XI x))
			| Some (Bounded (x, sc)) -> Some (Bounded (V.XI x, sc))
		in
		let rec witness : chgDirT -> Vec.t -> state_t Rtree.t -> witness_t
		=	let bound : Cs.Vec.Coeff.t -> chgDirT -> state_t -> bnd_t option
			= fun a ->
				let asign = Cs.Vec.Coeff.cmpz a in
				if asign = 0 then fun _ _ -> None
				else if asign < 0 then function
					| HasToIncr -> fun s -> s.low
					| HasToDecr -> fun s -> s.up
				else function
					| HasToIncr -> fun s -> s.up
					| HasToDecr -> fun s -> s.low
			in
			fun d v st ->
				match v, st with
				| Rtree.Nil, _ -> []
				| _, Rtree.Nil -> Stdlib.invalid_arg "Splx.picknbasic_steep"
				| Rtree.Sub (l1, a, r1), Rtree.Sub (l2, s, r2) ->
					let wl : witness_t = witness d l1 l2 in
					let wr : witness_t = witness d r1 r2 in
					match bound a d s with
					| None -> wl @ wr
					| Some b -> (b.id, Cs.Vec.Coeff.mul b.scale (Cs.Vec.Coeff.abs a)) :: (wl @ wr)
		in
		let rec find : chgDirT -> Vec.t -> state_t Rtree.t -> indepChoiceT option
		= fun d v st ->
			match v, st with
			| Rtree.Nil, _ -> None
			| Rtree.Sub _, Rtree.Nil -> Some (Unbounded V.XH)
			| Rtree.Sub (l1, n1, r1), Rtree.Sub (l2, n2, r2) ->
				let l = fromLeft (find d l1 l2) in
				let r = fromRight (find d r1 r2) in
				choose (choose l r) (candidate d n1 n2)
		in
		fun s d v ->
			match find d v s.state with
			| None -> UnsatSplx (witness d v s.state)
			| Some (Unbounded x) -> NonBasic x
			| Some (Bounded (x, _)) -> NonBasic x

end

type strategyT
= Bland | Steep

let pickBasic : strategyT -> t -> choiceT option
= function
	| Bland -> Bland.pickBasic
	| Steep -> Steep.pickBasic

let pickNBasic : strategyT -> t -> chgDirT -> Vec.t -> whatnext_t
= function
	| Bland -> Bland.pickNBasic
	| Steep -> Steep.pickNBasic

type stepT
= StepCont of t | StepSat of t | StepUnsat of witness_t

let step : strategyT -> t -> stepT
= fun strgy sx ->
	match pickBasic strgy sx with
	| None -> StepSat sx
	| Some ch ->
		let (whatNext, xival) =
			match _in_bound ch.st with
			| Ok -> Stdlib.failwith "step"
			| KoL l -> pickNBasic strgy sx HasToIncr ch.vec, l
			| KoU u -> pickNBasic strgy sx HasToDecr ch.vec, u
		in
		match whatNext with
		| UnsatSplx w -> StepUnsat w
		| NonBasic xj ->
			let xi = ch.var in
			let m = pivot sx.mat xi xj in
			let xiSt = Rtree.get {v = Scalar.Symbolic.z; low = None; up = None} sx.state xi in
			let st = Rtree.set {v=Scalar.Symbolic.z; low = None; up = None} sx.state xi {xiSt with v = xival} in
			StepCont {sx with mat = m; state = incrupdate (Scalar.Symbolic.sub xival xiSt.v) xi m st}

module Preprocessing
  = struct

    let getUnboundedVars : t -> V.Set.t
      = fun sx ->
      Rtree.mskBuild (fun st -> not (st.low = None && st.up = None)) [sx.state]
      |> Rtree.pathsGet
      |> V.Set.diff sx.vars

    let findOccurence : V.t -> t -> V.t option
      = let rec find : V.t -> (V.t -> V.t) -> Vec.t option Rtree.t -> V.t option
	  = fun x fcont ->
	  function
	  | Rtree.Nil -> None
	  | Rtree.Sub (l, o, r) ->
	     (match o with
	      | None -> None
	      | Some v ->
		 if Cs.Vec.Coeff.cmpz (Vec.get v x) <> 0
		 then Some (fcont V.XH)
		 else None)
	     |> function
	       | Some _ as r -> r
	       | None ->
		  match find x (fun x' -> fcont (V.XO x')) l with
		  | Some _ as r -> r
		  | None -> find x (fun x' -> fcont (V.XI x')) r
	in
	fun x sx -> find x (fun x' -> x') sx.mat

    let elim : V.t -> V.t -> t -> t
      = fun x xb sx ->
      let m = if x = xb then sx.mat else pivot sx.mat xb x in
      let state =
	let stb = Rtree.get {v = Scalar.Symbolic.z; low = None; up = None} sx.state xb in
	match _in_bound stb with
	| Ok -> sx.state
	| KoL v
	| KoU v ->
	   Rtree.set {v = Scalar.Symbolic.z; low = None; up = None} sx.state xb {stb with v = v}
	   |> incrupdate (Scalar.Symbolic.sub v stb.v) xb m
      in
      {sx with
	mat = Rtree.set None m x None;
	state = state;
	defs =
	  Defs.add
	    x (match Rtree.get None m x with
	       | None -> Stdlib.failwith "Splx.Preprocessing.elim"
	       | Some v -> v) sx.defs
      }

    let presimpl : t -> t
      = fun sx ->
      V.Set.fold
	(fun x sx' ->
	 match findOccurence x sx' with
	 | None -> sx'
	 | Some xb -> elim x xb sx'
	)
	(getUnboundedVars sx)
	sx

end

let check_loop : t -> t mayUnsatT
=	let chooseStrategy : int -> strategyT -> strategyT
	= fun cnt -> function
		| Bland -> Bland
		| Steep -> if cnt < 20 then Steep else Bland
	in
	let rec loop : int -> strategyT -> t -> t mayUnsatT
	= fun cnt strgy sx ->
		let strgy' = chooseStrategy cnt strgy in
		match step strgy' sx with
		| StepCont sx' -> loop (cnt+1) strgy' sx'
		| StepSat sx' -> IsOk sx'
		| StepUnsat w -> IsUnsat w
	in
	fun sx -> loop 1 Steep sx

let check : t -> t mayUnsatT
= fun sx -> check_loop (Preprocessing.presimpl sx)

let checkFromAdd : t mayUnsatT -> t mayUnsatT
= function
	| IsOk sx -> check sx
	| IsUnsat _ as u -> u

let getAsg : t -> Scalar.Symbolic.t Rtree.t
  = fun sx ->
  let state =
    Defs.fold
      (fun t' (x, v) ->
       {v = computeSymbolic t' x v;
	low = None;
	up = None
       }
       |> Rtree.set {v = Scalar.Symbolic.z; low = None; up = None} t' x
      )
      sx.state sx.defs
  in
  V.Set.fold
    (fun x t ->
     (Rtree.get {v = Scalar.Symbolic.z; low = None; up = None} state x).v
     |> Rtree.set Scalar.Symbolic.z t x
    )
    sx.vars Rtree.Nil

let compl s id =
	let f s =
		match s.low, s.up with
		| Some l, _ when l.id = id ->
			let u1 = { l with bv = Scalar.Symbolic.subdelta l.bv } in
			Some (Scalar.Symbolic.sub u1.bv s.v, { v = u1.bv; low = None; up = Some u1 })

		| _, Some u when u.id = id ->
			let l1 = { u with bv = Scalar.Symbolic.adddelta u.bv } in
			Some (Scalar.Symbolic.sub l1.bv s.v, { v = l1.bv; low = Some l1; up = None })

		| _, _ -> None
	in
	match Rtree.find f s.state with
	| None -> invalid_arg "Splx.compl"
	| Some (v, (delta, b)) ->
		let st1 = Rtree.set {v = Scalar.Symbolic.z; low = None; up = None} s.state v b in
		{s with state = incrupdate delta v s.mat st1}

let stricten : t -> int -> t mayUnsatT
=	let predUp : int -> state_t -> state_t option
	= fun id st ->
		match st.up with
		| None -> None
		| Some u -> if u.id = id && not (Scalar.Symbolic.hasDelta u.bv)
			then Some st
			else None
	in
	let pred : int -> state_t -> state_t option
	= fun id st ->
		match st.low with
		| None -> predUp id st
		| Some l -> if l.id = id && not (Scalar.Symbolic.hasDelta l.bv)
			then Some st
			else predUp id st
	in
	let tryStrictenLow : int -> bnd_t option -> bnd_t option
	= fun id -> function
		| None -> None
		| Some b as mb -> if b.id = id
			then Some {b with bv = Scalar.Symbolic.adddelta b.bv}
			else mb
	in
	let tryStrictenUp : int -> bnd_t option -> bnd_t option
	= fun id -> function
		| None -> None
		| Some b as mb -> if b.id = id
			then Some {b with bv = Scalar.Symbolic.subdelta b.bv}
			else mb
	in
	fun sx id ->
		match Rtree.find (pred id) sx.state with
		| None -> Stdlib.invalid_arg "Splx.stricten"
		| Some (x, st) ->
			let st' = {st with
				low = tryStrictenLow id st.low;
				up = tryStrictenUp id st.up
			} in
			match fitBnd st' with
			| BndUnsat w -> IsUnsat w
			| FitBnd (delta, st') ->
				let sTree = Rtree.set {v = Scalar.Symbolic.z; low = None; up = None}
					sx.state x st'
				in
				IsOk {sx with state = incrupdate delta x sx.mat sTree}

let forget s id =
	let f bnd =
		match bnd.low, bnd.up with
		| Some b, None | None, Some b when b.id = id ->
			Some (true, { bnd with low = None; up = None })

		| Some l, Some _ when l.id = id ->
			Some (false, { bnd with low = None })

		| Some _, Some u when u.id = id ->
			Some (false, { bnd with up = None })

		| _, _ -> None
	in
	match Rtree.find f s.state with
	| None -> invalid_arg "Splx.forget"
	| Some (v, (p, b)) ->
		let s1 = {s with state = Rtree.set {v = Scalar.Symbolic.z; low = None; up = None} s.state v b} in
		if not p then s1
		else
		  match Preprocessing.findOccurence v s1 with
		  | None -> s1
		  | Some xb -> Preprocessing.elim v xb s1
		  
let getAsgOpt : V.t -> (int * Cs.t) list -> Scalar.Symbolic.t Rtree.t option
	= fun horizon cstrs ->
	match mk horizon cstrs |> checkFromAdd with
	| IsUnsat _ -> None
	| IsOk sx -> Some (getAsg sx)
	
let getPointInside_cone : Cs.Vec.V.t -> Cs.t list -> Scalar.Symbolic.t Rtree.t option
	= fun horizon cstrs -> 
	let cstrs' = List.mapi
		(fun i cstr -> i, {cstr with 
		Cs.c = Cs.Vec.Coeff.sub cstr.Cs.c Cs.Vec.Coeff.u;
		Cs.typ = Cstr.Le})
		cstrs
	in
	getAsgOpt horizon cstrs'
	

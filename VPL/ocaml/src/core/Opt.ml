open Splx

type progressT = Unbnd | UpTo of Scalar.Symbolic.t | NoChange

type dirT = Incr | Decr

type actionT = Done | Move of (V.t * dirT * progressT)

type nextT = OptFinite of Scalar.Symbolic.t | OptUnbnd | GoOn of t

type optT
  = Finite of (t * Scalar.Rat.t * witness_t)
  | Sup of (t * Scalar.Rat.t * witness_t)
  | Infty

let prProgress = function
  | Unbnd -> "Unbnd"
  | UpTo v -> Printf.sprintf "UpTo %s" (Scalar.Symbolic.to_string v)
  | NoChange -> "NoChange"

let prDir = function
  | Incr -> "Incr"
  | Decr -> "Decr"

let prAction: (V.t -> string) -> actionT -> string
  = fun varPr -> function
	      | Done -> "Done"
	      | Move (v, d, bnd) -> Printf.sprintf "Move (%s, %s, %s)" (varPr v) (prDir d) (prProgress bnd)

let prNext: (V.t -> string) -> nextT -> string
  = fun varPr -> function
	      | GoOn s1 -> Printf.sprintf "GoOn\n%s\n" (pr varPr s1)
	      | OptUnbnd -> "OptUnbnd"
	      | OptFinite v1 -> Printf.sprintf "OptFinite %s" (Scalar.Symbolic.to_string v1)

let prOpt = function
  | Finite (_, n, w) -> Printf.sprintf "Finite %s, cert: %s" (Scalar.Rat.to_string n) (Witness.to_string w)
  | Sup (_, n, w) -> Printf.sprintf "Sup %s, cert: %s" (Scalar.Rat.to_string n) (Witness.to_string w)
  | Infty -> "Infty"

let tryDecr st =
  match st.low with
  | None -> Unbnd
  | Some l when Scalar.Symbolic.cmp l.bv st.v < 0 -> UpTo (Scalar.Symbolic.sub st.v l.bv)
  | Some _ -> NoChange

let tryIncr st =
  match st.up with
  | None -> Unbnd
  | Some u when Scalar.Symbolic.cmp u.bv st.v > 0 -> UpTo (Scalar.Symbolic.sub u.bv st.v)
  | Some _ -> NoChange

let pickNBasic z s =
  let rec find vec state =
    let walk l1 l2 r1 r2 =
      match find l1 l2 with
      | Move (x, dir, bnd) -> Move (V.XO x, dir, bnd)
      | Done ->
	 match find r1 r2 with
	 | Move (x, dir, bnd) -> Move (V.XI x, dir, bnd)
	 | Done -> Done
    in
    match vec, state with
    | Rtree.Nil, _ -> Done
    | Rtree.Sub (l, n, r), Rtree.Nil ->
       let nSign = Scalar.Rat.cmpz n in
       if nSign = 0 then
	 walk l Rtree.Nil r Rtree.Nil
       else
	 Move (V.XH, (if nSign < 0 then Decr else Incr), Unbnd)
    | Rtree.Sub (l1, n, r1), Rtree.Sub (l2, st, r2) ->
       let nSign = Scalar.Rat.cmpz n in
       if nSign = 0 then
	 walk l1 l2 r1 r2
       else
	 let (dir, tryFn) = if nSign < 0 then (Decr, tryDecr) else (Incr, tryIncr) in
	 match tryFn st with
	 | Unbnd | UpTo _ as b -> Move (V.XH, dir, b)
	 | NoChange -> walk l1 l2 r1 r2
  in
  match Rtree.get None s.mat z with
  | None -> invalid_arg "Opt.pickNBasic"
  | Some vec -> find (Vec.set vec z Scalar.Rat.z) s.state

let pickBasic s xN xNBnd dir =
  let choose x1 bnd1 x2 bnd2 =
    match bnd1, bnd2 with
    | NoChange, NoChange | Unbnd, Unbnd -> (x1, bnd1)
    | NoChange, Unbnd | NoChange, UpTo _ | UpTo _, Unbnd -> (x1, bnd1)
    | Unbnd, UpTo _ | Unbnd, NoChange | UpTo _, NoChange -> (x2, bnd2)
    | UpTo d1, UpTo d2 ->
       if Scalar.Symbolic.cmp d1 d2 <= 0 then
	 (x1, bnd1)
       else
	 (x2, bnd2)
  in
  let (tryPos, tryNeg) =
    match dir with
    | Incr -> (tryDecr, tryIncr)
    | Decr -> (tryIncr, tryDecr)
  in
  let rec find m st =
    match m, st with
    | Rtree.Nil, _ -> None
    | _, Rtree.Nil -> Some (V.XH, Unbnd)
    | Rtree.Sub (l1, n1, r1), Rtree.Sub (l2, n2, r2) ->
       let nN =
	 match n1 with
	 | None -> Unbnd
	 | Some cons ->
	    let aN = Vec.get cons xN in
	    match Scalar.Rat.cmpz aN with
	    | 0 -> Unbnd
	    | aSign ->
	       match (if aSign < 0 then tryPos else tryNeg) n2 with
	       | Unbnd | NoChange as bnd -> bnd
	       | UpTo d -> UpTo (Scalar.Symbolic.divr d (Scalar.Rat.abs aN))
       in
       let maybeL = find l1 l2 in
       let maybeR = find r1 r2 in
       match maybeL, maybeR with
       | None, None -> Some (V.XH, nN)
       | Some (xL, nL), None -> Some (choose (V.XO xL) nL V.XH nN)
       | None, Some (xR, nR) -> Some (choose (V.XI xR) nR V.XH nN)
       | Some (xL, nL), Some (xR, nR) ->
	  let (xS, nS) = choose (V.XO xL) nL (V.XI xR) nR in
	  Some (choose xS nS V.XH nN)
  in
  match find s.mat s.state with
  | None -> (xN, xNBnd)
  | Some (x, xBnd) -> choose xN xNBnd x xBnd

let step z s =
  match pickNBasic z s with
  | Done ->
     let zSt = Rtree.get {v = Scalar.Symbolic.z; low = None; up = None} s.state z in
     OptFinite zSt.v
  | Move (xN, dir, b) ->
     let (xB, xNBnd) = pickBasic s xN b dir in
     match xNBnd with
     | Unbnd -> OptUnbnd
     | NoChange -> GoOn {s with mat = pivot s.mat xB xN}
     | UpTo delta ->
	let xNSt = Rtree.get {v = Scalar.Symbolic.z; low = None; up = None} s.state xN in
	let nSt =
	  let upSymbolic = match dir with Incr -> Scalar.Symbolic.add | Decr -> Scalar.Symbolic.sub in
	  Rtree.set {v = Scalar.Symbolic.z; low = None; up = None} s.state xN {xNSt with v = upSymbolic xNSt.v delta}
	in
	let m =
	  if xB = xN then
	    s.mat
	  else
	    pivot s.mat xB xN
	in
	let d = function Incr -> delta | Decr -> Scalar.Symbolic.sub Scalar.Symbolic.z delta in
	GoOn {s with mat = m; state = incrupdate (d dir) xN s.mat nSt}

let setObj s obj =
  let cons = Vec.set (Vec.neg obj) s.nxt Scalar.Rat.u in
  let zSt = {v = setSymbolic cons s.state; low = None; up = None} in
  let nMat = Rtree.set None s.mat s.nxt (Some cons) in
  let nState = Rtree.set {v = Scalar.Symbolic.z; low = None; up = None} s.state s.nxt zSt in
  (s.nxt,
   {s with
     mat = nMat;
     state = nState;
     nxt = V.next s.nxt
  })

let mkCert z objCons state0 =
  let rec build cert vec state =
    match vec, state with
    | Rtree.Nil, _ -> cert
    | Rtree.Sub (_, _, _), Rtree.Nil -> invalid_arg "Opt.mkCert"
    | Rtree.Sub (l1, n, r1), Rtree.Sub (l2, st, r2) ->
       let cert1 =
	 (* XXX: what happens when fiddling with the sign of the coefficient when equations sneak in? *)
	 let nSign = Scalar.Rat.cmpz n in
	 if nSign = 0 then
	   cert
	 else if nSign < 0 then
	   match st.low with
	   | None -> invalid_arg "Opt.mkCert"
	   | Some l -> (l.id, Scalar.Rat.mul l.scale n)::cert
	 else
	   match st.up with
	   | None -> invalid_arg "Opt.mkCert"
	   | Some u -> (u.id, Scalar.Rat.mul u.scale (Scalar.Rat.neg n))::cert
       in
       let cert2 = build cert1 l1 l2 in
       build cert2 r1 r2
  in
  build [] (Vec.set objCons z Scalar.Rat.z) state0

let max : t -> Vec.t -> optT mayUnsatT
  = fun s0 obj ->
  let (z, s1) = setObj s0 obj in
  let rec optimize s =
    match step z s with
    | GoOn s1 -> optimize s1
    | OptUnbnd -> Infty
    | OptFinite o ->
       let objCons =
	 match Rtree.get None s.mat z with
	 | None -> failwith "Opt.max"
	 | Some c -> c
       in
       match Scalar.Rat.cmpz (Scalar.Symbolic.get_d o) with
       | 0 -> Finite (s, Scalar.Symbolic.get_v o, mkCert z objCons s.state)
       | n when n > 0 -> Sup (s, Scalar.Symbolic.get_v o, mkCert z objCons s.state)
       | _ -> failwith "Opt.max"
  in
  match check_loop s1 with
  | IsOk sx -> IsOk (optimize sx)
  | IsUnsat _ as u -> u

let max' : t mayUnsatT -> Vec.t -> optT mayUnsatT
  = function
  | IsUnsat _ as u -> fun _ -> u
  | IsOk sx -> fun obj -> max sx obj

let getAsg_and_value : V.t -> (int * Cs.t) list -> (Vector.Symbolic.Positive.t * Scalar.Rat.t option) option
	= let build_epsilon : V.t -> (int * Cs.t) list -> (int * Cs.t) list * Vec.t
		= fun horizon cstrs ->
			let epsilon = horizon in
			let obj = Cs.Vec.mk [Cs.Vec.Coeff.u, epsilon] in
			let cstrs' =
				(2500, Cs.le [Scalar.Rat.u, epsilon] (Scalar.Rat.of_float 100000.)):: (* TODO : changer ça! *)
				(List.map
					(fun (i,cstr) ->
						i,
						{  cstr with
							Cs.typ = Cstr.Le;
							Cs.v = Cs.Vec.set cstr.Cs.v epsilon Cs.Vec.Coeff.u})
					cstrs)
			in
			(cstrs', obj)
	in
	fun horizon cstrs ->
	let (cstrs', obj) = build_epsilon horizon cstrs in
	let horizon' = V.next horizon in (* car on a ajouté la variable epsilon *)
	let sx = mk horizon' cstrs' in
	match max' sx obj with
	| IsUnsat _ -> None
	| IsOk Infty -> begin
        match getAsgOpt horizon cstrs with
        | Some point -> Some (point, None)
        | None -> None
        end
	| IsOk (Sup (sx,obj_value,_)) | IsOk (Finite (sx,obj_value,_)) ->
		let point = Vector.Symbolic.Positive.set (getAsg sx) horizon Scalar.Symbolic.z in
		Some (point, Some obj_value)

let getAsg : V.t -> (int * Cs.t) list -> Vector.Symbolic.Positive.t option
	= fun horizon cstrs ->
	match getAsg_and_value horizon cstrs with
    | None -> None
    | Some (point,_) -> Some point

let getAsg_raw : Cs.t list -> Vector.Symbolic.Positive.t option
	= fun cstrs ->
	let horizon = Cs.getVars cstrs
		|> Cs.Vec.V.horizon
	in
	let cstrs_id = List.mapi (fun i cstr -> (i,cstr)) cstrs in
	getAsg horizon cstrs_id

let getAsg_and_value_raw : Cs.t list -> (Vector.Symbolic.Positive.t * Scalar.Rat.t option) option
	= fun cstrs ->
	let horizon = Cs.getVars cstrs
		|> Cs.Vec.V.horizon
	in
	let cstrs_id = List.mapi (fun i cstr -> (i,cstr)) cstrs in
	getAsg_and_value horizon cstrs_id

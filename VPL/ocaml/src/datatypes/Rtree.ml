(** This module is the basis of the VPL.
The type [t] defined below is used in almost every module.
It is an association table of variable identifiers (see {! V.t}) to some data. *)

module V = Var.Positive

type 'n t =
| Nil
| Sub of ('n t * 'n * 'n t)

type 'n rtree_t = 'n t

let empty = Nil

let is_empty = function
	| Nil -> true
	| _ -> false

let rec get (z: 'n) (rt: 'n rtree_t) (v: V.t) =
	match rt with
	| Nil -> z
	| Sub (l, n, r) ->
		match v with
		| V.XH -> n
		| V.XO t -> get z l t
		| V.XI t -> get z r t

let set (z: 'n) (rt0: 'n rtree_t) (v0: V.t) (n0: 'n) =
	let rec _set rt v: 'n rtree_t =
		match rt, v with
		| Nil, V.XH -> Sub (Nil, n0, Nil)
		| Sub (l, _, r), V.XH -> Sub (l, n0, r)
		| Nil, V.XO t -> Sub (_set Nil t, z, Nil)
		| Sub (l, n, r), V.XO t -> Sub (_set l t, n, r)
		| Nil, V.XI t -> Sub (Nil, z, _set Nil t)
		| Sub (l, n, r), V.XI t -> Sub (l, n, _set r t)
	in
		_set rt0 v0

let mk z l = List.fold_left (fun a (x, n) -> set z a x n) Nil l

let map (f: 'n -> 'm) (rt0: 'n rtree_t) =
	let rec _map rt =
		match rt with
		| Nil -> Nil
		| Sub (l, n, r) -> Sub (_map l, f n, _map r)
	in
		_map rt0

let map_cut (f: 'n -> 'm) (nul: 'm -> bool) (rt0: 'n rtree_t) =
	let cut : 'm rtree_t -> 'm -> 'm rtree_t -> 'm rtree_t 
		= fun l m r ->
		if nul m && l = Nil && r = Nil then
			Nil
		else
			Sub (l, m, r)
	in
	let rec _map rt =
		match rt with
		| Nil -> Nil
		| Sub (l, n, r) -> cut (_map l) (f n) (_map r)
	in
	_map rt0
		
	
let rec fold_rec (f: V.t -> 'a -> 'n -> 'a) (a: 'a) (rt: 'n rtree_t) (v:V.t) : 'a =
	match rt with
	| Nil -> a
	| Sub (l, n, r) -> fold_rec f (fold_rec f (f v a n) l (V.XO v)) r (V.XI v)

let fold (f: V.t -> 'a -> 'n -> 'a) (a: 'a) (rt: 'n rtree_t): 'a =
	fold_rec f a rt V.XH

let rec fold2_rec (f: V.t -> 'a -> 'n -> 'm -> 'a) (a: 'a) (rt1: 'n rtree_t) (rt2: 'm rtree_t) (v:V.t) : 'a =
	match rt1,rt2 with
	| Nil,_ | _,Nil-> a
	| Sub (l1, n, r1), Sub (l2,m,r2) -> fold2_rec f (fold2_rec f (f v a n m) l1 l2 (V.XO v)) r1 r2 (V.XI v)
	
let rec fold2 (f: V.t -> 'a -> 'n -> 'm -> 'a) (a: 'a) (rt1: 'n rtree_t) (rt2: 'm rtree_t): 'a =
	fold2_rec f a rt1 rt2 V.XH

let rec fold2_opt_rec (f: V.t -> 'a -> 'n option -> 'm option -> 'a) (a: 'a) (rt1: 'n rtree_t) (rt2: 'm rtree_t) (v:V.t) : 'a =
	match rt1,rt2 with
	| Nil, Nil -> f v a None None
	| Nil, Sub (l2,m,r2) -> 
		fold2_opt_rec f (fold2_opt_rec f (f v a None (Some m)) Nil l2 (V.XO v)) Nil r2 (V.XI v)
	| Sub (l1, n, r1), Nil -> 	
		fold2_opt_rec f (fold2_opt_rec f (f v a (Some n) None) l1 Nil (V.XO v)) r1 Nil (V.XI v)
	| Sub (l1, n, r1), Sub (l2,m,r2) -> 
	fold2_opt_rec f (fold2_opt_rec f (f v a (Some n) (Some m)) l1 l2 (V.XO v)) r1 r2 (V.XI v)
	
let rec fold2_opt (f: V.t -> 'a -> 'n option -> 'm option -> 'a) (a: 'a) (rt1: 'n rtree_t) (rt2: 'm rtree_t): 'a =
	fold2_opt_rec f a rt1 rt2 V.XH
	

let rec find (f: 'a -> 'b option): 'a t -> (V.t * 'b) option = function
	| Nil -> None
	| Sub (l, n, r) ->
		match f n with
		| Some b -> Some (V.XH, b)
		| None ->

		match find f l with
		| Some (v, b) -> Some (V.XO v, b)
		| None ->

		match find f r with
		| Some (v, b) -> Some (V.XI v, b)
		| None -> None

let rec find2_rec : V.t -> (V.t -> 'm -> 'n -> 'b option) -> 'm t -> 'n t -> (V.t * 'b) option 
	= fun v f m n ->
	match m,n with
	| Nil,_ | _,Nil -> None
	| Sub (l1, m, r1), Sub (l2, n, r2) ->
		match f v m n with
		| Some b -> Some (v, b)
		| None ->
		match find2_rec (V.XO v) f l1 l2 with
		| Some b as r -> r
		| None -> 
		match find2_rec (V.XI v) f r1 r2 with
		| Some b as r -> r
		| None -> None	

let find2: (V.t -> 'm -> 'n -> 'b option) -> 'm t -> 'n t -> (V.t * 'b) option 
	= fun f m n ->
	find2_rec V.XH f m n

let rec findPred pred =
	function
	| Nil -> None
	| Sub (l, n, r) ->
		if pred n then
			Some (V.XH, n)
		else
			match findPred pred l with
			| Some (x, n1) -> Some (V.XO x, n1)
			| None ->
				match findPred pred r with
				| Some (x, n1) -> Some (V.XI x, n1)
				| None -> None

let rec findPred2_rec : V.t -> ('m -> 'n -> bool) -> 'm t -> 'n t -> (V.t * 'm * 'n) option 
	= fun v pred m n ->
	match m,n with
	| Nil,_ | _,Nil -> None
	| Sub (l1, m, r1), Sub (l2, n, r2) ->
		if pred m n
		then Some (v, m, n)
		else match findPred2_rec (V.XO v) pred l1 l2 with
			| Some b as r -> r
			| None -> 
			match findPred2_rec (V.XI v) pred r1 r2 with
			| Some b as r -> r
			| None -> None	

let findPred2: ('m -> 'n -> bool) -> 'm t -> 'n t -> (V.t * 'm * 'n) option 
	= fun pred m n ->
	findPred2_rec V.XH pred m n
												
(* XXX: GC? *)
let rec mskBuild1 : ('a -> bool) -> bool t -> 'a t -> bool t
= fun pred m -> function
	| Nil -> m
	| Sub (l, n, r) ->
		match m with
		| Nil -> Sub (mskBuild1 pred Nil l, pred n, mskBuild1 pred Nil r)
		| Sub (l', n', r') ->
			Sub (mskBuild1 pred l' l, n' || pred n, mskBuild1 pred r' r)

(* XXX: GC? *)
let mskBuild: ('a -> bool) -> 'a t list -> bool t
= fun pred l -> List.fold_left (mskBuild1 pred) Nil l

(* XXX: GC? *)
let pathsGet : bool t -> V.Set.t
  = let rec gather: bool t -> V.t list
      = function
      | Nil -> []
      | Sub (l, n, r) ->
	 let lList = List.map (fun p -> V.XO p) (gather l) in
	 let rList = List.map (fun p -> V.XI p) (gather r) in
	 let sub = List.append lList rList in
	 if n then V.XH::sub else sub
    in
    fun t -> gather t |> V.Set.of_list

(* XXX: GC? *)
let basisBuild: ('a -> bool) -> (V.t -> string) -> 'a t list -> string t
= fun isNil pr l ->
  let nodes = mskBuild (fun n -> not (isNil n)) l |> pathsGet in
  V.Set.fold (fun p t -> set "#inval" t p (pr p)) nodes Nil

let rec toList: 'a t -> (V.t * 'a) list
= function
	| Nil -> []
	| Sub (l, n, r) ->
		let lList = List.map (fun (p, a) -> (V.XO p, a)) (toList l) in
		let rList = List.map (fun (p, a) -> (V.XI p, a)) (toList r) in
		(V.XH, n)::(List.append lList rList)

let to_string : string -> ('a -> string -> string) -> (V.t -> string) -> 'a t -> string
= fun sep nodePr pathPr tree ->
	let nodeList = List.map (fun (p, a) -> nodePr a (pathPr p)) (toList tree) in
	String.concat sep (List.filter (fun s -> String.length s <> 0) nodeList)

(* XXX: est-ce vraiment le comportement souhaité?*)
let rec merge_rec : V.t -> (V.t -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t
	= fun v f r1 r2 ->
	match r1,r2 with
	| Nil, Nil -> Nil
	| Nil, Sub (vl, vn, vr) -> begin
		match f v None (Some vn) with
		| None -> Nil 	
		| Some c ->	Sub (merge_rec (V.XO v) f Nil vl, c, merge_rec (V.XI v) f Nil vr)
		end
	| Sub (tl, tn, tr), Nil -> begin
		match f v (Some tn) None with
		| None -> Nil 	
		| Some c ->	Sub (merge_rec (V.XO v) f tl Nil, c, merge_rec (V.XI v) f tr Nil)
		end
	| Sub (tl, tn, tr), Sub (vl, vn, vr) -> begin
		match f v (Some tn) (Some vn) with
		| None -> Nil 
		| Some c ->	Sub (merge_rec (V.XO v) f tl vl, c, merge_rec (V.XI v) f tr vr)
		end

let merge : (V.t -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t
	= fun f r1 r2 ->
	merge_rec V.XH f r1 r2
	
let rec merge3_rec : V.t -> (V.t -> 'a option -> 'b option -> 'c option -> 'res option) -> 'a t -> 'b t -> 'c t -> 'res t
	= fun v f r1 r2 r3 ->
	match r1,r2,r3 with
	| Nil, Nil, Nil -> Nil
	| Sub(l1,a,r1), Nil, Nil -> begin
		match f v (Some a) None None with
		| None -> Nil
		| Some res -> Sub (merge3_rec (V.XO v) f l1 Nil Nil, res, merge3_rec (V.XI v) f r1 Nil Nil)
		end
	| Sub(l1,a,r1), Sub(l2,b,r2), Nil -> begin
		match f v (Some a) (Some b) None with
		| None -> Nil
		| Some res -> Sub (merge3_rec (V.XO v) f l1 l2 Nil, res, merge3_rec (V.XI v) f r1 r2 Nil)
		end
	| Sub(l1,a,r1), Sub(l2,b,r2), Sub(l3,c,r3) -> begin
		match f v (Some a) (Some b) (Some c) with
		| None -> Nil
		| Some res -> Sub (merge3_rec (V.XO v) f l1 l2 l3, res, merge3_rec (V.XI v) f r1 r2 r3)
		end
	| Nil, Sub(l2,b,r2), Sub(l3,c,r3) -> begin
		match f v None (Some b) (Some c) with
		| None -> Nil
		| Some res -> Sub (merge3_rec (V.XO v) f Nil l2 l3, res, merge3_rec (V.XI v) f Nil r2 r3)
		end
	| Nil, Nil, Sub(l3,c,r3) -> begin
		match f v None None (Some c) with
		| None -> Nil
		| Some res -> Sub (merge3_rec (V.XO v) f Nil Nil l3, res, merge3_rec (V.XI v) f Nil Nil r3)
		end
	| Sub(l1,a,r1), Nil, Sub(l3,c,r3) -> begin
		match f v (Some a) None (Some c) with
		| None -> Nil
		| Some res -> Sub (merge3_rec (V.XO v) f l1 Nil l3, res, merge3_rec (V.XI v) f r1 Nil r3)
		end
	| Nil, Sub(l2,b,r2), Nil -> begin
		match f v None (Some b) None with
		| None -> Nil
		| Some res -> Sub (merge3_rec (V.XO v) f Nil l2 Nil, res, merge3_rec (V.XI v) f Nil r2 Nil)
		end

let merge3 : (V.t -> 'a option -> 'b option -> 'c option -> 'res option) -> 'a t -> 'b t -> 'c t -> 'res t
	= fun f r1 r2 r3 ->
	merge3_rec V.XH f r1 r2 r3
	
let rec for_all2 : ('m option -> 'n option -> bool) -> 'm rtree_t -> 'n rtree_t -> bool
	= fun f m n ->
	match m,n with
	| Nil, Nil -> f None None
	| Sub (l1,m,r1), Nil-> 
		(f (Some m) None) && (for_all2 f l1 Nil) && (for_all2 f r1 Nil)
	| Nil, Sub (l2, n, r2) -> 
		(f None (Some n)) && (for_all2 f Nil l2) && (for_all2 f Nil r2)
	| Sub (l1, m, r1), Sub (l2,n,r2) -> 
		(f (Some m) (Some n)) && (for_all2 f l1 l2) && (for_all2 f r1 r2)
		
let rec equal : ('a -> 'a -> bool) -> 'a rtree_t -> 'a rtree_t -> bool
	= fun cmp m1 m2 ->
	match (m1,m2) with
	| Nil, Nil -> true
	| Sub (l1, m, r1), Sub (l2,n,r2) ->
		cmp m n && (equal cmp l1 l2) && (equal cmp r1 r2)
	| _,_ -> false

let rec size : 'a option rtree_t -> int
	= function
	| Nil -> 0
	| Sub (l, m, r) -> (match m with Some _ -> 1 | None -> 0) + (size l) + (size r) 

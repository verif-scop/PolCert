type env = ProgVar.PVar.t -> ZNoneItv.ZNItv.t;;

type mode = Both | Up | Low;;

module Debug = DebugTypes.Debug(struct let name = "IOracle" end)

module Poly = Poly.RelInt
module Coeff = Poly.Coeff
module Var = Poly.V

module MapMonomial = Map.Make(Poly.MonomialBasis)

module Term
	= struct
	
	type t = ASTerm.BasicZTerm.term
	
	let zero = ASTerm.BasicZTerm.Cte (PedraQOracles.zToCoqZ Coeff.z)
	
	let one = ASTerm.BasicZTerm.Cte (PedraQOracles.zToCoqZ Coeff.u)

	(* Développement *)
	let rec (to_polynomial: t -> Poly.t)
		= fun t -> 
		match t with 
		| ASTerm.BasicZTerm.Var x -> PedraQOracles.coqPosToZ x |> Scalar.RelInt.toInt |> Var.fromInt |> Poly.fromVar
		| ASTerm.BasicZTerm.Cte x -> PedraQOracles.coqZToZ x |> Scalar.RelInt.toInt |> Coeff.mk1 |> Poly.cste
		| ASTerm.BasicZTerm.Add (x1,x2) -> Poly.add (to_polynomial x1) (to_polynomial x2)
  		| ASTerm.BasicZTerm.Opp x -> Poly.mul (Poly.cste Coeff.negU) (to_polynomial x)
  		| ASTerm.BasicZTerm.Mul (x1,x2) -> Poly.mul (to_polynomial x1) (to_polynomial x2)
  		| ASTerm.BasicZTerm.Annot (annot, x) -> to_polynomial x;;
  	
	let rec (to_string : t -> string)
		= fun t ->
		match t with
		| ASTerm.BasicZTerm.Var x -> Printf.sprintf "x%s" (PedraQOracles.coqPosToZ x |> Scalar.RelInt.toInt |> string_of_int) 
		| ASTerm.BasicZTerm.Cte x -> PedraQOracles.coqZToZ x |> Scalar.RelInt.toInt |> string_of_int
		| ASTerm.BasicZTerm.Add (x1,x2) ->  Printf.sprintf "%s + %s" (to_string x1) (to_string x2)
  		| ASTerm.BasicZTerm.Opp x -> Printf.sprintf "-1*(%s)" (to_string x)
  		| ASTerm.BasicZTerm.Mul (x1,x2) -> (match (x1,x2) with
  			| (ASTerm.BasicZTerm.Add (_,_),ASTerm.BasicZTerm.Add(_,_)) -> Printf.sprintf "(%s)*(%s)" (to_string x1) (to_string x2)
  			| (ASTerm.BasicZTerm.Add (_,_),_) -> Printf.sprintf "(%s)*%s" (to_string x1) (to_string x2)
  			| (_,ASTerm.BasicZTerm.Add(_,_)) -> Printf.sprintf "%s*(%s)" (to_string x1) (to_string x2)
  			| _ -> Printf.sprintf "%s*%s" (to_string x1) (to_string x2))
  		| ASTerm.BasicZTerm.Annot (ASTerm.TopLevelAnnot.STATIC, x) -> Printf.sprintf "STATIC(%s)" (to_string x)
  		| ASTerm.BasicZTerm.Annot (ASTerm.TopLevelAnnot.AFFINE, x) -> Printf.sprintf "AFFINE(%s)" (to_string x)
  		| ASTerm.BasicZTerm.Annot (ASTerm.TopLevelAnnot.INTERV, x) -> Printf.sprintf "INTERV(%s)" (to_string x)
		| _ -> Stdlib.invalid_arg "IOtypes.to_string"
		
	let (of_cte : Coeff.t -> t)
		= fun i -> ASTerm.BasicZTerm.Cte (PedraQOracles.zToCoqZ i)
		
	let (of_var : Var.t -> t)
		= fun v -> ASTerm.BasicZTerm.Var (Var.toInt v |> Coeff.mk1 |> PedraQOracles.zToCoqPos)
		
	let (of_monomialBasis : Poly.MonomialBasis.t -> t)
		= fun m -> 
		List.fold_left 
		ASTerm.BasicZTerm.smartMul 
		one
		(List.map 
			(fun x -> if x |> Var.toInt = 0 
				then one
				else of_var x)
			m)

	let (of_monomial : Poly.Monomial.t ->t)
		= fun (m,c) ->
		ASTerm.BasicZTerm.smartScalMul
		(Scalar.RelInt.toInt c |> Coeff.mk1 |> PedraQOracles.zToCoqZ)
		(of_monomialBasis m);;
	
	let (of_polynomial : Poly.t -> t)
		= fun p ->
		List.fold_left
		(fun t m -> ASTerm.BasicZTerm.smartAdd t (of_monomial m))
		zero
		p
	
	let rec (center_zero_var : Poly.Monomial.t -> Var.t -> Var.t list-> BinNums.coq_Z list -> ASTerm.BasicZTerm.term list)
		= fun (m,c) vToKeep vlist clist ->
		match (vlist,clist) with
		| ([],[]) -> [ASTerm.BasicZTerm.smartMul 
			(ASTerm.BasicZTerm.smartAnnot
				ASTerm.TopLevelAnnot.INTERV
				(of_monomialBasis (Misc.pop (Var.equal) m vToKeep)))
			(ASTerm.BasicZTerm.annotAFFINE (of_monomial ([vToKeep],c)))]
		| ([],_) | (_,[]) -> Stdlib.failwith "Oracle.Term.center_zero_var"
		| (v :: vtl, x :: ctl) -> 
		let tlist1 = (center_zero_var (Misc.pop (Var.equal) m v,c) vToKeep vtl ctl) in
		let x' = PedraQOracles.coqZToZ x |> Scalar.RelInt.toInt |> Coeff.mk1 in
		let tlist2 = (center_zero_var (Misc.pop (Var.equal) m v, Coeff.mul c x') vToKeep vtl ctl) in
		List.concat 
		(List.map2 
		(fun t1 t2-> 
		[ASTerm.BasicZTerm.smartMul
			(ASTerm.BasicZTerm.smartAnnot
				ASTerm.TopLevelAnnot.INTERV
					(ASTerm.BasicZTerm.smartAdd
						(of_var v)
						(ASTerm.BasicZTerm.Opp (ASTerm.BasicZTerm.Cte x))))
			t1;
		t2])
		tlist1 tlist2)
	
	(* on ne translate que la variable qu'on garde*)
	let rec (translate : Poly.Monomial.t -> Var.t -> BinNums.coq_Z -> ASTerm.BasicZTerm.term * Poly.Monomial.t)
		= fun (m,c) vToKeep coeff ->
		let l = Misc.pop (Var.equal) m vToKeep in
		(ASTerm.BasicZTerm.smartMul
			(ASTerm.BasicZTerm.annotAFFINE
				(ASTerm.BasicZTerm.smartScalMul
					(c |> Scalar.RelInt.toInt |> Coeff.mk1 |> PedraQOracles.zToCoqZ)
					(ASTerm.BasicZTerm.smartAdd
						(of_var vToKeep)
						(ASTerm.BasicZTerm.Opp (ASTerm.BasicZTerm.Cte coeff)))))
			(ASTerm.BasicZTerm.smartAnnot
				ASTerm.TopLevelAnnot.INTERV
				(of_monomialBasis l)),
		(l,Coeff.mul c (coeff |> PedraQOracles.coqZToZ |> Scalar.RelInt.toInt |> Coeff.mk1)))
	
	(* Renvoie une partie affine en enlevant les annotations affines *)
	let (get_affine_part : t -> t)
		= let rec(get_affine_part_rec : t -> t option)
			= fun t ->
			match t with
			| ASTerm.BasicZTerm.Var x -> None
			| ASTerm.BasicZTerm.Cte x -> None
			| ASTerm.BasicZTerm.Add (x1,x2) ->  (match (get_affine_part_rec x1, get_affine_part_rec x2) with
				| (None, Some x) -> Some x
				| (Some x, None) -> Some x
				| (Some x1, Some x2) -> Some (ASTerm.BasicZTerm.smartAdd x1 x2)
				| _ -> None (* a modifier *))
  			| ASTerm.BasicZTerm.Opp x -> (match get_affine_part_rec x with
  				| Some y -> Some(ASTerm.BasicZTerm.Opp y)
  				| None -> None)
			| ASTerm.BasicZTerm.Mul (x1,x2) ->  (match (get_affine_part_rec x1, get_affine_part_rec x2) with
				| (None, Some x) -> Some x
				| (Some x, None) -> Some x
				| _ -> None (* a modifier *))
  			| ASTerm.BasicZTerm.Annot (a, x) when a = ASTerm.TopLevelAnnot.AFFINE -> Some x
  			| ASTerm.BasicZTerm.Annot (a, x) -> (match get_affine_part_rec x with
  				| Some y -> Some(ASTerm.BasicZTerm.Annot (a, y))
  				| None -> None)
	in fun t ->
 	match get_affine_part_rec t with 
  		| Some x -> x
  		| None -> Stdlib.raise Not_found
  	
  	(* remarque : retire les annotations interv*)
	let (get_interv_part : t -> t)
		= let rec(get_interv_part_rec : t -> t option)
			= fun t ->
			match t with
			| ASTerm.BasicZTerm.Var x -> None
			| ASTerm.BasicZTerm.Cte x -> None
			| ASTerm.BasicZTerm.Add (x1,x2) ->  (match (get_interv_part_rec x1, get_interv_part_rec x2) with
				| (None, Some x) -> Some x
				| (Some x, None) -> Some x
				| (Some x1, Some x2) -> Some (ASTerm.BasicZTerm.Add (x1,x2))
				| _ -> None)
  			| ASTerm.BasicZTerm.Opp x -> (match get_interv_part_rec x with
  				| Some y -> Some(ASTerm.BasicZTerm.Opp y)
  				| None -> None)
			| ASTerm.BasicZTerm.Mul (x1,x2) ->  (match (get_interv_part_rec x1, get_interv_part_rec x2) with
				| (None, Some x) -> Some x
				| (Some x, None) -> Some x
				| (Some x1, Some x2) -> Some(ASTerm.BasicZTerm.Mul (x1,x2))
				| _ -> None)
  			| ASTerm.BasicZTerm.Annot (a, x) when a = ASTerm.TopLevelAnnot.INTERV -> Some x
  			| ASTerm.BasicZTerm.Annot (a, x) -> (match get_interv_part_rec x with
  				| Some y -> Some(ASTerm.BasicZTerm.Annot (a, y))
  				| None -> None)
  	in fun t ->
  	match get_interv_part_rec t with 
  		| Some x -> x
 	 	| None -> one 

end


(* les annotations autorisées sont Interv et Static*)
module AnnotedVar
	= struct
	
	type t = 
	Var of Var.t
	| AVar of ASTerm.TopLevelAnnot.topLevelAnnot * t
	
	let (of_var : Var.t -> ASTerm.TopLevelAnnot.topLevelAnnot -> t)
		= fun v a -> 
		AVar(a,Var v)
	
	let rec (to_var : t -> Var.t)
		= fun x ->
		match x with 
		| Var v -> v
		| AVar (_,v) -> to_var v
		
	let rec (to_term : t -> ASTerm.BasicZTerm.term)
		= fun aV -> 
		match aV with
		| Var v -> ASTerm.BasicZTerm.Var (v |> Var.toInt |> Coeff.mk1 |> PedraQOracles.zToCoqPos)
		| AVar(a,aV') -> ASTerm.BasicZTerm.smartAnnot a (to_term aV')
		
	let rec (to_string : t -> string)
	= fun aV ->
	match aV with
	| Var v -> Var.to_string v
	| AVar (ASTerm.TopLevelAnnot.STATIC, aV') -> String.concat "" ["STATIC(" ; to_string aV' ; ")"]
	| AVar (ASTerm.TopLevelAnnot.INTERV, aV') -> String.concat "" ["INTERV(" ; to_string aV' ; ")"]
	| _ -> Stdlib.invalid_arg "IOtypes.AnnotedVar.to_string"
	
	(* utile pour prendre en compte les variables éliminées pour un monôme
	il faut prendre garde à ce que le pattern fournisse le monome original cependant *)
	let (update_monomial : Poly.MonomialBasis.t -> (t list) MapMonomial.t -> Poly.MonomialBasis.t)
		= fun m mapNKeep ->
		try List.fold_left 
			(fun m' v -> Misc.pop (Var.equal) m' v)
			m
			(List.map to_var (MapMonomial.find m mapNKeep))
		with Not_found -> m
  		
  	let (mem : Var.t -> t list -> bool)
  		= fun v aVarl ->
  		List.mem 
  			v
  			(List.map to_var aVarl)
  			
  	let (find : Var.t -> t list -> t)
  		= fun v aVarl ->
  		List.find 
  			(fun x -> Var.equal v (to_var x))
  			aVarl
  			
	let rec(apply : Term.t -> t list -> Term.t) 
		= fun t aVarl ->
		match t with
		| ASTerm.BasicZTerm.Var x when mem (PedraQOracles.coqPosToZ x |> Scalar.RelInt.toInt |> Var.fromInt) aVarl-> 
			to_term (find (PedraQOracles.coqPosToZ x |> Scalar.RelInt.toInt |> Var.fromInt) aVarl)
		| ASTerm.BasicZTerm.Opp x -> ASTerm.BasicZTerm.smartOpp (apply x aVarl)
		| ASTerm.BasicZTerm.Add (x1,x2) -> ASTerm.BasicZTerm.smartAdd (apply x1 aVarl) (apply x2 aVarl)
  		| ASTerm.BasicZTerm.Mul (x1,x2) -> ASTerm.BasicZTerm.smartMul (apply x1 aVarl) (apply x2 aVarl)
  		| ASTerm.BasicZTerm.Annot (annot, x) -> ASTerm.BasicZTerm.smartAnnot annot (apply x aVarl)
  		| _ -> t
end

module Itv
	= struct
	type t = ZNoneItv.ZNItv.t
	
	let (of_var : env -> Var.t -> t)
		= fun env v -> v |> Var.toInt 
		|> Coeff.mk1
		|> PedraQOracles.zToCoqPos
		|> env
	
	let rec (of_term : Term.t -> env -> t)
		= fun t env ->
		match t with
		| ASTerm.BasicZTerm.Var v -> env v
		| ASTerm.BasicZTerm.Cte x -> {ZNoneItv.ZNItv.low = Some x ; ZNoneItv.ZNItv.up = Some x}
		| ASTerm.BasicZTerm.Add (x1,x2) -> ZNoneItv.ZNItv.add DomainInterfaces.BOTH (of_term x1 env) (of_term x2 env)
  		| ASTerm.BasicZTerm.Opp x -> ZNoneItv.ZNItv.opp (of_term x env)
  		| ASTerm.BasicZTerm.Mul (x1,x2) -> ZNoneItv.ZNItv.mul DomainInterfaces.BOTH (of_term x1 env) (of_term x2 env)
  		| ASTerm.BasicZTerm.Annot (annot, x) -> of_term x env
	
	let (low : t -> ZNone.ZN.t)
		= fun itv -> ZNoneItv.ZNItv.low itv
	
	let (up : t -> ZNone.ZN.t)
		= fun itv -> ZNoneItv.ZNItv.up itv
		
	let (to_string : t -> string)
		= fun itv ->
		match (low itv, up itv) with
		| (None, Some b) -> Printf.sprintf "]-inf,%s]" (b |> PedraQOracles.coqZToZ |> Scalar.RelInt.toInt |> string_of_int)
		| (Some a,None) -> Printf.sprintf "[%s,+inf[" (a |> PedraQOracles.coqZToZ |> Scalar.RelInt.toInt |> string_of_int)
		| (Some a, Some b) -> Printf.sprintf "[%s,%s]" (a |> PedraQOracles.coqZToZ |> Scalar.RelInt.toInt |> string_of_int) 
			(b |> PedraQOracles.coqZToZ |> Scalar.RelInt.toInt |> string_of_int)
		| (None, None) -> Printf.sprintf "]-inf,+inf["
			
	let (range : t -> int)
		= fun itv -> 
		match (low itv, up itv) with
		| (None, _) | (_,None) -> -1
		| (Some a, Some b) -> (b |> PedraQOracles.coqZToZ |> Scalar.RelInt.toInt)-(a |> PedraQOracles.coqZToZ |> Scalar.RelInt.toInt)
	
	let (is_bounded : t -> bool)
		= fun itv ->
		match (low itv, up itv) with
			| (Some _, Some _) -> true
			| _ -> false

	let (is_fully_unbounded : t -> bool)
		= fun itv ->
		match (low itv, up itv) with
			| (None,None) -> true
			| _ -> false
			
	let (greatest : Poly.MonomialBasis.t -> env -> Var.t) 	
		= fun m env-> 
		let l = List.filter (fun x -> Var.toInt x > 0) m in		
		 List.map (fun x -> of_var env x |> range) l
		|> List.combine l (*liste de paire (variable, range de l'intervalle)*)
		|> List.filter (fun (v,x) -> x >= 0) (* on ne garde que les ranges positives (les négatives étant des itv non bornés) *)
		|> List.fast_sort (fun (v1,x1) (v2,x2) -> Stdlib.compare x1 x2)
		|> fun l -> List.nth l ((List.length l )-1) 
		|> fun (l1,l2) -> l1
	
	let (get_center :t -> BinNums.coq_Z)
		= fun itv ->
		match (low itv, up itv) with
			| (Some x1, Some x2) -> let a = PedraQOracles.coqZToZ x1 in
				let b = PedraQOracles.coqZToZ x2 in Coeff.div (Coeff.add a b) (Coeff.mk1 2) |> PedraQOracles.zToCoqZ
			| _ ->  Stdlib.failwith "Oracle.Misc.get_center"
	
	let (contains_zero : t -> bool)
		= fun itv ->
				match (low itv, up itv) with
			| (Some x1, Some x2) -> let a = x1 |> PedraQOracles.coqZToZ |> Scalar.RelInt.toInt |> Coeff.mk1 and 
				b = x2 |> PedraQOracles.coqZToZ |> Scalar.RelInt.toInt |> Coeff.mk1 in
				Coeff.le a (Coeff.z) && Coeff.le (Coeff.z) b
			| _ ->  false	
	
	let (get_translation_bound : t -> BinNums.coq_Z) 
		= fun itv -> 
			match (low itv, up itv) with
			| (Some x1, Some x2) -> 
				(*let a = x1 |> PedraQOracles.coqZToZ |> Scalar.RelInt.toInt |> Coeff.mk1 in *)
				let b = x2 |> PedraQOracles.coqZToZ |> Scalar.RelInt.toInt |> Coeff.mk1 in
				if Coeff.lt b (Coeff.z) then x2 else x1
			| _ -> Stdlib.failwith "Itv.get_translation_bound"
			
end


open IOtypes

	module Misc
		= struct
		
		let (sign_changing : Poly.Monomial.t -> Var.t -> env -> bool)
			= fun (m,c) v env ->
			let l = (Misc.pop Var.equal m v) in
			let l' = List.filter (fun v -> let itv = v |> Itv.of_var env in match (Itv.low itv, Itv.up itv) with 
				| (_, Some x) when PedraQOracles.coqZToZ x |> Scalar.RelInt.toInt <= 0 -> true
				| _ -> false) l in
				(List.length l' + (if c |> Scalar.RelInt.toInt < 0 then 1 else 0)) mod 2 = 1
				
		let (is_unbounded : Poly.MonomialBasis.t -> env -> bool)
			= fun m env -> 
			List.exists (fun v -> let itv = v |> Itv.of_var env in match (Itv.low itv, Itv.up itv) with 
			| (None, None) -> true 
			| _ -> false) m 
			||
			try let v = List.find (fun v -> let itv = v |> Itv.of_var env in match (Itv.low itv, Itv.up itv) with 
			| (None, Some _) | (Some _, None)-> true 
			| _ -> false) m in
			List.exists (fun v -> let itv = v |> Itv.of_var env in match (Itv.low itv, Itv.up itv) with 
			| (Some x, Some y) when PedraQOracles.coqZToZ x |> Scalar.RelInt.toInt < 0 && PedraQOracles.coqZToZ y |> Scalar.RelInt.toInt > 0 -> true 
			| (None, Some y) when PedraQOracles.coqZToZ y |> Scalar.RelInt.toInt > 0 -> true
			| (Some x, None) when PedraQOracles.coqZToZ x |> Scalar.RelInt.toInt < 0 -> true
			| _ -> false) (Misc.pop Var.equal m v)
			with Not_found -> false	
	end
	
	type t = 
	  UnboundedVar of Poly.Monomial.t * Var.t (* Exactly one variable in the monomial is unbounded. *)
	| UnboundedVarmode of Poly.Monomial.t * Var.t (* The variable is unbounded on the side allowed by the mode. *)
	| GreatestItv of Poly.Monomial.t * Var.t (* All variables are bounded; keep the variable with the largest interval. *)
	| VarCte of Poly.Monomial.t * Var.t (* This variable is constant. *)
	| MonomialCte of Poly.Monomial.t (* the monomial is a constant *)
	| LinearMonomial of Poly.Monomial.t * Var.t (* Linear monomial. *)
	| CenterZero of Poly.Monomial.t (* Rewrite the monomial to center variables not being kept at zero. *)
	| Translation of Poly.Monomial.t (* Rewrite the monomial by translating variables. *)
	| Screwed (* Every STATIC intervalization gives [None, None]; call Default directly to finish sooner. *)
	| FirstUnbounded of Poly.Monomial.t * Var.t (* Keep the first unbounded variable, or the variable with the largest interval if all are bounded. *)
	| NulScalar of Poly.Monomial.t (* The monomial coefficient is zero. *)
	| Multiplicity of (Poly.Monomial.t * int)list * Var.t (* The variable has high multiplicity. *)
	| Default of Poly.t (* Keep the first variable of the monomial. *)

	type matcher = (Poly.t -> env -> mode -> Var.t MapMonomial.t -> (AnnotedVar.t list) MapMonomial.t -> t option)
	
	(* Mark a variable 'to_keep'. *)
	let unboundedVar : matcher
		= fun p env mode mapKeep mapNKeep -> 
		try let (m,c) = (List.find 
			(fun (m',_) -> 
				not (MapMonomial.mem m' mapKeep) (* If the monomial does not already have a variable to keep. *)
				&& 
				(let l = List.find_all 
					(fun v -> (* Update:not (Var.equal v Var.null) &&*) Itv.of_var env v |> Itv.is_bounded |> not)
					(AnnotedVar.update_monomial m' mapNKeep)
				 in
				 List.length l >= 1)) (* If exactly one variable is unbounded. *)
			p)
			in Some (UnboundedVar ((m,c), 
			let l = (AnnotedVar.update_monomial m mapNKeep) in 
			try List.find (fun v -> Itv.of_var env v |> Itv.is_fully_unbounded) l
			with Not_found -> List.find (fun v -> Itv.of_var env v |> Itv.is_bounded |> not) l))
		with Not_found -> None
	
	(* Mark a variable 'to_interv'. *)
	let unboundedVarmode : matcher
		= fun p env mode mapKeep mapNKeep -> 
		match mode with
		| Both -> None
		| _ -> begin
			try 
				let (m,c) = (List.find (* First case. *)
				(fun (m',c') -> 
					let m'' = (AnnotedVar.update_monomial m' mapNKeep) in
					List.length m'' > 0 (* At least one variable remains. *) (* Update: 0 instead of 1. *)
				&& 
					not (Misc.is_unbounded m'' env) 
				&& 
				let v = List.find (fun v -> let itv = v |> Itv.of_var env in match (Itv.low itv, Itv.up itv) with 
					| (None, _) -> true 
					| _ -> false) m'' in
					match mode with 
					| Up -> not (Misc.sign_changing (m'',c') v env)
					| Low -> Misc.sign_changing (m'',c') v env
					| Both -> Stdlib.failwith "IPattern.unboundedVarmode")
					p)
				in Some (UnboundedVarmode ((m,c), 
				List.find (fun v -> let itv = v |> Itv.of_var env in match (Itv.low itv, Itv.up itv) with 
					| (None, _) -> true 
					| _ -> false) 
				(AnnotedVar.update_monomial m mapNKeep)))
			
			with Not_found ->
			try 
				let (m,c) = (List.find (* Second case. *)
				(fun (m',c') -> 
					let m'' = (AnnotedVar.update_monomial m' mapNKeep) in
					List.length m'' > 0 (* At least one variable remains. *) (* Update: 0 instead of 1. *)
				&& 
					not (Misc.is_unbounded m'' env) 
				&& 
				let v = List.find (fun v -> let itv = v |> Itv.of_var env in match (Itv.low itv, Itv.up itv) with 
					| (_,None) -> true 
					| _ -> false) m'' in
					match mode with 
					| Up -> Misc.sign_changing (m'',c') v env
					| Low -> not (Misc.sign_changing (m'',c') v env)
					| Both -> Stdlib.failwith "IPattern.unboundedVarmode")
					p)
				in Some (UnboundedVarmode ((m,c), 
				List.find (fun v -> let itv = v |> Itv.of_var env in match (Itv.low itv, Itv.up itv) with 
					| (_, None) -> true 
					| _ -> false)
				(AnnotedVar.update_monomial m mapNKeep)))
			with Not_found -> None
			end
	
	(* Mark a variable 'to_keep'. *)
	let greatestItv : matcher
		= fun p env mode mapKeep mapNKeep -> 
		try let (m,c) = (List.find 
			(fun (m',_) -> 
				not (MapMonomial.mem m' mapKeep) 
			&& (* If the monomial does not already have a variable to keep. *)
				List.for_all 
				(fun v -> (* Var.equal v Var.null ||*) Itv.of_var env v |> Itv.is_bounded) 
				(AnnotedVar.update_monomial m' mapNKeep)
			&& (* At least one constant is required. *)
				(AnnotedVar.update_monomial m' mapNKeep) <> []
			(* Update:
				List.exists (* at least one constant is required *)
				(fun v -> Var.toInt v <> 0)
				(AnnotedVar.update_monomial m' mapNKeep) *))
			p)
			in Some (GreatestItv ((m,c), Itv.greatest (AnnotedVar.update_monomial m mapNKeep) env))
		with Not_found -> None
	
	(* Mark a variable 'to_interv'. *)
	let varCte : matcher
		= fun p env mode mapKeep mapNKeep -> 
		try let (m,c) = (List.find 
			(fun (m',_) -> let l = (AnnotedVar.update_monomial m' mapNKeep) in 
			List.length l > 1 &&
			(List.exists
				(fun v -> Var.toInt v <> 0 && (v |> Itv.of_var env |> Itv.range = 0))
				l))
			p)
			in Some (VarCte ((m,c), 
			List.find 
				(fun v -> v |> Itv.of_var env |> Itv.range = 0)
				(AnnotedVar.update_monomial m mapNKeep)))
		with Not_found -> None
	
	(* Mark a variable 'to_interv'. *)
	let multiplicity : matcher
		= let get_monomial_multiplicity : Poly.MonomialBasis.t -> Var.t -> int
				= fun m v -> 
				let (l1,l2) = List.partition (fun v' -> Var.equal v v') m in
				if List.length l2 = 0
				then (List.length l1) - 1
				else List.length l1
		in let get_multiplicity : Poly.t -> Var.t -> int
			= fun p v ->
			List.fold_left
			(fun i (m,c) -> i + (get_monomial_multiplicity m v)) 0 p
		in fun p env mode mapKeep mapNKeep -> 
		try let v = 
			let p' = List.map (fun (m,c) -> (AnnotedVar.update_monomial m mapNKeep,c)) p in
			List.map (fun v -> (v,get_multiplicity p' v))
			(p' |> Poly.get_vars) 
			|> List.fast_sort (fun (v1,i1) (v2,i2) -> Stdlib.compare i1 i2)
			|> List.rev
			|> fun l -> match l with
				| [] | [_] -> Stdlib.raise Not_found
				| (v1,i1) :: (v2,i2) :: tl -> if i1 > i2 then v1 else Stdlib.raise Not_found
			in let l = List.map (fun (m,c) -> ((m,c),get_monomial_multiplicity (AnnotedVar.update_monomial m mapNKeep) v)) p
			in Some (Multiplicity (List.filter (fun ((m,c),i) -> i > 0) l,v))
		with Not_found -> None
	
	(* Mark a variable 'to_keep'. *)
	let linearMonomial : matcher
		= fun p env mode mapKeep mapNKeep -> 
		try let (m,c) = (List.find 
			(fun (m',_) -> 
				not (MapMonomial.mem m' mapKeep) 
			&& (* If the monomial does not already have a variable to keep. *)
				Poly.MonomialBasis.isLinear (AnnotedVar.update_monomial m' mapNKeep)) 
			p)
			in Some (LinearMonomial((m,c),List.hd (AnnotedVar.update_monomial m mapNKeep)))
		with Not_found -> None
	
	(* Remove a constant monomial.
        Use with centerZero, which may generate constant monomials. *)
	let monomialCte : matcher
		= fun p env mode mapKeep mapNKeep -> 
		try let (m,c) = (List.find Poly.Monomial.isConstant p)
			in Some (MonomialCte(m,c))
		with Not_found -> None
		
	(* Rewrite the polynomial. *)
	let centerZero : matcher
		= fun p env mode mapKeep mapNKeep -> 
		try let (m,c) = (List.find 
			(fun (m',_) -> (MapMonomial.mem m' mapKeep)) (* If the monomial already has a variable to keep. *)
			p)
			in Some (CenterZero(m,c))
		with Not_found -> None

	(* Rewrite the polynomial. *)
	let translation : matcher
		= fun p env mode mapKeep mapNKeep -> 
		try let (m,c) = (List.find 
			(fun (m',_) -> 
				not (Poly.MonomialBasis.isLinear m') 
			&& 
				try MapMonomial.find m' mapKeep
				|> Itv.of_var env |> (fun itv -> Itv.is_bounded itv && not (Itv.contains_zero itv))
				with Not_found -> false)
			p)
			in Some (Translation(m,c))
		with Not_found -> None
			
	(* Remove all remaining monomials to save time. *)
	let screwed : matcher
		= fun p env mode mapKeep mapNKeep -> 
		if (List.exists 
			(fun (m',_) -> not (MapMonomial.mem m' mapKeep) && (* If the monomial does not already have a variable to keep. *)
			Misc.is_unbounded (AnnotedVar.update_monomial m' mapNKeep) env)
			p)
		then Some Screwed
		else None
	
	(* Mark a variable 'to_keep'. *)
	let firstUnbounded : matcher
		= fun p env mode mapKeep mapNKeep -> 
		try let (m,c) = (List.find 
			(fun (m',_) -> not (MapMonomial.mem m' mapKeep))(* If the monomial does not already have a variable to keep. *)
			p)
			in Some (FirstUnbounded((m,c),
			let m' = (AnnotedVar.update_monomial m mapNKeep) in
			try List.find (fun v -> v |> Itv.of_var env |> Itv.is_bounded |> not) m'
				with Not_found -> Itv.greatest m' env))
		with Not_found -> None
	
	(* Remove the monomial; probably unnecessary. *)
	let nulScalar : matcher
		= fun p env mode mapKeep mapNKeep -> 
		try let (m,c) = (List.find 
			(fun (m',c') -> Coeff.equal c' Coeff.z)(* If the monomial does not already have a variable to keep. *)
			p)
			in Some (NulScalar(m,c))
		with Not_found -> None
	
	(* Matching order: exclude Default, which matching already uses as its default. *)
	let matching_order = [monomialCte ; linearMonomial ; varCte ; unboundedVar ; unboundedVarmode ; multiplicity ; greatestItv ; firstUnbounded ;
	centerZero]

	let (matching :  Poly.t -> env -> mode -> Var.t MapMonomial.t -> (AnnotedVar.t list) MapMonomial.t -> t)
		= let rec(find_first : Poly.t -> env -> mode -> matcher list -> Var.t MapMonomial.t -> (AnnotedVar.t list) MapMonomial.t -> t)
			= fun p env mode l mapKeep mapNKeep->
			match l with
			| [] -> Default p
			| matcher :: tl -> match matcher p env mode mapKeep mapNKeep with
				| Some pat -> pat
				| None -> find_first p env mode tl mapKeep mapNKeep in
		fun p env mode mapKeep mapNKeep -> 
		find_first p env mode matching_order mapKeep mapNKeep

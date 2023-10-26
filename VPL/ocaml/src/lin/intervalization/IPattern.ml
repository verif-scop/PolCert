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
	  UnboundedVar of Poly.Monomial.t * Var.t (* une seule variable est non-bornée dans le monôme *)
	| UnboundedVarmode of Poly.Monomial.t * Var.t (* variable non bornée mais du bon côté par rapport au mode *)
	| GreatestItv of Poly.Monomial.t * Var.t (* toutes les variables sont bornées et on garde la variable qui possède le plus grand intervalle *)
	| VarCte of Poly.Monomial.t * Var.t (* cette variable est cste *)
	| MonomialCte of Poly.Monomial.t (* the monomial is a constant *)
	| LinearMonomial of Poly.Monomial.t * Var.t (* monôme linéaire *)
	| CenterZero of Poly.Monomial.t (* on réécrit le monôme pour centrer les variables non gardées en 0 *)
	| Translation of Poly.Monomial.t (* on réécrit le monôme en translatant des variables *)
	| Screwed (* toute intervalization STATIQUE du monôme donne [None, None], on appelle directement Default pour en finir plus rapidement *)
	| FirstUnbounded of Poly.Monomial.t * Var.t (* Garde la première variable non-bornée. S'il n'y en a pas, garde la variable avec le plus grand intervalle*)
	| NulScalar of Poly.Monomial.t (* le scalaire du monôme est nul *)
	| Multiplicity of (Poly.Monomial.t * int)list * Var.t (* la variable a une grande multiplicité *)
	| Default of Poly.t (* On garde la première variable du monôme *)

	type matcher = (Poly.t -> env -> mode -> Var.t MapMonomial.t -> (AnnotedVar.t list) MapMonomial.t -> t option)
	
	(* Marque une variable 'to_keep' *)
	let unboundedVar : matcher
		= fun p env mode mapKeep mapNKeep -> 
		try let (m,c) = (List.find 
			(fun (m',_) -> 
				not (MapMonomial.mem m' mapKeep) (* si le monôme n'a pas déjà de variable gardée *)
				&& 
				(let l = List.find_all 
					(fun v -> (* MAJ:not (Var.equal v Var.null) &&*) Itv.of_var env v |> Itv.is_bounded |> not)
					(AnnotedVar.update_monomial m' mapNKeep)
				 in
				 List.length l >= 1)) (* si le nombre de variable non bornée est 1*)
			p)
			in Some (UnboundedVar ((m,c), 
			let l = (AnnotedVar.update_monomial m mapNKeep) in 
			try List.find (fun v -> Itv.of_var env v |> Itv.is_fully_unbounded) l
			with Not_found -> List.find (fun v -> Itv.of_var env v |> Itv.is_bounded |> not) l))
		with Not_found -> None
	
	(* Marque une variable 'to_interv' *)
	let unboundedVarmode : matcher
		= fun p env mode mapKeep mapNKeep -> 
		match mode with
		| Both -> None
		| _ -> begin
			try 
				let (m,c) = (List.find (* premier cas *)
				(fun (m',c') -> 
					let m'' = (AnnotedVar.update_monomial m' mapNKeep) in
					List.length m'' > 0 (* il reste plus d'une variable *) (* MAJ: 0 au lieu de 1 *) 
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
				let (m,c) = (List.find (* second cas *)
				(fun (m',c') -> 
					let m'' = (AnnotedVar.update_monomial m' mapNKeep) in
					List.length m'' > 0 (* il reste une variable *) (* MAJ: 0 au lieu de 1 *) 
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
	
	(* Marque une variable 'to_keep' *)
	let greatestItv : matcher
		= fun p env mode mapKeep mapNKeep -> 
		try let (m,c) = (List.find 
			(fun (m',_) -> 
				not (MapMonomial.mem m' mapKeep) 
			&& (* si le monôme n'a pas déjà de variable gardée *)
				List.for_all 
				(fun v -> (* Var.equal v Var.null ||*) Itv.of_var env v |> Itv.is_bounded) 
				(AnnotedVar.update_monomial m' mapNKeep)
			&& (* il faut qu'il y ait au moins une constante *)
				(AnnotedVar.update_monomial m' mapNKeep) <> []
			(* MAJ : 
				List.exists (* il faut qu'il y ait au moins une constante *)
				(fun v -> Var.toInt v <> 0)
				(AnnotedVar.update_monomial m' mapNKeep) *))
			p)
			in Some (GreatestItv ((m,c), Itv.greatest (AnnotedVar.update_monomial m mapNKeep) env))
		with Not_found -> None
	
	(* Marque une variable 'to_interv' *)
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
	
	(* Marque une variable 'to_interv' *)
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
	
	(* Marque une variable 'to_keep' *)
	let linearMonomial : matcher
		= fun p env mode mapKeep mapNKeep -> 
		try let (m,c) = (List.find 
			(fun (m',_) -> 
				not (MapMonomial.mem m' mapKeep) 
			&& (* si le monôme n'a pas déjà de variable gardée *)
				Poly.MonomialBasis.isLinear (AnnotedVar.update_monomial m' mapNKeep)) 
			p)
			in Some (LinearMonomial((m,c),List.hd (AnnotedVar.update_monomial m mapNKeep)))
		with Not_found -> None
	
	(* Supprime un monôme qui est constant
		A utiliser de paire avec centerZero qui risque de générer des monômes constants *)
	let monomialCte : matcher
		= fun p env mode mapKeep mapNKeep -> 
		try let (m,c) = (List.find Poly.Monomial.isConstant p)
			in Some (MonomialCte(m,c))
		with Not_found -> None
		
	(* Réécrit le polynôme *)
	let centerZero : matcher
		= fun p env mode mapKeep mapNKeep -> 
		try let (m,c) = (List.find 
			(fun (m',_) -> (MapMonomial.mem m' mapKeep)) (* si le monôme a déjà une variable gardée *)
			p)
			in Some (CenterZero(m,c))
		with Not_found -> None

	(* Réécrit le polynôme *)
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
			
	(* What's the point of even being alive?
		KILL THEM ALL!!
		Utile pour gagner du temps *)
	let screwed : matcher
		= fun p env mode mapKeep mapNKeep -> 
		if (List.exists 
			(fun (m',_) -> not (MapMonomial.mem m' mapKeep) && (* si le monôme n'a pas déjà de variable gardée *)
			Misc.is_unbounded (AnnotedVar.update_monomial m' mapNKeep) env)
			p)
		then Some Screwed
		else None
	
	(* Marque une variable 'to_keep' *)
	let firstUnbounded : matcher
		= fun p env mode mapKeep mapNKeep -> 
		try let (m,c) = (List.find 
			(fun (m',_) -> not (MapMonomial.mem m' mapKeep))(* si le monôme n'a pas déjà de variable gardée *)
			p)
			in Some (FirstUnbounded((m,c),
			let m' = (AnnotedVar.update_monomial m mapNKeep) in
			try List.find (fun v -> v |> Itv.of_var env |> Itv.is_bounded |> not) m'
				with Not_found -> Itv.greatest m' env))
		with Not_found -> None
	
	(* supprime le monôme
		inutile à priori *)
	let nulScalar : matcher
		= fun p env mode mapKeep mapNKeep -> 
		try let (m,c) = (List.find 
			(fun (m',c') -> Coeff.equal c' Coeff.z)(* si le monôme n'a pas déjà de variable gardée *)
			p)
			in Some (NulScalar(m,c))
		with Not_found -> None
	
	(* Ordre de matching!! ne doit pas contenir Default qui est par défaut dans matching*)
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


open IOtypes

	type prophecy = ASTerm.BasicZTerm.term list
	
	type t = Poly.t -> env -> mode -> Var.t MapMonomial.t -> (AnnotedVar.t list) MapMonomial.t -> IPattern.t -> (prophecy * Var.t MapMonomial.t * (AnnotedVar.t list) MapMonomial.t * Poly.t)

	let rec (default : t)
		= fun p env mode mapKeep mapNKeep pat ->
		match pat with
		| IPattern.Default p -> (match p with
			| [] -> ([], mapKeep, mapNKeep, [])
			| (m,c) :: tl -> let (pro', mapKeep', mapNKeep', poly') = default p env mode mapKeep mapNKeep (IPattern.Default tl) in
			let var_to_keep = try MapMonomial.find m mapKeep'
				with Not_found -> List.nth (AnnotedVar.update_monomial m mapNKeep') 0 in
			let aVarl = try MapMonomial.find m mapNKeep'
				with Not_found -> [] in
			let aff = ASTerm.BasicZTerm.annotAFFINE (Term.of_monomial ([var_to_keep], c)) in
			let mon = ASTerm.BasicZTerm.smartAnnot ASTerm.TopLevelAnnot.INTERV
				(Term.of_monomialBasis (Misc.pop Var.equal m var_to_keep)) 
				|> fun t -> AnnotedVar.apply t aVarl in
			let value = ASTerm.BasicZTerm.smartMul mon aff in
			( value :: pro', mapKeep', mapNKeep', poly'))
		| _ -> Stdlib.failwith "Heuristic.default"

	let (varCte : t)
		= fun p env mode mapKeep mapNKeep pat ->
		match pat with 
		| IPattern.VarCte((m,c),v) -> let l = 
			try MapMonomial.find m mapNKeep
			with Not_found -> [] in
			([], mapKeep, MapMonomial.add m ((AnnotedVar.of_var v ASTerm.TopLevelAnnot.STATIC) :: l) mapNKeep, p)
		| _ -> Stdlib.failwith "Heuristic.varCte"

	let (multiplicity : t)
		= 	let rec(range : int -> int -> int list)
			= fun i j->
			if i >= j then [] else i :: (range (i+1) j)
		in fun p env mode mapKeep mapNKeep pat ->
		match pat with 
		| IPattern.Multiplicity(l,v) -> 
		let mapNKeep' = 
		List.fold_left
		(fun map ((m,c),i) -> let l' = try MapMonomial.find m map with Not_found -> [] in
		let l'' =  List.map (fun j -> AnnotedVar.Var v) (range 0 i) in
		MapMonomial.add m (l''@l') map)
		mapNKeep
		l
		in ([], mapKeep, mapNKeep', p)
		| _ -> Stdlib.failwith "Heuristic.multiplicity"
		
	let (unboundedVarmode : t)
		= fun p env mode mapKeep mapNKeep pat ->
		match pat with 
		| IPattern.UnboundedVarmode((m,c),v) -> let l = 
			try MapMonomial.find m mapNKeep
			with Not_found -> [] in
			([], mapKeep, MapMonomial.add m (AnnotedVar.Var v :: l) mapNKeep, p)
		| _ -> Stdlib.failwith "Heuristic.unboundedVarmode"
			
	let (greatestItv : t)
		= fun p env mode mapKeep mapNKeep pat ->
		match pat with
		| IPattern.GreatestItv((m,c),v) -> ([], MapMonomial.add m v mapKeep, mapNKeep, p)
		| _ -> Stdlib.failwith "Heuristic.greatestItv"

	let (unboundedVar : t)
		= fun p env mode mapKeep mapNKeep pat ->
		match pat with
		| IPattern.UnboundedVar((m,c),v) -> ([], MapMonomial.add m v mapKeep, mapNKeep, p)
		| _ -> Stdlib.failwith "Heuristic.unboundedVar"		

	let (linearMonomial : t)
		= fun p env mode mapKeep mapNKeep pat ->
		match pat with
		| IPattern.LinearMonomial ((m,c),v) -> ([], MapMonomial.add m v mapKeep, mapNKeep, p)
		| _ -> Stdlib.failwith "Heuristic.linearMonomial"

	let (centerZero : t)
		= fun p env mode mapKeep mapNKeep pat ->
		match pat with
		| IPattern.CenterZero(m,c) -> let vToKeep = MapMonomial.find m mapKeep in
		let aVarl = try MapMonomial.find m mapNKeep with Not_found -> [] in
		let l = Misc.pop Var.equal m vToKeep
		|> List.filter (fun v -> v |> Var.toInt > 0 && 
			(v |> Itv.of_var env |> fun itv -> Itv.is_bounded itv && not (Itv.contains_zero itv)) &&
			(not (AnnotedVar.mem v aVarl))) in
		let tlist = Term.center_zero_var (m,c) vToKeep l (List.map (fun v -> v |> Itv.of_var env |> Itv.get_translation_bound) l)
		|> List.map (fun t -> AnnotedVar.apply t aVarl) in
		(tlist, mapKeep, mapNKeep, Poly.sub_monomial p m)
		| _ -> Stdlib.failwith "Heuristic.centerZero"		

	let (translation : t)
		= fun p env mode mapKeep mapNKeep pat ->
		match pat with
		| IPattern.Translation(m,c) ->
		let aVarl = try MapMonomial.find m mapNKeep with Not_found -> [] in
		let vToKeep = MapMonomial.find m mapKeep in
		let (t, m') = Term.translate (m,c) vToKeep (vToKeep |> Itv.of_var env |> Itv.get_translation_bound) in
		let t' = AnnotedVar.apply t aVarl in
		([t'], mapKeep, mapNKeep, Poly.add (Poly.sub_monomial p m) [m'])
		| _ -> Stdlib.failwith "Heuristic.translation"
	
	let (screwed : t)
		= fun p env mode mapKeep mapNKeep pat ->
		match pat with
		| IPattern.Screwed -> default p env mode mapKeep mapNKeep (IPattern.Default p)
		| _ -> Stdlib.failwith "Heuristic.screwed"

	let (monomialCte : t)
		= fun p env mode mapKeep mapNKeep pat ->
		match pat with
		| IPattern.MonomialCte (m,c) -> 
			([Term.of_monomial (m,c)], mapKeep, mapNKeep, Poly.sub_monomial p m)
		| _ -> Stdlib.failwith "Heuristic.monomialCte"

	let (firstUnbounded : t)
		= fun p env mode mapKeep mapNKeep pat ->
		match pat with
		| IPattern.FirstUnbounded ((m,c),v) -> ([], MapMonomial.add m v mapKeep, mapNKeep, p)
		| _ -> Stdlib.failwith "Heuristic.firstUnbounded"
		
	let (nulScalar : t)
		= fun p env mode mapKeep mapNKeep pat ->
		match pat with
		| IPattern.NulScalar (m,c) -> 
			([], mapKeep, mapNKeep, Poly.sub_monomial p m)
		| _ -> Stdlib.failwith "Heuristic.nulScalar"
		
	let (of_pattern : t)
		= fun p env mode mapKeep mapNKeep pat ->
		Debug.log DebugTypes.Normal (lazy "Heuristic used : ");
		match pat with
		| IPattern.NulScalar _ -> Debug.log DebugTypes.Normal (lazy "NulScalar\n");
			nulScalar p env mode mapKeep mapNKeep pat
		| IPattern.Multiplicity _ -> Debug.log DebugTypes.Normal (lazy "Multiplicity\n"); 
			multiplicity p env mode mapKeep mapNKeep pat
		| IPattern.MonomialCte _ -> Debug.log DebugTypes.Normal (lazy "MonomialCte\n"); 
			monomialCte p env mode mapKeep mapNKeep pat
		| IPattern.CenterZero _ -> Debug.log DebugTypes.Normal (lazy "CenterZero\n");
			centerZero p env mode mapKeep mapNKeep pat
		| IPattern.Translation _ -> Debug.log DebugTypes.Normal (lazy "Translation\n"); 
			translation p env mode mapKeep mapNKeep pat
		| IPattern.LinearMonomial _ -> Debug.log DebugTypes.Normal (lazy "LinearMonomial\n"); 
			linearMonomial p env mode mapKeep mapNKeep pat
		| IPattern.Screwed -> Debug.log DebugTypes.Normal (lazy "Screwed\n"); 
			screwed p env mode mapKeep mapNKeep pat
		| IPattern.VarCte _ -> Debug.log DebugTypes.Normal (lazy "VarCte\n"); 
			varCte p env mode mapKeep mapNKeep pat
		| IPattern.GreatestItv _ -> Debug.log DebugTypes.Normal (lazy "GreatestItv\n"); 
			greatestItv p env mode mapKeep mapNKeep pat
		| IPattern.UnboundedVar _ -> Debug.log DebugTypes.Normal (lazy "UnboundedVar\n"); 
			unboundedVar p env mode mapKeep mapNKeep pat
		| IPattern.UnboundedVarmode _ -> Debug.log DebugTypes.Normal (lazy "UnboundedVarmode\n"); 
			unboundedVarmode p env mode mapKeep mapNKeep pat
		| IPattern.FirstUnbounded _ -> Debug.log DebugTypes.Normal (lazy "FirstUnbounded\n"); 
			firstUnbounded p env mode mapKeep mapNKeep pat
		| IPattern.Default _ -> Debug.log DebugTypes.Normal (lazy "Default\n"); 
			default p env mode mapKeep mapNKeep pat


open IOtypes

let (map_to_string : 'a MapMonomial.t -> ('a -> string) -> string)
	= fun m to_string ->
	(String.concat " ; " (List.map 
		(fun (k,a) -> String.concat "" ["("; Poly.MonomialBasis.to_string k ;" -> "; to_string a ;")"]) 
		(MapMonomial.bindings m)))
			
(* choix d'une variable à garder par monome *)
let (choose_var: Poly.t -> env -> mode -> IHeuristic.prophecy)
	= let rec (choose_var_rec: Poly.t -> IHeuristic.prophecy -> Var.t MapMonomial.t -> (AnnotedVar.t list) MapMonomial.t -> env -> mode -> IHeuristic.prophecy)
		= fun p pro mapKeep mapNKeep env mode -> 
		if Poly.isZ p 
		then pro
		else 
			let (pro', mapKeep',mapNKeep',p') = IPattern.matching p env mode mapKeep mapNKeep 
				|> IHeuristic.of_pattern p env mode mapKeep mapNKeep 
			in
			Debug.log DebugTypes.Normal (lazy "Oracle - recursive call");
			Debug.log DebugTypes.Detail 
				(lazy (Printf.sprintf "p = %s, \nvariables marked \"to_keep\" = %s, \nvariables marked \"to intervalize\" = %s\nparts already treated : %s\n" 
				(Poly.to_string p') (map_to_string mapKeep' Var.to_string) 
				(map_to_string mapNKeep' (fun l -> Misc.list_to_string AnnotedVar.to_string l ","))
				(Misc.list_to_string Term.to_string (pro @ pro') ",")));
			choose_var_rec p' (pro @ pro') mapKeep' mapNKeep' env mode 
	in 
	fun p env mode ->
	choose_var_rec p [] MapMonomial.empty MapMonomial.empty env mode

(* Pour que la factorisation fonctionne : 
	Chaque terme doit être de la forme interv(...)*...*interv(...)*affine(cste * variable à guarder + cste)
*)
let rec(factorize : IHeuristic.prophecy -> ASTerm.BasicZTerm.term)
	= fun pro ->
	if List.length pro = 0 
	then Term.zero
	else let t = (List.hd pro) in 
		let t' = Term.get_interv_part t in
		let (l1,l2) = pro
		|> List.partition (fun y -> try Poly.equal 
			(Term.get_interv_part y |> Term.to_polynomial |> Poly.canon)
			(t' |> Term.to_polynomial |> Poly.canon)
			with Not_found -> false) in
		ASTerm.BasicZTerm.smartAdd
		(factorize l2)
		(ASTerm.BasicZTerm.smartMul
		(ASTerm.BasicZTerm.smartAnnot ASTerm.TopLevelAnnot.INTERV t')
		(ASTerm.BasicZTerm.annotAFFINE
		(l1 |> List.map (fun y -> try Term.get_affine_part y with 
			Not_found -> if ASTerm.BasicZTerm.isCte t then t else Stdlib.failwith (Printf.sprintf "factorisation : %s -> non-constant term with no affine part" (Term.to_string t)))
		|> List.fold_left
		ASTerm.BasicZTerm.smartAdd
		Term.zero)))
		
let rec (sum : IHeuristic.prophecy -> ASTerm.BasicZTerm.term)
	= fun pro ->
	if List.length pro = 0 
	then Term.zero
	else ASTerm.BasicZTerm.smartAdd
	(sum (List.tl pro))
	(List.hd pro)

let (get_mode : ASTerm.linearizeContext -> mode)
	= fun lc -> 
	match lc.ASTerm.cmp with
	| NumC.Le | NumC.Lt -> Up
	| _ -> Both

let rec (translateAF : Term.t -> env -> Term.t)
	= let (translate : Term.t -> Term.t -> BinNums.coq_Z -> env -> Term.t)
		= fun t_aff t_interv c env->
		let t_interv' = (ASTerm.BasicZTerm.smartScalMul c t_interv)
		|> Term.to_polynomial 
		|> fun p -> choose_var p env Both 
		|> factorize in
		ASTerm.BasicZTerm.smartAdd
			(ASTerm.BasicZTerm.smartMul
				t_interv
				(ASTerm.BasicZTerm.annotAFFINE 
					(ASTerm.BasicZTerm.smartAdd
						t_aff
						(ASTerm.BasicZTerm.Opp (ASTerm.BasicZTerm.Cte c)))))
			t_interv'
	in let rec (translateAF_mul : Term.t -> env -> Term.t)
		= fun t env ->  
		let t_aff = Term.get_affine_part t and t_interv = Term.get_interv_part t in
		let itv = Itv.of_term t_aff env in 
		if Itv.is_bounded itv && not (Itv.contains_zero itv)
		then translate t_aff t_interv (Itv.get_translation_bound itv) env
		else t
	in fun t env ->
	match t with
	| ASTerm.BasicZTerm.Mul(t1,t2) -> translateAF_mul t env
	| ASTerm.BasicZTerm.Add(t1,t2) -> ASTerm.BasicZTerm.smartAdd (translateAF t1 env) (translateAF t2 env)
	| _ -> t

let rec(factorize_affine : ASTerm.BasicZTerm.term -> ASTerm.BasicZTerm.term)
	= let rec (get_terms : ASTerm.BasicZTerm.term -> (ASTerm.BasicZTerm.term * ASTerm.BasicZTerm.term) list)
		= fun t -> 
		match t with
		| ASTerm.BasicZTerm.Add (x1,x2) -> (get_terms x1) @ (get_terms x2)
		| _ -> [(Term.get_affine_part t, Term.get_interv_part t)]
	in let rec(factorize_affine_rec : (ASTerm.BasicZTerm.term * ASTerm.BasicZTerm.term) list -> ASTerm.BasicZTerm.term)
		= fun l ->
		match l with 
		| [] -> Term.zero
		| (t_aff,t_itv) :: tl -> 
			let (l1,l2) = List.partition 
				(fun (t'_aff,t'_itv) -> Poly.equal (Term.to_polynomial t_aff) (Term.to_polynomial t'_aff))
				tl in
			ASTerm.BasicZTerm.smartAdd
			(ASTerm.BasicZTerm.smartMul
				(ASTerm.BasicZTerm.smartAnnot
				ASTerm.TopLevelAnnot.INTERV
				(List.fold_left 
					(fun t1 (_,t'_itv) -> ASTerm.BasicZTerm.smartAdd t1 t'_itv) 
					t_itv
					l1))
				(ASTerm.BasicZTerm.annotAFFINE t_aff))
			(factorize_affine_rec l2)
	in fun t ->
	(factorize_affine_rec (get_terms t))
		
let (oracle: ASTerm.linearizeContext -> ASTerm.ZTerm.t ImpureConfig.Core.Base.imp)
	= fun lc -> 
	let p = lc.ASTerm.nonaffine and env = lc.ASTerm.env and mo = get_mode lc in 
	let p' = (p |> Term.to_polynomial) in
	Debug.log DebugTypes.Title (lazy "Intervalization Oracle");
	Debug.log DebugTypes.MInput 
		(lazy (Printf.sprintf "polynomial : %s\nIntervals : %s"
		(Poly.to_string p')
		(Misc.list_to_string 
			(fun v -> Printf.sprintf "%s -> %s" (Var.to_string v) (v |> Itv.of_var env |> Itv.to_string)) (Poly.get_vars p') ",")));
	let pro = choose_var p' env mo in 
	Debug.log DebugTypes.Normal 
		(lazy (Printf.sprintf "Prophecy before factorization : \n%s" 
		(Misc.list_to_string Term.to_string pro ",\n\t")));
	let pro' = factorize pro in
	Debug.log DebugTypes.Normal 
		(lazy (Printf.sprintf "Polynomial after factorization : %s" 
		(Term.to_string pro')));
	let t = factorize_affine pro' in
	Debug.log DebugTypes.Normal 
		(lazy (Printf.sprintf "Polynomial after factorization of affine terms : %s" 
		(Term.to_string t)));
	let result = translateAF t env in 
	Debug.log DebugTypes.MOutput 
		(lazy (Printf.sprintf "polynomial : %s" 
		(Term.to_string result)));
	result


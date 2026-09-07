open IOtypes
(* Choose one variable to keep per monomial. *)
val choose_var: Poly.t -> env -> mode -> IHeuristic.prophecy
	
val factorize : IHeuristic.prophecy -> ASTerm.BasicZTerm.term
		
val sum : IHeuristic.prophecy -> ASTerm.BasicZTerm.term

val oracle: ASTerm.linearizeContext -> ASTerm.ZTerm.t ImpureConfig.Core.Base.imp

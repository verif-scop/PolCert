open IOtypes
(*	Règles pour créer une heuristique : 
	- Heuristique visant à supprimer un monôme : s'assurer qu'on prenne bien en compte les annotations contenues dans la map mapNKeep
*)
	type prophecy = ASTerm.BasicZTerm.term list;;
	
	type t = Poly.t -> env -> mode -> Var.t MapMonomial.t -> (AnnotedVar.t list) MapMonomial.t -> IPattern.t -> (prophecy * Var.t MapMonomial.t * (AnnotedVar.t list) MapMonomial.t * Poly.t)

	val default : t
	
	val varCte : t
		
	val greatestItv : t

	val unboundedVar : t		

	val linearMonomial : t

	val monomialCte : t
	
	val centerZero : t	

	val translation : t
	
	val screwed : t	
	
	val firstUnbounded : t

	val nulScalar : t
		
	val of_pattern : t


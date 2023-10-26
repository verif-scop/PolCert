open IOtypes
(* Il y a trois types d'heuristique :
	- pour marquer une variable 'à intervaliser'
	- pour marquer une variable 'à garder' dans une monôme sans supprimer le monôme. D'autres heuristiques pourront ensuite modifier la forme du monôme pour optimiser l'intervalisation des autres variables
	- pour supprimer un monôme, i.e. le monôme ne sera plus visité par l'Oracle
*)
(* Règles pour créer un Pattern :
	- Dans une monôme, veiller à considérer seulement les variables non marquées 'à intervaliser'
	- Pattern visant à marquer 'à intervaliser' une variable : s'assurer que la variable que l'on veut marquer n'est pas la seule restante du monôme -> sauf si l'heuristique linearMonomial est matchée avant
*)
	module Misc
		: sig
		
		val sign_changing : Poly.Monomial.t -> Var.t -> env -> bool
				
		val is_unbounded : Poly.MonomialBasis.t -> env -> bool
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

	type matcher = Poly.t -> env -> mode -> Var.t MapMonomial.t -> (AnnotedVar.t list) MapMonomial.t -> t option
	
	val unboundedVar : matcher
		
	val greatestItv : matcher
	
	val varCte : matcher
	
	val linearMonomial : matcher

	val monomialCte : matcher
		
	val centerZero : matcher
	
	val translation : matcher
		
	val screwed : matcher

	val firstUnbounded : matcher
	
	val nulScalar : matcher
		
	val matching_order : matcher list (* Ordre de matching!! ne dois pas comporer Default qui est par défaut dans matching*)

	val matching : Poly.t -> env -> mode -> Var.t MapMonomial.t -> (AnnotedVar.t list) MapMonomial.t -> t


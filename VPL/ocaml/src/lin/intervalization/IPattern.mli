open IOtypes
(* Three kinds of heuristics:
    - mark a variable for intervalization;
    - mark a variable to keep without removing its monomial, allowing later
      heuristics to reshape the monomial for intervalizing other variables;
    - remove a monomial so that the oracle no longer visits it. *)
(* Rules for creating a pattern:
    - consider only variables not marked for intervalization;
    - do not mark the last remaining variable for intervalization unless
      linearMonomial is matched first. *)
	module Misc
		: sig
		
		val sign_changing : Poly.Monomial.t -> Var.t -> env -> bool
				
		val is_unbounded : Poly.MonomialBasis.t -> env -> bool
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
		
	val matching_order : matcher list (* Matching order: exclude Default, which matching already uses as its default. *)

	val matching : Poly.t -> env -> mode -> Var.t MapMonomial.t -> (AnnotedVar.t list) MapMonomial.t -> t

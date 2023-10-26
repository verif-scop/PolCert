
type env = ProgVar.PVar.t -> ZNoneItv.ZNItv.t

type mode = Both | Up | Low

module Debug : DebugTypes.Type

module Poly = Poly.RelInt
module Coeff = Poly.Coeff
module Var = Poly.V

module MapMonomial : Map.S with type key = Poly.MonomialBasis.t

module Term
	: sig
	
	type t = ASTerm.BasicZTerm.term
	
	val zero : t
	
	val one : t
	
	val to_polynomial: t -> Poly.t
	
	val to_string : t -> string
	
	val of_cte : Coeff.t -> t
		
	val of_var : Var.t -> t
	
	val of_monomialBasis : Poly.MonomialBasis.t -> t

	val of_monomial : Poly.Monomial.t ->t
	
	val of_polynomial : Poly.t -> t
		
	val center_zero_var : Poly.Monomial.t -> Var.t -> Var.t list-> BinNums.coq_Z list -> ASTerm.BasicZTerm.term list
		
	val get_affine_part : t -> t
  	
	val get_interv_part : t -> t
	
	val translate : Poly.Monomial.t -> Var.t -> BinNums.coq_Z -> ASTerm.BasicZTerm.term * Poly.Monomial.t

end

(* les annotations autorisées sont Interv et Static*)
module AnnotedVar
	: sig
	
	type t = 
	Var of Var.t
	| AVar of ASTerm.TopLevelAnnot.topLevelAnnot * t
	
	val of_var : Var.t -> ASTerm.TopLevelAnnot.topLevelAnnot -> t
	
	val to_var : t -> Var.t
		
	val to_term : t -> ASTerm.BasicZTerm.term
		
	val to_string : t -> string
	
	(* utile pour prendre en compte les variables éliminées pour un monôme
	il faut prendre garde à ce que le pattern fournisse le monome original cependant *)
	val update_monomial : Poly.MonomialBasis.t -> (t list) MapMonomial.t -> Poly.MonomialBasis.t
	
	val apply : Term.t -> t list -> Term.t
	
	val mem : Var.t -> t list -> bool
	
  	val find : Var.t -> t list -> t
end

module Itv
	: sig
	
	type t = ZNoneItv.ZNItv.t
	
	val low : t -> ZNone.ZN.t
	
	val up : t -> ZNone.ZN.t
		
	val of_var : env -> Var.t -> t
	
	val of_term : Term.t -> env -> t
	
	val to_string : t -> string
			
	val range : t -> int
	
	val is_bounded : t -> bool

	val is_fully_unbounded : t -> bool
	
	val greatest : Poly.MonomialBasis.t -> env -> Var.t
	
	val get_center : t -> BinNums.coq_Z
	
	val contains_zero : t -> bool
	
	val get_translation_bound : t -> BinNums.coq_Z
end

(** /!\ Cas non géré : let x = <contrainte> in ...*)
module type Type = sig
	module CP : CstrPoly.Type
	module Cs = CP.Cs
	module Poly = CP.Poly
	module V = Cs.Vec.V
	
	module MapS : Map.S with type key = string
		
	module Pb : sig
		type t = {
			vars : V.t list;
			map : V.t MapS.t;
			cstrs : Cs.t list;
			polys : CP.t list;
		}
	
		val get : string -> t
	end
end
(*
module Build (CP : CstrPoly.Type) = struct
*)
module Positive = struct
	module CP = CstrPoly.Positive
	module Cs = CP.Cs
	module Poly = CP.Poly
	module V = Cs.Vec.V
	
	module MapS = Map.Make(struct type t = string let compare = Stdlib.compare end)
	
	module DeclareFun = struct
	
		let next_var : V.t ref = ref V.u 

		let map : (V.t MapS.t) ref = ref MapS.empty
	
		let vars : V.t list ref = ref []
	
		let symbol_to_var : Smtlib_syntax.symbol -> unit
			= function
			| Smtlib_syntax.Symbol(_,symbol) -> 
				if not (MapS.mem symbol !map)
				then 
					begin
					let v = !next_var in
					map := MapS.add symbol v !map;
					vars := v :: !vars;
					next_var := V.next !next_var
					end
			| _ -> Stdlib.invalid_arg "Expected Symbol"
	
		let treat_one : Smtlib_syntax.command -> unit
			= function
			| Smtlib_syntax.CommandDeclareFun (_, symbol, (_,sortl), sort) -> 
				symbol_to_var symbol
			| _ -> Stdlib.invalid_arg "Expected assertion" 
		
		let init_map : Smtlib_syntax.command list -> unit
			= fun l ->
			List.iter treat_one l
		
	
	end

	module Assert = struct
		
		type bindingT = 
			| B_P of Poly.t
			| B_CP of CP.t list
			| B_None
		
		type stateT = Smtlib_syntax.symbol -> bindingT
		
		let empty : stateT = fun _ -> B_None
		
		let specconstant_to_Q : Smtlib_syntax.specconstant -> Q.t
			= function
			| Smtlib_syntax.SpecConstsDec (_,s) -> Q.of_string s 
			| Smtlib_syntax.SpecConstNum (_,s) -> Q.of_string s 
			| _ -> Stdlib.invalid_arg "expected ConstsDec of ConstNum"

		type identifier = 
			| Var of V.t
			| P of Poly.t
			
		let identifier_to_var : stateT -> Smtlib_syntax.identifier -> identifier
			= fun state -> 
			function
			| Smtlib_syntax.IdSymbol (_,s) -> begin
				match s with
				| Smtlib_syntax.Symbol(_,symbol) -> begin
					try
						Var (MapS.find symbol !DeclareFun.map)
					with Not_found -> 
						match state s with
						| B_P p -> P p
						| _ -> Stdlib.failwith "Symbol not defined"
					end
				| _ -> Stdlib.invalid_arg "Expected Symbol"
				end
			| _ -> Stdlib.invalid_arg "Expected IdSymbol"
			
		(* Version where variables must be binded to polynomial constraints. *)
		let identifier_to_var' : stateT -> Smtlib_syntax.identifier -> CP.t list
			= fun state -> 
			function
			| Smtlib_syntax.IdSymbol (_,s) -> begin
				match state s with
				| B_CP cp -> cp
				| _ -> Stdlib.failwith "Symbol not defined"
				end
			| _ -> Stdlib.invalid_arg "Expected IdSymbol"

		let qualidentifier_to_var : stateT -> Smtlib_syntax.qualidentifier -> identifier
			= fun state ->
			function
			| Smtlib_syntax.QualIdentifierId (_,id) -> identifier_to_var state id
			| _ -> Stdlib.invalid_arg "Expected QualIdentifierId"

		let identifier_to_operator : Smtlib_syntax.identifier -> string
			= function
			| Smtlib_syntax.IdSymbol (_,Smtlib_syntax.Symbol(_,symbol)) -> symbol
			| _ -> Stdlib.invalid_arg "Expected IdSymbol"
	
		let qualidentifier_to_operator : Smtlib_syntax.qualidentifier -> string
			= function
			| Smtlib_syntax.QualIdentifierId (_,id) -> identifier_to_operator id
			| _ -> Stdlib.invalid_arg "Expected QualIdentifierId"
		
		let division : Poly.t -> Poly.t -> Poly.t 
			= fun p1 p2 ->
			if Poly.is_constant p1 && Poly.is_constant p2
			then Poly.cste (Poly.Coeff.div (Poly.get_constant p1) (Poly.get_constant p2))
			else Stdlib.invalid_arg "Polynomial Division not handled" 
		
		let binding_is_poly : Smtlib_syntax.term -> bool
			= function
			| Smtlib_syntax.TermSpecConst (_,cste) -> true
			| Smtlib_syntax.TermQualIdTerm (_, id, (_, [_])) -> 
				begin
				let operator = qualidentifier_to_operator id in
				match operator with
				| "-" -> true
				| _ -> false
				end
			| Smtlib_syntax.TermQualIdTerm (_, id, (_, _::_::[])) -> 
				begin
				let operator = qualidentifier_to_operator id in
				match operator with
				| "+" | "*" | "-" | "/" -> true
				| _ -> false
				end
			| _ -> false
			
		let rec operation_to_poly : stateT -> Smtlib_syntax.term -> Poly.t 
			= fun state -> 
			function
			| Smtlib_syntax.TermQualIdentifier (_, id) -> begin
				match qualidentifier_to_var state id with
				| Var v -> Poly.mk2 [([v],Q.one)]
				| P p -> p
				end
			| Smtlib_syntax.TermSpecConst (_,cste) -> Poly.cste (specconstant_to_Q cste)
			| Smtlib_syntax.TermQualIdTerm (_, id, (_,[t])) -> 
				begin
				let operator = qualidentifier_to_operator id in
				let p = operation_to_poly state t in
				match operator with
				| "-" -> Poly.neg p
				| _ -> Stdlib.invalid_arg "operation with one operand : invalid operator"
				end
			| Smtlib_syntax.TermQualIdTerm (_, id, (_,t1::t2::[])) -> 
				begin
				let operator = qualidentifier_to_operator id in
				let p1 = operation_to_poly state t1 and p2 = operation_to_poly state t2 in
				match operator with
				| "+" -> Poly.add p1 p2
				| "*" -> Poly.mul p1 p2
				| "-" -> Poly.sub p1 p2
				| "/" -> division p1 p2
				| _ -> Stdlib.invalid_arg "operation with two operands : invalid operator"
				end
			| _ -> Stdlib.invalid_arg "operation_to_poly"
		and
		comparison_to_cstr : stateT -> string -> Smtlib_syntax.term list -> CP.t list
			= fun state operator terms ->
			match operator with
			| "not" -> 
				Stdlib.invalid_arg "Operator not not yet supported"
			(*begin
				match terms with
				| [t] -> List.map CP.compl (term_to_cstr state t) 
				| _ -> Stdlib.invalid_arg "not : expected one operand"
				end*)
			| "and" -> begin
				match terms with
				| t1 :: t2 :: [] -> (term_to_cstr state t1) @ (term_to_cstr state t2) 
				| _ -> Stdlib.invalid_arg "and : expected two operands"
				end
			| "=" | "<=" | "<" | ">=" | ">" -> begin
				match terms with
				| t1 :: t2 :: [] ->
					begin
					let p1 = operation_to_poly state t1 and p2 = operation_to_poly state t2 in
					match operator with
					| "=" -> [CP.eq (Poly.sub p1 p2)]
					| "<=" -> [CP.le (Poly.sub p1 p2)]
					| "<" -> [CP.lt (Poly.sub p1 p2)]
					| ">=" -> [CP.le (Poly.sub p2 p1)]
					| ">" -> [CP.lt (Poly.sub p2 p1)]
					| _ -> Stdlib.invalid_arg "expected comparison operator"
					end 
				| _ -> Stdlib.invalid_arg "comparison : expected two operands"
				end
			| "or" -> Stdlib.invalid_arg "Operator or not yet supported"
			| _ -> Stdlib.invalid_arg "comparison_to_cstr"
		and
		state_of_binding : stateT -> Smtlib_syntax.varbinding list -> stateT
			= fun state varbindings ->
			let symb_eq : Smtlib_syntax.symbol * Smtlib_syntax.symbol -> bool
				= function
				 | Smtlib_syntax.Symbol(_,s1), Smtlib_syntax.SymbolWithOr (_, s2)
				 | Smtlib_syntax.Symbol(_,s1), Smtlib_syntax.Symbol (_, s2)
				 | Smtlib_syntax.SymbolWithOr(_,s1), Smtlib_syntax.Symbol (_, s2)
				 | Smtlib_syntax.SymbolWithOr(_,s1), Smtlib_syntax.SymbolWithOr (_, s2) ->
				 	Stdlib.compare s1 s2 = 0
			in
			List.fold_left
				(fun state (Smtlib_syntax.VarBindingSymTerm (_, symbol, term)) ->
					if binding_is_poly term
					then
						let p = operation_to_poly state term in
						(fun symb -> if symb_eq (symbol, symb) then B_P p else state symb)
					else 
						let cp = term_to_cstr state term in
						(fun symb -> if symbol = symb then B_CP cp else state symb)
				)
				state
				varbindings
		and	
		term_to_cstr : stateT -> Smtlib_syntax.term -> CP.t list
			= fun state ->
			function
			| Smtlib_syntax.TermQualIdentifier (_, 
					Smtlib_syntax.QualIdentifierId (_, 
					Smtlib_syntax.IdSymbol (_, symbol))) -> 
				begin
				match state symbol with
				| B_CP cp -> cp
				| _ -> Stdlib.invalid_arg "invalid symbol"
				end
			| Smtlib_syntax.TermQualIdTerm (_, id, (_,termlist)) -> 
				let operator = qualidentifier_to_operator id in 
				comparison_to_cstr state operator termlist
			| Smtlib_syntax.TermLetTerm (_, (_, varbindings), term) ->
				 let state' = state_of_binding state varbindings in
				 term_to_cstr state' term
			| _ -> Stdlib.invalid_arg "invalid term"

		let assert_to_cstr : Smtlib_syntax.command -> CP.t list
			= function
			| Smtlib_syntax.CommandAssert (_,term) -> term_to_cstr empty term
			| _ -> Stdlib.invalid_arg "Expected assertion" 

	end

	module Pb = struct
		let getData : Smtlib_syntax.commands -> Smtlib_syntax.command list * Smtlib_syntax.command list 
			= let rec getData_rec : Smtlib_syntax.command list -> Smtlib_syntax.command list * Smtlib_syntax.command list 
				= function 
				| [] -> ([],[])
				| (Smtlib_syntax.CommandDeclareFun (pd, symbol, cmd, sort))::tl -> 
					let (l1,l2) = getData_rec tl in
					 ((Smtlib_syntax.CommandDeclareFun (pd, symbol, cmd, sort)) :: l1, l2)
				| (Smtlib_syntax.CommandAssert (pd,term))::tl -> 
					let (l1,l2) = getData_rec tl in
					 (l1, (Smtlib_syntax.CommandAssert (pd,term))::l2)
				| _::tl -> getData_rec tl
			in
			function 
			| Smtlib_syntax.Commands (_ , (_,cmds)) -> getData_rec cmds

		let parse : string -> Smtlib_syntax.commands
			=  fun file_name ->
			let in_ch = open_in file_name in
			let lexbuf = Lexing.from_channel in_ch in 
			let parsed = Smtlib_parse.main Smtlib_lex.token lexbuf in
			close_in in_ch;
			match parsed with
			| None -> Stdlib.failwith "Empty problem"
			| Some x -> x
	
		type t = {
			vars : V.t list;
			map : V.t MapS.t;
			cstrs : Cs.t list;
			polys : CP.t list;
		}
	
		let get : string -> t
			= fun file_name ->
			let commands = parse file_name in
			let (decFuns, asserts) = getData commands in
			DeclareFun.init_map decFuns;
			let cstrpolys = List.map Assert.assert_to_cstr asserts |> List.concat in
			let (cstrs,polys) = CP.partition_affine cstrpolys in
			{map = !DeclareFun.map;
			 vars = !DeclareFun.vars;
			 cstrs = cstrs;
			 polys = polys;
			}

	end
end



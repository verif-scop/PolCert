(** This module implements a minimizing simplex, with parametric objective function.
It means that coefficients of the objective function are affine functions of parameters.  
The given simplex tableau must respect these conditions: 
{ul
	{- Variables are nonnegative. No need to provide nonnegativity constraints, they are implicitly known. }
	{- Constraints are nonstrict. }
}*)

module Debug = DebugTypes.Debug(struct let name = "PSplx" end)

module type Type = sig
	module Cs : Cstr.Rat.Type
	module type VecType = Vector.Type with module M = Cs.Vec.M
	module Vec : VecType
	module Objective : Objective.Type with module Cs = Cs
	module ParamCoeff = Objective.ParamCoeff
	module Pivot : Objective.Pivot with module Vec = Vec
	module Naming = Pivot.Naming
	
	type t
	  = {
	  obj : Objective.t;
	  mat : Tableau.Matrix.t;
	  basis : int list;
	  names : Naming.t
	}
	
	val empty : t
	
	val get_obj : t -> Objective.t
	val get_mat : t -> Tableau.Matrix.t
	val get_basis : t -> int list

	val to_string : t -> string

	val nRows : t -> int
	val nCols : t -> int
	val nVars : t -> int
	val nParams : t -> int
	
	val getVars : t -> Vec.V.t list
	val getParams : t -> Vec.V.t list
	
	val obj_value : t -> ParamCoeff.t
	val obj_value' : t -> Cs.t
	
	(** [getCurVal sx] returns the current value of the basic variables in [sx].
	The value of the other variables is implicitly zero.  Each basic variable
	is given its value as a pair (column number, value) *)
	val getCurVal : t -> (int * Q.t) list

	(** [equal sx sx'] returns true if [sx] and [sx'] are
	syntactically equal. *)
	val equal : t -> t -> bool

	(** [isFeasible sx] returns true is the basic solution is feasible,
	that is all variables have a non-negative value.  The basic solution
	consists in setting all the non-basic variables to zero and setting
	each basic variable to the right-hand side of the constraint it appears
	on. *)
	val isFeasible : t -> bool

	(** [addSlackAt i sx] adds a slack variable on row [i] of [sx].
	The slack variable is added as an extra column at the right of the
	tableau. *)
	val addSlackAt : int -> t -> t

	(** [addSlacks n sx] adds slack variables for the first [n] rows
	of the tableau. *)
	val addSlacks : int -> t -> t

	val get_row_pivot : Tableau.Matrix.t -> int -> int
	
	(** [pivot sx row col] performs a pivot between [row] and [col]. *)
	val pivot : t -> int -> int -> t

	module Diag : sig

	  (** [isCanon sx] returns true if the t tableau [sx] is in canonical form.
	What is checked is that each row of the matrix of constraints has a designated
	basic variable which appears only on that row. *)
	  val isCanon : t -> bool

	end

	module Explore : sig
		module Init : sig
		(** Module [Init] gathers all the functions necessary to find an
		initial feasible basis for a parametric linear problem.
		XXX: it uses an internal variable [a] which [VariablesInt.t] identifier is [-1].
		*)

		  val getReplacementForA : t -> int -> int
		  val buildInitFeasibilityPb : t -> t
		  val buildFeasibleTab : Objective.t -> t -> t
		  val correction : t -> t option
		  val findFeasibleBasis : t -> Vec.t -> t option
		end

		val push : Objective.pivotStrgyT -> Vec.t -> t -> t
		val init_and_push : Objective.pivotStrgyT -> Vec.t -> t -> t option
	end
	
	module Build : sig
		module Poly = ParamCoeff.Poly
		
		(** [from_poly vars ineqs eqs obj] builds the parametric simplex tableau with constraints [ineqs @ eqs], objective [obj] and where simplex variables are in [vars].
		@param ineqs represent polynomials of the form [p <= 0].*)
		val from_poly : Poly.V.t list -> Poly.t list -> Poly.t list -> Poly.t -> t
	end
end
		
module PSplx (Cs : Cstr.Rat.Type) = struct
	
	(* On fait un second foncteur pour forcer Cs et Vec à avoir le même type de variables *)
	module PSplx(Vec : Vector.Type with module M = Cs.Vec.M) = struct
		module type VecType = Vector.Type with module M = Cs.Vec.M
		module Cs = Cs
		module Vec = Vec
		
		module Objective = Objective.Objective(Cs)
		module ParamCoeff = Objective.ParamCoeff
		module Pivot = Objective.Pivot(Vec)
		module Naming = Pivot.Naming
		
		type t
		  = {
		  obj : Objective.t;
		  mat : Tableau.Matrix.t;
		  basis : int list;
		  names : Naming.t
		}
		
		let empty = { 
			obj = Objective.empty;
			mat = [];
			basis = [];
			names = Naming.empty;
		}
		
		let get_obj : t -> Objective.t
		  = fun sx -> sx.obj

		let get_mat : t -> Tableau.Matrix.t
		  = fun sx -> sx.mat

		let get_basis : t -> int list
		= fun sx -> sx.basis

		let nRows : t -> int
		  = fun sx -> Tableau.Matrix.nRows sx.mat

		let nCols : t -> int
		  = fun sx ->
		  let n = Tableau.Matrix.nCols sx.mat in
		  if n = Objective.nVars sx.obj + 1 then n
		  else Stdlib.invalid_arg "t.nCols: different sizes"

		let nVars : t -> int
		  = fun sx -> nCols sx - 1

		let nParams : t -> int
		  = fun sx -> Objective.nParams sx.obj
		
		let getParams : t -> Vec.V.t list
			= fun sx ->
			List.map 
				(fun i -> Naming.to_user sx.names Naming.Param i |> fst)
				(Misc.range 0 (nParams sx))
		
		let getVars : t -> Vec.V.t list
			= fun sx ->
			List.map 
				(fun i -> Naming.to_user sx.names Naming.Var i |> fst)
				(Misc.range 0 (nVars sx))
				
		let obj_value : t -> ParamCoeff.t
		  = fun sx -> Objective.value sx.obj
		
		let obj_value' : t -> Cs.t
			= fun sx ->
			let pCoeff = sx |> get_obj |> Objective.value in
			ParamCoeff.to_cstr 
			(fun i -> Naming.to_user sx.names Naming.Param i
				|> Stdlib.fst) 
			ParamCoeff.LE0 pCoeff  
			
		let equal : t -> t -> bool
		  = fun sx sx' ->
		  Objective.equal sx.obj sx'.obj
		  && Tableau.Matrix.equal sx.mat sx'.mat
		  && List.length sx.basis = List.length sx'.basis
		  && List.for_all2 (=) sx.basis sx'.basis
		  && Naming.equal sx.names sx'.names

		let isFeasible : t -> bool
		  = fun sx -> List.fold_left (fun r v -> r && Q.geq (Tableau.Vector.last v) Q.zero) true sx.mat

		let getCurVal : t -> (int * Q.t) list
		  = fun sx ->
		  List.map2 (fun xb v -> (xb, Tableau.Vector.last v)) sx.basis sx.mat

		let pivot : t -> int -> int -> t
		  = fun sx row col ->
		  {sx with
			 obj = Objective.elim sx.obj (Tableau.Matrix.getRow row sx.mat) col;
			 mat = Tableau.Matrix.pivot sx.mat row col;
			 basis = List.mapi (fun i j -> if i = row then col else j) sx.basis
		  }

		let addSlackAt : int -> t -> t
		  = fun i sx ->
		  let idx = nVars sx in
		  {
			 obj = Objective.add_col sx.obj (ParamCoeff.mkSparse (Objective.nParams sx.obj) [] Scalar.Rat.z) idx;
			 mat = Tableau.Matrix.add_col sx.mat
					 (Tableau.Vector.init (nRows sx)
								(fun i' -> if i' = i then Scalar.Rat.u else Scalar.Rat.z)
					 ) idx;
			 basis = sx.basis @ [idx];
			 names = Naming.allocAt Naming.Slack (Vec.V.fromInt (i+1)) idx sx.names (* +1 car on compte les slack à partir de 1*)
		  }

		let addSlacks : int -> t -> t
		  = fun n sx ->
		  List.fold_left (fun sx' i -> addSlackAt i sx') sx (Misc.range 0 n)

		(* PRETTY PRINTERS *)
		let (t_get_width_column_vector : t -> int list)
			= fun sx ->
			let l =
			  List.map2
				 Stdlib.max
				 (Tableau.Matrix.get_width_column_vector sx.mat)
				 (Objective.getColumnsWidth (Naming.to_string sx.names Naming.Param) sx.obj)
			in
			List.mapi
			  (fun i n ->
				let n' = Naming.to_string sx.names Naming.Var i |> String.length in
				Stdlib.max n n')
			  (Misc.sublist l 0 (List.length l - 1))
			@ [List.nth l (List.length l - 1)]

		let to_string : t -> string
			= fun sx0 ->
			let sx = (* XXX: The output of first_t does not have a complete basis. *)
			  let l = (nRows sx0) - (get_basis sx0 |> List.length) in
			  if l < 0 then Stdlib.failwith "t.print_t"
			  else
				 let rec gen : int -> int list
					= fun i -> if i = 0 then [] else -1 :: gen (i - 1)
				 in
				 {sx0 with basis = get_basis sx0 @ gen l}
			in
			let width_columns = t_get_width_column_vector sx in
			(String.concat "" 
			(
				["\n"]
			@ (List.mapi 
				(fun i width_col->
				 let s = Naming.to_string sx.names Naming.Var i in
				 let nb_spaces = width_col - (String.length s) in 
				if nb_spaces mod 2 = 1 
					then String.concat "" [Misc.string_repeat " " (nb_spaces/2) ; s ; Misc.string_repeat " " (nb_spaces/2 + 1) ; " | "]
					else String.concat "" [Misc.string_repeat " " (nb_spaces/2) ; s ; Misc.string_repeat " " (nb_spaces/2) ; " | " ])
				(Misc.sublist width_columns 0 ((List.length width_columns) - 1)))
			@ ["\n"]
			@ [Objective.pretty_print (Naming.to_string sx.names Naming.Param) sx.obj width_columns ; "\n"]
			@ (List.map (fun i -> String.concat "" [Misc.string_repeat "-" i ; " | "]) width_columns)
			@ ["\n"]
			@ (List.map2 
				(fun vec var -> String.concat "" [(Tableau.Vector.pretty_print vec width_columns) ; Naming.to_string sx.names Naming.Var var; "\n"])
					  sx.mat (get_basis sx))))

		let print : t -> unit
		  = fun sx ->
		  to_string sx
		  |> Stdlib.print_endline
	
		let get_row_pivot : Tableau.Matrix.t -> int -> int
		  = let bounds : Tableau.Matrix.t -> int -> Q.t option list
				= fun m col ->
				List.map2
					(fun a b -> if Q.sign a > 0 then Some (Q.div b a) else None)
					(List.map (fun r -> Tableau.Vector.get col r) m)
					(List.map (fun r -> Tableau.Vector.get (Tableau.Matrix.nCols m - 1) r) m)
			 	in
			 let min : (Q.t * int) option * int -> Q.t option -> (Q.t * int) option * int
				= fun (mcur, idx) ma ->
				let mcur' =
				match ma with
				| None -> mcur
				| Some a ->
					match mcur with
					| None -> Some (a, idx)
					| Some cur -> if Q.lt a (Stdlib.fst cur) then Some (a, idx) else mcur
					in
					(mcur', idx + 1)
			 in
			 fun m col ->
			 bounds m col |> List.fold_left min (None, 0)
			 |> function
				| None, _ -> Stdlib.failwith "t.get_row_pivot: unbounded"
				| Some (a, i), _ ->
			 if Q.sign a < 0
			 then Stdlib.failwith "t.get_row_pivot: negative right-hand side"
			 else i

		module Explore = struct
		
			module Obj = struct
				include Objective.Pivot (Vec)
			end
	
		 	let rec push' : Objective.pivotStrgyT -> Vec.t -> t -> t
				= fun st point sx ->
				Debug.log DebugTypes.Detail 
					(lazy (Printf.sprintf "push' : \n%s"
						(to_string sx)));
			  	match Pivot.getPivotCol
				  	(Naming.to_vpl sx.names)
				  	(Naming.vpl_max sx.names)
				  	st sx.names point sx.obj
			  	with
			  	| Objective.OptReached -> sx
			  	| Objective.PivotOn i ->
				  	pivot sx (get_row_pivot sx.mat i) i
				  	|> push' st point
			
			let push : Objective.pivotStrgyT -> Vec.t -> t -> t
				= fun st point sx ->
				Debug.log DebugTypes.Title
					(lazy "Parametric simplex");
			  	Debug.log DebugTypes.MInput
			  		(lazy (Printf.sprintf "Point %s\n%s"
			  			(Vec.to_string Vec.V.to_string point)
			  			(to_string sx)));
			  	let res = push' st point sx in
			  	Debug.exec res DebugTypes.MOutput (lazy (to_string res))
				  	
			module Init = struct

				let a_value : Vec.V.t ref = ref Vec.V.u;; 

				let getReplacementForA : t -> int -> int
					= fun sx row ->
					let r = Tableau.Matrix.getRow row sx.mat in
					let rowCoeffs = Misc.sublist r 0 (List.length r - 1) in
					try 
						let col = Misc.findi 
							(fun a -> not (Scalar.Rat.equal Scalar.Rat.z a)) 
							(List.tl rowCoeffs) in
						col + 1
					with Not_found -> Stdlib.failwith "t.a_still_in_basis"

			 	let buildInitFeasibilityPb : t -> t
					= let getMinRhs : Tableau.Matrix.t -> int
						= fun m ->
						let (_, i, a) = List.fold_left
							(fun (i, j, a) v ->
					 		let b = Tableau.Vector.last v in
					 		if Q.lt b a then (i + 1, i, b) else (i + 1, j, a))
						(0, -1, Q.zero) m
						in
						if Q.lt a Q.zero then i
						else Stdlib.failwith "t.buildInitFeasibilityPb"
					in
					fun sx ->
					a_value := Naming.slack_max sx.names;
					let sx' = {
						obj = Objective.mkSparse (nVars sx + 1) [0, ParamCoeff.mkCst Scalar.Rat.u] (ParamCoeff.mkCst Scalar.Rat.z);
						mat = List.map (fun v -> (if Q.lt (Tableau.Vector.last v) Q.zero then Q.minus_one else Q.zero) :: v) sx.mat;
						basis = List.map ((+) 1) sx.basis;
						names = Naming.allocSlackShift !a_value sx.names
					} in
					pivot sx' (getMinRhs sx.mat) 0

				let buildFeasibleTab : Objective.t -> t -> t
					= let syncObjWithBasis : Tableau.Matrix.t -> int list -> Objective.t -> Objective.t
						= fun m b o ->
						List.fold_left2 (fun o i v -> Objective.elim o v i) o b m
					in
					fun o sx ->
					let newMat = List.map List.tl sx.mat in
					let b = List.map (fun i -> i - 1) sx.basis in
					{
						obj = syncObjWithBasis newMat b o;
						mat = newMat;
						basis = b;
						names = Naming.freeSlackShift !a_value sx.names
					}

				let correction : t -> t option
					= let removeRow : int -> t -> t
						= let rec rm : int -> int * Tableau.Vector.t list -> Tableau.Vector.t -> int * Tableau.Vector.t list
					 		= fun r (i, l) v -> if i = r then (i + 1, l) else (i + 1, v :: l)
				  		in
						fun r sx ->
						let m = sx.mat
						|> List.fold_left (rm r) (0, [])
						|> Stdlib.snd
						|> List.rev
				  		in
				  		{sx with mat = m}
					in
					let rec chooseBasicVar : int -> t -> t option
						= fun row sx ->
						if row >= nRows sx then Some sx
						else
							let v = Tableau.Matrix.getRow row sx.mat in
							try
								let col = Misc.findi (fun a -> not (Scalar.Rat.isZ a)) v in
								if col > List.length v - 2 
								then None (* last column is the constant *)
					 			else
									{sx with
									obj = Objective.elim sx.obj (Tableau.Matrix.getRow row sx.mat) col;
									mat = Tableau.Matrix.pivot sx.mat row col;
									basis = sx.basis @ [col]
									}
									|> chooseBasicVar (row + 1)
							with Not_found ->
								removeRow row sx |> chooseBasicVar row
					in
					fun sx -> 
					chooseBasicVar (List.length sx.basis) sx

			  let (findFeasibleBasis : t -> Vec.t -> t option)
				 = fun sx0 point ->
				 match correction sx0 with
				 | None -> None
				 | Some sx ->
					 if isFeasible sx then Some sx
					 else
				 let sx' =
					buildInitFeasibilityPb sx 
					|> push Objective.Bland point
				 in
				 if not (obj_value sx' |> ParamCoeff.is_zero) then None
				 else
					let sx' =
					  try
					     let row = Misc.findi ((=) 0) sx'.basis in
					     getReplacementForA sx' row
						  |> pivot sx' row
					  with Not_found -> sx'
					in
					Some (buildFeasibleTab sx.obj sx')

			end
			  	
			let init_and_push : Objective.pivotStrgyT -> Vec.t -> t -> t option
				= fun st point sx ->
				match Init.findFeasibleBasis sx point with
				| None -> begin
					print_endline ("init -> unfeasible");
					None
					end
				| Some sx -> 
					Debug.exec (Some (push st point sx))
						DebugTypes.Detail (lazy (to_string sx)) 
		end

		module Diag
		  = struct

		  let isCanon : t -> bool
			 = fun sx ->
			 if List.length sx.basis <> nRows sx
			 then false
			 else
				let chkOccur : int -> t -> bool
			= let chkOccurMat : int -> Tableau.Matrix.t -> bool
				 = fun i m ->
				 1 = List.fold_left
				  (fun cnt v -> if Q.sign (Tableau.Vector.get i v) = 0 then cnt else cnt + 1)
				  0 m
			  in
			  fun i sx' ->
			  chkOccurMat i sx'.mat &&
				 Objective.get i sx'.obj |> ParamCoeff.is_zero
				in
				List.for_all2 (fun i r -> Q.equal (Tableau.Vector.get i r) Q.one && chkOccur i sx) sx.basis sx.mat

		end
	
		module Build = struct
			module Poly = ParamCoeff.Poly
		
			let obj_buildOfPoly : Poly.t list -> Poly.t -> Objective.t * Naming.t
			  = let module VSet = Set.Make (struct type varT = Poly.V.t type t = varT let compare = Poly.V.cmp end) in
				 let gatherParams1 : Poly.t -> VSet.t
					= fun p ->
					Poly.data2 p
					|> List.map Stdlib.fst
					|> List.concat
					|> List.fold_left (fun s x -> VSet.add x s) VSet.empty
					(*|> VSet.remove Poly.V.u*)
				 in
				 let gatherParams : Poly.t list -> (int * Poly.V.t) list
					= fun l ->
					List.map gatherParams1 l
					|> List.fold_left VSet.union VSet.empty
					|> VSet.elements
					|> List.mapi (fun i x -> (i, x))
				 in
				 fun lin cst ->
				 if not (List.for_all Poly.is_affine lin && Poly.is_affine cst)
				 then Stdlib.invalid_arg "Obj._buildOfPoly"
				 else
					let l = gatherParams (cst :: lin) in
					let nm =
				List.fold_left (fun nm' (i, x) -> Naming.allocAt Naming.Param x i nm')
							 Naming.empty
							 l
					in
					let lin' = List.map (ParamCoeff.ofPoly (Naming.to_index nm Naming.Param) (List.length l)) lin in
					let cst' = ParamCoeff.ofPoly (Naming.to_index nm Naming.Param) (List.length l) cst in
					(Objective.mk lin' cst', nm)

			let obj_of_polyList : Poly.t list -> Objective.t * Naming.t
			  = fun l ->
			  if List.length l < 1 then Stdlib.invalid_arg "Obj.of_polyList"
			  else
				 let l' = List.rev l in
				 obj_buildOfPoly (List.tl l' |> List.rev) (List.hd l')

			let obj_of_polySparseList : int -> (int * Poly.t) list -> Poly.t -> Objective.t * Naming.t
			  = let rec fill : int -> int -> (int * Poly.t) list -> Poly.t list
					= fun n i ->
					function
					| [] -> if i < n then Poly.z :: fill n (i + 1) [] else []
					| ((x, a) :: l') as l ->
				 if n <= i || x < i then Stdlib.invalid_arg "Obj.of_polySparseList"
				 else if x = i then a :: fill n (i + 1) l'
				 else Poly.z :: fill n (i + 1) l
				 in
				 fun n l a ->
				 obj_buildOfPoly (List.sort (fun (i, _) (i', _) -> Stdlib.compare i i') l |> fill n 0) a

			let rec obj_of_poly : Poly.t -> Poly.V.t list -> Objective.t * Naming.t
			  = fun p l ->
			  let lin = List.map (fun x -> Poly.monomial_coefficient_poly p (Poly.MonomialBasis.mk [x])) l in
			  let cst = Poly.sub p 
				(List.fold_left 
					(fun p1 x -> Poly.add 
						p1 
						(Poly.mul 
							(Poly.monomial_coefficient_poly p (Poly.MonomialBasis.mk [x])) 
							(Poly.mk2 [([x], Scalar.Rat.u)])))
				Poly.z l)
			  |> Poly.mul Poly.negU in
			  obj_buildOfPoly lin cst

			(** row_from_constraint p mb converts the Poly.t p into a row*)
			let rec (row_from_constraint : Poly.t -> Poly.V.t list -> Tableau.Vector.t)
			  = fun p vars ->
			  match vars with
			  | [] -> [Scalar.Rat.neg (Poly.get_constant p)]
			  | var :: tail -> let coeff = Poly.monomial_coefficient p (Poly.MonomialBasis.mk [var]) in 
						coeff::(row_from_constraint p tail);;
	
			let from_poly : Poly.V.t list -> Poly.t list -> Poly.t list -> Poly.t -> t
			  = fun vars ineqs eqs obj ->
			  if List.length vars + List.length ineqs < List.length ineqs + List.length eqs
			  then Stdlib.invalid_arg "PSplx.Build.from_poly: variables"
			  else
				 if List.exists Poly.isZ ineqs || List.exists Poly.isZ eqs
				 then Stdlib.invalid_arg "PSplx.Build.from_poly: constraints"
				 else
					let (o, nm) = obj_of_poly obj vars in
					{
				obj = o;
				mat = List.map (fun r -> row_from_constraint r vars) (ineqs @ eqs);
				basis = [];
				names = Naming.mkVar vars nm
					}
					|> addSlacks (List.length ineqs)
			
			(*
			(** Version for equalities only. *)
			module Max = struct
				
				let cstr_to_vector : V.t list -> Cs.t -> Tableau.Vector.t
					= fun variables cstr ->
					match cstr.Cs.typ with
					| Cstr.Eq ->
						let vec = Cs.get_v cstr in
						List.map
							(Vec.get vec)
							variables
						@ [Cs.get_c cstr]
					| _ -> Stdlib.failwith "Psplx.Build.Max.cstr_to_vector -> expected Eq"
				
				let cstrs_to_tableau : V.t list -> Cs.t -> Tableau.Vector.t list
					= fun variables cstrs ->
					List.map (cstr_to_vector variables) cstrs
					
				let max : Naming.t -> Cs.t list -> Objective.t -> Vec.t -> t
					= fun cstrs obj point ->
					
					
				
			end
			*)
		end
	end
end

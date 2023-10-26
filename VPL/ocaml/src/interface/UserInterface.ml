(** This is the entry point of the VPL.
It provides the Interface module (explained by module type Type).*)

(**/**)
open CWrappers

module Cs = Cstr.Rat.Positive
module Vec = Cs.Vec
module Var = Vec.V
module CP = CstrPoly.Positive
module Polynomial = CP.Poly
(**/**)

(** When an operator raises an exception, it is catched and handled by function {!val:report}.
Exception ReportHandled is raised afterwards. *)
exception ReportHandled

(** The module type of (not necesarily linear) terms used in the VPL. *)
module type Term_T = sig
	module Coeff : Scalar.Type

	(** Type [t] allows to define expressions in a tree shape (e.g. with [Add] or [Mul]), or with list of terms (e.g. with [Sum] or [Prod]).*)
	type t =
	| Var of Var.t
	| Cte of Coeff.t
	| Add of t * t
	| Sum of t list
	| Opp of t
	| Mul of t * t
	| Prod of t list
	| Annot of Annot.t * t

	(** Conversion from terms to VPL polynomials. *)
	val to_poly : t -> Polynomial.t

	(** Conversion from a term and a comparison sign to a polynomial constraint. *)
	val to_cp : cmpT * t -> CP.t

	(** Conversion into string. *)
	val to_string : (Var.t -> string) -> t -> string
end

(** Conditions used in the VPL. *)
module type Cond_T = sig

   module Term : Term_T

   (** Type for conditions. *)
	type t =
	| Basic of bool (** either true or false *)
	| Atom of Term.t * cmpT * Term.t (** a comparison between two terms *)
	| BinL of t * binl * t (** binary relation (either OR or AND) between two conditions *)
	| Not of t (** negation of a condition *)

	(** Conversion into string. *)
	val to_string : (Var.t -> string) -> t -> string
end

(** Type for user-defined variables. *)
module type Ident_T = sig
	type t

	(** [compare v1 v2] returns [0] if [v1 = v2], a negative integer if [v1 > v2] and a positive one otherwise. *)
	val compare: t -> t -> int

	(** Conversion into variables of type {!val:Var.Positive.t}. *)
	val toVar: t -> Var.t

	(** Conversion into string. *)
	val to_string: t -> string
end

(** Type for user-defined expressions. *)
module type Expr_T = sig
	module Coeff : Scalar.Type
	module Ident : Ident_T

	(** VPL terms *)
	module Term : Term_T with module Coeff = Coeff

	type t

	(** {!val:to_term} may raise this exception whenever it encounters something it cannot handle. *)
	exception Out_of_Scope

	(** Conversion into VPL terms.*)
	val to_term: t -> Term.t
end

(** Module containing a high level implementation of the polyhedra domain.
Several of them are available:
{ul
	{- {!module:CDomain.PedraQWrapper}: Certified domain with rational coefficients.}
	{- {!module:CDomain.PedraZWrapper}: Certified domain with integer coefficients.}
	{- {!module:NCVPL_Unit.Q}: Uncertified domain with rational coefficients.}
	{- {!module:NCVPL_Unit.Z}: Uncertified domain with integer coefficients.}
}*)
module type HighLevelDomain_T = sig

	module Coeff : Scalar.Type
	module Expr : Expr_T with module Coeff = Coeff
	module Term = Expr.Term
	module Cond : Cond_T with module Term = Term
end

(** Polyhedra domain *)
module type Type = sig

	(** If you want to use directly the VPL datatypes instead of providing your own expressions, instanciate the functor Interface with this module.*)
	module VPL_Expr : sig
	end

	(** The module is a functor taking a High Level Domain (of type {!module:HighLevelDomain_T}) and a user-defined expression module (of type {!module:Expr_T}).
	If you have no user-defined expressions, use {!module:VPL_Expr}. *)
	module Interface : functor (I : HighLevelDomain_T)(Expr : Expr_T) -> sig

		(** Type of polyhedron *)
		type t

		(** Defines conditions using the user-defined expressions. *)
		module UserCond : sig

			(** Type for conditions based on user-defined expressions. *)
			type t =
				| Basic of bool (** either true or false *)
				| Atom of Expr.t * cmpT * Expr.t (** a comparison between two terms *)
				| BinL of t * binl * t (** binary relation (either OR or AND) between two conditions *)
				| Not of t (** negation of a condition *)

			(** Conversion into VPL conditions. *)
			val to_cond : t -> I.Cond.t
		end

		(** This module contains polyhedral operators using VPL terms and conditions.
		If you have a user-defined expression module, use module {!module:User} instead.*)
		module BuiltIn : sig

			(** Unbounded polyhedron. *)
			val top: t

			(** Empty polyhedron. *)
			val bottom: t

			(** Checks if the given polyhedron is empty. *)
			val is_bottom: t -> bool

			(** Computes the intersection of two polyhedra. *)
			val meet : t -> t -> t

			(** Computes the convex hull of two polyhedra. *)
			val join: t -> t -> t

			(** Computes the minkowski sum of two polyhedra. *)
			val minkowski: t -> t -> t

			(** Eliminates the given list of variables from a polyhedron, by orthogonal projection. *)
			val project: Var.t list -> t -> t
			val projectM: Var.t list -> t -> t

			val widen: t -> t -> t

			(** Renames a variable into another one. (Not tested) *)
			val rename: Var.t -> Var.t -> t -> t

			(** Tests the inclusion of two polyhedra. *)
			val leq: t -> t -> bool

			(** Returns a string representing the given polyhedron.
				Requires a function to convert variables into strings. *)
			val to_string: (Var.t -> string) -> t -> string

			(** Returns the upper bound of an expression in a polyhedron. *)
			val getUpperBound : t -> I.Term.t -> Pol.bndT option

			(** Returns the lower bound of an expression in a polyhedron. *)
			val getLowerBound : t -> I.Term.t -> Pol.bndT option

			(** Returns both the upper and lower bounds of an expression in a polyhedron. *)
			val itvize : t -> I.Term.t -> Pol.itvT

			(** VPL inner type for a polyhedron. *)
			type rep = PedraQOracles.t

			(** Returns the inner representation of a polyhedron, and two functions [(f1,f2)]:
				{ul
					{- [f1] translates translates high-level variables into low-level variables}
					{- [f2] translates translates low-level variables into high-level variables}}*)
			val backend_rep : t -> (rep * ((ProgVar.PVar.t -> ProgVar.PVar.t) * (ProgVar.PVar.t -> ProgVar.PVar.t))) option

			(** Computes the intersection between a condition and a polyhedron. *)
			val assume: I.Cond.t -> t -> t

			(** Returns true if the given condition is satisfied in the given polyhedron. *)
			val asserts: I.Cond.t -> t -> bool

			(** Computes the effect of parallel assignments on a polyhedron. *)
			(* TODO: Specification of parallel assignments left to define. *)
			val assign: (Var.t * I.Term.t) list -> t -> t

			(** Apply the effect of parallel non-deterministic assignments *)
			(* TODO: Specification of parallel assignments left to define. *)
			(* TODO: Should it be (Var.t * I.Cond.t) list -> t -> t *)
			val guassign: (Var.t list) -> I.Cond.t -> t -> t

			(** Uncertified functions : *)

			(** [translate pol dir] translates polyhedron [pol] in direction [dir]. *)
			val translate : t -> Pol.Cs.Vec.t -> t

			(** [mapi f1 f2 pol] applies function [f1] to each equation and [f2] to each inequation of [pol]. *)
			val mapi : (int -> Pol.Cs.t -> Pol.Cs.t) -> (int -> Pol.Cs.t -> Pol.Cs.t) -> t -> t

     		(** [diff p1 p2] returns a list of polyhedra whose union is [p1 \ p2].
     		Careful: the comparison sign of the result may be wrong. *)
			val diff : t -> t -> t list

            (** [get_regions p] returns the partition into regions of p. *)
            val get_regions : t -> t list

            val size : t -> Scalar.Rat.t option

		end

		(** Defines operators in terms of the User datastructures. *)
		module User : sig

			(** Unbounded polyhedron. *)
			val top: t

			(** Empty polyhedron. *)
			val bottom: t

			(** Checks if the given polyhedron is empty. *)
			val is_bottom: t -> bool

			(** Computes the intersection of two polyhedra. *)
			val meet : t -> t -> t

			(** Computes the minkowski sum of two polyhedra. *)
			val minkowski: t -> t -> t

			(** Computes the convex hull of two polyhedra. *)
			val join: t -> t -> t

			(** Eliminates the given list of variables from a polyhedron, by orthogonal projection. *)
			val project: Expr.Ident.t list -> t -> t
			val projectM: Expr.Ident.t list -> t -> t

			val widen: t -> t -> t

			(** Renames a variable into another one. (Not tested) *)
			val rename: Var.t -> Var.t -> t -> t

			(** Test the inclusion of two polyhedra. *)
			val leq: t -> t -> bool

			(** Returns a string representing the given polyhedron.
				Requires a function to convert variables into strings. *)
			val to_string: (Var.t -> string) -> t -> string

			(** Returns the upper bound of an expression in a polyhedron. *)
			val getUpperBound : t -> Expr.t -> Pol.bndT option

			(** Returns the lower bound of an expression in a polyhedron. *)
			val getLowerBound : t -> Expr.t -> Pol.bndT option

			(** Returns both the upper and lower bounds of an expression in a polyhedron. *)
	  		val itvize : t -> Expr.t -> Pol.itvT

	  		(** VPL inner type for a polyhedron. *)
	  		type rep = PedraQOracles.t

			(** Returns the inner representation of a polyhedron, and two functions [(f1,f2)]:
				{ul
					{- [f1] translates translates high-level variables into low-level variables}
					{- [f2] translates translates low-level variables into high-level variables}}*)
			val backend_rep : t -> (rep * ((ProgVar.PVar.t -> ProgVar.PVar.t) * (ProgVar.PVar.t -> ProgVar.PVar.t))) option

			(** Computes the intersection between a condition and a polyhedron. *)
			val assume: UserCond.t -> t -> t

			(** Returns true if the given condition is satisfied in the given polyhedron. *)
			val asserts: UserCond.t -> t -> bool

			(** Computes the effect of parallel assignments on a polyhedron. *)
			(* TODO: Specification of parallel assignments left to define. *)
			val assign: (Expr.Ident.t * Expr.t) list -> t -> t

			(** Apply the effect of parallel non-deterministic assignments *)
			(* TODO: Specification of parallel assignments left to define. *)
			(* TODO: Should it be (Var.t * I.Cond.t) list -> t -> t *)
			val guassign: (Expr.Ident.t list) -> UserCond.t -> t -> t

	  		(** The following are uncertified functions : *)
			(** [translate pol dir] translates polyhedron [pol] in direction [dir]. *)
			val translate : t -> Pol.Cs.Vec.t -> t

			(** [mapi f1 f2 pol] applies function [f1] to each equation and [f2] to each inequation of [pol].
			Variables are translated from high-level to low-level before applying functions [f1] and [f2].
			[b = true] means that variables must be translated from high-level to low-level.*)
			val mapi : bool -> (int -> Pol.Cs.t -> Pol.Cs.t) -> (int -> Pol.Cs.t -> Pol.Cs.t) -> t -> t

			(** [diff p1 p2] returns a list of polyhedra whose union is [p1 \ p2]. *)
			val diff : t -> t -> t list

            (** [get_regions p] returns the partition into regions of p. *)
            val get_regions : t -> t list

            val size : t -> Scalar.Rat.t option
		end
	end
end

(**/**)
let send : unit -> unit
	= fun () -> () (*
	print_endline "Sending crash log";
	let attach = Netsendmail.wrap_attachment
		~content_disposition:("attachment", ["filename", Netmime_string.mk_param "log_file"])
		~content_Type:("text/plain", [])
		(new Netmime.file_mime_body Config.log_file)
	in
	let email = Netsendmail.compose
		~to_addrs: [("VPL", "marechalalex@gmail.com")]
		~subject: "VPL crash log"
		~attachments:[ attach ]
		(Printf.sprintf "Report sent")
	in
	Netsendmail.sendmail ~mailer:"/usr/sbin/sendmail" email
	*)

let report : exn -> unit
	= let rec report : exn -> unit
		= let read_char : char -> bool option
			= function
			| 'y' -> Some true
			| 'n' -> Some false
			| _ -> None
		in
		fun e ->
		print_endline "Would you like to automatically send a report? [y/n]";
		match Scanf.bscanf Scanf.Scanning.stdin "%c" read_char with
		| None -> report e
		| Some b -> if b then send() else ()
	in
	fun e -> begin match e with
    | CertcheckerConfig.CertCheckerFailure (_,s) ->
        Printf.sprintf "An exception was raised: %s"
		(Printexc.to_string e)
		|> print_endline;
        print_endline s
    | _ ->
	   Printf.sprintf "An exception was raised: %s"
		(Printexc.to_string e)
		|> print_endline
    end;
	report e

module Interface (Coeff : Scalar.Type) = struct

	include Interface(Coeff)

	module type Ident_T = sig
		type t

		val compare: t -> t -> int
		val toVar: t -> Var.t
		val to_string: t -> string
	end

	module type Expr_T = sig

		module Ident : Ident_T

		type t

		exception Out_of_Scope

		val to_term: t -> Term.t
	end

	module VPL_Expr = struct
		module Ident = struct
			include Var
			let compare x y = cmp x y

			let toVar x = x
		end

		type t = Term.t

		exception Out_of_Scope
		let to_term x = x
	end

	module Interface (I : HighLevelDomain)(Expr : Expr_T) = struct

		type t = {
			value: I.t;
			name: string;
			}

		(** Handles exception report *)
		let handle : 'a Lazy.t -> 'a
			= fun a ->
			try Lazy.force a with
			| Expr.Out_of_Scope -> Stdlib.raise Expr.Out_of_Scope
			| e -> begin
				report e;
				Stdlib.raise ReportHandled
			end

		module UserCond = struct

			type t =
				| Basic of bool
				| Atom of Expr.t * cmpT * Expr.t
				| BinL of t * binl * t
				| Not of t

			let rec to_cond : t -> Cond.t
				= function
				| Basic b -> Cond.Basic b
				| Atom (e1,cmp,e2) -> Cond.Atom (Expr.to_term e1, cmp, Expr.to_term e2)
				| BinL (c1,bl,c2) -> Cond.BinL(to_cond c1, bl, to_cond c2)
				| Not c -> Cond.Not (to_cond c)
		end

		module Record = struct

			let file = Config.log_file

			let write : string Lazy.t -> unit
				= fun s ->
				if !Flags.log_trace
				then begin
					let out_channel = Stdlib.open_out_gen [Open_creat ; Open_wronly ; Open_append] 0o640 !file in
					Stdlib.output_string out_channel ((Lazy.force s) ^ "\n");
					Stdlib.close_out(out_channel)
				end
		end

		module Names = struct
			let next : int ref = ref 0

			let mk : unit -> string
				= fun () -> begin
				let res = !next in
				next := !next + 1;
				Printf.sprintf "P%i" res
				end
		end

		module Track = struct
			let is_bottom : t -> unit
				= fun p ->
				lazy (Printf.sprintf "%s %s" Symbols.s_is_bottom p.name)
				|> Record.write

			let assume : Cond.t -> t -> string
				= fun cond p ->
				let next = Names.mk() in
				lazy (Printf.sprintf "%s %s %s %s %s"
					next
					Symbols.s_assign
					p.name
					Symbols.s_meet
					(Cond.to_string Pol.Var.to_string cond))
				|> Record.write;
				next

			let asserts : Cond.t -> t -> unit
				= fun cond p ->
				lazy (Printf.sprintf "%s %s in %s"
					Symbols.s_assert
					(Cond.to_string Pol.Var.to_string cond)
					p.name)
				|> Record.write

			let assign: (Var.t * Term.t) list -> t -> string
				= let assign_To_string : (Var.t * Term.t) list -> string
					= fun l ->
					List.map
						(fun (v,t) -> Printf.sprintf "%s %s %s"
							(Var.to_string v)
							Symbols.s_assign
							(Term.to_string Var.to_string t))
						l
					|> String.concat ", "
					|> Printf.sprintf "[%s]"
				in
				fun l p ->
				let next = Names.mk() in
				lazy (Printf.sprintf "%s %s %s in %s"
					next
					Symbols.s_assign
					(assign_To_string l)
					p.name)
				|> Record.write;
				next

			let guassign: (Var.t list) -> Cond.t -> t -> string
				= fun l cond p ->
				let next = Names.mk() in
				lazy (Printf.sprintf "guassign not implemented")
				|> Record.write;
				next

			let meet : t -> t -> string
				= fun p1 p2 ->
				let next = Names.mk() in
				lazy (Printf.sprintf "%s %s %s && %s"
					next Symbols.s_assign p1.name p2.name)
				|> Record.write;
				next

			let join : t -> t -> string
				= fun p1 p2 ->
				let next = Names.mk() in
				lazy (Printf.sprintf "%s %s %s %s %s"
					next Symbols.s_assign p1.name Symbols.s_join p2.name)
				|> Record.write;
				next

			let minkowski : t -> t -> string
				= fun p1 p2 ->
				let next = Names.mk() in
				lazy (Printf.sprintf "%s %s %s %s %s"
					next Symbols.s_assign p1.name Symbols.s_minkowski p2.name)
				|> Record.write;
				next

			let project : Var.t list -> t -> string
				= let print_vars : Var.t list -> string
					= fun vars ->
					String.concat "," (List.map Var.to_string vars)
					|> Printf.sprintf "[%s]"
				in
				fun vars p ->
				let next = Names.mk() in
				lazy (Printf.sprintf "%s %s %s %s %s"
					next Symbols.s_assign p.name Symbols.s_project (print_vars vars))
				|> Record.write;
				next

			let widen : t -> t -> string
				= fun p1 p2 ->
				let next = Names.mk() in
				lazy (Printf.sprintf "%s %s %s %s %s"
					next Symbols.s_assign p1.name Symbols.s_widen p2.name)
				|> Record.write;
				next

			let leq : t -> t -> unit
				= fun p1 p2 ->
				lazy (Printf.sprintf "%s %s %s" p1.name Symbols.s_includes p2.name)
				|> Record.write

			let getUpperBound : t -> Term.t -> unit
				= fun p t ->
				lazy (Printf.sprintf "%s %s in %s"
					Symbols.s_upper_bound (Term.to_string Var.to_string t) p.name)
				|> Record.write

			let getLowerBound : t -> Term.t -> unit
				= fun p t ->
				lazy (Printf.sprintf "%s %s in %s"
					Symbols.s_lower_bound (Term.to_string Var.to_string t) p.name)
				|> Record.write

			let itvize : t -> Term.t -> unit
				= fun p t ->
				lazy (Printf.sprintf "%s %s in %s" Symbols.s_itv (Term.to_string Var.to_string t) p.name)
				|> Record.write

			let translate : t -> Pol.Cs.Vec.t -> string
				= fun p vec ->
				let next = Names.mk() in
				lazy (Printf.sprintf "%s %s %s %s %s"
					next Symbols.s_assign p.name Symbols.s_translate
					(Pol.Cs.Vec.to_string Pol.Cs.Vec.V.to_string vec))
				|> Record.write;
				next

			let mapi : bool -> (int -> Pol.Cs.t -> Pol.Cs.t) -> (int -> Pol.Cs.t -> Pol.Cs.t) -> t -> string
				= fun _ _ _ _ ->
				let next = Names.mk() in
				next

		end

		(** Defines operators in terms of VPL datastructures. *)
		module BuiltIn = struct
			let mk: string -> I.t -> t
				= fun s p ->
				{value=p ; name = s}

			let top : t
				= mk "top" I.top

			let bottom : t
				= mk "bottom" I.bottom

			let to_string : (Var.t -> string) -> t -> string
				= fun varPr p ->
				I.to_string varPr p.value

			let is_bottom : t -> bool
				= let is_bottom' : t -> bool
					= fun p ->
					Track.is_bottom p;
					I.is_bottom p.value
				in
				fun p ->
				lazy (is_bottom' p)
				|> handle

			let assume :  Cond.t -> t -> t
				= let assume':  Cond.t -> t -> t
					= fun cond p ->
					let name = Track.assume cond p in
					mk name (I.assume cond p.value)
				in
				fun cond p ->
				lazy (assume' cond p)
				|> handle

			let asserts : Cond.t -> t -> bool
				= let asserts' : Cond.t -> t -> bool
					= fun cond p ->
					Track.asserts cond p;
					I.asserts cond p.value
				in
				fun cond p ->
				lazy (asserts' cond p)
				|> handle

			let assign : (Var.t * Term.t) list -> t -> t
				= let assign' : (Var.t * Term.t) list -> t -> t
					= fun l p ->
					let name = Track.assign l p in
					mk name (I.assign l p.value)
				in
				fun l p ->
				lazy (assign' l p)
				|> handle

			let guassign: (Var.t list) -> Cond.t -> t -> t
				= let guassign': (Var.t list) -> Cond.t -> t -> t
					= fun l cond p ->
					let name = Track.guassign l cond p in
					mk name (I.guassign l cond p.value)
				in
				fun l cond p ->
				lazy (guassign' l cond p)
				|> handle

			let meet : t -> t -> t
				= let meet' : t -> t -> t
					= fun p1 p2 ->
					let name = Track.meet p1 p2 in
					mk name (I.meet p1.value p2.value)
				in
				fun p1 p2 ->
				lazy (meet' p1 p2)
				|> handle

			let join : t -> t -> t
				= let join' : t -> t -> t
					= fun p1 p2 ->
					let name = Track.join p1 p2 in
					mk name (I.join p1.value p2.value)
				in
				fun p1 p2 ->
				lazy (join' p1 p2)
				|> handle

			let minkowski : t -> t -> t
				= let minkowski' : t -> t -> t
					= fun p1 p2 ->
					let name = Track.join p1 p2 in
					mk name (I.minkowski p1.value p2.value)
				in
				fun p1 p2 ->
				lazy (minkowski' p1 p2)
				|> handle

			let project: Var.t list -> t -> t
				= let project': Var.t list -> t -> t
					= fun vars p ->
					let name = Track.project vars p in
					mk name (I.project vars p.value)
				in
				fun vars p ->
				lazy (project' vars p)
				|> handle

			let projectM: Var.t list -> t -> t
				= let projectM': Var.t list -> t -> t
					= fun vars p ->
					let name = Track.project vars p in
					mk name (I.projectM vars p.value)
				in
				fun vars p ->
				lazy (projectM' vars p)
				|> handle

			let widen : t -> t -> t
				= let widen' : t -> t -> t
					= fun p1 p2 ->
					let name = Track.widen p1 p2 in
					mk name (I.widen p1.value p2.value)
				in
				fun p1 p2 ->
				lazy (widen' p1 p2)
				|> handle

			let leq : t -> t -> bool
				= let leq' : t -> t -> bool
					= fun p1 p2 ->
					Track.leq p1 p2;
					I.leq p1.value p2.value
				in
				fun p1 p2 ->
				lazy (leq' p1 p2)
				|> handle

			let getUpperBound : t -> Term.t -> Pol.bndT option
				= let getUpperBound' : t -> Term.t -> Pol.bndT option
					= fun p t ->
					Track.getUpperBound p t;
					I.getUpperBound p.value t
				in
				fun p t ->
				lazy (getUpperBound' p t)
				|> handle

			let getLowerBound : t -> Term.t -> Pol.bndT option
				= let getLowerBound' : t -> Term.t -> Pol.bndT option
					= fun p t ->
					Track.getLowerBound p t;
					I.getLowerBound p.value t
				in
				fun p t ->
				lazy (getLowerBound' p t)
				|> handle

			let itvize : t -> Term.t -> Pol.itvT
				= let itvize' : t -> Term.t -> Pol.itvT
					= fun p t ->
					Track.itvize p t;
					I.itvize p.value t
				in
				fun p t ->
				lazy (itvize' p t)
				|> handle

            (*************************************)
            (******* UNCERTIFIED OPERATORS *******)
            (*************************************)
			type rep = I.rep

			let backend_rep
				= let backend_rep' : t -> (rep * ((ProgVar.PVar.t -> ProgVar.PVar.t) * (ProgVar.PVar.t -> ProgVar.PVar.t))) option
					= fun p ->
					I.backend_rep p.value
				in
				fun p ->
				lazy (backend_rep' p)
				|> handle

            let get_cond : t -> Cond.t
                = fun p ->
                let (rep, toVar) = match backend_rep p with
                    | Some (p',(ofVar, toVar)) ->
                        let (_,_,toVar') = PedraQOracles.export_backend_rep (p',(ofVar,toVar)) in
                        (p', toVar')
                    | _ -> Stdlib.failwith "get_cond"
                in
                Pol.get_cstr rep
                |> List.map (fun cstr -> Pol.Cs.rename_f toVar cstr)
                |> Cond.of_cstrs

			let translate : t -> Pol.Cs.Vec.t -> t
				= let translate' : t -> Pol.Cs.Vec.t -> t
					= fun p vec ->
					let name = Track.translate p vec in
					mk name (I.translate p.value vec)
				in
				fun p vec ->
				lazy (translate' p vec)
				|> handle

			let mapi : bool -> (int -> Pol.Cs.t -> Pol.Cs.t) -> (int -> Pol.Cs.t -> Pol.Cs.t) -> t -> t
				= let mapi' : bool -> (int -> Pol.Cs.t -> Pol.Cs.t) -> (int -> Pol.Cs.t -> Pol.Cs.t) -> t -> t
					= fun b f1 f2 p ->
					let name = Track.mapi b f1 f2 p in
					mk name (I.mapi b f1 f2 p.value)
				in
				fun b f1 f2 p ->
				lazy (mapi' b f1 f2 p)
				|> handle

			let diff : t -> t -> t list
				= let compl : Pol.Cs.t -> Pol.Cs.t
					= fun cstr ->
					(* Complement that keeps the same comparison sign *)
					{(Cs.compl cstr) with Cs.typ = Cs.get_typ cstr}
					in
				let diff' = fun p1 p2 ->
				let (rep1,rep2, toVar2) = match backend_rep p1, backend_rep p2 with
					| Some (p1',_), Some (p2', (ofVar2, toVar2)) ->
						let (_,_,toVar2') = PedraQOracles.export_backend_rep (p2',(ofVar2,toVar2))
						in
						(p1',p2', toVar2')
					| _, _ -> Stdlib.failwith "diff"
				in
				let p2_ineqs = Pol.get_ineqs rep2
					|> List.map (fun (cstr,_) -> Pol.Cs.rename_f toVar2 cstr)
				in
				if p2_ineqs = []
				then [p1]
				else
					let hd = List.hd p2_ineqs in
					let fst_res = assume (Cond.of_cstrs [compl hd]) p1
					and fst_cont = assume (Cond.of_cstrs [hd]) p1
					in
					List.fold_left
						(fun (res,cont) ineq ->
							let pol_cont = List.hd cont in
							(assume (Cond.of_cstrs [compl ineq]) pol_cont :: res,
							 assume (Cond.of_cstrs [ineq]) pol_cont :: cont))
						([fst_res],[fst_cont]) (List.tl p2_ineqs)
					|> Stdlib.fst
			in
			fun p1 p2 ->
			lazy (diff' p1 p2)
			|> handle

            let get_regions : t -> t list
				= let get_regions' p =
                    let (rep, toVar) = match backend_rep p with
    					| Some (p',(ofVar, toVar)) ->
                            let (_,_,toVar') = PedraQOracles.export_backend_rep (p',(ofVar,toVar)) in
                            (p', toVar')
    					| _ -> Stdlib.failwith "get_regions"
    				in
                    let regions = Pol.get_regions Factory.Unit.factory rep in
                    List.map
                        (fun reg ->
                            let cond = Pol.get_cstr reg
                                |> List.map (fun cstr -> Pol.Cs.rename_f toVar cstr)
                                |> Cond.of_cstrs
                                in
                            assume cond top
                            )
                        regions
                in
                fun p ->
				lazy (get_regions' p)
				|> handle

            let size : t -> Scalar.Rat.t option
                = let size' p =
                    let rep = match backend_rep p with
    					| Some (p',_) -> p'
    					| _ -> Stdlib.failwith "size"
    				in
                    Pol.size rep
                in
                fun p ->
                lazy (size' p)
                |> handle
		end

		include BuiltIn

		(** Defines operators in terms of the User datastructures. *)
		module User = struct
			include BuiltIn

			let assume: UserCond.t -> t -> t
				= fun c p ->
				assume (UserCond.to_cond c) p

			let asserts: UserCond.t -> t -> bool
				= fun c p ->
				asserts (UserCond.to_cond c) p

			let assign: (Expr.Ident.t * Expr.t) list -> t -> t
				= fun l p ->
				assign
					(List.map (fun (v,e) -> Expr.Ident.toVar v, Expr.to_term e) l)
					p

			let project: Expr.Ident.t list -> t -> t
				= fun vars p ->
				let vars' = List.map Expr.Ident.toVar vars in
				project vars' p

			let projectM: Expr.Ident.t list -> t -> t
				= fun vars p ->
				let vars' = List.map Expr.Ident.toVar vars in
				projectM vars' p

			let guassign: (Expr.Ident.t list) -> UserCond.t -> t -> t
				= fun vl c p ->
				guassign (List.map Expr.Ident.toVar vl) (UserCond.to_cond c) p

			let getUpperBound : t -> Expr.t -> Pol.bndT option
				= fun p expr ->
				getUpperBound p (Expr.to_term expr)

			let getLowerBound : t -> Expr.t -> Pol.bndT option
				= fun p expr ->
				getLowerBound p (Expr.to_term expr)

	  		let itvize : t -> Expr.t -> Pol.itvT
	  			= fun p expr ->
				itvize p (Expr.to_term expr)
		end
	end
end

module Lift_Ident (I : sig
    type t
	val compare: t -> t -> int
	val to_string: t -> string
    end) = struct

    type t = I.t

    let compare = I.compare

    module Map_var_to_t = Map.Make(struct
		include Var
		let compare = cmp
		end)

	module Map_t_to_var = Map.Make(I)


	type map_var_to_t = t Map_var_to_t.t
	type map_t_to_var = Var.t Map_t_to_var.t

    type mapsT = {
		var_to_t : map_var_to_t ;
		t_to_var : map_t_to_var ;
		next : Var.t
    }

	let emptyMaps = {
		var_to_t = Map_var_to_t.empty ;
		t_to_var = Map_t_to_var.empty ;
		next = Var.u
    }

    let maps : mapsT ref = ref emptyMaps

    let print_maps : unit -> unit
		= fun () ->
		Printf.sprintf "map var to t : \n\t%s\nmap t to var: \n\t%s"
			(Misc.list_to_string
				(fun (v,v') -> Printf.sprintf "%s -> %s"
					(Var.to_string v)
                    (I.to_string v'))
				(Map_var_to_t.bindings !maps.var_to_t)
				" ; ")
			(Misc.list_to_string
				(fun (v',v) -> Printf.sprintf "%s -> %s"
					(I.to_string v')
                    (Var.to_string v))
				(Map_t_to_var.bindings !maps.t_to_var)
				" ; ")
		|> print_endline

    let mem : t -> bool
		= fun s -> Map_t_to_var.mem s !maps.t_to_var

    let addVars : t list-> unit
		= fun vars ->
            maps := List.fold_left
				(fun m var ->
				if mem var
                then m
				else {
					var_to_t = Map_var_to_t.add m.next var m.var_to_t ;
					t_to_var = Map_t_to_var.add var m.next m.t_to_var ;
					next = Var.next m.next
                })
				!maps vars

    let toVar : t -> Var.t
		= fun var ->
        if mem var
        then Map_t_to_var.find var !maps.t_to_var
        else begin
            let new_var = !maps.next in
            maps := {
				var_to_t = Map_var_to_t.add new_var var !maps.var_to_t ;
				t_to_var = Map_t_to_var.add var new_var !maps.t_to_var ;
				next = Var.next !maps.next
            };
            new_var
        end


	let ofVar : Var.t -> t
		= fun s -> Map_var_to_t.find s !maps.var_to_t

    let to_string: t -> string
		= fun var -> I.to_string var

	let get_string : Var.t -> string
		= fun var ->
		Map_var_to_t.find var !maps.var_to_t
        |> I.to_string
end

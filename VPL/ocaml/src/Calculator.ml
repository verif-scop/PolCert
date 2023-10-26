(** Test de Calculatrice avec la nouvelle UserInterface.ml*)
module CP = CstrPoly.Positive
module Poly = CP.Poly

include UserInterface.Interface(Scalar.Rat)

let folder = "/tmp/"

(** Donne le nombre d'occurence d'une string dans une string list **)
let nbOcc (s:string) (sl:string list):int
	= List.fold_left
		(fun n s' -> if (String.compare s s') = 0 then 1 + n else n)
		0 sl

let  oneOccListe (sl:string list):string list
	= List.fold_left (fun sl' s -> if (nbOcc s sl' ) = 0 then s::sl' else sl') [] sl

let rec getStringVar (p:PolyParserBuild.poly) : string list
	= match p with
	|PolyParserBuild.Leaf(ss,_) -> List.map Stdlib.fst ss
	|PolyParserBuild.Add(p1,p2) |PolyParserBuild.Mul(p1,p2) |PolyParserBuild.Sub(p1,p2) -> (getStringVar p1) @ (getStringVar p2)


module Ident = UserInterface.Lift_Ident (struct
    type t = string
    let compare = Stdlib.compare
    let to_string s = s
    end)

module Expr = struct

	type t = PolyParserBuild.poly

	exception Out_of_Scope

	module Ident = Ident

	let rec poly_to_pol_rec : PolyParserBuild.poly -> Poly.t
		= fun p ->
			match p with
			|PolyParserBuild.Leaf(l,coeff) -> [(List.map (fun el -> (Ident.toVar (Stdlib.fst el), Stdlib.snd el)) l,coeff)] |> Poly.mk3
			|PolyParserBuild.Add(p1,p2) -> Poly.add (poly_to_pol_rec p1) (poly_to_pol_rec p2)
			|PolyParserBuild.Sub(p1,p2) -> Poly.sub (poly_to_pol_rec p1) (poly_to_pol_rec p2)
			|PolyParserBuild.Mul(p1,p2) -> Poly.mul (poly_to_pol_rec p1) (poly_to_pol_rec p2)

	let to_poly: t -> Poly.t
		= fun p -> poly_to_pol_rec p

	let poly_to_term : Poly.t -> Term.t
		= fun p ->
		let term_list = List.map
			(fun (vl,c) ->
			let l = Term.Prod (List.map (fun v -> Term.Var v) vl)
			in
			Term.Mul (Term.Cte c, l))
			(Poly.data2 p)
		in
		Term.Sum term_list

	let to_term : t -> Term.t
		= fun p ->
		to_poly p |> poly_to_term
end

(*module VPL = Interface(CDomain.PedraQWrapper)(Expr)*)
module VPL = Interface(NCDomain.NCVPL_Unit.Q)(Expr)

let polyCP_to_polCP : PolyParserBuild.contrainte list -> VPL.UserCond.t
	= fun l ->
	List.fold_left
		(fun res (e1,cmp,e2) ->
			let atom = VPL.UserCond.Atom (e1,cmp,e2) in
			VPL.UserCond.BinL (res, CWrappers.AND, atom))
		(VPL.UserCond.Basic true)
		l

let stmtl_list_to_vpl : PolyParserBuild.stmt list -> VPL.t
	= fun stmt_list ->
	List.fold_left
		(fun vpl stmt ->
		match stmt with
		| PolyParserBuild.Constraints l -> VPL.User.assume (polyCP_to_polCP l) vpl
		| PolyParserBuild.Assigns l ->
			Ident.addVars (List.map (fst) l); VPL.User.assign l vpl) VPL.top stmt_list

let parse : string -> VPL.t =
	fun s ->
		stmtl_list_to_vpl (PolyParser.one_stmt_list PolyLexer.token (Lexing.from_string s))


let string_to_var_list : string -> string list
	= fun s -> PolyParser.one_var_list PolyLexer.token (Lexing.from_string s)
		|> Misc.rem_dupl (fun s1 s2 -> String.compare s1 s2 = 0)

module Print = struct

	let get_cstrs : VPL.t -> Pol.Cs.t list
		= fun p ->
		match VPL.backend_rep p with
		| None -> []
		| Some (p,(ofVar,toVar)) ->
			let (p',_,toVar') = PedraQOracles.export_backend_rep (p,(ofVar,toVar)) in
			let convert c =
				let v' = Pol.Cs.get_v c
					|> Pol.Cs.Vec.toList
					|> List.map (fun (v,c) -> c, (toVar' v))
					|> Pol.Cs.Vec.mk
				in
				{c with Pol.Cs.v = v'}
			in
			List.map (fun (_,c) -> Pol.Cons.get_c c |> convert) (Pol.get_eqs p')
			@ List.map (fun c -> Pol.Cons.get_c c |> convert) (Pol.get_ineqs p')

	let get_eqs_and_ineqs : VPL.t -> Pol.Cs.t list * Pol.Cs.t list (*eqs, ineqs*)
		= fun p ->
			get_cstrs p
			|> List.partition (fun c -> Pol.Cs.get_typ c = Cstr.Eq)

	let cs_string : string list -> string
		= fun l ->
		String.concat ", " (List.map (fun s -> "ring(\"" ^ s ^ "\")") l)

	let eq_string : string list -> string
		=fun sl -> "p_eq = ["^(String.map (fun c -> if c = '.' then '*' else c) (cs_string sl))^" ]\n"

	let ineq_string : string list -> string
		=fun sl -> "p_ineq = ["^(String.map (fun c -> if c = '.' then '*' else c) (cs_string sl))^" ]\n"

	let sage_beginning_string = "# coding=UTF-8\n"^PLPPlot.str_to_ieq^PLPPlot.str_projection^PLPPlot.str_plot_polyhedra^
		PLPPlot.str_plot_polynomial^
		PLPPlot.str_color^
		PLPPlot.str_color_from_polyhedra

	let var_list_to_parameters : string list -> string =
		fun sl -> List.fold_left (fun s sel -> s^"\""^sel^"\",") "" sl

	let getVars : VPL.t -> string list
		=  fun p ->
		get_cstrs p
		|> Pol.Cs.getVars
		|> Pol.Cs.Vec.V.Set.elements
		|> List.map (Ident.get_string)

	let occurIn : string -> string list -> bool
		= fun e el -> List.fold_left (fun b s -> b || s = e) false el

	(** [filter_vars l1 l2] filters [l1] so that no element of [l2] remains in [l1]. *)
	let filter_vars : string list -> string list -> string list
		= fun sl sl2 -> List.filter (fun s -> not (occurIn s sl2)) sl

	(** [prepare_p p sl] prepares polyhedron [p] for plotting, projecting variables from [sl] if necessary. *)
	let prepare_p : VPL.t -> string list -> VPL.t
		= fun p sl ->
		if sl = [] then p else
		let vars_to_project = filter_vars (getVars p) sl in
		VPL.User.projectM vars_to_project p

	(** If the polyhedron is plotted on one or two dimensions, the image is saved to be shown after Sage has terminated.
	Otherwise, it is directly plotted, as Jmol still works when Sage terminates. *)
	let sage_ending_string : int -> string
		= fun nbdim -> if nbdim <= 2
		then
			"\nto_plot.save(\"" ^ folder ^ "/pol.png\")\nimport time\ntime.sleep(2)"
		else "\nto_plot.show()\nimport time\ntime.sleep(10)"

	(** Translates a list of constraints into Sage constraints strings. *)
	let cs_list_to_string_list : Pol.Cs.t list -> string list
		= fun l ->
		List.map
			(fun c ->
				Printf.sprintf "-1 * (%s) + %s"
				(Pol.Cs.Vec.to_string Ident.get_string (Pol.Cs.get_v c ))
				(Pol.Cs.Vec.Coeff.to_string c.Pol.Cs.c))
			l

	let to_plot_custom : string list -> string list -> string -> int -> string
		= fun eq_list ineq_list parametres nb_dimens ->
		"\nparameters = [ "^parametres^" ]\n"^
		"ring = PolynomialRing(QQ,parameters,len(parameters))\n"^
		"nb_dim = "^(string_of_int nb_dimens)^"\n"^
		(eq_string eq_list)^
		(ineq_string ineq_list)^
		"\nineqs = [to_ieq(c,ring,parameters) for c in p_ineq]\n"^
		"eqs = [to_ieq(c,ring,parameters) for c in p_eq]\n"^
		"P = [Polyhedron(eqns = eqs,ieqs = ineqs)]\n"^
		"color_from_polyhedra(P)\nto_plot = plot_polyhedra(P, nb_dim)"

	let to_plot_for_show ?vars:(vars = "") (po:VPL.t) : string*int
		= let p = prepare_p po (string_to_var_list vars) in
		let var_list = (if vars <> "" then string_to_var_list vars else getVars p) in
		let parametres = var_list_to_parameters var_list in
		let cs_lists = get_eqs_and_ineqs p in
		let eq_list = cs_list_to_string_list (fst cs_lists) and ineq_list = cs_list_to_string_list (snd cs_lists) in
		let nb_dim = List.length var_list in
		((to_plot_custom eq_list ineq_list parametres nb_dim)^(sage_ending_string nb_dim),nb_dim)

	(** Gives the Sage string corresponding to the given polyhedron. *)
	let to_plot : VPL.t -> string
		= fun p -> fst (to_plot_for_show p)

	let write_file : string -> string -> unit
		= fun file message ->
	  (* Write message to file *)
	  let oc = open_out file in    (* create or truncate file, return channel *)
	  Printf.fprintf oc "%s\n" message;   (* write something *)
	  close_out oc              (* flush and close the channel *)

	let append_file : string -> string -> unit
		= fun file message ->
	  (* Write message to file *)
	  let oc = open_out_gen [Open_append] 777 file in    (* create or truncate file, return channel *)
	  Printf.fprintf oc "%s\n" message;   (* write something *)
	  close_out oc              (* flush and close the channel *)
end

(**
affiche le polyhedre avec comme argument optionnel les variables à regarder **)
let show ?vars:(vars = "") (po:VPL.t) : unit =
	let (body_string,nb_dim) = (Print.to_plot_for_show ~vars:vars po) in
	let u = Print.write_file (folder ^ "/pol.sage") (Print.sage_beginning_string^body_string) in
	let _ = Print.write_file (folder ^ "/launch_command") ("runfile " ^ folder ^ "/pol.sage") in
	let _ = Sys.command ("sage < " ^ folder ^ "/launch_command"^(if nb_dim <= 2 then "\neog " ^ folder ^ "/pol.png" else "")) in u

let show_regions : unit -> unit
	= fun () ->
	let _ = Print.append_file Config.sage_log "\nimport time\ntime.sleep(5)\n" in
	let _ = Print.write_file (folder ^ "/launch_command") ("runfile " ^ Config.sage_log) in
	let _ = Sys.command
		("sage < " ^ folder ^ "/launch_command") in
	()

(**
affiche toutes les contraintes et affectations du polyhèdre
**)
let print : VPL.t -> unit
	= fun p ->
	VPL.to_string Ident.get_string p
	|> print_endline

module Notations = struct
	let (&&) pol1 pol2 = VPL.meet pol1 pol2 (** VPL.t && VPL.t **)
	let (||) pol1 pol2 = VPL.join pol1 pol2 (** VPL.t || VPL.t **)
	let (|-) a b =
		let var_list = (string_to_var_list b) in
		Ident.addVars var_list ;
		VPL.User.projectM var_list a (** VPL.t |- string **)
end

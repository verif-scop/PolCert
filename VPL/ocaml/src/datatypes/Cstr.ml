type cmpT_extended
	= EQ | LE | LT | GE | GT | NEQ

let cmpT_extended_to_string = function
	| EQ -> "="
	| LE  -> "<="
	| LT  -> "<"
	| GE -> ">="
	| GT -> ">"
	| NEQ -> "≠"

type cmpT
	= Eq | Le | Lt

let cmpT_to_string = function
  | Eq -> "="
  | Le -> "<="
  | Lt -> "<";;

(** Affine constraints and operations on them. *)
module type Type = sig
	module Vec : Vector.Type

	(** The main type for affine contraints.
	A constraint [c] of type [t] represents [c.v c.typ c.c]. *)
	type t = {
		typ : cmpT; (** the comparison operator *)
		v: Vec.t; (** the linear term *)
		c: Vec.Coeff.t (** the constant *) }

	val name : string

	val get_typ : t -> cmpT
	val get_v : t -> Vec.t
	val get_c : t -> Vec.Coeff.t


	(** [pr b c] pretty-prints contraint [c] using the variables and their names from [b]. *)
	val to_string : (Vec.V.t -> string) -> t -> string

	val list_to_string : t list -> string

	val plot : Vec.V.t list -> t -> string

	val list_plot : t list -> string

	(** The type of properties the can be told by examining a constraint on its own. *)
	type prop_t =
	| Trivial (** 0 = 0 or 0 < 1 are Trivial *)
	| Contrad (** trivialy contradictory: e.g. 0 = 1 or 0 <  -1 *)
	| Nothing (** neither trivial nor trivialy contradictory *)

	(** See [mult]. *)
	exception BadMult

	(** See [elim]. *)
	exception CannotElim

	(** See [elim]. *)
	exception NoElim

	val cmpAdd: cmpT -> cmpT -> cmpT

	(** Compute the complement constraint to the given inequality.
	If the supplied linear constraint is an equality, [Invalid_argument "Cstr.compl"] is raised. *)
	val compl: t -> t

	(** Split the given equality (e.g. x = 1) into the two equivalent inequalities (e.g. x <= 1 and -x <= -1).
	If the supplied constraint is not an equality, [Invalid_argument "Cstr.split"] is raised. *)
	val split: t -> t * t

	(** [mk typ coefs cst] builds the linear constraint [coefs typ cst],
	where each member of [coefs] gives the coefficient of a given variable.
	Zero coefficients can be left implicit. *)
	val mk: cmpT -> (Vec.Coeff.t * Vec.V.t) list -> Vec.Coeff.t -> t

	val mk2: cmpT -> Vec.t -> Vec.Coeff.t -> t

	(** [eq lin cst] builds the equality [lin = cst],
	where each member of [lin] is the coefficient of a variable.
	Zero coefficients can be left implicit. *)
	val eq: (Vec.Coeff.t * Vec.V.t) list -> Vec.Coeff.t -> t

	(** [le lin cst] builds the non-strict inequality [lin <= cst],
	where each member of [lin] is the coefficient of a variable.
	Zero coefficients can be left implicit. *)
	val le: (Vec.Coeff.t * Vec.V.t) list -> Vec.Coeff.t -> t

	(** [lt lin cst] builds the strict inequality [lin < cst],
	where each member of [lin] is the coefficient of a variable.
	Zero coefficients can be left implicit. *)
	val lt: (Vec.Coeff.t * Vec.V.t) list -> Vec.Coeff.t -> t

	(** [mkInt] is equivalent to [mk] but transforms [coefs] < [cst] into [coefs] <= ([cst] - 1). *)
	val mkInt: cmpT -> (Vec.Coeff.t * Vec.V.t) list -> Vec.Coeff.t -> t

	(** Check the syntactical equality of two constraints.
	x = 1 and x = 1 are syntactically equal, but not 2 * x = 2 and x = 1. *)
	val equalSyn: t -> t -> bool

	(** Check the syntactical inclusion of one constraint in another.
	The linear term of both constraints must be syntactically equal.
	x = 0 is included in x < 1, but not is 2 * x < 2. *)
	val inclSyn: t -> t -> bool

	(** [equal c1 c2] checks whether the subspace described by [c1] is equal to that of [c2]. *)
	val equal: t -> t -> bool

	(** [incl c1 c2] checks whether the subspace described by [c1] is included in that of [c2]. *)
	val incl: t -> t -> bool

	(** Add two constraints. *)
	val add: t -> t -> t

	(** Multiply a constraint by a constant.
	If a negative constant is provided and the constraint is an inequality, then [BadMult] is raised. *)
	val mulc: Vec.Coeff.t -> t -> t

	(** Tell what can be infered on a constraint on its own.  See [prop_t]. *)
	val tellProp: t -> prop_t

	(** Build the set of variables which appear with non-zero coefficients in the constraints. *)
	val getVars: t list -> Vec.V.Set.t

	(** [getCoefsFor mx l] gathers the "coefficient" of [mx] in the constraints
	in [l]. If [mx] is [None] then the constants are gathered. If [mx] is
	[Some x], the coefficients of variable [x] are gathered. The order of the
	numbers in the returned list matches that of the constraints in [l]. *)
	val getCoefsFor : Vec.V.t option -> t list -> Vec.Coeff.t list

	(** Syntaxic comparison *)
	val cmp : t -> t -> int

	(** [eval c x] checks that the given point [x] satisfies the constraint [c]. *)
	val eval: t -> Vec.t -> bool

	(** [eval' c point] computes [a.point - b], where [c : ax cmp b]. *)
	val eval': t -> Vec.t -> Vec.Coeff.t

	(** [satisfy vec cstr] returns true if point [vec] satisfies constraint [cstr]. *)
	val satisfy : Vec.t -> t -> bool

	(** [saturate vec cstr] returns true if [vec] satisfies constraint [cstr] where [cstr.typ] has been replaced by {!const:cmpT.Eq}. *)
	val saturate : Vec.t -> t -> bool

	(** Rename fromX toY c *)
	val rename : Vec.V.t -> Vec.V.t -> t -> t

	val rename_f : (Vec.V.t -> Vec.V.t) -> t -> t

	(** [change_variable x lin c cstr] proceeds to the change of variable [x = lin + c] in [cstr]. *)
	val change_variable : Vec.V.t -> Vec.t -> Vec.Coeff.t -> t -> t

	(** Returns a point that saturates the hyperplane defined by the given constraint. *)
	val get_saturating_point : t -> Vec.t
end

module Cstr (Vec : Vector.Type) = struct

	module Coeff = Vec.Coeff
	module M = Vec.M
	module V = Vec.V

	let name = "Constraint with vector type : " ^ (Vec.name)

	type t = {
		typ: cmpT;
		v: Vec.t;
		c: Coeff.t }

	let get_typ (x : t) = x.typ
	let get_v (x : t) = x.v
	let get_c (x : t) = x.c

	type cstr_t = t

	type prop_t =
	| Trivial
	| Contrad
	| Nothing

	exception BadMult
	exception CannotElim
	exception NoElim

	let cmpAdd : cmpT -> cmpT -> cmpT
	= fun o1 o2 ->
		match o1 with
		| Eq -> o2
		| Lt as o -> o
		| Le as o ->
			match o2 with
			| Eq | Le -> o
			| Lt as o -> o

	let eval' : t -> Vec.t -> Coeff.t
		= fun c pt ->
		Coeff.sub (M.fold (fun _ -> Coeff.add) Coeff.z (Vec.mul_t c.v pt)) c.c

	let eval : t -> Vec.t -> bool
		= fun c pt ->
		let r = Coeff.cmp (M.fold (fun _ -> Coeff.add) Coeff.z (Vec.mul_t c.v pt)) c.c
		in
		match c.typ with Eq -> r = 0 | Le -> r <= 0 | Lt -> r < 0

	let add : t -> t -> t
		= fun c1 c2 ->
		{typ = cmpAdd c1.typ c2.typ;
		v = Vec.add c1.v c2.v;
		c = Coeff.add c1.c c2.c }

	(* XXX: c'est vraiment ce qu'on veut?*)
	let mulc : Coeff.t -> t -> t
		= fun c cstr ->
		if cstr.typ <> Eq && Coeff.le c Coeff.z
		then Stdlib.raise BadMult
		else { cstr with v = Vec.mulc c cstr.v; c = Coeff.mul c cstr.c }

	let compl : t -> t
		= fun c ->
		match c.typ with
		| Eq -> invalid_arg "Cstr.compl"
		| Le -> { typ = Lt; v = Vec.neg c.v; c = Coeff.neg c.c }
		| Lt -> { typ = Le; v = Vec.neg c.v; c = Coeff.neg c.c }

	let split : t -> t * t
		= fun c ->
		match c.typ with
		| Le | Lt -> invalid_arg "Cstr.split"
		| Eq -> ({ typ = Le; v = c.v; c = c.c },
			{ typ = Le; v = Vec.neg c.v; c = Coeff.neg c.c })

	let mk typ v c = { typ = typ; v = Vec.mk v; c = c }
	let mk2 typ v c = { typ = typ; v = v; c = c }
	let eq v c = mk Eq v c
	let le v c = mk Le v c
	let lt v c = mk Lt v c

	let mkInt typ v c =
		match typ with
		| Eq | Le -> { typ = typ; v = Vec.mk v; c = c }
		| Lt -> { typ = Le; v = Vec.mk v; c = Coeff.sub c Coeff.u }

	let equalSyn c1 c2 =
		c1.typ = c2.typ && Vec.equal c1.v c2.v && Coeff.equal c1.c c2.c

	let inclSyn c1 c2 =
		if Vec.equal c1.v c2.v then
			match c1.typ, c2.typ with
			| Eq, Eq -> Coeff.cmp c1.c c2.c = 0
			| Eq, Le | Le, Le
			| Lt, Lt | Lt, Le -> Coeff.cmp c1.c c2.c <= 0
			| Eq, Lt | Le, Lt -> Coeff.cmp c1.c c2.c < 0
			| Le, Eq | Lt, Eq -> false
		else
			false

	let equal c1 c2 =
		if c1.typ <> c2.typ then
			false
		else

		match Vec.isomorph c1.v c2.v with
		| None ->
			if Vec.equal Vec.nil c1.v && Vec.equal Vec.nil c2.v then
				Coeff.cmp c1.c c2.c = 0
			else
				false

		| Some ratio ->
			if Coeff.cmpz ratio > 0 then
				if c1.typ = Eq then
					Coeff.cmp c1.c (Coeff.mul ratio c2.c) = 0
				else
					false
			else
				Coeff.cmp c1.c (Coeff.mul ratio c2.c) = 0

	let incl c1 c2 =
		if Vec.equal Vec.nil c2.v
		then let r = Coeff.cmpz c2.c in
			(match c2.typ with
			| Eq -> r = 0
			| Le -> r <= 0
			| Lt -> r < 0)
		else if Vec.equal Vec.nil c1.v
			then false
			else match Vec.isomorph c1.v c2.v with
				| None -> false
				| Some ratio ->
					let res = Coeff.cmp c1.c (Coeff.mul ratio c2.c) in
					match c1.typ, c2.typ with
					| Eq, Eq -> res = 0
					| Le, Le | Lt, Lt
					| Lt, Le -> Coeff.cmpz ratio < 0 && res <= 0
					| Le, Lt -> Coeff.cmpz ratio < 0 && res < 0
					| Eq, Le -> res <= 0
					| Eq, Lt -> res < 0
					| Le, Eq | Lt, Eq -> false

	let tellProp c =
		if Vec.equal Vec.nil c.v then
			let r = Coeff.cmpz c.c in
			match c.typ with
			| Eq -> if r = 0 then Trivial else Contrad
			| Le -> if r <= 0 then Trivial else Contrad
			| Lt -> if r < 0 then Trivial else Contrad
		else
			Nothing

	let getVars: t list -> V.Set.t
	= fun l -> List.map get_v l |> Vec.getVars

	let getCoefsFor : V.t option -> t list -> Coeff.t list
	= function
		| None -> fun l -> List.map get_c l
		| Some x -> fun l -> List.map (fun c -> Vec.get (get_v c) x) l

	let to_string : (V.t -> string) -> t -> string
		= fun varPr c ->
			let sign =
				match c.typ with
				| Eq -> " = "
				| Le -> " <= "
				| Lt -> " < "
			in
			(Vec.to_string varPr c.v) ^ sign ^ (Coeff.to_string c.c)

	let plot : V.t list -> t -> string
		= fun vars c ->
		let vec = get_v c in
		let l = (get_c c) ::
			(List.map
				(fun v -> Coeff.mul Coeff.negU (Vec.get vec v))
				vars)
		in
		Misc.list_to_string Coeff.to_string l ","

	let list_plot : t list -> string
		= fun cstrs ->
		let vars = getVars cstrs |> V.Set.elements in
		Misc.list_to_string (plot vars) cstrs ", "

	let list_to_string : t list -> string
		= fun l ->
		Misc.list_to_string (to_string V.to_string) l " ; "


	let rec cmp : t -> t -> int
		= fun c1 c2 ->
		match (c1.typ,c2.typ) with
		| (Eq,Le) | (Le,Lt) | (Eq,Lt) -> -1
		| (Le,Eq) | (Lt,Le) | (Lt,Eq) -> 1
		| (_,_) ->	begin
			match Vec.cmp c1.v c2.v with
			| 0 -> Coeff.cmp c1.c c2.c
			| r -> r
			end

	let satisfy : Vec.t -> t -> bool
		= fun point c ->
		let res = M.fold (fun _ -> Coeff.add) Coeff.z (Vec.mul_t point c.v) in
		let r = Coeff.cmp res c.c in
		match c.typ with
		| Eq -> r = 0
		| Le -> r <= 0
		| Lt -> r < 0

	let saturate : Vec.t -> t -> bool
		= fun point c ->
		satisfy point {c with typ = Eq}

	let rename : Vec.V.t -> Vec.V.t -> t -> t
		= fun fromX toY c ->
		let v = get_v c in
		let v1 = Vec.set v fromX Vec.Coeff.z in
		let v2 = Vec.set v1 toY (Vec.get v fromX) in
		assert (Vec.Coeff.cmpz (Vec.get v toY) = 0);
		{c with v = v2}

	let rename_f : (Vec.V.t -> Vec.V.t) -> t -> t
		= fun f cstr ->
		List.fold_left
    		(fun cstr' var -> rename var (f var) cstr')
    		cstr
    		(getVars [cstr] |> Vec.V.Set.elements)

	(* TODO: vérifier la présence de x? *)
	let change_variable : Vec.V.t -> Vec.t -> Coeff.t -> t -> t
		= fun x lin c cstr ->
		let v = get_v cstr in
		let coeff = Vec.get v x in
		let v1 = Vec.set v x Vec.Coeff.z in
		let v2 = Vec.mulc coeff lin
			|> Vec.add v1 in
		let c2 = Coeff.sub (get_c cstr) (Coeff.mul coeff c) in
		{cstr with v = v2 ; c = c2}

	let get_saturating_point : t -> Vec.t
		= fun cstr ->
		let (var,coeff) = Vec.toList cstr.v
			|> List.hd in
		Vec.mk [Coeff.div cstr.c coeff, var]
end

module Rat = struct

	(* XXX: Comment faire pour éviter de redéfinir tout? *)
	(** This module type is the same as {!modtype:Cstr.Type} but where {!module:Cstr.Type.Vec} is restricted to {!modtype:Vector.Rat.Type}. *)
	module type Type = sig
		module Vec : Vector.Rat.Type
		(**/**)
		type t = {
			typ : cmpT;
			v: Vec.t;
			c: Vec.Coeff.t  }

		val get_typ : t -> cmpT
		val get_v : t -> Vec.t
		val get_c : t -> Vec.Coeff.t

		val to_string : (Vec.V.t -> string) -> t -> string
		val plot : Vec.V.t list -> t -> string
		val list_to_string : t list -> string
		val list_plot : t list -> string

		type prop_t =
		| Trivial
		| Contrad
		| Nothing

		exception BadMult
		exception CannotElim
		exception NoElim

		val name : string
		val cmpAdd: cmpT -> cmpT -> cmpT
		val compl: t -> t
		val split: t -> t * t
		val mk: cmpT -> (Vec.Coeff.t * Vec.V.t) list -> Vec.Coeff.t -> t
		val mk2: cmpT -> Vec.t -> Vec.Coeff.t -> t
		val eq: (Vec.Coeff.t * Vec.V.t) list -> Vec.Coeff.t -> t
		val le: (Vec.Coeff.t * Vec.V.t) list -> Vec.Coeff.t -> t
		val lt: (Vec.Coeff.t * Vec.V.t) list -> Vec.Coeff.t -> t
		val mkInt: cmpT -> (Vec.Coeff.t * Vec.V.t) list -> Vec.Coeff.t -> t
		val equalSyn: t -> t -> bool
		val inclSyn: t -> t -> bool
		val equal: t -> t -> bool
		val incl: t -> t -> bool
		val add: t -> t -> t
		val mulc: Vec.Coeff.t -> t -> t
		val tellProp: t -> prop_t
		val getVars: t list -> Vec.V.Set.t
		val getCoefsFor : Vec.V.t option -> t list -> Vec.Coeff.t list
		val cmp : t -> t -> int
		val eval: t -> Vec.t -> bool
		val eval': t -> Vec.t -> Vec.Coeff.t
		val satisfy : Vec.t -> t -> bool
		val saturate : Vec.t -> t -> bool
		val elim : t -> t -> Vec.V.t -> (t * Vec.Coeff.t * Vec.Coeff.t)
		val rename : Vec.V.t -> Vec.V.t -> t -> t
		val rename_f : (Vec.V.t -> Vec.V.t) -> t -> t
		val change_variable : Vec.V.t -> Vec.t -> Vec.Coeff.t -> t -> t
		val get_saturating_point : t -> Vec.t
		(**/**)

		(** Put the constraint in canonic form. *)
		val canon : t -> t

	end

	module Rat (Vec : Vector.Rat.Type) = struct

		include Cstr(Vec)

		(** [elim c1 c2 x] linearly combines [t1] and [t2] so as to eliminate [x] from the result.
		The coefficients applied to [c1] and [c2] are returned, in order.
		If [x] does not appear in any of the two, then exception [NoElim] is raised.
		If elimination is impossible, due to [x] not appearing in one of the two constraints
		or appearing with coefficients of the same sign in two inequalities, [CannotElim] is raised. *)
		let elim c1 c2 va =
			let a1 = Vec.get c1.v va in
				  let a2 = Vec.get c2.v va in
			let r1 = Vec.Coeff.cmpz a1 in
				  let r2 = Vec.Coeff.cmpz a2 in
			match (r1 = 0, r2 = 0) with
			| (true, true) -> raise NoElim
			| (true, false) | (false, true) -> raise CannotElim
			| (false, false) ->
				let (n1, n2) =
					match (c1.typ, c2.typ) with
					| (Eq, Eq) -> (Vec.Coeff.neg a2, a1)
					| (Le, Eq) | (Lt, Eq) ->
						if r2 > 0 then (Vec.Coeff.neg a2, a1) else (a2, Vec.Coeff.neg a1)

					| (Eq, Le) | (Eq, Lt) ->
						if r1 > 0 then (a2, Vec.Coeff.neg a1) else (Vec.Coeff.neg a2, a1)

					| Le, Le | Lt, Lt
					| Lt, Le | Le, Lt ->
						match (r1 > 0, r2 > 0) with
						| (true, true) | (false, false) -> raise CannotElim
						| (true, false) -> (a2, Vec.Coeff.neg a1)
						| (false, true) -> (Vec.Coeff.neg a2, a1)
				in
				let c = add (mulc n1 c1) (mulc n2 c2) in
				(c, n1, n2)
				(*let gcd = Vec.gcd c.v in
				(mulc gcd c,
				Vec.Coeff.mul gcd n1,
				Vec.Coeff.mul gcd n2)*)

		let canon : t -> t
			= fun cstr ->
			let g = Vec.gcd cstr.v in
			if Vec.Coeff.isZ g
			then cstr
			else {cstr with v = Vec.mulr g cstr.v ; c = Vec.Coeff.mulr g cstr.c}

	end

	module Positive = struct
		module Vec = Vector.Rat.Positive
		include Rat(Vec)
	end

	module Int = struct
		module Vec = Vector.Rat.Int
		include Rat(Vec)
	end

	module String = struct
		module Vec = Vector.Rat.String
		include Rat(Vec)
	end
end

module Float = struct
	module Positive = struct
		module Vec = Vector.Float.Positive
		include Cstr(Vec)
	end

	module Int = struct
		module Vec = Vector.Float.Int
		include Cstr(Vec)
	end
end

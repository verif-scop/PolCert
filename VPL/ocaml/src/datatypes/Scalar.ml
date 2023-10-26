(** Types for scalar values:
{ul
	{- {!module:Rat}: rationals}
	{- {!module:Symbolic}: rationals of the form [a + b.delta] where [delta] represents a symbolic error}
	{- {!module:Float}: floating points}
}*)

type roundT = Up | Down

module type Type = sig
	type t

	(** Name of the scalar type. *)
	val name : string

	(** Zero value. *)
	val z: t

	(** Value 1. *)
	val u: t

	(** Value -1. *)
	val negU: t

	(** Small value *)
	val delta : t

	val to_string : t -> string
	val of_string : string -> t

	(** [cmp x y] returns 0 if x = y, a negative integer if x < y, and a positive one otherwise. *)
	val cmp : t -> t -> int

	(** [le x y] returns true if x <= y, false otherwise. *)
	val le: t -> t -> bool

	(** [lt x y] returns true if x < y, false otherwise. *)
	val lt: t -> t -> bool

	(** [cmpz n] is equivalent to [cmp z n]. *)
	val cmpz: t -> int

	(** [equal x y] returns true if x = y, false otherwise. *)
	val equal : t -> t -> bool

	(** [equalApprox x y] returns true if [abs (x - y) <= delta]. *)
	val equalApprox : t -> t -> bool

	(** [isZ n] returns true is [n] is zero ([z]) and false otherwise. *)
	val isZ : t -> bool

	(** Compute the opposite of a number. *)
	val neg: t -> t

	(** Compute the inverse of a number. *)
	val inv: t -> t

	(** Compute the absolute value. *)
	val abs: t -> t

	val add : t -> t -> t
	val sub : t -> t -> t
	val mul : t -> t -> t
	val pow : t -> int -> t

	(** [div num den] *)
	val div : t -> t -> t

	(** Multiplication by a rational. *)
	val mulr : Q.t -> t -> t

	(** Division by a rational. *)
	val divr : t -> Q.t -> t

	val of_float : float -> t
	val to_float : t -> float

	val ofQ : Q.t -> t
	val toQ : t -> Q.t

	(** [toInt_round x Up] returns the smallest [i] such that [i >= x].
		[toInt_round x Down] returns the greatest [i] such that [i <= x].
		Returns None if x does not fit within a machine integer. *)
	val toInt_round : t -> roundT -> int option

	(** [mk ~den:i1 i2] builds an element of type {!type:t} and of value [i2]/[i1]. *)
	val mk: int -> int -> t

	(** [mk1 i] builds an element of type {!type:t} from integer [i]. *)
	val mk1 : int -> t

	(** [well_formed x] returns true if x is not +/- infinity *)
	val well_formed : t -> bool

	(** [well_formed_nonnull x] returns true if x is neither 0 nor +/- infinity *)
	val well_formed_nonnull : t -> bool

	(**/**)
	(** Used in the simplex tableau sharing during the distributed PLP.*)
	val plp_print : t -> string
end

module Float = struct
	type t = float

	let name = "Float"

	let delta = 0.00000001
	let to_string x =
		if x < 0.001
		then string_of_float x
		else Printf.sprintf "%.3f" x

	let plp_print : t -> string
		= fun v ->
		(Q.of_float v |> Q.to_string) ^ " 0"

	let z = float 0
	let u = float 1
	let negU = float (-1)

	let mul = ( *. )
	let pow : t -> int -> t
		= fun x exp ->
		List.fold_left
			(fun res _ -> mul res x)
			u
			(Misc.range 0 exp)

	let div  = ( /. )
	let add = ( +. )
	let sub = ( -. )
	let neg = mul negU
	let abs x = if x > z then x else mul negU x
	let inv x = div u x
	let cmp = Stdlib.compare
	let le  = (<=)
	let lt = (<)
	let cmpz = cmp z
	let equal c1 c2 = (cmp c1 c2 = 0)
	let equalApprox c1 c2 = le (sub c1 c2 |> abs) delta
	let isZ x = equal z x

	let of_string = float_of_string

	let ofQ : Q.t -> t
		= fun q ->
		(float_of_string (q.Q.num |> Z.to_string)) /. (float_of_string (q.Q.den |> Z.to_string))

	let toQ : t -> Q.t
		= fun n ->
		Q.of_float n

	let well_formed x = not (x = nan) && not (x = infinity) && not (x = neg_infinity)

	let well_formed_nonnull x = not (equal x z) && well_formed x
	let to_float t = t
	let of_float t = t

	let mulr : Q.t -> t -> t
		= fun q f ->
		mul (ofQ q) f

	let divr : t -> Q.t -> t
		= fun f q ->
		div f (ofQ q)

	let mk (den: int) (num: int) = float(num) /. float(den)
	let mk1 (num : int) = float(num)

	let toInt_round f round =
		let i = int_of_float f in
		if (match round with
			| Up -> mk1 i < f
			| Down -> mk1 i > f)
		then match round with
			| Up -> Some (i + 1)
			| Down -> Some(i - 1)
		else Some i

end

(** Rationals are used everywhere in the VPL.
	The implementation uses the ZArith front-end to GMP. *)
module Rat = struct
	type t = Q.t

	let name = "Rat"

	let z = Q.zero
	let u = Q.one
	let negU = Q.minus_one

	let cmp = Q.compare
	let le = Q.leq
	let lt = Q.lt
	let cmpz q = -(Q.sign q)

	let isZ : t -> bool
		= fun n -> cmpz n = 0

	let abs = Q.abs
	let neg = Q.neg
	let inv = Q.inv

	let add = Q.add
	let sub = Q.sub
	let mul = Q.mul
	let div = Q.div
	let pow : t -> int -> t
		= fun x exp ->
		List.fold_left
			(fun res _ -> mul res x)
			u
			(Misc.range 0 exp)

	let ofQ : Q.t -> t = fun n -> n
	let toQ : Q.t -> t = fun n -> n

	let mk (den: int) (num: int) = Q.of_ints num den
	let mk1 (num : int) = Q.of_ints num 1

	let of_float = Q.of_float

	let to_float : t -> float
		= fun v ->
        Z.to_float (Q.num v) /. Z.to_float (Q.den v)
		    
	let to_string = Q.to_string
	let of_string = Q.of_string

	let plp_print : t -> string
		= fun v ->
		(to_string v) ^ " 0"

	let equal c1 c2 = (cmp c1 c2 = 0)

	let delta = (of_float Float.delta)

	let equalApprox c1 c2 = cmp (sub c1 c2 |> abs) delta <= 0

	let well_formed_nonnull x = Q.classify x = Q.NZERO

	let well_formed x =
		let x_type = Q.classify x in
			x_type <> Q.INF && x_type <> Q.MINF && x_type <> Q.UNDEF

	(** Some operations can yield infinity (e.g. 1/0) or undefined results (0/0).
	[isReal n] returns true if [n] is neither infinite nor undefined. *)
	let isReal = Q.is_real

	(** [isInt n] returns true if [n] is a relative integer
	that is if its denominator is equal to [u]. *)
	let isInt n = Z.equal (Q.den n) Z.one

	(** The type of relative integers that rationals are made out of, and operations on them. *)
	module Z = struct
		type t = Z.t

		let z = Z.zero
		let u = Z.one

		let add : t -> t -> t
		= Z.add

		let sub : t -> t -> t
		= Z.sub

		let mul : t -> t -> t
		= Z.mul

		(** [div a b] yields the result of integer division [a]/[b].
		The result obeys the rule of signs.  Division by zero has
		undefined behaviour. *)
		let div : t -> t -> t
		= Z.div

		(** [rem a b] yields the remainder of integer division [a]/[b].
		The result has the sign of [a].  [rem a 0] has undefined behaviour. *)
		let rem : t -> t -> t
		= Z.rem

		let cmp = Z.compare
		let equal = Z.equal
		let neg = Z.neg
		let gcd = Z.gcd
		let lAnd = Z.logand
		let orL = Z.logor
		let shiftL = Z.shift_left
		let shiftR = Z.shift_right

		let mk = Z.of_int

		(** build a value of type [t] from its string representation in base 10 *)
		let ofString : string -> t
		= Z.of_string

		let toInt_round = Z.to_int
		let pr = Z.to_string
	end

	(** [gcd nGcd dGcd n] returns the greatest common divisor of nGcd and the numerator of [n]
	and that of [dGcd] and the denominator of [n]. *)
	let gcd (nGcd, dGcd) a =
		((if Z.equal Z.u nGcd then
			Z.u
		else
			Z.gcd nGcd (Q.num a)),
		(if Z.equal Z.u dGcd then
			Z.u
		else
			Z.gcd dGcd (Q.den a)))

	(** [toZ n] returns the numerator and denominator of [n], in that order. *)
	let toZ a = (Q.num a, Q.den a)

	(** [ofZ n d] builds a rational of numerator [n] and denominator [d]. *)
	let ofZ num den = Q.make num den

	let ofRat x = x
	let toRat x = x

	let mulr = mul

	let divr : t -> Q.t -> t
		= fun f q ->
		div f (ofQ q)

	let toInt_round q round =
		try
			let i = let (num,den) = toZ q in
				let num = Z.toInt_round num
				and den = Z.toInt_round den in
				num / den
			in
			if (match round with
				| Up -> lt (mk1 i) q
				| Down -> lt q (mk1 i))
			then match round with
				| Up -> Some (i + 1)
				| Down -> Some (i - 1)
			else Some i
		with _ -> None
		(*
	(* TODO: arrondi? *)
	let toInt_round : t -> int option
		= fun q ->
		try
			let (num,den) = toZ q in
			let num = Z.toInt_round num
			and den = Z.toInt_round den in
			Some (num / den)
		with _ -> None*)
end

module RelInt = struct
	type t = Z.t

	let name = "Z"

	let z = Z.zero
	let u = Z.one
	let negU = Z.minus_one

	let cmp = Z.compare
	let le = Z.leq
	let lt = Z.lt
	let cmpz q = -(Z.sign q)

	let isZ : t -> bool
		= fun n -> cmpz n = 0

	let abs = Z.abs
	let neg = Z.neg
	let inv x = Stdlib.failwith "Scalar.RelInt.inv"

	let add = Z.add
	let sub = Z.sub
	let mul = Z.mul
	let div = Z.div
	let pow : t -> int -> t
		= fun x exp ->
		List.fold_left
			(fun res _ -> mul res x)
			u
			(Misc.range 0 exp)

	let ofQ x = Stdlib.failwith "Scalar.RelInt.ofQ"
	let toQ n = Rat.ofZ n u

	let mk1 : int -> t
		= fun i ->
		Z.of_int i

	let mk: int -> int -> t
		= fun den nom ->
		Z.div (mk1 nom) (mk1 den)

	let toInt_round x round =
		try
			let i = Z.to_int x in
			if (match round with
				| Up -> lt (mk1 i) x
				| Down -> lt x (mk1 i))
			then match round with
				| Up -> Some (i + 1)
				| Down -> Some (i - 1)
			else Some i
		with _ -> None

	let toInt  = Z.to_int

	let of_float = Z.of_float

	let to_float : t -> float
		= fun v ->
		Z.to_int v
			|> float_of_int

	let to_string = Z.to_string
	let of_string = Z.of_string

	let plp_print : t -> string
		= fun v ->
		(to_string v) ^ " 0"

	let equal c1 c2 = (cmp c1 c2 = 0)

	let delta = z

	let equalApprox c1 c2 = cmp (sub c1 c2 |> abs) delta <= 0

	let well_formed_nonnull n = not (isZ n)

	let well_formed x = true

	(** Multiplication by a rational. *)
	let mulr : Q.t -> t -> t
		= fun q n ->
		Stdlib.failwith "Scalar.RelInt.mulr"

	let divr : t -> Q.t -> t
		= fun f q ->
		Stdlib.failwith "Scalar.RelInt.divr"
end

(** Symbolic values have the form [a + b.delta], where [a] and [b] are rationals, and [delta] is symbolic.
They are used in module {!module:Splx} and {!module:Opt} to represent values with strict inequalities. *)
module Symbolic = struct

	type t = { v: Rat.t; d: Rat.t }

	let name = "Symbolic"

	let get_d (x : t) = x.d
        let get_v (x : t) = x.v

	let ofRat n = { v = n; d = Rat.z }

	let pdelta n = { v = n; d = Rat.u }

	let ndelta n = { v = n; d = Rat.negU }

	let z = { v = Rat.z; d = Rat.z }

	let cmp v1 v2 =
		match Rat.cmp v1.v v2.v with
		| 0 -> Rat.cmp v1.d v2.d
		| n -> n

	let le v1 v2 = cmp v1 v2 <= 0

	let lt v1 v2 = cmp v1 v2 < 0

	let hasDelta v = (Rat.cmpz v.d <> 0)

	let ofQ n = { v = n; d = Q.zero }

	let toQ : t -> Q.t
		= fun v ->
		if hasDelta v
		then Q.add
				(get_v v)
				(Q.mul Rat.delta (get_d v))
		else get_v v

	let mulr n v = {
		v = Rat.mul v.v n;
		d = Rat.mul v.d n
	}

	let divr v n = {
		v = Rat.div v.v n;
		d = Rat.div v.d n
	}

	let add v1 v2 = {
		v = Rat.add v1.v v2.v;
		d = Rat.add v1.d v2.d
	}

	let sub v1 v2 = {
		v = Rat.sub v1.v v2.v;
		d = Rat.sub v1.d v2.d
	}

	let adddelta v = { v with d = Rat.add v.d Rat.u }

	let subdelta v = { v with d = Rat.sub v.d Rat.u }

	let to_string v = Printf.sprintf "%s + %s.delta" (Rat.to_string v.v) (Rat.to_string v.d)

	let cmpz = (cmp z)

	let isZ x = cmpz x = 0

	let negU = ofRat Rat.negU

	let abs x = if cmpz x > 0
		then mulr Rat.negU x
		else x

	let equal c1 c2 = (cmp c1 c2 = 0)

	let delta = pdelta Rat.z

	let equalApprox c1 c2 = cmp (sub c1 c2 |> abs) delta < 0

	let u = ofRat (Rat.u)

	let neg : t -> t
		= fun v ->
		mulr Rat.negU v

	(* On triche en négligeant les delta^2 *)
	let mul : t -> t -> t
		= fun v1 v2 ->
		add
			(add
				(mulr (Rat.mul (get_v v1) (get_d v2))
					(pdelta Rat.z))
				(mulr (Rat.mul (get_v v2) (get_d v1))
				(pdelta Rat.z)))
			(ofRat (Rat.mul (get_v v1) (get_v v2)))

	let pow : t -> int -> t
		= fun x exp ->
		List.fold_left
			(fun res _ -> mul res x)
			u
			(Misc.range 0 exp)

	(* On triche en négligeant les delta^2 *)
	let div : t -> t -> t
		= fun v1 v2 ->
		let a1 = get_v v1 and
		a2 = get_v v2 and
		b1 = get_d v1 and
		b2 = get_d v2 in
		let a3 = Rat.div a1 a2 in
		let b3 = Rat.div
			(Rat.sub
				(Rat.mul a3 b2)
				b1)
			(Rat.neg a2) in
		let res = add
	 	(mulr
	 		b3
	 		(pdelta Rat.z))
		 (ofRat a3) in
		 res

	let ofVal : t -> t
		= fun x -> x

	let to_rat : t -> Rat.t
		= fun v ->
		if hasDelta v
		then Rat.add
				(get_v v)
				(Rat.mul Rat.delta (get_d v))
		else get_v v

	let plp_print : t -> string
		= fun v ->
		(Rat.to_string (get_v v)) ^ " " ^ (Rat.to_string (get_d v))

	let inv x = div u x

	let of_float : float -> t
		= fun v ->
		Rat.of_float v
		|> ofRat

	let to_float : t -> float
		= let float_of_val : t -> float
			= fun v ->
			if hasDelta v
			then Float.add
					(get_v v |> Float.ofQ)
					(Float.mul Float.delta (get_d v |> Float.ofQ))
			else get_v v |> Float.ofQ
		in
		fun v ->
		float_of_val v
		|> Float.to_float

	let mk (den: int) (num: int) = ofRat (Rat.mk den num)
	let mk1 (num : int) = ofRat (Rat.mk1 num)

	let well_formed_nonnull x = Rat.well_formed_nonnull (get_v x) && Rat.well_formed_nonnull (get_d x)

	let well_formed x = Rat.well_formed (get_v x) && Rat.well_formed (get_d x)

	let of_string x = print_endline "Scalar.Val.of_string : not implemented" ; z

	let toInt_round _ _ = Stdlib.failwith "Scalar.Symbolic.toInt_round : not implemented"

end

module MachineInt = struct
	type t = int

	let name = "int"

	let z = 0
	let u = 1
	let negU = -1

	let cmp = Stdlib.compare
	let le = (<=)
	let lt = (<)
	let cmpz q = cmp z q

	let isZ : t -> bool
		= fun n -> cmpz n = 0

	let abs = abs
	let neg x = -1 * x
	let inv x = 1/x

	let add = (+)
	let sub = (-)
	let mul = ( * )
	let div = (/)
	let pow : t -> int -> t
		= fun x exp ->
		List.fold_left
			(fun res _ -> mul res x)
			u
			(Misc.range 0 exp)

	let ofQ x = Stdlib.failwith "Scalar.RelInt.ofQ"
	let toQ = Q.of_int

	let mk1 n = n

	let mk: int -> int -> t
		= fun den nom ->
		div (mk1 nom) (mk1 den)

	let toInt_round x _ = Some x

	let of_float = int_of_float

	let to_float = float_of_int

	let to_string = string_of_int
	let of_string = int_of_string

	let plp_print : t -> string
		= fun v ->
		(to_string v) ^ " 0"

	let equal c1 c2 = (cmp c1 c2 = 0)

	let delta = z

	let equalApprox c1 c2 = cmp (sub c1 c2 |> abs) delta <= 0

	let well_formed_nonnull n = not (isZ n)

	let well_formed x = true

	let mulr : Q.t -> t -> t
		= fun q n ->
		Stdlib.failwith "Scalar.MachineInt.mulr"

	let divr : t -> Q.t -> t
		= fun f q ->
		Stdlib.failwith "Scalar.MachineInt.divr"
end

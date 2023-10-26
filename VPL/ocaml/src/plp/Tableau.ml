module Print = struct

	let print_list : ('a -> string) -> 'a list -> string -> unit
		= fun pr l sep-> Misc.list_to_string pr l sep|> Stdlib.print_endline

	(** get_width c returns the length of the string to_string c *)
	let (get_width : Scalar.Rat.t -> int)
	= fun c ->
	String.length (Scalar.Rat.to_string c);;

end

module Vector
  = struct

  type t = Scalar.Rat.t list

  let to_string : t -> string
    = fun v ->
    "[" ^ (List.map Scalar.Rat.to_string v |> String.concat "; ") ^ "]"

  let size : t -> int
    = fun v ->
    let n = List.length v in
    if n > 0 then n
    else Stdlib.invalid_arg "Matrix.Vector.size: empty"

  let equal : t -> t -> bool
    = fun v v' ->
    if size v <> size v' then false
    else List.for_all2 Q.equal v v'

  let get : int -> t-> Q.t
    = fun i v ->
    if 0 <= i && i < size v then List.nth v i
    else
      Printf.sprintf "Matrix.Vector.get (%i) %s: out-of-bounds" i (to_string v)
      |> Stdlib.invalid_arg

  let last : t -> Q.t
    = fun v -> get (size v - 1) v

  (** [init i f] builds a value of type [t], of size [i] by initializing
the cell at index [i] with [f i].  If [i] is smaller than [1], then
[Invalid_argument] is raised. *)
  let init : int -> (int -> Q.t) -> t
    = fun i f ->
    if i < 1 then Stdlib.invalid_arg "Matrix.Vector.init"
    else List.map f (Misc.range 0 i)

  (** [consAppend a [a0; ...; aN]] builds the vector [[a0; ...; a; aN]].
If the vector has size 0, then [Invalid_argument] is raised. *)
  let consAppend : Q.t -> t -> t
    = fun a v ->
    let v' = Misc.sublist v 0 (size v - 1) in
    v' @ [a; last v]

  let add : t -> t -> t
    = fun v v' ->
    if size v = size v'
    then List.map2 Q.add v v'
    else Stdlib.invalid_arg "Matrix.Vector.add"

  let mul_scalar : t -> Q.t -> t
    = fun v a -> List.map (Q.mul a) v

	(** [pretty_print v l] returns a string corresponding to a row of a matrix. Each column has a fixed width *)
	let rec (pretty_print : t -> int list -> string)
		= fun v l ->
		match (v,l) with
		| ([],_) | (_,[]) -> ""
		| (p :: tail1 , i :: tail2) -> let nb_spaces = i - (Print.get_width p) in
		if nb_spaces mod 2 = 1
			then String.concat "" [Misc.string_repeat " " (nb_spaces/2) ; Q.to_string p ; Misc.string_repeat " " (nb_spaces/2 + 1) ; " | " ; pretty_print tail1 tail2]
			else String.concat "" [Misc.string_repeat " " (nb_spaces/2) ; Q.to_string p ; Misc.string_repeat " " (nb_spaces/2) ; " | " ; pretty_print tail1 tail2];;

	(** mult_vector v1 v2 returns the vector v1 x v2 *)
	let rec (mul : t -> t -> t)
		= fun v1 v2 ->
		List.map2 (fun p1 p2 -> Scalar.Rat.mul p1 p2) v1 v2;;

	(** add_vector v1 v2 adds v1 and v2! *)
	let rec (add : t -> t -> t)
		= fun v1 v2 ->
		List.map2 (fun p1 p2 -> Scalar.Rat.add p1 p2) v1 v2;;
	end

module Matrix
  = struct

  type t = Vector.t list

  let nRows : t -> int
    = fun m ->
    let n = List.length m in
    if n > 0 then n
    else Stdlib.invalid_arg "Matrix.Matrix.nRows: empty"

  let checkRow : t -> int -> bool
    = fun m i -> 0 <= i && i < nRows m

  let nCols : t -> int
    = function
    | [] -> Stdlib.invalid_arg "Matrix.Matrix.nCols: empty"
    | r :: t ->
       let n = Vector.size r in
       if List.for_all (fun r' -> Vector.size r' = n) t then n
       else Stdlib.invalid_arg "Matrix.Matrix.nCols: different sizes"

  let checkCol : t -> int -> bool
    = fun m i -> 0 <= i && i < nCols m

  let equal : t -> t -> bool
    = fun m m' ->
    if nRows m <> nRows m' || nCols m <> nCols m' then false
    else List.for_all2 Vector.equal m m'

	module Diag = struct

	    let sparsity : (Z.t * Z.t) Stdlib.ref
			= Stdlib.ref (Z.zero, Z.zero)
	    and sparsity_enabled : bool Stdlib.ref
			= Stdlib.ref false

	    let enable_sparsity : unit -> unit
			= fun () ->
			begin
		  	sparsity := (Z.zero, Z.zero);
		  	sparsity_enabled := true;
			end

	    let disable_sparsity : unit -> unit
			= fun () -> sparsity_enabled := false;;

    	let get_sparsity : unit -> Z.t * Z.t
			= fun () -> !sparsity

      	let update_sparsity : t -> unit
			= fun m ->
			if not !sparsity_enabled then ()
			else
				let (sn, sd) = !sparsity in
			  	begin
			    sparsity :=
			      (List.fold_left
				 (List.fold_left (fun n a -> if Q.equal Q.zero a then n else Z.add Z.one n))
				 sn m,
			       Z.of_int (nRows m * nCols m) |> Z.add sd);
			  	end
	end

  let mapi : (int -> Vector.t -> Vector.t) -> t -> t
    = fun f m -> List.mapi f m

  let getRow : int -> t -> Vector.t
    = fun i m ->
    if checkRow m i then List.nth m i
    else Stdlib.invalid_arg "Matrix.Matrix.getRow"

  let get : int -> int -> t -> Q.t
    = fun row col m-> Vector.get col (getRow row m)

  (** get_col m i returns the ith column of the matrix m as a vector *)
let rec(get_col : int -> t -> Vector.t)
	= fun col m->
	match m with
	| [] -> []
	| v :: tail -> (Vector.get col v) :: (get_col col tail);;

  let pivot : t -> int -> int -> t
    = fun m row col ->
    begin
      Diag.update_sparsity m;
      let pivRow = getRow row m in
      let pivElt = Vector.get col pivRow in
      if Q.sign pivElt <> 0
      then
	let normRow = Vector.mul_scalar pivRow (Q.inv pivElt) in
	let norm = fun i r ->
	  if i = row then normRow
	  else Vector.add (Vector.mul_scalar normRow (Q.neg (Vector.get col r))) r
	in
	mapi norm m
      else Stdlib.invalid_arg "Matrix.Matrix.pivot"
    end

	(** add_row m v i adds the row vector v at the index i in m*)
	let (add_row : t -> Vector.t -> int -> t)
		= let rec(add_row_rec : t -> Vector.t -> int -> int -> t)
		= fun m v i k ->
		if i = k then v :: (add_row_rec m v i (k+1))
		else match m with
		| [] -> []
		| vec :: tail -> vec :: (add_row_rec tail v i (k+1))
		in fun m v i ->
		add_row_rec m v i 0

	(** add_col m v i adds the column vector v at the index i in m *)
	let rec(add_col : t -> Vector.t -> int -> t)
		= fun m v col ->
		let len = List.length (List.nth m 0) in
		if len = 0
		then List.map (fun coeff -> [coeff]) v
		else List.map2 (fun vec coeff -> (Misc.sublist vec 0 col) @ [coeff] @ (Misc.sublist vec col len)) m v;;

	(** get_width_column m i returns the width (nb of char) of the ith column of the matrix m *)
	let (get_width_column : t -> int -> int)
		= fun m col->
		let l = List.map (fun p -> Print.get_width p) (get_col col m) in
		Misc.max compare l

	(** get_width_column_vector m returns the list [width of col 1 ; width of col 2 ; ...] *)
	let (get_width_column_vector : t -> int list)
		= fun m ->
		List.map (fun i -> get_width_column m i) (Misc.range 0 (nCols m));;

	let rec (to_string : t -> int list -> string)
		= fun m l ->
		match m with
		| [] -> ""
		| v :: tail -> String.concat "" [Vector.pretty_print v l ; "\n" ; to_string tail l];;

	(** rescale m i coeff returns the matrix m where the row i has been multiplied by coeff*)
	let (rescale : t -> int -> Scalar.Rat.t -> t)
		= let rec(rescale_rec : t -> int -> Scalar.Rat.t -> int -> t)
			= fun m row coeff k ->
			match m with
			| [] -> []
			| v :: tail -> if row = k then (Vector.mul_scalar v coeff) :: tail
			else v::(rescale_rec tail row coeff (k+1))
		in fun m row coeff ->
		rescale_rec m row coeff 0

	(** add_multiple_of_row m row1 row2 coeff returns the matrix m where row1 has been added the row2 multiplied by coeff*)
	let (add_multiple_of_row : t -> int -> int -> Scalar.Rat.t -> t)
		= let rec(add_multiple_of_row_rec : t -> int -> Vector.t -> Scalar.Rat.t -> int -> t)
			= fun m row v coeff k ->
			match m with
			| [] -> []
			| vec :: tail -> if row = k then (Vector.add vec (Vector.mul_scalar v coeff)) :: tail
			else vec :: (add_multiple_of_row_rec tail row v coeff (k+1))
		in fun m row1 row2 coeff ->
		add_multiple_of_row_rec m row1 (getRow row2 m) coeff 0
end

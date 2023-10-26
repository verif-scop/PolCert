(** This module provides efficient decompositions of list of indexes. *)

module Liste : sig

	type t = Index.Int.t list
	
	val to_string : t -> string
	
	val equal : t -> t -> bool
	
	(** [get_next dim l] returns an index that is either an element of [l] or an index smaller than [max 2 (l/2)] elements of [l].
	In the second case, this index is useful to compute [l] efficiently. 
	If [l] is a singleton, [get_next] returns a null index.
	@raise Failure if no such element has been found. *)
	val get_next : int -> t -> Index.Int.t
	
	(** [compute ind] returns the list of nonnull components of [ind].
	For instance, [compute [1;0;2] = [[1;0;0] ; [0,0,2]]]. *)
	val components : Index.Int.t -> t
	
	(** [get_preds ind] returns the list of indexes that are strictly smaller than [ind] {i w.r.t} function {!dunction Index.Int.le}. *)
	val get_preds : Index.Int.t -> t
	
	(** [le dim ind_max] returns the list of indexes of length dim whose value is smaller than [ind_max] {i w.r.t} {!Index.Int.value}. *)
	val le :  int -> int -> t
	
end 


module MapI : Map.S with type key = Index.Int.t

(** This module associates in a map an {!Index.Int.t} to a {!Liste.t}.
A list [il] associated to an index [i] represents a decomposition of [i] : sum_j il(j) = i. *)
module Map : sig
	
	type t = Liste.t MapI.t
	
	val to_string : t -> string
	
	(** [compute l] returns a map associating each index [ind] of [l] to a list of indexes whose sum is [ind]. 
	Indexes that have only one non null coefficient are not added into the map.
	@raise Invalid_argument if [l] is empty. *)
	val compute : Liste.t -> t

	(** Same as {!function compute} but starts from a given map. 
	@raise Invalid_argument if the input list is empty. *)
	val compute_list_from_map : Liste.t -> t -> t
	
	(** Same as {!function compute_list_from_map} but with a single index instead of a list. 
	Returns the corresponding {!type Liste.t} as well.*)	
	val compute_from_map : Index.Int.t -> t -> (Liste.t * t)

end


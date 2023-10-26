(** This module defines several generic functions to handle lists or strings *)

(** [sublist l i j] returns the sublist of [l] starting at index [i] and ending at index [j-1] *)
val sublist : 'a list -> int -> int -> 'a list
	
(** [index s c] returns the index of the character [c] in the string [s] if it exists, -1 otherwise *)
val index : string -> char -> int

(** [substring s i] returns the substring of [s] starting at index [i] *)
val substring : string -> int -> string

(** [findi p l] returns the index of the first element in [l] that satisfies predicate [p]. 
@raise Not_found if no such element exists *)		
val findi : ('a -> bool) -> 'a list -> int

val find_res : ('a -> (bool * 'a)) -> 'a list -> 'a

(** [popi l i] returns the list [l] where the [ith] element has been removed. 
If i < 0 or i > len(l), it returns l *)	
val popi : 'a list -> int -> 'a list

(** [pop eq l x] returns the list [l] where the first element equal to [x] ({i w.r.t} equality function [eq]) is removed *)		
val pop : ('a -> 'a -> bool) -> 'a list -> 'a -> 'a list

(** [pop eq l x] returns the list [l] where all elements equal to [x] ({i w.r.t} equality function [eq]) are removed *)	
val popAll : ('a -> 'a -> bool) -> 'a list -> 'a -> 'a list

(** [list_to_string to_string l sep] returns the string [to_string l(0) ^  sep ^ ... ^ sep ^ to_string l(len(l)-1)] *)
val list_to_string : ('a -> string) -> 'a list -> string -> string

(** [array_to_string to_string l sep] returns the string [to_string l(0) ^  sep ^ ... ^ sep ^ to_string l(len(l)-1)] *)
val array_to_string : ('a -> string) -> 'a array -> string -> string

(** [list_eq contains l1 l2] returns true if [l1] and [l2] contain the same elements.
[contains x l] returns [true] if x belongs to [l], [false] otherwise *)
val list_eq : ('a -> 'a list -> bool) -> 'a list -> 'a list -> bool

val list_eq2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool

(** [range a b] returns the list of consecutive integers from [a] to [b]-1 *)
val range : int -> int -> int list
 
(** [range a len] returns the list [a;a+1;a+2;...;a+len] *)
val range_len : int -> int -> int list

(** [max cmp l] returns the maximum element of [l] {i w.r.t} the comparison function [cmp] 
@raise Invalid_argument if the input list is empty *)	
val max : ('a -> 'a -> int) -> 'a list -> 'a

(** [maxi cmp l] returns the index of the maximum element of [l] {i w.r.t} the comparison function [cmp] 
@raise Invalid_argument if the input list is empty *)	
val maxi :  ('a -> 'a -> int) -> 'a list -> int

(** [min cmp l] returns the minimum element of [l] {i w.r.t} the comparison function [cmp]
@raise Invalid_argument if the input list is empty *)	
val min : ('a -> 'a -> int) -> 'a list -> 'a
	
(** [rem_dupl eq l] removes the multiple occurences of elements in [l], {i w.r.t} equality function [eq] *)		
val rem_dupl : ('a -> 'a -> bool) -> 'a list -> 'a list

(** [intersection eq l1 l2] returns the list of elements that are both in [l1] and [l2], {i w.r.t} equality function [eq] *)
val intersection : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list
	
(** [sublist l1 l2] returns [true] if [l1] is a sublist of [l2], [false] otherwise *)	
val is_sublist : 'a list -> 'a list -> bool

val map2i : (int -> 'a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list

(** [filter_i f l i] returns the [i] first elements of [l] that are true through [f] *)
val filter_i: ('a -> bool) -> 'a list -> int -> 'a list * 'a list

(** [string_repeat s i] returns a string composed of [i] times [s] *)
val string_repeat : string -> int -> string

(** [add_tab i s] adds [i] tabulations after each '\n' in [s]. *)
val add_tab : int -> string -> string

val fold_left_i : (int -> 'a -> 'b -> 'a) -> 'a -> 'b list -> 'a

val fold_right_i : (int -> 'a -> 'b -> 'b) -> 'a list -> 'b -> 'b

val string_equal : string -> string -> bool

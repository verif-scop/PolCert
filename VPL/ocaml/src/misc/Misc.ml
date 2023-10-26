(** sublist l i j returns l[i:j] (j exluded) *)
let rec(sublist : 'a list -> int -> int -> 'a list)
	= fun l i j->
	match (l,i,j) with
	| ([],_,_) -> []
	| (_,_,0) -> []
	| (p :: tail,_,_) -> if i > 0 
	then sublist tail (i-1) (j-1)
	else p :: (sublist tail i (j-1))
	
(** index s c returns the index of the character c in the string s if it exists, -1 otherwise *)
let index s c = try (String.index s c) with
	| Not_found -> -1

(** substring s i1 returns the substring of s starting at index i *)
let rec(substring : string -> int -> string)
	= fun s i ->
	(String.sub s i ((String.length s) - i))
	
let (findi : ('a -> bool) -> 'a list -> int)
	= let rec(findi_rec : ('a -> bool) -> 'a list -> int -> int)
		= fun prop l k ->
		match l with
		| [] -> Stdlib.raise Not_found 
		| v :: tail -> if prop v then k else findi_rec prop tail (k+1)
in fun prop l -> 
findi_rec prop l 0
	
let rec (find_res : ('a -> (bool * 'a)) -> 'a list -> 'a)
	= fun prop l ->
	match l with
	| [] -> Stdlib.raise Not_found 
	| v :: tail -> let (b,v') = prop v in
		if b then v' else find_res prop tail

let rec(string_repeat : string -> int -> string)
	= fun s i ->
	if i = 0 then "" else String.concat "" [s ; string_repeat s (i-1)];;

let (popi : 'a list -> int -> 'a list)
	= fun l i ->
	if i >= 0 && i <= List.length l 
	then (sublist l 0 i) @ (sublist l (i+1) (List.length l))
	else l
		
let (pop : ('a -> 'a -> bool) -> 'a list -> 'a -> 'a list)
	= fun eq l x ->
	let i = findi (fun y -> eq x y) l in
	popi l i

let (popAll : ('a -> 'a -> bool) -> 'a list -> 'a -> 'a list)
	= fun eq l x ->
	List.fold_left
		(fun res y -> if eq x y
			then res
			else y :: res)
		[] l
	
let (list_to_string : ('a -> string) -> 'a list -> string -> string)
	= fun to_string l sep->
	Printf.sprintf "[%s]" (String.concat sep (List.map to_string l))

let (array_to_string : ('a -> string) -> 'a array -> string -> string)
	= fun to_string l sep->
	Printf.sprintf "[%s]" (String.concat sep (Array.map to_string l |> Array.to_list))

(** compare two non-ordered list *)
let (list_eq : ('a -> 'a list -> bool) -> 'a list -> 'a list -> bool)
	= fun contains l1 l2 -> List.length l1 = List.length l2 &&
	List.for_all (fun e -> contains e l2) l1 && 
	List.for_all (fun e -> contains e l1) l2

(** compare two non-ordered list *)
let (list_eq2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool)
	= fun eq l1 l2 -> 
	List.length l1 = List.length l2 &&
	List.for_all (fun e1 -> List.exists (fun e2 -> eq e1 e2) l2) l1 && 
	List.for_all (fun e2 -> List.exists (fun e1 -> eq e1 e2) l1) l2
	
let rec(range : int -> int -> int list)
	= fun i j->
	if i >= j then [] else i :: (range (i+1) j)

(** [range a len] returns the list [a;a+1;a+2;...;a+len] *)
let rec(range_len : int -> int -> int list)
	= fun i j ->
	if j = 0 then [] else i :: (range (i+1) (j-1))
	
let (max : ('a -> 'a -> int) -> 'a list -> 'a)
	= fun cmp l ->
	try List.fold_left
	(fun i j -> if cmp i j > 0 then i else j)
	(List.hd l)
	(sublist l 1 (List.length l))
	with Failure _ -> Stdlib.invalid_arg "Misc.max : empty input list"

let (maxi :  ('a -> 'a -> int) -> 'a list -> int)
	= let rec (maxi_rec : ('a -> 'a -> int) -> 'a list -> 'a -> int -> int -> int)
		= fun cmp l max maxi i ->
		match l with
		| [] -> maxi
		| x::tl -> if cmp x max > 0 then maxi_rec cmp tl x i (i+1) else maxi_rec cmp tl max maxi (i+1) in
	fun cmp l ->
	try maxi_rec cmp (List.tl l) (List.hd l) 0 1
	with Failure _ -> Stdlib.invalid_arg "Misc.maxi : empty input list"
	
let (min : ('a -> 'a -> int) -> 'a list -> 'a)
	= fun cmp l ->
	try List.fold_left
	(fun i j -> if cmp i j < 0 then i else j)
	(List.hd l)
	(sublist l 1 (List.length l))
	with Failure _ -> Stdlib.invalid_arg "Misc.min : empty input list"
		
let rec(rem_dupl : ('a -> 'a -> bool) -> 'a list -> 'a list)
	= fun eq l ->
	match l with
	| [] -> []
	| x :: tl -> if List.exists (fun y -> eq x y) tl 
		then rem_dupl eq tl
		else x :: (rem_dupl eq tl)

let (intersection : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list)
	= fun equal l1 l2 ->
	List.filter (fun x -> List.exists (fun y -> equal x y) l2) l1

(** sublist l1 l2 Checks if l1 is a sublist of l2 *)	
let (is_sublist : 'a list -> 'a list -> bool)	
	= fun l1 l2 ->
	List.for_all (fun x -> List.mem x l2) l1

let (map2i : (int -> 'a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list)
	= fun f l1 l2 ->
	List.mapi
		(fun i x1 -> f i x1 (List.nth l2 i))
		l1

let rec filter_i: ('a -> bool) -> 'a list -> int -> 'a list * 'a list
	= fun f l max_sat ->
	if max_sat = 0 
	then ([],l)
	else match l with
		| [] -> ([],[])
		| x :: tl -> if f x 
			then let (a,b) = filter_i f tl (max_sat-1) in 
				(x :: a, b)
			else filter_i f tl max_sat 
			
let add_tab : int -> string -> string
	= fun n s ->
	let str_tab = String.make n '\t' in
	List.fold_left
		(fun res i -> let c = String.get s i in
			if c = '\n'
			then res ^ "\n" ^ str_tab
			else res ^ (String.make 1 c))
		str_tab
		(range 0 (String.length s))
		
let rec fold_left_i : (int -> 'a -> 'b -> 'a) -> 'a -> 'b list -> 'a
	= fun f a0 bs ->
	List.fold_left
		(fun a i -> f i a (List.nth bs i))
		a0
		(range 0 (List.length bs)) 

let rec fold_right_i : (int -> 'a -> 'b -> 'b) -> 'a list -> 'b -> 'b
	= fun f a_s b0 ->
	List.fold_right
		(fun i b -> f i (List.nth a_s i) b)
		(range 0 (List.length a_s)) 
		b0

let string_equal : string -> string -> bool
	= fun s1 s2 ->
	String.compare s1 s2 = 0

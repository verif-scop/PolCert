type poly = 
	| Leaf of (string * int) list  * Q.t
	| Add of poly * poly
	| Sub of poly * poly
	| Mul of poly * poly

type contrainte = poly * Cstr.cmpT_extended * poly

type assign = string*poly

type stmt = |Constraints of contrainte list |Assigns of assign list

(** renvoie le polynome multiplié par -1 *)
let rec neg : poly -> poly
	= fun p -> match p with
				|Leaf(l,nb) -> Leaf(l,Q.mul Q.minus_one nb)
				|Add(p1,p2) -> Add(neg p1,neg p2)
				|Sub(p1,p2) -> Sub(neg p1,neg p2)
				|Mul(p1,p2) -> Mul(neg p1,p2)



(** récurrence pour getCoeff **)
let rec getC (s:string) (n:int):string =
if n = String.length s
then
	try String.sub s 0 (n-1) with Invalid_argument _ -> "1" 
else begin
	if s.[n] >= '0' && s.[n] <= '9'
		then
			getC s (n+1)
	else
		if n = 0 
		then "1"
		else try String.sub s 0 n with Invalid_argument _ -> "1"  
end

(**
Semantique
string -> string
getCoeff (s) renvoie 1 si la string entrée ne commence pas par un nombre, sinon elle renvoie le nombre dans une string. (Elle sert à extraire le coefficient dans les cas 5x, 1234y, etc...
Exemples:
getCoeff "123x2" renvoie "123"
getCoeff "x3" renvoie  "1" (car x3 = x3*1)
**)

let getCoeff (s:string):string =
	if String.length s >= 2 && s.[0] = '-'
	then
		if s.[1] <'0' || s.[1] >'9'
		then
			"-1"
		else
		getC s 1
	else
		getC s 0

(**
Semantique
string -> string
getName (s) renvoie le nom de la variable
Exemples:
getNom "123x2" renvoie "x2"
getCoeff "x3" renvoie  "x3"
**)
let rec getNm (s:string) (n:int):string =
if n= String.length s then ""
else
	if s.[n] >= '0' && s.[n] <= '9'
		then
			getNm s (n+1)
	else 
		String.sub s n ((String.length s) - n)

let getName (s:string):string =
if String.length s > 1 && s.[0] = '-'
then getNm s 1
else getNm s 0


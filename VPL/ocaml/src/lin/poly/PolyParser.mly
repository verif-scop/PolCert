%token <string> INT
%token <string> VAR
%token <string> QxVar
%token EOF PLUS TIMES SLASH LESS EXP
%token LE LT GT GE EQ NEQ 
%token VRG PVRG
%token PARBEG PAREND
%token ASSIGN
%start one_poly
%start one_prefixed_poly
%start one_stmt_list
%start one_var_list
%type <PolyParserBuild.poly> one_poly
%type <PolyParserBuild.stmt list> one_stmt_list
%type <string list> one_var_list
%type <(Var.Positive.t list * Q.t) list> one_prefixed_poly
%type <string * PolyParserBuild.poly> assign
%type <(string * PolyParserBuild.poly) list> assign_list
%type <PolyParserBuild.poly * Cstr.cmpT_extended * PolyParserBuild.poly> contrainte
%type <(PolyParserBuild.poly * Cstr.cmpT_extended * PolyParserBuild.poly) list> contrainte_list
%type <(string * int) list * Q.t> element
%type <int> exposant
%type <(string * int) list * Q.t> monome
%type <Q.t> nb
%type <string * Q.t> nbVar
%type <PolyParserBuild.poly> polynomial
%type <Var.Positive.t list * Q.t> prefixed_element
%type <Var.Positive.t list * Q.t> prefixed_monomial
%type <(Var.Positive.t list * Q.t) list> prefixed_polynomial
%type <PolyParserBuild.stmt list> stmt_list
%type <string> var
%type <string list> var_list
%%
one_prefixed_poly:
	| prefixed_polynomial EOF {$1}
	| EOF {[]}
;
prefixed_polynomial:
	| prefixed_element {[Stdlib.fst $1, Stdlib.snd $1]}
	| prefixed_element PLUS prefixed_polynomial {((Stdlib.fst $1, Stdlib.snd $1) :: $3)}
;   
prefixed_element:
	| prefixed_monomial {$1}
	| prefixed_monomial TIMES prefixed_element {(fst $1 @ fst $3, Q.mul (snd $1) (snd $3))}
;
prefixed_monomial:
	| nb {([], $1)}
	| VAR {([Var.Positive.of_prefixed_string $1], Q.one)}
;
one_var_list : 
	| var_list EOF {$1}
	| EOF {[]}
;
var_list :
	| var {[$1]}
	| var PVRG var_list {$1 :: $3}
	| var VRG var_list {$1 :: $3}
;
one_stmt_list : 
	| stmt_list EOF {$1}
	| EOF {[]}
;
stmt_list :
	| assign_list {[ PolyParserBuild.Assigns($1) ]}
	| contrainte_list {[ PolyParserBuild.Constraints($1) ]}
	| contrainte_list PVRG stmt_list {PolyParserBuild.Constraints($1) :: $3}
	| assign_list PVRG stmt_list {PolyParserBuild.Assigns($1) :: $3}
;
assign_list :
	| assign {[ $1 ]}
	| assign VRG assign_list {$1 :: $3}
;
assign :
	var ASSIGN polynomial {($1,$3)}
;
contrainte_list :
	| contrainte {[ $1 ]}
	| contrainte VRG contrainte_list {$1 :: $3}
;
contrainte : 
	| polynomial LE polynomial {($1, Cstr.LE, $3)}
	| polynomial LT polynomial {($1, Cstr.LT, $3)}
	| polynomial GE polynomial {($1, Cstr.GE, $3)}
	| polynomial GT polynomial {($1, Cstr.GT, $3)}
	| polynomial EQ polynomial {($1, Cstr.EQ, $3)}
	| polynomial NEQ polynomial {($1, Cstr.NEQ, $3)}
;
polynomial:
	| element {PolyParserBuild.Leaf(fst $1, snd $1)}
	| monome TIMES PARBEG polynomial PAREND {PolyParserBuild.Mul(PolyParserBuild.Leaf(fst $1, snd $1),$4)}
	| PARBEG polynomial PAREND {$2}
	| polynomial PLUS polynomial {PolyParserBuild.Add ($1,$3)}
   | polynomial LESS element {PolyParserBuild.Sub($1,PolyParserBuild.Leaf(fst $3, snd $3))}
   | polynomial LESS PARBEG polynomial PAREND {PolyParserBuild.Sub($1,$4)}
	| polynomial TIMES polynomial {PolyParserBuild.Mul($1,$3)}
/* | element TIMES polynomial{PolyParserBuild.Mul(PolyParserBuild.Leaf(fst $1, snd $1),$3)}*/ /* cas inutile  */
   | PARBEG polynomial PAREND polynomial {PolyParserBuild.Mul($2,$4)} /* Pour les cas (1 + x1)x2 */
;
one_poly:
	| polynomial EOF {$1}
	| EOF {PolyParserBuild.Leaf([("",0)],Q.zero)}
;
element: 
	| monome {$1}
	| monome TIMES element {(fst $1 @ fst $3, Q.mul (snd $1) (snd $3))}
;
monome:
	| nb {([], $1)}
   | nbVar {([(fst $1, 1)], snd $1)}
   | nbVar EXP exposant {([(fst $1, $3)], snd $1)}	
;
exposant:
	INT {int_of_string $1}
;
nb:
	| INT {Q.of_string $1}
	| INT SLASH INT {Q.of_string (Printf.sprintf "%s/%s" $1 $3)}
;
nbVar: 							
	QxVar {((PolyParserBuild.getName $1) , Q.of_string (PolyParserBuild.getCoeff $1))}
;
var:
	nbVar {fst $1}
;

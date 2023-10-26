(** Inputs for the verifier extracted in Caml 

NB: Coq notations gives use a cheap parser for PL language...

*)

Require Import ZArith.
Require Import DemoPLVerifier.
Import NumC.
Import ASCond.ZCond.
Import Term.
Import String.
Import Annot.

Open Scope string_scope.
Open Scope Z_scope.
Open Scope cond_scope.
Open Scope term_scope.
Open Scope statement_scope.
Open Scope list_scope.

Local Notation var:=ProgVar.PVar.t.

Module Type VariableBasis.

  Parameter x y q r a x1 x2 y1 y2 aux lb ub c: var.

End VariableBasis.

Module Examples(B:VariableBasis).

Import B.

Coercion Var: var >-> term.

Definition idZ (x:Z) : ZNum.t := x.
Coercion idZ: Z >-> ZNum.t.
Coercion Cte: ZNum.t >-> term.
Coercion Annot: topLevelAnnot >-> Funclass.

Definition idTerm (x:term): ASTerm.ZTerm.term := x.
Coercion idTerm: term >-> ASTerm.ZTerm.term.


(**** BASIC TESTS ****)

(* a ::= abs(x) -; q ::= a / 2 -; r ::= a % 2 *)
Definition div2 (inv: cond):=
  If (0 <= x) Then
    a ::= x
  Else
    a ::= Opp x
  Fi -;
  r ::= a -;
  q ::= 0 -;
  While (2 <= r) Do
    q ::= q+1 -;
    r ::= r-2
  Inv (a=q*2 + r /\ 0 <= r /\ 0 <= q /\ inv)
  Done.

(* Statement expected to be accepted *)

Definition basic_tests_ok : list (string * statement) :=
   ("triv_guards0",
       Assume (x = 3) -;
       Assert "post1" (2 <= x) -;
       Assert "post2" (x = 3) -;
       Assert "post3" (x <> 4))
    ::("triv_guards1",
       Assume (100 <= x) -;
       Assert "post1" (0 <= x) -;
       Assume (0 <= x) -;
       Assert "post2" (0 <= x) -;
       Assert "post3" (100 <= x) -;
       Assume (y = x+1) -;
       Assert "post4" (101 <= y) -;
       Assert "post5" (0 <= y))
    ::("triv_assign",
       Assume (100 <= x) -;
       x ::= x+1 -;
       Assert "post1" (101 <= x) -;
       Assert "post2" (0 <= x) )
    ::("split_eq",
       Assume (1 <= x /\ x <= 3)-; 
       x::=x+1 -;
       Assert "post" (x = 2 \/ x = 3 \/ x = 4)  ) 
    ::("trans1",
       Assume (0 <= x /\ x <= 0) -;
       Assert "post1" (x = 0))
    ::("trans2",
       Assume (0 <= x /\ x <= y /\ y <= 0) -;
       Assert "post1" (x = 0) -;
       Assert "post2" (y = 0))
    ::("trans3",
       Assume (0 <= x /\ x <= y /\ y <= x1 /\ x1 <= x) -;
       Assert "post1" (x = y) -;
       Assert "post2" (x = x1))
    ::("trans",
       Assume (0 <= x /\ x <= y /\ 2*y <= x1) -;
       Assert "post1" (y <= x1) -;
       Assert "post2" (x <= x1) -;
       Assert "post3" (0 <= x1) -;
       Assume (2*x1+3*y <= x) -;
       Assert "post4" (x = y) -;
       Assert "post5" (y = x1) -;
       Assert "post6" (x = x1))
    ::("while1",
       r ::= 1 -;
       q ::= 7 -;
       While (r <= 10) Do
          q ::= q+2 -;
          r ::= r+1
          Inv (q = 2*r+5 /\ r <= 11)
       Done -;
       Assert "post1" (r = 11) -;
       Assert "post2" (q = 27))
    ::("while2",
       Assume (12 <= y /\ y <= 20 /\ y = 3*x+q /\ 0 <= q /\ q <= 3) -;
       While (q <= 10) Do
          q ::= q
          Inv (3 <= x /\ 2*x <= 14)
       Done)
    ::("convex_hull0",
       Assume (1 <= x /\ x <= 10) -;
       a::=3*x -;
       If (x <= 5) Then 
          y::=(x+5)  (* hence,  x in 1..5   and  y in 6..10 *)
       Else
          y::=(x-5)  (* hence,  x in 6..10  and  y in 1..5  *)
       Fi -;
       r ::= a-x+y -;
       Assert "post" (8 <= r /\ r <= 25) )
    ::("convex_hull1",
       Assume (1 <= x /\ x <= 10) -;
       a::=3*x -;
       If (x <= 5) Then 
          Assume (y <= (x+5))  (* hence,  x in 1..5   and  y <= 10 *)
       Else
          y::=(x-5)  (* hence,  x in 6..10  and  y in 1..5  *)
       Fi -;
       r ::= a-x+y -;
       Assert "post" (r <= 25))
    ::("convex_hull2",
       Assume (1 <= x /\ x <= 10) -;
       a::=3*x -;
       If (x <= 5) Then 
          Assume ((x+5) <= y)  (* hence,  x in 1..5   and  6 <= y *)
       Else
          y::=(x-5)  (* hence,  x in 6..10  and  y in 1..5  *)
       Fi -;
       r ::= a-x+y -;
       Assert "post" (8 <= r))
    ::("convex_hull3",
       Assume (1 <= x /\ x <= 10) -;
       a::=3*x -;
       If (x <= 5) Then 
          y::=(x+5)  (* hence,  x in 1..5   and  y in 6..10 *)
       Else
          Assume (y <= (x-5))  (* hence,  x in 6..10  and  y <= 5  *)
       Fi -;
       r ::= a-x+y -;
       Assert "post" (r <= 25) )
    ::("convex_hull4",
       Assume (1 <= x /\ x <= 10) -;
       a::=3*x -;
       If (x <= 5) Then 
          y::=(x+5)  (* hence,  x in 1..5   and  y in 6..10 *)
       Else
          Assume ((x-5) <= y)  (* hence,  x in 6..10  and  1 <= y  *)
       Fi -;
       r ::= a-x+y -;
       Assert "post" (8 <= r) )
    ::("convex_hull5",
       Assume (1 <= x /\ x <= 10) -;
       a::=3*x -;
       If (x <= 5) Then 
          Assume ((x+5) <= y)  (* hence,  x in 1..5   and  6 <= y *)
       Else
          Assume ((x-5) <= y) (* hence,  x in 6..10  and  1 <= y  *)
       Fi -;
       r ::= a-x+y -;
       Assert "post" (8 <= r))
    ::("convex_hull6",
       Assume (1 <= x /\ x <= 10) -;
       a::=3*x -;
       If (x <= 5) Then 
          Assume (y <= (x+5))  (* hence,  x in 1..5   and  y <= 10 *)
       Else
          Assume (y <= (x-5)) (* hence,  x in 6..10  and  y <= 5  *)
       Fi -;
       r ::= a-x+y -;
       Assert "post" (r <= 25))
    ::("convex_hull7",
       Assume (1 <= x /\ x <= 10) -;
       If (x <= 5) Then
          Assume ((x+5) <= y) -;  (* hence,  x in 1..5   and  6 <= y *)
          a::=3*x
       Else
          Assume ((x-5) <= y) -; (* hence,  x in 6..10  and  1 <= y  *)
          Assume (3*x <= a)
       Fi -;
       r ::= a-x+y -;
       Assert "post" (8 <= r))
    ::("convex_hull8",
       Assume (1 <= x /\ x <= 10) -;
       If (x <= 5) Then 
          Assume (y <= (x+5)) -; (* hence,  x in 1..5   and  y <= 10 *)
          a::=3*x
       Else
          Assume (y <= (x-5)) -; (* hence,  x in 6..10  and  y <= 5  *)
          Assume (a <= 3*x)
       Fi -;
       r ::= a-x+y -;
       Assert "post" (r <= 25))
    ::("div2_ok0",
       div2 true -;
       Assert "post" (0 <= q /\ 0 <= r /\ r <= 1) )
    ::("div2_ok1",
       Assume(-100 < x /\ x < 100)-; 
       div2 (a < 100) -;
       Assert "post" (0 <= q /\ q <= 49 /\ 0 <= r /\ r <= 1)  )
    ::("div2_ok2",
       Assume(x=0)-;
       div2 (a = 0) -;
       Assert "post" (q=0 /\ r=0) )
    ::("div2_ok3",
       Assume(x=99)-; 
       div2 (a = 99) -;
       Assert "post" (q = 49 /\ 0 <= r /\ r <= 1)  )
    ::nil.

(* Statement expected to be rejected (because either invalid or incompleteness) *)
Definition basic_tests_ko : list (string * statement) :=
    ("div2_ko_init",    
       div2 (a < 100) -; 
       Assert "post" (q <= 50)  )
    ::("div2_ko_post",
       Assume(-100 < x /\ x < 100)-; 
       div2 true -; 
       Assert "post" (0 <= q /\ q <= 50 /\ 0 <= r /\ r <= 1)  )
    ::("div2_ko_preserv",
       Assume(-100 < x /\ x < 100)-; 
       div2 (q <= 50) -; 
       Assert "post" (q <= 50)  )
    ::("div2_ko_integer_incompletude", 
       Assume(x=99)-; 
       div2 (a=99) -;
       Assert "post" (q=49 /\ r=1)  )
    ::("assertko1-2-3",
       x::=1 -;
       Assert "assertko1" (x <= 0) -;
       x::=x-1 -;
       Assert "assertok" (x <= 0) -;
       x::=x+1 -;
       Assert "assertko2" (x <= 0) -;
       x::=x+1 -;
       Assert "assertko3" (x <= 1))
    ::nil.


(*** LINEARIZATION TESTS (by intervalization) ***)

Definition CTE:Z:=10000000.

(* test called barycentre0 in Verasco examples *)
Definition barycentre name (lbz ubz cz:Z) :=
  (* instantiating paramaters *)
  lb::=lbz -;
  ub::=ubz -;
  c::=cz -;
  (* check test validity *)
  Assert (name++"CheckC") (0 <= c) -;
  Assert (name++"CheckBound") (lb <= ub) -;
  (* non-deterministic init *)
  x1::| (-CTE <= x1 /\ x1 <= CTE) -;
  x2::| (-CTE <= x2 /\ x2 <= CTE) -;
  y1::| (-CTE <= y1 /\ y1 <= CTE) -;
  y2::| (-CTE <= y2 /\ y2 <= CTE) -;
  (* initialization of inputs *)
  Assume(0 <= a /\ a <= c) -;
  Assume(lb <= (2*x1-3*x2) /\ (2*x1-3*x2) <= ub) -;
  Assume(lb <= (5*y1+3*y2) /\ (5*y1+3*y2) <= ub) -;
  
  (* TESTS *)
  aux::|(0 <= aux /\ aux <= 2) -;
  If (aux=0) Then
    r::=a*(2*x1-3*x2)+c*(5*y1+3*y2)-(5*y1+3*y2)*a
  Else If (aux=1) Then
    r::=a*((2*x1-3*x2)-(5*y1+3*y2))+c*(5*y1+3*y2)
  Else
    r::=(c-a)*(5*y1+3*y2)+(2*x1-3*x2)*a 
  Fi Fi -;

  (* RESULT CHECK *)
  Assert (name++"Inf") (c*lb <= r) -;
  Assert (name++"Sup") (r <= c*ub).

Definition test_barycentre := 
  barycentre "b1" (-100) 100 5 -;
  barycentre "b2" (-20) 12 1 -;
  barycentre "b3" 10 20 2 -;
  barycentre "b4" (-2) 3 3 -;
  barycentre "b5" (-2) 2 5 -;
  barycentre "b6" (-1) 1 5 -;
  barycentre "b7" 0 0 5 -;
  barycentre "b8" (-1) 5 5.

Definition imul4 s a b c d e f :=
  (("mul4_" ++ s ++ "_ok1")%string,
       Assume (a <= x /\ x <= b /\ c <= y /\ y <= d)-; 
       r::=INTERV (STATIC (x*y)) -;
       Assert "post" (e <= r /\ r <= f))
  ::(("mul4_" ++ s ++ "_ok2")%string,
       Assume (a <= x /\ x <= b /\ c <= y /\ y <= d)-; 
       r::=INTERV (STATIC (y*x)) -;
       Assert "post" (e <= r /\ r <= f) )
  :: (("mul4_" ++ s ++ "_ok3")%string,
       Assume (a <= x /\ x <= b /\ c <= y /\ y <= d)-; 
       Assume (y*x <= r) -;
       Assert "post" (e <= r) )
  :: (("mul4_" ++ s ++ "_ok4")%string,
       Assume (a <= x /\ x <= b /\ c <= y /\ y <= d)-; 
       Assume (r <= x*y)  -;
       Assert "post" (r <= f) )
  ::nil. 

Definition imul30 s a b c e f :=
  (("mul30_" ++ s ++ "_ok1")%string,
       Assume (a <= x /\ x <= b /\ c <= y)-; 
       r::=INTERV (STATIC (x*y)) -;
       Assert "post" (e <= r /\ r <= f) )
  ::(("mul30_" ++ s ++ "_ok2")%string,
       Assume (a <= x /\ x <= b /\ c <= y)-; 
       r::=INTERV (STATIC (y*x)) -;
       Assert "post" (e <= r /\ r <= f) )
  ::nil. 

Definition imul31 s a b c e :=
  (("mul31_" ++ s ++ "_ok1")%string,
       Assume (a <= x /\ x <= b /\ c <= y)-; 
       r::=INTERV (STATIC (x*y)) -;
       Assert "post" (e <= r) )
  ::(("mul31_" ++ s ++ "_ok2")%string,
       Assume (a <= x /\ x <= b /\ c <= y)-; 
       r::=INTERV (STATIC (y*x)) -;
       Assert "post" (e <= r) )
  ::nil. 

Definition imul32 s a b c f :=
  (("mul32_" ++ s ++ "_ok1")%string,
       Assume (a <= x /\ x <= b /\ c <= y)-; 
       r::=INTERV (STATIC (x*y)) -;
       Assert "post" (r <= f) )
  ::(("mul32_" ++ s ++ "_ok2")%string,
       Assume (a <= x /\ x <= b /\ c <= y)-; 
       r::=INTERV (STATIC (y*x)) -;
       Assert "post" (r <= f) )
  ::nil. 

(* Statement expected to be accepted *)
Definition itv_tests_ok : list (string * statement) :=
     ("nonlin_ok",
       Assume (1 <= x /\ x <= 0)-;
       x::=y*x -;
       Assert "post" false)
(* remarque: on est sensible au signe du au caractere non-symetrique du test de signe 
   cf skip1_2
*)
    ::("nonlin_skip1_1_ok",
       Assume (y < x /\ 1 <= r)-;
       Assume (x * r <= y) -;
       Assert "post" (x <= 0 /\ y <= 0) )
    ::("nonlin_skip1_X_ok",
       Assume (y < x /\ 1 <= r)-;
       Assume (SKIP_ORACLE (r * x) <= y) -;
       Assert "post" (x < 0 /\ y < 0) )
    ::("nonlin_skip2_ok",
       Assume (y < x /\ 1 <= r)-;
       Assume (r * x <= 1) -;
       Assert "post" (x <= 1 /\ y <= 1) )
    ::("nonlin_skip3_ok",
       Assume (y < x /\ r <= 1)-;
       Assume (r * x <= y) -;
       Assert "post" (0 <= x) )
    ::("nonlin_skip4_ok",
       Assume (y < x)-;
       Assume (r * x <= y) -;
       Assert "post" (y < x) )
    ::("nonlin1_ok", 
       Assume (-3 <= x /\ x <= 3)-;
       Assume(12 <= INTERV ((x+1)*(x+1))) -;
       Assert "post" (1 <= x))
    ::("nonlin2_ok", 
       Assume (-3 <= x /\ x <= 3)-;
       Assume(12 <= (x+1)*(x+1)) -;
       Assert "post" (11 <= 5*x /\ x = 3))
    ::("nonlin2_1_ok", 
       Assume (-3 <= x /\ x <= 3)-;
       Assume(11 < (x+1)*(x+1)) -;
       Assert "post" (11 <= 5*x /\ x = 3))
    ::("nonlin3_ok", 
       Assume (-1 < x /\ x < 1)-;
       Assume(0 <> x*x) -;
       Assert "post" (false))
    ::("nonlin_assign1_ok",
       Assume (-3 <= x /\ x <= 3)-;
       r::=(x+1)*(x+1) -;
       Assert "post" (2*x-8 <= r /\ r <= 2*x + 10))
    ::("nonlin_assign2_ok",
      Assume (5 <= x /\ 1 <= y /\ y <= 3)-;
       y::=(y+2)*(x*3) -;
       Assert "post" (5 <= x /\ x*9 <= y /\ y <= x*15))
(* NB: pas precis... voir assign3_ko ci-dessous ! *)
    ::("nonlin_assign3_ok",
       Assume (1 <= x /\ x <= 4 /\ 0 <= y)-;
       x::=((x-1)*x)*(x+y-1) -;
       Assert "post" ((-3) * y - 27 <= x /\ x <= 15 * (y + 4)))
(* Interv statique versus dynamique *)
    ::("nonlin_assign4_ok",
       Assume (1 <= x /\ x <= 10 /\ y=x-1)-;
       r::=INTERV (x*(y-x)) -;
       Assert "post" (r<=10))
(* Linearisation avec statique versus dynamique + decoupage au milieu *)
    ::("nonlin_assign5_0_ok",
       Assume (1 <= x /\ x <= 10 /\ y=5)-;
       r::=x*(y-x) -;
       Assert "post" (r <= 22))
    ::("nonlin_assign5_0_X_ok",
       Assume (1 <= x /\ x <= 10 /\ y=5)-;
       r::=SKIP_ORACLE (x*(y-x)) -;
       Assert "post" (r <= 20))
    ::("nonlin_assign5_2_ok",
       Assume (1 <= x /\ x <= 10)-;
       r::=x*(5-x) -;
       Assert "post" (r <= 22))
     ::("double_intervalization_unsat_ok",
       Assume (0 <= x /\ x+1 <= y /\ y <= 1000 /\ c <= -2) -;
       Assume (x*(y-2) <= c) -;
       Assert "post1" (1 <= x) -;
       Assert "post2" (2 <= y) -;
       Assert "post3" (false))
(* Barycentre *)
    ::("barycentre_ok1_1",   
       Assume (1 <= a /\ a <= 5 /\ -10 <= x /\ x <= 10 /\ -10 <= y /\ y <= 10)-;
       r::= a*(x-y) + 5*y -;
       Assert "post" (-50 <= r /\ r <= 50)
       )       
    ::("barycentre_ok1_2",   
       Assume (1 <= a /\ a <= 5 /\ -10 <= x /\ x <= 10 /\ -10 <= y /\ y <= 10)-;
       r::= a*x+(5-a)*y -;
       Assert "post" (-50 <= r /\ r <= 50)
       )
    ::("barycentre_ok2_1_X1",   
       Assume (0 <= a /\ a <= 5 /\ -1 <= x /\ x <= 1 /\ -1 <= y /\ y <= 1)-;
       r::= a*(x-y)+5*y -;
       Assert "post1" (-5 <= r) -;
       Assert "post2" (r <= 5)
       ) 
    ::("barycentre_ok2_1_X2",   
       Assume (0 <= a /\ a <= 5 /\ -1 <= x /\ x <= 1 /\ -1 <= y /\ y <= 1)-;
       r::= SKIP_ORACLE (a*(x-y)+5*y) -;
       Assert "post" (-5 <= r /\ r <= 5)
       ) 
    ::("barycentre_ok2_2",   
       Assume (0 <= a /\ a <= 5 /\ 1 <= x /\ x <= 3 /\ 1 <= y /\ y <= 3)-;
       r::= a*(x-y)+5*y -;
       Assert "post1" (5 <= r) -;
       Assert "post2" (r <= 15)
       ) 
    ::("barycentre_ok2_2_X",   
       Assume (0 <= a /\ a <= 5 /\ 1 <= x /\ x <= 3 /\ 1 <= y /\ y <= 3)-;
       r::= SKIP_ORACLE (a*(x-y)+5*y) -;
       Assert "post" (5 <= r /\ r <= 15)
       ) 
    ::("barycentre_ok3",   
       Assume (1 <= a /\ a <= 5 /\ y <= x)-;
       r::=a*(x-y) + 5*y -;
       Assume(y <= x) -;
       Assert "post" (r <= 5*x /\ 5*y <= r)
       )     
    ::("big_barycentre_ok",test_barycentre)
   
(* Parabole *)
    ::("parabola_ok", 
       Assume (a=2 /\ y=10 /\ q=100)-;
       Assume (y <= x /\ x <= q) -;
       r::=a*x*x -;
       Assert "post1" (a*y*y <= r) -;
       Assert "post2" (r <= a*q*q) -;
       Assert "post3" (r <= a*((q+y)*x-q*y)))
    ::("parabola_ok1", 
       Assume (a=2 /\ y=10 /\ q=100)-;
       Assume (y <= x /\ x <= q) -;
       r::=SKIP_ORACLE ((INTERV (a*(x-10)))*(x-y) + INTERV (2*a*10)*x - 100*a) -;
       Assert "post1" (a*y*y <= r) -;
       Assert "post2" (r <= a*q*q) -;
       Assert "post3" (r <= a*((q+y)*x-q*y)))
    ::("parabola_ok2", 
       Assume (a=2 /\ y=10 /\ q=100)-;
       Assume (y <= x /\ x <= q) -;
       r::=SKIP_ORACLE ((INTERV a)*(x*10-100) + 100*a + (INTERV (a*(x-10)))*(x-y) + (INTERV(a*10))*(x-10)) -;
       Assert "post1" (a*y*y <= r) -;
       Assert "post2" (r <= a*q*q) -;
       Assert "post3" (r <= a*((q+y)*x-q*y)))
(* basic checks on intervals *)
    ::((imul4 "pppp" 3 7 5 11 15 77)
    ++ (imul4 "nppp" (-7) 3 5 11 (-77) 33)
    ++ (imul4 "nnpp" (-7) (-3) 5 11 (-77) (-15))
    ++ (imul4 "nnnp" (-7) (-3) (-5) 11 (-77) 35)
    ++ (imul4 "nnnn" (-7) (-3) (-11) (-5) 15 77)
    ++ (imul4 "nzpp" (-7) 0 5 11 (-77) 0)
    ++ (imul30 "zp" 0 0 5 0 0)
    ++ (imul30 "zn" 0 0 (-5) 0 0)
    ++ (imul31 "ppp" 3 7 5 15)
    ++ (imul31 "ppn" 3 7 (-5) (-35))
    ++ (imul32 "nnp" (-7) (-3) 5 (-15))).

Definition itv_tests_ko : list (string * statement) :=
(* NB: influence of Opp on good interval *)
    ("nonlin_skip1_X_ko",
       Assume (y < x /\ 1 <= r)-;
       Assume (SKIP_ORACLE (Opp (r * (Opp x))) <= y) -;
       Assert "post" (x < 0 /\ y < 0) )
    ::("nonlin_skip1_ko",
       Assume (y < x /\ 1 <= r)-;
       Assume (r * x <= y) -;
       Assert "post" (x < 0 /\ y < 0) )
    ::("nonlin1_ko", 
       Assume (-3 <= x /\ x <= 3)-;
       Assume(12 <= SKIP_ORACLE (INTERV ((x+1)*(x+1)))) -;
       Assert "post" (2 <= x))
    ::("nonlin_assign3_ko",
       Assume (1 <= x /\ x <= 4 /\ 0 <= y)-;
       x::=((x-1)*x)*(x+y-1) -;
       Assert "post" (0 <= x /\ x <= y*12+36))
    ::("nonlin_assign4_ko",
       Assume (1 <= x /\ x <= 10 /\ y=x-1)-;
       r::=SKIP_ORACLE (INTERV (STATIC (x*(y-x)))) -;
       Assert "post" (r<=50))
    ::("nonlin_assign5_1_ko",
       Assume (1 <= x /\ x <= 10 /\ y=5)-;
       r::=SKIP_ORACLE (STATIC (x*(y-x))) -;
       Assert "post" (r <= 39))
    ::("nonlin_assign5_2_ko",
       Assume (1 <= x /\ x <= 10)-;
       r::=SKIP_ORACLE (x*(5-x)) -;
       Assert "post" (r <= 39))
    ::("nonlin_assign5_3_ko",
       Assume (1 <= x /\ x <= 10 /\ y=5)-;
       r::= x*(y-x) -;
       Assert "post" (r <= 21))
   ::("nonlin_assign5_4_ko",
       Assume (1 <= x /\ x <= 10)-;
       r::= x*(5-x) -;
       Assert "post" (r <= 21))
    ::("barycentre_ko",   
       Assume (1 <= a /\ a <= 5 /\ 1 <= x /\ x <= 3 /\ 1 <= y /\ y <= 3)-;
       r::=SKIP_ORACLE (INTERV (a*x+(5-a)*y)) -;
       Assert "post" (5 <= r /\ r <= 15)
       ) 
   ::nil.

Definition tests_ok := basic_tests_ok ++ itv_tests_ok.
Definition tests_ko := basic_tests_ko ++ itv_tests_ko.

End Examples.


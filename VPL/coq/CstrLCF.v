Require Export NumC.

(* A "Logical Consequences Factory" 
   for a set of constraints
   in a LCF-style !
*)
Record cstrLCF (E C: Type) := {
  top: C;
  triv: cmpT -> QNum.t -> C;
  add: C -> C -> C;
  mul: QNum.t -> C -> C;
  merge: C -> C -> C; (* merge of inequalities into one equality *)
  to_le: C -> C;
  export: C -> E;
}.

Record pedraInput (T E C: Type) := {
  lcf:> cstrLCF E C;
  backend: T;
  cert: (list C)
}. 


(* certificates for intervals *)

Inductive bndT (C:Type): Type
:=
  | Infty: bndT C
  | Open: QNum.t -> C -> bndT C
  | Closed: QNum.t -> C -> bndT C.

Arguments Infty {C}.
Arguments Open [C].
Arguments Closed [C].

Record itvT (C:Type): Type
:= mk {
       low: bndT C;
       up: bndT C
}.

Arguments low [C].
Arguments up [C].

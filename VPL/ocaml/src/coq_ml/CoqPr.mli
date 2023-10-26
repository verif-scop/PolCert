(** Pretty-printing support for Coq standard library types.
The [Raw] version of each function produces a string which
describes the structure of its argument in terms of constructors.
The primed version produces a Coq string. *)

val charListTr: char list -> string

val posPr: BinNums.positive -> string
val posPrRaw: BinNums.positive -> string

val posPr': BinNums.positive -> char list
val posPrRaw': BinNums.positive -> char list

val zPr: BinNums.coq_Z -> string
val zPrRaw: BinNums.coq_Z -> string

val zPr': BinNums.coq_Z -> char list
val zPrRaw': BinNums.coq_Z -> char list

val charListTr: char list -> string
val stringTr: string -> char list

val posTr: BinNums.positive -> Scalar.Rat.Z.t
val zTr: BinNums.coq_Z -> Scalar.Rat.Z.t

val exprPr: Ring_polynom_AddOnQ.coq_PExpr -> string
val exprPr': Ring_polynom_AddOnQ.coq_PExpr -> char list

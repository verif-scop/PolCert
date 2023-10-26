let charListTr: char list -> string
= fun l ->
(*
	let s = String.create (List.length l) in
	let _ = List.fold_left (fun i c -> String.set s i c; i + 1) 0 l in
	s
*)
  let buf = Buffer.create (List.length l) in
  List.iter (fun c -> Buffer.add_char buf c) l;
  Buffer.contents buf;;

let stringTr: string -> char list
= fun s ->
	let rec f: int -> char list -> char list
	= fun i l ->
		if i >= 0
		then f (i - 1) ((String.get s i)::l)
		else l
	in
	f ((String.length s) - 1) []

module Nb = Scalar.Rat

let posTr: BinNums.positive -> Nb.Z.t
= fun p0 ->
	let rec f: int -> Nb.Z.t -> BinNums.positive -> Nb.Z.t
	= fun shift acc -> function
		| BinNums.Coq_xH -> Nb.Z.orL acc (Nb.Z.shiftL Nb.Z.u shift)
		| BinNums.Coq_xO p -> f (shift + 1) acc p
		| BinNums.Coq_xI p -> f (shift + 1) (Nb.Z.orL acc (Nb.Z.shiftL Nb.Z.u shift)) p
	in f 0 Nb.Z.z p0

let posPr: BinNums.positive -> string
= fun p ->
	let z = posTr p in
	Nb.Z.pr z

let posPr': BinNums.positive -> char list
= fun p -> stringTr (posPr p)

let posPrRaw: BinNums.positive -> string
= fun p ->
	let rec pr l = function
		| BinNums.Coq_xH -> "xH"::l
		| BinNums.Coq_xI p -> pr ("xI"::l) p
		| BinNums.Coq_xO p -> pr ("xO"::l) p
	in
	String.concat " " (pr [] p)

let posPrRaw': BinNums.positive -> char list
= fun p -> stringTr (posPrRaw p)

let zTr: BinNums.coq_Z -> Nb.Z.t
= function
	| BinNums.Z0 -> Nb.Z.z
	| BinNums.Zpos p -> posTr p
	| BinNums.Zneg p -> Nb.Z.neg (posTr p)

let zPr: BinNums.coq_Z -> string
= fun z -> Nb.Z.pr (zTr z)

let zPr': BinNums.coq_Z -> char list
= fun z -> stringTr (zPr z)

let zPrRaw: BinNums.coq_Z -> string
    = function
	| BinNums.Z0 -> "Z0"
	| BinNums.Zpos p -> Printf.sprintf "Zpos (%s)" (posPrRaw p)
	| BinNums.Zneg p -> Printf.sprintf "Zneg (%s)" (posPrRaw p)

let zPrRaw': BinNums.coq_Z -> char list
    = fun z ->
    stringTr (zPrRaw z)

let qPr : QArith_base.coq_Q -> string
    = fun q ->
    Printf.sprintf "%s/%s"
        (zPr q.QArith_base.coq_Qnum)
        (posPr q.QArith_base.coq_Qden)

let rec exprPr: Ring_polynom_AddOnQ.coq_PExpr -> string
    = Ring_polynom.(function
    | PEO -> "0"
    | PEI -> "1"
    | PEc c -> qPr c
    | PEX p -> "x_" ^ (posPr p)
    | PEadd (p1,p2) -> Printf.sprintf "%s + %s" (exprPr p1) (exprPr p2)
    | PEsub (p1,p2) -> Printf.sprintf "%s - (%s)" (exprPr p1) (exprPr p2)
    | PEmul (p1,p2) -> Printf.sprintf "(%s) * (%s)" (exprPr p1) (exprPr p2)
    | PEopp (p) -> Printf.sprintf "-1*(%s)" (exprPr p)
    | PEpow (p,_) -> Printf.sprintf "(%s)^?" (exprPr p)
    )

let rec exprPr': Ring_polynom_AddOnQ.coq_PExpr -> char list
    = fun p ->
    exprPr p |> stringTr

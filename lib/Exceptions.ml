open OpenScopAST
open Printf
open Camlcoq
open Floats
(* open Cabs *)
open C
open C2C

exception CompilationError
exception Abort
exception TypecheckError

let comp_error (oloc: OpenScopAST.location option) f s =
  match oloc with
  | Some loc ->
     fprintf stdout "error(%d): %a" loc.lineno (fun oc -> fprintf oc f) s; raise CompilationError
  | None ->
     fprintf stdout "error: %a" (fun oc -> fprintf oc f) s; raise CompilationError

let type_error (oloc: OpenScopAST.location option) f s =
   match oloc with
   | Some loc ->
      fprintf stdout "type error(%d): %a" loc.lineno (fun oc -> fprintf oc f) s; raise TypecheckError
   | None ->
      fprintf stdout "type error: %a" (fun oc -> fprintf oc f) s; raise TypecheckError

 

exception Overflow
exception Bad_digit

let parse_int (base: int) (s: string) =
  let max_val = (* (2^64-1) / base, unsigned *)
    match base with
    (*|  8 -> 2305843009213693951L*)
    | 10 -> 1844674407370955161L
    | 16 -> 1152921504606846975L
    |  _ -> assert false in
  let v = ref 0L in
  for i = 0 to String.length s - 1 do
    let c = s.[i] in
    let digit =
      if c >= '0' && c <= '9' then Char.code c - 48
      else if c >= 'A' && c <= 'F' then Char.code c - 55
      else raise Bad_digit in
    if digit >= base then raise Bad_digit;
    if !v < 0L || !v > max_val then raise Overflow;
    (* because (2^64 - 1) % 10 = 5, not 9 *)
    if base = 10 && !v = max_val && digit > 5 then raise Overflow;
    v := Int64.mul !v (Int64.of_int base);
    v := Int64.add !v (Int64.of_int digit)
  done;
  !v

let elab_int_constant (i: OpenScopAST.intInfo) (loc: OpenScopAST.location) =
  let s = String.map (fun d -> match d with
  | '0'..'9' | 'A'..'F' -> d
  | 'a'..'f' -> Char.chr (Char.code d - 32)
  | _ -> raise Bad_digit) (camlstring_of_coqstring i.coq_II_integer) in
  (* Determine base *)
  let base = 10
  in
  (* Parse digits *)
  let v =
    try parse_int base s
    with
    | Overflow ->
        comp_error (Some loc) "integer literal %s is too large to be represented in any integer type" (camlstring_of_coqstring i.coq_II_integer)
    | Bad_digit ->
        comp_error (Some loc) "bad digit in integer literal %s" (camlstring_of_coqstring i.coq_II_integer)
  in
  if i.coq_II_isNegative then Int64.neg v else v


let elab_float_constant (f: OpenScopAST.floatInfo) (loc: OpenScopAST.location) =
  let ty = match f.suffix_FI with
    (* | Some ("l"|"L") -> FLongDouble *)
    (* | Some ("f"|"F") -> FFloat *)
    | None -> FDouble
    | _ -> assert false (* The lexer should not accept anything else. *)
  in
  let v = {
    hex=f.isHex_FI;
    intPart=begin match f.integer_FI with Some s -> camlstring_of_coqstring s | None -> ("0") end;
    fracPart=begin match f.fraction_FI with Some s -> camlstring_of_coqstring s | None -> ("0") end;
    exp=begin match f.exponent_FI with Some s -> camlstring_of_coqstring s | None -> ("0") end }
  in
  (v, ty)

(* convert to float64 *)
let convertFloatPure f kind =
  let mant = z_of_str f.C.hex (f.C.intPart ^ f.C.fracPart) 0 in
  match mant with
    | Z.Z0 ->
      begin match kind with
      | FFloat -> Float.to_single Float.zero
      | FDouble | FLongDouble -> Float.zero
      end
    | Z.Zpos mant ->
      let sgExp = match f.C.exp.[0] with '+' | '-' -> true | _ -> false in
      let exp = z_of_str false f.C.exp (if sgExp then 1 else 0) in
      let exp = if f.C.exp.[0] = '-' then Z.neg exp else exp in
      let shift_exp =
  (if f.C.hex then 4 else 1) * String.length f.C.fracPart in
      let exp = Z.sub exp (Z.of_uint shift_exp) in

      let base = P.of_int (if f.C.hex then 2 else 10) in

      begin match kind with
      | FFloat -> assert false
      | FDouble | FLongDouble ->
    let f = Float.from_parsed base mant exp in
          checkFloatOverflow f "double";
          f
      end

    | Z.Zneg _ -> assert false

module P = PolyLang.PolyLang(SInstr.SInstr)
open OpenScop

let z = Camlcoq.Z.of_sint
let n = Camlcoq.Nat.of_int
let chars = Camlcoq.coqstring_of_camlstring
let failures = ref 0
let checked_cases = ref 0

let relation kind outputs inputs parameters rows = {
  rel_type = kind;
  meta = {row_nb = n (List.length rows);
          col_nb = n (outputs + inputs + parameters + 2);
          out_dim_nb = n outputs; in_dim_nb = n inputs;
          local_dim_nb = n 0; param_nb = n parameters};
  constrs = List.map (fun (inequality, values) -> inequality, List.map z values) rows;
}

let scop iterators parameters rows =
  let names prefix count = List.init count (fun i -> chars (prefix ^ string_of_int i)) in
  let schedule = -1 :: List.init iterators (fun i -> if i = 0 then 1 else 0)
                   @ List.init parameters (fun _ -> 0) @ [0] in
  {context = {lang = chars "C"; params = Some (names "p" parameters);
              param_domain = relation CtxtTy 0 0 parameters []};
   statements = [{domain = relation DomTy iterators 0 parameters rows;
                  scattering = relation ScttTy 1 iterators parameters [false, schedule];
                  access = [];
                  stmt_exts_opt = Some [StmtBody (names "i" iterators, ArrSkip)]}];
   glb_exts = []}

let get = function
  | Result.Okk p -> p
  | Result.Err message -> failwith (Camlcoq.camlstring_of_coqstring message)

let domain ((pis, _), _) = (List.hd pis).P.pi_poly

let rec points = function
  | 0 -> [[]]
  | count -> List.concat_map (fun tail -> List.map (fun x -> x :: tail)
      [-2; -1; 0; 1; 2]) (points (count - 1))

let dot a b = List.fold_left (+) 0 (List.map2 ( * ) a b)

let satisfies rows point = List.for_all (fun (inequality, row) ->
  let coefficients = List.filteri (fun i _ -> i < List.length row - 1) row in
  let value = dot coefficients point + List.hd (List.rev row) in
  if inequality then value >= 0 else value = 0) rows

let test name iterators parameters rows =
  incr checked_cases;
  let candidate = scop iterators parameters rows in
  let raw = P.from_openscop_domain' (List.hd candidate.statements).domain.constrs
      (n iterators) (n parameters) in
  let imported = get (P.from_openscop_complete candidate) in
  let replaced = get (P.from_openscop imported candidate) in
  let outputs = ["row import", raw; "complete import", domain imported;
                 "source-based full import", domain replaced] in
  let mismatches = ref 0 in
  List.iter (fun point ->
    let internal_point = List.filteri (fun i _ -> i >= iterators) point
                       @ List.filteri (fun i _ -> i < iterators) point in
    let expected = satisfies rows point in
    List.iter (fun (entry, result) ->
      let actual = Linalg.in_poly (List.map z internal_point) result in
      if actual <> expected then begin
        incr mismatches;
        if !mismatches <= 3 then
          Printf.eprintf "[openscop-domain] mismatch %s: %s point=[%s] expected=%b actual=%b\n%!"
            name entry (String.concat "," (List.map string_of_int point)) expected actual
      end) outputs) (points (iterators + parameters));
  if !mismatches > 0 then incr failures;
  Printf.printf "[openscop-domain] %s %s (%d mismatches)\n%!"
    (if !mismatches = 0 then "PASS" else "FAIL") name !mismatches

let () =
  test "positive singleton" 1 0 [false, [1; -1]];
  test "sign-reversed positive singleton" 1 0 [false, [-1; 1]];
  test "negative singleton" 1 0 [false, [1; 1]];
  test "zero singleton" 1 0 [false, [1; 0]];
  test "fractional equality has no integer point" 1 0 [false, [2; -1]];
  test "scaled equality" 1 0 [false, [-2; 2]];
  test "parameter follows iterator in OpenScop" 1 1 [false, [1; -1; -1]];
  test "two iterator coordinates" 2 1 [false, [2; -1; 3; -2]];
  test "two parameter coordinates" 1 2 [false, [2; -3; 1; 1]];
  test "conjunction of equalities" 2 0 [false, [1; 0; -1]; false, [0; 1; 1]];
  test "mixed equality and inequality" 1 1 [false, [1; -1; 0]; true, [-1; 0; 1]];
  test "contradictory constant equality" 1 0 [false, [0; 1]];
  test "tautological equality" 1 0 [false, [0; 0]];
  test "unchanged nonzero inequality" 1 0 [true, [1; -1]];
  test "opposite inequality" 1 0 [true, [-1; 1]];
  Printf.printf "[openscop-domain] cases=%d failures=%d\n%!" !checked_cases !failures;
  if !failures <> 0 then exit 1

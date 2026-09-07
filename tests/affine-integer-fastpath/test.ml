module A = AffineValidator.AffineValidator(SPolIRs.SPolIRs)
module P = A.PolyLang
module I = SInstr.SInstr

let z = Camlcoq.Z.of_sint
let n = Camlcoq.Nat.of_int
let poly rows = List.map (fun (a, b) -> List.map z a, z b) rows
let unalarm (value, valid) = if valid then value else failwith "checker alarm"
let expect name expected actual =
  if expected <> actual then failwith (name ^ ": unexpected result");
  Printf.printf "[affine-integer-fastpath] PASS %s = %b\n%!" name actual

let () =
  let gap k = poly
    [([-1; 0], 0); ([1; 0], 2); ([0; -1], 0); ([0; 1], 2);
     ([1; -1], -1); ([-2; 2], k); ([2; -2], -k)] in
  let parity = gap 3 in
  expect "parity rational query has a witness" false
    (unalarm (PolyTest.isBottom parity));
  expect "integer fallback eliminates fractional witness" true
    (unalarm (A.isBottom_integer_fallback parity));
  expect "ordinary affine query uses integer fallback" true
    (unalarm (A.validate_lt_ge_pair [] [] parity));
  expect "real dependence is still rejected" false
    (unalarm (A.validate_lt_ge_pair [] [] (gap 2)));
  expect "primitive lattice-free case remains conservative" false
    (unalarm (A.isBottom_integer_fallback
       (poly [([-1; -1], -1); ([4; 1], 3); ([1; 4], 3)])));
  let aid = Camlcoq.intern_string "A" in
  let pi = {
    P.pi_depth = n 1;
    pi_instr = I.SAssign (I.AcVar aid, I.ExVar (n 0));
    pi_poly = poly [([-1], 0); ([1], 2)];
    pi_schedule = poly [([1], 0)];
    pi_point_witness = PointWitness.PSWIdentity (n 1);
    pi_transformation = poly [([1], 0)];
    pi_access_transformation = poly [([1], 0)];
    pi_waccess = [aid, []];
    pi_raccess = [];
  } in
  let program pi = (([pi], []), [aid, ()]) in
  let source = program pi in
  expect "unchanged program accepted" true
    (unalarm (A.validate_general source source));
  let reversed = {pi with P.pi_schedule = poly [([-1], 0)]} in
  expect "reversed scalar writes rejected" false
    (unalarm (A.validate_general source (program reversed)));
  let tied = {pi with P.pi_schedule = poly [([0], 0)]} in
  expect "dependent timestamp ties rejected" false
    (unalarm (A.validate_general source (program tied)));
  let changed_domain = {pi with P.pi_poly = poly [([-1], 0); ([1], 1)]} in
  expect "unchanged schedule does not bypass domain checks" false
    (unalarm (A.validate_general source (program changed_domain)));
  let bad_access = {pi with P.pi_waccess = []} in
  expect "unchanged schedule does not bypass access checks" false
    (unalarm (A.validate_general (program bad_access) (program bad_access)));
  let first = {pi with
    P.pi_poly = poly [([-1], 0); ([1], 0)];
    pi_schedule = poly [([0], 0)];
    pi_instr = I.SAssign (I.AcVar aid, I.ExConst (z 0))} in
  let second = {first with
    P.pi_schedule = poly [([0], 1)];
    pi_instr = I.SAssign (I.AcVar aid, I.ExConst (z 1))} in
  let pair a b = (([a; b], []), [aid, ()]) in
  let source_pair = pair first second in
  expect "unchanged statement pair accepted" true
    (unalarm (A.validate_general source_pair source_pair));
  expect "changing only the first statement cannot bypass checking" false
    (unalarm (A.validate_general source_pair
      (pair {first with P.pi_schedule = poly [([0], 2)]} second)));
  expect "changing only the second statement cannot bypass checking" false
    (unalarm (A.validate_general source_pair
      (pair first {second with P.pi_schedule = poly [([0], -1)]})))

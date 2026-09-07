module V = SParallelPolOpt.ValidatorCore
module C = V.ParallelCore
module P = SPolIRs.SPolIRs.PolyLang
module I = SInstr.SInstr

let z = Camlcoq.Z.of_sint
let n = Camlcoq.Nat.of_int
let rows rs = List.map (fun (a, b) -> List.map z a, z b) rs
let unalarm (v, ok) = if ok then v else failwith "checker alarm"
let expect name expected actual =
  if expected <> actual then failwith (name ^ ": unexpected result");
  Printf.printf "[parallel-scope] PASS %s\n%!" name
let plan dim statements =
  { C.scoped_dim = n dim; scoped_statements = List.map n statements }
let lower plans ((pis, env), vars) =
  ((List.mapi (fun index pi ->
    let zero = (List.init (List.length env + Camlcoq.Nat.to_int pi.P.pi_depth)
      (fun _ -> z 0), z 0) in
    { pi with P.pi_schedule = SParallelPolOpt.scoped_parallel_rows plans
        (n index) (n 0) zero pi.P.pi_schedule }) pis, env), vars)
let independent pp dim = unalarm (V.check_pprog_parallel_currentb pp (n dim))
let affine oldp newp = unalarm (V.validate_general oldp newp)
let mkpi depth instr writes reads schedule =
  let identity = List.init depth (fun k ->
    (List.init depth (fun j -> z (if j = k then 1 else 0)), z 0)) in
  let domain = List.concat (List.init depth (fun k ->
    [List.init depth (fun j -> z (if j = k then -1 else 0)), z 0;
     List.init depth (fun j -> z (if j = k then 1 else 0)), z 3])) in
  { P.pi_depth = n depth; pi_instr = instr; pi_poly = domain;
    pi_schedule = rows schedule; pi_point_witness = PointWitness.PSWIdentity (n depth);
    pi_transformation = identity; pi_access_transformation = identity;
    pi_waccess = writes; pi_raccess = reads }

let () =
  let a = Camlcoq.intern_string "scope_A" in
  let b = Camlcoq.intern_string "scope_B" in
  let a_t = I.AcArr (a, [I.AeVar (n 0)]) in
  let b_ti = I.AcArr (b, [I.AeVar (n 0); I.AeVar (n 1)]) in
  let s1 = mkpi 2 (I.SAssign (a_t, I.ExVar (n 1)))
    [a, rows [([1;0],0)]] [] [([1;0],0);([0;0],0);([0;1],0)] in
  let s2 = mkpi 2 (I.SAssign (b_ti, I.ExAccess a_t))
    [b, rows [([1;0],0);([0;1],0)]] [a, rows [([1;0],0)]]
    [([1;0],0);([0;0],1);([0;1],0)] in
  let source = (([s1;s2], []), [a,();b,()]) in
  expect "global dimension is not independent" false (independent source 2);
  let scoped = lower [plan 2 [1]] source in
  expect "local hint preserves order with a variable outer prefix" true (affine source scoped);
  expect "selected phase becomes certifiably parallel" true (independent scoped 5);
  expect "canonicalization keeps the mapped parallel slot independent" true
    (independent (P.canonicalize_schedule_pprog scoped) 3);
  let ((pis,_),_) = scoped in
  expect "unselected statement keeps sequential iterator" s1.P.pi_schedule
    (List.filteri (fun k _ -> k mod 2 = 0) (List.hd pis).P.pi_schedule);
  expect "unselected statement has a constant parallel slot" (rows [([0;0],0)])
    [List.nth (List.hd pis).P.pi_schedule 5];
  let wrong = lower [plan 2 [0]] source in
  expect "a scope does not bypass real dependences" false (independent wrong 5);
  expect "hint lowering does not alter instructions or domains" true
    (List.for_all2 (fun oldp newp ->
      oldp.P.pi_instr = newp.P.pi_instr && oldp.P.pi_poly = newp.P.pi_poly &&
      oldp.P.pi_transformation = newp.P.pi_transformation &&
      oldp.P.pi_waccess = newp.P.pi_waccess && oldp.P.pi_raccess = newp.P.pi_raccess)
      [s1;s2] pis);
  let a_ti = I.AcArr (a, [I.AeVar (n 0); I.AeVar (n 1)]) in
  let b_tj = I.AcArr (b, [I.AeVar (n 0); I.AeVar (n 2)]) in
  let x = mkpi 3 (I.SAssign (a_ti, I.ExVar (n 2)))
    [a, rows [([1;0;0],0);([0;1;0],0)]] []
    [([1;0;0],0);([0;0;0],0);([0;1;0],0);([0;0;1],0)] in
  let y = mkpi 3 (I.SAssign (b_tj, I.ExVar (n 1)))
    [b, rows [([1;0;0],0);([0;0;1],0)]] []
    [([1;0;0],0);([0;0;0],1);([0;1;0],0);([0;0;1],0)] in
  let source3 = (([x;y], []), [a,();b,()]) in
  expect "first shared dimension is not globally parallel" false (independent source3 2);
  expect "second shared dimension is not globally parallel" false (independent source3 3);
  let two_scopes = lower [plan 2 [0]; plan 3 [1]] source3 in
  expect "different local parallel depths preserve order" true (affine source3 two_scopes);
  expect "first phase parallel coordinate certifies" true (independent two_scopes 5);
  expect "second phase parallel coordinate certifies" true (independent two_scopes 7);
  expect "overlapping invalid hint remains rejected" false
    (independent (lower [plan 2 [0];plan 2 [1]] source3) 5);
  (* The first statement is independent across i, but its j iterations write
     the same A[t,i].  A certificate for i must not count as accepting both
     local hints.  The existing many-dimension collector intentionally keeps
     valid certificates; the scoped driver therefore needs its all-hints gate. *)
  let partial_scopes = lower [plan 2 [0]; plan 3 [0]] source3 in
  expect "partial multi-hint candidate preserves sequential semantics" true
    (affine source3 partial_scopes);
  let dimension_checks = List.map (independent partial_scopes) [5;7] in
  expect "partial multi-hint candidate has exactly one independent dimension"
    [true;false] dimension_checks;
  let certificates = unalarm
    (SParallelPolOpt.collect_parallel_current_codegen_certs partial_scopes
       (List.map n [5;7])) in
  expect "many-dimension collection retains only the valid certificate" 1
    (List.length certificates);
  expect "one certificate cannot satisfy both scoped hints" false
    (List.for_all (fun accepted -> accepted) dimension_checks)

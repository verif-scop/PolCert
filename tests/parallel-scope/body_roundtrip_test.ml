open OpenScop

let chars = Camlcoq.coqstring_of_camlstring
let z = Camlcoq.Z.of_sint
let atom name = ArrAtom (AVar (chars name))
let scalar name = ArrAccessAtom (ArrAccess (chars name, []))
let integer n = ArrAtom (AInt (z n))
let array name index = ArrAccess (chars name, [index])
let lhs = array "A" (AfVar (chars "$i0"))

let expect name condition =
  if not condition then failwith ("body-roundtrip: " ^ name);
  Printf.printf "[body-roundtrip] PASS %s\n%!" name

let read path =
  match OpenScopReader.read path with
  | Some scop -> scop
  | None -> failwith ("cannot parse OpenScop fixture: " ^ path)

let with_body scop body =
  match scop.statements with
  | [] -> failwith "body-roundtrip fixture contains no statements"
  | stmt :: _ ->
      let iterators = match stmt.stmt_exts_opt with
        | Some (StmtBody (iterators, _) :: _) -> iterators
        | _ -> failwith "body-roundtrip fixture has no statement body" in
      { scop with statements =
          [{ stmt with stmt_exts_opt = Some [StmtBody (iterators, body)] }] }

let body scop =
  match scop.statements with
  | [stmt] -> PlutoTilingValidator.stmt_body stmt
  | _ -> failwith "body-roundtrip expects one statement"

let roundtrip scop =
  let path = Filename.temp_file "polcert-body-roundtrip-" ".scop" in
  Fun.protect
    ~finally:(fun () -> Sys.remove path)
    (fun () ->
      OpenScopPrinter.openscop_printer path scop;
      read path)

let accepts name before after =
  PlutoTilingValidator.require_same_shape before after;
  expect name true

let rejects name before after =
  let rejected =
    try
      PlutoTilingValidator.require_same_shape before after;
      false
    with PlutoTilingValidator.ValidationError _ -> true in
  expect name rejected

let () =
  let fixture = read
    "tools/tiling_routes/fixtures/fusion5-scalar-interleaved.midtransform.scop" in
  (* The actual identity-route discrepancy: ExVar exports an ArrAtom/AVar,
     whereas reading the printed bare name produces a zero-index access. *)
  List.iter (fun name ->
    let before = with_body fixture (ArrAssign (lhs, atom name)) in
    let after = roundtrip before in
    expect (name ^ ": raw AST changes during printer/reader round trip")
      (body before <> body after);
    expect (name ^ ": reader produces a zero-index access")
      (body after = Some (ArrAssign (lhs, scalar name)));
    accepts (name ^ ": unchanged body survives round trip") before after)
    ["$i0"; "N"];

  (* Keep every operation and operand position; only the two bare-name
     constructors are interchangeable in this serialization-level check. *)
  let nested variable =
    ArrCond (
      ArrAnd (ArrLt (variable "$i0", integer 3),
              ArrEq (variable "N", integer 7)),
      ArrCall (chars "f", [
        ArrAdd (variable "$i0", integer 1);
        ArrMinus (variable "N", integer 2);
        ArrMulti (variable "$i0", integer 3);
        ArrDiv (variable "N", integer 4)]),
      ArrLe (variable "$i0", variable "N")) in
  let nested_before = with_body fixture (ArrAssign (lhs, nested atom)) in
  let nested_after = with_body fixture (ArrAssign (lhs, nested scalar)) in
  expect "nested operations, calls, and conditionals have distinct raw ASTs"
    (body nested_before <> body nested_after);
  accepts "nested operations, calls, and conditionals preserve their shape"
    nested_before nested_after;
  expect "body normalization is idempotent"
    (let normalized = PlutoTilingValidator.normalize_stmt_body
        (ArrAssign (lhs, nested atom)) in
     PlutoTilingValidator.normalize_stmt_body normalized = normalized);

  let base rhs = with_body fixture (ArrAssign (lhs, rhs)) in
  rejects "a changed variable is rejected"
    (base (atom "$i0")) (base (scalar "$i1"));
  rejects "a scalar is not confused with an indexed access"
    (base (atom "$i0"))
    (base (ArrAccessAtom (array "$i0" (AfInt (z 0)))));
  rejects "a changed operator is rejected"
    (base (ArrAdd (atom "$i0", integer 1)))
    (base (ArrMinus (scalar "$i0", integer 1)));
  rejects "a changed constant is rejected"
    (base (ArrAdd (atom "$i0", integer 1)))
    (base (ArrAdd (scalar "$i0", integer 2)));
  rejects "a changed function name is rejected"
    (base (ArrCall (chars "f", [atom "$i0"])))
    (base (ArrCall (chars "g", [scalar "$i0"])));
  rejects "a changed call argument order is rejected"
    (base (ArrCall (chars "f", [atom "$i0"; atom "N"])))
    (base (ArrCall (chars "f", [scalar "N"; scalar "$i0"])));
  rejects "swapped conditional branches are rejected"
    (base (ArrCond (atom "N", atom "$i0", integer 1)))
    (base (ArrCond (scalar "N", integer 1, scalar "$i0")));
  rejects "a changed read index is rejected"
    (base (ArrAccessAtom (array "B" (AfVar (chars "$i0")))))
    (base (ArrAccessAtom (array "B" (AfAdd (AfVar (chars "$i0"), AfInt (z 1))))));
  rejects "a changed write destination is rejected"
    (base (atom "$i0"))
    (with_body fixture (ArrAssign (array "B" (AfVar (chars "$i0")), scalar "$i0")));
  rejects "a changed write index is rejected"
    (base (atom "$i0"))
    (with_body fixture (ArrAssign (array "A" (AfInt (z 0)), scalar "$i0")));
  rejects "dropping the assignment is rejected"
    (base (atom "$i0")) (with_body fixture ArrSkip)

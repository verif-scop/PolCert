let z = Camlcoq.Z.of_sint
let loc = { OpenScopAST.lineno = 1; filename = "openscop-parser-test"; byteno = 0 }
let checks = ref 0
let failures = ref 0

let check name expected f =
  incr checks;
  let result =
    try if f () then "accepted" else "rejected" with
    | Exceptions.TypecheckError | Exceptions.CompilationError -> "rejected"
    | exn -> "unexpected exception: " ^ Printexc.to_string exn
  in
  if result = expected then
    Printf.printf "[openscop-parser] PASS %s %s\n%!" name result
  else begin
    incr failures;
    Printf.eprintf "[openscop-parser] FAIL %s expected=%s actual=%s\n%!"
      name expected result
  end

let relation ty meta rows = {
  OpenScopAST.rel_type_loc = (ty, loc);
  meta_loc = (List.map z meta, loc);
  constrs_loc = (List.map (List.map z) rows, loc);
}

let check_relation name expected ty meta rows =
  check name expected (fun () ->
    OpenScopAST2OpenScop.type_check_relation (relation ty meta rows); true)

let kinds = ["context", OpenScop.CtxtTy; "domain", OpenScop.DomTy;
  "scattering", OpenScop.ScttTy; "read", OpenScop.ReadTy;
  "write", OpenScop.WriteTy; "maywrite", OpenScop.MayWriteTy]

let fixture flag access_ty = Printf.sprintf
  "<OpenScop>\n\nC\n\nCONTEXT\n0 2 0 0 0 0\n\n0\n\n1\n\n3\n\nDOMAIN\n1 3 1 0 0 0\n%d 1 0\n\nSCATTERING\n1 4 1 1 0 0\n0 -1 1 0\n\n%s\n1 4 1 1 0 0\n0 -1 0 1\n\n0\n\n</OpenScop>\n" flag access_ty

let with_fixture text f =
  let path = Filename.temp_file "polcert-openscop-parser-" ".scop" in
  Fun.protect ~finally:(fun () -> Sys.remove path) (fun () ->
    let ch = open_out path in
    Fun.protect ~finally:(fun () -> close_out ch) (fun () -> output_string ch text);
    f path)

let () =
  List.iter (fun (name, ty) ->
    let cols, outs, payload = if ty = OpenScop.CtxtTy
      then 2, 0, [0] else 3, 1, [1;0] in
    let meta = [1;cols;outs;0;0;0] in
    List.iter (fun flag ->
      check_relation (Printf.sprintf "%s-flag-%d" name flag)
        (if flag = 0 || flag = 1 then "accepted" else "rejected")
        ty meta [flag :: payload]) [0;1;2;-1];
    check_relation (name ^ "-empty-relation") "accepted" ty
      [0;cols;outs;0;0;0] [];
    check_relation (name ^ "-empty-row") "rejected" ty meta [[]];
    check_relation (name ^ "-row-count") "rejected" ty
      [2;cols;outs;0;0;0] [1 :: payload];
    check_relation (name ^ "-column-count") "rejected" ty
      [1;cols+1;outs;0;0;0] [1 :: payload];
    check_relation (name ^ "-inconsistent-dimensions") "rejected" ty
      [1;cols;outs;0;1;0] [1 :: payload];
    check_relation (name ^ "-negative-meta") "rejected" ty
      [-1;cols;outs;0;0;0] [1 :: payload];
    check_relation (name ^ "-short-meta") "rejected" ty [1;cols] [1 :: payload];
    check_relation (name ^ "-empty-meta") "rejected" ty [] [1 :: payload]
  ) kinds;
  List.iter (fun (name, flag, access_ty, expected) ->
    check name expected (fun () ->
      with_fixture (fixture flag access_ty) (fun path ->
        match OpenScopReader.read path with
        | None -> false
        | Some scop ->
            let domain = (List.hd scop.OpenScop.statements).OpenScop.domain in
            fst (List.hd domain.OpenScop.constrs) = (flag = 1))))
    ["reader-equality",0,"WRITE","accepted";
     "reader-inequality",1,"WRITE","accepted";
     "reader-invalid-flag",2,"WRITE","rejected";
     "reader-valid-maywrite",1,"MAYWRITE","accepted"];
  check "huge-row-count" "rejected" (fun () ->
    let rel = relation OpenScop.DomTy [0;3;1;0;0;0] [] in
    let huge = Camlcoq.Z.add (z max_int) (z 1) in
    let rel = { rel with OpenScopAST.meta_loc = ([huge;z 3;z 1;z 0;z 0;z 0], loc) } in
    OpenScopAST2OpenScop.type_check_relation rel; true);
  Printf.printf "[openscop-parser] %d/%d passed\n%!" (!checks - !failures) !checks;
  if !failures <> 0 then exit 1

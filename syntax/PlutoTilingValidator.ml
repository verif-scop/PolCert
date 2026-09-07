open OpenScop

exception ValidationError of string

type affine_expr = {
  var_coeffs : (string * Camlcoq.Z.t) list;
  param_coeffs : (string * Camlcoq.Z.t) list;
  const : Camlcoq.Z.t;
}

type tile_link = {
  parent : string;
  expr : affine_expr;
  tile_size : Camlcoq.Z.t;
}

type statement_witness = {
  statement : int;
  original_iterators : string list;
  tiled_iterators : string list;
  added_iterators : string list;
  links : tile_link list;
}

type witness = {
  before_path : string;
  after_path : string;
  params : string list;
  statements : statement_witness list;
}

type statement_report = {
  statement : int;
  original_iterators : string list;
  tiled_iterators : string list;
  added_iterators : string list;
  links : tile_link list;
  witness_ok : bool;
  transformation_contract_ok : bool;
  base_domain_ok : bool;
  link_rows_ok : bool;
  access_ok : bool;
  compiled_relation_ok : bool;
  schedule_sanity_ok : bool;
  notes : string list;
}

type report = {
  before_path : string;
  after_path : string;
  params : string list;
  ok : bool;
  statements : statement_report list;
  limitations : string list;
}

type tiling_mode =
  | Ordinary
  | SecondLevel

type 'scop phase_artifact = {
  artifact_witness : witness;
  artifact_after_scop : 'scop;
}

type tile_row_kind =
  | LowerBound
  | UpperBound

type link_candidate = {
  candidate_parent : string;
  candidate_expr : affine_expr;
  candidate_tile_size : Camlcoq.Z.t;
}

type inferred_statement_shape = {
  inferred_before_vars : string list;
  inferred_after_vars : string list;
  inferred_added_iterators : string list;
  inferred_base_ok : bool;
  inferred_links_ok : bool;
  inferred_links : tile_link list;
  inferred_notes : string list;
}

let chars_to_string = Camlcoq.camlstring_of_coqstring

let z_to_string = Camlcoq.Z.to_string

let nat_to_int = Camlcoq.Nat.to_int

let z_eq = Camlcoq.Z.eq

let z_abs z =
  if Camlcoq.Z.lt z Camlcoq.Z.zero then Camlcoq.Z.neg z else z

let failf fmt = Printf.ksprintf (fun s -> raise (ValidationError s)) fmt

let rec take n xs =
  if n <= 0 then []
  else match xs with
  | [] -> []
  | x :: tl -> x :: take (n - 1) tl

let rec drop n xs =
  if n <= 0 then xs
  else match xs with
  | [] -> []
  | _ :: tl -> drop (n - 1) tl

let split_at n xs =
  (take n xs, drop n xs)

let rec last = function
  | [] -> None
  | [x] -> Some x
  | _ :: tl -> last tl

let sort_uniq xs =
  List.sort_uniq String.compare xs

let string_to_chars = Camlcoq.coqstring_of_camlstring

let rec remove_first pred = function
  | [] -> []
  | x :: xs -> if pred x then xs else x :: remove_first pred xs

let rec range_from start len =
  if len <= 0 then []
  else start :: range_from (start + 1) (len - 1)

let relation_param_names scop =
  match scop.context.params with
  | None -> []
  | Some params -> List.map chars_to_string params

let stmt_iterators_and_body stmt =
  match stmt.stmt_exts_opt with
  | None -> None
  | Some exts ->
      let rec go = function
        | [] -> None
        | StmtBody (iters, body) :: _ ->
            Some (List.map chars_to_string iters, body)
      in
      go exts

let stmt_iterators stmt =
  match stmt_iterators_and_body stmt with
  | Some (iters, _) -> iters
  | None -> []

let stmt_body stmt =
  match stmt_iterators_and_body stmt with
  | Some (_, body) -> Some body
  | None -> None

let affine_expr_dependencies expr =
  expr.var_coeffs
  |> List.filter_map (fun (name, coeff) ->
         if z_eq coeff Camlcoq.Z.zero then None else Some name)
  |> sort_uniq

let render_term name coeff =
  if z_eq coeff Camlcoq.Z.one then name
  else if z_eq coeff Camlcoq.Z.mone then "-" ^ name
  else z_to_string coeff ^ "*" ^ name

let render_affine_expr expr =
  let parts =
    (List.map (fun (name, coeff) -> render_term name coeff) expr.var_coeffs)
    @ (List.map (fun (name, coeff) -> render_term name coeff) expr.param_coeffs)
    @ (if z_eq expr.const Camlcoq.Z.zero then [] else [z_to_string expr.const])
  in
  match parts with
  | [] -> "0"
  | hd :: tl ->
      List.fold_left
        (fun acc item ->
          if String.length item > 0 && item.[0] = '-' then
            acc ^ " - " ^ String.sub item 1 (String.length item - 1)
          else
            acc ^ " + " ^ item)
        hd tl

let eq_row_compare (lhs : bool * Camlcoq.Z.t list) (rhs : bool * Camlcoq.Z.t list) =
  Stdlib.compare lhs rhs

let normalize_rows rows =
  List.sort eq_row_compare rows

let relation_rows relation = relation.constrs

let relation_input_count relation = nat_to_int relation.meta.in_dim_nb

let relation_output_count relation = nat_to_int relation.meta.out_dim_nb

let relation_param_count relation = nat_to_int relation.meta.param_nb

let ensure_stmt_iterators statement_index stmt =
  let iters = stmt_iterators stmt in
  if iters = [] && relation_input_count stmt.domain <> 0 then
    failf "statement %d: missing iterator names in statement extensions" statement_index;
  iters

(* The exporter represents an iterator expression as [ArrAtom (AVar name)],
   while the text reader parses every bare identifier as a zero-index access.
   Normalize this syntactic distinction without changing names or operations. *)
let rec normalize_body_expr = function
  | ArrAtom (AVar name) -> ArrAccessAtom (ArrAccess (name, []))
  | ArrAtom _ as expr -> expr
  | ArrAccessAtom _ as expr -> expr
  | ArrAdd (a, b) -> ArrAdd (normalize_body_expr a, normalize_body_expr b)
  | ArrMinus (a, b) -> ArrMinus (normalize_body_expr a, normalize_body_expr b)
  | ArrMulti (a, b) -> ArrMulti (normalize_body_expr a, normalize_body_expr b)
  | ArrDiv (a, b) -> ArrDiv (normalize_body_expr a, normalize_body_expr b)
  | ArrLt (a, b) -> ArrLt (normalize_body_expr a, normalize_body_expr b)
  | ArrLe (a, b) -> ArrLe (normalize_body_expr a, normalize_body_expr b)
  | ArrEq (a, b) -> ArrEq (normalize_body_expr a, normalize_body_expr b)
  | ArrAnd (a, b) -> ArrAnd (normalize_body_expr a, normalize_body_expr b)
  | ArrCond (c, a, b) ->
      ArrCond (normalize_body_expr c, normalize_body_expr a, normalize_body_expr b)
  | ArrCall (name, args) -> ArrCall (name, List.map normalize_body_expr args)

let normalize_stmt_body = function
  | ArrAssign (lhs, rhs) -> ArrAssign (lhs, normalize_body_expr rhs)
  | ArrSkip -> ArrSkip

let require_same_shape before_scop after_scop =
  let before_params = relation_param_names before_scop in
  let after_params = relation_param_names after_scop in
  if before_params <> after_params then
    failf "parameter mismatch: before=%s after=%s"
      (String.concat "," before_params) (String.concat "," after_params);
  let before_stmts = before_scop.statements in
  let after_stmts = after_scop.statements in
  if List.length before_stmts <> List.length after_stmts then
    failf "statement count mismatch: before=%d after=%d"
      (List.length before_stmts) (List.length after_stmts);
  List.iteri
    (fun idx (before_stmt, after_stmt) ->
      match (stmt_body before_stmt, stmt_body after_stmt) with
      | Some body1, Some body2
        when normalize_stmt_body body1 <> normalize_stmt_body body2 ->
          failf "statement %d: statement body changed across tiling" (idx + 1)
      | _ -> ())
    (List.combine before_stmts after_stmts)

let delete_domain_added_coeffs added_count param_count (is_ineq, coeffs) =
  let _, rest = split_at added_count coeffs in
  let remaining_vars_count = List.length coeffs - added_count - param_count - 1 in
  let kept_vars, rest = split_at remaining_vars_count rest in
  let params, rest = split_at param_count rest in
  match last rest with
  | None -> failf "malformed domain row"
  | Some const -> (is_ineq, kept_vars @ params @ [const])

let delete_access_added_coeffs output_dims input_dims_after added_count param_dims (is_ineq, coeffs) =
  let outs, rest = split_at output_dims coeffs in
  let inputs, rest = split_at input_dims_after rest in
  let params, rest = split_at param_dims rest in
  let added_inputs, kept_inputs = split_at added_count inputs in
  match last rest with
  | None -> failf "malformed access row"
  | Some const -> ((is_ineq, outs @ kept_inputs @ params @ [const]), added_inputs)

let make_affine_expr coeffs var_names param_coeffs param_names const =
  let var_coeffs =
    List.filter_map
      (fun (name, coeff) ->
        if z_eq coeff Camlcoq.Z.zero then None else Some (name, coeff))
      (List.combine var_names coeffs)
  in
  let param_coeffs =
    List.filter_map
      (fun (name, coeff) ->
        if z_eq coeff Camlcoq.Z.zero then None else Some (name, coeff))
      (List.combine param_names param_coeffs)
  in
  { var_coeffs; param_coeffs; const }

let negate_zs = List.map Camlcoq.Z.neg

let classify_tile_link_row coeffs var_names added_count param_names =
  let coeff_count = List.length coeffs in
  let expected = List.length var_names + List.length param_names + 1 in
  if coeff_count <> expected then None
  else
    let var_coeffs, rest = split_at (List.length var_names) coeffs in
    let param_coeffs, rest = split_at (List.length param_names) rest in
    match last rest with
    | None -> None
    | Some const ->
        let parent_positions =
          var_coeffs
          |> List.mapi (fun idx coeff -> (idx, coeff))
          |> List.filter_map (fun (idx, coeff) ->
                 if idx < added_count &&
                    (Camlcoq.Z.ge coeff (Camlcoq.Z.of_sint 2) ||
                     Camlcoq.Z.le coeff (Camlcoq.Z.of_sint (-2)))
                 then Some idx
                 else None)
        in
        begin match parent_positions with
        | [parent_idx] ->
            let parent_name = List.nth var_names parent_idx in
            let parent_coeff = List.nth var_coeffs parent_idx in
            let tile_size = z_abs parent_coeff in
            let residual_coeffs =
              List.mapi
                (fun idx coeff -> if idx = parent_idx then Camlcoq.Z.zero else coeff)
                var_coeffs
            in
            if Camlcoq.Z.lt parent_coeff Camlcoq.Z.zero then
              let expr = make_affine_expr residual_coeffs var_names param_coeffs param_names const in
              Some ({ candidate_parent = parent_name; candidate_expr = expr; candidate_tile_size = tile_size }, LowerBound)
            else
              let expr =
                make_affine_expr
                  (negate_zs residual_coeffs)
                  var_names
                  (negate_zs param_coeffs)
                  param_names
                  (Camlcoq.Z.sub (Camlcoq.Z.sub tile_size Camlcoq.Z.one) const)
              in
              Some ({ candidate_parent = parent_name; candidate_expr = expr; candidate_tile_size = tile_size }, UpperBound)
        | _ -> None
        end

let coeff_key pairs =
  String.concat ","
    (List.map (fun (name, coeff) -> name ^ ":" ^ z_to_string coeff) pairs)

let link_candidate_key candidate =
  String.concat "|"
    [
      candidate.candidate_parent;
      z_to_string candidate.candidate_tile_size;
      coeff_key candidate.candidate_expr.var_coeffs;
      coeff_key candidate.candidate_expr.param_coeffs;
      z_to_string candidate.candidate_expr.const;
    ]

let candidate_to_link candidate =
  {
    parent = candidate.candidate_parent;
    expr = candidate.candidate_expr;
    tile_size = candidate.candidate_tile_size;
  }

let tile_link_key link =
  link_candidate_key
    {
      candidate_parent = link.parent;
      candidate_expr = link.expr;
      candidate_tile_size = link.tile_size;
    }

let sort_links links =
  List.sort (fun lhs rhs -> String.compare (tile_link_key lhs) (tile_link_key rhs)) links

let canonicalize_links original_iterators added_iterators links =
  let rec loop available pending acc =
    match pending with
    | [] ->
        let ordered = List.rev acc in
        let parents = sort_uniq (List.map (fun link -> link.parent) ordered) in
        let expected = sort_uniq added_iterators in
        if parents <> expected then
          failf
            "ordered tile-link parents [%s] do not cover added iterators [%s]"
            (String.concat "," parents)
            (String.concat "," expected);
        ordered
    | _ ->
        let ready, _blocked =
          List.partition
            (fun link ->
              List.for_all
                (fun dep -> List.mem dep available)
                (affine_expr_dependencies link.expr))
            pending
        in
        if ready = [] then
          let unresolved =
            String.concat ", "
              (List.map
                 (fun link ->
                   Printf.sprintf "%s/%s"
                     link.parent
                     (z_to_string link.tile_size))
                 (sort_links pending))
          in
          failf "cannot topologically order tile links: %s" unresolved
        else
          let chosen = List.hd (sort_links ready) in
          let pending' =
            remove_first
              (fun link -> tile_link_key link = tile_link_key chosen)
              pending
          in
          loop (available @ [chosen.parent]) pending' (chosen :: acc)
  in
  loop original_iterators links []

let permutation_from_raw_to_canonical raw_added canonical_added =
  if List.length raw_added <> List.length canonical_added then
    failf
      "raw added iterators [%s] and canonical added iterators [%s] have different lengths"
      (String.concat "," raw_added)
      (String.concat "," canonical_added);
  let indexed_raw = List.mapi (fun idx name -> (name, idx)) raw_added in
  let perm =
    List.map
      (fun name ->
        match List.assoc_opt name indexed_raw with
        | Some idx -> idx
        | None ->
            failf
              "canonical added iterator %s does not occur in raw added iterators [%s]"
              name
              (String.concat "," raw_added))
      canonical_added
  in
  let expected = range_from 0 (List.length raw_added) in
  if List.sort Stdlib.compare perm <> expected then
    failf
      "raw/canonical added-iterator permutation is not a bijection: raw=[%s] canonical=[%s]"
      (String.concat "," raw_added)
      (String.concat "," canonical_added);
  perm

let permute_prefix permutation prefix =
  if List.length prefix <> List.length permutation then
    failf "cannot permute prefix of length %d with permutation of length %d"
      (List.length prefix)
      (List.length permutation);
  List.map
    (fun idx ->
      try List.nth prefix idx
      with Failure _ ->
        failf "permutation index %d is out of bounds for prefix length %d"
          idx
          (List.length prefix))
    permutation

let permute_added_prefix permutation added_count xs =
  let raw_added, suffix = split_at added_count xs in
  permute_prefix permutation raw_added @ suffix

let rewrite_relation_added_inputs relation added_count permutation =
  let output_dims = relation_output_count relation in
  let input_dims = relation_input_count relation in
  let param_dims = relation_param_count relation in
  let rewrite_row (is_ineq, coeffs) =
    let outs, rest = split_at output_dims coeffs in
    let inputs, rest = split_at input_dims rest in
    let params, rest = split_at param_dims rest in
    match last rest with
    | None -> failf "malformed relation row during second-level canonicalization"
    | Some const ->
        begin
          match relation.rel_type with
          | DomTy ->
              if output_dims < added_count then
                failf
                  "cannot rewrite domain relation with %d output dims using %d added iterators"
                  output_dims
                  added_count;
              let added_outputs, kept_outputs = split_at added_count outs in
              (is_ineq, permute_prefix permutation added_outputs @ kept_outputs @ inputs @ params @ [const])
          | _ ->
              if input_dims < added_count then
                failf
                  "cannot rewrite relation with %d input dims using %d added iterators"
                  input_dims
                  added_count;
              let added_inputs, kept_inputs = split_at added_count inputs in
              (is_ineq, outs @ permute_prefix permutation added_inputs @ kept_inputs @ params @ [const])
        end
  in
  { relation with constrs = List.map rewrite_row relation.constrs }

let rewrite_stmt_exts_added_iterators added_count permutation = function
  | None -> None
  | Some exts ->
      let rewrite_ext = function
        | StmtBody (iters, body) ->
            let names = List.map chars_to_string iters in
            let names' = permute_added_prefix permutation added_count names in
            StmtBody (List.map string_to_chars names', body)
      in
      Some (List.map rewrite_ext exts)

let rewrite_after_statement_added_iterators
    (after_stmt : OpenScop.coq_Statement)
    raw_added
    canonical_added =
  let added_count = List.length raw_added in
  if List.length canonical_added <> added_count then
    failf
      "raw added iterators [%s] and canonical added iterators [%s] have different lengths"
      (String.concat "," raw_added)
      (String.concat "," canonical_added);
  let permutation = permutation_from_raw_to_canonical raw_added canonical_added in
  { after_stmt with
    domain = rewrite_relation_added_inputs after_stmt.domain added_count permutation;
    scattering = rewrite_relation_added_inputs after_stmt.scattering added_count permutation;
    access =
      List.map
        (fun rel -> rewrite_relation_added_inputs rel added_count permutation)
        after_stmt.access;
    stmt_exts_opt =
      rewrite_stmt_exts_added_iterators added_count permutation after_stmt.stmt_exts_opt; }

let canonicalize_statement_witness (stmt : statement_witness) =
  let canonical_links =
    canonicalize_links stmt.original_iterators stmt.added_iterators stmt.links
  in
  let canonical_added = List.map (fun link -> link.parent) canonical_links in
  let canonical_tiled = canonical_added @ stmt.original_iterators in
  ({ stmt with
     tiled_iterators = canonical_tiled;
     added_iterators = canonical_added;
     links = canonical_links; },
   canonical_added)

let canonicalize_witness_and_after_scop
    (after_scop : OpenScop.coq_OpenScop)
    (witness : witness) =
  if List.length after_scop.statements <> List.length witness.statements then
    failf
      "statement count mismatch while canonicalizing second-level witness: after=%d witness=%d"
      (List.length after_scop.statements)
      (List.length witness.statements);
  let statements, after_statements =
    List.split
      (List.map2
         (fun stmt after_stmt ->
           let canonical_stmt, canonical_added =
             canonicalize_statement_witness stmt
           in
           let after_stmt' =
             rewrite_after_statement_added_iterators
               after_stmt
               stmt.added_iterators
               canonical_added
           in
           (canonical_stmt, after_stmt'))
         witness.statements
         after_scop.statements)
  in
  ({ witness with statements }, { after_scop with statements = after_statements })

let reject_second_level_links (witness : witness) =
  List.iter
    (fun (stmt : statement_witness) ->
      List.iter
        (fun link ->
          let dependent_added =
            List.filter
              (fun dep -> List.mem dep stmt.added_iterators)
              (affine_expr_dependencies link.expr)
          in
          if dependent_added <> [] then
            failf
              "statement %d: second-level tiling requires --second-level-tile (link %s depends on added iterators [%s])"
              stmt.statement
              link.parent
              (String.concat ", " dependent_added))
        stmt.links)
    witness.statements

let infer_statement_shape param_names stmt_idx before_stmt after_stmt =
  let before_vars = ensure_stmt_iterators stmt_idx before_stmt in
  let after_vars = ensure_stmt_iterators stmt_idx after_stmt in
  if List.length after_vars < List.length before_vars then
    failf "statement %d: after has fewer iterators than before" stmt_idx;
  let added_count = List.length after_vars - List.length before_vars in
  let after_suffix = drop added_count after_vars in
  if after_suffix <> before_vars then
    failf
      "statement %d: expected tiled iterators to end with original iterators, got before=[%s] after=[%s]"
      stmt_idx
      (String.concat "," before_vars)
      (String.concat "," after_vars);
  let before_param_count = relation_param_count before_stmt.domain in
  let before_rows = normalize_rows (relation_rows before_stmt.domain) in
  let base_rows = ref [] in
  let link_rows = ref [] in
  List.iter
    (fun ((_, coeffs) as row) ->
      let added_coeffs = take added_count coeffs in
      if List.for_all (fun coeff -> z_eq coeff Camlcoq.Z.zero) added_coeffs then
        base_rows := delete_domain_added_coeffs added_count before_param_count row :: !base_rows
      else
        link_rows := row :: !link_rows)
    (relation_rows after_stmt.domain);
  let base_ok = before_rows = normalize_rows !base_rows in
  let notes = ref [] in
  if not base_ok then
    notes := Printf.sprintf "statement %d: lifted base-domain rows do not match before-domain rows" stmt_idx :: !notes;
  let candidates = Hashtbl.create 8 in
  let links_ok = ref true in
  List.iter
    (fun (is_ineq, coeffs) ->
      if not is_ineq then begin
        links_ok := false;
        notes := Printf.sprintf "statement %d: unsupported equality row in tiled domain" stmt_idx :: !notes
      end else
        match classify_tile_link_row coeffs after_vars added_count param_names with
        | None ->
            links_ok := false;
            notes := Printf.sprintf "statement %d: unsupported non-base tiled-domain row" stmt_idx :: !notes
        | Some (candidate, kind) ->
            let key = link_candidate_key candidate in
            let current =
              match Hashtbl.find_opt candidates key with
              | None -> []
              | Some kinds -> kinds
            in
            Hashtbl.replace candidates key (kind :: current))
    !link_rows;
  let candidate_table : (string, link_candidate) Hashtbl.t = Hashtbl.create 8 in
  List.iter
    (fun (is_ineq, coeffs) ->
      if is_ineq then
        match classify_tile_link_row coeffs after_vars added_count param_names with
        | Some (candidate, _) ->
            Hashtbl.replace candidate_table (link_candidate_key candidate) candidate
        | None -> ())
    !link_rows;
  let links =
    Hashtbl.fold
      (fun key kinds acc ->
        if List.mem LowerBound kinds && List.mem UpperBound kinds then
          match Hashtbl.find_opt candidate_table key with
          | Some candidate -> candidate_to_link candidate :: acc
          | None -> acc
        else begin
          links_ok := false;
          notes := Printf.sprintf "statement %d: incomplete tile-link pair for %s" stmt_idx key :: !notes;
          acc
        end)
      candidates []
    |> sort_links
  in
  List.iter
    (fun link ->
      if List.mem link.parent (affine_expr_dependencies link.expr) then begin
        links_ok := false;
        notes := Printf.sprintf "statement %d: tile parent %s occurs in its own affine expression" stmt_idx link.parent :: !notes
      end)
    links;
  let parent_set = sort_uniq (List.map (fun link -> link.parent) links) in
  let added_names = sort_uniq (take added_count after_vars) in
  if parent_set <> added_names then begin
    links_ok := false;
    notes :=
      Printf.sprintf "statement %d: tile parents [%s] do not cover all added iterators [%s]"
        stmt_idx
        (String.concat "," parent_set)
        (String.concat "," added_names)
      :: !notes
  end;
  {
    inferred_before_vars = before_vars;
    inferred_after_vars = after_vars;
    inferred_added_iterators = take added_count after_vars;
    inferred_base_ok = base_ok;
    inferred_links_ok = !links_ok;
    inferred_links = links;
    inferred_notes = List.rev !notes;
  }

let extract_statement_witness param_names stmt_idx before_stmt after_stmt =
  let inferred = infer_statement_shape param_names stmt_idx before_stmt after_stmt in
  if not inferred.inferred_base_ok || not inferred.inferred_links_ok then
    failf
      "statement %d: cannot extract tiling witness: %s"
      stmt_idx
      (String.concat "; " inferred.inferred_notes);
  {
    statement = stmt_idx;
    original_iterators = inferred.inferred_before_vars;
    tiled_iterators = inferred.inferred_after_vars;
    added_iterators = inferred.inferred_added_iterators;
    links = inferred.inferred_links;
  }

let extract_raw_witness_from_scops ~before_path ~after_path before_scop after_scop =
  require_same_shape before_scop after_scop;
  let params = relation_param_names before_scop in
  {
    before_path;
    after_path;
    params;
    statements =
      List.mapi
        (fun idx (before_stmt, after_stmt) ->
          extract_statement_witness params (idx + 1) before_stmt after_stmt)
        (List.combine before_scop.statements after_scop.statements);
  }

let extract_phase_artifact_from_scops
    ?(tiling_mode = Ordinary)
    ~before_path ~after_path before_scop after_scop =
  let raw_witness =
    extract_raw_witness_from_scops ~before_path ~after_path before_scop after_scop
  in
  match tiling_mode with
  | Ordinary ->
      reject_second_level_links raw_witness;
      { artifact_witness = raw_witness; artifact_after_scop = after_scop }
  | SecondLevel ->
      let witness, after_scop =
        canonicalize_witness_and_after_scop after_scop raw_witness
      in
      { artifact_witness = witness; artifact_after_scop = after_scop }

let extract_witness_from_scops
    ?(tiling_mode = Ordinary)
    ~before_path ~after_path before_scop after_scop =
  let artifact =
    extract_phase_artifact_from_scops
      ~tiling_mode
      ~before_path
      ~after_path
      before_scop
      after_scop
  in
  artifact.artifact_witness

let extract_phase_artifact_from_files
    ?(tiling_mode = Ordinary)
    before_path after_path =
  let before_scop =
    match OpenScopReader.read before_path with
    | Some scop -> scop
    | None -> failf "cannot read OpenScop file %s" before_path
  in
  let after_scop =
    match OpenScopReader.read after_path with
    | Some scop -> scop
    | None -> failf "cannot read OpenScop file %s" after_path
  in
  extract_phase_artifact_from_scops
    ~tiling_mode
    ~before_path
    ~after_path
    before_scop
    after_scop

let extract_witness_from_files
    ?(tiling_mode = Ordinary)
    before_path after_path =
  let artifact =
    extract_phase_artifact_from_files ~tiling_mode before_path after_path
  in
  artifact.artifact_witness

let coeff_of name coeffs =
  match List.assoc_opt name coeffs with
  | Some coeff -> coeff
  | None -> Camlcoq.Z.zero

let expected_link_rows tiled_iterators param_names link =
  let lower_var_coeffs =
    List.map
      (fun var ->
        let expr_coeff = coeff_of var link.expr.var_coeffs in
        if String.equal var link.parent then Camlcoq.Z.sub expr_coeff link.tile_size else expr_coeff)
      tiled_iterators
  in
  let upper_var_coeffs =
    List.map
      (fun var ->
        let expr_coeff = coeff_of var link.expr.var_coeffs in
        let base = Camlcoq.Z.neg expr_coeff in
        if String.equal var link.parent then Camlcoq.Z.add base link.tile_size else base)
      tiled_iterators
  in
  let lower_param_coeffs =
    List.map (fun param -> coeff_of param link.expr.param_coeffs) param_names
  in
  let upper_param_coeffs =
    List.map (fun param -> Camlcoq.Z.neg (coeff_of param link.expr.param_coeffs)) param_names
  in
  let lower =
    (true, lower_var_coeffs @ lower_param_coeffs @ [link.expr.const])
  in
  let upper =
    ( true,
      upper_var_coeffs @ upper_param_coeffs @
      [Camlcoq.Z.sub (Camlcoq.Z.sub link.tile_size Camlcoq.Z.one) link.expr.const] )
  in
  [lower; upper]

let check_witness_shape stmt_idx actual_before_vars actual_after_vars (witness_stmt : statement_witness) =
  let notes = ref [] in
  let ok = ref true in
  let actual_added_count = List.length actual_after_vars - List.length actual_before_vars in
  let actual_added_vars = if actual_added_count <= 0 then [] else take actual_added_count actual_after_vars in
  if witness_stmt.statement <> stmt_idx then begin
    ok := false;
    notes := Printf.sprintf "statement %d: witness statement id is %d" stmt_idx witness_stmt.statement :: !notes
  end;
  if witness_stmt.original_iterators <> actual_before_vars then begin
    ok := false;
    notes :=
      Printf.sprintf "statement %d: witness original iterators [%s] do not match actual [%s]"
        stmt_idx
        (String.concat "," witness_stmt.original_iterators)
        (String.concat "," actual_before_vars)
      :: !notes
  end;
  if witness_stmt.tiled_iterators <> actual_after_vars then begin
    ok := false;
    notes :=
      Printf.sprintf "statement %d: witness tiled iterators [%s] do not match actual [%s]"
        stmt_idx
        (String.concat "," witness_stmt.tiled_iterators)
        (String.concat "," actual_after_vars)
      :: !notes
  end;
  if witness_stmt.added_iterators <> actual_added_vars then begin
    ok := false;
    notes :=
      Printf.sprintf "statement %d: witness added iterators [%s] do not match actual [%s]"
        stmt_idx
        (String.concat "," witness_stmt.added_iterators)
        (String.concat "," actual_added_vars)
      :: !notes
  end;
  List.iter
    (fun link ->
      if List.mem link.parent (affine_expr_dependencies link.expr) then begin
        ok := false;
        notes := Printf.sprintf "statement %d: tile parent %s occurs in its own affine expression" stmt_idx link.parent :: !notes
      end)
    witness_stmt.links;
  let parent_set = sort_uniq (List.map (fun link -> link.parent) witness_stmt.links) in
  if parent_set <> sort_uniq actual_added_vars then begin
    ok := false;
    notes :=
      Printf.sprintf "statement %d: witness tile parents [%s] do not cover actual added iterators [%s]"
        stmt_idx
        (String.concat "," parent_set)
        (String.concat "," (sort_uniq actual_added_vars))
      :: !notes
  end;
  (!ok, List.rev !notes)

let check_transformation_contract stmt_idx original_iterators tiled_iterators added_iterators links =
  let notes = ref [] in
  let ok = ref true in
  if tiled_iterators <> added_iterators @ original_iterators then begin
    ok := false;
    notes :=
      Printf.sprintf
        "statement %d: tiled iterator order is not added_iterators ++ original_iterators"
        stmt_idx
      :: !notes
  end;
  let parents = List.map (fun link -> link.parent) links in
  if parents <> added_iterators then begin
    ok := false;
    notes :=
      Printf.sprintf
        "statement %d: ordered tile-link parents do not match added iterators"
        stmt_idx
      :: !notes
  end;
  let seen = ref original_iterators in
  List.iter
    (fun link ->
      if Camlcoq.Z.le link.tile_size Camlcoq.Z.zero then begin
        ok := false;
        notes :=
          Printf.sprintf
            "statement %d: tile size for %s is not positive"
            stmt_idx link.parent
          :: !notes
      end;
      let unknown =
        List.filter (fun dep -> not (List.mem dep !seen)) (affine_expr_dependencies link.expr)
      in
      if unknown <> [] then begin
        ok := false;
        notes :=
          Printf.sprintf
            "statement %d: tile link %s depends on unresolved iterators [%s]"
            stmt_idx link.parent (String.concat ", " unknown)
          :: !notes
      end;
      if List.mem link.parent !seen then begin
        ok := false;
        notes :=
          Printf.sprintf
            "statement %d: tile parent %s is not fresh in ordered links"
            stmt_idx link.parent
          :: !notes
      end;
      seen := !seen @ [ link.parent ])
    links;
  (!ok, List.rev !notes)

let check_domain_with_witness param_names stmt_idx before_stmt after_stmt (witness_stmt : statement_witness) =
  let actual_before_vars = ensure_stmt_iterators stmt_idx before_stmt in
  let actual_after_vars = ensure_stmt_iterators stmt_idx after_stmt in
  let witness_ok, witness_notes =
    check_witness_shape stmt_idx actual_before_vars actual_after_vars witness_stmt
  in
  let actual_added_count = List.length actual_after_vars - List.length actual_before_vars in
  let before_param_count = relation_param_count before_stmt.domain in
  let before_rows = normalize_rows (relation_rows before_stmt.domain) in
  let base_rows = ref [] in
  let extra_rows = ref [] in
  List.iter
    (fun ((_, coeffs) as row) ->
      let added_coeffs = if actual_added_count <= 0 then [] else take actual_added_count coeffs in
      if List.for_all (fun coeff -> z_eq coeff Camlcoq.Z.zero) added_coeffs then
        base_rows := delete_domain_added_coeffs actual_added_count before_param_count row :: !base_rows
      else
        extra_rows := row :: !extra_rows)
    (relation_rows after_stmt.domain);
  let base_domain_ok = before_rows = normalize_rows !base_rows in
  let notes = ref witness_notes in
  if not base_domain_ok then
    notes := !notes @ [Printf.sprintf "statement %d: lifted base-domain rows do not match before-domain rows" stmt_idx];
  let expected_link_rows =
    witness_stmt.links
    |> List.map (expected_link_rows actual_after_vars param_names)
    |> List.flatten
    |> normalize_rows
  in
  let actual_link_rows = normalize_rows !extra_rows in
  let link_rows_ok = actual_link_rows = expected_link_rows in
  if not link_rows_ok then
    notes := !notes @ [Printf.sprintf "statement %d: witness link rows do not match tiled-domain rows" stmt_idx];
  (witness_ok, base_domain_ok, link_rows_ok, !notes)

let check_accesses stmt_idx added_count before_stmt after_stmt =
  let notes = ref [] in
  let before_accs = before_stmt.access in
  let after_accs = after_stmt.access in
  if List.length before_accs <> List.length after_accs then
    ( false,
      [
        Printf.sprintf
          "statement %d: access count changed from %d to %d"
          stmt_idx (List.length before_accs) (List.length after_accs);
      ] )
  else begin
    let ok = ref true in
    List.iteri
      (fun idx (before_acc, after_acc) ->
        if before_acc.rel_type <> after_acc.rel_type then begin
          ok := false;
          notes :=
            Printf.sprintf "statement %d: access %d kind changed" stmt_idx (idx + 1) :: !notes
        end else begin
          let before_input_dims = relation_input_count before_acc in
          let after_input_dims = relation_input_count after_acc in
          if after_input_dims <> before_input_dims + added_count then begin
            ok := false;
            notes :=
              Printf.sprintf
                "statement %d: access %d expected %d input dims, got %d"
                stmt_idx (idx + 1) (before_input_dims + added_count) after_input_dims
              :: !notes
          end else begin
            let output_dims = relation_output_count after_acc in
            let param_dims = relation_param_count after_acc in
            let reduced_rows =
              List.map
                (fun row ->
                  delete_access_added_coeffs output_dims after_input_dims added_count param_dims row)
                after_acc.constrs
            in
            if List.exists
                 (fun (_, added_inputs) ->
                   List.exists (fun coeff -> not (z_eq coeff Camlcoq.Z.zero)) added_inputs)
                 reduced_rows
            then begin
              ok := false;
              notes :=
                Printf.sprintf
                  "statement %d: access %d uses added tile iterators directly"
                  stmt_idx (idx + 1)
                :: !notes
            end;
            let normalized_after =
              reduced_rows
              |> List.map fst
              |> normalize_rows
            in
            let normalized_before = normalize_rows before_acc.constrs in
            if normalized_after <> normalized_before then begin
              ok := false;
              notes :=
                Printf.sprintf
                  "statement %d: access %d rows changed after removing added tile iterators"
                  stmt_idx (idx + 1)
                :: !notes
            end
          end
        end)
      (List.combine before_accs after_accs);
    (!ok, List.rev !notes)
  end

let check_scattering_sanity stmt_idx added_count before_stmt after_stmt =
  let notes = ref [] in
  let before_scat = before_stmt.scattering in
  let after_scat = after_stmt.scattering in
  let before_input_dims = relation_input_count before_scat in
  let after_input_dims = relation_input_count after_scat in
  if after_input_dims <> before_input_dims + added_count then
    ( false,
      [
        Printf.sprintf
          "statement %d: scattering input dims %d do not match before+added (%d+%d)"
          stmt_idx after_input_dims before_input_dims added_count;
      ] )
  else
    let after_output_dims = relation_output_count after_scat in
    let before_output_dims = relation_output_count before_scat in
    let ok = ref true in
    if after_output_dims < after_input_dims then begin
      ok := false;
      notes :=
        Printf.sprintf
          "statement %d: scattering output dims %d are fewer than input dims %d"
          stmt_idx after_output_dims after_input_dims
        :: !notes
    end;
    if List.exists (fun (is_ineq, _) -> is_ineq) after_scat.constrs then begin
      ok := false;
      notes := Printf.sprintf "statement %d: scattering contains non-equality rows" stmt_idx :: !notes
    end;
    if after_output_dims < before_output_dims then
      notes :=
        Printf.sprintf
          "statement %d: after scattering compresses source-style separator dimensions (%d -> %d)"
          stmt_idx before_output_dims after_output_dims
        :: !notes;
    (!ok, List.rev !notes)

let check_statement_with_witness param_names stmt_idx before_stmt after_stmt (witness_stmt : statement_witness) =
  let actual_before_vars = ensure_stmt_iterators stmt_idx before_stmt in
  let actual_after_vars = ensure_stmt_iterators stmt_idx after_stmt in
  let actual_added_count = List.length actual_after_vars - List.length actual_before_vars in
  let actual_added_vars =
    if actual_added_count <= 0 then [] else take actual_added_count actual_after_vars
  in
  let witness_ok, base_domain_ok, link_rows_ok, domain_notes =
    check_domain_with_witness param_names stmt_idx before_stmt after_stmt witness_stmt
  in
  let transformation_contract_ok, transformation_notes =
    check_transformation_contract
      stmt_idx
      actual_before_vars
      actual_after_vars
      actual_added_vars
      witness_stmt.links
  in
  let access_ok, access_notes =
    check_accesses stmt_idx actual_added_count before_stmt after_stmt
  in
  let schedule_sanity_ok, schedule_notes =
    check_scattering_sanity stmt_idx actual_added_count before_stmt after_stmt
  in
  let compiled_relation_ok =
    witness_ok &&
    transformation_contract_ok &&
    base_domain_ok &&
    link_rows_ok &&
    access_ok
  in
  {
    statement = stmt_idx;
    original_iterators = actual_before_vars;
    tiled_iterators = actual_after_vars;
    added_iterators = actual_added_vars;
    links = witness_stmt.links;
    witness_ok;
    transformation_contract_ok;
    base_domain_ok;
    link_rows_ok;
    access_ok;
    compiled_relation_ok;
    schedule_sanity_ok;
    notes = domain_notes @ transformation_notes @ access_notes @ schedule_notes;
  }

let check_witness_against_scops ~before_path ~after_path before_scop after_scop (witness : witness) =
  require_same_shape before_scop after_scop;
  let params = relation_param_names before_scop in
  if witness.params <> params then
    failf "witness parameter mismatch: witness=%s actual=%s"
      (String.concat "," witness.params)
      (String.concat "," params);
  if List.length witness.statements <> List.length before_scop.statements then
    failf "witness statement count mismatch: witness=%d actual=%d"
      (List.length witness.statements)
      (List.length before_scop.statements);
  let statements =
    List.map
      (fun ((idx, before_stmt), (after_stmt, witness_stmt)) ->
        check_statement_with_witness params idx before_stmt after_stmt witness_stmt)
      (List.combine
         (List.mapi (fun idx stmt -> (idx + 1, stmt)) before_scop.statements)
         (List.combine after_scop.statements witness.statements))
  in
  let ok =
    List.for_all
      (fun stmt ->
        stmt.compiled_relation_ok &&
        stmt.schedule_sanity_ok)
      statements
  in
  {
    before_path;
    after_path;
    params;
    ok;
    statements;
    limitations =
      [
        "prototype only targets Pluto-style affine floor-link tiling constraints";
        "schedule checking is only a structural sanity check, not a dependence proof";
        "bounded coverage, ISS, and parallel codegen are not checked here";
      ];
  }

let check_witness_files before_path after_path witness =
  let before_scop =
    match OpenScopReader.read before_path with
    | Some scop -> scop
    | None -> failf "cannot read OpenScop file %s" before_path
  in
  let after_scop =
    match OpenScopReader.read after_path with
    | Some scop -> scop
    | None -> failf "cannot read OpenScop file %s" after_path
  in
  check_witness_against_scops ~before_path ~after_path before_scop after_scop witness

let validate_scops
    ?(tiling_mode = Ordinary)
    ~before_path ~after_path before_scop after_scop =
  let artifact =
    extract_phase_artifact_from_scops
      ~tiling_mode
      ~before_path
      ~after_path
      before_scop
      after_scop
  in
  check_witness_against_scops
    ~before_path
    ~after_path
    before_scop
    artifact.artifact_after_scop
    artifact.artifact_witness

let validate_files
    ?(tiling_mode = Ordinary)
    before_path after_path =
  let artifact =
    extract_phase_artifact_from_files ~tiling_mode before_path after_path
  in
  let before_scop =
    match OpenScopReader.read before_path with
    | Some scop -> scop
    | None -> failf "cannot read OpenScop file %s" before_path
  in
  check_witness_against_scops
    ~before_path
    ~after_path
    before_scop
    artifact.artifact_after_scop
    artifact.artifact_witness

let render_link link =
  Printf.sprintf "%s = floor((%s) / %s)"
    link.parent
    (render_affine_expr link.expr)
    (z_to_string link.tile_size)

let render_witness (witness : witness) =
  let lines = ref [] in
  let push line = lines := line :: !lines in
  push ("before: " ^ witness.before_path);
  push ("after:  " ^ witness.after_path);
  if witness.params <> [] then
    push ("params: " ^ String.concat "," witness.params);
  List.iter
    (fun (stmt : statement_witness) ->
      push "";
      push (Printf.sprintf "statement %d:" stmt.statement);
      push ("  original iterators: " ^ String.concat " " stmt.original_iterators);
      push ("  tiled iterators:    " ^ String.concat " " stmt.tiled_iterators);
      if stmt.added_iterators <> [] then
        push ("  added iterators:    " ^ String.concat " " stmt.added_iterators);
      List.iter (fun link -> push ("  tile link: " ^ render_link link)) stmt.links)
    witness.statements;
  String.concat "\n" (List.rev !lines)

let render_report (report : report) =
  let lines = ref [] in
  let push line = lines := line :: !lines in
  push ("before: " ^ report.before_path);
  push ("after:  " ^ report.after_path);
  push ("overall: " ^ if report.ok then "PASS" else "FAIL");
  if report.params <> [] then
    push ("params: " ^ String.concat "," report.params);
  List.iter
    (fun (stmt : statement_report) ->
      push "";
      push
        (Printf.sprintf
           "statement %d: witness=%b transformation_contract=%b base_domain=%b links=%b access=%b compiled_relation=%b schedule_sanity=%b"
           stmt.statement
           stmt.witness_ok
           stmt.transformation_contract_ok
           stmt.base_domain_ok
           stmt.link_rows_ok
           stmt.access_ok
           stmt.compiled_relation_ok
           stmt.schedule_sanity_ok);
      push ("  original iterators: " ^ String.concat " " stmt.original_iterators);
      push ("  tiled iterators:    " ^ String.concat " " stmt.tiled_iterators);
      if stmt.added_iterators <> [] then
        push ("  added iterators:    " ^ String.concat " " stmt.added_iterators);
      List.iter (fun link -> push ("  tile link: " ^ render_link link)) stmt.links;
      List.iter (fun note -> push ("  note: " ^ note)) stmt.notes)
    report.statements;
  push "";
  push "limitations:";
  List.iter (fun item -> push ("  - " ^ item)) report.limitations;
  String.concat "\n" (List.rev !lines)

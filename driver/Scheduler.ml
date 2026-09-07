

(* let scheduler  *)
open Result
open Driveraux
(* open CPolIRs *)
open Camlcoq
open Filename
open Str  (* Required for regular expressions *)

type pluto_raw_loop_hint = {
  raw_hint_iterator : string;
  raw_hint_stmt_ids : int list;
  raw_hint_dim : int;
  raw_hint_directive : int;
}

type pluto_parallel_hint = {
  hint_iterator : string;
  hint_stmt_ids : int list;
  hint_raw_dim : int;
  hint_current_dim : int;
  hint_directive : int;
}

type tiling_mode =
  | OrdinaryTiling
  | SecondLevelTiling

type schedule_mode =
  | AffineSchedule
  | IdentitySchedule

type diamond_mode =
  | NoDiamondTiling
  | DiamondOneDimensionalStart
  | DiamondFullDimensionalStart

type intra_tile_mode =
  | DisableIntraTile
  | EnableIntraTile

type phase_pipeline_mode =
  | StagedPhases
  | SingleInvocationPhases

let current_tiling_mode = ref OrdinaryTiling
let current_schedule_mode = ref AffineSchedule
let current_diamond_mode = ref NoDiamondTiling
let current_intra_tile_mode = ref DisableIntraTile
let current_phase_pipeline_mode = ref StagedPhases
let current_pluto_extra_flags = ref []
let current_pluto_control_files = ref []
let current_checked_parallel_proposal = ref false

let with_checked_parallel_proposal action =
  let previous = !current_checked_parallel_proposal in
  current_checked_parallel_proposal := true;
  Fun.protect ~finally:(fun () -> current_checked_parallel_proposal := previous) action

let set_tiling_mode mode =
  current_tiling_mode := mode

let set_schedule_mode mode =
  current_schedule_mode := mode

let set_diamond_mode mode =
  current_diamond_mode := mode

let set_intra_tile_mode mode =
  current_intra_tile_mode := mode

let set_phase_pipeline_mode mode =
  current_phase_pipeline_mode := mode

let set_pluto_extra_flags flags =
  current_pluto_extra_flags := flags

let absolute_path path =
  if Filename.is_relative path then
    Filename.concat (Sys.getcwd ()) path
  else
    path

let set_pluto_control_files files =
  current_pluto_control_files :=
    List.map (fun (target, source) -> (target, absolute_path source)) files

let with_pluto_extra_flags flags =
  flags @ !current_pluto_extra_flags

let second_level_tiling_enabled () =
  !current_tiling_mode = SecondLevelTiling

let diamond_tiling_enabled () =
  !current_diamond_mode <> NoDiamondTiling

let full_dimensional_diamond_start_enabled () =
  !current_diamond_mode = DiamondFullDimensionalStart

let identity_schedule_enabled () =
  !current_schedule_mode = IdentitySchedule

let intra_tile_enabled () =
  !current_intra_tile_mode = EnableIntraTile

let post_tiling_affine_enabled () =
  diamond_tiling_enabled () || intra_tile_enabled ()

let intra_tile_flags () =
  match !current_intra_tile_mode with
  | DisableIntraTile -> ["--nointratileopt"]
  | EnableIntraTile -> ["--intratileopt"]

let identity_schedule_flags () =
  match !current_schedule_mode with
  | AffineSchedule -> []
  | IdentitySchedule -> ["--identity"]

let tmp_file_abs suff =
  absolute_path (tmp_file suff)

let copy_file src dst =
  let ic = open_in_bin src in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () ->
      let oc = open_out_bin dst in
      Fun.protect
        ~finally:(fun () -> close_out_noerr oc)
        (fun () ->
          let buf = Bytes.create 65536 in
          let rec loop () =
            let n = input ic buf 0 (Bytes.length buf) in
            if n > 0 then begin
              output oc buf 0 n;
              loop ()
            end
          in
          loop ()))

let with_pluto_control_workdir f =
  match !current_pluto_control_files with
  | [] -> f ()
  | files ->
      let installed = ref [] in
      Fun.protect
        ~finally:(fun () ->
          List.iter safe_remove !installed)
        (fun () ->
          List.iter
            (fun (target, source) ->
              if Sys.file_exists target then
                failwith
                  (Printf.sprintf
                     "explicit Pluto control file target %s already exists in the oracle working directory"
                     target);
              installed := target :: !installed;
              copy_file source target)
            files;
          f ())

let pluto_executable () =
  match Sys.getenv_opt "POLCERT_PLUTO" with
  | Some path when String.trim path <> "" -> path
  | _ ->
      let container_pluto = "/pluto/tool/pluto" in
      if Sys.file_exists container_pluto then
        container_pluto
      else
        "pluto"

let resolve_repo_file rel =
  let candidates =
    [ rel;
      Filename.concat (Sys.getcwd ()) rel;
      Filename.concat "/polcert" rel ]
  in
  match List.find_opt Sys.file_exists candidates with
  | Some path -> path
  | None -> failwith ("cannot locate repository file " ^ rel)

let read_file path =
  let ic = open_in path in
  let buf = Buffer.create 4096 in
  Fun.protect
    ~finally:(fun () -> close_in ic)
    (fun () ->
      (try
         while true do
           Buffer.add_string buf (input_line ic);
           Buffer.add_char buf '\n'
         done
       with End_of_file -> ());
      Buffer.contents buf)

(* These legacy Pluto inputs bypass the explicit PolOpt option surface.  In
   particular, skipdeps.txt can remove legality constraints before scheduling,
   while codegen.context can silently restrict the generated parameter domain. *)
let implicit_pluto_control_files =
  ["skipdeps.txt"; "codegen.context"; ".linearized"; ".nonlinearized"]

let implicit_pluto_control_file_error () =
  match List.find_opt Sys.file_exists implicit_pluto_control_files with
  | None -> None
  | Some path ->
      Some
        (coqstring_of_camlstring
           (Printf.sprintf
              "implicit Pluto control file %s is not supported by polopt; remove it or use a future explicit file option"
              path))

(** scop to scop *)

(** TODO: specify dump scop file name in pluto*)
let run_pluto_scop flags inscop =
  match implicit_pluto_control_file_error () with
  | Some msg -> Err msg
  | None ->
  let inscop_file = tmp_file_abs ".scop" in
  let outscop_file = inscop_file ^ ".afterscheduling.scop" in 
  OpenScopPrinter.openscop_printer inscop_file inscop;
  let cmd =
    List.concat
      [[pluto_executable (); "--dumpscop"; "--readscop"]; flags; [inscop_file]]
  in
  (* print_string ((String.concat " " cmd) ^ "\n"); *)
  let stdout = tmp_file_abs ".stdout" in
  let exc =
    with_pluto_control_workdir
      (fun () -> command ?stdout:(Some stdout) cmd)
  in
  let read_outscop () =
      if Sys.file_exists outscop_file then
      OpenScopReader.read outscop_file
    else
      None
  in
  match read_outscop () with
  | Some outscop -> Okk outscop
  | None ->
      if exc <> 0 then (
        safe_remove outscop_file;
        Err
          (coqstring_of_camlstring
             (Printf.sprintf "scheduler failed with exit code %d" exc))
      ) else
        Err (coqstring_of_camlstring ("scheduler failed"))

let text_has_line tag text =
  String.split_on_char '\n' text
  |> List.exists (fun line -> String.trim line = tag)

let run_pluto_scop_with_phase_dumps flags inscop =
  match implicit_pluto_control_file_error () with
  | Some msg -> Err msg
  | None ->
  let inscop_file = tmp_file_abs ".scop" in
  let midscop_file = inscop_file ^ ".midtransform.scop" in
  let posttile_file = inscop_file ^ ".posttile.scop" in
  let outscop_file = inscop_file ^ ".afterscheduling.scop" in
  OpenScopPrinter.openscop_printer inscop_file inscop;
  let cmd =
    List.concat
      [[pluto_executable (); "--dumpscop"; "--readscop"]; flags; [inscop_file]]
  in
  let stdout = tmp_file_abs ".stdout" in
  let exc =
    with_pluto_control_workdir
      (fun () -> command ?stdout:(Some stdout) cmd)
  in
  let read_scop path =
    if Sys.file_exists path then
      OpenScopReader.read path
    else
      None
  in
  match read_scop midscop_file, read_scop posttile_file, read_scop outscop_file with
  | Some midscop, Some posttile_scop, Some outscop ->
      Okk (midscop, posttile_scop, outscop)
  | _ ->
      if exc <> 0 then (
        safe_remove midscop_file;
        safe_remove posttile_file;
        safe_remove outscop_file;
        Err
          (coqstring_of_camlstring
             (Printf.sprintf "post-tiling affine scheduler failed with exit code %d" exc))
      ) else
        Err (coqstring_of_camlstring "post-tiling affine scheduler failed")

let trim_nonempty_lines lines =
  List.filter_map
    (fun line ->
      let line = String.trim line in
      if line = "" then None else Some line)
    lines

let payload_lines_between_tags begin_tag end_tag text =
  let rec seek = function
    | [] -> []
    | line :: rest ->
        if String.trim line = begin_tag then
          collect [] rest
        else
          seek rest
  and collect acc = function
    | [] -> List.rev acc
    | line :: rest ->
        if String.trim line = end_tag then
          List.rev acc
        else
          collect (line :: acc) rest
  in
  seek (String.split_on_char '\n' text)

let noncomment_payload_lines lines =
  trim_nonempty_lines lines
  |> List.filter (fun line -> line.[0] <> '#')

let split_ws s =
  List.filter (fun tok -> tok <> "")
    (Str.split (Str.regexp "[ \t\r]+") s)

let concat_map f xs =
  List.concat (List.map f xs)

let take n xs =
  let rec go k acc ys =
    if k <= 0 then List.rev acc
    else match ys with
      | [] -> List.rev acc
      | y :: ys' -> go (k - 1) (y :: acc) ys'
  in
  go n [] xs

let drop n xs =
  let rec go k ys =
    if k <= 0 then ys
    else match ys with
      | [] -> []
      | _ :: ys' -> go (k - 1) ys'
  in
  go n xs

let extract_loop_hints_from_outscop directive_mask outscop_file =
  try
    let text = read_file outscop_file in
    let scatnames =
      payload_lines_between_tags "<scatnames>" "</scatnames>" text
      |> noncomment_payload_lines
      |> concat_map split_ws
    in
    let loop_payload =
      payload_lines_between_tags "<loop>" "</loop>" text
      |> noncomment_payload_lines
    in
    let parse_loop_entries payload =
      match payload with
      | [] -> []
      | loop_count_s :: rest ->
          let loop_count = int_of_string loop_count_s in
          let rec parse count acc lines =
            if count <= 0 then List.rev acc
            else
              match lines with
              | iterator :: stmt_nb_s :: tail ->
                  let stmt_nb = int_of_string stmt_nb_s in
                  let stmt_ids = take stmt_nb tail in
                  if List.length stmt_ids <> stmt_nb then
                    raise (Failure "loop stmt id count mismatch");
                  begin
                    match drop stmt_nb tail with
                    | _private_vars :: directive_s :: rest' ->
                        let directive = int_of_string directive_s in
                        parse
                          (count - 1)
                          ((iterator, List.map int_of_string stmt_ids, directive) :: acc)
                          rest'
                    | _ ->
                        raise (Failure "truncated loop extension")
                  end
              | _ ->
                  raise (Failure "truncated loop extension")
          in
          parse loop_count [] rest
    in
    let loop_entries = parse_loop_entries loop_payload in
    let rec find_indices iterator i = function
      | [] -> []
      | name :: rest ->
          let tail = find_indices iterator (i + 1) rest in
          if String.equal name iterator then i :: tail else tail
    in
    let rec add_unique seen acc = function
      | [] -> List.rev acc
      | (iterator, stmt_ids, directive) :: rest ->
          if directive land directive_mask = 0 then
            add_unique seen acc rest
          else
            match find_indices iterator 0 scatnames with
            | [dim] ->
                let key = (iterator, stmt_ids, directive) in
                if List.mem key seen then
                  add_unique seen acc rest
                else
                  let hint =
                    {
                      raw_hint_iterator = iterator;
                      raw_hint_stmt_ids = stmt_ids;
                      raw_hint_dim = dim;
                      raw_hint_directive = directive;
                    }
                  in
                  add_unique (key :: seen) (hint :: acc) rest
            | _ -> add_unique seen acc rest
    in
    add_unique [] [] loop_entries
  with
  | Sys_error _
  | Failure _ -> []

let extract_parallel_hints_from_outscop outscop_file =
  extract_loop_hints_from_outscop 1 outscop_file

let extract_vector_hints_from_outscop outscop_file =
  extract_loop_hints_from_outscop 4 outscop_file

let extract_parallel_hint_from_outscop outscop_file =
  match extract_parallel_hints_from_outscop outscop_file with
  | [] -> None
  | hint :: _ -> Some hint

let extract_vector_hint_from_outscop outscop_file =
  match extract_vector_hints_from_outscop outscop_file with
  | [] -> None
  | hint :: _ -> Some hint

let map_parallel_hints_to_canonical_dims outscop hints =
  List.filter_map
    (fun hint ->
      match
        OpenScop.raw_to_canonical_schedule_dim
          outscop
          (Camlcoq.Nat.of_int hint.raw_hint_dim)
      with
      | Some dim ->
          let canonical_dim = Camlcoq.Nat.to_int dim in
          Some
            {
              hint_iterator = hint.raw_hint_iterator;
              hint_stmt_ids = hint.raw_hint_stmt_ids;
              hint_raw_dim = hint.raw_hint_dim;
              hint_current_dim = canonical_dim;
              hint_directive = hint.raw_hint_directive;
            }
      | None ->
          None)
    hints

let run_pluto_scop_with_loop_hint extractor map_hints flags inscop =
  match implicit_pluto_control_file_error () with
  | Some msg -> Err msg
  | None ->
  let inscop_file = tmp_file_abs ".scop" in
  let outscop_file = inscop_file ^ ".afterscheduling.scop" in
  let pluto_c_file = inscop_file ^ ".pluto.c" in
  OpenScopPrinter.openscop_printer inscop_file inscop;
  let cmd =
    List.concat
      [[pluto_executable (); "--dumpscop"; "--readscop"]; flags; [inscop_file]]
  in
  let stdout = tmp_file_abs ".stdout" in
  let exc =
    with_pluto_control_workdir
      (fun () -> command ?stdout:(Some stdout) cmd)
  in
  let read_outscop () =
    if Sys.file_exists outscop_file then
      OpenScopReader.read outscop_file
    else
      None
  in
  let hints = extractor outscop_file in
  match read_outscop () with
  | Some outscop ->
      Okk
        (outscop,
         map_hints outscop pluto_c_file hints)
  | None ->
      if exc <> 0 then (
        safe_remove outscop_file;
        Err
          (coqstring_of_camlstring
             (Printf.sprintf "scheduler failed with exit code %d" exc))
      ) else
        Err (coqstring_of_camlstring ("scheduler failed"))

let run_pluto_scop_with_parallel_hint flags inscop =
  run_pluto_scop_with_loop_hint
    extract_parallel_hints_from_outscop
    (fun outscop _ hints -> map_parallel_hints_to_canonical_dims outscop hints)
    flags
    inscop

let run_pluto_scop_with_vector_hint flags inscop =
  run_pluto_scop_with_loop_hint
    extract_vector_hints_from_outscop
    (fun outscop _ hints -> map_parallel_hints_to_canonical_dims outscop hints)
    flags
    inscop

let run_pluto_bridge flags inscop =
  match implicit_pluto_control_file_error () with
  | Some msg -> Err msg
  | None ->
  let inscop_file = tmp_file_abs ".scop" in
  let stdout_file = tmp_file_abs ".stdout" in
  OpenScopPrinter.openscop_printer inscop_file inscop;
  let cmd =
    List.concat
      [[pluto_executable (); "--readscop"]; flags; [inscop_file]]
  in
  let exc =
    with_pluto_control_workdir
      (fun () -> command ?stdout:(Some stdout_file) cmd)
  in
  let output = read_file stdout_file in
  if exc <> 0 then
    Err
      (coqstring_of_camlstring
         (Printf.sprintf "ISS debug dump export failed with exit code %d" exc))
  else if not (text_has_line "After ISS" output) then
    Okk output
  else
    try
      let bridge_tool = resolve_repo_file "tools/iss/pluto_iss_check.py" in
      let bridge_stdout = tmp_file_abs ".bridge.stdout" in
      let bridge_cmd =
        [ "python3";
          bridge_tool;
          "--emit-bridge-from-combined";
          stdout_file ]
      in
      let bridge_exc = command ?stdout:(Some bridge_stdout) bridge_cmd in
      let bridge_output = read_file bridge_stdout in
      if bridge_exc = 0 then
        Okk bridge_output
      else
        Err
          (coqstring_of_camlstring
             (Printf.sprintf
                "ISS bridge recovery from Pluto debug dump failed with exit code %d"
                bridge_exc))
    with Failure msg ->
      Err (coqstring_of_camlstring msg)

let affine_only_flags =
  [
    "--nointratileopt";
    "--nodiamond-tile";
    "--noprevector";
    "--smartfuse";
    "--nounrolljam";
    "--noparallel";
    "--notile";
  ]

let tile_only_flags () =
  [
    "--identity";
    "--tile";
    "--nodiamond-tile";
    "--noprevector";
    "--nounrolljam";
    "--noparallel";
  ] @ intra_tile_flags ()

let tile_only_second_level_flags () =
  tile_only_flags () @ ["--second-level-tile"]

let affine_with_iss_flags =
  ["--iss"] @ affine_only_flags

let affine_only_parallel_flags =
  [
    "--nointratileopt";
    "--nodiamond-tile";
    "--noprevector";
    "--smartfuse";
    "--nounrolljam";
    "--parallel";
    "--notile";
  ]

let affine_only_vector_flags =
  [
    "--nointratileopt";
    "--nodiamond-tile";
    "--prevector";
    "--smartfuse";
    "--nounrolljam";
    "--noparallel";
    "--notile";
  ]

let tile_only_parallel_flags () =
  [
    "--identity";
    "--tile";
    (* Parallel tile scheduling may add a wavefront.  The hinted consumer
       validates that actual schedule through the post-tiling affine pass.
       An explicit --innerpar request is forwarded with the extra flags. *)
    "--nodiamond-tile";
    "--noprevector";
    "--nounrolljam";
    "--parallel";
  ]
  (* Legacy consumers certify a separately generated pure-tile program.
     Only the actual-proposal consumer can accept a tile wavefront here. *)
  @ (if !current_checked_parallel_proposal then [] else ["--innerpar"])
  @ intra_tile_flags ()

let tile_only_vector_flags () =
  [
    "--identity";
    "--tile";
    "--nodiamond-tile";
    "--prevector";
    "--nounrolljam";
    "--noparallel";
  ] @ intra_tile_flags ()

let tile_only_parallel_second_level_flags () =
  tile_only_parallel_flags () @ ["--second-level-tile"]

let tile_only_vector_second_level_flags () =
  tile_only_vector_flags () @ ["--second-level-tile"]

let second_level_tiling_flags () =
  if second_level_tiling_enabled ()
  then ["--second-level-tile"]
  else []

let diamond_tiling_flags () =
  match !current_diamond_mode with
  | NoDiamondTiling -> ["--nodiamond-tile"]
  | DiamondOneDimensionalStart -> ["--diamond-tile"]
  | DiamondFullDimensionalStart ->
      ["--diamond-tile"; "--full-diamond-tile"]

let post_tiling_affine_flags () =
  identity_schedule_flags () @ [
    "--tile";
    "--noprevector";
    "--smartfuse";
    "--nounrolljam";
    "--noparallel";
  ]
  @ intra_tile_flags ()
  @
  diamond_tiling_flags ()
  @
  second_level_tiling_flags ()

let post_tiling_affine_parallel_flags () =
  identity_schedule_flags () @ [
    "--tile";
    "--noprevector";
    "--smartfuse";
    "--nounrolljam";
    "--parallel";
  ]
  @ intra_tile_flags ()
  @
  diamond_tiling_flags ()
  @
  second_level_tiling_flags ()

let post_tiling_affine_parallel_with_iss_flags () =
  "--iss" :: post_tiling_affine_parallel_flags ()

let post_tiling_affine_vector_flags () =
  identity_schedule_flags () @ [
    "--tile";
    "--prevector";
    "--smartfuse";
    "--nounrolljam";
    "--noparallel";
  ]
  @ intra_tile_flags ()
  @
  diamond_tiling_flags ()
  @
  second_level_tiling_flags ()

let post_tiling_affine_vector_with_iss_flags () =
  "--iss" :: post_tiling_affine_vector_flags ()

let post_tiling_affine_with_iss_flags () =
  "--iss" :: post_tiling_affine_flags ()

(* These aliases retain the names inspected by older tooling.  The recipe is
   shape-independent: it emits affine, post-tiling, and final schedule dumps
   for rectangular intratile optimization as well as diamond tiling. *)
let diamond_phase_flags = post_tiling_affine_flags

let diamond_phase_with_iss_flags = post_tiling_affine_with_iss_flags

let affine_with_iss_parallel_flags =
  ["--iss"] @ affine_only_parallel_flags

let affine_with_iss_vector_flags =
  ["--iss"] @ affine_only_vector_flags

let iss_identity_bridge_flags =
  [
    "--iss";
    "--identity";
    "--moredebug";
    "--silent";
  ]

let affine_candidate :
    (OpenScop.coq_OpenScop -> OpenScop.coq_OpenScop result) option ref = ref None

let with_affine_candidate candidate action =
  let previous = !affine_candidate in
  affine_candidate := Some candidate;
  Fun.protect ~finally:(fun () -> affine_candidate := previous) action

let affine_only_scop_scheduler inscop =
  match !affine_candidate with
  | Some candidate -> candidate inscop
  | None -> run_pluto_scop (with_pluto_extra_flags affine_only_flags) inscop

let tile_only_scop_scheduler inscop =
  let flags =
    if second_level_tiling_enabled ()
    then tile_only_second_level_flags ()
    else tile_only_flags ()
  in
  run_pluto_scop (with_pluto_extra_flags flags) inscop

let affine_only_scop_scheduler_with_parallel_hint inscop =
  run_pluto_scop_with_parallel_hint
    (with_pluto_extra_flags affine_only_parallel_flags)
    inscop

let affine_only_scop_scheduler_with_vector_hint inscop =
  run_pluto_scop_with_vector_hint
    (with_pluto_extra_flags affine_only_vector_flags)
    inscop

let tile_only_scop_scheduler_with_parallel_hint inscop =
  let flags =
    if second_level_tiling_enabled ()
    then tile_only_parallel_second_level_flags ()
    else tile_only_parallel_flags ()
  in
  run_pluto_scop_with_parallel_hint (with_pluto_extra_flags flags) inscop

let tile_only_scop_scheduler_with_vector_hint inscop =
  let flags =
    if second_level_tiling_enabled ()
    then tile_only_vector_second_level_flags ()
    else tile_only_vector_flags ()
  in
  run_pluto_scop_with_vector_hint (with_pluto_extra_flags flags) inscop

let affine_only_scop_scheduler_with_iss inscop =
  run_pluto_scop (with_pluto_extra_flags affine_with_iss_flags) inscop

let affine_only_scop_scheduler_with_iss_with_parallel_hint inscop =
  run_pluto_scop_with_parallel_hint
    (with_pluto_extra_flags affine_with_iss_parallel_flags)
    inscop

let affine_only_scop_scheduler_with_iss_with_vector_hint inscop =
  run_pluto_scop_with_vector_hint
    (with_pluto_extra_flags affine_with_iss_vector_flags)
    inscop

let iss_identity_bridge_from_scop inscop =
  run_pluto_bridge iss_identity_bridge_flags inscop

let normalize_phase_tiling_result midscop outscop =
  if second_level_tiling_enabled () then
    begin
      try
        let artifact =
          PlutoTilingValidator.extract_phase_artifact_from_scops
            ~tiling_mode:PlutoTilingValidator.SecondLevel
            ~before_path:"mid_affine"
            ~after_path:"after_tiled"
            midscop outscop
        in
        Okk (midscop, artifact.artifact_after_scop)
      with
      | PlutoTilingValidator.ValidationError msg ->
          Err (coqstring_of_camlstring msg)
      | exn -> Err (coqstring_of_camlstring (Printexc.to_string exn))
    end
  else Okk (midscop, outscop)

let run_pluto_phase_pipeline_staged inscop =
  match affine_only_scop_scheduler inscop with
  | Err msg -> Err msg
  | Okk midscop ->
      begin
        match tile_only_scop_scheduler midscop with
        | Err msg -> Err msg
        | Okk outscop -> normalize_phase_tiling_result midscop outscop
      end

let single_invocation_tiling_flags () =
  List.filter (fun flag -> flag <> "--notile") affine_only_flags
  @ ["--tile"] @ second_level_tiling_flags ()

(* Re-importing the affine midpoint can change Pluto's dependence decomposition
   and hence its selected band.  For a plain sequential tiling request, retain
   the two actual phases from the same invocation.  Their existing verified
   consumer still validates affine scheduling and tiling separately. *)
let run_pluto_phase_pipeline inscop =
  match !current_phase_pipeline_mode, !affine_candidate with
  | SingleInvocationPhases, None
      when not (identity_schedule_enabled ()) && not (post_tiling_affine_enabled ()) ->
      begin
        match run_pluto_scop_with_phase_dumps
                (with_pluto_extra_flags (single_invocation_tiling_flags ())) inscop with
        | Err msg -> Err msg
        | Okk (midscop, tiledscop, finalscop) ->
            if tiledscop <> finalscop then
              Err (coqstring_of_camlstring
                "plain tiling producer changed the post-tile schedule; a checked post-tiling route is required")
            else normalize_phase_tiling_result midscop tiledscop
      end
  | _ -> run_pluto_phase_pipeline_staged inscop

let run_pluto_identity_tiling_pipeline inscop =
  match tile_only_scop_scheduler inscop with
  | Err msg -> Err msg
  | Okk outscop ->
      if second_level_tiling_enabled () then
        begin
          try
            let artifact =
              PlutoTilingValidator.extract_phase_artifact_from_scops
                ~tiling_mode:PlutoTilingValidator.SecondLevel
                ~before_path:"identity_before"
                ~after_path:"identity_tiled"
                inscop
                outscop
            in
            Okk (inscop, artifact.artifact_after_scop)
          with
          | PlutoTilingValidator.ValidationError msg ->
              Err (coqstring_of_camlstring msg)
          | exn ->
              Err (coqstring_of_camlstring (Printexc.to_string exn))
        end
      else
        Okk (inscop, outscop)

let run_pluto_post_tiling_affine_pipeline inscop =
  run_pluto_scop_with_phase_dumps
    (with_pluto_extra_flags (post_tiling_affine_flags ()))
    inscop

(* An alternative untrusted proposal, consumed by the same verified three-stage
   pipeline.  The dynamic extent prevents a failed candidate from changing a
   later normal or strict compilation. *)
let post_tiling_affine_candidate :
    (OpenScop.coq_OpenScop ->
      (OpenScop.coq_OpenScop * (OpenScop.coq_OpenScop * OpenScop.coq_OpenScop)) result)
    option ref = ref None

let with_post_tiling_affine_candidate candidate action =
  let previous = !post_tiling_affine_candidate in
  post_tiling_affine_candidate := Some candidate;
  Fun.protect ~finally:(fun () -> post_tiling_affine_candidate := previous) action

let run_pluto_post_tiling_affine_pipeline_nested inscop =
  match !post_tiling_affine_candidate with
  | Some candidate -> candidate inscop
  | None ->
      match run_pluto_post_tiling_affine_pipeline inscop with
      | Err msg -> Err msg
      | Okk (midscop, posttile_scop, after_scop) ->
          Okk (midscop, (posttile_scop, after_scop))

let run_pluto_post_tiling_affine_pipeline_with_iss inscop =
  run_pluto_scop_with_phase_dumps
    (with_pluto_extra_flags (post_tiling_affine_with_iss_flags ()))
    inscop

let run_pluto_post_tiling_affine_pipeline_with_iss_nested inscop =
  match run_pluto_post_tiling_affine_pipeline_with_iss inscop with
  | Err msg -> Err msg
  | Okk (midscop, posttile_scop, after_scop) ->
      Okk (midscop, (posttile_scop, after_scop))

(* The extracted constants name the shape-independent phase composition:
   affine scheduling, checked tiling, then checked post-tiling affine
   rescheduling. *)
let run_pluto_post_tiling_affine_phase_pipeline_nested =
  run_pluto_post_tiling_affine_pipeline_nested

let run_pluto_post_tiling_affine_phase_pipeline_with_iss_nested =
  run_pluto_post_tiling_affine_pipeline_with_iss_nested

let run_pluto_phase_pipeline_with_parallel_hint inscop =
  match affine_only_scop_scheduler inscop with
  | Err msg -> Err msg
  | Okk midscop ->
      begin
        match tile_only_scop_scheduler_with_parallel_hint midscop with
        | Err msg -> Err msg
        | Okk (outscop, hint) -> Okk (midscop, outscop, hint)
      end

let run_pluto_phase_pipeline_with_vector_hint inscop =
  match affine_only_scop_scheduler inscop with
  | Err msg -> Err msg
  | Okk midscop ->
      begin
        match tile_only_scop_scheduler_with_vector_hint midscop with
        | Err msg -> Err msg
        | Okk (outscop, hint) -> Okk (midscop, outscop, hint)
      end

let post_tiling_affine_scop_scheduler_with_parallel_hint inscop =
  run_pluto_scop_with_parallel_hint
    (with_pluto_extra_flags (post_tiling_affine_parallel_flags ()))
    inscop

let post_tiling_affine_scop_scheduler_with_parallel_hint_with_iss inscop =
  run_pluto_scop_with_parallel_hint
    (with_pluto_extra_flags (post_tiling_affine_parallel_with_iss_flags ()))
    inscop

let post_tiling_affine_scop_scheduler_with_vector_hint inscop =
  run_pluto_scop_with_vector_hint
    (with_pluto_extra_flags (post_tiling_affine_vector_flags ()))
    inscop

let post_tiling_affine_scop_scheduler_with_vector_hint_with_iss inscop =
  run_pluto_scop_with_vector_hint
    (with_pluto_extra_flags (post_tiling_affine_vector_with_iss_flags ()))
    inscop

let run_pluto_phase_pipeline_with_iss inscop =
  match affine_only_scop_scheduler_with_iss inscop with
  | Err msg -> Err msg
  | Okk midscop ->
      begin
        match tile_only_scop_scheduler midscop with
        | Err msg -> Err msg
        | Okk outscop ->
            if second_level_tiling_enabled () then
              begin
                try
                  let artifact =
                    PlutoTilingValidator.extract_phase_artifact_from_scops
                      ~tiling_mode:PlutoTilingValidator.SecondLevel
                      ~before_path:"mid_affine"
                      ~after_path:"after_tiled"
                      midscop
                      outscop
                  in
                  Okk (midscop, artifact.artifact_after_scop)
                with
                | PlutoTilingValidator.ValidationError msg ->
                    Err (coqstring_of_camlstring msg)
                | exn ->
                    Err (coqstring_of_camlstring (Printexc.to_string exn))
              end
            else
              Okk (midscop, outscop)
      end

let run_pluto_phase_pipeline_with_iss_with_parallel_hint inscop =
  match affine_only_scop_scheduler_with_iss inscop with
  | Err msg -> Err msg
  | Okk midscop ->
      begin
        match tile_only_scop_scheduler_with_parallel_hint midscop with
        | Err msg -> Err msg
        | Okk (outscop, hint) -> Okk (midscop, outscop, hint)
      end

let run_pluto_phase_pipeline_with_iss_with_vector_hint inscop =
  match affine_only_scop_scheduler_with_iss inscop with
  | Err msg -> Err msg
  | Okk midscop ->
      begin
        match tile_only_scop_scheduler_with_vector_hint midscop with
        | Err msg -> Err msg
        | Okk (outscop, hint) -> Okk (midscop, outscop, hint)
      end

let phase_scop_scheduler = run_pluto_phase_pipeline

let infer_tiling_witness_scops before_scop after_scop =
  try
    let witness =
      let tiling_mode =
        if second_level_tiling_enabled ()
        then PlutoTilingValidator.SecondLevel
        else PlutoTilingValidator.Ordinary
      in
      PlutoTilingValidator.extract_witness_from_scops
        ~tiling_mode
        ~before_path:"mid_affine"
        ~after_path:"after_tiled"
        before_scop
        after_scop
    in
    Okk (PhaseTiling.convert_witness witness)
  with
  | PlutoTilingValidator.ValidationError msg ->
      Err (coqstring_of_camlstring msg)
  | exn ->
      Err (coqstring_of_camlstring (Printexc.to_string exn))

let scheduler' = affine_only_scop_scheduler


let find_and_extract_time filename =
  let ic = open_in filename in
  let rec process_lines () =
    try
      let line = input_line ic in
      let regex = regexp "\\[pluto\\] Auto-transformation time: \\([0-9.]+\\)s" in
      if string_match regex line 0 then begin
        let time_str = matched_group 1 line in
        let time_float = float_of_string time_str in
        close_in ic;
        time_float
      end else
        process_lines ()
    with
      End_of_file -> close_in ic; max_float
  in
  process_lines ()


(* also return the autoscheduling time, in pluto's stdout, "Auto-transformation time" *)
let invoke_pluto testname =
  let inscop_file = testname ^ ".beforescheduling.scop" in
  let outscop_file = testname ^ ".afterscheduling.scop" in
  let cmd = List.concat [
    [pluto_executable ();
    "--dumpscop";
    "--nointratileopt";
    "--nodiamond-tile";
    "--noprevector";
    "--smartfuse";     
    "--nounrolljam";
    "--noparallel";
    "--notile";
    (* Preserve the original 62-case evaluation recipe explicitly.  User-facing
       scheduler recipes follow Pluto's default and add RAR only on request. *)
    "--rar"];
    [testname ^ ".c"]
  ] in
  let stdout =  (tmp_file ("." ^ testname ^ ".stdout")) in
  print_string ("\027[90mInfo\027[0m: Executing \"" ^ (String.concat " " cmd) ^ "\"\n");
  let exc = command ?stdout:(Some stdout) cmd in
  if exc <> 0 then (
    command_error "invoke pluto failed" exc;)
  else 
    (* [pluto] Auto-transformation time: 0.001530s *)
    let runtime = find_and_extract_time stdout in
    Printf.printf "\027[90mInfo\027[0m: Invoke pluto succeed, with auto-transformation time %fs\n" runtime;
    print_string ("\027[90mInfo\027[0m: Reading " ^ (inscop_file) ^ " ...\n");
    match OpenScopReader.read inscop_file with 
    | Some inscop -> 
      print_string ("\027[90mInfo\027[0m: Read " ^ (inscop_file) ^ " successfully\n");
      (match OpenScopReader.read outscop_file with 
      | Some outscop ->
        print_string ("\027[90mInfo\027[0m: Read " ^ (outscop_file) ^ " successfully\n");
        Okk (inscop, outscop, runtime)
      | None -> Err (coqstring_of_camlstring ("invoke pluto failed"))
      )
    | None -> Err (coqstring_of_camlstring ("invoke pluto failed")) 
    
  (* match OpenScopReader.read inscop_file with
  | Some outscop -> Okk outscop
  | None -> Err (coqstring_of_camlstring ("cannot read " ^ inscop_file ^ "\n")) *)

(* let scheduler' cpol =
  let inscop = CPolIRs.PolyLang.to_openscop cpol in
  let inscop_file = tmp_file ".scop" in
  let outscop_file = tmp_file ".scop" in 
  OpenScopPrinter.openscop_printer inscop_file inscop;
  match OpenScopReader.read inscop_file with
  | Some outscop -> CPolIRs.PolyLang.from_openscop cpol outscop
  | None -> Err (coqstring_of_camlstring ("Error: cannot read " ^ inscop_file ^ "\n")) *)

let scop_scheduler inscop = scheduler' inscop;;

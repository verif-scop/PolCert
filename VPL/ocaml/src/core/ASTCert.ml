(* see comments in ASTCert.mli *)

module Rat = Scalar.Rat
module EqSet = IneqSet.EqSet
module Cons = IneqSet.Cons
module Cert = Cons.Cert
module Cs = EqSet.Cs
module Vec = Cs.Vec
module Var = Vec.V

type 'c op =
  | Hyp of Cs.t                 (* an hypothesis (from the inputs) *)
  | Top
  | Triv of Cstr.cmpT * Rat.t
  | Add of 'c * 'c 
  | Mul of Rat.t * 'c           (* in [Mul n c], [n] must be non-negative except if [c] is an equality ! *)
  | Merge of 'c * 'c            (* merge two inequalities an an equality *)
  | To_le of 'c                 (* relax as an non-strict inequality *) 
      
(* AST to build a "derived constraints" (e.g. a constraint included in some conjunction of input constraints) *) 
type dcstr = {
  mutable nbusers: int;
  mutable id: int;
  mutable order: int; (* for the topological sort *)
  def: dcstr op;
  mutable vardef: Var.t option;
}
  
let get_def (c: dcstr): dcstr op = c.def
let get_id (c: dcstr): int = c.id
let get_vardef (c: dcstr) = c.vardef

let make_dcstr (def: dcstr op) : dcstr = { nbusers = 0; id = 0; order = 0; def = def; vardef = None }

type env = {
  mutable inputs: dcstr list;
  mutable ndefs: int;
  mutable mdefs: dcstr list;
  mutable total: int;
  mutable xused: int;
  mutable all: dcstr list;
  mutable roots: dcstr list
}
  
(***********************************)
(* pretty-printing of certificates *)

let printid out c =
  match c.def with
  | Hyp _ -> Printf.fprintf out "h%d" c.id
  | Top -> Printf.fprintf out "top"
  | _ -> Printf.fprintf out "c%d" c.id
  
let rec printc out c =
  if c.id > 0 then
    printid out c
  else
    raw_printc out c
and p_printc out c =
  if c.id > 0 then
    printid out c
  else
    match c.def with
    | Hyp _ -> raw_printc out c
    | Top -> raw_printc out c
    | _ -> (
      Printf.fprintf out "(";
      printc out c;
      Printf.fprintf out ")"
    )
and raw_printc out c =
  match c.def with
  | Hyp _ -> printid out c
  | Top -> Printf.fprintf out "top"
  | Triv (t,n) -> Printf.fprintf out "0 %s %s" (Cstr.cmpT_to_string t) (Rat.to_string n)
  | Add (c1, c2) -> (
    p_printc out c1;
    Printf.fprintf out " + ";
    p_printc out c2)
  | Mul(n, c) -> (
    Printf.fprintf out "%s . " (Rat.to_string n);
    p_printc out c)
  | Merge(c1, c2) -> (
    p_printc out c1;
    Printf.fprintf out " & ";
    p_printc out c2)
  | To_le c -> (
    Printf.fprintf out "! ";
    printc out c)
  

 
(**********************************************)
(* importing inputs (of Polyhedra operations) *)

type input = (env option) ref;;

exception Invalid_Input;;

let make_profiling () = ref (Some { inputs = []; ndefs = 0; mdefs = []; total = 0; xused = 0; all = []; roots = []});;

let make_smart () = ref (Some { inputs = []; ndefs = 0; mdefs = []; total = -1; xused = 0; all = []; roots = []});;

let make_invalid () = ref (None)

let is_valid i = !i <> None

let top = make_dcstr Top

let get_env (i: input): env =
  match !i with
  | Some e -> e
  | None -> raise Invalid_Input;;
  
let pmake_dcstr (i: input) (def: dcstr op) : dcstr =
  let e = get_env i in
  e.total <- e.total+1;
  let r = { nbusers = 0; id = 0; order = 0; def = def; vardef = None } in
  e.all <- r::e.all;
  r
    
let profiling_factory i = {
  Cert.name = "ASTCert Profiling Factory";
  Cert.top = top;
  Cert.triv = (fun t n -> pmake_dcstr i (Triv (t,n)));
  Cert.add = (fun c1 c2 -> pmake_dcstr i (Add (c1,c2)));
  Cert.mul = (fun n c -> pmake_dcstr i (Mul (n,c)));
  Cert.merge = (fun c1 c2 -> pmake_dcstr i (Merge (c1,c2)));
  Cert.to_le = (fun c -> pmake_dcstr i (To_le c));
  Cert.to_string = (fun _ -> failwith "ASTCert LCF: to_string not yet implemented");
  Cert.rename = (fun _ -> failwith "No rename in ASTCert LCF")
}

let basic_mul n c = 
  if (Rat.equal Rat.u n) then c else make_dcstr(Mul(n,c))

(* let mu = Rat.neg (Rat.u) *)
    
let smart_mul n c =
  assert ((Rat.cmpz n) <> 0);
  if (Rat.equal Rat.u n) then
    c
  else (
    match c.def with
    | Top -> c
    | Triv(t, n') -> make_dcstr (Triv(t, Rat.mul n n'))
    | Mul(n', c') -> basic_mul (Rat.mul n n') c'
    (* | Merge(c1, c2) when (Rat.equal mu n) -> make_dcstr (Merge(c2,c1)) *)   (* NOT CLEAR: duplication risk versus little gain ! *)
    | _ -> make_dcstr (Mul(n, c))
  )

let smart_add c1 c2 =
  match c1.def, c2.def with
  | Top, _ -> c2
  | _, Top -> c1
  (* TODO: triv / Mul *)
  | Mul(n1, c1'), Mul(n2,c2') ->
     if Rat.cmpz n1 < 0 then
       let m = Rat.div n2 n1 in
       basic_mul n1 (make_dcstr (Add(c1', basic_mul m c2')))
     else
       let m = Rat.div n1 n2 in
       basic_mul n2 (make_dcstr (Add(basic_mul m c1', c2')))
  | _, _ -> make_dcstr (Add(c1, c2))

let smart_merge c1 c2 =
  match c1.def, c2.def with
  | Mul(n1, c1'), Mul(n2,c2') ->
     assert (Rat.cmpz n1 < 0);
     let m = Rat.div n2 n1 in
     basic_mul n1 (make_dcstr (Merge(c1', basic_mul m c2')))
  | _, _ -> make_dcstr (Merge(c1, c2))

let smart_factory = {
  Cert.name = "ASTCert Smart Factory";
  Cert.top = top;
  Cert.triv = (fun t n -> make_dcstr (Triv (t,n)));
  Cert.add = smart_add;
  Cert.mul = smart_mul;
  Cert.merge = smart_merge;
  Cert.to_le = (fun c -> make_dcstr (To_le c));
  Cert.to_string = (fun _ -> failwith "ASTCert LCF: to_string not yet implemented");
  Cert.rename = (fun _ -> failwith "No rename in ASTCert LCF")
}

let factory i =
  let e = get_env i in
  if e.total >= 0
  then 
    profiling_factory i
  else
    smart_factory

    
let rec rec_import (e: env) (access:'a -> Cs.t) (update: 'a -> dcstr -> 'b) (l: 'a list) (acc_input: 'b list) =
  match l with
  | [] -> acc_input
  | c :: l' ->
     let a = make_dcstr (Hyp (access c)) in
     e.inputs <- a::e.inputs;
     rec_import e access update l' ((update c a) :: acc_input)

let import (i: input) (access:'a -> Cs.t) (update: 'a -> dcstr -> 'b) (l: 'a list) =
  rec_import (get_env i) access update l []

    
let import_pol (i: input) (p: 'a Pol.t) =
  let e = get_env i in
  let eqs = rec_import e (fun (a, (c,_)) -> c) (fun (a, (c,_)) cert -> (a,(c,cert))) p.Pol.eqs [] in
  let ineqs = rec_import e  (fun (c,_) -> c) (fun (c, _) cert -> (c, cert)) p.Pol.ineqs [] in
  {Pol.eqs = eqs; Pol.ineqs = ineqs}


(***********************************************)
(* exporting outputs (of Polyhedra operations) *)
  
let set_output input roots =
  let e = get_env input in
  if e.roots <> [] then raise Invalid_Input;
  e.roots <- roots

let set_output_from_pol (i: input) (p: dcstr Pol.t) =
  let l0 = List.fold_left (fun l (_, cert) -> cert::l) [] (List.rev_append p.Pol.ineqs []) in
  let l1 = List.fold_left (fun l (x, (_,cert)) -> cert.vardef <- Some x; cert::l) l0 (List.rev_append p.Pol.eqs []) in
  set_output i l1

let skip_mul c =
  match c.def with
  | Mul(_, c) -> c
  | _ -> c

let set_output_map f input roots =
  set_output input (List.fold_left (fun l cert -> (f cert)::l) [] roots)

let set_output_fp_map f i p =
  (* equalities in the good order for the Coq tactic ! *)
  let l0 = List.fold_left (fun l (x, (_, cert)) -> let cert = (f cert) in cert.vardef <- Some x; cert::l) [] (List.rev_append p.Pol.eqs []) in
  let l1 = List.fold_left (fun l (_, cert) -> (f cert)::l) l0 p.Pol.ineqs in
  set_output i l1
    
     
let get_sons (n: 'c op) =
  match n with
  | Add (c1, c2) -> [| c1; c2 |]
  | Mul (_, c) -> [| c |]
  | Merge (c1, c2) -> [| c1; c2 |]
  | To_le c -> [| c |]
  | _ -> [| |]      

     
let rec countusers c =
  if c.order = 0 then (
    c.order <- -1;
    let sons = get_sons c.def in
    for i=0 to Array.length(sons)-1 do
      sons.(i).nbusers <- sons.(i).nbusers + 1;
    done;
    Array.iter countusers sons
  )

let inspect q c =
  match c.def with
  | Hyp _ -> ()
  | Top -> ()
  | _ -> (
    c.order <- (if c.order = -1 then c.nbusers else c.order) - 1;
    if c.order = 0 then
      Queue.push c q
  )

let register_name e c =
  e.ndefs <- 1 + e.ndefs;
  c.id <- e.ndefs

let topological_sort e l =
  let q = Queue.create () in
  let inspect = inspect q in
  List.iter inspect l; 
  while not (Queue.is_empty q) do
    let c = Queue.pop q in
    match c.def with
    | Hyp _ -> ()
    | Top -> ()
    | _ -> (
      e.xused <- e.xused + 1;
      if c.nbusers > 1 then (
        register_name e c;
        e.mdefs <- c::e.mdefs
      );
      let sons = get_sons c.def in
      Array.iter inspect sons
    )
  done
    
type output = {
  hyps: dcstr list; (* name of inputs. in the reverse ORDER than inputs !*)
  defs: dcstr list; (* intermediate definitions *)
  res: dcstr list;  
  numdefs: int;     (* = length defs *)
  usedhyps: int;    (* = number of hyps that are used *)
  used: int         (* number of derived constraints which are used *)
}

let analyze e roots =
  List.iter (fun c -> c.nbusers <- 1) roots;
  List.iter countusers roots;
  topological_sort e roots

let register_used e l =
  List.iter (fun c -> if c.nbusers > 0 then (register_name e c)) l

let export_env e =
  analyze e e.roots;
  let ndefs = e.ndefs in
  register_used e e.inputs;
  { hyps = e.inputs;
    defs = e.mdefs;
    res = e.roots;
    numdefs = ndefs;
    usedhyps = e.ndefs - ndefs;
    used = e.xused
  }
       
let extract_unused e =
  let l_unused = ref [] in
  let l_other = ref [] in
  List.iter (fun c ->
    if c.nbusers=0 then
      l_unused := c::(!l_unused)
    else (
      c.order <- -2;
      c.nbusers <- 1;
      l_other := c::(!l_other))) e.all;
  let unused_hyps = List.filter (fun c -> c.nbusers = 0) e.inputs in
  analyze e (!l_unused);
  register_used e unused_hyps;
  let l_shared =
    List.fold_left (fun l c ->
      if c.nbusers>1 then (
        (if c.id = 0 then register_name e c);
        c::l)
      else l) [] (!l_other) in
  (!l_unused, unused_hyps, l_shared)  

let export (i: input) =
  let e = get_env i in
  i := None;
  export_env e  

let print_defid out c =
  (if (c.id <> 0) then printid out c else Printf.fprintf out "_");
  Printf.fprintf out " := "

    
let print_hyps out l =     
  List.iter
    (fun c ->
      print_defid out c;
      match c.def with
      | Hyp cs -> Printf.fprintf out "%s\n%!" (Cs.to_string Var.to_string cs)
      | _ -> assert false) l
    
let print_defs out l =
  List.iter (fun c ->
    print_defid out c;
    raw_printc out c;
    Printf.fprintf out "\n") l

let print_res out l =
  if l=[] then (
    Printf.fprintf out "  TOP"
  ) else (
    List.iter (fun c ->
      Printf.fprintf out "    ";
      (match c.vardef with
       | None -> ()
       | Some x -> Printf.fprintf out "[%s]" (Var.to_string x));
      printc out c;
      Printf.fprintf out "\n%!")
      l
  )

let print_output out o =
  print_hyps out o.hyps;
  print_defs out o.defs;
  print_res out o.res;
  Printf.fprintf out "\nCertificate Stats: \n";
  Printf.fprintf out "  number of intermediate definitions %d\n" o.numdefs;
  Printf.fprintf out "  number of used hypotheses %d\n" o.usedhyps;
  Printf.fprintf out "  number of used derived constraints %d\n" o.used

let print_profiling out i =
  let e = get_env i in
  i := None;
  let o = export_env e in
  print_output out o;
  if e.total > o.used then (
    Printf.fprintf out "  number of unused derived constraints %d\n" (e.total - o.used);
    let (u,h,s) = extract_unused e in
    Printf.fprintf out "  list of unused derived constraints:\n";
    print_defs out u;
    if s <> [] then (
      Printf.fprintf out "  list of shared constraints (between used and unused):\n";
      print_defs out s
    );
    if h <> [] then (
      Printf.fprintf out "  list of unused hypotheses (which may be used in above unused constraints):\n";
      print_hyps out h
    )
  ) else if e.total = o.used then (
    Printf.fprintf out "  NO unused derived constraint\n"
  ) else (
    Printf.fprintf out "  NO OTHER PROFILING INFO (i.e. smart input)\n"
  );  
  Printf.fprintf out "-----\n\n%!";;

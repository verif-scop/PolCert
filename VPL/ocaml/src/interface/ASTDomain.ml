(** A Domain to log certificates internally built by Pol module.
    These certificates are printed here as AST (see ASTCert).

*)

(* not clear how to plug this in NCDomain ! *)
module Cs = Cstr.Rat.Positive
module Vec = Cs.Vec
module Var = Vec.V
module CP = CstrPoly.Positive
module Polynomial = CP.Poly
module Coeff = Scalar.Rat

module CW = CWrappers

let profiling = ref true;;

module Polyhedron: NCInterface.Polyhedron_Type = struct

  let last_name = ref 0;;

  let fresh_name () =
    last_name := 1 + !last_name;
    !last_name

  type nonempty = {
    name: int;
    input: ASTCert.input;
    pol: ASTCert.dcstr Pol.t;
  }

  type t =
    | NonBot of nonempty
    | Bottom

  let make () =
    if !profiling then
      ASTCert.make_profiling ()
    else
      ASTCert.make_smart ()

  let outc: out_channel = stdout;; (* everything is printer here ! *)

  let top = NonBot {
    name = 0;
    input = ASTCert.make_invalid();
    pol=Pol.top }

  let bottom = Bottom

  let is_bottom p = p = Bottom

  let to_string : (Var.t -> string) -> t -> string
    = fun varPr -> function
    | Bottom -> "bottom"
    | NonBot p ->
       if p.pol = Pol.top then
	 "top"
       else
	 Pol.to_string varPr p.pol

  let print_pol msg p =
    Printf.fprintf outc "--%s POLYHEDRA P%d:\n " msg p.name;
    Printf.fprintf outc "%s\n%!" (Pol.to_string Var.to_string p.pol)

  let synchro: bool -> nonempty -> nonempty
    = fun verb p ->
      if (ASTCert.is_valid p.input)
      then p
      else (
        let i = make() in
        let pol = ASTCert.import_pol i p.pol in
        if verb && p.name > 0 then (
	  print_pol " REUSING" p
        );
        { name = p.name; input = i; pol = pol }
      )

  let fresh: ASTCert.input -> ASTCert.dcstr Pol.t -> nonempty
    = fun i pol ->
      { name = fresh_name(); input = i; pol=pol }

  let export: string -> nonempty -> unit
    = fun msg p ->
      print_pol msg p;
      if (ASTCert.is_valid p.input) then (
        Printf.fprintf outc "-- USING CERTIFICATE:\n";
        ASTCert.set_output_from_pol p.input p.pol;
        ASTCert.print_profiling outc p.input;
        Printf.fprintf outc "\n%!"
      )

  let export_list: string -> ASTCert.input -> ASTCert.dcstr list -> unit
    = fun msg i l ->
      Printf.fprintf outc "-- %s from CERTIFICATE:\n" msg;
      ASTCert.set_output i l;
      ASTCert.print_profiling outc i;
      Printf.fprintf outc "\n%!"

  let addM : t -> Cs.t list -> t =
    fun p cs ->
      match p with
      | Bottom -> p
      | NonBot p ->
         let p = synchro true p in
         let cs = ASTCert.import p.input (fun c -> c) (fun c a -> (c,a)) cs in
	 match Pol.addM (ASTCert.factory p.input) p.pol cs with
	 | Pol.Added pol -> (
            let p = fresh p.input pol in
            NonBot p)
	 | Pol.Contrad ce -> (
            export_list "CONTRAD" p.input [ce];
            Bottom)

  let addNLM : t -> CP.t list -> t
    = fun _ _ -> assert false

  let incl : t -> t -> bool
    = fun p1 p2 ->
      match p1,p2 with
      | Bottom, Bottom | Bottom, NonBot _ -> true
      | NonBot _, Bottom -> false
      | NonBot p1', NonBot p2' -> (
        export " ARG 1 OF INCL =" p1';
        if p2'.name = 0
        then true
        else
          let p1' = synchro false p1' in
          match Pol.incl (ASTCert.factory p1'.input) p1'.pol p2'.pol with
          | Pol.Incl cert -> (
            print_pol "INCLUDED IN" p2';
            export_list "INCL" p1'.input cert;
            true
          )
          | Pol.NoIncl ->  (print_pol "NOT INCLUDED IN" p2'; false)
      )

  let meet : t -> t -> t
    = fun p1 p2 -> assert false

  let join : t -> t -> t
    = fun p1 p2 ->
      match p1, p2 with
      | Bottom, Bottom -> Bottom
      | Bottom, NonBot _ -> p2
      | NonBot _, Bottom -> p1
      | NonBot p1, NonBot p2 ->
         let p1 = synchro true p1 in
         let p2 = synchro true p2 in
	 let (p1',p2') = Pol.join (ASTCert.factory p1.input) (ASTCert.factory p2.input) p1.pol p2.pol in
         let p1 = fresh p1.input p1' in
         export "Join from left" p1;
         let p2 = fresh p2.input p2' in
         export "Join from right" p2;
         NonBot p1


  let project : t -> Var.t list -> t
    = fun p vars ->
      match p with
      | Bottom -> Bottom
      | NonBot p ->
         let p = synchro true p in
	 let p = fresh p.input (Pol.projectM (ASTCert.factory p.input) p.pol vars) in
	 NonBot p

  let widen: t -> t -> t
    = fun p1 p2 -> assert false


	let getUpperBound : t -> Vec.t -> Pol.bndT option
	  = fun p vec -> assert false

	let getLowerBound : t -> Vec.t -> Pol.bndT option
	  = fun p vec -> assert false

	let itvize : t -> Vec.t -> Pol.itvT
	  = fun p vec -> assert false

        let dump: nonempty -> unit Pol.t = fun p ->
          let ineqs = List.fold_left (fun l (c, _) -> (c, ())::l) [] p.pol.Pol.ineqs in
          let eqs = List.fold_left (fun l (a, (c,_)) -> (a,(c,()))::l) [] p.pol.Pol.eqs in
          {Pol.eqs = eqs; Pol.ineqs = ineqs}

        exception Wrong_Certificate of string

	let get_cstr = function
	  | Bottom -> []
	  | NonBot p -> Pol.get_cstr (dump p)

	let rename : Var.t -> Var.t -> t -> t
	  = fun fromX toY -> assert false

	type rep = unit Pol.t

  	let backend_rep : t -> rep option
  	  = fun p ->
  	    match p with
  	    | Bottom -> (print_endline "None"; None)
  	    | NonBot p -> Some (dump p)

  	let translate p vec = failwith "not_yet_implemented : translate"

  	let mapi _ _ _ _ = failwith "not_yet_implemented : map"

  	let minkowski _ _ = failwith "not_yet_implemented : minkowski"

	let projectM _ _ = failwith "not_yet_implemented : projectM"
end


module HLDomain = struct
  module I = NCInterface.Interface (Polyhedron)
  module I_Q = I.QInterface
  module Q = CW.MakeHighLevel (I_Q)

  module I_Z = I.ZInterface
  module Z = CW.MakeZ (I_Z)
end

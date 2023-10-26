(* Library to export LCF style certificates into an AST 
   Currently, not functorized (like Pol)
*)

module Rat = Scalar.Rat
module EqSet = IneqSet.EqSet
module Cons = IneqSet.Cons
module Cert = Cons.Cert
module Cs = EqSet.Cs
module Vec = Cs.Vec
module Var = Vec.V

(* [op] = type of operations in the factory see file Cert.ml.
 (i.e. a Farkas operation).
Here parameter 'c = the type of AST (representing a constraint)

*)

type 'c op =
  | Hyp of Cs.t                 (* an hypothesis (from the inputs) *)
  | Top
  | Triv of Cstr.cmpT * Rat.t
  | Add of 'c * 'c 
  | Mul of Rat.t * 'c           (* in [Mul n c], [n] must be non-negative except if [c] is an equality ! *)
  | Merge of 'c * 'c            (* merge two inequalities an an equality *)
  | To_le of 'c                 (* relax as an non-strict inequality *) 

(* type of "derived constraints" (e.g. a constraint included in some conjunctions of input constraints) *) 
type dcstr

val get_def: dcstr -> dcstr op
val get_id: dcstr -> int  (* a 0 id result means "unused" for an Hyp or "used once" otherwise *)
val get_vardef: dcstr -> Var.t option

(**********************************************)
(* importing inputs (of Polyhedra operations) *)

type input
  
(* a valid input has not already been exported *)
val is_valid: input -> bool

(* exception raised if an input is accessed when not valid *) 
exception Invalid_Input;;

(* returns an empty valid input for profiling *)
val make_profiling: unit -> input  

(* returns an empty valid input with smart factory *)
val make_smart: unit -> input  

(* returns an empty invalid input *)
val make_invalid: unit -> input  

 
val factory: input -> dcstr Cert.t

(* [import_pol i p] returns [p'] where [p'] has the same constraints than [p] 
   but with fresh certificates marked as "hypotheses" in input.

   NB: order of hypothesis matter (cf. output)
    => equalities are taken first (in the same order), 
       and then inequalities...

   (however, order of constraints of [p'] is in the REVERSE ORDER than [p].)
*)   
val import_pol: input -> 'a Pol.t -> dcstr Pol.t

(* a "low-level" variant of [import_pol] above *) 
val import: input -> ('a -> Cs.t) -> ('a -> dcstr -> 'b) -> 'a list ->  ('b list) 


(***********************************************)
(* exporting outputs (of Polyhedra operations) *)  

(* order of output in preserverd in res *)
val set_output: input -> dcstr list -> unit

(* order of output in preserverd in res *)
val set_output_from_pol: input -> dcstr Pol.t -> unit

val skip_mul: dcstr -> dcstr

(* map to output, but reverse the order *)
val set_output_map: ('a -> dcstr) -> input -> 'a list -> unit

(* map output to output, order non-determinated *)
val set_output_fp_map:  ('a -> dcstr) -> input -> 'a Pol.t -> unit

  
type output = {
  hyps: dcstr list; (* name of inputs. in the reverse ORDER than inputs !*)
  defs: dcstr list; (* intermediate definitions *)
  res: dcstr list;  (* result: see the order on set_output ! *)
  numdefs: int;     (* = length defs *)
  usedhyps: int;    (* = number of hyps that are used *)
  used: int;        (* number of derived constraints which are used *)
}
  
val export: input -> output

val print_output: out_channel -> output -> unit

val print_profiling: out_channel -> input -> unit

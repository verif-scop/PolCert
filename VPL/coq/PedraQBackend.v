Require Import String.
Require Import ProgVar.
Require Import CstrC.
Require Export CstrLCF.
Require Import ConsSet.
Require Export ImpureConfig.

Axiom t: Type.
Extract Constant t => "PedraQOracles.t".

Axiom top: t.
Extract Constant top => "PedraQOracles.top".

Definition pedraCert := pedraInput t Cstr.t.

Axiom isEmpty: forall {C}, (pedraCert C) -> imp (option C).
Extract Constant isEmpty => "PedraQOracles.isEmpty".

Axiom isIncl: forall {C}, (pedraCert C) * t -> imp (option (bool*(list C))).
Extract Constant isIncl => "PedraQOracles.isIncl".

Axiom add: forall {C}, (pedraCert C) * (list C) -> imp ((option t) * (list C)).
Extract Constant add => "PedraQOracles.add".

Axiom join: forall {C1 C2}, (pedraCert C1) * (pedraCert C2) -> imp (t * ((list C1) * (list C2))).
Extract Constant join => "PedraQOracles.join".

Axiom project: forall {C}, (pedraCert C) * PVar.t -> imp (t * (list C)).
Extract Constant project => "PedraQOracles.project".

Axiom meet: forall {C}, (pedraCert C) * (t * (list C)) -> imp ((option t) * (list C)).
Extract Constant meet => "PedraQOracles.meet".

(* Without certificates *)
Axiom rename: PVar.t * PVar.t * t -> imp t.
Extract Constant rename => "PedraQOracles.rename".

Axiom widen: t * t -> imp (t * Cs.t).
Extract Constant widen => "PedraQOracles.widen".

Axiom getItv: forall {C}, (pedraCert C) * LinQ.t -> imp (itvT C).
Extract Constant getItv => "PedraQOracles.getItv".

Axiom getUpperBound: forall {C}, (pedraCert C) * LinQ.t -> imp (bndT C).
Extract Constant getUpperBound => "PedraQOracles.getUpperBound".

Axiom getLowerBound: forall {C}, (pedraCert C) * LinQ.t -> imp (bndT C).
Extract Constant getLowerBound => "PedraQOracles.getLowerBound".

(* TODO: en toute rigueur, il faut ajouter un "imp" ici !
   A remplacer par un affichage plutôt que retourner une chaine ?
*)
Axiom pr: t -> string. (* not used in proofs (debugging only) *)
Extract Constant pr => "PedraQOracles.pr".



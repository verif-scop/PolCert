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
Extract Constant isEmpty => "(fun x -> Core.Base.pure (PedraQOracles.isEmpty x))".

Axiom isIncl: forall {C}, (pedraCert C) * t -> imp (option (bool*(list C))).
Extract Constant isIncl => "(fun x -> Core.Base.pure (PedraQOracles.isIncl x))".

Axiom add: forall {C}, (pedraCert C) * (list C) -> imp ((option t) * (list C)).
Extract Constant add => "(fun x -> Core.Base.pure (PedraQOracles.add x))".

Axiom join: forall {C1 C2}, (pedraCert C1) * (pedraCert C2) -> imp (t * ((list C1) * (list C2))).
Extract Constant join => "(fun x -> Core.Base.pure (PedraQOracles.join x))".

Axiom project: forall {C}, (pedraCert C) * PVar.t -> imp (t * (list C)).
Extract Constant project => "(fun x -> Core.Base.pure (PedraQOracles.project x))".

Axiom meet: forall {C}, (pedraCert C) * (t * (list C)) -> imp ((option t) * (list C)).
Extract Constant meet => "(fun x -> Core.Base.pure (PedraQOracles.meet x))".

(* Without certificates *)
Axiom rename: PVar.t * PVar.t * t -> imp t.
Extract Constant rename => "(fun x -> Core.Base.pure (PedraQOracles.rename x))".

Axiom widen: t * t -> imp (t * Cs.t).
Extract Constant widen => "(fun x -> Core.Base.pure (PedraQOracles.widen x))".

Axiom getItv: forall {C}, (pedraCert C) * LinQ.t -> imp (itvT C).
Extract Constant getItv => "(fun x -> Core.Base.pure (PedraQOracles.getItv x))".

Axiom getUpperBound: forall {C}, (pedraCert C) * LinQ.t -> imp (bndT C).
Extract Constant getUpperBound => "(fun x -> Core.Base.pure (PedraQOracles.getUpperBound x))".

Axiom getLowerBound: forall {C}, (pedraCert C) * LinQ.t -> imp (bndT C).
Extract Constant getLowerBound => "(fun x -> Core.Base.pure (PedraQOracles.getLowerBound x))".

(* TODO: strictly speaking, an imp is needed here.
   Should this print its result instead of returning a string? *)
Axiom pr: t -> string. (* not used in proofs (debugging only) *)
Extract Constant pr => "PedraQOracles.pr".

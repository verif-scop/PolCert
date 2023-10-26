Require Import ImpureConfig.
Require Import ASTerm.
Require Export Map_poly.

(** The oracle is expected to return a polynomial which equals to lc.nonaffine.
*) 

Axiom oracle: linearizeContext -> imp ZTerm.t.
Extract Constant oracle => "IOracle.oracle".

Axiom handelman_oracle : PedraQBackend.t -> cmpG -> QTerm.t -> list Map_poly.Handelman_compute.certif.
Extract Constant handelman_oracle => "HOracle_backend.oracle".
(* The implementation below is provided as a default stub ! 

IMPORTANT: keep oracle as a lemma in order to ensure that the default implementation is not used in proofs.
*)

(*

Lemma oracle (lc:linearizeContext): imp ZTerm.t.
Proof.
  exact (pure (nonaffine lc)).
Qed.
Global Opaque oracle.

*)

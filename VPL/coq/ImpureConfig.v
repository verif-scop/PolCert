(** Impure Config for UNTRUSTED backend !!! *)

Require Export Impure.

(** Decomment this to test that coq proofs still work with a state impure monad !
*)


(* Module Core: FullImpureMonad.

  Declare Module State: TYPE.

  Module Base:=StateImpureMonad State. 

  Include ImpureMonadTheory Base.

End Core. *)


(** Pure computations (used for extraction !) 

We keep module [Core] opaque in order to check that Coq proof do not depend on 
the implementation of [Base].

*)

Module Core: FullImpureMonad.

  Module Base.
    Include PureImpureMonad.
  End Base.

  Include ImpureMonadTheory Base.

End Core.


Export Core.

Global Opaque pure bind imp mayReturn impeq.
Extraction Inline imp bind pure.

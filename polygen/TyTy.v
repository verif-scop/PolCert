Require Import Bool.
Module Type TY.

    (* Here type t is variable's annotation, containing arr information *)
    Parameter t: Type.
    Parameter dummy: t.
    Parameter eqb: t -> t -> bool.
    Parameter eqb_eq: forall x y, eqb x y = true <-> x = y.

End TY.

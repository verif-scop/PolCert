Require Import AST.
Require Import ZArith.

Module Type STATE.
    Parameter t: Type.
    Parameter non_alias: t -> Prop.
    Parameter eq: t -> t -> Prop.
    
    Parameter eq_sym: 
        forall s1 s2, eq s1 s2 -> eq s2 s1. 

    Parameter eq_refl:
        forall s, eq s s.

    Parameter eq_trans:
        forall s1 s2 s3, eq s1 s2 -> eq s2 s3 -> eq s1 s3.

    Parameter dummy_state: t.
    (* Parameter compat: t -> list ident -> list Z -> Prop. *)
End STATE.

(** A simple library of Monotonic Predicate Transformers *)

Require Export ImpureConfig.

Module MPP_Definitions.

(** A more fundamental notion than Monotonic Predicate Transformers: Monotonic Predicates of Predicate *)
Record MPP (A: Type):=
  {
    apply:> (A -> Prop) -> Prop ;
    apply_monotone (P Q: A -> Prop): apply P -> (forall m, P m -> Q m) -> apply Q
  }.
Arguments apply [A].

Bind Scope MPP_scope with MPP.
Delimit Scope MPP_scope with MPP.

Local Hint Resolve apply_monotone.

(** Refinement *)

Notation "mp1 °|= mp2" := (forall P, apply mp2 P -> apply mp1 P) (at level 120, no associativity): MPP_scope.

Program Definition ret {A} (a:A): MPP A
  := {|
      apply := fun Q => Q a
     |}.

Program Definition bind {A B} (mp1: MPP A) (mp2: A -> MPP B): MPP B
  := {|
       apply := fun Q => mp1 (fun x => (mp2 x) Q)
     |}.
Obligation 1.
  eapply apply_monotone; eauto.
  simpl; eauto.
Qed.

Infix "-;" := (fun mp1 mp2 => bind mp1 (fun _ => mp2)) (at level 55, right associativity): MPP_scope.


Program Definition join {A} (mp1 mp2: MPP A): MPP A
  := {|
      apply := fun Q => (mp1 Q) /\ (mp2 Q)
      |}.
Obligation 1.
  intuition eauto.
Qed.

Program Definition meet {A} (mp1 mp2: MPP A): MPP A
  := {|
      apply := fun Q => (mp1 Q) \/ (mp2 Q)
      |}.
Obligation 1.
  intuition eauto.
Qed.


Program Definition assume (P: Prop): MPP unit
  := {|
      apply := fun Q => P -> Q tt
     |}.

Program Definition prop {A} (P: Prop): MPP A
  := {|
      apply := fun _ => P
     |}.


Program Definition fguard {A} (P: A -> Prop) (mp: MPP A) : MPP A
  := {|
      apply := fun Q => (forall a, Q a -> P a) -> mp P
     |}.


Program Definition try {A B:Type} (o: option A) (mp1: A -> MPP B) (mp2: MPP B)
  := {|
       apply := fun Q => wte o (fun x => (mp1 x) Q) (mp2 Q) 
      |}.
Obligation 1.
  xasimplify eauto.
Qed.

Program Definition UMeet A: MPP A
  := {|
        apply := fun Q => exists a, Q a
      |}.
Obligation 1.
  firstorder eauto.
Qed.

Program Definition UJoin A: MPP A
  := {|
        apply := fun Q => forall a, Q a
      |}.

End MPP_Definitions.

Export MPP_Definitions.



(** Usual monotonic predicate transformers from meta-predicates *)

Definition Skip {A} : A -> MPP A := ret.

Definition Update {A} (f: A -> A) (m: A) :MPP A 
  :=  ret (f m).

Definition Seq {A B C} (mp1: A -> MPP B) (mp2: B -> MPP C) (m:A): MPP C
  := bind (mp1 m) mp2.

Infix "°;" := (@Seq _ _ _) (at level 115, right associativity): MPP_scope.

Definition Join {A B} (mp1 mp2: A -> MPP B) (m:A) : MPP B
 := join (mp1 m) (mp2 m).

Infix "°\/" := (@Join _ _) (at level 101, right associativity): MPP_scope.

Local Open Scope MPP_scope.

Definition Assume {A} (P: A -> Prop) (m:A): MPP A 
 := assume (P m) -; ret m.

Notation "°-|" := (@Assume _) (at level 96): MPP_scope.

Definition Abort {A} (m:A): MPP A := prop False.

Definition Assert {A} (P: A -> Prop) (m:A): MPP A 
 := join (prop (P m)) (ret m).

Notation "°|-" := (@Assert _) (at level 96): MPP_scope.

Definition Meet {A B} (mp1 mp2: A -> MPP B) (m:A) : MPP B
 := meet (mp1 m) (mp2 m).

Infix "°/\" := (@Meet _ _) (at level 99, right associativity): MPP_scope.

Definition UMeet {A B C} (mp: A -> B -> MPP C) (m:B): MPP C 
 := bind (UMeet A) (fun x => mp x m).  

Definition UJoin {A B C} (mp: A -> B -> MPP C) (m:B): MPP C 
 := bind (UJoin A) (fun x => mp x m).  

Definition Try {A B C:Type} (o: option A) (mp1: A -> B -> MPP C) (mp2: B -> MPP C) (m:B): MPP C 
 := try o (fun x => mp1 x m) (mp2 m).

Definition Fguard {A B} (P: A -> B -> Prop) (mp: A -> MPP B) (m:A): MPP B
  := fguard (P m) (mp m).

Ltac simpl_ex :=
   repeat (match goal with
           | [E: (ex _) |- _ ] => destruct E
           end; intuition (subst; eauto));
   repeat (eapply ex_intro; intuition eauto).

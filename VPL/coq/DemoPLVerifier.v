(** A Demo: a Hoare-triple verifier for a tiny imperative programming language called PL 

This little demo illustrates how to use our polyhedral abstract domain on Z
through the GCL abstraction.

*)

Require Import String.
Require Import OptionMonad.
Require Import PredTrans.
Require Import DomainGCL.
Require Export PedraZ.
Require Export ASCond.
Import ZCond.
Import Term.

Local Open Scope MPP_scope.
Local Open Scope impure.

Local Notation var := positive.
Local Notation value := Z.
Local Notation mem := (Mem.t ZNum.t).

(** * SPECIFICATION PART *)

(** ** Abstract syntax of statement of PL 
PL is a tiny while-loop language, extended with guarded commands.
*)
Inductive statement: Type :=
 | Assume (c: cond)
 | Assert (msg: string) (c: cond)
 | Assign (x: var) (t: term)
 | Guassign (x:var) (c: cond)
 | Seq (s1 s2: statement)
 | Ifs (c: cond) (s1 s2: statement)
 | While (c: cond) (s: statement) (inv: cond)
  .

(** Notations (concrete syntax) *)
Bind Scope statement_scope with statement.
Bind Scope cond_scope with cond.
Bind Scope term_scope with term.
Delimit Scope statement_scope with statement.
Delimit Scope cond_scope with cond.
Delimit Scope term_scope with term.

Definition sub (x y: term) := Add x (Opp y).

Infix "+" := Add: term_scope.
Infix "-" := sub: term_scope.
Infix "*" := Mul: term_scope.
Infix "<=" := (Atom Le): cond_scope.
Infix "<" := (Atom Lt): cond_scope.
Infix "=" := (Atom Eq): cond_scope.
Infix "<>" := (Atom Neq): cond_scope.
Infix "/\" := (BinL AND): cond_scope.
Infix "\/" := (BinL OR): cond_scope.

Infix "::=" := Assign
  (at level 54, no associativity): statement_scope.

Infix "::|" := Guassign
  (at level 54, no associativity): statement_scope.


Notation "s1 -;  s2" := (Seq s1 s2): statement_scope.

Notation "'If' c 'Then' s1 'Else' s2 'Fi'" :=(Ifs c s1 s2)
  (at level 95, c at level 95, no associativity):  statement_scope.
Notation "'While' c 'Do' s 'Inv' pi 'Done'" :=(While c s pi)
  (at level 95, c at level 95, no associativity):  statement_scope.

(** ** Big-steps semantics of statement *)
Open Scope statement.

Inductive sem: statement -> mem -> (option mem) -> Prop  :=
 | sem_assume c m: 
     sat c m -> sem (Assume c) m (Some m)
 | sem_assert_ok msg c m: 
     sat c m -> sem (Assert msg c) m (Some m)
 | sem_assert_ko msg c m: 
     ~(sat c m) -> sem (Assert msg c) m None
 | sem_assign x t m: 
     sem (x ::= t) m (Some (Mem.assign x (Term.eval t m) m))
 | sem_guassign x c v m:
     xsat c m (Mem.assign x v m) ->
     sem (x ::| c) m (Some (Mem.assign x v m))
 | sem_seq_ok s1 s2 m0 m1 m2:
     sem s1 m0 (Some m1) 
     -> sem s2 m1 m2 
     -> sem (s1 -; s2) m0 m2
 | sem_seq_ko s1 s2 m0:
     sem s1 m0 None  
     -> sem (s1 -; s2) m0 None
 | sem_ifs_true c s1 s2 m0 m1: 
     sat c m0 
     -> sem s1 m0 m1
     -> sem (If c Then s1 Else s2 Fi) m0 m1
 | sem_ifs_false c s1 s2 m0 m1: 
     ~(sat c m0) 
     -> sem s2 m0 m1
     -> sem (If c Then s1 Else s2 Fi) m0 m1
 | sem_while_false c s inv m: 
     ~(sat c m) 
     -> sem (While c Do s Inv inv Done) m (Some m)
 | sem_while_true_ok c s m0 m1 m2 inv:
    sat c m0
    -> sem s m0 (Some m1)
     -> sem (While c Do s Inv inv Done) m1 m2
      -> sem (While c Do s Inv inv Done) m0 m2
 | sem_while_true_ko c s m0 inv:
    sat c m0
    -> sem s m0 None
      -> sem (While c Do s Inv inv Done) m0 None
 .

(** * Definition of partial correction *) 

Definition is_ok (s: statement) m := 
  forall m', sem s m m' -> m' <> None. 

(** * IMPLEMENTATION PART *)

Module G := FullAlarmGCL ZNum ZCond PedraZ.FullDom.

Import G.DAlarm.

Definition embed c := G.DAlarm.assume c FullDom.top.

Fixpoint postfinder s: G.cdac :=
  match s with
  | Assume c => G.assume c
  | Assert msg c => G.assert msg c
  | (x ::= t) => G.assign x t
  | (x ::| c) => G.guassign x c
  | (s1 -; s2) => G.seq (postfinder s1) (postfinder s2)
  | (If c Then s1 Else s2 Fi) =>
      G.join (G.seq (G.assume c) (postfinder s1))
             (G.seq (G.assume (Not c)) (postfinder s2))
  | (While c Do s Inv inv Done) =>
       G.seq (G.loop (G.seq (G.assume c) (postfinder s)) (fun _ => embed inv))
             (G.assume (Not c))
  end.

Program Definition postfinderX s :=
  G.cast (postfinder s)
         (UJoin (fun m' => °-| (fun m => sem s m m') °; Try m' (fun m0 => Update (fun _ => m0)) Abort))%MPP.
Obligation 1.
  generalize P H; clear P H.
  induction H0; simpl in * |- *; intuition;
  try ((eapply IHsem || apply IHsem2; eauto with vpl; simpl; eapply IHsem1); eauto with vpl; simpl_ex; eauto 20 with vpl).
  (* while false *)
  - simpl_ex.
  (* while true *)
  - simpl_ex.
Qed.

(** * MAIN THEOREM *)

(* TODO: ajouter une projection dans Alarm... *)

Definition verifier (s: statement) : Core.Base.imp bool :=
   BIND p <- G.impl (postfinderX s) FullDom.top -;
   BIND b <- FullDom.isBottom (fst p) -;
   if b then
     pure (trace INFO "** found absurd postcondition ! **" (snd p))
   else
     pure (snd p).

Hint Resolve FullDom.top_correct FullDom.isBottom_correct: vpl.
Hint Resolve G.impl_correct: vpl.
Local Opaque G.impl.

(** This theorem ensures that when "verifier s" computes "true"
    then "s" has no undefined behavior !
*) 
Theorem verifier_correct s:
  WHEN b <- verifier s THEN b=true -> forall m, is_ok s m.
Proof.
  unfold verifier, trace, is_ok; simpl.
  generalize (G.impl_correct (postfinderX s) FullDom.top).
  unfold CoreAlarm.wlp, CoreAlarm.Base.mayReturn, gamma.
  simpl.
  xasimplify ltac:(eauto with vpl);
  intros; destruct exta;
  simpl in * |- ; subst;
  lapply (H _ Hexta m); eauto with vpl;
  intros H4; generalize (H4 _ H3); clear H4;
  destruct m'; simpl; congruence.
Qed.


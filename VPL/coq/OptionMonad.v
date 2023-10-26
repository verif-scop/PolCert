(*  Here, we provide :
      - monadic notations on "option" computations
      - a small wp-computation in ltac, to help reasoning on these computations.
      - we provides also reasoning on boolean computations in the same way,
        because type "bool" could be encoded as "option unit".
*)

Require Export Setoid.
Require Export Relation_Definitions.
Require Export Morphisms.
Require Export Bool.
Require Export Sumbool.
Require Import Debugging.
Require Export Extraction.

Open Scope lazy_bool_scope.

(* Weakest-precondition style operators.

Motivations: 
  wte and ifprop are names introduced to make eauto works.
*)

(* wte k P Q = "when k then P else Q" *)
Definition wte {A} (k: option A) (P: A -> Prop) (Q: Prop) :=
     match k with
     | Some a => P a
     | None => Q
     end.

Definition ifprop (k: bool) (P Q: Prop) :=
 if k then P else Q.

(* Notations *)

Bind Scope option_scope with option.
Delimit Scope option_scope with option.
Open Scope option.

Notation "'TRY' x '<-' k 'IN' f 'CATCH' opt" := (match k with Some x => f | None => opt end)
    (at level 55, k at level 53, right associativity): option_scope.

Notation "'SOME' x '<-' k1 '-;' k2" := (TRY x <- k1 IN k2 CATCH None)
    (at level 55, k1 at level 53, right associativity): option_scope.

Notation "k1 '-;'  k2" := (SOME tt <- k1 -; k2)
  (at level 55, right associativity): option_scope.

Notation "'WHEN' x '<-' k 'THEN' R" := (wte k (fun x => R) True)
    (at level 73, R at level 100, right associativity): option_scope.

Notation "'WHEN' k 'THEN' R" := (wte k (fun _: unit => R) True)
    (at level 73, R at level 100, right associativity): option_scope.

Notation "'FAILS' k" := (wte k (fun _ => False) True)
    (at level 73): option_scope.

Notation "'EXISTS' x '<-' k 'SUCH' R" := (wte k (fun x => R) False)
    (at level 73, R at level 100, right associativity): option_scope.

Notation "'If' k 'THEN' R" := (ifprop k R True)
    (at level 73, R at level 100, right associativity): option_scope.


Definition check (b:bool) : option unit :=
  if b then Some tt else None.
Extraction Inline check.

(*
Definition essai {A B C} (x: option A) (y: A -> option B) (f: B -> C) :=
  SOME a <- x -;
  SOME b <- (y a) -;
  Some (f b).
Extraction essai.
*)

(* Properties used in our wp-calculus (see tactic "simplifyx" below)  *)
Lemma ifprop_monotone (k:bool) (P1 P2 Q1 Q2: Prop):
        ifprop k P1 Q1 
        -> (k=true -> P1 -> P2)
        -> (k=false -> Q1 -> Q2)
        -> ifprop k P2 Q2.
Proof.
  destruct k; simpl; intuition eauto.
Qed.

Lemma wte_monotone A (k:option A) (P1 P2: A -> Prop) (Q1 Q2: Prop):
        wte k P1 Q1 
        -> (forall a, k=Some a -> P1 a -> P2 a)
        -> (k=None -> Q1 -> Q2)
        -> wte k P2 Q2.
Proof.
  destruct k; simpl; intuition eauto.
Qed.

Add Parametric Morphism (A:Type): ifprop with
  signature Logic.eq ==> iff ==> iff ==> iff
  as ifprop_compat.
Proof.
  intros k P1 P2 H1 Q1 Q2; destruct k; simpl; firstorder.
Qed.

Add Parametric Morphism (A:Type): (@wte A) with
  signature Logic.eq ==> (pointwise_relation A iff) ==> iff ==> iff
  as wte_compat.
Proof.
  intros k P1 P2 H1 Q1 Q2; destruct k; simpl; firstorder.
Qed.

Lemma if_decomp {A} (b:bool) (k1 k2: A) (P: A -> Prop):
    (ifprop b (P k1) (P k2))
    -> P (if b then k1 else k2).
Proof.
   destruct b; simpl; auto.
Qed.

Lemma if_decomp_ifprop (b:bool) (k1 k2: bool) (P Q: Prop):
    (ifprop b (ifprop k1 P Q) (ifprop k2 P Q))
    -> ifprop (if b then k1 else k2) P Q.
Proof.
  intros; eapply if_decomp; eauto.
Qed.

Lemma if_decomp_wte {A} (b:bool) (k1 k2: option A) (P: A -> Prop) (Q: Prop):
    (ifprop b (wte k1 P Q) (wte k2 P Q))
    -> wte (if b then k1 else k2) P Q.
Proof.
  intros; eapply if_decomp; eauto.
Qed.

Lemma try_catch_decomp A B (k: option A) f opt (P:B -> Prop):
         (wte k (fun x => P (f x)) (P opt)) -> P (TRY x <- k IN (f x) CATCH opt).
Proof.
  destruct k; simpl; intuition.
Qed.

Lemma try_catch_decomp_ifprop A (k: option A) f opt (P Q:Prop):
         (wte k (fun x => ifprop (f x) P Q) (ifprop opt P Q)) -> ifprop (TRY x <- k IN (f x) CATCH opt) P Q.
Proof.
  intros; eapply try_catch_decomp; eauto.
Qed.

Lemma try_catch_decomp_wte A B (k: option A) f opt (P:B -> Prop) (Q:Prop):
         (wte k (fun x => wte (f x) P Q) (wte opt P Q)) -> wte (TRY x <- k IN (f x) CATCH opt) P Q.
Proof.
  intros; eapply try_catch_decomp; eauto.
Qed.


Lemma sumbool_decomp A (P Q: Prop) (k: {P}+{Q}) (k1 k2: A) (F: A -> Prop):
    (forall pf: P, k=(left pf) -> F k1)
     -> (forall pf: Q, k=(right pf) -> F k2)
        -> F (if k then k1 else k2). 
Proof.
  destruct k; simpl; eauto.
Qed.

Lemma sumbool_decomp_ifprop (P Q: Prop) (k: {P}+{Q}) (k1 k2: bool) (FP FQ:Prop):
    (forall pf: P, k=(left pf) -> ifprop k1 FP FQ)
     -> (forall pf: Q, k=(right pf) -> ifprop k2 FP FQ)
        -> ifprop (if k then k1 else k2) FP FQ. 
Proof.
  intros; eapply sumbool_decomp; eauto.
Qed.

Lemma sumbool_decomp_wte A (P Q: Prop) (k: {P}+{Q}) (k1 k2: option A) (FP: A -> Prop) (FQ:Prop):
    (forall pf: P, k=(left pf) -> wte k1 FP FQ)
     -> (forall pf: Q, k=(right pf) -> wte k2 FP FQ)
        -> wte (if k then k1 else k2) FP FQ. 
Proof.
  intros; eapply sumbool_decomp; eauto.
Qed.



Lemma prod_decomp (A B C: Type) (p: A*B) (f: A -> B -> C) (P: C -> Prop):
  (P (f (fst p) (snd p)))
    -> (P (let (x,y):=p in (f x y))).
Proof.
  destruct p; simpl; eauto.
Qed.

Lemma prod_decomp_ifprop (A B: Type) (p: A*B) (f: A -> B -> bool) (P Q: Prop):
  (ifprop (f (fst p) (snd p)) P Q)
    -> (ifprop (let (x,y):=p in (f x y)) P Q).
Proof.
  intros; eapply prod_decomp; eauto.
Qed.

Lemma prod_decomp_wte (A B C: Type) (p: A*B) (f: A -> B -> option C) (P: C -> Prop) (Q: Prop):
  (wte (f (fst p) (snd p)) P Q)
    -> (wte (let (x,y):=p in (f x y)) P Q).
Proof.
  intros; eapply prod_decomp; eauto.
Qed.


Lemma wte_decomp A (k: option A) (P: A -> Prop) (Q: Prop):
  (forall a, k = Some a -> P a) -> (k = None -> Q) -> wte k P Q.
Proof.
  intro H; destruct k; simpl; intuition.
Qed.

Lemma ifprop_decomp (b:bool) (P Q: Prop):
    (b=true -> P)
     -> (b=false -> Q)
        -> (ifprop b P Q).
Proof.
  destruct b; simpl; auto.
Qed.


(* Other properties: not used in the wp-calculus, but which may be useful
   to eliminate "wte" properties...  

  Typical usage (where H: (EXISTS x <- _ SUCH _) 
    "case (EXISTS_simpl H)"

*)

Lemma EXISTS_simpl {A} {k: option A} {P: A -> Prop}:
   (EXISTS x <- k SUCH P x) -> exists x, k=Some x /\ P x.
Proof.
  case k; simpl; firstorder.
Qed.


Lemma WHENTHEN_simpl {A} {k: option A} {P: A -> Prop}:
   (WHEN x <- k THEN P x) -> forall x, k=Some x -> P x. 
Proof.
  intros; subst; simpl in * |- *; auto.
Qed.

(* Not useful ? use simplify instead ??
Lemma WHENTHEN_elim {A} {k: option A} {P: A -> Prop}:
   (WHEN x <- k THEN P x) -> 
     forall Q: option A -> Prop, 
       (forall x, k=Some x -> P x -> Q (Some x)) ->
       (k=None -> Q None) -> 
           Q k.
Proof.
  destruct k; simpl; eauto. 
Qed.
*)

Lemma IfTHEN_simpl {b:bool} {P:Prop}: (If b THEN P) -> b=true -> P.
Proof.
  intros; subst; auto.
Qed.

Lemma wte_simpl {A} {k: option A} {P: A -> Prop} {Q: Prop} :
   wte k P Q -> { v | k=Some v & P v } + { k=None /\ Q }.
Proof.
  case k; simpl; firstorder.
Qed.

Lemma SOME_assoc {A B C} (k1: option A) (k2: A -> option B) (k3: B -> option C):
  SOME y <- (SOME x <- k1 -; k2 x) -; k3 y 
  = SOME x <- k1 -;
    SOME y <- k2 x -; 
    k3 y.
Proof.
  destruct k1; simpl; auto.
Qed.
  


(* Tactics 

MAIN tactics:  
  - xsimplify "base": simplification using from hints in "base" database (in particular "wte" lemmas).
  - xstep "base": only one step of simplification.

For good performance, it is recommanded to have several databases.

*)


(* if goal is of the form "_ = _ -> ...",
   introduce equality as "anonymous" hypothesis and rewrite it everywhere !

NB: this idea is inspired from "Program" proof obligations.
*) 
Ltac intro_rewrite := let H:= fresh "Heq_simplified" in intro H; try (rewrite !H in * |- *; simpl in * |- *).


(* decompose the current wte goal using "introduction" rules *)
Ltac wte_decompose :=
      apply prod_decomp_wte
   || apply try_catch_decomp_wte
   || (apply sumbool_decomp_wte; intro; intro_rewrite)
   || apply if_decomp_wte.

(* this tactic simplifies the current "wte" goal using any hint found via tactic "hint". *) 
Ltac apply_wte_hint hint :=
    eapply wte_monotone;
      [ hint; fail | idtac | idtac ] ;
      simpl;
      [ intro | idtac ]; intro_rewrite.

(* same as above for "ifprop" goal *)
Ltac ifprop_decompose :=
      apply prod_decomp_ifprop
   || apply try_catch_decomp_ifprop
   || (apply sumbool_decomp_ifprop; intro; intro_rewrite)
   || apply if_decomp_ifprop.

(* same as above for "ifprop" goal *)
Ltac apply_ifprop_hint hint :=
    eapply ifprop_monotone;
     [ hint; fail | idtac | idtac ] ;
     intro_rewrite.

(* default tactic when nothing else succeeds *)
Ltac default_simplify :=
      apply prod_decomp
   || apply try_catch_decomp
  (* || (apply sumbool_decomp; intro; intro_rewrite) *)
   || apply if_decomp.

(* one step of xsimplify 
see xsimplify below
*)
Ltac xstep hint :=
 match goal with
 | |- (wte _ _ _) => wte_decompose
                || apply_wte_hint hint
                || (apply wte_decomp; [ intro | idtac]; intro_rewrite)
 | |- (ifprop _ _ _) => ifprop_decompose
                || apply_ifprop_hint hint
                || (apply ifprop_decomp; intro_rewrite)
 | |- _ => default_simplify
 end.

(* one step parametrized by a base *)
(* DO NOT WORK ?
Ltac step base := xstep ltac:(eauto with base).
*)
 
(* main general tactic 
WARNING: for the good behavior of "xsimplify", "hint" must at least perform a "eauto".

Example of use:
  xsimplify ltac:(intuition eauto with base).
*)
Ltac xsimplify hint := 
 repeat (intros; xstep hint ; simpl; (tauto || hint)).

(* main tactic *)
(* DO NOT WORK ?
Ltac simplify base :=
  xsimplify ltac:(eauto with base).
*)

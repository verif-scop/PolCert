(** Impure monad for interface with impure code

Little reasoning support is provided in ltac (similar to OptionMonad).

*)

Require Import String.
Require Import Debugging.
Require Export Setoid.
Require Export OptionMonad.

Module Type ImpureMonad.

  Axiom imp: Type -> Type.
  Axiom pure: forall {A}, A -> imp A.
  Axiom bind: forall {A B}, imp A -> (A -> imp B) -> imp B.

  Axiom mayReturn: forall {A:Type}, imp A -> A -> Prop.

  Axiom mayReturn_pure: forall (A:Type) (a b:A), 
     mayReturn (pure a) b -> a=b.

  Axiom mayReturn_bind: forall (A B:Type) (k1:imp A) (k2: A -> imp B) (b:B),
     mayReturn (bind k1 k2) b -> exists a:A, mayReturn k1 a /\ mayReturn (k2 a) b.

  Axiom impeq: forall {A}, imp A -> imp A -> Prop.

  Declare Instance impeq_equiv A: Equivalence (@impeq A).
  Declare Instance bind_eq_compat A B: Proper ((@impeq A) ==> (pointwise_relation A (@impeq B)) ==> (@impeq B)) (@bind A B).
  Declare Instance mayReturn_eq_compat A: Proper ((@impeq A) ==> Logic.eq ==> iff) (@mayReturn A).

  Axiom impeq_bind_pure_l: forall (A B:Type) (k: A -> imp B) (a:A),
     (impeq (bind (pure a) k) (k a)).

  Axiom impeq_bind_pure_r: forall (A:Type) (k: imp A),
     (impeq (bind k (fun b => pure b)) k).

  Axiom impeq_bind_assoc: forall (A B C:Type) (k1: imp A) (k2: A -> imp B) (k3: B -> imp C),
     (impeq (bind (bind k1 k2) (fun b => k3 b)) (bind k1 (fun a => bind (k2 a) (fun b => k3 b)))).

End ImpureMonad.

Module Type TYPE.
   Axiom t: Type.
End TYPE.

(** model of state-monad computations *)
Module StateImpureMonad(State:TYPE)<: ImpureMonad.
   
   Definition imp (A:Type) := State.t -> A * State.t.

   (* may-return semantics of computations *)
   Definition mayReturn {A:Type} (k: imp A) (a:A): Prop := 
     exists s, fst (k s)=a.

   (* observational equivalence computations *)
  Definition impeq {A} (k1 k2: imp A) := forall s, (k1 s)=(k2 s).

   Definition pure {A:Type} (a:A) := fun (s:State.t) => (a,s).

   Definition bind {A B:Type} (k1: imp A) (k2: A -> imp B) := 
     fun s0 => let r := k1 s0 in k2 (fst r) (snd r).

   Lemma mayReturn_pure (A:Type) (a b:A): (mayReturn (pure a) b) -> a=b.
   Proof.
     unfold mayReturn, pure. simpl.
     firstorder. 
   Qed.

   Lemma mayReturn_bind (A B:Type) (k1:imp A) (k2: A -> imp B) (b:B):
         (mayReturn (bind k1 k2) b) -> exists (a:A), (mayReturn k1 a) /\ (mayReturn (k2 a) b).
   Proof.
     unfold mayReturn, bind. 
     firstorder eauto.
   Qed.

  Instance impeq_equiv A: Equivalence (@impeq A).
  Proof.
    unfold impeq; constructor 1; intro x; congruence.
  Qed.

  Instance bind_eq_compat A B: Proper ((@impeq A) ==> (pointwise_relation A (@impeq B)) ==> (@impeq B)) (@bind A B).
  Proof.
    unfold impeq, bind; intros x y; congruence.
  Qed.

  Instance mayReturn_eq_compat A: Proper ((@impeq A) ==> Logic.eq ==> iff) (@mayReturn A).
  Proof.
    unfold impeq, mayReturn, iff; intros k1 k2 H x y H0.
    subst; firstorder subst;
    eapply ex_intro; rewrite H; eauto.
  Qed.

  Lemma impeq_bind_pure_l (A B:Type) (k: A -> imp B) (a:A):
     (impeq (bind (pure a) k) (k a)).
  Proof.
    unfold impeq, pure, bind; simpl; auto.
  Qed.

  Lemma impeq_bind_pure_r (A:Type) (k: imp A):
     (impeq (bind k (fun b => pure b)) k).
  Proof.
    unfold impeq, pure, bind. intros s; destruct (k s); simpl; auto.
  Qed.

  Lemma impeq_bind_assoc (A B C:Type) (k1: imp A) (k2: A -> imp B) (k3: B -> imp C):
     (impeq (bind (bind k1 k2) (fun b => k3 b)) (bind k1 (fun a => bind (k2 a) (fun b => k3 b)))).
  Proof.
    unfold impeq, bind. intros s; simpl; auto.
  Qed.

End StateImpureMonad.

(** Model of impure computation as predicate *)
Module StandardImpureMonad<: ImpureMonad.
 
   Definition imp (A:Type) := A -> Prop.

   (* may-return semantics of computations *)
   Definition mayReturn {A:Type} (k: imp A) (a:A): Prop := k a.

   (* observational equivalence computations *)
   Definition impeq {A} (k1 k2: imp A) := forall a, (k1 a) <-> (k2 a).

   Definition pure {A:Type} (a:A) := eq a.

   Definition bind {A B:Type} (k1: imp A) (k2: A -> imp B) := 
     fun b => exists a, k1 a /\ k2 a b.

   Lemma mayReturn_pure {A:Type} (a b:A): (mayReturn (pure a) b) -> a=b.
   Proof.
     unfold mayReturn, pure. firstorder.
   Qed.

   Lemma mayReturn_bind {A B:Type} (k1:imp A) (k2: A -> imp B) (b:B):
         (mayReturn (bind k1 k2) b) -> exists (a:A), (mayReturn k1 a) /\ (mayReturn (k2 a) b).
   Proof.
     unfold mayReturn, bind. 
     firstorder.
   Qed.

  Instance impeq_equiv A: Equivalence (@impeq A).
  Proof.
    unfold impeq; constructor 1; intro x.
    - intuition.
    - firstorder.
    - intros y z H H0 a. rewrite H. auto.
  Qed.

  Instance bind_eq_compat A B: Proper ((@impeq A) ==> (pointwise_relation A (@impeq B)) ==> (@impeq B)) (@bind A B).
  Proof.
    unfold impeq, bind; intros x y H; unfold pointwise_relation; simpl.
    intros f. firstorder.
  Qed.

  Instance mayReturn_eq_compat A: Proper ((@impeq A) ==> Logic.eq ==> iff) (@mayReturn A).
  Proof.
    unfold impeq, mayReturn; intros k1 k2 H x y H0.
    subst; firstorder subst.
  Qed.

  Lemma impeq_bind_pure_l (A B:Type) (k: A -> imp B) (a:A):
     (impeq (bind (pure a) k) (k a)).
  Proof.
    unfold impeq, pure, bind; firstorder subst; auto.
  Qed.

  Lemma impeq_bind_pure_r (A:Type) (k: imp A):
     (impeq (bind k (fun b => pure b)) k).
  Proof.
    unfold impeq, pure, bind; firstorder subst; auto.
  Qed.

  Lemma impeq_bind_assoc (A B C:Type) (k1: imp A) (k2: A -> imp B) (k3: B -> imp C):
     (impeq (bind (bind k1 k2) (fun b => k3 b)) (bind k1 (fun a => bind (k2 a) (fun b => k3 b)))).
  Proof.
    unfold impeq, bind;  firstorder subst;
    repeat (eapply ex_intro; intuition eauto).
  Qed.

End StandardImpureMonad.


Module PureImpureMonad<: ImpureMonad.
   
   Definition imp (A:Type) := A.

   (* may-return semantics of computations *)
   Definition mayReturn {A:Type} (a b:A): Prop := a=b.

   (* observational equivalence computations *)
   Definition impeq {A} := @eq A.

   Definition pure {A:Type} (a:A) := a.
   Definition bind {A B:Type} (k1: A) (k2: A -> B) := k2 k1.

   Lemma mayReturn_pure (A:Type) (a b:A): (mayReturn (pure a) b) -> a=b.
   Proof.
     intuition.
   Qed.

   Lemma mayReturn_bind (A B:Type) (k1:imp A) (k2: A -> imp B) (b:B):
         (mayReturn (bind k1 k2) b) -> exists (a:A), (mayReturn k1 a) /\ (mayReturn (k2 a) b).
   Proof.
     firstorder.
   Qed.

  Instance impeq_equiv A: Equivalence (@impeq A).
  Proof.
    unfold impeq; constructor 1; intro x; congruence.
  Qed.

  Instance bind_eq_compat A B: Proper ((@impeq A) ==> (pointwise_relation A (@impeq B)) ==> (@impeq B)) (@bind A B).
  Proof.
    unfold impeq, bind; intros x y; congruence.
  Qed.

  Instance mayReturn_eq_compat A: Proper ((@impeq A) ==> Logic.eq ==> iff) (@mayReturn A).
  Proof.
    unfold impeq, mayReturn, iff; intros k1 k2 H x y H0; firstorder congruence.
  Qed.

  Lemma impeq_bind_pure_l (A B:Type) (k: A -> imp B) (a:A):
     (impeq (bind (pure a) k) (k a)).
  Proof.
    unfold impeq, pure, bind; simpl; auto.
  Qed.

  Lemma impeq_bind_pure_r (A:Type) (k: imp A):
     (impeq (bind k (fun b => pure b)) k).
  Proof.
    unfold impeq, pure, bind. simpl; auto.
  Qed.

  Lemma impeq_bind_assoc (A B C:Type) (k1: imp A) (k2: A -> imp B) (k3: B -> imp C):
     (impeq (bind (bind k1 k2) (fun b => k3 b)) (bind k1 (fun a => bind (k2 a) (fun b => k3 b)))).
  Proof.
    unfold impeq, bind. simpl; auto.
  Qed.

End PureImpureMonad.

Module ImpureMonadTheory(Export M: ImpureMonad).

  Definition impeq_bind_pure_l:=impeq_bind_pure_l.
  Definition impeq_bind_pure_r:=impeq_bind_pure_r.
  Definition impeq_bind_assoc:=impeq_bind_assoc.

  Hint Rewrite @impeq_bind_pure_l @impeq_bind_pure_r @impeq_bind_assoc: impeq.
  Hint Immediate (fun A x => @Equivalence_Reflexive _ _ (@impeq_equiv A) x).

  Definition wlp {A:Type} (k: imp A) (P: A -> Prop): Prop
    := forall a, mayReturn k a -> P a.


(* compatibility with rewriting *)

  Add Parametric Morphism (A:Type): (@wlp A) with
    signature (@impeq A) ==> (pointwise_relation A iff) ==> iff
    as wlp_compat.
  Proof.
    intros k1 k2 H P Q H0. unfold pointwise_relation, iff in H.
    constructor 1; unfold wlp; intros.
    rewrite <- H in * |- ; firstorder.
    rewrite H in * |-; firstorder.
  Qed.

(* wlp lemmas for tactics *)

  Lemma wlp_unfold A (k:imp A)(P: A -> Prop):
    (forall a, mayReturn k a -> P a)
    -> wlp k P.
  Proof.
    auto.
  Qed.

  Lemma wlp_monotone A (k:imp A) (P1 P2: A -> Prop):
    wlp k P1
    -> (forall a, mayReturn k a -> P1 a -> P2 a)
    -> wlp k P2.
  Proof.
    unfold wlp; eauto.
  Qed.

  Lemma wlp_forall A B (k:imp A) (P: B -> A -> Prop):
    (forall x, wlp k (P x))
    -> wlp k (fun a => forall x, P x a).
  Proof.
    unfold wlp; auto.
  Qed.

  Lemma wlp_pure A (P: A -> Prop) a:
    P a -> wlp (pure a) P.
  Proof.
    unfold wlp.
    intros H b H0; 
      rewrite <- (mayReturn_pure _ _ _ H0).
    auto.
  Qed.

  Lemma wlp_bind: forall A B (k1:imp A) (k2: A -> imp B) (P: B -> Prop),
    wlp k1 (fun a => wlp (k2 a) P) -> wlp (bind k1 k2) P.
  Proof.
    unfold wlp.
    intros A B k1 k2 P H a H0.
    case (mayReturn_bind _ _ _ _ _ H0); clear H0.
    intuition eauto.
  Qed.

(** Example of Higher-order reasoning *)
  Lemma List_fold_left_impeq_run (A B:Type) (f: B -> A -> imp A) (l:list B) (i: imp A):
   impeq (List.fold_left (fun k x => bind k (f x)) l i)
         (bind i (fun a => List.fold_left (fun k x => bind k (f x)) l (pure a))).
  Proof.
    simpl. 
    generalize i.
    induction l as [| a0 l IHl]; simpl.
    - intros; autorewrite with impeq; auto.
    - intros; rewrite IHl.
      autorewrite with impeq.
      apply bind_eq_compat. 
      + auto.
      + intros a. rewrite IHl; auto;
           autorewrite with impeq; auto.  
  Qed.

  Lemma wlp_List_fold_left (A B:Type) (f: B -> A -> imp A) (l:list B) (i: imp A) (P: A -> Prop): 
    wlp i (fun a => wlp (List.fold_left (fun k x => bind k (f x)) l (pure a)) P)
     -> wlp (List.fold_left (fun k x => bind k (f x)) l i) P.
  Proof.
    intros H; rewrite List_fold_left_impeq_run.
    apply wlp_bind. auto.
  Qed.

(* Tactics 

MAIN tactics:  
  - xtsimplify "base": simplification using from hints in "base" database (in particular "wlp" lemmas).
  - xtstep "base": only one step of simplification.

For good performance, it is recommanded to have several databases.

*)

  Ltac introcomp :=
    let a:= fresh "exta" in
      let H:= fresh "Hexta" in
        intros a H.

(* decompose the current wlp goal using "introduction" rules *)
  Ltac wlp_decompose :=
    apply wlp_pure
 || apply wlp_bind.

(* this tactic simplifies the current "wlp" goal using any hint found via tactic "hint". *) 
  Ltac apply_wlp_hint hint :=
    eapply wlp_monotone;
      [ hint; fail | idtac ] ;
      simpl; introcomp.

(* one step of xsimplify 
see xtsimplify below
*)
  Ltac xtstep hint :=
    match goal with
      | |- (wlp _ _) => wlp_decompose
        || apply_wlp_hint hint
          || (apply wlp_unfold; 
            introcomp)
    end.

(* main general tactic 
WARNING: for the good behavior of "xtsimplify", "hint" must at least perform a "eauto".

Example of use:
  xtsimplify ltac:(intuition eauto with base).
*)
  Ltac xtsimplify hint := 
    repeat (intros; xtstep hint ; simpl; (tauto || hint)).

  Ltac xastep hint :=
    match goal with
      | |- (wlp _ _) => wlp_decompose
        || apply_wlp_hint hint
      | |- (wte _ _ _) => wte_decompose
        || apply_wte_hint hint
          || (apply wte_decomp; [ intro | idtac]; intro_rewrite)
      | |- (ifprop _ _ _) => ifprop_decompose
        || apply_ifprop_hint hint
          || (apply ifprop_decomp; intro_rewrite)
      | |- _ =>    default_simplify
        || (apply wlp_unfold; 
          introcomp)
    end.


  Ltac xasimplify hint:=
    repeat (intros; xastep hint; simpl; (tauto || hint)).


(* Notations *)

  Bind Scope impure_scope with imp.
  Delimit Scope impure_scope with impure.
  Open Scope impure.

  Notation "'BIND' x '<-' k1 '-;' k2" := (bind k1 (fun x => k2))
    (at level 55, k1 at level 53, x at level 99, right associativity): impure_scope.

  Notation "'SOME' x '<-' k1 '-;' k2" := (TRY x <- k1 IN k2 CATCH (pure None))
    (at level 55, k1 at level 53, right associativity): impure_scope.

  Notation "k1 '-;'  k2" := (bind k1 (fun x:unit => k2))
    (at level 55, right associativity): impure_scope.

  Notation "'WHEN' a '<-' k 'THEN' R" := (wlp k (fun a => R))
    (at level 73, R at level 100, right associativity): impure_scope.

  Notation "'If' k 'THEN' R" := (wlp k (fun b => ifprop b R True))
    (at level 73, R at level 100, right associativity): impure_scope.

End ImpureMonadTheory.


Module Type FullImpureMonad.

  Declare Module Base: ImpureMonad.

  Include ImpureMonadTheory Base.

End FullImpureMonad.

Module MkFullImpureMonad(M: ImpureMonad) <: FullImpureMonad.

  Module Base.
    Include M.
  End Base.

  Include ImpureMonadTheory Base.

End MkFullImpureMonad.



Module Type FullAlarmedMonad.

  Include FullImpureMonad.

  Axiom alarm: forall {A:Type}, string -> A -> imp A. 

  Axiom mayReturn_alarm: forall (A:Type) msg (a b:A),
     (mayReturn (alarm msg a) b) -> False.

End FullAlarmedMonad.



(** Lift an impure monad into an alarmed monad.
*)
Module AlarmImpureMonad(Import M: FullImpureMonad) <: FullAlarmedMonad.

   Module Base.

   Definition imp (A:Type) := Base.imp (A*bool).

   (* may-return semantics of computations *)
   Definition mayReturn {A:Type} (k: imp A) (a:A): Prop := 
       M.Base.mayReturn k (a,true).

   (* observational equivalence computations *)
   Definition impeq {A} := @Base.impeq (A*bool).

   Definition pure {A:Type} (a:A) := M.Base.pure (a,true).

   (** &&&: lazy bool `and`*)
   Definition bind {A B:Type} (k1: imp A) (k2: A -> imp B) := 
     BIND r1 <- k1 -;
     let (a1,b1):=r1 in
     BIND r2 <- k2 a1 -;
     let (a2,b2):=r2 in
     M.Base.pure (a2,b1 &&& b2).

   Definition lift {A:Type} (k: M.Base.imp A) : imp A := 
     BIND a <- k -; M.Base.pure (a,true).

   Lemma mayReturn_pure (A:Type) (a b:A): (mayReturn (pure a) b) -> a=b.
   Proof.
     unfold mayReturn, pure.
     intro H; generalize (Base.mayReturn_pure _ _ _ H).
     congruence.
   Qed.

   Lemma mayReturn_lift (A:Type) (k: M.Base.imp A) (a:A): (mayReturn (lift k) a) -> (M.Base.mayReturn k a).
   Proof.
     unfold mayReturn, lift. intuition.
     destruct (Base.mayReturn_bind _ _ _ _ _ H) as [x H0]; clear H.
     destruct H0 as [H H0].   
     generalize (Base.mayReturn_pure _ _ _ H0).
     intros H1; inversion H1; subst; auto.
   Qed.

   Lemma bool_and_eq_true (b1 b2: bool): b1 &&& b2 = true -> b1=true /\ b2=true.
   Proof.
     destruct b1; simpl; auto.
     discriminate.
   Qed.

   Lemma mayReturn_bind (A B:Type) (k1:imp A) (k2: A -> imp B) (b:B):
         (mayReturn (bind k1 k2) b) -> exists (a:A), (mayReturn k1 a) /\ (mayReturn (k2 a) b).
   Proof.
     unfold mayReturn, bind.
     intro H; destruct (M.Base.mayReturn_bind _ _ _ _ _ H) as [x H0]; clear H.
     destruct x as [a1 b1].
     destruct H0 as [H H0].
     destruct (M.Base.mayReturn_bind _ _ _ _ _ H0) as [x H1]; clear H0.
     destruct x as [a2 b2].
     destruct H1 as [H0 H1].
     generalize (M.Base.mayReturn_pure _ _ _ H1).
     intros H2; inversion H2.
     destruct (bool_and_eq_true _ _ H5); subst; eauto.
   Qed.

  Instance impeq_equiv A: Equivalence (@impeq A).
  Proof.
    unfold impeq. apply Base.impeq_equiv.
  Qed.

  Instance bind_eq_compat A B: Proper ((@impeq A) ==> (pointwise_relation A (@impeq B)) ==> (@impeq B)) (@bind A B).
  Proof.
    unfold impeq, bind; intros x y H k1 k2 H0.
    apply Base.bind_eq_compat; auto.
    intros r. destruct r. rewrite H0; auto.
  Qed.

  Instance mayReturn_eq_compat A: Proper ((@impeq A) ==> Logic.eq ==> iff) (@mayReturn A).
  Proof.
    unfold impeq, mayReturn, iff; intros k1 k2 H x y H0.
    subst. rewrite H. intuition.
  Qed.

  Lemma impeq_bind_pure_l (A B:Type) (k: A -> imp B) (a:A):
     (impeq (bind (pure a) k) (k a)).
  Proof.
    unfold impeq, pure, bind; simpl.
    eapply Equivalence_Transitive.
    apply Base.impeq_bind_pure_l.
    simpl.
    eapply Equivalence_Transitive.
    2: apply Base.impeq_bind_pure_r.
    eapply M.Base.bind_eq_compat;eauto.
    intros x; destruct x; simpl; auto.
  Qed.

  Lemma impeq_bind_pure_r (A:Type) (k: imp A):
     (impeq (bind k (fun b => pure b)) k).
  Proof.
    unfold impeq, pure, bind.
    eapply Equivalence_Transitive.
    2: apply Base.impeq_bind_pure_r.
    eapply M.Base.bind_eq_compat;eauto.
    intros x; destruct x; simpl; auto.
    eapply Equivalence_Transitive.
    apply M.Base.impeq_bind_pure_l.
    destruct b; simpl; auto.
  Qed.

   Definition bindx {A B:Type} (k1: imp A) (k2: A -> imp B) := 
     BIND r1 <- k1 -;
     BIND r2 <- k2 (fst r1) -;
     M.Base.pure ((fst r2),(snd r1) &&& (snd r2)).

  Lemma bind_bindx_eq A B (k1: imp A) (k2: A -> imp B):
    impeq (bind k1 k2) (bindx k1 k2).
  Proof.
    unfold impeq, bind, bindx.
    eapply M.Base.bind_eq_compat; eauto.
    intros x; destruct x; simpl.
    eapply M.Base.bind_eq_compat; eauto.
    intros x; destruct x; simpl.
    auto.
  Qed.

  Lemma impeq_bind_assoc (A B C:Type) (k1: imp A) (k2: A -> imp B) (k3: B -> imp C):
     (impeq (bind (bind k1 k2) (fun b => k3 b)) (bind k1 (fun a => bind (k2 a) (fun b => k3 b)))).
  Proof.
    unfold impeq. 
    repeat (rewrite bind_bindx_eq; unfold bindx). 
    eapply Equivalence_Transitive.
    eapply Base.impeq_bind_assoc.
    eapply M.Base.bind_eq_compat; eauto.
    intros x; destruct x; simpl.
    eapply Equivalence_Transitive.
    eapply Base.impeq_bind_assoc.
    rewrite bind_bindx_eq; unfold bindx.
    eapply Equivalence_Transitive.
    2: symmetry; eapply Base.impeq_bind_assoc.
    eapply M.Base.bind_eq_compat; eauto.
    intros x; destruct x; simpl.
    eapply Equivalence_Transitive.
    apply M.Base.impeq_bind_pure_l.
    eapply Equivalence_Transitive.
    2: symmetry; eapply Base.impeq_bind_assoc.
    eapply M.Base.bind_eq_compat; eauto.
    intros x; destruct x; simpl.
    eapply Equivalence_Transitive.
    2: symmetry; apply M.Base.impeq_bind_pure_l.
    simpl; destruct b; simpl; auto.
  Qed.

  End Base.

  Include ImpureMonadTheory Base.

  Definition alarm {A:Type} (msg: string) (a:A) := 
     let a:=trace INFO msg a in
     M.Base.pure (a,false).
  
   Lemma mayReturn_alarm (A:Type) msg (a b:A): (Base.mayReturn (alarm msg a) b) -> False.
   Proof.
     unfold Base.mayReturn, alarm.
     unfold trace; simpl; intro H.
     generalize (M.Base.mayReturn_pure _ _ _ H).
     congruence.
   Qed.

End AlarmImpureMonad.

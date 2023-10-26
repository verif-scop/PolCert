Require Import String.
Require Import Impure.
Require Import PredTrans.
Require Export DomainInterfaces.

  (*
    on donne une description de plus haut niveau des operateurs des domaines abstraits.
    un opérateur d'un domaine "implémente" un transformateur de prédicats.

    Intérêt:
    1. on peut raisonner sur le niveau "transfo de predicat" sans redescendre au niveau domaine abstrait...
    2. utiliser la tactique "Program" pour définir l'implem et la spec en même temps (surmonter des limites de 
       VPLAsimplify)...

    NB: on utilise des transfo de prédicat en backward, car bien compatibles avec CPS.
   *)

Module GeneralizedBasicGCL (Export Imp: FullImpureMonad) (N: NumSig) (D: BasicDomainG Imp N).

  (* CDAC = Correctness Diagram of Abstract Computations *)
  (* inital version with bad extraction... 
  Record cdac: Type :=
    build_cdac {
      impl: D.t -> imp D.t  ;
      spec: (Mem.t N.t) -> MPP (Mem.t N.t) ;
      impl_correct: 
        forall a, WHEN a' <- impl a THEN forall m, gamma a m -> spec m (gamma a')
    }.
  (* NB sur l'extraction: MP n'est pas eliminé bien que non-informatif ! *)
  *)

  (** We inline MP definition, but emulate the constructor and the spec projection of the initial version ! *)
  Record cdac: Type :=
    raw_build_cdac {
      impl: D.t -> imp D.t  ;
      sapp: (Mem.t N.t) -> ((Mem.t N.t) -> Prop) -> Prop ;
      sapp_monotone: forall m (P Q: Mem.t N.t -> Prop), sapp m P -> (forall m', P m' -> Q m') -> sapp m Q ;
      impl_correct: 
        forall a, WHEN a' <- impl a THEN forall m, D.gamma a m -> sapp m (D.gamma a')
    }.

  Bind Scope cdac_scope with cdac.
  Delimit Scope cdac_scope with cdac.

  Program Definition build_cdac 
     (impl:  D.t -> imp D.t) 
     (spec: (Mem.t N.t) -> MPP (Mem.t N.t) | forall a, WHEN a' <- impl a THEN forall m, D.gamma a m -> spec m (D.gamma a')) : cdac
  :=
    {| 
       impl := impl ;
       sapp := fun m => spec m
    |}.
  Obligation 1.
    eapply apply_monotone; eauto.
  Qed.

  Program Definition spec (gc: cdac) m: MPP (Mem.t N.t) :=
    {| apply := sapp gc m |}.
  Obligation 1.
    eapply sapp_monotone; eauto.
  Qed.

  Extraction Inline impl spec build_cdac.
  Hint Resolve sapp_monotone impl_correct apply_monotone: vpl.

  Coercion spec: cdac >-> Funclass.
  Notation "#" := impl: cdac_scope.

  Open Scope cdac.

  Program Definition cast (gc: cdac) 
           (spec': (Mem.t N.t) -> MPP (Mem.t N.t) | forall m, (spec' m °|= gc m)%MPP): cdac
     := build_cdac
         (* impl *) (#gc)
         (* spec *) spec'
        .
  Obligation 1.
     xasimplify ltac:(eauto with vpl).
  Qed.
  Extraction Inline cast.

  Program Definition skip: cdac
     := build_cdac
        (* impl *) pure
        (* spec *) Skip
       . 
  Obligation 1.
    xasimplify ltac:(eauto with vpl).
  Qed.
  Extraction Inline skip.

  Import String.
  (* NB: fail is an internal error ! *)
  Program Definition fail (msg: string): cdac
     := build_cdac
        (* impl *) (fun a => pure (failwith DEMO msg a))
        (* spec *) Skip
       .
  Obligation 1.
    xasimplify ltac:(eauto with vpl).
  Qed.
  Extraction Inline fail.

  Program Definition seq (gc1 gc2: cdac) : cdac
     := build_cdac
         (* impl *) (fun a => BIND a' <- #gc1 a -;
                              BIND b <- D.isBottom a' -;
                              if b then
                                pure a'
                              else
                                #gc2 a') 
         (* spec *) (gc1 °; gc2)%MPP
       .
  Obligation 1.
    xasimplify ltac:(eauto with vpl).
    intros; eapply sapp_monotone; eauto with vpl.
    intros m' X; case (H0 m'); auto.
  Qed.
  Extraction Inline seq.

  Program Definition join gc1 gc2: cdac
     := build_cdac
         (* impl *) (fun a => BIND a1 <- #gc1 a -;
                              BIND a2 <- #gc2 a -;
                              D.join a1 a2)
         (* spec *) (gc1 °\/ gc2)%MPP
       .
  Obligation 1.
    xasimplify ltac:(eauto with vpl).
    simpl in * |- *; intuition eauto with vpl.
  Qed.
  Extraction Inline join.

  Program Definition loop gc (oracle: D.t -> imp D.t): cdac
   := build_cdac
           (* impl *)(fun a => 
                       BIND inv <- oracle a -;
                       BIND b <- D.isIncl a inv -;
                       if b 
                       then
                         BIND a' <- #gc inv -;
                         BIND b' <- D.isIncl a' inv -;
                         if b'
                         then pure inv
                         else 
                           let inv:=failwith DEMO "invariant preservation" D.top in
                           (* test #gc does not fail on top invariant ! *) 
                           BIND _ <- #gc inv -;
                           pure inv
                       else
                         let inv:=failwith DEMO "invariant init" D.top in
                         (* test #gc does not fail on top invariant ! *)
                         BIND _ <- #gc inv -;
                         pure inv)
           (* spec *) 
     (UMeet (fun (inv: Mem.t N.t -> Prop) => 
          °|- inv °;
          °|- (fun _ => forall m', inv m' -> gc m' inv) °;
          (UJoin (fun m => Update (fun _ => m) °; °-| inv))))%MPP
       .
  Obligation 1.
     xasimplify ltac:(eauto with vpl).
     (* normal case: invariant is given by exta *)
     - constructor 1 with (x:=D.gamma exta). intuition eauto with vpl.
     (* failwith preservation *)
     - unfold failwith; constructor 1 with (x:=(fun _ => True));
       intuition eauto with vpl.
     (* failwith init *)
     - unfold failwith; constructor 1 with (x:=(fun _ => True));
       intuition eauto with vpl.
  Qed. 
  Extraction Inline loop.

  Definition skip_info:=("#skip#")%string.

  Program Definition try {A:Type} (o: option A) (gc: A -> cdac): cdac :=
     build_cdac
      (* impl *) (fun a => match o with
                           | Some x => #(gc x) a
                           | None => (* DEBUG: pure (failwith gskip_info a) *)
                                      let a:=trace INFO skip_info a in pure a  
                         end) 
      (* spec *) (Try o (fun x => (gc x)) Skip).
  Obligation 1.
    destruct o; simpl; xasimplify ltac:(eauto with vpl).
  Qed.
  Extraction Inline try.

  Program Definition bind {A:Type} (ge: D.t -> imp A) (gc: A -> cdac) 
           (post: A -> Mem.t N.t -> Prop | forall a, WHEN r <- ge a THEN forall m, D.gamma a m -> post r m)
   := build_cdac
       (* impl *) (fun a => BIND x <- ge a -;
                            #(gc x) a) 
       (* spec *) (UMeet (fun x => °|- (post x) °; (gc x)))%MPP
      .
  Obligation 1.
    xasimplify ltac:(eauto with vpl).
  Qed.
  Extraction Inline bind.

  Close Scope cdac.

End GeneralizedBasicGCL.

Module BasicGCL (N: NumSig) (D: BasicDomain N).
  Include GeneralizedBasicGCL Core N D.
End BasicGCL.

Module GeneralizedFullGCL (Export Imp: FullAlarmedMonad) (N: NumSig) (Import Cond: XCondSig N) (D: FullAbstractDomainG Imp N Cond).

  Include GeneralizedBasicGCL Imp N D.

  Program Definition assume cond : cdac
    := build_cdac
        (* impl *) (D.assume cond)
        (* spec *) (°-| (fun m => Cond.sat cond m))%MPP
       .
  Obligation 1.
    xasimplify ltac:(eauto with vpl).
  Qed.
  Extraction Inline assume.

  Definition assert_msg: string := "failed assert:"%string. 

  Program Definition assert msg cond: cdac
    := build_cdac
        (* impl *) (fun a => 
                    let a := trace DEBUG ("Checking assert " ++ msg) a in
                    BIND b <- D.assert cond a -;
                    if b then
                      pure a
                    else
                      Imp.alarm (assert_msg ++ msg) a)
        (* spec *) (°|- (Cond.sat cond))%MPP
       .
  Obligation 1.
    xasimplify ltac:(intuition eauto with vpl);
    case (mayReturn_alarm _ _ _ _  Hexta0).
  Qed.
  Extraction Inline assert.

  Program Definition assign x te : cdac
    := build_cdac
        (* impl *) (D.assign x te)
        (* spec *) (Update (fun m => Mem.assign x (Term.eval te m) m))%MPP
       .
  Obligation 1.
    xasimplify ltac:(eauto with vpl).
  Qed.
  Extraction Inline assign.

  Program Definition guassign x c : cdac
    := build_cdac
        (* impl *) (D.guassign x c)
        (* spec *) (UJoin (fun v => °-| (fun m => Cond.xsat c m (Mem.assign x v m)) °;
                           Update (Mem.assign x v)))%MPP
       .
  Obligation 1.
    xasimplify ltac:(eauto with vpl).
  Qed.
  Extraction Inline guassign.

End GeneralizedFullGCL.

(** Now, add actually alarm handling ! *)

Module CoreAlarm <: FullAlarmedMonad.
  Include AlarmImpureMonad Core.
End CoreAlarm.

(** Straight-forward lifting of a FullAbstractDomain without alarm into a FullAbstractDomain on CoreAlarm. *)
Module LiftCoreAlarm (N: NumSig) (Cond: XCondSig N) (D: FullAbstractDomain N Cond) <: FullAbstractDomainG CoreAlarm N Cond.

  Import CoreAlarm.

  Definition t:=D.t.

  Definition gamma:=D.gamma.

  Instance gamma_ext: Proper (Logic.eq ==> pointwise_relation PVar.t Logic.eq ==> iff) gamma.
  Proof D.gamma_ext. 

  Hint Resolve Base.mayReturn_lift: vpl.

  Ltac lift_simplify name name_correct :=
    unfold name; intros; unfold wlp;
    intros; eapply name_correct; eauto with vpl.

  Definition isIncl a a' := lift (D.isIncl a a').
  Lemma isIncl_correct: forall a1 a2, If (isIncl a1 a2) THEN forall m, gamma a1 m -> gamma a2 m.
  Proof.
    lift_simplify isIncl D.isIncl_correct.
  Qed.

  Definition top:=D.top.
  Lemma top_correct: forall m, gamma top m.
  Proof D.top_correct.

  Definition join (a1 a2: t): imp t := lift (D.join a1 a2).

  Lemma join_correct: forall a1 a2, WHEN p <- join a1 a2 THEN forall m, gamma a1 m \/ gamma a2 m -> gamma p m.
  Proof.
    lift_simplify join D.join_correct.
  Qed.

  Definition widen (a1 a2:t): imp t := lift (D.widen a1 a2).

  Definition bottom := D.bottom.
  Lemma bottom_correct: forall m, (gamma bottom m)->False.
  Proof D.bottom_correct.

  Definition isBottom (a:t): imp bool := lift (D.isBottom a).
  Lemma isBottom_correct: forall a, If isBottom a THEN forall m, (gamma a m)->False.
  Proof.
    lift_simplify isBottom D.isBottom_correct.
  Qed.

  Definition project (a:t) (x:PVar.t) : imp t := lift (D.project a x).
  Lemma project_correct: forall a x, WHEN p <- project a x THEN forall m v, gamma a m -> gamma p (Mem.assign x v m).
  Proof.
    lift_simplify project D.project_correct.
  Qed.

  Definition assume c a:= lift (D.assume c a).
  Lemma assume_correct: forall c a, WHEN p <- assume c a THEN forall m, Cond.sat c m -> gamma a m -> gamma p m.
  Proof.
    lift_simplify assume D.assume_correct.
  Qed.
   
  Definition assert c a:= lift (D.assert c a).
  Lemma assert_correct: forall c a, If assert c a THEN forall m, gamma a m -> Cond.sat c m.
  Proof.
    lift_simplify assert D.assert_correct.
  Qed.

  Definition assign x t a := lift (D.assign x t a).
  Lemma assign_correct: forall x te a, WHEN p <- assign x te a THEN
    forall m, gamma a m -> gamma p (Mem.assign x (Cond.Term.eval te m) m).
  Proof.
    lift_simplify assign D.assign_correct.
  Qed.

  Definition guassign x c a := lift (D.guassign x c a).
  Lemma guassign_correct: forall x c a, WHEN p <- guassign x c a THEN 
     forall m v, Cond.xsat c m (Mem.assign x v m) -> gamma a m -> gamma p (Mem.assign x v m).
  Proof.
    lift_simplify guassign D.guassign_correct.
  Qed.

End LiftCoreAlarm.

Module FullAlarmGCL (N: NumSig) (Cond: XCondSig N) (D: FullAbstractDomain N Cond).
  Module DAlarm.
    Include LiftCoreAlarm N Cond D.
  End DAlarm.
  Include GeneralizedFullGCL CoreAlarm N Cond DAlarm.
End FullAlarmGCL.

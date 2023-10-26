(** Abstract Syntax of atomic conditions (e.g. arithmetic comparisons).

    At, the end of the module, some functors are provided to lift domains 
    with a "assume" on Cstr into "assume" on these conditions.

=> This is the place of Linearisation...

*)

Require Import Itv.
Require Import Bool.
Require Import ZArith.
Require Export ASTerm.
Require Import LinTerm.
Require Import CstrC.
Require Import OptionMonad.
Require Export DomainInterfaces.
Require Import PredTrans.
Require Import DomainGCL.
Require Import LinearizeBackend.
Require Import String.
Require Import List.
Require Import Lia. 

(* Atomic conditions *)
Module AtomicCond (N: NumSig) (Import Term: ASTermSig(N)) <: CondSig N.

  Record atomicCond : Type := { cmpOp: cmpG; right: Term.t }.

  Definition t :=  atomicCond.

  (* Semantics *)
  Definition sat (c:t) (m: Mem.t N.t): Prop := 
    N.cmpDenote (cmpOp c) N.z (eval (right c) m).

 Definition make (t1: term) (cmp:cmpG) (t2:term) : t :=
    {| cmpOp:=cmp; right:=smartAdd t2 (smartOpp t1) |}.

  Lemma make_correct t1 cmp t2 m: 
     sat (make t1 cmp t2) m <-> N.cmpDenote cmp (Term.eval t1 m) (Term.eval t2 m).
  Proof.
    unfold sat, make; simpl. autorewrite with linterm num.
    intuition; N.cmp_simplify. 
  Qed.

End AtomicCond.



Module Type AtomicCondSig (N: NumSig) (Import Term: ASTermSig(N)).

  Include AtomicCond N Term.

End AtomicCondSig.


(* 
 * Atomic Conditions on Q
 *
 * Currently, there is no linearization !
 *)

Module QAtomicCond <: AtomicCondSig QNum QTerm.

  Import QAffTerm.
  Import QTerm.

  Include AtomicCond QNum QTerm.

  (** Translations from QAtomicCond.t into Cstr.t *) 

  Lemma switch_sides: forall (cmp:cmpT) (n1 n2: QNum.t),
     QNum.cmpDenote cmp QNum.z (QNum.add n1 n2) <->
     QNum.cmpDenote cmp (QNum.opp n1) n2.
  Proof.
    intuition; QNum.cmp_simplify.
  Qed.

  Definition toCstr (cmp:cmpT) (aft: QAffTerm.t) : Cstr.t :=
    {| Cstr.coefs:= LinQ.opp (lin aft) ; Cstr.typ:=cmp; Cstr.cst:= (cte aft) |}.

  Lemma toCstr_correct cmp aft m: Cstr.sat (toCstr cmp aft) m <-> QNum.cmpDenote cmp QNum.z (QAffTerm.eval aft m).
  Proof.
    unfold toCstr, Cstr.sat, QAffTerm.eval; destruct aft as [lt aux]; simpl.
    autorewrite with linterm num.
    rewrite <- switch_sides.
    autorewrite with linterm num; intuition.
  Qed.

  Global Opaque toCstr.

End QAtomicCond.


Module QAtomicCondAssume (D: BasicDomain QNum)
                         (CstrD: HasAssume QNum Cstr D) 
                         <: HasAssume QNum QAtomicCond D.


  Import QAffTerm.
  Import QAtomicCond.
  Import D.

  Import QArith.
  Import Qcanon.

  Lemma neq_join (n1 n2: QNum.t): n1 <> n2 -> n1 < n2 \/ n2 < n1.
  Proof.
    intro H; destruct (Q_dec n1 n2) as [H0|H0]; try (intuition).
    destruct H. auto.
  Qed.

  Open Scope option_scope.
  Open Scope impure_scope.
 
  Definition affAssume cmp aft a :=
    match cmpG2T cmp with
    | Some cmpT => CstrD.assume (toCstr cmpT aft) a
    | None => 
          BIND a1 <- CstrD.assume (toCstr LtT aft) a -;
          BIND a2 <- CstrD.assume (toCstr LtT (QAffTerm.opp aft)) a -;
          D.join a1 a2
    end.

  Local Arguments QNum.add x y: simpl never.
  Local Hint Resolve QNum.cmpG2T_correct: vpl.

  Lemma affAssume_correct cmp aft a:
      WHEN p <- affAssume cmp aft a THEN 
      forall m, QNum.cmpDenote cmp QNum.z (QAffTerm.eval aft m) -> gamma a m -> gamma p m.
  Proof.
    unfold affAssume.
    VPLAsimplify; (intros X; intros; apply X; clear X; auto).
    (* Some case *)
    + rewrite toCstr_correct. rewrite H; auto.
    (* neq case *)
    + destruct cmp; try discriminate.
      simpl in * |-.
      destruct (neq_join _ _ H2);
      [ constructor 1; apply H0 | constructor 2; apply H1]; 
      try (rewrite toCstr_correct; simpl); 
      auto.
      rewrite <- QNum.OppZ. autorewrite with linterm. 
      rewrite <- QNum.OppLt. auto.
  Qed.
  Local Hint Resolve affAssume_correct: vpl.
  Opaque affAssume.


  Definition assume (c:QAtomicCond.t) (a: D.t):  imp D.t :=
     let ti := right c in
     let (te,aft) := QTerm.affineDecompose ti in
     if QTerm.pseudoIsZero te then
       (* affine condition ! *)
       affAssume (cmpOp c) aft a
     else
       failwith NYI "Non-linear terms over Q are not yet supported"%string (pure a).

  Add Ring QRing: QNum.Ring.

  Lemma assume_correct: forall c a, WHEN p <- assume c a THEN 
     forall m, QAtomicCond.sat c m -> gamma a m -> gamma p m.
  Proof.

    unfold assume, sat; xasimplify ltac:(eauto with pedraQ vpl).
    intros X m; intros; apply X; auto.
    QNum.cmp_simplify.
    rewrite <- QTerm.affineDecompose_correct, H.
    ring.

  Qed.
  Global Opaque assume.
  Global Hint Resolve assume_correct: vpl.

End QAtomicCondAssume.



(* 
 * Atomic Conditions on Z (with linearization a la Miné)
 *
 *)


Module ZAtomicCond <: AtomicCondSig ZNum ZTerm.
 
  Import ZAffTerm.
  Import ZTerm.
  Include AtomicCond ZNum ZTerm.

  (** Translation from ZAtomicCond.t into Cstr.t (by lifting of QAtomicCond) *) 

  Definition toCstr (cmp:cmpT) (aft: ZAffTerm.t) : Cstr.t :=
    QAtomicCond.toCstr cmp (QAffTerm.lift aft).

  Lemma toCstr_correct cmp aft m: Cstr.sat (toCstr cmp aft) (Mem.lift ZtoQ.ofZ m) <-> ZNum.cmpDenote cmp ZNum.z (ZAffTerm.eval aft m).
  Proof.
    unfold toCstr, ZAffTerm.eval.
    rewrite QAtomicCond.toCstr_correct.
    unfold QAffTerm.lift; destruct cmp; simpl; autorewrite with linterm num; intuition.
  Qed.

End ZAtomicCond.


Module ZtoQCstr <: CondSig ZNum.

Definition t := Cstr.t.

Definition sat c m := Cstr.sat c (Mem.lift ZtoQ.ofZ m).

End ZtoQCstr.


Require Import ZNone.
Require Import ZNoneItv.
Require FMapPositive.

(* A functor that lift conditions from "ZtoQCstr" to "ZCond" 

This is the place of the intervalization/linearization

*)
Module ZAtomicCondAssume (D: BasicDomain ZNum) 
                         (CstrD: HasAssume ZNum ZtoQCstr D) 
                         (ItvD: HasGetItvMode ZNum ZTerm ZNItv D)
                          <: HasAssume ZNum ZAtomicCond D.

  Import ZAffTerm.
  Import ZAtomicCond.
  Import ZTerm.
  Import D.
  Add Ring ZRing: ZNum.Ring.

  Open Scope Z_scope.
  Open Scope option_scope.
  Import String.
  Open Scope impure.

  (** Assume of affine terms (on Z)
    0 < x is written 0 <= x-1
    0 <> x is written  0 <= x-1 \/ 0 <= -1-x 
   *)
  Definition affAssumeLe aft a :=
     CstrD.assume (toCstr LeT aft) a.

  Lemma affAssumeLe_correct aft a:
      WHEN p <- affAssumeLe aft a THEN 
      forall m, 0 <= ZAffTerm.eval aft m -> gamma a m -> gamma p m.
  Proof.
    unfold affAssumeLe; simpl; VPLAsimplify;
    intros X; intros; apply X; auto;
    unfold ZtoQCstr.sat; rewrite toCstr_correct;
    simpl; ZNum.simplify.
  Qed.
  Local Hint Resolve affAssumeLe_correct: vpl.
  Extraction Inline affAssumeLe.
  Local Opaque affAssumeLe.

  Definition affAssumeLt aft a :=
    affAssumeLe (ZAffTerm.addc (-1)%Z aft) a.

  Lemma affAssumeLt_correct aft a:
      WHEN p <- affAssumeLt aft a THEN 
      forall m, 0 < ZAffTerm.eval aft m -> gamma a m -> gamma p m.
  Proof.
    unfold affAssumeLt; VPLAsimplify.
    intros X; intros; apply X; auto.
    autorewrite with linterm; ZNum.simplify.
  Qed.
  Local Hint Resolve affAssumeLt_correct: vpl.
  Extraction Inline affAssumeLt.
  Local Opaque affAssumeLt.

  Definition affAssumeGt aft a :=
    affAssumeLt (ZAffTerm.opp aft) a.

  Lemma affAssumeGt_correct aft a:
      WHEN p <- affAssumeGt aft a THEN 
      forall m, ~0 <= (ZAffTerm.eval aft m) -> gamma a m -> gamma p m.
  Proof.
    unfold affAssumeGt; VPLAsimplify. simpl in * |- *.
    intros X; intros; apply X; clear X; auto.
    autorewrite with linterm.
    ZNum.simplify.
  Qed.
  Local Hint Resolve affAssumeGt_correct: vpl.
  Extraction Inline affAssumeGt.
  Opaque affAssumeGt.

    Lemma neq_join n1 n2: n1 <> n2 -> n1 < n2 \/ n2 < n1.
    Proof.
      intro H ; destruct (Ztrichotomy_inf n1 n2) as [H0|H0]; auto with zarith.
      destruct H0; auto with zarith.
    Qed.
 
  Definition affAssume cmp aft a :=
    match cmp with
    | Eq => CstrD.assume (toCstr EqT aft) a
    | Le => affAssumeLe aft a
    | Lt => affAssumeLt aft a
    | Neq => BIND a1 <- affAssumeLt aft a -;
             BIND a2 <- affAssumeGt aft a -;
             D.join a1
                    a2
    end.

  Local Arguments ZNum.add x y: simpl never.

  Lemma affAssume_correct cmp aft a:
      WHEN p <- affAssume cmp aft a THEN 
      forall m, ZNum.cmpDenote cmp ZNum.z (ZAffTerm.eval aft m) -> gamma a m -> gamma p m.
  Proof.
    unfold affAssume; destruct cmp; simpl; VPLAsimplify;
    intros X; intros; apply X; auto.
    (* eq case *)
    unfold ZtoQCstr.sat; rewrite toCstr_correct;
    autorewrite with linterm; simpl; ZNum.simplify.
    (* neq case *)
      simpl in * |- *; case (neq_join _ _ H1);
      [ constructor 1; apply H | constructor 2; apply H0];
      ZNum.simplify.
  Qed.
  Local Hint Resolve affAssume_correct: vpl.
  Opaque affAssume.


  (** Early Computation of the interval of all variables *) 
  Section EarlyVariableIntervals.

  Import FMapPositive.

  Definition add_variable (a: D.t) (x: PVar.t) (mitv: PositiveMap.t ZNItv.t): imp (PositiveMap.t ZNItv.t) :=
    match PositiveMap.find x mitv with
    | Some _ => pure mitv
    | None   => BIND itv <- ItvD.getItvMode BOTH (ZTerm.Var x) a -;
                pure (PositiveMap.add x itv mitv)
    end.

  Definition get_variables (a: D.t) te: imp (PositiveMap.t ZNItv.t) :=
    ZTerm.fold_variables te (fun x i => 
       BIND mitv <- i -;
       add_variable a x mitv) (pure (PositiveMap.Leaf)).

  Lemma PositiveMap_find_None {A} x:
    FAILS PositiveMap.find x (PositiveMap.Leaf (A:=A)).
  Proof.
    rewrite PositiveMap.gleaf; simpl; auto.
  Qed.
  Local Hint Resolve PositiveMap_find_None.

  Lemma get_variables_correct a te:
    WHEN mitv <- get_variables a te THEN 
      forall x m, gamma a m -> 
       (WHEN itv <- PositiveMap.find x mitv THEN ZNItv.sat itv (m x))%option. 
  Proof.
     unfold get_variables, add_variable.
     apply ZTerm.fold_variables_preserv;
     xasimplify ltac:(eauto with vpl).
     simpl in * |- *; destruct (PositiveMap.E.eq_dec x0 x).
       + subst; rewrite PositiveMap.gss in * |- *.
         inversion Heq_simplified0. subst. auto.
       + rewrite PositiveMap.gso in * |- *; auto.
         generalize (H0 x0 m).
         pattern (PositiveMap.find x0 exta);
         rewrite Heq_simplified0; simpl. auto.
  Qed.

  Definition mitv_find (mitv: PositiveMap.t ZNItv.t) x:  ZNItv.t :=
    match PositiveMap.find x mitv with
    | Some itv => itv
    | None   => ZNItv.top
    end.

  Local Hint Resolve get_variables_correct.

  Definition isItvEnv (env: PVar.t -> ZNItv.t) (m: Mem.t ZNum.t): Prop := forall x, ZNItv.sat (env x) (m x).

  Lemma isItvEnv_unfold env m: isItvEnv env m -> forall x, ZNItv.sat (env x) (m x).
  Proof.
    auto.
  Qed.

  Hint Resolve isItvEnv_unfold: zn.

    
  Theorem mitv_find_get_variables a te:
    WHEN mitv <- get_variables a te THEN 
     forall m, gamma a m -> isItvEnv (mitv_find mitv) m.
  Proof.
    unfold mitv_find, isItvEnv. xasimplify ltac:(eauto with vpl zn).
  Qed.
 
  End EarlyVariableIntervals.
  Extraction Inline ZTerm.fold_variables.

  Local Hint Resolve mitv_find_get_variables: vpl.


  (** Dealing with non-affine terms.
     - We treat equality as a conjunct of two inequalities
       (rem: this may be not the better choice ! See below...)
     - Strict inequalities are not supported (they should be eliminated through nnfForAssume) 
   *)

  Section Intervalization.

    Variable env: PVar.t -> ZNItv.t.

    Fixpoint intervalize (sic: bool) mo (te:term) (a:D.t): imp ZNItv.t
      := match te with
         | Var x => 
             if sic then pure (env x) 
                    else ItvD.getItvMode mo (Var x) a
         | Cte c => pure (ZNItv.single c)
         | Add tl tr => BIND i1 <- intervalize sic mo tl a -;
                        BIND i2 <- intervalize sic mo tr a -;
                         pure (ZNItv.add mo i1 i2)
         | Opp te => BIND i <- intervalize sic (ZNItv.oppMode mo) te a -;
                     pure (ZNItv.opp i)
         | Mul tl tr => 
              match (matchCte tr) with
              | Some c => 
                     BIND i <- intervalize sic (if Z_isNat c then mo else ZNItv.oppMode mo) tl a -;
                     pure (ZNItv.mulZ mo c i)
              | _ => BIND i1 <- intervalize sic BOTH tl a -;
                     BIND i2 <- intervalize sic BOTH tr a -;
                     pure (ZNItv.mul mo i1 i2)
              end
         | Annot AFFINE te => 
             if sic then intervalize sic mo te a
                    else ItvD.getItvMode mo te a
         | Annot STATIC te => 
             let te:=trace DEBUG "!INTERV STATIC!" te in
             intervalize true mo te a
         | Annot _ te => 
             intervalize sic mo te a
       end.


   Theorem intervalize_correct te a: forall sic mo,
     WHEN itv <- intervalize sic mo te a THEN forall m, isItvEnv env m -> gamma a m -> ZNItv.sat itv (eval te m).
   Proof.
    induction te; simpl; try (xasimplify ltac:(eauto with zn vpl); fail).
    (* mul *)
    + xasimplify ltac:(eauto with zn vpl).
      (* cte case *) 
      intros; simpl in * |- *; rewrite H. unfold ZNum.mul. 
      rewrite Z.mul_comm; eauto with zn.
    (* annot *)
    + destruct a0; simpl; xasimplify ltac:(eauto with zn pedraQ vpl).
   Qed.

  End Intervalization.
  Local Hint Resolve intervalize_correct: vpl.

  Module G := BasicGCL ZNum D.
  Import G.

  Program Definition gAffAssumeLe aft : cdac
    := build_cdac
        (* impl *) (affAssumeLe aft)
        (* spec *) (°-| (fun m => 0 <= ZAffTerm.eval aft m))%MPP
       .
  Obligation 1.
    VPLAsimplify.
  Qed.
  Extraction Inline gAffAssumeLe.

  Program Definition gAffAssumeLt aft : cdac
    := build_cdac
        (* impl *) (affAssumeLt aft)
        (* spec *) (°-| (fun m => 0 < ZAffTerm.eval aft m))%MPP
       .
  Obligation 1.
    VPLAsimplify.
  Qed.
  Extraction Inline gAffAssumeLt.

  Program Definition gAffAssumeGt aft : cdac
    := build_cdac
        (* impl *) (affAssumeGt aft)
        (* spec *) (°-| (fun m => ~ 0 <= ZAffTerm.eval aft m))%MPP
       .
  Obligation 1.
    VPLAsimplify.
  Qed.
  Extraction Inline gAffAssumeGt.

  Program Definition gIntervalize env sic mo te (k: ZNItv.t -> cdac): cdac 
     := G.bind (intervalize env sic mo te) k (fun itv m => isItvEnv env m -> ZNItv.sat itv (eval te m)).
  Obligation 1.
    VPLAsimplify.
  Qed.
  Extraction Inline gIntervalize.

  Program Definition intervalizeG env sic mo (te: ZTerm.t) (k: NAItv.itv -> cdac): cdac  :=
     G.cast
       (gIntervalize env sic mo te (fun i => k (NAItv.cte i)))
       (°-| (fun m => isItvEnv env m) °;
            (UMeet (fun itv => °|- (fun m => ZNItv.sat (NAItv.eval itv m) (ZTerm.eval te m)) °; spec (k itv))))%MPP.
   Obligation 1.
     intuition; simpl_ex;
     autorewrite with linterm; auto.
   Qed.
   Extraction Inline intervalizeG.

  Definition castAFFINE_error := "ASAtomicCond.castAFFINE over non-affine term "%string.

  Program Definition castAFFINE te (k: ZAffTerm.t -> cdac): cdac :=
     G.cast
       (let (te',aft) := ZTerm.affineDecompose te in
        if ZTerm.pseudoIsZero te' then
          (* affine condition ! *)
          k aft
        else 
          G.fail (castAFFINE_error ++ (pr te)))
       (Skip °/\ UMeet (fun aft => °|- (fun m => ZAffTerm.eval aft m=ZTerm.eval te m) °; spec (k aft)))%MPP.
  Obligation 1.
     generalize (affineDecompose_correct te).
     destruct (affineDecompose te) as [te0 aft].
     generalize (pseudoIsZero_correct te0).
     destruct (pseudoIsZero te0); simpl; auto.
     intros H0 H1; constructor 2.
     simpl_ex.
     rewrite <- (H1 m), (H0 m).
     ring.
  Qed.

  Program Definition caseSign te (aP: ZAffTerm.t -> cdac) (aN: ZAffTerm.t -> cdac): cdac :=
     (castAFFINE te (fun aft =>
                       G.join (G.seq (gAffAssumeLe aft) 
                                     (aP aft))
                              (G.seq (gAffAssumeGt aft)
                                     (aN aft)))).
  Extraction Inline caseSign. 

  Program Definition linearizeMul env (sic:bool) mo (tl tr: term) (k: NAItv.itv -> cdac) : cdac :=
    let omo := ZNItv.oppMode mo in
    G.cast 
          (* impl *)
          (if sic then  (* we factorize the intervalization on both branch *)
             (gIntervalize env true BOTH tl (fun itv =>
                  (caseSign tr (fun aftr => k (NAItv.mulP1 mo itv aftr))
                               (fun aftr => k (NAItv.mulN mo itv aftr)))))
           else (* we delay the intervalization in both branch *)
             (caseSign tr (fun aftr => gIntervalize env sic mo tl (fun itv => k (NAItv.mulP1 mo itv aftr)))
                          (fun aftr => gIntervalize env sic omo tl (fun itv => k (NAItv.mulN mo itv aftr)))))
          (* spec *)
          (°-| (fun m => isItvEnv env m) °;
               ((Skip °/\ UMeet (fun itv => °|- (fun m => ZNItv.sat (NAItv.eval itv m) (ZTerm.eval (Mul tl tr) m)) °;
                                              spec (k itv)))))%MPP.
  Obligation 1.
     destruct sic; simpl in * |-; intuition; simpl_ex; rewrite <- H1; clear H1 tr.
     - destruct (Z_le_dec 0 (ZAffTerm.eval x0 m));
       [lapply H | lapply H4]; clear H H4; intuition;
       constructor 2; simpl_ex;
       autorewrite with linterm; ZNum.simplify; rewrite Z.mul_comm;
       auto with zn.
     - destruct (Z_le_dec 0 (ZAffTerm.eval x m));
       [lapply H | lapply H3]; clear H H3; intuition;
       constructor 2; simpl_ex;
       autorewrite with linterm; ZNum.simplify; rewrite Z.mul_comm;
       auto with zn.
  Qed. 

   Fixpoint linearizeG env sic mo (te:term) (k: NAItv.itv -> cdac): cdac 
     := match te with
          | Add tl tr =>
            linearizeG env sic mo tl (fun itvl => 
                linearizeG env sic mo tr (fun itvr => k (NAItv.add mo itvl itvr))) 
          | Opp te => linearizeG env sic (ZNItv.oppMode mo) te (fun itv => k (NAItv.opp mo itv)) 
          | Mul tl (Annot AFFINE tr) => 
              match matchCte tr with
              | Some c => linearizeG env sic (if Z_isNat c then mo else ZNItv.oppMode mo) tl (fun itv => k (NAItv.mulZ mo c itv))
              | _ => linearizeMul env sic mo tl tr k
              end
          | Annot AFFINE te => 
             castAFFINE te (fun aft => k (NAItv.single aft))
          | Annot STATIC te => 
             linearizeG env true mo te k
          | Annot INTERV te =>
             intervalizeG env sic mo te k
          | Annot _ te =>
             linearizeG env sic mo te k
          | te => intervalizeG env sic mo te k
        end.

  Program Definition linearizeGX env sic mo (te:term) (k: NAItv.itv -> cdac): cdac :=
     G.cast
       (linearizeG env sic mo te k)
       (°-| (fun m => isItvEnv env m) °; 
          (Skip °/\ UMeet (fun itv => °|- (fun m => ZNItv.sat (NAItv.eval itv m) (ZTerm.eval te m)) °;
                                        spec (k itv))))%MPP.
  Obligation 1.
   generalize sic mo k P H; clear sic mo k P H; induction te; simpl; intros sic mo k P; intuition.
   - (* PLUS *)
     case (IHte1 _ _ _ _ H); clear H IHte1; intuition.
     simpl_ex.
     case (IHte2 _ _ _ _ H2); clear H2 IHte2; intuition.
     constructor 2; simpl_ex.
     autorewrite with linterm.
     ZNum.simplify. auto with zn.
  -  (* OPP *)
     case (IHte _ _ _ _ H); clear H IHte; intuition.
     constructor 2; simpl_ex.
     autorewrite with linterm.
     ZNum.simplify. auto with zn.
  -  (* MULT AFFINE *)
     destruct te2; simpl in * |- *; auto;
     destruct a; simpl in * |- *; auto.
     generalize (matchCte_def te2).
     destruct (matchCte te2); simpl in * |- *; auto.
     intros H1; rewrite H1.
     case (IHte1 _ _ _ _ H); clear H IHte1; intuition.
     constructor 2; simpl_ex.
     autorewrite with linterm.
     ZNum.simplify. rewrite Z.mul_comm; auto with zn.
  - (* ANNOT *)
     destruct a; simpl in * |- *; eauto.
     destruct H; simpl in * |- *; auto.
     constructor 2; simpl_ex. 
     autorewrite with linterm; rewrite H1; ZNum.simplify. 
     auto with zn.
  Qed.

  Ltac wte_elim:=
   repeat (match goal with
           | [_: (wte ?t _ _) |- _ ] => destruct t; simpl in * |- *; intuition
           end); autorewrite with linterm in * |- *; simpl in * |- *; ZNum.simplify.
 
  Lemma eq_zero n1 n2: 0 = n1 + n2 -> n1 = -n2.
  Proof.
    lia.
  Qed.

  Program Definition assumeOpCPS env sic cmp te aft :=
    let te := trace DEBUG ("assumeOp.te:" ++ (ZTerm.pr te)) te in
    let te := trace DEBUG ("assumeOp.aft:" ++ (ZTerm.pr (smartAdd (fromLin (lin aft)) (Cte (cte aft))))) te in
    G.cast
    (match cmp with
    | Eq => linearizeGX env sic BOTH te (fun i => G.seq (G.try (NAItv.up i) (fun u => gAffAssumeLe (ZAffTerm.add u aft)))
                                                        (G.try (NAItv.low i) (fun l => gAffAssumeLe (ZAffTerm.opp (ZAffTerm.add l aft)))))
    | Le => linearizeGX env sic UP te (fun i => G.try (NAItv.up i) (fun u => gAffAssumeLe (ZAffTerm.add u aft)))
    | Lt => linearizeGX env sic UP te (fun i => G.try (NAItv.up i) (fun u => gAffAssumeLt (ZAffTerm.add u aft)))
    | Neq => linearizeGX env sic BOTH te (fun i => G.join (G.try (NAItv.up i) (fun u => gAffAssumeLt (ZAffTerm.add u aft)))
                                                          (G.try (NAItv.low i) (fun l => gAffAssumeGt (ZAffTerm.add l aft))))
    end)
   (°-| (fun m => isItvEnv env m /\ ZNum.cmpDenote cmp 0 (ZTerm.eval te m + ZAffTerm.eval aft m)))%MPP.
  Obligation 1.
     destruct cmp; unfold trace; simpl in * |- *; unfold ZNItv.sat in * |-; intuition; simpl_ex; 
     autorewrite with linterm in * |-; simpl in * |-.
     + (* eq *) rewrite (eq_zero _ _ H1) in * |-. clear H1.
       wte_elim. 
     lapply H3; clear H3.
     - intros H3. wte_elim. 
     - ZNum.simplify.
     + (* le *) wte_elim.
     + (* lt *) wte_elim.
     + (* neq *) case (neq_join _ _ H1); clear H1.
       - intros; clear H5; wte_elim.
       - intros; clear H2; wte_elim.
  Qed.

  Program Definition assumeOpAnnot env sic cmp te aft :=
   G.cast
   (assumeOpCPS env sic cmp (annotAFFINE te) aft)
   (°-| (fun m => isItvEnv env m /\ ZNum.cmpDenote cmp 0 (ZTerm.eval te m + ZAffTerm.eval aft m)))%MPP.
  Obligation 1.
    unfold trace in * |-; simpl in * |-.
    rewrite annotAFFINE_correct in * |- ; auto.
  Qed.
  Extraction Inline assumeOpAnnot.

  Module ZPeq := ZPomialEquality ZTerm ZTerm.
  Import ZPeq.

  Local Hint Resolve ZPeq.pomial_eq_correct: vpl.

  Definition test_eq (te te': ZTerm.t): ZTerm.t :=
    if pomial_eq te te' 
    then te' 
    else failwith CERT "LinearizeOracleBug ? The two polynomial differs..." te.
  Extraction Inline assumeOpAnnot.

  Lemma test_eq_correct te te': 
     forall m, eval (test_eq te te') m = eval te m.
  Proof.
    unfold test_eq, failwith; xasimplify ltac:(eauto with vpl).
  Qed.
  Opaque test_eq.

  Fixpoint skip_oracle (te: ZTerm.t) : bool :=
   match te with
   | Annot SKIP_ORACLE _ => trace DEBUG "ORACLE SKIPPED !" true
   | Annot _ te => skip_oracle te
   | Opp te => skip_oracle te
   | _ => false
   end.

  Program Definition assumeOpFromOracle env sic lc cmp te aft: cdac 
   := G.cast 
      (G.bind (fun _ => oracle lc) (fun te0 =>
        if (skip_oracle te0) then
          skip
        else
          let te' := test_eq te te0 in
          (assumeOpAnnot env sic cmp te' aft))
        (* post oracle *)
        (fun _ m => True))
       (* cast in *)
       (°-| (fun m => isItvEnv env m /\ ZNum.cmpDenote cmp 0 (ZTerm.eval te m + ZAffTerm.eval aft m)))%MPP
  .
  Obligation 1.
    VPLAsimplify.
  Qed.
  Obligation 2.
    destruct (skip_oracle H); simpl in * |-; auto.
    rewrite test_eq_correct in * |-; intuition.
  Qed.
  Extraction Inline assumeOpFromOracle.

  (* in order to ensure a minimal precision, we ask systematically 
     a naive static intervalization on the original "te"
  *)
  Program Definition assumeOp2 env sic lc cmp te aft :=
   G.cast
    (G.seq (assumeOpCPS env true cmp (Annot INTERV te) aft)
           (assumeOpFromOracle env sic lc cmp te aft))
    (°-| (fun m => isItvEnv env m /\ ZNum.cmpDenote cmp 0 (ZTerm.eval te m + ZAffTerm.eval aft m)))%MPP.

  (** general wrapper for linearization *)
  Definition assumeOp sic cmp (te: ZTerm.t) (aft: ZAffTerm.t) (ti:ZTerm.t) (a:D.t) : imp D.t :=
        BIND mitv <- get_variables a te -;
        let env:=(mitv_find mitv) in
        let lc:={| nonaffine := te; env:=env; affine:=aft; cmp:=cmp; source:=ti |} in
        let te := trace DEBUG ("assumeOp.ti:"++(ZTerm.pr ti)) te in
        if skip_oracle te then
          (#(assumeOpAnnot env sic cmp te aft))%cdac a
        else
          (#(assumeOp2 env sic lc cmp te aft))%cdac a.

  Opaque impl.
  Lemma assumeOp_correct sic cmp te aft ti a:
      WHEN a' <- assumeOp sic cmp te aft ti a THEN 
      forall m, ZNum.cmpDenote cmp 0 (ZTerm.eval te m + ZAffTerm.eval aft m) -> gamma a m -> gamma a' m.
  Proof.
    unfold assumeOp, trace; simpl; xasimplify ltac:(eauto with vpl);
    simpl; intros X; intros; apply X; intuition.
  Qed.
  Local Hint Resolve assumeOp_correct: vpl.
  Local Opaque assumeOp.

  (** The general case *)
  Definition assume (c:ZAtomicCond.t) (a: D.t):  imp D.t :=
     let ti := right c in
     let (te,aft) := ZTerm.affineDecompose ti in
     if ZTerm.pseudoIsZero te then
       (* affine condition ! *)
       affAssume (cmpOp c) aft a
     else
       assumeOp false (cmpOp c) te aft ti a.

  Lemma assume_correct: forall c a, WHEN p <- assume c a THEN 
     forall m, ZAtomicCond.sat c m -> gamma a m -> gamma p m.
  Proof.
    unfold assume, sat; unfold trace; simpl; xasimplify ltac:(eauto with pedraQ vpl).
    - simpl in * |- *.
      intros X m; intros; apply X; auto.
      ZNum.cmp_simplify.
      rewrite <- ZTerm.affineDecompose_correct, H.
      ring.
    - simpl in * |- *.
      intros.
      rewrite <- ZTerm.affineDecompose_correct in * |- *.
      apply H0; auto.
  Qed.
  Global Opaque assume.
  Global Hint Resolve assume_correct: vpl.

  (* Systematic intervalization in dynamic mode ! 
     NB: this could be cheap and efficient if there is a few non-linear subterms
  *)
  Definition getItvMode mo te a :=
    intervalize (fun _ => ZNItv.top) false mo (annotAFFINE te) a.

  Extraction Inline getItvMode.

  Lemma getItvMode_correct mo t a:
      WHEN i <- getItvMode mo t a THEN forall m, gamma a m -> ZNItv.sat i (ZTerm.eval t m).
  Proof.
     unfold getItvMode. VPLAsimplify. 
     intros H m. generalize (H m); clear H.
     rewrite annotAFFINE_correct; unfold isItvEnv; simpl; auto with zn.
  Qed.

  Global Opaque getItvMode.
  Global Hint Resolve getItvMode_correct: vpl.

End ZAtomicCondAssume.

Close Scope impure.

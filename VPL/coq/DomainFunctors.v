Require Import AssignD.
Require Import ASAtomicCond.
Require Import String. 
Require Import List.
(**************************************************************************)
(* A generic functor to lift a "low-level" domain into a "high-level" one *)
Module MakeFull (N: NumSig) (Import Cond: ASCondSig N) (I: ItvSig N) 
                (AtomC: AtomicCondSig N Cond.Term)
                (Import D: BasicDomain N) (AtomD: HasAssume N AtomC D) (R: HasRename N D)
                (DI: HasGetItvMode N Cond.Term I D)
                (DP: HasSimplePrinting N D)
               <: FullItvAbstractDomain N Cond I with Definition rep := DP.rep.

  Module Dom <: AbstractDomain N Cond 
  := D <+ CondAssume N Cond AtomC D AtomD 
       <+ ASCondAssert N Cond.

  Include CoreAssign N Cond Dom R <+ AssignLiftItv N Cond I Dom R DI 
                                  <+ AssignSimplePrinting N Cond Dom R DP.

End MakeFull.


(*************************************************************************)
(* A generic functor to lift a "low-level" domain on Q into domains on Z *)

Require Import CstrC.
Require Import Itv.
Require Import ZNoneItv.
Require Import Impure.

Module MakeZ
 (D: BasicDomain QNum) 
 (QCstrD: HasAssume QNum Cstr D) 
 (QItvD: HasGetItvMode QNum QAffTerm QItv D)
 (R: HasRename QNum D)
 (DP: HasSimplePrinting QNum D)
 <: FullItvAbstractDomain ZNum ZCond ZNItv with Definition rep := DP.rep.

  Import LinTerm.
  Import ZNItv.

  Local Open Scope impure_scope.

  Module BasicD.

    Definition t:= D.t.

    Definition gamma (a:t) m
      := D.gamma a (Mem.lift ZtoQ.ofZ m).

     Instance gamma_ext: Proper (Logic.eq ==> pointwise_relation PVar.t Logic.eq ==> iff) gamma.
     Proof.
       unfold gamma.
       intros x y H m1 m2 H0. subst; rewrite H0; tauto.
     Qed.

     Definition isIncl:=D.isIncl.
     Global Opaque D.isIncl.

     Lemma isIncl_correct: forall a1 a2, If isIncl a1 a2 THEN forall m, gamma a1 m -> gamma a2 m.
     Proof.
       unfold gamma. VPLAsimplify.
     Qed.

     Definition top:= D.top.

     Lemma top_correct: forall m, gamma top m.
       unfold top, gamma; auto with vpl.
     Qed.
     Hint Resolve top_correct: vpl.

     Definition bottom: t := D.bottom.

     Lemma bottom_correct: forall m, ~(gamma bottom m).
     Proof.
       unfold bottom, gamma; eauto with vpl.
     Qed.

     Definition isBottom : t -> imp bool
       := fun p => D.isBottom p.

     Lemma isBottom_correct : forall a, If isBottom a THEN forall m, gamma a m -> False.
     Proof.
       unfold isBottom.
       unfold gamma.
       VPLAsimplify.
     Qed.

     Definition widen:= D.widen.

     Definition join:= D.join.

     Lemma join_correct a1 a2: WHEN p <- join a1 a2 THEN forall m, gamma a1 m \/ gamma a2 m -> gamma p m.
     Proof.
       unfold gamma; VPLAsimplify.
     Qed.

     Definition project (a:t) (x:PVar.t) : imp t :=
        D.project a x.

     Lemma project_correct: forall a x, WHEN p <- project a x THEN forall m v, gamma a m -> gamma p (Mem.assign x v m).
     Proof.
       unfold gamma. VPLAsimplify.
       simpl. intros; autorewrite with vpl; auto.
     Qed.

     Definition rename (x y: PVar.t) (a:t): imp t :=
       R.rename x y a.

     Lemma rename_correct: forall x y a, WHEN p <- (rename x y a) THEN
       forall m, gamma a (Mem.assign x (m y) m) -> gamma p m.
     Proof.
      unfold rename, gamma. VPLAsimplify.
      simpl; intros H m; autorewrite with vpl; auto.
     Qed.

     Definition pr: t -> String.string
       := fun ab => DP.pr ab.

     Definition to_string := DP.to_string.

     Definition rep := DP.rep.

     Definition backend_rep := DP.backend_rep.

     Definition backend_rep_correct := DP.backend_rep_correct.

     Definition meet := DP.meet.

     Lemma meet_correct a1 a2: WHEN p <- meet a1 a2 THEN forall m, gamma a1 m -> gamma a2 m -> gamma p m.
     Proof.
       unfold gamma; VPLAsimplify.
     Qed.

  End BasicD.

  Module ZNItvD<: HasGetItvMode ZNum ZTerm ZNoneItv.ZNItv BasicD.

     Import ZNum.
     Import BasicD.

     Definition getItvMode mo te (a:t) :=
        let (te,aft) := ZTerm.affineDecompose te in
        if ZTerm.pseudoIsZero te then
             BIND qitv <- QItvD.getItvMode mo (QAffTerm.lift aft) a -;
             pure (fromQItv qitv)
        else
            pure (failwith INTERN "get_itv: non-affine term"%string ZNItv.top).
     Extraction Inline getItvMode.

     Lemma getItvMode_correct mo t a:
        WHEN i <- getItvMode mo t a THEN forall m, gamma a m -> ZNItv.sat i (ZTerm.eval t m).
     Proof.
        unfold getItvMode.
        xasimplify ltac: (eauto with pedraQ vpl zn). simpl in * |- *.
        intros m X. 
        generalize (ZTerm.affineDecompose_correct t m).
        rewrite H. intros X0; ring_simplify in X0. rewrite <- X0.
        apply fromQItv_correct. 
        rewrite <- QAffTerm.lift_correct.
        auto.
     Qed.

    Global Hint Resolve getItvMode_correct: vpl.
    Global Opaque getItvMode.

   End ZNItvD.

  Module CstrD <: HasAssume ZNum ZtoQCstr BasicD.

      Import BasicD.

      Definition assume (c:ZtoQCstr.t) (a: t): imp t :=
        QCstrD.assume c a.

      Lemma assume_correct: forall c a, WHEN p <- assume c a THEN forall m, ZtoQCstr.sat c m -> gamma a m -> gamma p m.
      Proof.
        unfold gamma. VPLAsimplify.
      Qed.

   End CstrD.


  Module AtomicD := BasicD <+ ZAtomicCondAssume BasicD CstrD ZNItvD.

  Include MakeFull ZNum ZCond ZNItv ZAtomicCond AtomicD AtomicD AtomicD AtomicD AtomicD.

End MakeZ.

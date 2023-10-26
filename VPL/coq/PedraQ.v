(** This module implements the basic abstract domain of polyhedra
on atomic conditions over rationals.

It builds on [ConsSet] and adds to it the coupling with opaque
Ocaml polyhedra, operations on which serve as an oracle for
operations in [ConsSet]. It also adds the possibility for a
polyhedron to be empty. 

*)

Require Import List.
Require Import String.
Require CoqAddOn.
Require Import LinTerm.
Require Import ConsSet.
Require Import PedraQBackend.
Require Import Itv.
Require Import ASAtomicCond.
Require Export ASCond.
Require Import Debugging.
Require Export Impure.
Require DomainFunctors.
Require Import ArithRing Ring.

Open Scope impure.

Module BasicD <: BasicDomain QNum.

(** Coupling of a [ConsSet] with an opaque Ocaml polyhedron. *)
  Record polT: Type := mk {
    cons: Cs.t;
    ml: PedraQBackend.t
  }.

  Definition polPr: polT -> string
    := fun p =>
      CoqAddOn.sprintf "{coq:\n%s\nocaml:\n%s}"
      ((Cs.pr (cons p))::(PedraQBackend.pr (ml p))::nil).

  Definition pol_to_string f p: string
    := Cs.to_string f (cons p).

  Program Definition wrap (p: polT) : pedraCert (Cs.cstr (Cs.sat (cons p)))
  := {| lcf := Cs.certCstrLCF;
        backend := ml p;
        cert := Cs.wrap (cons p) |}.

  Definition polTop: polT
    := mk nil PedraQBackend.top.

(** Empty polyhedron is encoded as [None], 
    [Some p] encodes a non-empty polyhedron
*)
  Definition t:=option polT.

  Local Open Scope string_scope.
  Definition pr: t -> string
    := fun p =>
      match p with
        | None => "bot"
        | Some p' => "notbot " ++ (polPr p')
      end.

  Definition to_string f p: string :=
      match p with
        | None => "bot"
        | Some p' => "notbot " ++ (pol_to_string f p')
      end.

  Definition id (x: PVar.t):= x.

  Definition rep := PedraQBackend.t.

  Definition backend_rep p := 
     match p with 
     | None => None
     | Some p' => Some ((ml p'), (id, id))
     end.

  Lemma backend_rep_correct: 
     forall a, (WHEN r <- backend_rep a THEN forall x, (snd (snd r) (fst (snd r) x) = x))%option.
  Proof.
      VPLAsimplify.
  Qed.

  Definition gamma (a: t) (m: Mem.t QNum.t) :=
    (EXISTS p <- a SUCH Cs.sat (cons p) m)%option.

   Instance gamma_ext: Proper (Logic.eq ==> pointwise_relation PVar.t Logic.eq ==> iff) gamma.
   Proof.
     eapply sat_compat_iff; unfold gamma.
     intros x y H m1 m2 H0 H1. subst; PedraQsimplify. 
     erewrite (eval_pointwise_compat Cs.sat_mdo); eauto.
   Qed.

  Definition top: t
    := Some polTop.

  Lemma top_correct: forall m, gamma top m.
    simpl; auto.
  Qed.
  Hint Resolve top_correct: vpl.

  Definition my_assert  (mesg: string) (b: bool): bool :=
    if b then true else failwith CERT mesg false.
  Extraction Inline my_assert.

  Definition bottom: t := None.

  Lemma bottom_correct: forall m, ~(gamma bottom m).
  Proof.
    simpl; auto.
  Qed.

  Definition isBottom : t -> imp bool
    := fun p => 
          match p with
          | None => pure true
          | Some pol =>
               BIND isEmpty <- PedraQBackend.isEmpty (wrap pol) -;
               pure match isEmpty with
                     | None => false
                     | Some cert => my_assert "isBottom: not empty" (Cstr.isContrad (Cs.rep cert))
                     end
          end.

  Lemma isBottom_correct : forall a, If isBottom a THEN forall m, gamma a m -> False.
  Proof.
    unfold isBottom.
    xasimplify ltac:(eauto with pedraQ).
  Qed.

  Global Opaque isBottom.

  Definition isIncl (p1 p2:t) : imp bool
    :=  match p1 with
          | None => pure true
          | Some pol1 =>
            let wp1 := (wrap pol1) in
            match p2 with
              | None => 
                BIND isEmpty <- PedraQBackend.isEmpty wp1 -;
                pure match isEmpty with
                     | None => false
                     | Some cert => my_assert "isIncl: not empty (1)" (Cstr.isContrad (Cs.rep cert))
                     end
              | Some pol2 =>
                BIND isIncl <- PedraQBackend.isIncl (wp1, ml pol2) -;
                pure match isIncl with
                     | None => false
                     | Some (false,cert) => my_assert "isIncl: do not match" (Cs.isEq (Cs.unwrap cert) (cons pol2))
                     | Some (true,cert) => my_assert "isIncl: not empty (2)" (Cs.isContrad (Cs.unwrap cert))
                     end
            end
        end.

  Lemma isIncl_correct p1 p2: If isIncl p1 p2 THEN forall m, gamma p1 m -> gamma p2 m.
  Proof.
    unfold isIncl. xasimplify ltac:(eauto with pedraQ).
    intros; elimtype False; eauto with pedraQ.
  Qed.
  Hint Resolve isIncl_correct: vpl.
  Global Opaque isIncl.


  Definition join (p1 p2:t) : imp t := 
    match p1, p2 with
      | None, None => pure None
      | None, pol
      | pol, None => pure pol
      | Some pol1, Some pol2 =>
        BIND join <- PedraQBackend.join (wrap pol1, wrap pol2) -;
        pure 
          match join with
          | (shadow, (cert1, cert2)) =>
            Some (mk (Cs.join (cons pol1) (cons pol2) cert1 cert2) shadow)
          end
    end.

  Lemma join_correct p1 p2: WHEN p <- join p1 p2 THEN forall m, gamma p1 m \/ gamma p2 m -> gamma p m.
  Proof.
    unfold join; xasimplify ltac:(intuition eauto with pedraQ).
  Qed.
  Global Hint Resolve join_correct: vpl.

  Definition meet (p1 p2:t): imp t :=
    SOME p1' <- p1 -;
    SOME p2' <- p2 -;
    let (l1,l2) := Cs.wrap2 (cons p1') (cons p2') in
    let wp1 :=
     {| lcf := Cs.certCstrLCF;
        backend := ml p1';
        cert := l1 |} in
    BIND res0 <- PedraQBackend.meet (wp1, (ml p2', l2)) -;
    pure (
      let (opt, cert) := res0 in
      let res := Cs.unwrap cert in
      match opt with
        | None =>
          if Cs.isContrad res then 
            None
          else
            failwith CERT "PedraQ.meet" p1
        | Some p' => Some (mk res p')
      end).

  Lemma meet_correct p1 p2: WHEN p <- meet p1 p2 THEN forall m, gamma p1 m -> gamma p2 m -> gamma p m.
  Proof.
    unfold meet. xasimplify ltac:(eauto with pedraQ).
  Qed.

  Definition widen (p1 p2: t): imp t :=
    match p1, p2 with
      | None, None => pure None
      | None, p | p, None => pure p
      | Some pol1, Some pol2 =>
        BIND widen <- PedraQBackend.widen (ml pol1, ml pol2) -;
        let (cs, shadow) := widen in
          pure (Some (mk shadow cs))
    end.

  Definition project (p: t) (x: PVar.t): imp t
    := SOME p1 <- p -;
       BIND project <- PedraQBackend.project (wrap p1, x) -;
       pure (
         let (shadow, cert) := project in
         let res := Cs.unwrap cert in
           if Cs.isFree x res then
             Some (mk res shadow)
           else
             failwith CERT ("project: "++(PVar.pr x)++" not free in "++(Cs.pr res)) top).

  Lemma project_correct a x: WHEN p <- project a x THEN forall m v, gamma a m -> gamma p (Mem.assign x v m).
  Proof.
    unfold project; xasimplify ltac:(eauto with pedraQ).
    intros; erewrite (mdoExt_free Cs.sat_mdo); eauto with pedraQ progvar.
  Qed.
  Global Hint Resolve project_correct: vpl.

End BasicD.


Module LinItvD <: HasGetItvMode QNum LinQ QItv BasicD.

  Import BasicD.

  Definition buildLow (p: polT) (v: LinQ.t) (b: bndT (Cs.cstr (Cs.sat (cons p)))): QItv.bndT :=
      match b with
        | Infty => QItv.Infty
        | Open n c =>
            let c0 := Cstr.lowerToCstr v n in
            (* let c0 := trace DEBUG ("buildLow.O: " ++ (Cstr.pr c0)) c0 in *)
            if Cstr.isEq (Cs.rep c) c0 
            then QItv.Open n 
            else failwith CERT "PedraQ.buildLow.Open" QItv.Infty
        | Closed n c =>
            let c0 := Cstr.lowerOrEqualsToCstr v n in
            (* let c0 := trace DEBUG ("buildLow.C: " ++ (Cstr.pr c0)) c0 in *)
            if Cstr.isEq (Cs.rep c) c0
            then QItv.Closed n
            else failwith CERT "PedraQ.buildLow.Close" QItv.Infty
      end.

  Lemma buildLow_correct (p: polT) (v: LinQ.t) b m: 
    gamma (Some p) m -> QItv.satLower (buildLow p v b) (LinQ.eval v m).
  Proof.
    unfold buildLow; destruct b; simpl; auto; PedraQsimplify.
  Qed.

  Definition buildUp (p: polT) (v: LinQ.t) (b: bndT (Cs.cstr (Cs.sat (cons p)))): QItv.bndT :=
      match b with
        | Infty => QItv.Infty
        | Open n c =>
            let c0 := Cstr.upperToCstr v n in
            (* let c0 := trace DEBUG ("buildUp.O: " ++ (Cstr.pr c0)) c0 in *)
            if Cstr.isEq (Cs.rep c) c0 
            then QItv.Open n 
            else failwith CERT "PedraQ.buildUp.Open" QItv.Infty
        | Closed n c =>
            let c0 := Cstr.upperOrEqualsToCstr v n in
            (* let c0 := trace DEBUG ("buildUp.C: " ++ (Cstr.pr c0)) c0 in *)
            if Cstr.isEq (Cs.rep c) c0 
            then QItv.Closed n 
            else failwith CERT "PedraQ.buildUp.Close" QItv.Infty
      end.

  Lemma buildUp_correct (p: polT) (v: LinQ.t) b m: 
    gamma (Some p) m -> QItv.satUpper (buildUp p v b) (LinQ.eval v m).
  Proof.
    unfold buildUp; destruct b; simpl; auto; PedraQsimplify.
  Qed.

  (** wrapping "mk" function of QItv *)
  Definition getItv (p: t) (v: LinQ.t): imp QItv.t := 
    match p with
    | None => pure QItv.bot
    | Some pol =>
      BIND sItv <- PedraQBackend.getItv (wrap pol, v) -;
      let low := buildLow pol v (low sItv) in
      let up := buildUp pol v (up sItv) in
          pure (QItv.mk low up)
    end.

  Local Hint Resolve buildUp_correct buildLow_correct  QItv.mk_correct: pedraQ.

  Lemma getItv_correct (p: t) (v: LinQ.t):
    WHEN i <- getItv p v THEN forall m, gamma p m -> QItv.sat i (LinQ.eval v m).
  Proof.
    unfold getItv; xasimplify ltac: (eauto with pedraQ).
  Qed.
  Global Hint Resolve getItv_correct: pedraQ.

  Definition getLowerBound : t -> LinQ.t -> imp QItv.bndT
    := fun p v =>
         match p with
           | None => failwith CERT "PedraQ.ItvD.getLowerBound" (pure QItv.Infty)
           | Some pol =>
             BIND b <- PedraQBackend.getLowerBound (wrap pol, v) -;
                  pure (buildLow pol v b)
         end.

  Lemma getLowerBound_correct (p : t) (v : LinQ.t) :
    WHEN b <- getLowerBound p v THEN forall m, gamma p m -> QItv.satLower b (LinQ.eval v m).
  Proof.
    unfold getLowerBound; xasimplify ltac: (eauto with pedraQ).
  Qed.

  Definition getUpperBound : t -> LinQ.t -> imp QItv.bndT
    := fun p v =>
         match p with
           | None => failwith CERT "PedraQ.ItvD.getUpperBound" (pure QItv.Infty)
           | Some pol =>
             BIND b <- PedraQBackend.getUpperBound (wrap pol, v) -;
                  pure (buildUp pol v b)
         end.

  Lemma getUpperBound_correct (p : t) (v : LinQ.t) :
    WHEN b <- getUpperBound p v THEN forall m, gamma p m -> QItv.satUpper b (LinQ.eval v m).
  Proof.
    unfold getUpperBound; xasimplify ltac: (eauto with pedraQ).
  Qed.
  Hint Resolve getUpperBound_correct getLowerBound_correct: pedraQ.

  Definition getItvMode mo (v: LinQ.t) (p:t): imp QItv.t :=
    match mo with
    | BOTH => getItv p v
    | UP => BIND b <- getUpperBound p v -;
            pure (QItv.mk QItv.Infty b)
    | LOW => BIND b <- getLowerBound p v -;
            pure (QItv.mk b QItv.Infty)
    end.
  Extraction Inline getItvMode.

  Lemma getItvMode_correct mo v p:
    WHEN i <- (getItvMode mo v p) THEN
      forall m, gamma p m -> QItv.sat i (LinQ.eval v m). 
  Proof.
    unfold getItvMode; destruct mo; xasimplify ltac: (eauto with pedraQ);
    simpl in * |- *; intros; eapply QItv.mk_correct; simpl; eauto.
  Qed.
  Hint Resolve getItvMode_correct: vpl.

End LinItvD.


Module AffItvD <: HasGetItvMode QNum QAffTerm QItv BasicD.

     Import BasicD.
     Import LinItvD.

     Definition getItvMode mo aft (a:t) :=
       BIND qitv <- getItvMode mo (QAffTerm.lin aft) a -;
       pure (QItv.shift qitv (QAffTerm.cte aft)).

     Lemma getItvMode_correct mo t a:
        WHEN i <- getItvMode mo t a THEN forall m, gamma a m -> QItv.sat i (QAffTerm.eval t m).
     Proof.
        unfold getItvMode. VPLAsimplify.
        intros; unfold QAffTerm.eval. 
        rewrite QNum.AddComm.
        apply QItv.shift_correct.
        auto.
     Qed.

    Global Hint Resolve getItvMode_correct: vpl.
    Global Opaque getItvMode.

End AffItvD.


Module ItvD <: HasGetItvMode QNum QTerm QItv BasicD.

     Import BasicD.
     Import AffItvD.

     Definition getItvMode mo te (a:t) :=
        let (te,aft) := QTerm.affineDecompose te in
        if QTerm.pseudoIsZero te then
             getItvMode mo aft a
        else
            pure (failwith INTERN "getItvMode: non-affine term" QItv.top).
     Extraction Inline getItvMode.

     Local Hint Resolve QItv.top_correct.
     Import QNum.

     Lemma getItvMode_correct mo t a:
        WHEN i <- getItvMode mo t a THEN forall m, gamma a m -> QItv.sat i (QTerm.eval t m).
     Proof.
        unfold getItvMode, failwith.
        xasimplify ltac:(eauto with pedraQ vpl); simpl in * |- *.
        intros H0 m X. generalize (QTerm.affineDecompose_correct t m).
        rewrite H. intros X0; ring_simplify in X0. rewrite <- X0.
        auto.
     Qed.

    Global Hint Resolve getItvMode_correct: vpl.
    Global Opaque getItvMode.

    Definition get_itv:= getItvMode BOTH.

    Lemma get_itv_correct t a:
      WHEN i <- get_itv t a THEN forall m, gamma a m -> QItv.sat i (QTerm.eval t m).
    Proof.
      unfold get_itv; VPLAsimplify.
    Qed.

    Hint Resolve get_itv_correct: vpl.

End ItvD.


Module CstrD <: HasAssume QNum Cstr BasicD.

  Import BasicD.

  Definition assume (c: Cstr.t) (p: t): imp t :=
    SOME p1 <- p -;
    let p1 := trace DEBUG ("assume input:" ++ (polPr p1) ++ " /\ " ++ (Cstr.pr c)) p1 in
    let l := Cs.wrap2 (cons p1) (c::nil) in
    let wp1 :=
     {| lcf := Cs.certCstrLCF;
        backend := ml p1;
        cert := fst l |} in
    BIND aux <- PedraQBackend.add (wp1, snd l) -;
    pure (let (opt, cert) := aux in
      let res := Cs.unwrap cert in
      match opt with
        | None =>
          if Cs.isContrad res then 
            None
          else
            failwith CERT "CstrD.assume" p
        | Some p' => Some (mk res p')
      end).

  Lemma assume_correct: forall c a, WHEN p <- assume c a THEN forall m, Cstr.sat c m -> gamma a m -> gamma p m.
  Proof.
    unfold assume, trace, failwith. xasimplify ltac:(eauto with pedraQ).
    - destruct exta; simpl in * |- *.
      apply Cs.unwrap_correct. unfold Cs.sat2. simpl; intuition.
    - destruct exta; simpl in * |- *.
      subst; intros X; eapply X.
      eapply Cs.unwrap_correct. unfold Cs.sat2. simpl; intuition eauto.
  Qed.

  Global Opaque assume.
  Global Hint Resolve assume_correct: vpl.

End CstrD.


(* implementation of rename *)
Module Rename <: HasRename QNum BasicD.

  Import BasicD.

  Definition rename (x y: PVar.t) (a:t) : imp t :=
  SOME p <- a -;
  BIND aux <- PedraQBackend.rename (x,y,ml p) -;
  pure (Some {| cons := Cs.rename x y (cons p) ; ml := aux |}).

  Lemma rename_correct: forall x y a, WHEN p <- (rename x y a) THEN
    forall m, gamma a (Mem.assign x (m y) m) -> gamma p m.
  Proof.
    unfold Basics.impl, rename.
    intros; xasimplify idtac.
    intros; rewrite Cs.rename_correct.
    auto.
  Qed. 
  Global Hint Resolve rename_correct: vpl.

End Rename.

Require Map_poly.
Require Ring_polynom_AddOnQ.
Require Qop.

Module QAtomicCondAssume <: HasAssume QNum QAtomicCond BasicD.


  Import QAffTerm.
  Import QAtomicCond.
  Import BasicD.

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
          BasicD.join a1 a2
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

  Import Map_poly.
  Import Qop.

  Definition applyHandelman_one (cmp : cmpG) (qt:QTerm.t) (pol : polT) (a : t) (cert : Handelman_compute.certif) :  imp t :=
    let aff := Handelman_compute.eq_witness pol.(cons) cert qt in
      affAssume cmp aff a.
  
  Import Ring_polynom_AddOnQ.
  
  Lemma Handelman_pos_le (m : Mem.t QNum.t) (g : QTerm.t) (P : Cs.t) (cert : Handelman_compute.certif) :
    Cs.sat P m  ->
    0 <= QTerm.eval g m ->
    0 <= eval (Handelman_compute.eq_witness P cert g) m.
  Proof.
    intros SAT POS.
    apply Handelman_compute.eq_witness_pos.
    assumption.
    rewrite Handelman_compute.QPom.toPExpr_correct in POS.
    rewrite <- QOp.to_PExpr_compat_pos.
    assumption.
  Qed.

  Lemma applyHandelman_one_correct_le: forall qt pol cert, 
    WHEN p <- applyHandelman_one Le qt pol (Some pol) cert THEN 
    forall m, QAtomicCond.sat {| cmpOp := Le ; right := qt |} m -> gamma (Some pol) m -> gamma p m.
  Proof.
    unfold applyHandelman_one, sat ; xasimplify ltac:(eauto with pedraQ vpl).
    intros X m ; intros ; apply X ; auto.
    apply Handelman_pos_le; assumption.
  Qed. 
  Local Hint Resolve applyHandelman_one_correct_le: vpl.
  Opaque applyHandelman_one_correct_le.

  Lemma Handelman_pos_lt (m : Mem.t QNum.t) (g : QTerm.t) (P : Cs.t) (cert : Handelman_compute.certif) :
    Cs.sat P m  ->
    0 < QTerm.eval g m ->
    0 < eval (Handelman_compute.eq_witness P cert g) m.
  Proof.
    intros SAT POS.
    apply Handelman_compute.eq_witness_pos_strict.
    assumption.
    rewrite Handelman_compute.QPom.toPExpr_correct in POS.
    rewrite <- QOp.to_PExpr_compat_pos_strict.
    assumption.
  Qed.

  Lemma applyHandelman_one_correct_lt: forall qt pol cert, 
    WHEN p <- applyHandelman_one Lt qt pol (Some pol) cert THEN 
    forall m, QAtomicCond.sat {| cmpOp := Lt ; right := qt |} m -> gamma (Some pol) m -> gamma p m.
  Proof.
    unfold applyHandelman_one, sat ; xasimplify ltac:(eauto with pedraQ vpl).
    intros X m ; intros ; apply X ; auto.
    
    apply Handelman_pos_lt; assumption.
  Qed. 
  Local Hint Resolve applyHandelman_one_correct_lt: vpl.
  Opaque applyHandelman_one_correct_lt.

  Open Scope list_scope.
  Import Datatypes.
  Import List.ListNotations.

  Definition f (cmp : cmpG) (qt:QTerm.t) (pol: polT) (cert : Handelman_compute.certif) (a: imp t) : imp t :=
   BIND a1 <- a -;
   applyHandelman_one cmp qt pol a1 cert.

  Definition applyHandelman (cmp : cmpG) (qt:QTerm.t) (pol: polT) (certs : list Handelman_compute.certif) : imp t :=    
    fold_right (f cmp qt pol) (pure (Some (pol))) certs.

  Lemma applyHandelman_correct_le: forall qt certs pol,
    WHEN p <- applyHandelman Le qt pol certs THEN 
    forall m, QAtomicCond.sat {| cmpOp := Le ; right := qt |} m -> gamma (Some pol) m -> gamma p m.
  Proof.
    unfold applyHandelman, sat. simpl.
    induction certs.
    xasimplify ltac:(eauto with pedraQ vpl).
    intros. simpl.
    xasimplify ltac:(eauto with pedraQ vpl).
    intuition. apply H0; intuition.
    apply Handelman_pos_le; auto.
  Qed.
  
  Local Hint Resolve applyHandelman_correct_le: vpl.
  Opaque applyHandelman_correct_le.

  Lemma applyHandelman_correct_lt: forall qt certs pol,
    WHEN p <- applyHandelman NumC.Lt qt pol certs THEN 
    forall m, QAtomicCond.sat {| cmpOp := NumC.Lt ; right := qt |} m -> gamma (Some pol) m -> gamma p m.
  Proof.
    unfold applyHandelman, sat. simpl.
    induction certs.
    xasimplify ltac:(eauto with pedraQ vpl).
    intros. simpl.
    xasimplify ltac:(eauto with pedraQ vpl).
    intuition. apply H0; intuition.
    apply Handelman_pos_lt; auto.
  Qed.
  Local Hint Resolve applyHandelman_correct_lt: vpl.
  Opaque applyHandelman_correct_lt.

  Definition assume_eq (qt : QTerm.t) (pol : polT) : imp t :=
    let opp := QTerm.Opp qt in
    BIND a1 <- applyHandelman Le qt pol (LinearizeBackend.handelman_oracle pol.(ml) Le qt) -;
    BIND a2 <- applyHandelman Le opp pol (LinearizeBackend.handelman_oracle pol.(ml) Le opp) -;
    BasicD.meet a1 a2.

  Lemma assume_eq_correct: 
  forall qt pol, WHEN p <- assume_eq qt pol THEN 
  forall m, QAtomicCond.sat {| cmpOp := NumC.Eq ; right := qt |} m -> gamma (Some pol) m -> gamma p m.
  Proof.
    unfold assume_eq, sat.
    VPLAsimplify.
    intros.
    apply (meet_correct exta exta0);auto.
    - apply H; unfold sat, QNum.cmpDenote ; simpl.
      rewrite H1.
      intuition.
      assumption.
    - apply H0; unfold sat, QNum.cmpDenote ; simpl.
      unfold QNum.opp. rewrite <- H1.
      intuition.
      assumption.
  Qed.

  Definition assume_neq (qt : QTerm.t) (pol : polT) : imp t :=
    let opp := QTerm.Opp qt in
    BIND a1 <- applyHandelman NumC.Lt qt pol (LinearizeBackend.handelman_oracle pol.(ml) NumC.Lt qt) -;
    BIND a2 <- applyHandelman NumC.Lt opp pol (LinearizeBackend.handelman_oracle pol.(ml) NumC.Lt opp) -;
    BasicD.join a1 a2.
  
  Lemma assume_neq_correct: 
  forall qt pol, WHEN p <- assume_neq qt pol THEN 
  forall m, QAtomicCond.sat {| cmpOp := Neq ; right := qt |} m -> gamma (Some pol) m -> gamma p m.
  Proof.
    unfold assume_neq, sat.
    VPLAsimplify.
    intros.
    apply (join_correct exta exta0);auto.
    destruct (neq_join _ _ H2);
    [ constructor 1; apply H | constructor 2; apply H0]; 
      try (rewrite toCstr_correct; simpl); 
      auto.
      unfold sat ; simpl.
      rewrite <- QNum.OppZ.  
      rewrite <- QNum.OppLt. auto.
  Qed.

   Definition assume (c:QAtomicCond.t) (a: t):  imp t :=
   let ti := right c in
   let (te,aft) := QTerm.affineDecompose ti in
   if QTerm.pseudoIsZero te then
     (* affine condition ! *)
     affAssume (cmpOp c) aft a
   else
      match a with
      | None => pure None
      | Some pol =>
        match (cmpOp c) with
        | NumC.Eq => assume_eq ti pol
        | Neq => assume_neq ti pol
        | _ => applyHandelman (cmpOp c) ti pol (LinearizeBackend.handelman_oracle pol.(ml) (cmpOp c) ti)
        end
      end. 
  
  Add Ring QRing: QNum.Ring.
  Lemma assume_correct: forall c a, WHEN p <- assume c a THEN 
     forall m, QAtomicCond.sat c m -> gamma a m -> gamma p m.
  Proof.
    unfold assume, sat; xasimplify ltac:(eauto with pedraQ vpl).
    - intros X m; intros; apply X; auto.
    QNum.cmp_simplify.
    rewrite <- QTerm.affineDecompose_correct, H.
    ring.
    - destruct (cmpOp c).
      (* Case Eq *)
      -- intros m EQ SAT.
      apply (assume_eq_correct (right c) a0 _ Hexta) ; simpl; auto.
      (* Case Leq *)
      -- intros m H0 H1.
      apply (applyHandelman_correct_le (right c) _ _ _ Hexta) ; simpl; auto.
      (* Case Lt *)
      -- intros m H0 H1.
       apply (applyHandelman_correct_lt (right c) _ _ _ Hexta) ; simpl; auto.
       (* Case Neq *)
      -- intros m NEQ SAT.
      apply (assume_neq_correct (right c) a0 _ Hexta) ; simpl; auto.
  Qed. 
    
End QAtomicCondAssume.

(* Gluing all this together *)

Module AtomicD := BasicD <+ QAtomicCondAssume.

Module FullDom <: FullItvAbstractDomain QNum QCond QItv
 := DomainFunctors.MakeFull QNum QCond QItv QAtomicCond
                  AtomicD AtomicD Rename ItvD AtomicD.
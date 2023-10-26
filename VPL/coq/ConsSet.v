Require Import String.
Require Import List.
Require Export NumC.
Require Export ProgVar.
Require Export CstrC.
Require Import CstrLCF.
Require Import Debugging.
Require Import OptionMonad.


Module CsImpl(Cstr: CstrSig).

  (* A first representation of Polyhedra as list of constraints *)

  Definition t := list Cstr.t.

  Definition pr: t -> string
    := fun cs => CoqAddOn.concat CoqAddOn.nl (List.map Cstr.pr cs).

  Definition to_string (f: PVar.t -> string) (cs: t): string
    := CoqAddOn.concat CoqAddOn.nl (List.map (Cstr.to_string f) cs).

  Fixpoint sat (l: t) m: Prop :=
    match l with
      | nil => True
      | c::l' => Cstr.sat c m  /\ sat l' m
    end.

  Fixpoint mayDependOn (l: t) (x: PVar.t) : Prop :=
    match l with
      | nil => False
      | c::l' => Cstr.mayDependOn c x \/  mayDependOn l' x
    end.

  Lemma sat_mdo: mdoExt mayDependOn sat Logic.eq.
  Proof.
    unfold mdoExt, bExt; induction e; simpl; try tauto.
    intros m1 m2 H; erewrite IHe; eauto.
    erewrite Cstr.sat_mdo; intuition eauto.
  Qed.

  Definition Incl (l1 l2: t): Prop
    := forall m, sat l1 m -> sat l2 m.
  Local Hint Unfold Incl: pedraQ. 

  Lemma InclTrans: forall l1 l2 l3, Incl l1 l2 -> Incl l2 l3 -> Incl l1 l3.
  Proof.
    unfold Incl; eauto.
  Qed.

  Lemma InclFold l1 l2 m: Incl l1 l2 -> sat l1 m -> sat l2 m.
  Proof.
    unfold Incl; auto.
  Qed.
  Hint Resolve InclFold: pedraQ.

  Fixpoint isEq (l1 l2: t): bool :=
    match l1, l2 with
      | nil, nil => true
      | c1::l1', c2::l2' =>
        Cstr.isEq c1 c2 
        &&& isEq l1' l2'
      | _, _ => false
    end.

  Lemma isEq_correct l1: forall l2, If isEq l1 l2 THEN Incl l1 l2.
  Proof.
    unfold Incl; induction l1; simpl; auto;
    destruct l2; simpl; auto with pedraQ.
    PedraQsimplify.
    intuition eauto with pedraQ.
  Qed.
  Hint Resolve isEq_correct: pedraQ.

  Definition isContrad (l: t): bool :=
  match l with
  | c::nil => Cstr.isContrad c
  | _ => failwith CERT "isContrad expects a singleton" false
  end.

  Lemma isContrad_correct l: If isContrad l THEN forall m, (sat l m)->False.
  Proof.
    destruct l; simpl; auto. destruct l; simpl; auto. 
    xsimplify ltac:(intuition eauto with pedraQ). 
  Qed.
  Global Opaque isContrad. 
  Hint Resolve isContrad_correct: pedraQ.


  Fixpoint isFree (x: PVar.t) (l: t): bool :=
    match l with
      | nil => true
      | c::cs' => Cstr.isFree x c &&& isFree x cs'
    end.

  Lemma isFree_correct x cs: If (isFree x cs) THEN ~(mayDependOn cs x).
  Proof.
    induction cs; simpl; PedraQsimplify. auto.
  Qed.
  Hint Resolve isFree_correct: pedraQ.

  Fixpoint rename (x y: PVar.t) (cs: t): t :=
    match cs with
      | nil => nil
      | c::cs' => (Cstr.rename x y c)::(rename x y cs')
    end.

  Lemma rename_correct (x y:PVar.t) (cs: list Cstr.t) m: 
    (sat (rename x y cs) m)=(sat cs (Mem.assign x (m y) m)).
  Proof.
    induction cs; simpl; auto.
    rewrite Cstr.rename_correct. congruence.
  Qed.

  (*** Building the LCF ***)

  Record cstr (mod: Mem.t QNum.t -> Prop): Type :=
  {
    rep:> Cstr.t;
    rep_sat: forall m, (mod m) -> (Cstr.sat rep m);
  }.
  Arguments rep [mod]. 

  Hint Resolve rep_sat: pedraQ.

  Section CstrLCFImplem.

  Variable mod: Mem.t QNum.t -> Prop.

  Program Definition m_top: cstr mod := {| rep := Cstr.top |}.
  Obligation 1.
   auto with pedraQ.
  Qed.

  Program Definition m_triv (typ: cmpT) (coeff: QNum.t): cstr mod 
  := {| rep := Cstr.triv typ coeff |}.
  Obligation 1.
    auto with pedraQ.
  Qed.

  Program Definition m_add (c1 c2: cstr mod): cstr mod 
  := {| rep := Cstr.add c1 c2 |}.
  Obligation 1.
    auto with pedraQ.
  Qed.

  Program Definition m_mul (coeff: QNum.t) (c: cstr mod): cstr mod 
  := {| rep := Cstr.mul coeff c |}.
  Obligation 1.
    auto with pedraQ.
  Qed.

  Program Definition m_to_le (c: cstr mod): cstr mod 
  := {| rep := Cstr.to_le c |}.
  Obligation 1.
    auto with pedraQ.
  Qed.

  Program Definition m_merge (c1 c2: cstr mod): cstr mod 
   := {| rep := Cstr.merge (rep c1) (rep c2) |}.
  Obligation 1.
    auto with pedraQ.
  Qed.

  Definition certCstrLCF : cstrLCF Cstr.t (cstr mod)
   := {|
         export := fun c => rep c;
         top := m_top;
         triv := m_triv;
         add := m_add;  
         mul := m_mul;
         (* split := m_split; *)
         merge := m_merge;
         to_le := m_to_le
      |}.

  Program Fixpoint x_unwrap (l: list (cstr mod)) (acc: t | forall m, mod m -> sat acc m): { r: t | forall m, mod m -> sat r m} :=
  match l with
  | nil => acc
  | c::l' => x_unwrap l' ((rep c)::acc)
  end.
  Obligation 1.
    simpl in * |- *. firstorder. intuition.
  Qed.

  Program Definition unwrap (l: list (cstr mod)): t :=
   x_unwrap l nil.

  Lemma unwrap_correct l m: mod m -> sat (unwrap l) m.
  Proof.
    unfold unwrap. intro s.
    match goal with
    | |- (sat (proj1_sig ?r) m) => destruct r; simpl
    end.
    auto.
  Qed.

  End CstrLCFImplem.

  Arguments certCstrLCF {mod}.
  Arguments unwrap [mod].
  Hint Resolve unwrap_correct: pedraQ.

  Definition join (l1 l2: t) (cert1: list (cstr (sat l1))) (cert2: list (cstr (sat l2))): t :=
  let res := unwrap cert1 in
  if isEq (unwrap cert2) res  
  then res
  else failwith CERT "join: both sides do not match" nil.

  Lemma join_correct1 l1 l2 cert1 cert2: forall m, sat l1 m -> sat (join l1 l2 cert1 cert2) m.
  Proof.
    unfold join; PedraQsimplify.
  Qed.
  Hint Resolve join_correct1: pedraQ.

  Lemma join_correct2 l1 l2 cert1 cert2: forall m, sat l2 m -> sat (join l1 l2 cert1 cert2) m.
  Proof.
    unfold join.  PedraQsimplify.
  Qed.
  Hint Resolve join_correct2: pedraQ.

  Program Fixpoint x_wrap (l: t) (mod: Mem.t QNum.t -> Prop) (H:forall m, mod m -> sat l m) (acc: list (cstr mod)): list (cstr mod) :=
  match l with
  | nil => acc
  | c::l' => x_wrap l' mod _ ({| rep := c |}::acc)
  end.
  Obligation 1.
    simpl in * |- *. firstorder.
  Qed.
  Obligation 2.
    simpl in * |- *. firstorder.
  Qed.

  Program Definition wrap (l: t): list (cstr (sat l)) :=
   x_wrap l _ _ nil.

  Definition sat2 (l1 l2:t) m: Prop := (sat l1 m) /\ (sat l2 m).

  Program Definition wrap2 (l1 l2: t): list (cstr (sat2 l1 l2)) * list (cstr (sat2 l1 l2)) :=
   (x_wrap l1 _ _ nil, x_wrap l2 _ _ nil).
  Obligation 1.
   unfold sat2 in * |-; intuition.
  Qed.
  Obligation 2.
   unfold sat2 in * |-; intuition.
  Qed.
  
  (* Ajout pour Handelman *)
  Definition geti (i:nat) (l:t) (d:Cstr.t) : Cstr.t :=
  (nth i l d).
  
  Lemma sat_forall : forall P:t, forall d x:Cstr.t, forall mem: Mem.t QNum.t,
  sat P mem -> In x P -> Cstr.sat x mem.
  Proof.
    intros.
    induction P.
    - simpl in *.
      contradiction H0. 
    - simpl in *.
      intuition.
      subst. assumption.
  Qed.
  
  Lemma sat_compat : forall P:t, forall d:Cstr.t, forall mem: Mem.t QNum.t,
   sat P mem -> forall i:nat, Peano.lt i (length P) -> Cstr.sat (geti i P d) mem.
  Proof.
    intros.
    unfold geti.
    apply (sat_forall P d (nth i P d) mem).
    assumption.
    apply nth_In.
    assumption.
  Qed.

  Definition default : Cstr.t := Cstr.top.
  (* Fin ajout pour Handelman *)

  Global Hint Unfold sat2: pedraQ.

End CsImpl.

(*Module Cs := CsImpl Cstr.*)
Module Cs.
  Include CsImpl Cstr.
  
  (* Ajout pour Handelman *)
  Require Import QArith.
  Require Import Ring_polynom_AddOnQ.
  Require Import Qop.
  Definition mem_compat (m:Mem.t QNum.t) (p:positive) : Q :=
  QNum.to_Q (m (p)).
  
  Lemma to_PExpr_compat : forall c : LinQ.t, forall mem : Mem.t QNum.t,
  Qcanon.Q2Qc (PEsem (LinQ.to_PExpr c) (mem_compat mem)) = LinQ.eval c mem.
  Proof.
    intros c mem.
    unfold LinQ.to_PExpr.
    rewrite LinQ.export_correct.
    unfold LinQ.absEval.
    apply LinQ.exportT_prop.
  Qed.
  
  Lemma Qminus_opp : forall q1 q2 : Q,
  q1 <= q2 -> 0 <= q2 - q1.
  Proof. 
    intros q1 q2 LEQ.
    assert (0 <= q2 +- q1) by (apply (Qle_minus_iff q1 q2);assumption).
    auto.
  Qed.

  Lemma sem_compat_default : forall i:nat, forall P:t, forall mem: Mem.t QNum.t,
  sat P mem -> 0%Q <= (PEsem (Cstr.to_PExpr (geti i P default)) (mem_compat mem)).
  Proof.
    intros i P mem sat.
    Open Scope nat_scope.
    assert (DEC : {(length P) <= i} + {i < (length P)}) by apply le_lt_dec.
    elim DEC.
    - intro LE.
      unfold geti.
      rewrite nth_overflow ; auto.
      simpl.
      intuition.
    - intro LT. 
      assert (Csat : Cstr.sat (geti i P default) mem) by (apply sat_compat;assumption).
      assert (compat : Qcanon.Q2Qc (PEsem (LinQ.to_PExpr (Cstr.coefs (geti i P default))) (mem_compat mem)) = LinQ.eval (Cstr.coefs (geti i P default)) mem) 
      by apply to_PExpr_compat.
      apply QOp.to_PExpr_compat_pos.
      unfold Cstr.sat in Csat.
      simpl.
      rewrite QOp.Qcanon_minus_Q2Qc.
      rewrite compat. 
      apply <- QOp.to_PExpr_compat_pos.
      unfold QNum.cmpDenote in Csat.
    
      rewrite QOp.Qcanon_opp_compat.
      apply Qminus_opp.
      unfold QNum.to_Q.
      simpl.
      rewrite Qred_correct.
      destruct (Cstr.typ (geti i P default));
      simpl in Csat.
      -- rewrite Csat.
        apply Qle_refl.
      -- rewrite <- QOp.QNum_to_Q_le_compat.
        assumption.
      -- apply QOp.QNum_to_Q_lt_compat.
        assumption.
  Qed.

End Cs.


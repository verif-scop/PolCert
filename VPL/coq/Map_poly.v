Require Import Ring_polynom_AddOnQ.
Require Import NArith.
Require Import QArith.
Require Import OrderedType.
Require Import CIndex.
Require Import ASTerm.
Require Import Qpower.
Require Import Qop.
Require Import Lia.

Require Import FMapAVL.
Require Import ConsSet.
Require Import String.
Require Import List.

Module M := FMapAVL.Make(CIndex.NatIndex).

(* 2*N represents the real exponent *)
Definition squares : Type := list (PExpr * N).

Definition compute_squares (s : squares) : PExpr := 
  fold_right 
    (fun s res => let '(p,n) := s in PEmul res (PEpow p (2 * n))) 
    (PEc 1%Q) s.

Module MapPoly.
  Local Open Scope list_scope.
  Import List.ListNotations.

  Definition t := M.t PExpr.

  Definition indexi (i n :nat) : list nat:= 
  map (fun j => if Nat.eq_dec i j then 1%nat else 0%nat) (seq 0 n).

  Local Open Scope nat_scope.

  Fixpoint init_rec (i:nat) (l:Cs.t) (d:Cstr.t) : t :=
  match i with
  | 0 => M.empty PExpr
  | S p => M.add (indexi p (length l)) (Cstr.to_PExpr (Cs.geti p l d)) (init_rec p l d)
  end.
 
  Definition init (l:Cs.t) (d:Cstr.t) : t :=
  init_rec (length l) l d.
  
  Lemma mapsto_add_compat: forall x:M.key, forall p e : PExpr, forall m : t,
  M.MapsTo x p (M.add x e m) -> e = p.
  Proof.
    intros x p e m map.
    assert (M.MapsTo x e (M.add x e m)).
    apply M.add_1.
    apply CIndex.NatIndex.eq_refl.
    assert (M.find x (M.add x e m) = M.find x (M.add x e m)).
    reflexivity.
    assert (M.find x (M.add x e m) = Some p).
    apply M.find_1.
    assumption.
    rewrite H1 in H0 at 1.
    assert (M.find x (M.add x e m) = Some e).
    apply M.find_1.
    assumption.
    rewrite H2 in H0.
    inversion H0.
    reflexivity.
  Qed.

  (* Ce résultat est trop fort et est probablement inutile *)
  Lemma maps_to_compat : forall P : Cs.t, forall k:M.key, forall p:PExpr, forall d:Cstr.t,
  M.MapsTo k p (init P d) -> exists i:nat, Peano.lt i (length P) /\ (Cstr.to_PExpr (Cs.geti i P d)) = p.
  Proof.
    intros P k p d map.
    unfold init in map.
    induction (length P).
    simpl in *.
    - assert (not_map : ~ M.MapsTo k p (M.empty PExpr)).
      apply (M.empty_1).
      contradiction not_map.
    - simpl in *.
      assert (EQdec : {CIndex.NatIndex.eq (indexi n (length P)) k} + {~CIndex.NatIndex.eq (indexi n (length P)) k}).
      apply CIndex.NatIndex.eq_dec.
      elim EQdec; clear EQdec.
      intro EQ.
      exists n.
      split.
      lia.
      assert (M.MapsTo (indexi n (length P)) p
        (M.add (indexi n (length P)) (Cstr.to_PExpr (Cs.geti n P d))
           (init_rec n P d))). 
      apply M.MapsTo_1 with (x := k).
      apply CIndex.NatIndex.eq_sym. assumption.
      assumption.
      
        
      apply (mapsto_add_compat (indexi n (length P)) _ _ (init_rec n P d)).
      assumption.
 
      intro NEQ.
      assert(Ex : exists i : nat, i < n /\ Cstr.to_PExpr (Cs.geti i P d) = p).
      apply IHn.
      apply (M.add_3) with (x := indexi n (length P)) (e' := Cstr.to_PExpr (Cs.geti n P d)).
      unfold CIndex.NatIndex.eq in NEQ.
      assumption.
      assumption.
      elim Ex.
      intros i and.
      elim and.
      intros LT EQ.
      exists i.
      split.
      lia.
      assumption.
    Qed.
  
  Close Scope nat_scope.

  Lemma init_pos : forall P : Cs.t, forall k:M.key, forall p:PExpr, forall mem: Mem.t QNum.t,
  Cs.sat P mem -> M.MapsTo k p (init P Cs.default) -> 0%Q <= PEsem p (Cs.mem_compat mem).
  Proof.
    intros P k p mem sat map.
    assert (EX : exists i:nat, Peano.lt i (length P) /\ (Cstr.to_PExpr (Cs.geti i P Cs.default)) = p).
    apply (maps_to_compat P k p Cs.default);assumption.
    elim EX.
    intros i and.
    elim and. clear and.
    intros len EQ.
    assert (POS:0%Q <= (PEsem (Cstr.to_PExpr (Cs.geti i P Cs.default)) (Cs.mem_compat mem))).
    apply Cs.sem_compat_default;assumption.
    rewrite <- EQ.
    assumption.
  Qed.

  Record ind_cons : Type:= mk {
      ind: CIndex.NatIndex.t;
      cons: list CIndex.NatIndex.t}.
  
  Definition buildOrder : Type := list ind_cons.
  
  Lemma le_0_1 : 0 <= 1.
  Proof. intuition. Qed.
  
  Lemma lt_0_1 : 0 < 1.
  Proof. intuition. Qed.

  Definition find_or_1 (i : CIndex.NatIndex.t) (m : t) : PExpr :=
  match M.find i m with
  | Some p => p
  | _ => failwith CERT "find_or_1: element not found in map"%string (PEc 1%Q)
  end.

  Definition cons_rec (l : list CIndex.NatIndex.t) (m : t) : PExpr :=
  fold_right 
  (fun i p => PEmul (find_or_1 i m) p )
  (PEc 1%Q)
  l.

  Definition map_pos (P : Cs.t) (m:t) : Prop :=
  forall k:M.key, forall d:Cstr.t, forall p:PExpr, forall mem: Mem.t QNum.t,
  Cs.sat P mem -> M.MapsTo k p m -> 0%Q <= PEsem p (Cs.mem_compat mem).
  
  Lemma find_or_1_pos : forall P : Cs.t, forall i:CIndex.NatIndex.t, forall d:Cstr.t, forall mem: Mem.t QNum.t,
  forall m:t, map_pos P m -> Cs.sat P mem -> 0%Q <= PEsem (find_or_1 i m) (Cs.mem_compat mem).
  Proof.
    intros P i d mem m pos sat.
    unfold find_or_1.
    elimtype (exists o, o=M.find (elt:=PExpr) i m); eauto.
    intros o H; rewrite <- H; destruct o as [x|y].
    apply (pos i d x mem).
    assumption.
    apply M.find_2.
    rewrite H.
    reflexivity.
    simpl.
    apply le_0_1.
  Qed.

  Lemma cons_rec_pos : forall P : Cs.t, forall d:Cstr.t, forall l:list CIndex.NatIndex.t, forall mem: Mem.t QNum.t,
  forall m : t, map_pos P m -> Cs.sat P mem -> 0%Q <= PEsem (cons_rec l m) (Cs.mem_compat mem).
  Proof.
    intros P d l mem m pos sat.
    induction l.
    simpl.
    apply le_0_1.
    simpl.
    apply Qmult_le_0_compat.
    apply (find_or_1_pos P).
    assumption.
    assumption.
    assumption.
    assumption.
  Qed.

  Definition cons_map (c:buildOrder) (m:t) : t :=
  fold_right
  (fun ic map => M.add ic.(ind) (cons_rec ic.(cons) map) map) (* m ou map? *)
  m c.

  Lemma cons_map_pos : forall P : Cs.t, forall c:buildOrder, 
    map_pos P (cons_map c (init P Cs.default)).
  Proof.
    intros P c.
    induction c.
    - unfold map_pos.
      intros k d' p mem sat map.
      unfold cons_map in map.
      simpl in map.
      apply (init_pos P k p mem);
      assumption.
    - unfold map_pos.
      intros k d' p mem sat map.
      simpl in *.
      
      assert (EQdec : {CIndex.NatIndex.eq (ind a) k} + {~CIndex.NatIndex.eq (ind a) k}).
      apply CIndex.NatIndex.eq_dec.
      elim EQdec; clear EQdec.
      intro EQ.
      assert (M.MapsTo (ind a) p
        (M.add (ind a) (cons_rec (cons a) (cons_map c (init P Cs.default)))
           (cons_map c (init P Cs.default)))).
      apply M.MapsTo_1 with (x := k).
      apply CIndex.NatIndex.eq_sym. assumption.
      assumption.
      assert (cons_rec (cons a) (cons_map c (init P Cs.default)) = p).
      apply (mapsto_add_compat (ind a) _ _ (cons_map c (init P Cs.default))).
      assumption.
      rewrite <- H0.
      apply (cons_rec_pos P);assumption.
      
      intro NEQ.
      unfold map_pos in IHc.
      apply (IHc k).
      assumption.
      assumption.
      apply (M.add_3) with (x := ind a) (e' := (cons_rec (cons a) (cons_map c (init P Cs.default)))).
      unfold CIndex.NatIndex.eq in NEQ.
      assumption.
      assumption.
    Qed.

  Definition coeff_pos (T : Type) (l : list (Q * T)) : Prop :=
  forall x: Q * T , In x l -> 0 <= fst x.
  
  Lemma coeff_pos_is_pos : forall T : Type, forall q : Q, forall hi : T, 
  coeff_pos T [(q, hi)] -> 0 <= q.
  Proof.
    intros T q hi pos.
    unfold coeff_pos in pos.
    simpl in pos.
    assert (OR : (q, hi) = (q,hi) \/ False -> let '(q0, _) := (q,hi) in 0 <= q0) by apply pos.
    simpl in OR.
    apply OR.
    left.
    reflexivity.
  Qed.
  
  Definition to_posQ (q:Q) : Q := 
  if Qlt_le_dec 0%Q q
  then q
  else failwith CERT "A coefficient in the Handelman certificate is not positive" 0%Q.

  Definition to_pos1 (T : Type) (x:Q * T) : Q * T :=
    let '(q,y) := x in (to_posQ q, y).

  Definition to_pos (T : Type) (l : list (Q * T)) : list (Q * T) :=
  map (fun x => to_pos1 T x) l.

  Lemma coeff_pos_app : forall T : Type, forall x: Q * T, forall l : list (Q * T), 
  coeff_pos T [x] /\ coeff_pos T l -> coeff_pos T (x::l).
  Proof.
    intros T x l AND.
    unfold coeff_pos.
    intros x' Hin.
    destruct x' as (q,hi).
    simpl in *.
    elim Hin.
    - intro EQ.
      subst.
      apply (coeff_pos_is_pos T q hi).
      apply AND.
    - intro In.
      elim AND.
      intros Hx Hl.
      unfold coeff_pos in Hl.
      assert (LEQ : List.In (q,hi) l -> let '(q0, _) := (q,hi) in 0 <= q0) by apply Hl.
      simpl in LEQ.
      apply LEQ;assumption.
  Qed.
  
  Lemma to_posQ_pos (q : Q) : 0 <= to_posQ q.
  Proof.
    unfold to_posQ.
    destruct (Qlt_le_dec 0 q) as [LT|LE] ; intuition.
  Qed.
  
  Lemma to_pos1_pos (T : Type) (x : Q * T) : 0 <= fst (to_pos1 T x).
  Proof.  
    unfold to_pos1.
    intuition.
    unfold fst.
    apply to_posQ_pos.
  Qed.

  Lemma coeff_are_pos : forall T : Type, forall l : list (Q * T), coeff_pos T (to_pos T l).
  Proof.
    induction l.
    - simpl.
      unfold coeff_pos ; unfold fst.
      intuition.
    - simpl in *.
      apply coeff_pos_app.
      split.
      
      -- unfold coeff_pos.
      unfold In.
      intros x In.
      intuition.
      rewrite <- H.
      apply to_pos1_pos.
     -- unfold coeff_pos.
      intros x In.
      intuition.
  Qed.
  
  Lemma to_pos_app : forall T : Type, forall x: Q * T, forall l : list (Q * T), 
  to_pos T (x::l) = to_pos1 T x :: to_pos T l.
  Proof. intuition. Qed.

  Import Qcanon.
  Open Scope nat_scope.

  Fixpoint compute_varBound (P : Cs.t) (vb : CIndex.QcIndex.t) (i : nat) : PExpr := 
    match vb with
    | [] => PEc 0%Q
    | qc :: tl =>
      let cstr := Cstr.to_PExpr (Cs.geti i P Cs.default) in
      let qc' := to_posQ qc.(this) in
      PEadd (PEmul (PEc qc') cstr) (compute_varBound P tl (i+1))
    end.

  Definition compute_varBounds (P : Cs.t) (vbs : list CIndex.QcIndex.t) : PExpr := 
    fold_right
      (fun vb res => PEmul res (compute_varBound P vb 0%nat))
    (PEc 1%Q) vbs.
  
  Definition schweighofer : Type := CIndex.NatIndex.t * squares * list CIndex.QcIndex.t.

  Definition calculus P m x p := 
    let '(q,(i,s,vbs)):= x in 
    let inter := PEmul (compute_squares s)
      (PEmul p (PEmul (PEc q) (find_or_1 i m))) in
    PEmul inter (compute_varBounds P vbs).

  Definition computeH (P:Cs.t) (l : list (Q * schweighofer)) (c:buildOrder) : PExpr := 
    let m := (cons_map c (init P Cs.default)) in
    fold_right 
      (fun x p => calculus P m x p)
    (PEc 1%Q)
    (to_pos schweighofer l).
    
  Open Scope Q_scope.
  
  Lemma compute_varBound_pos (P : Cs.t) (vb : CIndex.QcIndex.t) (mem : Mem.t QNum.t) : 
    Cs.sat P mem ->
    forall i : nat, 0 <= PEsem (compute_varBound P vb i) (Cs.mem_compat mem).
  Proof.
    intro SAT.
    induction vb.
    - simpl ; intros ; apply Qle_refl.
    - unfold compute_varBound.
    intro i.
    fold (compute_varBound P vb (i+1)).
    assert (0 <= PEsem (Cstr.to_PExpr (Cs.geti i P Cs.default)) mem) by (apply Cs.sem_compat_default ; assumption).
    assert (EQ0 : 0 == 0 + 0) by ring.
    rewrite EQ0.
    simpl in *.
    fold (Cstr.to_PExpr (Cs.geti i P Cs.default)).
    apply Qplus_le_compat.
    -- apply Qmult_le_0_compat.
      apply to_posQ_pos.
      assumption.
    -- apply IHvb.
  Qed. 

  Lemma compute_varBounds_pos (P : Cs.t) (vbs : list CIndex.QcIndex.t) (mem : Mem.t QNum.t) : 
    Cs.sat P mem ->
    0 <= PEsem (compute_varBounds P vbs) (Cs.mem_compat mem).
  Proof.
    intro SAT.
    induction vbs.
    - simpl. apply le_0_1.
    - simpl.
      apply Qmult_le_0_compat.
      assumption.
      apply compute_varBound_pos ; assumption.
  Qed.
  
  Lemma computeH_app P x l c m: 
  PEsem (computeH P (x :: l) c) m ==
  PEsem (computeH P l c) m * PEsem (computeH P [x] c) m.
  Proof.
    unfold computeH at 1.
    rewrite to_pos_app.
    
    assert (EQ : to_pos1 schweighofer x :: to_pos schweighofer l = [to_pos1 schweighofer x] ++ to_pos schweighofer l) by auto.
    rewrite EQ. clear EQ.
    rewrite fold_right_app.
   (*
    fold (computeH P l c).
    *)
    
    unfold computeH at 2.
    simpl.
    
    destruct (to_pos1 schweighofer x) as (q,(hi,vbs)).
    destruct hi as (i,s).
    simpl.
    
    (* ugly thing to fold afterwards >*)
    rewrite Qmult_assoc.
    rewrite (Qmult_comm (PEsem (compute_squares s) m)
      (PEsem
  (fold_right
     (fun (x0 : Q * (NatIndex.t * squares * list QcIndex.t))
        (p : Ring_polynom.PExpr Q) =>
      calculus P (cons_map c (init P Cs.default)) x0 p) 
     (PEc 1) (to_pos schweighofer l)) m)).
    fold (computeH P l c).

    ring.
  Qed.
  
  Lemma q_square_pos: forall q : Q, 0<= q*q.
  Proof.
  intro q. apply Qsqr_nonneg.
  Qed.

  Lemma squares_pos s m:  
  0 <= PEsem (compute_squares s) m.
  Proof.
  induction s.
  - simpl. apply le_0_1.
  - simpl.
  destruct a as (poly,exp).
  simpl.
  apply Qmult_le_0_compat.
    assumption.
    
    destruct exp.
      simpl. apply le_0_1.
    
      simpl. apply q_square_pos.
  Qed.

  Lemma computeH_pos : forall P : Cs.t, forall l :list (Q * schweighofer), forall c:buildOrder, forall mem: Mem.t QNum.t,
  Cs.sat P mem -> 0%Q <= PEsem (computeH P l c) (Cs.mem_compat mem).
  Proof.
    intros P l c mem sat.
    induction l.
    - simpl ; apply le_0_1.
    - destruct a as (q, (hi, vbs)).
      destruct hi as (i, s).
      rewrite computeH_app.
      apply Qmult_le_0_compat.
      -- apply IHl.
      -- assert (pos : coeff_pos schweighofer (to_pos schweighofer [(q, (i, s, vbs))])) by (apply (coeff_are_pos schweighofer)).
        unfold computeH.
        simpl in *.
        fold (to_pos1 schweighofer (q,(i,s,vbs))) in *.
        destruct (to_pos1 schweighofer (q, (i,s,vbs))) as (q',(hi,vbs')).
        destruct hi as (i',s').
        apply Qmult_le_0_compat.
        --- apply Qmult_le_0_compat.
          apply squares_pos.
          apply Qmult_le_0_compat.
          ---- apply le_0_1.
          ---- apply Qmult_le_0_compat.
            apply to_posQ_pos.
            apply (find_or_1_pos P).
            apply Cs.default.
            apply cons_map_pos.
            assumption.
        --- apply compute_varBounds_pos ; assumption.

  Qed.

End MapPoly.

Module Handelman_compute.
  Record certif : Type := mk{
  aff : QTerm.t;
  sch : list (Q * MapPoly.schweighofer);
  bo : MapPoly.buildOrder}.
  
  Module QPom := QTerm2Pomial QTerm.

  Definition witness (P : Cs.t) (c:certif) (g:QTerm.t) : PExpr:=
  PEadd (QPom.toPExpr g) (MapPoly.computeH P c.(sch) c.(bo)).
  
  Local Open Scope Q_scope.
  
  Lemma witness_pos : forall P:Cs.t, forall c:certif, forall mem: Mem.t QNum.t, forall g:QTerm.t,
  Cs.sat P mem -> 
  0 <= PEsem (QPom.toPExpr g) (Cs.mem_compat mem) ->
  0 <= PEsem (witness P c g) (Cs.mem_compat mem).
  Proof.
    intros P c mem g sat pos.
    simpl.
    assert (Z : 0 = 0 + 0) by reflexivity.
    rewrite Z. clear Z.
    apply Qplus_le_compat.
    assumption.
    apply MapPoly.computeH_pos.
    assumption.
  Qed.

  Lemma witness_pos_strict : forall P:Cs.t, forall c:certif, forall mem: Mem.t QNum.t, forall g:QTerm.t,
  Cs.sat P mem -> 
  0 < PEsem (QPom.toPExpr g) (Cs.mem_compat mem) ->
  0 < PEsem (witness P c g) (Cs.mem_compat mem).
  Proof.
    intros P c mem g sat pos.
    simpl.
    assert (Z : 0 = 0 + 0) by reflexivity.
    rewrite Z. clear Z.
    apply Qplus_lt_le_compat.
    assumption.
    apply MapPoly.computeH_pos.
    assumption.
  Qed.
  
  Definition one := {| QAffTerm.lin:= QAffTerm.Lin.nil; QAffTerm.cte := QNum.u |}.
  
  Lemma OneEval m s : QAffTerm.eval (failwith CERT s one) m = QNum.u.
  Proof.
    unfold QAffTerm.eval; simpl ; autorewrite with linterm ; intuition. 
  Qed.
  
  Lemma OneEvalPos_strict m s : QNum.Lt QNum.z (QAffTerm.eval (failwith CERT s one) m).
  Proof.
    rewrite OneEval ; unfold QNum.Lt ; unfold QNum.z ; unfold QNum.u.
    apply MapPoly.lt_0_1.
  Qed.

  Definition eq_witness (P : Cs.t) (c:certif) (g:QTerm.t) : QAffTerm.t :=
  if Ring_polynom_AddOnQ.PExpr_eq (witness P c g) (QPom.toPExpr c.(aff))
  then let (te,aft) := QTerm.affineDecompose c.(aff) in
    if QTerm.pseudoIsZero te 
    then aft
    else failwith CERT "eq_witness : aff is not linear" one
  else failwith CERT "eq_witness : the two polynomials differ" one.
  
  Open Scope Q_scope.

  Lemma eq_witness_pos_strict (m : Mem.t QNum.t) (P : Cs.t) (c:certif) (g:QTerm.t) :
    Cs.sat P m -> 
    0 < PEsem (QPom.toPExpr g) (Cs.mem_compat m) ->
    QNum.Lt QNum.z (QAffTerm.eval (eq_witness P c g) m).
  Proof.
    intros SAT POS.
    unfold eq_witness.
    remember (witness P c g) as w.
    remember (QPom.toPExpr (aff c)) as aff_pe.
    assert (EQ_DEC : {Ring_polynom_AddOnQ.PExpr_eq w aff_pe = true} + {Ring_polynom_AddOnQ.PExpr_eq w aff_pe = false}) by (apply PExpr_eq_dec).
    destruct EQ_DEC as [EQ | NEQ].
    - assert (QEQ : Qeq (PEsem w (Cs.mem_compat m)) (PEsem aff_pe (Cs.mem_compat m))) 
      by (apply PExpr_eq_correct ; assumption).
    destruct (Ring_polynom_AddOnQ.PExpr_eq w aff_pe) ; try intuition.
    assert (POS1 : 0 < PEsem (witness P c g) (Cs.mem_compat m)) 
      by (apply witness_pos_strict ; assumption).
    rewrite <- Heqw in POS1.
    assert (POS2 : 0 < PEsem aff_pe (Cs.mem_compat m)).
 
    apply (QOp.pos_compat_strict ( PEsem w (Cs.mem_compat m))) ; assumption.
    
    assert (COMPAT : QTerm.eval (aff c) m = Qcanon.Q2Qc (PEsem (QPom.toPExpr (aff c)) (Cs.mem_compat m)))
      by (apply QPom.toPExpr_correct).
    
    rewrite <- QTerm.affineDecompose_correct in COMPAT.
    destruct (QTerm.affineDecompose (aff c)) as (te,aft).
    simpl in COMPAT.
    
    assert (IS_ZERO : QTerm.pseudoIsZero te = true -> QTerm.eval te m = QNum.z).
    apply QTerm.pseudoIsZero_correct2.

    destruct (QTerm.pseudoIsZero te).
    -- rewrite IS_ZERO in COMPAT.
      Import Qcanon.
      rewrite Qcplus_0_l in COMPAT. 
      rewrite COMPAT.
      
      rewrite <- Heqaff_pe.
      rewrite QOp.to_PExpr_compat_pos_strict.
      assumption.
     
      reflexivity.
      
    -- apply OneEvalPos_strict.
    -- apply OneEvalPos_strict.
 
  - destruct (Ring_polynom_AddOnQ.PExpr_eq w aff_pe).
    -- absurd (true = false) ; intuition ; try assumption.
    -- apply OneEvalPos_strict.
  Qed.
  
  Lemma OneEvalPos m s : QNum.Le QNum.z (QAffTerm.eval (failwith CERT s one) m).
  Proof.
    unfold QNum.Le.
    apply Qclt_le_weak.
    apply OneEvalPos_strict.
  Qed.
  
  Open Scope Q_scope.
  Lemma eq_witness_pos (m : Mem.t QNum.t) (P : Cs.t) (c:certif) (g:QTerm.t) :
    Cs.sat P m -> 
    0 <= PEsem (QPom.toPExpr g) (Cs.mem_compat m) ->
    QNum.Le QNum.z (QAffTerm.eval (eq_witness P c g) m).
  Proof.
    intros SAT POS.
    unfold eq_witness.
    remember (witness P c g) as w.
    remember (QPom.toPExpr (aff c)) as aff_pe.
    assert (EQ_DEC : {Ring_polynom_AddOnQ.PExpr_eq w aff_pe = true} + {Ring_polynom_AddOnQ.PExpr_eq w aff_pe = false}) by (apply PExpr_eq_dec).
    destruct EQ_DEC as [EQ | NEQ].
    - assert (QEQ : Qeq (PEsem w (Cs.mem_compat m)) (PEsem aff_pe (Cs.mem_compat m))) 
      by (apply PExpr_eq_correct ; assumption).
    destruct (Ring_polynom_AddOnQ.PExpr_eq w aff_pe).
    assert (POS1 : 0 <= PEsem (witness P c g) (Cs.mem_compat m)) by (apply witness_pos ; assumption).
    rewrite <- Heqw in POS1.
    assert (POS2 : 0 <= PEsem aff_pe (Cs.mem_compat m)).
 
    apply (QOp.pos_compat( PEsem w (Cs.mem_compat m))) ; assumption.
    
    assert (COMPAT : QTerm.eval (aff c) m = Qcanon.Q2Qc (PEsem (QPom.toPExpr (aff c)) (Cs.mem_compat m)))
      by (apply QPom.toPExpr_correct).
    
    rewrite <- QTerm.affineDecompose_correct in COMPAT.
    destruct (QTerm.affineDecompose (aff c)) as (te,aft).
    simpl in COMPAT.
    
    assert (IS_ZERO : QTerm.pseudoIsZero te = true -> QTerm.eval te m = QNum.z).
    apply QTerm.pseudoIsZero_correct2.

    destruct (QTerm.pseudoIsZero te).
    -- rewrite IS_ZERO in COMPAT.
      Import Qcanon.
      rewrite Qcplus_0_l in COMPAT. 
      rewrite COMPAT.
      
      rewrite <- Heqaff_pe.
      rewrite QOp.to_PExpr_compat_pos.
      assumption.
      reflexivity.
      
    -- apply OneEvalPos.
    -- apply OneEvalPos. 
 
    - destruct (Ring_polynom_AddOnQ.PExpr_eq w aff_pe).
    -- absurd (true = false) ; intuition ; try assumption.
    -- apply OneEvalPos.
  Qed.

End Handelman_compute.



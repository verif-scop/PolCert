(** This module gives an abstract syntax (inspired from logical terms) for arithmetic terms.

*)

Require Export ProgVar.
Require Export NumC.
Require Import Bool.
Require Import ZArith.
Require Import LinTerm.
Require Export DomainInterfaces.
Require Import Equalities.
Require Import Ring_polynom_AddOn.
Require Import Qop.

Create HintDb vpl discriminated.

(* arithmetic terms as expressions *)
Module AnnotatedTerm (N: NumSig) (Annot: Typ) <: TermSig N.

  (* annotations are simply considered as comments in standard [eval] semantics *)
  Inductive term: Type :=
  | Var (x: PVar.t)
  | Cte (c: N.t)
  | Add (tl tr: term)
  | Opp (te: term)
  | Mul (tl tr:term)
  | Annot (a:Annot.t) (te:term).

  Definition t:=term.

  (* Standard evaluation (annotations are skipped) *)
  Fixpoint eval (te:term) (m: Mem.t N.t) : N.t := 
    match te with
      | Var x => m x
      | Cte c => c
      | Add tl tr => N.add (eval tl m) (eval tr m)
      | Opp te => N.opp (eval te m)
      | Mul tl tr => N.mul (eval tl m) (eval tr m)
      | Annot a te => (eval te m)
    end.

  (* Useless: derived from eval_pointwise_compat ?
  Add Parametric Morphism: eval with
   signature Logic.eq ==> pointwise_relation PVar.t Logic.eq ==> Logic.eq
   as eval_compat.
  Proof.
     intros t m1 m2 H; induction t; simpl; try congruence.
  Qed.
  *)

 (* MayDependOn + mdBound *)
  Fixpoint mayDependOn (te: term) (x: PVar.t): Prop := 
    match te with
      | Var y => x=y 
      | Cte c => False
      | Add tl tr => mayDependOn tl x \/ mayDependOn tr x
      | Opp te => mayDependOn te x
      | Mul te tr => mayDependOn te x \/ mayDependOn tr x
      | Annot _ te => mayDependOn te x 
    end.

  Hint Resolve (@mdBounds_fold _ mayDependOn): progvar.

  Fixpoint mdBound (te:term) (bound: PVar.t): PVar.t := 
    match te with
      | Var x => PVar.max bound x
      | Cte _ => bound
      | Add tl tr => mdBound tl (mdBound tr bound)
      | Opp te => mdBound te bound
      | Mul tl tr => mdBound tl (mdBound tr bound)
      | Annot _ te => mdBound te bound
    end.

  Program Instance mdBound_mdBoundVar: MDBoundVar (mayDependOn:=mayDependOn) (mdBound:=mdBound).
  Obligation 1.
    generalize bound; induction e; simpl; intros; autorewrite with rwmax; auto;
    (rewrite IHe2; rewrite IHe1; eapply eq_sym; rewrite IHe1;
     autorewrite with rwmax; auto).
  Qed.
  Hint Resolve mdBound_mdBoundVar_obligation_1: progvar.
  Obligation 2.
    unfold mdBounds; generalize bound; induction e; simpl; intros; subst; intuition; eauto with progvar.
  Qed.
  Hint Resolve mdBound_mdBoundVar_obligation_2: progvar.

  Lemma eval_mdo: mdoExt mayDependOn eval Logic.eq.
  Proof.
    unfold mdoExt, bExt; induction e; simpl; intuition auto.
  Qed.

  Fixpoint fold_variables {A} (te: term) (f: PVar.t -> A -> A) (i: A): A :=
    match te with
      | Var x => f x i
      | Cte _ => i
      | Add tl tr => fold_variables tl f (fold_variables tr f i)
      | Opp te => fold_variables te f i
      | Mul tl tr => fold_variables tl f (fold_variables tr f i)
      | Annot _ te => fold_variables te f i
    end.
  Extraction Inline fold_variables.

  Lemma fold_variables_preserv {A} (P: A -> Prop) f te: 
    forall i, P i -> (forall x y, P y -> P (f x y)) -> P (fold_variables te f i).
  Proof.
    induction te; simpl; auto.
  Qed. 

  (* Mapping of variables 
     Currently, we preserve all annotations !
  *)
  Fixpoint map (te: term) (f: Mem.t PVar.t) : term := 
    match te with
      | Var x => Var (f x)
      | Add tl tr => Add (map tl f) (map tr f)
      | Opp te => Opp (map te f)
      | Mul te tr => Mul (map te f) (map tr f)
      | Annot a te => Annot a (map te f)
      | Cte c as te => te
    end.

  Lemma eval_map: forall te f m, eval (map te f) m = eval te (fun x => m (f x)).
  Proof.
    induction te; simpl; auto.
    (* Annot intros; destruct a; simpl; auto. *)
  Qed.
  Hint Resolve eval_map: vpl.

   (** Smart Constructors: they perform a few constant propagations at constant cost (over the AST) ! *)

   Add Ring NRing: N.Ring.

   Definition pseudoIsZero (te: term): bool :=
     match te with
     | Cte c => if N.isZero c then true else false
     | _ => false
     end.
   Extraction Inline pseudoIsZero.

   Local Open Scope option_scope.

   Lemma pseudoIsZero_correct te:
     If pseudoIsZero te THEN forall m, eval te m = N.z.
   Proof.
     unfold pseudoIsZero; case te; simpl; auto.
     intros c; destruct (N.isZero c); simpl; subst; auto.
   Qed.
   Hint Resolve pseudoIsZero_correct: pedraQ.

   Lemma pseudoIsZero_correct2 te m :
     pseudoIsZero te = true -> eval te m = N.z.
   Proof.
     unfold pseudoIsZero; case te; simpl;
     intros; try (absurd (false = true) ; auto ; assumption).
    destruct (N.isZero c); simpl; subst; auto.
    absurd (false = true) ; auto ; assumption.
   Qed.

   (* when t is not itself a cte *) 
   Definition smartScalAdd1 (c:N.t) (te: term): term :=  
       if N.isZero c then te else (Add (Cte c) te).
   Extraction Inline smartScalAdd1.

   Lemma smartScalAdd1_correct c te m:
      eval (smartScalAdd1 c te) m = N.add c (eval te m).
   Proof.
      unfold smartScalAdd1; destruct (N.isZero c); simpl; intros; subst; ring.
   Qed.
   Hint Rewrite smartScalAdd1_correct: linterm.

   Definition smartScalAdd (c:N.t) (te: term): term :=  
     match te with 
       | Cte c' => Cte (N.add c c')
       | _ => smartScalAdd1 c te
       end.

   Lemma smartScalAdd_correct c te m:
      eval (smartScalAdd c te) m = N.add c (eval te m).
   Proof.
      unfold smartScalAdd; destruct te; simpl; autorewrite with linterm; auto. 
   Qed.
   Hint Rewrite smartScalAdd_correct: linterm.

   Definition smartAdd (te1 te2: term): term :=
     match te1 with
     | Cte c => smartScalAdd c te2
     | _ => match te2 with
            | Cte c => smartScalAdd1 c te1
            | _ => Add te1 te2
            end
     end.

   Lemma smartAdd_correct te1 te2 m:
      eval (smartAdd te1 te2) m = N.add (eval te1 m)  (eval te2 m).
   Proof.
      unfold smartAdd; destruct te1; autorewrite with linterm; auto;
      (destruct te2; autorewrite with linterm; simpl; try ring).
   Qed.

   Definition smartOpp (te: term): term :=  
     match te with
     | Cte c => Cte (N.opp c)
     | te => Opp te
     end.
   Extraction Inline smartOpp.

   Lemma smartOpp_correct te m:
      eval (smartOpp te) m = N.opp (eval te m).
   Proof.
      unfold smartOpp; destruct te; simpl; auto.
   Qed.

   (* when te is not itself a constant *)
   Definition smartScalMul1 (c:N.t) (te: term): term :=  
     match N.mulDiscr c with 
       | IsZero => Cte N.z
       | IsUnit => te
       | IsOppUnit => Opp te
       | Other => Mul te (Cte c) (* Scal-right CONVENTION ! *)
       end.

   Lemma smartScalMul1_correct c te m:
      eval (smartScalMul1 c te) m = N.mul c (eval te m).
   Proof.
      unfold smartScalMul1; generalize (N.mulDiscr_correct c); destruct (N.mulDiscr c); 
      simpl; try (intro H; rewrite H; ring_simplify); auto.
      intros; rewrite N.MulComm; auto.
   Qed.
  Hint Rewrite smartScalMul1_correct: linterm.
  Opaque smartScalMul1_correct.

   Definition smartScalMul (c:N.t) (te: term): term :=  
     match te with 
       | Cte c' => Cte (N.mul c c')
       | _ => smartScalMul1 c te 
       end.
   Extraction Inline smartScalMul.

   Lemma smartScalMul_correct c te m:
      eval (smartScalMul c te) m = N.mul c (eval te m).
   Proof.
      unfold smartScalMul; destruct te; autorewrite with linterm num; simpl; auto.
   Qed.
   Hint Rewrite smartScalMul_correct: linterm.

   Definition smartMul (te1 te2: term): term :=
     match te1 with
     | Cte c => smartScalMul c te2
     | _ => match te2 with
            | Cte c => smartScalMul1 c te1
            | _ => Mul te1 te2
            end
     end.

   Lemma smartMul_correct te1 te2 m:
      eval (smartMul te1 te2) m = N.mul (eval te1 m)  (eval te2 m).
   Proof.
      unfold smartMul; destruct te1; autorewrite with linterm; auto;
      (destruct te2; autorewrite with linterm; simpl; try ring).
   Qed.

   (* We forbid annotation of constants ! *)
   Definition smartAnnot (a: Annot.t) (te: term): term :=
      match te with
     | Cte c => te
     | _ => Annot a te
     end.
  
   Lemma smartAnnot_correct te a m:
      eval (smartAnnot a te) m = eval te m.
   Proof. 
      unfold smartAnnot; destruct te; simpl; auto.
   Qed.

   Hint Rewrite smartAdd_correct smartOpp_correct smartAnnot_correct smartMul_correct: linterm.

  (** import: optimized for list given by current implementation of Linterms
   *)      
  Fixpoint import_acc (l: list (PVar.t * N.t)) acc: term :=
    match l with
    | nil => acc 
    | cons (x,c) l => import_acc l (Add acc (smartScalMul1 c (Var x)))
    end.
 
  Lemma import_acc_correct (l: list (PVar.t * N.t)) m: forall acc,
    eval (import_acc l acc) m 
    = N.add (List.fold_right (fun p sum => N.add sum (N.mul (m (fst p)) (snd p)))
                      N.z l) (eval acc m).
  Proof.
    induction l as [| (x,c) l' IHl' ]; simpl.
    - intros; ring.
    - intros acc; rewrite IHl'; simpl; autorewrite with linterm num; simpl.
    ring.
  Qed.

 Definition import (l: list (PVar.t * N.t)): term :=
   match l with 
   | nil => Cte N.z
   | cons (x,c) l => import_acc l (smartScalMul1 c (Var x))
   end.

  Lemma import_correct (l: list (PVar.t * N.t)) m:
    eval (import l) m 
    = (List.fold_right (fun p sum => N.add sum (N.mul (m (fst p)) (snd p)))
                      N.z l).
  Proof.
    destruct l as [| (x,c) l']; simpl; auto.
    rewrite import_acc_correct; autorewrite with linterm num; simpl.
    ring.
  Qed.
  Hint Rewrite import_correct: linterm.

End AnnotatedTerm.

Module Type AnnotatedTermSig(N: NumSig).
  Declare Module Annot : Typ.
  Include AnnotatedTerm N Annot.
End AnnotatedTermSig.

Module AffineDecompose(N: NumSig) (Import Affine: AffineTermSig N) (Import Term: AnnotatedTermSig N). 

   Definition fromLin (lt: Lin.t): term := 
      (import (Lin.export lt)).

  Lemma fromLin_correct lt m:
    Term.eval (fromLin lt) m = Lin.eval lt m.
  Proof.
     unfold fromLin; autorewrite with linterm. auto.
  Qed.
  Hint Rewrite fromLin_correct: linterm.
  
  Definition fromAff (aff : affTerm) : term :=
     Add (fromLin (lin aff)) (Cte (cte aff)) .
  
  Lemma fromAff_correct aff m:
    Term.eval (fromAff aff) m = Affine.eval aff m.
  Proof.
    unfold fromAff.
    simpl.
    unfold Affine.eval.
    rewrite fromLin_correct.
    reflexivity.
  Qed.

  Hint Rewrite fromLin_correct: linterm.

  (* This function decomposes a polynom "te" into the sum of an affine term and 
     a polynome which is either nul or with all its monome of degre >= 2 

   NB: in the correctness proof, we only show that the source polynom is preserved by the
       decomposition.

   We preserve annotations on non-linear terms, except on cte !
   *)

   Fixpoint affineDecompose (te:term): term * Affine.t   := 
    match te with
      | Annot a t0 => 
         let (t,aft):=affineDecompose t0 in
         (smartAnnot a t, aft)
      | Var x => (Cte N.z, {| lin:=Lin.single x N.u; cte := N.z |})
      | Cte c => (Cte N.z, {| lin:=Lin.nil ; cte := c |})
      | Add tl tr => 
         let (t1,aft1):=affineDecompose tl in
         let (t2,aft2):=affineDecompose tr in
         (smartAdd t1 t2, Affine.add aft1 aft2)
      | Opp t0 => 
         let (t,aft):=affineDecompose t0 in
         (smartOpp t, Affine.opp aft)
      | Mul tl tr =>
         let (t1,aft1):=affineDecompose tl in
         let (t2,aft2):=affineDecompose tr in
         let p1 := if pseudoIsZero t2 &&& Lin.isNil (lin aft2) then Cte N.z else smartAdd t1 (fromLin (lin aft1)) in
         let p2 := if pseudoIsZero t1 &&& Lin.isNil (lin aft1) then Cte N.z else smartAdd t2 (fromLin (lin aft2)) in
         (smartAdd (smartMul p1 p2)
                    (smartAdd (smartScalMul (cte aft1) t2)
                              (smartScalMul (cte aft2) t1)),
          Affine.add (Affine.mul (cte aft1) aft2) {| lin:=Lin.mul (cte aft2) (lin aft1); cte:=N.z |})
    end.

  Lemma affineDecompose_correct te m: 
      N.add (Term.eval (fst (affineDecompose te)) m) (Affine.eval (snd (affineDecompose te)) m)
      = (Term.eval te m).
  Proof.
    induction te; simpl; 
    try ((destruct (affineDecompose te1) as [t1 aft1], (affineDecompose te2) as [t2 aft2] || destruct (affineDecompose te)));
    simpl in * |- *;
    try ((rewrite <- IHte1, <- IHte2) || rewrite <- IHte);
    autorewrite with num linterm; try ring.
    (* multiplication case *)
    unfold Affine.eval. PedraQsimplify;
    intros; autorewrite with linterm;
    try (rewrite H); try (rewrite H0); try (rewrite H1); try (rewrite H2);
    autorewrite with linterm;
    ring_simplify; auto.
  Qed.

End AffineDecompose.

Module ZTerm2Pomial (Import ATerm: AnnotatedTermSig ZNum).
 
  (** A translation of terms into Ring_polynom_AddOn.PExpr. 
   *)
    Fixpoint toPExpr (te:term): PExpr := 
    match te with
      | Var x => PEX _ x
      | Cte c => PEc c
      | Add tl tr => PEadd (toPExpr tl) (toPExpr tr)
      | Opp te => PEopp (toPExpr te)
      | Mul tl tr => PEmul (toPExpr tl) (toPExpr tr)
      | Annot a te => toPExpr te
    end.

    Lemma toPExpr_correct te m:
       eval te m = PEsem (toPExpr te) m.
    Proof.
      induction te; simpl; auto.
    Qed.

End ZTerm2Pomial.

(** A polynomial equality of two terms with different annotation types *)
Module ZPomialEquality (ATerm1: AnnotatedTermSig ZNum) (ATerm2: AnnotatedTermSig ZNum). 

    Module M1:=ZTerm2Pomial ATerm1.
    Module M2:=ZTerm2Pomial ATerm2.

    Definition pomial_eq (te1:ATerm1.t) (te2:ATerm2.t): bool :=
      PExpr_eq (M1.toPExpr te1) (M2.toPExpr te2).

    Local Open Scope option_scope.

    Theorem pomial_eq_correct te1 te2:
      If pomial_eq te1 te2 THEN forall m, ATerm1.eval te1 m = ATerm2.eval te2 m.
    Proof.
      unfold pomial_eq; PedraQsimplify. intros; rewrite M1.toPExpr_correct, M2.toPExpr_correct. 
      apply PExpr_eq_correct; auto.
    Qed. 

End ZPomialEquality.

Module QTerm2Pomial (Import ATerm: AnnotatedTermSig QNum).
 
  (** A translation of terms into Ring_polynom_AddOnQ.PExpr. 
   *)
    Fixpoint toPExpr (te:term): Ring_polynom_AddOnQ.PExpr := 
    match te with
      | Var x => PEX _ x
      | Cte c => PEc (QNum.to_Q c)
      | Add tl tr => PEadd (toPExpr tl) (toPExpr tr)
      | Opp te => PEopp (toPExpr te)
      | Mul tl tr => PEmul (toPExpr tl) (toPExpr tr)
      | Annot a te => toPExpr te
    end.
    Import ConsSet.
    Import QArith.
    Local Open Scope Q_scope.
    Lemma toPExpr_correct te m:
       eval te m = Qcanon.Q2Qc (Ring_polynom_AddOnQ.PEsem (toPExpr te) (Cs.mem_compat m)).
    Proof.
      induction te;simpl.
      - unfold Cs.mem_compat.
        apply eq_sym.
        apply QOp.Q2Qc_this_eq.
      - apply eq_sym. 
        apply QOp.Q2Qc_this_eq.
      - rewrite IHte1. rewrite IHte2.
        unfold QNum.add.
        apply eq_sym.
        apply QOp.Qcanon_add_Q2Qc.
      - rewrite IHte.
        unfold QNum.opp.
        unfold Qcanon.Qcopp.
        rewrite QOp.Qcanon_opp.
        rewrite QOp.Qcanon_opp.
        simpl.
        rewrite QOp.Qred_Q2Qc_compat.
        reflexivity.
      - rewrite IHte1. rewrite IHte2.
        unfold QNum.mul.
        apply eq_sym.
        apply QOp.Qcanon_mult_Q2Qc.
      - rewrite IHte.
        reflexivity.
      Qed.
    
End QTerm2Pomial.

(*
Unused following module : 
(** A polynomial equality of two terms with different annotation types *)
Module QPomialEquality (ATerm1: AnnotatedTermSig QNum) (ATerm2: AnnotatedTermSig QNum). 

    Module M1:=QTerm2Pomial ATerm1.
    Module M2:=QTerm2Pomial ATerm2.

    Definition pomial_eq (te1:ATerm1.t) (te2:ATerm2.t): bool :=
      Ring_polynom_AddOnQ.PExpr_eq (M1.toPExpr te1) (M2.toPExpr te2).

    Local Open Scope option_scope.

    Theorem pomial_eq_correct te1 te2:
      If pomial_eq te1 te2 THEN forall m, ATerm1.eval te1 m = ATerm2.eval te2 m.
    Proof.
      unfold pomial_eq; PedraQsimplify. intros; rewrite M1.toPExpr_correct, M2.toPExpr_correct. 
      assert (QArith_base.Qeq (Ring_polynom_AddOnQ.PEsem (M1.toPExpr te1) (ConsSet.Cs.mem_compat m))
      (Ring_polynom_AddOnQ.PEsem (M2.toPExpr te2) (ConsSet.Cs.mem_compat m))).
      apply Ring_polynom_AddOnQ.PExpr_eq_correct; auto.
      apply Qcanon.Qc_is_canon.
      simpl.
      rewrite H.
      reflexivity.
    Qed. 

End QPomialEquality.
*)
Module TopLevelAnnot <: Typ.

  Inductive topLevelAnnot: Set :=
  | OLD         (* Induces a two-state semantics used in guarded assignment *)    
  | AFFINE      (* Indicates that the term is affine *)
  | INTERV      (* Use intervalization instead of linearization *)
  | STATIC      (* Use static intervalization (if any) instead of dynamic one *)
  | SKIP_ORACLE (* Skip oracle (for debugging) *)
  . 

  Definition t:=topLevelAnnot.

  (* for debugging *)
  Import String.
  Open Scope string_scope.
  Definition pr (a: topLevelAnnot): string :=
    match a with
    | OLD => "OLD"
    | AFFINE => "AFFINE"
    | INTERV => "INTERV"
    | STATIC => "STATIC"
    | SKIP_ORACLE => "SKIP_ORACLE" 
    end.
  Close Scope string_scope.

End TopLevelAnnot.


Module ModalTerm(N: NumSig) <: AnnotatedTermSig N.

  (* Here, we mainly use trivial annotation as a modal "Old" operator !
     This operator is used to speak about an implicit "old" state. 
     In the usual semantics, the "old" state is identified with the "current" state.
  *)
  Export TopLevelAnnot.

  Module Annot <: Typ := TopLevelAnnot.

  Include AnnotatedTerm N Annot.

  Definition Old te := Annot OLD te.

  Local Coercion Var: PVar.t >-> term.
  Local Coercion Cte: N.t >-> term.
   
  (* Extended evaluation (two states) *)
  Fixpoint xeval (te:term) (old new:Mem.t N.t) : N.t := 
    match te with
      | Var x => new x
      | Cte c => c
      | Add tl tr => N.add (xeval tl old new) (xeval tr old new)
      | Opp te => N.opp (xeval te old new)
      | Mul tl tr => N.mul (xeval tl old new) (xeval tr old new)
      | Annot OLD te => eval te old
      | Annot a te => xeval te old new
    end. 

  Lemma xeval_eval te m: xeval te m m = eval te m.
  Proof.
    induction te; simpl; try congruence.
    (* Annot *)
    destruct a; simpl; try congruence.
  Qed.
  Hint Rewrite xeval_eval: vpl.

  (* Useless: derived from eval_pointwise_compat ?
  Add Parametric Morphism: xeval with
    signature Logic.eq ==> pointwise_relation PVar.t Logic.eq ==> pointwise_relation PVar.t Logic.eq ==> Logic.eq
    as xeval_compat.
  Proof.
     intros t old1 old2 H1 new1 new2 H2; induction t; simpl; try congruence.
     erewrite eval_compat; eauto.
  Qed.
  *)

 
  Lemma xeval_old_mdo old: mdoExt mayDependOn (fun t => xeval t old) Logic.eq.
  Proof.
    unfold mdoExt, bExt; induction e; simpl; intuition.
    (* Annot *)
    destruct a; simpl; intuition.
  Qed.

  Lemma xeval_new_mdo new: mdoExt mayDependOn (fun t old => xeval t old new) Logic.eq.
  Proof.
    unfold mdoExt, bExt; induction e; simpl; intuition.
    erewrite eval_mdo; eauto.
    (* Annot *)
    destruct a; simpl; intuition.
  Qed.

  (* Extended mapping (one for old variables, one for new) *)
  Fixpoint xmap (te: term) (old new: Mem.t PVar.t): term := 
    match te with
      | Var x => Var (new x)
      | Add tl tr => Add (xmap tl old new) (xmap tr old new)
      | Opp te => Opp (xmap te old new)
      | Mul tl tr => Mul (xmap tl old new) (xmap tr old new)
      | Annot OLD te => Old (map te old)
      | Annot a te => Annot a (xmap te old new)
      | Cte c as te => te
    end.

  Lemma xeval_xmap: forall te old new f g, xeval (xmap te f g) old new  = xeval te (fun x => old (f x)) (fun x => new (g x)).
  Proof.
    induction te; simpl; auto with vpl.
    (* Annot *)
    destruct a; simpl; auto with vpl.
  Qed.
  Hint Resolve xeval_xmap: vpl.

  (** Recursive annotation of a term with AFFINE tag
       if the term is already affine then we return None
       otherwise a recursively annotated term ! 

   NB: we follow the following convention: 
       on multiplication between a non-affine term and an affine term, 
       this one is one the right.
   *)
   
   Open Scope option_scope.

   Fixpoint isCte (te: term): bool :=
     match te with
     | Cte _ => true
     | Annot _ te => isCte te
     | _ => false 
     end.  

  Definition annotAFFINEx te :=
   match te with
   | Annot AFFINE _ => te 
   | _ => Annot AFFINE te
   end.

   Lemma annotAFFINEx_correct te m: eval (annotAFFINEx te) m = eval te m.
   Proof.   
     destruct te; simpl; auto.
     destruct a; simpl; auto.
   Qed.

   Local Hint Resolve annotAFFINEx_correct.

   Fixpoint annotAFFINE_rec (te:term): option term   := 
    match te with
      | Annot AFFINE _ => None
      | Annot a t0 => 
         SOME t0' <- annotAFFINE_rec t0 -;
         Some (Annot a t0')
      | Add tl tr => 
         match annotAFFINE_rec tl with
         | Some tl' => match annotAFFINE_rec tr with
                       | Some tr' => Some (Add tl' tr')
                       | None => Some (Add tl' (annotAFFINEx tr))
                       end
         | None => SOME tr' <- annotAFFINE_rec tr -;
                   Some (Add (annotAFFINEx tl) tr')
         end
      | Opp t0 => 
         SOME t0' <- annotAFFINE_rec t0 -;
         Some (Opp t0')
      | Mul tl tr => 
         match annotAFFINE_rec tl with
         | Some tl' => match annotAFFINE_rec tr with
                       | Some tr' => Some (Mul tl' tr')
                       | None => Some (Mul tl' (annotAFFINEx tr))
                       end
         | None =>     match annotAFFINE_rec tr with
                       | Some tr' => Some (Mul tr' (annotAFFINEx tl))
                       | None => 
                          if (isCte tl) ||| (isCte tr) 
                          then None
                          else Some (Mul (annotAFFINEx tl) (annotAFFINEx tr))
                       end
         end
     | _ => None
     end.

  Lemma annotAFFINE_rec_correct te: 
    WHEN te' <- annotAFFINE_rec te THEN forall m, eval te' m = eval te m.
  Proof.
    induction te; simpl; try (xasimplify ltac:(eauto);
                              auto; intros; rewrite IHte2, N.MulComm; auto).
    - destruct a; simpl; xasimplify ltac:(eauto); auto.
  Qed.
  Local Hint Resolve annotAFFINE_rec_correct.


  (** Main function for annotating a term with AFFINE tag 
  *)
  Definition annotAFFINE te :=
   match annotAFFINE_rec te with
   | Some te' => te'
   | None => annotAFFINEx te
   end.

  Lemma annotAFFINE_correct te m: eval (annotAFFINE te) m = eval te m.
  Proof.
    unfold annotAFFINE; xasimplify ltac:(eauto).
  Qed.

  (** special cases for cte *)
   Fixpoint matchCte (te: term): option N.t :=
     match te with
     | Cte c => Some c
     | Annot _ te => matchCte te
     | _ => None
     end.
   Extraction Inline matchCte.

  Lemma matchCte_def te:
    WHEN c <- matchCte te THEN forall m, eval te m=c.
  Proof.
    induction te; simpl; auto.
  Qed.
  Hint Resolve matchCte_def: vpl.

  Close Scope option_scope.

  (** printing (for debugging) *)
  (* for debugging *)
  Import String.
  Open Scope string_scope.
  Fixpoint pr (te: term): string :=
    match te with
      | Var x =>  PVar.pr x
      | Cte c => N.pr c
      | Add tl tr => (pr tl) ++ "+" ++ (pr tr)
      | Opp te => "-(" ++ (pr te) ++ ")"
      | Mul tl tr => "(" ++ (pr tl) ++ ")*(" ++ (pr tr) ++ ")"
      | Annot a te => (Annot.pr a) ++ "(" ++ (pr te) ++ ")" 
    end.  
  Close Scope string_scope.  

End ModalTerm.

Module Type ASTermSig(N: NumSig).
  Include ModalTerm(N).
End ASTermSig.


Module BasicQTerm := ModalTerm QNum.
Module QTerm := BasicQTerm <+ AffineDecompose QNum QAffTerm BasicQTerm.

Module BasicZTerm := ModalTerm ZNum.
Module ZTerm := BasicZTerm <+ AffineDecompose ZNum ZAffTerm BasicZTerm.

Require Import ZNoneItv.

Record linearizeContext: Type := {
  nonaffine: ZTerm.t;     (* non-affine part of the term *)
  env: PVar.t -> ZNItv.t; (* environment *)
  affine: ZAffTerm.t;     (* affine part *)
  source: ZTerm.t;        (* source = nonaffine + affine *) 
  cmp: cmpG               (* guard: "0 cmp source" *)
}.



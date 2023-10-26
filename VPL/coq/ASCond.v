(** This module gives an abstract syntax (inspired from logic formula) for 
    "conditions", e.g. arbitrary boolean formula where atoms are 
    arithmetic constrains.

    At, the end of the module, some functors are provided to lift domains 
    with a "assume/assert" on Cstr into "assume/assert" on these conditions.

*)

Require Import Bool.
Require Import ZArith.
Require Export ASTerm.
Require Import LinTerm.
Require Import ASAtomicCond.
Require Import OptionMonad.
Require Export DomainInterfaces.
Require Import String.
Require Import List.

Inductive binl: Set := AND | OR.

Definition binlDenote (og: binl) : Prop -> Prop -> Prop
  := if og then and else or.
Extraction Inline binlDenote.  


(* polyhedra as logical expressions *)
Module Cond (N: NumSig) (Import Term: ASTermSig(N)). 

  Hint Resolve N.cmpDenote_dec: vpl.

  Inductive cond: Type :=
  | Basic (b: bool)
  | Atom (oc: cmpG) (tl tr: term)
  | BinL (op: binl) (cl cr: cond)
  | Not (c:cond) .

  Coercion Basic: bool >-> cond.
  Coercion Atom: cmpG >-> Funclass.
  Coercion BinL: binl >-> Funclass.

  Definition t := cond.

    (* Semantics *)
  Fixpoint sat (c:t) (m: Mem.t N.t): Prop := 
    match c with
      | Basic b => Is_true b
      | Atom oc tl tr => N.cmpDenote oc (eval tl m) (eval tr m)
      | BinL op cl cr => binlDenote op (sat cl m) (sat cr m)
      | Not c => ~(sat c m)
    end. 

  Lemma sat_dec (c: t) (m: Mem.t N.t): {sat c m} + {~ sat c m}.
  Proof.
    induction c; simpl; auto with vpl.
    - case b; simpl; auto.
    - case op; simpl; intuition.
    - intuition.
  Qed.

  Fixpoint xsat (c:t) (old new: Mem.t N.t): Prop := 
    match c with
      | Basic b => Is_true b
      | Atom oc tl tr => N.cmpDenote oc (xeval tl old new) (xeval tr old new)
      | BinL op cl cr => binlDenote op (xsat cl old new) (xsat cr old new)
      | Not c => ~(xsat c old new)
    end. 

  Lemma xsat_dec (c: t) (old new: Mem.t N.t): {xsat c old new} + {~ xsat c old new}.
  Proof.
    induction c; simpl; auto with vpl.
    - case b; simpl; auto.
    - case op; simpl; intuition.
    - intuition.
  Qed.

  (* Useless: derived from eval_pointwise_compat ?  
    Add Parametric Morphism: sat with
    signature Logic.eq ==> pointwise_relation PVar.t Logic.eq ==> Logic.eq
    as sat_compat.
    Proof.
       intros c m1 m2 H; induction c; simpl; try congruence.
       case oc; simpl; rewrite H; auto.
    Qed.
   *)

  Lemma xsat_sat c m: xsat c m m = sat c m.
  Proof.
    induction c; simpl; autorewrite with vpl; try congruence.
  Qed.
  Hint Rewrite xsat_sat: vpl.

  (* Useless: derived from eval_pointwise_compat ?
    Add Parametric Morphism: xsat with
    signature Logic.eq ==> pointwise_relation PVar.t Logic.eq ==> pointwise_relation PVar.t Logic.eq ==> Logic.eq
    as xsat_compat.
    Proof.
     intros c o1 o2 H1 n1 n2 H2; induction c; simpl; try congruence.
     case oc; simpl; rewrite H1; rewrite H2; auto.
    Qed.
  *)

   (** mayDependOn for conditions *)
  Fixpoint mayDependOn (c: cond) (x: PVar.t): Prop := 
    match c with
      | Basic _ => False
      | Atom _ tl tr => Term.mayDependOn tl x \/ Term.mayDependOn tr x 
      | BinL _ cl cr => mayDependOn cl x \/ mayDependOn cr x
      | Not c => mayDependOn c x
    end.

  Hint Resolve (@mdBounds_fold _ mayDependOn): progvar.

  Fixpoint mdBound (c:cond) (bound: positive): positive := 
    match c with
      | Basic _ => bound
      | Atom _ tl tr => Term.mdBound tl (Term.mdBound tr bound) 
      | BinL _ cl cr => mdBound cl (mdBound cr bound)
      | Not c => mdBound c bound
    end.

  Program Instance mdBound_mdBoundVar: MDBoundVar (mayDependOn:=mayDependOn) (mdBound:=mdBound).
  Obligation 1.
    generalize bound; induction e; simpl; intros; autorewrite with rwmax; auto.
    rewrite Term.mdBound_mdBoundVar_obligation_1 with (e:=tl);
    rewrite Term.mdBound_mdBoundVar_obligation_1 with (e:=tr);
    apply eq_sym.
    rewrite Term.mdBound_mdBoundVar_obligation_1.
    autorewrite with rwmax; auto.
    rewrite IHe1; rewrite IHe2. 
    apply eq_sym.
    rewrite IHe1; autorewrite with rwmax; auto.     
  Qed.
  Hint Resolve mdBound_mdBoundVar_obligation_1: progvar.
  Obligation 2.
    unfold mdBounds; generalize bound; induction e; simpl; intros; subst; intuition; eauto with progvar.
  Qed.
  Hint Resolve mdBound_mdBoundVar_obligation_2: progvar.

  Lemma sat_mdo: mdoExt mayDependOn sat Logic.eq.
  Proof.
    unfold mdoExt, bExt; induction e; simpl; intuition.
    - erewrite Term.eval_mdo with (m2:=m2); eauto. 
    erewrite Term.eval_mdo with (e:=tr) (m2:=m2); intuition eauto.
    - erewrite IHe; eauto.
  Qed.

  Lemma xsat_old_mdo old: mdoExt mayDependOn (fun c => xsat c old) Logic.eq.
  Proof.
    unfold mdoExt, bExt; induction e; simpl; intuition.
    - erewrite Term.xeval_old_mdo; auto.
    erewrite Term.xeval_old_mdo with (e:=tr); eauto.
    - erewrite IHe; eauto.
  Qed.

  Lemma xsat_new_mdo new: mdoExt mayDependOn (fun c old => xsat c old new) Logic.eq.
  Proof.
    unfold mdoExt, bExt; induction e; simpl; intuition.
    - erewrite xeval_new_mdo; auto.
    erewrite xeval_new_mdo with (e:=tr); eauto.
    - erewrite IHe; eauto.
  Qed.

  Fixpoint map (c:cond) f : cond :=
    match c with
      | Atom oc tl tr => Atom oc (Term.map tl f) (Term.map tr f) 
      | BinL op cl cr => BinL op (map cl f) (map cr f)
      | Not c => Not (map c f)
      | c0 => c0
    end.

  Lemma sat_map: forall c f m, sat (map c f) m = sat c (fun x => m (f x)).
  Proof.
    induction c; simpl; auto with vpl.
  Qed.

  Fixpoint xmap (c:cond) old new : cond := 
    match c with
      | Atom oc tl tr => Atom oc (Term.xmap tl old new) (Term.xmap tr old new) 
      | BinL op cl cr => BinL op (xmap cl old new) (xmap cr old new)
      | Not c => Not (xmap c old new)
      | c0 => c0
    end.

  Lemma xsat_xmap: forall c old new f g, xsat (xmap c f g) old new = xsat c (fun x => old (f x)) (fun x => new (g x)).
  Proof.
    induction c; simpl; auto with vpl.
  Qed.
  Hint Resolve xsat_xmap: vpl.

  (* 

  Elimination of negation in conditions (Negative Normal Form) 

  *)

      Definition dual (cmp: cmpG) (t1 t2: term): t :=
        match cmp with
          | Eq => Neq t1 t2
          | Le => Lt t2 t1
          | Lt => Le t2 t1
          | Neq => Eq t1 t2
        end.
      Extraction Inline dual.

      Lemma dual_sound: forall (cmp:cmpG) t1 t2 old new, ~(xsat (cmp t1 t2) old new) -> xsat (dual cmp t1 t2) old new.
      Proof.
        intros cmp t1 t2 old new; case cmp; simpl; autorewrite with num; auto.
        intro H; case (N.eqDec (xeval t2 old new) (xeval t1 old new)); auto.
        intros; case H; auto.
      Qed.
      Hint Resolve dual_sound: vpl.

      Fixpoint nnf (c:t):  t :=
        match c with
          | Atom op tl tr => op tl tr
          | BinL op cl cr => op (nnf cl) (nnf cr)
          | Not c0 => nnfNot c0
          | c0 => c0
        end
      with nnfNot (c:t):  t :=
        match c with
          | Basic b => negb b
          | Atom op tl tr => dual op tl tr
          | BinL AND cl cr => OR (nnfNot cl) (nnfNot cr)
          | BinL OR cl cr => AND (nnfNot cl) (nnfNot cr)
          | Not c0 => nnf c0
        end.

      Fixpoint nnf_xsound (c:t) old new {struct c}: (xsat c old new) -> (xsat (nnf c) old new)
      with nnfNot_xsound (c:t) old new {struct c}: ~(xsat c old new) -> (xsat (nnfNot c) old new).
      Proof.
        * destruct c; simpl; auto with vpl.
        case op; simpl; intuition.
        * destruct c; simpl; auto with vpl.
        - case b; simpl; auto.
        - case op; simpl; intuition.
        case (xsat_dec c1 old new); intuition.
        - intros H; case (xsat_dec c old new); intuition.
      Qed.
      Hint Resolve nnf_xsound: vpl.

      Lemma nnf_sound (c:cond) m: (sat c m) -> (sat (nnf c) m).
      Proof.
        rewrite <- !xsat_sat. auto with vpl.
      Qed.
      Hint Resolve nnf_sound: vpl.

      Lemma dual_complete: forall (cmp:cmpG) t1 t2 old new, xsat (dual cmp t1 t2) old new -> ~(N.cmpDenote cmp (xeval t1 old new) (xeval t2 old new)).
      Proof.
        intros cmp t1 t2 old new; case cmp; simpl in * |- *; autorewrite with num; auto.
      Qed.
      Hint Resolve dual_complete: vpl.

      Fixpoint nnf_xcomplete (c:t) old new {struct c}: (xsat (nnf c) old new) -> (xsat c old new)
      with NnfNot_xcomplete (c:t) old new {struct c}: (xsat (nnfNot c) old new) -> ~(xsat c old new).
      Proof.
        * destruct c; simpl; auto with vpl.
        case op; simpl; intuition.
        * destruct c; simpl; auto with vpl.
        - case b; simpl; auto.
        - case op; simpl; intuition eauto.
      Qed.
      Hint Resolve nnf_xcomplete: vpl.

      Lemma nnf_complete (c:cond) m: (sat (nnf c) m) -> (sat c m).
      Proof.
        rewrite <- !xsat_sat. auto with vpl.
      Qed.
      Hint Resolve nnf_complete: vpl.

      (* Nnf and mayDependOn *)
      Fixpoint nnf_mdBound (c:t) x {struct c}: mdBound (nnf c) x = mdBound c x
      with nnfNot_mdBound (c:t) x {struct c}: mdBound (nnfNot c) x = mdBound c x.
      Proof.
        * destruct c; simpl; auto.
           rewrite !nnf_mdBound; auto.
        * destruct c; simpl; auto.
           - case oc; simpl; auto;
             erewrite mdBound_comm; auto.
           - case op; simpl;
             rewrite !nnfNot_mdBound; auto.
      Qed.

  Hint Resolve nnf_xsound nnf_sound nnf_complete: vpl.

  (*
  Extraction nnf.
  *)

End Cond.

Module Type ASCondSig (N: NumSig). (* <: XCondSig N with Module Term := Term. *)

  Declare Module Term: ASTermSig N.

  Include Cond N Term.

End ASCondSig.


Module QCond <: ASCondSig QNum.

  Module Term := QTerm.

  Include Cond QNum QTerm.

End QCond.


Module ZCond <: ASCondSig ZNum.

  Module Term := ZTerm.

  Include Cond ZNum ZTerm.

End ZCond.



Open Scope impure.

(***
 A tiny functor that lift conditions from "AtomCond" to "Cond" 
 with full genericity on Nums.
***)

Module CondAssume (N: NumSig) (Import Cond: ASCondSig N) (AtomC: AtomicCondSig N Cond.Term)
                  (Import D: BasicDomain N) (AtomD: HasAssume N AtomC D) <: HasAssume N Cond D.

(** assumeRec: 
  for good precision, "Not" and "Neq" must have been eliminated from "c" ...
*)
  Definition skipBottom (a:t) (k: imp t): imp t :=
    BIND b <- isBottom a -;
    if b then (pure a) else k.
  
  Lemma skipBottom_correct a k: 
    WHEN a' <- skipBottom a k THEN 
     forall m, gamma a m -> (WHEN a'' <- k THEN forall m', gamma a'' m')
       -> gamma a' m. 
  Proof.
    VPLAsimplify.
  Qed.
  Extraction Inline skipBottom. (* IMPORTANT: lazy operator !  *)
  Hint Resolve skipBottom_correct: vpl.

  Fixpoint assumeRec (c:Cond.t) (a: t):  imp t :=
    match c with
      | Basic b => pure (if b then a else bottom)
      | Atom cmp tl tr => AtomD.assume (AtomC.make tl cmp tr) a
      | BinL AND cl cr => BIND aux <- assumeRec cl a -;
                          skipBottom aux
                          (assumeRec cr aux)
      | BinL OR cl cr => BIND auxl <- assumeRec cl a -;
                         BIND auxr <- assumeRec cr a -;
                         join auxl auxr
      | Not c0 => pure (failwith INTERN "assume:Not" top)
    end.

  Lemma assumeRec_correct: forall c a, WHEN p <- assumeRec c a THEN 
     forall m, sat c m -> gamma a m -> gamma p m.
  Proof.
    induction c; simpl.
    - destruct b; simpl; VPLAsimplify.
    - VPLAsimplify.
      simpl in * |- *. intros X m.
      rewrite <- AtomC.make_correct; 
     auto with vpl.
    - case op; simpl; xasimplify ltac:(intuition eauto with vpl).
    - VPLAsimplify.
  Qed.
  Local Hint Resolve assumeRec_correct: vpl.

  Definition assume (c:cond) (a: t):= skipBottom a (assumeRec (nnf c) a).

  Lemma assume_correct: forall c a, WHEN p <- assume c a THEN 
     forall m, sat c m -> gamma a m -> gamma p m.
  Proof.
    unfold assume; VPLAsimplify.
  Qed.
  Global Opaque assume.
  Global Hint Resolve assume_correct: vpl.

End CondAssume.


(* a naive generic version deriving "assert" from "assume" (using negation !) *)
Module NaiveAssert (N: NumSig) (Import Cond:ASCondSig N) (Import D: WeakAbstractDomain N Cond) <: HasAssert N Cond D.

  Open Scope impure.

  Definition assert (c:cond) (a:t) := 
    BIND aux <- assume (Not c) a -;
    (isBottom aux).

  Lemma assert_correct (c:cond) (a:t): If assert c a THEN forall m, (gamma a m) -> (sat c m).
  Proof.
    unfold assert; unfold trace; VPLAsimplify.
    intros X m; case (sat_dec c m); auto.
    intros H2 H3;  case (H0 m). 
    auto with vpl.
  Qed.
  Hint Resolve assert_correct: vpl.
  Global Opaque assert.

  Close Scope impure.

End NaiveAssert.


(* a generic assert from a assume *)
Module ASCondAssert (N: NumSig) 
  (Import Cond:ASCondSig N) 
  (Import D:WeakAbstractDomain N Cond)  
  <: HasAssert N Cond D.

  Module Naive := NaiveAssert N Cond D.

  Fixpoint assertRec (c:Cond.t) (a: t):  imp bool :=
    match c with
      | Basic b => if b then pure true else isBottom a
      | Atom Eq tl tr => 
        BIND b1 <- Naive.assert (Le tl tr) a -;
        if b1 
        then Naive.assert (Le tr tl) a
        else pure false 
      | BinL AND cl cr => 
        BIND b1 <- assertRec cl a -;
        if b1 
        then assertRec cr a
        else pure false 
      | _ => Naive.assert c a
    end.

(* NOTE on "assertRec" implementation:

For the AND we do not loose precision.

For the OR, we can not test if one of the branch is implied:
  x <= 2  implies  "x < 2" OR "0 < x < 3"
                  (i.e. "x <= 1" OR "1 <= x <= 2" sur Z !)
But it does not implies neither of these alternatives !


But, by going into negation:

 assert "x < 2  \/ (0 < x /\ x < 3)"
 
 devient

 assume "x >= 2 /\ ( x <= 0 \/ x >= 3)" in "x <= 2"

reduces to "bottom" with the algorithm of ZCondAssume !

And,
 
  assume "( x <= 0 \/ x => 3) /\ x >= 2" in "x <= 2"

also reduces to "bottom" !
*)

  Lemma assertRec_correct (c:cond) (a:t): If assertRec c a THEN forall m, (gamma a m) -> (sat c m).
  Proof.
    induction c; try (VPLAsimplify; fail).
    - case b; VPLAsimplify.
    - (* Atom *) case oc; simpl; VPLAsimplify.
      intros; rewrite <- N.LeLeEq. intuition.
    - (* AND *) case op; simpl; VPLAsimplify.
  Qed.

  Local Hint Resolve assertRec_correct: vpl.

  Definition assert (c:Cond.t) (a: t):= assertRec (nnf c) a.
  Lemma assert_correct (c:cond) (a:t): If assert c a THEN forall m, (gamma a m) -> (sat c m).
  Proof.
    unfold assert; VPLAsimplify.
  Qed.
  Global Opaque assert.
  Global Hint Resolve assert_correct: vpl.

End ASCondAssert.


(* a naive (and inefficient) implementation of rename 
 THIS IS USELESS ! (Just for fun :-)
*)
Module NaiveRename (Import BasicD: BasicDomain ZNum) (Import D: HasAssume ZNum ZCond BasicD) <: HasRename ZNum BasicD.

  Import ZCond.
  Import BasicD.

  Definition rename (x y: PVar.t) (a:t): imp t :=
    BIND p <- assume (Eq (Term.Var y) (Term.Var x)) a -;
    project p x.

  Lemma rename_correct: forall x y a, WHEN p <- (rename x y a) THEN
    forall m, gamma a (Mem.assign x (m y) m) -> gamma p m.
  Proof.
    unfold Basics.impl, rename.
    intros; xasimplify ltac:(eauto with vpl). simpl in * |- *.
    intros X m H0. eapply gamma_ext.
    Focus 3. 
      eapply project_correct; [ eauto | eapply H; [idtac | eauto]].
      autorewrite with progvar.
      unfold Mem.assign. case (PVar.eq_dec x y); auto.
    auto.
    autorewrite with progvar.
    intros x'; erewrite @Mem.assign_id; auto.
  Qed. 

End NaiveRename.

Close Scope impure.


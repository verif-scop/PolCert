Require String.
Require Export LinTerm.
Require Export Debugging.
(* Require Export DomainInterfaces. (* Removed because of circular dependencies. *) *)
Require Import CoqAddOn.
Require Import Ring_polynom_AddOnQ.

Open Scope option.

Module Type CstrSig. (* <: CondSig QNum. (* Keep this true ! *) *)
(** This is the interface for linear relation representations. *)

  Parameter t: Type.

  Parameter sat: t -> Mem.t QNum.t -> Prop.

  Parameter mayDependOn: t -> PVar.t -> Prop.
  Parameter sat_mdo: mdoExt mayDependOn sat Logic.eq.

  Definition Incl (c1: t) (c2: t): Prop
    := forall m, sat c1 m -> sat c2 m.
  Hint Unfold Incl: pedraQ.

  Parameter isEq: t -> t -> bool.
  Parameter isEq_correct: forall c1 c2: t, If isEq c1 c2 THEN Incl c1 c2.
  Hint Resolve isEq_correct: pedraQ.

  Parameter isContrad: t -> bool.
  Parameter isContrad_correct: forall c: t, If isContrad c THEN forall m, (sat c m)->False.
  Hint Resolve isContrad_correct: pedraQ.

  Parameter top: t.
  Parameter top_correct: forall m, sat top m.

  Parameter triv: cmpT -> QNum.t -> t.
  Parameter triv_correct: forall typ n m, sat (triv typ n) m.
  Hint Resolve triv_correct: pedraQ.

  Parameter to_le: t -> t.  
  Parameter to_le_correct: forall c m, sat c m -> sat (to_le c) m.
  Hint Resolve to_le_correct: pedraQ.

  Parameter add: t -> t -> t.
  Parameter add_correct: forall (c1 c2: t) m,
    sat c1 m -> sat c2 m -> sat (add c1 c2) m.

  Parameter mul: QNum.t -> t -> t.
  Parameter mul_correct: forall n c m, sat c m -> sat (mul n c) m.

  Parameter merge: t -> t -> t.
  Parameter merge_correct: forall c1 c2 m, sat c1 m -> sat c2 m -> sat (merge c1 c2) m.

  Hint Resolve top_correct add_correct mul_correct merge_correct: pedraQ.

  Parameter isFree: PVar.t -> t -> bool.
  Parameter isFree_correct: forall (x: PVar.t) (c: t), (If (isFree x c) THEN ~(mayDependOn c x)).
  Hint Resolve isFree_correct:pedraQ.

  (* Rename *)
  Parameter rename: PVar.t -> PVar.t -> t -> t.
  Parameter rename_correct: forall (x y:PVar.t) (l:t) m, 
    (sat (rename x y l) m)=(sat l (Mem.assign x (m y) m)).

  Parameter pr: t -> String.string.
  Parameter to_string: (PVar.t -> String.string) -> t -> String.string.

End CstrSig.

Module CstrImpl (L: LinSig QNum) <: CstrSig.
(** Standard parametric representation in a normalized form,
with all variables on one side of the relation operator and the
constant on the other. *)

  Record tInd: Type := mk { coefs: L.t; typ: cmpT; cst: QNum.t }.
  Definition t := tInd.

  Import String.
  Local Open Scope string_scope.

  Definition cmpPr: cmpT -> string
    := fun c =>
      match c with
        | EqT => "="
        | LeT => "<="
        | LtT => "<"
      end.

  Definition pr: t -> string
    := fun c => (L.pr (coefs c)) ++ " " ++ (cmpPr (typ c))
      ++ " " ++ (QNum.pr (cst c)).

  Definition to_string (f: PVar.t -> string) (c:t): string
    := (L.to_string f (coefs c)) ++ " " ++ (cmpPr (typ c))
      ++ " " ++ (QNum.pr (cst c)).

  Definition sat (c: t) m: Prop
    := QNum.cmpDenote (typ c) (L.eval (coefs c) m) (cst c).

  Definition mayDependOn (c:t) (x: PVar.t) : Prop :=
    L.mayDependOn (coefs c) x.

  Lemma sat_mdo: mdoExt mayDependOn sat Logic.eq.
  Proof.
    unfold mdoExt, bExt, sat, mayDependOn; destruct e; simpl.
    intros; erewrite L.eval_mdo; eauto.
  Qed. 

  Definition top := {| coefs:= L.nil; typ:= EqT; cst:=QNum.z |}.

  Lemma top_correct m: sat top m.
  Proof.
    unfold sat; rewrite L.NilEval.
    simpl; auto.
  Qed.
  Hint Resolve top_correct: pedraQ.

  Definition bot := {| coefs:= L.nil; typ:= EqT; cst:=QNum.u |}.

  Lemma bot_correct m: ~(sat bot m).
  Proof.
    unfold sat; rewrite L.NilEval.
    simpl. apply QNum.ZNotU.
  Qed.
  Hint Resolve bot_correct: pedraQ.

  Definition triv (typ:cmpT) (n:QNum.t) :=  
  if QNum.cmpDenote_dec typ QNum.z n then
    {| coefs:= L.nil; typ:= typ; cst:=n |}
  else
    failwith CERT "triv: unsat arg" top.

  Lemma triv_correct typ n m: sat (triv typ n) m.
  Proof.
    unfold triv, sat.
    destruct (QNum.cmpDenote_dec typ QNum.z n);
    simpl; rewrite L.NilEval; auto.
  Qed.
  Hint Resolve triv_correct: pedraQ.

  Definition to_le  (c: t): t :=  
    {| coefs:= (coefs c); typ:= LeT; cst:=(cst c) |}.

  Lemma to_le_correct c m: sat c m -> sat (to_le c) m.
  Proof.
    unfold to_le, sat. destruct (typ c); simpl; auto with num.
    intros H; rewrite H; auto with num.
  Qed.
  Hint Resolve to_le_correct: pedraQ.


  Definition Incl (c1: t) (c2: t): Prop
    := forall m, sat c1 m -> sat c2 m.

  (* tactic to destruct "typ c" (where c:t) 
     with introduction on a hypothesis H of the form "typ c = ..."
  *)
  Ltac destructyp c H :=
    elimtype (exists x, (typ c)=x); eauto;
      let cmp:=fresh "cmp" in
        intros cmp H; rewrite !H in * |- *; destruct cmp; simpl.


  Definition isContrad (c: t): bool :=
    L.isEq (coefs c) L.nil
    &&& match typ c with
          | EqT => if QNum.eqDec QNum.z (cst c) then false else true
          | LtT => if QNum.ltLeDec QNum.z (cst c) then false else true
          | LeT => if QNum.ltLeDec (cst c) QNum.z then true else false
        end.

  Lemma isContrad_correctx c: If isContrad c THEN forall m, ~(sat c m).
  Proof.
    unfold isContrad, sat. 
    destructyp c X; PedraQsimplify;
    intros; rewrite H, L.NilEval; eauto with num.
  Qed.

  Lemma isContrad_correct c: If isContrad c THEN forall m, (sat c m)->False.
  Proof isContrad_correctx c.
  Hint Resolve isContrad_correct: pedraQ.
  Global Opaque isContrad. 

  Local Hint Resolve cmpT_eq_correct: pedraQ.

  Definition isEq (c1 c2: t): bool :=
    QNum.eqDec (cst c1) (cst c2)
    &&& cmpT_eq (typ c1) (typ c2)
    &&& L.isEq (coefs c1) (coefs c2).

  Lemma isEq_correct c1 c2: If isEq c1 c2 THEN Incl c1 c2.
  Proof.
    destruct c1, c2; simpl.
    unfold isEq, Incl, sat; PedraQsimplify; subst.
    unfold L.Eq. intros X m; rewrite X. auto.
  Qed.
  Hint Resolve isEq_correct: pedraQ.
  Global Opaque isEq.

  Definition cmpAdd: cmpT -> cmpT -> cmpT
    := fun t1 t2 =>
      match t1 with
        | EqT => t2
        | LtT => LtT
        | LeT =>
          match t2 with
            | EqT => LeT
            | LeT => LeT
            | LtT => LtT
          end
      end.

  Definition add (c1 c2: t): t :=
    mk (L.add (coefs c1) (coefs c2)) (cmpAdd (typ c1) (typ c2))
    (QNum.add (cst c1) (cst c2)).

  Lemma add_correct: forall (c1 c2: t) m,
    sat c1 m -> sat c2 m -> sat (add c1 c2) m.
  Proof.
    intros c1 c2 x; destruct c1 as [lt1 ty1 c1], c2 as [lt2 ty2 c2]; unfold sat, add; simpl;
      rewrite L.Add_correct;
        destruct ty1; destruct ty2; simpl; intros; subst;
          ((auto with num; fail) || (rewrite QNum.AddComm, (QNum.AddComm (cst c1) (cst c2)); auto with num)).
  Qed.

  Definition mulSimpl (c: t) n: t :=
    mk (L.mul n (coefs c)) (typ c) (QNum.mul n (cst c)).

  Lemma mulSimpl_correct: forall (c: t) n (hn: typ c = EqT \/ not (QNum.Le n QNum.z))
    m, sat c m -> sat (mulSimpl c n) m.
    intros c n hn x; unfold sat, mulSimpl; simpl;
      destruct hn as [hn | hn];
        [ rewrite hn; simpl; rewrite (L.Mul_correct n (coefs c) x); intro h; rewrite h; trivial
          | destruct (typ c); simpl; rewrite (L.Mul_correct n (coefs c) x)].
    - intro h; rewrite h; trivial.
    - apply QNum.MulLe1, QNum.LtLe, QNum.LtNotLe.
    assumption.
    - apply QNum.MulLt, QNum.LtNotLe.
    assumption.
  Qed.
  Local Hint Resolve mulSimpl_correct: pedraQ.

  Definition mul (n: QNum.t) (c: t): t :=
    match typ c with
      | EqT => mulSimpl c n
      | _ => if QNum.ltLeDec QNum.z n then mulSimpl c n else failwith CERT "mul" top
    end.

  Lemma mul_correct n c m: sat c m -> sat (mul n c) m.
  Proof.
    unfold mul.
    destructyp c X;
    destruct (QNum.ltLeDec QNum.z n); simpl;
      intuition eauto with pedraQ num.
  Qed.

  Definition merge c1 c2: t := 
    match typ c1 with
      | LeT => 
        match typ c2 with
          | LeT =>
            if L.isEq (coefs c2) (L.opp (coefs c1)) then
              if QNum.eqDec (cst c2) (QNum.opp (cst c1)) then
                mk (coefs c1) EqT (cst c1)
                else
                  failwith CERT "merge_1" top
              else
                failwith CERT "merge_2" top
          | _ => failwith CERT "merge_3" top
        end
      | _ => failwith CERT "merge_4" top
    end.

  Lemma merge_correct c1 c2 m: sat c1 m -> sat c2 m -> sat (merge c1 c2) m.
  Proof.
    unfold merge.
    destructyp c1 X1; auto with pedraQ.
    destructyp c2 X2; auto with pedraQ.
    intros H1 H2.
    PedraQsimplify; simpl; auto.
    intro H3. case (QNum.eqDec (cst c2) (QNum.opp (cst c1))); simpl; auto with pedraQ.
    intro H4; unfold sat in * |- *.
    rewrite X1, X2, H3, H4 in * |- *; simpl in * |- *.
    autorewrite with linterm in H2.
    auto with num.
  Qed.

(*
  Definition split (c: t): option (t * t) :=
    match c with
      | mk a EqT b => Some (mk a LeT b, mk (L.opp a) LeT (QNum.opp b))
      | _ => None
    end.

  Hint Resolve add_correct mul_correct merge_correct: pedraQ.

  Lemma split_correct c: WHEN p <- split c THEN Incl c (fst p) /\ Incl c (snd p).
  Proof.
    unfold split, Incl.
    destruct c as [ c0 ty0 cst0].
    destruct ty0; simpl; auto.
    unfold sat; simpl; intuition subst; autorewrite with linterm; auto with num.
  Qed.
  Local Hint Resolve split_correct: pedraQ.
*)

  Definition isFree (x: PVar.t) (c: t): bool
    := L.isFree x (coefs c).

  Lemma isFree_correct: forall (x: PVar.t) (c: t), (If (isFree x c) THEN ~(mayDependOn c x)).
  Proof.
    PedraQsimplify. 
  Qed.
  Hint Resolve isFree_correct: pedraQ.

  Definition rename x y c : t 
    := {| coefs:= L.rename x y (coefs c); typ:=(typ c); cst:=(cst c) |}.
  
  (** Below, the preservation of this strong property from LinTerm to CstrC
      is simpler to prove than the preservation of a weaker version using 
      an hypothesis than [y] has no effect on the result.
 
      Indeed, it is not obvious to prove than if [y] has no effect on the result 
      of [sat c] then it has no effect on the result of [eval (coef c)].
  *) 
  Lemma rename_correct (x y:PVar.t) (l:t) m: 
    (sat (rename x y l) m)=(sat l (Mem.assign x (m y) m)).
  Proof.
    unfold rename, sat; simpl. 
    rewrite L.rename_correct. auto.
  Qed.

End CstrImpl.

Module Cstr <: CstrSig.

  Include CstrImpl LinQ.

  (** Intervals *)

  Definition upperToCstr (v: LinQ.t) (n: QNum.t): t
   := {| coefs:= v ; typ:= LtT; cst := n |}.

  Lemma upperToCstr_correct l n m:
    sat (upperToCstr l n) m -> QNum.Lt (LinQ.eval l m) n.
  Proof.
    unfold upperToCstr, sat; simpl; auto.
  Qed.

  Definition upperOrEqualsToCstr (v: LinQ.t) (n: QNum.t): t
   := {| coefs:= v ; typ:= LeT; cst := n |}.

  Lemma upperOrEqualsToCstr_correct l n m:
    sat (upperOrEqualsToCstr l n) m -> QNum.Le (LinQ.eval l m) n.
  Proof.
    unfold upperOrEqualsToCstr, sat; simpl; auto.
  Qed.

  Definition lowerToCstr (v: LinQ.t) (n: QNum.t): t
   := {| coefs:=LinQ.opp v ; typ:= LtT; cst := QNum.opp n |}.

  Lemma lowerToCstr_correct l n m:
    sat (lowerToCstr l n) m -> QNum.Lt n (LinQ.eval l m).
  Proof.
    unfold lowerToCstr, sat; simpl; autorewrite with linterm num; auto.
  Qed.

  Definition lowerOrEqualsToCstr (v: LinQ.t) (n: QNum.t): t
   := {| coefs:=LinQ.opp v ; typ:= LeT; cst := QNum.opp n |}.

  Lemma lowerOrEqualsToCstr_correct l n m:
      sat (lowerOrEqualsToCstr l n) m -> QNum.Le n (LinQ.eval l m).
  Proof.
    unfold lowerOrEqualsToCstr, sat; simpl; autorewrite with linterm num; auto.
  Qed.

  Definition to_PExpr : t -> PExpr
  := fun cstr => PEsub (PEc (QNum.to_Q (cstr.(cst)))) (LinQ.to_PExpr (cstr.(coefs))) .

  Hint Resolve upperToCstr_correct upperOrEqualsToCstr_correct lowerToCstr_correct lowerOrEqualsToCstr_correct: pedraQ.
 
  (* Opaque upperToCstr upperOrEqualsToCstr lowerToCstr lowerOrEqualsTo *)

End Cstr.

Close Scope option.

Require String.
Require Export OptionMonad.
Require Export NumC.
Require Export ProgVar.
Require Export Debugging.
Require Import PositiveMapAddOn.
Require Import Sorting.Permutation.
Require Import Ring_polynom_AddOnQ.
Require Import Qop.

(* database used until "PedraQ" construction *)
Create HintDb pedraQ discriminated.

(* a tiny wrapper to OptionMonad.simplify *)
Ltac PedraQsimplify :=
  xsimplify ltac:(eauto with pedraQ).


Module Type LinSig(N: NumSig).
(** The interface of that an implementation of linear terms must provide.
*)

  Parameter t: Type.

  Parameter eval: t -> Mem.t N.t -> N.t.

  Parameter mayDependOn: t -> PVar.t -> Prop.
 
  Parameter eval_mdo: mdoExt mayDependOn eval Logic.eq.

  Parameter nil: t.
  Parameter NilEval: forall m, eval nil m = N.z.

  Parameter isNil: t -> bool.
  Parameter IsNil_correct: forall lt, If isNil lt THEN lt=nil.

  Parameter single: PVar.t -> N.t -> t.
  Parameter single_correct: forall x n m, eval (single x n) m = N.mul (m x) n.

  Parameter opp: t -> t.
  Parameter Opp_correct: forall lt m, eval (opp lt) m = N.opp (eval lt m).

  Parameter mul: N.t -> t -> t.
  Parameter Mul_correct: forall n lt m, eval (mul n lt) m = N.mul n (eval lt m).

  Definition Eq (lt1 lt2: t): Prop
    := forall m, eval lt1 m = eval lt2 m.

  Parameter isEq: t -> t -> bool.
  Parameter isEq_correct: forall lt1 lt2, If isEq lt1 lt2 THEN Eq lt1 lt2.


  Parameter add: t -> t -> t.
  Parameter Add_correct: forall lt1 lt2 m, eval (add lt1 lt2) m = N.add (eval lt1 m) (eval lt2 m).

  Definition exportT: Set
    := list (PVar.t * N.t).

  Parameter export: t -> exportT.

  Parameter export_correct: forall lt m,
    (eval lt m)=List.fold_right (fun p sum => N.add sum (N.mul (m (fst p)) (snd p)))
                       N.z  (export lt).


  Parameter isFree: PVar.t -> t -> bool.
  Parameter isFree_correct: forall x l, If isFree x l THEN ~(mayDependOn l x).
  Global Hint Resolve IsNil_correct isEq_correct isFree_correct:pedraQ.
  Hint Rewrite NilEval Add_correct Mul_correct Opp_correct single_correct: linterm.
  Hint Rewrite <- export_correct: linterm.

  (** Rename of a variable by an arbitrary variable. 
      we choose a strong version because proofs are simpler in CstrC.v and ConsSet.v !
  *)
  Parameter rename: PVar.t -> PVar.t -> t -> t.
  Parameter rename_correct: forall (x y:PVar.t) (l:t) m, 
    (eval (rename x y l) m)=(eval l (Mem.assign x (m y) m)).

  Parameter pr: t -> String.string.
  Parameter to_string: (PVar.t -> String.string) -> t -> String.string.

End LinSig.

Module PositiveMapVec (Import N: NumSig) <: LinSig N.
(** Implementation of linear terms as radix map-tree from variable to coefficients (PositiveMap.t).

Implicit invariant for this data structure: there is no explicit zero coefficient, nor un-needed 
"None" in the PositiveMap (or in other word, PositiveMaps are only handled in normal form).

However, this invariant is not needed for correctness (but only for efficiency & precision).
Hence, we do not prove it !
*)

  Local Open Scope type_scope.
  Local Open Scope list_scope.
  Import List.ListNotations.

  Definition t: Type
    := PositiveMap.t N.t.

  Definition absEval (l: list (PVar.t*N.t)) (m:Mem.t N.t) : N.t :=
   List.fold_right (fun p sum => N.add sum (N.mul (m (fst p)) (snd p)))
                       N.z  l.

  Definition eval (lt:t) (m:Mem.t N.t) : N.t
    := absEval (PositiveMap.elements lt) m.

  Definition mayDependOn (lt:t) (x: PVar.t) : Prop 
    := List.fold_right (fun p sum => x=(fst p) \/ sum)
                        False
                        (PositiveMap.elements lt).

  Lemma mayDependOn_altDef (lt:t) (x: PVar.t): mayDependOn lt x <-> exists c, List.In (x,c) (PositiveMap.elements lt).
  Proof.
    unfold mayDependOn; induction (PositiveMap.elements lt); simpl; firstorder (subst; eauto).
    destruct a; simpl. eapply ex_intro; eauto.
  Qed.

  Lemma eval_mdo: mdoExt mayDependOn eval Logic.eq.
  Proof.
    unfold mdoExt, bExt, mayDependOn, eval. intro e; induction (PositiveMap.elements e); simpl; auto.
  Qed. 

  Definition exportT: Set
    := list (PVar.t * N.t).

  Extraction Inline PositiveMap.fold PositiveMap.xfoldi.
  Definition export (lt: t) : exportT
    := PositiveMap.fold (fun x c l => (x,c)::l) lt nil.
 
(*
   Lemma List_fold_right_remark0 (l: list (PVar.t * N.t)) m: forall acc1 acc2,
   N.add (List.fold_right (fun p sum => N.add sum (N.mul (m (fst p)) (snd p)))
                      acc1 l) acc2 =
    List.fold_right (fun p sum => N.add sum (N.mul (m (fst p)) (snd p)))
                      (N.add acc1 acc2) l.
 Proof.
    induction l as [| (x,c) l' IHl' ]; simpl.
    - intros; ring.
    - intros acc1 acc2.
      rewrite <- IHl'.
      ring.
 Qed.

 Lemma absEval_remark1 (l: list (PVar.t * N.t)) m: forall acc,
   N.add (absEval l m) acc =
    List.fold_right (fun p sum => N.add sum (N.mul (m (fst p)) (snd p)))
                      acc l.
  Proof.
    unfold absEval; intros; rewrite List_fold_right_remark0. cutrewrite (N.add N.z acc = acc); auto.
    ring.
  Qed.
*)
  
 Lemma absEval_remark2 l m: forall l2,
  N.add
  (absEval
     (List.fold_left
        (fun (a : list (positive * N.t)) (p : PositiveMap.key * N.t) =>
         (fst p, snd p) :: a) l []) m) (absEval l2 m) =
  absEval
    (List.fold_left
      (fun (a : list (positive * N.t)) (p : PositiveMap.key * N.t) =>
       (fst p, snd p) :: a) l l2) m.
  Proof.
    induction l as [| (x,c) l' IHl' ]; simpl.
    -  intros; ring.
    - intros l2. unfold PVar.t, PositiveMap.key in * |- *. rewrite <- (IHl' ((x, c) :: l2)).
      rewrite <- IHl'. simpl. ring.
  Qed.

  Lemma export_correct lt: forall m,
    (eval lt m)=absEval (export lt) m.
  Proof.
    unfold eval, export.
    intros; rewrite PositiveMap.fold_1.
    induction (PositiveMap.elements lt) as [| (x,c) l IHl]; clear lt; simpl; auto.
    rewrite IHl. rewrite <- (absEval_remark2 _ _ [(x,c)]).
    simpl. apply f_equal. ring.
  Qed.
 
 
  Definition nil: t
    := PositiveMap.Leaf.

  Lemma NilEval: forall m, eval nil m = N.z.
  Proof.
    intro m;
    reflexivity.
  Qed.

  Definition isNil (lt:t) := match lt with PositiveMap.Leaf => true | _ => false end.

  Lemma IsNil_correct: forall lt, If isNil lt THEN lt=nil.
  Proof.
     unfold eval; intros lt; case lt; simpl; xsimplify ltac:(eauto with PedraQ); auto.
  Qed.

  Definition single (x:PVar.t) (n:N.t) : t :=
    if N.isZero n then nil else single x n.

  Lemma single_correct: forall x n m, eval (single x n) m = N.mul (m x) n.
  Proof.
    intros; unfold single.
    case (N.isZero n).
    - intros; subst; ring_simplify; auto.
    - intros; unfold eval; rewrite elements_single; simpl.
      ring.
  Qed.

  Extraction Inline map option_map.
  Definition opp (lt:t) := map (fun c => N.opp c) lt.

  Lemma Opp_correct: forall lt m, eval (opp lt) m = N.opp (eval lt m).
  Proof.
    intros; unfold eval, opp; rewrite elements_map.
    generalize (PositiveMap.elements lt); induction l; simpl; ring_simplify; try rewrite IHl; auto.
  Qed.

  Definition mul (n:N.t) (lt:t) : t
    := match N.mulDiscr n with 
       | IsZero => nil
       | IsUnit => lt
       | IsOppUnit => opp lt
       | Other => map (fun c => N.mul n c) lt
       end.

  Lemma Mul_correct: forall n lt m, eval (mul n lt) m = N.mul n (eval lt m).
  Proof.
    intros; unfold mul.
    generalize (N.mulDiscr_correct n); destruct (N.mulDiscr n); simpl; try (intro H; rewrite H; ring_simplify); auto.
    - apply Opp_correct.
    - intros; unfold eval; rewrite elements_map.
      generalize (PositiveMap.elements lt); induction l; simpl.
      ring.
      rewrite IHl. clear IHl; ring_simplify. auto.
  Qed. 
 
  Definition Eq (lt1 lt2: t): Prop
    := forall m, eval lt1 m = eval lt2 m.

  Definition N_eqb (x y: N.t): bool :=N.eqDec x y ||| false.

  Lemma N_eqb_correct: forall x y, If N_eqb x y THEN x=y.
  Proof.
    unfold N_eqb; intros; PedraQsimplify.
  Qed.

  Definition isEq: t -> t -> bool := (equal N_eqb).

  Local Hint Resolve (equal_correct _ N_eqb_correct) : PedraQ.
  Lemma isEq_correct: forall lt1 lt2, If isEq lt1 lt2 THEN Eq lt1 lt2.
  Proof.
    unfold isEq. xsimplify ltac:(eauto with PedraQ).
    intros; subst; unfold Eq; auto.
  Qed.

  Extraction Inline merge.
  Definition add: t -> t -> t
    := merge (fun n1 n2 => let r:=N.add n1 n2 in
                            if N.isZero r then None else Some r).

  Lemma Add_correct: forall lt1 lt2 m, eval (add lt1 lt2) m = N.add (eval lt1 m) (eval lt2 m).
  Proof.
    unfold add, eval; intros lt1 lt2.
    set (f:=(fun n1 n2 => let r:=N.add n1 n2 in
                            if N.isZero r then None else Some r)).
    generalize (elements_merge f lt1 lt2).
    generalize (PositiveMap.elements lt1) (PositiveMap.elements lt2) (PositiveMap.elements (merge f lt1 lt2)).
    unfold f; clear f.
    induction 1; simpl in * |- *.
    - intros; ring_simplify; auto.
    - intros; ring_simplify; auto.
    - intros; rewrite IHinMerge. ring_simplify; auto.
    - intros; rewrite IHinMerge. 
      destruct (N.isZero (N.add v1 v2)) as [X | X]; try discriminate.
      injection H; intro; subst. ring_simplify; auto.
    - intros; rewrite IHinMerge. destruct (N.isZero (N.add v1 v2)) as [X|X]; try discriminate.
      cutrewrite (v2 = N.sub N.z v1).
      ring_simplify; auto.
      rewrite <- X; ring.
    - intros; rewrite IHinMerge. ring_simplify; auto.
  Qed.
  Hint Rewrite NilEval Add_correct Mul_correct Opp_correct single_correct: linterm.


  Definition isFree (x: PVar.t) (l: t): bool := negb (PositiveMap.mem x l).

  Lemma isFree_correct: forall x l, If (isFree x l) THEN ~(mayDependOn l x).
  Proof.
    unfold isFree; PedraQsimplify.
    rewrite mayDependOn_altDef.
    intro H; destruct H as [v H].
    erewrite In_mem in Heq_simplified; eauto.
    discriminate.
  Qed.
  Hint Resolve IsNil_correct isFree_correct isEq_correct: pedraQ.

  Lemma absEval_permutation l l' m: Permutation l l' -> absEval l m=absEval l' m.
  Proof.
    induction 1; simpl; congruence || ring.
  Qed.

  Lemma eval_remove_free x (l:t) v m: eval (PositiveMap.remove x l) (Mem.assign x v m)= eval (PositiveMap.remove x l) m.
  Proof.
    unfold eval. rewrite elements_remove.
    induction (PositiveMap.elements l); simpl; auto.
    unfold eq_key at 1 4.
    destruct a as (x1,c1); simpl.
    destruct (BinPos.Pos.eq_dec x x1); simpl; auto.
    rewrite Mem.assign_out; auto.
  Qed.

  (** Below, a rename that works even if [y] is not free in [l] 
      It is simple to prove using previous lemmas.

      Actually, exploiting the fact that [y] is free, we could optimize
      a bit using:
          [PositiveMap.add y c (PositiveMap.remove x l)]
      instead of [add (single y c) (PositiveMap.remove x l)]

      However, this tiny optimization would results in much harder proofs in CstrC.v
      and ConsSet.v ! 

      A more interesting optimization could be to have a [find/remove] in one operation on the map.
  *)
  Definition rename (x y: PVar.t) (l:t) : t :=
    match PositiveMap.find x l with
    | Some c => add (single y c) (PositiveMap.remove x l)
    | None => l
    end.

  Lemma rename_correct (x y:PVar.t) (l:t) m: 
    (eval (rename x y l) m)=(eval l (Mem.assign x (m y) m)).
  Proof.
    unfold rename. 
    generalize (find_remove_elements_Permutation x l) (eval_remove_free x l (m y) m).
    case (PositiveMap.find x l); simpl.
    - intros v H. autorewrite with linterm. 
      unfold eval. rewrite <- (absEval_permutation _ _ _ H).
      simpl. autorewrite with progvar.
      intros H1; rewrite H1; ring.
    - unfold eval. intros H; rewrite H; auto.
  Qed.

  Import String.
  Local Open Scope string_scope.

  Fixpoint fmtAux (l: list string): string -> string
    := fun s =>
         match l with
           | [] => s
           | prem::l' => fmtAux l' (prem ++ s)
         end.

  Definition fmt (l: list string): string
    :=  match l with
           | [] => "0"
           | prem::l' => fmtAux l' prem
         end.

  Definition pairPr (p: PVar.t * N.t) : string
    := "+ " ++ (PVar.pr (fst p)) ++ " * " ++ (N.pr (snd p)).

  Definition pr: t -> string
    := fun lt => 
           let l:=(PositiveMap.elements lt) in fmt (List.rev (List.map pairPr l)).

  Definition pair_to_string (f: PVar.t -> string) (p: PVar.t * N.t) : string
    := "+ " ++ (f (fst p)) ++ " * " ++ (N.pr (snd p)).

  Definition to_string (f: PVar.t -> string) (lt: t): string
    := let l:=(PositiveMap.elements lt) in fmt (List.rev (List.map (pair_to_string f) l)).

  Hint Rewrite NilEval Add_correct Mul_correct Opp_correct single_correct: linterm.

End PositiveMapVec.

Module LinZ <: LinSig ZNum := PositiveMapVec ZNum.

Module LinQ <: LinSig QNum.

  Include PositiveMapVec QNum.
  
  (* Ajout pour Handelman *)
  Local Open Scope list_scope.
  Import List.ListNotations.

  Fixpoint exportT_to_PExpr (e: exportT) :PExpr 
  := match e with
  | [] => PEc 0
  | (v,c)::tail => PEadd (PEmul (PEc (QNum.to_Q c)) (PEX _ v)) (exportT_to_PExpr tail)
  end.

  Definition to_PExpr : t -> PExpr 
  := fun lt => exportT_to_PExpr (export lt).

  Definition mem_compat (m:Mem.t QNum.t) (p:positive) : Q :=
  QNum.to_Q (m (p)).

  Lemma exportT_prop l (m: Mem.t QNum.t): 
  Qcanon.Q2Qc (PEsem (exportT_to_PExpr l) (mem_compat m)) 
  = (List.fold_right (fun p sum => QNum.add sum (QNum.mul (m (fst p)) (snd p))) QNum.z l).
  Proof.
    induction l; auto.
    simpl exportT_to_PExpr.
    destruct a.
    simpl PEsem.
    assert (app_eq : [(t0, t1)] ++ l = (t0,t1) :: l) by auto.
    rewrite <- app_eq.
    rewrite List.fold_right_app.
    simpl List.fold_right.
    rewrite <- IHl.
    unfold mem_compat.
    apply QOp.Qcanon_distrib_Q2Qc.
  Qed.

  (* Fin ajout pour Handelman *)

  Definition import: exportT -> t
    := fun l => List.fold_left (fun lt p => add (single (fst p) (snd p)) lt) l nil.

  Definition lift (lt:LinZ.t): t := map ZtoQ.ofZ lt.

  Lemma lift_correct: forall lt m, eval (lift lt) (Mem.lift ZtoQ.ofZ m) = ZtoQ.ofZ (LinZ.eval lt m).
  Proof.
    intros; unfold eval, LinZ.eval, lift. rewrite elements_map.
    generalize (PositiveMap.elements lt); induction l; simpl; autorewrite with num; auto.
  Qed.
  Hint Rewrite lift_correct: linterm.

End LinQ.

Module AffineTerm(Import N: NumSig)(L:LinSig N).

  Record affTerm := make { lin: L.t; cte: N.t }.

  Definition t:=affTerm.

  Definition eval aft m := N.add (L.eval (lin aft) m) (cte aft). 
 
  Lemma make_correct lt c m:  eval {|lin:=lt; cte:= c|} m = N.add (L.eval lt m) c.
  Proof.
    unfold eval; simpl; auto.
  Qed.

  Definition nil := {| lin:= L.nil; cte := N.z |}. 

  Lemma NilEval m: eval nil m = N.z.
  Proof.
    unfold eval; simpl; autorewrite with linterm. ring.
  Qed.

  Definition opp aft:= {| lin:= L.opp (lin aft); cte := N.opp (cte aft) |}.
 
  Lemma Opp_correct aft m: eval (opp aft) m = N.opp (eval aft m).
  Proof.
    unfold eval; simpl; autorewrite with linterm; ring.
  Qed.

  Definition mul c aft:=  
      {| lin:= L.mul c (lin aft); cte := N.mul c (cte aft) |}.

  Lemma Mul_correct c aft m: eval (mul c aft) m = N.mul c (eval aft m).
  Proof.
    unfold eval; simpl; autorewrite with linterm; ring.
  Qed.

  Definition add aft1 aft2 := {| lin:= L.add (lin aft1) (lin aft2); cte := N.add (cte aft1) (cte aft2) |}.

  Lemma Add_correct aft1 aft2 m: eval (add aft1 aft2) m = N.add (eval aft1 m) (eval aft2 m).
  Proof.
    unfold eval; simpl; autorewrite with linterm; ring.
  Qed.

  Definition addc c aft := {| lin:= (lin aft); cte := N.add c (cte aft) |}.

  Lemma Addc_correct c aft m: eval (addc c aft) m = N.add c (eval aft m).
  Proof.
    unfold eval; simpl; autorewrite with linterm; ring.
  Qed.

  Definition addx x aft := {| lin:= L.add (L.single x N.u) (lin aft); cte := (cte aft) |}.

  Lemma Addx_correct x aft m: eval (addx x aft) m = N.add (m x) (eval aft m).
  Proof.
    unfold eval; simpl; autorewrite with linterm; ring.
  Qed.

  Definition addnx x aft := {| lin:= L.add (L.single x (N.opp N.u)) (lin aft); cte := (cte aft) |}.

  Lemma Addnx_correct x aft m: eval (addnx x aft) m = N.add (N.opp (m x)) (eval aft m).
  Proof.
    unfold eval; simpl; autorewrite with linterm; ring.
  Qed.

  Definition isZero aft:= N.isZero (cte aft) &&& L.isNil (lin aft).

  Lemma isZero_correct aft:
    If isZero aft THEN aft=nil.
  Proof.
    unfold eval, isZero; PedraQsimplify. destruct aft; simpl in * |- *; intros; subst; auto.
  Qed.
  Global Hint Resolve isZero_correct: vpl.
  Global Opaque isZero.  

  Hint Rewrite make_correct NilEval Opp_correct Mul_correct Add_correct Addc_correct Addx_correct Addnx_correct: linterm.
  
End AffineTerm.

Module Type AffineTermSig (N: NumSig).
  
  Declare Module Lin: LinSig N.

  Include AffineTerm N Lin.
 
End AffineTermSig.



Module ZAffTerm <: AffineTermSig ZNum. 

  Module Lin:= LinZ.

  Include AffineTerm ZNum LinZ.

End ZAffTerm.


Module QAffTerm <: AffineTermSig QNum. 

  Module Lin:= LinQ.

  Include AffineTerm QNum LinQ.

  Definition lift (aft:ZAffTerm.t): t := {| lin := LinQ.lift (ZAffTerm.lin aft) ; cte := ZtoQ.ofZ (ZAffTerm.cte aft) |}.

  Lemma lift_correct: forall aft m, eval (lift aft) (Mem.lift ZtoQ.ofZ m) = ZtoQ.ofZ (ZAffTerm.eval aft m).
  Proof.
    intros; unfold eval, ZAffTerm.eval, lift. simpl.
    autorewrite with linterm num.
    auto.
  Qed.
  Hint Rewrite lift_correct: linterm.

End QAffTerm.


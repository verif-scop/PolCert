Require Import Ring.
Require Import ZArith.
Require Import QArith.
Require Import Qcanon.
Require Import Qround.
Require CoqAddOn.
Require List.
Require String.
Require Import OptionMonad.
Require Import Lia.

(*
Ltac qc := match goal with
 | q:Qc |- _ => destruct q; qc
 | _ => apply Qc_is_canon; simpl; rewrite ?Qred_correct
end.
*)

(* Trivial cases in multiplication *)
Inductive trivialMulDiscr :=
  IsZero | IsUnit | IsOppUnit | Other.

Module Type BasicNumSig.

  Parameter t: Set.

  Parameter z: t.
  Parameter u: t.

  Parameter add: t -> t -> t.
  Parameter mul: t -> t -> t.
  Parameter opp: t -> t.
  Parameter sub: t -> t -> t.

  Parameter Ring: ring_theory z u add mul sub opp eq.

  Parameter ZNotU: z <> u. (* non trivial ring !*)

  Parameter Le: t -> t -> Prop.
  Parameter Lt: t -> t -> Prop.

  Parameter Ltzu: Lt z u.
  Parameter LtNotLe: forall n1 n2 : t, Lt n1 n2 <-> ~ Le n2 n1.
  Parameter LeNotLt: forall n1 n2 : t, Le n1 n2 <-> ~ Lt n2 n1.
  Parameter LtLe: forall n1 n2: t, Lt n1 n2 -> Le n1 n2.

  Parameter eqDec: forall n1 n2: t, {n1 = n2} + {n1 <> n2}.
  Parameter ltLeDec: forall n1 n2: t, {Lt n1 n2} + {Le n2 n1}.
  Parameter dec: forall n1 n2: t, {Lt n1 n2} + {Lt n2 n1} + {n1 = n2}.

  Parameter LeRefl: forall n1: t, Le n1 n1.
  Parameter LeLeEq: forall n1 n2: t, Le n1 n2 /\ Le n2 n1 <-> n1 = n2.

  Parameter LeTrans: forall n1 n2 n3: t, Le n1 n2 -> Le n2 n3 -> Le n1 n3.
  Parameter LtTrans: forall n1 n2 n3: t, Lt n1 n2 -> Lt n2 n3 -> Lt n1 n3.
  Parameter LeLtTrans: forall n1 n2 n3: t, Le n1 n2 -> Lt n2 n3 -> Lt n1 n3.
  Parameter LtLeTrans: forall n1 n2 n3: t, Lt n1 n2 -> Le n2 n3 -> Lt n1 n3.

  Parameter isZero: forall n: t, {n = z} + {n <> z}.

  Parameter mulDiscr: t ->  trivialMulDiscr.
  Parameter mulDiscr_correct: forall n,
    match (mulDiscr n) with
    | IsZero => n=z
    | IsUnit => n=u
    | IsOppUnit => n=opp u
    | _ => True
    end.

(* useless
  Parameter AddEqEq: forall n1 n2 n3 n4: t,
                   n1 = n2 -> n3 = n4 -> (add n1 n3) = (add n2 n4).
*)

  Parameter AddLeLe: forall n1 n2 n3 n4: t,
                   Le n1 n2 -> Le n3 n4 -> Le (add n1 n3) (add n2 n4).

  Parameter AddLtLt: forall n1 n2 n3 n4: t,
                   Lt n1 n2 -> Lt n3 n4 -> Lt (add n1 n3) (add n2 n4).

(* useless
  Parameter AddEqLe: forall n1 n2 n3 n4: t,
                   n1 = n2 -> Le n3 n4 -> Le (add n1 n3) (add n2 n4).

  Parameter AddEqLt: forall n1 n2 n3 n4: t,
                   n1 = n2 -> Lt n3 n4 -> Lt (add n1 n3) (add n2 n4).
*)

  Parameter AddLeLt: forall n1 n2 n3 n4: t,
                   Le n1 n2 -> Lt n3 n4 -> Lt (add n1 n3) (add n2 n4).

  Parameter AddLtLe: forall n1 n2 n3 n4: t,
                   Lt n1 n2 -> Le n3 n4 -> Lt (add n1 n3) (add n2 n4).


  Parameter MulZL: forall n: t, mul z n = z.

  Parameter MulLe1: forall n1 n2 n3: t,
                 Le z n1 -> Le n2 n3 -> Le (mul n1 n2) (mul n1 n3).

  Parameter MulLe2: forall n1 n2 n3: t,
                 Lt z n1 -> Le (mul n1 n2) (mul n1 n3) -> Le n2 n3.

  Parameter MulLt: forall n1 n2 n3: t,
                 Lt z n1 -> (Lt n2 n3 <-> Lt (mul n1 n2) (mul n1 n3)).

  Parameter OppZ: opp z = z.
  Parameter OppOpp: forall n: t, opp (opp n) = n.
  Parameter OppLt: forall n1 n2: t, Lt n1 n2 <-> Lt (opp n2) (opp n1).
  Parameter OppLe: forall n1 n2: t, Le n1 n2 <-> Le (opp n2) (opp n1).

  Parameter MulUR: forall n1: t, mul n1 u = n1.
  Parameter MulAssoc: forall n1 n2 n3: t, mul n1 (mul n2 n3) = mul (mul n1 n2) n3.
  Parameter AddOppDistr: forall n1 n2: t, add (opp n1) (opp n2) = opp (add n1 n2).
  Parameter MulAddDistr: forall n1 n2 n3: t, mul (add n1 n2) n3 = add (mul n1 n3) (mul n2 n3).
  Parameter MulOppDistrR: forall n1 n2: t, mul n1 (opp n2) = opp (mul n1 n2).
  Parameter MulOppDistrL: forall n1 n2: t, mul (opp n1) n2 = opp (mul n1 n2).
  Parameter MulComm: forall n1 n2: t, mul n1 n2 = mul n2 n1.

  (** Pretty-print in a human-readable way *)
  Parameter pr: t -> String.string.

  (** Pretty-print the inner structure of [t] *)
  Parameter prRaw: t -> String.string.

  Hint Rewrite -> MulUR MulZL: num.
  Hint Rewrite <- OppLt OppLe LeNotLt LtNotLe MulLt: num.
  Hint Resolve AddLeLe AddLeLt AddLtLt AddLtLe LeRefl LtLe MulLe1: num.
  (* Hint Resolve LeTrans LtLe LtLeTrans LeLtTrans: num. *)

End BasicNumSig.

(* type of transitive comparisons *)
Inductive cmpT: Set
  := EqT | LeT | LtT.

Inductive cmpG: Set
  := Eq | Le | Lt | Neq.

Definition cmpT2G (c: cmpT): cmpG :=
  match c with
  | EqT => Eq
  | LeT => Le
  | LtT => Lt
  end.

Global Coercion cmpT2G: cmpT >-> cmpG.
Extraction Inline cmpT2G.


Definition cmpG2T (cmp:cmpG): option cmpT :=
   match cmp with
   | Eq => Some EqT
   | Le => Some LeT
   | Lt => Some LtT
   | Neq => None
   end.

Definition cmpT_eq (cmp1 cmp2: cmpT) : bool := 
  match cmp1, cmp2 with
  | EqT, EqT => true
  | LeT, LeT => true
  | LtT, LtT => true
  | _, _ => false
  end.

Lemma cmpT_eq_correct (cmp1 cmp2: cmpT): If (cmpT_eq cmp1 cmp2) THEN cmp1=cmp2.
Proof.
  destruct cmp1, cmp2; simpl; auto.
Qed.

Module CmpTheory(N: BasicNumSig).

  Add Ring NRing: N.Ring.

  Definition cmpDenote (cmp: cmpG): N.t -> N.t -> Prop
    := match cmp with
       | Eq => eq
       | Le => N.Le
       | Lt => N.Lt
       | Neq => fun x y => x <> y
       end.
 
  Lemma cmp_add_preserve {cmp n1 n2 n3}:
    cmpDenote cmp n1 n2 -> cmpDenote cmp (N.add n1 n3) (N.add n2 n3).
  Proof.
    destruct cmp; simpl; intros; subst; auto with num.
    (* neq *)
    intros X. destruct H.
    cutrewrite (n1 = N.add (N.add n1 n3) (N.opp n3)); try ring.
    rewrite X; ring.
  Qed.
  Local Hint Resolve cmp_add_preserve: num.
 
  Lemma cmp_zero_left {cmp n1 n2}: 
    cmpDenote cmp n1 n2 ->
      cmpDenote cmp N.z (N.add n2 (N.opp n1)).
  Proof.
    intros H; cutrewrite (N.z=N.add n1 (N.opp n1)); auto with num.
    ring.
  Qed. 
  Local Hint Resolve cmp_zero_left: num.

  Lemma cmp_transfo {cmp n1 n2 n3 n4}: 
    cmpDenote cmp n1 n2 ->
     n4 = (N.add (N.add n2 (N.opp n1)) n3)->
     cmpDenote cmp n3 n4.
  Proof.
    intros H H0; subst.
    cut (n3=N.add N.z n3).
    intros X; rewrite X at 1; clear X.
    auto with num.
    ring.
  Qed.    
  
  Ltac cmp_simplify := eapply cmp_transfo; [ eauto | try ring ].

  Lemma cmpG2T_correct cmp: 
    WHEN c <- cmpG2T cmp THEN
    forall v1 v2, cmpDenote c v1 v2 <-> cmpDenote cmp v1 v2.
  Proof.
    destruct cmp; simpl; intuition.
  Qed.

  Lemma cmpDenote_dec (cmp: cmpG) (n1 n2: N.t): {cmpDenote cmp n1 n2} + {~ cmpDenote cmp n1 n2}. 
    refine (match cmp return {cmpDenote cmp n1 n2} + {~ cmpDenote cmp n1 n2} with
              | Eq => N.eqDec n1 n2
              | Le =>
                match N.ltLeDec n2 n1 with
                  | left pf => right (proj1 (N.LtNotLe n2 n1) pf)
                  | right pf => left pf
                end
              | Lt =>
                match N.ltLeDec n1 n2 with
                  | left pf => left pf
                  | right pf => right (proj1 (N.LeNotLt n2 n1) pf)
                end
              | Neq =>
                match N.eqDec n1 n2 with
                  | left pf => right (fun H => H pf)
                  | right pf => left pf
                end
            end).
  Qed.
  Extraction Inline cmpDenote_dec.

End CmpTheory.


Module Type NumSig := BasicNumSig <+ CmpTheory.


Module QBasicNum <: BasicNumSig.

  Add Ring QcRing: Qcrt.

  Definition t: Set := Qc.

  Definition z: t := 0.
  Definition u: t := 1.

  Lemma ZNotU: z <> u.
    discriminate.
  Qed.

  Definition Le: t -> t -> Prop := Qcle.
  Definition Lt: t -> t -> Prop := Qclt.

  Definition add: t -> t -> t := Qcplus.
  Definition sub: t -> t -> t := Qcminus.
  Definition mul: t -> t -> t := Qcmult.
  Definition div: t -> t -> t := Qcdiv.

  Definition opp: t -> t := Qcopp.
  Definition inv: t -> t := Qcinv.

  Definition eqDec: forall n1 n2: t, {n1 = n2} + {n1 <> n2}
    := Qc_eq_dec.

  Definition ltLeDec: forall n1 n2: t, {Lt n1 n2} + {Le n2 n1}
    := Qclt_le_dec.

  Definition dec: forall n1 n2: t, {Lt n1 n2} + {Lt n2 n1} + {n1 = n2}
    := Qc_dec.

  Lemma zero_unique (n:t): (Qnum (this n))=0%Z -> n=z.
  Proof.
      intros; destruct n. destruct this; apply Qc_is_canon. simpl in * |- *.
      subst. vm_compute. auto.
  Qed.


  Program Definition isZero (n: t): {n = z} + {n <> z}
    := match (Qnum (this n)) with
       | Z0 => left _
       | _ => right _
       end.
  Obligation 1.
    apply zero_unique. auto.
  Qed.
  Obligation 2.
    intros H0. subst; apply H. vm_compute. auto.
  Qed.

  Lemma one_unique (n:t): Qnum (this n)=1%Z -> Qden (this n)=1%positive -> n=u.
  Proof.
    intros. destruct n. destruct this; apply Qc_is_canon. simpl in * |- *.
    subst. vm_compute. auto.
  Qed.

  Lemma opp_one_unique (n:t): Qnum (this n)=(-1)%Z -> Qden (this n)=1%positive -> n=(opp u).
  Proof.
    intros. destruct n. destruct this. apply Qc_is_canon. simpl. simpl in * |- *.
    subst. vm_compute. auto.
  Qed.
  
  Lemma Ltzu: Lt z u.
  Proof.
    vm_compute. auto.
  Qed.

  Definition mulDiscr (n: t)
    := match (Qden (this n)) with
       | 1%positive => 
          match (Qnum (this n)) with
          | 0%Z => IsZero
          | 1%Z => IsUnit
          | (-1)%Z => IsOppUnit
          | _ => Other
          end
       | _ => Other
       end.

  Lemma mulDiscr_correct n:
    match (mulDiscr n) with
    | IsZero => n=z
    | IsUnit => n=u
    | IsOppUnit => n=opp u
    | _ => True
    end.
  Proof.
    unfold mulDiscr.
    generalize (zero_unique n) (one_unique n) (opp_one_unique n).
    destruct (Qden (this n)); simpl; auto.
    destruct (Qnum n); simpl; auto;
    destruct p; simpl; auto.
  Qed.

  Extraction Inline add sub mul div opp inv eqDec ltLeDec dec isZero mulDiscr.

  Lemma LeRefl: forall n: t, Le n n.
  Proof Qcle_refl.

  Lemma LeLeEq: forall n1 n2: t, Le n1 n2 /\ Le n2 n1 <-> n1 = n2.
    intros n1 n2.
    split;
      intro h.
    - apply Qcle_antisym;
      [exact (proj1 h)|exact (proj2 h)].
    - subst n2.
      split;
        apply LeRefl.
  Qed.

  Lemma LtLe: forall n1 n2: t, Lt n1 n2 -> Le n1 n2.
  Proof Qclt_le_weak.

  Lemma LtNotLe: forall n1 n2: t, Lt n1 n2 <-> not (Le n2 n1).
    intros n1 n2.
    split;
      intro h.
    - apply Qclt_not_le.
      assumption.
    - apply Qcnot_le_lt.
      assumption.
  Qed.

  Lemma LeNotLt: forall n1 n2: t, Le n1 n2 <-> not (Lt n2 n1).
    intros n1 n2.
    split;
      intro h.
    - apply Qcle_not_lt.
      assumption.
    - apply Qcnot_lt_le.
      assumption.
  Qed.

  Lemma LeTrans: forall n1 n2 n3: t, Le n1 n2 -> Le n2 n3 -> Le n1 n3.
  Proof Qcle_trans.

  Lemma LtTrans: forall n1 n2 n3: t, Lt n1 n2 -> Lt n2 n3 -> Lt n1 n3.
  Proof Qclt_trans.

  Lemma LeLtTrans: forall n1 n2 n3: t, Le n1 n2 -> Lt n2 n3 -> Lt n1 n3.
  Proof Qcle_lt_trans.

  Lemma LtLeTrans: forall n1 n2 n3: t, Lt n1 n2 -> Le n2 n3 -> Lt n1 n3.
  Proof Qclt_le_trans.

  Lemma SplitEq: forall n1 n2: t,
                   Le n1 n2 -> Le (opp n1) (opp n2) -> n1 = n2.
    unfold opp; intros n1 n2 Hle HleN.
    apply Qcle_antisym;
      [ | apply Qcopp_le_compat in HleN;
          rewrite (Qcopp_involutive n2), (Qcopp_involutive n1) in HleN ];
      assumption.
  Qed.

  Lemma MulAddDistrL: forall n1 n2 n3: t,
                        mul (add n1 n2) n3 = add (mul n1 n3) (mul n2 n3).
    exact Qcmult_plus_distr_l.
  Qed.

  Lemma AddAssoc: forall n1 n2 n3: t,
                    add n1 (add n2 n3) = add (add n1 n2) n3.
  Proof Qcplus_assoc.

  Lemma AddComm: forall n1 n2: t, add n1 n2 = add n2 n1.
  Proof Qcplus_comm.

  Lemma AddZL: forall n: t, add z n = n.
  Proof Qcplus_0_l.

  Lemma AddZR: forall n: t, add n z = n.
  Proof Qcplus_0_r.

  Lemma AddOpp: forall n: t, add n (opp n) = z.
  Proof Qcplus_opp_r.

  Lemma AddOppDistr: forall n1 n2: t, add (opp n1) (opp n2) = opp (add n1 n2).
    unfold t, add, opp.
    intros.
    ring.
  Qed.

  Lemma MulUL: forall n: t, mul u n = n.
  Proof Qcmult_1_l.

  Lemma MulUR: forall n1: t, mul n1 u = n1.
  Proof Qcmult_1_r.

  Lemma MulZL: forall n: t, mul z n = z.
    intro; compute;
    apply Qc_is_canon; reflexivity.
  Qed.

  Lemma MulAssoc: forall n1 n2 n3: t,
                    mul n1 (mul n2 n3) = mul (mul n1 n2) n3.
  Proof Qcmult_assoc.

  Lemma MulComm: forall n1 n2: t, mul n1 n2 = mul n2 n1.
  Proof Qcmult_comm.

  Lemma MulAddDistr: forall n1 n2 n3: t, mul (add n1 n2) n3 = add (mul n1 n3) (mul n2 n3).
  Proof Qcmult_plus_distr_l.

  Lemma MulOppDistrR: forall n1 n2: t, mul n1 (opp n2) = opp (mul n1 n2).
    unfold t, mul, opp.
    intros.
    ring.
  Qed.

  Lemma MulOppDistrL: forall n1 n2: t, mul (opp n1) n2 = opp (mul n1 n2).
    unfold t, mul, opp.
    intros.
    ring.
  Qed.

  Lemma SubAdd: forall n1 n2: t, sub n1 n2 = add n1 (opp n2).
    intros; unfold sub, add, opp, Qcminus; trivial.
  Qed.

(*
  Lemma AddEqEq: forall n1 n2 n3 n4: t,
                   n1 = n2 -> n3 = n4 -> (add n1 n3) = (add n2 n4).
    intros n1 n2 n3 n4 h1 h2; rewrite h1, h2; trivial.
  Qed.
*)

  Lemma AddLeLe: forall n1 n2 n3 n4: t,
                   Le n1 n2 -> Le n3 n4 -> Le (add n1 n3) (add n2 n4).
  Proof Qcplus_le_compat.

  Lemma AddLtLt: forall n1 n2 n3 n4: t,
                   Lt n1 n2 -> Lt n3 n4 -> Lt (add n1 n3) (add n2 n4).
  Proof CoqAddOn.Qc.Qcplus_lt_compat.

(*
  Lemma AddEqLe: forall n1 n2 n3 n4: t,
                   n1 = n2 -> Le n3 n4 -> Le (add n1 n3) (add n2 n4).
    intros n1 n2 n3 n4 h1 h2;
    assert (h3 := Qcle_refl n1); rewrite h1 in h3 at 2;
    exact (AddLeLe _ _ _ _ h3 h2).
  Qed.
*)
  Lemma AddEqLt: forall n1 n2 n3 n4: t,
                   n1 = n2 -> Lt n3 n4 -> Lt (add n1 n3) (add n2 n4).
  Proof CoqAddOn.Qc.Qcplus_eqlt_compat.


  Lemma AddLeLt: forall n1 n2 n3 n4: t,
                   Le n1 n2 -> Lt n3 n4 -> Lt (add n1 n3) (add n2 n4).
  Proof.
    intros n1 n2 n3 n4 h; unfold Le in h.
    apply Qcle_lt_or_eq in h; destruct h; 
    intros; [ apply AddLtLt | apply AddEqLt]; auto.
  Qed.

  Lemma AddLtLe: forall n1 n2 n3 n4: t,
                   Lt n1 n2 -> Le n3 n4 -> Lt (add n1 n3) (add n2 n4).
    intros.
    rewrite (AddComm n1 n3).
    rewrite (AddComm n2 n4).
    apply AddLeLt;
      assumption.
  Qed.

  Hint Resolve AddLeLe AddLeLt AddLtLt AddLtLe SplitEq LeRefl: num.

  Lemma MulLe1: forall n1 n2 n3: t,
                  Le z n1 -> Le n2 n3 -> Le (mul n1 n2) (mul n1 n3).
    intros n1 n2 n3 h1 h2.
    rewrite (MulComm n1 n2), (MulComm n1 n3).
      apply Qcmult_le_compat_r;
        assumption.
  Qed.

  Lemma MulLe2: forall n1 n2 n3: t,
                  Lt z n1 -> Le (mul n1 n2) (mul n1 n3) -> Le n2 n3.
    intros n1 n2 n3 h1 h2.
    rewrite (MulComm n1 n2), (MulComm n1 n3) in h2.
    apply Qcmult_lt_0_le_reg_r with (z := n1);
      assumption.
  Qed.

  Lemma MulLt: forall n1 n2 n3: t,
                 Lt z n1 -> (Lt n2 n3 <-> Lt (mul n1 n2) (mul n1 n3)).
    intros n1 n2 n3 h1.
    rewrite (MulComm n1 n2), (MulComm n1 n3).
    split;
      intro h2.
    - unfold Lt, mul, Qcmult.
      apply (proj1 (CoqAddOn.Qc.QcQLt _ _)).
      apply Qmult_lt_r;
        assumption.
    - unfold Lt, mul, Qcmult in h2.
      apply (proj2 (CoqAddOn.Qc.QcQLt _ _)) in h2.
      apply Qmult_lt_r in h2;
        assumption.
  Qed.

  Lemma OppZ: opp z = z.
    reflexivity.
  Qed.

  Lemma OppOpp: forall n: t, opp (opp n) = n.
  Proof Qcopp_involutive.

  Lemma OppLe: forall n1 n2: t, Le n1 n2 <-> Le (opp n2) (opp n1).
    intros n1 n2.
    split; [exact (Qcopp_le_compat n1 n2) |].
    intro h.
    apply (AddLeLe n1 n1 (opp n2) (opp n1)) in h; auto with num.
    eapply (AddLeLe n2 n2) in h; auto with num.
    unfold add in h.
    rewrite (Qcplus_comm n1 (opp n2)) in h.
    rewrite (Qcplus_assoc n2 (opp n2) n1) in h.
    repeat rewrite Qcplus_opp_r in h.
    rewrite Qcplus_0_l ,Qcplus_0_r in h.
    assumption.
  Qed.

  Lemma OppLt: forall n1 n2: t, Lt n1 n2 <-> Lt (opp n2) (opp n1).
  Proof CoqAddOn.Qc.Qcopp_lt_compat.

  Definition Ring := mk_rt z u add mul sub opp eq AddZL AddComm AddAssoc
                           MulUL MulComm MulAssoc MulAddDistrL SubAdd AddOpp.

  Import List String.
  Local Open Scope string_scope.

  Definition pr: t -> string
    := fun q =>
         let nstr := CoqAddOn.zPr (Qnum (this q)) in
         let dstr := CoqAddOn.posPr (Qden (this q)) in
         CoqAddOn.sprintf "(%s/%s)" (cons nstr (cons dstr nil)).

  Definition prRaw: t -> string
    := fun q =>
         let nstr := CoqAddOn.zPrRaw (Qnum (this q)) in
         let dstr := CoqAddOn.posPrRaw (Qden (this q)) in
         CoqAddOn.sprintf "{num = %s; den = %s}" (cons nstr (cons dstr nil)).

  Lemma LtLeAbsurd: forall n1 n2: t, Lt n1 n2 -> Le n2 n1 -> False.
    intros n1 n2; case (LtNotLe n1 n2); intuition.
  Qed.

  Definition to_Q : t -> Q 
  := fun qc => qc.(this).

  Hint Resolve LtLeAbsurd LeTrans LtLe LtLeTrans LeLtTrans: num.
  Hint Rewrite SubAdd: num.
  Hint Rewrite <- OppLt OppLe LeNotLt LtNotLe: num.

End QBasicNum.

Module QNum <: NumSig := QBasicNum <+ CmpTheory.

Import ZArith_base.

Module ZBasicNum <: BasicNumSig.

  Local Open Scope Z_scope.

  Definition t: Set := Z.

  Definition z: t := 0.
  Definition u: t := 1.

  Lemma ZNotU: z <> u.
    discriminate.
  Qed.

  Definition Le: t -> t -> Prop
    := fun n1 n2 => n1 <= n2.

  Definition Lt: t -> t -> Prop
    := fun n1 n2 => n1 < n2.

  Lemma LtNotLe: forall n1 n2 : t, Lt n1 n2 <-> ~ Le n2 n1.
    intros n1 n2.
    split;
      intro h.
    - apply Zlt_not_le.
      assumption.
    - apply Znot_ge_lt.
      intro hcontr.
      apply h, Z.ge_le.
      assumption.
  Qed.

  Lemma LeNotLt: forall n1 n2 : t, Le n1 n2 <-> ~ Lt n2 n1.
    intros n1 n2.
    split;
      intro h.
    - apply Zle_not_lt.
      assumption.
    - apply Znot_gt_le.
      intro hcontr.
      apply h, Z.gt_lt.
      assumption.
  Qed.

  Lemma LtLe: forall n1 n2: t, Lt n1 n2 -> Le n1 n2.
  Proof Zlt_le_weak.

  Definition eqDec: forall n1 n2: t, {n1 = n2} + {n1 <> n2}
    := Z.eq_dec.

  Definition ltLeDec: forall n1 n2: t, {Lt n1 n2} + {Le n2 n1}
    := ZArith_dec.Z_lt_le_dec.

  Definition dec: forall n1 n2: t, {Lt n1 n2} + {Lt n2 n1} + {n1 = n2}
    := ZArith_dec.Z_dec'.

  Lemma LeRefl: forall n1: t, Le n1 n1.
  Proof Z.le_refl.

  Lemma LeLeEq: forall n1 n2: t, Le n1 n2 /\ Le n2 n1 <-> n1 = n2.
    intros n1 n2.
    split;
      intro h.
    - apply Z.le_antisymm;
      [exact (proj1 h)|exact (proj2 h)].
    - subst n2.
      split;
        apply LeRefl.
  Qed.

  Lemma LeTrans: forall n1 n2 n3: t, Le n1 n2 -> Le n2 n3 -> Le n1 n3.
  Proof Z.le_trans.

  Lemma LtTrans: forall n1 n2 n3: t, Lt n1 n2 -> Lt n2 n3 -> Lt n1 n3.
  Proof Z.lt_trans.

  Lemma LeLtTrans: forall n1 n2 n3: t, Le n1 n2 -> Lt n2 n3 -> Lt n1 n3.
  Proof Z.le_lt_trans.

  Lemma LtLeTrans: forall n1 n2 n3: t, Lt n1 n2 -> Le n2 n3 -> Lt n1 n3.
  Proof Z.lt_le_trans.

  Lemma Ltzu: Lt z u.
  Proof.
    unfold Lt, z, u. lia.
  Qed.

  Definition add: t -> t -> t
    := fun n1 n2 => n1 + n2.

(*
  Lemma AddEqEq: forall n1 n2 n3 n4: t,
                   n1 = n2 -> n3 = n4 -> (add n1 n3) = (add n2 n4).
    intros n1 n2 n3 n4 h1 h2; rewrite h1, h2; trivial.
  Qed.
*)

  Lemma AddLeLe: forall n1 n2 n3 n4: t,
                   Le n1 n2 -> Le n3 n4 -> Le (add n1 n3) (add n2 n4).
  Proof Z.add_le_mono.

  Lemma AddLtLt: forall n1 n2 n3 n4: t,
                   Lt n1 n2 -> Lt n3 n4 -> Lt (add n1 n3) (add n2 n4).
  Proof Z.add_lt_mono.


(*
  Lemma AddEqLe: forall n1 n2 n3 n4: t,
                   n1 = n2 -> Le n3 n4 -> Le (add n1 n3) (add n2 n4).
    intros n1 n2 n3 n4 h1 h2.
    subst n1.
    apply Zplus_le_compat_l.
    assumption.
  Qed.

  Lemma AddEqLt: forall n1 n2 n3 n4: t,
                   n1 = n2 -> Lt n3 n4 -> Lt (add n1 n3) (add n2 n4).
    intros n1 n2 n3 n4 h1 h2.
    subst n1.
    apply Zplus_lt_compat_l.
    assumption.
  Qed.
*)

  Lemma AddLeLt: forall n1 n2 n3 n4: t,
                   Le n1 n2 -> Lt n3 n4 -> Lt (add n1 n3) (add n2 n4).
  Proof Z.add_le_lt_mono.

  Lemma AddLtLe: forall n1 n2 n3 n4: t,
                   Lt n1 n2 -> Le n3 n4 -> Lt (add n1 n3) (add n2 n4).
  Proof Z.add_lt_le_mono.

  Definition mul: t -> t -> t
    := fun n1 n2 => n1 * n2.

  Lemma MulZL: forall n: t, mul z n = z.
  Proof Z.mul_0_l.

  Lemma MulLe1: forall n1 n2 n3: t,
                 (Le z n1) -> Le n2 n3 -> Le (mul n1 n2) (mul n1 n3).
    intros n1 n2 n3 h1 h2.
    apply Zmult_le_compat_l;
      assumption.
  Qed.

  Lemma MulLe2: forall n1 n2 n3: t,
                 Lt z n1 -> Le (mul n1 n2) (mul n1 n3) -> Le n2 n3.
    intros n1 n2 n3 h1 h2.
    apply Zmult_le_reg_r with (p := n1).
    - apply Z.lt_gt.
      assumption.
    - unfold mul in h2.
      rewrite (Z.mul_comm n1 n2), (Z.mul_comm n1 n3) in h2.
      assumption.
  Qed.

  Lemma MulLt: forall n1 n2 n3: t,
                 Lt z n1 -> (Lt n2 n3 <-> Lt (mul n1 n2) (mul n1 n3)).
    intros n1 n2 n3 h1.
    split;
      intro h2.
    - apply Zmult_lt_compat_l;
      assumption.
    - apply Zmult_lt_reg_r with (p := n1);
      unfold mul in h2;
      [idtac|rewrite (Z.mul_comm n1 n2), (Z.mul_comm n1 n3) in h2];
      assumption.
  Qed.

  Definition opp: t -> t
    := fun n1 => - n1.

  Lemma OppZ: opp z = z.
    reflexivity.
  Qed.

  Lemma OppOpp: forall n: t, opp (opp n) = n.
  Proof Z.opp_involutive.

  Lemma OppLt: forall n1 n2: t, Lt n1 n2 <-> Lt (opp n2) (opp n1).
    intros n1 n2.
    unfold Lt, Z.lt.
    rewrite Z.compare_opp.
    reflexivity.
  Qed.

  Lemma OppLe: forall n1 n2: t, Le n1 n2 <-> Le (opp n2) (opp n1).
    intros n1 n2.
    unfold Le, Z.le.
    rewrite Z.compare_opp.
    reflexivity.
  Qed.

  Lemma AddOpp: forall n: t, add n (opp n) = z.
  Proof Zplus_opp_r.


  Lemma MulUR: forall n1: t, mul n1 u = n1.
  Proof Z.mul_1_r.

  Lemma MulAssoc: forall n1 n2 n3: t, mul n1 (mul n2 n3) = mul (mul n1 n2) n3.
  Proof Z.mul_assoc.

  Lemma MulAddDistr: forall n1 n2 n3: t, mul (add n1 n2) n3 = add (mul n1 n3) (mul n2 n3).
  Proof Z.mul_add_distr_r.

  Lemma AddOppDistr: forall n1 n2: t, add (opp n1) (opp n2) = opp (add n1 n2).
    intros n1 n2.
    rewrite Z.opp_add_distr.
    reflexivity.
  Qed.

  Lemma MulOppDistrR: forall n1 n2: t, mul n1 (opp n2) = opp (mul n1 n2).
  Proof Z.mul_opp_r.

  Lemma MulOppDistrL: forall n1 n2: t, mul (opp n1) n2 = opp (mul n1 n2).
  Proof Z.mul_opp_l.

  Definition pr: t -> String.string
    := fun z => CoqAddOn.zPr z.

  Definition prRaw: t -> String.string
    := fun z => CoqAddOn.zPrRaw z.

  Definition sub: t -> t -> t := Zminus.

  Lemma SubAdd: forall n1 n2: t, sub n1 n2 = add n1 (opp n2).
    intros; unfold sub, add, opp, Zminus; trivial.
  Qed.

  Definition Ring := mk_rt z u add mul sub opp eq Zplus_0_l Zplus_comm Zplus_assoc
                           Zmult_1_l Zmult_comm MulAssoc Zmult_plus_distr_l SubAdd AddOpp.

  Hint Rewrite SubAdd: num.

  Program Definition isZero (n: t): {n = z} + {n <> z}
    := match n with
       | Z0 => left _
       | _ => right _
       end.

  Definition mulDiscr (n: t)
    := match n with
       | 0%Z => IsZero
       | 1%Z => IsUnit
       | (-1)%Z => IsOppUnit
       | _ => Other
       end.

  Lemma mulDiscr_correct n:
    match (mulDiscr n) with
    | IsZero => n=z
    | IsUnit => n=u
    | IsOppUnit => n=opp u
    | _ => True
    end.
  Proof.
    unfold mulDiscr; destruct n; simpl; auto;
    destruct p; simpl; auto.
  Qed.

  Extraction Inline add sub mul opp eqDec ltLeDec dec isZero mulDiscr.
  Hint Resolve AddLeLe AddLeLt AddLtLt AddLtLe LeRefl: num.

  Definition MulComm := Z.mul_comm.

  Ltac simplify := unfold z, u, add, sub, mul, opp, Le, Lt in * |- *; lia || auto with zarith.

End ZBasicNum.

Module ZNum <: NumSig := ZBasicNum <+ CmpTheory.

Module ZtoQ.

  Lemma PosGcdOne: forall p: positive, Pos.gcd p 1%positive = 1%positive.
    intro p.
    unfold Pos.gcd.
    generalize (Pos.size_nat p + Pos.size_nat 1)%nat.
    intro n.
    unfold Pos.gcdn.
    destruct n;
      [idtac|destruct p];
      reflexivity.
  Qed.

  Lemma ZGcdOne: forall z: Z, Z.gcd z 1%Z = 1%Z.
    intro z.
    unfold Z.gcd.
    destruct z;
      try rewrite PosGcdOne;
      reflexivity.
  Qed.

  Lemma ZGgcdOne: forall z: Z, snd (Z.ggcd z 1%Z) = (z, 1%Z).
    intro z.
    assert (pf1 := Z.ggcd_gcd z 1%Z).
    assert (pf2 := Z.ggcd_correct_divisors z 1%Z).
    rewrite (surjective_pairing (Z.ggcd z 1%Z)) in pf2.
    rewrite (surjective_pairing (snd (Z.ggcd z 1%Z))) in pf2.
    rewrite pf1, ZGcdOne in pf2.
    do 2 rewrite Z.mul_1_l in pf2.
    rewrite (surjective_pairing (snd (Z.ggcd z 1%Z))).
    rewrite <- (proj1 pf2), <- (proj2 pf2).
    reflexivity.
  Qed.

  Lemma QredOne: forall z: Z, Qred (z # 1%positive) = z # 1%positive.
    intro z.
    unfold Qred.
    rewrite ZGgcdOne.
    reflexivity.
  Qed.

  Definition ofZ: ZNum.t -> QNum.t
    := fun z => Qcmake (QArith_base.inject_Z z) (QredOne _).
  
  Extraction Inline ofZ.

  Lemma ofZ_zero: ofZ ZNum.z = QNum.z.
  Proof.
    apply Qc_is_canon; vm_compute; auto.
  Qed.

  Lemma ofZ_one: ofZ ZNum.u = QNum.u.
  Proof.
    apply Qc_is_canon; vm_compute; auto.
  Qed.
  Hint Rewrite ofZ_zero ofZ_one: num.

  Lemma EqCommutes: forall z1 z2: ZNum.t, z1 = z2 <-> (ofZ z1) = (ofZ z2).
    intros z1 z2.
    split;
      intro h;
      [rewrite h|inversion h];
      reflexivity.
  Qed.

  Ltac solveOrder a b
    :=  let h := fresh "h" in
        (split;
         unfold a, b;
         simpl;
         intro h);
         [do 2 rewrite Z.mul_1_r | do 2 rewrite Z.mul_1_r in h];
         assumption.

  Lemma LeCommutes: forall z1 z2: ZNum.t,
                      ZNum.Le z1 z2 <-> QNum.Le (ofZ z1) (ofZ z2).
    intros z1 z2.
    unfold ZNum.Le, QNum.Le, ofZ.
    solveOrder Qcle Qle.
  Qed.

  Lemma LtCommutes: forall z1 z2: ZNum.t,
                      ZNum.Lt z1 z2 <-> QNum.Lt (ofZ z1) (ofZ z2).
    intros z1 z2.
    unfold ZNum.Lt, QNum.Lt, ofZ.
    solveOrder Qclt Qlt.
  Qed.

  Lemma AddCommutes: forall z1 z2: ZNum.t,
                       ofZ (ZNum.add z1 z2) = QNum.add (ofZ z1) (ofZ z2).
    intros z1 z2.
    apply Qc_is_canon.
    simpl.
    rewrite ZGgcdOne.
    do 2 rewrite Z.mul_1_r.
    simpl.
    reflexivity.
  Qed.

  Lemma MulCommutes: forall z1 z2: ZNum.t,
                       ofZ (ZNum.mul z1 z2) = QNum.mul (ofZ z1) (ofZ z2).
    intros z1 z2.
    apply Qc_is_canon.
    simpl.
    rewrite ZGgcdOne.
    reflexivity.
  Qed.

  Lemma OppCommutes: forall z: ZNum.t,
                       ofZ (ZNum.opp z) = QNum.opp (ofZ z).
    intros z.
    apply Qc_is_canon.
    simpl.
    rewrite ZGgcdOne.
    reflexivity.
  Qed.
   
  Hint Rewrite EqCommutes LeCommutes LtCommutes LtCommutes AddCommutes MulCommutes OppCommutes: num.

  Lemma isInZ_test q: Qden(this(q))=1%positive -> q=ofZ(Qnum(this(q))).
  Proof.
     intros H; destruct q; apply Qc_is_canon; simpl in * |- *.
     generalize H; clear H canon.
     case this. simpl; intros; subst; simpl. reflexivity.
  Qed.

  Local Hint Resolve isInZ_test.
  Program Definition isInZ (q: QNum.t): option (q=ofZ(Qnum(this(q)))) :=
    match Qden(this(q)) with
    | 1%positive => Some _
    | _ => None
    end.     

  Definition floor: QNum.t -> ZNum.t
    := fun n => Qfloor n.

  Lemma FloorZ: forall z: ZNum.t, floor (ofZ z) = z.
    apply Qfloor_Z.
  Qed.

  Lemma FloorLeZ: forall n1 n2: QNum.t, QNum.Le n1 n2 -> ZNum.Le (floor n1) (floor n2).
    intros n1 n2 h.
    apply Qfloor_resp_le.
    assumption.
  Qed.

  Definition ceil: QNum.t -> ZNum.t
    := fun n => Qceiling n.

  Lemma CeilZ: forall z: ZNum.t, ceil (ofZ z) = z.
    apply Qceiling_Z.
  Qed.

  Lemma CeilLeZ: forall n1 n2: QNum.t, QNum.Le n1 n2 -> ZNum.Le (ceil n1) (ceil n2).
    intros n1 n2 h.
    apply Qceiling_resp_le.
    assumption.
  Qed.

  Lemma FloorQLt: forall (q1 q2 : QNum.t),
                    QNum.Lt q1 q2 -> QNum.Lt (ofZ (floor q1)) q2.
    intros q1 q2 h.
    apply (QNum.LeLtTrans _ q1 _).
    apply Qfloor_le.
    assumption.
  Qed.

  Lemma CeilQLt: forall (q1 q2: QNum.t),
                    QNum.Lt q1 q2 -> QNum.Lt q1 (ofZ (ceil q2)).
    intros q1 q2 h.
    apply (QNum.LtLeTrans _ q2 _).
    assumption.
    apply Qle_ceiling.
  Qed.

  Lemma CeilQLe: forall (q1 q2: QNum.t),
                    QNum.Le q1 q2 -> QNum.Le q1 (ofZ (ceil q2)).
    intros q1 q2 h.
    apply (QNum.LeTrans _ q2 _).
    assumption.
    apply Qle_ceiling.
  Qed.

  Lemma Ceil_exact q: q=ofZ(Qnum(this(q))) -> (ceil q)=Qnum(this(q)).
  Proof.
    intros H; rewrite H at 1. rewrite CeilZ; auto.
  Qed.

  Lemma Floor_exact q: q=ofZ(Qnum(this(q))) -> (floor q)=Qnum(this(q)).
  Proof.
    intros H; rewrite H at 1. rewrite FloorZ; auto.
  Qed.


End ZtoQ.

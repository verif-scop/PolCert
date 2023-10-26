Require String.
Require Import NumC.
Require Import DomainInterfaces.
Require Import Lia.
(*
Module Type AffItvSig (N: NumSig) <: ItvSig N.

  Parameter t: Set.

  Parameter sat: t -> N.t -> Prop.

  (** Build a singleton interval *)
  Definition Mk1Spec (n: N.t) (i: t): Prop
    := forall n': N.t, n = n' <-> sat i n'.

  Parameter mk1Dep: forall n: N.t, {i: t | Mk1Spec n i}.
  Parameter mk1: N.t -> t.
  Parameter Mk1_correct: forall n: N.t, Mk1Spec n (mk1 n).

  (** Sum of two intervals *)
  Definition AddSpec (i1 i2 i: t): Prop
    := forall n1 n2: N.t, sat i1 n1 /\ sat i2 n2 -> sat i (N.add n1 n2).

  Parameter addDep: forall i1 i2: t, {i: t | AddSpec i1 i2 i}.
  Parameter add: t -> t -> t.
  Parameter Add_correct: forall i1 i2: t, AddSpec i1 i2 (add i1 i2).

  (** Opposite of an interval *)
  Definition OppSpec (i1 i2: t): Prop
    := forall n: N.t, sat i1 n <-> sat i2 (N.opp n).

  Parameter oppDep: forall i0: t, {i: t | OppSpec i0 i}.
  Parameter opp: t -> t.
  Parameter Opp_correct: forall i1: t, OppSpec i1 (opp i1).

  (** Multiplication by a constant *)
  Definition MulcSpec (i1: t) (n: N.t) (i2: t): Prop
    := forall n': N.t, sat i1 n' -> sat i2 (N.mul n n').

  Parameter mulcDep: forall (i0: t) (n: N.t), {i: t | MulcSpec i0 n i}.
  Parameter mulc: t -> N.t -> t.
  Parameter Mulc_correct: forall (i1: t) (n: N.t), MulcSpec i1 n (mulc i1 n).

  Parameter pr: t -> String.string.

End AffItvSig.
*)

Module StdItv (N: NumSig)<: ItvSig N.

  Inductive bndT: Set
    :=
    | Infty: bndT
    | Open: N.t -> bndT
    | Closed: N.t -> bndT.

  Record tInd: Set := mk { lower: bndT; upper: bndT }.

  Definition t: Set := tInd.

  Definition satLower (b: bndT) (x: N.t): Prop :=
    match b with
      | Infty => True
      | Open n => N.Lt n x
      | Closed n => N.Le n x
    end.

  Definition satUpper (b: bndT) (x: N.t): Prop :=
    match b with
      | Infty => True
      | Open n => N.Lt x n
      | Closed n => N.Le x n
    end.

  Definition sat (i: t) (x: N.t): Prop := satLower (lower i) x /\ satUpper (upper i) x.
  Local Hint Unfold sat.

  Lemma mk_correct l u x: satLower l x -> satUpper u x -> sat (mk l u) x.
  Proof.
    unfold sat; intuition.
  Qed.

  Definition top: t := {| lower := Infty; upper := Infty |}.

  Lemma top_correct n: (sat top n).
  Proof.
    unfold sat; simpl. intuition.
  Qed.


  Definition bot: t := {| lower := Closed N.u; upper := Closed N.z |}.

  Lemma bot_correct n: ~(sat bot n).
  Proof.
    unfold sat; simpl. intuition.
    assert (X: ~(N.Lt N.z N.u)). autorewrite with num. eapply N.LeTrans; eauto.
    apply X. apply N.Ltzu.
  Qed.

  Definition is_not_upper (n: N.t) (b:bndT) : bool :=
    match b with
      | Infty => false
      | Open m => if N.ltLeDec n m then false else true
      | Closed m => if N.ltLeDec m n then true else false
    end.

  Lemma is_not_upper_correct n b: is_not_upper n b = true -> ~(satUpper b n).
  Proof.
   destruct b; simpl; autorewrite with num.
   + intuition.
   + destruct (N.ltLeDec n t0); simpl; auto; try discriminate.
   + destruct (N.ltLeDec t0 n); simpl; auto; try discriminate.
  Qed.

  Definition is_bot (i: t): bool :=
  match lower i with
  | Infty => false
  | Open n => match upper i with
              | Infty => false
              | Open m =>  if N.ltLeDec n m then false else true
              | Closed m => if N.ltLeDec n m then false else true
              end
  | Closed n => is_not_upper n (upper i)
  end.

  Local Hint Resolve N.LeTrans N.LtTrans N.LtLeTrans N.LtLeTrans N.LeLtTrans.

  Lemma is_bot_correct i n: is_bot i = true -> ~(sat i n).
  Proof.
   unfold is_bot, sat; destruct (lower i); intuition.
   + destruct (upper i); simpl in * |-; intuition.
     - destruct (N.ltLeDec t0 t1); intuition.
       assert (X:~(N.Lt t0 t1)); autorewrite with num; eauto.
     - destruct (N.ltLeDec t0 t1); intuition.
       assert (X:~(N.Lt t0 t1)); autorewrite with num; eauto.
  + eapply is_not_upper_correct; eauto.
    destruct (upper i); simpl in * |- *; intuition eauto.
  Qed.

  Definition mk1 (n: N.t): t := {| lower := Closed n; upper := Closed n |}.

  Lemma mk1_correct n: sat (mk1 n) n.
  Proof.
    unfold sat; simpl; auto with num.
  Qed.
  Local Hint Resolve mk1_correct.

  Definition bndAdd (b1 b2: bndT): bndT
    := match b1 with
         | Infty => Infty
         | Open n1 =>
           match b2 with
             | Infty => Infty
             | Open n2 => Open (N.add n1 n2)
             | Closed n2 => Open (N.add n1 n2)
           end
         | Closed n1 =>
           match b2 with
             | Infty => Infty
             | Open n2 => Open (N.add n1 n2)
             | Closed n2 => Closed (N.add n1 n2)
           end
       end.
  
  Lemma bndAdd_lower (b1 b2: bndT) x1 x2: satLower b1 x1 -> satLower b2 x2 -> satLower (bndAdd b1 b2) (N.add x1 x2).
  Proof.
    destruct b1; simpl; auto; destruct b2; simpl; auto with num.
  Qed.

  Lemma bndAdd_upper (b1 b2: bndT) x1 x2: satUpper b1 x1 -> satUpper b2 x2 -> satUpper (bndAdd b1 b2) (N.add x1 x2).
  Proof.
    destruct b1; simpl; auto; destruct b2; simpl; auto with num.
  Qed.

  Local Hint Resolve bndAdd_lower bndAdd_upper.

  Definition add i1 i2 := {| lower := bndAdd (lower i1) (lower i2) ; upper := bndAdd (upper i1) (upper i2) |}.

  Lemma add_correct i1 i2 x1 x2: sat i1 x1 -> sat i2 x2 -> sat (add i1 i2) (N.add x1 x2).
  Proof.
    unfold sat, add; simpl; intuition.
  Qed.
  Local Hint Resolve add_correct.

  Definition bndOpp: bndT -> bndT
    := fun b =>
         match b with
           | Infty => Infty
           | Open n => Open (N.opp n)
           | Closed n => Closed (N.opp n)
         end.

  Lemma bndOpp_lower (b: bndT) x: satLower b x -> satUpper (bndOpp b) (N.opp x).
  Proof.
    destruct b; simpl; autorewrite with num; auto.
  Qed.

  Lemma bndOpp_upper (b: bndT) x: satUpper b x -> satLower (bndOpp b) (N.opp x).
  Proof.
    destruct b; simpl; autorewrite with num; auto.
  Qed.
  Local Hint Resolve bndOpp_lower bndOpp_upper.

  Definition opp i := {| lower := bndOpp (upper i); upper := bndOpp (lower i) |}.

  Lemma opp_correct i x: sat i x -> sat (opp i) (N.opp x).
  Proof.
    unfold sat, opp; simpl; intuition.
  Qed.
  Local Hint Resolve opp_correct.

  (** A FINIR **)
  Definition bndMulc: bndT -> N.t -> bndT
    := fun i n =>
         match i with
           | Infty => Infty
           | Open n' => Open (N.mul n n')
           | Closed n' => Closed (N.mul n n')
         end.

  Lemma bndMulc_lower (b: bndT) n x: N.Lt N.z n -> satLower b x -> satLower (bndMulc b n) (N.mul n x).
  Proof.
    destruct b; simpl; intros; autorewrite with num; auto with num.
  Qed.

  Lemma bndMulc_upper (b: bndT) n x: N.Lt N.z n -> satUpper b x -> satUpper (bndMulc b n) (N.mul n x).
  Proof.
    destruct b; simpl; intros; autorewrite with num; auto with num.
  Qed.
  Local Hint Resolve bndMulc_lower bndMulc_upper.

  Definition mulcPos (i:t) (n: N.t) := 
   {| lower := bndMulc (lower i) n; upper := bndMulc (upper i) n |}.

  Lemma mulcPos_correct i n x: N.Lt N.z n -> sat i x -> sat (mulcPos i n) (N.mul n x).
  Proof.
    unfold sat, mulcPos; simpl; intuition.
  Qed.
  Local Hint Resolve mulcPos_correct.

  Definition mulc (i:t) (n: N.t):=
    match N.dec N.z n with
    | inleft pfn => if pfn then mulcPos i n else opp (mulcPos i (N.opp n))
    | _ => mk1 N.z
    end.

  Lemma mulc_correct i n x: sat i x -> sat (mulc i n) (N.mul n x).
  Proof.
    unfold mulc; intros; case (N.dec N.z n).
    + intros pfn; destruct pfn; auto.
      rewrite <- (N.OppOpp n) at 2. rewrite N.MulOppDistrL. 
      rewrite N.OppLt, N.OppZ in * |-. auto. 
    + intros; subst. autorewrite with num; auto.
  Qed.

  Import String.
  Local Open Scope string_scope.

  Definition pr: t -> string
    := fun i =>
         let lstr :=
           match lower i with
           | Infty => "]-infty"
           | Open n => "]" ++ (N.pr n)
           | Closed n => "[" ++ (N.pr n)
           end
         in let ustr := 
           match upper i with
           | Infty => "+infty["
           | Open n => (N.pr n) ++ "["
           | Closed n => (N.pr n) ++ "]"
           end
         in
           lstr ++ ", " ++ ustr.

  Definition shift (i:t) (n:N.t) := add (mk1 n) i.

  Lemma shift_correct (i:t) (n x:N.t):
    sat i x -> sat (shift i n) (N.add n x).
  Proof.
    unfold shift. auto.
  Qed. 

End StdItv.

Module QItv <: ItvSig (QNum).
  Include StdItv QNum.

(*
  Definition ShiftSpec (i1 i2: t) (n: QNum.t): Prop
    := forall x: QNum.t, sat i1 x -> sat i2 (QNum.add n x).

  Definition shiftDep (i0: t) (n: QNum.t): {i: t | ShiftSpec i0 i n}.
    refine (
        match i0
              return {i: t | ShiftSpec i0 i n}
        with
          | Bot => exist _ Bot (fun x (h: sat Bot x) => match h with end)
          | NotBot low up pf =>
            let (i1, pf1) :=
                match low, up
                      return BndOk low up -> {i: bndT * bndT |
                              BndOk (fst i) (snd i) /\
                              (forall x, satLower low x -> satLower (fst i) (QNum.add n x)) /\
                              (forall x, satUpper up x -> satUpper (snd i) (QNum.add n x))}
                with
                  | Infty, Infty =>
                    fun pfb => exist _ (Infty, Infty) _
                  | Infty, Open n1 =>
                    fun pfb => exist _ (Infty, Open (QNum.add n n1)) _
                  | Infty, Closed n1 =>
                    fun pfb => exist _ (Infty, Closed (QNum.add n n1)) _
                  | Open n1, Infty =>
                    fun pfb => exist _ (Open (QNum.add n n1), Infty) _
                  | Open n1, Open n2 =>
                    fun pfb => exist _ (Open (QNum.add n n1), Open (QNum.add n n2)) _
                  | Open n1, Closed n2 =>
                    fun pfb => exist _ (Open (QNum.add n n1), Closed (QNum.add n n2)) _
                  | Closed n1, Infty =>
                    fun pfb => exist _ (Closed (QNum.add n n1), Infty) _
                  | Closed n1, Open n2 =>
                    fun pfb => exist _ (Closed (QNum.add n n1), Open (QNum.add n n2)) _
                  | Closed n1, Closed n2 =>
                    fun pfb => exist _ (Closed (QNum.add n n1), Closed (QNum.add n n2)) _
                end pf
            in
            let pf': BndOk (fst i1) (snd i1) := _ in
            exist _ (NotBot (fst i1) (snd i1) pf') _
        end);
    repeat split;
    simpl;
    intros;
    match goal with
      | |- BndOk _ _ => constructor; inversion pfb
      | _ => idtac
    end; auto with num;
    match goal with
      | h: sat _ _ |- _ => unfold sat in h
      | _ => idtac
    end;
      intuition.
  Defined.

  Definition shift: t -> QNum.t -> t
    := fun i n => proj1_sig (shiftDep i n).

  Lemma Shift_correct: forall (i: t) (n: QNum.t), ShiftSpec i (shift i n) n.
  Proof (fun i n => proj2_sig (shiftDep i n)).
*)

End QItv.

Module ZItv <: ItvSig (ZNum).

  Include StdItv ZNum.

  Local Hint Resolve ZtoQ.CeilLeZ ZtoQ.FloorLeZ QNum.LtLe.

  Import ZArith.

  Lemma ZNumLtLeSucc z1 z2: ZNum.Lt z1 z2 -> ZNum.Le (z1+1)%Z z2.
  Proof. 
    unfold ZNum.Lt, ZNum.Le. lia.
  Qed.

  Program Definition tightenL (qb: QItv.bndT): {zb: bndT | forall z: ZNum.t, QItv.satLower qb (ZtoQ.ofZ z) -> satLower zb z } :=
    match qb with
    | QItv.Infty => Infty
    | QItv.Open q => if ZtoQ.isInZ q then Closed ((ZtoQ.ceil q)+1)%Z else Closed (ZtoQ.ceil q)
    | QItv.Closed q => Closed (ZtoQ.ceil q)
    end.
  Obligation 2.
   rewrite ZtoQ.Ceil_exact; auto.
   apply ZNumLtLeSucc.
   rewrite ZtoQ.LtCommutes. rewrite <- e.
   auto.
  Qed.
  Obligation 3.
    rewrite <- (ZtoQ.CeilZ z); auto.
  Qed.
  Obligation 4.
    rewrite <- (ZtoQ.CeilZ z); auto.
  Qed.

  Lemma ZNumLtLePred z1 z2: ZNum.Lt z1 z2 -> ZNum.Le z1 (z2-1)%Z.
  Proof. 
    unfold ZNum.Lt, ZNum.Le. lia.
  Qed.

  Program Definition tightenU (qb: QItv.bndT): {zb: bndT | forall z: ZNum.t, QItv.satUpper qb (ZtoQ.ofZ z) -> satUpper zb z } :=
     match qb with
     | QItv.Infty => Infty
     | QItv.Open q => if ZtoQ.isInZ q then Closed ((ZtoQ.floor q)-1)%Z else Closed (ZtoQ.floor q)
     | QItv.Closed q => Closed (ZtoQ.floor q)
     end.
  Obligation 2.
   rewrite ZtoQ.Floor_exact; auto.
   apply ZNumLtLePred.
   rewrite ZtoQ.LtCommutes. rewrite <- e.
   auto.
  Qed.
  Obligation 3.
   rewrite <- (ZtoQ.FloorZ z); auto.
  Qed.
  Obligation 4.
   rewrite <- (ZtoQ.FloorZ z); auto.
  Qed.

  Program Definition fromQItv (qi: QItv.t): t
  := {| lower := tightenL (QItv.lower qi); upper :=  tightenU (QItv.upper qi) |}.

  Lemma fromQItv_correct (qi: QItv.t) (z: ZNum.t): QItv.sat qi (ZtoQ.ofZ z) -> sat (fromQItv qi) z.
  Proof.
    unfold fromQItv, sat, QItv.sat.
    destruct (tightenL (QItv.lower qi)).
    destruct (tightenU (QItv.upper qi)).
    simpl; intuition.
  Qed.

End ZItv.

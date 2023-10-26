(** We provide here a basic interval abstract domain
    for polynomial expressions over Z.

  Authors: Alexandre Maréchal et Sylvain Boulmé.
 *)

Require Import NumC.
Require Import Debugging.
Require Import Itv.
Require Export ZNone.
Require Import DomainInterfaces.
Require Import LinTerm.
Require Import String.
Require Import Lia.
Open Scope string_scope.
Import ZN.

Open Scope Z_scope.
Open Scope option_scope.
Open Scope ZN.

Module ZNItv <: ItvSig ZNum.

Record itv: Type := { low: ZN.t; up: ZN.t}.

Definition t:=itv.

Definition sat (i:itv) zn: Prop := low i <= Some zn <= up i.
Hint Unfold sat: zn.

Lemma sat_low i zn: sat i zn -> low i <= Some zn.
Proof.
  unfold sat; intuition.
Qed.
Hint Resolve sat_low: zn.

Lemma sat_up i zn: sat i zn -> Some zn <= up i.
Proof.
  unfold sat; intuition.
Qed.
Hint Resolve sat_up: zn.

Program Definition top: itv 
  := {| low := None ; up := None |}.

Lemma top_correct zn: sat top zn.
Proof.
  unfold sat; simpl; intuition. 
Qed.
Hint Resolve top_correct: zn.


(** Import from Alexis's datatype *)
Program Definition fromBndT (b: ZItv.bndT): ZN.t :=
  match b with
  | ZItv.Infty => None
  | ZItv.Open n => failwith INTERN "ZNItv.fromZItv requires no open bound"%string None
  | ZItv.Closed n => Some n
  end.

Lemma ceilFromBndT_correct b z: ZItv.satLower b z -> (fromBndT b) <= (Some z).
Proof.
  destruct b; simpl; auto.
Qed.
Hint Resolve ceilFromBndT_correct: zn.

Lemma floorFromBndT_correct b z: ZItv.satUpper b z -> (Some z) <= (fromBndT b).
Proof.
  destruct b; simpl; auto.
Qed. 
Hint Resolve floorFromBndT_correct: zn.

Local Hint Resolve ceilFromBndT_correct floorFromBndT_correct.

(* preconditions for precision (not verified in Coq):
     interval [i] must not use Open bounds !
*)
Definition fromZItv (i:ZItv.t): itv
 := {| low := fromBndT (ZItv.lower i); up := fromBndT (ZItv.upper i) |}.

Lemma fromZItv_correct i z: ZItv.sat i z -> sat (fromZItv i) z.
Proof.
  unfold sat, ZItv.sat.
  destruct i; simpl; intuition; simpl_arith.
Qed.

(** converse *)
Program Definition toBndT (b: ZN.t): ZItv.bndT :=
  match b with
  | None => ZItv.Infty 
  | Some n => ZItv.Closed n
  end.

Lemma ceilToBndT_correct b z: b <= (Some z) -> ZItv.satLower (toBndT b) z.
Proof.
  destruct b; simpl; auto.
Qed.

Lemma floorToBndT_correct b z: (Some z) <= b -> ZItv.satUpper (toBndT b) z.
Proof.
  destruct b; simpl; auto.
Qed. 

Local Hint Resolve ceilToBndT_correct floorToBndT_correct.
Definition toZItv (i:itv): ZItv.t
 := {| ZItv.lower := toBndT (low i); ZItv.upper := toBndT (up i) |}.

Lemma toZItv_correct i z: sat i z -> ZItv.sat (toZItv i) z.
Proof.
  unfold sat, ZItv.sat.
  destruct i; simpl; intuition; simpl_arith.
Qed.

(* preconditions for precision (not verified in Coq):
     interval [i] must not be ZItv.Bot !
*)
Program Definition fromQItv (i:QItv.t): itv
 := fromZItv (ZItv.fromQItv i).

Lemma fromQItv_correct i z: QItv.sat i (ZtoQ.ofZ z) -> sat (fromQItv i) z.
Proof.
  intros; apply fromZItv_correct.
  apply ZItv.fromQItv_correct; auto.
Qed.

(** Operators of the abstract domain *)
Definition single (z:Z): itv := 
  let zn:=Some z in
  {| low := zn  ; up := zn |}.

Lemma single_correct z:  sat (single z) z.
Proof.
  unfold sat; intuition auto with zn.
Qed.
Hint Resolve single_correct: zn.

Definition select (m:mode) l u :=
  match m with
  | BOTH => {| low:=l; up := u |}
  | UP => {| low:=None; up:=u |}
  | LOW => {| low := l; up := None |}
  end.
(* VERY IMPORTANT FOR EFFICENCY ! 
   => select must be a LAZY operator...
*)
Extraction Inline select.

Lemma select_correct m l u zn: l <= Some zn -> Some zn <= u -> sat (select m l u) zn.
Proof.
  unfold sat, select.
  destruct m;  simpl_arith; intuition auto with zn.
Qed.
Hint Resolve select_correct: zn.

Definition add (m:mode) (i1 i2: itv): itv 
  := select m ((low i1)+(low i2)) ((up i1)+(up i2)).
(* Extraction add. *)

Lemma add_correct m i1 i2 zn1 zn2: sat i1 zn1 -> sat i2 zn2 -> sat (add m i1 i2) (zn1+zn2).
Proof.
  unfold add. intros; apply select_correct; fold ((Some zn1)+(Some zn2)); auto with zn.
Qed.
Hint Resolve add_correct: zn.

(* opp with a mode with mode *)
Definition oppX m (i: itv): itv 
  := select m (opp(up i)) (opp(low i)).

Lemma oppX_correct m i zn: sat i zn -> sat (oppX m i) (Z.opp zn).
Proof.
  unfold oppX. intros; apply select_correct; fold (ZN.opp (Some zn)); auto with zn.
Qed.
Hint Resolve oppX_correct: zn.

(* A version of opp without mode because it does not improve efficiency ! *) 
Definition opp (i: itv): itv 
  := {| low:=opp(up i); up:=opp(low i) |}.

Lemma opp_correct i zn: sat i zn -> sat (opp i) (Z.opp zn).
Proof.
  unfold sat. 
  fold (ZN.opp (Some zn)).
  generalize (Some zn); simpl; intuition auto with zn.
Qed.
Hint Resolve opp_correct: zn.

Definition oppMode m :=
  match m with
  | BOTH => BOTH
  | UP => LOW
  | LOW => UP
  end.

Definition join (m: mode) (i1 i2: itv): itv 
  := select m (ZN.meet (low i1) (low i2)) (ZN.join (up i1) (up i2)).

Lemma join_correct_l m i1 i2 zn: sat i1 zn -> sat (join m i1 i2) zn.
Proof.
  unfold join; simpl_arith; auto with zn.
Qed.

Lemma join_correct_r m i1 i2 zn: sat i2 zn -> sat (join m i1 i2) zn.
Proof.
  unfold join; simpl_arith; auto with zn.
Qed.

(* multiplication of [Some(a),Some(a)] with i *)
Definition mulZ m (a:Z) (i: itv): itv
  := if Z_isNat a then
       select m (ZN.mulZ a (low i)) (ZN.mulZ a (up i))
     else (* a < 0 *)
       select m (ZN.mulZ1 a (up i)) (ZN.mulZ1 a (low i)).
Extraction Inline mulZ.

Lemma mulZ_correct m z1 i z2: sat i z2 -> sat (mulZ m z1 i) (z1*z2).
Proof.
  unfold mulZ; intro H; destruct (Z_isNat z1); apply select_correct;
  try (rewrite <- mulZ_Some); unfold sat in * |-; generalize (Some z2) H; 
  intuition; simpl_arith.
Qed.
Hint Resolve mulZ_correct: zn.

(* multiplication of [Some(a),Some(b)] with i *)
Definition mulZZ m (a b:Z) (i2: itv): itv
  := join m (mulZ m a i2) (mulZ m b i2).
Extraction Inline mulZZ.

Lemma mulZZ_correct m a b z1 i2 z2: (a <= z1)%Z -> (z1 <= b)%Z -> sat i2 z2 -> sat (mulZZ m a b i2) (z1*z2).
Proof.
  generalize (mulZ_correct m a i2 z2) (mulZ_correct m b i2 z2);
  intros; unfold sat in * |-; intuition; apply select_correct. 
  * destruct (Z_isNat z2).
    + apply meet_le_l.
      eapply ZN.le_trans; eauto.
      simpl. auto with zarith.
    + apply meet_le_r.
      eapply ZN.le_trans; eauto.
      simpl. auto with zarith.
  * destruct (Z_isNat z2).
    + apply join_le_r with (z:=Some(z1*z2)).
      eapply ZN.le_trans; eauto.
      simpl. auto with zarith.
    + apply join_le_l with (z:=Some(z1*z2)).
      eapply ZN.le_trans; eauto.
      simpl. auto with zarith.
Qed.
Hint Resolve mulZZ_correct: zn.

(* multiplication of [None,None] with i *)
Definition mulNN i: itv
  := if ZN.isZero (low i) then
       if ZN.isZero (up i) then
         i
       else
         top
     else
       top.
Extraction Inline mulNN.

Lemma mulNN_correct z1 i z2: sat i z2 -> sat (mulNN i) (z1*z2).
Proof.
  unfold mulNN.
  case (isZero (low i)); auto with zn.
  case (isZero (up i)); auto with zn.
  unfold sat; intros H H0; rewrite H, H0; simpl.
  intros; cutrewrite (z2=0); lia.
Qed.
Hint Resolve mulNN_correct: zn.

Definition bndLow z: itv
  := {| low:=Some z; up:=None |}.
Extraction Inline bndLow.

Definition bndUp z: itv
  := {| low:=None; up:=Some z |}.
Extraction Inline bndUp.

Definition isLOW (m: mode): bool :=
  match m with
  | LOW => true
  | _ => false
  end.
Extraction Inline isLOW.

Definition isUP (m: mode): bool :=
  match m with
  | UP => true
  | _ => false
  end.
Extraction Inline isUP.

(* multiplication of [Some b1,None] with [None, Some b2] *)
Definition mulZNNZ m b1 b2: itv 
  := if isLOW m then top
     else if Z_isNat b1 then (* 0 <= b1 *)
       if Z_isNegNat b2 then (* b2 <= 0 *)
         bndUp (b1*b2)
       else
         top
     else (* b1 < 0 *) 
       top.
Extraction Inline mulZNNZ.

Lemma mulZNNZ_correct m b1 z1 b2 z2: (b1 <= z1)%Z  -> (z2 <= b2)%Z -> sat (mulZNNZ m b1 b2) (z1*z2).
Proof.
  unfold mulZNNZ.
  case (isLOW m); auto with zn.
  case (Z_isNat b1); auto with zn.
  case (Z_isNegNat b2); auto with zn.
  unfold sat; simpl. intuition.
  eauto with zle_compat.
Qed.
Hint Resolve mulZNNZ_correct: zn.

(* multiplication of [Some b1,None] with [Some b2, None] *)
Definition mulZNZN m b1 b2: itv 
 := if isUP m then top
    else if Z_isNat b1 then (* 0 <= b1 *)
       if Z_isNat b2 then (* 0 <= b2  *)
         bndLow (b1*b2)
       else
         top
     else (* b1 < 0 *) 
       top.
Extraction Inline mulZNZN.

Lemma mulZNZN_correct m b1 z1 b2 z2: (b1 <= z1)%Z  -> (b2 <= z2)%Z -> sat (mulZNZN m b1 b2) (z1*z2).
Proof.
  unfold mulZNZN.
  case (isUP m); auto with zn.
  case (Z_isNat b1); auto with zn.
  case (Z_isNat b2); auto with zn.
  unfold sat; simpl. intuition.
  eauto with zle_compat.
Qed.
Hint Resolve mulZNZN_correct: zn.

(* multiplication of [None, Some b1] with [None, Some z2] *)
Definition mulNZNZ m b1 b2: itv 
 := if isUP m then top
    else if Z_isNegNat b1 then (* b1 <= 0 *)
       if Z_isNegNat b2 then (* b2 <= 0 *)
         bndLow (b1*b2)
       else
         top
     else (* b1 > 0 *) 
       top.
Extraction Inline mulNZNZ.

Lemma mulNZNZ_correct m b1 z1 b2 z2: (z1 <= b1)%Z  -> (z2 <= b2)%Z -> sat (mulNZNZ m b1 b2) (z1*z2).
Proof.
  unfold mulNZNZ.
  case (isUP m); auto with zn.
  case (Z_isNegNat b1); auto with zn.
  case (Z_isNegNat b2); auto with zn.
  unfold sat; simpl. intuition.
  eauto with zle_compat.
Qed.
Hint Resolve mulNZNZ_correct: zn.

(* At last, multiplication of two intervals ! *)
Definition mul m i1 i2: itv
  := match (low i1), (up i1) with
     | None, None => mulNN i2
     | Some l1, Some u1 => mulZZ m l1 u1 i2
     | Some l1, None => 
         match (low i2), (up i2) with
         | None, None => top
         | Some l2, Some u2 => mulZZ m l2 u2 i1 (* commut *)
         | Some l2, None => mulZNZN m l1 l2
         | None, Some u2 => mulZNNZ m l1 u2
         end
     | None, Some u1 => 
         match (low i2), (up i2) with
         | None, None => top
         | Some l2, Some u2 => mulZZ m l2 u2 i1 (* commut *)
         | Some l2, None => mulZNNZ m l2 u1
         | None, Some u2 => mulNZNZ m u1 u2 (* commut *)
         end
    end.

Lemma mul_correct m i1 z1 i2 z2: sat i1 z1 -> sat i2 z2 -> sat (mul m i1 i2) (z1*z2).
Proof.
  unfold mul.
  destruct i1 as [l1 u1]; destruct i2 as [l2 u2]; simpl.
  xsimplify ltac: (eauto with zn);
    intros; try subst;
    unfold sat in * |-; simpl in * |-;
    intuition; simpl_arith;
    (* for remainder cases: commut !  *)
    rewrite Z.mul_comm;
    simpl_arith.
Qed.
Hint Resolve mul_correct: zn.

End ZNItv.

Close Scope ZN.
Import ZAffTerm.

Module NA.

  Definition t := (option ZAffTerm.t).

  Definition eval (aft: t) m : ZN.t := (SOME aft <- aft -; Some (ZAffTerm.eval aft m))%option.

  Definition cte (zn: ZN.t) : t :=
   (SOME z <- zn -;
    Some ({| lin := Lin.nil ; cte := z |}))%option.

   Lemma cte_correct zn m: eval (cte zn) m = zn.
   Proof.
      unfold cte; xsimplify ltac:(autorewrite with linterm;eauto).
   Qed.

   Definition add (aft1 aft2: t): t :=
     (SOME aft1 <- aft1 -;
      SOME aft2 <- aft2 -;
      Some (ZAffTerm.add aft1 aft2))%option.

   Lemma add_correct aft1 aft2 m: eval (add aft1 aft2) m = ZN.add (eval aft1 m) (eval aft2 m).
   Proof.
      unfold add; xsimplify ltac:(autorewrite with linterm;eauto).
   Qed.

   Definition opp (aft: t): t :=
     (SOME aft <- aft -;
      Some (ZAffTerm.opp aft))%option.

   Lemma opp_correct aft m: eval (opp aft) m = ZN.opp (eval aft m).
   Proof.
      unfold opp; xsimplify ltac:(autorewrite with linterm;eauto).
   Qed.

   (* NB: imprecise if aft is zero in the context ! *)
    Definition mul (zn:ZN.t) (aft: ZAffTerm.t): t :=
       if ZAffTerm.isZero aft then
          Some ZAffTerm.nil
       else
          (SOME z <- zn -;
           Some (ZAffTerm.mul z aft))%option.

   Lemma mul_correctX c aft m: eval (mul c aft) m = ZN.mulZ1 (ZAffTerm.eval aft m) c \/ aft=nil.
   Proof.
      unfold mul. intros; generalize (ZAffTerm.isZero_correct aft); destruct (ZAffTerm.isZero aft); simpl; intuition.
      constructor 1; xsimplify ltac:(autorewrite with linterm;eauto).
      rewrite Z.mul_comm; auto.
   Qed.

   Lemma mul_correct c aft m: aft<>nil -> eval (mul c aft) m = ZN.mulZ1 (ZAffTerm.eval aft m) c.
   Proof.
      unfold mul. intros; case (mul_correctX c aft m); intuition.
   Qed.

   Definition mulZ1 z (aft: t) : t :=
     (SOME aft <- aft -;
      Some (ZAffTerm.mul z aft))%option.
      
   Lemma mulZ1_correct c aft m: eval (mulZ1 c aft) m = ZN.mulZ1 c (eval aft m).
   Proof.
      unfold mulZ1; xsimplify ltac:(autorewrite with linterm;eauto).
   Qed.

   Definition mulZ z (aft: t) : t :=
     match aft with
     | Some aft => Some (ZAffTerm.mul z aft)
     | None => if Z_isZero z then
                  Some ZAffTerm.nil
               else
                  None
     end.
       
   Lemma mulZ_correct c aft m: eval (mulZ c aft) m = ZN.mulZ c (eval aft m).
   Proof.
      unfold mulZ; xsimplify ltac:(autorewrite with linterm;eauto).
      - unfold ZNum.mul; ZN.simpl_arith.
      - destruct (Z_isZero c); intros; subst; simpl; ZN.simpl_arith.
   Qed.
    
   Hint Rewrite mulZ1_correct mulZ_correct cte_correct add_correct mul_correct opp_correct: linterm.

End NA.

Module NAItv.

   Record itv: Type := { low: NA.t; up: NA.t}.

   Definition eval (i: itv) m: ZNItv.t := {| ZNItv.low := NA.eval (low i) m ; ZNItv.up := NA.eval (up i) m |}.

   Definition cte (i: ZNItv.t) : itv :=
     {| low := NA.cte (ZNItv.low i); up := NA.cte (ZNItv.up i) |}.

   Lemma cte_correct i m: eval (cte i) m = i.
   Proof.
      unfold cte, eval; destruct i; simpl; autorewrite with linterm. auto.
   Qed.

   Definition single aft: itv := 
     let bnd:=Some aft in
     {| low := bnd  ; up := bnd |}.

   Lemma single_correct aft m: eval (single aft) m = ZNItv.single (ZAffTerm.eval aft m).
   Proof.
     auto.
   Qed.
   Hint Rewrite single_correct: linterm.

   Definition select mo l u :=
   match mo with
   | BOTH => {| low:=l; up := u |}
   | UP => {| low:=None; up:=u |}
   | LOW => {| low := l; up := None |}
   end.
   Extraction Inline select.

   Lemma select_correct mo l u m: eval (select mo l u) m = ZNItv.select mo (NA.eval l m) (NA.eval u m).
   Proof.
     case mo; simpl; auto.
   Qed.
   Hint Rewrite select_correct: linterm.
   
   Definition add mo (i1 i2: itv): itv 
     := select mo (NA.add (low i1) (low i2)) (NA.add (up i1) (up i2)).

   Lemma add_correct mo i1 i2 m: eval (add mo i1 i2) m = ZNItv.add mo (eval i1 m) (eval i2 m).
   Proof.
     unfold add, ZNItv.add; autorewrite with linterm. auto.
   Qed.

   Definition opp mo (i: itv): itv 
     := select mo (NA.opp (up i)) (NA.opp (low i)).

   Lemma opp_correct mo i m: eval (opp mo i) m = ZNItv.oppX mo (eval i m).
   Proof.
     unfold opp, ZNItv.oppX; autorewrite with linterm. auto.
   Qed.

   Definition mulZ mo c (i:itv) : itv 
     := if Z_isNat c then
         select mo (NA.mulZ c (low i)) (NA.mulZ c (up i))
        else
         select mo (NA.mulZ1 c (up i)) (NA.mulZ1 c (low i)).

   Lemma mulZ_correct mo c i m: eval (mulZ mo c i) m = ZNItv.mulZ mo c (eval i m).
   Proof.
     unfold mulZ, ZNItv.mulZ; destruct (Z_isNat c); autorewrite with linterm; auto.
   Qed.

   Definition mulN mo (i: ZNItv.t) aft: itv 
     := select mo (NA.mul (ZNItv.up i) aft) (NA.mul (ZNItv.low i) aft).

   Lemma mulN_correct mo i aft m: ~(0 <= ZAffTerm.eval aft m) -> eval (mulN mo i aft) m = ZNItv.mulZ mo (ZAffTerm.eval aft m) i.
   Proof.
     unfold mulN, ZNItv.mulZ.
     intros X; assert (H: aft <> nil).
     - intro Y; subst; case X; autorewrite with linterm; ZNum.simplify.
     - intros; destruct (Z_isNat (ZAffTerm.eval aft m)); try lia.
     autorewrite with linterm; auto.
   Qed.

   Definition mulP1 mo (i: ZNItv.t) aft: itv 
     := select mo (NA.mul (ZNItv.low i) aft) (NA.mul (ZNItv.up i) aft).

   Local Transparent ZAffTerm.isZero.
   Lemma mulP1_correct mo i aft z m: 0 <= ZAffTerm.eval aft m -> ZNItv.sat i z -> 
        ZNItv.sat (eval (mulP1 mo i aft) m) ((ZAffTerm.eval aft m)*z).
   Proof.
     unfold mulP1; intros; rewrite select_correct. apply ZNItv.select_correct.
     - destruct (NA.mul_correctX (ZNItv.low i) aft m) as [H1|H1]; rewrite H1; clear H1.
       + rewrite <- ZN.mulZ1_Some; 
         unfold ZNItv.sat in * |-; generalize (Some z) H0;
         intuition; ZN.simpl_arith. 
       + unfold NA.mul; simpl; autorewrite with linterm; ZNum.simplify.
     - destruct (NA.mul_correctX (ZNItv.up i) aft m) as [H1|H1]; rewrite H1; clear H1.
       + rewrite <- ZN.mulZ1_Some;
         unfold ZNItv.sat in * |-; generalize (Some z) H0;
         intuition; ZN.simpl_arith.
       + unfold NA.mul; simpl; autorewrite with linterm; ZNum.simplify.
  Qed.
  Hint Resolve mulP1_correct: zn.
  Hint Rewrite cte_correct add_correct opp_correct mulZ_correct mulP1_correct mulN_correct: linterm.

End NAItv.


(* Basic definitions on variables *)

Require Export BinNums.
Require Import PArith.BinPosDef.
Require Import PArith.BinPos.
Require Import ZArith.
Require String.
Require CoqAddOn.
Require Import Structures.Equalities.

Require Export Setoid.
Require Export Relation_Definitions.
Require Export Morphisms.
Require Import Program.Basics.
Require Import Lia.
Require Extraction.

Hint Resolve f_equal f_equal2.

Module PVar.
(** Wrapper of [positive] numbers (variable are positive).
Provides also functions for communication with Ocaml. *)

  Definition t := positive.

  Definition isEq: t -> t -> bool
    := Pos.eqb.

  Lemma EqIsEq: forall x1 x2: t, isEq x1 x2 = true <-> x1 = x2.
  Proof Pos.eqb_eq.

  Lemma eq_dec: forall (x y: t), {x=y} + {x<>y}.
  Proof Pos.eq_dec.
  (* Extraction directives in order to have a good extraction
     for "var_eq_dec"
  *)
  Extraction Inline Pos.eq_dec eq_rec eq_rec_r f_equal.

  (* Check the resulting extraction. *)
  (*
  Extraction eq_dec.
  *)

  Import Orders.

  Definition Lt: t -> t -> Prop
    := Pos.lt.
  
  Definition isLt: t -> t -> bool
    := Pos.ltb.

  Lemma LtIsLt: forall x1 x2: t, isLt x1 x2 = true <-> Lt x1 x2.
    intros x1 x2.
    unfold isLt, Pos.ltb, Lt, Pos.lt.
    destruct (Pos.compare_spec x1 x2); intuition (discriminate || auto).
  Qed.

  Definition Le: t -> t -> Prop
    :=Pos.le.

  Definition isLe: t -> t -> bool
    := Pos.leb.

  Lemma LeIsLe: forall x1 x2: t, isLe x1 x2 = true <-> Le x1 x2.
    intros x1 x2; unfold isLe, Le. rewrite <- Pos.leb_le.
    intuition.
  Qed.

  Lemma IsLeTotal : forall x1 x2, isLe x1 x2 = true \/ isLe x2 x1 = true.
    intros x1 x2.
    unfold isLe.
    assert (IsLtTotal := PArith.BinPos.Pos.lt_total).
    assert (LeIsLtEq := BinPos.Pos.le_lteq).
    destruct (IsLtTotal x1 x2) as [h | [h | h]].
    refine (Logic.or_introl (Logic.proj2 (LeIsLe _ _) _)).
    exact ((Logic.proj2 (LeIsLtEq x1 x2)) (Logic.or_introl h)).

    refine (Logic.or_introl (Logic.proj2 (LeIsLe _ _) _)).
    exact ((Logic.proj2 (LeIsLtEq x1 x2)) (Logic.or_intror h)).

    refine (Logic.or_intror (Logic.proj2 (LeIsLe _ _) _)).
    exact ((Logic.proj2 (LeIsLtEq x2 x1)) (Logic.or_introl h)).
  Qed.

  Definition export: t -> BinNums.positive
    := fun x => x.

  Definition import: BinNums.positive -> t
    := fun x => x.

  Import Ascii String.
  Local Open Scope char_scope.
  Local Open Scope Z_scope.


  Lemma Psucc_lift n: Zpos (Pos.succ n)=1+(Zpos n).
  Proof.
    simpl.
    case n; simpl; auto.
  Qed.

  Lemma Zpos_eq n m: n=m <-> Zpos n=Zpos m.
  Proof.
    intuition; auto.
    congruence.
  Qed.

  Lemma Zpos_Lt n m: Lt n m <-> Zpos n < Zpos m.
  Proof.
    unfold PVar.Lt; intuition.
  Qed.

  Lemma Zpos_Le n m: Le n m <-> Zpos n <= Zpos m.
  Proof.
    unfold PVar.Le; intuition.
  Qed.

  Hint Rewrite Zpos_eq Zpos_Lt Zpos_Le Psucc_lift: pos2Z.

  Ltac pvar_solve := intros; autorewrite with pos2Z in * |- *; try lia.

  Lemma Le_refl : forall x, Le x x.
  Proof.
    pvar_solve.
  Qed.

  Lemma Le_antisym: forall x y, Le x y -> Le y x -> x=y.
  Proof.
    pvar_solve.
  Qed.

  Lemma Le_trans: forall x y z, Le x y -> Le y z -> Le x z.
  Proof.
    pvar_solve.
  Qed.

  Lemma Lt_le_trans:forall x y z, Lt y z -> Le x y -> Lt x z.
  Proof.
    pvar_solve.
  Qed.

  Lemma Lt_diff: forall x y, Lt x y -> x = y -> False.
  Proof.
    pvar_solve.
  Qed.

  Lemma negLt_le: forall x y, ~Lt x y -> Le y x.
  Proof.
    pvar_solve.
  Qed.

  Lemma Lt_negLe: forall x y, Lt x y -> ~Le y x.
  Proof.
    pvar_solve.
  Qed.

  Lemma Lt_succ n: Lt n (Pos.succ n).
  Proof.
    pvar_solve.
  Qed.

  Lemma Succ_Le_compat_r n m: Le n m -> Le n (Pos.succ m).
  Proof.
    pvar_solve.
  Qed.


  Lemma Le_pred n: Le (Pos.pred n) n.
  Proof.
    case (Pos.succ_pred_or n).
    intros; subst; simpl; intuition.
    intros H; rewrite <- H at 2.
    pvar_solve.
  Qed.
  
  Lemma Le_Lt_pred n m: n <> m -> (Lt (Pos.pred n) m <-> Lt n m).
  Proof.
    case (Pos.succ_pred_or n).
    intros; subst; simpl; intuition.
    intros H; rewrite <- H at 1 3.
    pvar_solve.
  Qed.
  
  Lemma xH_min: forall n, Le xH n.
  Proof.
    intros; generalize (Zgt_pos_0 n); pvar_solve.
  Qed.

  Definition max : t -> t -> t := PArith.BinPos.Pos.max.

  Definition max_l: forall x y, Le x (max x y) := PArith.BinPos.Pos.le_max_l.

  Definition max_r: forall x y, Le y (max x y) := PArith.BinPos.Pos.le_max_r.

  Lemma max_1_l: forall x, max xH x = x.
  Proof.
    intros; rewrite Pos.max_r_iff.
    apply xH_min.
  Qed.

  Lemma max_1_r: forall x, max x xH = x.
  Proof.
    intros; rewrite Pos.max_l_iff.
    apply xH_min.
  Qed.

  Lemma rew_max_l: forall n m, Le m n -> max n m=n.
  Proof. 
    intros; rewrite Pos.max_l_iff; auto.
  Qed.

  Lemma rew_max_r: forall n m, Le n m -> max n m = m.
  Proof. 
    intros; rewrite Pos.max_r_iff; auto.
  Qed.

  Lemma max_id: forall n, max n n = n.
  Proof.
    intros; rewrite Pos.max_id; auto.
  Qed.

  Hint Rewrite max_1_l max_1_r: rwmax1.
  
  Lemma max_assoc m n p : max (max m n) p = max m (max n p).
  Proof.
    unfold max; rewrite Pos.max_assoc; auto.
  Qed.
  Hint Rewrite max_1_l max_1_r max_id max_assoc: rwmax.

  Definition max_comm: forall n m, max n m = max m n := Pos.max_comm.

  Create HintDb progvar discriminated.
  Hint Resolve xH_min Le_refl Le_pred Le_trans max_l max_r LeIsLe LtIsLt Lt_le_trans Lt_diff Succ_Le_compat_r Lt_succ: progvar.

  Lemma Le_max_rew_r: forall x y z, Le x (max y z) <-> (Le x y \/ Le x z).
  Proof.
    intros; constructor 1.
    apply Pos.max_case_strong; intuition.
    intuition eauto with progvar.
  Qed.

  Lemma Le_max_rew_l: forall x y z, Le (max y z) x <-> (Le y x /\ Le z x).
  Proof.
    intros; apply Pos.max_case_strong; intuition eauto with progvar.
  Qed.

  Lemma Le_max_inject_l: forall x1 x2 y1 y2 z, Le x1 x2 -> Le y1 y2 -> Le (max x2 y2) z -> Le (max x1 y1) z.
  Proof.
    intros; rewrite Le_max_rew_l in * |- *; intuition eauto with progvar.
  Qed.

  Definition pr: t -> string
    := fun x => String "v" (CoqAddOn.posPr x).

  Ltac max_simplify := autorewrite with rwmax1 in * |- ; 
  repeat (rewrite max_id in * |- * 
     || rewrite Le_max_rew_l 
     || rewrite Le_max_rew_r); 
    intuition auto with progvar.

End PVar.

Definition bExt {A B} (pred: A -> Prop) (f1 f2: A -> B)
  := forall x, (pred x) -> (f1 x)=(f2 x).

Lemma bExt_refl {A B} pred (f: A -> B):
  bExt pred f f.
Proof.
  unfold bExt; auto.
Qed.

Lemma bExt_sym {A B} (pred: A -> Prop) (f1 f2: A -> B):
  bExt pred f1 f2 -> bExt pred f2 f1.
Proof.
  unfold bExt; intros; symmetry; auto.
Qed.

Hint Immediate bExt_sym.

Lemma bExt_trans {A B} (pred: A -> Prop) (f1 f2 f3: A -> B):
  bExt pred f1 f2 -> bExt pred f2 f3 -> bExt pred f1 f3.
Proof.
  unfold bExt; intros; apply eq_trans with (y:=f2 x); auto.
Qed.

Lemma bExt_monotonic {A B} (pred1 pred2: A -> Prop) (f1 f2: A -> B):
  bExt pred1 f1 f2 -> (forall x, pred2 x -> pred1 x) -> bExt pred2 f1 f2.
Proof.
  unfold bExt; eauto.
Qed.

Hint Unfold bExt.

Instance bExt_equiv {A B} (pred: A -> Prop): Equivalence (@bExt A B pred).
Proof.
  constructor 1.
  + intros f; apply bExt_refl.
  + intros f1 f2; apply bExt_sym.
  + intros f1 f2 f3; apply bExt_trans.
Qed.

(* Basic definitions to handle "maps" on variables, 
   with maps encoded as total functions.
*)

Infix "°=" := (pointwise_relation _ Logic.eq) (at level 70, no associativity).
Hint Unfold pointwise_relation.

Hint Resolve bExt_monotonic: bExt.

Module Mem.

  Definition t (A:Type) := PVar.t -> A.

(** [assign x val s] = push the pair [(x,val)] into [m] *)
  Definition assign {A} (x: PVar.t) (val:A) (m: Mem.t A)
    := fun x' => if PVar.eq_dec x x' then val else (m x'). 

  Lemma assign_in {A} x (val:A) m: assign x val m x = val.
  Proof.
    unfold assign; case (PVar.eq_dec x x); tauto.
  Qed.
  Hint Resolve assign_in: progvar.
  Hint Rewrite @assign_in: progvar.

  Lemma assign_out {A} x (val:A) m x': x<>x' -> assign x val m x' = m x'.
  Proof.
    unfold assign; case (PVar.eq_dec x x'); try (intros; subst; tauto).
  Qed.
  Hint Resolve assign_out: progvar. 

  Lemma assign_id {A} x y (m:Mem.t A): assign x (m x) m y = m y.
  Proof.
    unfold assign; case (PVar.eq_dec x y); auto.
  Qed.
  Hint Resolve assign_id: progvar.
  Hint Rewrite @assign_id: progvar.

  Lemma assign_commutes {A} x1 x2 (m:Mem.t A) v1 v2:
   x1 <> x2 -> assign x1 v1 (assign x2 v2 m) °= assign x2 v2 (assign x1 v1 m).
  Proof.
    intros H x; unfold assign.
    case (PVar.eq_dec x1 x); case (PVar.eq_dec x2 x); intros; subst; auto.
    case H; auto.
  Qed.

  Lemma assign_absorbes {A} x (m:Mem.t A) v1 v2:
     assign x v1 (assign x v2 m) °= assign x v1 m.
  Proof.
    intros x'; unfold assign.
    case (PVar.eq_dec x x'); intros; auto.
  Qed.
  Hint Rewrite @assign_absorbes: progvar.


  Add Parametric Morphism A: (@assign A) with 
    signature Logic.eq ==> Logic.eq ==> pointwise_relation PVar.t Logic.eq ==> pointwise_relation PVar.t Logic.eq
    as assign_morphism.
  Proof.
    unfold assign; intros x v m m' H y.
    case (PVar.eq_dec x y); congruence.
  Qed.

  Lemma free_equiv {A} x (m1 m2:Mem.t A): bExt (fun x' => x<>x') m1 m2 <-> m1 °= assign x (m1 x) m2.
  Proof.
    unfold bExt, assign; constructor 1; intros H x'; 
    generalize (H x'); clear H; case (PVar.eq_dec x x'); intros; subst; intuition.
  Qed.


  Definition lift {A B} (f: A -> B) (m:Mem.t A): Mem.t B
    := fun x => f (m x).

  Lemma lift_commutes {A B} (f: A -> B) x v m :
    (lift f (assign x v m)) °= (assign x (f v) (lift f m)).
  Proof.
    unfold assign, lift; intro y; simpl. case (PVar.eq_dec x y); auto.
  Qed.
  Hint Rewrite @lift_commutes: vpl.

  Add Parametric Morphism A B: (@lift A B) with 
    signature pointwise_relation A Logic.eq ==> pointwise_relation PVar.t Logic.eq ==> pointwise_relation PVar.t Logic.eq
    as lift_morphism.
  Proof.
    unfold lift; intros f1 f2 H m1 m2 H0; congruence.
  Qed.

End Mem.


Section MayDependOnDefinitions.

  Context `{expr: Type}.

  Context {mayDependOn: expr -> PVar.t -> Prop}.

  Definition mdBounds (bound: positive) (e: expr) :=
    forall x, (mayDependOn e x) -> PVar.Le x bound.

  Lemma mdBounds_fold (bound: positive) (e: expr) x: (mayDependOn e x) -> mdBounds bound e ->  PVar.Le x bound.
  Proof.
    unfold mdBounds; auto.
  Qed.

  Lemma md_mdBounds e x:  
    mayDependOn e x -> forall bound, mdBounds bound e -> PVar.Lt bound x -> False.
  Proof.
    unfold mdBounds; simpl; intuition eauto with progvar.
  Qed.

  Context {mdBound: expr -> PVar.t -> PVar.t}.

  Class MDBoundVar := {
    mdBound_max: forall e bound, (mdBound e bound) = PVar.max bound (mdBound e xH);
    mdBound_mdBounds: forall e bound, mdBounds (mdBound e bound) e
  }.

   Hypothesis mdb_max: forall e bound, (mdBound e bound) = PVar.max bound (mdBound e xH).

   Lemma mdBound_le: forall e bound, PVar.Le bound (mdBound e bound).
   Proof.
     intros. rewrite mdb_max.
     auto with progvar.
   Qed.

End MayDependOnDefinitions.

Hint Resolve @mdBound_le: progvar.


Section MDBoundProp.

   Context `{mdb:MDBoundVar}.

   Lemma mdBound_comm: forall e1 e2 bound, mdBound e1 (mdBound e2 bound) = mdBound e2 (mdBound e1 bound).
   Proof.
     intros; 
     rewrite mdBound_max.
     rewrite mdBound_max with (e:=e2).
     apply eq_sym;
     rewrite mdBound_max. 
     rewrite mdBound_max with (e:=e1);
     autorewrite with rwmax;
     rewrite (PVar.max_comm (mdBound e1 xH)); auto.
   Qed.

   Lemma mdBound_invol: forall e bound, mdBound e (mdBound e bound) = mdBound e (bound).
   Proof.
     intros; 
     rewrite mdBound_max.
     rewrite (mdBound_max e bound).
     autorewrite with rwmax; auto.
   Qed.

End MDBoundProp.



Section mdoExtDefinition.

  Context {expr: Type} {value: Type} {observer:Type}.

  Context (mayDependOn: expr -> PVar.t -> Prop).

  Context (eval: expr -> (PVar.t -> value) -> observer).
  
  Context (obs_eq: observer -> observer -> Prop).

  Definition frames (pred: PVar.t -> Prop) (e: expr) := forall m1 m2, bExt pred m1 m2 -> obs_eq (eval e m1) (eval e m2).

  Lemma frames_monotonic (pred1 pred2: PVar.t -> Prop) (e: expr): 
    frames pred1 e -> (forall x, pred1 x -> pred2 x) -> frames pred2 e.
  Proof.
    unfold frames; eauto with bExt.
  Qed.

  Definition mdoExt := forall e m1 m2, bExt (mayDependOn e) m1 m2 -> obs_eq (eval e m1) (eval e m2).
                       (* ie. forall e, frames (mayDependOn e) e *)

End mdoExtDefinition.

Section mdoExtProp.

  (* Derived properties *)
  Context {expr: Type} {value: Type} {observer:Type}.
  Context {mayDependOn: expr -> PVar.t -> Prop}.
  Context {eval: expr -> (PVar.t -> value) -> observer}.
  Context {obs_eq: observer -> observer -> Prop}.
  Context {obs_eq_eq:@Equivalence observer obs_eq}.
  Context (eval_mdo: mdoExt mayDependOn eval obs_eq).

  (* extensionality of eval *)
  Instance eval_pointwise_compat: Proper (Logic.eq ==> pointwise_relation PVar.t Logic.eq ==> obs_eq) eval.
  Proof.
    intros x y H1 m1 m2 H2.
    subst.
    erewrite eval_mdo; eauto.
  Qed.

 
  Lemma mdoExt_free: forall e x m1 m2, ~(mayDependOn e x) -> bExt (fun x' => x <> x') m1 m2 -> obs_eq (eval e m1) (eval e m2).
                     (* ie. forall e x, ~(mayDependOn e x) ->  frames eval obs_eq (fun x' => x <> x') e *)
  Proof.
     intros.
     eapply eval_mdo; eauto.
     intros y H1. rewrite H0; auto.
     intro; subst; intuition.
  Qed.
 

End mdoExtProp.

Section MayDepOnWithIff.

  Context {expr: Type} {value: Type}.

  Context {mayDependOn: expr -> PVar.t -> Prop}.

  Context {sat: expr -> (PVar.t -> value) -> Prop}.
  Context (sat_mdo_impl: mdoExt mayDependOn sat impl).
 
  Lemma sat_mdo_iff: mdoExt mayDependOn sat iff.
  Proof.
    constructor 1; (intros; eapply sat_mdo_impl; [idtac | eauto]); auto.  
  Qed.    

End MayDepOnWithIff.



Section ExtensionalityWithIff.

  Context {expr:Type} {value:Type}.

  Context (sat: expr -> (PVar.t -> value) -> Prop).
  Context (sat_compat_impl: Proper (Logic.eq ==> pointwise_relation PVar.t Logic.eq ==> impl) sat).

  Program Instance sat_compat_iff: Proper (Logic.eq ==> pointwise_relation PVar.t Logic.eq ==> iff) sat.
  Obligation 1.
    constructor 1; rewrite H; rewrite H0; auto.
  Qed.    
 
End ExtensionalityWithIff.


Section Rename.

  Context {expr: Type} {value: Type} {observer:Type}.
  Context (eval: expr -> (PVar.t -> value) -> observer).
  Context (obs_eq: observer -> observer -> Prop).
  (** obs_eq is "morally" an equivalence. But a preorder suffices *)
  Context {obs_eq_eq:@PreOrder observer obs_eq}.

  (** Condition stating that [re] is a rename of [e] where [x] is replaced by [y].
      This is a strong version, with no hypothesis on [y]
  *)
  Definition isRename (re e: expr) (x y:PVar.t) : Prop :=
    forall m, obs_eq (eval e (Mem.assign x (m y) m)) (eval re m).

  (** A variant of the previous definition, where [y] is assumed to be "fresh" in the context
      (or more exactly, [y] has no effect on the result of [eval e m])
  *) 
  Definition isFreshOnlyRename  (re e: expr) (x y:PVar.t): Prop :=
    forall m, 
     (forall m2, bExt (fun x' => y <> x') m m2 -> obs_eq (eval e m) (eval e m2))
      -> (forall v, obs_eq (eval e m) (eval re (Mem.assign y (m x) (Mem.assign x v m)))).

  Lemma rename_prop (re e: expr) (x y:PVar.t):
     (isRename re e x y) -> (isFreshOnlyRename re e x y).
  Proof.
    unfold isRename, isFreshOnlyRename.
    intros H1 m H2 v. rewrite <- H1. autorewrite with progvar.
    apply H2; unfold bExt; intros x' H3.
    case (PVar.eq_dec x y).
    - intros; subst; autorewrite with progvar; auto.
    - intros;
      rewrite Mem.assign_commutes; auto.
      rewrite Mem.assign_out; auto.
      autorewrite with progvar; auto.
   Qed.

End Rename.

Hint Resolve iff_equivalence.

Hint Resolve sat_mdo_iff: progvar.

Hint Unfold mdBounds: progvar.


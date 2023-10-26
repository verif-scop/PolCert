(** Additional operations and Lemmas w.r.t PositiveMap Library

In particular, we provide correspondance between some operations on PositiveMaps
and (list) operations on "elements". 

This gives an abstract (but computational) view of operations on PositiveMaps
as operations on strictly ordered list of pairs. 

This is useful for LinTerm.v
*)

Require Export BinNums.
Require Import PArith.BinPosDef.
Require Import PArith.BinPos.
Require Export OptionMonad.
Require Export FMapPositive.
Require Import List.
Require Import CoqAddOn.
Require Import Sorting.Permutation.

Local Open Scope type_scope.
Local Open Scope list_scope.
Import List.ListNotations.

Import PositiveMap.

Hint Unfold E.eq.
Hint Resolve f_equal f_equal2.

Arguments Leaf {A}.

(** A particular case of [add] *)
Fixpoint single {A} (x:positive) (v:A) : t A :=
  match x with
  | xH => Node Leaf (Some v) Leaf
  | xO x' => Node (single x' v) None Leaf
  | xI x' => Node Leaf None (single x' v)
  end.

Lemma append_assoc i: forall j k, append (append i j) k = append i (append j k).
Proof.
  induction i; simpl; auto.
Qed.
Hint Rewrite append_assoc append_neutral_r append_neutral_l app_nil_r @SOME_assoc: posmap.
(* Hint Rewrite <- append_assoc_0 append_assoc_1: posmap. *)

Lemma xelements_single {A} x (v:A): forall path, xelements (single x v) path = [(append path x,v)].
Proof.
  induction x; simpl; intros path; try (rewrite IHx); autorewrite with posmap; auto.
Qed.

Theorem elements_single {A} x (v:A): elements (single x v) = [(x,v)].
Proof.
  unfold elements; rewrite xelements_single.
  autorewrite with posmap; auto.
Qed.

Lemma single_equiv_add_Leaf {A} x (v:A): single x v = add x v Leaf.
Proof.
  induction x; simpl; congruence.
Qed.

(* NOT USEFUL ?
Lemma PositiveMap_addspec {A} x1 x2 (v:A) (m: PositiveMap.t A):
  PositiveMap.find x1 (PositiveMap.add x2 v m) = if (Pos.eq_dec x1 x2) then Some v else PositiveMap.find x1 m.
Proof.
  case (Pos.eq_dec x1 x2).
  intros; subst. rewrite PositiveMap.add_1; auto.
  intros; rewrite PositiveMap.gso; auto.
Qed.

Lemma find_single {A} x x0 (v:A): wte (find x0 (single x v)) (fun v0 => (x0,v0)=(x,v)) (x0<>x).
Proof.
  rewrite single_equiv_add_Leaf, PositiveMap_addspec.
  case (Pos.eq_dec x0 x); simpl; auto.
  case x0; simpl; auto.
Qed.
*)


(** Mapping of maps *)

Section SimplerMap.

  Context {A B: Type}.

  Variable f : A -> B.

  Fixpoint map (m : t A) : t B :=
       match m with
        | Leaf => Leaf
        | Node l o r => Node (map l)
                             (option_map f o)
                             (map r)
       end.

Lemma xelements_map (m: t A): forall path, 
  xelements (map m) path = List.map (fun p => (fst p, f (snd p))) (xelements m path).
Proof.
  induction m; simpl; auto.
  intros path. 
  destruct o; simpl; 
  rewrite IHm1, IHm2, List.map_app; auto.
Qed.

Theorem elements_map (m: t A): 
  elements (map m) = List.map (fun p => (fst p, f (snd p))) (elements m).
Proof.
  unfold map, mapi, elements.
  apply xelements_map.
Qed.

End SimplerMap.

(*
Lemma xelements_map {A B} (f: A -> B) (m: t A): forall path, 
  xelements (xmapi (fun _ => f) m path) path = List.map (fun p => (fst p, f (snd p))) (xelements m path).
Proof.
  induction m; simpl; auto.
  intros path. 
  destruct o; simpl; 
  rewrite IHm1, IHm2, List.map_app; auto.
Qed.

Theorem elements_map {A B} (f: A -> B) (m: t A): 
  elements (map f m) = List.map (fun p => (fst p, f (snd p))) (elements m).
Proof.
  unfold map, mapi, elements.
  apply xelements_map.
Qed.
*)

Section SimplerEqual.

Context {A: Type}.
Variable cmp: A -> A -> bool.
Hypothesis cmp_correct: forall x y, If cmp x y THEN x=y.

(* a simpler definition of [equal], where we don't care about un-normalized PositiveMap *)
Fixpoint equal (m1 m2 : t A) : bool :=
    match m1, m2 with
      | Leaf, Leaf => true
      | Node l1 o1 r1, Node l2 o2 r2 =>
           (match o1, o2 with
             | None, None => true
             | Some v1, Some v2 => cmp v1 v2
             | _, _ => false
            end)
           && equal l1 l2 && equal r1 r2
       | _,_  => false
     end.

Lemma equal_correct m1: forall m2, If equal m1 m2 THEN m1=m2.
Proof.
  induction m1; destruct m2; simpl; auto.
  OptionMonad.xsimplify ltac:(subst; eauto).
Qed.

(* NOT USEFUL
Hypothesis cmp_sym: forall x y, cmp x y = cmp y x.
Lemma equal_sym m1: forall m2, equal m1 m2 = equal m2 m1.
Proof.
  induction m1; destruct m2; simpl; auto.
  OptionMonad.xsimplify ltac:(subst; auto).
Qed.
*)

End SimplerEqual.


Lemma elements_spec {A} m x (v:A): List.In (x,v) (elements m) <-> find x m = Some v.
Proof.
  constructor 1; intros H.
  + eapply elements_complete; eauto.
  + eapply elements_correct; eauto.
Qed.

Lemma In_mem {A} m x (v:A): List.In (x,v) (PositiveMap.elements m) -> (PositiveMap.mem x m)=true.
Proof.
  rewrite mem_find, elements_spec.
  intro H; rewrite H; simpl; auto.
Qed.

(* a smart constructor that preserves normalization of PositiveMap *)
Definition node {A} (l:PositiveMap.t A) o (r:PositiveMap.t A) :=
  match l,r,o with
  | Leaf,Leaf,None => Leaf
  | _ , _, _ => Node l o r
  end.

Lemma find_node {A} (l:PositiveMap.t A) o (r:PositiveMap.t A) x: find x (node l o r) = find x (Node l o r).
Proof.
  unfold node; destruct x; destruct l; destruct o; destruct r; simpl; (try (rewrite gempty)); auto.
Qed.

Lemma xelements_node {A} (l:PositiveMap.t A) o (r:PositiveMap.t A): forall path, xelements (node l o r) path = xelements (Node l o r) path.
Proof.
  unfold node; destruct l; destruct o; destruct r; simpl; auto.
Qed.

(** Intermediate lemmas on lt_key and xelements *)

Lemma lt_key_append_O path: forall p, E.lt (append path (xO p)) path.
Proof.
  induction path; simpl; auto.
Qed.

Lemma lt_key_append_I path: forall p, E.lt path (append path (xI p)).
Proof.
  induction path; simpl; auto.
Qed.

Lemma lt_key_append_O_I path: forall p1 p2, E.lt (append path (xO p1)) (append path (xI p2)).
Proof.
  induction path; simpl; auto.
Qed.
Local Hint Resolve lt_key_append_O lt_key_append_I lt_key_append_O_I.

Lemma xelements_Forall_ltkey_O {A} (m:t A): forall path p,
  Forall (fun c => E.lt (fst c) path) (xelements m (append path (xO p))).
Proof.
  induction m; simpl; auto.
  destruct o as [a0 |]; simpl;
  intros; apply Forall_app; autorewrite with posmap; simpl; intuition.
Qed.

Lemma xelements_Forall_ltkey_I {A} (m:t A): forall path p,
  Forall (fun c => E.lt path (fst c)) (xelements m (append path (xI p))).
Proof.
  induction m; simpl; auto.
  destruct o as [a0 |]; simpl;
  intros; apply Forall_app; autorewrite with posmap; simpl; intuition.
Qed.

Lemma xelements_Forall_ltkey_O_I {A} (m:t A): forall path p1 p2,
  Forall (fun c => E.lt (append path (xO p1)) (fst c)) (xelements m (append path (xI p2))).
Proof.
  induction m; simpl; auto.
  destruct o as [a0 |]; simpl;
  intros; apply Forall_app; autorewrite with posmap; simpl; intuition.
Qed.

Lemma xelements_Forall_ltkey_I_O {A} (m:t A): forall path p1 p2,
  Forall (fun c => E.lt (fst c) (append path (xI p1))) (xelements m (append path (xO p2))).
Proof.
  induction m; simpl; auto.
  destruct o as [a0 |]; simpl;
  intros; apply Forall_app; autorewrite with posmap; simpl; intuition.
Qed.
Local Hint Resolve xelements_Forall_ltkey_O xelements_Forall_ltkey_I xelements_Forall_ltkey_O_I xelements_Forall_ltkey_I_O.

Lemma xelements_Forall_exclusion {A} (m1: t A): forall (m2:t A) path p3 p2,
  Forall (fun c => Forall (fun c' => E.lt (fst c) (fst c')) (xelements m2 (append path (xI p3)))) (xelements m1 (append path (xO p2))).
Proof.
  induction m1; simpl; auto.
  destruct o as [a |]; simpl;
  intros; apply Forall_app; autorewrite with posmap; simpl; intuition.
Qed.
Local Hint Resolve xelements_Forall_exclusion.


(** Theorem elements_remove *)

(* a simpler definition of remove for proofs *)
Fixpoint altRemove {A} (i : positive) (m : t A) : t A :=
    match m with
      | Leaf => Leaf
      | Node l o r =>
        match i with
          | xH => node l None r
          | xO i => node (altRemove i l) o r
          | xI i => node l o (altRemove i r)
        end
    end.

Lemma altRemove_def {A} (m: t A): forall i, altRemove i m = remove i m.
Proof.
  induction m as [|m1 IHm1 o m2 IHm2]; destruct i as [i|i|]; simpl; auto.
  rewrite IHm2. unfold node; destruct m1, (remove i m2), o; simpl; auto.
  rewrite IHm1. unfold node; destruct (remove i m1), m2, o; simpl; auto.
Qed.

Lemma append_discr_xI p1: forall p2, append p1 (xI p2) = p1 -> False.
Proof.
  induction p1; simpl; congruence.
Qed.

Lemma append_discr_xO p1: forall p2, append p1 (xO p2) = p1 -> False.
Proof.
  induction p1; simpl; congruence.
Qed.

Lemma append_discr_xI_xO p p1 p2: append p (xI p1) = append p (xO p2) -> False.
Proof.
  induction p; simpl; congruence.
Qed.

Definition eq_key {A} x (c:positive*A) := Pos.eq_dec x (fst c) ||| false.

Lemma Forall_lt_neq_key_1 {A} p (l: list (positive * A)): 
  Forall (fun c => E.lt p (fst c)) l -> Forall (fun c => negb (eq_key p c) = true) l .
Proof.
  intros; eapply Forall_monotone; eauto.
  unfold lt_key, eq_key; simpl; intros c; case (Pos.eq_dec p (fst c)); auto.
  intros; subst; case (E.bits_lt_antirefl (fst c)); auto.
Qed.
Local Hint Resolve Forall_lt_neq_key_1.

Lemma Forall_lt_neq_key_2 {A} p (l: list (positive * A)): 
  Forall (fun c => E.lt (fst c) p) l -> Forall (fun c => negb (eq_key p c) = true) l.
Proof.
  intros; eapply Forall_monotone; eauto.
  unfold lt_key, eq_key; simpl; intros c; case (Pos.eq_dec p (fst c)); auto.
  intros; subst; case (E.bits_lt_antirefl (fst c)); auto.
Qed.
Local Hint Resolve Forall_lt_neq_key_2.

Lemma xelements_remove {A} (m: t A) : forall x path, 
  xelements (remove x m) path = List.filter (fun c => negb (eq_key (append path x) c)) (xelements m path).
Proof.
  intros x path; rewrite <- altRemove_def.
  generalize x path; clear x path.
  induction m as [| m1 IHm1 o m2 IHm2 ]; 
  destruct x as [ x | x |]; simpl; auto;
  intro path; rewrite xelements_node; simpl;
  destruct o as [a |]; simpl; rewrite !filter_app; simpl;
  try rewrite !filter_app; autorewrite with posmap.
  + unfold eq_key at 2; simpl. destruct (Pos.eq_dec (append path x~1) path) as [X|X].
    case (append_discr_xI _ _ X). 
    rewrite IHm2. autorewrite with posmap; simpl; auto.
    rewrite filter_triv_true with (l:=(xelements m1 (append path 2))); auto.
  + rewrite IHm2; autorewrite with posmap; simpl; auto.
    rewrite filter_triv_true with (l:=(xelements m1 (append path 2))); auto.
  + unfold eq_key at 2; simpl. destruct (Pos.eq_dec (append path x~0) path) as [X|X].
    case (append_discr_xO _ _ X). 
    rewrite IHm1; autorewrite with posmap; auto.
    rewrite filter_triv_true with (l:=(xelements m2 (append path 3))); auto.
  + rewrite IHm1; autorewrite with posmap; auto.
    rewrite filter_triv_true with (l:=(xelements m2 (append path 3))); auto.
  + unfold eq_key at 2; simpl. 
    destruct (Pos.eq_dec path path) as [X|X].
    rewrite !filter_triv_true; auto.
    case X; auto.
  + rewrite !filter_triv_true; auto.
Qed.

Lemma elements_remove {A} x (m: t A):
  elements (remove x m) = List.filter (fun c => negb (eq_key x c)) (elements m).
Proof.
  unfold elements; autorewrite with posmap; apply xelements_remove.
Qed.


(** Find/Elements *)
Local Hint Resolve Forall_negb_true_false.

Lemma find_xelements {A} (m:t A): 
 forall x path, match find x m with Some v => [ (append path x,v) ] | None => [] end = 
                 List.filter (eq_key (append path x)) (xelements m path).
Proof.
  induction m; destruct x; simpl; auto;
  intro path; destruct o; simpl; rewrite !filter_app; simpl;
  try rewrite !filter_app; autorewrite with posmap.
  + unfold eq_key at 2; simpl; destruct (Pos.eq_dec (append path x~1) path) as [X|X].
    case (append_discr_xI _ _ X). 
    rewrite filter_triv_false; simpl; auto.
    generalize (IHm2 x (append path 3)). autorewrite with posmap; simpl; auto.
  + rewrite filter_triv_false; auto.
    generalize (IHm2 x (append path 3)). autorewrite with posmap; simpl; auto.
  + unfold eq_key at 2; simpl; destruct (Pos.eq_dec (append path x~0) path) as [X|X].
    case (append_discr_xO _ _ X). 
    rewrite filter_triv_false with (l:=(xelements m2 (append path 3))); auto.
    generalize (IHm1 x (append path 2)). autorewrite with posmap; simpl; auto.
  + rewrite filter_triv_false with (l:=(xelements m2 (append path 3))); auto.
    generalize (IHm1 x (append path 2)). autorewrite with posmap; simpl; auto.
  + unfold eq_key at 2; simpl; destruct (Pos.eq_dec path path) as [X|X].
    rewrite !filter_triv_false; simpl; auto.
    case X; auto.
  + rewrite !filter_triv_false; auto.
Qed.

Lemma find_elements {A} x (m: t A) :
  match find x m with Some v => [ (x,v) ] | None => [] end = List.filter (eq_key x) (elements m).  
Proof.
  rewrite find_xelements with (path:=xH); autorewrite with posmap; auto. 
Qed.

Local Hint Resolve filter_triv_true Forall_false_negb_true filter_empty_false.

Theorem find_remove_elements_Permutation {A} x (m: t A):
  wte (find x m) (fun v => Permutation ((x,v)::(elements (remove x m))) (elements m))
                 (elements (remove x m)=elements m).
Proof.
  rewrite elements_remove. generalize (find_elements x m).
  case (find x m); simpl; auto.
  intros a H; generalize (filter_split _ (eq_key x) (elements m)).
  rewrite <- H; auto.
Qed.

(** Merge Definition and Property *)

Section merge.

  Context {A : Type}.
  Variable f : A -> A -> option A.

  Definition nodeMerge (o1 o2: option A) :=
    match o1 with
    | None => o2
    | Some v1 => match o2 with
                 | None => o1
                 | Some v2 => f v1 v2
                 end
    end.

  Lemma nodeMerge_None_r (o: option A): nodeMerge o None = o.
  Proof.
    destruct o; simpl; auto.
  Qed.

  Fixpoint merge (m1 : t A)(m2 : t A) : t A :=
    match m1 with
    | Leaf => m2
    | Node l1 o1 r1 =>
        match m2 with
        | Leaf => m1
        | Node l2 o2 r2 => node (merge l1 l2) (nodeMerge o1 o2) (merge r1 r2)
        end
    end.

    Lemma find_merge: forall (m1 m2:t A) (i: positive),
      find i (merge m1 m2) = nodeMerge (find i m1) (find i m2).
    Proof.
      induction m1; simpl.
      - intros; rewrite !gempty; simpl; auto.
      - destruct m2; simpl.
          + intros; rewrite !gempty. rewrite nodeMerge_None_r; auto.
          + intros; rewrite find_node. destruct i; simpl; auto.
    Qed.

  Inductive inMerge: list (positive*A) -> list (positive*A) -> list (positive*A) -> Prop :=
  | inM_nil_l l: inMerge [] l l
  | inM_nir_r l: inMerge l [] l
  | inM_LT c1 l1 c2 l2 l: E.lt (fst c1) (fst c2) -> inMerge l1 (c2::l2) l -> inMerge (c1::l1) (c2::l2) (c1::l)
  | inM_EQ_Some x v1 l1 v2 l2 r l: f v1 v2=Some r -> inMerge l1 l2 l -> inMerge ((x,v1)::l1) ((x,v2)::l2) ((x,r)::l)
  | inM_EQ_None x v1 l1 v2 l2 l: f v1 v2=None -> inMerge l1 l2 l -> inMerge ((x,v1)::l1) ((x,v2)::l2) l
  | inM_GT c1 l1 c2 l2 l: E.lt (fst c2) (fst c1) -> inMerge (c1::l1) l2 l -> inMerge (c1::l1) (c2::l2) (c2::l).
  Local Hint Resolve inM_nil_l inM_nir_r inM_LT inM_EQ_Some inM_EQ_None inM_GT Forall_Forall_cons.


  Lemma inMerge_app_r l2: forall l1,
     Forall (fun c => Forall (fun c' => E.lt (fst c) (fst c')) l1) l2
     -> inMerge l1 l2 (l2 ++ l1).
  Proof.
    induction l2; simpl; auto.
    destruct l1; simpl; autorewrite with posmap; intuition auto.
  Qed.

  Lemma inMerge_app_l l1: forall l2,
     Forall (fun c => Forall (fun c' => E.lt (fst c) (fst c')) l2) l1
     -> inMerge l1 l2 (l1 ++ l2).
  Proof.
    induction l1; simpl; auto.
    destruct l2; simpl; autorewrite with posmap; intuition auto.
  Qed.
  Local Hint Resolve inMerge_app_r inMerge_app_l Forall_cons.

  Lemma inMerge_GT_app l2: forall l1 r2 r3, inMerge l1 r2 r3 ->
     (Forall (fun c => Forall (fun c' => E.lt (fst c) (fst c')) l1) l2)
     -> inMerge l1 (l2 ++ r2) (l2 ++ r3).
  Proof.
    induction l2; simpl; auto.
    destruct 1; simpl; autorewrite with posmap; intuition auto.
    apply inMerge_app_r. auto. 
  Qed.

  Lemma inMerge_LT_app l1: forall l2 r1 r3, inMerge r1 l2 r3 ->
     (Forall (fun c => Forall (fun c' => E.lt (fst c) (fst c')) l2) l1)
     -> inMerge (l1 ++ r1) l2 (l1 ++ r3).
  Proof.
    induction l1; simpl; auto.
    destruct 1; simpl; autorewrite with posmap; intuition auto.
    apply inMerge_app_l. auto.
  Qed.
  Local Hint Resolve inMerge_LT_app inMerge_GT_app.

  Lemma inMerge_app l1 l2 l3: inMerge l1 l2 l3 -> 
    forall r1 r2 r3, 
    (Forall (fun c => Forall (fun c' => E.lt (fst c) (fst c')) r2) l1)
    -> (Forall (fun c => Forall (fun c' => E.lt (fst c) (fst c')) r1) l2)
     -> inMerge r1 r2 r3
     -> inMerge (l1 ++ r1) (l2 ++ r2) (l3 ++ r3).
  Proof.
    induction 1; simpl; intuition auto.
    + intros; apply inM_LT; auto.
      apply IHinMerge; intuition auto.
    + intros; apply inM_GT; auto.
      apply IHinMerge; intuition auto.
  Qed.
  Local Hint Resolve inMerge_app.

  Lemma xelements_merge m1: forall m2 path, inMerge (xelements m1 path) (xelements m2 path) (xelements (merge m1 m2) path).
  Proof.
    induction m1 as [| m1_1 IHm1_1 o1 m1_2 IHm1_2 ]; simpl; auto.
    destruct m2 as [| m2_1 o2 m2_2 ]; simpl; auto.
    intro path; destruct o1 as [a1|]; destruct o2 as [a2|]; rewrite xelements_node; simpl.
    elimtype (exists o, f a1 a2=o); eauto.
    intros o H; rewrite H; destruct o as [a |]; auto.
    + apply inMerge_app; auto.
      apply inMerge_LT_app with (l1:=[(path, a1)]); auto.
      simpl; intuition auto.
    + apply inMerge_app; auto.
      apply inMerge_GT_app with (l2:=[(path, a2)]); auto.
      simpl; intuition auto.
    + apply inMerge_app; auto.
  Qed.

  Theorem elements_merge m1 m2: inMerge (elements m1) (elements m2) (elements (merge m1 m2)).
  Proof.
     apply xelements_merge.
  Qed.

End merge.
 

 

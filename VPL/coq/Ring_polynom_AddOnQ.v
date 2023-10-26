(** Adapter of Ring_polynom for VPL needs. 
  - We instantiate polynomials on Q
  - We introduce an alternative definition of evaluation closer to our needs.
*)

Require Coq.setoid_ring.Cring.
Require Export Coq.setoid_ring.Ring_polynom.
Require Export QArith.
Require Import Equivalence.
Require Import Lia.
Open Scope Q_scope.
Require Extraction.

(* * First: We declare Q as commutative ring of Cring.Cring ! *)

(* below: we could derive Zops and Zri from a generic mapping 
    ring_theory >-> Ncring.Ring.

*)

Instance Qops: (@Ncring.Ring_ops Q 0%Q 1%Q Qplus Qmult Qminus Qopp (Qeq)).
Defined.
Instance Qri : (Ncring.Ring (Ro:=Qops)).
constructor;try Morphisms.solve_proper.
- exact Q_Setoid.
- exact Qplus_0_l.
- exact Qplus_comm. 
- exact Qplus_assoc. 
- exact Qmult_1_l.
- exact Qmult_1_r.  
- exact Qmult_assoc.
- exact Qmult_plus_distr_l. 
- intros.
apply (Qmult_plus_distr_r z x y).
- exact Qplus_opp_r.
Defined.

Instance Qcri : (Cring.Cring (R:=Q)).
- exact Qmult_comm.
Defined.

Definition Qpower: Q -> N -> Q 
 := pow_N 1 Qmult.

(* * Second: We instantiate generic definitions on Q *)

(* type of polynomial expression on Q *)
Definition PExpr:=PExpr Q.

(* efficient type of polynomials (e.g. as a kind of list of monomials) *)
Definition Pol:=Pol Q.

(* evaluation of polynomial expressions *)
Definition PEeval (l:list Q) (p:PExpr): Q
 := PEeval 0 1 Qplus Qmult Qminus Qopp (fun x => x) (fun x => x) Qpower l p.

(* evaluation of efficient polynomials *)
Definition Pphi (l:list Q) (p:Pol): Q
 := Pphi 0 Qplus Qmult (fun x => x) l p.

(* normalisation *)
Definition norm (pe:PExpr): Pol := 
  norm_aux 0 1 Qplus Qmult Qminus Qopp Qeq_bool pe.

(* polynomial equality test *)
Definition Peq (p1 p2:Pol) : bool :=
  Peq Qeq_bool p1 p2.

Definition PExpr_eq (pe1 pe2: PExpr): bool :=
  Peq (norm pe1) (norm pe2).  

Extraction Inline PExpr_eq Peq norm.

(* The semantics (or evaluation) used in VPL for polynomial expressions *)
Fixpoint PEsem (pe: PExpr) (m: positive -> Q): Q :=
 match pe with
  | PEO => 0
  | PEI => 1
  | PEc c => c
  | PEX _ j => m j 
  | PEadd pe1 pe2 => Qplus (PEsem pe1 m) (PEsem pe2 m)
  | PEsub pe1 pe2 => Qminus (PEsem pe1 m) (PEsem pe2 m)
  | PEmul pe1 pe2 => Qmult (PEsem pe1 m) (PEsem pe2 m)
  | PEopp pe1 => Qopp (PEsem pe1 m)
  | PEpow pe1 n => Qpower (PEsem pe1 m) n
  end.

Require Import String.

Definition to_string (pe: PExpr) : string := "".

(* We relate PEsem and PEeval. We are in the semantics, 
   hence we do not need an "efficient" translation
*)

(*** BEGIN STUB
In Coq 8.4, this were in the standard library ?
But not in Coq 8.5 ??
*)

(* Taken from Ring_polynom_Addon *)
Fixpoint nat_iter {A} (n:nat) (f: A -> A) (x:A) :=
 match n with
 | O => x
 | S n => f (nat_iter n f x)
 end.

Lemma nat_iter_plus A (f: A -> A) x n m:
  nat_iter (n+m) f x = nat_iter n f (nat_iter m f x).
Proof.
  induction n; simpl; congruence.
Qed.

Lemma nat_iter_succ_r A (f: A -> A) x n:
  nat_iter (S n) f x = nat_iter n f (f x).
Proof.
  cutrewrite ((S n) = (n + 1)%nat).
  rewrite nat_iter_plus. auto.
  lia.
Qed.

(*** END STUB *)

(* First: some work on list operations *)

Require Import Coq.setoid_ring.BinList.

Lemma jump_iter_tl_aux {A} (n:nat): forall (l:list A), 
  jump (Pos.of_nat (S n)) l = nat_iter (S n) (@tl _) l.
Proof.
  simpl; induction n; simpl; auto.
  intros; rewrite <- IHn.
  rewrite jump_succ. simpl; auto.
Qed.

Lemma jump_iter_tl {A} (p:positive) (l: list A): 
  jump p l = nat_iter (Pos.to_nat p) (@tl _) l.
Proof.
  rewrite <- (Pos2Nat.id p) at 1.
  generalize (Pos2Nat.is_pos p).
  generalize (Pos.to_nat p).
  intros n; case n.
  - intros H; inversion H.
  - intros n0 H; clear H.
  apply jump_iter_tl_aux.
Qed.

Lemma nth_positive_nat_iter {A} (p:positive): forall (l:list A) d, 
  nth d p l = hd d (nat_iter (pred (Pos.to_nat p)) (@tl _) l).
Proof.
  induction p; auto. 
    - intros; simpl; rewrite IHp; simpl.
      rewrite jump_iter_tl.
      rewrite <- nat_iter_plus.
      rewrite <- nat_iter_succ_r.
      cutrewrite ((S (pred (Pos.to_nat p) + Pos.to_nat p))=(Pos.to_nat p~0)).
      simpl; auto.
      rewrite Pos2Nat.inj_xO.
      generalize (Pos2Nat.is_pos p).
      lia.
  - intros; simpl; rewrite IHp; simpl.
      rewrite jump_iter_tl.
      rewrite <- nat_iter_plus.
      cutrewrite (((pred (Pos.to_nat p)) + Pos.to_nat p)%nat=pred (Pos.to_nat p~0)).
      simpl; auto.
      rewrite Pos2Nat.inj_xO.
      generalize (Pos2Nat.is_pos p).
      lia.
Qed.

Lemma List_nth_hd_iter_tl {A} (n:nat): forall (l:list A) (d:A),
  List.nth n l d = hd d (nat_iter n (@tl _) l).
Proof.
  induction n.
    - destruct l; simpl; auto.
    - intros; rewrite nat_iter_succ_r.
      rewrite <- IHn.
      destruct l; simpl; auto. destruct n; simpl; auto.
Qed.

Lemma nth_positive_nat {A} (p:positive) (l:list A) d: 
  nth d p l = List.nth (pred (Pos.to_nat p)) l d.
Proof.
  intros; rewrite List_nth_hd_iter_tl, nth_positive_nat_iter.
  auto.
Qed.

Definition mkMemoryList {A} (bound: positive) (mem: positive -> A)
 := List.map (fun n => mem (Pos.of_nat n)) (List.seq (S O) (Pos.to_nat bound)).

Lemma nth_mkMemoryList {A} p bnd (mem: positive -> A) d:
  (p <= bnd)%positive -> nth d p (mkMemoryList bnd mem) = mem p.
Proof.
  unfold mkMemoryList.
  intros; assert (Y:(pred (Pos.to_nat p) < Pos.to_nat bnd)%nat).
    assert (X:forall (n m:nat), (0 < n)%nat -> (n <= m)%nat -> (pred n < m)%nat).
    intros; lia.
    apply X.
    apply Pos2Nat.is_pos.
    rewrite <- Pos2Nat.inj_le. auto.
  clear H; rewrite nth_positive_nat; erewrite nth_indep.
  - rewrite List.map_nth, seq_nth.
    apply f_equal.
    assert (X:forall (n:nat), (0 < n)%nat -> (1 + pred n)%nat = n).
    + intros; lia. 
    + rewrite X. apply Pos2Nat.id.
      apply Pos2Nat.is_pos.
    + auto.
  - intros; autorewrite with list; auto.
  Grab Existential Variables. apply O.
Qed.

Fixpoint bound (pe:PExpr): positive :=
  match pe with
  | PEX _ x => x
  | PEadd pe1 pe2 => Pos.max (bound pe1) (bound pe2)
  | PEsub pe1 pe2 => Pos.max (bound pe1) (bound pe2)
  | PEmul pe1 pe2 => Pos.max (bound pe1) (bound pe2)
  | PEopp pe => bound pe
  | PEpow pe _ => bound pe
  | _ => xH
  end.
Local Hint Resolve Pos.max_lub_l Pos.max_lub_r Pos.le_max_l Pos.le_max_r.

Theorem PEsem_Eval (pe: PExpr) (m: positive -> Q) bnd:
 ((bound pe) <= bnd)%positive -> PEsem pe m = PEeval (mkMemoryList bnd m) pe.
Proof.
  induction pe; simpl; auto; try (intros; rewrite IHpe || rewrite IHpe1, IHpe2; eauto).
  intros; rewrite nth_mkMemoryList; auto.
Qed.

Local Hint Resolve Qeq_bool_eq.

Theorem PEnorm_correct (pe: PExpr) (m: positive -> Q) bnd:
 ((bound pe) <= bnd)%positive -> 
   Qeq (PEsem pe m) (Pphi (mkMemoryList bnd m) (norm pe)). 
Proof.
  intros; erewrite PEsem_Eval; eauto.
  unfold PEeval, Pphi, norm; eapply norm_aux_spec.
  - apply Q_Setoid. 
  - eapply Cring.cring_eq_ext; eauto.
  - eapply Cring.cring_almost_ring_theory; eauto.
  - eapply mkmorph; eauto;reflexivity.
  - apply Cring.cring_power_theory; eauto.
Qed.

Theorem PExpr_eq_correct (pe1 pe2: PExpr) (m: positive -> Q):
  PExpr_eq pe1 pe2 = true -> Qeq (PEsem pe1 m) (PEsem pe2 m).
Proof.
  unfold PExpr_eq, Peq. intro H; rewrite! PEnorm_correct with (bnd:=Pos.max (bound pe1) (bound pe2)); auto.
  unfold Pphi. refine (Peq_ok Q_Setoid _ _ _ _ H _).
  - eapply Cring.cring_eq_ext.
  - eapply mkmorph.
     instantiate (1 := 0);auto.
     instantiate (1 := 1);eauto. instantiate(1 := 1);auto.
     instantiate (1 := Qplus).
     intros. exact (Qeq_refl (Qplus x y)).
     instantiate (1 := Qplus);instantiate (1 := Qplus).
     intros. exact (Qeq_refl (Qplus x y)).
     instantiate (1 := Qmult);
     intros. exact (Qeq_refl (Qmult x y)).
     instantiate (1 := Qopp).
     intros. exact (Qeq_refl (Qopp x)).
     eauto.
Qed.

Theorem PExpr_eq_dec (pe1 pe2: PExpr) : {PExpr_eq pe1 pe2 = true} + {PExpr_eq pe1 pe2 = false}.
Proof. intuition. Qed.

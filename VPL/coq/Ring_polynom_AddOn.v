(** Adapter of Ring_polynom for VPL needs. 
  - We instantiate polynomials on Z
  - We introduce an alternative definition of evaluation
    closer to our needs.
*)

Require Coq.setoid_ring.Cring.
Require Export Coq.setoid_ring.Ring_polynom.
Require Export ZArith.
Require Import Equivalence.
Require Import Lia.
Require Extraction.

Open Scope Z_scope.

(* * First: We declare Z as commutative ring of Cring.Cring ! *)

(* below: we could derive Zops and Zri from a generic mapping 
    ring_theory >-> Ncring.Ring.

*)
Notation Zopp := (Z.opp).
Instance Zops: (@Ncring.Ring_ops Z 0%Z 1%Z Zplus Zmult Zminus Zopp (@eq Z)).
Defined.
Instance Qri : (Ncring.Ring (Ro:=Zops)).
constructor; try Morphisms.solve_proper.
- exact eq_equivalence.
- exact Zplus_comm.
- exact Zplus_assoc. 
- exact Zmult_1_l.  
- exact Zmult_1_r. 
- exact Zmult_assoc.
- exact Zmult_plus_distr_l. 
- intros; apply Zmult_plus_distr_r. 
- exact Zplus_opp_r.
Defined.

Instance Zcri : (Cring.Cring (R:=Z)).
- exact Zmult_comm.
Defined.

Definition Zpower: Z -> N -> Z 
 := pow_N 1 Zmult.

(* * Second: We instantiate generic definitions on Z *)

(* type of polynomial expression on Z *)
Definition PExpr:=PExpr Z.

(* efficient type of polynomials (e.g. as a kind of list of monomials) *)
Definition Pol:=Pol Z.

(* evaluation of polynomial expressions *)
Definition PEeval (l:list Z) (p:PExpr): Z
 := PEeval 0 1 Zplus Zmult Zminus Zopp (fun x => x) (fun x => x) Zpower l p.

(* evaluation of efficient polynomials *)
Definition Pphi (l:list Z) (p:Pol): Z
 := Pphi 0 Zplus Zmult (fun x => x) l p.

(* normalisation *)
Definition norm (pe:PExpr): Pol := 
  norm_aux 0 1 Zplus Zmult Zminus Zopp Zeq_bool pe.

(* polynomial equality test *)
Definition Peq (p1 p2:Pol) : bool :=
  Peq Zeq_bool p1 p2.

Definition PExpr_eq (pe1 pe2: PExpr): bool :=
  Peq (norm pe1) (norm pe2).  

Extraction Inline PExpr_eq Peq norm.

(* The semantics (or evaluation) used in VPL for polynomial expressions *)
Fixpoint PEsem (pe: PExpr) (m: positive -> Z): Z :=
 match pe with
  | PEO => 0
  | PEI => 1
  | PEc c => c
  | PEX _ j => m j 
  | PEadd pe1 pe2 => Zplus (PEsem pe1 m) (PEsem pe2 m)
  | PEsub pe1 pe2 => Zminus (PEsem pe1 m) (PEsem pe2 m)
  | PEmul pe1 pe2 => Zmult (PEsem pe1 m) (PEsem pe2 m)
  | PEopp pe1 => Zopp (PEsem pe1 m)
  | PEpow pe1 n => Zpower (PEsem pe1 m) n
  end.


(* We relate PEsem and PEeval. We are in the semantics, 
   hence we do not need an "efficient" translation
*)

(* First: some work on list operations *)
Require Import Coq.setoid_ring.BinList.

(*** BEGIN STUB
In Coq 8.4, this were in the standard library ?
But not in Coq 8.5 ??
*)

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

Theorem PEsem_Eval (pe: PExpr) (m: positive -> Z) bnd:
 ((bound pe) <= bnd)%positive -> PEsem pe m = PEeval (mkMemoryList bnd m) pe.
Proof.
  induction pe; simpl; auto; try (intros; rewrite IHpe || rewrite IHpe1, IHpe2; eauto).
  intros; rewrite nth_mkMemoryList; auto.
Qed.

Local Hint Resolve Zeq_bool_eq.

Theorem PEnorm_correct (pe: PExpr) (m: positive -> Z) bnd:
 ((bound pe) <= bnd)%positive -> 
   PEsem pe m = Pphi (mkMemoryList bnd m) (norm pe). 
Proof.
  intros; erewrite PEsem_Eval; eauto.
  unfold PEeval, Pphi, norm; eapply norm_aux_spec.
  - apply Eqsth.
  - eapply Cring.cring_eq_ext; eauto.
  - eapply Cring.cring_almost_ring_theory; eauto.
  - eapply mkmorph; eauto.
  - apply Cring.cring_power_theory; eauto.
Qed.

Theorem PExpr_eq_correct (pe1 pe2: PExpr) (m: positive -> Z):
  PExpr_eq pe1 pe2 = true -> PEsem pe1 m = PEsem pe2 m.
Proof.
  unfold PExpr_eq, Peq. intro H; rewrite! PEnorm_correct with (bnd:=Pos.max (bound pe1) (bound pe2)); auto.
  unfold Pphi. refine (Peq_ok _ _ _ _ _ H _).
  - eapply Cring.cring_eq_ext; eauto.
  - eapply mkmorph; eauto.
  Grab Existential Variables. 
    apply Zplus.
    apply 0.
Qed.

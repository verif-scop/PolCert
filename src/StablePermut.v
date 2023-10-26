Require Import List.
Import List.ListNotations.
Require Import Permutation.
Require Import Lia.
Require Import LibTactics.
Require Import sflib.

Inductive StablePermut_step {A: Type}:
    (A -> A -> bool) -> (A -> A -> bool) -> (A -> A -> bool) -> list A -> list A -> Prop := 
| stable_permut_skip:
    forall ltb eqb stablefunc l1 l2 tau l1' l2', 
        l1 = tau :: l1' -> 
        l2 = tau :: l2' -> 
        StablePermut_step ltb eqb stablefunc l1' l2' -> 
        StablePermut_step ltb eqb stablefunc l1 l2
| stable_permut_swap: 
    forall ltb eqb stablefunc l1 l2 tau1 tau2 l', 
        l1 = tau1 :: (tau2 :: l') ->
        l2 = tau2 :: (tau1 :: l') ->
        ltb tau1 tau2 = false -> (** stable for sorted elements *)
        eqb tau1 tau2 = false -> (** stable for equal elements *) 
        stablefunc tau1 tau2 = true -> (** stable for custom function *)
        StablePermut_step ltb eqb stablefunc l1 l2
    .


Inductive StablePermut' {A: Type}: 
    (A -> A -> bool) -> (A -> A -> bool) -> (A -> A -> bool) -> list A -> list A -> nat -> Prop := 
| stable_permut_nil: 
    forall ltb eqb sfunc l,
    StablePermut' ltb eqb sfunc l l 0
| stable_permut_intro:
    forall ltb eqb sfunc l1 l2 l3 n, 
    StablePermut_step ltb eqb sfunc l1 l2 ->
    StablePermut' ltb eqb sfunc l2 l3 n -> 
    StablePermut' ltb eqb sfunc l1 l3 (n+1).

Definition StablePermut {A: Type} (ltb: A -> A -> bool) (eqb: A -> A -> bool) (sfunc: A -> A -> bool) (l1 l2: list A) : Prop := 
    exists n, StablePermut' ltb eqb sfunc l1 l2 n.

(** some facts about stable permute *)
(** 1. stable permute implies permutation *)

Lemma stable_permut'_trans: 
    forall A ltb eqb sfunc n1 n2 l1 l2 l3, 
        @StablePermut' A ltb eqb sfunc l1 l2 n1 -> 
        @StablePermut' A ltb eqb sfunc l2 l3 n2 ->
        @StablePermut' A ltb eqb sfunc l1 l3 (n1+n2).
Proof.
    induction n1.
    {
        intros; simpls.
        inv H; eauto; try lia.
    }
    {
        intros; simpls.
        inv H; eauto; try lia.
        assert (n = n1). {lia. }
        clear H1. subst.
        eapply IHn1 in H0; eauto.
        clear H8.
        eapply stable_permut_intro in H0; eauto. 
        replace (n1 + n2 + 1) with (S (n1 + n2)) in H0; try lia. 
        trivial. 
    }
Qed.

Lemma stable_permut_trans: 
    forall A ltb eqb sfunc l1 l2 l3, 
        @StablePermut A ltb eqb sfunc l1 l2 -> 
        @StablePermut A ltb eqb sfunc l2 l3 ->
        @StablePermut A ltb eqb sfunc l1 l3.
Proof. 
    intros.
    unfolds StablePermut.
    destruct H; destruct H0. eexists.
    eapply stable_permut'_trans; eauto.
Qed.

Lemma stable_permut'_hd_cons_preserve_step: 
    forall A ltb eqb sfunc n l1 l2 a,
        @StablePermut' A ltb eqb sfunc l1 l2 n -> 
        @StablePermut' A ltb eqb sfunc (a::l1) (a::l2) n.
Proof.
    induction n.
    {
        intros.
        simpls.
        inv H; econs; eauto; try lia.
    }
    {
        intros.
        inv H; simpls.
        assert (n0 = n). {try lia. }
        clear H0.
        subst.
        eapply IHn with (a:=a) in H7; eauto.
        eapply stable_permut_skip with (tau:=a) in H1; eauto.
        econs; eauto.
        Unshelve. eauto.
    }
Qed. 

Lemma stable_permut_hd_cons: 
    forall A ltb eqb sfunc l1 l2 a,
        @StablePermut A ltb eqb sfunc l1 l2 -> 
        @StablePermut A ltb eqb sfunc (a::l1) (a::l2).
Proof.
    intros.
    unfolds StablePermut.
    destruct H.
    eexists.
    eapply stable_permut'_hd_cons_preserve_step; eauto.
Qed. 

Lemma stable_permut_refl: 
    forall A ltb eqb sfunc l1, 
        @StablePermut A ltb eqb sfunc l1 l1.
Proof. 
    intros.
    unfold StablePermut.
    eexists; econs; eauto.
Qed.

Lemma stable_permut_step_implies_permutation: 
    forall A ltb eqb sfunc l1 l2,
        @StablePermut_step A ltb eqb sfunc l1 l2 -> 
        Permutation l1 l2.
Proof.
    induction l1.
    {
        intros.
        inv H; try discriminate.
    }
    {
        intros.
        inv H.
        {
            rewrite H0.   
            econs; eauto.
            inv H0.
            eapply IHl1 in H2.
            trivial.
        }
        {
            rewrite H0.
            econs; eauto.
        }
    }
Qed.

Lemma stable_permut'_implies_permutation: 
    forall A ltb eqb sfunc n l1 l2,
        @StablePermut' A ltb eqb sfunc l1 l2 n -> 
        Permutation l1 l2.
Proof. 
    induction n.
    {
        intros.
        inv H; eauto.
        lia.
    }
    {
        intros; simpls.
        inv H. 
        assert (n0 = n). {lia. }
        clear H0.
        subst; eauto.
        eapply IHn in H7.
        eapply stable_permut_step_implies_permutation in H1; eauto.
        econs; eauto.
    }
Qed.

Lemma stable_permut_implies_permutation: 
    forall A ltb eqb sfunc l1 l2,
        @StablePermut A ltb eqb sfunc l1 l2 -> 
        Permutation l1 l2.
Proof.
    intros.
    unfold StablePermut in H.
    destruct H.
    eapply stable_permut'_implies_permutation; eauto.
Qed.

Lemma stable_permut_perserves_elems: 
    forall A ltb eqb sfunc l1 l2 tau,
        @StablePermut A ltb eqb sfunc l1 l2 -> 
        (In tau l1 <-> In tau l2).
Proof.
    intros.
    eapply stable_permut_implies_permutation in H.
    split; intro.
    eapply Permutation_in in H0; eauto.
    eapply Permutation_in in H0; eauto.
    eapply Permutation_sym; eauto.
Qed.

Lemma stable_permut_step_implies_stable_permut: 
    forall A ltb eqb sfunc l1 l2,
        @StablePermut_step A ltb eqb sfunc l1 l2 -> 
        @StablePermut A ltb eqb sfunc l1 l2.
Proof.
    intros.
    econs; eauto.
    econs; eauto.
    econs; eauto.
Qed.
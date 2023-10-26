Require Import Permutation.
Require Import Sorting.Sorted.
Require Import List.
Import ListNotations.
Require Import Arith.
Require Import sflib.
Require Import LibTactics.
Require Import Base.
Require Import StablePermut.
Require Import Lia.
Require Import Bool.
Require Import Classical.

(** Note: This implementation of SelectionSort is stable. *)
(** Modified from *Verfied Functional Algorithm*'s selection sort implementation*)

(** x is nth element of list l *)
Fixpoint select_helper {A: Type} (ltb: A -> A -> bool) (eqb: A -> A -> bool) (l: list A) (x: A) (n: nat) (r: list A): A * list A := 
    match r with 
    | [] =>  (x, remove_nth n l)
    | x'::r' => 
        if orb (ltb x x') (eqb x x') 
        then select_helper ltb eqb (l++[x']) x n r' 
        else select_helper ltb eqb (l++[x']) x' (length l) r' 
    end.

Definition select {A: Type} (ltb: A -> A -> bool) (eqb: A -> A -> bool) (x: A) (l: list A) : A * list A :=
    select_helper ltb eqb [x] x 0 l.

(* Compute (select Nat.ltb 1 [3;0;4]). *)

(** n is the fuel for structurally decreasing restriction *)
Fixpoint selsort {A: Type} (ltb: A -> A -> bool) (eqb: A -> A -> bool) (l : list A) (n : nat) : list A :=
    match l, n with
    | _, O => [] (* ran out of fuel *)
    | [], _ => []
    | x :: r, S n' => let (y, r') := select ltb eqb x r
                    in y :: selsort ltb eqb r' n'
  end.

Definition SelectionSort {A: Type} (ltb: A -> A -> bool) (eqb: A -> A -> bool) (l: list A): list A := 
    selsort ltb eqb l (length l).

Example sort_pi: 
    SelectionSort Nat.ltb Nat.eqb [3;1;4;1;5;9;2;6;5;3;5] = [1;1;2;3;3;4;5;5;5;6;9].
Proof.
  unfold SelectionSort.
  simpl. reflexivity.
Qed.

(** permutation & sorted & stable permutation *)
(** 1. Let's prove SelectionSort implies Permutation first *)
Lemma select_helper_perm: 
    forall A ltb eqb r l x n y l', 
        n < length l ->
        nth n l x = x ->
        select_helper ltb eqb l x n r = (y, l') -> 
        @Permutation A (l ++ r) (y :: l').
Proof.
    induction r. 
    {
        intros until l'. intros LENGTH Hnth Hselect.
        unfold select_helper in Hselect.
        
        inv Hselect; eauto.
        replace (l ++ []) with l. 
            2: { rewrite app_nil_r; trivial. }
        eapply remove_nth_cons_nth_permut; eauto.
    }
    {
        intros until l'. intros LENGTH Hnth Hselect.
        unfold select_helper in Hselect.
        folds (@select_helper A).
        des_ifH Hselect.
        {
            eapply IHr in Hselect; eauto.
            replace (l ++ a :: r) with ((l ++ [a]) ++ r).
            2: {
                rewrite <- app_assoc.
                simpls; eauto.
            }
            eauto.
            rewrite app_length. lia.
            rewrite app_nth1; eauto.
        }
        {
            eapply IHr in Hselect; eauto.
            replace (l ++ a :: r) with ((l ++ [a]) ++ r).
            2: {
                rewrite <- app_assoc.
                simpls; eauto.
            }
            eauto.
            rewrite app_length. 
            unfold length.
            lia.
            rewrite app_nth2; eauto. 
            replace (length l - length l) with 0; try lia.
            simpl; trivial.    
        }
    }
Qed.

Lemma select_perm: 
    forall A ltb eqb l x y r,
        select ltb eqb x l = (y, r) -> 
        @Permutation A (x :: l) (y :: r).
Proof.
    intros.
    unfold select in H.
    eapply select_helper_perm in H; eauto.
Qed.

Lemma select_helper_length: 
    forall A ltb eqb r l x n y l', 
        n < length l ->
        @nth A n l x = x ->
        select_helper ltb eqb l x n r = (y, l') -> 
        length (l++r) = length (y::l').
Proof.
    induction r.
    {
        intros.
        unfold select_helper in H1.
        inv H1.
        rewrite app_nil_r.
        replace (y::remove_nth n l) with ([y]++remove_nth n l).
        2: {
            simpl; eauto.
        }
        rewrite app_length.
        eapply remove_nth_length in H0; eauto.
        rewrite <- H0.
        simpl. lia.
    }
    {
        intros.
        unfold select_helper in H1.
        folds (@select_helper A).
        des_ifH H1.
        {
            eapply IHr in H1; eauto.
            replace (l ++ a :: r) with ((l ++ [a]) ++ r).
            2: {
                rewrite <- app_assoc.
                simpls; eauto.
            }
            eauto.
            rewrite app_length. lia.
            rewrite app_nth1; eauto.
        }
        {
            eapply IHr in H1; eauto.
            replace (l ++ a :: r) with ((l ++ [a]) ++ r).
            2: {
                rewrite <- app_assoc.
                simpls; eauto.
            }
            eauto.
            rewrite app_length. 
            unfold length.
            lia.
            rewrite app_nth2; eauto. 
            replace (length l - length l) with 0; try lia.
            simpl; trivial.    
        }
    }
Qed.

Lemma select_rest_length:
    forall A ltb eqb l x y r,
        @select A ltb eqb x l = (y, r) ->
        length l = length r.
Proof.
    intros.
    unfolds select.
    eapply select_helper_length in H; eauto.
Qed.

Lemma selsort_perm: 
    forall A ltb eqb n l, 
        length l = n -> 
        @Permutation A l (selsort ltb eqb l n).
Proof.
    induction n as [|n IH].
    {
        intros. eapply length_zero_iff_nil in H. subst.
        unfold selsort. 
        eauto.
    }
    {
        intros.
        remember (selsort ltb eqb l (S n)) as l'.
        unfold selsort in Heql'.
        folds (@selsort A).
        destruct l eqn:Hl; try discriminate.
        destruct (select ltb eqb a l0) eqn:Hselect; eauto.
        assert (length l0 = n). {
            unfolds length; eauto. 
        }
        eapply select_perm in Hselect.
        eapply IH in H0. subst.
        assert (Permutation l1 (selsort ltb eqb l1 n)). {
            eapply IH.
            eapply Permutation_length in Hselect.
            rewrite H in Hselect.
            symmetry in Hselect.
            unfolds length; eauto.
        }
        eapply Permutation_trans in Hselect; eauto.
        eapply (perm_skip a0) in H1.
        eapply Permutation_trans; eauto.
    }
Qed.

Lemma selection_sort_perm: 
    forall A ltb eqb l, 
        @Permutation A l (SelectionSort ltb eqb l).
Proof.
    intros.
    unfolds SelectionSort. 
    eapply selsort_perm; eauto.
Qed.


Lemma select_helper_fst_leq: 
    forall A ltb eqb r l x n y l', 
        transitive ltb ->
        reflexive eqb -> 
        @total A ltb eqb ->
        eqb_ltb_implies_ltb ltb eqb -> 
        n < length l ->
        @nth A n l x = x ->
        select_helper ltb eqb l x n r = (y, l') -> 
        ltb y x = true \/ eqb y x = true.
Proof.
    induction r. 
    {
        intros until l'; intros TRANS REFLEX TOTAL LTEQL; intros. 
        unfold select_helper in H1. inv H1. right; eauto.
    }
    {
        intros until l'; intros TRANS REFLEX TOTAL LTEQL; intros. 
        unfold select_helper in H1. folds (@select_helper A).
        destruct (orb (ltb x a) (eqb x a)) eqn:Hordxa.
        {
            eapply IHr in H1; eauto.
            rewrite app_length; lia.
            rewrite app_nth1; eauto. 
        }
        {
            eapply IHr in H1; eauto.
            {
                destruct H1.
                {
                    unfold total in TOTAL.
                    pose proof (TOTAL x a).
                    assert (ltb a x = true). {
                        eapply orb_false_elim in Hordxa.
                        destruct Hordxa.
                        rewrite H3 in H2; rewrite H4 in H2.
                        firstorder.
                    } 
                    clear H2 Hordxa.
                    left.
                    unfold transitive in TRANS.
                    assert (ltb y x = true). {
                        eapply TRANS; eauto.
                    }
                    eauto.                
                }
                {
                    unfold total in TOTAL.
                    pose proof (TOTAL x a).
                    assert (ltb a x = true). {
                        eapply orb_false_elim in Hordxa.
                        destruct Hordxa.
                        rewrite H3 in H2; rewrite H4 in H2.
                        firstorder.
                    }
                    left. 
                    unfold transitive in TRANS.
                    assert (ltb y x = true). {
                        unfold ltb_eqb_implies_ltb in LTEQL.
                        eapply LTEQL; eauto.
                    }
                    subst; eauto. 
                }
            }
            {
                rewrite app_length. simpl. lia.
            }
            {
                rewrite app_nth2. 
                replace (length l - length l) with 0; try lia.
                simpl; eauto.
                lia.
            }   
        }
    }
Qed. 

Lemma select_fst_leq: 
    forall A ltb eqb al x y bl,
        transitive ltb ->
        reflexive eqb -> 
        symmetric eqb -> 
        @total A ltb eqb ->
        eqb_ltb_implies_ltb ltb eqb ->
        @select A ltb eqb x al = (y, bl) -> 
        ltb y x = true \/ eqb x y = true.
Proof.
    intros.
    unfold select in H4.
    eapply select_helper_fst_leq in H4; eauto. 
    unfold symmetric in H1. 
    destruct H4. tauto. 
    rewrite H1 in H4.
    right; eauto.
Qed.

Definition ord_all {A: Type} (ltb: A -> A -> bool) (x: A) (xs: list A) := Forall (fun y => if ltb x y then True else False) xs.

Lemma ord_all_ord_one: 
    forall A ltb x y xs,
        @ord_all A ltb x xs -> 
        In y xs -> 
        ltb x y = true.
Proof.
    intros.
    unfolds ord_all.
    eapply Forall_forall in H; eauto.
    destruct (ltb x y); eauto. 
Qed. 


Lemma ord_all_trans: 
    forall A ltb x xs a,
        transitive ltb ->
        @ord_all A ltb x xs -> 
        ltb a x = true -> 
        ord_all ltb a xs.
Proof.
    intros.
    unfold ord_all.
    unfold transitive in H.
    eapply Forall_forall; eauto. 
    intros.
    eapply ord_all_ord_one in H0; eauto.
    assert (ltb a x0 = true).
    {
        eapply H; eauto.
    }
    rewrite H3; eauto. 
Qed.

Lemma ord_all_but_nth_and_nth: 
    forall A ltb x n l a, 
        n < length l ->
        @ord_all A ltb x (remove_nth n l) -> 
        nth n l a = a -> 
        ltb x a -> 
        ord_all ltb x l.
Proof.
    intros.
    remember (remove_nth n l) as l'.
    symmetry in Heql'.
    eapply remove_nth_implies_splits with (x:=a) in Heql'; eauto.
    destruct Heql' as (Hl & Hl').
    unfold ord_all in H0.
    rewrite Hl' in H0.
    eapply Forall_app in H0; eauto.
    destruct H0 as (Hfirst & Hskip).
    rewrite Hl.
    eapply Forall_app; eauto.
    splits; eauto.
    simpl.
    eapply Forall_cons; eauto. 
    rewrite H2; eauto. 
Qed.

Lemma ord_all_remove_nth_ord_all: 
    forall A ltb x n l, 
        n < length l -> (** this is redundant*)
        @ord_all A ltb x l -> 
        ord_all ltb x (remove_nth n l).
Proof.
    intros.
    unfolds ord_all.
    remember (remove_nth n l) as l'.
    symmetry in Heql'.
    remember (nth n l x) as x'.
    symmetry in Heqx'.
    (* remember (nth n l ) *)
    eapply remove_nth_implies_splits in Heql'; eauto.
    destruct Heql' as (Hl & Hl').
    rewrite Hl'.
    rewrite Hl in H0.
    remember (firstn n l) as lf.
    remember (skipn (n+1) l) as ls. 
    eapply Forall_app in H0. 
    destruct H0.
    eapply Forall_app in H1.
    destruct H1.
    eapply Forall_app; splits; firstorder.
Qed.

Lemma select_helper_smallest: 
    forall A ltb eqb r l n x y l', 
        transitive ltb ->
        transitive eqb ->
        reflexive eqb -> 
        symmetric eqb -> 
        @total A ltb eqb ->
        eqb_ltb_implies_ltb ltb eqb -> 
        ltb_eqb_implies_ltb ltb eqb ->
        n < length l ->
        ord_all (combine_leb ltb eqb) x (remove_nth n l) -> 
        nth n l x = x ->
        select_helper ltb eqb l x n r = (y, l') -> 
        ord_all (combine_leb ltb eqb) y l'.
Proof.
    induction r.
    {
        intros until l'; intros TRANS TRANS_EQ REFLEX SYMM TOTAL TRANSL TRANSR; intros.
        unfold select_helper in H2. 
        inversion H2.
        subst; eauto.
    }
    {
        intros until l'; intros TRANS TRANS_EQ REFLEX SYMM TOTAL TRANSL TRANSR; intros.
        unfold select_helper in H2. folds (@select_helper A).
        destruct ((ltb x a)||(eqb x a)) eqn:Hord; eauto.
        {
            {
                pose proof (IHr (l++[a]) n x y l' TRANS TRANS_EQ REFLEX SYMM TOTAL TRANSL TRANSR).
                eapply H3; eauto.
                rewrite app_length; lia.
                {
                    remember (remove_nth n l) as ll.
                    symmetry in Heqll. 
                    pose proof (remove_nth_app A n l ll [a]).
                    rewrite H4; eauto. subst; eauto.
                    unfold ord_all. 
                    eapply Forall_app. 
                    splits.
                    {       
                        unfolds ord_all; eauto. 
                    }
                    {
                        eapply Forall_cons; eauto.
                        unfold combine_leb.
                        rewrite Hord; simpl; eauto.
                    }
                }
                rewrite app_nth1; eauto.   
            }
        }
        {
            {
                simpl in H2; eauto.

                pose proof (IHr (l++[a]) (length l) a y l' TRANS TRANS_EQ REFLEX SYMM TOTAL TRANSL TRANSR).
                eapply H3; eauto.
                rewrite app_length; simpl; lia.
                {
                    (** transitivity *)
                    pose proof (TOTAL x a).
                    assert (ltb a x = true \/ eqb x a = true). {
                        clear - Hord H4.
                        eapply orb_false_iff in Hord.
                        destruct Hord.
                        rewrite H in H4; rewrite H0 in H4. 
                        firstorder.
                    }
                    clear H4 Hord.
                    rewrite remove_nth_length_append_one.
                    destruct H5.
                    {
                        (** transitivity *)
                        assert ((combine_leb ltb eqb) a x = true). {
                            unfold combine_leb.
                            rewrite H4. simpl; eauto.
                        }
                        eapply ord_all_trans with (a:=a) in H0; eauto.
                        eapply ord_all_but_nth_and_nth; eauto.
                        eapply transitive_combine_implies_transitive; eauto.
                    }
                    {
                        subst; eauto.
                        assert ((combine_leb ltb eqb) x a = true). {
                            unfold combine_leb.
                            eapply orb_true_iff.
                            right; eauto.
                        }
                        eapply ord_all_but_nth_and_nth in H0; eauto.
                        {
                            clear - H0 H4 H5 TRANS TRANS_EQ TRANSL TRANSR SYMM.
                            unfold ord_all.
                            eapply Forall_forall; intros.
                            unfold ord_all in H0.
                            eapply Forall_forall with (x:=x0) in H0; eauto.
                            destruct (combine_leb ltb eqb x x0) eqn:Hle.
                            {
                                assert (combine_leb ltb eqb a x0 = true).
                                {
                                    unfolds combine_leb.
                                    (* clear - Hle H4. *)
                                    eapply orb_true_iff in Hle.
                                    eapply orb_true_iff.
                                    destruct Hle.
                                    {
                                        left.
                                        unfold eqb_ltb_implies_ltb in TRANSL.
                                        unfold symmetric in SYMM.
                                        rewrite SYMM in H4.
                                        eapply TRANSL; eauto.
                                    }
                                    {
                                        right.
                                        unfold symmetric in SYMM.
                                        rewrite SYMM in H4.
                                        unfold transitive in TRANS_EQ.
                                        eapply TRANS_EQ; eauto.
                                    }    
                                }
                                rewrite H1; eauto.
                            }
                            {
                                contradiction.
                            }
                        }
                        {
                            clear - REFLEX.
                            unfold combine_leb.
                            eapply orb_true_iff.
                            right.
                            unfolds reflexive; eapply REFLEX.
                        }
                    }
                }
                rewrite app_nth2; eauto.
                replace (length l - length l) with 0; simpl; try lia; trivial.
            }        
        }
    }
Qed.

Lemma select_smallest: 
    forall A ltb eqb al x y bl, 
        transitive ltb ->
        transitive eqb ->
        reflexive eqb -> 
        symmetric eqb -> 
        @total A ltb eqb ->
        eqb_ltb_implies_ltb ltb eqb -> 
        ltb_eqb_implies_ltb ltb eqb ->
        @select A ltb eqb x al = (y, bl) -> 
        ord_all (combine_leb ltb eqb) y bl.
Proof. 
    intros.
    unfold select in H6.
    eapply select_helper_smallest in H6; eauto.
    {
        unfold ord_all; simpls; eauto. 
    }
Qed.

Lemma select_helper_in: 
    forall A ltb eqb r l x n y l', 
        n < length l ->
        @nth A n l x = x ->
        select_helper ltb eqb l x n r = (y, l') -> 
        In y (l++r).
Proof.
    induction r.
    {
        intros.
        simpls; eauto.
        inv H1.
        rewrite app_nil_r.
        pose proof (@nth_In A n l y).
        eapply H1 in H; eauto.
        rewrite H0 in H; eauto.
    }
    {
        intros.
        simpls; eauto.
        des_ifH H1.
        {
            eapply IHr in H1; simpls; eauto.
            assert ((l++[a])++r = l++a::r). 
            {
                rewrite <- app_assoc.   
                simpl; eauto.
            }
            rewrite <- H2; eauto.
            rewrite app_length; try lia.
            rewrite app_nth1; eauto.
        }
        {
            eapply IHr in H1; simpls; eauto.
            assert ((l++[a])++r = l++a::r). 
            {
                rewrite <- app_assoc.   
                simpl; eauto.
            }
            rewrite <- H2; eauto.
            rewrite app_length; simpls; try lia. 
            rewrite app_nth2; eauto.
            replace (length l - length l) with 0; try lia. 
            simpls; eauto.
        }
    }
Qed.

Lemma select_in: 
    forall A ltb eqb al x y bl,
        @select A ltb eqb x al = (y, bl) -> 
        In y (x :: al).
Proof.
    intros.
    unfolds select.    
    eapply select_helper_in in H; eauto.
Qed.

Lemma cons_of_small_maintains_sort: 
    forall A ltb eqb x bl n, 
    n = length bl -> 
    @ord_all A (combine_leb ltb eqb) x bl -> 
    Sorted_b (combine_leb ltb eqb) (selsort ltb eqb bl n) -> 
    Sorted_b (combine_leb ltb eqb) (x :: selsort ltb eqb bl n).
Proof.
    intros.
    unfolds Sorted_b.
    eapply Sorted_cons; eauto.
    destruct (selsort ltb eqb bl n) eqn:Hselsort; eauto.

    eapply ord_all_ord_one in H0; eauto.
    unfolds selsort.
    destruct n eqn:Hn; eauto.
    {
        symmetry in H.
        eapply length_zero_iff_nil in H.
        rewrite H in Hselsort. 
        discriminate.
    }
    {
        destruct bl eqn:Hbl; simpls; try discriminate.
        destruct (select ltb eqb a0 l0) as (y, r') eqn:Hselect.
        folds (@selsort A).
        eapply select_in in Hselect.
        inv Hselsort.
        eauto.
    }
Qed.

Lemma selsort_sorted: 
    forall A ltb eqb n al,
    transitive ltb ->
    transitive eqb ->
    reflexive eqb -> 
    symmetric eqb -> 
    @total A ltb eqb ->
    eqb_ltb_implies_ltb ltb eqb -> 
    ltb_eqb_implies_ltb ltb eqb ->
    n = length al -> 
    Sorted_b (combine_leb ltb eqb) (@selsort A ltb eqb al n).
Proof. 
    intros until ltb.
    induction n.
    { (** n = 0*)
        intro; intros TRANS_LT TRANS_EQ REFLEX_EQ SYMM_EQ TOTAL TRANSL TRANSR; intros.
        symmetry in H.
        rewrite length_zero_iff_nil in H.
        subst.
        unfolds selsort. 
        unfolds Sorted_b.
        eapply Sorted_nil; eauto.
    }
    { (** n = S O *)
        intro; intros TRANS_LT TRANS_EQ REFLEX_EQ SYMM_EQ TOTAL TRANSL TRANSR; intros.
        remember (selsort ltb eqb al (S n)) as bl.
        assert (al <> []). {
            intro.
            symmetry in H.
            eapply length_zero_iff_nil in H0.
            rewrite H in H0.
            discriminate.
        }
        assert (exists hd tl, al = hd :: tl). 
        {
            destruct al; eauto; try discriminate.
        }
        destruct H1 as (hd & tl & Hal); eauto.
        unfold selsort in Heqbl.
        rewrite Hal in Heqbl. folds (@selsort A). 
        destruct (select ltb eqb hd tl) as (y, r') eqn:Hal'.
        remember (selsort ltb eqb r' n) as bl'.
        assert (n = length r'). {
            pose proof Hal'.
            eapply select_rest_length in Hal'.
            rewrite <- Hal'.
            rewrite Hal in H. unfold length in H. inversion H. subst; eauto.
        }
        pose proof (IHn r' TRANS_LT TRANS_EQ REFLEX_EQ SYMM_EQ TOTAL TRANSL TRANSR H1).
        rewrite <- Heqbl' in H2.
        eapply select_smallest in Hal'; eauto.
        eapply cons_of_small_maintains_sort in Hal'; eauto. 
        subst; eauto.
    }
Qed.

Lemma selection_sort_sorted: 
    forall A ltb eqb al, 
    transitive ltb ->
    transitive eqb ->
    reflexive eqb -> 
    symmetric eqb -> 
    @total A ltb eqb ->
    eqb_ltb_implies_ltb ltb eqb -> 
    ltb_eqb_implies_ltb ltb eqb ->
    Sorted_b (combine_leb ltb eqb) (@SelectionSort A ltb eqb al).
Proof. 
    intros until al; intros TRANS_LT TRANS_EQ REFLEX_EQ SYMM_EQ TOTAL TRANSL TRANSR.
    remember (SelectionSort ltb eqb al) as bl.
    unfolds SelectionSort.
    pose proof (selsort_sorted A ltb eqb (length al) al).
    rewrite <- Heqbl in H.
    eauto.
Qed.

Theorem selection_sort_is_correct: 
    forall A ltb eqb al bl, 
    transitive ltb ->
    transitive eqb ->
    reflexive eqb -> 
    symmetric eqb -> 
    @total A ltb eqb ->
    eqb_ltb_implies_ltb ltb eqb -> 
    ltb_eqb_implies_ltb ltb eqb ->
    @SelectionSort A ltb eqb al = bl -> 
    (
        Permutation al bl /\
        Sorted_b (combine_leb ltb eqb) bl
    ).
Proof.
    intros until bl; intros TRANS_LT TRANS_EQ REFLEX_EQ SYMM_EQ TOTAL TRANSL TRANSR; intros. splits.
    pose proof (selection_sort_perm A ltb eqb al).
    subst; eauto.
    pose proof (selection_sort_sorted A ltb eqb al).
    subst; eauto.
Qed.

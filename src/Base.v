Require Import List. 
Import List.ListNotations.
Require Import AST.
Require Import BinPos.
Require Import Arith.
Require Import Sorting.Sorted.
Require Import sflib.
Require Import LibTactics.
Require Import Lia.
Require Import Bool.
Require Import Classical.
Require Import Permutation.
Require Import Misc. 
Require Import SetoidList.
Scheme Equality for list.

Require Import MSets.
Require Import Coq.MSets.MSetProperties.
Require Import AST.
Require Import Ctypes.


(** Below used in validator's proof *)
Fixpoint mapi' {A B: Type} (f: nat -> A -> B) (li: list nat) (l: list A) := 
    match li, l with 
    | i::li', e::l' => f i e :: mapi' f li' l'
    | [], [] => []
    | _, _ => []
    end.

Definition mapi {A B: Type} (f: nat -> A -> B) (l: list A) := 
  let index_list := rev (n_range (length l)) in
  mapi' f index_list l.

Definition mapi_ascend {A B: Type} (f: nat -> A -> B) (l: list A) := 
  rev (mapi f (rev l)).

Example example_mapi_ascend:
    mapi_ascend (fun i n => (i, n)) [1;2;3] = [(0, 1); (1, 2); (2, 3)].
Proof. reflexivity. Qed.  

Lemma mapi_nil:
  forall A B f,
    @mapi A B f [] = [].
Proof.
  intros; simpls.
  unfold mapi. simpls. trivial.
Qed.

Lemma mapi_asc_nil:
  forall A B f,
    @mapi_ascend A B f [] = [].
Proof.
  intros; simpls.
  unfold mapi_ascend. simpls. trivial.
Qed.

Lemma mapi_cons:
  forall A B l f a, 
    @mapi A B f (a::l) = f (length l) a :: @mapi A B f l.
Proof.
  induction l.
  {
    intros.
    rewrite mapi_nil. simpls.
    unfold mapi. simpls. trivial.
  }
  {
    intros.
    rewrite IHl.
    simpls.
    remember (mapi f (a0 :: a :: l)) as Hm.
    unfold mapi in HeqHm. simpls.
    do 2 rewrite rev_app_distr in HeqHm.
    simpls.
    intros; unfold mapi; simpls.
    rewrite HeqHm. trivial.
  }
Qed.

Lemma mapi_asc_app_singleton: 
  forall A B l f a, 
    @mapi_ascend A B f (l++[a]) = (@mapi_ascend A B f l) ++ [f (length l) a].
Proof.
  intros. simpl.
  unfold mapi_ascend. simpls.
  rewrite rev_app_distr. simpls.
  rewrite mapi_cons; simpls.
  replace (length (rev l ++ [a])) with (S (length l)). 
  2: {simpls. rewrite app_length. simpls. rewrite rev_length. ring. }
  rewrite rev_length.
  trivial.
Qed.

Lemma in_mapi_iff : 
  forall A B l f y, 
    In y (@mapi A B f l) <-> exists x n, f (length l-n-1) x = y /\ nth_error l n = Some x.
Proof.
  induction l.
  {
    intros; simpls.
    split; intro; tryfalse.
    destruct H as (x & n & E & N).
    destruct n; tryfalse.
  }
  { 
    intros. 
    split; intro.
    {
      unfold mapi in H. simpl in H. 
      rewrite rev_app_distr in H. simpl in H.
      destruct H.
      {
        exists a 0; simpls.  
        splits; eauto.
        replace (length l - 0) with (length l); try lia. trivial.
      }
      {
        eapply IHl in H.
        destruct H as (x & n & Ele & Nth).
        exists x (n+1); simpls.
        splits; eauto. 
        {
          destruct n; simpls; tryfalse; trivial.
          replace (length l - (n+1) - 1) with (length l - S n - 1); try lia.
          trivial.
        }
        {
          replace (n+1) with (S n); try lia. simpls. trivial.
        }
      }
    }
    {
      simpls.
      destruct H as (x & n & Ele & Nth).
      destruct n eqn:Hn; simpls.
      {
        inv Nth.
        replace (length l - 0) with (length l); try lia.
        rewrite mapi_cons.
        eapply in_eq.
      }
      {
        rewrite mapi_cons.
        eapply in_cons.
        eapply IHl.
        exists x n0. splits; trivial.
      }
    }
  }
Qed.

Lemma nth_error_rev_some:
  forall A n l (x: A),
    nth_error l n = Some x ->
    nth_error (rev l) (length l - n - 1) = Some x.
Proof.
  induction n.
  {
    intros; simpls. destruct l eqn:Hl; tryfalse. simpls. 
    rewrite nth_error_app2.
    {
      replace (length l - 0 - 1) with (length l - 1); try lia.
      rewrite rev_length; trivial.
      replace (length l0 - 0 - length l0) with 0; try lia. simpls; trivial.
    }
    {
      rewrite rev_length; lia.
    }
  }
  {
    intros.
    simpl in H.
    destruct l eqn:Hl; tryfalse.
    simpl.
    rewrite nth_error_app1.
    {
      eapply IHn; eauto.
    }
    {
      eapply nth_error_Some.
      eapply IHn in H; eauto.
      rewrite H; discriminate.
    }
  }
Qed.

Lemma in_mapi_asc_iff: 
  forall A B l f y, 
    In y (@mapi_ascend A B f l) <-> exists x n, f n x = y /\ nth_error l n = Some x.
Proof.
  intros.
  unfold mapi_ascend.
  rewrite <- in_rev.
  rewrite in_mapi_iff.
  split; intro.
  {
    destruct H as (x & n & E & N).
    exists x (length l - n - 1).
    - rewrite rev_length in E. 
      splits; try ring; eauto.
      eapply nth_error_rev_some in N.
      rewrite rev_involutive in N. rewrite rev_length in N. trivial.
  }
  {
    destruct H as (x & n & E & N).
    exists x (length l - n - 1).
    rewrite rev_length. split.
    - 
      assert (n < length l). {
        eapply nth_error_Some. rewrite N; discriminate.
      }
      clear - H E. 
      replace (length l - (length l - n - 1) - 1) with n; try lia; trivial.
    - eapply nth_error_rev_some in N; trivial.
  }
Qed.

Fixpoint unwrap_option {A: Type} (olst: list (option A)): option (list A) := 
    match olst with 
    | [] => Some []
    | None::olst' => None
    | (Some elem)::olst' =>
      match unwrap_option olst' with 
      | Some lst => Some (elem::lst) 
      | None => None
      end 
    end.

Lemma unwrap_option_app_singleton:
  forall A (l1: list (option A)) a1,
    unwrap_option (l1 ++ [a1]) = 
      match a1 with
      | Some a1' => match unwrap_option l1 with
                    | Some l1' => Some (l1' ++ [a1'])
                    | None => None
                    end
      | None => None
      end.
Proof.
  induction l1.
  {
    intros; simpls.
    destruct a1; simpls; trivial.
  }
  {
    intros; simpls.
    destruct a eqn:Ha; simpls.
    rewrite IHl1.
    destruct a1 eqn:Ha1; simpls; eauto.    
    destruct (unwrap_option l1) eqn:Hl1; eauto.
    destruct a1; trivial.
  }
Qed.

  
Lemma unwrap_option_nil: 
  forall A,
    @unwrap_option A [] = Some [].
Proof.
  reflexivity.
Qed.

Lemma unwrap_option_forall: 
  forall A olst lst,
    @unwrap_option A olst = Some lst ->
    Forall (fun x => exists y, x = Some y) olst.
Proof.
  induction olst.
  {
    intros; simpls. 
    inv H. eapply Forall_nil.
  }
  {
    intros; simpls.
    destruct a eqn:Ha; tryfalse.
    destruct (unwrap_option olst) eqn:Holst; tryfalse.
    inversion H.
    pose proof (IHolst l). 
    eapply Forall_cons; eauto.
  }
Qed.

Lemma unwrap_option_exists: 
  forall A olst ,
    @unwrap_option A olst = None ->
    Exists (fun x => x = None) olst.
Proof.
  induction olst.
  {
    intros; simpls. 
    inv H. 
  }
  {
    intros; simpls.
    destruct a eqn:Ha; tryfalse.
    {
      destruct (unwrap_option olst) eqn:Holst; tryfalse.
      eapply Exists_cons; eauto.
    }
    {
      eapply Exists_cons; eauto.
    }
  }
Qed.


Fixpoint rel_list {A B: Type} (R: A -> B -> Prop) (l1: list A) (l2: list B): Prop := 
  match l1, l2 with 
  | a::l1', b::l2' => R a b /\ rel_list R l1' l2' 
  | [], [] => True 
  | _, _ => False
  end.

Lemma rel_list_app: 
  forall A B (R: A -> B -> Prop) l1 l2 l3 l4,
    rel_list R l1 l2 ->
    rel_list R l3 l4 ->
    rel_list R (l1 ++ l3) (l2 ++ l4).
Proof.
  induction l1.
  {
    intros; simpls.
    destruct l2; tryfalse. simpls. trivial.
  }
  {
    intros; simpls.
    destruct l2 eqn:Hl2; tryfalse. simpls; trivial.
    destruct H.
    splits; trivial.
    eapply IHl1; eauto.
  }
Qed.

Lemma rel_list_map: 
  forall A B C (R: A -> B -> Prop) l f1 f2, 
    (forall (e:C), 
      In e l -> 
      R (f1 e) (f2 e)) -> 
    rel_list R (map f1 l) (map f2 l).
Proof.
  induction l.
  {
    reflexivity.
  }
  {
    intros; simpls.
    splits.
    {
      eapply H. left; trivial.
    }
    {
      eapply IHl; eauto.
    }
  }
Qed.

Lemma rel_list_implies_eq_length: 
  forall A B (R: A -> B -> Prop) l1 l2, 
    rel_list R l1 l2 -> 
    length l1 = length l2.
Proof.
  induction l1.
  {
    intros; simpls.
    destruct l2; tryfalse.
    trivial.
  }
  {
    intros; simpls.
    destruct l2; tryfalse.
    inv H.
    simpl.
    f_equal.
    eapply IHl1; eauto.
  }
Qed.


Lemma rel_list_nth: 
  forall A B R n l1 l2,
  @rel_list A B R l1 l2 -> 
  (exists e1,
  nth_error l1 n = Some e1) <->
  (exists e2, 
  nth_error l2 n = Some e2).
Proof.
  induction n.
  {
    intros; simpls.
    split; intro.
    {
      destruct H0.
      destruct l1 eqn:Hl1; tryfalse.
      destruct l2 eqn:Hl2; tryfalse.
      eexists; eauto.
    }
    {
      destruct H0.
      destruct l1 eqn:Hl1; tryfalse.
      destruct l2 eqn:Hl2; tryfalse.
      eexists; eauto.
    }
  }
  {
    intros; simpls.
    split; intro.
    {
      destruct H0.
      destruct l1 eqn:Hl1; tryfalse.
      destruct l2 eqn:Hl2; tryfalse.
      simpls.
      destruct H.
      eapply IHn in H1; eauto.
      eapply H1; eauto.
    }
    {
      destruct H0.
      destruct l2 eqn:Hl2; tryfalse.
      destruct l1 eqn:Hl1; tryfalse.
      simpls.
      destruct H.
      eapply IHn in H1; eauto.
      eapply H1; eauto.
    }
  }
Qed. 

Lemma rel_list_implies_rel_nth:
  forall A B (R: A -> B -> Prop) pil1 pil2 n pi1 pi2,
  rel_list R pil1 pil2 -> 
  nth_error pil1 n = Some pi1 -> 
  nth_error pil2 n = Some pi2 -> 
  R pi1 pi2.
Proof.
  induction pil1.
  {
    intros; simpls.
    destruct pil2; tryfalse.
    destruct n; tryfalse.
  }
  {
    intros; simpls.
    destruct pil2 eqn:Hpil2; tryfalse.
    destruct H.
    rename a into pi1'. rename pil1 into pil1'.
    rename b into pi2'. rename l into pil2'.
    destruct n.
    {
      simpls.
      inv H0; inv H1; trivial.    
    }
    {
      simpls.
      eapply IHpil1 in H2; eauto.
    }
  }
Qed.

Lemma rel_list_symm:
  forall {A: Type} (l1 l2: list A) (R: A -> A -> Prop),
    (forall (a1 a2: A),
      R a1 a2 -> R a2 a1
    ) ->
    rel_list R l1 l2 -> 
    rel_list R l2 l1.
Proof. 
  induction l1.
  - intros. destruct l2; try solve [inversion H0].
    econs.
  - intros. destruct l2; try solve [inversion H0].
    inversion H0. subst. econs; eauto.
Qed.

Lemma rel_list_app_singleton:
  forall A B R l1 l2 a1 a2 ,
    @rel_list A B R (l1 ++ [a1]) (l2 ++ [a2]) ->
    @rel_list A B R l1 l2 /\ R a1 a2.
Proof.
  induction l1.
  {
    intros; simpls.
    destruct l2 eqn:Hl2; simpls. 
    - destruct H. split; trivial.
    - destruct H. destruct (l++[a2]) eqn:Hl'; tryfalse.   
      destruct l; tryfalse.
  }
  {
    intros; simpls.
    destruct l2 eqn:Hl2; simpls.
    - destruct H. destruct (l1++[a1]) eqn:Hl1; tryfalse.
      destruct l1 eqn:Hl'; tryfalse.
    - split. split.
      + destruct H. trivial.
      + destruct H. eapply IHl1; eauto.
      + destruct H. eapply IHl1; eauto. 
  }
Qed.

Definition Context := list ident.  
    
Definition Sorted_b {A: Type} (ord: A -> A -> bool) (l: list A): Prop := 
    Sorted (fun x y => ord x y = true) l. 


Definition total {A: Type} (ltb: A -> A -> bool) (eqb: A -> A -> bool) := 
    forall x y, ltb x y = true \/ ltb y x = true \/ eqb x y = true.

Definition transitive {A: Type} (ltb: A -> A -> bool) :=
    forall a b c : A, (ltb a b = true) -> (ltb b c = true) -> (ltb a c = true).

Definition reflexive {A: Type} (eqb: A -> A -> bool) := 
    forall x, eqb x x = true.

Definition symmetric {A: Type} (ord: A -> A -> bool) := 
    forall x y, 
        ord x y = ord y x. 

Definition irreflexive {A: Type} (ltb: A -> A -> bool) (eqb: A -> A -> bool):= 
    forall x y, eqb x y = true -> ltb x y = false.

Definition antisymmetric {A: Type} (ord: A -> A -> bool) (eqb: A -> A -> bool):= 
    forall x y, 
        ord x y = true -> ord y x = true -> eqb x y = true.

Definition combine_leb {A: Type} (ltb: A -> A -> bool) (eqb: A -> A -> bool) :=
        fun x y => (ltb x y) || (eqb x y). 

Definition ltb_eqb_implies_ltb {A: Type} (ltb: A -> A -> bool) (eqb: A -> A -> bool) := 
    forall x y z, 
        ltb x y = true -> 
        eqb y z = true -> 
        ltb x z = true.

Definition eqb_ltb_implies_ltb {A: Type} (ltb: A -> A -> bool) (eqb: A -> A -> bool) := 
    forall x y z, 
        eqb x y = true -> 
        ltb y z = true -> 
        ltb x z = true.

Lemma transitive_combine_implies_transitive: 
forall A ltb eqb, 
    @transitive A ltb -> 
    @transitive A eqb -> 
    ltb_eqb_implies_ltb ltb eqb -> 
    eqb_ltb_implies_ltb ltb eqb -> 
    transitive (combine_leb ltb eqb).
Proof.
    intros.
    unfolds transitive.
    unfolds combine_leb.
    intros.
    eapply orb_true_iff.
    eapply orb_true_iff in H3. 
    eapply orb_true_iff in H4. 
    destruct H3; destruct H4.
    {
        left; eapply H; eauto.
    }
    {
        unfolds ltb_eqb_implies_ltb.
        left; eapply H1; eauto.
    }
    {
        unfolds eqb_ltb_implies_ltb.
        left; eapply H2; eauto.
    }
    {
        right; eapply H0; eauto.
    }
Qed.

(** remove nth element, start from zero. *)
Fixpoint remove_nth {A: Type} (n: nat) (l: list A): list A := 
    match n, l with 
    | O, a::l => l 
    | S n', a::l => a :: remove_nth n' l
    | _, [] => []
    end.

Lemma remove_nth_length: 
    forall A n l l' x, 
        n < length l -> 
        @nth A n l x = x -> 
        remove_nth n l = l' -> 
        length l' + 1 = length l.
Proof. 
    induction n. 
    {
        intros.
        unfold remove_nth in H1.
        destruct l; eauto.
        {   
            simpl in H. lia.
        }
        {
            subst.
            replace (a::l') with ([a]++l'); simpl; eauto; lia.
        }
    }
    {
        intros.
        unfold remove_nth in H1. 
        fold (@remove_nth A) in H1.
        destruct l; eauto.
        {   
            simpl in H. lia.
        }
        {
            assert (length l = length l'). 
            {
                remember (remove_nth n l) as l''.
                symmetry in Heql''.
                eapply IHn in Heql''; eauto. 
                subst.
                rewrite <- Heql''.
                simpl. lia.
                simpl in H. lia.
            }
            simpl; rewrite H2; lia. 
        }
    }
Qed.

Lemma remove_nth_implies_splits: 
    forall A n l l' x x0,
        n < length l -> 
        @nth A n l x0 = x -> (** TODO: default x to any x0 is ok *)
        remove_nth n l = l' -> 
        (
            l = (firstn n l) ++ [x] ++ (skipn (n+1) l)  
            /\ 
            l' = (firstn n l) ++ (skipn (n+1) l)
        ).
Proof. 
    induction n.
    {
        intros.
        unfold remove_nth in H1.
        destruct l; simpls; eauto; try lia.
        subst; eauto.
    }
    intros.

    remember (firstn (S n) l) as ll.
    remember (skipn (S n + 1) l) as lr.
    unfold remove_nth in H1. folds (@remove_nth A).
    destruct l eqn:Hl. 
    simpls; eauto; lia.
    assert (n < length l0). { 
        unfold length in H.
        fold (@length A) in H.
        lia.
    }
    assert (nth n l0 x0 = x). {
        simpl in H0.
        eauto.
    }
    remember (remove_nth n l0) as l1.
    symmetry in Heql1.
    eapply IHn in H2; eauto.
    destruct H2 as (Hl0 & Hl1).
    remember (firstn n l0) as ll'.
    remember (skipn (n+1) l0) as lr'.
    rewrite firstn_cons in Heqll.
    simpl in Heqlr.
    splits.
    {
        subst. simpls. 
        rewrite <- Hl0; eauto.
    }
    {
        subst. simpls. 
        rewrite <- Hl1; eauto.
    }
Qed.

Lemma remove_nth_cons_nth_permut: 
    forall A n l y,
        n < length l ->
        nth n l y = y ->
        @Permutation A l (y :: remove_nth n l).
Proof.
    intros.
    remember (remove_nth n l) as l'.
    symmetry in Heql'.
    eapply remove_nth_implies_splits in Heql'; eauto.
    destruct Heql' as (Hl & Hl').
    subst.
    replace (y :: (firstn n l) ++ (skipn (n+1) l)) with ([y] ++ (firstn n l) ++ (skipn (n+1) l)); eauto.
    rewrite Hl at 1.
    eapply Permutation_app_swap_app; eauto.
Qed. 

Lemma remove_nth_app: 
    forall A n l l' l'',
    n < length l ->
    @remove_nth A n l = l' -> 
    remove_nth n (l++l'') = l'++l''.
Proof. 
    induction n.
    {
        intros.
        unfolds remove_nth.
        destruct l; simpls; eauto. 
        lia. subst; trivial.
    }
    {
        intros.
        unfold remove_nth in H0.
        destruct l; simpls; eauto; try lia.
        folds (@remove_nth A).
        remember (remove_nth n l) as ll.
        symmetry in Heqll.
        eapply IHn with (l'':=l'') in Heqll; eauto.
        rewrite Heqll.
        replace (a :: ll ++ l'') with ((a :: ll) ++ l'').
        rewrite H0; eauto.
        simpl; eauto.
        lia.
    }
Qed.

Lemma remove_nth_length_append_one:
    forall A l a,
    @remove_nth A (length l) (l ++ [a]) = l.
Proof.
    induction l.
    {
        intros. simpls; eauto.
    }
    {
        intros. simpls.
        rewrite IHl; eauto.
    }
Qed.
    

Lemma remove_nth_maps_comm: 
    forall A B n f l,
        @remove_nth A n (map f l) = map f (@remove_nth B n l).
Proof.
    induction n.
    {
        intros; simpls.
        destruct l eqn:Hl; simpls; trivial.
    }
    {
        intros; simpls.
        destruct l eqn:Hl; simpls; trivial.
        rewrite IHn; trivial.
    }
Qed.

Lemma remove_nth_in:
    forall A n x l l',
    @remove_nth A n l = l' -> 
    In x l' -> 
    In x l.
Proof.
    induction n.
    {
        intros; simpls.
        destruct l.
        rewrite <- H in H0.
        tryfalse.
        subst.
        eapply in_cons; trivial.
    }
    {
        intros; simpls.
        destruct l eqn:Hl.
        {
            subst. tryfalse.
        }
        {
            rewrite <- H in H0.
            inversion H0.
            {
                econs; trivial.
            }
            {
                remember (remove_nth n l0) as l0'.
                symmetry in Heql0'.
                eapply IHn in Heql0'; eauto.
                eapply in_cons; trivial.
            }
        }
    }
Qed.

Lemma remove_nth_preserve_sorted: 
  forall A ord n l,
    (transitive ord) ->
    Sorted_b ord l -> 
    Sorted_b ord (@remove_nth A n l).
Proof.
    induction n.
    {
        intros; simpls; eauto.
        destruct l; eauto.
        inv H0; eauto.
    }
    {
        intros.
        simpls.
        destruct l eqn:Hl; eauto.
        econs; eauto.
        {
            eapply IHn; eauto.
            inv H0; eauto.
        }
        {
            eapply Sorted_StronglySorted in H0; eauto.
            inv H0.
            remember (remove_nth n l0) as l'.
            destruct l'; simpls; eauto.
            econs.
            eapply Forall_forall with (x:=a0) in H4; eauto.
            eapply remove_nth_in with (n:=n); eauto.
            rewrite <- Heql'.
            econs; trivial.
        }
    }
Qed.

Lemma InA_map:
  forall A B eq (f: A -> B) l x,
    InA eq x (map f l) <->
    exists y, In y l /\ eq x (f y).
Proof.
  induction l.
  {
    intros. simpls. split; intro.
    - eapply InA_nil in H; tryfalse.
    - destruct H as (y & Hin & Heq); tryfalse. 
  }
  {
    intros. simpls. 
    rewrite InA_cons.
    split; intro.
    - destruct H.
      + subst. exists a. split; eauto.
      + eapply IHl in H. destruct H as (y & Hin & Heq).
        exists y. split; eauto.
    - destruct H as (y & Hin & Heq).
      eapply InA_cons.
      destruct Hin.
      + subst. left; trivial.
      + right. eapply IHl. exists y. split; eauto. 
  }
Qed.

Lemma app_inv_singleton:
  forall A l1 l2 (a1 a2: A), 
    l1 ++ [a1] = l2 ++ [a2] -> 
    l1 = l2 /\ a1 = a2.
Proof.
  induction l1.
  {
    intros; simpls.
    destruct l2 eqn:Hl2; simpls.
    - inv H; split; trivial.
    - inv H. destruct l; tryfalse. 
  }
  {
    intros; simpls.
    destruct l2 eqn:Hl2; simpls.
    - inv H. destruct l1; tryfalse.
    - inv H.
      eapply IHl1 in H2. 
      destruct H2; subst; split; trivial. 
  }
Qed.

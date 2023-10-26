(* 
  
  Some lemmas that can be used in conjunction with those in Coq.Lists.List
  
  See https://coq.inria.fr/library/Coq.Lists.List.html
 
 *)

(*
    This file is copied from: 
    https://gist.github.com/Agnishom/d686ef345d7c7b408362e1d2c9c64581
*)

Require Import Lia.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Wf_nat.

Require Import Datatypes.
Require Import Misc.

Import ListNotations.

(* firstn / skipn / nth_error / map / combine *)

Lemma nth_error_skipn {X} : forall (xs : list X) i d,
  nth_error xs (i + d) = nth_error (skipn d xs) i.
Proof.
  intros.
  rewrite <- firstn_skipn with (n := d) (l := xs) at 1.
  assert (d < length xs \/ d >= length xs) as Hxs by lia.
  destruct Hxs.
  - rewrite nth_error_app2.
    + rewrite firstn_length.
      f_equal. lia.
    + rewrite firstn_length.
      lia.
  - rewrite firstn_all2 by lia.
    rewrite skipn_all2 by lia.
    rewrite app_nil_r.
    replace (nth_error (@nil X) i) with (@None X)
      by now destruct i.
    replace (nth_error xs (i + d)) with (@None X).
    auto.
    symmetry. apply nth_error_None. lia.
Qed.

Lemma nth_error_firstn {X : Type} (l : list X) : forall d i,
  i < d
  -> nth_error (firstn d l) i = nth_error l i.
Proof.
  intros d i Hdi.
  assert (d <= length l \/ d > length l) as [Hdl | Hdl] by lia.
  + rewrite <- firstn_skipn with (l := l) (n := d) at 2.
  rewrite nth_error_app1. auto.
  rewrite firstn_length. lia.
  + now rewrite firstn_all2 by lia.
Qed.

Lemma firstn_in {X : Type} : forall (l : list X) n,
  forall x, In x (firstn n l) -> In x l.
Proof.
  intros.
  rewrite <- (firstn_skipn n l) at 1.
  apply in_or_app. auto.
Qed.

Lemma skipn_in {X : Type} : forall (l : list X) n,
  forall x, In x (skipn n l) -> In x l.
Proof.
  intros.
  rewrite <- (firstn_skipn n l) at 1.
  apply in_or_app. auto.
Qed.

Lemma hd_error_skipn {X : Type} (l : list X) : forall i,
  hd_error (skipn i l) = nth_error l i.
Proof.
  intro i.
  generalize dependent l. induction i.
  - intro. rewrite skipn_O. destruct l; auto.
  - intro. destruct l; auto.
    simpl. auto.
Qed.

Lemma hd_error_nth_error {X : Type} (l : list X) :
  hd_error l = nth_error l 0.
Proof.
  destruct l; auto.
Qed.

Lemma nth_error_rev {A: Type} (l : list A) (n : nat) :
  n < length l ->
  nth_error (rev l) n = nth_error l (length l - S n).
Proof.
  destruct l.
  - simpl. destruct n; reflexivity.
  - intros. remember (a :: l) as l'.
    rewrite nth_error_nth' with (d := a).
    rewrite nth_error_nth' with (d := a).
    f_equal. apply rev_nth.
    auto. lia. auto.
    rewrite rev_length. auto.
Qed.

Lemma map_id {X} : forall (xs : list X),
  map id xs = xs.
Proof.
  induction xs; auto.
  simpl. rewrite IHxs. auto.
Qed.

Lemma combine_map {X Y M N} : forall (f : X -> M) (g : Y -> N) xs ys,
  combine (map f xs) (map g ys) = map (fun '(x, y) => (f x, g y)) (combine xs ys).
Proof.
  induction xs.
  - auto.
  - intros. destruct ys.
    + simpl. auto.
    + simpl. rewrite IHxs. auto.
Qed.

Lemma combine_app {X Y} : forall (xs1 xs2 : list X) (ys1 ys2 : list Y),
  length xs1 = length ys1
  -> combine (xs1 ++ xs2) (ys1 ++ ys2) = combine xs1 ys1 ++ combine xs2 ys2.
Proof.
  intros.
  revert ys1 H.
  induction xs1.
  - intros. destruct ys1. auto. simpl in H. discriminate.
  - intros. destruct ys1. simpl in H. discriminate.
    simpl. rewrite IHxs1. auto.
    simpl in H. inversion H. auto.
Qed.

Lemma combine_rev {X Y} : forall (xs : list X) (ys : list Y),
  length xs = length ys
  -> combine (rev xs) (rev ys) = rev (combine xs ys).
Proof.
  intros.
  revert ys H.
  induction xs.
  - intros. destruct ys. auto. simpl in H. discriminate.
  - intros. destruct ys. simpl in H. discriminate.
    simpl. simpl in H. inversion H.
    rewrite combine_app. simpl. rewrite IHxs. auto.
    auto.
    repeat rewrite rev_length. auto.
Qed. 

Lemma map_repeat {X Y : Type} (f : X -> Y) (x : X) n :
  map f (repeat x n) = repeat (f x) n.
Proof.
  induction n; auto.
  simpl. rewrite IHn. auto.
Qed.

Lemma repeat_iff {X : Type} (x : X) l:
  l = repeat x (length l) <-> (forall y, In y l -> y = x).
Proof.
  split.
  - intros. rewrite H in H0.
    apply repeat_spec in H0. auto.
  - intros. apply Forall_eq_repeat.
    apply Forall_forall. firstorder.
Qed.

(* zipWith *)

Definition zipWith {X Y Z} (f : X -> Y -> Z) (xs : list X) (ys : list Y) : list Z :=
  map (fun '(x, y) => f x y) (combine xs ys).

Lemma zipWith_length {X Y Z} : forall (f : X -> Y -> Z) xs ys,
  length (zipWith f xs ys) = min (length xs) (length ys).
Proof.
  intros. unfold zipWith.
  now rewrite map_length, combine_length.
Qed.

Lemma zipWith_in {X Y Z} : forall (P : X -> Prop) (Q : Y -> Prop) (R : Z -> Prop) (f : X -> Y -> Z) xs ys,
  (forall x, In x xs -> P x)
  -> (forall y, In y ys -> Q y)
  -> (forall x y, P x -> Q y -> R (f x y))
  -> forall z, In z (zipWith f xs ys) -> R z.
Proof.
  intros P Q R f.
  induction xs; intros ys Hxs Hys Hf z Hz.
  - simpl in Hz. inversion Hz.
  - simpl in Hz. destruct ys.
    + inversion Hz.
    + destruct Hz.
      * subst. apply Hf.
        apply Hxs. now left.
        apply Hys. now left.
      * rewrite in_map_iff in H.
        destruct H as [[xx yy] [H1 H2]].
        subst. apply Hf.
        apply Hxs. right.
        now apply in_combine_l in H2.
        apply Hys. right.
        now apply in_combine_r in H2.
Qed.

Lemma nth_error_zipWith {X Y Z} : forall (f : X -> Y -> Z) xs ys n,
  nth_error (zipWith f xs ys) n = 
  match nth_error xs n, nth_error ys n with
  | Some x, Some y => Some (f x y)
  | _, _ => None
  end.
Proof.
  intros f. induction xs.
  - intros ys n.
    assert (zipWith f [] ys = []). {
      unfold zipWith. destruct ys; auto.
    }
    rewrite H.
    remember (nth_error [] n) as nz.
    assert (nz = None). {
      subst. destruct n; auto.
    }
    remember (nth_error (@nil X) n) as nx.
    assert (nx = None). {
      subst. destruct n; auto.
    }
    rewrite H0, H1. auto.
  - intros. destruct n.
    + simpl. destruct ys.
      * auto.
      * simpl. auto.
    + destruct ys.
      * simpl. destruct (nth_error xs n); auto.
      * simpl.
        rewrite <- IHxs.
        auto.
Qed.

Lemma zipWith_cons {X Y Z} : forall (f : X -> Y -> Z) x xs y ys,
  zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys.
Proof.
  auto.
Qed.

Lemma zipWith_repeat_l {X Y Z} : forall n (f : X -> Y -> Z) x ys,
  n >= length ys
  -> zipWith f (repeat x n) ys = map (f x) ys.
Proof.
  induction n.
  - intros. simpl. destruct ys; [auto | simpl in H; lia].
  - intros. destruct ys.
    + simpl. auto.
    + simpl. rewrite zipWith_cons.
      rewrite IHn. auto.
      simpl in H. lia.
Qed.

Lemma zipWith_repeat_r {X Y Z} : forall n (f : X -> Y -> Z) xs y,
  n >= length xs
  -> zipWith f xs (repeat y n) = map (fun x => f x y) xs.
Proof.
  induction n.
  - intros. simpl. destruct xs; [auto | simpl in H; lia].
  - intros. destruct xs.
    + simpl. auto.
    + simpl. rewrite zipWith_cons.
      rewrite IHn. auto.
      simpl in H. lia.
Qed.

Lemma zipWith_firstn_l {X Y Z} : forall (f : X -> Y -> Z) xs ys,
  zipWith f xs ys = zipWith f xs (firstn (length xs) ys).
Proof.
  unfold zipWith. intros. rewrite combine_firstn_l. auto.
Qed.

Lemma zipWith_firstn_r {X Y Z} : forall (f : X -> Y -> Z) xs ys,
  zipWith f xs ys = zipWith f (firstn (length ys) xs) ys.
Proof.
  unfold zipWith. intros. rewrite combine_firstn_r. auto.
Qed.

Lemma zipWith_firstn {X Y Z} : forall (f : X -> Y -> Z) xs ys,
  zipWith f xs ys = 
    let n := (min (length xs) (length ys)) in 
    zipWith f (firstn n xs) (firstn n ys).
Proof.
  intros. 
  assert (length xs <= length ys \/ length xs > length ys) as [H | H] by lia.
  - replace (min (length xs) (length ys)) with (length xs) by lia.
    simpl.
    assert (zipWith f xs ys = zipWith f xs (firstn (length xs) ys)) as H1.
    { apply zipWith_firstn_l. }
    assert (zipWith f xs (firstn (length xs) ys) = 
            zipWith f (firstn (length xs) xs) (firstn (length xs) ys)) as H3.
    { f_equal. now rewrite firstn_all. }
    congruence.
  - replace (min (length xs) (length ys)) with (length ys) by lia.
    simpl.
    assert (zipWith f xs ys = zipWith f (firstn (length ys) xs) ys) as H1.
    { apply zipWith_firstn_r. }
    assert (zipWith f (firstn (length ys) xs) ys = 
            zipWith f (firstn (length ys) xs) (firstn (length ys) ys)) as H3.
    { f_equal. now rewrite firstn_all. }
    congruence.
Qed.

Lemma zipWith_map { M N X Y Z }: forall (f : M -> N -> Z) (g : X -> M) (h : Y -> N) (xs : list X) (ys : list Y),
  zipWith f (map g xs) (map h ys) = map (fun '(x, y) => f (g x) (h y)) (combine xs ys).
Proof.
  intros. unfold zipWith.
  rewrite combine_map. rewrite map_map.
  apply map_ext. intros. destruct a. auto.
Qed.

Lemma zipWith_assoc {X}: forall (f : X -> X -> X) xs ys zs,
  (forall x y z, f x (f y z) = f (f x y) z)
  -> zipWith f xs (zipWith f ys zs) = zipWith f (zipWith f xs ys) zs.
Proof.
  intros f xs.
  remember (length xs) as len.
  generalize dependent xs.
  induction len. 
  - intros. destruct xs. auto. simpl in Heqlen. discriminate.
  - intros. destruct xs.
    + auto. 
    + destruct ys.
      * auto.
      * destruct zs.
        -- auto.
        -- simpl. repeat rewrite zipWith_cons.
          rewrite H. rewrite IHlen.
          ++ auto.
          ++ simpl in Heqlen. inversion Heqlen. auto.
          ++ apply H. 
Qed.

Lemma zipWith_ext { X Y Z M N } : forall (f : X -> Y -> Z) (g : M -> N -> Z) xs ys ms ns,
  (forall x y m n, In ((x, y), (m, n)) (combine (combine xs ys) (combine ms ns)) -> f x y = g m n)
  -> length xs = length ms
  -> length ys = length ns
  -> zipWith f xs ys = zipWith g ms ns.
Proof.
  intros f g xs.
  remember (length xs) as len.
  generalize dependent xs.
  induction len. 
  - intros. destruct xs. destruct ms. auto.
    simpl in H0. discriminate. simpl in H0. discriminate.
  - intros. destruct xs. {
    simpl in Heqlen. discriminate.
  } destruct ms. {
    simpl in Heqlen. discriminate.
  } destruct ys. {
    simpl in H1. simpl in H0.
    destruct ns. auto. simpl in H1. discriminate.
  } destruct ns. {
    simpl in H1. discriminate.
  }
  rewrite zipWith_cons. rewrite zipWith_cons.
  simpl in H. f_equal.
  + apply H. auto.
  + apply IHlen.
    1 : { simpl in Heqlen. inversion Heqlen. auto. }
    3 : { simpl in H1. inversion H1. auto. }    
    2 : { simpl in H. firstorder. }
    firstorder.
Qed.

Lemma zipWith_cons_singleton {X} : forall (xs : list X) (xss : list (list X)),
  zipWith cons xs xss = zipWith (@app X) (map (fun x => [x]) xs) xss.
Proof.
  intros.
  apply zipWith_ext.
  2 : { now rewrite map_length. }
  2 : { auto. }
  revert xss.
  induction xs.
  - intros. simpl in H. tauto.
  - intros. destruct xss.
    + simpl in H. tauto.
    + simpl in H. destruct H.
      * inversion H. auto.
      * eapply IHxs. eauto.
Qed. 

Lemma zipWith_rev {X Y Z} : forall (f : X -> Y -> Z) xs ys,
  length xs = length ys
  -> zipWith f (rev xs) (rev ys) = rev (zipWith f xs ys).
Proof.
  intros. unfold zipWith.
  rewrite combine_rev by assumption.
  apply map_rev.
Qed.

Lemma zipWith_map2 {X Y Z W : Type} (f : X -> Y -> Z) (g : Z -> W) (xs : list X) (ys : list Y) :
  map g (zipWith f xs ys) = zipWith (fun x y => g (f x y)) xs ys.
Proof.
  unfold zipWith at 2.
  replace (map (fun '(x, y) => g (f x y)) (combine xs ys))
    with (map g (map (fun '(x, y) => f x y) (combine xs ys))). 2: {
    rewrite map_map. apply map_ext_in. intros [x y]. auto.
  } 
  auto.
Qed.

Lemma zipWith_ext_id_l {X Y : Type} (f : X -> Y -> X) (xs : list X) (ys : list Y) :
  (forall x y, In (x, y) (combine xs ys) -> f x y = x)
  -> length xs <= length ys
  -> zipWith f xs ys = xs.
Proof.
  remember (length xs) as len.
  generalize dependent xs.
  generalize dependent ys.
  induction len.
  - intros. destruct xs; destruct ys; auto.
    simpl in Heqlen. discriminate.
    simpl in H0. discriminate.
  - intros. destruct xs; destruct ys; auto.
    + simpl in H0. lia.
    + simpl in H. rewrite zipWith_cons.
      f_equal.
      * specialize (H x y). auto.
      * apply IHlen. 
        simpl in Heqlen. lia.
        intros. apply H. auto. 
        simpl in H0. lia.
Qed.

Lemma zipWith_ext_id_r {X Y : Type} (f : X -> Y -> Y) (xs : list X) (ys : list Y) :
  (forall x y, In (x, y) (combine xs ys) -> f x y = y)
  -> length xs >= length ys
  -> zipWith f xs ys = ys.
Proof.
  remember (length xs) as len.
  generalize dependent xs.
  generalize dependent ys.
  induction len.
  - intros. destruct xs; destruct ys; auto.
    simpl in H0. lia.
    simpl in H0. discriminate.
  - intros. destruct xs; destruct ys; auto.
    + simpl in H0. discriminate.
    + simpl in H. rewrite zipWith_cons.
      f_equal.
      * specialize (H x y). auto.
      * apply IHlen. 
        simpl in Heqlen. lia.
        intros. apply H. auto. 
        simpl in H0. lia.
Qed.

(* transpose *)

Fixpoint transpose {X : Type} (len : nat) (tapes : list (list X)) : list (list X) :=
  match tapes with
  | [] => repeat [] len
  | t :: ts => zipWith cons t (transpose len ts)
  end.

  Lemma transpose_length {X : Type} : forall len (tapes : list (list X)),
  (forall t, 
    In t tapes -> length t >= len)
  -> length (transpose len tapes) = len.
Proof.
  intros len tapes. revert len.
  induction tapes; intros len Hlen.
  - simpl. now rewrite repeat_length.
  - simpl. rewrite zipWith_length.
    rewrite IHtapes.
    + simpl in Hlen. specialize (Hlen a).
      assert (length a >= len) by auto.
      lia.
    + intros t Ht. apply Hlen. now right.
Qed.

Lemma transpose_inner_length {X : Type}: forall len (tapes : list (list X)),
  forall u,
    In u (transpose len tapes)
    -> length u = length tapes.
Proof.
  intros len tapes. revert len.
  induction tapes; intros len u Hu.
  - simpl in *. apply repeat_spec in Hu.
    subst. auto.
  - simpl in *.
    unfold zipWith in Hu.
    rewrite in_map_iff in Hu.
    destruct Hu as [[u1 us] [Hu Hus]].
    apply in_combine_r in Hus.
    subst. simpl. f_equal.
    firstorder.
Qed.

Lemma transpose_inner_length_eq {X : Type} : forall len (tapes : list (list X)),
  forall u v,
    In u (transpose len tapes)
    -> In v (transpose len tapes)
    -> length u = length v.
Proof.
  intros.
  apply transpose_inner_length in H.
  apply transpose_inner_length in H0.
  congruence.
Qed.

Lemma transpose_app {X : Type} : forall len (tapes1 tapes2 : list (list X)),
  (forall t, In t tapes1 -> length t >= len)
  -> (forall t, In t tapes2 -> length t >= len)
  -> transpose len (tapes1 ++ tapes2) = 
  zipWith (@app X) (transpose len tapes1) (transpose len tapes2).
Proof.
  intros len tapes1 tapes2 Ht1 Ht2.
  induction tapes1.
  - simpl.
    rewrite zipWith_repeat_l.
    rewrite <- map_id with (xs := transpose _ _) at 1.
    apply map_ext. auto.
    rewrite transpose_length. auto. auto.
  - simpl. rewrite IHtapes1.
    + rewrite zipWith_cons_singleton.
      rewrite zipWith_cons_singleton.
      rewrite zipWith_assoc by apply app_assoc.
      auto.
    + simpl in Ht1. firstorder.  
Qed.

Lemma transpose_singleton {X : Type} : forall (t : list X),
  transpose (length t) [t] = map (fun x => [x]) t.
Proof.
  intros. unfold transpose. 
  now rewrite zipWith_repeat_r by lia.
Qed.

Lemma transpose_rev_aux {X : Type} : forall (xss : list (list X)) (l : list X),
  (forall t u, In t xss -> In u xss -> length t = length u)
  -> zipWith (@app X) (map (@rev X) xss) (map (fun x => [x]) l) 
    = map (@rev X) (zipWith (@app X) (map (fun x => [x]) l) xss).
Proof.
  induction xss as [ | xs xss].
  - intros. simpl.
    destruct l.
    + auto.
    + simpl. unfold zipWith. auto.
  - intros. destruct l.
    + simpl. unfold zipWith. auto.
    + simpl map at 1 2. rewrite zipWith_cons.
      simpl map at 3. f_equal.
      rewrite IHxss. auto.
      simpl in H. firstorder.
Qed.

Lemma transpose_rev {X : Type} : forall len (tapes : list (list X)),
  (forall t, In t tapes -> length t = len)
  -> transpose len (rev tapes) = map (@rev X) (transpose len tapes).
Proof.
  intros len tapes Hlen.
  induction tapes.
  - simpl. rewrite <- map_id with (xs := repeat [] len) at 1.
    apply map_ext_in. intros.
    apply repeat_spec in H. subst. auto.
  - simpl. simpl in Hlen.
    assert (length a = len) as Ha. {
      apply Hlen. auto.
    }
    rewrite transpose_app.
    rewrite IHtapes.
    rewrite zipWith_cons_singleton.
    rewrite <- Ha.
    rewrite transpose_singleton.
    rewrite transpose_rev_aux. auto.
    + apply transpose_inner_length_eq.
    + auto.
    + intros. rewrite <- in_rev in H.
      enough (length t = len) by lia. auto.
    + simpl. intros. 
      enough (length t = len) by lia. firstorder.
Qed.

Lemma transpose_zipWith_cons {X : Type} : forall len (mat : list (list X)) t,
    (forall u, In u mat -> length u >= len) 
  -> length t = length mat
  -> transpose (S len) (zipWith cons t mat) = t :: transpose len mat.
Proof.
  intros len mat. revert len. induction mat as [ | t1 mat1 IHmat].
  - intros. simpl. destruct t; auto. simpl in H0. discriminate.
  - intros. simpl. destruct t.
    + simpl in H0. discriminate.
    + rewrite zipWith_cons.
      simpl transpose. rewrite IHmat.
      * now rewrite zipWith_cons.
      * simpl in H. firstorder.
      * simpl in H0. now inversion H0.
Qed.


Lemma transpose_involutive {X : Type} : forall len (tapes : list (list X)),
  (forall t, In t tapes -> length t = len)
  -> transpose (length tapes) (transpose len tapes) = tapes.
Proof.
  intros len tapes. revert len.
  induction tapes as [ | t tapes1 IHtapes].
  - simpl. intros.
    destruct len; auto.
  - intros. simpl. rewrite transpose_zipWith_cons.
    + rewrite IHtapes. auto.
      simpl in H. firstorder.
    + simpl in H. intros.
      enough (length u = length tapes1) by lia.
      eapply transpose_inner_length; eauto.
    + rewrite transpose_length.
      * simpl in H. apply H. auto.
      * simpl in H. intros.
        enough (length t0 = len) by lia.
        apply H. auto.
Qed.

Lemma transpose_rev2 {X : Type} : forall len (tapes : list (list X)),
  (forall t, In t tapes -> length t = len)
  -> rev (transpose len tapes) = transpose len (map (@rev X) tapes).
Proof.
  intros len tapes Hlen.
  pose proof (@transpose_rev X (length tapes) (transpose len tapes)).
  assert (forall t, In t (transpose len tapes) -> length t = length tapes) as Hlen2. {
    intros; now apply transpose_inner_length in H0.
  }
  specialize (H Hlen2).
  rewrite transpose_involutive in H.
  apply (f_equal (fun x => transpose len x)) in H.
  replace len with (length (rev (transpose len tapes))) in H at 1. 2 :{
    rewrite rev_length. rewrite transpose_length. auto.
    intros. enough (length t = len) by lia. auto.
  }
  rewrite transpose_involutive in H. auto.
  - intros. rewrite <- in_rev in H0.
    eapply transpose_inner_length; eauto.
  - auto.
  (* (1) from transpose_rev: transpose (rev tapes) = map rev (transpose tapes)
    (2) plugin (tapes := transpose tapes): 
            transpose (rev (transpose tapes)) 
          = map rev (transpose (transpose tapes)) 
          = map rev tapes 
      (3) apply transpose to both sides.
  *)
Qed.

Lemma transpose_firstn {X : Type} : forall len (tapes : list (list X)) n,
  (forall t, In t tapes -> length t >= len)
  -> transpose len (firstn n tapes) = map (firstn n) (transpose len tapes).
Proof.
  intros len tapes n Hlen.
  assert (n > length tapes \/ n <= length tapes) as [Hn | Hn] by lia. {
    rewrite firstn_all2 by lia.
    rewrite map_ext_in with (g := id).
    now rewrite map_id.
    intros. simpl.
    rewrite firstn_all2.
    auto. apply transpose_inner_length in H. lia.
  }
  rewrite <- firstn_skipn with (l := tapes) (n := n) at 2.
  rewrite transpose_app. rewrite zipWith_map2.
  rewrite zipWith_ext_id_l. auto.
  - intros. rewrite firstn_app.
    enough (n = length x). {
      rewrite H0.
      replace (length x - length x) with 0 by lia.
      rewrite firstn_O. rewrite firstn_all. apply app_nil_r.
    }
    apply in_combine_l in H.
    apply transpose_inner_length in H.
    rewrite firstn_length in H.
    lia.
  - repeat rewrite transpose_length. auto.
    * intros. apply skipn_in in H. auto.
    * intros. apply firstn_in in H. auto.
  - intros. apply firstn_in in H. auto.
  - intros. apply skipn_in in H. auto.
Qed.

Lemma transpose_skipn {X : Type} : forall len (tapes : list (list X)) n,
  (forall t, In t tapes -> length t >= len)
  -> transpose len (skipn n tapes) = map (skipn n) (transpose len tapes).
Proof.
  intros len tapes n Hlen.
  assert (n > length tapes \/ n <= length tapes) as [Hn | Hn] by lia. {
    rewrite skipn_all2 by lia.
    simpl. revert Hn.
    induction tapes.
    - simpl. rewrite map_repeat. destruct n; auto.
    - simpl. intros. rewrite zipWith_map2. unfold zipWith.
      rewrite map_ext_in with (g := (fun x => [])). 2 : {
        intros. destruct a0. 
        pose proof H as H0.
        apply in_combine_l in H.
        apply in_combine_r in H0.
        apply skipn_all2.
        simpl. apply transpose_inner_length in H0.
        lia.
      } 
      assert (length (combine a (transpose len tapes)) = len). {
        rewrite combine_length. simpl in Hlen.
        rewrite transpose_length. specialize (Hlen a ltac:(auto)). lia.
        auto.
      }
      remember (map _ (combine _ _)) as rhs.
      assert (rhs = repeat [] (length rhs)). {
        rewrite repeat_iff. subst rhs. intros.
        apply in_map_iff in H0. destruct H0 as [? [? ?]].
        auto.
      }
      rewrite Heqrhs in H0 at 2. rewrite map_length in H0.
      rewrite H in H0. auto.
  }
  rewrite <- firstn_skipn with (l := tapes) (n := n) at 2.
  rewrite transpose_app. rewrite zipWith_map2.
  rewrite zipWith_ext_id_r. auto.
  - intros. rewrite skipn_app; trivial.
    enough (n = length x). { 
      rewrite H0. trivial.
    }
    apply in_combine_l in H.
    apply transpose_inner_length in H.
    rewrite firstn_length in H.
    lia.
  - repeat rewrite transpose_length. auto.
    * intros. apply skipn_in in H. auto.
    * intros. apply firstn_in in H. auto.
  - intros. apply firstn_in in H. auto.
  - intros. apply skipn_in in H. auto.
Qed.

Lemma skipn_zipWith_cons {X : Type} (xs : list X) (xss : list (list X)) :
length xs >= length xss
  -> map (skipn 1) (zipWith cons xs xss) = xss.
Proof.
  generalize dependent xs.
  induction xss; intros.
  - destruct xs; auto.
  - destruct xs.
    + simpl in H. lia.
    + rewrite zipWith_cons.
      rewrite map_cons.
      simpl skipn at 1.
      f_equal. apply IHxss. 
      simpl in H. lia.
Qed.


(* ij_error *)

Definition ij_error {X : Type} (i j : nat) (l : list (list X)) : option X :=
  match nth_error l i with
  | Some l' => nth_error l' j
  | None => None
  end.

Lemma ij_error_remove_rows {X : Type} (i j d : nat) (l : list (list X)) :
  ij_error (i + d) j l = ij_error i j (skipn d l).
Proof.
  unfold ij_error.
  rewrite nth_error_skipn.
  auto.
Qed.

Lemma ij_error_remove_cols {X : Type} (i j d : nat) (l : list (list X)) :
  ij_error i (j + d) l = ij_error i j (map (skipn d) l).
Proof.
  unfold ij_error.
  remember (nth_error l i) as row_i.
  destruct row_i.
  2 : {
    symmetry in Heqrow_i. 
    rewrite nth_error_None in Heqrow_i.
    assert (nth_error (map (skipn d) l) i = None). {
      rewrite nth_error_None.
      now rewrite map_length.
    }
    rewrite H. auto.
  }
  assert (length l > i) as Hlen. {
    symmetry in Heqrow_i.
    assert (nth_error l i <> None) by congruence.
    rewrite nth_error_Some in H.
    lia.
  }
  remember (nth_error (map (skipn d) l) i) as row_i'.
  destruct row_i'.
  2 : {
    symmetry in Heqrow_i'.
    rewrite nth_error_None in Heqrow_i'.
    rewrite map_length in Heqrow_i'. lia.
  }
  symmetry in Heqrow_i'.
  rewrite Misc.nth_error_map_iff in Heqrow_i'.
  destruct Heqrow_i' as [row_i [Hnth Heqrow_i']].
  rewrite Hnth in Heqrow_i.
  inversion Heqrow_i. subst.
  now rewrite nth_error_skipn.
Qed.

Lemma transpose_spec_0 {X : Type} : forall (xs : list X) (xss : list (list X)) i,
  length xss = length xs
  -> nth_error xs i = ij_error i 0 (zipWith cons xs xss).
Proof.
  induction xs.
  - intros. simpl. destruct i; auto.
  - intros xss. destruct i.
    + intros. simpl. unfold ij_error.
      destruct xss.
      * simpl in H. lia.
      * simpl. auto.
    + intros. simpl. unfold ij_error.
      destruct xss.
      * simpl in H. lia.
      * rewrite zipWith_cons.
        simpl nth_error. 
        rewrite IHxs with (xss := xss).
        auto. simpl in H. lia.
Qed. 

Lemma transpose_spec {X : Type} : forall len (tapes : list (list X)),
  (forall t,
    In t tapes -> length t = len)
  -> forall i j,
    ij_error i j tapes = ij_error j i (transpose len tapes).
Proof.
  induction tapes as [|l tapes IHt]; simpl; intros H.
- (* when the matrix is empty *)
  intros i j.
  destruct i.
  + unfold ij_error at 1. simpl.
    unfold ij_error. 
    assert (j < len \/ j >= len) by lia.
    destruct H0.
    ++ 
    rewrite Misc.nth_error_repeat by apply H0.
      auto.
    ++ assert (nth_error (repeat (@nil X) len) j = None). {
        rewrite nth_error_None by lia.
        rewrite repeat_length.
        auto.
      }
      rewrite H1. auto.
  + unfold ij_error at 1. simpl.
    unfold ij_error. 
    assert (j < len \/ j >= len) by lia.
    destruct H0.
    ++ rewrite nth_error_repeat by apply H0.
      auto.
    ++ assert (nth_error (repeat (@nil X) len) j = None). {
        rewrite nth_error_None by lia.
        rewrite repeat_length.
        auto.
      }
      rewrite H1. auto. 
- destruct i.
  + (* ij_error 0 j and ij_error j 0 *)
    intros j.
    unfold ij_error at 1. simpl.
    apply transpose_spec_0.
    rewrite transpose_length.
    symmetry. apply H. auto.
    intros. enough (length t = len) by lia.
    apply H. auto.
  + (* ij_error (S i) j and ij_error j (S i *)
    replace (S i) with (i + 1) by lia. intros.
    rewrite ij_error_remove_cols.
    rewrite ij_error_remove_rows.
    simpl skipn at 1.
    rewrite IHt. 
    rewrite skipn_zipWith_cons. auto.
    * rewrite transpose_length.
      enough (length l = len) by lia.
      apply H. auto.
      intros.
      enough (length t = len) by lia.
      apply H. auto.
    * intros. 
      enough (length t = len) by lia.
      apply H. auto.
Qed.

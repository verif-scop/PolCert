(** Miscellaneous extensions of "Coq" standard library *)

Require List.
Require Import Sorting.Permutation.
Import List.ListNotations.
Local Open Scope list_scope.

(** A "fixpoint" variant of "List.Forall" (in the style of "List.In") *)
Fixpoint Forall {A} (P: A -> Prop) (l: list A) : Prop :=
  match l with
  | [] => True
  | x::l' => P x /\ Forall P l'
  end.

Lemma Forall_monotone {A} (l: list A) (P Q: A -> Prop):
  Forall P l -> (forall x, P x -> Q x) -> Forall Q l.
Proof.
  induction l; simpl; intuition.
Qed.

Lemma Forall_ListForall  {A} (l: list A) (P: A -> Prop):
  Forall P l <-> List.Forall P l.
Proof.
  constructor 1.
    - induction l; simpl; intuition.
    - induction 1; simpl; intuition.
Qed.

Lemma Forall_ListForIn  {A} (l: list A) (P: A -> Prop):
  Forall P l <-> (forall x, List.In x l -> P x).
Proof.
  induction l; simpl; intuition (subst; auto).
Qed.

Lemma Forall_cons {A} (x : A) (l : list A) (P: A -> Prop): P x -> Forall P l -> Forall P (x :: l).
Proof.
  simpl; intuition.
Qed.

Lemma Forall_app {A} (l1 l2 : list A) (P: A -> Prop): Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
Proof.
  induction l1; simpl; intuition auto.
Qed.
Hint Resolve Forall_app.

Lemma Forall_Forall_cons {A} l1: forall a (P: A -> A -> Prop) (l2: list A),
   Forall (fun x => P x a) l1 -> Forall (fun x => Forall (P x) l2) l1 -> Forall (fun x => Forall (P x) (a::l2)) l1.
Proof.
  simpl; induction l1; simpl; intuition auto.
Qed.



Section FilterProp.

Variable A : Type.
Variable f : A -> bool.

Lemma Forall_negb_true_false (l: list A):
  Forall (fun x => negb (f x) = true) l -> Forall (fun x => (f x)=false) l.
Proof.
  intros; eapply Forall_monotone; eauto.
  simpl; intros x; case (f x); simpl; auto.
Qed.

Lemma Forall_false_negb_true (l: list A):
  Forall (fun x => (f x)=false) l -> Forall (fun x => negb (f x) = true) l.
Proof.
  intros; eapply Forall_monotone; eauto.
  simpl; intros x; case (f x); simpl; auto.
Qed.

Lemma filter_app l1 l2: List.filter f (l1++l2) = (List.filter f l1) ++ (List.filter f l2).
Proof.  
  induction l1; simpl; auto.
  destruct (f a); simpl; congruence.
Qed.

Lemma filter_triv_true l: (Forall (fun x => f x = true) l) -> List.filter f l = l.
Proof.
  induction l; simpl; intuition auto.
  rewrite H0; simpl; congruence.
Qed.

Lemma filter_triv_false l: (Forall (fun x => f x = false) l) -> List.filter f l = [].
Proof.
  induction l; simpl; intuition auto.
  rewrite H0; simpl; congruence.
Qed.

Lemma filter_empty_false l: List.filter f l = [] -> (Forall (fun x => f x = false) l).
Proof.
  induction l; simpl; auto.
  case (f a); simpl; intuition discriminate.
Qed.


Local Hint Constructors Permutation.
Local Hint Resolve Permutation_sym Permutation_middle.
Lemma filter_split l: Permutation ((List.filter f l)++(List.filter (fun x => negb (f x)) l)) l.
Proof.
  induction l; simpl; auto.
  destruct (f a); simpl; auto.
  apply Permutation_sym.
  eapply Permutation_trans. 
  2: eauto.
  auto.
Qed.

End FilterProp.



(** Additional lemmas on Q *)
Require NArith.
Require ZArith.
Require QArith.
Require Qcanon.
Require BinInt.

Module Q.
  Import NArith.
  Import ZArith.
  Import QArith.
  Import Z.
(* XXX: The proofs in this module are ugly. *)

  Lemma PZMul: forall n1 n2 n3: positive, Zmult (Zpos n1) (Zpos (Pmult n2 n3)) = Zmult (Zpos (Pmult n1 n2)) (Zpos n3).
    intros n1 n2 n3; unfold Zmult; rewrite Pmult_assoc; trivial.
  Qed.

  Lemma Qplus_lt_compat: forall n1 n2 n3 n4: Q, Qlt n1 n2 -> Qlt n3 n4 -> Qlt (Qplus n1 n3) (Qplus n2 n4).
    unfold Qlt, Qplus.
    intros [n1 d1] [n2 d2] [n3 d3] [n4 d4].
    simpl.
    intros h1 h2.
    repeat ring_simplify.
    apply Zplus_lt_compat.

    rewrite (Pmult_comm d2 d4), (Pmult_comm d1 d3).
    repeat rewrite <- Zmult_assoc.
    rewrite (PZMul d3 d4 d2), (PZMul d4 d3 d1).
    rewrite (Zmult_comm (Zpos (Pmult d3 d4)) (Zpos d2)). 
    rewrite (Zmult_comm (Zpos (Pmult d4 d3)) (Zpos d1)).
    repeat rewrite Zmult_assoc.
    rewrite (Pmult_comm d4 d3).
    apply Zmult_lt_compat_r;
      [ apply gt_lt_iff; apply Zgt_pos_0 | assumption ].

    rewrite (Pmult_comm d2 d4), (Pmult_comm d1 d3).
    rewrite (Zmult_comm (Zpos (Pmult d4 d2)) n3), (Zmult_comm (Zpos (Pmult d3 d1)) n4).
    repeat rewrite <- Zmult_assoc.
    repeat rewrite <- PZMul.
    repeat rewrite Zmult_assoc.
    rewrite (Pmult_comm d2 d1).
    apply Zmult_lt_compat_r;
    [ apply gt_lt_iff; apply Zgt_pos_0 | assumption ].
  Qed.

  Lemma Qplus_eqlt_compat: forall n1 n2 n3 n4: Q, n1 = n2 -> Qlt n3 n4 -> Qlt (Qplus n1 n3) (Qplus n2 n4).
    intros [n1 d1] [n2 d2] [n3 d3] [n4 d4] h1.
    rewrite h1.
    unfold Qlt, Qplus.
    simpl.
    intro h2.
    repeat ring_simplify.
    rewrite <- (Zmult_assoc n2 (Zpos d3) (Zpos (Pmult d2 d4))), <- (Zmult_assoc n2 (Zpos d4) (Zpos (Pmult d2 d3))).
    rewrite (Pmult_comm d2 d4), (Pmult_comm d2 d3).
    rewrite (PZMul d3 d4 d2), (PZMul d4 d3 d2).
    rewrite (Pmult_comm d4 d3).
    apply Zplus_lt_compat_l.
    rewrite (Zmult_comm (Zpos (Pmult d4 d2)) n3).
    rewrite <- Zmult_assoc.
    rewrite <- (PZMul d4 d2 d2).
    rewrite Zmult_assoc.
    rewrite (Pmult_comm d3 d2).
    rewrite (PZMul d2 d2 d3).
    rewrite <- (Zmult_assoc (Zpos (Pmult d2 d2)) (Zpos d3) n4).
    rewrite (Zmult_comm (Zpos (Pmult d2 d2)) (Zmult (Zpos d3) n4)).
    rewrite (Zmult_comm (Zpos d3) n4).
    apply Zmult_lt_compat_r;
    [ apply gt_lt_iff; apply Zgt_pos_0 | assumption ].
  Qed.

End Q.

Module Qc.
  Import QArith.
  Import Qcanon.

  Lemma Qcplus_lt_compat: forall n1 n2 n3 n4: Qc,
      Qclt n1 n2 -> Qclt n3 n4 -> Qclt (Qcplus n1 n3) (Qcplus n2 n4).
    unfold Qcplus, Qclt, Q2Qc, this.
    intros [n1 nP1] [n2 nP2] [n3 nP3] [n4 nP4] h1 h2.
    repeat rewrite Qred_correct.
    apply Q.Qplus_lt_compat; assumption.
  Qed.

  Lemma Qcplus_eqlt_compat: forall n1 n2 n3 n4: Qc,
      n1 = n2 -> Qclt n3 n4 -> Qclt (Qcplus n1 n3) (Qcplus n2 n4).
    intros [n1 nP1] [n2 nP2] [n3 nP3] [n4 nP4] h1; rewrite h1.
    unfold Qcplus, Qclt, Q2Qc, this.
    repeat rewrite Qred_correct.
    apply Q.Qplus_eqlt_compat; trivial.
  Qed.

  Lemma Qcopp_lt_compat1: forall n1 n2: Qc,
                           Qclt n1 n2 -> Qclt (Qcopp n2) (Qcopp n1).
    intros n1 n2 h.
    apply (Qcplus_eqlt_compat (Qcopp n2) (Qcopp n2) n1 n2 eq_refl) in h.
    apply (Qcplus_eqlt_compat (Qcopp n1) (Qcopp n1) _ _ eq_refl) in h.
    rewrite (Qcplus_comm (Qcopp n2) n1) in h.
    rewrite (Qcplus_assoc (Qcopp n1) n1 (Qcopp n2)) in h.
    rewrite (Qcplus_comm (Qcopp n1) n1) in h.
    rewrite (Qcplus_comm (Qcopp n2) n2) in h.
    repeat rewrite Qcplus_opp_r in h.
    rewrite Qcplus_0_l, Qcplus_0_r in h.
    exact h.
  Qed.

  Lemma Qcopp_lt_compat2: forall n1 n2: Qc,
                            Qclt (Qcopp n1) (Qcopp n2) -> Qclt n2 n1.
    intros n1 n2 h.
    apply Qcopp_lt_compat1 in h.
    repeat rewrite Qcopp_involutive in h.
    exact h.
  Qed.

  Lemma Qcopp_lt_compat: forall n1 n2: Qc,
                           Qclt n1 n2 <-> Qclt (Qcopp n2) (Qcopp n1).
    exact (fun n1 n2 => conj (Qcopp_lt_compat1 n1 n2) (Qcopp_lt_compat2 n2 n1)).
  Qed.

  Lemma QcQLt: forall q1 q2: Q, Qlt q1 q2 <-> Qclt (Q2Qc q1) (Q2Qc q2).
    intros q1 q2.
    split;
      intro h.
    - apply Qclt_alt.
      unfold Qccompare.
      simpl.
      rewrite <- Qred_compare.
      assumption.
    - apply (proj1 (Qclt_alt _ _)) in h.
      unfold Qccompare in h.
      simpl in h.
      rewrite <- Qred_compare in h.
      assumption.
  Qed.

End Qc.

Require BinNums.
Require String.
Axiom posPr: BinNums.positive -> String.string.
Axiom posPrRaw: BinNums.positive -> String.string.
Axiom zPr: BinNums.Z -> String.string.
Axiom zPrRaw: BinNums.Z -> String.string.

Require List.
Import Ascii String.
Local Open Scope string_scope.

(** New line *)
Definition nl: string := String (ascii_of_nat 10%nat) EmptyString.

(** Append one character at the end of a string.
This is really not an efficient way to build a string,
build this will do for now. *)
Definition append1: string -> ascii -> string
  := fun s c => append s (String c EmptyString).

(** Concatenate the elements of a list of strings, separating each
pair of elements by [sep]. *)
Fixpoint concat (sep: string) (l: list string): string
  := match l with
       | nil => EmptyString
       | cons h1 l1 =>
         match l1 with
           | nil => h1
           | cons h2 l2 => h1 ++ sep ++ (concat sep l1)
         end
     end.

Definition substStr: string -> list string -> string
  := fun s l =>
       match l with
         | List.nil => append s "[missing arg]"
         | List.cons h _ => append s h
       end.

Fixpoint sprintfAux (s: string): list string -> string -> string
  := fun l acc =>
       match s with
         | EmptyString => acc
         | String c s1 =>
           match ascii_dec "%"%char c with
             | left _ =>
               match s1 with
                 | EmptyString => append acc "[bad %_]"
                 | String c' s2 =>
                   match ascii_dec "s"%char c' with
                     | left _ => sprintfAux s2 (List.tl l) (substStr acc l)
                     | right _ =>
                   match ascii_dec "%"%char c' with
                     | left _ => sprintfAux s2 l (append1 acc c')
                     | right _ => sprintfAux s2 l (append acc "[bad %_]")
                   end
                   end
               end
             | right _ =>
           match ascii_dec "\"%char c with
             | left _ =>
               match s1 with
                 | EmptyString => append acc "[bad \_]"
                 | String c' s2 =>
                   match ascii_dec "n"%char c' with
                     | left _ => sprintfAux s2 l (append acc nl)
                     | right _ =>
                   match ascii_dec "\"%char c' with
                     | left _ => sprintfAux s2 l (append1 acc c')
                     | right _ => sprintfAux s2 l (append acc "[bad \_]")
                   end
                   end
               end
             | right _ => sprintfAux s1 l (append1 acc c)
           end
           end
       end.

(** Poor man's implementation of [sprintf].
It only recognizes only ["%s"] and ["%%"] specifications.
For ["%s"] specification, a corresponding parameter is looked
up in the [list string] argument. ["\n"] substrings are replaced
by new line charaters. Use ["\\"] to output a backslash.
Invalid arguments (e.g. bad specifications or wrong number 
of string arguments) lead to inline errors in the output string. *)
Definition sprintf: string -> list string -> string
  := fun s l => sprintfAux s l EmptyString.

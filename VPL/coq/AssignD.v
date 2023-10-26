(* Ideas:

  We introduce a "functor" that extends any abstract domain having assume, projection, etc...
  into a domain with assignement (and non-deterministic assignement).

  Principle, if "x" is fresh in "t" and in the precondition, then
    x <- t 
  can be encoded as "assume x=t".

  Exploiting this fact, the main idea our abstract domain is the following:

    At each point of the program, each "concrete variable" [x] 
    is "abstracted" as a variable [xI x] or as variable [xO x]
    of our abstract domain.

    In other word, the "renaming" of x as [xO x] or [xI x] is 
    stored in a state of the "extended" abstract domain.
 
    Hence, a value of the "extended" abstract domain is a pair of 
    an "underlying" abstract value with a renaming from "concrete" 
    variables (e.g. "x") to "abstract" variables (e.g. "[xO x]" or "[xI x]").

    Hence, assuming that in the precondition "[renaming x] is [xO x]",
    then concrete assignement "x <- t"
    is encoded as 
      assume (xI x) = [t];
      project (xO x) ;
      renames x as [xI p] (in the extension of the underlying domain)

   We have the symmetric case when "[renaming x] is [xI x]" in the precondition.

==> Interest of this functor:
  - no need of untrusted ocaml code for assignement.
  - independent from polyhedra representation in Coq.
  - efficiency: there is no renaming inside the underlying domain except on joins and 
     inclusion test. These renaming are very similar to "phi-formula" on joins in SSA-forms.

Indeed: the technique emploied could be generalized to work with a "lazy" projection. 
This corresponds exactly to compute a SSA-form on the fly, encoded in the abstract domain !

NB: currently renaming on the underlying domain is encoded through as assume+project
    (through assignement "x <- x" actually !!!). A specific operation of renaming 
    could be interesting to improve efficiency....

*)

Require Export ASCond.
Require Import Debugging.
Require Import BinPos.
Require Import String.

Require Import MSets.MSetPositive.
Require MSetDecide.
Module PositiveSetDecide := MSetDecide.Decide(PositiveSet).
Require MSetFacts.
Module Import PositiveSetFacts:=MSetFacts.Facts(PositiveSet). 
Require Export Setoid.
Require Export Relation_Definitions.

Existing Instance PositiveSet.eq_equiv.

Module CoreAssign (N: NumSig) (Cond: ASCondSig N) (D: AbstractDomain N Cond) (R: HasRename N D). 

  Import Cond.

(* Preliminary stuffs 

 We use PositiveSets to encode renamings described above 
 (e.g. finite maps from variables to booleans).

*)

  Definition encode (b:bool) (p:positive) :=
    if b 
      then xI p
      else xO p.

  Definition decode (p:positive) :=
    match p with
      | xH => xH (* dummy value *)
      | xI p => p
      | xO p => p
    end.

  Lemma decode_encode_id b (p:positive) : decode (encode b p)=p.
  Proof.
    unfold decode, encode; case b; simpl; auto.
  Qed.

  Hint Resolve decode_encode_id: vpl.

  Definition encodeE r x := encode (PositiveSet.mem x r) x.
  Definition encodeO r x := encode (negb (PositiveSet.mem x r)) x.


  Lemma encode_unalias: forall r x x0,
    (encodeO r x) <> (encodeE r x0).
  Proof.
    unfold encodeO, encodeE; intros r x x0;  case (PVar.eq_dec x0 x).
    - intros; subst; destruct (PositiveSet.mem x r); simpl; discriminate.
    - intros H1 H2; case H1; generalize H2; clear H1 H2.
    destruct (PositiveSet.mem x r); destruct (PositiveSet.mem x0 r); simpl; intro H; inversion H; auto.
  Qed.
  Hint Resolve encode_unalias: vpl.

(* USEFULL for a better projection

Lemma encodeE_diff_xO: forall r x,
  (encodeE r x)<>(xO x) -> encodeE r x = xI x.
Proof.
  unfold encodeE. intros r x; case (PositiveSet.mem x r); simpl; auto.
  intro H; case H; auto.
Qed.

*)

(* Below: "aux" is a state on the "encoded" variables (of the underlying domain).
              it speaks about "ghost" variables.
          "m" is a state on the concrete variables
             
   (decodeIn r aux) thus maps a state "m" on the concrete variables
                              into a state on the "encoded" variables 
         - an encoded variable "p" that is constrained by the underlying domain
             is associated to "m (decode p)"
         - an encoded variable "p" that is not constrainted by the underlying domain
             is associated to "aux p"   
 
   Hence: "aux" expresses the value of the encoded variables that are not constrained !
     Our "gamma", defined below, explicits that values of "aux" are irrelevant.

   See: the full concretization "gamma" below
*)
  Definition decodeIn (r:PositiveSet.t) (aux m: Mem.t N.t) (p:positive) :=
    match p with
      | xH => (aux xH) (* remark: this explicits that xH is never used in the abstract domain *)
      | xI p => if PositiveSet.mem p r then m p else aux (xI p) 
      | xO p => if PositiveSet.mem p r then aux (xO p) else m p
    end.

  Lemma decode_encodeE r aux m x: decodeIn r aux m (encodeE r x) = m x.
  Proof.
    unfold decodeIn, encodeE, encode.
    elimtype (exists b, (PositiveSet.mem x r)=b); eauto.
    intro b; destruct b; intro H; rewrite H; simpl; rewrite H; simpl; auto.
  Qed.

  Hint Resolve decode_encodeE: vpl.
  Hint Rewrite decode_encodeE: vpl.

  Local Opaque PositiveSet.mem.

  Lemma decode_diff_encodeE r aux m x: x <> (encodeE r (decode x)) -> decodeIn r aux m x = aux x.
  Proof.
    unfold decodeIn, encodeE, encode; destruct x as [p | p | ]; simpl;
      try (destruct (PositiveSet.mem p r); simpl; intuition).
    destruct (PositiveSet.mem 1%positive r); simpl; auto.
  Qed.

  Lemma decode_encodeO r aux m x: decodeIn r aux m (encodeO r x) = aux (encodeO r x).
  Proof.
    unfold decodeIn, encodeO, encode.
    elimtype (exists b, (PositiveSet.mem x r)=b); eauto.
    intro b; destruct b; intro H; rewrite H; simpl; rewrite H; simpl; auto.
  Qed.

  Hint Rewrite decode_encodeO: vpl.

  Lemma decodeIn_simplify r aux1 m1 aux2 m2 x: 
    (x=(encodeE r (decode x)) -> m1 (decode x) = m2 (decode x))
    ->(x<>(encodeE r (decode x)) -> aux1 x = aux2 x)
    -> decodeIn r aux1 m1 x = decodeIn r aux2 m2 x.
  Proof.
    unfold decodeIn, encodeE, encodeO, encode; destruct x as [ p | p | ]; simpl;
      try (destruct (PositiveSet.mem p r); simpl; intros H H0; try (apply H0; intro; discriminate); intuition). 
    case (PositiveSet.mem 1 r); simpl; intros H H0; try (apply H0; intro; discriminate); intuition.
  Qed.


(* USEFUL for a better projection !

Lemma remove_id x r: PositiveSet.mem x (PositiveSet.remove x r) = false.
Proof.
  generalize (PositiveSet.remove_spec r x x).
  unfold PositiveSet.In; case (PositiveSet.mem x (PositiveSet.remove x r)); simpl; intuition.
Qed.
Hint Rewrite remove_id: vpl.

Lemma remove_diff x r y: y<>x -> PositiveSet.mem y (PositiveSet.remove x r) = PositiveSet.mem y r.
Proof.
  intros H; generalize (PositiveSet.remove_spec r x y);
  unfold PositiveSet.In. 
  destruct (PositiveSet.mem y r);
  destruct (PositiveSet.mem y (PositiveSet.remove x r)); intuition; try discriminate; auto.
Qed.

*)

(* Our atomic assignement on renaming is "switch" *)

  Fixpoint switch (m:PositiveSet.t) (i: positive) : PositiveSet.t :=
    match m with
      | PositiveSet.Leaf => PositiveSet.add i PositiveSet.Leaf
      | PositiveSet.Node l o r =>
        match i with
          | xH => PositiveSet.node l (negb o) r
          | xO p => PositiveSet.node (switch l p) o r
          | xI p => PositiveSet.node l o (switch r p)
        end
    end.

  Local Opaque PositiveSet.node.
  Local Transparent PositiveSet.mem.

  Lemma switch_out m: forall x y,  y<>x -> PositiveSet.mem y (switch m x) = PositiveSet.mem y m.
  Proof.
    induction m; simpl.
    + intros x y H. generalize (PositiveSet.add_spec PositiveSet.Leaf x y).
      unfold PositiveSet.In; simpl.
      destruct (PositiveSet.mem y (PositiveSet.add x PositiveSet.Leaf));
      intuition.
    + intro x; destruct x; simpl; intros y; rewrite PositiveSet.mem_node; 
      destruct y; simpl; intuition.
  Qed. 

  Lemma switch_in m: forall x, PositiveSet.mem x (switch m x) = negb (PositiveSet.mem x m).
  Proof.
    induction m; simpl.
    + intros x; generalize (PositiveSet.add_spec PositiveSet.Leaf x x).
    unfold PositiveSet.In; simpl.
    cutrewrite (PositiveSet.mem x PositiveSet.Leaf = false); simpl.
    - destruct (PositiveSet.mem x (PositiveSet.add x PositiveSet.Leaf));
      intuition.
    - case x; simpl; auto.
    + intro x; destruct x; rewrite PositiveSet.mem_node; simpl; auto.
  Qed.
  Hint Rewrite switch_in: vpl.

  Local Opaque switch PositiveSet.mem.

  Lemma decode_sw_encodeE r aux m x:
    decodeIn (switch r x) aux m (encodeE r x) = aux (encodeE r x).
  Proof.
    unfold decodeIn, encodeE, encode.
    elimtype (exists b, (PositiveSet.mem x r)=b); eauto.
    intro b; destruct b; intro H; rewrite H; simpl; rewrite switch_in;  rewrite H; simpl; auto.
  Qed.

  Lemma decode_sw_encodeO r aux m x:
    decodeIn (switch r x) aux m (encodeO r x) = m x.
  Proof.
    unfold decodeIn, encodeO, encode.
    elimtype (exists b, (PositiveSet.mem x r)=b); eauto.
    intro b; destruct b; intro H; rewrite H; simpl; rewrite switch_in;  rewrite H; simpl; auto.
  Qed.
  Hint Rewrite decode_sw_encodeE decode_sw_encodeO: vpl.

  Lemma decode_sw_out r aux m x y:
    y <> (encodeE r x) -> y <> (encodeO r x) ->
    decodeIn (switch r x) aux m y = 
    decodeIn r aux m y.
  Proof.
    unfold decodeIn, encodeE, encodeO, encode.
    elimtype (exists b, (PositiveSet.mem x r)=b); eauto.
    intro b; destruct b; intro H; rewrite H; simpl;
      destruct y; intros H0 H1; try (rewrite switch_out); auto.
  Qed.

(* Abstract domain *)

  Record assignDomain := 
    mk { pol: D.t ;
      renaming:  PositiveSet.t 
    }.

  Definition t:=assignDomain.

  Definition gamma (a:t) m := forall aux, D.gamma (pol a) (decodeIn (renaming a) aux m).

(* NO MORE NEEDED FOR BoundVarD

  Instance mdo: MayDependOn := {| mayDependOn:=fun a x => mayDependOn (pol a) (encodeE (renaming a) x)  |}.
  Hint Immediate D.gamma_mdo: pedraQ.

  Instance gamma_mdo: mdoExt gamma iff.
  Proof.
    assert (mdoExt gamma Program.Basics.impl); auto with progvar.
    unfold gamma, Basics.impl. constructor 1. 
    + intros e m1 m2 H H0 aux; erewrite <- eval_mdo_compat.
    eapply (H0 aux).
    auto with pedraQ.
    unfold bExt in * |- *; intros.
    apply decodeIn_simplify; eauto.
    intros X; rewrite X.
    unfold encodeE.
    rewrite decode_encode_id.
    eapply H.
    unfold mayDependOn; simpl. rewrite <- X; auto.
    +  intros e x m1 m2 H H0 H1 aux; erewrite <- eval_diff_compat.
    eapply (H1 aux).
    auto with pedraQ.
    unfold not; unfold mayDependOn in * |-; simpl in * |-; eauto.
    unfold bExt in * |- *; intros.
    apply decodeIn_simplify; eauto.
    intros X; rewrite X.
    unfold encodeE.
    rewrite decode_encode_id.
    eapply H0.
    intro Y; subst x; auto.
  Qed.
*)

  Instance decodeIn_compat : Proper (PositiveSet.Equal ==>
    pointwise_relation PVar.t Logic.eq ==>
    pointwise_relation PVar.t Logic.eq ==>
    pointwise_relation PVar.t Logic.eq) decodeIn.
  Proof.
    intros r1 r2 H1 aux1 aux2 H2 m1 m2 H3 x; subst.
    destruct x as [ p | p |]; simpl; try congruence;
        rewrite H1; case (PositiveSet.mem p r2); simpl; auto.
  Qed.

  Instance gamma_ext: Proper (Logic.eq ==> pointwise_relation PVar.t Logic.eq ==> iff) gamma.
  Proof.
     eapply sat_compat_iff; unfold gamma.
     intros x y H m1 m2 H0 H1 aux. rewrite <- H. rewrite <- H0; auto.
  Qed.

(* straight-forward lifting of operations *)

  Definition top: t
    := {| pol := D.top ; renaming := PositiveSet.empty |}.

  Lemma top_correct: forall m, gamma top m.
    unfold gamma; simpl; auto with vpl.
  Qed.

  Definition bottom: t
    := {| pol := D.bottom ; renaming := PositiveSet.empty |}.

  Lemma bottom_correct m: gamma bottom m -> False.
    unfold gamma; simpl; intros.
    eapply D.bottom_correct.
    eapply (H m).
  Qed.

  Open Scope impure.
 
  Definition isBottom : t -> imp bool
    := fun p => D.isBottom (pol p).

  Lemma isBottom_correct : forall a, If isBottom a THEN forall m, gamma a m -> False.
  Proof.
    unfold isBottom.
    VPLAsimplify.
    Grab Existential Variables.
    exact m.
  Qed.

  Definition assume (c:cond) (a: t) : imp t :=
  BIND res <-  D.assume (map c (encodeE (renaming a))) (pol a) -;
  pure {| pol := res ; 
          renaming := renaming a |}.

  Hint Unfold pointwise_relation.

  Lemma assume_correct (c:cond) (a:t): WHEN p <- assume c a THEN 
    forall m, (sat c m) -> (gamma a m) -> gamma p m.
  Proof.
    unfold gamma, assume; VPLAsimplify. simpl in * |- *.
    intros m H0 H1 aux; eapply H; auto.
    rewrite sat_map.
    erewrite (eval_pointwise_compat sat_mdo); eauto with vpl.
  Qed.
  Hint Resolve assume_correct: vpl.

  Definition assert (c:cond) (a: t) : imp bool := D.assert (map c (encodeE (renaming a))) (pol a).

  Lemma assert_correct (c:cond): forall (a:t), If assert c a THEN forall m, (gamma a m) -> (sat c m).
  Proof.
    unfold gamma, assert. VPLAsimplify.
    intros HX m H0. generalize (H _ (H0 m)).
    rewrite sat_map.
    intros; erewrite (eval_pointwise_compat sat_mdo); eauto with vpl.
  Qed.
  Hint Resolve assert_correct: vpl.

(* projection *)

  Definition project (a:t) (x:PVar.t) : imp t 
    :=  
     BIND res <-  D.project (pol a) (encodeE (renaming a) x) -;
     pure {| pol := res ; renaming := (renaming a) |}.

  Lemma project_correct a x: WHEN p <- project a x THEN forall m v, gamma a m -> gamma p (Mem.assign x v m).
  Proof.
    unfold project, gamma. VPLAsimplify. simpl in * |- *.
    intros m v H0 aux.
    eapply D.gamma_ext; [ eauto | idtac | idtac ].
    Focus 2.
    + eapply D.project_correct with (m:=decodeIn (renaming a) aux m) (v:=v);
      eauto.
    + intro x'; unfold Mem.assign at 2.
    case (PVar.eq_dec (encodeE (renaming a) x) x').
    - intro; subst. autorewrite with progvar vpl; auto.
    - intros; apply decodeIn_simplify; auto with vpl.
    intros; rewrite Mem.assign_out; auto.   
    intro; subst x; intuition.
  Qed.

(* TODO: a better projection !

Definition project (a:t) (x:PVar.t) : t 
  := {| pol := D.project (pol a) (encodeE (renaming a) x) ;
        renaming := PositiveSet.remove x (renaming a) |}.
 

Lemma project_correct a x m v: gamma a m -> gamma (project a x) (Mem.assign x v m).
Proof.
 unfold gamma. simpl.
 intros H aux.
    eapply (eval_pointwise_compat _ iff (eval_mdo:=D.gamma_mdo)); [ eauto | idtac | idtac ].
    Focus 2.
    + refine (D.project_correct _ _ (decodeIn (renaming a) aux 
                                     (if PVar.eq_dec (encodeE (renaming a) x) (xO x)
                                      then m
                                      else ???
                                     ))
                                     (if PVar.eq_dec (encodeE (renaming a) x) (xO x)
                                      then v 
                                      else (aux (encodeE (renaming a) x))) _).
     eauto.
   + intro x'; unfold Mem.assign at 2.
        case (PVar.eq_dec (encodeE (renaming a) x) x').
        - intro; subst.
          case (PVar.eq_dec (encodeE (renaming a) x) (xO x)).
          * intro X; rewrite X; simpl; autorewrite with progvar vpl; auto.
          * intro; rewrite encodeE_diff_xO; simpl; autorewrite with progvar vpl; auto.
       -  destruct x'; simpl; auto;
            (case (PVar.eq_dec x x') ; [
               try (intro; subst; autorewrite with vpl; simpl;
               unfold encodeE; destruct (PositiveSet.mem x' (renaming a)); simpl; 
               autorewrite with progvar; intuition auto; fail) 
            |
               intros; rewrite remove_diff; auto; rewrite Mem.assign_out; auto
            ]).
               intro; subst. autorewrite with vpl; simpl.
           unfold encodeE; destruct (PositiveSet.mem x' (renaming a)); simpl; autorewrite with progvar; auto.
     
Qed.
*)

(* Assignements *)

  Definition guassignAux x (c:cond) (a: t) : imp t :=
    let a:=trace DEBUG "guassign called"%string a in
    BIND tmp <- D.assume c (pol a) -;
    BIND aux <- D.project tmp (encodeE (renaming a) x) -;
    pure  {| pol := aux ; renaming := switch (renaming a) x |}.

  Lemma guassignAux_correct x c a:
    let f:=(encodeE (renaming a)) in
    let c1:=(xmap c f (Mem.assign x (encodeO (renaming a) x) f)) in
    WHEN p <- guassignAux x c1 a THEN
        forall m v, 
          xsat c m (Mem.assign x v m) ->
          gamma a m -> 
            gamma p (Mem.assign x v m).
  Proof.
    simpl; unfold guassignAux, trace; VPLAsimplify. simpl in * |- *. unfold gamma; intros m v Hxsat H1 aux.
    eapply D.gamma_ext; [ eauto | idtac | idtac ].
    Focus 2.
    refine (H0 (decodeIn (renaming a) (Mem.assign (encodeO (renaming a) x) v aux) _) (aux (encodeE (renaming a) x)) _).
      eapply H; eauto.
    rewrite <- xsat_sat.
    rewrite xsat_xmap.
    erewrite (eval_pointwise_compat (xsat_old_mdo _)); eauto.
    erewrite (eval_pointwise_compat (xsat_new_mdo _)); eauto.
    - intros x'; simpl. autorewrite with vpl; auto.
    - intros x'. unfold Mem.assign at 2.
    case (PVar.eq_dec (encodeE (renaming a) x) x'); simpl.
    * intro; subst. autorewrite with vpl; auto.
    * intro H2. case (PVar.eq_dec x' (encodeO (renaming a) x)).
      + intros; subst; autorewrite with progvar vpl; auto.
      + intro H3; rewrite decode_sw_out; auto.
        apply decodeIn_simplify; auto with vpl.
        intros; rewrite Mem.assign_out; auto.   
        intro; subst x; intuition.
        rewrite Mem.assign_out; auto.
    - intro x'. unfold Mem.assign at 2 3.
    case (PVar.eq_dec x x'); intros; autorewrite with progvar vpl; auto.
  Qed.

  Definition guassign x (c:cond) (a: t) : imp t :=   
    let f:=(encodeE (renaming a)) in
      let c1:=(xmap c f (Mem.assign x (encodeO (renaming a) x) f)) in
        guassignAux x c1 a.

  Local Hint Resolve guassignAux_correct: vpl.
  Opaque guassignAux.

  Lemma guassign_correct x c a:
    WHEN p <- guassign x c a THEN forall m v,
    xsat c m (Mem.assign x v m) ->
    gamma a m ->  gamma p (Mem.assign x v m).
  Proof.
    VPLAsimplify.
  Qed.

  Definition assign x te (a: t) : imp t := 
    let c:=(Atom Eq (Term.Var (encodeO (renaming a) x)) (Term.Old (Term.map te (encodeE (renaming a))))) in
      guassignAux x c a.

  Lemma assign_correct (x: PVar.t) (te: Term.t) (a:t): WHEN p <- assign x te a THEN 
     forall m, gamma a m -> gamma p (Mem.assign x (Term.eval te m) m).
  Proof.
    generalize (guassignAux_correct x (Atom Eq (Term.Var x) (Term.Old te)) a).
    simpl. VPLAsimplify.
    autorewrite with progvar in H.
    intros; eapply H; eauto with progvar.  
  Qed.
  Hint Resolve guassign_correct assign_correct: vpl.  

(* Auxiliary definitions of inclusion "isIncl" and join 
     We recover here a form "phi"-assignement like in SSA-form.
*)

  Definition nop (x: PVar.t) a : imp t :=  
    (* below, this code is an optimized version of "assign x (Term.Var x) a" *)
    BIND res <- R.rename (encodeE (renaming a) x) (encodeO (renaming a) x) (pol a) -;
    pure {| pol := res ; renaming := switch (renaming a) x |}.
   
  Lemma nop_correct (x: PVar.t) (a:t): 
    WHEN p <- nop x a THEN forall m, gamma a m -> gamma p m.
  Proof.
    unfold nop, gamma; VPLAsimplify.
    intros m H0 aux; eapply R.rename_correct; eauto.
    autorewrite with vpl.
    eapply D.gamma_ext; [ eauto | idtac | eapply H0 with (aux:=Mem.assign (encodeO (renaming a) x) (m x) aux) ].
    intros x0.
    case (PVar.eq_dec (encodeE (renaming a) x) x0).
    - intros; subst; autorewrite with progvar vpl; auto.
    - intros. rewrite Mem.assign_out; auto.
      case (PVar.eq_dec (encodeO (renaming a) x) x0).
      + intros; subst; autorewrite with progvar vpl; auto.
      + intros. rewrite decode_sw_out; auto.
        intros; apply decodeIn_simplify; auto.
        intros; rewrite Mem.assign_out; auto.
  Qed.
  Local Hint Resolve nop_correct: vpl.

  Lemma nop_effect_1 (x: PVar.t) (a:t): WHEN p <- nop x a THEN PositiveSet.mem x (renaming p) = negb (PositiveSet.mem x (renaming a)). 
  Proof.
    unfold nop; xasimplify idtac.
    autorewrite with vpl.
    destruct (PositiveSet.mem x (renaming a)); simpl; intuition.
  Qed.

  Lemma nop_effect_2 (x y: PVar.t) (a:t): x <> y -> WHEN p <- nop x a THEN PositiveSet.mem y (renaming p) = (PositiveSet.mem y (renaming a)). 
  Proof.
    unfold nop; xasimplify idtac.
    intros; rewrite switch_out; intuition.
  Qed.

  Local Opaque nop.

  Definition switchAll (r:PositiveSet.t) (a:t) : imp t :=
    PositiveSet.fold (fun x0 k => bind k (nop x0))
                     r 
                     (pure a).

  (* TODO: this proof could probably be simplified through xfold with an explicit reasoning on path
        instead of lists without duplicates.
     See PositiveMapAddOn.v 
  *)
  Lemma switchAll_correct r (a:t): WHEN p <- switchAll r a THEN forall m, gamma a m -> gamma p m.
  Proof.
    unfold switchAll; rewrite PositiveSet.fold_spec.
    eapply wlp_forall; intro m.
    eapply wlp_forall; intro H.
    cut (WHEN p <- pure a THEN gamma p m).
    clear H.
    cut (forall x : PVar.t,
      PositiveSet.InL x (PositiveSet.elements r) ->
      PositiveSet.In x r).
    generalize (PositiveSet.elements_spec2w r).
    unfold PositiveSet.E.eq.
    generalize (PositiveSet.elements r).
    intros l H. generalize (pure a); clear a.
    induction H as [| a0 l H H0 IHl]; simpl.
    - auto.
    - intros. eapply IHl; eauto.
      VPLAsimplify.
    - intros; rewrite <- PositiveSet.elements_spec1; auto.
    - VPLAsimplify.
  Qed.

  Hint Rewrite SetoidList.InA_nil SetoidList.InA_cons: vplx.
  Hint Rewrite nop_effect_1: vplx. 

  Lemma bool_eq_False b1 b2: (False <-> (b1=b2)) <-> b1 = negb b2.
  Proof.
    case b1; case b2; simpl; intuition.
  Qed.

  Lemma negb_negb b : negb (negb b) = b.
  Proof.
    case b; simpl; auto.
  Qed.

  Hint Rewrite bool_eq_False negb_negb: vplx.   

  (* TODO: this proof could probably be simplified through xfold with an explicit reasoning on path
        instead of lists without duplicates.
     See PositiveMapAddOn.v 
  *)
  Lemma switchAll_effect r a x: 
    WHEN p <- switchAll r a THEN
      (PositiveSet.In x r) <-> (PositiveSet.mem x (renaming p)) = negb (PositiveSet.mem x (renaming a)).
  Proof.
    assert (WHEN p <- switchAll r a THEN
      PositiveSet.InL x (PositiveSet.elements r) <-> (PositiveSet.mem x (renaming p)) = negb (PositiveSet.mem x (renaming a))).
    unfold switchAll. 
    rewrite PositiveSet.fold_spec.
    generalize (PositiveSet.elements_spec2w r).
    unfold PositiveSet.E.eq.
    generalize (PositiveSet.elements r).
    intros l H; generalize a; clear a.
    * induction H as [| x0 l H H0 IHl]; simpl; intro a. 
    - VPLAsimplify. rewrite SetoidList.InA_nil, bool_eq_False, negb_negb. auto.
    - apply wlp_List_fold_left.
      VPLAsimplify. 
      simpl in * |- *. intros H2; clear IHl.
      rewrite SetoidList.InA_cons.
      case (PVar.eq_dec x x0).
      + intro; subst.
        assert (X: (SetoidList.InA eq x0 l) <-> False).
        intuition.
        rewrite X in * |- *; clear X.
        rewrite bool_eq_False, negb_negb in H2.
        rewrite H2; clear H2; intuition.
        apply nop_effect_1; auto.
       + intros.
         rewrite H2; clear H2.
         generalize exta Hexta; clear exta Hexta H1 Hexta0.
         eapply wlp_monotone. 
         eapply nop_effect_2; eauto.
         simpl. intros a1 H1 H2; rewrite H2; clear H2.
         intuition.
    * VPLAsimplify. simpl.
      intros a0; rewrite <- (PositiveSet.elements_spec1 r). auto.
  Qed.


  Lemma switchAll_effect_set r1 a: 
       WHEN p <- (switchAll r1 a) THEN
         let r2:=(renaming a) in 
         PositiveSet.Equal (renaming p) (PositiveSet.union (PositiveSet.diff r2 r1) (PositiveSet.diff r1 r2)).
  Proof.
    unfold PositiveSet.Equal.
    apply wlp_forall. intros x. 
    elimtype (exists r2, r2=(renaming a)); eauto.
    intros r2 H.
    eapply wlp_monotone.
    eapply switchAll_effect with (x:=x).
    simpl; intros p. generalize
      (PositiveSet.diff_spec r2 r1 x)
      (PositiveSet.diff_spec r1 r2 x)
      (PositiveSet.union_spec (PositiveSet.diff r2 r1) (PositiveSet.diff r1 r2) x).
    unfold PositiveSet.In; rewrite <- H; clear H.
    generalize (PositiveSet.mem x (renaming p)); intro b1.
    generalize (PositiveSet.mem x (PositiveSet.diff r2 r1)); intro b2.
    generalize (PositiveSet.mem x r2); intro b3.
    generalize (PositiveSet.mem x (PositiveSet.diff r1 r2)); intro b4.
    generalize (PositiveSet.mem x
      (PositiveSet.union (PositiveSet.diff r2 r1) (PositiveSet.diff r1 r2))); intro b5.
    generalize (PositiveSet.mem x r1); intro b6.
    generalize (PositiveSet.mem x r2); intro b7.
    destruct b1, b2, b3, b4, b5, b6; simpl; intuition.
  Qed.


  Lemma switchAll_prop1 r a:
      WHEN p <- switchAll (PositiveSet.diff (renaming a) r) a THEN
        PositiveSet.Equal (renaming p) (PositiveSet.inter (renaming a) r).
  Proof.
    eapply wlp_monotone.
    eapply switchAll_effect_set.
    simpl.
    PositiveSetDecide.fsetdec.
  Qed.

  Lemma switchAll_prop2 r1 r2 a: 
    WHEN p <- switchAll (PositiveSet.diff r2 r1) a THEN
      (PositiveSet.Equal (renaming a) (PositiveSet.inter r1 r2) 
      -> PositiveSet.Equal (renaming p) r2).
  Proof.
    eapply wlp_monotone.
    eapply switchAll_effect_set.
    simpl.    
    PositiveSetDecide.fsetdec.
  Qed.

(* inclusion *)

  Definition isIncl (a1 a2:t): imp bool
    := let r1 := (PositiveSet.diff (renaming a1) (renaming a2)) in
       let r2 := (PositiveSet.diff (renaming a2) (renaming a1)) in
       BIND aux1 <- switchAll r1 a1 -;
       BIND aux2 <- switchAll r2 aux1 -;
        D.isIncl (pol aux2) (pol a2).

  Lemma isIncl_correct a1 a2: If isIncl a1 a2 THEN forall m, gamma a1 m -> gamma a2 m.
  Proof.
    VPLAsimplify.
    intros HX m H0; assert (X: gamma exta0 m).
    - repeat (eapply switchAll_correct; eauto).
    - clear HX H0.
      unfold gamma.
      intros aux; generalize (X aux); clear X.
      cut (PositiveSet.Equal (renaming exta0) (renaming a2)).
      + intros X1 X2.
        rewrite <- X1; auto.
      + eapply switchAll_prop2; eauto.
        eapply switchAll_prop1; eauto.
  Qed.

  Definition join (a1 a2:t): imp t 
    :=  let r1 := (PositiveSet.diff (renaming a1) (renaming a2)) in
        let r2 := (PositiveSet.diff (renaming a2) (renaming a1)) in 
        BIND aux1 <- switchAll r1 a1 -;
        BIND aux2 <- switchAll r2 a2 -;
        BIND res <- D.join (pol aux1) (pol aux2) -;
        pure {| pol := res ; renaming := PositiveSet.inter (renaming a1) (renaming a2) |}.

  Lemma join_correct a1 a2: WHEN p <- join a1 a2 THEN forall m, gamma a1 m \/ gamma a2 m -> gamma p m.
  Proof.
    unfold join; VPLAsimplify. simpl in * |- *.
    intros m H0 aux; simpl.
    case H0; clear H0; intro H0.
    * assert (H1: gamma exta m).
      eapply switchAll_correct; eauto.
      unfold gamma in H1.
      generalize (switchAll_prop1 (renaming a2) a1 _ Hexta).
      intro H2; rewrite <- H2; clear H2.
      eauto.
    * assert (H1: gamma exta0 m).
      eapply switchAll_correct; eauto.
      unfold gamma in H1.
      generalize (switchAll_prop1 (renaming a1) a2 _ Hexta0).
      intro X.
      eapply D.gamma_ext; [ eauto | idtac | eauto ].
      intros x; eapply decodeIn_compat; auto.
      rewrite X.
      PositiveSetDecide.fsetdec.
  Qed.

 (* widening (calqué sur le join) *)
  Definition widen (a1 a2:t) : imp t :=
    let r1 := (PositiveSet.diff (renaming a1) (renaming a2)) in
    let r2 := (PositiveSet.diff (renaming a2) (renaming a1)) in 
    BIND aux1 <- switchAll r1 a1 -;
    BIND aux2 <- switchAll r2 a2 -;
    BIND res <- D.widen (pol aux1) (pol aux2) -;
    pure  {| pol := res ; renaming := PositiveSet.inter (renaming a1) (renaming a2) |}.

  Global Opaque assign join assume isIncl assert guassign project.
  Hint Resolve isIncl_correct top_correct join_correct bottom_correct project_correct
    assign_correct guassign_correct: vpl.


  Definition rename x y a := 
    BIND r <- R.rename (encodeE (renaming a) x) (encodeE (renaming a) y) (pol a) -;
    pure {| pol := r ; renaming := renaming a |}.

  Lemma rename_correct x y a: 
    WHEN p <- (rename x y a) THEN
    (forall m, gamma a (Mem.assign x (m y) m) -> gamma p m).
  Proof.
    unfold gamma; VPLAsimplify.
    intros m H0 aux.
    eapply R.rename_correct; eauto.
    autorewrite with vpl.
    eapply D.gamma_ext; [ eauto | idtac | idtac ].
    Focus 2.
    + eapply (H0 aux);
      eauto.
    + intro x'; unfold Mem.assign at 1.
    case (PVar.eq_dec (encodeE (renaming a) x) x').
    - intro; subst. autorewrite with progvar vpl; auto.
    - intros; apply decodeIn_simplify; auto with vpl.
    intros; rewrite Mem.assign_out; auto.
    intro; subst x; intuition.
  Qed.
  Local Hint Resolve rename_correct: vpl.

End CoreAssign.

(* An interface derived from "CoreAssign" *)
Module Type CoreAssignSig (N: NumSig) (Cond: ASCondSig N) (D: AbstractDomain N Cond) (R: HasRename N D).

  Include CoreAssign N Cond D R.

End CoreAssignSig.


Module MakeAssign (N: NumSig) (Cond: ASCondSig N) (D: AbstractDomain N Cond) (R: HasRename N D) <: FullAbstractDomain N Cond
  := CoreAssign N Cond D R.


(* An extension of CoreAssign with getItvMode *)
Module AssignLiftItv (N: NumSig) (Cond: ASCondSig N) (I: ItvSig N) 
   (D: AbstractDomain N Cond) (R: HasRename N D) (DI: HasGetItvMode N Cond.Term I D)
   (CD: CoreAssignSig N Cond D R) <: HasGetItvMode N Cond.Term I CD.

  Import Cond DI.
  Import CD.

  Definition getItvMode mo (te:Term.t) (a:t) := getItvMode mo (Term.map te (encodeE (renaming a))) (pol a).

  Lemma getItvMode_correct mo (te: Term.t) (a: t): WHEN i <- getItvMode mo te a THEN
    forall m, gamma a m -> I.sat i (Term.eval te m).
  Proof.
    unfold getItvMode, gamma. VPLAsimplify. simpl. 
    (* eliminate variable aux *) intros H m H0; generalize (H0 m); clear H0; intro H0.
    erewrite f_equal; eauto with vpl.
    erewrite Term.eval_map. 
    apply (eval_pointwise_compat Term.eval_mdo); auto.
    intros x; autorewrite with vpl; auto.
  Qed.

End AssignLiftItv.

Module AssignSimplePrinting (N: NumSig) (Cond: ASCondSig N) (D: AbstractDomain N Cond) (R: HasRename N D) (DP: HasSimplePrinting N D)
   (Import CD: CoreAssignSig N Cond D R) <: HasSimplePrinting N CD with Definition rep := DP.rep.

  Definition pr (a:t) := DP.pr (pol a).

  Definition to_string (f: PVar.t -> String.string) (a:t) := DP.to_string (fun x => f (decode x)) (pol a).

  Definition rep := DP.rep.

  Definition backend_rep (a:t) := 
    match DP.backend_rep (pol a) with
    | None => None
    | Some (r, (fa, fu)) => Some(r, (fun x => encodeE (renaming a) (fa x), fun x => fu (decode x)))
    end.

  Lemma backend_rep_correct: 
     forall a, (WHEN r <- backend_rep a THEN forall x, (snd (snd r) (fst (snd r) x) = x))%option.
  Proof.
     VPLAsimplify. intros x. unfold encodeE. rewrite decode_encode_id. auto.
  Qed.

  (** meet copy-past on join. TODO: an intermediate definition avoiding copy-paste ! *)
  Definition meet (a1 a2:t): imp t 
    :=  let r1 := (PositiveSet.diff (renaming a1) (renaming a2)) in
        let r2 := (PositiveSet.diff (renaming a2) (renaming a1)) in 
        BIND aux1 <- switchAll r1 a1 -;
        BIND aux2 <- switchAll r2 a2 -;
        BIND res <- DP.meet (pol aux1) (pol aux2) -;
        pure {| pol := res ; renaming := PositiveSet.inter (renaming a1) (renaming a2) |}.

  Lemma meet_correct a1 a2: WHEN p <- meet a1 a2 THEN forall m, gamma a1 m -> gamma a2 m -> gamma p m.
  Proof.
    unfold meet; VPLAsimplify. simpl in * |- *.
    intros m H0 H1; simpl.
    assert (H0': gamma exta m).
    eapply switchAll_correct; eauto.
    assert (H1': gamma exta0 m).
    eapply switchAll_correct; eauto.
    unfold gamma; simpl.
    intros aux; apply H; clear H.
    unfold gamma in H0', H1'.
    * generalize (switchAll_prop1 (renaming a2) a1 _ Hexta).
      intro H2; rewrite <- H2; clear H2.
      eauto.
    * generalize (switchAll_prop1 (renaming a1) a2 _ Hexta0).
      intro X.
      eapply D.gamma_ext; [ eauto | idtac | eauto ].
      intros x; eapply decodeIn_compat; auto.
      rewrite X.
      PositiveSetDecide.fsetdec.
  Qed.

End AssignSimplePrinting.



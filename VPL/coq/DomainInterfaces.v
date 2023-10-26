(** Version of the main interfaces in VPL hierarchy 
    where the backend is not trusted to be pure.
*)

Require Export NumC.
Require Export ProgVar.
Require Export Debugging.
Require Export PedraQBackend.

Create HintDb vpl discriminated.

Ltac VPLTsimplify :=
  xtsimplify ltac:(eauto with vpl).

Ltac VPLAsimplify :=
  xasimplify ltac:(eauto with vpl).

(* TODO: cut BasicDomain in smaller pieces ? *)

Module Type BasicDomainG (Import Imp: FullImpureMonad) (N: NumSig).

  Parameter t: Type.

  Parameter gamma: t -> Mem.t N.t -> Prop.

  Declare Instance gamma_ext: Proper (Logic.eq ==> pointwise_relation PVar.t Logic.eq ==> iff) gamma.

  Parameter isIncl: t -> t -> imp bool.
  Parameter isIncl_correct: forall a1 a2, If (isIncl a1 a2) THEN (forall m, gamma a1 m -> gamma a2 m).

  Parameter top: t.
  Parameter top_correct: forall m, gamma top m.

  Parameter join: t -> t -> imp t.
  Parameter join_correct: forall a1 a2, WHEN p <- join a1 a2 THEN (forall m, gamma a1 m \/ gamma a2 m -> gamma p m).

  Parameter widen: t -> t -> imp t.

  Parameter bottom: t.
  Parameter bottom_correct: forall m, (gamma bottom m)->False.

  Parameter isBottom: t -> imp bool.
  Parameter isBottom_correct: forall a, If isBottom a THEN (forall m, (gamma a m)->False).

  Parameter project: t -> PVar.t -> imp t.
  Parameter project_correct: forall a x, WHEN p <- project a x THEN (forall m v, gamma a m -> gamma p (Mem.assign x v m)).

  Hint Resolve isIncl_correct top_correct join_correct bottom_correct project_correct: vpl.
  Hint Resolve isBottom_correct: vpl.

End BasicDomainG.


Module Type BasicDomain (N: NumSig).
  Include BasicDomainG ImpureConfig.Core N.
End BasicDomain.


Module Type HasSimplePrinting (N: NumSig) (Import D: BasicDomain N).

  Parameter pr: t -> String.string.

  Parameter to_string: (PVar.t -> String.string) -> t -> String.string.

  (* Returns the backend representation together with a renaming variable from "user" names.
     This renaming is given as pair a: user -> actual, u: actual -> user
     such that u(a(x))=x (hence a is injective and u is surjective).
  *)
  Parameter rep: Type.

  Parameter backend_rep: t -> option (rep * ((PVar.t -> PVar.t) * (PVar.t -> PVar.t))).

  Parameter backend_rep_correct: 
     forall a, (WHEN r <- backend_rep a THEN forall x, (snd (snd r) (fst (snd r) x) = x))%option.

  Hint Resolve backend_rep_correct: vpl.

  (* TODO: Having this operation in this module is really weird ! Rename the module or move this away... *)
  Parameter meet: t -> t -> imp t.
  Parameter meet_correct: forall p1 p2, WHEN p <- meet p1 p2 THEN (forall m, gamma p1 m -> gamma p2 m -> gamma p m).

  Hint Resolve meet_correct: vpl.

End HasSimplePrinting.

(* Require Program.Basics. *)
Module Type HasRename (N: NumSig) (Import D: BasicDomain N).
  (* Import Program.Basics. *)

  (** [rename x y a] renames variable [x] by [y] in [a].

   WARNING: For the underlying "shadow" implementation in ML, 
              [y] must be a fresh variable in [a]
            However, we do not need to make this precondition explicit 
            for correctness (thus, this is simpler to let it hidden).

    Hence, this precondition is only dynamically verified by an "assert" in ML code.
  *)
  Parameter rename: PVar.t -> PVar.t -> t -> imp t.
  Parameter rename_correct: forall x y a, WHEN p <- (rename x y a) THEN
    (forall m, gamma a (Mem.assign x (m y) m) -> gamma p m).
    (* ie. forall x y a, isRename gamma impl (rename x y a) a x y. *)

  Hint Resolve rename_correct: vpl.

End HasRename.

(** Interval from Terms *)

Module Type ItvSig(N:NumSig).
  
  Parameter t: Type.
  Parameter sat: t -> N.t -> Prop.

End ItvSig.

Module Type TermSig(N:NumSig).
  
  Parameter t: Type.
  Parameter eval: t -> Mem.t N.t -> N.t.

End TermSig.


(** deprecated: this module was only used in the wrapper of Verasco analyzer 
See more general [getItvMode] below.
**)
Module Type HasGetItv (N: NumSig) (Import T: TermSig N) (Import I: ItvSig N) (Import D: BasicDomain N).

  Parameter get_itv: T.t -> t -> imp I.t.

  Parameter get_itv_correct: forall (te: T.t) (a: t), WHEN i <- (get_itv te a) THEN
    (forall m, gamma a m -> I.sat i (T.eval te m)).

  Hint Resolve get_itv_correct: vpl.

End HasGetItv.

(** computation mode of intervals:
  - [BOTH]: both sides of the bound.
  - [UP]: we are only interested in a precise up bound
  - [LOW]: we are only interested in a precise low bound
*)
Inductive mode : Set := BOTH | UP | LOW.

Module Type HasGetItvMode (N: NumSig) (Import T: TermSig N) (Import I: ItvSig N) (Import D: BasicDomain N).

  Parameter getItvMode: mode -> T.t -> t -> imp I.t.

  Parameter getItvMode_correct: forall mo (te: T.t) (a: t), WHEN i <- (getItvMode mo te a) THEN
    (forall m, gamma a m -> I.sat i (T.eval te m)).
  Hint Resolve getItvMode_correct: vpl.

End HasGetItvMode.


(** Assume/Require of conditions  *)

Module Type CondSig(N:NumSig).
  
  Parameter t: Type.
  Parameter sat: t -> Mem.t N.t -> Prop.

End CondSig.


Module Type HasAssumeG (Import Imp: FullImpureMonad) (N: NumSig) (Cond: CondSig N) (D:BasicDomainG Imp N).

  Import Cond.
  Import D.

  Parameter assume: Cond.t -> t -> imp t.
  Parameter assume_correct: forall c a, WHEN p <- assume c a THEN (forall m, sat c m -> gamma a m -> gamma p m).

  Hint Resolve assume_correct: vpl.

End HasAssumeG.

Module Type HasAssume (N: NumSig) (Cond: CondSig N) (D:BasicDomain N).
  Include HasAssumeG ImpureConfig.Core N Cond D.
End HasAssume.

Module Type HasAssertG (Import Imp: FullImpureMonad) (N: NumSig) (Cond: CondSig N) (D:BasicDomainG Imp N).
  
  Import Cond.
  Import D.

  Parameter assert: Cond.t -> t -> imp bool.
  Parameter assert_correct: forall c a, If assert c a THEN (forall m, gamma a m -> sat c m).

  Hint Resolve assert_correct: vpl.

End HasAssertG.

Module Type HasAssert (N: NumSig) (Cond: CondSig N) (D:BasicDomain N).
  Include HasAssertG ImpureConfig.Core N Cond D.
End HasAssert.

Module Type HasConcreteConditions (N: NumSig) (Cond: CondSig N) (D: BasicDomain N) 
  := HasAssume N Cond D <+ HasAssert N Cond D.

Module Type WeakAbstractDomainG (Imp: FullImpureMonad) (N: NumSig) (Cond: CondSig N) 
  := BasicDomainG Imp N <+ HasAssumeG Imp N Cond.

Module Type WeakAbstractDomain (N: NumSig) (Cond: CondSig N). 
  Include WeakAbstractDomainG ImpureConfig.Core N Cond.
End WeakAbstractDomain.

Module Type AbstractDomainG (Imp: FullImpureMonad) (N: NumSig) (Cond: CondSig N) 
  := WeakAbstractDomainG Imp N Cond <+ HasAssertG Imp N Cond.

Module Type AbstractDomain (N: NumSig) (Cond: CondSig N). 
  Include AbstractDomainG ImpureConfig.Core N Cond.
End AbstractDomain.



(* Assignement *)
Module Type XCondSig(N:NumSig).
  
  Declare Module Term: TermSig N.
  Include CondSig N.

  (** two state semantics:
    [xsat c old new] means that "c" is a relation between "old" state and "new" state.
  *)
  Parameter xsat: t -> Mem.t N.t -> Mem.t N.t -> Prop.

  Parameter xsat_sat: forall c m, xsat c m m = sat c m.

End XCondSig.


Module Type HasAssignG (Import Imp: FullImpureMonad) (N: NumSig) (Cond: XCondSig N) (D: BasicDomainG Imp N).
  
  Import Cond.Term.
  Import Cond.
  Import D.
  
  (* deterministic assignement *)
  Parameter assign: PVar.t -> Term.t -> t -> imp t.
  Parameter assign_correct: forall x te a, WHEN p <- assign x te a THEN
    (forall m, gamma a m -> gamma p (Mem.assign x (eval te m) m)).

  (* guarded assignement *)
  Parameter guassign: PVar.t -> Cond.t -> t -> imp t.
  Parameter guassign_correct: forall x c a, WHEN p <- guassign x c a THEN 
     (forall m v, xsat c m (Mem.assign x v m) -> gamma a m -> gamma p (Mem.assign x v m)).

  Hint Resolve assign_correct guassign_correct: vpl.

End HasAssignG.

Module Type HasAssign (N: NumSig) (Cond: XCondSig N) (D:BasicDomain N).
  Include HasAssignG ImpureConfig.Core N Cond D.
End HasAssign.


Module Type FullAbstractDomainG (Imp: FullImpureMonad) (N: NumSig) (Cond: XCondSig N) := AbstractDomainG Imp N Cond <+ HasAssignG Imp N Cond.

Module Type FullAbstractDomain (N: NumSig) (Cond: XCondSig N) := AbstractDomain N Cond <+ HasAssign N Cond.

Module Type FullItvAbstractDomain (N: NumSig) (Cond: XCondSig N) (I: ItvSig N)
  := FullAbstractDomain N Cond <+ HasGetItvMode N Cond.Term I <+ HasSimplePrinting N.

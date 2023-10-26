Require Import CState.
Require Import InstrTy.
Require Import ZArith.
Require Import IterSemantics.
Require Import ImpureAlarmConfig.
Require Import Base. 
Require Import PolyBase.
Require Import AST.
Require Import Ctypes.
Require Import List.
Require Import OpenScop.
Require Import String.
Require Import Cop.
Require Import Csem.
Require Import Values.
Require Import Bool.
Require Import Integers.
Require Import Memory.
Require Import Linalg.
Require Import Coqlib.
Import List.ListNotations.
Require Import sflib.
Require Import LibTactics. 
Require Import CTy.
Local Open Scope string_scope.

(** A[i][...] = B[j][...] +/-/... *)
(* CTy is a self-defined type, as a sugar of CompCert.type *)
(* we will convert it to original version for dynamic semantics *)
Module CInstr <: INSTR.
  Module State := CState.
  Module Ty := CTy.
  Definition ident := AST.ident.
  Definition ident_eqb := Pos.eqb.
  Definition ident_eqb_eq := Pos.eqb_eq.
  Definition ident_to_openscop_ident (id: ident) := id.
  Definition openscop_ident_to_ident (id: ident) := id.
  
  Definition ident_to_varname := AST.ident_to_varname.
  Definition varname_to_ident := AST.varname_to_ident.
  Definition bind_ident_varname := AST.bind_ident_varname.
  Definition iterator_to_varname := AST.iterator_to_varname.

  (** may-affine expression for array index *)
  (** change to all Z, no type (assuming int32s as defaulted when evalutaing to value) *)
  Inductive ma_expr: Type :=
  | MAval (v: Z)
  | MAvarz (n: nat)
    (* identifier in polyhedral model is nameless. *) 
    (* all iterators are deprived of their characters and can be considered as normal symbolic constant *)
  | MAunop (op: unary_operation) (r: ma_expr)
  | MAbinop (op: binary_operation) (r1 r2: ma_expr)
  .
  
  (* each dimension's upper bound is restricted in typing environment *)
  Inductive arr_access: Type := 
  | Avar (id: ident) (ty: Ty.basetype)
    (** pure variable, non-affine-related *)
  | Aarr (id: ident) (el: ma_exprlist) (ty: Ty.basetype)
    (** multi-dimension arr *)
  with ma_exprlist : Type :=
  | MAsingleton (r: ma_expr)
  | MAcons (r1: ma_expr) (rl: ma_exprlist).

  Inductive expr: Type := 
  | Eval (v: val) (ty: Ty.basetype)
  | Evarz (n: nat) (ty: Ty.basetype)            
    (** affine related variable (varctxt and iterators); ty should be signed integer *)
    (* The semantics will change value of Z to int32s. *)
    (* The transition may induce overflow. This is not what we deal with here. *)
  | Eaccess (x: arr_access) (ty: Ty.basetype)           
  | Eunop (op: unary_operation) (r: expr) (ty: Ty.basetype)
                                              (**r unary arithmetic operation *)
  | Ebinop (op: binary_operation) (r1 r2: expr) (ty: Ty.basetype)
                                          (**r binary arithmetic operation *)
  (* | Eseqand (r1 r2: expr) (ty: type)        *)
                          (**r sequential "and" [r1 && r2] *)
  (* | Eseqor (r1 r2: expr) (ty: type)         *)
                          (**r sequential "or" [r1 || r2] *)
  .

  (* CompCert compcert_typeof_expr *)
  Definition typeof_expr (a: expr) : Ty.basetype :=
    match a with
    | Evarz _ ty => ty
    | Eval _ ty => ty
    | Eunop _ _ ty => ty
    | Ebinop _ _ _ ty => ty
    | Eaccess _ ty => ty
    end.

  Definition typeof_access (a: arr_access): Ty.basetype := 
    match a with
    | Avar _ ty => ty
    | Aarr _ _ ty => ty
    end.


  Inductive CInstr: Type := 
    | Iskip: CInstr
    | Iassign: arr_access -> expr -> CInstr 
      (* eval expr under ty of arr_access, and assign it to arr_access's cell *)
    .

  Definition t : Type := CInstr.

  Fixpoint ma_expr_to_openscop (e: ma_expr) (names: list varname): option AffineExpr := 
    match e with
    | MAval v => Some (AfInt v)
    | MAvarz n => 
        match nth_error names n with
        | Some name => Some (AfVar name)
        | None => Some (AfVar (ident_to_varname (free_ident tt)))
                  (* should not be in this case *)
        end
    | MAunop Cop.Oneg r => 
        match ma_expr_to_openscop r names with
        | Some r' => Some (AfMinus (AfInt 0%Z) r')
        | None => None
        end
    | MAbinop Cop.Oadd r1 r2 => 
        match ma_expr_to_openscop r1 names, ma_expr_to_openscop r2 names with
        | Some r1', Some r2' => Some (AfAdd r1' r2')
        | _, _ => None
        end
    | MAbinop Cop.Osub r1 r2 =>
        match ma_expr_to_openscop r1 names, ma_expr_to_openscop r2 names with
        | Some r1', Some r2' => Some (AfMinus r1' r2')
        | _, _ => None
        end
    | MAbinop Cop.Omul r1 r2 =>
        match ma_expr_to_openscop r1 names, ma_expr_to_openscop r2 names with
        | Some r1', Some r2' => Some (AfMulti r1' r2')
        | _, _ => None
        end
    | MAbinop Cop.Odiv r1 r2 =>
        match ma_expr_to_openscop r1 names, ma_expr_to_openscop r2 names with
        | Some r1', Some r2' => Some (AfDiv r1' r2')
        | _, _ => None
        end
    | _ => None 
    end
  .


  Fixpoint ma_exprlist_to_openscop (el: ma_exprlist) (names: list varname): option (list AffineExpr) :=
    match el with 
    | MAsingleton r => 
      match ma_expr_to_openscop r names with
      | Some r' => Some (r' :: nil)
      | None => None
      end
    | MAcons r rl => 
      match ma_expr_to_openscop r names, ma_exprlist_to_openscop rl names with
      | Some r', Some rl' => Some (r' :: rl')
      | _, _ => None
      end
    end.

  Definition access_to_openscop (a: arr_access) (names: list varname): option ArrayAccess := 
    match a with
    | Avar id _ => Some (ArrAccess (ident_to_varname id) nil)
    | Aarr id el _ => 
      match ma_exprlist_to_openscop el names with
      | Some el' => Some (ArrAccess (ident_to_varname id) el')
      | None => None 
      end
    end
  .

  Fixpoint expr_to_openscop (e: expr) (iter_names: list varname): option ArrayExpr := 
    match e with
    | Eval v _ => 
      match v with
      | Vint n => Some (ArrAtom (AInt (Int.signed n)))
      | Vfloat f => Some (ArrAtom (AFloat f))
      | _ => None
      end
    | Evarz n _ => 
        match nth_error iter_names n with
        | Some name => Some (ArrAtom (AVar name))
        | None => Some (ArrAtom (AVar (ident_to_varname (free_ident tt))))
        end
    | Eaccess a _ => 
      match access_to_openscop a iter_names with
      | Some a' => Some (ArrAccessAtom a')
      | None => None
      end
    | Eunop Cop.Oneg r _ => 
        match expr_to_openscop r iter_names with
        | Some r' => Some (ArrMinus (ArrAtom (AInt 0%Z)) r')
        | None => None
        end
    | Ebinop Cop.Oadd r1 r2 _ =>
        match expr_to_openscop r1 iter_names, expr_to_openscop r2 iter_names with
        | Some r1', Some r2' => Some (ArrAdd r1' r2')
        | _, _ => None
        end
    | Ebinop Cop.Osub r1 r2 _ =>
        match expr_to_openscop r1 iter_names, expr_to_openscop r2 iter_names with
        | Some r1', Some r2' => Some (ArrMinus r1' r2')
        | _, _ => None
        end
    | Ebinop Cop.Omul r1 r2 _ =>
        match expr_to_openscop r1 iter_names, expr_to_openscop r2 iter_names with
        | Some r1', Some r2' => Some (ArrMulti r1' r2')
        | _, _ => None
        end
    | Ebinop Cop.Odiv r1 r2 _ =>
        match expr_to_openscop r1 iter_names, expr_to_openscop r2 iter_names with
        | Some r1', Some r2' => Some (ArrDiv r1' r2')
        | _, _ => None
        end
    | _ => None 
    end.

  (* Transformation to openscop arraystmt *)
  Definition to_openscop (cinstr: t) (iter_names: list varname): option OpenScop.ArrayStmt :=
    match cinstr with 
    | Iskip => Some ArrSkip
    | Iassign a e => 
      match access_to_openscop a iter_names, expr_to_openscop e iter_names with
      | Some a', Some e' => Some (ArrAssign a' e')
      | _, _ => None
      end
    end.
  

  (* return the max varz's natural number *)
  Fixpoint depth_ma_expr (r: ma_expr) := 
    match r with 
    | MAval _ => 0
    | MAvarz n => n
    | MAunop _ r => depth_ma_expr r
    | MAbinop _ r1 r2 => Nat.max (depth_ma_expr r1) (depth_ma_expr r2)
    end.
  
  Fixpoint depth_ma_exprlist (el: ma_exprlist) :=
    match el with 
    | MAsingleton r => depth_ma_expr r
    | MAcons r rl => Nat.max (depth_ma_expr r) (depth_ma_exprlist rl)
    end.

  Definition depth_access (a: arr_access) := 
    match a with
    | Avar _ _ => 0
    | Aarr _ el _ => depth_ma_exprlist el
    end.

  Fixpoint depth_expr (e: expr) := 
    match e with 
    | Eval _ _ => 0
    | Evarz n _ => n
    | Eaccess a _ => depth_access a
    | Eunop _ r _ => depth_expr r
    | Ebinop _ r1 r2 _ => Nat.max (depth_expr r1) (depth_expr r2)
    (* | Eseqand r1 r2 _ => Nat.max (depth_expr r1) (depth_expr r2) *)
    (* | Eseqor r1 r2 _ => Nat.max (depth_expr r1) (depth_expr r2) *)
    end.
  
  Definition depth (i: t): nat :=
    match i with
    | Iskip => 0
    | Iassign a e => Nat.max (depth_access a) (depth_expr e)
    end.


  (* affine expr do not access memory, evaluating in Z only *)
  (* currently, only support basic operators *)
  Definition sem_unary_operation_Z
  (op: unary_operation)
  (v: Z): option Z :=
  match op with
    | Oneg => Some (Z.opp v)
    | _ => None
  end.

  Lemma sem_unary_operation_Z_correct:
    forall v,
      sem_unary_operation_Z Oneg v = Some (Z.opp v).
  Proof. intros. simpls. trivial. Qed.

  Definition sem_binary_operation_Z
  (op: binary_operation)
  (v1: Z) (v2: Z): option Z :=
  match op with
  | Oadd => Some (Z.add v1 v2)
  | Osub => Some (Z.sub v1 v2)
  | Omul => Some (Z.mul v1 v2)
  | _ => None 
  end.

  Inductive eval_maexpr: ma_expr -> list Z -> Z -> Prop :=
  | eval_ma_val: forall envv v,
    eval_maexpr (MAval v) envv v
  | eval_ma_var: forall n envv z,
    nth_error envv n = Some z ->
    eval_maexpr (MAvarz n) envv z
  | eval_ma_unop: forall op r envv v v',
    eval_maexpr r envv v ->
    sem_unary_operation_Z op v = Some v' ->
    eval_maexpr (MAunop op r) envv v'
  | eval_ma_binop: forall r1 r2 envv v1 v2 v op,
    eval_maexpr r1 envv v1 ->
    eval_maexpr r2 envv v2 ->
    sem_binary_operation_Z op v1 v2 = Some v ->
    eval_maexpr (MAbinop op r1 r2) envv v
  .

  
  Fixpoint eval_maexpr_symb (e: ma_expr): option (list Z * Z) :=
    match e with
    | MAval z => Some (nil, z)
    | MAvarz n => Some (List.app (V0 (n)) [1%Z], 0%Z)
    | MAunop op r => 
      match eval_maexpr_symb r with
      | Some (v, c) =>
        match op with
        | Oneg => Some (--v, Z.opp c)
        | _ => None
        end
      | _ => None
      end
    | MAbinop op r1 r2 =>
      match eval_maexpr_symb r1, eval_maexpr_symb r2 with
      | Some (v1, c1), Some (v2, c2) => 
        match op with
        | Oadd => Some (add_vector v1 v2, Z.add c1 c2)
        | Osub => Some (add_vector v1 (--v2), Z.sub c1 c2)
        | Omul =>
            (* trivially let all lhs is constant *) 
            if negb (is_null v1) then None
            else Some (mult_vector c1 v2, Z.mul c1 c2)
        | _ => None
        end
      | _, _ => None
      end 
    end.

  
  Definition M := MAvarz 0%nat.
  Definition N := MAvarz 1%nat.
  Definition x := MAvarz 2%nat.
  Definition y := MAvarz 3%nat.
  Delimit Scope aff_scope with aff.
  Notation "x * y" := (MAbinop Omul x y) : aff_scope.
  Notation "x + y" := (MAbinop Oadd x y) : aff_scope.
  Notation "x - y" := (MAbinop Osub x y) : aff_scope.
  Notation "- x" := (MAunop Oneg x) : aff_scope.
  Notation "$ x" := (MAval x) (at level 30) : aff_scope.

  Local Open Scope aff_scope.
  Example eval_maexpr_symb_test:
    eval_maexpr_symb ( $(-8) + M + ($3 * $2) * x + (-y) + $4 )%aff = 
    Some ([1%Z; 0%Z; 6%Z; (-1)%Z], (-4)%Z).
  Proof. simpl. reflexivity. Qed.


  Inductive eval_maexpr_list: ma_exprlist -> list Z -> list Z -> Prop :=
  | eval_ma_singleton:
    forall e envv v,
    eval_maexpr e envv v ->
    eval_maexpr_list (MAsingleton e) envv (v::nil)
  | eval_ma_cons:
    forall e envv v el vl,
    eval_maexpr e envv v ->
    eval_maexpr_list el envv vl ->
    eval_maexpr_list (MAcons e el) envv (v::vl)
  .

  Inductive access_cell: arr_access -> list Z -> MemCell -> Prop :=
  | AccessVar: forall a envv id ty, 
    a = Avar id ty ->
    access_cell a envv {|arr_id := id; arr_index := nil|}
  | AccessArr: forall a id envv el zl ty, 
    a = Aarr id el ty ->
    eval_maexpr_list el envv zl ->
    access_cell a envv {|arr_id := id; arr_index := zl|}
  .


  (** Definitions of syntax and semantics *)
  (* while evaluation, only "read" is possible *)
  Inductive eval_expr: expr -> list Z -> list MemCell -> State.t -> val -> Prop := 
  | eval_val: forall v ty envv st,
    eval_expr (Eval v ty) envv nil st v
  | eval_var: forall n ty envv st z,
    nth_error envv n = Some z ->
    eval_expr (Evarz n ty) envv nil st (Values.Vint (Int.repr z))
  | eval_access: forall a envv rcell ty v st,
    access_cell a envv rcell -> 
    State.read_cell rcell ty v st ->
    eval_expr (Eaccess a ty) envv (rcell::nil) st v 
  | eval_unop: forall op r ty envv rcells st v v' ge e m,
    st = (ge, e, m) ->
    eval_expr r envv rcells st v ->
    sem_unary_operation op v (Ty.basetype_to_compcert_type (typeof_expr r)) m = Some v' ->
    eval_expr (Eunop op r ty) envv rcells st v'
  | eval_binop: forall st ge e m r1 r2 envv rcs1 rcs2 v1 v2 v op ty,
    st = (ge, e, m) ->
    eval_expr r1 envv rcs1 st v1 ->
    eval_expr r2 envv rcs2 st v2 ->
    sem_binary_operation ge op v1 (Ty.basetype_to_compcert_type (typeof_expr r1)) v2 (Ty.basetype_to_compcert_type (typeof_expr r2)) m = Some v ->
    eval_expr (Ebinop op r1 r2 ty) envv (rcs1++rcs2) st v
  .


  Inductive semantics : t -> list Z -> list MemCell -> list MemCell -> State.t -> State.t -> Prop :=
  | IskipSem:  forall vl st st',
      State.eq st st' ->
      semantics Iskip vl nil nil st st'
  | IassignSem: 
      forall a e envv st st' v wcell rcells,
        access_cell a envv wcell ->
        eval_expr e envv rcells st v -> 
        State.write_cell wcell (typeof_access a) v st st' -> 
        semantics (Iassign a e) envv (wcell::nil) rcells st st'
  .

  Definition instr := t.
  Definition dummy_instr := Iskip.
  Definition instr_semantics := semantics. 
  Module IterSem := IterSem State.
  Module IterSemImpure := IterSem.IterImpureSemantics(CoreAlarmed).

  (* could be stronger *)
  Definition NonAlias (st: State.t) : Prop :=
      State.non_alias st.

  Lemma sema_prsv_nonalias:
    forall i p wcs rcs st1 st2,
        NonAlias st1 ->
        instr_semantics i p wcs rcs st1 st2 ->
        NonAlias st2.
  Proof.
    intros. inv H0; trivial.
    - eapply State.eq_prsv_nonalias; eauto.
    - eapply State.write_cell_prsv_nonalias; eauto.
  Qed.

  (* initial context's values are inherited from the state *)
  (* below we suppose all context should be int32s *)
  Definition InitEnv (vars: list ident) (vals: list Z) (st: State.t) : Prop :=
      List.length vars = List.length vals /\
      (forall n var z, 
        nth_error vars n = Some var ->
        nth_error vals n = Some z ->
        exists z', 
        State.read_cell {| arr_id := var; arr_index := nil |}
          Ty.int32s (Vint z') st /\ z = Int.signed z'
      ).

  (* initial state should be compatible to variables declarations, like, correctly allocated *)
  Inductive Compat': list (ident * Ty.arrtype) -> State.t -> Prop :=
  | compat_nil:
      forall st, Compat' nil st
  | compat_cons:
      forall id ty vars st,
        State.valid id ty st ->
        Compat' vars st ->
        Compat' ((id, ty) :: vars) st.

  Definition Compat (vars: list (ident * Ty.arrtype)) (st: State.t): Prop := Compat' vars st.

  Lemma init_env_samelen: 
      forall vars vals st, InitEnv vars vals st -> List.length vars = List.length vals.
  Proof. intros. destruct H; trivial. Qed.

  (** Symbolic evaluation of may-affine expressions *)
  Fixpoint eval_maexpr_list_symb (el: ma_exprlist): option (list (list Z * Z)) :=
    match el with
    | MAsingleton e =>
      match eval_maexpr_symb e with
      | Some listzz => Some (listzz::nil)
      | _ => None
      end
    | MAcons e el =>
      match eval_maexpr_symb e, eval_maexpr_list_symb el with
      | Some listzz, Some listzzs => Some (listzz::listzzs)
      | _, _ => None
      end
    end.

  Lemma eval_maexpr_opp_val_opp:
    forall e p v,
      eval_maexpr e p v <->
      eval_maexpr (-e) p (-v).
  Proof. 
    intros. split; intro.
    - econs; eauto.
    - inv H. rewrite sem_unary_operation_Z_correct in H5. inv H5. 
      assert (v0 = v)%Z. {lia. } subst; trivial. 
  Qed.

  Lemma eval_opp_maexpr_val_opp:
    forall e p v,
      eval_maexpr e p v <->
      eval_maexpr (-(-e)) p v.
  Proof.
    intros. 
    do 2 rewrite eval_maexpr_opp_val_opp. 
    assert (v = -(-v))%Z. lia. rewrite H at 2.
    split; trivial. 
  Qed.

  Lemma eval_add_maexpr_val_add:
    forall e1 e2 p v,
    eval_maexpr (e1 + e2) p v ->
    exists v1 v2,
    eval_maexpr e1 p v1 /\
    eval_maexpr e2 p v2 /\
    (v1 + v2 = v)%Z.
  Proof. 
    intros.
    inv H.
    do 2 eexists; splits; eauto.
    unfold sem_binary_operation_Z in H7. inv H7. lia.
  Qed.

  Lemma eval_add_maexpr_val_sub:
    forall e1 e2 p v,
    eval_maexpr (e1 - e2) p v ->
    exists v1 v2,
    eval_maexpr e1 p v1 /\
    eval_maexpr e2 p v2 /\
    (v1 - v2 = v)%Z.
  Proof. 
    intros.
    inv H.
    do 2 eexists; splits; eauto.
    unfold sem_binary_operation_Z in H7. inv H7. lia.
  Qed.

  Lemma eval_add_maexpr_val_mul:
    forall e1 e2 p v,
    eval_maexpr (e1 * e2) p v ->
    exists v1 v2,
    eval_maexpr e1 p v1 /\
    eval_maexpr e2 p v2 /\
    (v1 * v2 = v)%Z.
  Proof. 
    intros.
    inv H.
    do 2 eexists; splits; eauto.
    unfold sem_binary_operation_Z in H7. inv H7. lia.
  Qed.

  Lemma eval_maexpr_symb_correct:
    forall e v1 c1 p v,
      eval_maexpr_symb e = Some (v1, c1) ->
      eval_maexpr e p v ->
      (dot_product v1 p + c1)%Z = v.
  Proof.
    induction e.
    - intros. simpls. inv H. 
      inv H0. simpls. destruct p; trivial.
    - intros. simpls. inv H. inv H0.
      eapply v0_n_app_1_dot_product_p_is_nth_p in H1. rewrite H1. lia.
    - intros. simpls. 
      destruct (eval_maexpr_symb e) eqn:He; tryfalse.
      destruct op; destruct p0 as (v0, c0); tryfalse.
      inv H. rewrite dot_product_opp_l. 
      assert (dot_product v0 p + c0 = -v)%Z. {
        eapply IHe; eauto.
        eapply eval_maexpr_opp_val_opp in H0.
        eapply eval_opp_maexpr_val_opp. trivial.
      }
      lia.
    - intros. simpls. 
      destruct (eval_maexpr_symb e1) eqn:He1; tryfalse.
      destruct p0 as (v0, c0).
      destruct (eval_maexpr_symb e2) eqn:He2; tryfalse.
      destruct p0 as (v0', c0').
      destruct op; tryfalse.
      + (* Oadd *)
        inv H.
        rewrite add_vector_dot_product_distr_left.
        eapply eval_add_maexpr_val_add in H0. 
        destruct H0 as (v1 & v2 & Heval1 & Heval2 & Hadd).
        eapply IHe1 in Heval1; eauto.
        eapply IHe2 in Heval2; eauto.
        lia.
      + (* Osub *)
        inv H.
        rewrite add_vector_dot_product_distr_left.
        rewrite dot_product_opp_l.
        eapply eval_add_maexpr_val_sub in H0.
        destruct H0 as (v1 & v2 & Heval1 & Heval2 & Hsub).
        eapply IHe1 in Heval1; eauto.
        eapply IHe2 in Heval2; eauto.
        lia.
      + (* Omul *)
        inv H.
        destruct (negb (is_null v0)) eqn:Hv0null; tryfalse.
        inv H2.
        eapply negb_false_iff in Hv0null; eauto.
        rewrite dot_product_mult_left.
        eapply eval_add_maexpr_val_mul in H0.
        destruct H0 as (v1 & v2 & Heval1 & Heval2 & Hmul).
        assert (c0 * (dot_product v0' p + c0') = v)%Z. {
          eapply IHe1 in Heval1; eauto.
          eapply IHe2 in Heval2; eauto.
          rewrite dot_product_null_left in Heval1; trivial.
          lia.
        }
        lia.
  Qed.

  Lemma eval_maexpr_list_symb_correct:
    forall (el: ma_exprlist) func func' p c id ty,
      eval_maexpr_list_symb el = Some func ->
      length func' = length func ->
      forallb
         (fun aff1aff2 : list Z * Z * (list Z * Z) =>
          let (aff1, aff2) := aff1aff2 in
          let (v1, c1) := aff1 in let (v2, c2) := aff2 in is_eq v1 v2 && (c1 =? c2)%Z)
         (combine func' func) = true ->
      access_cell (Aarr id el ty) p c ->
      cell_eq (exact_cell (id, func') p) c.
  Proof.  
    induction el.
    - intros.
      simpls. destruct (eval_maexpr_symb r) eqn:Hevalr; tryfalse. inv H.
      rename p0 into vec.
      destruct func' eqn:Hfunc'; tryfalse.
      rename p0 into vec'. 
      assert (l = nil). {
        destruct l eqn:Hl; tryfalse. trivial.
      }
      subst; simpls. clear H0.
      destruct vec as (v1, c1).
      destruct vec' as (v2, c2).
      do 2 rewrite andb_true_iff in H1.
      destruct H1 as ((Heq & Hc) & Haff).
      eapply Z.eqb_eq in Hc. subst.
      inv H2; tryfalse.
      unfold cell_eq. 
      inv H0; tryfalse. inv H.
      split; simpls; trivial.
      eapply eval_maexpr_symb_correct in Hevalr; eauto.
      assert (veq v2 v1). {trivial. }
      rewrite H.
      unfold veq. simpls. rewrite andb_true_iff.
      split; trivial. lia.
    - intros.
      simpls. destruct (eval_maexpr_symb r1) eqn:Hevalr1; tryfalse. inv H0.
      destruct (eval_maexpr_list_symb el) eqn:Hevalel; tryfalse. inv H2; tryfalse.
      inv H0. unfold cell_eq. simpl; split; trivial.
      inv H. destruct func' eqn:Hfunc'; tryfalse.
      simpls.
      rewrite andb_true_iff in H1. destruct H1.
      destruct zl eqn:Hzl.
      + inv H3; tryfalse.
      + inv H3.
        destruct p1 as (v1, c1). destruct p0 as (v2, c2).
        rewrite andb_true_iff in H. destruct H.
        assert (veq v1 v2). {trivial. }
        eapply Z.eqb_eq in H1. subst.
        (* assert (exists cell, arr_index cell ) *)
        eapply IHel with (p:=p) in H0; eauto.
        {
          unfold cell_eq in H0.
          destruct H0.
          unfold veq. simpl.
          rewrite andb_true_iff.
          split; trivial.
          eapply eval_maexpr_symb_correct with (p:=p) (v:=z) in Hevalr1; trivial. 
          - rewrite H2. clear - Hevalr1. lia.
          - simpls.
            rewrite H1. 
            instantiate (1:= {|arr_id := 1%positive; arr_index:=l1 |}). simpl.
            eapply is_eq_reflexive.
        }
        {
          econs; eauto.
        }
    Unshelve. exact Ty.int32s.
  Qed.

  Lemma access_cell_var_implies_cell_eq:
    forall id p c ty,
      access_cell (Avar id ty) p c ->
      cell_eq (exact_cell (id, []) p) c.
  Proof. 
    intros.
    inv H; tryfalse.
    simpls. unfold cell_eq. simpls. inv H0. split; trivial. eapply veq_refl. 
  Qed.

  Lemma access_cell_arr_implies_cell_eq:
    forall el id p c l (af: AccessFunction) ty,
      access_cell (Aarr id el ty) p c ->
      eval_maexpr_list_symb el = Some l ->
      (let (id', func) := af in
        (id' =? id)%positive && (Datatypes.length func =? Datatypes.length l)%nat &&
        forallb
          (fun aff1aff2 : list Z * Z * (list Z * Z) =>
            let (aff1, aff2) := aff1aff2 in
            let (v1, c1) := aff1 in let (v2, c2) := aff2 in is_eq v1 v2 && (c1 =? c2)%Z) 
          (combine func l)) = true ->
      cell_eq (exact_cell af p) c.
  Proof. 
    intros.
    destruct af as (id' & func').
    do 2 rewrite andb_true_iff in H1.
    destruct H1 as ((Hid & Hlen) & Haff).
    eapply Pos.eqb_eq in Hid.
    eapply Nat.eqb_eq in Hlen.
    subst.
    eapply eval_maexpr_list_symb_correct; eauto.
  Qed.

  (** Properties of semantics *)
  Lemma eval_expr_prsv_val_if_state_eq:
    forall e p rcs st st' v,
      State.eq st st' ->
      eval_expr e p rcs st v ->
      eval_expr e p rcs st' v.
  Proof. 
    induction e; intros.
    - inv H0. econs; eauto.
    - inv H0. econs; eauto.
    - inv H0. econs; eauto.
      eapply State.read_cell_stable_under_eq; eauto. 
    - inv H0. 
      destruct st' as ((ge', e'), m').
      econs; eauto.
      eapply State.sem_unary_operation_eq_invariant; eauto.
    - inv H0.
      destruct st' as ((ge', e'), m').
      econs; eauto.
      eapply State.sem_binary_operation_eq_invariant; eauto.  
  Qed.

  Lemma eval_expr_prsv_val_if_neq_wr_cell:
  forall e p wc rcs v v' st1 st2 bty,
    State.write_cell wc bty v' st1 st2 ->
    Forall (fun rc => cell_neq rc wc) rcs ->
    State.non_alias st1 ->
    eval_expr e p rcs st2 v <->
    eval_expr e p rcs st1 v.
  Proof.
    induction e.
    all: try solve [intros; split; intro; inv H2; econstructor; eauto].
    - (* Eaccess *)
      intros until bty. intros H H0 Halias.  split; intro.
      + inv H1. inv H0. clear H5. 
        econstructor; eauto.
        eapply State.read_after_write_cell_neq; eauto. eapply cell_neq_symm; trivial.
      + inv H1. inv H0. clear H5. 
        econstructor; eauto.
        rewrite <- State.read_after_write_cell_neq; eauto. eapply cell_neq_symm; trivial.
    - (* unop *)  
      intros until bty. intros H H0 Halias. split; intro. 
      + inversion_clear H1. 
        rename e0 into env2. rename m into m2. rename ge into ge2.
        destruct st1 as ((ge1 & env1) & m1) eqn:Hst1. subst.
        assert (sem_unary_operation op v0 (Ty.basetype_to_compcert_type (typeof_expr e)) m1 = Some v). {
          eapply State.sem_unary_operation_write_cell_invariant with 
            (op:=op) (v:=v0) (ty':= (typeof_expr e)) (v':=v) in H; eauto.
          eapply H. trivial.
        }
        rewrite IHe with (st2:=(ge2, env2, m2)) in H3; eauto.
        eapply eval_unop; eauto.
      + inversion_clear H1. 
        rename e0 into env1. rename m into m1. rename ge into ge1.
        destruct st2 as ((ge2 & env2) & m2) eqn:Hst2. subst.
        assert (sem_unary_operation op v0  (Ty.basetype_to_compcert_type (typeof_expr e)) m2 = Some v). {
          eapply State.sem_unary_operation_write_cell_invariant with 
            (op:=op) (v:=v0) (ty':= ((typeof_expr e))) (v':=v) in H; eauto.
          eapply H. trivial.
        }
        rewrite <- IHe with (st2:=(ge2, env2, m2)) in H3; eauto.
        eapply eval_unop; eauto.
    - (* binop *)
      intros until bty. intros H H0 Halias. split; intro. 
      + inversion H1. subst.
        destruct st1 as ((ge1 & env1) & m1) eqn:Hst1. subst.
        assert (sem_binary_operation ge op v1 (Ty.basetype_to_compcert_type (typeof_expr e1)) v2 (Ty.basetype_to_compcert_type (typeof_expr e2)) m1 = Some v). {
          pose proof State.sem_binary_operation_write_cell_invariant op v1 v2.
          eapply H2 with (m4:=m) (m3:=m1) in H13; trivial.
          assert (ge = ge1). 
          {inv H. clear - H16 H17. destruct H16. destruct H17. subst; trivial. }
          subst. eauto.
        }
        rewrite IHe1 with (st2:=(ge, e, m)) in H11; eauto. 
        2: {eapply Forall_app in H0; destruct H0; trivial. }
        rewrite IHe2 with (st2:=(ge, e, m)) in H12; eauto.
        2: {eapply Forall_app in H0; destruct H0; trivial. }
        eapply eval_binop; eauto.
        assert (ge1 = ge). 
        {inv H. clear - H16 H15. destruct H16. destruct H15. subst; trivial.  }
        subst. trivial.
      + inversion H1. subst.
        destruct st2 as ((ge2 & env2) & m2) eqn:Hst2. subst.
        assert (sem_binary_operation ge op v1 (Ty.basetype_to_compcert_type (typeof_expr e1)) v2 (Ty.basetype_to_compcert_type (typeof_expr e2)) m2 = Some v). {
          pose proof State.sem_binary_operation_write_cell_invariant op v1 v2.
          eapply H2 with (m4:=m2) in H13; trivial. eauto.
        }
        rewrite <- IHe1 with (st1:=(ge, e, m)) in H11; eauto. 
        2: {eapply Forall_app in H0; destruct H0; trivial. }
        rewrite <- IHe2 with (st1:=(ge, e, m)) in H12; eauto.
        2: {eapply Forall_app in H0; destruct H0; trivial. }
        eapply eval_binop; eauto.
        assert (ge = ge2). 
        {inv H. clear - H16 H15. destruct H16. destruct H15. subst; trivial. }
        subst. trivial.
  Qed.

  Lemma instr_semantics_stable_under_state_eq:
    forall i p wcs rcs st1 st2 st1' st2',
      State.eq st1 st1' ->
      State.eq st2 st2' ->
      instr_semantics i p wcs rcs st1 st2 ->
      instr_semantics i p wcs rcs st1' st2'.
  Proof.
    destruct i.
    - intros. inv H1. econs; eauto.
      eapply State.eq_sym in H.
      eapply State.eq_trans; eauto.  
      eapply State.eq_trans; eauto.  
    - intros. inv H1. 
      econs; trivial.
      instantiate (1:=v).
      eapply eval_expr_prsv_val_if_state_eq; eauto.
      eapply State.write_cell_stable_under_eq; eauto.
  Qed.


  Fixpoint ma_expr_eqb (e1 e2: ma_expr) := 
    match e1, e2 with 
    | MAval v, MAval v' => Z.eqb v v'
    | MAvarz n, MAvarz n' => 
        Nat.eqb n n'
    | MAunop op r, MAunop op' r' => 
      unaryop_eq_dec op op' && ma_expr_eqb r r'
    | MAbinop op r1 r2, MAbinop op' r1' r2' =>
      biop_eq_dec op op' && ma_expr_eqb r1 r1' && ma_expr_eqb r2 r2'
    | _, _ => false
    end.
  
  Fixpoint ma_exprlist_eqb (el1 el2: ma_exprlist) := 
    match el1, el2 with
    | MAsingleton r1, MAsingleton r2 => 
      ma_expr_eqb r1 r2
    | MAcons r1 rl1, MAcons r2 rl2 => 
      ma_expr_eqb r1 r2 && ma_exprlist_eqb rl1 rl2
    | _, _ => false
    end.
  
  Definition arr_access_eqb (a a': arr_access):= 
    match a, a' with
    | Aarr id el ty, Aarr id' el' ty' => 
      Pos.eqb id id' && ma_exprlist_eqb el el' && Ty.basetype_eqb ty ty'
    | Avar id ty, Avar id' ty' =>
      Pos.eqb id id' && Ty.basetype_eqb ty ty'
    | _, _ => false
    end.
  
  Fixpoint expr_eqb (e1 e2: expr) := 
    match e1, e2 with 
    | Eval v ty, Eval v' ty' => 
      Val.eqb v v' && Ty.basetype_eqb ty ty'
    (* | Evar id ty, Evar id' ty' =>  *)
      (* Pos.eqb id id' && type_eqb ty ty' *)
    | Evarz n ty, Evarz n' ty' 
      => Nat.eqb n n' && Ty.basetype_eqb ty ty'
    | Eaccess a ty, Eaccess a' ty' => 
      arr_access_eqb a a' && Ty.basetype_eqb ty ty'
    | Eunop op r ty, Eunop op' r' ty' => 
      unaryop_eq_dec op op' && expr_eqb r r' && Ty.basetype_eqb ty ty'
    | Ebinop op r1 r2 ty, Ebinop op' r1' r2' ty' =>
      biop_eq_dec op op' && expr_eqb r1 r1' && expr_eqb r2 r2' && Ty.basetype_eqb ty ty'
    (* | Eseqand r1 r2 ty, Eseqand r1' r2' ty' =>
      expr_eqb r1 r1' && expr_eqb r2 r2' && type_eqb ty ty'
    | Eseqor r1 r2 ty, Eseqor r1' r2' ty' =>
      expr_eqb r1 r1' && expr_eqb r2 r2' && type_eqb ty ty' *)
    | _, _ => false
    end.
  
  Definition cinst_eqb (inst1 inst2: CInstr) := 
    match inst1, inst2 with 
    | Iskip, Iskip => true 
    | Iassign a1 e1, Iassign a2 e2 => 
      arr_access_eqb a1 a2 && expr_eqb e1 e2
    | _, _ => false 
    end
  . 

  Definition eqb (i1 i2: t) : bool :=
    cinst_eqb i1 i2.

  Lemma ma_expr_eqb_refl: 
    forall e, 
      ma_expr_eqb e e = true.
  Proof.
    induction e; 
    unfold ma_expr_eqb; fold ma_expr_eqb. 
    {
      eapply Z.eqb_refl.
    }
    {
        eapply Nat.eqb_refl.
    }
    {
      rewrite andb_true_iff. 
      split. eapply unaryop_eqb_refl. eapply IHe.
    }
    {
      do 2 rewrite andb_true_iff.
      eapply and_assoc.
      splits.
      eapply biop_eqb_refl.
      eapply IHe1.
      eapply IHe2.
    }
  Qed.
  
  Lemma ma_expr_eqb_eq: 
    forall e e', 
      ma_expr_eqb e e' = true <-> 
      e = e'.
  Proof.
    induction e. 
    {
      intros. split.
      {
        intro.
        unfold ma_expr_eqb in H.
        destruct e' eqn:He'; tryfalse.
        eapply Z.eqb_eq in H.
        subst; trivial.
      }
      {
        intros.
        unfold ma_expr_eqb.
        destruct e' eqn:He'; tryfalse.
        inv H. eapply Z.eqb_refl. 
      }
    }
    {
      intros. split.
      {
        intro.
        unfold ma_expr_eqb in H.
        destruct e' eqn:He'; tryfalse.
        eapply Nat.eqb_eq in H.
        subst; trivial.
      }
      {
        intros.
        unfold ma_expr_eqb.
        destruct e' eqn:He'; tryfalse.
        inv H.
        rewrite Nat.eqb_eq; trivial.
      }
    }
    { 
      intros. split.
      {
        intro.
        unfold ma_expr_eqb in H.
        fold ma_expr_eqb in H.
        destruct e' eqn:He'; tryfalse.
        eapply andb_true_iff in H.
        destruct H.
        eapply unaryop_eqb_eq in H.
        eapply IHe in H0.
        subst; trivial.
      }
      {
        intros.
        rewrite H.
        eapply ma_expr_eqb_refl.
      }
    }
    {
      intro. split.
      {
        intro.
        unfold ma_expr_eqb in H.
        fold ma_expr_eqb in H.
        destruct e' eqn:He'; tryfalse.
        do 2 rewrite andb_true_iff in H.
        do 2 destruct H.
        eapply biop_eqb_eq in H.
        eapply IHe1 in H1.
        eapply IHe2 in H0.
        subst; trivial.
      }
      {
        intro.
        rewrite H.
        eapply ma_expr_eqb_refl.
      }
    }
  Qed.
  
  Lemma ma_exprlist_eqb_eq: 
    forall es es', 
      ma_exprlist_eqb es es' = true <-> 
      es = es'.
  Proof.
    induction es. 
    {
      intros. split.
      {
        intro.
        destruct es'; tryfalse.
        simpls.
        eapply ma_expr_eqb_eq in H. subst; trivial.
      }
      {
        intro.
        rewrite <- H.
        simpls.
        eapply ma_expr_eqb_refl.
      }
    }
    {
      intros. split.
      {
        intros.
        destruct es'; tryfalse.
        simpls.
        rewrite andb_true_iff in H.
        destruct H.
        eapply ma_expr_eqb_eq in H.
        eapply IHes in H0. 
        subst; trivial.
      }
      {
        intro.
        rewrite <- H.
        simpls.
        rewrite andb_true_iff.
        split.
        eapply ma_expr_eqb_refl.
        eapply IHes; trivial.
      }
    }
  Qed.
  
  Lemma arr_access_eqb_eq: 
      forall a a', 
      arr_access_eqb a a' = true <-> 
      a = a'.
  Proof.
    intros. split.
    { 
      intro.
      unfold arr_access_eqb in H.
      destruct a; destruct a'; tryfalse.
      {
        rewrite andb_true_iff in H.
        destruct H.
        eapply Pos.eqb_eq in H.
        eapply Ty.basetype_eqb_eq in H0.
        subst; trivial.
      }
      {
        do 2 rewrite andb_true_iff in H.
        do 2 destruct H.
        eapply Pos.eqb_eq in H.
        eapply ma_exprlist_eqb_eq in H1.
        eapply Ty.basetype_eqb_eq in H0.
        subst; trivial.
      }
    }
    {
      intro.
      rewrite H.
      unfold arr_access_eqb.
      destruct a'.
      {
        rewrite andb_true_iff.
        split.
        eapply Pos.eqb_refl.
        eapply Ty.basetype_eqb_eq; trivial.
      }
      {
        do 2 rewrite andb_true_iff.
        eapply and_assoc. splits; simpls.
        eapply Pos.eqb_eq; trivial.
        eapply ma_exprlist_eqb_eq; trivial.
        eapply Ty.basetype_eqb_eq; trivial.
      }
    }
  Qed.
  
  Lemma expr_eqb_eq: 
    forall e1 e2, 
      expr_eqb e1 e2 = true <-> 
      e1 = e2.
  Proof.
    induction e1.
    {
      intro. split. 
      {
        intro.
        destruct e2 eqn:He2; tryfalse.
        simpls.
        rewrite andb_true_iff in H. destruct H.
        eapply Val.eqb_eq in H.
        eapply Ty.basetype_eqb_eq in H0.
        subst; trivial.
      }
      {
        intro.
        destruct e2 eqn:He2; tryfalse.
        rewrite H.
        simpls.
        rewrite andb_true_iff.
        split; trivial.
        eapply Val.eqb_eq; trivial.
        eapply Ty.basetype_eqb_eq; trivial.
      }
    }
    {
      intro. split.
      {
        intro.
        destruct e2 eqn:He2; tryfalse; simpls; try destruct oid; tryfalse.         
        rewrite andb_true_iff in H.
        destruct H.
        eapply Nat.eqb_eq in H.
        eapply Ty.basetype_eqb_eq in H0.
        subst; trivial.
      }
      {
        intro.
        destruct e2 eqn:He2; tryfalse. 
        rewrite H. simpls.
        rewrite andb_true_iff.
        split; trivial.
        eapply Nat.eqb_eq; trivial.
        eapply Ty.basetype_eqb_eq; trivial.
      } 
    }
    {
      intro. split.
      {
        intro.
        destruct e2 eqn:He2; tryfalse.
        simpls.
        rewrite andb_true_iff in H. destruct H.
        eapply arr_access_eqb_eq in H.
        eapply Ty.basetype_eqb_eq in H0.
        subst; eauto.
      }
      {
        intro.
        destruct e2 eqn:He2; tryfalse.
        rewrite H.
        simpls.
        rewrite andb_true_iff.
        split; trivial.
        eapply arr_access_eqb_eq; trivial.
        eapply Ty.basetype_eqb_eq; trivial.
      }
    }
    {
      intro. split. 
      {
        intro.
        destruct e2 eqn:He2; tryfalse.
        simpls.
        do 2 rewrite andb_true_iff in H. 
        do 2 destruct H.
        eapply unaryop_eqb_eq in H.
        eapply IHe1 in H1.
        eapply Ty.basetype_eqb_eq in H0.
        subst; eauto.
      }
      {
        intro.
        rewrite <- H.
        simpls.
        do 2 rewrite andb_true_iff.
        eapply and_assoc.
        splits; trivial.
        eapply unaryop_eqb_eq; trivial.
        rewrite IHe1; trivial.
        eapply Ty.basetype_eqb_eq; trivial.
      }
    }
    {
      intro. split. 
      {
        intro.
        destruct e2 eqn:He2; tryfalse.
        simpls.
        do 3 rewrite andb_true_iff in H.
        do 3 destruct H.
        eapply biop_eqb_eq in H.
        eapply IHe1_1 in H2.
        eapply IHe1_2 in H1.
        eapply Ty.basetype_eqb_eq in H0.
        subst; eauto.
      }
      {
        intro.
        rewrite <- H.
        simpls.
        do 3 rewrite andb_true_iff.
        do 2 eapply and_assoc.
        splits; trivial.
        eapply biop_eqb_eq; trivial.
        eapply IHe1_1; trivial.
        eapply IHe1_2; trivial.
        eapply Ty.basetype_eqb_eq; trivial.
      }
    }
  Qed.
  
  
  Lemma cinst_eqb_eq: 
    forall i1 i2, 
      cinst_eqb i1 i2 = true <-> 
      i1 = i2.
  Proof.
    intros. split.
    {
      intro.
      destruct i1; destruct i2; simpl; tryfalse; try tauto.
      simpls.
      eapply andb_true_iff in H.
      destruct H.
      eapply arr_access_eqb_eq in H.
      eapply expr_eqb_eq in H0.
      subst; eauto.
    }
    {
      intro.
      subst.
      destruct i2; simpl; trivial.
      eapply andb_true_iff. split.
      eapply arr_access_eqb_eq; trivial.
      eapply expr_eqb_eq; trivial.
    }
  Qed.

  Lemma eqb_eq : forall i1 i2, eqb i1 i2 = true <-> i1 = i2.
  Proof. 
      intros. unfold eqb. 
      eapply cinst_eqb_eq; eauto.
  Qed.


  Definition eval_arr_access_to_function (a: arr_access): option AccessFunction 
  := match a with
  | Avar id _ => Some (id, nil)
  | Aarr id el _ => 
    match eval_maexpr_list_symb el with
    | Some func => Some (id, func) 
    | None => None
    end
  end.

  Fixpoint eval_expr_access_to_functions (e: expr): option (list AccessFunction) :=
    match e with
    | Eval _ _ => Some nil
    | Evarz id _ => Some nil
    | Eaccess a _ => 
      match eval_arr_access_to_function a with
      | Some func => Some (func :: nil)
      | None => None
      end
    | Eunop _ e _ =>
      match eval_expr_access_to_functions e with
      | Some func => Some func
      | None => None
      end
    | Ebinop _ e1 e2 _ =>
      match eval_expr_access_to_functions e1, eval_expr_access_to_functions e2 with
      | Some func1, Some func2 => Some (List.app func1 func2)
      | _, _ => None
      end
    end.


  (** FIXME *)
  Definition waccess (i: t): option (list AccessFunction) := 
    match i with
    | Iskip => Some nil
    | Iassign a e => match eval_arr_access_to_function a with 
      | Some func => Some (func :: nil)
      | None => None
      end
    end
  .

  Definition raccess (i: t): option (list AccessFunction) := 
    match i with
    | Iskip => Some nil
    | Iassign a e => eval_expr_access_to_functions e
    end         
  .

  (* Definition valid_access_cells (p: DomIndex) (cells: list MemCell) (al: list AccessFunction): Prop :=
    forall c,
      In c cells ->
      exists a,
        In a al ->
        cell_eq (exact_cell a p) c. *)

(* forall p, p|=i access cell c, c equals to some (wa, p) while wa in wal*)
  (* Definition valid_waccess_function (wal: list AccessFunction) (i: t): Prop := 
    forall p wa,
      State.compat st p ->
      instr_semantics i p envv wcells rcells st st' ->
      exists wa,
        In wa wal /\ In wcells  *)
  (* Definition valid_raccess_function (ral: list AccessFunction) (i: t): Prop := True. *)

  Definition valid_access_function (wal: list AccessFunction) (ral: list AccessFunction) (i: t): Prop := 
    forall p st st' wcells rcells,
      (* State.compat st p -> *)
      instr_semantics i p wcells rcells st st' ->
      valid_access_cells p wcells wal /\ valid_access_cells p rcells ral.

  (* if always return true, we suppose the access function always correct *)
  Definition access_function_checker_access 
    (al: list AccessFunction) (a: arr_access) := 
    match a with
    | Avar id _ =>
        existsb (fun (a:AccessFunction) => 
          let (id', func) := a in 
          Pos.eqb id' id && Nat.eqb (length func) 0
        ) al
    | Aarr id el _ => 
        match eval_maexpr_list_symb el with
        | Some func' => 
          existsb (fun (a:AccessFunction) => 
            let (id', func) := a in 
            Pos.eqb id' id &&
            Nat.eqb (length func) (length func') &&
            forallb (fun (aff1aff2: (list Z * Z) * (list Z * Z)) => 
              let (aff1, aff2) := aff1aff2 in
              let (v1, c1) := aff1 in
              let (v2, c2) := aff2 in
              is_eq v1 v2 && Z.eqb c1 c2 
            ) (combine func func')
          ) al
        | None => false
        end
    end
  . 

  (* expr only reads, so only read access function list here *)
  Fixpoint access_function_checker_e (rl: list AccessFunction) (e: expr): bool := 
    match e with
    | Eval v _ => true
    | Evarz n _ => true
    | Eunop _ e _ =>
      access_function_checker_e rl e
    | Ebinop _ e1 e2 _ => 
      access_function_checker_e rl e1 && 
      access_function_checker_e rl e2
    | Eaccess a _ =>
      access_function_checker_access rl a
    end
  .

  Definition access_function_checker (wl rl: list AccessFunction) (i: t): bool :=
    match i with
    | Iskip => true
    | Iassign a e =>
      access_function_checker_access wl a &&
      access_function_checker_e rl e
    end.


  Lemma access_function_checker_access_correct:
    forall al a p cell,
      access_function_checker_access al a = true ->
      access_cell a p cell ->
      valid_access_cells p [cell] al.
  Proof.
    intros.
    unfold access_function_checker_access in H.
    unfold valid_access_cells.
    intros c Hin. inv Hin; tryfalse.
    destruct a eqn:Ha.
    - (* access a variable *) 
      eapply existsb_exists in H.
      destruct H as (af & Haf & H).
      exists af.
      destruct af as (id' & func').
      rewrite andb_true_iff in H.
      destruct H. eapply Pos.eqb_eq in H. eapply Nat.eqb_eq in H1.
      eapply length_zero_iff_nil in H1. subst.
      split; trivial.
      eapply access_cell_var_implies_cell_eq; eauto.
    - (* acccess an array *)
      destruct (eval_maexpr_list_symb el) eqn:Heval; tryfalse.
      eapply existsb_exists in H.
      destruct H as (af & Haf & H).
      exists af.
      split; trivial.
      eapply access_cell_arr_implies_cell_eq; eauto.
  Qed.

  Lemma access_function_checker_expr_correct:
    forall e rl p rcells st v,
      access_function_checker_e rl e = true ->
      eval_expr e p rcells st v ->
      valid_access_cells p rcells rl.
  Proof. 
    induction e.
    - intros. simpls. inv H0. 
      unfold valid_access_cells. intros. inv H0.
    - intros. simpls. inv H0. 
      unfold valid_access_cells. intros. inv H0.
    - intros. simpls. inv H0.
      eapply  access_function_checker_access_correct; eauto.
    - intros. simpls. inv H0.
      eapply IHe; eauto.
    - intros. simpls. rewrite andb_true_iff in H.
      destruct H. inv H0.
      eapply IHe1 with (p:=p) (rcells:=rcs1) in H11; eauto. 
      eapply IHe2 with (p:=p) (rcells:=rcs2) in H12; eauto.
      clear - H11 H12.
      unfolds valid_access_cells. intros. eapply in_app in H.
      destruct H.
      eapply H11; eauto.
      eapply H12; eauto.
  Qed. 

  (** correct access function implies BC condition *)
  Lemma access_function_checker_correct:
    forall wl rl i, 
      access_function_checker wl rl i = true -> 
      valid_access_function wl rl i.
  Proof. 
    intros.
    unfold access_function_checker in H.
    unfold valid_access_function. intros.
    destruct i.
    - (* Iskip *)
      inv H0. firstorder.
    - (* Iassign *)
      rewrite andb_true_iff in H.
      destruct H as (WC & RC).
      inv H0. split.
      + (* write *)
        clear H3 RC.
        eapply access_function_checker_access_correct; eauto.
      + (* read *)
        clear H2 H9 WC.
        eapply access_function_checker_expr_correct; eauto.
  Qed.

  (* Well formed check should include this. *)
  Definition check_never_written (varctxt: list ident) (i: t): bool :=
    match i with
    | Iskip => true
    | Iassign a e => 
      match a with
      | Avar id _ => 
        negb (existsb (fun x => Pos.eqb x id) varctxt)
      | Aarr id _ _ =>
        negb (existsb (fun x => Pos.eqb x id) varctxt)
      end
    end.

  Lemma bc_condition_implie_permutbility:
    forall i1 p1 wcs1 rcs1 st1 st2 st3 i2 p2 wcs2 rcs2,
      NonAlias st1 ->
      (instr_semantics i1 p1 wcs1 rcs1 st1 st2 /\ instr_semantics i2 p2 wcs2 rcs2 st2 st3) ->
      (
        Forall (fun wc2 => 
            Forall (fun wc1 => cell_neq wc1 wc2) wcs1
        ) wcs2
      )
      /\
      (
          Forall (fun rc2 => 
              Forall (fun wc1 => cell_neq wc1 rc2) wcs1
          ) rcs2
      )
      /\
      (
          Forall (fun wc2 => 
              Forall (fun rc1 => cell_neq rc1 wc2 ) rcs1
          ) wcs2
      )
      ->
      (exists st2' st3', instr_semantics i2 p2 wcs2 rcs2 st1 st2' /\ instr_semantics i1 p1 wcs1 rcs1 st2' st3' /\ State.eq st3 st3')
    .
  Proof. 
    intros until rcs2.
    intros NOALIAS SEMA BC.
    destruct SEMA as (SEMA1 & SEMA2).
    destruct BC as (WW & WR & RW).
    inv SEMA1; inv SEMA2; tryfalse.
    {
      (* Case: skip, skip. trivial. *)
      exists st3 st3. 
      split; econs; eauto. 
      eapply State.eq_trans; eauto. econs; eauto.
      eapply State.eq_refl.
      eapply State.eq_refl.
    }
    {
      (* Case: skip, assign. trivial. *)
      exists st3 st3. splits.
      eapply eval_expr_prsv_val_if_state_eq with (st':=st1) in H1. 
      econs; eauto.
      eapply State.write_cell_stable_under_eq; eauto.
      eapply State.eq_sym; trivial. eapply State.eq_refl. 
      eapply State.eq_sym; trivial. econs; eapply State.eq_refl.
      eapply State.eq_refl.
    }
    {
      (* Case: assign, skip. trivial. *)
      exists st1 st3. splits. econs; eauto. 
      eapply State.eq_refl.
      econs; eauto. 
      eapply State.write_cell_stable_under_eq 
        with (st1:=st1) (st1':=st1) (st2:=st2) (st2':=st3) in H1; eauto.
      eapply State.eq_refl. 
      eapply State.eq_refl.
    }
    {
      (* Case: assign, assign. *)    
      rename H into Hw1. 
      rename v0 into v2. rename a0 into a2. rename a into a1. rename wcell0 into wcell2. rename v into v1. rename e into e1. rename e0 into e2. rename wcell into wcell1.
      assert (exists st1' st2', State.write_cell_dec wcell2 (typeof_access a2) v2 st1' = Some st2' /\ State.eq st1 st1'). {
        clear - H1 H4.
        inv H1. inv H4.
        destruct st1 as ((ge1 & env1) & m1) eqn:Hst1. 
        destruct st2 as ((ge2 & env2) & m2) eqn:Hst2.
        destruct st3 as ((ge3 & env3) & m3) eqn:Hst3.
        simpls.
        destruct H10 as (EQGE & EQE & EQM4); subst.
        destruct H11 as (EQGE & EQE & EQM2); subst.
        destruct H18 as (EQGE & EQE & EQM3); subst.
        destruct H17 as (EQGE & EQE & EQM1); subst.
        eapply State.advance_store_valid with (m2:=m') in H15; eauto.
        destruct H15 as (m2' & Hw2').
        exists (ge2,env2,m) (ge2,env2,m2').
        simpls.
        (* destruct H *)
        rewrite H1. rewrite H9. rewrite H12.
        rewrite Ty.basetype_eqb_refl. rewrite H13. rewrite H14.
        rewrite Hw2'; trivial. splits; trivial. 
        - clear - EQM4. unfolds State.mem_eq. destruct EQM4; split; trivial.
        - clear - EQM2 EQM1. unfolds State.mem_eq.
          destruct EQM1. destruct EQM2. split; trivial.
          eapply Memory.Mem.extends_extends_compose; eauto.
          eapply Memory.Mem.extends_extends_compose; eauto.
      }
      destruct H as (st1'&st2'& Hw2_dec & HEQ1).
      eapply State.write_cell_dec_correct in Hw2_dec.
      assert (cell_neq wcell1 wcell2) as NEQ. {
        clear - WW.
        inv WW. inv H1. trivial.
      }
      assert (State.write_cell wcell2 (typeof_access a2) v2 st1 st2'). {
        clear - Hw2_dec HEQ1.
        eapply State.write_cell_stable_under_eq in Hw2_dec; eauto.
        eapply State.eq_sym; trivial.
        eapply State.eq_refl.
      }
      pose proof State.write_after_write_cell_neq wcell1 wcell2 v1 v2 
         st1 st2 st3 st2' (typeof_access a1) (typeof_access a2) H1 H4 NEQ H NOALIAS.
      destruct H5 as (st3' & Hw1' & Heq).
      (* Now we tries to prove the execution is permutable *) 
      (* 1. instantiate st2' with (assign wcell2 with v2)*)
      exists st2' st3'. split.
      (* 2. Then we prove Iassign a2 e2 => st2': all val of e2 do not read wcell1, so v2 does not change (WR). wcell2 is still accessible. case finished. *)
      - eapply IassignSem with (v:=v2); eauto.
        + 
          eapply eval_expr_prsv_val_if_neq_wr_cell with (wc:=wcell1) (st2:=st2) (v:=v2); eauto.
          clear - WR.
          eapply Forall_forall. intros.
          eapply Forall_forall in WR; simpls; eauto.
          inv WR. eapply cell_neq_symm. trivial.
      (* 3. Then we prove Iassign a1 e1 (st2') => st3: all val of e1 do not read wcell2 (RW), so v1 does not change; and wcell1 is not wcell2 (WW), so the final state are equal (setoid) *)
      - split. 
        eapply IassignSem with (v:=v1); eauto.
        + 
          eapply eval_expr_prsv_val_if_neq_wr_cell with (st1:=st1) (wc:=wcell2) (v':=v2) (bty:=(typeof_access a2)); trivial.
          inv RW. trivial.
        + trivial.
    }
  Qed.
End CInstr.

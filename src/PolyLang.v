(** inner representation for Poly *)
Require Import Bool.
Require Import Base.
Require Import List.
Require Import SetoidList.
Require Import MSets.
Require Import Coq.MSets.MSetProperties.
Require Import Setoid Morphisms.
Require Import Linalg.
Require Import Base.
Require Import LinalgExt.
Require Import SelectionSort.
Require Import StablePermut.
Require Import Classical.
Require Import ZArith.
Require Import PolyBase.
Require Import TilingWitness.
Require Import PointWitness.
Require Import Misc.
Require Import ListExt.
Require Import Sorting.Sorted.
Require Import Permutation.
Require Import Coqlib.
Require Import LibTactics.
Require Import sflib.
Import ListNotations.

Require Import InstanceListSema.

Require Import StateTy.
Require Import InstrTy.

Require Import AST.
Require Import OpenScop.
Require Import Result.

Require Import ImpureAlarmConfig.

Import ListNotations.

Module PolyLang (Instr: INSTR).

Definition ident := Instr.ident.
Module State := Instr.State.
Module Ty := Instr.Ty.
Definition NonAlias := Instr.NonAlias.
Module ILSema := ILSema Instr.

Record PolyInstr := {
  pi_depth : nat;                    (** nested depth in nested loop *)
  pi_instr : Instr.t;                (** instruction *)
  pi_poly : Domain;                  (** domain *)
  pi_schedule : Schedule;            (** schedule function*)
  pi_point_witness: point_space_witness; (** current/base point-space relation *)
  pi_transformation: Transformation; (** source/instruction transformation *)
  pi_access_transformation: Transformation; (** validator/access transformation *)
  pi_waccess: list AccessFunction;        (** write accesses *)
  pi_raccess: list AccessFunction;   (** read accesses *)
}.

Definition dummy_pi := {|
  pi_depth := 0;
  pi_instr := Instr.dummy_instr ;
  pi_poly := nil;
  pi_point_witness := PSWIdentity 0;
  pi_transformation := nil;
  pi_access_transformation := nil;
  pi_schedule := nil;
  pi_waccess := [aff_func_dummy];
  pi_raccess := [aff_func_dummy];
|}.

(** single polyhedral program is defined as triple (pis, varctxt, vars) *)
(** where pis stands for polyhedral instructions *)
(** varctxt stands for symbolic constants (those not written in the loop nests) *)
(** note: we will assure varctxt (with a simple theorem) remains untouch during executions *)
(** vars stands for all variables that may appear in the fragments, associated with its type *)
(** note: vars can be superset of actual free variables of the loop nests, and it is used for state's initialization *)
(** note: nameless iterators are not recorded in `vars`, they do not touch the semantics of underlying Instr. *)
Definition t := ((list PolyInstr) * (list ident) * (list (ident * Ty.t)))%type.

Definition pinstr_current_dim (env : list ident) (pi : PolyInstr) : nat :=
  let cols := (length env + pi.(pi_depth))%nat in
  Nat.max cols
    (Nat.max (poly_nrl pi.(pi_poly))
       (poly_nrl pi.(pi_schedule))).

Definition pprog_current_dim (pp : t) : nat :=
  let '(pis, varctxt, vars) := pp in
  List.fold_left Nat.max
    (List.map (pinstr_current_dim varctxt) pis)
    (length vars).

Lemma fold_left_max_ge_init :
  forall ds acc,
    acc <= List.fold_left Nat.max ds acc.
Proof.
  induction ds as [|d ds IH]; intros acc; simpl.
  - lia.
  - eapply Nat.le_trans.
    + apply Nat.le_max_l.
    + apply IH.
Qed.

Lemma fold_left_max_mono_acc :
  forall ds acc1 acc2,
    acc1 <= acc2 ->
    List.fold_left Nat.max ds acc1 <= List.fold_left Nat.max ds acc2.
Proof.
  induction ds as [|d ds IH]; intros acc1 acc2 Hle; simpl.
  - exact Hle.
  - eapply IH.
    apply Nat.max_le_compat_r.
    exact Hle.
Qed.

Lemma fold_left_max_ge_member :
  forall ds acc x,
    In x ds ->
    x <= List.fold_left Nat.max ds acc.
Proof.
  induction ds as [|d ds IH]; intros acc x Hin; simpl in *.
  - contradiction.
  - destruct Hin as [<- | Hin].
    + eapply Nat.le_trans.
      * apply Nat.le_max_r.
      * apply fold_left_max_ge_init.
    + eapply Nat.le_trans.
      * apply IH; exact Hin.
      * apply fold_left_max_mono_acc.
        apply Nat.le_max_l.
Qed.

Lemma pprog_current_dim_ge_pinstr :
  forall pis varctxt vars pi,
    In pi pis ->
    pinstr_current_dim varctxt pi <= pprog_current_dim (pis, varctxt, vars).
Proof.
  intros pis varctxt vars pi Hin.
  unfold pprog_current_dim.
  assert (Hinmap :
    In (pinstr_current_dim varctxt pi)
       (List.map (pinstr_current_dim varctxt) pis)).
  {
    eapply List.in_map.
    exact Hin.
  }
  eapply fold_left_max_ge_member; eauto.
Qed.

Definition dummy: t := (nil, nil, nil).

(** Some conversion functions for OpenScop format *)

Definition listzzs_to_domain_constr (constr: list Z * Z) (varctxt_dim: nat) (iters_dim: nat): (bool * openscop_constraint) := 
  let (zs, z) := constr in 
  (* because openscop use >= (zs + z >= 0 ), PolyLang use <= (zs <= z) , we flip zs *)
  let zs := map Z.opp zs in
  let varctxt_constr := firstn varctxt_dim zs in 
  let iters_constr := skipn varctxt_dim zs in
  (true, iters_constr ++ varctxt_constr ++ [z]).

Fixpoint list_Z_eqb (xs ys: list Z) : bool :=
  match xs, ys with
  | nil, nil => true
  | x :: xs', y :: ys' => Z.eqb x y && list_Z_eqb xs' ys'
  | _, _ => false
  end.

Definition affine_constraint_eqb (c1 c2: list Z * Z) : bool :=
  let '(zs1, z1) := c1 in
  let '(zs2, z2) := c2 in
  list_Z_eqb zs1 zs2 && Z.eqb z1 z2.

Fixpoint dedup_domain_rows (rows: Domain) : Domain :=
  match rows with
  | nil => nil
  | row :: rows' =>
      let rows'' := dedup_domain_rows rows' in
      if existsb (affine_constraint_eqb row) rows''
      then rows''
      else row :: rows''
  end.

Definition listzzs_to_sctt_constr (idx: nat) (aff_func: list Z * Z) (varctxt_dim: nat) (iters_dim: nat)(sctt_dim:nat) : (bool * openscop_constraint) := 
  let (zs, z) := aff_func in 
  let tgt_aff := (repeat 0%Z idx) ++ [-1%Z] ++ (repeat 0%Z (sctt_dim - idx - 1)) in 
  let varctxt_aff := firstn varctxt_dim zs in 
  let iters_aff := skipn varctxt_dim zs in
  (false, tgt_aff ++ iters_aff ++ varctxt_aff ++ [z]).

Definition zero_affine_function (dim: nat) : (list Z * Z) :=
  (repeat 0%Z dim, 0%Z).

Definition constant_affine_function (dim: nat) (c: Z) : (list Z * Z) :=
  (repeat 0%Z dim, c).

Definition affine_function_is_zero (aff: list Z * Z) : bool :=
  let (zs, z) := aff in
  forallb (Z.eqb 0%Z) zs && Z.eqb z 0%Z.

Definition affine_function_is_const (aff: list Z * Z) : bool :=
  let (zs, _) := aff in
  forallb (Z.eqb 0%Z) zs.

Definition remove_zero_schedule_dims (sched: Schedule) : Schedule :=
  filter (fun aff => negb (affine_function_is_zero aff)) sched.

Definition split_trailing_const_schedule (sched: Schedule) : Schedule * option Z :=
  match rev sched with
  | nil => (nil, None)
  | aff :: sched_rev =>
      let '(zs, c) := aff in
      if affine_function_is_const (zs, c)
      then (rev sched_rev, Some c)
      else (sched, None)
  end.

Definition padded_sctt_out_dim (compact_dim: nat) : nat :=
  S (compact_dim + compact_dim).

Definition zero_sctt_constr
    (idx varctxt_dim iters_dim openscop_sctt_dim: nat) : (bool * openscop_constraint) :=
  listzzs_to_sctt_constr idx
    (zero_affine_function (varctxt_dim + iters_dim))
    varctxt_dim iters_dim openscop_sctt_dim.

Definition constant_sctt_constr
    (idx varctxt_dim iters_dim openscop_sctt_dim: nat) (c: Z)
    : (bool * openscop_constraint) :=
  listzzs_to_sctt_constr idx
    (constant_affine_function (varctxt_dim + iters_dim) c)
    varctxt_dim iters_dim openscop_sctt_dim.

Fixpoint schedule_to_source_like_rows (sched: Schedule) : Schedule :=
  match sched with
  | nil => nil
  | aff1 :: tl =>
      match tl with
      | nil => aff1 :: nil
      | aff2 :: _ =>
          if andb (negb (affine_function_is_const aff1))
                  (negb (affine_function_is_const aff2))
          then aff1 :: zero_affine_function (length (fst aff1)) ::
               schedule_to_source_like_rows tl
          else aff1 :: schedule_to_source_like_rows tl
      end
  end.

Definition source_like_sctt_rows
    (sched: Schedule)
    (tail_const: option Z)
    (dim: nat) : Schedule :=
  match sched with
  | nil =>
      [match tail_const with
       | Some c => constant_affine_function dim c
       | None => zero_affine_function dim
       end]
  | aff :: _ =>
      (if affine_function_is_const aff
       then schedule_to_source_like_rows sched
       else zero_affine_function dim :: schedule_to_source_like_rows sched) ++
      [match tail_const with
       | Some c => constant_affine_function dim c
       | None => zero_affine_function dim
       end]
  end.

Definition affine_rows_to_sctt_constrs
    (rows: Schedule)
    (varctxt_dim iters_dim openscop_sctt_dim: nat)
    : list (bool * openscop_constraint) :=
  mapi_ascend
    (fun idx aff =>
       listzzs_to_sctt_constr idx aff varctxt_dim iters_dim openscop_sctt_dim)
    rows.

Definition tail_const_of_affine (aff: list Z * Z) : option Z :=
  if affine_function_is_zero aff
  then None
  else if affine_function_is_const aff then Some (snd aff) else None.

Definition drop_leading_zero_schedule_row (rows: Schedule) : Schedule :=
  match rows with
  | aff :: rows' =>
      if affine_function_is_zero aff then rows' else rows
  | nil => nil
  end.

Definition source_like_rows_to_compact_schedule
    (rows: Schedule) : Schedule * option Z :=
  let rows' := drop_leading_zero_schedule_row rows in
  let '(body_rows, tail_aff_opt) :=
    match rev rows' with
    | nil => (nil, None)
    | aff :: rows_rev => (rev rows_rev, Some aff)
    end in
  let tail_const :=
    match tail_aff_opt with
    | Some aff => tail_const_of_affine aff
    | None => None
    end in
  (remove_zero_schedule_dims body_rows, tail_const).

  
Definition listzzs_to_access_constr (idx: nat) (aff_func: list Z * Z) (varctxt_dim: nat) (iters_dim: nat) (arr_dim: nat): (bool * openscop_constraint) := 
  let (zs, z) := aff_func in 
  let tgt_aff := (repeat 0%Z (idx+1)) ++ [-1%Z] ++ (repeat 0%Z (arr_dim - idx - 1)) in 
  let varctxt_aff := firstn varctxt_dim zs in 
  let iters_aff := skipn varctxt_dim zs in
  (false, tgt_aff ++ iters_aff ++ varctxt_aff ++ [z]).


Definition access_to_openscop (access: AccessFunction) (ty: RelType) (varctxt_dim: nat) (iters_dim: nat): OpenScop.Relation :=
  let (id, aff_func) := access in 
  let arr_dim := length aff_func in
  {|
    OpenScop.rel_type := ty;
    OpenScop.meta := {|
      OpenScop.row_nb := arr_dim + 1;
      OpenScop.col_nb := arr_dim + 1 + iters_dim + varctxt_dim + 2;
      OpenScop.out_dim_nb := arr_dim + 1;
      OpenScop.in_dim_nb := iters_dim;
      OpenScop.local_dim_nb := 0;
      OpenScop.param_nb := varctxt_dim;
    |};
    OpenScop.constrs :=
      (false, [-1%Z] ++ repeat 0%Z (arr_dim + iters_dim + varctxt_dim) ++ [Zpos id]) ::
      (mapi_ascend (fun idx aff => listzzs_to_access_constr idx aff varctxt_dim iters_dim arr_dim) aff_func) 
    ;
  |}.

Definition pi_to_openscop_statement
    (pi: PolyInstr) (varctxt: list ident) (_global_compact_sctt_dim: nat): option Statement :=
  let normalized_sched := remove_zero_schedule_dims pi.(pi_schedule) in
  let '(sched_core, tail_const) := split_trailing_const_schedule normalized_sched in
  let compact_sctt_dim := List.length sched_core in
  let domain_rows := dedup_domain_rows pi.(pi_poly) in
  let domain_dim := list_max (map 
    (fun (constr: (list Z * Z)) => let (zs, z) := constr in 
      length zs) domain_rows) in
  let varctxt_dim := length varctxt in
  let iters_dim := domain_dim - varctxt_dim in
  let rows := source_like_sctt_rows sched_core tail_const (varctxt_dim + iters_dim) in
  let varctxt_varnames := map Instr.ident_to_varname varctxt in
  let iters_varnames := map Instr.iterator_to_varname (seq 0 (pi.(pi_depth))) in
  match (Instr.to_openscop pi.(pi_instr) (List.app varctxt_varnames iters_varnames)) with
  | Some arr_stmt =>
    let openscop_sctt_dim := padded_sctt_out_dim compact_sctt_dim in
    Some {|
      OpenScop.domain := {|
        (** the domain relation *)
        OpenScop.rel_type := OpenScop.DomTy;
        OpenScop.meta := {|
          OpenScop.row_nb := List.length domain_rows;
          OpenScop.col_nb := iters_dim + varctxt_dim + 2;
          OpenScop.out_dim_nb := iters_dim;
          OpenScop.in_dim_nb := 0;
          OpenScop.local_dim_nb := 0;
          OpenScop.param_nb := varctxt_dim;
        |};
        OpenScop.constrs := map (fun constr => listzzs_to_domain_constr constr varctxt_dim iters_dim) domain_rows;
      |};
      (* schedule *)
      (*
         OpenScop/Pluto does not carry a separate transformation field.
         For source schedules, middle constant rows encode statement-order
         skeleton directly. They must therefore be emitted as constant rows,
         not as "zero row + constant row" pairs; otherwise the resulting
         source scattering no longer matches Clan on imperfect nests.
       *)
      OpenScop.scattering := {|
        OpenScop.rel_type := OpenScop.ScttTy;
        OpenScop.meta := {|
          OpenScop.row_nb := length (source_like_sctt_rows sched_core tail_const (varctxt_dim + iters_dim));
          OpenScop.col_nb := length (source_like_sctt_rows sched_core tail_const (varctxt_dim + iters_dim)) + iters_dim + varctxt_dim + 2;
          OpenScop.out_dim_nb := length (source_like_sctt_rows sched_core tail_const (varctxt_dim + iters_dim));
          OpenScop.in_dim_nb := iters_dim;
          OpenScop.local_dim_nb := 0;
          OpenScop.param_nb := varctxt_dim;
        |};
        OpenScop.constrs :=
          affine_rows_to_sctt_constrs rows varctxt_dim iters_dim (length rows);
      |};  
      OpenScop.access := 
        (map (fun access => access_to_openscop access OpenScop.WriteTy varctxt_dim iters_dim) (pi.(pi_waccess))) ++
        (map (fun access => access_to_openscop access OpenScop.ReadTy varctxt_dim iters_dim) (pi.(pi_raccess)))
      ;
      OpenScop.stmt_exts_opt := 
      Some ([
        OpenScop.StmtBody (
          iters_varnames
        )
        arr_stmt
      ]);  
    |}
  | None => None 
  end
  .

Definition pi_to_openscop_statement_global
    (pi: PolyInstr) (varctxt: list ident) (global_compact_sctt_dim: nat): option Statement :=
  let normalized_sched := remove_zero_schedule_dims pi.(pi_schedule) in
  let '(sched_core_raw, tail_const) := split_trailing_const_schedule normalized_sched in
  let compact_sctt_dim := Nat.max global_compact_sctt_dim (List.length sched_core_raw) in
  let domain_rows := dedup_domain_rows pi.(pi_poly) in
  let domain_dim := list_max (map
    (fun (constr: (list Z * Z)) => let (zs, z) := constr in
      length zs) domain_rows) in
  let varctxt_dim := length varctxt in
  let iters_dim := domain_dim - varctxt_dim in
  let sched_core :=
    repeat (constant_affine_function (varctxt_dim + iters_dim) 0%Z)
      (compact_sctt_dim - List.length sched_core_raw) ++
    sched_core_raw in
  let rows := source_like_sctt_rows sched_core tail_const (varctxt_dim + iters_dim) in
  let varctxt_varnames := map Instr.ident_to_varname varctxt in
  let iters_varnames := map Instr.iterator_to_varname (seq 0 (pi.(pi_depth))) in
  match (Instr.to_openscop pi.(pi_instr) (List.app varctxt_varnames iters_varnames)) with
  | Some arr_stmt =>
    Some {|
      OpenScop.domain := {|
        OpenScop.rel_type := OpenScop.DomTy;
        OpenScop.meta := {|
          OpenScop.row_nb := List.length domain_rows;
          OpenScop.col_nb := iters_dim + varctxt_dim + 2;
          OpenScop.out_dim_nb := iters_dim;
          OpenScop.in_dim_nb := 0;
          OpenScop.local_dim_nb := 0;
          OpenScop.param_nb := varctxt_dim;
        |};
        OpenScop.constrs := map (fun constr => listzzs_to_domain_constr constr varctxt_dim iters_dim) domain_rows;
      |};
      OpenScop.scattering := {|
        OpenScop.rel_type := OpenScop.ScttTy;
        OpenScop.meta := {|
          OpenScop.row_nb := length rows;
          OpenScop.col_nb := length rows + iters_dim + varctxt_dim + 2;
          OpenScop.out_dim_nb := length rows;
          OpenScop.in_dim_nb := iters_dim;
          OpenScop.local_dim_nb := 0;
          OpenScop.param_nb := varctxt_dim;
        |};
        OpenScop.constrs :=
          affine_rows_to_sctt_constrs rows varctxt_dim iters_dim (length rows);
      |};
      OpenScop.access :=
        (map (fun access => access_to_openscop access OpenScop.WriteTy varctxt_dim iters_dim) (pi.(pi_waccess))) ++
        (map (fun access => access_to_openscop access OpenScop.ReadTy varctxt_dim iters_dim) (pi.(pi_raccess)));
      OpenScop.stmt_exts_opt :=
      Some ([
        OpenScop.StmtBody (
          iters_varnames
        )
        arr_stmt
      ]);
    |}
  | None => None
  end
  .

(** Part 0: transformation from and to OpenScop *)
Definition to_openscop (pol: t): option OpenScop := 
  let '(pis, varctxt, vars) := pol in 
  let context := {|
    OpenScop.lang := "C";
    OpenScop.param_domain := {|
      OpenScop.rel_type := OpenScop.CtxtTy;
      OpenScop.meta := {|
        OpenScop.row_nb := 0;
        OpenScop.col_nb := List.length (varctxt) + 2;
        OpenScop.out_dim_nb := 0;
        OpenScop.in_dim_nb := 0;
        OpenScop.local_dim_nb := 0;
        OpenScop.param_nb := List.length (varctxt);
      |};
      OpenScop.constrs := nil;
    |};
    OpenScop.params := Some (List.map Instr.ident_to_varname varctxt);  
  |} in 
  let ostatements := unwrap_option (List.map (fun pi => pi_to_openscop_statement pi varctxt 0) pis) in 
  let glb_exts := (
      ArrayExt (List.map (fun x => (Instr.ident_to_openscop_ident (fst x), Instr.ident_to_varname (fst x))) vars)
  )::nil in 
  match ostatements with
  | Some statements => 
    Some {|
      OpenScop.context := context; 
      OpenScop.statements := statements;
      OpenScop.glb_exts := glb_exts;
    |}
  | None => None
  end
  .

Definition to_openscop_global_padded (pol: t): option OpenScop :=
  let '(pis, varctxt, vars) := pol in
  let context := {|
    OpenScop.lang := "C";
    OpenScop.param_domain := {|
      OpenScop.rel_type := OpenScop.CtxtTy;
      OpenScop.meta := {|
        OpenScop.row_nb := 0;
        OpenScop.col_nb := List.length (varctxt) + 2;
        OpenScop.out_dim_nb := 0;
        OpenScop.in_dim_nb := 0;
        OpenScop.local_dim_nb := 0;
        OpenScop.param_nb := List.length (varctxt);
      |};
      OpenScop.constrs := nil;
    |};
    OpenScop.params := Some (List.map Instr.ident_to_varname varctxt);
  |} in
  let compact_sctt_dim :=
    list_max (List.map
      (fun pi =>
        let normalized_sched := remove_zero_schedule_dims pi.(pi_schedule) in
        let '(sched_core, _) := split_trailing_const_schedule normalized_sched in
        List.length sched_core)
      pis) in
  let ostatements := unwrap_option (List.map (fun pi => pi_to_openscop_statement_global pi varctxt compact_sctt_dim) pis) in
  let glb_exts := (
      ArrayExt (List.map (fun x => (Instr.ident_to_openscop_ident (fst x), Instr.ident_to_varname (fst x))) vars)
  )::nil in 
  match ostatements with
  | Some statements => 
    Some {|
      OpenScop.context := context; 
      OpenScop.statements := statements;
      OpenScop.glb_exts := glb_exts;
    |}
  | None => None
  end
  .

Definition canonical_scattering_output_rowb
    (slot out_dim: nat) (row: bool * openscop_constraint) : bool :=
  let '(is_inequality, coeffs) := row in
  negb is_inequality &&
  Nat.ltb slot out_dim &&
  list_beq Z.t Z.eqb
    (firstn out_dim coeffs)
    (repeat 0%Z slot ++
     [-1%Z] ++
     repeat 0%Z (out_dim - S slot)).

Fixpoint canonical_scattering_output_rowsb
    (slot out_dim: nat)
    (rows: list (bool * openscop_constraint)) : bool :=
  match rows with
  | [] => Nat.eqb slot out_dim
  | row :: rows' =>
      canonical_scattering_output_rowb slot out_dim row &&
      canonical_scattering_output_rowsb (S slot) out_dim rows'
  end.

Definition canonical_function_scatteringb (sctt: Relation) : bool :=
  canonical_scattering_output_rowsb
    O
    (OpenScop.out_dim_nb (OpenScop.meta sctt))
    (OpenScop.constrs sctt).

Definition check_pol_openscop_consistency (pol: t) (scop: OpenScop) : bool :=
  let '(pis, _, _) := pol in
  Nat.eqb (List.length pis) (List.length (OpenScop.statements scop)) &&
  forallb
    (fun stmt =>
       canonical_function_scatteringb (OpenScop.scattering stmt))
    (OpenScop.statements scop).

Fixpoint odd_positions {A: Type} (l: list A) : list A :=
  match l with
  | _ :: x :: xs => x :: odd_positions xs
  | _ => nil
  end.

Definition openscop_constraint_eqb
    (c1 c2: bool * openscop_constraint) : bool :=
  let '(b1, zs1) := c1 in
  let '(b2, zs2) := c2 in
  Bool.eqb b1 b2 && list_beq Z.t Z.eqb zs1 zs2.

Definition openscop_sctt_row_to_affine
    (constr: bool * openscop_constraint)
    (openscop_sctt_dim varctxt_dim iters_dim: nat) : list Z * Z :=
  let '(_, aff) := constr in
  let aff' := List.removelast aff in
  let iters := firstn iters_dim (skipn openscop_sctt_dim aff') in
  let varctxt := skipn iters_dim (skipn openscop_sctt_dim aff') in
  (varctxt ++ iters, List.last aff 0%Z).

Fixpoint even_slots_are_zero_sctt_rows
    (constrs: list (bool * openscop_constraint))
    (slot openscop_sctt_dim varctxt_dim iters_dim: nat) : bool :=
  match constrs with
  | nil => true
  | constr :: constrs' =>
      let slot_ok :=
        if Nat.even slot
        then
          let aff :=
            openscop_sctt_row_to_affine constr openscop_sctt_dim varctxt_dim iters_dim in
          if Nat.eqb slot (openscop_sctt_dim - 1)
          then affine_function_is_const aff
          else affine_function_is_zero aff
        else true in
      slot_ok &&
      even_slots_are_zero_sctt_rows
        constrs' (S slot) openscop_sctt_dim varctxt_dim iters_dim
  end.

Definition uses_padded_sctt_shape
    (constrs: list (bool * openscop_constraint))
    (openscop_sctt_dim varctxt_dim iters_dim: nat) : bool :=
  Nat.odd openscop_sctt_dim &&
  even_slots_are_zero_sctt_rows
    constrs 0 openscop_sctt_dim varctxt_dim iters_dim.

Fixpoint drop_trailing_zero_schedule_rev (sched: Schedule) : Schedule :=
  match sched with
  | aff :: sched' =>
      if affine_function_is_zero aff
      then drop_trailing_zero_schedule_rev sched'
      else aff :: sched'
  | nil => nil
  end.

Definition drop_trailing_zero_schedule (sched: Schedule) : Schedule :=
  rev (drop_trailing_zero_schedule_rev (rev sched)).

Definition from_openscop_sctt_to_pol_schedule
    (sctt: Relation) (varctxt_dim: nat) (iters_dim: nat) (sctt_dim: nat): Schedule :=
  let aff_func := sctt.(OpenScop.constrs) in
  map (fun (aff: bool * openscop_constraint) => 
    let (_, aff) := aff in 
    let aff' := List.removelast aff in
    let iters := firstn iters_dim (skipn sctt_dim aff') in
    let varctxt := skipn iters_dim (skipn sctt_dim aff') in
    (varctxt ++ iters, List.last aff 0%Z)  
  ) aff_func
  .

Definition from_openscop_sctt_to_sched_rows
    (sctt: Relation) (varctxt_dim: nat) (iters_dim: nat): Schedule :=
  let openscop_sctt_dim := OpenScop.out_dim_nb (OpenScop.meta sctt) in
  let aff_func :=
    if uses_padded_sctt_shape
        sctt.(OpenScop.constrs) openscop_sctt_dim varctxt_dim iters_dim
    then odd_positions sctt.(OpenScop.constrs)
    else sctt.(OpenScop.constrs) in
  map (fun (aff: bool * openscop_constraint) =>
    let (_, aff) := aff in
    let aff' := List.removelast aff in
    let iters := firstn iters_dim (skipn openscop_sctt_dim aff') in
    let varctxt := skipn iters_dim (skipn openscop_sctt_dim aff') in
    (varctxt ++ iters, List.last aff 0%Z)
  ) aff_func.

Definition from_openscop_sctt_to_compact_schedule
    (sctt: Relation) (varctxt_dim: nat) (iters_dim: nat) : Schedule * option Z :=
  let openscop_sctt_dim := OpenScop.out_dim_nb (OpenScop.meta sctt) in
  let rows :=
    map (fun (aff: bool * openscop_constraint) =>
      let (_, aff) := aff in
      let aff' := List.removelast aff in
      let iters := firstn iters_dim (skipn openscop_sctt_dim aff') in
      let varctxt := skipn iters_dim (skipn openscop_sctt_dim aff') in
      (varctxt ++ iters, List.last aff 0%Z)
    ) sctt.(OpenScop.constrs) in
  if uses_padded_sctt_shape
      sctt.(OpenScop.constrs) openscop_sctt_dim varctxt_dim iters_dim
  then
    let tail := List.last rows (zero_affine_function (varctxt_dim + iters_dim)) in
    let tail_const :=
      if affine_function_is_zero tail then None
      else if affine_function_is_const tail then Some (snd tail) else None in
    (odd_positions rows, tail_const)
  else split_trailing_const_schedule rows.

Definition from_openscop_sctt_to_source_like_compact_schedule
    (sctt: Relation) (varctxt_dim: nat) (iters_dim: nat) : Schedule * option Z :=
  let openscop_sctt_dim := OpenScop.out_dim_nb (OpenScop.meta sctt) in
  let rows :=
    map (fun (aff: bool * openscop_constraint) =>
      let (_, aff) := aff in
      let aff' := List.removelast aff in
      let iters := firstn iters_dim (skipn openscop_sctt_dim aff') in
      let varctxt := skipn iters_dim (skipn openscop_sctt_dim aff') in
      (varctxt ++ iters, List.last aff 0%Z)
    ) sctt.(OpenScop.constrs) in
  source_like_rows_to_compact_schedule rows.

Definition split_const_and_nonconst_schedule_rows
    (sched: Schedule) : Schedule * Schedule :=
  fold_right
    (fun aff acc =>
      let '(const_rows, dyn_rows) := acc in
      if affine_function_is_const aff
      then (aff :: const_rows, dyn_rows)
      else (const_rows, aff :: dyn_rows))
    (nil, nil) sched.

Fixpoint refill_schedule_from_template
    (template const_rows dyn_rows: Schedule) : Schedule :=
  match template with
  | nil => nil
  | aff :: template' =>
      if affine_function_is_const aff
      then match const_rows with
           | const_row :: const_rows' =>
               const_row :: refill_schedule_from_template template' const_rows' dyn_rows
           | nil =>
               zero_affine_function (length (fst aff)) ::
               refill_schedule_from_template template' nil dyn_rows
           end
      else match dyn_rows with
           | dim :: dims' =>
               dim :: refill_schedule_from_template template' const_rows dims'
           | nil =>
               aff :: refill_schedule_from_template template' const_rows nil
           end
  end.

Fixpoint refill_schedule_from_template_keep_zero_consts
    (template const_rows dyn_rows: Schedule) : Schedule :=
  match template with
  | nil => nil
  | aff :: template' =>
      if affine_function_is_const aff
      then if affine_function_is_zero aff
           then aff :: refill_schedule_from_template_keep_zero_consts template' const_rows dyn_rows
           else match const_rows with
                | const_row :: const_rows' =>
                    const_row :: refill_schedule_from_template_keep_zero_consts template' const_rows' dyn_rows
                | nil =>
                    aff :: refill_schedule_from_template_keep_zero_consts template' nil dyn_rows
                end
      else match dyn_rows with
           | dim :: dims' =>
               dim :: refill_schedule_from_template_keep_zero_consts template' const_rows dims'
           | nil =>
               aff :: refill_schedule_from_template_keep_zero_consts template' const_rows nil
           end
  end.

Fixpoint interleave_zero_schedule_rows (dim : nat) (sched : Schedule) : Schedule :=
  match sched with
  | nil => nil
  | aff :: sched' =>
      zero_affine_function dim :: aff :: interleave_zero_schedule_rows dim sched'
  end.

Definition compact_schedule_to_source_like
    (dim : nat) (sched_core : Schedule) (tail_const : option Z) : Schedule :=
  interleave_zero_schedule_rows dim sched_core ++
  [match tail_const with
   | Some c => constant_affine_function dim c
   | None => zero_affine_function dim
   end].

Definition source_like_rows_from_schedule
    (dim : nat) (sched : Schedule) : Schedule :=
  let normalized_sched := remove_zero_schedule_dims sched in
  let '(sched_core, tail_const) := split_trailing_const_schedule normalized_sched in
  source_like_sctt_rows sched_core tail_const dim.

Definition pad_schedule_to_len (dim len : nat) (sched : Schedule)
  : Schedule :=
  List.app sched
    (List.repeat (zero_affine_function dim) (len - List.length sched)).

Definition source_like_pi_schedule (env_dim : nat) (pi : PolyInstr)
  : Schedule :=
  source_like_rows_from_schedule (env_dim + pi_depth pi) (pi_schedule pi).

Definition source_like_schedule_pprog (pp : t) : t :=
  let '(pis, varctxt, vars) := pp in
  let env_dim := List.length varctxt in
  let canon_pi pi :=
    {|
      pi_depth := pi_depth pi;
      pi_instr := pi_instr pi;
      pi_poly := pi_poly pi;
      pi_schedule := source_like_pi_schedule env_dim pi;
      pi_point_witness := pi_point_witness pi;
      pi_transformation := pi_transformation pi;
      pi_access_transformation := pi_access_transformation pi;
      pi_waccess := pi_waccess pi;
      pi_raccess := pi_raccess pi;
    |} in
  (List.map canon_pi pis, varctxt, vars).

Definition max_schedule_len (pis : list PolyInstr) : nat :=
  List.fold_left Nat.max
    (List.map (fun pi => List.length (pi_schedule pi)) pis) 0.

Definition keep_schedule_row_at
    (env_dim len idx : nat) (pis : list PolyInstr) : bool :=
  existsb
    (fun pi =>
       negb (affine_function_is_zero
               (List.nth idx
                 (pad_schedule_to_len
                    (env_dim + pi_depth pi) len
                    (pi_schedule pi))
                 (zero_affine_function
                    (env_dim + pi_depth pi)))))
    pis.

Fixpoint keep_schedule_rows
    (dim idx : nat) (mask : list bool) (sched : Schedule)
  : Schedule :=
  match mask with
  | nil => nil
  | keep :: mask' =>
      let aff := List.nth idx sched (zero_affine_function dim) in
      let rest := keep_schedule_rows dim (S idx) mask' sched in
      if keep then aff :: rest else rest
  end.

Definition canonicalize_schedule_pprog (pp : t) : t :=
  let '(pis, varctxt, vars) := pp in
  let env_dim := List.length varctxt in
  let len := max_schedule_len pis in
  let mask :=
    List.map
      (fun idx => keep_schedule_row_at env_dim len idx pis)
      (List.seq 0 len) in
  let canon_pi pi :=
    let dim := env_dim + pi_depth pi in
    let sched :=
      keep_schedule_rows dim 0 mask
        (pad_schedule_to_len dim len (pi_schedule pi)) in
    {|
      pi_depth := pi_depth pi;
      pi_instr := pi_instr pi;
      pi_poly := pi_poly pi;
      pi_schedule := sched;
      pi_point_witness := pi_point_witness pi;
      pi_transformation := pi_transformation pi;
      pi_access_transformation := pi_access_transformation pi;
      pi_waccess := pi_waccess pi;
      pi_raccess := pi_raccess pi;
    |} in
  (List.map canon_pi pis, varctxt, vars).

Definition raw_scattering_rows
    (sctt : Relation) (varctxt_dim iters_dim : nat) : Schedule :=
  let openscop_sctt_dim := OpenScop.out_dim_nb (OpenScop.meta sctt) in
  map (fun (aff: bool * openscop_constraint) =>
    openscop_sctt_row_to_affine aff openscop_sctt_dim varctxt_dim iters_dim)
    sctt.(OpenScop.constrs).

Fixpoint overwrite_last_schedule_const
    (sched : Schedule) (tail_const : option Z) : Schedule :=
  match sched with
  | nil => nil
  | aff :: nil =>
      if affine_function_is_const aff
      then match tail_const with
           | Some c => constant_affine_function (length (fst aff)) c :: nil
           | None => aff :: nil
           end
      else aff :: nil
  | aff :: sched' => aff :: overwrite_last_schedule_const sched' tail_const
  end.

Definition refill_source_like_schedule_from_template
    (template rows : Schedule) (tail_const : option Z) : Schedule :=
  let '(const_rows, dyn_rows) := split_const_and_nonconst_schedule_rows rows in
  overwrite_last_schedule_const
    (refill_schedule_from_template_keep_zero_consts template const_rows dyn_rows)
    tail_const.

Definition source_like_template_matches_scattering
    (template : Schedule) (sctt : Relation) (varctxt_dim iters_dim : nat) : bool :=
  let rows := raw_scattering_rows sctt varctxt_dim iters_dim in
  let '(sched_core, tail_const) := source_like_rows_to_compact_schedule rows in
  let sched :=
    refill_source_like_schedule_from_template template sched_core tail_const in
  listzzs_strict_eqb
    (drop_trailing_zero_schedule rows)
    (drop_trailing_zero_schedule
       (source_like_rows_from_schedule (varctxt_dim + iters_dim) sched)).

Definition from_openscop_schedule_only (pol: t) (scop: OpenScop): result t := 
  if check_pol_openscop_consistency pol scop then 
  (
    (* FUTURE: vars may change due to tiling or else *)
  let '(pis, varctxt, vars) := pol in 
  (* not counting trailing zeros *)
  let varctxt_dim := length varctxt in
  let pis' := map (fun (pair: PolyInstr * (OpenScop.Statement)) =>
    let (pi, stmt_scop) := pair in
    let domain_dim := list_max (map 
    (fun (constr: (list Z * Z)) => let (zs, z) := constr in 
      length zs) pi.(pi_poly)) in
    let iters_dim := domain_dim - varctxt_dim in
    let sctt_dim := length (stmt_scop.(OpenScop.scattering).(OpenScop.constrs)) in
    {|
      pi_depth := pi.(pi_depth);
      pi_instr := pi.(pi_instr);
      pi_poly := pi.(pi_poly);
      pi_schedule :=
        from_openscop_sctt_to_pol_schedule
          (OpenScop.scattering stmt_scop) domain_dim iters_dim sctt_dim;
      pi_point_witness := pi.(pi_point_witness);
      pi_transformation := pi.(pi_transformation);
      pi_access_transformation := pi.(pi_access_transformation);
      pi_waccess := pi.(pi_waccess);
      pi_raccess := pi.(pi_raccess);
    |}
  ) (List.combine pis (OpenScop.statements scop)) in
  Okk (canonicalize_schedule_pprog (pis', varctxt, vars))
  )
  else Err "from_openscop_schedule_only: pol and scop are not consistent".


Definition from_openscop_like_source (pol: t) (scop: OpenScop): result t := 
  if check_pol_openscop_consistency pol scop then 
  (
  let '(pis, varctxt, vars) := pol in 
  let varctxt_dim := length varctxt in
  let pis' := map (fun (pair: PolyInstr * (OpenScop.Statement)) =>
    let (pi, stmt_scop) := pair in
    let domain_dim := list_max (map 
      (fun (constr: (list Z * Z)) => let (zs, z) := constr in 
        length zs) pi.(pi_poly)) in
    let iters_dim := domain_dim - varctxt_dim in
    {|
      pi_depth := pi.(pi_depth);
      pi_instr := pi.(pi_instr);
      pi_poly := pi.(pi_poly);
      pi_schedule :=
        if source_like_template_matches_scattering
             pi.(pi_schedule) (OpenScop.scattering stmt_scop) varctxt_dim iters_dim
        then
          let '(sched_core, tail_const) :=
            from_openscop_sctt_to_source_like_compact_schedule
              (OpenScop.scattering stmt_scop) varctxt_dim iters_dim in
          refill_source_like_schedule_from_template pi.(pi_schedule) sched_core tail_const
        else
          from_openscop_sctt_to_pol_schedule
            (OpenScop.scattering stmt_scop)
            domain_dim iters_dim
            (length (OpenScop.constrs (OpenScop.scattering stmt_scop)));
      pi_point_witness := pi.(pi_point_witness);
      pi_transformation := pi.(pi_transformation);
      pi_access_transformation := pi.(pi_access_transformation);
      pi_waccess := pi.(pi_waccess);
      pi_raccess := pi.(pi_raccess);
    |}
  ) (List.combine pis (OpenScop.statements scop)) in
  Okk (pis', varctxt, vars)
  )
  else Err "from_openscop_like_source: pol and scop are not consistent".

Definition from_openscop_ctxt (ctxtscop: OpenScop.ContextScop): list ident := 
  match (OpenScop.params ctxtscop) with
  | Some idlist => map (Instr.varname_to_ident) idlist 
  | None => nil 
  end
.

Fixpoint from_openscop_vars (glb_exts: OpenScop.GlbExts): list ident := 
  match glb_exts with
  | nil => nil
  | (OpenScop.ArrayExt ident_varname_list)::ext' => 
      (* this function binds all ident-varname pairs and return all idents. *)
      Instr.bind_ident_varname (map (fun (id_str: AST.ident * string) => let (id, str) := id_str in 
      (Instr.openscop_ident_to_ident id, str)) ident_varname_list)
  | _::ext' => from_openscop_vars ext'
  end.

Definition from_openscop_iterlist' (stmt_exts: OpenScop.StmtExts): list ident := 
  match stmt_exts with
  | (OpenScop.StmtBody varnames _) :: stmt_ext' =>
      map (Instr.varname_to_ident) varnames
  | nil => nil
  end.
  

Definition from_openscop_iterlist (stmt_exts_opt: option (OpenScop.StmtExts)): list ident :=
  match stmt_exts_opt with
  | Some stmt_exts => from_openscop_iterlist' stmt_exts
  | None => nil
  end.

(* for a openscop constraint, 
  the first bool is 0 for equlity, 1 for >=, 
  and then iterators, then ctxt, 
  the last is the constant *)
Fixpoint from_openscop_domain' (constrs: list (bool * openscop_constraint)) (iters_dim: nat) (varctxt_dim: nat): Domain :=
  match constrs with
  | (true, constr) :: constrs' =>
    (* exclude naive cases *)
    if is_null constr then from_openscop_domain' constrs' iters_dim varctxt_dim
      else
      (-- ((skipn iters_dim (removelast constr)) 
        ++ (firstn iters_dim (removelast constr))), 
        (last constr 0%Z)) ::
      from_openscop_domain' constrs' iters_dim varctxt_dim
  | (false, constr) :: constrs' =>
    if is_null constr then from_openscop_domain' constrs' iters_dim varctxt_dim
    else
      (* a.x + c = 0 becomes a.x <= -c and -a.x <= c. *)
      (   ((skipn iters_dim (removelast constr)) 
            ++ (firstn iters_dim (removelast constr))), 
            (- last constr 0%Z)%Z) ::
      (-- ((skipn iters_dim (removelast constr)) 
            ++ (firstn iters_dim (removelast constr))), 
            (last constr 0%Z)) ::
      from_openscop_domain' constrs' iters_dim varctxt_dim
  | nil => nil
  end.

Definition from_openscop_domain (domain: OpenScop.Relation) (iters_dim varctxt_dim: nat): Domain := 
  from_openscop_domain' (OpenScop.constrs domain) iters_dim varctxt_dim.

Definition from_openscop_access (access: OpenScop.Relation) (iters_dim varctxt_dim: nat): AccessFunction := 
  let constrs' := OpenScop.constrs access in
  let id_constr := hd (false, []) constrs' in
  let constrs := tl constrs' in
  let arr_dim := length constrs in
  let (b, constr) := id_constr in
  let id := Z.to_pos (last constr 999%Z) in
  let aff := map (fun (constr: bool * openscop_constraint) =>
      let (b, aff) := constr in 
      let iters_v := firstn iters_dim (skipn (arr_dim+1) (removelast aff)) in 
      let ctxt_v := skipn iters_dim (skipn (arr_dim+1) (removelast aff)) in
      (ctxt_v ++ iters_v, last aff 0%Z)
    ) constrs in
  (id, aff).

Fixpoint from_openscop_waccesslist (accesslist: list OpenScop.Relation) (iters_dim varctxt_dim: nat) : list AccessFunction := 
  match accesslist with
  | a :: accesslist' => 
    match (OpenScop.rel_type a) with
    | WriteTy => 
      from_openscop_access a iters_dim varctxt_dim :: from_openscop_waccesslist accesslist' iters_dim varctxt_dim
    | _ => from_openscop_waccesslist accesslist' iters_dim varctxt_dim
    end
  | nil => nil
  end.

Fixpoint from_openscop_raccesslist (accesslist: list OpenScop.Relation) (iters_dim varctxt_dim: nat): list AccessFunction :=
  match accesslist with
  | a :: accesslist' => 
    match (OpenScop.rel_type a) with
    | ReadTy => 
      from_openscop_access a iters_dim varctxt_dim :: from_openscop_raccesslist accesslist' iters_dim varctxt_dim
    | _ => from_openscop_raccesslist accesslist' iters_dim varctxt_dim
    end
  | nil => nil
  end.

Definition from_openscop (pol: t) (scop: OpenScop): result t := 
  if check_pol_openscop_consistency pol scop then 
  (
  let '(pis, varctxt, vars) := pol in 
  let varctxt_dim := length varctxt in
  let pis' := map (fun (pair: PolyInstr * (OpenScop.Statement)) =>
    let (pi, stmt_scop) := pair in
    let domain_dim := 
      list_max (map (fun (constr: (bool * list Z)) => let (_, zs) := constr in length zs - 1)
                    (OpenScop.constrs (OpenScop.domain stmt_scop))) in
    let iters_dim := domain_dim - varctxt_dim in
    {|
      pi_depth := pi.(pi_depth);
      pi_instr := pi.(pi_instr);
      pi_poly := from_openscop_domain (OpenScop.domain stmt_scop) iters_dim varctxt_dim;
      pi_schedule := 
        let sctt_dim := length (stmt_scop.(OpenScop.scattering).(OpenScop.constrs)) in
        from_openscop_sctt_to_pol_schedule 
          (OpenScop.scattering stmt_scop) domain_dim iters_dim sctt_dim; 
      pi_point_witness := pi.(pi_point_witness);
      pi_transformation := pi.(pi_transformation);
      pi_access_transformation := pi.(pi_access_transformation);
      pi_waccess := from_openscop_waccesslist (OpenScop.access stmt_scop) iters_dim varctxt_dim;
      pi_raccess := from_openscop_raccesslist (OpenScop.access stmt_scop) iters_dim varctxt_dim;
    |}
  ) (List.combine pis (OpenScop.statements scop)) in
  Okk (pis', varctxt, vars)
  )
  else Err "from_openscop: pol and scop are not consistent".

(* for reordering-only validation, we always premuse transformation is identical *)
Definition create_id_transformation (dim: nat): Transformation := 
  map (fun k => (assign k (1%Z) (V0 dim), 0%Z)) (seq 0 dim)  
.

(* This function transforms a openscop to polyhedral model, with itself. *)
(* Instruction will be omitted (viewed as a dummy one) *)
(* And therefore no instruction-level semantics guarantee anymore. *)
Definition from_openscop_complete (scop: OpenScop): result t := 
  if forallb
       (fun stmt =>
          canonical_function_scatteringb (OpenScop.scattering stmt))
       (OpenScop.statements scop)
  then
    let vars := from_openscop_vars (OpenScop.glb_exts scop) in
    let varctxt := from_openscop_ctxt (OpenScop.context scop) in
    let varctxt_dim := length varctxt in
    let pis' := map (fun (stmt_scop: OpenScop.Statement) =>
      let domain_dim :=
        list_max (map (fun (constr: (bool * list Z)) => let (z, zs) := constr in length zs -1) (OpenScop.constrs (OpenScop.domain stmt_scop))) in
      let iters_dim := domain_dim - varctxt_dim in
      {|
        pi_depth := length (from_openscop_iterlist (OpenScop.stmt_exts_opt stmt_scop));
        pi_instr := Instr.dummy_instr;
        pi_poly := from_openscop_domain (OpenScop.domain stmt_scop) iters_dim varctxt_dim;
        pi_schedule :=
          let sctt_dim := length (stmt_scop.(OpenScop.scattering).(OpenScop.constrs)) in
          from_openscop_sctt_to_pol_schedule
            (OpenScop.scattering stmt_scop) domain_dim iters_dim sctt_dim;
        pi_point_witness := PSWIdentity iters_dim;
        pi_transformation := create_id_transformation (varctxt_dim + iters_dim);
        pi_access_transformation := create_id_transformation (varctxt_dim + iters_dim);
        pi_waccess := from_openscop_waccesslist (OpenScop.access stmt_scop) iters_dim varctxt_dim;
        pi_raccess := from_openscop_raccesslist (OpenScop.access stmt_scop) iters_dim varctxt_dim;
      |}
    ) (OpenScop.statements scop) in
    Okk (pis', varctxt, map (fun var => (var, Ty.dummy)) vars)
  else Err "from_openscop_complete: non-canonical scattering".

Definition wf_pinstr (env: list ident) (vars: list (ident*Ty.t)) (pi: PolyInstr) := 
  (* forall env_dim iters_dim domain_size cols,  *)
    let env_dim := length env in 
    let iters_dim := (pi_depth pi) in 
    (* have at least one constraint *)
    let domain_size := length (pi.(pi_poly)) in 
    let cols := env_dim + iters_dim in 
    let base_cols := env_dim + witness_base_point_dim (pi.(pi_point_witness)) in
    let arg_cols := length (pi.(pi_transformation)) in
    let current_dim := pinstr_current_dim env pi in
    witness_current_point_dim (pi.(pi_point_witness)) = iters_dim /\
    cols <= current_dim /\ 
    poly_nrl (pi_poly pi) <= current_dim /\
    poly_nrl (pi_schedule pi) <= current_dim /\ 
    (* domain cols *)
    exact_listzzs_cols cols (pi.(pi_poly)) /\ 
    (* transformation cols *)
    exact_listzzs_cols base_cols (pi.(pi_transformation)) /\
    exact_listzzs_cols base_cols (pi.(pi_access_transformation)) /\
    (* sched cols *)
    exact_listzzs_cols cols (pi.(pi_schedule)) /\ 
    (* write access function cols *)
    (
      Forall (fun (waccess:AccessFunction) => 
        let (arrid, waccess_func) := waccess in
        exact_listzzs_cols arg_cols waccess_func
      ) (pi.(pi_waccess))
    )
    (* read access function cols *)
    /\ (
      Forall (fun (raccess:AccessFunction) => 
        let (arrid, raccess_func) := raccess in
        exact_listzzs_cols arg_cols raccess_func
      ) (pi.(pi_raccess))
    )
  .  

Definition wf_pinstr_affine (env: list ident) (vars: list (ident*Ty.t)) (pi: PolyInstr) :=
  wf_pinstr env vars pi /\
  pi.(pi_point_witness) = PSWIdentity pi.(pi_depth) /\
  pi.(pi_transformation) = pi.(pi_access_transformation).

(* General witness-aware well-formedness used by tiling and other non-affine
   current-space views. *)
Definition wf_pinstr_general (env: list ident) (vars: list (ident*Ty.t)) (pi: PolyInstr) :=
  wf_pinstr env vars pi /\
  pi.(pi_transformation) = pi.(pi_access_transformation).

Definition wf_pinstr_tiling := wf_pinstr_general.

Definition wf_pprog (pp: t) := 
  let '(pil, varctxt, vars) := pp in 
  let env_dim := length varctxt in
  let var_dim := length vars in
  let pil_dim := length pil in
    env_dim <= var_dim /\
    forall pi, 
      In pi pil -> 
      wf_pinstr varctxt vars pi. 

Definition wf_pprog_affine (pp: t) := 
  let '(pil, varctxt, vars) := pp in 
  let env_dim := length varctxt in
  let var_dim := length vars in
    env_dim <= var_dim /\
    forall pi, 
      In pi pil -> 
      wf_pinstr_affine varctxt vars pi.

(* General witness-aware program well-formedness.  The current main consumer is
   tiling, so the historical [wf_pprog_tiling] name is kept as a compatibility
   alias below. *)
Definition wf_pprog_general (pp: t) :=
  let '(pil, varctxt, vars) := pp in
  let env_dim := length varctxt in
  let var_dim := length vars in
    env_dim <= var_dim /\
    forall pi,
      In pi pil ->
      wf_pinstr_general varctxt vars pi.

Definition wf_pprog_tiling := wf_pprog_general.

Definition current_env_dim_of
    (pw: point_space_witness) (current: list Z) : nat :=
  (length current - witness_current_point_dim pw)%nat.

Definition current_base_point_of
    (pw: point_space_witness) (current: list Z) : list Z :=
  projected_base_point_of_current
    (firstn (current_env_dim_of pw current) current)
    pw current.

Definition current_insert_zeros_constraint
    (d i: nat) (c: list Z * Z) : list Z * Z :=
  (resize i (fst c) ++ repeat 0%Z d ++ skipn i (fst c), snd c).

Fixpoint current_transformation_for_witness
    (env_dim: nat) (pw: point_space_witness) (tf: Transformation) : Transformation :=
  match pw with
  | PSWIdentity _ => tf
  | PSWTiling w =>
      List.map
        (current_insert_zeros_constraint
           (witness_added_dims (PSWTiling w))
           env_dim)
        tf
  | PSWInsertAfterEnv added_dim inner =>
      List.map
        (current_insert_zeros_constraint added_dim env_dim)
        (current_transformation_for_witness env_dim inner tf)
  | PSWInsertAtEnd added_dim inner =>
      List.map
        (fun '(coeffs, rhs) =>
           (resize (length coeffs + added_dim) coeffs, rhs))
        (current_transformation_for_witness env_dim inner tf)
  end.

Definition current_transformation_at
    (env_dim: nat) (pi: PolyInstr) : Transformation :=
  current_transformation_for_witness env_dim pi.(pi_point_witness) pi.(pi_transformation).

Definition current_access_transformation_at
    (env_dim: nat) (pi: PolyInstr) : Transformation :=
  current_transformation_for_witness env_dim pi.(pi_point_witness) pi.(pi_access_transformation).

Definition current_transformation_of
    (pi: PolyInstr) (current: list Z) : Transformation :=
  current_transformation_at
    (current_env_dim_of pi.(pi_point_witness) current) pi.

Definition current_access_transformation_of
    (pi: PolyInstr) (current: list Z) : Transformation :=
  current_access_transformation_at
    (current_env_dim_of pi.(pi_point_witness) current) pi.

Definition current_src_args_at
    (env_dim: nat) (pi: PolyInstr) (current: list Z) : list Z :=
  affine_product (current_transformation_at env_dim pi) current.

Definition current_src_args_of
    (pi: PolyInstr) (current: list Z) : list Z :=
  current_src_args_at
    (current_env_dim_of pi.(pi_point_witness) current) pi current.

Definition current_env_dim_in_dim
    (dim: nat) (pw: point_space_witness) : nat :=
  (dim - witness_current_point_dim pw)%nat.

Definition current_src_args_in_dim
    (dim: nat) (pi: PolyInstr) (current: list Z) : list Z :=
  current_src_args_at
    (current_env_dim_in_dim dim pi.(pi_point_witness)) pi current.

Definition current_view_pi
    (env_dim: nat) (pi: PolyInstr) : PolyInstr :=
  {|
    pi_depth := pi.(pi_depth);
    pi_instr := pi.(pi_instr);
    pi_poly := pi.(pi_poly);
    pi_schedule := pi.(pi_schedule);
    pi_point_witness := PSWIdentity pi.(pi_depth);
    pi_transformation := current_transformation_at env_dim pi;
    pi_access_transformation := current_access_transformation_at env_dim pi;
    pi_waccess := pi.(pi_waccess);
    pi_raccess := pi.(pi_raccess);
  |}.

Definition current_view_pprog (pp: t) : t :=
  let '(pis, varctxt, vars) := pp in
  (List.map (current_view_pi (length varctxt)) pis, varctxt, vars).

Lemma exact_listzzs_cols_current_insert_zeros_constraint :
  forall cols added env_dim affs,
    exact_listzzs_cols cols affs ->
    (env_dim <= cols)%nat ->
    exact_listzzs_cols (cols + added)%nat
      (List.map (current_insert_zeros_constraint added env_dim) affs).
Proof.
  intros cols added env_dim affs Hcols Henv listz z listzz Hin Heq.
  rewrite in_map_iff in Hin.
  destruct Hin as [[v c] [Hmap Hin0]].
  rewrite Heq in Hmap.
  unfold current_insert_zeros_constraint in Hmap; simpl in Hmap.
  inversion Hmap; subst listz z.
  specialize (Hcols v c (v, c) Hin0 eq_refl).
  unfold current_insert_zeros_constraint; simpl.
  rewrite app_length, app_length.
  rewrite repeat_length, resize_length, skipn_length.
  rewrite Hcols.
  lia.
Qed.

Local Lemma exact_listzzs_cols_resize_at_end :
  forall cols added affs,
    exact_listzzs_cols cols affs ->
    exact_listzzs_cols (cols + added)%nat
      (List.map
        (fun '(coeffs, rhs) =>
          (resize (length coeffs + added) coeffs, rhs))
        affs).
Proof.
  intros cols added affs Hcols coeffs rhs pair Hin Heq.
  apply in_map_iff in Hin.
  destruct Hin as [[source_coeffs source_rhs] [Hmap Hin]].
  rewrite Heq in Hmap; simpl in Hmap.
  inversion Hmap; subst coeffs rhs.
  rewrite resize_length.
  specialize (Hcols
    source_coeffs source_rhs (source_coeffs, source_rhs) Hin eq_refl).
  lia.
Qed.

Lemma exact_listzzs_cols_current_transformation_for_witness :
  forall (env: list ident) (pw: point_space_witness) tf,
    exact_listzzs_cols
      (length env + witness_base_point_dim pw)%nat
      tf ->
    exact_listzzs_cols
      (length env + witness_current_point_dim pw)%nat
      (current_transformation_for_witness (length env) pw tf).
Proof.
  intros env pw.
  induction pw as [dim|w|added inner IH|added inner IH]; intros tf Htf; simpl in *.
  - unfold witness_current_point_dim, witness_base_point_dim, witness_added_dims in *.
    simpl in *.
    replace (length env + (dim + 0))%nat with (length env + dim)%nat by lia.
    exact Htf.
  - assert
      (Hcurdim:
         (length env + witness_current_point_dim (PSWTiling w))%nat =
         (length env + witness_base_point_dim (PSWTiling w) + witness_added_dims (PSWTiling w))%nat).
    { unfold witness_current_point_dim. lia. }
    rewrite Hcurdim.
    eapply exact_listzzs_cols_current_insert_zeros_constraint; [exact Htf|lia].
  - assert
      (Hinner:
         exact_listzzs_cols
           (length env + witness_current_point_dim inner)%nat
           (current_transformation_for_witness (length env) inner tf)).
    { apply IH. exact Htf. }
    assert
      (Hcurdim:
         (length env + witness_current_point_dim (PSWInsertAfterEnv added inner))%nat =
         (length env + witness_current_point_dim inner + added)%nat).
    { unfold witness_current_point_dim, witness_base_point_dim, witness_added_dims; simpl; lia. }
    rewrite Hcurdim.
    eapply exact_listzzs_cols_current_insert_zeros_constraint; [exact Hinner|lia].
  - assert
      (Hinner:
         exact_listzzs_cols
           (length env + witness_current_point_dim inner)%nat
           (current_transformation_for_witness (length env) inner tf)).
    { apply IH. exact Htf. }
    assert
      (Hcurdim:
         (length env + witness_current_point_dim (PSWInsertAtEnd added inner))%nat =
         (length env + witness_current_point_dim inner + added)%nat).
    { unfold witness_current_point_dim, witness_base_point_dim, witness_added_dims; simpl; lia. }
    rewrite Hcurdim.
    apply exact_listzzs_cols_resize_at_end.
    exact Hinner.
Qed.

Lemma exact_listzzs_cols_current_transformation_at :
  forall (env: list ident) (pi: PolyInstr),
    exact_listzzs_cols
      (length env + witness_base_point_dim (pi_point_witness pi))%nat
      (pi_transformation pi) ->
    exact_listzzs_cols
      (length env + witness_current_point_dim (pi_point_witness pi))%nat
      (current_transformation_at (length env) pi).
Proof.
  intros env pi Htf.
  unfold current_transformation_at.
  apply exact_listzzs_cols_current_transformation_for_witness.
  exact Htf.
Qed.

Lemma exact_listzzs_cols_current_access_transformation_at :
  forall (env: list ident) (pi: PolyInstr),
    exact_listzzs_cols
      (length env + witness_base_point_dim (pi_point_witness pi))%nat
      (pi_access_transformation pi) ->
    exact_listzzs_cols
      (length env + witness_current_point_dim (pi_point_witness pi))%nat
      (current_access_transformation_at (length env) pi).
Proof.
  intros env pi Htf.
  unfold current_access_transformation_at.
  apply exact_listzzs_cols_current_transformation_for_witness.
  exact Htf.
Qed.

Lemma current_transformation_for_witness_preserve_length :
  forall env_dim pw tf,
    length (current_transformation_for_witness env_dim pw tf) =
    length tf.
Proof.
  intros env_dim pw.
  induction pw as [dim|w|added inner IH|added inner IH]; intros tf; simpl; rewrite ?map_length, ?IH; reflexivity.
Qed.

Lemma current_transformation_at_preserve_length :
  forall (env: list ident) (pi: PolyInstr),
    length (current_transformation_at (length env) pi) =
    length (pi_transformation pi).
Proof.
  intros env pi.
  unfold current_transformation_at.
  apply current_transformation_for_witness_preserve_length.
Qed.

Lemma current_access_transformation_at_preserve_length :
  forall (env: list ident) (pi: PolyInstr),
    length (current_access_transformation_at (length env) pi) =
    length (pi_access_transformation pi).
Proof.
  intros env pi.
  unfold current_access_transformation_at.
  apply current_transformation_for_witness_preserve_length.
Qed.

Lemma current_transformation_of_current_view_pi :
  forall env_dim pi current,
    current_transformation_of (current_view_pi env_dim pi) current =
    current_transformation_at env_dim pi.
Proof.
  intros env_dim pi current.
  unfold current_transformation_of, current_view_pi.
  simpl.
  reflexivity.
Qed.

Lemma current_access_transformation_of_current_view_pi :
  forall env_dim pi current,
    current_access_transformation_of (current_view_pi env_dim pi) current =
    current_access_transformation_at env_dim pi.
Proof.
  intros env_dim pi current.
  unfold current_access_transformation_of, current_view_pi.
  simpl.
  reflexivity.
Qed.

Lemma current_src_args_of_current_view_pi :
  forall env_dim pi current,
    current_src_args_of (current_view_pi env_dim pi) current =
    affine_product (current_transformation_at env_dim pi) current.
Proof.
  intros env_dim pi current.
  unfold current_src_args_of, current_src_args_at.
  unfold current_view_pi, current_transformation_at, current_env_dim_of.
  unfold witness_current_point_dim, witness_base_point_dim, witness_added_dims.
  simpl.
  reflexivity.
Qed.

Lemma current_src_args_of_current_view_pi_eq :
  forall env_dim pi current,
    witness_current_point_dim (pi_point_witness pi) = pi_depth pi ->
    length current = (env_dim + pi_depth pi)%nat ->
    current_src_args_of (current_view_pi env_dim pi) current =
    current_src_args_of pi current.
Proof.
  intros env_dim pi current Hwit Hlen.
  rewrite current_src_args_of_current_view_pi.
  unfold current_src_args_of, current_src_args_at, current_transformation_at, current_env_dim_of.
  replace
    (length current - witness_current_point_dim (pi_point_witness pi))%nat
    with env_dim by lia.
  reflexivity.
Qed.

Definition eqdom_pinstr (pi1 pi2: PolyLang.PolyInstr) := 
  pi1.(pi_depth) = pi2.(pi_depth) /\
  pi1.(pi_instr) = pi2.(pi_instr) /\ 
  pi1.(pi_poly) = pi2.(pi_poly) /\ 
  pi1.(pi_point_witness) = pi2.(pi_point_witness) /\
  pi1.(pi_transformation) = pi2.(pi_transformation) /\
  pi1.(pi_access_transformation) = pi2.(pi_access_transformation) /\
  pi1.(pi_waccess) = pi2.(pi_waccess) /\ 
  pi1.(pi_raccess) = pi2.(pi_raccess)
.
  
Definition eqdom_pprog (pp1 pp2: PolyLang.t) := 
  forall pil1 pil2 varctxt1 varctxt2 vars1 vars2, 
    pp1 = (pil1, varctxt1, vars1) -> 
    pp2 = (pil2, varctxt2, vars2) -> 
    varctxt1 = varctxt2 /\
    vars1 = vars2 /\ 
    length pil1 = length pil2 /\  
    rel_list eqdom_pinstr pil1 pil2.

Lemma eqdom_pinstr_symm:
  forall pi1 pi2,
    eqdom_pinstr pi1 pi2 ->
    eqdom_pinstr pi2 pi1.
Proof.
  intros. unfolds eqdom_pinstr.
  splits; firstorder.
Qed.

Lemma eqdom_pprog_symm:
  forall pp1 pp2, 
    eqdom_pprog pp1 pp2 -> 
    eqdom_pprog pp2 pp1.
Proof.
  intros pp1 pp2 Heqdom.
  unfold eqdom_pprog in *.
  intros pil1 pil2 varctxt1 varctxt2 vars1 vars2 H1 H2.
  pose proof Heqdom pil2 pil1 varctxt2 varctxt1 vars2 vars1 H2 H1 as Heqdom'.
  destruct Heqdom' as [Hvarctxt [Hvars [Hlen Heqdom']]].
  splits; try solve [symmetry; trivial].
  eapply rel_list_symm; eauto.
  eapply eqdom_pinstr_symm.
Qed.

Definition scanned to_scan n p m q := to_scan m q && negb (is_eq p q && (n =? m)%nat).
Hint Unfold scanned.

Instance scanned_proper : Proper ((eq ==> veq ==> eq) ==> eq ==> veq ==> (eq ==> veq ==> eq)) scanned.
Proof.
  intros to_scan1 to_scan2 Hto_scan n1 n2 Hn p1 p2 Hp m1 m2 Hm q1 q2 Hq.
  unfold scanned.
  erewrite Hto_scan by (exact Hm || exact Hq).
  rewrite Hn. rewrite Hm. rewrite Hp. rewrite Hq.
  reflexivity.
Qed.

(** dim should be max dim of all domain *)
Definition env_scan (poly_instrs : (list PolyInstr)) (env : list Z) (dim : nat) (n : nat) (p : list Z) :=
  match nth_error poly_instrs n with
  | Some pi => is_eq env (resize (length env) p) && is_eq p (resize dim p) && in_poly p pi.(pi_poly)
  | None => false
  end.


Instance env_scan_proper : forall prog env dim, Proper (eq ==> veq ==> eq) (env_scan prog env dim).
Proof.
  intros pis env dim n1 n2 Hn p1 p2 Hp. rewrite Hn. unfold env_scan.
  destruct (nth_error pis n2) as [pi|]; simpl; auto.
  rewrite Hp at 1 2 4; rewrite Hp at 1. reflexivity.
Qed.

Notation "'wf_scan'" := (Proper (eq ==> veq ==> eq)) (only parsing).

(** Polyhedral model's semantics, with implicit instance point. Taken from POPL'21 *)
(** G, E, p |- (P, Q, M) -> (P, Q\{p}, M') *)

Inductive poly_semantics : nat -> (nat -> list Z -> bool) -> (list PolyInstr) -> State.t -> State.t -> Prop :=
| PolyDone : forall env_dim to_scan poly_instrs st, 
    (forall n p, to_scan n p = false) -> 
    poly_semantics env_dim to_scan poly_instrs st st
| PolyProgress : forall env_dim to_scan poly_instrs st1 st2 st3 wcs rcs poly_instr n p,
    to_scan n p = true -> 
    nth_error poly_instrs n = Some poly_instr ->
    (forall n2 p2 poly_instr2, nth_error poly_instrs n2 = Some poly_instr2 ->
                          lex_compare (affine_product poly_instr2.(pi_schedule) p2) (affine_product poly_instr.(pi_schedule) p) = Lt ->
                          to_scan n2 p2 = false) ->
    Instr.instr_semantics poly_instr.(pi_instr) (current_src_args_in_dim env_dim poly_instr p) wcs rcs st1 st2 ->
    poly_semantics env_dim (scanned to_scan n p) poly_instrs st2 st3 ->
    poly_semantics env_dim to_scan poly_instrs st1 st3.

Definition env_poly_semantics (env : list Z) (dim : nat) (pis : list PolyInstr) (mem1 mem2 : State.t) :=
  poly_semantics dim (env_scan pis env dim) pis mem1 mem2.

(** Semantics wrapped with initialization *)
Inductive semantics: t -> State.t -> State.t -> Prop :=
| PSemaIntro: forall pprog pis varctxt vars envv st1 st2,
    pprog = (pis, varctxt, vars) -> 
    Instr.Compat vars st1 ->
    Instr.NonAlias st1 -> 
    Instr.InitEnv varctxt envv st1 ->
    env_poly_semantics envv (pprog_current_dim pprog) pis st1 st2 ->
    semantics pprog st1 st2.

Theorem poly_semantics_extensionality :
  forall env_dim to_scan1 prog mem1 mem2,
    poly_semantics env_dim to_scan1 prog mem1 mem2 ->
    forall to_scan2,
      (forall n p, to_scan1 n p = to_scan2 n p) ->
      poly_semantics env_dim to_scan2 prog mem1 mem2.
Proof.
  intros env_dim to_scan1 prog mem1 mem2 Hsem.
  induction Hsem.
  - intros to_scan2 Heq.
    apply PolyDone.
    intros n p.
    rewrite <- Heq.
    apply H.
  - intros to_scan2 Heq.
    eapply PolyProgress; eauto.
    apply IHHsem.
    intros n0 p0.
    unfold scanned.
    rewrite <- Heq.
    reflexivity.
Qed.


Lemma scanned_wf_compat :
  forall to_scan n p, wf_scan to_scan -> wf_scan (scanned to_scan n p).
Proof.
  intros to_scan n p Hwf. apply scanned_proper; [exact Hwf | reflexivity | reflexivity].
Qed.

(** Part 2: Instruction Point Semantics *)
(* Record InstrPoint := {
  ip_nth: nat;  (** belongs to nth polyhedral instruction *)
  ip_index: DomIndex;  (** index of the domain, i.e., iterator's value *)
  ip_transformation: Transformation; (** transformation function *)
  ip_time_stamp: TimeStamp;  (** schedule *)
  ip_instruction: Instr.t;  (** basic instruction *)
  ip_depth: nat;  (** surrounded iterator depth *)
}. *)

Notation InstrPoint := ILSema.InstrPoint.
Notation ip_nth := ILSema.ip_nth.
Notation ip_index := ILSema.ip_index.
Notation ip_transformation := ILSema.ip_transformation.
Notation ip_time_stamp := ILSema.ip_time_stamp.
Notation ip_instruction := ILSema.ip_instruction.
Notation ip_depth := ILSema.ip_depth.

Record InstrPoint_ext := {
  ip_nth_ext: nat;  (** belongs to nth polyhedral instruction *)
  ip_index_ext: DomIndex;  (** index of the domain, i.e., iterator's value *)
  ip_transformation_ext: Transformation; (** transformation function *)
  ip_access_transformation_ext: Transformation; (** validator/access transformation *)
  ip_time_stamp1_ext: TimeStamp;  (** old schedule *)
  ip_time_stamp2_ext: TimeStamp;  (** new schedule *)
  ip_instruction_ext: Instr.t;  (** basic instruction *)
  ip_depth_ext: nat;  (** surrounded iterator's name *)
}.


Definition eq_except_sched := 
  ILSema.eq_except_sched.

(* Definition eq_except_sched (ip1 ip2: InstrPoint): Prop := 
  ip1.(ip_nth) = ip2.(ip_nth) /\ 
  ip1.(ip_index) = ip2.(ip_index) /\ 
  ip1.(ip_transformation) = ip2.(ip_transformation) /\
  ip1.(ip_instruction) = ip2.(ip_instruction) /\ 
  ip1.(ip_depth) = ip2.(ip_depth). *)

Definition old_of_ext (ip_ext: InstrPoint_ext): InstrPoint := 
  {|
    ip_nth := ip_ext.(ip_nth_ext); 
    ip_index := ip_ext.(ip_index_ext); 
    ip_transformation := ip_ext.(ip_transformation_ext);
    ip_time_stamp := ip_ext.(ip_time_stamp1_ext); 
    ip_instruction := ip_ext.(ip_instruction_ext); 
    ip_depth := ip_ext.(ip_depth_ext); 
  |}.

Definition new_of_ext (ip_ext: InstrPoint_ext) := 
  {|
    ip_nth := ip_ext.(ip_nth_ext); 
    ip_index := ip_ext.(ip_index_ext); 
    ip_transformation := ip_ext.(ip_transformation_ext);
    ip_time_stamp := ip_ext.(ip_time_stamp2_ext); 
    ip_instruction := ip_ext.(ip_instruction_ext); 
    ip_depth := ip_ext.(ip_depth_ext); 
  |}.

Definition old_of_ext_list (ipl_ext: list InstrPoint_ext) := 
  map old_of_ext ipl_ext.
  
Definition new_of_ext_list (ipl_ext: list InstrPoint_ext) := 
  map new_of_ext ipl_ext.

Notation instr_point_sema := ILSema.instr_point_sema.
(* Inductive instr_point_sema (ip: InstrPoint) 
  (st1 st2: State.t): Prop :=
  | ip_sema_intro: forall wcs rcs,
    Instr.instr_semantics ip.(ip_instruction) 
      (affine_product ip.(ip_transformation) ip.(ip_index)) wcs rcs st1 st2 -> 
    instr_point_sema ip st1 st2. *)

Definition instr_point_sched_le (ip1 ip2: InstrPoint): Prop := 
  lex_compare ip1.(ip_time_stamp) ip2.(ip_time_stamp) = Lt \/ 
  lex_compare ip1.(ip_time_stamp) ip2.(ip_time_stamp) = Eq. 

Lemma instr_point_sched_le_trans:
  forall ip1 ip2 ip3,
    instr_point_sched_le ip1 ip2 ->
    instr_point_sched_le ip2 ip3 ->
    instr_point_sched_le ip1 ip3.
Proof.
  intros. unfolds instr_point_sched_le.
  destruct H; destruct H0. 
  - left. eapply lex_compare_trans; eauto.
  - left.
    rewrite <- is_eq_iff_cmp_eq in H0.
    eapply lex_compare_right_eq with (t1:=ip_time_stamp ip1) in H0; eauto.
    rewrite <- H0; trivial. 
  - left.
    rewrite <- is_eq_iff_cmp_eq in H.
    eapply lex_compare_left_eq with (t3:=ip_time_stamp ip3) in H; eauto.
    rewrite H; trivial.
  - right. eapply lex_compare_trans; eauto.
Qed. 

Definition instr_point_ext_old_sched_lt (ip1 ip2: InstrPoint_ext): Prop := 
  lex_compare ip1.(ip_time_stamp1_ext) ip2.(ip_time_stamp1_ext) = Lt. 

  
Definition instr_point_ext_old_sched_le (ip1 ip2: InstrPoint_ext): Prop := 
  lex_compare ip1.(ip_time_stamp1_ext) ip2.(ip_time_stamp1_ext) = Lt \/ 
  lex_compare ip1.(ip_time_stamp1_ext) ip2.(ip_time_stamp1_ext) = Eq. 

(* TODO: Move to Base.v. Require Coqlib.v *)
(* Definition comparison_eq_dec: 
  forall (x y: comparison), { x = y } + { x <> y }.
  decide equality.
Defined. *)
(* 
Definition instr_point_sched_ltb (ip1 ip2: InstrPoint): bool := 
  comparison_eqb (lex_compare ip1.(ip_time_stamp) ip2.(ip_time_stamp)) Lt.

Definition instr_point_sched_eqb (ip1 ip2: InstrPoint): bool := 
  comparison_eqb (lex_compare ip1.(ip_time_stamp) ip2.(ip_time_stamp)) Eq.
 *)

Notation instr_point_sched_ltb := ILSema.instr_point_sched_ltb.
Notation instr_point_sched_eqb := ILSema.instr_point_sched_eqb.

Definition instr_point_ext_old_sched_ltb (ip1 ip2: InstrPoint_ext): bool := 
  comparison_eqb (lex_compare ip1.(ip_time_stamp1_ext) ip2.(ip_time_stamp1_ext)) Lt.

Definition instr_point_ext_old_sched_eqb (ip1 ip2: InstrPoint_ext): bool := 
  comparison_eqb (lex_compare ip1.(ip_time_stamp1_ext) ip2.(ip_time_stamp1_ext)) Eq.
  
Definition instr_point_ext_old_sched_leb (ip1 ip2: InstrPoint_ext): bool := 
  comparison_eqb (lex_compare ip1.(ip_time_stamp1_ext) ip2.(ip_time_stamp1_ext)) Lt 
  ||   
  comparison_eqb (lex_compare ip1.(ip_time_stamp1_ext) ip2.(ip_time_stamp1_ext)) Eq. 

Definition instr_point_ext_new_sched_le (ip1 ip2: InstrPoint_ext): Prop := 
  lex_compare ip1.(ip_time_stamp2_ext) ip2.(ip_time_stamp2_ext) = Lt \/ 
  lex_compare ip1.(ip_time_stamp2_ext) ip2.(ip_time_stamp2_ext) = Eq. 

Definition instr_point_ext_new_sched_ge (ip1 ip2: InstrPoint_ext): Prop := 
  lex_compare ip1.(ip_time_stamp2_ext) ip2.(ip_time_stamp2_ext) = Eq \/ 
  lex_compare ip1.(ip_time_stamp2_ext) ip2.(ip_time_stamp2_ext) = Gt. 

Definition instr_point_ext_new_sched_leb (ip1 ip2: InstrPoint_ext): bool := 
  comparison_eqb (lex_compare ip1.(ip_time_stamp2_ext) ip2.(ip_time_stamp2_ext)) Lt 
  ||   
  comparison_eqb (lex_compare ip1.(ip_time_stamp2_ext) ip2.(ip_time_stamp2_ext)) Eq. 

Definition instr_point_ext_new_sched_geb (ip1 ip2: InstrPoint_ext): bool := 
  comparison_eqb (lex_compare ip1.(ip_time_stamp2_ext) ip2.(ip_time_stamp2_ext)) Gt 
  ||   
  comparison_eqb (lex_compare ip1.(ip_time_stamp2_ext) ip2.(ip_time_stamp2_ext)) Eq. 

Notation Permutable := ILSema.Permutable.
Notation Permutable_symm := ILSema.Permutable_symm. 

(** Note: this is irrelevent to schedule, so either old_of_ext or new_of_ext is ok *)
Definition Permutable_ext (ip1_ext ip2_ext: InstrPoint_ext) := 
  Permutable (old_of_ext ip1_ext) (old_of_ext ip2_ext).
  
Lemma Permutable_ext_symm:
  forall ip1 ip2, 
    Permutable_ext ip1 ip2 -> Permutable_ext ip2 ip1.
Proof.
  intros.
  unfolds Permutable_ext.
  eapply Permutable_symm. trivial.
Qed. 

Notation instr_point_list_semantics:= ILSema.instr_point_list_semantics.
Notation veq_instance := ILSema.veq_instance.
Notation veq_instance_refl := ILSema.veq_instance_refl.

Definition belongs_to (ip: InstrPoint) (pi: PolyInstr): Prop :=
  in_poly ip.(ip_index) pi.(pi_poly) 
  /\ ip.(ip_transformation) = current_transformation_of pi ip.(ip_index)
  /\ ip.(ip_time_stamp) = affine_product (pi.(pi_schedule)) ip.(ip_index) 
  /\ ip.(ip_instruction) = pi.(pi_instr)
  /\ ip.(ip_depth) = pi.(pi_depth)
  .
  

Definition np_lt (ip1 ip2: InstrPoint): Prop :=
  ip1.(ip_nth) < ip2.(ip_nth) 
  \/ 
  (ip1.(ip_nth) = ip2.(ip_nth) /\ lex_compare ip1.(ip_index) ip2.(ip_index) = Lt).

Lemma np_lt_irrefl:
  forall i,
    ~np_lt i i.
Proof.
  intro. intro. unfold np_lt in H.
  destruct H; try lia;
  destruct H; try lia.
  rewrite lex_compare_reflexive in H0. tryfalse.
Qed.

Lemma np_lt_trans:
  Relations_1.Transitive np_lt.
Proof.
  intros x y z. intros.
  unfolds np_lt. 
  destruct H; destruct H0; destruct H; destruct H0; try lia.
  right. split; try lia.
  eapply lex_compare_trans; eauto.
Qed.

Lemma np_lt_strict:
  StrictOrder np_lt.
Proof.
  split.
  - intro ip. unfold complement. intro.
    unfold np_lt in H. destruct H; tryfalse; try lia.
    destruct H.
    rewrite lex_compare_reflexive in H0; tryfalse.
  - intros x y z. intros.
    unfolds np_lt.
    destruct H; destruct H0; try lia.
    destruct H; destruct H0. right. split; try lia.
    eapply lex_compare_trans; eauto.
Qed. 

Definition np_eq (ip1 ip2: InstrPoint) := 
  ip1.(ip_nth) = ip2.(ip_nth) /\ lex_compare ip1.(ip_index) ip2.(ip_index) = Eq.

Lemma np_eq_equivalence:
  Equivalence np_eq.
Proof.
  split.
  - intros. split; trivial. eapply lex_compare_reflexive. 
  - 
    unfolds np_eq. 
    split; trivial. 
    destruct H. lia. 
    destruct H. rewrite lex_compare_antisym. rewrite H0; trivial.
  - split. 
    destruct H; destruct H0. lia.
    destruct H; destruct H0. eapply lex_compare_trans; eauto.
Qed.

Instance np_lt_proper:
  Proper (np_eq ==> np_eq ==> iff) np_lt.
Proof.
  intros ip1 ip2 Heq1 ip1' ip2' Heq2.
  split. 
  - intro LT. unfolds np_eq. unfolds np_lt.
    destruct Heq1; destruct Heq2.
    destruct LT; try lia.
    destruct H3.
    right. split; try lia. 
    eapply is_eq_iff_cmp_eq in H0.
    eapply is_eq_iff_cmp_eq in H2.
    eapply lex_compare_left_eq with (t3:=ip_index ip1') in H0.
    eapply lex_compare_right_eq with (t1:=ip_index ip2) in H2.
    rewrite <- H2. rewrite <- H0. trivial.
  - intro LT. unfolds np_eq. unfolds np_lt.
    destruct Heq1; destruct Heq2.
    destruct LT; try lia.
    destruct H3.
    right. split; try lia. 
    eapply is_eq_iff_cmp_eq in H0. 
    rewrite is_eq_commutative in H0.
    eapply is_eq_iff_cmp_eq in H2.
    rewrite is_eq_commutative in H2.
    eapply lex_compare_left_eq with (t3:=ip_index ip1') in H0.
    eapply lex_compare_right_eq with (t1:=ip_index ip2) in H2.
    rewrite <- H0. rewrite <- H2. trivial.
Qed.

Definition flatten_instrs (envv: list Z) (poly_instrs: list PolyInstr) (ipl: list InstrPoint): Prop := 
  (
    (* 1. firstn of length env is envv.
       Redundant with clause 2 after the env-scoped membership repair, but
       kept to minimize breakage in existing proofs. *)
    forall ip,
      In ip ipl ->
      firstn (length envv) ip.(ip_index) = envv 
  )
  /\
  (
    (* 2. contains only but all env-scoped instances of all instructions *)
    forall ip,
      In ip ipl
      <->
      (
      exists pi,
        nth_error poly_instrs ip.(ip_nth) = Some pi 
        /\ firstn (length envv) ip.(ip_index) = envv
        /\ belongs_to ip pi
        /\ length ip.(ip_index) = length envv + pi.(pi_depth) 
      )
  )
  /\
  (
    (* 3. Uniqueness *)
      NoDup ipl
  )
  /\
  (
    (* 4. Ordered. for determinism *)
      Sorted np_lt ipl
  )
.

Definition flatten_instr_nth (envv: list Z) (nth: nat) (pi: PolyInstr) (ipl: list InstrPoint): Prop := 
  (
    (* 1. firstn of length env is envv.
       Redundant with clause 2 after the env-scoped membership repair, but
       kept to minimize breakage in existing proofs. *)
    forall ip,
      In ip ipl ->
      firstn (length envv) ip.(ip_index) = envv 
  )
  /\
  (
    (* 2. contains only but all env-scoped instances of this instruction *)
    forall ip,
      In ip ipl
      <->
      firstn (length envv) ip.(ip_index) = envv
      /\
      belongs_to ip pi
      /\ ip.(ip_nth) = nth
      /\ length ip.(ip_index) = length envv + pi.(pi_depth) 
  )
  /\
  (
    (* 3. Uniqueness *)
      NoDup ipl
  )
  /\
  (
    (* 4. Ordered. for determinism *)
      Sorted np_lt ipl
  )
.

Lemma belongs_to_current_view_pi_iff :
  forall (env_dim: nat) (pi: PolyInstr) (ip: InstrPoint),
    witness_current_point_dim (pi_point_witness pi) = pi_depth pi ->
    length (ip_index ip) = (env_dim + pi_depth pi)%nat ->
    belongs_to ip (current_view_pi env_dim pi) <->
    belongs_to ip pi.
Proof.
  intros env_dim pi ip Hwit Hlen.
  unfold belongs_to.
  split; intros Hbel;
    destruct Hbel as [Hpoly [Htf [Hts [Hin Hdepth]]]];
    repeat split; try assumption; simpl in *.
  - rewrite current_transformation_of_current_view_pi in Htf.
    unfold current_transformation_of, current_env_dim_of.
    replace
      (length (ip_index ip) - witness_current_point_dim (pi_point_witness pi))%nat
      with env_dim by lia.
    exact Htf.
  - rewrite current_transformation_of_current_view_pi.
    unfold current_transformation_of, current_env_dim_of in Htf.
    replace
      (length (ip_index ip) - witness_current_point_dim (pi_point_witness pi))%nat
      with env_dim in Htf by lia.
    exact Htf.
Qed.

Local Lemma flatten_instr_nth_current_view_member_iff :
  forall envv env_dim nth pi ip,
    length envv = env_dim ->
    witness_current_point_dim (pi_point_witness pi) = pi_depth pi ->
    (firstn (length envv) (ip_index ip) = envv /\
     belongs_to ip (current_view_pi env_dim pi) /\
     ip_nth ip = nth /\
     length (ip_index ip) =
       length envv + pi_depth (current_view_pi env_dim pi))
    <->
    (firstn (length envv) (ip_index ip) = envv /\
     belongs_to ip pi /\
     ip_nth ip = nth /\
     length (ip_index ip) = length envv + pi_depth pi).
Proof.
  intros envv env_dim nth pi ip Henvdim Hcurrent.
  assert (Hindex_length :
    length (ip_index ip) = length envv + pi_depth pi <->
    length (ip_index ip) =
      length envv + pi_depth (current_view_pi env_dim pi)).
  { simpl; tauto. }
  assert (Hbelongs :
    length (ip_index ip) = length envv + pi_depth pi ->
    (belongs_to ip (current_view_pi env_dim pi) <-> belongs_to ip pi)).
  {
    intro Hlength.
    apply belongs_to_current_view_pi_iff; [exact Hcurrent|].
    rewrite Henvdim in Hlength; exact Hlength.
  }
  split; intros (Hprefix & Hbel & Hnth & Hlength).
  - refine (conj Hprefix (conj _ (conj Hnth _))).
    + apply (proj1 (Hbelongs (proj2 Hindex_length Hlength))).
      exact Hbel.
    + apply (proj1 Hindex_length); exact Hlength.
  - refine (conj Hprefix (conj _ (conj Hnth _))).
    + apply (proj2 (Hbelongs Hlength)).
      exact Hbel.
    + apply (proj2 Hindex_length); exact Hlength.
Qed.

Lemma flatten_instr_nth_current_view_iff :
  forall (envv: list Z) (env_dim nth: nat) (pi: PolyInstr) (ipl: list InstrPoint),
    length envv = env_dim ->
    witness_current_point_dim (pi_point_witness pi) = pi_depth pi ->
    flatten_instr_nth envv nth (current_view_pi env_dim pi) ipl <->
    flatten_instr_nth envv nth pi ipl.
Proof.
  intros envv env_dim nth pi ipl Henvdim Hcur.
  unfold flatten_instr_nth.
  split; intros (Hprefix & Hmember & Hnodup & Hsorted);
    refine (conj Hprefix (conj _ (conj Hnodup Hsorted)));
    intro ip; rewrite Hmember.
  - apply flatten_instr_nth_current_view_member_iff; assumption.
  - symmetry.
    apply flatten_instr_nth_current_view_member_iff; assumption.
Qed.

Lemma NoDup_app:
  forall A (l1 l2: list A),
    NoDup l1 ->
    NoDup l2 ->
    (forall i, In i l1 -> ~In i l2) ->
    NoDup (l1++l2).
Proof.
  intros. induction H.
  - simpls. trivial.
  - simpls. econstructor.
    + intro. eapply in_app_or in H3. 
      destruct H3; eauto. 
      pose proof (H1 x).
      assert (~ In x l2). {eapply H4; left; trivial. }
      tryfalse.
    + eapply IHNoDup; eauto.
Qed.

Lemma nth_error_Some':
  forall [A : Type] (l : list A) (x: A) (n : nat),
    nth_error l n = Some x -> n < Datatypes.length l.
Proof.
  intros.  
  eapply nth_error_Some.
  rewrite H; intro; tryfalse. 
Qed. 

Lemma Sorted_app:
  forall A (l1 l2: list A) lt,
    Sorted lt l1 ->
    Sorted lt l2 ->
    (forall i1 i2, In i1 l1 -> In i2 l2 -> lt i1 i2) ->
    Sorted lt (l1++l2).
Proof.
  intros. induction H.
  - simpls. trivial.
  - simpls. econs.
    + eapply IHSorted; eauto.
    + 
      destruct (l++l2) eqn:Heq; eauto.
      destruct l; simpls; tryfalse.
      -- 
      econs.
      assert (In a0 l2). {
        clear - Heq.
        destruct l2; simpls; tryfalse; inv Heq; eauto.
      }
      eapply H1; eauto.
      --
      econs.
      inv H2. inv Heq. trivial.
Qed.

Local Lemma flatten_append_singleton_shape:
  forall (Point Item : Type)
    (rank : Point -> nat)
    (prefix : Point -> Prop)
    (facts : Point -> Item -> Prop)
    (order : Point -> Point -> Prop)
    (items : list Item) (item : Item) (left right : list Point),
    (forall point, In point left -> prefix point) ->
    (forall point,
      In point left <->
      exists old_item,
        nth_error items (rank point) = Some old_item /\
        facts point old_item) ->
    NoDup left ->
    Sorted order left ->
    (forall point, In point right -> prefix point) ->
    (forall point,
      In point right <->
      facts point item /\ rank point = length items) ->
    NoDup right ->
    Sorted order right ->
    (forall point1 point2,
      rank point1 < rank point2 -> order point1 point2) ->
    (forall point, In point (left ++ right) -> prefix point) /\
    (forall point,
      In point (left ++ right) <->
      exists old_item,
        nth_error (items ++ [item]) (rank point) = Some old_item /\
        facts point old_item) /\
    NoDup (left ++ right) /\
    Sorted order (left ++ right).
Proof.
  intros Point Item rank prefix facts order items item left right
    Hleft_prefix Hleft_member Hleft_nodup Hleft_sorted
    Hright_prefix Hright_member Hright_nodup Hright_sorted Hrank_order.
  refine (conj _ (conj _ (conj _ _))).
  - intros point Hin.
    apply in_app_or in Hin.
    destruct Hin as [Hin|Hin].
    + exact (Hleft_prefix point Hin).
    + exact (Hright_prefix point Hin).
  - intros point.
    split.
    + intro Hin.
      apply in_app_or in Hin.
      destruct Hin as [Hin|Hin].
      * apply Hleft_member in Hin.
        destruct Hin as (old_item & Hnth & Hfacts).
        exists old_item; split; [|exact Hfacts].
        rewrite nth_error_app1; [exact Hnth|].
        apply nth_error_Some' in Hnth; exact Hnth.
      * apply Hright_member in Hin.
        destruct Hin as [Hfacts Hrank].
        exists item; split; [|exact Hfacts].
        rewrite nth_error_app2; [|lia].
        rewrite Hrank, Nat.sub_diag.
        reflexivity.
    + intros (old_item & Hnth & Hfacts).
      apply nth_error_Some' in Hnth as Hrank_bound.
      rewrite app_length in Hrank_bound; simpl in Hrank_bound.
      destruct (Nat.lt_trichotomy (rank point) (length items))
        as [Hleft|[Heq|Hright]]; [| |lia].
      * apply in_or_app; left.
        apply Hleft_member.
        exists old_item; split; [|exact Hfacts].
        rewrite nth_error_app1 in Hnth; [exact Hnth|exact Hleft].
      * apply in_or_app; right.
        apply Hright_member.
        split; [|exact Heq].
        rewrite nth_error_app2 in Hnth; [|lia].
        rewrite Heq, Nat.sub_diag in Hnth.
        simpl in Hnth; inversion Hnth; subst.
        exact Hfacts.
  - eapply NoDup_app; eauto.
    intros point Hin_left Hin_right.
    apply Hleft_member in Hin_left.
    apply Hright_member in Hin_right.
    destruct Hin_left as (old_item & Hnth & Hfacts_left).
    destruct Hin_right as [Hfacts_right Hrank].
    rewrite Hrank in Hnth.
    assert (Hnone : nth_error items (length items) = None).
    { apply nth_error_None; lia. }
    rewrite Hnone in Hnth; discriminate.
  - eapply Sorted_app; eauto.
    intros point1 point2 Hin1 Hin2.
    apply Hleft_member in Hin1.
    apply Hright_member in Hin2.
    destruct Hin1 as (old_item & Hnth & Hfacts1).
    destruct Hin2 as [Hfacts2 Hrank2].
    apply Hrank_order.
    rewrite Hrank2.
    apply nth_error_Some' in Hnth; exact Hnth.
Qed.

Lemma flatten_instrs_app_singleton:
  forall envv pis pi ipl ipl' ,
    flatten_instrs envv pis ipl ->
    flatten_instr_nth envv (length pis) pi ipl' ->
    flatten_instrs envv (pis++[pi]) (ipl++ipl').
Proof.
  intros envv pis pi ipl ipl_tail Hflat Htail.
  unfold flatten_instrs in Hflat |- *.
  unfold flatten_instr_nth in Htail.
  destruct Hflat as (Hprefix & Hmember & Hnodup & Hsorted).
  destruct Htail as (Htail_prefix & Htail_member & Htail_nodup & Htail_sorted).
  eapply flatten_append_singleton_shape with
    (rank := ip_nth)
    (prefix := fun ip => firstn (length envv) (ip_index ip) = envv)
    (facts := fun ip item =>
      firstn (length envv) (ip_index ip) = envv /\
      belongs_to ip item /\
      length (ip_index ip) = length envv + pi_depth item)
    (order := np_lt);
    try eassumption.
  - intros point.
    specialize (Htail_member point).
    tauto.
  - intros point1 point2 Hrank.
    unfold np_lt; left; exact Hrank.
Qed.

Lemma flatten_instrs_ipl_n_lt_len:
  forall envv pis ipl,
    flatten_instrs envv pis ipl ->
    forall ip,
      In ip ipl ->
      ip_nth ip < length pis.
Proof.
  intros.
  destruct H as (H1 & H2 & H3 & H4).
  eapply H2 in H0.
  destruct H0 as (pi & NTH & HPREF & BEL & LEN).
  eapply nth_error_Some' in NTH. trivial.
Qed.

Local Lemma flatten_split_singleton_shape:
  forall (Point Item : Type)
    (rank : Point -> nat)
    (prefix : Point -> Prop)
    (facts : Point -> Item -> Prop)
    (equiv order : Point -> Point -> Prop)
    (items : list Item) (item : Item) (whole : list Point),
    Equivalence equiv ->
    StrictOrder order ->
    Proper (equiv ==> equiv ==> iff) order ->
    (forall point, In point whole -> prefix point) ->
    (forall point,
      In point whole <->
      exists old_item,
        nth_error (items ++ [item]) (rank point) = Some old_item /\
        facts point old_item) ->
    NoDup whole ->
    Sorted order whole ->
    (forall point1 point2,
      rank point1 < rank point2 -> order point1 point2) ->
    exists left right,
      ((forall point, In point left -> prefix point) /\
       (forall point,
         In point left <->
         exists old_item,
           nth_error items (rank point) = Some old_item /\
           facts point old_item) /\
       NoDup left /\ Sorted order left) /\
      ((forall point, In point right -> prefix point) /\
       (forall point,
         In point right <->
         facts point item /\ rank point = length items) /\
       NoDup right /\ Sorted order right) /\
      whole = left ++ right.
Proof.
  intros Point Item rank prefix facts equiv order items item whole
    Hequiv Horder Hproper Hprefix Hmember Hnodup Hsorted Hrank_order.
  set (is_left := fun point : Point => rank point <? length items).
  set (is_right := fun point : Point => Nat.eqb (length items) (rank point)).
  exists (filter is_left whole).
  exists (filter is_right whole).
  assert (Hrank_bound :
    forall point, In point whole -> rank point <= length items).
  {
    intros point Hin.
    apply Hmember in Hin.
    destruct Hin as (old_item & Hnth & Hfacts).
    apply nth_error_Some' in Hnth.
    rewrite app_length in Hnth; simpl in Hnth; lia.
  }
  refine (conj _ (conj _ _)).
  - refine (conj _ (conj _ (conj _ _))).
    + intros point Hin.
      apply filter_In in Hin.
      exact (Hprefix point (proj1 Hin)).
    + intros point.
      split.
      * intro Hin.
        apply filter_In in Hin.
        destruct Hin as [Hin Hleft].
        apply Hmember in Hin.
        destruct Hin as (old_item & Hnth & Hfacts).
        exists old_item; split; [|exact Hfacts].
        rewrite nth_error_app1 in Hnth; [exact Hnth|].
        unfold is_left in Hleft.
        apply Nat.ltb_lt in Hleft; exact Hleft.
      * intros (old_item & Hnth & Hfacts).
        apply filter_In; split.
        -- apply Hmember.
           exists old_item; split; [|exact Hfacts].
           rewrite nth_error_app1; [exact Hnth|].
           apply nth_error_Some' in Hnth; exact Hnth.
        -- unfold is_left.
           apply Nat.ltb_lt.
           apply nth_error_Some' in Hnth; exact Hnth.
    + apply NoDup_filter; exact Hnodup.
    + eapply filter_sort; eauto.
  - refine (conj _ (conj _ (conj _ _))).
    + intros point Hin.
      apply filter_In in Hin.
      exact (Hprefix point (proj1 Hin)).
    + intros point.
      split.
      * intro Hin.
        apply filter_In in Hin.
        destruct Hin as [Hin Hright].
        apply Hmember in Hin.
        destruct Hin as (old_item & Hnth & Hfacts).
        unfold is_right in Hright.
        apply Nat.eqb_eq in Hright.
        rewrite nth_error_app2 in Hnth; [|lia].
        rewrite <- Hright, Nat.sub_diag in Hnth.
        simpl in Hnth; inversion Hnth; subst.
        split; [exact Hfacts|symmetry; exact Hright].
      * intros [Hfacts Hrank].
        apply filter_In; split.
        -- apply Hmember.
           exists item; split; [|exact Hfacts].
           rewrite nth_error_app2; [|lia].
           rewrite Hrank, Nat.sub_diag; reflexivity.
        -- unfold is_right.
           apply Nat.eqb_eq; symmetry; exact Hrank.
    + apply NoDup_filter; exact Hnodup.
    + eapply filter_sort; eauto.
  - assert (Hsplit :
      whole = filter is_left whole ++ filter (fun point => negb (is_left point)) whole).
    {
      eapply filter_split; eauto.
      intros point1 point2 Hleft Hright.
      apply Hrank_order.
      unfold is_left in Hleft, Hright.
      apply Nat.ltb_lt in Hleft.
      apply Nat.ltb_ge in Hright.
      lia.
    }
    rewrite Hsplit at 1.
    f_equal.
    apply filter_ext_in.
    intros point Hin.
    specialize (Hrank_bound point Hin).
    unfold is_left, is_right.
    destruct (rank point <? length items) eqn:Hleft;
      destruct (Nat.eqb (length items) (rank point)) eqn:Hright;
      simpl; try reflexivity.
    + apply Nat.ltb_lt in Hleft.
      apply Nat.eqb_eq in Hright; lia.
    + apply Nat.ltb_ge in Hleft.
      apply Nat.eqb_neq in Hright; lia.
Qed.

Lemma flatten_instrs_app_singleton_inv:
  forall envv pis pi ipl0 ,
    flatten_instrs envv (pis++[pi]) (ipl0) ->
    exists ipl ipl',
    flatten_instrs envv pis ipl /\ flatten_instr_nth envv (length pis) pi ipl' /\ ipl0 = ipl++ipl'.
Proof.
  intros envv pis pi ipl0 Hflat.
  unfold flatten_instrs in Hflat.
  destruct Hflat as (Hprefix & Hmember & Hnodup & Hsorted).
  pose proof
    (flatten_split_singleton_shape
      InstrPoint PolyInstr ip_nth
      (fun ip => firstn (length envv) (ip_index ip) = envv)
      (fun ip item =>
        firstn (length envv) (ip_index ip) = envv /\
        belongs_to ip item /\
        length (ip_index ip) = length envv + pi_depth item)
      np_eq np_lt pis pi ipl0
      np_eq_equivalence np_lt_strict np_lt_proper
      Hprefix Hmember Hnodup Hsorted
      (fun point1 point2 Hrank => or_introl Hrank))
    as Hsplit.
  destruct Hsplit as (ipl & ipl_tail & Hleft & Hright & Happ).
  exists ipl.
  exists ipl_tail.
  refine (conj Hleft (conj _ Happ)).
  unfold flatten_instr_nth.
  destruct Hright as
    (Htail_prefix & Htail_member & Htail_nodup & Htail_sorted).
  refine (conj Htail_prefix (conj _ (conj Htail_nodup Htail_sorted))).
  intros point.
  specialize (Htail_member point).
  tauto.
Qed.

Lemma flatten_instrs_nil_implies_nil:
  forall envv ipl, 
  flatten_instrs envv [] ipl -> ipl = nil.
Proof.
  intros; simpls; trivial; tryfalse.
  destruct H as (ENV& BEL & NODUP & SORTED).
  destruct ipl; trivial. exfalso.
  pose proof (BEL i). 
  destruct H. 
  assert ( exists pi,
    nth_error [] (ip_nth i) = Some pi /\
    firstn (Datatypes.length envv) (ip_index i) = envv /\
    belongs_to i pi /\
    Datatypes.length (ip_index i) = Datatypes.length envv + pi_depth pi). {
      eapply H. eapply in_eq.
  }
  destruct H1 as (pi & NTH & _).
  eapply nth_error_rev_some in NTH; tryfalse.
Qed.

Lemma flatten_instrs_nil_sub_nil:
  forall envv pis pi,
    flatten_instrs envv (pis++[pi]) [] <->
    flatten_instrs envv pis [] /\ flatten_instr_nth envv (length pis) pi [].
Proof.
  intros envv pis pi.
  split.
  - intro Hflat.
    destruct (flatten_instrs_app_singleton_inv envv pis pi [] Hflat)
      as (left & right & Hleft & Hright & Happ).
    symmetry in Happ.
    apply app_eq_nil in Happ as [Hleft_nil Hright_nil].
    subst left right.
    split; assumption.
  - intros [Hleft Hright].
    change (flatten_instrs envv (pis ++ [pi]) ([] ++ [])).
    apply flatten_instrs_app_singleton; assumption.
Qed.

Lemma flatten_instrs_nil:
  forall envv,
    flatten_instrs envv [] [].
Proof.
  intros. splits; intros; tryfalse.
  split; intros; tryfalse.
  destruct H as (pi & NTH & HPREF & BEL & LEN).
  rewrite nth_error_nil in NTH. tryfalse.
  econs. econs.
Qed.


Lemma np_lt_map_prsv_np_lt:
  forall f,
    (forall ip, 
      ip_nth (f ip) = ip_nth ip /\
      ip_index (f ip) = ip_index ip
    ) ->
    forall ip1 ip2,
      np_lt ip1 ip2 ->
      np_lt (f ip1) (f ip2).
Proof. 
  intros.
  unfold np_lt.
  assert (ip_nth (f ip1) = ip_nth ip1). {
    eapply H.
  }
  assert (ip_index (f ip1) = ip_index ip1). {
    eapply H.
  }
  assert (ip_nth (f ip2) = ip_nth ip2). {
    eapply H.
  }
  assert (ip_index (f ip2) = ip_index ip2). {
    eapply H.
  }
  unfold np_lt in H0.
  rewrite <- H1 in H0.
  rewrite <- H3 in H0.
  rewrite <- H2 in H0.
  rewrite <- H4 in H0.
  trivial. 
Qed.

Lemma Sorted_ipl_map_np_sorted_np:
  forall ipl f,
    Sorted np_lt ipl ->
    (forall ip, 
      ip_nth (f ip) = ip_nth ip /\
      ip_index (f ip) = ip_index ip
    ) ->
    Sorted np_lt (map f ipl).
Proof.
  induction ipl.
  - intros; simpls; eauto.
  - intros; simpls. econs.
    -- eapply IHipl; eauto. inv H; trivial.
    -- inv H.
      destruct ipl; simpls; try econs.
      inv H4. eapply np_lt_map_prsv_np_lt; eauto.
Qed.

Lemma NoDupA_iplies_map_np_implies_NoDupA_np:
  forall ipl f,
    NoDupA np_eq ipl ->
    (forall ip, 
      ip_nth (f ip) = ip_nth ip /\
      ip_index (f ip) = ip_index ip
    ) ->
    NoDupA np_eq (map f ipl).
Proof.
  induction ipl.
  - intros; simpls; eauto.
  - intros; simpls. econs.
    -- intro. 
      eapply InA_map in H1.
      destruct H1 as (ip' & H1 & H1').
      inv H. eapply H4.
      eapply InA_alt.
      exists ip'. split; trivial.
      rename a into ip1. rename ip' into ip2.
      assert (ip_nth (f ip1) = ip_nth ip1). {
        eapply H0.
      }
      assert (ip_index (f ip1) = ip_index ip1). {
        eapply H0.
      }
      assert (ip_nth (f ip2) = ip_nth ip2). {
        eapply H0.
      }
      assert (ip_index (f ip2) = ip_index ip2). {
        eapply H0.
      }
      unfolds np_eq.
      rewrite H in H1'.
      rewrite H2 in H1'.
      rewrite H3 in H1'.
      rewrite H6 in H1'. trivial.
    -- eapply IHipl; eauto. inv H; trivial.
Qed.

Lemma NoDup_implies_NoDupA_np:
  forall ipl,
    NoDupA np_eq ipl ->
    NoDup ipl.
Proof.
  induction ipl.
  - intros; simpls; eauto. econs.
  - intros; simpls. econs.
    -- intro. inv H. 
        apply H3. eapply In_InA; eauto.
        eapply np_eq_equivalence; eauto.
    -- eapply IHipl; eauto. inv H; trivial.
Qed.

Lemma belongs_to_implies_NoDupA_np:
  forall ipl pi len n,
    (forall ip : InstrPoint,
     In ip ipl ->
     belongs_to ip pi /\
     ip_nth ip = n /\
     Datatypes.length (ip_index ip) = len) ->
    NoDup ipl ->
    NoDupA np_eq ipl.
Proof. 
  induction ipl.
  - intros; simpls; eauto.
  - econs.
    -- intro. 
      inv H0.
      eapply InA_alt in H1.
      destruct H1 as (ip' & BEL & IN). rename a into ip.
      simpl in H.
      assert (ip = ip' \/ In ip' ipl). {
        right; trivial.
      }
      assert (ip = ip \/ In ip ipl). {
        left; trivial.
      }
      eapply (H ip') in H0; eauto.
      destruct H0 as (BEL' & NTH & LEN).
      eapply H in H1; eauto.
      destruct H1 as (BEL'' & NTH' & LEN').
      unfolds belongs_to.
      destruct BEL' as (POL & TS & T & I & D).
      destruct BEL'' as (POL' & TS' & T' & I' & D').
      assert (ip = ip'). {
        destruct ip eqn:Hip. destruct ip' eqn:Hip'. simpls; subst. eauto.
        unfold np_eq in BEL. simpls. destruct BEL.
        eapply is_eq_iff_cmp_eq in H1.
        eapply same_length_eq in H1; eauto. subst. trivial.
      }
      subst; tryfalse.
    -- 
      inv H0. 
      eapply IHipl; eauto.
      intros. 
      pose proof H ip. 
      eapply H. right; trivial.
Qed.

Lemma flatten_instr_nth_NoDupA_np:
  forall envv nth pi ipl,
    flatten_instr_nth envv nth pi ipl ->
    NoDupA np_eq ipl.
Proof.
  intros.
  destruct H as (H1 & H2 & H3 & H4).
  eapply belongs_to_implies_NoDupA_np; eauto.
  intros.
  eapply H2; eauto.
Qed.

Definition retime_ip (sch: Schedule) (ip: InstrPoint) : InstrPoint :=
  {|
    ip_nth := ip.(ip_nth);
    ip_index := ip.(ip_index);
    ip_transformation := ip.(ip_transformation);
    ip_time_stamp := affine_product sch ip.(ip_index);
    ip_instruction := ip.(ip_instruction);
    ip_depth := ip.(ip_depth);
  |}.

Local Lemma eqdom_pinstr_retime_belongs :
  forall pi1 pi2 ip,
    eqdom_pinstr pi1 pi2 ->
    belongs_to ip pi1 ->
    belongs_to (retime_ip (pi_schedule pi2) ip) pi2.
Proof.
  intros pi1 pi2 ip Heq Hbelongs.
  destruct Heq as (Hdepth & Hinstr & Hdomain & Hwitness & Htf & Haccess & Hw & Hr).
  destruct Hbelongs as (Hpoly & Htransformation & Htimestamp & Hinstruction & Hpoint_depth).
  unfold belongs_to, retime_ip; simpl.
  refine (conj _ (conj _ (conj eq_refl (conj _ _)))).
  - rewrite <- Hdomain; exact Hpoly.
  - unfold current_transformation_of, current_transformation_at in *; simpl in *.
    rewrite <- Hwitness, <- Htf.
    exact Htransformation.
  - rewrite <- Hinstr; exact Hinstruction.
  - rewrite <- Hdepth; exact Hpoint_depth.
Qed.

Local Lemma retime_ip_roundtrip :
  forall pi1 pi2 ip,
    belongs_to ip pi2 ->
    retime_ip (pi_schedule pi2) (retime_ip (pi_schedule pi1) ip) = ip.
Proof.
  intros pi1 pi2
    [point_nth point_index point_transformation point_timestamp
     point_instruction point_depth]
    Hbelongs.
  destruct Hbelongs as
    (Hpoly & Htransformation & Htimestamp & Hinstruction & Hdepth).
  simpl in *; subst point_timestamp; reflexivity.
Qed.

Lemma eqdom_pinstr_implies_flatten_instr_nth_retime:
  forall ipl1 pi1 pi2 envv n,
    eqdom_pinstr pi1 pi2 ->
    flatten_instr_nth envv n pi1 ipl1 ->
    flatten_instr_nth envv n pi2 (map (retime_ip (pi_schedule pi2)) ipl1).
Proof.
  intros ipl1 pi1 pi2 envv n Heq Hflat.
  pose proof Heq as Heq_original.
  destruct Heq as (DEPTH & INSTR & DOM & WIT & TSF & ATSF & W & R).
  destruct Hflat as (Hprefix & Hmem & Hnodup & Hsorted).
  refine (conj _ (conj _ (conj _ _))).
  - intros ip Hin.
    apply in_map_iff in Hin.
    destruct Hin as (ip1 & Hip & Hin1).
    subst ip. simpl.
    apply Hprefix. exact Hin1.
  - intros ip.
    split.
    + intro Hin.
      rewrite in_map_iff in Hin.
      destruct Hin as (ip1 & Hip & Hin1).
      subst ip.
      destruct (Hmem ip1) as [Hin1_to _].
      destruct (Hin1_to Hin1) as (Hprefix1 & Hbelongs1 & Hnth1 & Hlength1).
      refine (conj Hprefix1 (conj _ (conj Hnth1 _))).
      * apply eqdom_pinstr_retime_belongs with (pi1 := pi1); assumption.
      * simpl; rewrite <- DEPTH; exact Hlength1.
    + intro Hin.
      destruct Hin as (HPREF & HBEL & HNTH & HLEN).
      rewrite in_map_iff.
      exists (retime_ip (pi_schedule pi1) ip).
      split.
      * apply retime_ip_roundtrip; exact HBEL.
      * destruct (Hmem (retime_ip (pi_schedule pi1) ip)) as [_ Hback].
        apply Hback.
        refine (conj HPREF _).
        refine (conj _ _).
        { apply eqdom_pinstr_retime_belongs with (pi1 := pi2).
          - apply eqdom_pinstr_symm; exact Heq_original.
          - exact HBEL. }
        { split; [exact HNTH|].
          simpl; rewrite DEPTH; exact HLEN. }
  - pose proof (conj Hprefix (conj Hmem (conj Hnodup Hsorted))) as G0.
    eapply flatten_instr_nth_NoDupA_np in G0.
    eapply NoDup_implies_NoDupA_np.
    eapply NoDupA_iplies_map_np_implies_NoDupA_np; eauto.
  - eapply Sorted_ipl_map_np_sorted_np; eauto.
Qed.

Lemma eqdom_pinstr_implies_flatten_instr_nth_exists:
  forall ipl1 pi1 pi2 envv n,
    eqdom_pinstr pi1 pi2 ->
    flatten_instr_nth envv n pi1 ipl1 ->
    exists ipl2,
    flatten_instr_nth envv n pi2 ipl2.
Proof.
  intros ipl1 pi1 pi2 envv n Heq Hflat.
  exists (map (retime_ip (pi_schedule pi2)) ipl1).
  eapply eqdom_pinstr_implies_flatten_instr_nth_retime; eauto.
Qed.

Lemma same_elem_lt_sorted_implies_same_list_pre:
  forall A (l1 l2: list A) lt,
    NoDup l1 ->
    NoDup l2 ->
    (forall i,
      In i l1 <-> In i l2) ->
    (forall i, ~lt i i) ->
    (Relations_1.Transitive lt) ->
    Sorted lt l1 ->
    Sorted lt l2 ->
    l1 = l2.
Proof.
  intros A l1 l2 lt Hnodup1 Hnodup2 Helems Hirrefl Htrans Hsorted1 Hsorted2.
  eapply ListExt.NoDup_sorted_same_elements; eauto.
Qed.


Lemma retime_ip_eq_except_sched:
  forall sch ip,
    eq_except_sched ip (retime_ip sch ip).
Proof.
  intros sch ip.
  unfold eq_except_sched, retime_ip.
  destruct ip; simpl.
  repeat split; reflexivity.
Qed.

Lemma retime_ip_list_eq_except_sched:
  forall sch ipl,
    rel_list eq_except_sched ipl (map (retime_ip sch) ipl).
Proof.
  intros sch ipl.
  induction ipl as [|ip ipl IH]; simpl.
  - constructor.
  - split.
    + apply retime_ip_eq_except_sched.
    + exact IH.
Qed.

Lemma flatten_instr_nth_det:
  forall envv nth pi ipl1 ipl2,
    flatten_instr_nth envv nth pi ipl1 ->
    flatten_instr_nth envv nth pi ipl2 ->
    ipl1 = ipl2.
Proof.
  intros envv nth pi ipl1 ipl2 Hflat1 Hflat2.
  destruct Hflat1 as (Hprefix1 & Hmem1 & Hnodup1 & Hsorted1).
  destruct Hflat2 as (Hprefix2 & Hmem2 & Hnodup2 & Hsorted2).
  eapply same_elem_lt_sorted_implies_same_list_pre.
  - exact Hnodup1.
  - exact Hnodup2.
  - intros ip; split; intro Hin.
    + apply Hmem2. apply Hmem1 in Hin. exact Hin.
    + apply Hmem1. apply Hmem2 in Hin. exact Hin.
  - exact np_lt_irrefl.
  - exact np_lt_trans.
  - exact Hsorted1.
  - exact Hsorted2.
Qed.

Lemma eqdom_pinstrs_implies_flatten_instrs_exists:
  forall pil1 pil2 ipl1 envv,
    rel_list PolyLang.eqdom_pinstr pil1 pil2 ->
    PolyLang.flatten_instrs envv pil1 ipl1 -> 
    exists ipl2, 
      PolyLang.flatten_instrs envv pil2 ipl2.
Proof.
  induction pil1 using rev_ind.
  - intros. 
    exists (@nil InstrPoint).
    assert (pil2 = nil). {
      eapply rel_list_implies_eq_length in H.
      simpls; symmetry in H.
      eapply length_zero_iff_nil in H. trivial.
    }
    subst; trivial. 
    eapply flatten_instrs_nil.
  - intros.
    rename x into pi1. rename pil1 into pil1'.
    assert (exists pil2' pi2, pil2 = pil2' ++ [pi2]). {
      eapply rel_list_implies_eq_length in H; simpls. 
      rewrite app_length in H; simpls; try lia.
      destruct pil2; simpls; try lia.
      exists (removelast (p::pil2)) (last (p::pil2) dummy_pi). 
      eapply app_removelast_last; intro; tryfalse.
    } 
    destruct H1 as (pil2' & pi2 & EQ').
    subst.
    eapply rel_list_app_singleton in H.
    destruct H.
    assert (length pil1' = length pil2') as LEN. {
      eapply rel_list_implies_eq_length; eauto.
    }
   
    eapply flatten_instrs_app_singleton_inv in H0.
    destruct H0 as (ipl1' & ipl1'' & FL1 & FL2 & EQ').
    subst.
    eapply IHpil1 in H; eauto.
    destruct H as (ipl2 & FL2').
    eapply eqdom_pinstr_implies_flatten_instr_nth_exists in FL2; eauto.
    destruct FL2 as (ipl2' & FL2).
    eapply flatten_instrs_app_singleton in FL2'; eauto.
    rewrite <- LEN.
    eauto.
Qed.

Lemma eqdom_pinstr_implies_flatten_instr_same_len:
  forall pi1 pi2 envv ipl1 ipl2 n,
    eqdom_pinstr pi1 pi2 ->
    flatten_instr_nth envv n pi1 ipl1 ->
    flatten_instr_nth envv n pi2 ipl2 ->
    length ipl1 = length ipl2.
Proof.
  intros pi1 pi2 envv ipl1 ipl2 n Heq Hflat1 Hflat2.
  pose proof (eqdom_pinstr_implies_flatten_instr_nth_retime ipl1 pi1 pi2 envv n Heq Hflat1) as Hflat2'.
  pose proof (flatten_instr_nth_det envv n pi2 (map (retime_ip (pi_schedule pi2)) ipl1) ipl2 Hflat2' Hflat2) as Heqipl.
  rewrite <- Heqipl.
  rewrite map_length.
  reflexivity.
Qed.

Lemma eqdom_pinstr_implies_flatten_instr_nth_rel':
  forall ipl1 pi1 pi2 envv n ipl2 ,
    eqdom_pinstr pi1 pi2 ->
    flatten_instr_nth envv n pi1 ipl1 ->
    flatten_instr_nth envv n pi2 ipl2 -> 
    rel_list eq_except_sched ipl1 ipl2.
Proof.
  intros ipl1 pi1 pi2 envv n ipl2 Heq Hflat1 Hflat2.
  pose proof (eqdom_pinstr_implies_flatten_instr_nth_retime ipl1 pi1 pi2 envv n Heq Hflat1) as Hflat2'.
  pose proof (flatten_instr_nth_det envv n pi2 (map (retime_ip (pi_schedule pi2)) ipl1) ipl2 Hflat2' Hflat2) as Heqipl.
  rewrite <- Heqipl.
  apply retime_ip_list_eq_except_sched.
Qed.


Lemma eqdom_pinstrs_implies_flatten_instr_nth_rel':
  forall pil1 pil2 ipl1 envv ipl2 ,
    rel_list eqdom_pinstr pil1 pil2 ->
    flatten_instrs envv pil1 ipl1 ->
    flatten_instrs envv pil2 ipl2 -> 
    rel_list eq_except_sched ipl1 ipl2.
Proof. 
  induction pil1 using rev_ind.
  - intros. 
    assert (pil2 = nil). {
      eapply rel_list_implies_eq_length in H. 
      simpls; symmetry in H.
      eapply length_zero_iff_nil in H. trivial.
    } subst.
    eapply flatten_instrs_nil_implies_nil in H0.
    eapply flatten_instrs_nil_implies_nil in H1.
    subst. econs.
  - intros.
    eapply flatten_instrs_app_singleton_inv in H0.
    destruct H0 as (ipl1' & ipl1'' & FL1 & FL2 & EQ).
    assert (exists pil2' pi2, pil2 = pil2' ++ [pi2]). {
      eapply rel_list_implies_eq_length in H; simpls. 
      rewrite app_length in H; simpls; try lia.
      destruct pil2; simpls; try lia.
      exists (removelast (p::pil2)) (last (p::pil2) dummy_pi). 
      eapply app_removelast_last; intro; tryfalse.
    } destruct H0 as (pil2' & EQ').
    destruct EQ' as (pi2 & EQ').
    subst.
    eapply rel_list_app_singleton in H.
    destruct H as (RELL & REL).
    eapply flatten_instrs_app_singleton_inv in H1.
    destruct H1 as (ipl2' & ipl2'' & FL1' & FL2' & EQ').
    subst.
    eapply rel_list_app.
    eapply IHpil1; eauto.
    eapply eqdom_pinstr_implies_flatten_instr_nth_rel'; eauto.
    assert (length pil1 = length pil2'). {
      eapply rel_list_implies_eq_length; eauto.
    }
    rewrite H. trivial.
Qed.

Lemma same_elem_lt_sorted_implies_same_list:
  forall A (l1 l2: list A) lt,
    NoDup l1 ->
    NoDup l2 ->
    (forall i, 
      In i l1 <-> In i l2) ->
    (forall i, ~lt i i) ->
    (Relations_1.Transitive lt) ->
    Sorted lt l1 ->
    Sorted lt l2 ->
    l1 = l2.
Proof.
  exact same_elem_lt_sorted_implies_same_list_pre.
Qed.

Lemma flatten_instrs_det:
  forall ipl1 ipl2 envv pis,
    flatten_instrs envv pis ipl1 ->
    flatten_instrs envv pis ipl2 ->
    ipl1 = ipl2.
Proof.
  intros.
  destruct H as (ENV1 & BEL1 & ND1 & SO1).
  destruct H0 as (ENV2 & BEL2 & ND2 & SO2).
  eapply same_elem_lt_sorted_implies_same_list; eauto.
  - 
    intro. 
    split; intro.
    -- 
    eapply BEL1 in H. eapply BEL2 in H. trivial.
    -- 
    eapply BEL2 in H. eapply BEL1 in H. trivial.
  - eapply np_lt_irrefl.
  - eapply np_lt_trans.
Qed.

Lemma flatten_instrs_current_view_iff :
  forall (envv: list Z) (env_dim: nat) (pis: list PolyInstr) (ipl: list InstrPoint),
    length envv = env_dim ->
    Forall
      (fun pi =>
         witness_current_point_dim (pi_point_witness pi) = pi_depth pi)
      pis ->
    flatten_instrs envv (List.map (current_view_pi env_dim) pis) ipl <->
    flatten_instrs envv pis ipl.
Proof.
  intros envv env_dim pis.
  induction pis using rev_ind; intros ipl Henvdim Hcur.
  - simpl. split; trivial.
  - rewrite map_app. simpl.
    rewrite Forall_app in Hcur.
    destruct Hcur as [Hcur_init Hcur_last].
    assert
      (Hcur_x:
         witness_current_point_dim (pi_point_witness x) = pi_depth x).
    { remember [x] as xs eqn:Hxs.
      revert x Hxs.
      induction Hcur_last; intros x0 Hxs.
      - discriminate.
      - destruct l as [|y l'].
        + inversion Hxs; subst. exact H.
        + discriminate.
    }
    split; intro Hflat.
    + eapply flatten_instrs_app_singleton_inv in Hflat.
      destruct Hflat as [ipl_init [ipl_last [Hflat_init [Hflat_last Heq]]]].
      subst ipl.
      eapply flatten_instrs_app_singleton.
      * apply (proj1 (IHpis ipl_init Henvdim Hcur_init)); exact Hflat_init.
      * rewrite map_length in Hflat_last.
        apply (proj1 (flatten_instr_nth_current_view_iff envv env_dim (length pis) x ipl_last Henvdim Hcur_x)).
        exact Hflat_last.
    + eapply flatten_instrs_app_singleton_inv in Hflat.
      destruct Hflat as [ipl_init [ipl_last [Hflat_init [Hflat_last Heq]]]].
      subst ipl.
      eapply flatten_instrs_app_singleton.
      * apply (proj2 (IHpis ipl_init Henvdim Hcur_init)); exact Hflat_init.
      * rewrite map_length.
        apply (proj2 (flatten_instr_nth_current_view_iff envv env_dim (length pis) x ipl_last Henvdim Hcur_x)).
        exact Hflat_last.
Qed.

Inductive poly_instance_list_semantics: list Z -> PolyLang.t -> State.t -> State.t -> Prop := 
| PolyPointListSema: forall envv pprog pis varctxt vars st1 st2 ipl sorted_ipl,
    pprog = (pis, varctxt, vars) ->
    flatten_instrs envv pis ipl ->
    Permutation ipl sorted_ipl ->
    Sorted instr_point_sched_le sorted_ipl ->
    instr_point_list_semantics sorted_ipl st1 st2 ->
    poly_instance_list_semantics envv pprog st1 st2.

Inductive instance_list_semantics: t -> State.t -> State.t -> Prop :=
| PIPSemaIntro: forall pprog pis varctxt vars envv st1 st2,
    pprog = (pis, varctxt, vars) -> 
    Instr.Compat vars st1 ->
    Instr.NonAlias st1 -> 
    Instr.InitEnv varctxt envv st1 ->
    poly_instance_list_semantics envv pprog st1 st2 ->
    instance_list_semantics pprog st1 st2.

Local Lemma poly_instance_list_semantics_current_view_iff :
  forall envv pis varctxt vars st1 st2,
    length varctxt = length envv ->
    Forall
      (fun pi =>
        witness_current_point_dim (pi_point_witness pi) = pi_depth pi)
      pis ->
    poly_instance_list_semantics
      envv (current_view_pprog (pis, varctxt, vars)) st1 st2 <->
    poly_instance_list_semantics envv (pis, varctxt, vars) st1 st2.
Proof.
  intros envv pis varctxt vars st1 st2 Henvdim Hcurpis.
  split; intro Hsem;
    inversion Hsem as
      [envv' pprog' pis' varctxt' vars' st1' st2' ipl sorted_ipl
        Hpprog Hflat Hperm Hsorted Hiplsem];
    subst;
    simpl in Hpprog;
    inversion Hpprog; subst; clear Hpprog.
  - eapply PolyPointListSema with (ipl := ipl) (sorted_ipl := sorted_ipl);
      simpl; try reflexivity; try exact Hperm; try exact Hsorted; try exact Hiplsem.
    pose proof
      (flatten_instrs_current_view_iff
        envv (length envv) _ ipl eq_refl Hcurpis) as Hflatiff.
    rewrite Henvdim in Hflat.
    apply (proj1 Hflatiff); exact Hflat.
  - eapply PolyPointListSema with (ipl := ipl) (sorted_ipl := sorted_ipl);
      simpl; try reflexivity; try exact Hperm; try exact Hsorted; try exact Hiplsem.
    pose proof
      (flatten_instrs_current_view_iff
        envv (length envv) _ ipl eq_refl Hcurpis) as Hflatiff.
    rewrite Henvdim.
    apply (proj2 Hflatiff); exact Hflat.
Qed.

Lemma instance_list_semantics_current_view_iff :
  forall (pprog: t) (st1 st2: State.t),
    wf_pprog_tiling pprog ->
    instance_list_semantics (current_view_pprog pprog) st1 st2 <->
    instance_list_semantics pprog st1 st2.
Proof.
  intros [[pis varctxt] vars] st1 st2 Hwf.
  unfold wf_pprog_tiling in Hwf; simpl in Hwf.
  destruct Hwf as [_ Hwfpis].
  assert (Hcurpis :
    Forall
      (fun pi =>
        witness_current_point_dim (pi_point_witness pi) = pi_depth pi)
      pis).
  {
    apply Forall_forall.
    intros pi Hin.
    specialize (Hwfpis pi Hin).
    unfold wf_pinstr_tiling, wf_pinstr_general, wf_pinstr in Hwfpis.
    tauto.
  }
  split; intro Hsem;
    inversion Hsem as
      [pprog' pis' varctxt' vars' envv st1' st2'
        Hpprog Hcompat Hnonalias Hinit Hpoly];
    subst;
    simpl in Hpprog;
    inversion Hpprog; subst; clear Hpprog.
  - eapply PIPSemaIntro with (envv := envv); simpl.
    + reflexivity.
    + exact Hcompat.
    + exact Hnonalias.
    + exact Hinit.
    + pose proof (Instr.init_env_samelen _ _ _ Hinit) as Henvdim.
      apply (proj1
        (poly_instance_list_semantics_current_view_iff
          envv _ _ _ _ _ Henvdim Hcurpis)).
      exact Hpoly.
  - eapply PIPSemaIntro with (envv := envv); simpl.
    + reflexivity.
    + exact Hcompat.
    + exact Hnonalias.
    + exact Hinit.
    + pose proof (Instr.init_env_samelen _ _ _ Hinit) as Henvdim.
      apply (proj2
        (poly_instance_list_semantics_current_view_iff
          envv _ _ _ _ _ Henvdim Hcurpis)).
      exact Hpoly.
Qed.


Record PolyInstr_ext := {
  pi_depth_ext: nat;
  pi_instr_ext: Instr.t;
  pi_poly_ext: Domain; 
  pi_point_witness_ext: point_space_witness;
  pi_transformation_ext: Transformation;
  pi_access_transformation_ext: Transformation;
  pi_schedule1_ext: Schedule; 
  pi_schedule2_ext: Schedule; 
  pi_waccess_ext: list AccessFunction;   
  pi_raccess_ext: list AccessFunction;   
}.

Definition dummy_pi_ext := {|
  pi_depth_ext := 0;
  pi_instr_ext := Instr.dummy_instr ;
  pi_poly_ext := nil;
  pi_point_witness_ext := PSWIdentity 0;
  pi_transformation_ext := nil;
  pi_access_transformation_ext := nil;
  pi_schedule1_ext := nil;
  pi_schedule2_ext := nil;
  pi_waccess_ext := [aff_func_dummy];
  pi_raccess_ext := [aff_func_dummy];
|}.

Definition wf_pinstr_ext (env: list ident) (pi_ext: PolyInstr_ext) := 
    let env_dim := length env in 
    let iters_dim := pi_ext.(pi_depth_ext) in 
    let domain_size := length (pi_ext.(pi_poly_ext)) in 
    let cols := env_dim + iters_dim in 
    let arg_cols := length (pi_ext.(pi_transformation_ext)) in
    witness_current_point_dim (pi_ext.(pi_point_witness_ext)) = iters_dim /\
    (* domain cols *)
    exact_listzzs_cols cols (pi_ext.(pi_poly_ext)) /\ 
    (* transformation cols *)
    exact_listzzs_cols cols (pi_ext.(pi_transformation_ext)) /\
    exact_listzzs_cols cols (pi_ext.(pi_access_transformation_ext)) /\
    (* sched cols *)
    exact_listzzs_cols cols (pi_ext.(pi_schedule1_ext)) /\ 
    exact_listzzs_cols cols (pi_ext.(pi_schedule2_ext)) /\ 
    (* write access function cols *)
    (
      Forall (
        fun (waccess:AccessFunction) => 
        let (arrid, waccess_func) := waccess in 
        exact_listzzs_cols arg_cols waccess_func 
      ) pi_ext.(pi_waccess_ext)
    )
    (* read access function cols *)
    /\ (
      Forall (
        fun (raccess:AccessFunction) => 
        let (arrid, raccess_func) := raccess in 
        exact_listzzs_cols arg_cols raccess_func 
      ) pi_ext.(pi_raccess_ext)
    )
  .

Definition wf_pinstr_ext_affine (env: list ident) (pi_ext: PolyInstr_ext) :=
  wf_pinstr_ext env pi_ext /\
  pi_ext.(pi_point_witness_ext) = PSWIdentity pi_ext.(pi_depth_ext) /\
  pi_ext.(pi_transformation_ext) = pi_ext.(pi_access_transformation_ext).

Definition wf_pinstr_ext_tiling (env: list ident) (pi_ext: PolyInstr_ext) :=
  wf_pinstr_ext env pi_ext /\
  pi_ext.(pi_transformation_ext) = pi_ext.(pi_access_transformation_ext).

Lemma wf_pinstr_affine_implies_wf_pinstr :
  forall env vars pi,
    wf_pinstr_affine env vars pi ->
    wf_pinstr env vars pi.
Proof.
  intros env vars pi Hwf.
  unfold wf_pinstr_affine in Hwf.
  destruct Hwf as [Hwf _].
  exact Hwf.
Qed.

Lemma wf_pinstr_tiling_implies_wf_pinstr :
  forall env vars pi,
    wf_pinstr_tiling env vars pi ->
    wf_pinstr env vars pi.
Proof.
  intros env vars pi Hwf.
  unfold wf_pinstr_tiling, wf_pinstr_general in Hwf.
  destruct Hwf as [Hwf _].
  exact Hwf.
Qed.

Lemma wf_pinstr_general_implies_wf_pinstr :
  forall env vars pi,
    wf_pinstr_general env vars pi ->
    wf_pinstr env vars pi.
Proof.
  exact wf_pinstr_tiling_implies_wf_pinstr.
Qed.

Lemma wf_pinstr_affine_implies_wf_pinstr_tiling :
  forall env vars pi,
    wf_pinstr_affine env vars pi ->
    wf_pinstr_tiling env vars pi.
Proof.
  intros env vars pi Hwf.
  unfold wf_pinstr_affine, wf_pinstr_tiling, wf_pinstr_general in *.
  destruct Hwf as [Hwf [_ Htf]].
  split; auto.
Qed.

Lemma wf_pinstr_affine_implies_wf_pinstr_general :
  forall env vars pi,
    wf_pinstr_affine env vars pi ->
    wf_pinstr_general env vars pi.
Proof.
  exact wf_pinstr_affine_implies_wf_pinstr_tiling.
Qed.

Lemma wf_pprog_affine_implies_wf_pprog :
  forall pp,
    wf_pprog_affine pp ->
    wf_pprog pp.
Proof.
  intros [[pil varctxt] vars] Hwf.
  unfold wf_pprog_affine, wf_pprog in *; simpl in *.
  destruct Hwf as [Hctxt Hpis].
  split; [exact Hctxt|].
  intros pi Hin.
  eapply wf_pinstr_affine_implies_wf_pinstr.
  eapply Hpis; eauto.
Qed.

Lemma wf_pprog_tiling_implies_wf_pprog :
  forall pp,
    wf_pprog_tiling pp ->
    wf_pprog pp.
Proof.
  intros [[pil varctxt] vars] Hwf.
  unfold wf_pprog_tiling, wf_pprog in *; simpl in *.
  destruct Hwf as [Hctxt Hpis].
  split; [exact Hctxt|].
  intros pi Hin.
  eapply wf_pinstr_tiling_implies_wf_pinstr.
  eapply Hpis; eauto.
Qed.

Lemma wf_pprog_general_implies_wf_pprog :
  forall pp,
    wf_pprog_general pp ->
    wf_pprog pp.
Proof.
  exact wf_pprog_tiling_implies_wf_pprog.
Qed.

Lemma wf_pprog_affine_implies_wf_pprog_tiling :
  forall pp,
    wf_pprog_affine pp ->
    wf_pprog_tiling pp.
Proof.
  intros [[pil varctxt] vars] Hwf.
  unfold wf_pprog_affine, wf_pprog_tiling in *; simpl in *.
  destruct Hwf as [Hctxt Hpis].
  split; [exact Hctxt|].
  intros pi Hin.
  eapply wf_pinstr_affine_implies_wf_pinstr_tiling.
  eapply Hpis; eauto.
Qed.

Lemma wf_pprog_affine_implies_wf_pprog_general :
  forall pp,
    wf_pprog_affine pp ->
    wf_pprog_general pp.
Proof.
  exact wf_pprog_affine_implies_wf_pprog_tiling.
Qed.

Lemma wf_pinstr_tiling_current_view_affine :
  forall env vars pi,
    wf_pinstr_tiling env vars pi ->
    wf_pinstr_affine env vars (current_view_pi (length env) pi).
Proof.
  intros env vars pi Hwf.
  unfold wf_pinstr_tiling in Hwf.
  destruct Hwf as [Hwf Htf_eq].
  unfold wf_pinstr_affine.
  split.
  - unfold wf_pinstr in *.
    destruct Hwf as
        (Hcur & Hcols_le & Hpoly_nrl & Hsched_nrl &
         Hpoly & Htf & Hacc_tf & Hsched & Hw & Hr).
    repeat split.
    + unfold current_view_pi.
      assert
        (Hwcur:
           witness_current_point_dim (PSWIdentity (pi_depth pi)) =
           pi_depth pi).
      { unfold witness_current_point_dim, witness_base_point_dim, witness_added_dims.
        simpl.
        lia. }
      exact Hwcur.
    + exact Hcols_le.
    + exact Hpoly_nrl.
    + exact Hsched_nrl.
    + exact Hpoly.
    + replace
        (length env +
         witness_base_point_dim (pi_point_witness (current_view_pi (length env) pi)))%nat
        with
          (length env + witness_current_point_dim (pi_point_witness pi))%nat.
      * exact (exact_listzzs_cols_current_transformation_at env pi Htf).
      * unfold current_view_pi.
        simpl.
        rewrite Hcur.
        reflexivity.
    + replace
        (length env +
         witness_base_point_dim (pi_point_witness (current_view_pi (length env) pi)))%nat
        with
          (length env + witness_current_point_dim (pi_point_witness pi))%nat.
      * exact (exact_listzzs_cols_current_access_transformation_at env pi Hacc_tf).
      * unfold current_view_pi.
        simpl.
        rewrite Hcur.
        reflexivity.
    + exact Hsched.
    + unfold current_view_pi; simpl.
      rewrite current_transformation_at_preserve_length.
      exact Hw.
    + unfold current_view_pi; simpl.
      rewrite current_transformation_at_preserve_length.
      exact Hr.
  - split.
    + reflexivity.
    + unfold current_view_pi.
      simpl.
      unfold current_transformation_at, current_access_transformation_at.
      destruct (pi_point_witness pi); simpl;
        rewrite Htf_eq; reflexivity.
Qed.

Lemma wf_pinstr_general_current_view_affine :
  forall env vars pi,
    wf_pinstr_general env vars pi ->
    wf_pinstr_affine env vars (current_view_pi (length env) pi).
Proof.
  exact wf_pinstr_tiling_current_view_affine.
Qed.

Lemma wf_pprog_tiling_current_view_affine :
  forall pp,
    wf_pprog_tiling pp ->
    wf_pprog_affine (current_view_pprog pp).
Proof.
  intros [[pil varctxt] vars] Hwf.
  unfold wf_pprog_tiling, wf_pprog_affine, current_view_pprog in *; simpl in *.
  destruct Hwf as [Hctxt Hpis].
  split; [exact Hctxt|].
  intros pi' Hin.
  apply in_map_iff in Hin.
  destruct Hin as [pi [Hpi Hin0]].
  subst pi'.
  eapply wf_pinstr_tiling_current_view_affine.
  eapply Hpis; eauto.
Qed.

Lemma wf_pprog_general_current_view_affine :
  forall pp,
    wf_pprog_general pp ->
    wf_pprog_affine (current_view_pprog pp).
Proof.
  exact wf_pprog_tiling_current_view_affine.
Qed.

Lemma wf_pinstr_ext_affine_implies_wf_pinstr_ext :
  forall env pi_ext,
    wf_pinstr_ext_affine env pi_ext ->
    wf_pinstr_ext env pi_ext.
Proof.
  intros env pi_ext Hwf.
  unfold wf_pinstr_ext_affine in Hwf.
  destruct Hwf as [Hwf _].
  exact Hwf.
Qed.

Lemma wf_pinstr_ext_tiling_implies_wf_pinstr_ext :
  forall env pi_ext,
    wf_pinstr_ext_tiling env pi_ext ->
    wf_pinstr_ext env pi_ext.
Proof.
  intros env pi_ext Hwf.
  unfold wf_pinstr_ext_tiling in Hwf.
  destruct Hwf as [Hwf _].
  exact Hwf.
Qed.

Lemma wf_pinstr_ext_affine_implies_wf_pinstr_ext_tiling :
  forall env pi_ext,
    wf_pinstr_ext_affine env pi_ext ->
    wf_pinstr_ext_tiling env pi_ext.
Proof.
  intros env pi_ext Hwf.
  unfold wf_pinstr_ext_affine, wf_pinstr_ext_tiling in *.
  destruct Hwf as [Hwf [_ Htf]].
  split; auto.
Qed.

Definition compose_pinstr_ext (pi1 pi2: PolyLang.PolyInstr): PolyInstr_ext := {|
  pi_depth_ext := pi1.(pi_depth);
  pi_instr_ext := pi1.(pi_instr) ;
  pi_poly_ext := pi1.(pi_poly) ;
  pi_point_witness_ext := pi1.(pi_point_witness) ;
  pi_transformation_ext := pi1.(pi_transformation) ;
  pi_access_transformation_ext := pi1.(pi_access_transformation) ;
  pi_schedule1_ext := pi1.(pi_schedule) ;
  pi_schedule2_ext := pi2.(pi_schedule) ;
  pi_waccess_ext := pi1.(pi_waccess) ;
  pi_raccess_ext := pi1.(pi_raccess) ;
|}.

Lemma wf_pinstr_implies_wf_pinstr_ext: 
  forall env vars pi pi', 
    wf_pinstr env vars pi -> wf_pinstr env vars pi' -> 
    eqdom_pinstr pi pi' ->
    witness_base_point_dim (pi.(pi_point_witness)) = pi.(pi_depth) ->
    wf_pinstr_ext env (compose_pinstr_ext pi pi').
Proof.
  intros env vars pi pi' Hwf1 Hwf2 Heq Hbase.
  unfold wf_pinstr_ext, compose_pinstr_ext.
  unfold wf_pinstr in Hwf1, Hwf2.
  destruct Hwf1 as
    (Hcur1 & Hcols1 & Hpoly_nrl1 & Hsched_nrl1 &
     Hpoly1 & Htf1 & Hacc_tf1 & Hsched1 & Hw1 & Hr1).
  destruct Hwf2 as
    (Hcur2 & Hcols2 & Hpoly_nrl2 & Hsched_nrl2 &
     Hpoly2 & Htf2 & Hacc_tf2 & Hsched2 & Hw2 & Hr2).
  destruct Heq as
    (Hdepth & Hinstr & Hpoly_eq & Hwit_eq &
     Htf_eq & Hacc_tf_eq & Hw_eq & Hr_eq).
  repeat split.
  - exact Hcur1.
  - exact Hpoly1.
  - rewrite <- Hbase. exact Htf1.
  - rewrite <- Hbase. exact Hacc_tf1.
  - exact Hsched1.
  - rewrite Hdepth. exact Hsched2.
  - exact Hw1.
  - exact Hr1.
Qed.

Lemma wf_pinstr_affine_implies_wf_pinstr_ext_affine :
  forall env vars pi pi', 
  wf_pinstr_affine env vars pi -> wf_pinstr_affine env vars pi' -> 
  eqdom_pinstr pi pi' ->
  witness_base_point_dim (pi.(pi_point_witness)) = pi.(pi_depth) ->
  wf_pinstr_ext_affine env (compose_pinstr_ext pi pi').
Proof.
  intros env vars pi pi' Hwf1 Hwf2 Heqdom Hbase.
  unfold wf_pinstr_ext_affine.
  split.
  - eapply wf_pinstr_implies_wf_pinstr_ext; eauto.
    eapply wf_pinstr_affine_implies_wf_pinstr; eauto.
    eapply wf_pinstr_affine_implies_wf_pinstr; eauto.
  - unfold wf_pinstr_affine in Hwf1.
    destruct Hwf1 as [_ [Hw Heq]].
    repeat split; assumption.
Qed.

Definition veq_instance_ext (ip1 ip2: InstrPoint_ext): Prop :=
  ip1.(ip_nth_ext) = ip2.(ip_nth_ext) 
  /\ veq ip1.(ip_index_ext) ip2.(ip_index_ext) 
  /\ ip1.(ip_transformation_ext) = ip2.(ip_transformation_ext)
  /\ ip1.(ip_access_transformation_ext) = ip2.(ip_access_transformation_ext)
  /\ ip1.(ip_time_stamp1_ext) = ip2.(ip_time_stamp1_ext)
  /\ ip1.(ip_time_stamp2_ext) = ip2.(ip_time_stamp2_ext)
  /\ ip1.(ip_instruction_ext) = ip2.(ip_instruction_ext)
  /\ ip1.(ip_depth_ext) = ip2.(ip_depth_ext)
.

Definition belongs_to_ext (ip: InstrPoint_ext) (pi: PolyInstr_ext): Prop :=
  in_poly ip.(ip_index_ext) pi.(pi_poly_ext) 
  /\ ip.(ip_transformation_ext) = pi.(pi_transformation_ext) 
  /\ ip.(ip_access_transformation_ext) = pi.(pi_access_transformation_ext) 
  /\ ip.(ip_time_stamp1_ext) = affine_product (pi.(pi_schedule1_ext)) ip.(ip_index_ext) 
  /\ ip.(ip_time_stamp2_ext) = affine_product (pi.(pi_schedule2_ext)) ip.(ip_index_ext) 
  /\ ip.(ip_instruction_ext) = pi.(pi_instr_ext)
  /\ ip.(ip_depth_ext) = pi.(pi_depth_ext)
  .

Definition np_lt_ext (ip1 ip2: InstrPoint_ext): Prop :=
  ip1.(ip_nth_ext) < ip2.(ip_nth_ext) 
  \/ (ip1.(ip_nth_ext) = ip2.(ip_nth_ext) /\ lex_compare ip1.(ip_index_ext) ip2.(ip_index_ext) = Lt).

Lemma np_lt_ext_irrefl:
  forall i,
    ~np_lt_ext i i.
Proof.
  intro. intro. unfold np_lt_ext in H.
  destruct H; try lia;
  destruct H; try lia.
  rewrite lex_compare_reflexive in H0. tryfalse.
Qed.

Lemma np_lt_ext_trans:
  Relations_1.Transitive np_lt_ext.
Proof.
  intros x y z. intros.
  unfolds np_lt_ext. 
  destruct H; destruct H0; destruct H; destruct H0; try lia.
  right. split; try lia.
  eapply lex_compare_trans; eauto.
Qed.


Lemma np_lt_ext_strict:
  StrictOrder np_lt_ext.
Proof.
  split.
  - intro ip. unfold complement. intro.
    unfold np_lt_ext in H. destruct H; tryfalse; try lia.
    destruct H.
    rewrite lex_compare_reflexive in H0; tryfalse.
  - intros x y z. intros.
    unfolds np_lt_ext.
    destruct H; destruct H0; try lia.
    destruct H; destruct H0. right. split; try lia.
    eapply lex_compare_trans; eauto.
Qed. 

Definition np_eq_ext (ip1 ip2: InstrPoint_ext) := 
  ip1.(ip_nth_ext) = ip2.(ip_nth_ext) /\ lex_compare ip1.(ip_index_ext) ip2.(ip_index_ext) = Eq.

Lemma np_eq_ext_equivalence:
  Equivalence np_eq_ext.
Proof.
  split.
  - intros. split; trivial. eapply lex_compare_reflexive. 
  - 
    unfolds np_eq_ext. 
    split; trivial. 
    destruct H. lia. 
    destruct H. rewrite lex_compare_antisym. rewrite H0; trivial.
  - split. 
    destruct H; destruct H0. lia.
    destruct H; destruct H0. eapply lex_compare_trans; eauto.
Qed.

Instance np_lt_ext_proper:
  Proper (np_eq_ext ==> np_eq_ext ==> iff) np_lt_ext.
Proof.
  intros ip1 ip2 Heq1 ip1' ip2' Heq2.
  split. 
  - intro LT. unfolds np_eq_ext. unfolds np_lt_ext.
    destruct Heq1; destruct Heq2.
    destruct LT; try lia.
    destruct H3.
    right. split; try lia. 
    eapply is_eq_iff_cmp_eq in H0.
    eapply is_eq_iff_cmp_eq in H2.
    eapply lex_compare_left_eq with (t3:=ip_index_ext ip1') in H0.
    eapply lex_compare_right_eq with (t1:=ip_index_ext ip2) in H2.
    rewrite <- H2. rewrite <- H0. trivial.
  - intro LT. unfolds np_eq_ext. unfolds np_lt_ext.
    destruct Heq1; destruct Heq2.
    destruct LT; try lia.
    destruct H3.
    right. split; try lia. 
    eapply is_eq_iff_cmp_eq in H0. 
    rewrite is_eq_commutative in H0.
    eapply is_eq_iff_cmp_eq in H2.
    rewrite is_eq_commutative in H2.
    eapply lex_compare_left_eq with (t3:=ip_index_ext ip1') in H0.
    eapply lex_compare_right_eq with (t1:=ip_index_ext ip2) in H2.
    rewrite <- H0. rewrite <- H2. trivial.
Qed.


Definition flatten_instrs_ext (envv: list Z) (poly_instrs: list PolyInstr_ext) (ipl: list InstrPoint_ext): Prop := 
  (
    (* 1. firstn of length env is envv.
       Redundant with clause 2 after the env-scoped membership repair, but
       kept to minimize breakage in existing proofs. *)
    forall ip,
      In ip ipl ->
      firstn (length envv) ip.(ip_index_ext) = envv 
  )
  /\
  (
    (* 2. contains only but all env-scoped instances of all instructions *)
    forall ip,
      In ip ipl
      <->
      exists pi,
      nth_error poly_instrs ip.(ip_nth_ext) = Some pi 
      /\ firstn (length envv) ip.(ip_index_ext) = envv
      /\ belongs_to_ext ip pi
      /\ length ip.(ip_index_ext) = length envv + pi.(pi_depth_ext)
  )
  /\
  (
    (* 3. Uniqueness *)
      NoDup ipl
  )
  /\
  (
    (* 4. Ordered. for determinism *)
      Sorted np_lt_ext ipl
  )
  .

Definition flatten_instr_nth_ext (envv: list Z) (nth: nat) (pi: PolyInstr_ext) (ipl: list InstrPoint_ext): Prop := 
    (
      (* 1. firstn of length env is envv.
         Redundant with clause 2 after the env-scoped membership repair, but
         kept to minimize breakage in existing proofs. *)
      forall ip,
        In ip ipl ->
        firstn (length envv) ip.(ip_index_ext) = envv 
    )
    /\
    (
      (* 2. contains only but all env-scoped instances of this instruction *)
      forall ip,
        In ip ipl
        <->
        firstn (length envv) ip.(ip_index_ext) = envv
        /\
        belongs_to_ext ip pi
        /\ ip.(ip_nth_ext) = nth
        /\ length ip.(ip_index_ext) = length envv + pi.(pi_depth_ext) 
    )
    /\
    (
      (* 3. Uniqueness *)
        NoDup ipl
    )
    /\
    (
      (* 4. Ordered. for determinism *)
        Sorted np_lt_ext ipl
    )
  .
  
Lemma flatten_instrs_ext_nil:
forall envv , 
  flatten_instrs_ext envv [] [].
Proof.
  intros. splits; intros; tryfalse.
  split; intros; tryfalse.
  destruct H as (pi & NTH & BEL & LEN).
  rewrite nth_error_nil in NTH. tryfalse.
  econs. econs.
Qed.

Lemma flatten_instrs_ext_nil_implies_nil:
  forall envv ipl, 
  flatten_instrs_ext envv [] ipl -> ipl = nil.
Proof.
  intros; simpls; trivial; tryfalse.
  destruct H as (ENV& BEL & NODUP & SORTED).
  destruct ipl; trivial. exfalso.
  pose proof (BEL i). 
  destruct H. 
  assert ( exists pi,
    nth_error [] (ip_nth_ext i) = Some pi /\
    firstn (Datatypes.length envv) (ip_index_ext i) = envv /\
    belongs_to_ext i pi /\
    Datatypes.length (ip_index_ext i) = Datatypes.length envv + pi_depth_ext pi). {
      eapply H. eapply in_eq.
  }
  destruct H1 as (pi & NTH & _ & _ & _).
  eapply nth_error_rev_some in NTH; tryfalse.
Qed.

Lemma flatten_instrs_ext_det:
  forall envv pprog ipl1 ipl2,
    flatten_instrs_ext envv pprog ipl1 ->
    flatten_instrs_ext envv pprog ipl2 ->
    ipl1 = ipl2.
Proof.
  intros.
  destruct H as (ENV1 & BEL1 & ND1 & SO1).
  destruct H0 as (ENV2 & BEL2 & ND2 & SO2).
  eapply same_elem_lt_sorted_implies_same_list; eauto.
  - 
    intro. 
    split; intro.
    -- 
    eapply BEL1 in H. eapply BEL2 in H. trivial.
    -- 
    eapply BEL2 in H. eapply BEL1 in H. trivial.
  - eapply np_lt_ext_irrefl.
  - eapply np_lt_ext_trans.
Qed.

Lemma flatten_instrs_ext_app_singleton:
  forall envv pis pi ipl ipl' ,
    flatten_instrs_ext envv pis ipl ->
    flatten_instr_nth_ext envv (length pis) pi ipl' ->
    flatten_instrs_ext envv (pis++[pi]) (ipl++ipl').
Proof.
  intros envv pis pi ipl ipl_tail Hflat Htail.
  unfold flatten_instrs_ext in Hflat |- *.
  unfold flatten_instr_nth_ext in Htail.
  destruct Hflat as (Hprefix & Hmember & Hnodup & Hsorted).
  destruct Htail as (Htail_prefix & Htail_member & Htail_nodup & Htail_sorted).
  eapply flatten_append_singleton_shape with
    (rank := ip_nth_ext)
    (prefix := fun ip => firstn (length envv) (ip_index_ext ip) = envv)
    (facts := fun ip item =>
      firstn (length envv) (ip_index_ext ip) = envv /\
      belongs_to_ext ip item /\
      length (ip_index_ext ip) = length envv + pi_depth_ext item)
    (order := np_lt_ext);
    try eassumption.
  - intros point.
    specialize (Htail_member point).
    tauto.
  - intros point1 point2 Hrank.
    unfold np_lt_ext; left; exact Hrank.
Qed.

Lemma flatten_instrs_ext_ipl_n_lt_len:
  forall envv pis ipl,
    flatten_instrs_ext envv pis ipl ->
    forall ip,
      In ip ipl ->
      ip_nth_ext ip < length pis.
Proof.
  intros.
  destruct H as (H1 & H2 & H3 & H4).
  eapply H2 in H0.
  destruct H0 as (pi & NTH & HPREF & BEL & LEN).
  eapply nth_error_Some' in NTH. trivial.
Qed.

Lemma flatten_instrs_ext_app_singleton_inv:
  forall envv pis pi ipl0 ,
    flatten_instrs_ext envv (pis++[pi]) (ipl0) ->
    exists ipl ipl',
    flatten_instrs_ext envv pis ipl /\ flatten_instr_nth_ext envv (length pis) pi ipl' /\ ipl0 = ipl++ipl'.
Proof.
  intros envv pis pi ipl0 Hflat.
  unfold flatten_instrs_ext in Hflat.
  destruct Hflat as (Hprefix & Hmember & Hnodup & Hsorted).
  pose proof
    (flatten_split_singleton_shape
      InstrPoint_ext PolyInstr_ext ip_nth_ext
      (fun ip => firstn (length envv) (ip_index_ext ip) = envv)
      (fun ip item =>
        firstn (length envv) (ip_index_ext ip) = envv /\
        belongs_to_ext ip item /\
        length (ip_index_ext ip) = length envv + pi_depth_ext item)
      np_eq_ext np_lt_ext pis pi ipl0
      np_eq_ext_equivalence np_lt_ext_strict np_lt_ext_proper
      Hprefix Hmember Hnodup Hsorted
      (fun point1 point2 Hrank => or_introl Hrank))
    as Hsplit.
  destruct Hsplit as (ipl & ipl_tail & Hleft & Hright & Happ).
  exists ipl.
  exists ipl_tail.
  refine (conj Hleft (conj _ Happ)).
  unfold flatten_instr_nth_ext.
  destruct Hright as
    (Htail_prefix & Htail_member & Htail_nodup & Htail_sorted).
  refine (conj Htail_prefix (conj _ (conj Htail_nodup Htail_sorted))).
  intros point.
  specialize (Htail_member point).
  tauto.
Qed.

Fixpoint compose_pinstrs_ext (pil1 pil2: list PolyLang.PolyInstr): list PolyInstr_ext := 
  match pil1, pil2 with 
  | pi1::pil1, pi2::pil2 => (compose_pinstr_ext pi1 pi2)::(compose_pinstrs_ext pil1 pil2)
  | [], [] => []
  | _, _ => []
  end.

Lemma wf_pil_implies_wf_pil_ext: 
  forall pil pil' env vars, 
    Forall (wf_pinstr env vars) pil -> Forall (wf_pinstr env vars) pil' -> 
    Forall (fun pi => witness_base_point_dim (pi.(pi_point_witness)) = pi.(pi_depth)) pil ->
    rel_list eqdom_pinstr pil pil' ->
    Forall (wf_pinstr_ext env) (compose_pinstrs_ext pil pil').
Proof.
  induction pil.
  {
    intros; simpls.
    destruct pil'; econs.
  }
  {
    intros; simpls.
    inv H.
    destruct pil'; simpls.
    {
      econs.
    }
    {
      econs; inv H0; inv H1.
      eapply wf_pinstr_implies_wf_pinstr_ext; eauto.
      destruct H2; trivial.
      destruct H2; eapply IHpil; eauto.
    }
  }
Qed.

Lemma wf_pil_affine_implies_wf_pil_ext_affine: 
  forall pil pil' env vars, 
    Forall (wf_pinstr_affine env vars) pil ->
    Forall (wf_pinstr_affine env vars) pil' -> 
    Forall (fun pi => witness_base_point_dim (pi.(pi_point_witness)) = pi.(pi_depth)) pil ->
    rel_list eqdom_pinstr pil pil' ->
    Forall (wf_pinstr_ext_affine env) (compose_pinstrs_ext pil pil').
Proof.
  induction pil.
  {
    intros; simpls.
    destruct pil'; econs.
  }
  {
    intros; simpls.
    inv H.
    destruct pil'; simpls.
    {
      econs.
    }
    {
      econs; inv H0; inv H1.
      eapply wf_pinstr_affine_implies_wf_pinstr_ext_affine; eauto.
      destruct H2; trivial.
      destruct H2; eapply IHpil; eauto.
    }
  }
Qed.

Lemma ip_index_in_dom_ext: 
  forall envv nth pi ipl ip,
    flatten_instr_nth_ext envv nth pi ipl -> 
    In ip ipl -> 
    in_poly (ip_index_ext ip) (pi_poly_ext pi).
Proof.
  intros.
  destruct H as (ENV & BELONG & NODUP & SORTED).
  eapply BELONG in H0. 
  destruct H0 as (HPREF & BEL & NTH & LEN).
  destruct BEL as (DOM & TSF & TS1 & TS2 & I & D).
  subst; simpls; trivial.
Qed.

Lemma expand_ip_instr_eq_pi_instr_ext: 
  forall pi ipl ip envv nth,
    flatten_instr_nth_ext envv nth pi ipl -> 
    In ip ipl -> 
    ip_instruction_ext ip = pi_instr_ext pi.
Proof. 
  intros.
  destruct H as (ENV & BELONG & NODUP & SORTED).
  eapply BELONG in H0. 
  destruct H0 as (HPREF & BEL & NTH & LEN).
  destruct BEL as (DOM & TSF & ATSF & TS1 & TS2 & I & D).
  subst; simpls; trivial.
Qed.


Lemma expand_ip_instr_eq_pi_tf_ext: 
  forall pi ipl ip envv nth,
    flatten_instr_nth_ext envv nth pi ipl -> 
    In ip ipl -> 
    ip_transformation_ext ip = pi_transformation_ext pi.
Proof. 
  intros.
  destruct H as (ENV & BELONG & NODUP & SORTED).
  eapply BELONG in H0. 
  destruct H0 as (HPREF & BEL & NTH & LEN).
  destruct BEL as (DOM & TSF & ATSF & TS1 & TS2 & I & D).
  subst; simpls; trivial.
Qed.

Lemma expand_ip_instr_eq_pi_access_tf_ext: 
  forall pi ipl ip envv nth,
    flatten_instr_nth_ext envv nth pi ipl -> 
    In ip ipl -> 
    ip_access_transformation_ext ip = pi_access_transformation_ext pi.
Proof. 
  intros.
  destruct H as (ENV & BELONG & NODUP & SORTED).
  eapply BELONG in H0. 
  destruct H0 as (HPREF & BEL & NTH & LEN).
  destruct BEL as (DOM & TSF & ATSF & TS1 & TS2 & I & D).
  subst; simpls; trivial.
Qed.

Lemma ip_index_size_eq_pi_dom_size_ext: 
  forall envv nth pi ipl ip,
  flatten_instr_nth_ext envv nth pi ipl -> 
    In ip ipl -> 
    length (ip_index_ext ip) = length envv + (pi_depth_ext pi).
Proof.
  intros.
  destruct H as (ENV & BELONG & NODUP & SORTED).
  eapply BELONG in H0. 
  destruct H0 as (HPREF & BEL & NTH & LEN).
  destruct BEL as (DOM & TSF & ATSF & TS1 & TS2 & I & D).
  subst; simpls; trivial.
Qed.

Lemma expand_same_env_ip_index_env_eq: 
  forall envv nth1 nth2 pi1 pi2 ip1 ip2 ipl1 ipl2,
    flatten_instr_nth_ext envv nth1 pi1 ipl1 -> 
    flatten_instr_nth_ext envv nth2 pi2 ipl2 ->
    In ip1 ipl1 -> 
    In ip2 ipl2 -> 
    firstn (length envv) (ip_index_ext ip1) = firstn (length envv) (ip_index_ext ip2).
Proof.
  intros.
  destruct H as (ENV & BELONG & NODUP & SORTED).
  destruct H0 as (ENV' & BELONG' & NODUP' & SORTED').
  eapply ENV in H1. eapply ENV' in H2. rewrite H1; rewrite H2; trivial.
Qed.

Lemma expand_same_env_implies_in_eq_env_pol_ext: 
  forall ipl1 ipl2 envv nth1 pi1 ip1 nth2 pi2 ip2,
    flatten_instr_nth_ext envv nth1 pi1 ipl1 -> 
    flatten_instr_nth_ext envv nth2 pi2 ipl2 ->
    In ip1 ipl1 -> 
    In ip2 ipl2 -> 
    in_poly (ip1.(ip_index_ext) ++ ip2.(ip_index_ext)) 
      (make_poly_env_eq (length envv) ((pi_depth_ext pi1))
      ((pi_depth_ext pi2))) = true.
Proof.
  intros.
  eapply make_poly_env_eq_correct.
  eapply expand_same_env_ip_index_env_eq with (ipl1:=ipl1) (ipl2:=ipl2); eauto.
  all: eapply ip_index_size_eq_pi_dom_size_ext; eauto.
Qed.

Lemma expand_same_env_implies_in_domain_product_pol:
  forall env envv nth1 pi1 ipl1 ip1 nth2 pi2 ipl2 ip2,
    WHEN in_domain_pol <- (poly_product 
      (PolyLang.pi_poly_ext pi1) 
      (PolyLang.pi_poly_ext pi2)
      (length envv + (pi_depth_ext pi1))
      (length envv + (pi_depth_ext pi2))) THEN
    wf_pinstr_ext env pi1 ->
    length env = length envv -> 
    flatten_instr_nth_ext envv nth1 pi1 ipl1 -> 
    flatten_instr_nth_ext envv nth2 pi2 ipl2 ->
    In ip1 ipl1 -> 
    In ip2 ipl2 -> 
    in_poly (ip1.(ip_index_ext) ++ ip2.(ip_index_ext)) in_domain_pol = true.
Proof.
  intros. intros pol' Hprod Hwf1 Hlen Hexp1 Hexp2 Hin1 Hin2.
  pose proof Hin1 as Gin1; pose proof Hin2 as Gin2.
  eapply ip_index_size_eq_pi_dom_size_ext 
    with (envv:=envv) (nth:=nth1) (pi:=pi1) in Hin1; trivial.
  eapply ip_index_size_eq_pi_dom_size_ext 
    with (envv:=envv) (nth:=nth2) (pi:=pi2) in Hin2; trivial.
  eapply poly_product_correct; eauto.
  {
    destruct Hwf1 as (_ & D & _).
    rewrite Hlen in D.
    rewrite <- Hin1 in D.
    trivial. 
  }
  splits; eapply ip_index_in_dom_ext; eauto.
Qed.

Lemma expand_ts1_eq_sched_index_product_ext: 
  forall envv nth pi ipl ip,
    flatten_instr_nth_ext envv nth pi ipl -> 
    In ip ipl -> 
    (ip_time_stamp1_ext ip = affine_product (pi.(pi_schedule1_ext)) (ip.(ip_index_ext))).
Proof.
  intros.
  destruct H as (ENV & BELONG & NODUP & SORTED).
  eapply BELONG in H0. 
  destruct H0 as (HPREF & BEL & NTH & LEN).
  destruct BEL as (DOM & TSF & ATSF & TS1 & TS2 & I & D).
  subst; simpls; trivial.
Qed.

Lemma expand_ts2_eq_sched_index_product_ext: 
  forall envv nth pi ipl ip,
    flatten_instr_nth_ext envv nth pi ipl -> 
    In ip ipl -> 
    (ip_time_stamp2_ext ip = affine_product (pi.(pi_schedule2_ext)) (ip.(ip_index_ext))).
Proof.
  intros.
  intros.
  destruct H as (ENV & BELONG & NODUP & SORTED).
  eapply BELONG in H0. 
  destruct H0 as (HPREF & BEL & NTH & LEN).
  destruct BEL as (DOM & TSF & ATSF & TS1 & TS2 & I & D).
  subst; simpls; trivial.
Qed.

(* We only need to guarantee that, all possible permuted instance pairs are considered by 
the validator. So the lemma is single direction, that's enough. *)
Lemma ip_old_sched_lt_implies_in_pi_old_sched_lt_pol: 
  forall env envv nth1 pi1 ipl1 ip1 nth2 pi2 ipl2 ip2,
    flatten_instr_nth_ext envv nth1 pi1 ipl1 -> 
    flatten_instr_nth_ext envv nth2 pi2 ipl2 ->
    In ip1 ipl1 -> 
    In ip2 ipl2 -> 
    length env = length envv -> 
    wf_pinstr_ext env pi1 ->
    instr_point_ext_old_sched_lt ip1 ip2 ->
    Exists
      (fun pol => 
        in_poly (ip1.(ip_index_ext) ++ ip2.(ip_index_ext)) pol = true
      )   
      (make_poly_lt (PolyLang.pi_schedule1_ext pi1) (PolyLang.pi_schedule1_ext pi2)
        (length env + (pi_depth_ext pi1))
        (length env + (pi_depth_ext pi2)) []).
Proof.
  intros until ip2. intros Hep1 Hep2 Hin1 Hin2 Hlen Hwf1 Hlt.
  unfold instr_point_ext_old_sched_lt in Hlt.
  assert (ip_time_stamp1_ext ip1 = affine_product (pi1.(pi_schedule1_ext)) (ip1.(ip_index_ext))) as TS1. {eapply expand_ts1_eq_sched_index_product_ext; eauto. }
  assert (ip_time_stamp1_ext ip2 = affine_product (pi2.(pi_schedule1_ext)) (ip2.(ip_index_ext))) as TS2. {eapply expand_ts1_eq_sched_index_product_ext; eauto. }
  rewrite TS1, TS2 in Hlt.
  rewrite Hlen.
  eapply make_poly_lt_correct; eauto.
  eapply ip_index_size_eq_pi_dom_size_ext; eauto.
  eapply ip_index_size_eq_pi_dom_size_ext; eauto.
  clear - Hwf1 Hlen. 
  unfold wf_pinstr_ext in Hwf1. 
  destruct Hwf1 as (_ & _ & _ & _ & S & _ & _ & _).
  rewrite Hlen in S. trivial.
Qed.

Lemma ip_new_sched_ge_implies_in_pi_new_sched_ge_pol: 
  forall env envv nth1 pi1 ipl1 ip1 nth2 pi2 ipl2 ip2,
    flatten_instr_nth_ext envv nth1 pi1 ipl1 -> 
    flatten_instr_nth_ext envv nth2 pi2 ipl2 ->
    In ip1 ipl1 -> 
    In ip2 ipl2 -> 
    length env = length envv -> 
    wf_pinstr_ext env pi1 ->
    instr_point_ext_new_sched_ge ip1 ip2 ->
    Exists
      (fun pol => 
        in_poly (ip1.(ip_index_ext) ++ ip2.(ip_index_ext)) pol = true
      )   
      (make_poly_ge (PolyLang.pi_schedule2_ext pi1) (PolyLang.pi_schedule2_ext pi2)
        (length env + (pi_depth_ext pi1))
        (length env + (pi_depth_ext pi2)) []).
Proof. 
  intros until ip2. intros Hep1 Hep2 Hin1 Hin2 Hlen Hwf1 Hge.
  unfold instr_point_ext_new_sched_ge in Hge.
  assert (ip_time_stamp2_ext ip1 = affine_product (pi1.(pi_schedule2_ext)) (ip1.(ip_index_ext))) as TS1. {eapply expand_ts2_eq_sched_index_product_ext; eauto. }
  assert (ip_time_stamp2_ext ip2 = affine_product (pi2.(pi_schedule2_ext)) (ip2.(ip_index_ext))) as TS2. {eapply expand_ts2_eq_sched_index_product_ext; eauto. }
  rewrite TS1, TS2 in Hge.
  rewrite Hlen.
  eapply make_poly_ge_correct; eauto.
  eapply ip_index_size_eq_pi_dom_size_ext; eauto.
  eapply ip_index_size_eq_pi_dom_size_ext; eauto.
  clear - Hwf1 Hlen. 
  unfold wf_pinstr_ext in Hwf1. 
  destruct Hwf1 as (_ & _ & _ & _ & _ & S & _ & _).
  rewrite Hlen in S. trivial.
Qed.

Lemma ext_permut_implies_permut_old: 
  forall (ipl_ext ipl_ext': list InstrPoint_ext), 
    Permutation ipl_ext ipl_ext' -> 
    Permutation (old_of_ext_list ipl_ext) (old_of_ext_list ipl_ext').
Proof.
  intros.
  unfolds old_of_ext_list.
  eapply Permutation_map; eauto.
Qed.

Lemma permut_implies_ext_permut_new: 
  forall (ipl_ext: list InstrPoint_ext) (ipl ipl': list InstrPoint), 
    Permutation ipl ipl' -> 
    new_of_ext_list ipl_ext = ipl -> 
    (exists ipl_ext', 
      Permutation ipl_ext ipl_ext' /\ 
      new_of_ext_list ipl_ext' = ipl'
    ).
Proof.
  intros.
  unfolds new_of_ext_list.
  rewrite <- H0 in H.
  symmetry in H.
  eapply Permutation_map_inv in H; eauto.
  destruct H as (l3 & IPL' & PERMUT); eexists; eauto.
Qed.

Lemma point_ext_old_new_equivalence: 
  forall ip st1 st2, 
    instr_point_sema (old_of_ext ip) st1 st2 <-> 
    instr_point_sema (new_of_ext ip) st1 st2.
Proof.
  intros.
  split.
  {
    intro.
    unfolds old_of_ext.
    unfolds new_of_ext.
    inv H; simpls.
    econs; eauto.
  }
  {
    intro.
    unfolds old_of_ext.
    unfolds new_of_ext.
    inv H; simpls.
    econs; eauto.
  }
Qed.

Lemma sorted_ge_implies_ext_sorted_ge: 
  forall lext, 
  Sorted instr_point_sched_le (new_of_ext_list lext) -> 
  Sorted_b instr_point_ext_new_sched_leb lext.
Proof.
  intros lext Hsorted.
  unfold Sorted_b.
  unfold new_of_ext_list in Hsorted.
  eapply ListExt.Sorted_map_inv_by; [|exact Hsorted].
  intros point1 point2 Hle.
  unfold instr_point_sched_le in Hle.
  unfold instr_point_ext_new_sched_leb.
  simpl in Hle |- *.
  rewrite orb_true_iff.
  rewrite !comparison_eqb_iff_eq.
  exact Hle.
Qed.

Lemma list_ext_old_new_equivalence: 
forall ip_ext st1 st2, 
  instr_point_list_semantics (old_of_ext_list ip_ext) st1 st2 
  <-> 
  instr_point_list_semantics (new_of_ext_list ip_ext) st1 st2.
Proof.
  induction ip_ext.
  {
    intros.
    simpls.
    firstorder.
  }
  {
    intros.
    split.
    {
      intro.
      unfolds old_of_ext_list.
      unfolds new_of_ext_list.
      inv H.
      eapply IHip_ext in H5; eauto.
      econs; eauto.
      eapply point_ext_old_new_equivalence; eauto.
    }
    {
      intro.
      unfolds old_of_ext_list.
      unfolds new_of_ext_list.
      inv H.
      eapply IHip_ext in H5; eauto.
      econs; eauto.
      eapply point_ext_old_new_equivalence; eauto.
    }
  }
Qed. 

(** Below defines properties about lexorder (based on instruction point) *)
(** used in stable permuted instance list's equivalence *)

Lemma instr_point_sched_ltb_trans: 
    transitive instr_point_sched_ltb.
Proof. 
  unfold transitive.
  intros.
  unfolds instr_point_sched_ltb.
  eapply comparison_eqb_iff_eq in H.
  eapply comparison_eqb_iff_eq in H0.
  eapply comparison_eqb_iff_eq.
  eapply lex_compare_trans; eauto.
Qed.

Lemma instr_point_ext_old_sched_ltb_trans: 
    transitive instr_point_ext_old_sched_ltb.
Proof. 
  unfold transitive.
  intros.
  eapply comparison_eqb_iff_eq in H.
  eapply comparison_eqb_iff_eq in H0.
  eapply comparison_eqb_iff_eq.
  eapply lex_compare_trans; eauto.
Qed.

Lemma instr_point_ext_new_sched_leb_trans: 
    transitive instr_point_ext_new_sched_leb.
Proof.
  unfold transitive.
  intros point1 point2 point3 H12 H23.
  change
    (LinalgExt.lex_compare_leb
      (ip_time_stamp2_ext point1) (ip_time_stamp2_ext point2) = true)
    in H12.
  change
    (LinalgExt.lex_compare_leb
      (ip_time_stamp2_ext point2) (ip_time_stamp2_ext point3) = true)
    in H23.
  change
    (LinalgExt.lex_compare_leb
      (ip_time_stamp2_ext point1) (ip_time_stamp2_ext point3) = true).
  eapply LinalgExt.lex_compare_leb_trans; eauto.
Qed.

Lemma instr_point_ext_new_sched_geb_trans: 
    transitive instr_point_ext_new_sched_geb.
Proof.
  unfold transitive.
  intros point1 point2 point3 H12 H23.
  change
    (LinalgExt.lex_compare_geb
      (ip_time_stamp2_ext point1) (ip_time_stamp2_ext point2) = true)
    in H12.
  change
    (LinalgExt.lex_compare_geb
      (ip_time_stamp2_ext point2) (ip_time_stamp2_ext point3) = true)
    in H23.
  change
    (LinalgExt.lex_compare_geb
      (ip_time_stamp2_ext point1) (ip_time_stamp2_ext point3) = true).
  eapply LinalgExt.lex_compare_geb_trans; eauto.
Qed.




Lemma instr_point_sched_cmp_total: 
  total instr_point_sched_ltb instr_point_sched_eqb.
Proof.
  unfold total.
  intros.
  unfolds instr_point_sched_ltb.
  unfolds instr_point_sched_eqb.
  do 3 rewrite comparison_eqb_iff_eq.
  eapply lex_compare_total; eauto.
Qed.

Lemma instr_point_ext_old_sched_cmp_total: 
  total instr_point_ext_old_sched_ltb instr_point_ext_old_sched_eqb.
Proof.
  unfold total.
  intros.
  unfolds instr_point_ext_old_sched_ltb.
  unfolds instr_point_ext_old_sched_eqb.
  do 3 rewrite comparison_eqb_iff_eq.
  eapply lex_compare_total; eauto.
Qed.

Lemma instr_point_sched_cmp_irrefl: 
  irreflexive instr_point_sched_ltb instr_point_sched_eqb.
Proof.
  unfold irreflexive.
  intros.
  unfold instr_point_sched_eqb in H.
  unfold instr_point_sched_ltb.
  eapply comparison_eqb_iff_eq in H.
  pose proof (lex_compare_total (ip_time_stamp x) (ip_time_stamp y)).
  eapply comparison_eqb_false_iff_neq.
  firstorder; congruence.
Qed.

Lemma instr_point_ext_old_sched_cmp_irrefl: 
  irreflexive instr_point_ext_old_sched_ltb instr_point_ext_old_sched_eqb.
Proof.
  unfold irreflexive.
  intros.
  unfold instr_point_ext_old_sched_eqb in H.
  unfold instr_point_ext_old_sched_ltb.
  eapply comparison_eqb_iff_eq in H.
  pose proof (lex_compare_total (ip_time_stamp1_ext x) (ip_time_stamp1_ext y)).
  eapply comparison_eqb_false_iff_neq.
  firstorder; congruence.
Qed.

Lemma instr_point_sched_cmp_antisymm: 
  antisymmetric instr_point_sched_ltb instr_point_sched_eqb.
Proof.
  unfold antisymmetric.
  intros.
  unfolds instr_point_sched_ltb.
  unfolds instr_point_sched_eqb.
  rewrite comparison_eqb_iff_eq.
  rewrite comparison_eqb_iff_eq in H.
  rewrite comparison_eqb_iff_eq in H0.
  rewrite lex_compare_antisym in H0.
  rewrite H in H0. 
  unfold CompOpp in H0. 
  tryfalse.
Qed.

Lemma instr_point_ext_old_sched_cmp_antisymm: 
  antisymmetric instr_point_ext_old_sched_ltb instr_point_ext_old_sched_eqb.
Proof.
  unfold antisymmetric.
  intros.
  unfolds instr_point_ext_old_sched_ltb.
  unfolds instr_point_ext_old_sched_eqb.
  rewrite comparison_eqb_iff_eq.
  rewrite comparison_eqb_iff_eq in H.
  rewrite comparison_eqb_iff_eq in H0.
  rewrite lex_compare_antisym in H0.
  rewrite H in H0. 
  unfold CompOpp in H0. 
  tryfalse.
Qed.


Lemma instr_point_sched_eqb_refl: 
  reflexive instr_point_sched_eqb.
Proof. 
  unfold reflexive.
  unfold instr_point_sched_eqb.
  intros.
  rewrite comparison_eqb_iff_eq.
  eapply lex_compare_reflexive.
Qed.

Lemma instr_point_ext_old_sched_eqb_refl: 
  reflexive instr_point_ext_old_sched_eqb.
Proof. 
  unfold reflexive.
  unfold instr_point_ext_old_sched_eqb.
  intros.
  rewrite comparison_eqb_iff_eq.
  eapply lex_compare_reflexive.
Qed.

Lemma instr_point_sched_eqb_trans: 
  transitive instr_point_sched_eqb.
Proof. 
  unfold transitive.
  intros.
  unfolds instr_point_sched_eqb.
  eapply comparison_eqb_iff_eq in H.
  eapply comparison_eqb_iff_eq in H0.
  eapply comparison_eqb_iff_eq.
  eapply lex_compare_trans; eauto.
Qed.

Lemma instr_point_ext_old_sched_eqb_trans: 
  transitive instr_point_ext_old_sched_eqb.
Proof. 
  unfold transitive.
  intros.
  unfolds instr_point_ext_old_sched_eqb.
  eapply comparison_eqb_iff_eq in H.
  eapply comparison_eqb_iff_eq in H0.
  eapply comparison_eqb_iff_eq.
  eapply lex_compare_trans; eauto.
Qed.


Lemma instr_point_sched_eqb_symm: 
  symmetric instr_point_sched_eqb.
Proof. 
  unfold symmetric.
  intros.
  unfolds instr_point_sched_eqb.
  remember (comparison_eqb (lex_compare (ip_time_stamp x) (ip_time_stamp y)) Eq) as res1.
  remember (comparison_eqb (lex_compare (ip_time_stamp y) (ip_time_stamp x)) Eq) as res2.
  symmetry in Heqres1.
  symmetry in Heqres2.

  destruct res1; destruct res2; try congruence.
  {
    rewrite comparison_eqb_iff_eq in Heqres1.
    rewrite comparison_eqb_false_iff_neq in Heqres2.
    rewrite lex_compare_antisym in Heqres2.
    rewrite Heqres1 in Heqres2.
    unfolds CompOpp.
    tryfalse. 
  }
  {
    rewrite comparison_eqb_iff_eq in Heqres2.
    rewrite comparison_eqb_false_iff_neq in Heqres1.
    rewrite lex_compare_antisym in Heqres1.
    rewrite Heqres2 in Heqres1.
    unfolds CompOpp.
    tryfalse. 
  }
Qed.

Lemma instr_point_ext_old_sched_eqb_symm: 
  symmetric instr_point_ext_old_sched_eqb.
Proof. 
  unfold symmetric.
  intros.
  unfolds instr_point_ext_old_sched_eqb.
  remember (comparison_eqb (lex_compare (ip_time_stamp1_ext x) (ip_time_stamp1_ext y)) Eq) as res1.
  remember (comparison_eqb (lex_compare (ip_time_stamp1_ext y) (ip_time_stamp1_ext x)) Eq) as res2.
  symmetry in Heqres1.
  symmetry in Heqres2.

  destruct res1; destruct res2; try congruence.
  {
    rewrite comparison_eqb_iff_eq in Heqres1.
    rewrite comparison_eqb_false_iff_neq in Heqres2.
    rewrite lex_compare_antisym in Heqres2.
    rewrite Heqres1 in Heqres2.
    unfolds CompOpp.
    tryfalse. 
  }
  {
    rewrite comparison_eqb_iff_eq in Heqres2.
    rewrite comparison_eqb_false_iff_neq in Heqres1.
    rewrite lex_compare_antisym in Heqres1.
    rewrite Heqres2 in Heqres1.
    unfolds CompOpp.
    tryfalse. 
  }
Qed.

Lemma instr_point_sched_eqb_ltb_implies_ltb: 
  eqb_ltb_implies_ltb instr_point_sched_ltb instr_point_sched_eqb.
Proof.
  unfold eqb_ltb_implies_ltb.
  intros.
  unfolds instr_point_sched_eqb.
  unfolds instr_point_sched_ltb.
  rewrite comparison_eqb_iff_eq in H.
  rewrite comparison_eqb_iff_eq in H0.
  rewrite comparison_eqb_iff_eq.
  remember (ip_time_stamp x) as a.
  remember (ip_time_stamp y) as b.
  remember (ip_time_stamp z) as c.
  clear Heqa Heqb Heqc.
  rewrite lex_compare_left_eq with (t2:=b); trivial.
  eapply is_eq_iff_cmp_eq; eauto. 
Qed.

Lemma instr_point_ext_old_sched_eqb_ltb_implies_ltb: 
  eqb_ltb_implies_ltb instr_point_ext_old_sched_ltb instr_point_ext_old_sched_eqb.
Proof.
  unfold eqb_ltb_implies_ltb.
  intros.
  unfolds instr_point_ext_old_sched_eqb.
  unfolds instr_point_ext_old_sched_ltb.
  rewrite comparison_eqb_iff_eq in H.
  rewrite comparison_eqb_iff_eq in H0.
  rewrite comparison_eqb_iff_eq.
  remember (ip_time_stamp1_ext x) as a.
  remember (ip_time_stamp1_ext y) as b.
  remember (ip_time_stamp1_ext z) as c.
  clear Heqa Heqb Heqc.
  rewrite lex_compare_left_eq with (t2:=b); trivial.
  eapply is_eq_iff_cmp_eq; eauto. 
Qed.

Lemma instr_point_sched_ltb_eqb_implies_ltb: 
  ltb_eqb_implies_ltb instr_point_sched_ltb instr_point_sched_eqb.
Proof.
  unfold ltb_eqb_implies_ltb.
  intros.
  unfolds instr_point_sched_eqb.
  unfolds instr_point_sched_ltb.
  rewrite comparison_eqb_iff_eq in H.
  rewrite comparison_eqb_iff_eq in H0.
  rewrite comparison_eqb_iff_eq.
  remember (ip_time_stamp x) as a.
  remember (ip_time_stamp y) as b.
  remember (ip_time_stamp z) as c.
  clear Heqa Heqb Heqc.
  eapply is_eq_iff_cmp_eq in H0; eauto. 
  eapply lex_compare_right_eq with (t1:=a) in H0; eauto.
  rewrite H0 in H; trivial.
Qed.

Lemma instr_point_ext_old_sched_ltb_eqb_implies_ltb: 
  ltb_eqb_implies_ltb instr_point_ext_old_sched_ltb instr_point_ext_old_sched_eqb.
Proof.
  unfold ltb_eqb_implies_ltb.
  intros.
  unfolds instr_point_ext_old_sched_eqb.
  unfolds instr_point_ext_old_sched_ltb.
  rewrite comparison_eqb_iff_eq in H.
  rewrite comparison_eqb_iff_eq in H0.
  rewrite comparison_eqb_iff_eq.
  remember (ip_time_stamp1_ext x) as a.
  remember (ip_time_stamp1_ext y) as b.
  remember (ip_time_stamp1_ext z) as c.
  clear Heqa Heqb Heqc.
  eapply is_eq_iff_cmp_eq in H0; eauto. 
  eapply lex_compare_right_eq with (t1:=a) in H0; eauto.
  rewrite H0 in H; trivial.
Qed.

Lemma selection_sort_instance_list_is_correct:
  forall ipl1 ipl2,  
      SelectionSort instr_point_sched_ltb instr_point_sched_eqb ipl1 = ipl2 ->
      (
        Permutation ipl1 ipl2 /\
        Sorted_b (combine_leb instr_point_sched_ltb instr_point_sched_eqb) ipl2
      ).
Proof. 
  intros.
  eapply selection_sort_is_correct; eauto.
  eapply instr_point_sched_ltb_trans.
  eapply instr_point_sched_eqb_trans.
  eapply instr_point_sched_eqb_refl.
  eapply instr_point_sched_eqb_symm.
  eapply instr_point_sched_cmp_total.
  eapply instr_point_sched_eqb_ltb_implies_ltb.
  eapply instr_point_sched_ltb_eqb_implies_ltb.
Qed.

Lemma sortedb_lexorder_implies_sorted_lexorder: 
  forall ipl,
    Sorted_b
      (combine_leb instr_point_sched_ltb instr_point_sched_eqb)
      ipl -> 
    Sorted instr_point_sched_le ipl.
Proof.
  induction ipl; eauto.
  intros.
  unfold Sorted_b in H.
  inv H; eauto.
  eapply IHipl in H2; eauto.
  inv H3; eauto.
  assert (instr_point_sched_le a b). {
    unfold combine_leb in H.
    unfold instr_point_sched_le.
    unfold instr_point_sched_ltb in H.
    unfold instr_point_sched_eqb in H.
    rewrite orb_true_iff in H.
    do 2 rewrite comparison_eqb_iff_eq in H.
    trivial.
  }
  econs; eauto.
Qed.

Lemma ext_old_ltb_implies_ltb: 
  forall tau1 tau2, 
    instr_point_ext_old_sched_ltb tau1 tau2 
    = 
    instr_point_sched_ltb (old_of_ext tau1) (old_of_ext tau2).
Proof.
  intros.
  unfold instr_point_ext_old_sched_ltb.
  unfold instr_point_sched_ltb.
  simpls; trivial.
Qed.

Lemma ext_old_eqb_implies_eqb: 
  forall tau1 tau2, 
    instr_point_ext_old_sched_eqb tau1 tau2 
    = 
    instr_point_sched_eqb (old_of_ext tau1) (old_of_ext tau2).
Proof.
  intros.
  unfold instr_point_ext_old_sched_eqb.
  unfold instr_point_sched_eqb.
  trivial.
Qed.

Lemma select_helper_list_ext_implies_old_normal:
  forall r l x n y r',
    select_helper instr_point_ext_old_sched_ltb
      instr_point_ext_old_sched_eqb l x n r = (y, r') ->
    select_helper instr_point_sched_ltb instr_point_sched_eqb
      (old_of_ext_list l) (old_of_ext x) n (old_of_ext_list r) =
      (old_of_ext y, old_of_ext_list r').
Proof.
  intros r l x n y r' Hselect.
  unfold old_of_ext_list.
  eapply select_helper_map; eauto.
  - exact ext_old_ltb_implies_ltb.
  - exact ext_old_eqb_implies_eqb.
Qed.

Lemma select_instance_list_ext_implies_old_normal:
  forall i l y r',
  select instr_point_ext_old_sched_ltb instr_point_ext_old_sched_eqb i l = (y, r')
  -> 
  select instr_point_sched_ltb instr_point_sched_eqb (old_of_ext i) (old_of_ext_list l) = ((old_of_ext y), (old_of_ext_list r')).
Proof. 
  intros.
  unfolds select.
  eapply select_helper_list_ext_implies_old_normal in H; eauto.
Qed.

Lemma selsort_instance_list_ext_implies_old_normal:
  forall n ipl1_ext ipl2_ext,
    selsort instr_point_ext_old_sched_ltb instr_point_ext_old_sched_eqb
      ipl1_ext n = ipl2_ext ->
    selsort instr_point_sched_ltb instr_point_sched_eqb
      (old_of_ext_list ipl1_ext) n = old_of_ext_list ipl2_ext.
Proof.
  intros n ipl1_ext ipl2_ext Hsort.
  subst ipl2_ext.
  unfold old_of_ext_list.
  eapply selsort_map.
  - exact ext_old_ltb_implies_ltb.
  - exact ext_old_eqb_implies_eqb.
Qed.

Lemma selection_sort_instance_list_ext_implies_old_normal: 
  forall ipl1_ext ipl2_ext,  
    SelectionSort instr_point_ext_old_sched_ltb instr_point_ext_old_sched_eqb ipl1_ext = ipl2_ext ->
    SelectionSort instr_point_sched_ltb instr_point_sched_eqb (old_of_ext_list ipl1_ext) = (old_of_ext_list ipl2_ext).
Proof.
  intros.
  unfolds SelectionSort.
  eapply selsort_instance_list_ext_implies_old_normal in H; eauto.
  unfolds old_of_ext_list.
  rewrite map_length; trivial.
Qed.

Definition sfunc tau1 tau2 :=
  instr_point_ext_new_sched_leb tau1 tau2.

Local Lemma instr_point_ext_new_sched_ge_flip:
  forall y x,
    instr_point_ext_new_sched_geb y x =
    instr_point_ext_new_sched_leb x y.
Proof.
  intros y x.
  unfold instr_point_ext_new_sched_geb, instr_point_ext_new_sched_leb.
  rewrite lex_compare_antisym.
  destruct (lex_compare (ip_time_stamp2_ext x) (ip_time_stamp2_ext y));
    reflexivity.
Qed.

Lemma stable_permut_multi_skip:
  forall l1 y l2,
    ord_all instr_point_ext_new_sched_geb y l1 ->
    ord_all instr_point_ext_old_sched_ltb y l1 ->
    StablePermut instr_point_ext_old_sched_ltb
      instr_point_ext_old_sched_eqb sfunc
      (l1 ++ [y] ++ l2) (y :: l1 ++ l2).
Proof.
  intros l1 y l2 Hnew_ge Hold_lt.
  eapply stable_permut_multi_skip_generic.
  - exact instr_point_ext_old_sched_cmp_irrefl.
  - exact instr_point_ext_old_sched_cmp_antisymm.
  - exact instr_point_ext_old_sched_eqb_symm.
  - unfold ord_all in Hnew_ge |- *.
    rewrite !Forall_forall in Hnew_ge |- *.
    intros x Hin.
    rewrite <- instr_point_ext_new_sched_ge_flip.
    exact (Hnew_ge x Hin).
  - exact Hold_lt.
Qed.

Lemma sorted_implies_ord_all:
  forall lfirst y lskip,
    Sorted_b instr_point_ext_new_sched_leb (lfirst ++ y :: lskip) ->
    ord_all instr_point_ext_new_sched_geb y lfirst.
Proof.
  intros lfirst y lskip Hsorted.
  eapply sorted_prefix_implies_ord_all_reverse.
  - exact instr_point_ext_new_sched_geb_trans.
  - intros x z Hxz.
    rewrite instr_point_ext_new_sched_ge_flip.
    exact Hxz.
  - exact Hsorted.
Qed.
     
Lemma select_helper_stable_permut:
  forall r l x (n : nat) y l',
    Sorted_b instr_point_ext_new_sched_leb (l ++ r) ->
    nth n l x = x ->
    n < length l ->
    ord_all instr_point_ext_old_sched_ltb x (firstn n l) ->
    ord_all
      (combine_leb instr_point_ext_old_sched_ltb
        instr_point_ext_old_sched_eqb)
      x (remove_nth n l) ->
    select_helper instr_point_ext_old_sched_ltb
      instr_point_ext_old_sched_eqb l x n r = (y, l') ->
    StablePermut instr_point_ext_old_sched_ltb
      instr_point_ext_old_sched_eqb sfunc (l ++ r) (y :: l').
Proof.
  intros r l x n y l' Hsorted Hnth Hbound Hprefix Hremain Hselect.
  eapply select_helper_stable_permut_generic.
  - exact instr_point_ext_old_sched_ltb_trans.
  - exact instr_point_ext_old_sched_cmp_total.
  - exact instr_point_ext_old_sched_eqb_refl.
  - exact instr_point_ext_old_sched_eqb_trans.
  - exact instr_point_ext_old_sched_eqb_ltb_implies_ltb.
  - exact instr_point_ext_old_sched_ltb_eqb_implies_ltb.
  - exact instr_point_ext_old_sched_eqb_symm.
  - exact instr_point_ext_old_sched_cmp_irrefl.
  - exact instr_point_ext_old_sched_cmp_antisymm.
  - intros lfirst selected lskip Hsorted_prefix.
    pose proof
      (sorted_implies_ord_all lfirst selected lskip Hsorted_prefix)
      as Hnew_ge.
    unfold ord_all in Hnew_ge |- *.
    rewrite !Forall_forall in Hnew_ge |- *.
    intros point Hin.
    unfold sfunc.
    rewrite <- instr_point_ext_new_sched_ge_flip.
    exact (Hnew_ge point Hin).
  - exact Hsorted.
  - exact Hnth.
  - exact Hbound.
  - exact Hprefix.
  - exact Hremain.
  - exact Hselect.
Qed.

Lemma select_stable_permut: 
    forall l x y r,
        Sorted_b instr_point_ext_new_sched_leb ([x] ++ l) ->
        select instr_point_ext_old_sched_ltb instr_point_ext_old_sched_eqb x l = (y, r) -> 
        StablePermut instr_point_ext_old_sched_ltb instr_point_ext_old_sched_eqb sfunc (x :: l) (y :: r).
Proof.
    intros.
    unfolds select.
    eapply select_helper_stable_permut in H0; eauto.
    simpls; eauto. 
    unfold ord_all.
    eapply Forall_nil.
    simpls.
    eapply Forall_nil.
Qed.



Lemma select_helper_preserve_remain_sorted:
  forall r x l y n r',
    Sorted_b instr_point_ext_new_sched_leb (l ++ r) ->
    select_helper instr_point_ext_old_sched_ltb
      instr_point_ext_old_sched_eqb l x n r = (y, r') ->
    Sorted_b instr_point_ext_new_sched_leb r'.
Proof.
  intros r x l y n r' Hsorted Hselect.
  eapply select_helper_preserve_remain_sorted_generic; eauto.
  exact instr_point_ext_new_sched_leb_trans.
Qed.

Lemma select_preserve_remain_sorted:
    forall x l y r',
        Sorted_b instr_point_ext_new_sched_leb (x::l) ->
        select instr_point_ext_old_sched_ltb instr_point_ext_old_sched_eqb x l = (y, r') ->
        Sorted_b instr_point_ext_new_sched_leb r'.
Proof.
  intros.
  unfold select in H0.
  eapply select_helper_preserve_remain_sorted in H0; eauto.
Qed.

Lemma selsort_stable_permut:
  forall n l,
    Sorted_b instr_point_ext_new_sched_leb l ->
    length l = n ->
    StablePermut instr_point_ext_old_sched_ltb
      instr_point_ext_old_sched_eqb sfunc l
      (selsort instr_point_ext_old_sched_ltb
        instr_point_ext_old_sched_eqb l n).
Proof.
  intros n l Hsorted Hlength.
  eapply selsort_stable_permut_generic.
  - intros x xs y rest Hxs_sorted Hselect.
    eapply select_stable_permut; eauto.
  - intros x xs y rest Hxs_sorted Hselect.
    eapply select_preserve_remain_sorted; eauto.
  - exact Hsorted.
  - exact Hlength.
Qed.

Lemma selection_sort_instance_list_ext_is_stable_permut: 
  forall ipl1_ext ipl2_ext,  
    Sorted_b instr_point_ext_new_sched_leb ipl1_ext ->
    SelectionSort instr_point_ext_old_sched_ltb instr_point_ext_old_sched_eqb ipl1_ext = ipl2_ext -> 
    StablePermut instr_point_ext_old_sched_ltb instr_point_ext_old_sched_eqb sfunc ipl1_ext ipl2_ext.
Proof.
  intros.
  unfold SelectionSort in H0.
  pose proof (selsort_stable_permut (Datatypes.length ipl1_ext) ipl1_ext).
  eapply H1 in H; eauto.
  rewrite H0 in H; trivial.
Qed.


Notation instr_point_list_sema_stable_under_state_eq := ILSema.instr_point_list_sema_stable_under_state_eq.

(** Stable permutations preserve instance-list semantics up to state equivalence. *)
Local Lemma stable_swap_points_permutable:
  forall ipl tau1 tau2,
    (forall point1 point2,
      In point1 ipl ->
      In point2 ipl ->
      instr_point_ext_old_sched_lt point1 point2 ->
      instr_point_ext_new_sched_ge point1 point2 ->
      Permutable_ext point1 point2) ->
    In tau1 ipl ->
    In tau2 ipl ->
    instr_point_ext_old_sched_ltb tau1 tau2 = false ->
    instr_point_ext_old_sched_eqb tau1 tau2 = false ->
    sfunc tau1 tau2 = true ->
    Permutable_ext tau1 tau2.
Proof.
  intros ipl tau1 tau2 Hpermutable Hin1 Hin2 Hnot_lt Hnot_eq Hstable.
  assert (Hreverse_lt : instr_point_ext_old_sched_ltb tau2 tau1 = true).
  {
    destruct (instr_point_ext_old_sched_cmp_total tau1 tau2)
      as [Hlt | [Hgt | Heq]]; congruence.
  }
  apply Permutable_symm.
  eapply Hpermutable.
  - exact Hin2.
  - exact Hin1.
  - unfold instr_point_ext_old_sched_lt.
    unfold instr_point_ext_old_sched_ltb in Hreverse_lt.
    apply comparison_eqb_iff_eq in Hreverse_lt.
    exact Hreverse_lt.
  - unfold sfunc, instr_point_ext_new_sched_leb in Hstable.
    unfold instr_point_ext_new_sched_ge.
    apply orb_true_iff in Hstable.
    destruct Hstable as [Hlt | Heq].
    + right.
      rewrite lex_compare_antisym.
      apply comparison_eqb_iff_eq in Hlt.
      rewrite Hlt.
      reflexivity.
    + left.
      rewrite lex_compare_antisym.
      apply comparison_eqb_iff_eq in Heq.
      rewrite Heq.
      reflexivity.
Qed.

Lemma stable_permut_step_ext_lists_are_equivalent: 
  forall ipl1_ext ipl2_ext,
    (forall tau1 tau2,
      In tau1 ipl1_ext -> 
      In tau2 ipl1_ext ->
      instr_point_ext_old_sched_lt tau1 tau2 -> 
      instr_point_ext_new_sched_ge tau1 tau2 -> 
      Permutable_ext tau1 tau2 ) ->
    StablePermut_step instr_point_ext_old_sched_ltb instr_point_ext_old_sched_eqb sfunc ipl1_ext ipl2_ext -> 
    (
      forall st1, 
        Instr.NonAlias st1 ->
        (forall st2,
          instr_point_list_semantics (old_of_ext_list ipl1_ext) st1 st2 ->
          exists st2',
          instr_point_list_semantics (old_of_ext_list ipl2_ext) st1 st2' /\ 
          Instr.State.eq st2 st2'
        ) /\
        (forall st2,
          instr_point_list_semantics (old_of_ext_list ipl2_ext) st1 st2 ->
          exists st2',
          instr_point_list_semantics (old_of_ext_list ipl1_ext) st1 st2' /\ 
          Instr.State.eq st2 st2'
        )
    ).
Proof.
  induction ipl1_ext as [|head tail IH].
  - intros ipl2_ext Hpermutable Hstable.
    inversion Hstable; subst; discriminate.
  - intros ipl2_ext Hpermutable Hstable.
    change
      (ILSema.instr_point_lists_equivalent
        (old_of_ext_list (head :: tail)) (old_of_ext_list ipl2_ext)).
    inversion Hstable as
      [ltb eqb stablefunc l1 l2 tau l1' l2' Hl1 Hl2 Htail
      |ltb eqb stablefunc l1 l2 tau1 tau2 l' Hl1 Hl2
        Hnot_lt Hnot_eq Hstable_swap];
      subst.
    + inversion Hl1; subst.
      assert (Htail_equiv :
        ILSema.instr_point_lists_equivalent
          (old_of_ext_list l1') (old_of_ext_list l2')).
      {
        change
          (forall st1,
            Instr.NonAlias st1 ->
            (forall st2,
              instr_point_list_semantics (old_of_ext_list l1') st1 st2 ->
              exists st2',
                instr_point_list_semantics (old_of_ext_list l2') st1 st2' /\
                Instr.State.eq st2 st2') /\
            (forall st2,
              instr_point_list_semantics (old_of_ext_list l2') st1 st2 ->
              exists st2',
                instr_point_list_semantics (old_of_ext_list l1') st1 st2' /\
                Instr.State.eq st2 st2')).
        apply IH; [|exact Htail].
        intros point1 point2 Hin1 Hin2 Hold_lt Hnew_ge.
        apply Hpermutable; simpl; auto.
      }
      unfold old_of_ext_list.
      simpl.
      exact (ILSema.instr_point_lists_equivalent_cons
        (old_of_ext tau) (map old_of_ext l1') (map old_of_ext l2')
        Htail_equiv).
    + inversion Hl1; subst.
      pose proof
        (stable_swap_points_permutable
          (tau1 :: tau2 :: l') tau1 tau2 Hpermutable)
        as Hswap.
      specialize (Hswap
        (or_introl eq_refl) (or_intror (or_introl eq_refl))
        Hnot_lt Hnot_eq Hstable_swap).
      unfold Permutable_ext in Hswap.
      unfold old_of_ext_list.
      simpl.
      exact (ILSema.instr_point_lists_equivalent_swap
        (old_of_ext tau1) (old_of_ext tau2)
        (map old_of_ext l') Hswap).
Qed.

Lemma stable_permut'_ext_lists_are_equivalent: 
  forall n ipl1_ext ipl2_ext,
    (forall tau1 tau2,
      In tau1 ipl1_ext -> 
      In tau2 ipl1_ext ->
      instr_point_ext_old_sched_lt tau1 tau2 -> 
      instr_point_ext_new_sched_ge tau1 tau2 -> 
      Permutable_ext tau1 tau2 ) ->
    StablePermut' instr_point_ext_old_sched_ltb instr_point_ext_old_sched_eqb sfunc ipl1_ext ipl2_ext n -> 
    (
      forall st1, 
        Instr.NonAlias st1 ->
        (forall st2,
          instr_point_list_semantics (old_of_ext_list ipl1_ext) st1 st2 ->
          exists st2',
          instr_point_list_semantics (old_of_ext_list ipl2_ext) st1 st2' /\ 
          Instr.State.eq st2 st2'
        ) /\
        (forall st2,
          instr_point_list_semantics (old_of_ext_list ipl2_ext) st1 st2 ->
          exists st2',
          instr_point_list_semantics (old_of_ext_list ipl1_ext) st1 st2' /\ 
          Instr.State.eq st2 st2'
        )
    ).
Proof.
  induction n as [|n IH]; intros ipl1_ext ipl2_ext Hpermutable Hstable.
  - pose proof
      (stable_permut'_zero_inv
        _ _ _ _ _ _ Hstable) as Heq.
    subst ipl2_ext.
    change
      (ILSema.instr_point_lists_equivalent
        (old_of_ext_list ipl1_ext) (old_of_ext_list ipl1_ext)).
    apply ILSema.instr_point_lists_equivalent_refl.
  - destruct
      (stable_permut'_succ_inv
        _ _ _ _ _ _ _ Hstable)
      as (ipl_mid & Hstep & Htail).
    change
      (ILSema.instr_point_lists_equivalent
        (old_of_ext_list ipl1_ext) (old_of_ext_list ipl2_ext)).
    pose proof
      (stable_permut_step_implies_stable_permut
        _ _ _ _ _ _ Hstep) as Hstep_permut.
    assert (Hpermutable_tail :
      forall tau1 tau2,
        In tau1 ipl_mid ->
        In tau2 ipl_mid ->
        instr_point_ext_old_sched_lt tau1 tau2 ->
        instr_point_ext_new_sched_ge tau1 tau2 ->
        Permutable_ext tau1 tau2).
    {
      intros tau1 tau2 Hin1 Hin2 Hold_lt Hnew_ge.
      apply Hpermutable; try assumption.
      - apply (proj2
          (stable_permut_perserves_elems
            _ _ _ _ _ _ tau1 Hstep_permut)).
        exact Hin1.
      - apply (proj2
          (stable_permut_perserves_elems
            _ _ _ _ _ _ tau2 Hstep_permut)).
        exact Hin2.
    }
    pose proof
      (stable_permut_step_ext_lists_are_equivalent
        ipl1_ext ipl_mid Hpermutable Hstep) as Hstep_equiv.
    change
      (ILSema.instr_point_lists_equivalent
        (old_of_ext_list ipl1_ext) (old_of_ext_list ipl_mid)) in Hstep_equiv.
    pose proof
      (IH ipl_mid ipl2_ext Hpermutable_tail Htail) as Htail_equiv.
    change
      (ILSema.instr_point_lists_equivalent
        (old_of_ext_list ipl_mid) (old_of_ext_list ipl2_ext)) in Htail_equiv.
    exact (ILSema.instr_point_lists_equivalent_trans
      _ _ _ Hstep_equiv Htail_equiv).
Qed.

Lemma stable_permut_ext_lists_are_equivalent: 
  forall ipl1_ext ipl2_ext,
    (forall tau1 tau2,
      In tau1 ipl1_ext -> 
      In tau2 ipl1_ext ->
      instr_point_ext_old_sched_lt tau1 tau2 -> 
      instr_point_ext_new_sched_ge tau1 tau2 -> 
      Permutable_ext tau1 tau2 ) ->
    StablePermut instr_point_ext_old_sched_ltb instr_point_ext_old_sched_eqb sfunc ipl1_ext ipl2_ext -> 
    (
      forall st1, 
        Instr.NonAlias st1 ->
        (forall st2,
          instr_point_list_semantics (old_of_ext_list ipl1_ext) st1 st2 ->
          exists st2',
          instr_point_list_semantics (old_of_ext_list ipl2_ext) st1 st2' /\ 
          Instr.State.eq st2 st2'
        ) /\
        (forall st2,
          instr_point_list_semantics (old_of_ext_list ipl2_ext) st1 st2 ->
          exists st2',
          instr_point_list_semantics (old_of_ext_list ipl1_ext) st1 st2' /\ 
          Instr.State.eq st2 st2'
        )
    ).
Proof.
  intros.
  destruct H0 as (n & STABLE).
  eapply stable_permut'_ext_lists_are_equivalent; eauto.
Qed.

(** Part 3: PolyLex semantics, for codegen *)

Inductive poly_lex_semantics : nat -> (nat -> list Z -> bool) -> (list PolyInstr) -> State.t -> State.t -> Prop :=
| PolyLexDone : forall env_dim to_scan prog mem,
    (forall n p, to_scan n p = false) ->
    poly_lex_semantics env_dim to_scan prog mem mem
| PolyLexProgress : forall env_dim to_scan prog st1 st2 st3 poly_instr n p wcs rcs,
    to_scan n p = true -> nth_error prog n = Some poly_instr ->
    (forall n2 p2, lex_compare p2 p = Lt -> to_scan n2 p2 = false) ->
    Instr.instr_semantics poly_instr.(pi_instr) (current_src_args_in_dim env_dim poly_instr p) wcs rcs st1 st2 ->
    poly_lex_semantics env_dim (scanned to_scan n p) prog st2 st3 ->
    poly_lex_semantics env_dim to_scan prog st1 st3.


Definition env_poly_lex_semantics (env : list Z) (dim : nat) (pis : list PolyInstr) (mem1 mem2 : State.t) :=
  poly_lex_semantics dim (env_scan pis env dim) pis mem1 mem2.
    
Inductive lex_semantics: t -> State.t -> State.t -> Prop :=
| PLexSemaIntro: forall pprog pis varctxt vars env st1 st2,
    pprog = (pis, varctxt, vars) -> 
    Instr.Compat vars st1 ->
    Instr.NonAlias st1 -> 
    Instr.InitEnv varctxt env st1 ->
    env_poly_lex_semantics env (pprog_current_dim pprog) pis st1 st2 ->
    lex_semantics pprog st1 st2.

Theorem poly_lex_semantics_extensionality :
  forall env_dim to_scan1 prog mem1 mem2,
    poly_lex_semantics env_dim to_scan1 prog mem1 mem2 ->
    forall to_scan2,
      (forall n p, to_scan1 n p = to_scan2 n p) ->
      poly_lex_semantics env_dim to_scan2 prog mem1 mem2.
Proof.
  intros env_dim to_scan1 prog mem1 mem2 Hsem.
  induction Hsem.
  - intros to_scan2 Heq.
    apply PolyLexDone.
    intros n p.
    rewrite <- Heq.
    apply H.
  - intros to_scan2 Heq.
    eapply PolyLexProgress; eauto.
    apply IHHsem.
    intros n0 p0.
    unfold scanned.
    rewrite <- Heq.
    reflexivity.
Qed.
  
Lemma poly_lex_semantics_pis_ext_single :
  forall env_dim pis1 pis2 to_scan mem1 mem2,
    Forall2
      (fun pi1 pi2 =>
         pi1.(pi_instr) = pi2.(pi_instr) /\
         pi1.(pi_point_witness) = pi2.(pi_point_witness) /\
         pi1.(pi_transformation) = pi2.(pi_transformation))
      pis1 pis2 ->
    poly_lex_semantics env_dim to_scan pis1 mem1 mem2 ->
    poly_lex_semantics env_dim to_scan pis2 mem1 mem2.
Proof.
  intros env_dim pis1 pis2 to_scan mem1 mem2 Hsame Hsem.
  induction Hsem as
      [env_dim to_scan1 prog mem Hdone
      |env_dim to_scan1 prog mem1 mem2 mem3 pi n p wcs rcs Hscanp Heqpi Hts Hsem1 Hsem2 IH].
  - apply PolyLexDone; auto.
  - destruct (Forall2_nth_error _ _ _ _ _ _ _ Hsame Heqpi) as [pi2 [Hpi2 [H1 [Hw H2]]]].
    eapply PolyLexProgress; [exact Hscanp|exact Hpi2|exact Hts| |apply IH; auto].
    rewrite <- H1.
    unfold current_src_args_in_dim, current_src_args_at, current_env_dim_in_dim,
      current_transformation_at.
    rewrite <- Hw, <- H2.
    exact Hsem1.
Qed.

Lemma poly_lex_semantics_pis_ext_iff :
  forall env_dim pis1 pis2 to_scan mem1 mem2,
    Forall2
      (fun pi1 pi2 =>
         pi1.(pi_instr) = pi2.(pi_instr) /\
         pi1.(pi_point_witness) = pi2.(pi_point_witness) /\
         pi1.(pi_transformation) = pi2.(pi_transformation))
      pis1 pis2 ->
    poly_lex_semantics env_dim to_scan pis1 mem1 mem2 <->
    poly_lex_semantics env_dim to_scan pis2 mem1 mem2.
Proof.
  intros env_dim pis1 pis2 to_scan mem1 mem2 Hsame.
  split.
  - apply poly_lex_semantics_pis_ext_single; auto.
  - apply poly_lex_semantics_pis_ext_single.
    eapply Forall2_imp; [|apply Forall2_sym; exact Hsame].
    intros x y H; simpl in *.
    destruct H as [HI [HW HT]].
    split; [symmetry; exact HI|].
    split; [symmetry; exact HW|].
    symmetry; exact HT.
Qed.

Lemma poly_lex_semantics_ext_iff :
  forall env_dim pis to_scan1 to_scan2 mem1 mem2,
    (forall n p, to_scan1 n p = to_scan2 n p) ->
    poly_lex_semantics env_dim to_scan1 pis mem1 mem2 <->
    poly_lex_semantics env_dim to_scan2 pis mem1 mem2.
Proof.
  intros env_dim pis to_scan1 to_scan2 mem1 mem2 Hsame.
  split; intros H.
  - eapply poly_lex_semantics_extensionality; [exact H|]. auto.
  - eapply poly_lex_semantics_extensionality; [exact H|]. auto.
Qed.

Local Lemma scanned_disjoint_right :
  forall (to_scan1 to_scan2 : nat -> list Z -> bool) (n : nat) (p : list Z),
    (forall m q, to_scan1 m q = false \/ to_scan2 m q = false) ->
    forall m q,
      scanned to_scan1 n p m q = false \/ to_scan2 m q = false.
Proof.
  intros to_scan1 to_scan2 n p Hdisjoint m q.
  unfold scanned.
  destruct (to_scan1 m q) eqn:Hscan1; simpl.
  - destruct (Hdisjoint m q) as [Hfalse|Hfalse].
    + congruence.
    + right; exact Hfalse.
  - left; reflexivity.
Qed.

Local Lemma scanned_cross_disjoint_right :
  forall (to_scan1 to_scan2 : nat -> list Z -> bool) (n : nat) (p : list Z),
    (forall n1 p1 n2 p2,
      lex_compare p2 p1 = Lt ->
      to_scan1 n1 p1 = false \/ to_scan2 n2 p2 = false) ->
    forall n1 p1 n2 p2,
      lex_compare p2 p1 = Lt ->
      scanned to_scan1 n p n1 p1 = false \/ to_scan2 n2 p2 = false.
Proof.
  intros to_scan1 to_scan2 n p Hcross n1 p1 n2 p2 Hlt.
  destruct (Hcross n1 p1 n2 p2 Hlt) as [Hfalse|Hfalse].
  - left; unfold scanned; rewrite Hfalse; reflexivity.
  - right; exact Hfalse.
Qed.

Local Lemma scanned_union_compat :
  forall (to_scan1 to_scan2 : nat -> list Z -> bool) (n : nat) (p : list Z),
    wf_scan to_scan1 ->
    to_scan1 n p = true ->
    (forall m q, to_scan1 m q = false \/ to_scan2 m q = false) ->
    forall m q,
      scanned to_scan1 n p m q || to_scan2 m q =
      scanned (fun n0 p0 => to_scan1 n0 p0 || to_scan2 n0 p0) n p m q.
Proof.
  intros to_scan1 to_scan2 n p Hwf Hcurrent Hdisjoint m q.
  unfold scanned; simpl.
  destruct (Hdisjoint m q) as [Hfalse|Hfalse].
  - rewrite Hfalse; simpl.
    destruct (is_eq p q && (n =? m)%nat) eqn:Hequal; simpl.
    + reflect. destruct Hequal as [Heqp Hn].
      rewrite Heqp, Hn in Hcurrent; congruence.
    + rewrite andb_true_r; reflexivity.
  - rewrite Hfalse.
    destruct (to_scan1 m q); simpl; rewrite ?orb_false_r; reflexivity.
Qed.


Theorem poly_lex_concat :
  forall env_dim to_scan1 prog mem1 mem2,
    poly_lex_semantics env_dim to_scan1 prog mem1 mem2 ->
    forall to_scan2 mem3,
    wf_scan to_scan1 ->
    (forall n p, to_scan1 n p = false \/ to_scan2 n p = false) ->
    (forall n1 p1 n2 p2, lex_compare p2 p1 = Lt -> to_scan1 n1 p1 = false \/ to_scan2 n2 p2 = false) ->
    poly_lex_semantics env_dim to_scan2 prog mem2 mem3 ->
    poly_lex_semantics env_dim (fun n p => to_scan1 n p || to_scan2 n p) prog mem1 mem3.
Proof.
  intros env_dim to_scan1 prog mem1 mem2 Hsem.
  induction Hsem as
      [env_dim to_scan3 prog1 mem4 Hdone
      |env_dim to_scan3 prog1 mem4 mem5 mem6 pi n p wcs rcs Hscanp Heqpi Hts Hsem1 Hsem2 IH].
  - intros to_scan2 mem3 Hwf1 Hdisj Hcmp Hsem1.
    eapply poly_lex_semantics_extensionality with (to_scan1 := to_scan2); [exact Hsem1|].
    intros n0 p0.
    destruct (to_scan2 n0 p0); simpl.
    + rewrite (Hdone n0 p0). reflexivity.
    + rewrite (Hdone n0 p0). reflexivity.
  - intros to_scan2 mem3 Hwf1 Hdisj Hcmp Hsem3. eapply PolyLexProgress with (n := n) (p := p) (wcs:=wcs) (rcs:=rcs) (poly_instr:=pi) (st2:=mem5); trivial. eauto.
    + intros n2 p2 Hts2.
      reflect. split.
      * apply (Hts n2 p2); auto.
      * destruct (Hcmp n p n2 p2) as [H | H]; auto; congruence.
    + assert (Hrest :
          poly_lex_semantics env_dim
            (fun n0 p0 => scanned to_scan3 n p n0 p0 || to_scan2 n0 p0)
            prog1 mem5 mem3).
      {
        assert (Hwf_scanned : wf_scan (scanned to_scan3 n p)).
        { apply scanned_wf_compat; auto. }
        assert (Hdisj_scanned :
          forall n0 p0,
            scanned to_scan3 n p n0 p0 = false \/ to_scan2 n0 p0 = false).
        { apply scanned_disjoint_right; exact Hdisj. }
        assert (Hcmp_scanned :
          forall n1 p1 n2 p2,
            lex_compare p2 p1 = Lt ->
            scanned to_scan3 n p n1 p1 = false \/ to_scan2 n2 p2 = false).
        { apply scanned_cross_disjoint_right; exact Hcmp. }
        pose proof (IH to_scan2 mem3 Hwf_scanned Hdisj_scanned Hcmp_scanned Hsem3) as Hrest.
        exact Hrest.
      }
      eapply poly_lex_semantics_extensionality with
          (to_scan1 := fun n0 p0 => scanned to_scan3 n p n0 p0 || to_scan2 n0 p0).
      * exact Hrest.
      * apply scanned_union_compat; assumption.
Qed.

Theorem poly_lex_concat_seq :
  forall env_dim A to_scans (l : list A) prog mem1 mem2,
  Instr.IterSem.iter_semantics (fun x => poly_lex_semantics env_dim (to_scans x) prog) l mem1 mem2 ->
    (forall x, wf_scan (to_scans x)) ->
    (forall x1 k1 x2 k2 n p, to_scans x1 n p = true -> to_scans x2 n p = true -> nth_error l k1 = Some x1 -> nth_error l k2 = Some x2 -> k1 = k2) ->
    (forall x1 n1 p1 k1 x2 n2 p2 k2, lex_compare p2 p1 = Lt -> to_scans x1 n1 p1 = true -> to_scans x2 n2 p2 = true -> nth_error l k1 = Some x1 -> nth_error l k2 = Some x2 -> (k2 <= k1)%nat) ->
    poly_lex_semantics env_dim (fun n p => existsb (fun x => to_scans x n p) l) prog mem1 mem2.
Proof.
  intros env_dim A to_scans l1 prog mem1 mem3 Hsem.
  induction Hsem as [mem|x l mem1 mem2 mem3 Hsem1 Hsem2 IH].
  - intros Hwf Hscans Hcmp.
    simpl.
    apply PolyLexDone; auto.
  - intros Hwf Hscans Hcmp.
    eapply poly_lex_semantics_extensionality.
    + eapply poly_lex_concat; [exact Hsem1| | | |apply IH; auto].
      * apply Hwf.
      * intros n p. simpl.
        destruct (to_scans x n p) eqn:Hscanl; [|auto]. right.
        apply not_true_is_false; rewrite existsb_exists; intros [x1 [Hin Hscanx1]].
        apply In_nth_error in Hin; destruct Hin as [u Hu].
        specialize (Hscans x O x1 (S u) n p Hscanl Hscanx1).
        simpl in Hscans. intuition congruence.
      * intros n1 p1 n2 p2 H.
        destruct (to_scans x n1 p1) eqn:Hscanl; [|auto]. right.
        apply not_true_is_false; rewrite existsb_exists; intros [x1 [Hin Hscanx1]].
        apply In_nth_error in Hin; destruct Hin as [u Hu].
        specialize (Hcmp x n1 p1 O x1 n2 p2 (S u) H Hscanl Hscanx1).
        intuition lia.
      * intros x1 k1 x2 k2 n p H1 H2 H3 H4; specialize (Hscans x1 (S k1) x2 (S k2) n p).
        intuition congruence.
      * intros x1 n1 p1 k1 x2 n2 p2 k2 H1 H2 H3 H4 H5; specialize (Hcmp x1 n1 p1 (S k1) x2 n2 p2 (S k2)).
        intuition lia.
    + intros n p. simpl. reflexivity.
Qed.

Open Scope Z_scope.
Open Scope list_scope.
(** * Translating a program from explicit scheduling to lexicographical scanning *)

Definition insert_zeros (d : nat) (i : nat) (l : list Z) :=
  resize i l ++ repeat 0 d ++ skipn i l.
Definition insert_zeros_constraint (d : nat) (i : nat) (c : list Z * Z) := (insert_zeros d i (fst c), snd c).

(** [make_null_poly d n] creates a polyhedron with the constraints that the variables from [d] to [d+n-1] are null *)
Fixpoint make_null_poly (d : nat) (n : nat) :=
  match n with
  | O => nil
  | S n => (repeat 0 d ++ (-1 :: nil), 0) :: (repeat 0 d ++ (1 :: nil), 0) :: make_null_poly (S d) n
  end.

(** [make_sched_poly d i env_size l] adds the lexicographical constraints in [l] as equalities, preserving the [env_size] first variables,
    and inserting [d] variables after that. *)
Fixpoint make_sched_poly (d : nat) (i : nat) (env_size : nat) (l : list (list Z * Z)) :=
  (* add scheduling constraints in polyhedron after env, so that with fixed env, lexicographical ordering preserves semantics *)
  match l with
  | nil => make_null_poly (i + env_size)%nat (d - i)%nat
  | (v, c) :: l =>
    let vpref := resize env_size v in
    let vsuf := skipn env_size v in
    (vpref ++ repeat 0 i ++ (-1 :: repeat 0 (d - i - 1)%nat) ++ vsuf, -c)
      :: (mult_vector (-1) vpref ++ repeat 0 i ++ (1 :: repeat 0 (d - i - 1)%nat) ++ (mult_vector (-1) vsuf), c)
      :: make_sched_poly d (S i) env_size l
  end.

Theorem make_null_poly_correct :
  forall n d p q r, length p = d -> length q = n -> in_poly (p ++ q ++ r) (make_null_poly d n) = is_null q.
Proof.
  induction n.
  - intros; destruct q; simpl in *; auto; lia.
  - intros d p q r Hlp Hlq.
    destruct q as [|x q]; simpl in *; [lia|].
    unfold satisfies_constraint; simpl.
    repeat (rewrite dot_product_app; [|rewrite repeat_length; lia]; simpl).
    autorewrite with vector.
    assert (He : p ++ x :: q ++ r = (p ++ (x :: nil)) ++ q ++ r).
    { rewrite <- app_assoc; auto. }
    rewrite He. rewrite IHn; [|rewrite app_length; simpl; lia|lia].
    rewrite andb_assoc. f_equal.
    destruct (x =? 0) eqn:Hx; reflect; lia.
Qed.

Theorem make_sched_poly_correct_aux :
  forall l i d es, (length l <= d - i)%nat ->
           forall p q r s, length p = es -> length q = i -> length r = (d - i)%nat ->
                    in_poly (p ++ q ++ r ++ s) (make_sched_poly d i es l) = is_eq r (affine_product l (p ++ s)).
Proof.
  induction l.
  - intros. simpl in *. rewrite is_eq_nil_right. rewrite app_assoc. apply make_null_poly_correct; auto. rewrite app_length; lia.
  - intros i d es Hlength p q r s Hlp Hlq Hlr.
    simpl in *. destruct a as [v c]. simpl in *.
    destruct r as [|x r]; simpl in *; [lia|].
    unfold satisfies_constraint; simpl.
    repeat (rewrite dot_product_app; [|rewrite ?repeat_length, ?mult_vector_length, ?resize_length; lia]; simpl).
    autorewrite with vector.
    assert (He : p ++ q ++ x :: r ++ s = p ++ (q ++ (x :: nil)) ++ r ++ s).
    { rewrite <- app_assoc. auto. }
    rewrite He. rewrite IHl; [|lia|auto|rewrite app_length;simpl;lia|lia].
    rewrite andb_assoc. f_equal.
    assert (Hde : Linalg.dot_product v (p ++ s) =
                  Linalg.dot_product p (resize es v) +
                  Linalg.dot_product s (skipn es v)).
    { pose proof (dot_product_app_right v p s) as Htmp.
      rewrite dot_product_commutative with (xs := resize (length p) v) (ys := p) in Htmp.
      rewrite dot_product_commutative with (xs := skipn (length p) v) (ys := s) in Htmp.
      rewrite Hlp in Htmp.
      exact Htmp. }
    destruct (x =? Linalg.dot_product v (p ++ s) + c) eqn:Hx; reflect; lia.
Qed.

Theorem make_sched_poly_correct :
  forall l d es, (length l <= d)%nat ->
            forall p q r, length p = es -> length q = d ->
                    in_poly (p ++ q ++ r) (make_sched_poly d 0%nat es l) = is_eq q (affine_product l (p ++ r)).
Proof.
  intros. apply make_sched_poly_correct_aux with (q := nil); auto; lia.
Qed.

Theorem make_null_poly_nrl :
  forall n d, (poly_nrl (make_null_poly d n) <= d + n)%nat.
Proof.
  induction n.
  - intros; unfold poly_nrl; simpl; lia.
  - intros d. simpl. unfold poly_nrl; simpl.
    rewrite !Nat.max_lub_iff.
    split; [|split; [|specialize (IHn (S d)); unfold poly_nrl in *; lia]];
      rewrite <- nrlength_def, resize_app_le, repeat_length by (rewrite repeat_length; lia);
      replace (d + S n - d)%nat with (S n) by lia; simpl;
        f_equiv; f_equiv; rewrite resize_eq; simpl; (reflexivity || lia).
Qed.

Theorem make_sched_poly_nrl_aux :
  forall l i d es, (length l + i <= d)%nat -> (poly_nrl (make_sched_poly d i es l) <= d + (Nat.max es (poly_nrl l)))%nat.
Proof.
  induction l.
  - simpl; intros i d es H.
    generalize (make_null_poly_nrl (d - i)%nat (i + es)%nat). lia.
  - intros i d es H; simpl in *. destruct a as [a c]. unfold poly_nrl in *; simpl in *.
    rewrite !Nat.max_lub_iff. split; [|split; [|rewrite IHl; lia]].
    all: rewrite nrlength_app; transitivity (es + (i + S ((d - i - 1) + (nrlength a - es))))%nat; [|lia].
    all: rewrite ?mult_vector_length, resize_length; apply Nat.add_le_mono_l.
    all: rewrite nrlength_app, repeat_length; apply Nat.add_le_mono_l.
    all: rewrite nrlength_cons; apply -> Nat.succ_le_mono.
    all: rewrite nrlength_app, repeat_length; apply Nat.add_le_mono_l.
    all: rewrite ?nrlength_mult, nrlength_skipn; lia.
Qed.

Theorem make_sched_poly_nrl :
  forall l d es, (length l <= d)%nat -> (poly_nrl (make_sched_poly d 0%nat es l) <= d + (Nat.max es (poly_nrl l)))%nat.
Proof.
  intros; apply make_sched_poly_nrl_aux; lia.
Qed.

Lemma insert_zeros_nrl :
  forall d es v, (nrlength (insert_zeros d es v) <= d + nrlength v)%nat.
Proof.
  induction es.
  - intros v; unfold insert_zeros; simpl. rewrite nrlength_app, repeat_length; lia.
  - intros [|x v]; unfold insert_zeros in *; simpl.
    + case_if eq H; reflect; [lia|].
      exfalso; apply H. apply nrlength_null_zero.
      unfold is_null. rewrite !forallb_app; reflect.
      split; [apply resize_nil_null|]. split; [apply repeat_zero_is_null|auto].
    + case_if eq H1; reflect; [lia|].
      case_if eq H2; reflect.
      * destruct H2 as [-> H2]; apply nrlength_zero_null in H2. destruct H1 as [H1 | H1]; [lia|].
        exfalso; apply H1. apply nrlength_null_zero.
        rewrite resize_null_repeat by auto.
        unfold is_null; rewrite !forallb_app; reflect.
        split; [apply repeat_zero_is_null|]. split; [apply repeat_zero_is_null|].
        apply nrlength_zero_null; apply nrlength_null_zero in H2.
        rewrite nrlength_skipn; lia.
      * specialize (IHes v). lia.
Qed.

Definition pi_elim_schedule (d : nat) (env_size : nat) (pi : PolyInstr) :=
  {|
    pi_depth:= pi.(pi_depth);
    pi_instr := pi.(pi_instr) ;
    pi_schedule := nil ;
    pi_point_witness := PSWInsertAfterEnv d pi.(pi_point_witness) ;
    pi_transformation := pi.(pi_transformation) ;
    pi_access_transformation := pi.(pi_access_transformation) ;
    pi_poly := make_sched_poly d 0%nat env_size pi.(pi_schedule) ++
                map (insert_zeros_constraint d env_size) pi.(pi_poly) ;
    pi_waccess := pi.(pi_waccess);
    pi_raccess := pi.(pi_raccess);
  |}.

Lemma pi_elim_schedule_nrl :
  forall d es pi,
    (length pi.(pi_schedule) <= d)%nat ->
    (poly_nrl (pi_elim_schedule d es pi).(pi_poly) <= d + (Nat.max es (Nat.max (poly_nrl pi.(pi_poly)) (poly_nrl pi.(pi_schedule)))))%nat.
Proof.
  intros d es pi H. simpl.
  rewrite poly_nrl_app. rewrite Nat.max_lub_iff; split.
  - rewrite make_sched_poly_nrl; lia.
  - unfold poly_nrl, insert_zeros_constraint in *. rewrite map_map. apply list_le_max; intros u Hu.
    rewrite in_map_iff in Hu. destruct Hu as [c [Hu Hc]]; simpl in *.
    transitivity (d + nrlength (fst c))%nat;
      [|apply Nat.add_le_mono_l; rewrite !Nat.max_le_iff; right; left; apply list_max_ge; rewrite in_map_iff; exists c; auto].
    rewrite <- Hu; apply insert_zeros_nrl.
Qed.


Definition elim_schedule (d : nat) (env_size : nat) (p : list PolyInstr) := map (pi_elim_schedule d env_size) p.


Lemma split3_eq :
  forall i d l, resize i l ++ resize d (skipn i l) ++ skipn (d + i)%nat l =v= l.
Proof.
  intros.
  rewrite <- is_eq_veq.
  rewrite is_eq_app_left. autorewrite with vector. rewrite is_eq_reflexive. simpl.
  rewrite is_eq_app_left. autorewrite with vector. rewrite is_eq_reflexive. simpl.
  rewrite skipn_skipn. apply is_eq_reflexive.
Qed.

Lemma insert_zeros_product_skipn :
  forall d i l1 l2,
    Linalg.dot_product (insert_zeros d i l1) l2 =
    Linalg.dot_product l1 (resize i l2 ++ skipn (d + i)%nat l2).
Proof.
  intros.
  unfold insert_zeros.
  rewrite !dot_product_app_left, dot_product_app_right.
  autorewrite with vector. rewrite repeat_length.
  rewrite skipn_skipn. lia.
Qed.

Lemma affine_product_skipn :
  forall d i m l, affine_product (map (insert_zeros_constraint d i) m) l = affine_product m (resize i l ++ skipn (d + i)%nat l).
Proof.
  intros. unfold affine_product. rewrite map_map.
  apply map_ext. intros.
  unfold insert_zeros_constraint; simpl.
  rewrite insert_zeros_product_skipn. auto.
Qed.

Lemma insert_zeros_commute_after_env :
  forall added d i l,
    insert_zeros added (i + d)%nat (insert_zeros d i l) =
    insert_zeros d i (insert_zeros added i l).
Proof.
  exact LinalgExt.insert_zeros_at_commute.
Qed.

Lemma current_transformation_at_pi_elim_schedule :
  forall d env_dim es pi,
    current_transformation_at env_dim (pi_elim_schedule d es pi) =
    map (insert_zeros_constraint d env_dim) (current_transformation_at env_dim pi).
Proof.
  intros d env_dim es pi.
  unfold current_transformation_at, pi_elim_schedule.
  simpl.
  reflexivity.
Qed.

Lemma current_src_args_at_pi_elim_schedule :
  forall d env_dim es pi current,
    (env_dim <= length current)%nat ->
    current_src_args_at env_dim (pi_elim_schedule d es pi) current =
    current_src_args_at env_dim pi
      (firstn env_dim current ++ skipn (d + env_dim)%nat current).
Proof.
  intros d env_dim es pi current Henv.
  unfold current_src_args_at.
  rewrite current_transformation_at_pi_elim_schedule.
  rewrite affine_product_skipn.
  eapply affine_product_proper; [reflexivity|].
  rewrite <- is_eq_veq.
  rewrite is_eq_app by (rewrite resize_length, firstn_length; lia).
  assert (Hresize : is_eq (resize env_dim current) (firstn env_dim current) = true).
  {
    assert (Heq_rf : resize env_dim current = firstn env_dim current).
    {
      revert current Henv.
      induction env_dim as [|env_dim IH]; intros current Henv.
      - destruct current; reflexivity.
      - destruct current as [|x xs].
        { exfalso. simpl in Henv. lia. }
        simpl in Henv.
        simpl. f_equal. apply IH. lia.
    }
    rewrite Heq_rf.
    apply is_eq_reflexive.
  }
  rewrite Hresize.
  rewrite is_eq_reflexive.
  simpl. reflexivity.
Qed.

Lemma current_env_dim_of_pi_elim_schedule_drop :
  forall d pw current,
    (witness_current_point_dim (PSWInsertAfterEnv d pw) <= length current)%nat ->
    current_env_dim_of pw
      (firstn (current_env_dim_of (PSWInsertAfterEnv d pw) current) current ++
       skipn (d + current_env_dim_of (PSWInsertAfterEnv d pw) current)%nat current) =
    current_env_dim_of (PSWInsertAfterEnv d pw) current.
Proof.
  intros d pw current Hlen.
  unfold current_env_dim_of.
  unfold witness_current_point_dim in Hlen |- *.
  cbn [witness_added_dims witness_base_point_dim] in Hlen |- *.
  set (wd := witness_current_point_dim pw).
  set (lc := length current).
  set (env_dim := (lc - (d + wd))%nat).
  assert (Henv : (env_dim <= length current)%nat).
  { unfold env_dim, lc. lia. }
  rewrite app_length.
  rewrite firstn_length_le by (unfold env_dim, wd, lc; simpl; lia).
  rewrite skipn_length.
  unfold env_dim, lc, wd.
  replace
    (length current -
     (d +
      (length current -
       (witness_base_point_dim pw + (d + witness_added_dims pw)))))%nat
    with (witness_base_point_dim pw + witness_added_dims pw)%nat by lia.
  replace
    ((length current - (witness_base_point_dim pw + (d + witness_added_dims pw))) +
     (witness_base_point_dim pw + witness_added_dims pw) -
     (witness_base_point_dim pw + witness_added_dims pw))%nat
    with (length current -
          (witness_base_point_dim pw + (d + witness_added_dims pw)))%nat by lia.
  reflexivity.
Qed.

Lemma current_src_args_of_pi_elim_schedule :
  forall d es pi current,
    (witness_current_point_dim (pi_elim_schedule d es pi).(pi_point_witness) <= length current)%nat ->
    current_src_args_of (pi_elim_schedule d es pi) current =
    current_src_args_of pi
      (firstn (current_env_dim_of (pi_elim_schedule d es pi).(pi_point_witness) current) current ++
       skipn
         (d + current_env_dim_of (pi_elim_schedule d es pi).(pi_point_witness) current)%nat
         current).
Proof.
  intros d es pi current Hlen.
  unfold current_src_args_of.
  rewrite current_src_args_at_pi_elim_schedule.
  2: {
    unfold current_env_dim_of in *.
    simpl in Hlen.
    lia.
  }
  unfold current_src_args_of.
  f_equal.
  symmetry.
  apply current_env_dim_of_pi_elim_schedule_drop.
  exact Hlen.
Qed.

Lemma current_src_args_at_pi_elim_schedule_resize :
  forall d env_dim es pi current,
    current_src_args_at env_dim (pi_elim_schedule d es pi) current =
    current_src_args_at env_dim pi
      (resize env_dim current ++ skipn (d + env_dim)%nat current).
Proof.
  intros d env_dim es pi current.
  unfold current_src_args_at.
  rewrite current_transformation_at_pi_elim_schedule.
  apply affine_product_skipn.
Qed.

Lemma current_env_dim_in_dim_pi_elim_schedule :
  forall d es dim pi,
    current_env_dim_in_dim (dim + d) (pi_elim_schedule d es pi).(pi_point_witness) =
    current_env_dim_in_dim dim pi.(pi_point_witness).
Proof.
  intros d es dim pi.
  unfold current_env_dim_in_dim.
  simpl.
  unfold witness_current_point_dim, witness_base_point_dim, witness_added_dims.
  simpl.
  lia.
Qed.

Lemma current_src_args_in_dim_pi_elim_schedule_resize :
  forall d es dim pi current,
    current_src_args_in_dim (dim + d) (pi_elim_schedule d es pi) current =
    current_src_args_in_dim dim pi
      (resize (current_env_dim_in_dim dim pi.(pi_point_witness)) current ++
       skipn (d + current_env_dim_in_dim dim pi.(pi_point_witness))%nat current).
Proof.
  intros d es dim pi current.
  unfold current_src_args_in_dim.
  rewrite current_env_dim_in_dim_pi_elim_schedule.
  apply current_src_args_at_pi_elim_schedule_resize.
Qed.

Theorem poly_elim_schedule_semantics_preserve :
  forall d es scan_dim env to_scan_lex prog_lex mem1 mem2,
    (d <= scan_dim)%nat ->
    poly_lex_semantics scan_dim to_scan_lex prog_lex mem1 mem2 ->
    forall to_scan prog,
      prog_lex = elim_schedule d es prog ->
      wf_scan to_scan -> wf_scan to_scan_lex ->
      (forall n pi, nth_error prog n = Some pi -> (length pi.(pi_schedule) <= d)%nat) ->
      (forall n pi, nth_error prog n = Some pi ->
         current_env_dim_in_dim (scan_dim - d) pi.(pi_point_witness) = es) ->
      (forall n p q ts pi, nth_error prog n = Some pi -> length p = es -> length ts = d ->
                      to_scan_lex n (p ++ ts ++ q) = is_eq ts (affine_product pi.(pi_schedule) (p ++ q)) && to_scan n (p ++ q)) ->
      (forall n p q, length p = es -> to_scan n (p ++ q) = true -> p =v= env) ->
      (forall n p, nth_error prog n = None -> to_scan n p = false) ->
      poly_semantics (scan_dim - d) to_scan prog mem1 mem2.
Proof.
  intros d es scan_dim env to_scan_lex prog_lex mem1 mem2 Hdscan Hsem.
  remember scan_dim as scan_dim0 eqn:Hscan_dim in Hsem.
  revert scan_dim Hdscan Hscan_dim.
  induction Hsem as
      [env_dim to_scan_l1 prog_l1 mem3 Hdone
      |env_dim to_scan_l1 prog_l1 mem3 mem4 mem5 pi n p wcs rcs Hscanp Heqpi Hts Hsem1 Hsem2 IH];
    intros scan_dim Hdscan Hscan_dim.
  - subst env_dim.
    intros to_scan prog Hprogeq Hwf Hwflex Hsched_length Henvdim Hcompat Hscanenv Hout.
    apply PolyDone. intros n p.
    destruct (nth_error prog n) as [pi|] eqn:Heq.
    + specialize (Hcompat n (resize es p) (skipn es p) (resize d (affine_product pi.(pi_schedule) p)) pi Heq).
      assert (Hlenp : length (resize es p) = es) by apply resize_length.
      assert (Hlents : length (resize d (affine_product (pi_schedule pi) p)) = d) by apply resize_length.
      specialize (Hcompat Hlenp Hlents).
      rewrite Hdone in Hcompat.
      rewrite resize_skipn_eq in Hcompat.
      rewrite resize_eq in Hcompat by (unfold affine_product; rewrite map_length; eauto).
      rewrite is_eq_reflexive in Hcompat.
      simpl in Hcompat.
      symmetry. exact Hcompat.
    + auto.
  - subst env_dim.
    intros to_scan prog Hprogeq Hwf Hwflex Hsched_length Henvdim Hcompat Hscanenv Hout.
    rewrite <- split3_eq with (d := d) (i := es) in Hscanp.
    rewrite Hprogeq in *; unfold elim_schedule in Heqpi.
    destruct (nth_error prog n) as [pi1|] eqn:Hpi1;
      [| rewrite map_nth_error_none in Heqpi; congruence].
    erewrite map_nth_error in Heqpi; eauto.
    inversion Heqpi; subst pi; clear Heqpi.
    pose proof Hscanp as Hscanp_lex.
    rewrite Hcompat with (pi := pi1) in Hscanp; auto.
    reflect; destruct Hscanp as [Heqp Hscan].
    refine
      (@PolyProgress
         (scan_dim - d) to_scan prog mem3 mem4 mem5 wcs rcs pi1 n
         (resize es p ++ skipn (d + es)%nat p)
         _ _ _ _ _).
    + exact Hscan.
    + exact Hpi1.
    + intros n2 p2 pi2 Heqpi2 Hcmp.
      specialize
        (Hts n2
           (resize es p2 ++ resize d (affine_product pi2.(pi_schedule) p2) ++ skipn es p2)).
      rewrite Hcompat with (pi := pi2) in Hts; auto.
      rewrite resize_skipn_eq in Hts.
      rewrite resize_eq in Hts by (unfold affine_product; rewrite map_length; eauto).
      simpl in Hts.
      destruct (to_scan n2 p2) eqn:Hscan2; auto.
      apply Hts.
      rewrite <- split3_eq with (l := p) (d := d) (i := es).
      rewrite !lex_compare_app by (rewrite !resize_length; reflexivity).
      rewrite Hscanenv with (p := resize es p2) by (apply resize_length || rewrite resize_skipn_eq; apply Hscan2).
      rewrite Hscanenv with (p := resize es p) by (apply resize_length || apply Hscan).
      rewrite lex_compare_reflexive. simpl.
      rewrite Heqp.
      rewrite resize_eq by (unfold affine_product; rewrite map_length; eauto).
      rewrite Hcmp.
      reflexivity.
    + simpl in Hsem1.
      replace scan_dim with ((scan_dim - d) + d)%nat in Hsem1 by lia.
      rewrite
        (current_src_args_in_dim_pi_elim_schedule_resize
           d es (scan_dim - d) pi1 p)
        in Hsem1.
      rewrite (Henvdim n pi1 Hpi1) in Hsem1.
      apply Hsem1.
    + apply IH; auto.
      * apply scanned_wf_compat; auto.
      * apply scanned_wf_compat; auto.
      * intros n0 p0 q0 ts pi0 Hpi0 Hlp0 Hlts.
        unfold scanned.
        rewrite Hcompat with (pi := pi0); auto.
        destruct (is_eq ts (affine_product (pi_schedule pi0) (p0 ++ q0))) eqn:Htseq; auto.
        simpl.
        f_equal; f_equal.
        destruct (n =? n0)%nat eqn:Heqn; [|rewrite !andb_false_r; auto].
        rewrite !andb_true_r.
        rewrite <- split3_eq with (l := p) (d := d) (i := es) at 1.
        rewrite !is_eq_app by (rewrite resize_length; auto).
        destruct (is_eq (resize es p) p0) eqn:Heqp0; simpl; auto.
        destruct (is_eq (skipn (d + es)%nat p) q0) eqn:Heqq0; simpl; auto using andb_false_r.
        rewrite andb_true_r.
        reflect.
        rewrite Heqn in *.
        assert (Heqpi0 : pi0 = pi1) by congruence.
        subst pi0.
        rewrite Heqp.
        rewrite Htseq.
        f_equal.
        assert (Hveq : p0 ++ q0 =v= resize es p ++ skipn (d + es) p).
        {
          rewrite <- is_eq_veq.
          rewrite is_eq_app by (rewrite resize_length; auto).
          reflect; split; symmetry; assumption.
        }
        rewrite Hveq.
        reflexivity.
      * intros n0 p0 q0 Hlp0 Hscan0.
        unfold scanned in Hscan0.
        apply andb_prop in Hscan0 as [Hscan0 _].
        eapply Hscanenv; eauto.
      * intros n0 p0 Hnone.
        unfold scanned.
        rewrite Hout; auto.
Qed.

Local Lemma env_scan_elim_schedule_point :
  forall d env dim prog n p q ts pi,
    nth_error prog n = Some pi ->
    (length pi.(pi_schedule) <= d)%nat ->
    (length env <= dim)%nat ->
    length p = length env ->
    length ts = d ->
    env_scan (elim_schedule d (length env) prog) env (dim + d)
      n (p ++ ts ++ q) =
    is_eq ts (affine_product pi.(pi_schedule) (p ++ q)) &&
      env_scan prog env dim n (p ++ q).
Proof.
  intros d env dim prog n p q ts pi Heqpi Hschedule Henvdim Hlp Hlts.
  unfold env_scan, elim_schedule.
  rewrite map_nth_error with (d := pi); auto.
  rewrite Heqpi.
  unfold pi_elim_schedule; simpl.
  rewrite !resize_app with (n := length env) by apply Hlp.
  destruct (is_eq env p); simpl; auto using andb_false_r.
  rewrite in_poly_app.
  rewrite andb_comm, <- andb_assoc.
  f_equal.
  - apply make_sched_poly_correct; eauto.
  - rewrite andb_comm.
    f_equal.
    + rewrite !resize_app_le by lia.
      rewrite !is_eq_app by lia.
      rewrite !is_eq_reflexive.
      simpl.
      f_equal; f_equal; lia.
    + unfold in_poly.
      rewrite forallb_map.
      apply forallb_ext.
      intros c.
      unfold satisfies_constraint, insert_zeros_constraint.
      simpl.
      f_equal.
      rewrite dot_product_commutative.
      rewrite insert_zeros_product_skipn.
      rewrite resize_app by apply Hlp.
      rewrite app_assoc, skipn_app, app_length, <- Hlp, <- Hlts.
      rewrite dot_product_commutative, skipn_app.
      rewrite skipn_all2; try lia.
      simpl.
      rewrite skipn_all2; try lia.
      simpl.
      replace
        (length ts + length p - (length p + length ts))%nat
        with 0%nat by lia.
      rewrite skipn_O.
      reflexivity.
Qed.

Local Lemma env_scan_true_prefix :
  forall prog env dim n p q,
    length p = length env ->
    env_scan prog env dim n (p ++ q) = true ->
    p =v= env.
Proof.
  intros prog env dim n p q Hlp Hscan.
  unfold env_scan in Hscan.
  destruct (nth_error prog n) as [pi|]; [|discriminate].
  reflect.
  destruct Hscan as [[Henv _] _].
  rewrite resize_app in Henv by congruence.
  symmetry; exact Henv.
Qed.

Local Lemma env_scan_nth_error_none :
  forall prog env dim n p,
    nth_error prog n = None ->
    env_scan prog env dim n p = false.
Proof.
  intros prog env dim n p Hnone.
  unfold env_scan.
  rewrite Hnone.
  reflexivity.
Qed.

Theorem poly_elim_schedule_semantics_env_preserve :
  forall d es env dim prog mem1 mem2,
    es = length env ->
    (es <= dim)%nat ->
    env_poly_lex_semantics env (dim + d) (elim_schedule d es prog) mem1 mem2 ->
    (forall n pi, nth_error prog n = Some pi -> (length pi.(pi_schedule) <= d)%nat) ->
    (forall n pi, nth_error prog n = Some pi ->
         current_env_dim_in_dim dim pi.(pi_point_witness) = es) ->
    env_poly_semantics env dim prog mem1 mem2.
Proof.
  intros d es env dim prog mem1 mem2 Hlength Hdim Hsem Hsched_length Henvdim.
  subst es.
  unfold env_poly_semantics.
  unfold env_poly_lex_semantics in Hsem.
  replace dim with (dim + d - d)%nat by lia.
  eapply (poly_elim_schedule_semantics_preserve
            d (length env) (dim + d) env
            (env_scan (elim_schedule d (length env) prog) env (dim + d))
            (elim_schedule d (length env) prog) mem1 mem2); simpl.
  - lia.
  - exact Hsem.
  - reflexivity.
  - apply env_scan_proper.
  - apply env_scan_proper.
  - exact Hsched_length.
  - intros n pi Hpi.
    replace (dim + d - d)%nat with dim by lia.
    exact (Henvdim n pi Hpi).
  - intros n p q ts pi Heqpi Hlp Hlts.
    replace (dim + d - d)%nat with dim by lia.
    eapply env_scan_elim_schedule_point; eauto.
  - intros n p q Hlp Hscanp.
    eapply env_scan_true_prefix; eauto.
  - intros n p Hnone.
    eapply env_scan_nth_error_none; eauto.
Qed.

Definition elim_schedule_prog (pprog: t): t := 
    let '(pis, varctxt, vars) := pprog in 
    let pis' := elim_schedule (pprog_current_dim pprog) (length varctxt) pis in 
    (pis', varctxt, vars).

End PolyLang.

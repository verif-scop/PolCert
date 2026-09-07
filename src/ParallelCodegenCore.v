Require Import List.
Require Import ZArith.
Require Import Lia.
Require Import Misc.
Require Import Linalg.
Require Import Result.
Require Import String.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.
Require Import PolIRs.
Require Import PolyBase.
Require Import PrepareCodegen.
Require Import RawCodegenOrigin.
Require Import ParallelLoop.
Require Import ParallelValidator.

Import ListNotations.

Module ParallelCodegenCore (PolIRs : POLIRS).

Module Instr := PolIRs.Instr.
Module PolyLang := PolIRs.PolyLang.
Module Loop := PolIRs.Loop.
Module PrepareCore := PrepareCodegen PolIRs.
Module RawOrigin := RawCodegenOrigin PolIRs.
Module ParallelLoop := ParallelLoop Instr.
Module ParallelValidator := ParallelValidator PolIRs.

Definition parallel_codegen_cert_sound
    (pp : PolyLang.t) (cert : ParallelValidator.parallel_cert) : Prop :=
  ParallelValidator.parallel_cert_pointwise_sound pp cert /\
  (cert.(ParallelValidator.certified_dim) <
   ParallelValidator.schedule_width pp)%nat.

(** * Proof map

    The parallel proof has four stages.  First, standard code generation emits
    a sequential loop nest whose origin tags identify the padded schedule
    coordinates.  Second, the trace-origin lemmas below map every instruction
    in an actual annotated execution back to a source polyhedral instance.
    Third, each accepted certificate proves that points from distinct
    iterations of its tagged loop commute; the concrete execution therefore
    admits an [ordered_semantics] derivation.  Finally, erasure serializes that
    ordered execution and [PrepareCodegen] relates it to the polyhedral source.

    The checked endpoint tries metadata-preserving simplification, structural
    cleanup, and sequential-singleton elimination first.  It falls back to the
    standard raw loop unless every representation required by the reflection
    proof has affine instruction traces.  Cleanup correctness reflects the
    chosen execution to the certified pre-clean loop, so origin tags need not
    be reconstructed after a loop disappears.  Multi-dimensional
    parallelization uses the same argument with one owning certificate per
    parallel tag.  Vectorization follows a separate structural proof: it
    introduces no parallel interleaving and also checks that vector annotations
    are innermost. *)

(** Generated and source instruction points belong to distinct functor
    instances.  Equality of their records is neither available nor needed;
    parallel safety only depends on their observable instruction semantics. *)
Definition point_sema_equiv
    (generated : ParallelLoop.InstrPoint)
    (source : PolyLang.InstrPoint) : Prop :=
  forall st1 st2,
    ParallelLoop.ILSema.instr_point_sema generated st1 st2 <->
    PolyLang.ILSema.instr_point_sema source st1 st2.

Lemma permutable_of_point_sema_equiv :
  forall generated1 source1 generated2 source2,
    point_sema_equiv generated1 source1 ->
    point_sema_equiv generated2 source2 ->
    PolyLang.ILSema.Permutable source1 source2 ->
    ParallelLoop.ILSema.Permutable generated1 generated2.
Proof.
  intros generated1 source1 generated2 source2 Hequiv1 Hequiv2 Hperm
    st1 Hnonalias.
  specialize (Hperm st1 Hnonalias).
  destruct Hperm as [Hforward Hbackward].
  split.
  - intros st2 st3 Hstep1 Hstep2.
    apply (proj1 (Hequiv1 st1 st2)) in Hstep1.
    apply (proj1 (Hequiv2 st2 st3)) in Hstep2.
    destruct (Hforward st2 st3 Hstep1 Hstep2)
      as [st2' [st3' [Hstep2' [Hstep1' Heq]]]].
    exists st2', st3'.
    repeat split; auto.
    + apply (proj2 (Hequiv2 st1 st2')). exact Hstep2'.
    + apply (proj2 (Hequiv1 st2' st3')). exact Hstep1'.
  - intros st2 st3 Hstep2 Hstep1.
    apply (proj1 (Hequiv2 st1 st2)) in Hstep2.
    apply (proj1 (Hequiv1 st2 st3)) in Hstep1.
    destruct (Hbackward st2 st3 Hstep2 Hstep1)
      as [st2' [st3' [Hstep1' [Hstep2' Heq]]]].
    exists st2', st3'.
    repeat split; auto.
    + apply (proj2 (Hequiv1 st1 st2')). exact Hstep1'.
    + apply (proj2 (Hequiv2 st2' st3')). exact Hstep2'.
Qed.

Definition generated_source_point
    (pp : PolyLang.t)
    (generated : ParallelLoop.InstrPoint)
    (source : PolyLang.InstrPoint) : Prop :=
  point_sema_equiv generated source /\
  exists pi,
    nth_error (ParallelValidator.pprog_pis pp)
      source.(PolyLang.ip_nth) = Some pi /\
    PolyLang.belongs_to source pi /\
    Datatypes.length source.(PolyLang.ip_index) =
      (Datatypes.length (ParallelValidator.pprog_varctxt pp) +
       pi.(PolyLang.pi_depth))%nat.

(** The raw interleaving relation consumes every point from every family
    member.  This is the direction needed to lift membership from a child
    trace into the actual interleaved parent trace. *)
Lemma interleave_family_concat_member_in_output :
  forall trs out ip,
    ParallelLoop.interleave_family trs out ->
    In ip (List.concat trs) ->
    In ip out.
Proof.
  intros trs out ip Hinter.
  induction Hinter as
      [|trs out Hinter IH
       |pre x xs post out Hinter IH]; intro Hin.
  - exact Hin.
  - simpl in Hin. eapply IH. exact Hin.
  - simpl.
    apply in_concat in Hin.
    destruct Hin as [tr [Htr Hin]].
    apply in_app_or in Htr.
    destruct Htr as [Hpre | Hrest].
    + right. apply IH. apply in_concat.
      exists tr. split.
      * apply in_or_app. left. exact Hpre.
      * exact Hin.
    + simpl in Hrest.
      destruct Hrest as [Heq | Hpost].
      * subst tr. simpl in Hin.
        destruct Hin as [-> | Hin].
        -- left. reflexivity.
        -- right. apply IH. apply in_concat.
           exists xs. split.
           ++ apply in_or_app. right. simpl. auto.
           ++ exact Hin.
      * right. apply IH. apply in_concat.
        exists tr. split.
        -- apply in_or_app. right. simpl. right. exact Hpost.
        -- exact Hin.
Qed.

Definition point_has_effect
    (ip : ParallelLoop.InstrPoint)
    (i : PolIRs.Instr.t)
    (args : list Z) : Prop :=
  forall st1 st2,
    ParallelLoop.ILSema.instr_point_sema ip st1 st2 <->
    exists wcs rcs,
      PolIRs.Instr.instr_semantics i args wcs rcs st1 st2.

Definition point_matches_event
    (ip : ParallelLoop.InstrPoint) (ev : RawOrigin.scan_event) : Prop :=
  ev.(RawOrigin.se_point) = rev ip.(ParallelLoop.ILSema.ip_index) /\
  point_has_effect ip ev.(RawOrigin.se_instr) ev.(RawOrigin.se_args).

Record generated_source_point_full
    (pp : PolyLang.t) (width : nat)
    (generated : ParallelLoop.InstrPoint)
    (source : PolyLang.InstrPoint) : Prop := {
  gspf_basic : generated_source_point pp generated source;
  gspf_env_prefix :
    firstn (Datatypes.length (ParallelValidator.pprog_varctxt pp))
      source.(PolyLang.ip_index) =
    resize (Datatypes.length (ParallelValidator.pprog_varctxt pp))
      (rev generated.(ParallelLoop.ILSema.ip_index));
  gspf_schedule_coordinates :
    resize width (skipn
      (Datatypes.length (ParallelValidator.pprog_varctxt pp))
      (rev generated.(ParallelLoop.ILSema.ip_index))) =
    resize width source.(PolyLang.ip_time_stamp)
}.

Lemma prepare_source_args_eq :
  forall pis varctxt vars cols m pi p,
    PolyLang.wf_pprog_affine (pis, varctxt, vars) ->
    (PolyLang.pprog_current_dim (pis, varctxt, vars) <= cols)%nat ->
    nth_error pis m = Some pi ->
    p =v= resize cols p ->
    PolyLang.current_src_args_in_dim cols
      (PrepareCore.prepare_pi (Datatypes.length varctxt) cols pi) p =
    affine_product
      (PolyLang.current_transformation_of pi
        (resize (Datatypes.length varctxt + pi.(PolyLang.pi_depth)) p))
      (resize (Datatypes.length varctxt + pi.(PolyLang.pi_depth)) p).
Proof.
  intros pis varctxt vars cols m pi p Hwf Hdim Hnth Hp.
  pose proof Hwf as Hwf_all.
  pose proof (nth_error_In _ _ Hnth) as Hpi_in.
  unfold PolyLang.wf_pprog_affine in Hwf.
  destruct Hwf as [_ Hwfpis].
  pose proof (Hwfpis pi Hpi_in) as Hwfpi.
  unfold PolyLang.wf_pinstr_affine in Hwfpi.
  destruct Hwfpi as [Hwfpi [Hwit_eq _]].
  unfold PolyLang.wf_pinstr in Hwfpi.
  destruct Hwfpi as
    [_ [_ [_ [_ [_ [Htf_exact [_ [_ [_ _]]]]]]]]].
  rewrite Hwit_eq in Htf_exact.
  simpl in Htf_exact.
  pose proof
    (PrepareCore.wf_pprog_affine_implies_source_cols_le
      pis varctxt vars cols pi Hwf_all Hdim Hpi_in) as Hcols.
  rewrite PrepareCore.prepare_pi_current_src_args_in_dim_affine.
  2: exact Hcols.
  2: exact Hwit_eq.
  2: exact Hp.
  rewrite
    (PrepareCore.prepare_pi_transformation_eval
      (Datatypes.length varctxt) cols pi p Htf_exact Hcols).
  assert (Htf_current :
    PolyLang.current_transformation_of pi
      (resize (Datatypes.length varctxt + pi.(PolyLang.pi_depth)) p) =
    pi.(PolyLang.pi_transformation)).
  {
    unfold PolyLang.current_transformation_of,
      PolyLang.current_transformation_at,
      PolyLang.current_env_dim_of.
    rewrite Hwit_eq.
    simpl.
    replace
      (Datatypes.length varctxt + pi.(PolyLang.pi_depth) -
       pi.(PolyLang.pi_depth))%nat
      with (Datatypes.length varctxt) by lia.
    reflexivity.
  }
  rewrite Htf_current.
  reflexivity.
Qed.

Lemma point_sema_equiv_of_prepared_effect :
  forall pis varctxt vars cols m pi p ip,
    PolyLang.wf_pprog_affine (pis, varctxt, vars) ->
    (PolyLang.pprog_current_dim (pis, varctxt, vars) <= cols)%nat ->
    nth_error pis m = Some pi ->
    p =v= resize cols p ->
    point_has_effect ip
      (PrepareCore.prepare_pi
        (Datatypes.length varctxt) cols pi).(PolyLang.pi_instr)
      (PolyLang.current_src_args_in_dim cols
        (PrepareCore.prepare_pi (Datatypes.length varctxt) cols pi) p) ->
    point_sema_equiv ip
      (PrepareCore.source_ip_of
        (Datatypes.length varctxt) m pi p).
Proof.
  intros pis varctxt vars cols m pi p ip Hwf Hdim Hnth Hp Heffect.
  pose proof
    (prepare_source_args_eq
      pis varctxt vars cols m pi p Hwf Hdim Hnth Hp) as Hargs.
  unfold point_sema_equiv, point_has_effect in *.
  intros st1 st2.
  specialize (Heffect st1 st2).
  split.
  - intro Hgenerated.
    apply Heffect in Hgenerated.
    destruct Hgenerated as [wcs [rcs Hstep]].
    econstructor.
    unfold PrepareCore.source_ip_of. simpl.
    simpl in Hstep.
    rewrite <- Hargs.
    exact Hstep.
  - intro Hsource.
    apply Heffect.
    inversion Hsource as [wcs rcs Hstep]; subst.
    exists wcs, rcs.
    unfold PrepareCore.source_ip_of in Hstep. simpl in Hstep.
    simpl.
    rewrite Hargs.
    exact Hstep.
Qed.

(** Convert the neutral RawCodegenOrigin endpoint back to an instruction point
    of the unprepared source program. *)
Theorem prepared_event_to_source_point :
  forall pis varctxt vars cols width ip ev,
    PolyLang.wf_pprog_affine (pis, varctxt, vars) ->
    (PolyLang.pprog_current_dim (pis, varctxt, vars) <= cols)%nat ->
    point_matches_event ip ev ->
    RawOrigin.prepared_source_event
      (map (PrepareCore.prepare_pi (Datatypes.length varctxt) cols) pis)
      (Datatypes.length varctxt) cols width ev ->
    exists source_ip,
      generated_source_point_full
        ((pis, varctxt), vars) width ip source_ip.
Proof.
  intros pis varctxt vars cols width ip ev Hwf Hdim Hmatch Hprepared.
  (* Recover the original instruction and current point hidden by [prepare_pi]
     and schedule elimination. *)
  destruct Hmatch as [Hevent_point Heffect].
  destruct Hprepared as
    [m [prep_pi
      [Hprep_lookup
       [Hp_len
        [Hprep_domain
         [Hevent_instr
          [Hevent_args [Henv_prefix Hschedule]]]]]]]].
  rewrite nth_error_map_iff in Hprep_lookup.
  destruct Hprep_lookup as [pi [Hpi Hprep_pi]].
  subst prep_pi.
  set (env_dim := Datatypes.length varctxt).
  set (p := RawOrigin.drop_schedule_coords env_dim width
    ev.(RawOrigin.se_point)).
  assert (Henv_cols : (env_dim <= cols)%nat).
  {
    pose proof
      (PolyLang.pprog_current_dim_ge_pinstr
        pis varctxt vars pi (nth_error_In _ _ Hpi)) as Hpi_dim.
    unfold PolyLang.pinstr_current_dim in Hpi_dim.
    unfold env_dim.
    lia.
  }
  assert (Hp_resize : p =v= resize cols p).
  {
    rewrite resize_length_eq by exact Hp_len.
    reflexivity.
  }
  set (envv := resize env_dim p).
  assert (Henvv_len : Datatypes.length envv = Datatypes.length varctxt).
  {
    unfold envv, env_dim. rewrite resize_length. reflexivity.
  }
  assert (Hscan :
    PolyLang.env_scan
      (map (PrepareCore.prepare_pi (Datatypes.length varctxt) cols) pis)
      envv cols m p = true).
  {
    unfold PolyLang.env_scan.
    rewrite map_nth_error with (d := pi); [|exact Hpi].
    simpl.
    apply andb_true_intro. split.
    - apply andb_true_intro. split.
      + unfold envv, env_dim. rewrite resize_length. apply is_eq_reflexive.
      + rewrite is_eq_veq. exact Hp_resize.
    - exact Hprep_domain.
  }
  (* Preparation's scan theorem supplies source membership, depth, and the
     environment prefix. *)
  pose proof
    (PrepareCore.prepare_env_scan_true_implies_source_ip_props
      pis varctxt vars cols envv m p pi Hwf Hdim Henvv_len Hpi Hscan)
    as Hprops.
  change (
    firstn (Datatypes.length varctxt)
      (PrepareCore.source_ip_of
        (Datatypes.length varctxt) m pi p).(PolyLang.ip_index) = envv /\
    PolyLang.belongs_to
      (PrepareCore.source_ip_of
        (Datatypes.length varctxt) m pi p) pi /\
    Datatypes.length
      (PrepareCore.source_ip_of
        (Datatypes.length varctxt) m pi p).(PolyLang.ip_index) =
      (Datatypes.length varctxt + pi.(PolyLang.pi_depth))%nat /\
    is_eq p (resize cols p) = true /\
    is_null
      (skipn (Datatypes.length varctxt + pi.(PolyLang.pi_depth))
        (resize cols p)) = true) in Hprops.
  destruct Hprops as [Hprefix [Hbelongs [Hsource_len [_ _]]]].
  set (source_ip :=
    PrepareCore.source_ip_of (Datatypes.length varctxt) m pi p).
  exists source_ip.
  (* Package semantic equivalence, the source witness, and both coordinate
     correspondences needed by the parallel certificate proof. *)
  constructor.
  - split.
    + subst source_ip.
      eapply point_sema_equiv_of_prepared_effect; eauto.
      unfold point_has_effect in *.
      intros st1 st2.
      specialize (Heffect st1 st2).
      change
        (ev.(RawOrigin.se_args) =
         PolyLang.current_src_args_in_dim cols
           (PrepareCore.prepare_pi
             (Datatypes.length varctxt) cols pi) p)
        in Hevent_args.
      rewrite <- Hevent_instr, <- Hevent_args.
      exact Heffect.
    + exists pi.
      subst source_ip. simpl.
      split; [exact Hpi|].
      split; assumption.
  - subst source_ip.
    transitivity envv.
    + exact Hprefix.
    + unfold envv, p, env_dim, RawOrigin.drop_schedule_coords.
      rewrite resize_app.
      * rewrite Hevent_point. reflexivity.
      * rewrite resize_length. reflexivity.
  - subst source_ip.
    transitivity
      (resize width
        (affine_product
          (PrepareCore.prepare_pi
            (Datatypes.length varctxt) cols pi).(PolyLang.pi_schedule) p)).
    + rewrite <- Hevent_point.
      exact Hschedule.
    + rewrite <- PrepareCore.source_ip_of_timestamp_prepare
        with (pis := pis) (varctxt := varctxt) (vars := vars)
             (cols := cols) (n := m) (pi := pi) (p := p); eauto.
Qed.

Fixpoint tag_expr (e : Loop.expr) : ParallelLoop.expr :=
  match e with
  | Loop.Constant z => ParallelLoop.BaseLoop.Constant z
  | Loop.Sum e1 e2 => ParallelLoop.BaseLoop.Sum (tag_expr e1) (tag_expr e2)
  | Loop.Mult z e1 => ParallelLoop.BaseLoop.Mult z (tag_expr e1)
  | Loop.Div e1 z => ParallelLoop.BaseLoop.Div (tag_expr e1) z
  | Loop.Mod e1 z => ParallelLoop.BaseLoop.Mod (tag_expr e1) z
  | Loop.Var n => ParallelLoop.BaseLoop.Var n
  | Loop.Max e1 e2 => ParallelLoop.BaseLoop.Max (tag_expr e1) (tag_expr e2)
  | Loop.Min e1 e2 => ParallelLoop.BaseLoop.Min (tag_expr e1) (tag_expr e2)
  end.

Fixpoint tag_test (t : Loop.test) : ParallelLoop.test :=
  match t with
  | Loop.LE e1 e2 => ParallelLoop.BaseLoop.LE (tag_expr e1) (tag_expr e2)
  | Loop.EQ e1 e2 => ParallelLoop.BaseLoop.EQ (tag_expr e1) (tag_expr e2)
  | Loop.And t1 t2 => ParallelLoop.BaseLoop.And (tag_test t1) (tag_test t2)
  | Loop.Or t1 t2 => ParallelLoop.BaseLoop.Or (tag_test t1) (tag_test t2)
  | Loop.Not t1 => ParallelLoop.BaseLoop.Not (tag_test t1)
  | Loop.TConstantTest b => ParallelLoop.BaseLoop.TConstantTest b
  end.

Fixpoint erase_expr (e : ParallelLoop.expr) : Loop.expr :=
  match e with
  | ParallelLoop.BaseLoop.Constant z => Loop.Constant z
  | ParallelLoop.BaseLoop.Sum e1 e2 => Loop.Sum (erase_expr e1) (erase_expr e2)
  | ParallelLoop.BaseLoop.Mult z e1 => Loop.Mult z (erase_expr e1)
  | ParallelLoop.BaseLoop.Div e1 z => Loop.Div (erase_expr e1) z
  | ParallelLoop.BaseLoop.Mod e1 z => Loop.Mod (erase_expr e1) z
  | ParallelLoop.BaseLoop.Var n => Loop.Var n
  | ParallelLoop.BaseLoop.Max e1 e2 => Loop.Max (erase_expr e1) (erase_expr e2)
  | ParallelLoop.BaseLoop.Min e1 e2 => Loop.Min (erase_expr e1) (erase_expr e2)
  end.

Fixpoint erase_test (t : ParallelLoop.test) : Loop.test :=
  match t with
  | ParallelLoop.BaseLoop.LE e1 e2 => Loop.LE (erase_expr e1) (erase_expr e2)
  | ParallelLoop.BaseLoop.EQ e1 e2 => Loop.EQ (erase_expr e1) (erase_expr e2)
  | ParallelLoop.BaseLoop.And t1 t2 => Loop.And (erase_test t1) (erase_test t2)
  | ParallelLoop.BaseLoop.Or t1 t2 => Loop.Or (erase_test t1) (erase_test t2)
  | ParallelLoop.BaseLoop.Not t1 => Loop.Not (erase_test t1)
  | ParallelLoop.BaseLoop.TConstantTest b => Loop.TConstantTest b
  end.

(** * Tagging, erasure, and sequential trace transport *)

Lemma erase_tag_expr_eq :
  forall e,
    erase_expr (tag_expr e) = e.
Proof.
  induction e; simpl; try rewrite ?IHe, ?IHe1, ?IHe2; reflexivity.
Qed.

Lemma erase_tag_test_eq :
  forall t,
    erase_test (tag_test t) = t.
Proof.
  induction t; simpl; try rewrite ?IHt, ?IHt1, ?IHt2; try rewrite ?erase_tag_expr_eq; reflexivity.
Qed.

Lemma map_erase_tag_expr_eq :
  forall es,
    List.map erase_expr (List.map tag_expr es) = es.
Proof.
  induction es as [|e es IH]; simpl.
  - reflexivity.
  - rewrite erase_tag_expr_eq, IH. reflexivity.
Qed.

Fixpoint tag_loop_stmt_at (d : nat) (s : Loop.stmt) {struct s} : ParallelLoop.stmt
with tag_loop_stmts_at (d : nat) (ss : Loop.stmt_list) {struct ss} : ParallelLoop.stmt_list.
Proof.
  - destruct s; simpl.
    + exact (ParallelLoop.Loop ParallelLoop.SeqMode (Some d) (tag_expr e) (tag_expr e0) (tag_loop_stmt_at (S d) s)).
    + exact (ParallelLoop.Instr i (List.map tag_expr l)).
    + exact (ParallelLoop.Seq (tag_loop_stmts_at d s)).
    + exact (ParallelLoop.Guard (tag_test t) (tag_loop_stmt_at d s)).
  - destruct ss; simpl.
    + exact ParallelLoop.SNil.
    + exact (ParallelLoop.SCons (tag_loop_stmt_at d s) (tag_loop_stmts_at d ss)).
Defined.

Definition tag_loop (p : Loop.t) : ParallelLoop.t :=
  match p with
  | ((s, ctxt), vars) => (tag_loop_stmt_at 0 s, ctxt, vars)
  end.

Fixpoint erase_to_loop_stmt (s : ParallelLoop.stmt) {struct s} : Loop.stmt
with erase_to_loop_stmts (ss : ParallelLoop.stmt_list) {struct ss} : Loop.stmt_list.
Proof.
  - destruct s; simpl.
    + exact (Loop.Loop (erase_expr e) (erase_expr e0) (erase_to_loop_stmt s)).
    + exact (Loop.Instr i (List.map erase_expr l)).
    + exact (Loop.Seq (erase_to_loop_stmts s)).
    + exact (Loop.Guard (erase_test t) (erase_to_loop_stmt s)).
  - destruct ss; simpl.
    + exact Loop.SNil.
    + exact (Loop.SCons (erase_to_loop_stmt s) (erase_to_loop_stmts ss)).
Defined.

Definition erase_to_loop (p : ParallelLoop.t) : Loop.t :=
  match p with
  | ((s, ctxt), vars) => (erase_to_loop_stmt s, ctxt, vars)
  end.

Fixpoint tagged_from_depth_stmt (d : nat) (s : ParallelLoop.stmt) : Prop
with tagged_from_depth_stmts (d : nat) (ss : ParallelLoop.stmt_list) : Prop.
Proof.
  - destruct s; simpl.
    + exact (o = Some d /\ tagged_from_depth_stmt (S d) s).
    + exact True.
    + exact (tagged_from_depth_stmts d s).
    + exact (tagged_from_depth_stmt d s).
  - destruct ss; simpl.
    + exact True.
    + exact (tagged_from_depth_stmt d s /\ tagged_from_depth_stmts d ss).
Defined.

Definition tagged_from_top (p : ParallelLoop.t) : Prop :=
  match p with
  | ((s, _), _) => tagged_from_depth_stmt 0 s
  end.

Fixpoint tag_loop_stmt_tagged_from_depth
  (d : nat) (s : Loop.stmt) {struct s}
  : tagged_from_depth_stmt d (tag_loop_stmt_at d s)
with tag_loop_stmts_tagged_from_depth
  (d : nat) (ss : Loop.stmt_list) {struct ss}
  : tagged_from_depth_stmts d (tag_loop_stmts_at d ss).
Proof.
  - destruct s; simpl.
    + split; auto.
    + auto.
    + apply tag_loop_stmts_tagged_from_depth.
    + apply tag_loop_stmt_tagged_from_depth.
  - destruct ss; simpl.
    + auto.
    + split.
      * apply tag_loop_stmt_tagged_from_depth.
      * apply tag_loop_stmts_tagged_from_depth.
Qed.

(** Vector annotation never introduces a parallel loop.  Consequently the
    external ordering invariant required by parallel semantics is structural
    for every tagged vector program. *)
Lemma vectorize_tag_loop_stmt_ordered :
  forall target depth s,
    ParallelLoop.parallel_families_ordered_stmt
      (ParallelLoop.vectorize_dim_stmt target (tag_loop_stmt_at depth s))
with vectorize_tag_loop_stmts_ordered :
  forall target depth ss,
    ParallelLoop.parallel_families_ordered_stmts
      (ParallelLoop.vectorize_dim_stmts target (tag_loop_stmts_at depth ss)).
Proof.
  - intros target depth s.
    destruct s; simpl.
    + destruct (Nat.eqb target depth); simpl;
        eapply vectorize_tag_loop_stmt_ordered.
    + exact I.
    + eapply vectorize_tag_loop_stmts_ordered.
    + eapply vectorize_tag_loop_stmt_ordered.
  - intros target depth ss.
    destruct ss; simpl.
    + exact I.
    + split.
      * eapply vectorize_tag_loop_stmt_ordered.
      * eapply vectorize_tag_loop_stmts_ordered.
Qed.

Lemma tag_loop_stmt_ordered :
  forall depth s,
    ParallelLoop.parallel_families_ordered_stmt
      (tag_loop_stmt_at depth s)
with tag_loop_stmts_ordered :
  forall depth ss,
    ParallelLoop.parallel_families_ordered_stmts
      (tag_loop_stmts_at depth ss).
Proof.
  - intros depth s. destruct s; simpl.
    + eapply tag_loop_stmt_ordered.
    + exact I.
    + eapply tag_loop_stmts_ordered.
    + eapply tag_loop_stmt_ordered.
  - intros depth ss. destruct ss; simpl.
    + exact I.
    + split.
      * eapply tag_loop_stmt_ordered.
      * eapply tag_loop_stmts_ordered.
Qed.

Lemma tag_loop_ordered :
  forall loop,
    ParallelLoop.parallel_families_ordered (tag_loop loop).
Proof.
  intros [[s ctxt] vars]. simpl.
  eapply tag_loop_stmt_ordered.
Qed.

Fixpoint erase_parallelize_dim_stmt_to_loop_eq
  (d : nat) (s : ParallelLoop.stmt) {struct s}
  : erase_to_loop_stmt (ParallelLoop.parallelize_dim_stmt d s) = erase_to_loop_stmt s
with erase_parallelize_dim_stmts_to_loop_eq
  (d : nat) (ss : ParallelLoop.stmt_list) {struct ss}
  : erase_to_loop_stmts (ParallelLoop.parallelize_dim_stmts d ss) = erase_to_loop_stmts ss.
Proof.
  - destruct s; simpl.
    + destruct l; destruct o as [n|]; simpl; rewrite erase_parallelize_dim_stmt_to_loop_eq; reflexivity.
    + reflexivity.
    + rewrite erase_parallelize_dim_stmts_to_loop_eq. reflexivity.
    + rewrite erase_parallelize_dim_stmt_to_loop_eq. reflexivity.
  - destruct ss; simpl.
    + reflexivity.
    + rewrite erase_parallelize_dim_stmt_to_loop_eq, erase_parallelize_dim_stmts_to_loop_eq.
      reflexivity.
Qed.

Lemma erase_parallelize_dim_to_loop_eq :
  forall d p,
    erase_to_loop (ParallelLoop.parallelize_dim d p) = erase_to_loop p.
Proof.
  intros d [[s ctxt] vars]; simpl.
  rewrite erase_parallelize_dim_stmt_to_loop_eq.
  reflexivity.
Qed.

Fixpoint erase_vectorize_dim_stmt_to_loop_eq
  (d : nat) (s : ParallelLoop.stmt) {struct s}
  : erase_to_loop_stmt (ParallelLoop.vectorize_dim_stmt d s) = erase_to_loop_stmt s
with erase_vectorize_dim_stmts_to_loop_eq
  (d : nat) (ss : ParallelLoop.stmt_list) {struct ss}
  : erase_to_loop_stmts (ParallelLoop.vectorize_dim_stmts d ss) = erase_to_loop_stmts ss.
Proof.
  - destruct s; simpl.
    + destruct l; destruct o as [n|]; simpl; rewrite erase_vectorize_dim_stmt_to_loop_eq; reflexivity.
    + reflexivity.
    + rewrite erase_vectorize_dim_stmts_to_loop_eq. reflexivity.
    + rewrite erase_vectorize_dim_stmt_to_loop_eq. reflexivity.
  - destruct ss; simpl.
    + reflexivity.
    + rewrite erase_vectorize_dim_stmt_to_loop_eq, erase_vectorize_dim_stmts_to_loop_eq.
      reflexivity.
Qed.

Lemma erase_vectorize_dim_to_loop_eq :
  forall d p,
    erase_to_loop (ParallelLoop.vectorize_dim d p) = erase_to_loop p.
Proof.
  intros d [[s ctxt] vars]; simpl.
  rewrite erase_vectorize_dim_stmt_to_loop_eq.
  reflexivity.
Qed.

Lemma erase_tag_loop_stmt_at_eq :
  forall d s,
    erase_to_loop_stmt (tag_loop_stmt_at d s) = s
with erase_tag_loop_stmts_at_eq :
  forall d ss,
    erase_to_loop_stmts (tag_loop_stmts_at d ss) = ss.
Proof.
  - intros d s. destruct s; simpl.
    + rewrite !erase_tag_expr_eq, erase_tag_loop_stmt_at_eq. reflexivity.
    + rewrite map_erase_tag_expr_eq. reflexivity.
    + rewrite erase_tag_loop_stmts_at_eq. reflexivity.
    + rewrite erase_tag_test_eq, erase_tag_loop_stmt_at_eq. reflexivity.
  - intros d ss. destruct ss; simpl.
    + reflexivity.
    + rewrite erase_tag_loop_stmt_at_eq, erase_tag_loop_stmts_at_eq. reflexivity.
Qed.

Lemma erase_tag_loop_eq :
  forall p,
    erase_to_loop (tag_loop p) = p.
Proof.
  intros [[s ctxt] vars]; simpl.
  rewrite erase_tag_loop_stmt_at_eq.
  reflexivity.
Qed.

Lemma erase_expr_eval_eq :
  forall env e,
    Loop.eval_expr env (erase_expr e) =
    ParallelLoop.BaseLoop.eval_expr env e.
Proof.
  induction e; simpl; try rewrite ?IHe, ?IHe1, ?IHe2; reflexivity.
Qed.

Lemma erase_expr_list_map_eval_eq :
  forall env es,
    List.map (Loop.eval_expr env) (List.map erase_expr es) =
    List.map (ParallelLoop.BaseLoop.eval_expr env) es.
Proof.
  induction es as [|e es IH]; simpl.
  - reflexivity.
  - rewrite erase_expr_eval_eq, IH. reflexivity.
Qed.

Lemma erase_test_eval_eq :
  forall env t,
    Loop.eval_test env (erase_test t) =
    ParallelLoop.BaseLoop.eval_test env t.
Proof.
  induction t; simpl; try rewrite ?IHt, ?IHt1, ?IHt2; try rewrite ?erase_expr_eval_eq; reflexivity.
Qed.

Lemma iter_semantics_refine_exact :
  forall A (P Q : A -> Instr.State.t -> Instr.State.t -> Prop),
    forall xs st1 st2,
      Instr.IterSem.iter_semantics P xs st1 st2 ->
      (forall x stA stB, In x xs -> P x stA stB -> Q x stA stB) ->
      Instr.IterSem.iter_semantics Q xs st1 st2.
Proof.
  intros A P Q xs st1 st2 Hiter.
  induction Hiter; intros Hstep.
  - constructor.
  - econstructor.
    + eapply Hstep; eauto.
      left; reflexivity.
    + eapply IHHiter.
      intros y stA stB Hin HP.
      eapply Hstep; eauto.
      right; exact Hin.
Qed.

Scheme pl_stmt_mutind := Induction for ParallelLoop.stmt Sort Prop
with pl_stmts_mutind := Induction for ParallelLoop.stmt_list Sort Prop.
Combined Scheme pl_stmt_stmts_mutind from pl_stmt_mutind, pl_stmts_mutind.

Lemma interleave_family_member_in_concat :
  forall trs tr ip,
    ParallelLoop.interleave_family trs tr ->
    In ip tr ->
    In ip (List.concat trs).
Proof.
  intros trs tr ip Hinter.
  induction Hinter; intro Hin.
  - contradiction.
  - simpl. eapply IHHinter. exact Hin.
  - simpl in Hin.
    destruct Hin as [<- | Hin].
    + apply in_concat.
      exists (x :: xs).
      split.
      * apply in_or_app. right. simpl. auto.
      * simpl. auto.
    + eapply ParallelLoop.concat_pop_in.
      eapply IHHinter. exact Hin.
Qed.

Lemma Forall2_in_right_local :
  forall A B (R : A -> B -> Prop) xs ys y,
    Forall2 R xs ys ->
    In y ys ->
    exists x, In x xs /\ R x y.
Proof.
  intros A B R xs ys y Hfor.
  induction Hfor; intro Hin.
  - contradiction.
  - simpl in Hin.
    destruct Hin as [<- | Hin].
    + exists x. split; [left; reflexivity|assumption].
    + destruct (IHHfor Hin) as [x' [Hin' HR]].
      exists x'. split; [right; exact Hin'|exact HR].
Qed.

Definition point_extends_stmt_goal (s : ParallelLoop.stmt) : Prop :=
  forall env tr ip,
    ParallelLoop.trace_safe_stmt s ->
    ParallelLoop.par_trace s env tr ->
    In ip tr ->
    exists suffix, ip.(ParallelLoop.ILSema.ip_index) = suffix ++ env.

Definition point_extends_stmts_goal (ss : ParallelLoop.stmt_list) : Prop :=
  forall env tr ip,
    ParallelLoop.trace_safe_stmts ss ->
    ParallelLoop.par_traces ss env tr ->
    In ip tr ->
    exists suffix, ip.(ParallelLoop.ILSema.ip_index) = suffix ++ env.

Lemma par_trace_point_extends_env_mutual :
  (forall s, point_extends_stmt_goal s) /\
  (forall ss, point_extends_stmts_goal ss).
Proof.
  apply pl_stmt_stmts_mutind;
    unfold point_extends_stmt_goal, point_extends_stmts_goal.
  - intros mode od lb ub body IH env tr ip Hsafe Htrace Hin.
    inversion Htrace; subst.
    + apply in_concat in Hin.
      destruct Hin as [tri [Htri Hin]].
      destruct (Forall2_in_right_local _ _ _ _ _ _ H7 Htri)
        as [z [Hz Hbody]].
      destruct (IH (z :: env) tri ip Hsafe Hbody Hin) as [suffix Hsuffix].
      exists (suffix ++ [z]).
      rewrite Hsuffix. simpl. rewrite <- app_assoc. reflexivity.
    + apply in_concat in Hin.
      destruct Hin as [tri [Htri Hin]].
      destruct (Forall2_in_right_local _ _ _ _ _ _ H7 Htri)
        as [z [Hz Hbody]].
      destruct (IH (z :: env) tri ip Hsafe Hbody Hin) as [suffix Hsuffix].
      exists (suffix ++ [z]).
      rewrite Hsuffix. simpl. rewrite <- app_assoc. reflexivity.
    + pose proof
        (interleave_family_member_in_concat _ _ _ H8 Hin) as Hin_concat.
      apply in_concat in Hin_concat.
      destruct Hin_concat as [tri [Htri Hintri]].
      destruct (Forall2_in_right_local _ _ _ _ _ _ H7 Htri)
        as [z [Hz Hbody]].
      destruct (IH (z :: env) tri ip Hsafe Hbody Hintri) as [suffix Hsuffix].
      exists (suffix ++ [z]).
      rewrite Hsuffix. simpl. rewrite <- app_assoc. reflexivity.
  - intros i es env tr ip Hsafe Htrace Hin.
    inversion Htrace; subst.
    simpl in Hin.
    destruct Hin as [<- | Hin]; [|contradiction].
    destruct Hsafe as [affs Haff].
    exists []. unfold ParallelLoop.BaseLoop.mk_instr_point. rewrite Haff. reflexivity.
  - intros ss IH env tr ip Hsafe Htrace Hin.
    inversion Htrace; subst. eapply IH; eauto.
  - intros test body IH env tr ip Hsafe Htrace Hin.
    inversion Htrace; subst; [eapply IH; eauto|contradiction].
  - intros env tr ip Hsafe Htrace Hin.
    inversion Htrace; subst. contradiction.
  - intros s IHs ss IHss env tr ip Hsafe Htrace Hin.
    inversion Htrace; subst.
    destruct Hsafe as [Hsafe_s Hsafe_ss].
    apply in_app_or in Hin.
    destruct Hin as [Hin | Hin]; [eapply IHs|eapply IHss]; eauto.
Qed.

Lemma par_trace_point_extends_env :
  forall s env tr ip,
    ParallelLoop.trace_safe_stmt s ->
    ParallelLoop.par_trace s env tr ->
    In ip tr ->
    exists suffix, ip.(ParallelLoop.ILSema.ip_index) = suffix ++ env.
Proof.
  exact (proj1 par_trace_point_extends_env_mutual).
Qed.

Definition par_trace_seq_cover_stmt_goal (s : ParallelLoop.stmt) : Prop :=
  forall env tr,
    ParallelLoop.trace_safe_stmt s ->
    ParallelLoop.par_trace s env tr ->
    exists seqtr,
      ParallelLoop.seq_trace s env seqtr /\
      (forall ip, In ip tr -> In ip seqtr).

Definition par_trace_seq_cover_stmts_goal (ss : ParallelLoop.stmt_list) : Prop :=
  forall env tr,
    ParallelLoop.trace_safe_stmts ss ->
    ParallelLoop.par_traces ss env tr ->
    exists seqtr,
      ParallelLoop.seq_traces ss env seqtr /\
      (forall ip, In ip tr -> In ip seqtr).

Lemma Forall2_par_trace_seq_cover :
  forall body env,
    par_trace_seq_cover_stmt_goal body ->
    forall zs trs,
      ParallelLoop.trace_safe_stmt body ->
      Forall2 (fun z tr => ParallelLoop.par_trace body (z :: env) tr) zs trs ->
      exists seqtrs,
        Forall2 (fun z tr => ParallelLoop.seq_trace body (z :: env) tr) zs seqtrs /\
        (forall ip, In ip (List.concat trs) -> In ip (List.concat seqtrs)).
Proof.
  intros body env IH zs trs Hsafe Hfor.
  induction Hfor as [|z tr zs trs Htrace Hfor IHfor].
  - exists []. split; [constructor|]. simpl. tauto.
  - destruct (IH (z :: env) tr Hsafe Htrace)
      as [seqtr [Hseq Hcover]].
    destruct IHfor as [seqtrs [Hseqs Hcovers]].
    exists (seqtr :: seqtrs).
    split.
    + constructor; assumption.
    + intros ip Hin.
      simpl in *.
      apply in_app_or in Hin.
      apply in_or_app.
      destruct Hin as [Hin | Hin].
      * left. eapply Hcover. exact Hin.
      * right. eapply Hcovers. exact Hin.
Qed.

Lemma par_trace_seq_cover_mutual :
  (forall s, par_trace_seq_cover_stmt_goal s) /\
  (forall ss, par_trace_seq_cover_stmts_goal ss).
Proof.
  apply pl_stmt_stmts_mutind;
    unfold par_trace_seq_cover_stmt_goal,
      par_trace_seq_cover_stmts_goal.
  - intros mode od lb ub body IH env tr Hsafe Htrace.
    inversion Htrace; subst.
    + destruct (Forall2_par_trace_seq_cover body env IH _ _ Hsafe H7)
        as [seqtrs [Hseqtrs Hcover]].
      exists (List.concat seqtrs).
      split.
      * econstructor; eauto.
      * intros ip Hin. eapply Hcover. exact Hin.
    + destruct (Forall2_par_trace_seq_cover body env IH _ _ Hsafe H7)
        as [seqtrs [Hseqtrs Hcover]].
      exists (List.concat seqtrs).
      split.
      * econstructor; eauto.
      * intros ip Hin. eapply Hcover. exact Hin.
    + destruct (Forall2_par_trace_seq_cover body env IH _ _ Hsafe H7)
        as [seqtrs [Hseqtrs Hcover]].
      exists (List.concat seqtrs).
      split.
      * econstructor; eauto.
      * intros ip Hin.
        eapply Hcover.
        eapply interleave_family_member_in_concat; eauto.
  - intros i es env tr Hsafe Htrace.
    inversion Htrace; subst.
    exists [ParallelLoop.BaseLoop.mk_instr_point i es env].
    split; [constructor|]. tauto.
  - intros ss IH env tr Hsafe Htrace.
    inversion Htrace as [|env0 ss0 tr0 Hsub| | | | |]; subst.
    destruct (IH env tr Hsafe Hsub) as [seqtr [Hseq Hcover]].
    exists seqtr. split; [constructor; exact Hseq|exact Hcover].
  - intros test body IH env tr Hsafe Htrace.
    inversion Htrace as
      [| |
       env0 test0 body0 tr0 Htest Hbody
       | env0 test0 body0 Htest
       | | |]; subst.
    + destruct (IH env tr Hsafe Hbody) as [seqtr [Hseq Hcover]].
      exists seqtr. split; [econstructor; eauto|exact Hcover].
    + exists []. split.
      * apply ParallelLoop.STGuardFalse. assumption.
      * auto.
  - intros env tr Hsafe Htrace.
    inversion Htrace; subst.
    exists []. split; [constructor|].
    contradiction.
  - intros s IHs ss IHss env tr Hsafe Htrace.
    inversion Htrace as
      [|env0 s0 ss0 tr1 tr2 Hhead Htail]; subst.
    destruct Hsafe as [Hsafe_s Hsafe_ss].
    destruct (IHs env tr1 Hsafe_s Hhead)
      as [seqtr1 [Hseq1 Hcover1]].
    destruct (IHss env tr2 Hsafe_ss Htail)
      as [seqtr2 [Hseq2 Hcover2]].
    exists (seqtr1 ++ seqtr2).
    split.
    + econstructor; eauto.
    + intros ip Hin.
      apply in_app_or in Hin.
      apply in_or_app.
      destruct Hin as [Hin | Hin].
      * left. eapply Hcover1. exact Hin.
      * right. eapply Hcover2. exact Hin.
Qed.

Lemma par_trace_seq_cover :
  forall s env tr,
    ParallelLoop.trace_safe_stmt s ->
    ParallelLoop.par_trace s env tr ->
    exists seqtr,
      ParallelLoop.seq_trace s env seqtr /\
      (forall ip, In ip tr -> In ip seqtr).
Proof.
  exact (proj1 par_trace_seq_cover_mutual).
Qed.

Definition seq_trace_parallelize_inv_stmt_goal (s : ParallelLoop.stmt) : Prop :=
  forall d env tr,
    ParallelLoop.seq_trace (ParallelLoop.parallelize_dim_stmt d s) env tr ->
    ParallelLoop.seq_trace s env tr.

Definition seq_trace_parallelize_inv_stmts_goal (ss : ParallelLoop.stmt_list) : Prop :=
  forall d env tr,
    ParallelLoop.seq_traces (ParallelLoop.parallelize_dim_stmts d ss) env tr ->
    ParallelLoop.seq_traces ss env tr.

Lemma seq_trace_parallelize_dim_inv_mutual :
  (forall s, seq_trace_parallelize_inv_stmt_goal s) /\
  (forall ss, seq_trace_parallelize_inv_stmts_goal ss).
Proof.
  apply pl_stmt_stmts_mutind;
    unfold seq_trace_parallelize_inv_stmt_goal,
      seq_trace_parallelize_inv_stmts_goal.
  - intros mode od lb ub body IHbody d env tr Htrace.
    destruct mode; destruct od as [origin|]; simpl in Htrace;
      try destruct (Nat.eqb d origin);
      inversion Htrace; subst.
    all: econstructor; eauto.
    all: eapply Forall2_imp;
      [intros z tri Hbody; eapply IHbody; exact Hbody
      | eassumption].
  - intros i es d env tr Htrace. simpl in Htrace. exact Htrace.
  - intros ss IH d env tr Htrace.
    simpl in Htrace. inversion Htrace; subst.
    constructor. eapply IH. eauto.
  - intros test body IH d env tr Htrace.
    simpl in Htrace. inversion Htrace; subst.
    + econstructor; [eassumption|].
      eapply IH; eassumption.
    + econstructor; eassumption.
  - intros d env tr Htrace. simpl in Htrace.
    inversion Htrace; subst. constructor.
  - intros s IHs ss IHss d env tr Htrace.
    simpl in Htrace. inversion Htrace; subst.
    econstructor.
    + eapply IHs; eauto.
    + eapply IHss; eauto.
Qed.

Lemma seq_trace_parallelize_dim_stmt_inv :
  forall d s env tr,
    ParallelLoop.seq_trace (ParallelLoop.parallelize_dim_stmt d s) env tr ->
    ParallelLoop.seq_trace s env tr.
Proof.
  intros d s.
  exact ((proj1 seq_trace_parallelize_dim_inv_mutual) s d).
Qed.

Definition generated_event (ip : ParallelLoop.InstrPoint) : RawOrigin.scan_event :=
  {| RawOrigin.se_point := rev ip.(ParallelLoop.ILSema.ip_index);
     RawOrigin.se_instr := ip.(ParallelLoop.ILSema.ip_instruction);
     RawOrigin.se_args :=
       affine_product ip.(ParallelLoop.ILSema.ip_transformation)
         ip.(ParallelLoop.ILSema.ip_index) |}.

Lemma tag_expr_eval :
  forall e env,
    ParallelLoop.BaseLoop.eval_expr env (tag_expr e) = Loop.eval_expr env e.
Proof.
  induction e; intros env; simpl;
    try rewrite ?IHe, ?IHe1, ?IHe2; reflexivity.
Qed.

Lemma map_tag_expr_eval :
  forall es env,
    map (ParallelLoop.BaseLoop.eval_expr env) (map tag_expr es) =
    map (Loop.eval_expr env) es.
Proof.
  induction es as [|e es IH]; intros env; simpl.
  - reflexivity.
  - rewrite tag_expr_eval, IH. reflexivity.
Qed.

Lemma tag_test_eval :
  forall test env,
    ParallelLoop.BaseLoop.eval_test env (tag_test test) = Loop.eval_test env test.
Proof.
  induction test; intros env; simpl;
    try rewrite ?IHtest, ?IHtest1, ?IHtest2;
    try rewrite ?tag_expr_eval; reflexivity.
Qed.

Lemma map_concat_generated_event :
  forall traces,
    map generated_event (List.concat traces) =
    List.concat (map (map generated_event) traces).
Proof.
  induction traces as [|tr traces IH]; simpl.
  - reflexivity.
  - rewrite map_app, IH. reflexivity.
Qed.

Scheme loop_stmt_mutind := Induction for Loop.stmt Sort Prop
with loop_stmts_mutind := Induction for Loop.stmt_list Sort Prop.
Combined Scheme loopl_stmt_stmts_mutind
  from loop_stmt_mutind, loop_stmts_mutind.

Definition tagged_seq_trace_origin_stmt_goal (s : Loop.stmt) : Prop :=
  forall depth env tr,
    ParallelLoop.trace_safe_stmt (tag_loop_stmt_at depth s) ->
    ParallelLoop.seq_trace (tag_loop_stmt_at depth s) env tr ->
    RawOrigin.loop_trace s env (map generated_event tr).

Definition tagged_seq_trace_origin_stmts_goal (ss : Loop.stmt_list) : Prop :=
  forall depth env tr,
    ParallelLoop.trace_safe_stmts (tag_loop_stmts_at depth ss) ->
    ParallelLoop.seq_traces (tag_loop_stmts_at depth ss) env tr ->
    RawOrigin.loop_traces ss env (map generated_event tr).

Lemma tagged_seq_trace_origin_mutual :
  (forall s, tagged_seq_trace_origin_stmt_goal s) /\
  (forall ss, tagged_seq_trace_origin_stmts_goal ss).
Proof.
  apply loopl_stmt_stmts_mutind;
    unfold tagged_seq_trace_origin_stmt_goal,
      tagged_seq_trace_origin_stmts_goal.
  - intros lb ub body IH depth env tr Hsafe Htrace.
    simpl in Htrace, Hsafe.
    inversion Htrace as
      [| | | |
       mode0 od0 lb0 ub0 body0 env0 zs0 trs0 tr0
         Hrange Htraces Hconcat]; subst.
    rewrite map_concat_generated_event.
    econstructor.
    + reflexivity.
    + rewrite <- !tag_expr_eval.
      clear Htrace.
      induction Htraces as [|z tri zs trs Htri Htraces IHtraces].
      * constructor.
      * constructor.
        -- eapply IH; eauto.
        -- exact IHtraces.
  - intros i es depth env tr Hsafe Htrace.
    simpl in Hsafe, Htrace.
    inversion Htrace; subst.
    simpl.
    destruct Hsafe as [affs Haff].
    unfold generated_event, ParallelLoop.BaseLoop.mk_instr_point.
    rewrite Haff. simpl.
    assert (Hargs :
      affine_product affs env = map (Loop.eval_expr env) es).
    {
      rewrite <- map_tag_expr_eval.
      symmetry.
      eapply ParallelLoop.BaseLoop.exprlist_to_aff_correct. exact Haff.
    }
    rewrite Hargs.
    constructor.
  - intros ss IH depth env tr Hsafe Htrace.
    simpl in Hsafe, Htrace.
    inversion Htrace; subst.
    constructor. eapply IH; eauto.
  - intros test body IH depth env tr Hsafe Htrace.
    simpl in Hsafe, Htrace.
    inversion Htrace; subst.
    + eapply RawOrigin.LETGuardTrue.
      * rewrite <- tag_test_eval. eassumption.
      * eapply IH; eauto.
    + eapply RawOrigin.LETGuardFalse.
      rewrite <- tag_test_eval. eassumption.
  - intros depth env tr Hsafe Htrace.
    simpl in Htrace. inversion Htrace; subst.
    simpl. constructor.
  - intros s IHs ss IHss depth env tr Hsafe Htrace.
    simpl in Hsafe, Htrace.
    destruct Hsafe as [Hsafe_s Hsafe_ss].
    inversion Htrace; subst.
    rewrite map_app.
    constructor.
    + eapply IHs; eauto.
    + eapply IHss; eauto.
Qed.

Lemma tagged_seq_trace_origin :
  forall s depth env tr,
    ParallelLoop.trace_safe_stmt (tag_loop_stmt_at depth s) ->
    ParallelLoop.seq_trace (tag_loop_stmt_at depth s) env tr ->
    RawOrigin.loop_trace s env (map generated_event tr).
Proof.
  exact (proj1 tagged_seq_trace_origin_mutual).
Qed.

Definition erase_stmt_sem_goal (s : ParallelLoop.stmt) : Prop :=
  forall env st1 st2,
    ParallelLoop.BaseLoop.loop_semantics (ParallelLoop.erase_stmt s) env st1 st2 ->
    Loop.loop_semantics (erase_to_loop_stmt s) env st1 st2.

Definition erase_stmts_sem_goal (ss : ParallelLoop.stmt_list) : Prop :=
  forall env st1 st2,
    ParallelLoop.BaseLoop.loop_semantics
      (ParallelLoop.BaseLoop.Seq (ParallelLoop.erase_stmt_list ss)) env st1 st2 ->
    Loop.loop_semantics (Loop.Seq (erase_to_loop_stmts ss)) env st1 st2.

Lemma erase_to_loop_stmt_semantics_mutual :
  (forall s, erase_stmt_sem_goal s) /\
  (forall ss, erase_stmts_sem_goal ss).
Proof.
  apply (pl_stmt_stmts_mutind erase_stmt_sem_goal erase_stmts_sem_goal).
  - intros mode od lb ub body IHbody env st1 st2 Hsem.
    inversion Hsem as
      [| | | | |
       env0 lb0 ub0 body0 st10 st20 Hiter]; subst.
    eapply Loop.LLoop.
    rewrite !erase_expr_eval_eq.
    pose proof Hiter as Hiter'.
    eapply iter_semantics_refine_exact with
      (Q := fun x => Loop.loop_semantics (erase_to_loop_stmt body) (x :: env))
      in Hiter'.
    + exact Hiter'.
    + intros x stA stB _ Hbody_sem.
      eapply IHbody; eauto.
  - intros i es env st1 st2 Hsem.
    inversion Hsem; subst.
    eapply Loop.LInstr.
    rewrite erase_expr_list_map_eval_eq.
    eauto.
  - intros ss IHss env st1 st2 Hsem.
    eapply IHss; eauto.
  - intros test body IHbody env st1 st2 Hsem.
    inversion Hsem; subst.
    + eapply Loop.LGuardTrue.
      * eapply IHbody; eauto.
      * rewrite erase_test_eval_eq. eauto.
    + eapply Loop.LGuardFalse.
      rewrite erase_test_eval_eq. eauto.
  - intros env st1 st2 Hsem.
    inversion Hsem; subst.
    constructor.
  - intros s IHs ss IHss env st1 st2 Hsem.
    inversion Hsem; subst.
    eapply Loop.LSeq.
    + eapply IHs; eauto.
    + eapply IHss; eauto.
Qed.

Lemma erase_to_loop_stmt_semantics :
  forall s env st1 st2,
    ParallelLoop.BaseLoop.loop_semantics (ParallelLoop.erase_stmt s) env st1 st2 ->
    Loop.loop_semantics (erase_to_loop_stmt s) env st1 st2.
Proof.
  exact (proj1 erase_to_loop_stmt_semantics_mutual).
Qed.

Lemma erase_to_loop_stmts_semantics :
  forall ss env st1 st2,
    ParallelLoop.BaseLoop.loop_semantics
      (ParallelLoop.BaseLoop.Seq (ParallelLoop.erase_stmt_list ss)) env st1 st2 ->
    Loop.loop_semantics (Loop.Seq (erase_to_loop_stmts ss)) env st1 st2.
Proof.
  exact (proj2 erase_to_loop_stmt_semantics_mutual).
Qed.

Lemma erase_to_loop_semantics :
  forall p st1 st2,
    ParallelLoop.BaseLoop.semantics (ParallelLoop.erase_parallel p) st1 st2 ->
    Loop.semantics (erase_to_loop p) st1 st2.
Proof.
  intros [[s ctxt] vars] st1 st2 Hsem.
  inversion Hsem as [loop_ext loop ctxt' vars' env st1' st2' Heq Hcompat Hna Hinit Hloop];
    subst.
  inversion Heq; subst.
  econstructor; eauto.
  reflexivity.
  eapply erase_to_loop_stmt_semantics; eauto.
Qed.

Definition tagged_prepared_codegen
  (pp : PolyLang.t) : imp ParallelLoop.t :=
  BIND loop <- PrepareCore.prepared_codegen pp -;
  pure (tag_loop loop).

(** * Executable annotation paths *)

Definition tagged_prepared_codegen_raw
  (pp : PolyLang.t) : imp ParallelLoop.t :=
  BIND loop <- PrepareCore.prepared_codegen_raw pp -;
  pure (tag_loop loop).

Record codegen_matches_current_dims
  (_pp : PolyLang.t) (pl : ParallelLoop.t) : Prop := {
  cmd_origin_tagged :
    tagged_from_top pl
}.

Definition annotated_codegen
  (pp : PolyLang.t)
  (cert : ParallelValidator.parallel_cert)
  : imp ParallelLoop.t :=
  BIND pl <- tagged_prepared_codegen pp -;
  pure (ParallelLoop.parallelize_dim cert.(ParallelValidator.certified_dim) pl).

Definition annotated_codegen_raw
  (pp : PolyLang.t)
  (cert : ParallelValidator.parallel_cert)
  : imp ParallelLoop.t :=
  BIND pl <- tagged_prepared_codegen_raw pp -;
  pure (ParallelLoop.parallelize_dim cert.(ParallelValidator.certified_dim) pl).

Definition program_par_trace
    (pl : ParallelLoop.t) (env : list Z) (tr : list ParallelLoop.InstrPoint) : Prop :=
  let '((s, _), _) := pl in ParallelLoop.par_trace s env tr.

Lemma generated_event_matches :
  forall ip,
    point_matches_event ip (generated_event ip).
Proof.
  intros ip.
  unfold point_matches_event, generated_event.
  simpl. split; [reflexivity|].
  unfold point_has_effect.
  intros st1 st2. split.
  - intro Hsem.
    inversion Hsem as [wcs rcs Hstep]; subst.
    exists wcs, rcs. exact Hstep.
  - intros [wcs [rcs Hstep]].
    econstructor. exact Hstep.
Qed.

Lemma prepared_schedule_width_eq :
  forall pis varctxt vars cols,
    list_max
      (map (fun pi => Datatypes.length pi.(PolyLang.pi_schedule))
        (map (PrepareCore.prepare_pi (Datatypes.length varctxt) cols) pis)) =
    ParallelValidator.schedule_width ((pis, varctxt), vars).
Proof.
  intros pis varctxt vars cols.
  unfold ParallelValidator.schedule_width, ParallelValidator.schedule_width_of_pis, ParallelValidator.pprog_pis.
  simpl.
  rewrite map_map.
  f_equal.
  apply map_ext.
  intro pi.
  simpl.
  unfold PrepareCore.resize_affine_list.
  rewrite map_length.
  reflexivity.
Qed.

Definition trace_safe_parallelize_inv_stmt_goal (s : ParallelLoop.stmt) : Prop :=
  forall d,
    ParallelLoop.trace_safe_stmt (ParallelLoop.parallelize_dim_stmt d s) ->
    ParallelLoop.trace_safe_stmt s.

Definition trace_safe_parallelize_inv_stmts_goal (ss : ParallelLoop.stmt_list) : Prop :=
  forall d,
    ParallelLoop.trace_safe_stmts (ParallelLoop.parallelize_dim_stmts d ss) ->
    ParallelLoop.trace_safe_stmts ss.

Lemma trace_safe_parallelize_dim_inv_mutual :
  (forall s, trace_safe_parallelize_inv_stmt_goal s) /\
  (forall ss, trace_safe_parallelize_inv_stmts_goal ss).
Proof.
  apply pl_stmt_stmts_mutind;
    unfold trace_safe_parallelize_inv_stmt_goal,
      trace_safe_parallelize_inv_stmts_goal.
  - intros mode od lb ub body IH d Hsafe.
    destruct mode; destruct od as [origin|]; simpl in Hsafe |- *;
      try destruct (Nat.eqb d origin);
      eapply IH; exact Hsafe.
  - intros i es d Hsafe. exact Hsafe.
  - intros ss IH d Hsafe. simpl in Hsafe |- *. eapply IH; eauto.
  - intros test body IH d Hsafe. simpl in Hsafe |- *. eapply IH; eauto.
  - intros d Hsafe. exact I.
  - intros s IHs ss IHss d Hsafe.
    simpl in Hsafe |- *.
    destruct Hsafe as [Hs Hss].
    split; [eapply IHs|eapply IHss]; eauto.
Qed.

Lemma trace_safe_parallelize_dim_stmt_inv :
  forall d s,
    ParallelLoop.trace_safe_stmt (ParallelLoop.parallelize_dim_stmt d s) ->
    ParallelLoop.trace_safe_stmt s.
Proof.
  intros d s.
  exact ((proj1 trace_safe_parallelize_dim_inv_mutual) s d).
Qed.

Definition vector_annotated_codegen
  (pp : PolyLang.t)
  (cert : ParallelValidator.parallel_cert)
  : imp ParallelLoop.t :=
  BIND pl <- tagged_prepared_codegen pp -;
  pure (ParallelLoop.vectorize_dim cert.(ParallelValidator.certified_dim) pl).

Definition vector_annotated_codegen_raw
  (pp : PolyLang.t)
  (cert : ParallelValidator.parallel_cert)
  : imp ParallelLoop.t :=
  BIND pl <- tagged_prepared_codegen_raw pp -;
  pure (ParallelLoop.vectorize_dim cert.(ParallelValidator.certified_dim) pl).

Fixpoint parallelize_certified_dims
  (certs : list ParallelValidator.parallel_cert)
  (pl : ParallelLoop.t) : ParallelLoop.t :=
  match certs with
  | nil => pl
  | cons cert certs' =>
      parallelize_certified_dims
        certs'
        (ParallelLoop.parallelize_dim cert.(ParallelValidator.certified_dim) pl)
  end.

Definition annotated_codegen_many
  (pp : PolyLang.t)
  (certs : list ParallelValidator.parallel_cert)
  : imp ParallelLoop.t :=
  BIND pl <- tagged_prepared_codegen pp -;
  pure (parallelize_certified_dims certs pl).

Definition annotated_codegen_many_raw
  (pp : PolyLang.t)
  (certs : list ParallelValidator.parallel_cert)
  : imp ParallelLoop.t :=
  BIND pl <- tagged_prepared_codegen_raw pp -;
  pure (parallelize_certified_dims certs pl).

Definition result_is_ok {A} (r : result A) : bool :=
  match r with
  | Okk _ => true
  | Err _ => false
  end.

(** * Checked trace-safety and cleanup gates *)

Fixpoint all_es_safeb_stmt (s : ParallelLoop.stmt) : bool
with all_es_safeb_stmts (ss : ParallelLoop.stmt_list) : bool.
Proof.
  - destruct s; simpl.
    + exact (all_es_safeb_stmt s).
    + exact (result_is_ok (ParallelLoop.BaseLoop.exprlist_to_aff l)).
    + exact (all_es_safeb_stmts s).
    + exact (all_es_safeb_stmt s).
  - destruct ss; simpl.
    + exact true.
    + exact (all_es_safeb_stmt s && all_es_safeb_stmts ss).
Defined.

Definition all_es_safeb (p : ParallelLoop.t) : bool :=
  match p with
  | ((s, _), _) => all_es_safeb_stmt s
  end.

Lemma all_es_safeb_stmt_sound :
  forall s,
    all_es_safeb_stmt s = true ->
    ParallelLoop.trace_safe_stmt s
with all_es_safeb_stmts_sound :
  forall ss,
    all_es_safeb_stmts ss = true ->
    ParallelLoop.trace_safe_stmts ss.
Proof.
  - intros s Hsafe.
    destruct s; simpl in *.
    + eapply all_es_safeb_stmt_sound; eauto.
    + destruct (ParallelLoop.BaseLoop.exprlist_to_aff l) eqn:Haff;
        inversion Hsafe; subst; eauto.
    + eapply all_es_safeb_stmts_sound; eauto.
    + eapply all_es_safeb_stmt_sound; eauto.
  - intros ss Hsafe.
    destruct ss; simpl in *.
    + constructor.
    + rewrite andb_true_iff in Hsafe.
      destruct Hsafe as [Hs Hss].
      split.
      * eapply all_es_safeb_stmt_sound; eauto.
      * eapply all_es_safeb_stmts_sound; eauto.
Qed.

Lemma all_es_safeb_sound :
  forall p,
    all_es_safeb p = true ->
    ParallelLoop.trace_safe p.
Proof.
  intros [[s ctxt] vars] Hsafe; simpl in *.
  eapply all_es_safeb_stmt_sound; eauto.
Qed.

(** Cleanup is returned only when every representation used by its semantic
    reflection proof has affine instruction traces.  The final simplifier can
    remove a non-affine dead branch or reduce a non-affine expression such as
    division by one, so checking only the final program would not establish
    safety of the intermediate traces. *)
Definition parallel_cleanup_safe (p : ParallelLoop.t) : Prop :=
  match p with
  | ((s, _), _) =>
      ParallelLoop.trace_safe_stmt s /\
      ParallelLoop.trace_safe_stmt (ParallelLoop.simplify_stmt s) /\
      ParallelLoop.trace_safe_stmt
        (ParallelLoop.cleanup_stmt (ParallelLoop.simplify_stmt s)) /\
      ParallelLoop.trace_safe_stmt
        (ParallelLoop.singleton_elim_stmt
          (ParallelLoop.cleanup_stmt (ParallelLoop.simplify_stmt s))) /\
      ParallelLoop.trace_safe_stmt
        (ParallelLoop.simplify_stmt
          (ParallelLoop.singleton_elim_stmt
            (ParallelLoop.cleanup_stmt (ParallelLoop.simplify_stmt s)))) /\
      ParallelLoop.trace_safe_stmt (ParallelLoop.cleanup_stmt_pass s)
  end.

Definition parallel_cleanup_safeb (p : ParallelLoop.t) : bool :=
  match p with
  | ((s, _), _) =>
      all_es_safeb_stmt s &&
      all_es_safeb_stmt (ParallelLoop.simplify_stmt s) &&
      all_es_safeb_stmt
        (ParallelLoop.cleanup_stmt (ParallelLoop.simplify_stmt s)) &&
      all_es_safeb_stmt
        (ParallelLoop.singleton_elim_stmt
          (ParallelLoop.cleanup_stmt (ParallelLoop.simplify_stmt s))) &&
      all_es_safeb_stmt
        (ParallelLoop.simplify_stmt
          (ParallelLoop.singleton_elim_stmt
            (ParallelLoop.cleanup_stmt (ParallelLoop.simplify_stmt s)))) &&
      all_es_safeb_stmt (ParallelLoop.cleanup_stmt_pass s)
  end.

Lemma parallel_cleanup_safeb_sound :
  forall p,
    parallel_cleanup_safeb p = true ->
    parallel_cleanup_safe p.
Proof.
  intros [[s ctxt] vars] Hsafe.
  unfold parallel_cleanup_safeb, parallel_cleanup_safe in *.
  repeat rewrite andb_true_iff in Hsafe.
  destruct Hsafe as [[[[[H0 H1] H2] H3] H4] H5].
  repeat split; eapply all_es_safeb_stmt_sound; eauto.
Qed.

Definition vector_codegen_safeb (p : ParallelLoop.t) : bool :=
  all_es_safeb p && ParallelLoop.vector_annotations_innermostb p.

Lemma vector_codegen_safeb_sound :
  forall p,
    vector_codegen_safeb p = true ->
    ParallelLoop.trace_safe p /\
    ParallelLoop.vector_annotations_innermostb p = true.
Proof.
  intros p Hsafe.
  apply andb_true_iff in Hsafe.
  destruct Hsafe as [Htrace Hvector].
  split.
  - eapply all_es_safeb_sound; eauto.
  - exact Hvector.
Qed.

Definition checked_annotated_codegen
  (pp : PolyLang.t)
  (cert : ParallelValidator.parallel_cert)
  : imp (result ParallelLoop.t) :=
  BIND pl_raw <- annotated_codegen_raw pp cert -;
  let pl_clean := ParallelLoop.full_cleanup pl_raw in
  if parallel_cleanup_safeb pl_raw then pure (Okk pl_clean)
  else if all_es_safeb pl_raw then pure (Okk pl_raw)
  else pure (Err "Annotated parallel codegen produced non-affine instruction trace loop"%string).

Definition checked_vector_annotated_codegen
  (pp : PolyLang.t)
  (cert : ParallelValidator.parallel_cert)
  : imp (result ParallelLoop.t) :=
  BIND pl_raw <- vector_annotated_codegen_raw pp cert -;
  let pl_clean := ParallelLoop.full_cleanup pl_raw in
  if parallel_cleanup_safeb pl_raw &&
     ParallelLoop.vector_annotations_innermostb pl_clean
  then pure (Okk pl_clean)
  else if vector_codegen_safeb pl_raw then pure (Okk pl_raw)
  else
    pure
      (Err
         "Annotated vector codegen produced a non-affine trace, a non-innermost vector loop, or no vector loop"%string).

Definition checked_annotated_codegen_many
  (pp : PolyLang.t)
  (certs : list ParallelValidator.parallel_cert)
  : imp (result ParallelLoop.t) :=
  BIND pl_raw <- annotated_codegen_many_raw pp certs -;
  let pl_clean := ParallelLoop.full_cleanup pl_raw in
  if parallel_cleanup_safeb pl_raw then pure (Okk pl_clean)
  else if all_es_safeb pl_raw then pure (Okk pl_raw)
  else pure (Err "Annotated parallel codegen produced non-affine instruction trace loop"%string).

Lemma tagged_prepared_codegen_matches :
  forall pp pl,
    mayReturn (tagged_prepared_codegen pp) pl ->
    codegen_matches_current_dims pp pl.
Proof.
  intros pp pl Hgen.
  unfold tagged_prepared_codegen in Hgen.
  apply mayReturn_bind in Hgen.
  destruct Hgen as [loop [Hprep Hpure]].
  apply mayReturn_pure in Hpure.
  subst pl.
  constructor.
  destruct loop as [[s ctxt] vars]; simpl.
  apply tag_loop_stmt_tagged_from_depth.
Qed.

Lemma tagged_prepared_codegen_erase_eq :
  forall pp pl,
    mayReturn (tagged_prepared_codegen pp) pl ->
    exists loop,
      mayReturn (PrepareCore.prepared_codegen pp) loop /\
      erase_to_loop pl = loop.
Proof.
  intros pp pl Hgen.
  unfold tagged_prepared_codegen in Hgen.
  apply mayReturn_bind in Hgen.
  destruct Hgen as [loop [Hprep Hpure]].
  apply mayReturn_pure in Hpure.
  subst pl.
  exists loop.
  split; auto.
  simpl.
  apply erase_tag_loop_eq.
Qed.

Lemma tagged_prepared_codegen_raw_erase_eq :
  forall pp pl,
    mayReturn (tagged_prepared_codegen_raw pp) pl ->
    exists loop,
      mayReturn (PrepareCore.prepared_codegen_raw pp) loop /\
      erase_to_loop pl = loop.
Proof.
  intros pp pl Hgen.
  unfold tagged_prepared_codegen_raw in Hgen.
  apply mayReturn_bind in Hgen.
  destruct Hgen as [loop [Hprep Hpure]].
  apply mayReturn_pure in Hpure.
  subst pl.
  exists loop.
  split; auto.
  simpl.
  apply erase_tag_loop_eq.
Qed.

Lemma annotated_codegen_erase_eq :
  forall pp cert pl,
    mayReturn (annotated_codegen pp cert) pl ->
    exists loop,
      mayReturn (PrepareCore.prepared_codegen pp) loop /\
      erase_to_loop pl = loop.
Proof.
  intros pp cert pl Hgen.
  unfold annotated_codegen in Hgen.
  apply mayReturn_bind in Hgen.
  destruct Hgen as [tagged [Htag Hpure]].
  apply mayReturn_pure in Hpure.
  subst pl.
  pose proof (tagged_prepared_codegen_erase_eq pp tagged Htag) as Herase.
  destruct Herase as [loop [Hprep Herase]].
  exists loop.
  split; auto.
  rewrite erase_parallelize_dim_to_loop_eq.
  exact Herase.
Qed.

Lemma annotated_codegen_raw_erase_eq :
  forall pp cert pl,
    mayReturn (annotated_codegen_raw pp cert) pl ->
    exists loop,
      mayReturn (PrepareCore.prepared_codegen_raw pp) loop /\
      erase_to_loop pl = loop.
Proof.
  intros pp cert pl Hgen.
  unfold annotated_codegen_raw in Hgen.
  apply mayReturn_bind in Hgen.
  destruct Hgen as [tagged [Htag Hpure]].
  apply mayReturn_pure in Hpure.
  subst pl.
  pose proof (tagged_prepared_codegen_raw_erase_eq pp tagged Htag) as Herase.
  destruct Herase as [loop [Hprep Herase]].
  exists loop.
  split; auto.
  rewrite erase_parallelize_dim_to_loop_eq.
  exact Herase.
Qed.

Lemma vector_annotated_codegen_erase_eq :
  forall pp cert pl,
    mayReturn (vector_annotated_codegen pp cert) pl ->
    exists loop,
      mayReturn (PrepareCore.prepared_codegen pp) loop /\
      erase_to_loop pl = loop.
Proof.
  intros pp cert pl Hgen.
  unfold vector_annotated_codegen in Hgen.
  apply mayReturn_bind in Hgen.
  destruct Hgen as [tagged [Htag Hpure]].
  apply mayReturn_pure in Hpure.
  subst pl.
  pose proof (tagged_prepared_codegen_erase_eq pp tagged Htag) as Herase.
  destruct Herase as [loop [Hprep Herase]].
  exists loop.
  split; auto.
  rewrite erase_vectorize_dim_to_loop_eq.
  exact Herase.
Qed.

Lemma vector_annotated_codegen_raw_erase_eq :
  forall pp cert pl,
    mayReturn (vector_annotated_codegen_raw pp cert) pl ->
    exists loop,
      mayReturn (PrepareCore.prepared_codegen_raw pp) loop /\
      erase_to_loop pl = loop.
Proof.
  intros pp cert pl Hgen.
  unfold vector_annotated_codegen_raw in Hgen.
  apply mayReturn_bind in Hgen.
  destruct Hgen as [tagged [Htag Hpure]].
  apply mayReturn_pure in Hpure.
  subst pl.
  pose proof (tagged_prepared_codegen_raw_erase_eq pp tagged Htag) as Herase.
  destruct Herase as [loop [Hprep Herase]].
  exists loop.
  split; auto.
  rewrite erase_vectorize_dim_to_loop_eq.
  exact Herase.
Qed.

Lemma erase_parallelize_certified_dims_to_loop_eq :
  forall certs pl,
    erase_to_loop (parallelize_certified_dims certs pl) = erase_to_loop pl.
Proof.
  induction certs as [|cert certs IH]; intros pl; simpl.
  - reflexivity.
  - rewrite IH.
    apply erase_parallelize_dim_to_loop_eq.
Qed.

Lemma annotated_codegen_many_erase_eq :
  forall pp certs pl,
    mayReturn (annotated_codegen_many pp certs) pl ->
    exists loop,
      mayReturn (PrepareCore.prepared_codegen pp) loop /\
      erase_to_loop pl = loop.
Proof.
  intros pp certs pl Hgen.
  unfold annotated_codegen_many in Hgen.
  apply mayReturn_bind in Hgen.
  destruct Hgen as [tagged [Htag Hpure]].
  apply mayReturn_pure in Hpure.
  subst pl.
  pose proof (tagged_prepared_codegen_erase_eq pp tagged Htag) as Herase.
  destruct Herase as [loop [Hprep Herase]].
  exists loop.
  split; auto.
  rewrite erase_parallelize_certified_dims_to_loop_eq.
  exact Herase.
Qed.

Lemma annotated_codegen_many_raw_erase_eq :
  forall pp certs pl,
    mayReturn (annotated_codegen_many_raw pp certs) pl ->
    exists loop,
      mayReturn (PrepareCore.prepared_codegen_raw pp) loop /\
      erase_to_loop pl = loop.
Proof.
  intros pp certs pl Hgen.
  unfold annotated_codegen_many_raw in Hgen.
  apply mayReturn_bind in Hgen.
  destruct Hgen as [tagged [Htag Hpure]].
  apply mayReturn_pure in Hpure.
  subst pl.
  pose proof (tagged_prepared_codegen_raw_erase_eq pp tagged Htag) as Herase.
  destruct Herase as [loop [Hprep Herase]].
  exists loop.
  split; auto.
  rewrite erase_parallelize_certified_dims_to_loop_eq.
  exact Herase.
Qed.


End ParallelCodegenCore.

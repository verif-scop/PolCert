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

Require Import ParallelCodegenCore.

Module ParallelCodegenCompatibility (PolIRs : POLIRS).
Include ParallelCodegenCore PolIRs.

(** * Compatibility layer and support interface

    These low-level lemmas predate the certificate-to-trace connection and
    accept an explicit [parallel_families_ordered] invariant.  They remain as
    compatibility APIs and are not used by the checked parallel driver.

    The second half of this file is not legacy: it exposes checked-result
    inversions, schedule-slice facts, and the root-origin interface consumed by
    [ParallelCodegenCorrect]. *)

(** ** Legacy global-ordering wrappers *)

Lemma annotated_codegen_refines_prepared_codegen :
  forall pp cert pl st st',
    mayReturn (annotated_codegen pp cert) pl ->
    ParallelLoop.trace_safe pl ->
    ParallelLoop.parallel_families_ordered pl ->
    ParallelLoop.semantics pl st st' ->
    exists loop st'',
      mayReturn (PrepareCore.prepared_codegen pp) loop /\
      Loop.semantics loop st st'' /\
      Instr.State.eq st' st''.
Proof.
  intros pp cert [[s ctxt] vars] st st' Hgen Hsafe Hordered Hsem.
  pose proof (annotated_codegen_erase_eq pp cert ((s, ctxt), vars) Hgen)
    as [loop [Hprep Herase]].
  pose proof (ParallelLoop.semantics_refines_erased_global
    ((s, ctxt), vars) st st' Hsafe Hordered Hsem)
    as [st'' [Herased Heq]].
  exists loop, st''.
  split; [exact Hprep|].
  split.
  - rewrite <- Herase.
    eapply erase_to_loop_semantics.
    exact Herased.
  - exact Heq.
Qed.

Lemma annotated_codegen_raw_refines_prepared_codegen :
  forall pp cert pl st st',
    mayReturn (annotated_codegen_raw pp cert) pl ->
    ParallelLoop.trace_safe pl ->
    ParallelLoop.parallel_families_ordered pl ->
    ParallelLoop.semantics pl st st' ->
    exists loop st'',
      mayReturn (PrepareCore.prepared_codegen_raw pp) loop /\
      Loop.semantics loop st st'' /\
      Instr.State.eq st' st''.
Proof.
  intros pp cert [[s ctxt] vars] st st' Hgen Hsafe Hordered Hsem.
  pose proof (annotated_codegen_raw_erase_eq pp cert ((s, ctxt), vars) Hgen)
    as [loop [Hprep Herase]].
  pose proof (ParallelLoop.semantics_refines_erased_global
    ((s, ctxt), vars) st st' Hsafe Hordered Hsem)
    as [st'' [Herased Heq]].
  exists loop, st''.
  split; [exact Hprep|].
  split.
  - rewrite <- Herase.
    eapply erase_to_loop_semantics.
    exact Herased.
  - exact Heq.
Qed.

Lemma vector_annotated_codegen_refines_prepared_codegen :
  forall pp cert pl st st',
    mayReturn (vector_annotated_codegen pp cert) pl ->
    ParallelLoop.trace_safe pl ->
    ParallelLoop.semantics pl st st' ->
    exists loop st'',
      mayReturn (PrepareCore.prepared_codegen pp) loop /\
      Loop.semantics loop st st'' /\
      Instr.State.eq st' st''.
Proof.
  intros pp cert [[s ctxt] vars] st st' Hgen Hsafe Hsem.
  assert (Hordered :
    ParallelLoop.parallel_families_ordered ((s, ctxt), vars)).
  {
    unfold vector_annotated_codegen in Hgen.
    apply mayReturn_bind in Hgen.
    destruct Hgen as [tagged [Htag Hpure]].
    apply mayReturn_pure in Hpure. inversion Hpure; subst.
    unfold tagged_prepared_codegen in Htag.
    apply mayReturn_bind in Htag.
    destruct Htag as [loop [Hloop Hpure_loop]].
    apply mayReturn_pure in Hpure_loop. inversion Hpure_loop; subst.
    destruct loop as [[loop_stmt loop_ctxt] loop_vars].
    simpl. apply vectorize_tag_loop_stmt_ordered.
  }
  pose proof (vector_annotated_codegen_erase_eq pp cert ((s, ctxt), vars) Hgen)
    as [loop [Hprep Herase]].
  pose proof (ParallelLoop.semantics_refines_erased_global
    ((s, ctxt), vars) st st' Hsafe Hordered Hsem)
    as [st'' [Herased Heq]].
  exists loop, st''.
  split; [exact Hprep|].
  split.
  - rewrite <- Herase.
    eapply erase_to_loop_semantics.
    exact Herased.
  - exact Heq.
Qed.

Lemma vector_annotated_codegen_raw_refines_prepared_codegen :
  forall pp cert pl st st',
    mayReturn (vector_annotated_codegen_raw pp cert) pl ->
    ParallelLoop.trace_safe pl ->
    ParallelLoop.semantics pl st st' ->
    exists loop st'',
      mayReturn (PrepareCore.prepared_codegen_raw pp) loop /\
      Loop.semantics loop st st'' /\
      Instr.State.eq st' st''.
Proof.
  intros pp cert [[s ctxt] vars] st st' Hgen Hsafe Hsem.
  assert (Hordered :
    ParallelLoop.parallel_families_ordered ((s, ctxt), vars)).
  {
    unfold vector_annotated_codegen_raw in Hgen.
    apply mayReturn_bind in Hgen.
    destruct Hgen as [tagged [Htag Hpure]].
    apply mayReturn_pure in Hpure. inversion Hpure; subst.
    unfold tagged_prepared_codegen_raw in Htag.
    apply mayReturn_bind in Htag.
    destruct Htag as [loop [Hloop Hpure_loop]].
    apply mayReturn_pure in Hpure_loop. inversion Hpure_loop; subst.
    destruct loop as [[loop_stmt loop_ctxt] loop_vars].
    simpl. apply vectorize_tag_loop_stmt_ordered.
  }
  pose proof (vector_annotated_codegen_raw_erase_eq pp cert ((s, ctxt), vars) Hgen)
    as [loop [Hprep Herase]].
  pose proof (ParallelLoop.semantics_refines_erased_global
    ((s, ctxt), vars) st st' Hsafe Hordered Hsem)
    as [st'' [Herased Heq]].
  exists loop, st''.
  split; [exact Hprep|].
  split.
  - rewrite <- Herase.
    eapply erase_to_loop_semantics.
    exact Herased.
  - exact Heq.
Qed.

Lemma annotated_codegen_many_refines_prepared_codegen :
  forall pp certs pl st st',
    mayReturn (annotated_codegen_many pp certs) pl ->
    ParallelLoop.trace_safe pl ->
    ParallelLoop.parallel_families_ordered pl ->
    ParallelLoop.semantics pl st st' ->
    exists loop st'',
      mayReturn (PrepareCore.prepared_codegen pp) loop /\
      Loop.semantics loop st st'' /\
      Instr.State.eq st' st''.
Proof.
  intros pp certs [[s ctxt] vars] st st' Hgen Hsafe Hordered Hsem.
  pose proof (annotated_codegen_many_erase_eq pp certs ((s, ctxt), vars) Hgen)
    as [loop [Hprep Herase]].
  pose proof (ParallelLoop.semantics_refines_erased_global
    ((s, ctxt), vars) st st' Hsafe Hordered Hsem)
    as [st'' [Herased Heq]].
  exists loop, st''.
  split; [exact Hprep|].
  split.
  - rewrite <- Herase.
    eapply erase_to_loop_semantics.
    exact Herased.
  - exact Heq.
Qed.

Lemma annotated_codegen_many_raw_refines_prepared_codegen :
  forall pp certs pl st st',
    mayReturn (annotated_codegen_many_raw pp certs) pl ->
    ParallelLoop.trace_safe pl ->
    ParallelLoop.parallel_families_ordered pl ->
    ParallelLoop.semantics pl st st' ->
    exists loop st'',
      mayReturn (PrepareCore.prepared_codegen_raw pp) loop /\
      Loop.semantics loop st st'' /\
      Instr.State.eq st' st''.
Proof.
  intros pp certs [[s ctxt] vars] st st' Hgen Hsafe Hordered Hsem.
  pose proof (annotated_codegen_many_raw_erase_eq pp certs ((s, ctxt), vars) Hgen)
    as [loop [Hprep Herase]].
  pose proof (ParallelLoop.semantics_refines_erased_global
    ((s, ctxt), vars) st st' Hsafe Hordered Hsem)
    as [st'' [Herased Heq]].
  exists loop, st''.
  split; [exact Hprep|].
  split.
  - rewrite <- Herase.
    eapply erase_to_loop_semantics.
    exact Herased.
  - exact Heq.
Qed.

Theorem annotated_codegen_correct_general :
  forall pol cert pl st st',
    mayReturn (annotated_codegen (PolyLang.current_view_pprog pol) cert) pl ->
    PolyLang.wf_pprog_general pol ->
    ParallelLoop.trace_safe pl ->
    ParallelLoop.parallel_families_ordered pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\
      Instr.State.eq st' st''.
Proof.
  intros pol cert pl st st' Hcodegen Hwf Hsafe Hordered Hsem.
  destruct
    (annotated_codegen_refines_prepared_codegen
       (PolyLang.current_view_pprog pol) cert pl st st'
       Hcodegen Hsafe Hordered Hsem)
    as [loop [st'' [Hprep [Hloop Heq]]]].
  exists st''.
  split.
  - eapply PrepareCore.prepared_codegen_correct_general; eauto.
  - exact Heq.
Qed.

Theorem annotated_codegen_raw_correct_general :
  forall pol cert pl st st',
    mayReturn (annotated_codegen_raw (PolyLang.current_view_pprog pol) cert) pl ->
    PolyLang.wf_pprog_general pol ->
    ParallelLoop.trace_safe pl ->
    ParallelLoop.parallel_families_ordered pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\
      Instr.State.eq st' st''.
Proof.
  intros pol cert pl st st' Hcodegen Hwf Hsafe Hordered Hsem.
  destruct
    (annotated_codegen_raw_refines_prepared_codegen
       (PolyLang.current_view_pprog pol) cert pl st st'
       Hcodegen Hsafe Hordered Hsem)
    as [loop [st'' [Hprep [Hloop Heq]]]].
  exists st''.
  split.
  - eapply PrepareCore.prepared_codegen_raw_correct_general; eauto.
  - exact Heq.
Qed.

Theorem vector_annotated_codegen_correct_general :
  forall pol cert pl st st',
    mayReturn (vector_annotated_codegen (PolyLang.current_view_pprog pol) cert) pl ->
    PolyLang.wf_pprog_general pol ->
    ParallelLoop.trace_safe pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\
      Instr.State.eq st' st''.
Proof.
  intros pol cert pl st st' Hcodegen Hwf Hsafe Hsem.
  destruct
    (vector_annotated_codegen_refines_prepared_codegen
       (PolyLang.current_view_pprog pol) cert pl st st'
       Hcodegen Hsafe Hsem)
    as [loop [st'' [Hprep [Hloop Heq]]]].
  exists st''.
  split.
  - eapply PrepareCore.prepared_codegen_correct_general; eauto.
  - exact Heq.
Qed.

Theorem vector_annotated_codegen_raw_correct_general :
  forall pol cert pl st st',
    mayReturn (vector_annotated_codegen_raw (PolyLang.current_view_pprog pol) cert) pl ->
    PolyLang.wf_pprog_general pol ->
    ParallelLoop.trace_safe pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\
      Instr.State.eq st' st''.
Proof.
  intros pol cert pl st st' Hcodegen Hwf Hsafe Hsem.
  destruct
    (vector_annotated_codegen_raw_refines_prepared_codegen
       (PolyLang.current_view_pprog pol) cert pl st st'
       Hcodegen Hsafe Hsem)
    as [loop [st'' [Hprep [Hloop Heq]]]].
  exists st''.
  split.
  - eapply PrepareCore.prepared_codegen_raw_correct_general; eauto.
  - exact Heq.
Qed.

Theorem annotated_codegen_many_correct_general :
  forall pol certs pl st st',
    mayReturn (annotated_codegen_many (PolyLang.current_view_pprog pol) certs) pl ->
    PolyLang.wf_pprog_general pol ->
    ParallelLoop.trace_safe pl ->
    ParallelLoop.parallel_families_ordered pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\
      Instr.State.eq st' st''.
Proof.
  intros pol certs pl st st' Hcodegen Hwf Hsafe Hordered Hsem.
  destruct
    (annotated_codegen_many_refines_prepared_codegen
       (PolyLang.current_view_pprog pol) certs pl st st'
       Hcodegen Hsafe Hordered Hsem)
    as [loop [st'' [Hprep [Hloop Heq]]]].
  exists st''.
  split.
  - eapply PrepareCore.prepared_codegen_correct_general; eauto.
  - exact Heq.
Qed.

Theorem annotated_codegen_many_raw_correct_general :
  forall pol certs pl st st',
    mayReturn (annotated_codegen_many_raw (PolyLang.current_view_pprog pol) certs) pl ->
    PolyLang.wf_pprog_general pol ->
    ParallelLoop.trace_safe pl ->
    ParallelLoop.parallel_families_ordered pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\
      Instr.State.eq st' st''.
Proof.
  intros pol certs pl st st' Hcodegen Hwf Hsafe Hordered Hsem.
  destruct
    (annotated_codegen_many_raw_refines_prepared_codegen
       (PolyLang.current_view_pprog pol) certs pl st st'
       Hcodegen Hsafe Hordered Hsem)
    as [loop [st'' [Hprep [Hloop Heq]]]].
  exists st''.
  split.
  - eapply PrepareCore.prepared_codegen_raw_correct_general; eauto.
  - exact Heq.
Qed.

(** ** Checked-codegen result inversions *)

Lemma checked_annotated_codegen_ok_inv :
  forall pp cert pl,
    mayReturn (checked_annotated_codegen pp cert) (Okk pl) ->
    (exists pl_raw,
      mayReturn (annotated_codegen_raw pp cert) pl_raw /\
      pl = ParallelLoop.full_cleanup pl_raw /\
      parallel_cleanup_safe pl_raw) \/
    (mayReturn (annotated_codegen_raw pp cert) pl /\
     ParallelLoop.trace_safe pl).
Proof.
  intros pp cert pl Hcodegen.
  unfold checked_annotated_codegen in Hcodegen.
  apply mayReturn_bind in Hcodegen.
  destruct Hcodegen as [pl_raw [Hann Hret]].
  destruct (parallel_cleanup_safeb pl_raw) eqn:Hsafe_clean.
  - apply mayReturn_pure in Hret.
    inversion Hret; subst pl.
    left. exists pl_raw. repeat split; auto.
    eapply parallel_cleanup_safeb_sound; eauto.
  - destruct (all_es_safeb pl_raw) eqn:Hsafe_raw.
    + apply mayReturn_pure in Hret.
      inversion Hret; subst pl.
      right. split; [exact Hann|].
      eapply all_es_safeb_sound; eauto.
    + apply mayReturn_pure in Hret. discriminate.
Qed.

Lemma checked_vector_annotated_codegen_ok_inv :
  forall pp cert pl,
    mayReturn (checked_vector_annotated_codegen pp cert) (Okk pl) ->
    (exists pl_raw,
      mayReturn (vector_annotated_codegen_raw pp cert) pl_raw /\
      pl = ParallelLoop.full_cleanup pl_raw /\
      parallel_cleanup_safe pl_raw /\
      ParallelLoop.vector_annotations_innermostb pl = true) \/
    (mayReturn (vector_annotated_codegen_raw pp cert) pl /\
     ParallelLoop.trace_safe pl /\
     ParallelLoop.vector_annotations_innermostb pl = true).
Proof.
  intros pp cert pl Hcodegen.
  unfold checked_vector_annotated_codegen in Hcodegen.
  apply mayReturn_bind in Hcodegen.
  destruct Hcodegen as [pl_raw [Hann Hret]].
  destruct (parallel_cleanup_safeb pl_raw &&
    ParallelLoop.vector_annotations_innermostb
      (ParallelLoop.full_cleanup pl_raw)) eqn:Hsafe.
  - apply mayReturn_pure in Hret.
    inversion Hret; subst pl.
    apply andb_true_iff in Hsafe.
    destruct Hsafe as [Hcleanup Hinner].
    left. exists pl_raw. repeat split; auto.
    eapply parallel_cleanup_safeb_sound; eauto.
  - destruct (vector_codegen_safeb pl_raw) eqn:Hsafe_raw.
    + apply mayReturn_pure in Hret.
      inversion Hret; subst pl_raw.
      right.
      split.
      * exact Hann.
      * eapply vector_codegen_safeb_sound; eauto.
    + apply mayReturn_pure in Hret.
      discriminate.
Qed.

Lemma checked_annotated_codegen_many_ok_inv :
  forall pp certs pl,
    mayReturn (checked_annotated_codegen_many pp certs) (Okk pl) ->
    (exists pl_raw,
      mayReturn (annotated_codegen_many_raw pp certs) pl_raw /\
      pl = ParallelLoop.full_cleanup pl_raw /\
      parallel_cleanup_safe pl_raw) \/
    (mayReturn (annotated_codegen_many_raw pp certs) pl /\
     ParallelLoop.trace_safe pl).
Proof.
  intros pp certs pl Hcodegen.
  unfold checked_annotated_codegen_many in Hcodegen.
  apply mayReturn_bind in Hcodegen.
  destruct Hcodegen as [pl_raw [Hann Hret]].
  destruct (parallel_cleanup_safeb pl_raw) eqn:Hsafe_clean.
  - apply mayReturn_pure in Hret.
    inversion Hret; subst pl.
    left. exists pl_raw. repeat split; auto.
    eapply parallel_cleanup_safeb_sound; eauto.
  - destruct (all_es_safeb pl_raw) eqn:Hsafe_raw.
    + apply mayReturn_pure in Hret.
      inversion Hret; subst pl.
      right. split; [exact Hann|].
      eapply all_es_safeb_sound; eauto.
    + apply mayReturn_pure in Hret. discriminate.
Qed.

(** ** Generated schedule slices and source-point transport *)

Definition generated_schedule_coords
    (env_dim width : nat) (current : list Z) : list Z :=
  resize width (skipn env_dim current).

Lemma generated_schedule_coords_sibling :
  forall env_dim width d env z suffix,
    Datatypes.length env = (env_dim + d)%nat ->
    (d < width)%nat ->
    generated_schedule_coords env_dim width
      (rev (z :: env) ++ suffix) =
      skipn env_dim (rev env) ++
        z :: resize (width - S d)%nat suffix.
Proof.
  intros env_dim width d env z suffix Henv Hd.
  set (outer := firstn env_dim (rev env)).
  set (prefix := skipn env_dim (rev env)).
  assert (Houter_len : Datatypes.length outer = env_dim).
  {
    unfold outer. rewrite firstn_length_le; [reflexivity|].
    rewrite rev_length, Henv. lia.
  }
  assert (Hprefix_len : Datatypes.length prefix = d).
  {
    unfold prefix. rewrite skipn_length, rev_length, Henv. lia.
  }
  assert (Hrev : rev env = outer ++ prefix).
  {
    unfold outer, prefix. symmetry. apply firstn_skipn.
  }
  unfold generated_schedule_coords.
  simpl. rewrite Hrev. rewrite <- !app_assoc.
  rewrite skipn_app by exact Houter_len.
  replace (env_dim - Datatypes.length outer)%nat with 0%nat by lia.
  simpl.
  rewrite resize_app_le by (rewrite Hprefix_len; lia).
  rewrite Hprefix_len.
  replace (width - d)%nat with (S (width - S d)) by lia.
  simpl. reflexivity.
Qed.

Lemma sibling_generated_slice_lists :
  forall env_dim width d env z1 z2 suffix1 suffix2,
    Datatypes.length env = (env_dim + d)%nat ->
    (d < width)%nat ->
    z1 <> z2 ->
    resize env_dim (rev (z1 :: env) ++ suffix1) =
      resize env_dim (rev (z2 :: env) ++ suffix2) /\
    firstn d
      (generated_schedule_coords env_dim width
        (rev (z1 :: env) ++ suffix1)) =
      firstn d
        (generated_schedule_coords env_dim width
          (rev (z2 :: env) ++ suffix2)) /\
    nth_error
      (generated_schedule_coords env_dim width
        (rev (z1 :: env) ++ suffix1)) d <>
      nth_error
        (generated_schedule_coords env_dim width
          (rev (z2 :: env) ++ suffix2)) d.
Proof.
  intros env_dim width d env z1 z2 suffix1 suffix2 Henv Hd Hneq.
  assert (Hprefix_len :
    Datatypes.length (skipn env_dim (rev env)) = d).
  { rewrite skipn_length, rev_length, Henv. lia. }
  repeat split.
  - simpl.
    rewrite
      (resize_app_ge env_dim (rev env ++ [z1]) suffix1),
      (resize_app_ge env_dim (rev env ++ [z2]) suffix2)
      by (rewrite app_length, rev_length, Henv; simpl; lia).
    rewrite
      (resize_app_ge env_dim (rev env) [z1]),
      (resize_app_ge env_dim (rev env) [z2])
      by (rewrite rev_length, Henv; lia).
    reflexivity.
  - rewrite
      (generated_schedule_coords_sibling
        env_dim width d env z1 suffix1 Henv Hd),
      (generated_schedule_coords_sibling
        env_dim width d env z2 suffix2 Henv Hd).
    rewrite !firstn_app, Hprefix_len, Nat.sub_diag.
    simpl. rewrite !firstn_all2 by lia.
    now rewrite !app_nil_r.
  - rewrite
      (generated_schedule_coords_sibling
        env_dim width d env z1 suffix1 Henv Hd),
      (generated_schedule_coords_sibling
        env_dim width d env z2 suffix2 Henv Hd).
    rewrite !nth_error_app2 by lia.
    rewrite Hprefix_len.
    replace (d - d)%nat with 0%nat by lia.
    simpl. congruence.
Qed.

Lemma generated_source_point_env_dim :
  forall pp width generated source,
    generated_source_point_full pp width generated source ->
    ParallelValidator.env_dim_of source = Datatypes.length (ParallelValidator.pprog_varctxt pp).
Proof.
  intros pp width generated source Hfull.
  destruct Hfull as [Hbasic Hprefix Hschedule].
  destruct Hbasic as [Hequiv [pi [Hnth [Hbelongs Hlength]]]].
  unfold ParallelValidator.env_dim_of.
  unfold PolyLang.belongs_to in Hbelongs.
  destruct Hbelongs as [_ [_ [_ [_ Hdepth]]]].
  rewrite Hlength, Hdepth. lia.
Qed.

Lemma generated_source_siblings_same_slice :
  forall pp width d env z1 z2 suffix1 suffix2
      generated1 generated2 source1 source2,
    width = ParallelValidator.schedule_width pp ->
    Datatypes.length env =
      (Datatypes.length (ParallelValidator.pprog_varctxt pp) + d)%nat ->
    (d < width)%nat ->
    z1 <> z2 ->
    generated1.(ParallelLoop.ILSema.ip_index) = suffix1 ++ z1 :: env ->
    generated2.(ParallelLoop.ILSema.ip_index) = suffix2 ++ z2 :: env ->
    generated_source_point_full pp width generated1 source1 ->
    generated_source_point_full pp width generated2 source2 ->
    ParallelValidator.same_parallel_slice pp d source1 source2.
Proof.
  intros pp width d env z1 z2 suffix1 suffix2
    generated1 generated2 source1 source2 Hwidth Henv Hd Hneq
    Hindex1 Hindex2 Hfull1 Hfull2.
  pose proof Hfull1 as Hfull1_dim.
  pose proof Hfull2 as Hfull2_dim.
  destruct Hfull1 as [Hbasic1 Henv1 Hschedule1].
  destruct Hfull2 as [Hbasic2 Henv2 Hschedule2].
  pose proof
    (generated_source_point_env_dim
      pp width generated1 source1 Hfull1_dim) as Henvdim1.
  pose proof
    (generated_source_point_env_dim
      pp width generated2 source2 Hfull2_dim) as Henvdim2.
  set (env_dim := Datatypes.length (ParallelValidator.pprog_varctxt pp)) in *.
  destruct
    (sibling_generated_slice_lists env_dim width d env z1 z2
      (rev suffix1) (rev suffix2) Henv Hd Hneq)
    as [Hsibling_env [Hsibling_prefix Hsibling_dim]].
  assert (Hrevindex1 :
    rev generated1.(ParallelLoop.ILSema.ip_index) =
      rev (z1 :: env) ++ rev suffix1).
  { rewrite Hindex1, rev_app_distr. reflexivity. }
  assert (Hrevindex2 :
    rev generated2.(ParallelLoop.ILSema.ip_index) =
      rev (z2 :: env) ++ rev suffix2).
  { rewrite Hindex2, rev_app_distr. reflexivity. }
  unfold ParallelValidator.same_parallel_slice, ParallelValidator.same_env_of, ParallelValidator.env_prefix_of,
    ParallelValidator.same_prefix_before, ParallelValidator.different_dim_at, ParallelValidator.padded_timestamp.
  rewrite Henvdim1, Henvdim2. rewrite <- Hwidth.
  repeat split.
  - rewrite Henv1, Henv2, Hrevindex1, Hrevindex2.
    exact Hsibling_env.
  - rewrite <- Hschedule1, <- Hschedule2.
    unfold generated_schedule_coords in Hsibling_prefix.
    rewrite Hrevindex1, Hrevindex2. exact Hsibling_prefix.
  - rewrite <- Hschedule1, <- Hschedule2.
    unfold generated_schedule_coords in Hsibling_dim.
    rewrite Hrevindex1, Hrevindex2. exact Hsibling_dim.
Qed.

Lemma Forall2_imp_in_right :
  forall A B (R S : A -> B -> Prop) xs ys,
    Forall2 R xs ys ->
    (forall x y, In y ys -> R x y -> S x y) ->
    Forall2 S xs ys.
Proof.
  intros A B R S xs ys Hfor.
  induction Hfor; intro Himp.
  - constructor.
  - constructor.
    + eapply Himp; [left; reflexivity|exact H].
    + apply IHHfor.
      intros x' y' Hin HR.
      eapply Himp; [right; exact Hin|exact HR].
Qed.

Scheme p_stmt_mutind := Induction for ParallelLoop.stmt Sort Prop
with p_stmts_mutind := Induction for ParallelLoop.stmt_list Sort Prop.
Combined Scheme p_stmt_stmts_mutind from p_stmt_mutind, p_stmts_mutind.

(** ** Trace-safety transport and the root-origin interface *)

Definition trace_safe_parallelize_stmt_goal (s : ParallelLoop.stmt) : Prop :=
  forall d,
    ParallelLoop.trace_safe_stmt s ->
    ParallelLoop.trace_safe_stmt (ParallelLoop.parallelize_dim_stmt d s).

Definition trace_safe_parallelize_stmts_goal (ss : ParallelLoop.stmt_list) : Prop :=
  forall d,
    ParallelLoop.trace_safe_stmts ss ->
    ParallelLoop.trace_safe_stmts (ParallelLoop.parallelize_dim_stmts d ss).

Lemma trace_safe_parallelize_dim_mutual :
  (forall s, trace_safe_parallelize_stmt_goal s) /\
  (forall ss, trace_safe_parallelize_stmts_goal ss).
Proof.
  apply p_stmt_stmts_mutind;
    unfold trace_safe_parallelize_stmt_goal,
      trace_safe_parallelize_stmts_goal.
  - intros mode od lb ub body IH d Hsafe.
    destruct mode; destruct od; simpl; eauto.
  - intros i es d Hsafe. exact Hsafe.
  - intros ss IH d Hsafe. simpl. eapply IH. exact Hsafe.
  - intros test body IH d Hsafe. simpl. eapply IH. exact Hsafe.
  - intros d Hsafe. exact I.
  - intros s IHs ss IHss d Hsafe.
    destruct Hsafe as [Hs Hss]. simpl. split; eauto.
Qed.

Lemma trace_safe_parallelize_dim_stmt :
  forall s d,
    ParallelLoop.trace_safe_stmt s ->
    ParallelLoop.trace_safe_stmt (ParallelLoop.parallelize_dim_stmt d s).
Proof.
  intros s. exact ((proj1 trace_safe_parallelize_dim_mutual) s).
Qed.

Definition root_origin_oracle
    (pp : PolyLang.t) (root : list ParallelLoop.InstrPoint) : Prop :=
  forall generated,
    In generated root ->
    exists source,
      generated_source_point_full
        pp (ParallelValidator.schedule_width pp) generated source.


End ParallelCodegenCompatibility.

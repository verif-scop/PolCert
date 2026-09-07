Require Import ImpureAlarmConfig.
Require Import Result.
Require Import SPolIRs.
Require Import SParallelPolOpt.
Require Import SParallelPolOptShared.
Require Import Vpl.Impure.

Local Open Scope impure_scope.

Module FunctorCore := SParallelPolOptShared.Core.

(** [SParallelPolOpt] provides stable concrete definitions for extraction,
    whereas [FunctorCore] is the instance for which generic correctness was
    proved.  These [impeq] lemmas align their monadic control flow.  They are
    implementation-correspondence proofs, not additional transformation
    correctness arguments. *)

Lemma entry_bind_assoc_compat {A B C : Type}
    (extract : imp A)
    (concrete_prepared functor_prepared : A -> imp B)
    (finish : B -> imp C) :
  (forall a, impeq (concrete_prepared a) (functor_prepared a)) ->
  impeq
    (BIND a <- extract -; BIND b <- concrete_prepared a -; finish b)
    (BIND b <- (BIND a <- extract -; functor_prepared a) -; finish b).
Proof.
  intros Hprepared.
  symmetry.
  rewrite impeq_bind_assoc.
  apply bind_eq_compat; [reflexivity|].
  intros a.
  apply bind_eq_compat; [symmetry; apply Hprepared|].
  intros b. reflexivity.
Qed.

Lemma select_after_tiling_route_impeq :
  forall pol_after route,
    impeq
      (SParallelPolOpt.select_after_tiling_route pol_after route)
      (FunctorCore.select_after_tiling_route pol_after route).
Proof.
  intros pol_after route.
  destruct route; reflexivity.
Qed.

Lemma try_verified_tiling_after_phase_mid_poly_impeq :
  forall pol_mid mid_scop after_scop,
    impeq
      (SParallelPolOpt.try_verified_tiling_after_phase_mid_poly
         pol_mid mid_scop after_scop)
      (FunctorCore.try_verified_tiling_after_phase_mid_poly
         pol_mid mid_scop after_scop).
Proof.
  intros pol_mid mid_scop after_scop.
  unfold SParallelPolOpt.try_verified_tiling_after_phase_mid_poly,
    FunctorCore.try_verified_tiling_after_phase_mid_poly.
  destruct (FunctorCore.CoreOpt.infer_tiling_witness_scops mid_scop after_scop)
    as [ws|]; [|reflexivity].
  destruct
    (FunctorCore.ValidatorCore.import_canonical_tiled_after_poly
       pol_mid after_scop ws) as [pol_after|]; [|reflexivity].
  apply bind_eq_compat; [reflexivity|].
  intros route.
  rewrite SParallelPolOpt.observe_tiling_validation_route_eq.
  destruct route.
  - apply bind_eq_compat; [reflexivity|].
    intros wf_after. destruct wf_after.
    + apply select_after_tiling_route_impeq.
    + reflexivity.
  - apply bind_eq_compat; [reflexivity|].
    intros wf_after. destruct wf_after.
    + apply select_after_tiling_route_impeq.
    + reflexivity.
  - unfold SParallelPolOpt.reject_tiling, FunctorCore.reject_tiling.
    rewrite SParallelPolOpt.observe_tiling_validation_route_eq.
    reflexivity.
Qed.

Lemma try_phase_pipeline_from_source_pol_poly_impeq :
  forall pol_source phase_runner before_scop,
    impeq
      (SParallelPolOpt.try_phase_pipeline_from_source_pol_poly
         pol_source phase_runner before_scop)
      (FunctorCore.try_phase_pipeline_from_source_pol_poly
         pol_source phase_runner before_scop).
Proof.
  intros pol_source phase_runner before_scop.
  unfold SParallelPolOpt.try_phase_pipeline_from_source_pol_poly,
    FunctorCore.try_phase_pipeline_from_source_pol_poly.
  destruct (phase_runner before_scop) as [[mid_scop after_scop]|];
    [|reflexivity].
  destruct
    (SPolIRs.PolyLang.from_openscop_schedule_only pol_source mid_scop)
    as [pol_mid|]; [|reflexivity].
  apply bind_eq_compat; [reflexivity|].
  intros affine_ok. destruct affine_ok.
  - apply try_verified_tiling_after_phase_mid_poly_impeq.
  - unfold SParallelPolOpt.reject_tiling, FunctorCore.reject_tiling.
    rewrite SParallelPolOpt.observe_tiling_validation_route_eq.
    reflexivity.
Qed.

Lemma try_identity_tiling_phase_pipeline_from_source_pol_poly_impeq :
  forall pol_source before_scop,
    impeq
      (SParallelPolOpt.try_identity_tiling_phase_pipeline_from_source_pol_poly
         pol_source before_scop)
      (FunctorCore.try_identity_tiling_phase_pipeline_from_source_pol_poly
         pol_source before_scop).
Proof.
  intros pol_source before_scop.
  unfold
    SParallelPolOpt.try_identity_tiling_phase_pipeline_from_source_pol_poly,
    FunctorCore.try_identity_tiling_phase_pipeline_from_source_pol_poly.
  destruct (FunctorCore.CoreOpt.run_pluto_identity_tiling_pipeline before_scop)
    as [[mid_scop after_scop]|]; [|reflexivity].
  destruct
    (SPolIRs.PolyLang.from_openscop_like_source pol_source mid_scop)
    as [pol_mid|]; [|reflexivity].
  apply bind_eq_compat; [reflexivity|].
  intros affine_ok. destruct affine_ok.
  - apply try_verified_tiling_after_phase_mid_poly_impeq.
  - unfold SParallelPolOpt.reject_tiling, FunctorCore.reject_tiling.
    rewrite SParallelPolOpt.observe_tiling_validation_route_eq.
    reflexivity.
Qed.

Lemma try_verified_post_tiling_affine_after_phase_mid_poly_impeq :
  forall pol_mid mid_scop posttile_scop after_scop,
    impeq
      (SParallelPolOpt.try_verified_post_tiling_affine_after_phase_mid_poly
         pol_mid mid_scop posttile_scop after_scop)
      (FunctorCore.try_verified_post_tiling_affine_after_phase_mid_poly
         pol_mid mid_scop posttile_scop after_scop).
Proof.
  intros pol_mid mid_scop posttile_scop after_scop.
  unfold SParallelPolOpt.try_verified_post_tiling_affine_after_phase_mid_poly,
    FunctorCore.try_verified_post_tiling_affine_after_phase_mid_poly.
  destruct
    (FunctorCore.CoreOpt.infer_tiling_witness_scops mid_scop posttile_scop)
    as [ws|]; [|reflexivity].
  destruct
    (FunctorCore.ValidatorCore.import_canonical_tiled_after_poly
       pol_mid posttile_scop ws) as [pol_posttile|]; [|reflexivity].
  apply bind_eq_compat; [reflexivity|].
  intros route.
  rewrite SParallelPolOpt.observe_tiling_validation_route_eq.
  destruct route.
  - apply bind_eq_compat; [reflexivity|].
    intros wf_posttile. destruct wf_posttile; [|reflexivity].
    destruct
      (SPolIRs.PolyLang.from_openscop_schedule_only
         pol_posttile after_scop) as [pol_after|]; [|reflexivity].
    apply bind_eq_compat; [reflexivity|].
    intros final_ok. destruct final_ok; [|reflexivity].
    apply bind_eq_compat; [reflexivity|].
    intros wf_after. destruct wf_after.
    + apply select_after_tiling_route_impeq.
    + reflexivity.
  - apply bind_eq_compat; [reflexivity|].
    intros wf_posttile. destruct wf_posttile; [|reflexivity].
    destruct
      (SPolIRs.PolyLang.from_openscop_schedule_only
         pol_posttile after_scop) as [pol_after|]; [|reflexivity].
    apply bind_eq_compat; [reflexivity|].
    intros final_ok. destruct final_ok; [|reflexivity].
    apply bind_eq_compat; [reflexivity|].
    intros wf_after. destruct wf_after.
    + apply select_after_tiling_route_impeq.
    + reflexivity.
  - unfold SParallelPolOpt.reject_tiling, FunctorCore.reject_tiling.
    rewrite SParallelPolOpt.observe_tiling_validation_route_eq.
    reflexivity.
Qed.

Lemma try_post_tiling_affine_phase_pipeline_from_source_pol_poly_impeq :
  forall pol_source before_scop,
    impeq
      (SParallelPolOpt.try_post_tiling_affine_phase_pipeline_from_source_pol_poly
         pol_source before_scop)
      (FunctorCore.try_post_tiling_affine_phase_pipeline_from_source_pol_poly
         pol_source before_scop).
Proof.
  intros pol_source before_scop.
  unfold SParallelPolOpt.try_post_tiling_affine_phase_pipeline_from_source_pol_poly,
    FunctorCore.try_post_tiling_affine_phase_pipeline_from_source_pol_poly.
  destruct (FunctorCore.CoreOpt.run_pluto_post_tiling_affine_phase_pipeline before_scop)
    as [[mid_scop [posttile_scop after_scop]]|]; [|reflexivity].
  destruct
    (SPolIRs.PolyLang.from_openscop_schedule_only pol_source mid_scop)
    as [pol_mid|]; [|reflexivity].
  apply bind_eq_compat; [reflexivity|].
  intros affine_ok. destruct affine_ok.
  - apply try_verified_post_tiling_affine_after_phase_mid_poly_impeq.
  - reflexivity.
Qed.

Lemma try_post_tiling_affine_phase_pipeline_from_source_pol_poly_with_iss_impeq :
  forall pol_source before_scop,
    impeq
      (SParallelPolOpt.try_post_tiling_affine_phase_pipeline_from_source_pol_poly_with_iss
         pol_source before_scop)
      (FunctorCore.try_post_tiling_affine_phase_pipeline_from_source_pol_poly_with_iss
         pol_source before_scop).
Proof.
  intros pol_source before_scop.
  unfold
    SParallelPolOpt.try_post_tiling_affine_phase_pipeline_from_source_pol_poly_with_iss,
    FunctorCore.try_post_tiling_affine_phase_pipeline_from_source_pol_poly_with_iss.
  destruct
    (FunctorCore.CoreOpt.run_pluto_post_tiling_affine_phase_pipeline_with_iss before_scop)
    as [[mid_scop [posttile_scop after_scop]]|]; [|reflexivity].
  destruct
    (SPolIRs.PolyLang.from_openscop_schedule_only pol_source mid_scop)
    as [pol_mid|]; [|reflexivity].
  apply bind_eq_compat; [reflexivity|].
  intros affine_ok. destruct affine_ok.
  - apply try_verified_post_tiling_affine_after_phase_mid_poly_impeq.
  - reflexivity.
Qed.

Lemma try_checked_iss_phase_pipeline_from_poly_poly_impeq :
  forall pol before_scop,
    impeq
      (SParallelPolOpt.try_checked_iss_phase_pipeline_from_poly_poly
         pol before_scop)
      (FunctorCore.try_checked_iss_phase_pipeline_from_poly_poly
         pol before_scop).
Proof.
  intros pol before_scop.
  unfold SParallelPolOpt.try_checked_iss_phase_pipeline_from_poly_poly,
    FunctorCore.try_checked_iss_phase_pipeline_from_poly_poly.
  destruct (FunctorCore.CoreOpt.infer_iss_from_source_scop pol before_scop)
    as [iss_result|].
  - destruct iss_result as [[pol_iss w]|].
    + destruct
        (FunctorCore.ValidatorCore.checked_iss_complete_cut_shape_validate
           pol pol_iss w).
      * apply bind_eq_compat; [reflexivity|].
        intros iss_wf. destruct iss_wf.
        -- destruct (FunctorCore.CoreOpt.export_for_phase_scheduler pol_iss).
           ++ apply try_phase_pipeline_from_source_pol_poly_impeq.
           ++ reflexivity.
        -- apply try_phase_pipeline_from_source_pol_poly_impeq.
      * apply try_phase_pipeline_from_source_pol_poly_impeq.
    + apply try_phase_pipeline_from_source_pol_poly_impeq.
  - apply try_phase_pipeline_from_source_pol_poly_impeq.
Qed.

Lemma try_checked_iss_post_tiling_affine_phase_pipeline_from_poly_poly_impeq :
  forall pol before_scop,
    impeq
      (SParallelPolOpt.try_checked_iss_post_tiling_affine_phase_pipeline_from_poly_poly
         pol before_scop)
      (FunctorCore.try_checked_iss_post_tiling_affine_phase_pipeline_from_poly_poly
         pol before_scop).
Proof.
  intros pol before_scop.
  unfold SParallelPolOpt.try_checked_iss_post_tiling_affine_phase_pipeline_from_poly_poly,
    FunctorCore.try_checked_iss_post_tiling_affine_phase_pipeline_from_poly_poly.
  destruct (FunctorCore.CoreOpt.infer_iss_from_source_scop pol before_scop)
    as [iss_result|].
  - destruct iss_result as [[pol_iss w]|].
    + destruct
        (FunctorCore.ValidatorCore.checked_iss_complete_cut_shape_validate
           pol pol_iss w).
      * apply bind_eq_compat; [reflexivity|].
        intros iss_wf. destruct iss_wf.
        -- destruct (FunctorCore.CoreOpt.export_for_phase_scheduler pol_iss).
           ++ apply try_post_tiling_affine_phase_pipeline_from_source_pol_poly_impeq.
           ++ reflexivity.
        -- apply try_post_tiling_affine_phase_pipeline_from_source_pol_poly_impeq.
      * apply try_post_tiling_affine_phase_pipeline_from_source_pol_poly_impeq.
    + apply try_post_tiling_affine_phase_pipeline_from_source_pol_poly_impeq.
  - apply try_post_tiling_affine_phase_pipeline_from_source_pol_poly_impeq.
Qed.

Lemma phase_pipeline_opt_prepared_from_poly_no_iss_poly_impeq :
  forall pol,
    impeq
      (SParallelPolOpt.phase_pipeline_opt_prepared_from_poly_no_iss_poly pol)
      (FunctorCore.phase_pipeline_opt_prepared_from_poly_no_iss_poly pol).
Proof.
  intros pol.
  unfold SParallelPolOpt.phase_pipeline_opt_prepared_from_poly_no_iss_poly,
    FunctorCore.phase_pipeline_opt_prepared_from_poly_no_iss_poly.
  destruct (FunctorCore.CoreOpt.has_nonscalar_stmt pol); [|reflexivity].
  destruct (FunctorCore.CoreOpt.export_for_phase_scheduler pol);
    [apply try_phase_pipeline_from_source_pol_poly_impeq|reflexivity].
Qed.

Lemma phase_pipeline_opt_prepared_from_poly_with_iss_poly_impeq :
  forall pol,
    impeq
      (SParallelPolOpt.phase_pipeline_opt_prepared_from_poly_with_iss_poly pol)
      (FunctorCore.phase_pipeline_opt_prepared_from_poly_with_iss_poly pol).
Proof.
  intros pol.
  unfold SParallelPolOpt.phase_pipeline_opt_prepared_from_poly_with_iss_poly,
    FunctorCore.phase_pipeline_opt_prepared_from_poly_with_iss_poly.
  destruct (FunctorCore.CoreOpt.has_nonscalar_stmt pol); [|reflexivity].
  destruct (FunctorCore.CoreOpt.export_for_phase_scheduler pol);
    [apply try_checked_iss_phase_pipeline_from_poly_poly_impeq|reflexivity].
Qed.

Lemma identity_tiling_opt_prepared_from_poly_no_iss_poly_impeq :
  forall pol,
    impeq
      (SParallelPolOpt.identity_tiling_opt_prepared_from_poly_no_iss_poly pol)
      (FunctorCore.identity_tiling_opt_prepared_from_poly_no_iss_poly pol).
Proof.
  intros pol.
  unfold SParallelPolOpt.identity_tiling_opt_prepared_from_poly_no_iss_poly,
    FunctorCore.identity_tiling_opt_prepared_from_poly_no_iss_poly.
  destruct (FunctorCore.CoreOpt.has_nonscalar_stmt pol); [|reflexivity].
  destruct (FunctorCore.CoreOpt.export_for_phase_scheduler pol);
    [apply try_identity_tiling_phase_pipeline_from_source_pol_poly_impeq
    |reflexivity].
Qed.

Lemma iss_only_prepared_from_poly_impeq :
  forall pol,
    impeq
      (SParallelPolOpt.iss_only_prepared_from_poly pol)
      (FunctorCore.iss_only_prepared_from_poly pol).
Proof. intros pol. reflexivity. Qed.

Lemma iss_affine_prepared_from_poly_impeq :
  forall pol,
    impeq
      (SParallelPolOpt.iss_affine_prepared_from_poly pol)
      (FunctorCore.iss_affine_prepared_from_poly pol).
Proof.
  intros pol.
  unfold SParallelPolOpt.iss_affine_prepared_from_poly,
    FunctorCore.iss_affine_prepared_from_poly.
  apply bind_eq_compat; [apply iss_only_prepared_from_poly_impeq|].
  intros pol_iss. reflexivity.
Qed.

Lemma identity_tiling_opt_prepared_from_poly_with_iss_poly_impeq :
  forall pol,
    impeq
      (SParallelPolOpt.identity_tiling_opt_prepared_from_poly_with_iss_poly pol)
      (FunctorCore.identity_tiling_opt_prepared_from_poly_with_iss_poly pol).
Proof.
  intros pol.
  unfold SParallelPolOpt.identity_tiling_opt_prepared_from_poly_with_iss_poly,
    FunctorCore.identity_tiling_opt_prepared_from_poly_with_iss_poly.
  apply bind_eq_compat; [apply iss_only_prepared_from_poly_impeq|].
  intros pol_iss.
  apply identity_tiling_opt_prepared_from_poly_no_iss_poly_impeq.
Qed.

Lemma post_tiling_affine_phase_pipeline_opt_prepared_from_poly_no_iss_poly_impeq :
  forall pol,
    impeq
      (SParallelPolOpt.post_tiling_affine_phase_pipeline_opt_prepared_from_poly_no_iss_poly
         pol)
      (FunctorCore.post_tiling_affine_phase_pipeline_opt_prepared_from_poly_no_iss_poly
         pol).
Proof.
  intros pol.
  unfold
    SParallelPolOpt.post_tiling_affine_phase_pipeline_opt_prepared_from_poly_no_iss_poly,
    FunctorCore.post_tiling_affine_phase_pipeline_opt_prepared_from_poly_no_iss_poly.
  destruct (FunctorCore.CoreOpt.has_nonscalar_stmt pol); [|reflexivity].
  destruct (FunctorCore.CoreOpt.export_for_phase_scheduler pol);
    [apply try_post_tiling_affine_phase_pipeline_from_source_pol_poly_impeq|reflexivity].
Qed.

Lemma post_tiling_affine_phase_pipeline_opt_prepared_from_poly_with_iss_poly_impeq :
  forall pol,
    impeq
      (SParallelPolOpt.post_tiling_affine_phase_pipeline_opt_prepared_from_poly_with_iss_poly
         pol)
      (FunctorCore.post_tiling_affine_phase_pipeline_opt_prepared_from_poly_with_iss_poly
         pol).
Proof.
  intros pol.
  unfold
    SParallelPolOpt.post_tiling_affine_phase_pipeline_opt_prepared_from_poly_with_iss_poly,
    FunctorCore.post_tiling_affine_phase_pipeline_opt_prepared_from_poly_with_iss_poly.
  destruct (FunctorCore.CoreOpt.has_nonscalar_stmt pol); [|reflexivity].
  destruct (FunctorCore.CoreOpt.export_for_phase_scheduler pol).
  - apply try_checked_iss_post_tiling_affine_phase_pipeline_from_poly_poly_impeq.
  - reflexivity.
Qed.

Ltac prepared_bind bridge :=
  apply bind_eq_compat; [apply bridge|]; intros; reflexivity.

Lemma parallel_current_identity_prepared_from_poly_impeq :
  forall pol d,
    impeq
      (SParallelPolOpt.parallel_current_identity_prepared_from_poly pol d)
      (FunctorCore.parallel_current_identity_prepared_from_poly pol d).
Proof. intros pol d. reflexivity. Qed.

Lemma parallel_current_affine_prepared_from_poly_impeq :
  forall pol d,
    impeq
      (SParallelPolOpt.parallel_current_affine_prepared_from_poly pol d)
      (FunctorCore.parallel_current_affine_prepared_from_poly pol d).
Proof. intros pol d. reflexivity. Qed.

Lemma parallel_current_prepared_from_poly_impeq :
  forall pol d,
    impeq
      (SParallelPolOpt.parallel_current_prepared_from_poly pol d)
      (FunctorCore.parallel_current_prepared_from_poly pol d).
Proof.
  intros pol d; unfold SParallelPolOpt.parallel_current_prepared_from_poly,
    FunctorCore.parallel_current_prepared_from_poly.
  prepared_bind phase_pipeline_opt_prepared_from_poly_no_iss_poly_impeq.
Qed.

Lemma parallel_current_identity_tiled_prepared_from_poly_impeq :
  forall pol d,
    impeq
      (SParallelPolOpt.parallel_current_identity_tiled_prepared_from_poly pol d)
      (FunctorCore.parallel_current_identity_tiled_prepared_from_poly pol d).
Proof.
  intros pol d;
    unfold SParallelPolOpt.parallel_current_identity_tiled_prepared_from_poly,
      FunctorCore.parallel_current_identity_tiled_prepared_from_poly.
  prepared_bind identity_tiling_opt_prepared_from_poly_no_iss_poly_impeq.
Qed.

Lemma parallel_current_identity_tiled_prepared_from_poly_with_iss_impeq :
  forall pol d,
    impeq
      (SParallelPolOpt.parallel_current_identity_tiled_prepared_from_poly_with_iss
         pol d)
      (FunctorCore.parallel_current_identity_tiled_prepared_from_poly_with_iss
         pol d).
Proof.
  intros pol d;
    unfold
      SParallelPolOpt.parallel_current_identity_tiled_prepared_from_poly_with_iss,
      FunctorCore.parallel_current_identity_tiled_prepared_from_poly_with_iss.
  prepared_bind identity_tiling_opt_prepared_from_poly_with_iss_poly_impeq.
Qed.

Lemma parallel_current_post_tiling_affine_prepared_from_poly_impeq :
  forall pol d,
    impeq
      (SParallelPolOpt.parallel_current_post_tiling_affine_prepared_from_poly pol d)
      (FunctorCore.parallel_current_post_tiling_affine_prepared_from_poly pol d).
Proof.
  intros pol d; unfold SParallelPolOpt.parallel_current_post_tiling_affine_prepared_from_poly,
    FunctorCore.parallel_current_post_tiling_affine_prepared_from_poly.
  prepared_bind post_tiling_affine_phase_pipeline_opt_prepared_from_poly_no_iss_poly_impeq.
Qed.

Lemma parallel_current_post_tiling_affine_prepared_from_poly_with_iss_impeq :
  forall pol d,
    impeq
      (SParallelPolOpt.parallel_current_post_tiling_affine_prepared_from_poly_with_iss pol d)
      (FunctorCore.parallel_current_post_tiling_affine_prepared_from_poly_with_iss pol d).
Proof.
  intros pol d;
    unfold SParallelPolOpt.parallel_current_post_tiling_affine_prepared_from_poly_with_iss,
      FunctorCore.parallel_current_post_tiling_affine_prepared_from_poly_with_iss.
  prepared_bind post_tiling_affine_phase_pipeline_opt_prepared_from_poly_with_iss_poly_impeq.
Qed.

Lemma parallel_current_identity_prepared_from_poly_with_iss_impeq :
  forall pol d,
    impeq
      (SParallelPolOpt.parallel_current_identity_prepared_from_poly_with_iss pol d)
      (FunctorCore.parallel_current_identity_prepared_from_poly_with_iss pol d).
Proof.
  intros pol d;
    unfold SParallelPolOpt.parallel_current_identity_prepared_from_poly_with_iss,
      FunctorCore.parallel_current_identity_prepared_from_poly_with_iss.
  prepared_bind iss_only_prepared_from_poly_impeq.
Qed.

Lemma parallel_current_affine_prepared_from_poly_with_iss_impeq :
  forall pol d,
    impeq
      (SParallelPolOpt.parallel_current_affine_prepared_from_poly_with_iss pol d)
      (FunctorCore.parallel_current_affine_prepared_from_poly_with_iss pol d).
Proof.
  intros pol d;
    unfold SParallelPolOpt.parallel_current_affine_prepared_from_poly_with_iss,
      FunctorCore.parallel_current_affine_prepared_from_poly_with_iss.
  prepared_bind iss_affine_prepared_from_poly_impeq.
Qed.

Lemma parallel_current_prepared_from_poly_with_iss_impeq :
  forall pol d,
    impeq
      (SParallelPolOpt.parallel_current_prepared_from_poly_with_iss pol d)
      (FunctorCore.parallel_current_prepared_from_poly_with_iss pol d).
Proof.
  intros pol d;
    unfold SParallelPolOpt.parallel_current_prepared_from_poly_with_iss,
      FunctorCore.parallel_current_prepared_from_poly_with_iss.
  prepared_bind phase_pipeline_opt_prepared_from_poly_with_iss_poly_impeq.
Qed.

Lemma parallel_current_many_identity_tiled_prepared_from_poly_impeq :
  forall pol dims,
    impeq
      (SParallelPolOpt.parallel_current_many_identity_tiled_prepared_from_poly
         pol dims)
      (FunctorCore.parallel_current_many_identity_tiled_prepared_from_poly
         pol dims).
Proof.
  intros pol dims;
    unfold
      SParallelPolOpt.parallel_current_many_identity_tiled_prepared_from_poly,
      FunctorCore.parallel_current_many_identity_tiled_prepared_from_poly.
  prepared_bind identity_tiling_opt_prepared_from_poly_no_iss_poly_impeq.
Qed.

Lemma parallel_current_many_identity_prepared_from_poly_impeq :
  forall pol dims,
    impeq
      (SParallelPolOpt.parallel_current_many_identity_prepared_from_poly pol dims)
      (FunctorCore.parallel_current_many_identity_prepared_from_poly pol dims).
Proof. intros pol dims. reflexivity. Qed.

Lemma parallel_current_many_affine_prepared_from_poly_impeq :
  forall pol dims,
    impeq
      (SParallelPolOpt.parallel_current_many_affine_prepared_from_poly pol dims)
      (FunctorCore.parallel_current_many_affine_prepared_from_poly pol dims).
Proof. intros pol dims. reflexivity. Qed.

Lemma parallel_current_many_identity_tiled_prepared_from_poly_with_iss_impeq :
  forall pol dims,
    impeq
      (SParallelPolOpt.parallel_current_many_identity_tiled_prepared_from_poly_with_iss
         pol dims)
      (FunctorCore.parallel_current_many_identity_tiled_prepared_from_poly_with_iss
         pol dims).
Proof.
  intros pol dims;
    unfold
      SParallelPolOpt.parallel_current_many_identity_tiled_prepared_from_poly_with_iss,
      FunctorCore.parallel_current_many_identity_tiled_prepared_from_poly_with_iss.
  prepared_bind identity_tiling_opt_prepared_from_poly_with_iss_poly_impeq.
Qed.

Lemma parallel_current_many_prepared_from_poly_impeq :
  forall pol dims,
    impeq
      (SParallelPolOpt.parallel_current_many_prepared_from_poly pol dims)
      (FunctorCore.parallel_current_many_prepared_from_poly pol dims).
Proof.
  intros pol dims; unfold SParallelPolOpt.parallel_current_many_prepared_from_poly,
    FunctorCore.parallel_current_many_prepared_from_poly.
  prepared_bind phase_pipeline_opt_prepared_from_poly_no_iss_poly_impeq.
Qed.

Lemma parallel_current_many_post_tiling_affine_prepared_from_poly_impeq :
  forall pol dims,
    impeq
      (SParallelPolOpt.parallel_current_many_post_tiling_affine_prepared_from_poly pol dims)
      (FunctorCore.parallel_current_many_post_tiling_affine_prepared_from_poly pol dims).
Proof.
  intros pol dims;
    unfold SParallelPolOpt.parallel_current_many_post_tiling_affine_prepared_from_poly,
      FunctorCore.parallel_current_many_post_tiling_affine_prepared_from_poly.
  prepared_bind post_tiling_affine_phase_pipeline_opt_prepared_from_poly_no_iss_poly_impeq.
Qed.

Lemma parallel_current_many_post_tiling_affine_prepared_from_poly_with_iss_impeq :
  forall pol dims,
    impeq
      (SParallelPolOpt.parallel_current_many_post_tiling_affine_prepared_from_poly_with_iss
         pol dims)
      (FunctorCore.parallel_current_many_post_tiling_affine_prepared_from_poly_with_iss
         pol dims).
Proof.
  intros pol dims;
    unfold
      SParallelPolOpt.parallel_current_many_post_tiling_affine_prepared_from_poly_with_iss,
      FunctorCore.parallel_current_many_post_tiling_affine_prepared_from_poly_with_iss.
  prepared_bind post_tiling_affine_phase_pipeline_opt_prepared_from_poly_with_iss_poly_impeq.
Qed.

Lemma parallel_current_many_identity_prepared_from_poly_with_iss_impeq :
  forall pol dims,
    impeq
      (SParallelPolOpt.parallel_current_many_identity_prepared_from_poly_with_iss
         pol dims)
      (FunctorCore.parallel_current_many_identity_prepared_from_poly_with_iss
         pol dims).
Proof.
  intros pol dims;
    unfold
      SParallelPolOpt.parallel_current_many_identity_prepared_from_poly_with_iss,
      FunctorCore.parallel_current_many_identity_prepared_from_poly_with_iss.
  prepared_bind iss_only_prepared_from_poly_impeq.
Qed.

Lemma parallel_current_many_affine_prepared_from_poly_with_iss_impeq :
  forall pol dims,
    impeq
      (SParallelPolOpt.parallel_current_many_affine_prepared_from_poly_with_iss
         pol dims)
      (FunctorCore.parallel_current_many_affine_prepared_from_poly_with_iss
         pol dims).
Proof.
  intros pol dims;
    unfold
      SParallelPolOpt.parallel_current_many_affine_prepared_from_poly_with_iss,
      FunctorCore.parallel_current_many_affine_prepared_from_poly_with_iss.
  prepared_bind iss_affine_prepared_from_poly_impeq.
Qed.

Lemma parallel_current_many_prepared_from_poly_with_iss_impeq :
  forall pol dims,
    impeq
      (SParallelPolOpt.parallel_current_many_prepared_from_poly_with_iss pol dims)
      (FunctorCore.parallel_current_many_prepared_from_poly_with_iss pol dims).
Proof.
  intros pol dims;
    unfold SParallelPolOpt.parallel_current_many_prepared_from_poly_with_iss,
      FunctorCore.parallel_current_many_prepared_from_poly_with_iss.
  prepared_bind phase_pipeline_opt_prepared_from_poly_with_iss_poly_impeq.
Qed.

Lemma vector_current_prepared_from_poly_impeq :
  forall pol d,
    impeq
      (SParallelPolOpt.vector_current_prepared_from_poly pol d)
      (FunctorCore.vector_current_prepared_from_poly pol d).
Proof.
  intros pol d; unfold SParallelPolOpt.vector_current_prepared_from_poly,
    FunctorCore.vector_current_prepared_from_poly.
  prepared_bind phase_pipeline_opt_prepared_from_poly_no_iss_poly_impeq.
Qed.

Lemma vector_current_identity_prepared_from_poly_impeq :
  forall pol d,
    impeq
      (SParallelPolOpt.vector_current_identity_prepared_from_poly pol d)
      (FunctorCore.vector_current_identity_prepared_from_poly pol d).
Proof. intros pol d. reflexivity. Qed.

Lemma vector_current_affine_prepared_from_poly_impeq :
  forall pol d,
    impeq
      (SParallelPolOpt.vector_current_affine_prepared_from_poly pol d)
      (FunctorCore.vector_current_affine_prepared_from_poly pol d).
Proof. intros pol d. reflexivity. Qed.

Lemma vector_current_identity_tiled_prepared_from_poly_impeq :
  forall pol d,
    impeq
      (SParallelPolOpt.vector_current_identity_tiled_prepared_from_poly pol d)
      (FunctorCore.vector_current_identity_tiled_prepared_from_poly pol d).
Proof.
  intros pol d;
    unfold SParallelPolOpt.vector_current_identity_tiled_prepared_from_poly,
      FunctorCore.vector_current_identity_tiled_prepared_from_poly.
  prepared_bind identity_tiling_opt_prepared_from_poly_no_iss_poly_impeq.
Qed.

Lemma vector_current_identity_tiled_prepared_from_poly_with_iss_impeq :
  forall pol d,
    impeq
      (SParallelPolOpt.vector_current_identity_tiled_prepared_from_poly_with_iss
         pol d)
      (FunctorCore.vector_current_identity_tiled_prepared_from_poly_with_iss
         pol d).
Proof.
  intros pol d;
    unfold
      SParallelPolOpt.vector_current_identity_tiled_prepared_from_poly_with_iss,
      FunctorCore.vector_current_identity_tiled_prepared_from_poly_with_iss.
  prepared_bind identity_tiling_opt_prepared_from_poly_with_iss_poly_impeq.
Qed.

Lemma vector_current_post_tiling_affine_prepared_from_poly_impeq :
  forall pol d,
    impeq
      (SParallelPolOpt.vector_current_post_tiling_affine_prepared_from_poly pol d)
      (FunctorCore.vector_current_post_tiling_affine_prepared_from_poly pol d).
Proof.
  intros pol d; unfold SParallelPolOpt.vector_current_post_tiling_affine_prepared_from_poly,
    FunctorCore.vector_current_post_tiling_affine_prepared_from_poly.
  prepared_bind post_tiling_affine_phase_pipeline_opt_prepared_from_poly_no_iss_poly_impeq.
Qed.

Lemma vector_current_post_tiling_affine_prepared_from_poly_with_iss_impeq :
  forall pol d,
    impeq
      (SParallelPolOpt.vector_current_post_tiling_affine_prepared_from_poly_with_iss pol d)
      (FunctorCore.vector_current_post_tiling_affine_prepared_from_poly_with_iss pol d).
Proof.
  intros pol d;
    unfold SParallelPolOpt.vector_current_post_tiling_affine_prepared_from_poly_with_iss,
      FunctorCore.vector_current_post_tiling_affine_prepared_from_poly_with_iss.
  prepared_bind post_tiling_affine_phase_pipeline_opt_prepared_from_poly_with_iss_poly_impeq.
Qed.

Lemma vector_current_identity_prepared_from_poly_with_iss_impeq :
  forall pol d,
    impeq
      (SParallelPolOpt.vector_current_identity_prepared_from_poly_with_iss pol d)
      (FunctorCore.vector_current_identity_prepared_from_poly_with_iss pol d).
Proof.
  intros pol d;
    unfold SParallelPolOpt.vector_current_identity_prepared_from_poly_with_iss,
      FunctorCore.vector_current_identity_prepared_from_poly_with_iss.
  prepared_bind iss_only_prepared_from_poly_impeq.
Qed.

Lemma vector_current_affine_prepared_from_poly_with_iss_impeq :
  forall pol d,
    impeq
      (SParallelPolOpt.vector_current_affine_prepared_from_poly_with_iss pol d)
      (FunctorCore.vector_current_affine_prepared_from_poly_with_iss pol d).
Proof.
  intros pol d;
    unfold SParallelPolOpt.vector_current_affine_prepared_from_poly_with_iss,
      FunctorCore.vector_current_affine_prepared_from_poly_with_iss.
  prepared_bind iss_affine_prepared_from_poly_impeq.
Qed.

Lemma vector_current_prepared_from_poly_with_iss_impeq :
  forall pol d,
    impeq
      (SParallelPolOpt.vector_current_prepared_from_poly_with_iss pol d)
      (FunctorCore.vector_current_prepared_from_poly_with_iss pol d).
Proof.
  intros pol d;
    unfold SParallelPolOpt.vector_current_prepared_from_poly_with_iss,
      FunctorCore.vector_current_prepared_from_poly_with_iss.
  prepared_bind phase_pipeline_opt_prepared_from_poly_with_iss_poly_impeq.
Qed.

Ltac prove_entry_impeq concrete_entry functor_entry functor_result prepared :=
  intros loop arg;
  unfold concrete_entry, functor_entry, functor_result;
  apply entry_bind_assoc_compat;
  intros pol0;
  apply prepared.

Lemma opt_parallel_current_identity_impeq :
  forall loop d,
    impeq
      (SParallelPolOpt.opt_parallel_current_identity loop d)
      (FunctorCore.Opt_parallel_current_identity loop d).
Proof.
  prove_entry_impeq SParallelPolOpt.opt_parallel_current_identity
    FunctorCore.Opt_parallel_current_identity
    FunctorCore.Opt_parallel_current_identity_result
    parallel_current_identity_prepared_from_poly_impeq.
Qed.

Lemma opt_parallel_current_identity_tiled_impeq :
  forall loop d,
    impeq
      (SParallelPolOpt.opt_parallel_current_identity_tiled loop d)
      (FunctorCore.Opt_parallel_current_identity_tiled loop d).
Proof.
  prove_entry_impeq SParallelPolOpt.opt_parallel_current_identity_tiled
    FunctorCore.Opt_parallel_current_identity_tiled
    FunctorCore.Opt_parallel_current_identity_tiled_result
    parallel_current_identity_tiled_prepared_from_poly_impeq.
Qed.

Lemma opt_parallel_current_identity_tiled_with_iss_impeq :
  forall loop d,
    impeq
      (SParallelPolOpt.opt_parallel_current_identity_tiled_with_iss loop d)
      (FunctorCore.Opt_parallel_current_identity_tiled_with_iss loop d).
Proof.
  prove_entry_impeq SParallelPolOpt.opt_parallel_current_identity_tiled_with_iss
    FunctorCore.Opt_parallel_current_identity_tiled_with_iss
    FunctorCore.Opt_parallel_current_identity_tiled_with_iss_result
    parallel_current_identity_tiled_prepared_from_poly_with_iss_impeq.
Qed.

Lemma opt_parallel_current_affine_impeq :
  forall loop d,
    impeq
      (SParallelPolOpt.opt_parallel_current_affine loop d)
      (FunctorCore.Opt_parallel_current_affine loop d).
Proof.
  prove_entry_impeq SParallelPolOpt.opt_parallel_current_affine
    FunctorCore.Opt_parallel_current_affine
    FunctorCore.Opt_parallel_current_affine_result
    parallel_current_affine_prepared_from_poly_impeq.
Qed.

Lemma opt_parallel_current_impeq :
  forall loop d,
    impeq
      (SParallelPolOpt.opt_parallel_current loop d)
      (FunctorCore.Opt_parallel_current loop d).
Proof.
  prove_entry_impeq SParallelPolOpt.opt_parallel_current
    FunctorCore.Opt_parallel_current
    FunctorCore.Opt_parallel_current_result
    parallel_current_prepared_from_poly_impeq.
Qed.

Lemma opt_parallel_current_post_tiling_affine_impeq :
  forall loop d,
    impeq
      (SParallelPolOpt.opt_parallel_current_post_tiling_affine loop d)
      (FunctorCore.Opt_parallel_current_post_tiling_affine loop d).
Proof.
  prove_entry_impeq SParallelPolOpt.opt_parallel_current_post_tiling_affine
    FunctorCore.Opt_parallel_current_post_tiling_affine
    FunctorCore.Opt_parallel_current_post_tiling_affine_result
    parallel_current_post_tiling_affine_prepared_from_poly_impeq.
Qed.

Lemma opt_parallel_current_post_tiling_affine_with_iss_impeq :
  forall loop d,
    impeq
      (SParallelPolOpt.opt_parallel_current_post_tiling_affine_with_iss loop d)
      (FunctorCore.Opt_parallel_current_post_tiling_affine_with_iss loop d).
Proof.
  prove_entry_impeq SParallelPolOpt.opt_parallel_current_post_tiling_affine_with_iss
    FunctorCore.Opt_parallel_current_post_tiling_affine_with_iss
    FunctorCore.Opt_parallel_current_post_tiling_affine_with_iss_result
    parallel_current_post_tiling_affine_prepared_from_poly_with_iss_impeq.
Qed.

Lemma opt_parallel_current_identity_with_iss_impeq :
  forall loop d,
    impeq
      (SParallelPolOpt.opt_parallel_current_identity_with_iss loop d)
      (FunctorCore.Opt_parallel_current_identity_with_iss loop d).
Proof.
  prove_entry_impeq SParallelPolOpt.opt_parallel_current_identity_with_iss
    FunctorCore.Opt_parallel_current_identity_with_iss
    FunctorCore.Opt_parallel_current_identity_with_iss_result
    parallel_current_identity_prepared_from_poly_with_iss_impeq.
Qed.

Lemma opt_parallel_current_affine_with_iss_impeq :
  forall loop d,
    impeq
      (SParallelPolOpt.opt_parallel_current_affine_with_iss loop d)
      (FunctorCore.Opt_parallel_current_affine_with_iss loop d).
Proof.
  prove_entry_impeq SParallelPolOpt.opt_parallel_current_affine_with_iss
    FunctorCore.Opt_parallel_current_affine_with_iss
    FunctorCore.Opt_parallel_current_affine_with_iss_result
    parallel_current_affine_prepared_from_poly_with_iss_impeq.
Qed.

Lemma opt_parallel_current_with_iss_impeq :
  forall loop d,
    impeq
      (SParallelPolOpt.opt_parallel_current_with_iss loop d)
      (FunctorCore.Opt_parallel_current_with_iss loop d).
Proof.
  prove_entry_impeq SParallelPolOpt.opt_parallel_current_with_iss
    FunctorCore.Opt_parallel_current_with_iss
    FunctorCore.Opt_parallel_current_with_iss_result
    parallel_current_prepared_from_poly_with_iss_impeq.
Qed.

Lemma opt_vector_current_identity_impeq :
  forall loop d,
    impeq
      (SParallelPolOpt.opt_vector_current_identity loop d)
      (FunctorCore.Opt_vector_current_identity loop d).
Proof.
  prove_entry_impeq SParallelPolOpt.opt_vector_current_identity
    FunctorCore.Opt_vector_current_identity
    FunctorCore.Opt_vector_current_identity_result
    vector_current_identity_prepared_from_poly_impeq.
Qed.

Lemma opt_vector_current_identity_tiled_impeq :
  forall loop d,
    impeq
      (SParallelPolOpt.opt_vector_current_identity_tiled loop d)
      (FunctorCore.Opt_vector_current_identity_tiled loop d).
Proof.
  prove_entry_impeq SParallelPolOpt.opt_vector_current_identity_tiled
    FunctorCore.Opt_vector_current_identity_tiled
    FunctorCore.Opt_vector_current_identity_tiled_result
    vector_current_identity_tiled_prepared_from_poly_impeq.
Qed.

Lemma opt_vector_current_identity_tiled_with_iss_impeq :
  forall loop d,
    impeq
      (SParallelPolOpt.opt_vector_current_identity_tiled_with_iss loop d)
      (FunctorCore.Opt_vector_current_identity_tiled_with_iss loop d).
Proof.
  prove_entry_impeq SParallelPolOpt.opt_vector_current_identity_tiled_with_iss
    FunctorCore.Opt_vector_current_identity_tiled_with_iss
    FunctorCore.Opt_vector_current_identity_tiled_with_iss_result
    vector_current_identity_tiled_prepared_from_poly_with_iss_impeq.
Qed.

Lemma opt_vector_current_affine_impeq :
  forall loop d,
    impeq
      (SParallelPolOpt.opt_vector_current_affine loop d)
      (FunctorCore.Opt_vector_current_affine loop d).
Proof.
  prove_entry_impeq SParallelPolOpt.opt_vector_current_affine
    FunctorCore.Opt_vector_current_affine
    FunctorCore.Opt_vector_current_affine_result
    vector_current_affine_prepared_from_poly_impeq.
Qed.

Lemma opt_vector_current_impeq :
  forall loop d,
    impeq
      (SParallelPolOpt.opt_vector_current loop d)
      (FunctorCore.Opt_vector_current loop d).
Proof.
  prove_entry_impeq SParallelPolOpt.opt_vector_current
    FunctorCore.Opt_vector_current
    FunctorCore.Opt_vector_current_result
    vector_current_prepared_from_poly_impeq.
Qed.

Lemma opt_vector_current_post_tiling_affine_impeq :
  forall loop d,
    impeq
      (SParallelPolOpt.opt_vector_current_post_tiling_affine loop d)
      (FunctorCore.Opt_vector_current_post_tiling_affine loop d).
Proof.
  prove_entry_impeq SParallelPolOpt.opt_vector_current_post_tiling_affine
    FunctorCore.Opt_vector_current_post_tiling_affine
    FunctorCore.Opt_vector_current_post_tiling_affine_result
    vector_current_post_tiling_affine_prepared_from_poly_impeq.
Qed.

Lemma opt_vector_current_post_tiling_affine_with_iss_impeq :
  forall loop d,
    impeq
      (SParallelPolOpt.opt_vector_current_post_tiling_affine_with_iss loop d)
      (FunctorCore.Opt_vector_current_post_tiling_affine_with_iss loop d).
Proof.
  prove_entry_impeq SParallelPolOpt.opt_vector_current_post_tiling_affine_with_iss
    FunctorCore.Opt_vector_current_post_tiling_affine_with_iss
    FunctorCore.Opt_vector_current_post_tiling_affine_with_iss_result
    vector_current_post_tiling_affine_prepared_from_poly_with_iss_impeq.
Qed.

Lemma opt_vector_current_identity_with_iss_impeq :
  forall loop d,
    impeq
      (SParallelPolOpt.opt_vector_current_identity_with_iss loop d)
      (FunctorCore.Opt_vector_current_identity_with_iss loop d).
Proof.
  prove_entry_impeq SParallelPolOpt.opt_vector_current_identity_with_iss
    FunctorCore.Opt_vector_current_identity_with_iss
    FunctorCore.Opt_vector_current_identity_with_iss_result
    vector_current_identity_prepared_from_poly_with_iss_impeq.
Qed.

Lemma opt_vector_current_affine_with_iss_impeq :
  forall loop d,
    impeq
      (SParallelPolOpt.opt_vector_current_affine_with_iss loop d)
      (FunctorCore.Opt_vector_current_affine_with_iss loop d).
Proof.
  prove_entry_impeq SParallelPolOpt.opt_vector_current_affine_with_iss
    FunctorCore.Opt_vector_current_affine_with_iss
    FunctorCore.Opt_vector_current_affine_with_iss_result
    vector_current_affine_prepared_from_poly_with_iss_impeq.
Qed.

Lemma opt_vector_current_with_iss_impeq :
  forall loop d,
    impeq
      (SParallelPolOpt.opt_vector_current_with_iss loop d)
      (FunctorCore.Opt_vector_current_with_iss loop d).
Proof.
  prove_entry_impeq SParallelPolOpt.opt_vector_current_with_iss
    FunctorCore.Opt_vector_current_with_iss
    FunctorCore.Opt_vector_current_with_iss_result
    vector_current_prepared_from_poly_with_iss_impeq.
Qed.

Lemma opt_parallel_current_many_identity_impeq :
  forall loop dims,
    impeq
      (SParallelPolOpt.opt_parallel_current_many_identity loop dims)
      (FunctorCore.Opt_parallel_current_many_identity loop dims).
Proof.
  prove_entry_impeq SParallelPolOpt.opt_parallel_current_many_identity
    FunctorCore.Opt_parallel_current_many_identity
    FunctorCore.Opt_parallel_current_many_identity_result
    parallel_current_many_identity_prepared_from_poly_impeq.
Qed.

Lemma opt_parallel_current_many_identity_tiled_impeq :
  forall loop dims,
    impeq
      (SParallelPolOpt.opt_parallel_current_many_identity_tiled loop dims)
      (FunctorCore.Opt_parallel_current_many_identity_tiled loop dims).
Proof.
  prove_entry_impeq SParallelPolOpt.opt_parallel_current_many_identity_tiled
    FunctorCore.Opt_parallel_current_many_identity_tiled
    FunctorCore.Opt_parallel_current_many_identity_tiled_result
    parallel_current_many_identity_tiled_prepared_from_poly_impeq.
Qed.

Lemma opt_parallel_current_many_identity_tiled_with_iss_impeq :
  forall loop dims,
    impeq
      (SParallelPolOpt.opt_parallel_current_many_identity_tiled_with_iss
         loop dims)
      (FunctorCore.Opt_parallel_current_many_identity_tiled_with_iss loop dims).
Proof.
  prove_entry_impeq
    SParallelPolOpt.opt_parallel_current_many_identity_tiled_with_iss
    FunctorCore.Opt_parallel_current_many_identity_tiled_with_iss
    FunctorCore.Opt_parallel_current_many_identity_tiled_with_iss_result
    parallel_current_many_identity_tiled_prepared_from_poly_with_iss_impeq.
Qed.

Lemma opt_parallel_current_many_affine_impeq :
  forall loop dims,
    impeq
      (SParallelPolOpt.opt_parallel_current_many_affine loop dims)
      (FunctorCore.Opt_parallel_current_many_affine loop dims).
Proof.
  prove_entry_impeq SParallelPolOpt.opt_parallel_current_many_affine
    FunctorCore.Opt_parallel_current_many_affine
    FunctorCore.Opt_parallel_current_many_affine_result
    parallel_current_many_affine_prepared_from_poly_impeq.
Qed.

Lemma opt_parallel_current_many_impeq :
  forall loop dims,
    impeq
      (SParallelPolOpt.opt_parallel_current_many loop dims)
      (FunctorCore.Opt_parallel_current_many loop dims).
Proof.
  prove_entry_impeq SParallelPolOpt.opt_parallel_current_many
    FunctorCore.Opt_parallel_current_many
    FunctorCore.Opt_parallel_current_many_result
    parallel_current_many_prepared_from_poly_impeq.
Qed.

Lemma opt_parallel_current_many_post_tiling_affine_impeq :
  forall loop dims,
    impeq
      (SParallelPolOpt.opt_parallel_current_many_post_tiling_affine loop dims)
      (FunctorCore.Opt_parallel_current_many_post_tiling_affine loop dims).
Proof.
  prove_entry_impeq SParallelPolOpt.opt_parallel_current_many_post_tiling_affine
    FunctorCore.Opt_parallel_current_many_post_tiling_affine
    FunctorCore.Opt_parallel_current_many_post_tiling_affine_result
    parallel_current_many_post_tiling_affine_prepared_from_poly_impeq.
Qed.

Lemma opt_parallel_current_many_post_tiling_affine_with_iss_impeq :
  forall loop dims,
    impeq
      (SParallelPolOpt.opt_parallel_current_many_post_tiling_affine_with_iss loop dims)
      (FunctorCore.Opt_parallel_current_many_post_tiling_affine_with_iss loop dims).
Proof.
  prove_entry_impeq SParallelPolOpt.opt_parallel_current_many_post_tiling_affine_with_iss
    FunctorCore.Opt_parallel_current_many_post_tiling_affine_with_iss
    FunctorCore.Opt_parallel_current_many_post_tiling_affine_with_iss_result
    parallel_current_many_post_tiling_affine_prepared_from_poly_with_iss_impeq.
Qed.

Lemma opt_parallel_current_many_identity_with_iss_impeq :
  forall loop dims,
    impeq
      (SParallelPolOpt.opt_parallel_current_many_identity_with_iss loop dims)
      (FunctorCore.Opt_parallel_current_many_identity_with_iss loop dims).
Proof.
  prove_entry_impeq SParallelPolOpt.opt_parallel_current_many_identity_with_iss
    FunctorCore.Opt_parallel_current_many_identity_with_iss
    FunctorCore.Opt_parallel_current_many_identity_with_iss_result
    parallel_current_many_identity_prepared_from_poly_with_iss_impeq.
Qed.

Lemma opt_parallel_current_many_affine_with_iss_impeq :
  forall loop dims,
    impeq
      (SParallelPolOpt.opt_parallel_current_many_affine_with_iss loop dims)
      (FunctorCore.Opt_parallel_current_many_affine_with_iss loop dims).
Proof.
  prove_entry_impeq SParallelPolOpt.opt_parallel_current_many_affine_with_iss
    FunctorCore.Opt_parallel_current_many_affine_with_iss
    FunctorCore.Opt_parallel_current_many_affine_with_iss_result
    parallel_current_many_affine_prepared_from_poly_with_iss_impeq.
Qed.

Lemma opt_parallel_current_many_with_iss_impeq :
  forall loop dims,
    impeq
      (SParallelPolOpt.opt_parallel_current_many_with_iss loop dims)
      (FunctorCore.Opt_parallel_current_many_with_iss loop dims).
Proof.
  prove_entry_impeq SParallelPolOpt.opt_parallel_current_many_with_iss
    FunctorCore.Opt_parallel_current_many_with_iss
    FunctorCore.Opt_parallel_current_many_with_iss_result
    parallel_current_many_prepared_from_poly_with_iss_impeq.
Qed.

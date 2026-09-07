Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Require Import PolOptBandTiling.
Require Import SBandTilingOpt.
Require Import SBandTilingOptShared.
Require Import SPolIRs.
Require Import STilingBandSched.

Local Open Scope impure_scope.

Module BandGeneric := SBandTilingOptShared.BandGeneric.

(** The executable [SBandTilingOpt] module is hand-instantiated so extraction
    exposes stable concrete names.  Correctness is proved once for the generic
    [BandGeneric] functor.  This file proves [impeq] correspondence between the
    two implementations, branch by branch; it does not re-prove tiling
    semantics.  The final [opt_*_impeq_generic] theorems are the only bridge
    facts needed by the extracted pipeline proof. *)

Lemma impeq_refl {A : Type} (x : imp A) : impeq x x.
Proof.
  exact (@Equivalence_Reflexive _ _ (impeq_equiv A) x).
Qed.

Lemma reject_tiling_impeq_generic :
  impeq
    (SBandTilingOpt.reject_tiling tt)
    (BandGeneric.reject_tiling tt).
Proof.
  unfold SBandTilingOpt.reject_tiling, BandGeneric.reject_tiling.
  rewrite SBandTilingOpt.observe_tiling_validation_route_eq.
  apply impeq_refl.
Qed.

Lemma prepared_codegen_after_tiling_route_impeq :
  forall pol_after route,
    impeq
      (SBandTilingOpt.prepared_codegen_after_tiling_route
         pol_after route)
      (BandGeneric.prepared_codegen_after_tiling_route
         pol_after route).
Proof.
  intros pol_after route.
  destruct route; apply impeq_refl.
Qed.

Lemma reject_post_tiling_affine_impeq_generic :
  forall route,
    impeq
      (SBandTilingOpt.reject_post_tiling_affine route tt)
      (BandGeneric.reject_post_tiling_affine route tt).
Proof.
  intro route.
  unfold SBandTilingOpt.reject_post_tiling_affine,
    BandGeneric.reject_post_tiling_affine.
  destruct route; apply impeq_refl.
Qed.

Lemma try_verified_tiling_after_phase_mid_band_impeq_generic :
  forall pol_mid mid_scop after_scop,
    impeq
      (SBandTilingOpt.try_verified_tiling_after_phase_mid_band
         pol_mid mid_scop after_scop)
      (BandGeneric.try_verified_tiling_after_phase_mid_band
         pol_mid mid_scop after_scop).
Proof.
  intros pol_mid mid_scop after_scop.
  unfold SBandTilingOpt.try_verified_tiling_after_phase_mid_band,
    BandGeneric.try_verified_tiling_after_phase_mid_band.
  destruct (BandGeneric.BaseOpt.infer_tiling_witness_scops mid_scop after_scop)
    as [ws|msg].
  - change
      (BandGeneric.ValidatorCore
         .import_canonical_tiled_after_poly pol_mid after_scop ws)
      with
      (BandGeneric.BaseOpt.ValidatorCore
         .import_canonical_tiled_after_poly pol_mid after_scop ws).
    destruct
      (BandGeneric.BaseOpt.ValidatorCore
         .import_canonical_tiled_after_poly pol_mid after_scop ws)
      as [pol_after|msg_after].
    + apply bind_eq_compat.
      * apply impeq_refl.
      * intro route.
        rewrite SBandTilingOpt.observe_tiling_validation_route_eq.
        destruct route; simpl.
        -- apply bind_eq_compat.
           ++ apply impeq_refl.
           ++ intro wf_after. destruct wf_after.
              ** apply impeq_refl.
              ** apply reject_tiling_impeq_generic.
        -- apply bind_eq_compat.
           ++ apply impeq_refl.
           ++ intro wf_after. destruct wf_after.
              ** apply impeq_refl.
              ** apply reject_tiling_impeq_generic.
        -- apply reject_tiling_impeq_generic.
    + apply reject_tiling_impeq_generic.
  - apply reject_tiling_impeq_generic.
Qed.

Lemma try_verified_post_tiling_affine_after_phase_mid_band_impeq_generic :
  forall pol_mid mid_scop posttile_scop after_scop,
    impeq
      (SBandTilingOpt.try_verified_post_tiling_affine_after_phase_mid_band
         pol_mid mid_scop posttile_scop after_scop)
      (BandGeneric.try_verified_post_tiling_affine_after_phase_mid_band
         pol_mid mid_scop posttile_scop after_scop).
Proof.
  intros pol_mid mid_scop posttile_scop after_scop.
  unfold SBandTilingOpt.try_verified_post_tiling_affine_after_phase_mid_band,
    BandGeneric.try_verified_post_tiling_affine_after_phase_mid_band.
  destruct (BandGeneric.BaseOpt.infer_tiling_witness_scops
              mid_scop posttile_scop)
    as [ws|msg].
  - destruct
      (BandGeneric.BaseOpt.ValidatorCore
         .import_canonical_tiled_after_poly pol_mid posttile_scop ws)
      as [pol_posttile|msg_posttile].
    + apply bind_eq_compat.
      * apply impeq_refl.
      * intro route.
        rewrite SBandTilingOpt.observe_tiling_validation_route_eq.
        destruct route; simpl.
        -- apply bind_eq_compat.
           ++ apply impeq_refl.
           ++ intro wf_posttile. destruct wf_posttile.
              ** destruct
                   (BandGeneric.PolyLang.from_openscop_schedule_only
                      pol_posttile after_scop)
                   as [pol_after|msg_after].
                 --- apply bind_eq_compat.
                     +++ apply impeq_refl.
                     +++ intro final_ok. destruct final_ok.
                         *** apply bind_eq_compat.
                             ---- apply impeq_refl.
                             ---- intro wf_after. destruct wf_after.
                                  ++++ apply impeq_refl.
                                  ++++ apply impeq_refl.
                         *** apply impeq_refl.
                 --- apply impeq_refl.
              ** apply reject_tiling_impeq_generic.
        -- apply bind_eq_compat.
           ++ apply impeq_refl.
           ++ intro wf_posttile. destruct wf_posttile.
              ** destruct
                   (BandGeneric.PolyLang.from_openscop_schedule_only
                      pol_posttile after_scop)
                   as [pol_after|msg_after].
                 --- apply bind_eq_compat.
                     +++ apply impeq_refl.
                     +++ intro final_ok. destruct final_ok.
                         *** apply bind_eq_compat.
                             ---- apply impeq_refl.
                             ---- intro wf_after. destruct wf_after.
                                  ++++ apply impeq_refl.
                                  ++++ apply impeq_refl.
                         *** apply impeq_refl.
                 --- apply impeq_refl.
              ** apply reject_tiling_impeq_generic.
        -- apply reject_tiling_impeq_generic.
    + apply reject_tiling_impeq_generic.
  - apply reject_tiling_impeq_generic.
Qed.

Lemma try_phase_pipeline_from_source_pol_band_impeq_generic :
  forall pol_source phase_runner before_scop,
    impeq
      (SBandTilingOpt.try_phase_pipeline_from_source_pol_band
         pol_source phase_runner before_scop)
      (BandGeneric.try_phase_pipeline_from_source_pol_band
         pol_source phase_runner before_scop).
Proof.
  intros pol_source phase_runner before_scop.
  unfold SBandTilingOpt.try_phase_pipeline_from_source_pol_band,
    BandGeneric.try_phase_pipeline_from_source_pol_band.
  destruct (phase_runner before_scop)
    as [[mid_scop after_scop]|msg].
  - destruct (BandGeneric.PolyLang.from_openscop_schedule_only pol_source mid_scop)
      as [pol_mid|msg_mid].
    + apply bind_eq_compat.
      * apply impeq_refl.
      * intro affine_ok. destruct affine_ok.
        -- apply try_verified_tiling_after_phase_mid_band_impeq_generic.
        -- apply reject_tiling_impeq_generic.
    + apply reject_tiling_impeq_generic.
  - apply reject_tiling_impeq_generic.
Qed.

Lemma try_identity_phase_pipeline_from_source_pol_band_impeq_generic :
  forall pol_source phase_runner before_scop,
    impeq
      (SBandTilingOpt.try_identity_phase_pipeline_from_source_pol_band
         pol_source phase_runner before_scop)
      (BandGeneric.try_identity_phase_pipeline_from_source_pol_band
         pol_source phase_runner before_scop).
Proof.
  intros pol_source phase_runner before_scop.
  unfold SBandTilingOpt.try_identity_phase_pipeline_from_source_pol_band,
    BandGeneric.try_identity_phase_pipeline_from_source_pol_band.
  destruct (phase_runner before_scop)
    as [[mid_scop after_scop]|msg].
  - destruct (BandGeneric.PolyLang.from_openscop_like_source pol_source mid_scop)
      as [pol_mid|msg_mid].
    + apply bind_eq_compat.
      * apply impeq_refl.
      * intro affine_ok. destruct affine_ok.
        -- apply try_verified_tiling_after_phase_mid_band_impeq_generic.
        -- apply reject_tiling_impeq_generic.
    + apply reject_tiling_impeq_generic.
  - apply reject_tiling_impeq_generic.
Qed.

Lemma try_post_tiling_affine_phase_pipeline_from_source_pol_band_impeq_generic :
  forall pol_source before_scop,
    impeq
      (SBandTilingOpt.try_post_tiling_affine_phase_pipeline_from_source_pol_band
         pol_source before_scop)
      (BandGeneric.try_post_tiling_affine_phase_pipeline_from_source_pol_band
         pol_source before_scop).
Proof.
  intros pol_source before_scop.
  unfold SBandTilingOpt.try_post_tiling_affine_phase_pipeline_from_source_pol_band,
    BandGeneric.try_post_tiling_affine_phase_pipeline_from_source_pol_band.
  destruct (BandGeneric.BaseOpt.run_pluto_post_tiling_affine_phase_pipeline before_scop)
    as [[mid_scop [posttile_scop after_scop]]|msg].
  - destruct (BandGeneric.PolyLang.from_openscop_schedule_only pol_source mid_scop)
      as [pol_mid|msg_mid].
    + apply bind_eq_compat.
      * apply impeq_refl.
      * intro affine_ok. destruct affine_ok.
        -- apply try_verified_post_tiling_affine_after_phase_mid_band_impeq_generic.
        -- apply reject_tiling_impeq_generic.
    + apply reject_tiling_impeq_generic.
  - apply reject_tiling_impeq_generic.
Qed.

Lemma try_post_tiling_affine_phase_pipeline_from_source_pol_band_with_iss_impeq_generic :
  forall pol_source before_scop,
    impeq
      (SBandTilingOpt
         .try_post_tiling_affine_phase_pipeline_from_source_pol_band_with_iss
         pol_source before_scop)
      (BandGeneric.try_post_tiling_affine_phase_pipeline_from_source_pol_band_with_iss
         pol_source before_scop).
Proof.
  intros pol_source before_scop.
  unfold
    SBandTilingOpt.try_post_tiling_affine_phase_pipeline_from_source_pol_band_with_iss,
    BandGeneric.try_post_tiling_affine_phase_pipeline_from_source_pol_band_with_iss.
  destruct
    (BandGeneric.BaseOpt.run_pluto_post_tiling_affine_phase_pipeline_with_iss before_scop)
    as [[mid_scop [posttile_scop after_scop]]|msg].
  - destruct (BandGeneric.PolyLang.from_openscop_schedule_only pol_source mid_scop)
      as [pol_mid|msg_mid].
    + apply bind_eq_compat.
      * apply impeq_refl.
      * intro affine_ok. destruct affine_ok.
        -- apply try_verified_post_tiling_affine_after_phase_mid_band_impeq_generic.
        -- apply reject_tiling_impeq_generic.
    + apply reject_tiling_impeq_generic.
  - apply reject_tiling_impeq_generic.
Qed.

Lemma try_checked_iss_phase_pipeline_from_poly_band_impeq_generic :
  forall pol before_scop,
    impeq
      (SBandTilingOpt.try_checked_iss_phase_pipeline_from_poly_band
         pol before_scop)
      (BandGeneric.try_checked_iss_phase_pipeline_from_poly_band
         pol before_scop).
Proof.
  intros pol before_scop.
  unfold SBandTilingOpt.try_checked_iss_phase_pipeline_from_poly_band,
    BandGeneric.try_checked_iss_phase_pipeline_from_poly_band.
  destruct (BandGeneric.BaseOpt.infer_iss_from_source_scop pol before_scop)
    as [iss_opt|msg].
  - destruct iss_opt as [[pol_iss w]|].
    + destruct
        (BandGeneric.BaseOpt.ValidatorCore
           .checked_iss_complete_cut_shape_validate pol pol_iss w).
      * apply bind_eq_compat.
        -- apply impeq_refl.
        -- intro iss_wf. destruct iss_wf.
           ++ destruct (BandGeneric.BaseOpt.export_for_phase_scheduler pol_iss).
              ** apply try_phase_pipeline_from_source_pol_band_impeq_generic.
              ** apply reject_tiling_impeq_generic.
           ++ apply try_phase_pipeline_from_source_pol_band_impeq_generic.
      * apply try_phase_pipeline_from_source_pol_band_impeq_generic.
    + apply try_phase_pipeline_from_source_pol_band_impeq_generic.
  - apply try_phase_pipeline_from_source_pol_band_impeq_generic.
Qed.

Lemma phase_pipeline_opt_prepared_from_poly_no_iss_band_impeq_generic :
  forall pol,
    impeq
      (if BandGeneric.BaseOpt.has_nonscalar_stmt pol then
         match BandGeneric.BaseOpt.export_for_phase_scheduler pol with
         | Some before_scop =>
             SBandTilingOpt.try_phase_pipeline_from_source_pol_band
               pol BandGeneric.BaseOpt.run_pluto_phase_pipeline before_scop
         | None => SBandTilingOpt.reject_tiling tt
         end
       else SBandTilingOpt.reject_tiling tt)
      (BandGeneric.phase_pipeline_opt_prepared_from_poly_no_iss_band pol).
Proof.
  intro pol.
  unfold BandGeneric.phase_pipeline_opt_prepared_from_poly_no_iss_band.
  destruct (BandGeneric.BaseOpt.has_nonscalar_stmt pol).
  - destruct (BandGeneric.BaseOpt.export_for_phase_scheduler pol).
    + apply try_phase_pipeline_from_source_pol_band_impeq_generic.
    + apply reject_tiling_impeq_generic.
  - apply reject_tiling_impeq_generic.
Qed.

Lemma phase_pipeline_opt_prepared_from_poly_with_iss_band_impeq_generic :
  forall pol,
    impeq
      (if BandGeneric.BaseOpt.has_nonscalar_stmt pol then
         match BandGeneric.BaseOpt.export_for_phase_scheduler pol with
         | Some before_scop =>
             SBandTilingOpt.try_checked_iss_phase_pipeline_from_poly_band
               pol before_scop
         | None => SBandTilingOpt.reject_tiling tt
         end
       else SBandTilingOpt.reject_tiling tt)
      (BandGeneric.phase_pipeline_opt_prepared_from_poly_with_iss_band pol).
Proof.
  intro pol.
  unfold BandGeneric.phase_pipeline_opt_prepared_from_poly_with_iss_band.
  destruct (BandGeneric.BaseOpt.has_nonscalar_stmt pol).
  - destruct (BandGeneric.BaseOpt.export_for_phase_scheduler pol).
    + apply try_checked_iss_phase_pipeline_from_poly_band_impeq_generic.
    + apply reject_tiling_impeq_generic.
  - apply reject_tiling_impeq_generic.
Qed.

Lemma opt_identity_tiled_from_poly_impeq_generic :
  forall pol,
    impeq
      (SBandTilingOpt.opt_identity_tiled_from_poly pol)
      (BandGeneric.identity_tiling_opt_prepared_from_poly_band pol).
Proof.
  intro pol.
  unfold SBandTilingOpt.opt_identity_tiled_from_poly,
    BandGeneric.identity_tiling_opt_prepared_from_poly_band.
  destruct (BandGeneric.BaseOpt.has_nonscalar_stmt pol).
  - destruct (BandGeneric.BaseOpt.export_for_phase_scheduler pol).
    + apply try_identity_phase_pipeline_from_source_pol_band_impeq_generic.
    + apply reject_tiling_impeq_generic.
  - apply reject_tiling_impeq_generic.
Qed.

Lemma try_checked_iss_identity_tiling_phase_pipeline_from_poly_band_impeq_generic :
  forall pol before_scop,
    impeq
      (SBandTilingOpt
         .try_checked_iss_identity_tiling_phase_pipeline_from_poly_band
         pol before_scop)
      (BandGeneric
         .try_checked_iss_identity_tiling_phase_pipeline_from_poly_band
         pol before_scop).
Proof.
  intros pol before_scop.
  unfold
    SBandTilingOpt.try_checked_iss_identity_tiling_phase_pipeline_from_poly_band,
    BandGeneric.try_checked_iss_identity_tiling_phase_pipeline_from_poly_band.
  destruct (BandGeneric.BaseOpt.infer_iss_from_source_scop pol before_scop)
    as [iss_opt|msg].
  - destruct iss_opt as [[pol_iss w]|].
    + destruct
        (BandGeneric.BaseOpt.ValidatorCore
           .checked_iss_complete_cut_shape_validate pol pol_iss w).
      * apply bind_eq_compat.
        -- apply impeq_refl.
        -- intro iss_wf. destruct iss_wf.
           ++ destruct (BandGeneric.BaseOpt.export_for_phase_scheduler pol_iss).
              ** apply try_identity_phase_pipeline_from_source_pol_band_impeq_generic.
              ** apply reject_tiling_impeq_generic.
           ++ apply opt_identity_tiled_from_poly_impeq_generic.
      * apply opt_identity_tiled_from_poly_impeq_generic.
    + apply opt_identity_tiled_from_poly_impeq_generic.
  - apply opt_identity_tiled_from_poly_impeq_generic.
Qed.

Lemma identity_tiling_opt_prepared_from_poly_with_iss_band_impeq_generic :
  forall pol,
    impeq
      (if BandGeneric.BaseOpt.has_nonscalar_stmt pol then
         match BandGeneric.BaseOpt.export_for_phase_scheduler pol with
         | Some before_scop =>
             SBandTilingOpt
               .try_checked_iss_identity_tiling_phase_pipeline_from_poly_band
               pol before_scop
         | None => SBandTilingOpt.reject_tiling tt
         end
       else SBandTilingOpt.reject_tiling tt)
      (BandGeneric.identity_tiling_opt_prepared_from_poly_with_iss_band pol).
Proof.
  intro pol.
  unfold BandGeneric.identity_tiling_opt_prepared_from_poly_with_iss_band.
  destruct (BandGeneric.BaseOpt.has_nonscalar_stmt pol).
  - destruct (BandGeneric.BaseOpt.export_for_phase_scheduler pol).
    + apply
        try_checked_iss_identity_tiling_phase_pipeline_from_poly_band_impeq_generic.
    + apply reject_tiling_impeq_generic.
  - apply reject_tiling_impeq_generic.
Qed.

Lemma try_checked_iss_post_tiling_affine_phase_pipeline_from_poly_band_impeq_generic :
  forall pol before_scop,
    impeq
      (SBandTilingOpt.try_checked_iss_post_tiling_affine_phase_pipeline_from_poly_band
         pol before_scop)
      (BandGeneric.try_checked_iss_post_tiling_affine_phase_pipeline_from_poly_band
         pol before_scop).
Proof.
  intros pol before_scop.
  unfold SBandTilingOpt.try_checked_iss_post_tiling_affine_phase_pipeline_from_poly_band,
    BandGeneric.try_checked_iss_post_tiling_affine_phase_pipeline_from_poly_band.
  destruct (BandGeneric.BaseOpt.infer_iss_from_source_scop pol before_scop)
    as [iss_opt|msg].
  - destruct iss_opt as [[pol_iss w]|].
    + destruct
        (BandGeneric.BaseOpt.ValidatorCore
           .checked_iss_complete_cut_shape_validate pol pol_iss w).
      * apply bind_eq_compat.
        -- apply impeq_refl.
        -- intro iss_wf. destruct iss_wf.
           ++ destruct (BandGeneric.BaseOpt.export_for_phase_scheduler pol_iss).
              ** apply try_post_tiling_affine_phase_pipeline_from_source_pol_band_impeq_generic.
              ** apply reject_tiling_impeq_generic.
           ++ apply try_post_tiling_affine_phase_pipeline_from_source_pol_band_impeq_generic.
      * apply try_post_tiling_affine_phase_pipeline_from_source_pol_band_impeq_generic.
    + apply try_post_tiling_affine_phase_pipeline_from_source_pol_band_impeq_generic.
  - apply try_post_tiling_affine_phase_pipeline_from_source_pol_band_impeq_generic.
Qed.

Lemma phase_post_tiling_affine_opt_prepared_from_poly_no_iss_band_impeq_generic :
  forall pol,
    impeq
      (if BandGeneric.BaseOpt.has_nonscalar_stmt pol then
         match BandGeneric.BaseOpt.export_for_phase_scheduler pol with
         | Some before_scop =>
             SBandTilingOpt.try_post_tiling_affine_phase_pipeline_from_source_pol_band
               pol before_scop
         | None => SBandTilingOpt.reject_tiling tt
         end
       else SBandTilingOpt.reject_tiling tt)
      (BandGeneric.phase_post_tiling_affine_opt_prepared_from_poly_no_iss_band pol).
Proof.
  intro pol.
  unfold BandGeneric.phase_post_tiling_affine_opt_prepared_from_poly_no_iss_band.
  destruct (BandGeneric.BaseOpt.has_nonscalar_stmt pol).
  - destruct (BandGeneric.BaseOpt.export_for_phase_scheduler pol).
    + apply try_post_tiling_affine_phase_pipeline_from_source_pol_band_impeq_generic.
    + apply reject_tiling_impeq_generic.
  - apply reject_tiling_impeq_generic.
Qed.

Lemma phase_post_tiling_affine_opt_prepared_from_poly_with_iss_band_impeq_generic :
  forall pol,
    impeq
      (if BandGeneric.BaseOpt.has_nonscalar_stmt pol then
         match BandGeneric.BaseOpt.export_for_phase_scheduler pol with
         | Some before_scop =>
             SBandTilingOpt
               .try_checked_iss_post_tiling_affine_phase_pipeline_from_poly_band
               pol before_scop
         | None => SBandTilingOpt.reject_tiling tt
         end
       else SBandTilingOpt.reject_tiling tt)
      (BandGeneric.phase_post_tiling_affine_opt_prepared_from_poly_with_iss_band pol).
Proof.
  intro pol.
  unfold BandGeneric.phase_post_tiling_affine_opt_prepared_from_poly_with_iss_band.
  destruct (BandGeneric.BaseOpt.has_nonscalar_stmt pol).
  - destruct (BandGeneric.BaseOpt.export_for_phase_scheduler pol).
    + apply
        try_checked_iss_post_tiling_affine_phase_pipeline_from_poly_band_impeq_generic.
    + apply reject_tiling_impeq_generic.
  - apply reject_tiling_impeq_generic.
Qed.

Theorem opt_impeq_generic :
  forall loop,
    impeq (SBandTilingOpt.opt loop) (BandGeneric.Opt_band loop).
Proof.
  intro loop.
  unfold SBandTilingOpt.opt, BandGeneric.Opt_band,
    BandGeneric.Opt_prepared_band, BandGeneric.phase_pipeline_opt_prepared_band.
  apply bind_eq_compat.
  - apply impeq_refl.
  - intro pol0.
    apply phase_pipeline_opt_prepared_from_poly_no_iss_band_impeq_generic.
Qed.

Theorem opt_with_iss_impeq_generic :
  forall loop,
    impeq
      (SBandTilingOpt.opt_with_iss loop)
      (BandGeneric.Opt_band_with_iss loop).
Proof.
  intro loop.
  unfold SBandTilingOpt.opt_with_iss, BandGeneric.Opt_band_with_iss,
    BandGeneric.Opt_prepared_band_with_iss,
    BandGeneric.phase_pipeline_opt_prepared_with_iss_band.
  apply bind_eq_compat.
  - apply impeq_refl.
  - intro pol0.
    apply phase_pipeline_opt_prepared_from_poly_with_iss_band_impeq_generic.
Qed.

Theorem opt_identity_tiled_impeq_generic :
  forall loop,
    impeq
      (SBandTilingOpt.opt_identity_tiled loop)
      (BandGeneric.Opt_identity_tiled_band loop).
Proof.
  intro loop.
  unfold SBandTilingOpt.opt_identity_tiled,
    BandGeneric.Opt_identity_tiled_band,
    BandGeneric.Opt_prepared_identity_tiled_band,
    BandGeneric.identity_tiling_opt_prepared_band.
  apply bind_eq_compat.
  - apply impeq_refl.
  - intro pol0. apply opt_identity_tiled_from_poly_impeq_generic.
Qed.

Theorem opt_identity_tiled_with_iss_impeq_generic :
  forall loop,
    impeq
      (SBandTilingOpt.opt_identity_tiled_with_iss loop)
      (BandGeneric.Opt_identity_tiled_band_with_iss loop).
Proof.
  intro loop.
  unfold SBandTilingOpt.opt_identity_tiled_with_iss,
    BandGeneric.Opt_identity_tiled_band_with_iss,
    BandGeneric.Opt_prepared_identity_tiled_band_with_iss,
    BandGeneric.identity_tiling_opt_prepared_with_iss_band.
  apply bind_eq_compat.
  - apply impeq_refl.
  - intro pol0.
    apply
      identity_tiling_opt_prepared_from_poly_with_iss_band_impeq_generic.
Qed.

Theorem opt_post_tiling_affine_impeq_generic :
  forall loop,
    impeq
      (SBandTilingOpt.opt_post_tiling_affine loop)
      (BandGeneric.Opt_post_tiling_affine_band loop).
Proof.
  intro loop.
  unfold SBandTilingOpt.opt_post_tiling_affine, BandGeneric.Opt_post_tiling_affine_band,
    BandGeneric.Opt_prepared_post_tiling_affine_band,
    BandGeneric.phase_post_tiling_affine_opt_prepared_band.
  apply bind_eq_compat.
  - apply impeq_refl.
  - intro pol0.
    apply phase_post_tiling_affine_opt_prepared_from_poly_no_iss_band_impeq_generic.
Qed.

Theorem opt_post_tiling_affine_with_iss_impeq_generic :
  forall loop,
    impeq
      (SBandTilingOpt.opt_post_tiling_affine_with_iss loop)
      (BandGeneric.Opt_post_tiling_affine_band_with_iss loop).
Proof.
  intro loop.
  unfold SBandTilingOpt.opt_post_tiling_affine_with_iss,
    BandGeneric.Opt_post_tiling_affine_band_with_iss,
    BandGeneric.Opt_prepared_post_tiling_affine_band_with_iss,
    BandGeneric.phase_post_tiling_affine_opt_prepared_with_iss_band.
  apply bind_eq_compat.
  - apply impeq_refl.
  - intro pol0.
    apply phase_post_tiling_affine_opt_prepared_from_poly_with_iss_band_impeq_generic.
Qed.

Corollary opt_prepared_impeq_generic :
  forall loop,
    impeq
      (SBandTilingOpt.opt_prepared loop)
      (BandGeneric.Opt_prepared_band loop).
Proof.
  intro loop. exact (opt_impeq_generic loop).
Qed.

Corollary opt_post_tiling_affine_prepared_impeq_generic :
  forall loop,
    impeq
      (SBandTilingOpt.opt_post_tiling_affine_prepared loop)
      (BandGeneric.Opt_prepared_post_tiling_affine_band loop).
Proof.
  intro loop. exact (opt_post_tiling_affine_impeq_generic loop).
Qed.

Corollary opt_post_tiling_affine_with_iss_prepared_impeq_generic :
  forall loop,
    impeq
      (SBandTilingOpt.opt_post_tiling_affine_with_iss_prepared loop)
      (BandGeneric.Opt_prepared_post_tiling_affine_band_with_iss loop).
Proof.
  intro loop. exact (opt_post_tiling_affine_with_iss_impeq_generic loop).
Qed.

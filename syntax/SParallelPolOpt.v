Require Import Result.
Require Import List.
Require Import String.
Require Import PolyLang.
Require Import SPolIRs.
Require Import OpenScop.
Require Import ParallelCodegen.
Require Import Validator.
Require Import PolOpt.
Require Import SParallelPolOptShared.
Require Import STilingBandSched.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Module FunctorCore := SParallelPolOptShared.Core.
Module CoreOpt := FunctorCore.CoreOpt.
Module PolyLang := FunctorCore.PolyLang.
Module ValidatorCore := FunctorCore.ValidatorCore.
Module ParallelCodegenCore := FunctorCore.ParallelCodegenCore.
Module TilingSched := FunctorCore.TilingSched.
Module LoopIR := FunctorCore.LoopIR.
Module ParallelLoop := ParallelCodegenCore.ParallelLoop.

Definition scoped_parallel_rows :=
  ValidatorCore.ParallelCore.scoped_parallel_rows_from.

Definition parallel_plan_of_dim (d : nat) : ValidatorCore.parallel_plan :=
  {| ValidatorCore.ParallelCore.target_dim := d |}.

Definition checked_parallel_current_annotated_codegen
    (pol : PolyLang.t)
    (plan : ValidatorCore.parallel_plan)
  : imp (result ParallelLoop.t) :=
  BIND cert_res <- ValidatorCore.checked_parallelize_current
                     (PolyLang.current_view_pprog pol) plan -;
  match cert_res with
  | Okk cert =>
      let cert' :=
        {| ParallelCodegenCore.ParallelValidator.certified_dim :=
             cert.(ValidatorCore.ParallelCore.certified_dim) |} in
      ParallelCodegenCore.checked_annotated_codegen
        (PolyLang.current_view_pprog pol) cert'
  | Err msg => pure (Err msg)
  end.

Definition checked_parallel_current_annotated_codegen_at
    (pol : PolyLang.t)
    (d : nat)
  : imp (result ParallelLoop.t) :=
  checked_parallel_current_annotated_codegen pol (parallel_plan_of_dim d).

Definition checked_vector_current_annotated_codegen
    (pol : PolyLang.t)
    (plan : ValidatorCore.parallel_plan)
  : imp (result ParallelLoop.t) :=
  BIND cert_res <- ValidatorCore.checked_parallelize_current
                     (PolyLang.current_view_pprog pol) plan -;
  match cert_res with
  | Okk cert =>
      let cert' :=
        {| ParallelCodegenCore.ParallelValidator.certified_dim :=
             cert.(ValidatorCore.ParallelCore.certified_dim) |} in
      ParallelCodegenCore.checked_vector_annotated_codegen
        (PolyLang.current_view_pprog pol) cert'
  | Err msg => pure (Err msg)
  end.

Definition checked_vector_current_annotated_codegen_at
    (pol : PolyLang.t)
    (d : nat)
  : imp (result ParallelLoop.t) :=
  checked_vector_current_annotated_codegen pol (parallel_plan_of_dim d).

Definition parallel_codegen_cert_of_validator_cert
    (cert : ValidatorCore.parallel_cert)
  : ParallelCodegenCore.ParallelValidator.parallel_cert :=
  {| ParallelCodegenCore.ParallelValidator.certified_dim :=
       cert.(ValidatorCore.ParallelCore.certified_dim) |}.

Fixpoint collect_parallel_current_codegen_certs
    (pp : PolyLang.t)
    (dims : list nat)
  : imp (list ParallelCodegenCore.ParallelValidator.parallel_cert) :=
  match dims with
  | nil => pure nil
  | cons d dims' =>
      BIND cert_res <-
        ValidatorCore.checked_parallelize_current pp (parallel_plan_of_dim d) -;
      match cert_res with
      | Okk cert =>
          BIND certs <- collect_parallel_current_codegen_certs pp dims' -;
          pure (cons (parallel_codegen_cert_of_validator_cert cert) certs)
      | Err _ =>
          collect_parallel_current_codegen_certs pp dims'
      end
  end.

Definition checked_parallel_current_many_annotated_codegen_at
    (pol : PolyLang.t)
    (dims : list nat)
  : imp (result ParallelLoop.t) :=
  let current := PolyLang.current_view_pprog pol in
  BIND certs <- collect_parallel_current_codegen_certs current dims -;
  match certs with
  | nil => pure (Err "Parallel validation failed"%string)
  | cons _ _ =>
      ParallelCodegenCore.checked_annotated_codegen_many current certs
  end.

Definition parallel_current_identity_prepared_from_poly
    (pol : PolyLang.t)
    (d : nat)
  : imp (result ParallelLoop.t) :=
  checked_parallel_current_annotated_codegen_at pol d.

Definition parallel_current_affine_prepared_from_poly
    (pol : PolyLang.t)
    (d : nat)
  : imp (result ParallelLoop.t) :=
  BIND pol' <- CoreOpt.checked_affine_schedule pol -;
  checked_parallel_current_annotated_codegen_at pol' d.

Definition tiling_validation_route_label
    (route: TilingSched.tiling_band_validation_route) : string :=
  match route with
  | TilingSched.DirectBandAccepted => "permutable-band"%string
  | TilingSched.GeneralScheduleAccepted => "actual-schedule"%string
  | TilingSched.Rejected => "rejected"%string
  end.

Definition observe_tiling_validation_route
    (route: TilingSched.tiling_band_validation_route)
  : TilingSched.tiling_band_validation_route :=
  PolOpt.print
    (fun selected =>
       STilingBandSched.print_tiling_validation_route_label
         (tiling_validation_route_label selected))
    route.

Lemma observe_tiling_validation_route_eq :
  forall route, observe_tiling_validation_route route = route.
Proof. reflexivity. Qed.

Definition reject_tiling (_: unit) : imp PolyLang.t :=
  match observe_tiling_validation_route TilingSched.Rejected with
  | TilingSched.Rejected =>
      res_to_alarm PolyLang.dummy
        (Err "Tiling validation rejected or unavailable."%string)
  | TilingSched.DirectBandAccepted | TilingSched.GeneralScheduleAccepted =>
      res_to_alarm PolyLang.dummy
        (Err "Impossible accepted result while recording tiling rejection."%string)
  end.

Definition select_after_tiling_route
    (pol_after: PolyLang.t)
    (route: TilingSched.tiling_band_validation_route)
  : imp PolyLang.t :=
  match route with
  | TilingSched.DirectBandAccepted | TilingSched.GeneralScheduleAccepted =>
      pure (PolyLang.current_view_pprog pol_after)
  | TilingSched.Rejected =>
      res_to_alarm PolyLang.dummy
        (Err "Tiling validation rejected."%string)
  end.

Definition reject_post_tiling_affine
    (route: TilingSched.tiling_band_validation_route) : imp PolyLang.t :=
  match route with
  | TilingSched.DirectBandAccepted | TilingSched.GeneralScheduleAccepted =>
      res_to_alarm PolyLang.dummy
        (Err "Post-tiling affine validation failed.")
  | TilingSched.Rejected =>
      res_to_alarm PolyLang.dummy
        (Err "Post-tiling affine validation failed.")
  end.

Definition try_verified_tiling_after_phase_mid_poly
    (pol_mid : PolyLang.t)
    (mid_scop after_scop : OpenScop)
  : imp PolyLang.t :=
  let rejected := reject_tiling in
  match CoreOpt.infer_tiling_witness_scops mid_scop after_scop with
  | Err _ =>
      rejected tt
  | Okk ws =>
      match ValidatorCore.import_canonical_tiled_after_poly pol_mid after_scop ws with
      | Err _ =>
          rejected tt
      | Okk pol_after =>
          BIND route <-
            TilingSched.checked_tiling_schedule_sourceb_first_runtime_validate_route
              pol_mid pol_after ws -;
          match route with
          | TilingSched.DirectBandAccepted | TilingSched.GeneralScheduleAccepted =>
              BIND wf_after <-
                ValidatorCore.check_wf_polyprog_general pol_after -;
              if wf_after then
                select_after_tiling_route
                  pol_after
                  (observe_tiling_validation_route route)
              else rejected tt
          | TilingSched.Rejected =>
              rejected tt
          end
      end
  end.

Definition try_phase_pipeline_from_source_pol_poly
    (pol_source : PolyLang.t)
    (phase_runner : OpenScop -> result (OpenScop * OpenScop))
    (before_scop : OpenScop)
  : imp PolyLang.t :=
  let rejected :=
    reject_tiling in
  match phase_runner before_scop with
  | Err _ =>
      rejected tt
  | Okk (mid_scop, after_scop) =>
      match PolyLang.from_openscop_schedule_only pol_source mid_scop with
      | Err _ =>
          rejected tt
      | Okk pol_mid =>
          BIND affine_ok <- ValidatorCore.validate pol_source pol_mid -;
          if affine_ok then
            try_verified_tiling_after_phase_mid_poly pol_mid mid_scop after_scop
          else
            rejected tt
      end
  end.

Definition try_identity_tiling_phase_pipeline_from_source_pol_poly
    (pol_source : PolyLang.t)
    (before_scop : OpenScop)
  : imp PolyLang.t :=
  let rejected :=
    reject_tiling in
  match CoreOpt.run_pluto_identity_tiling_pipeline before_scop with
  | Err _ =>
      rejected tt
  | Okk (mid_scop, after_scop) =>
      match PolyLang.from_openscop_like_source pol_source mid_scop with
      | Err _ =>
          rejected tt
      | Okk pol_mid =>
          BIND affine_ok <- ValidatorCore.validate pol_source pol_mid -;
          if affine_ok then
            try_verified_tiling_after_phase_mid_poly pol_mid mid_scop after_scop
          else
            rejected tt
      end
  end.

Definition try_verified_post_tiling_affine_after_phase_mid_poly
    (pol_mid : PolyLang.t)
    (mid_scop posttile_scop after_scop : OpenScop)
  : imp PolyLang.t :=
  let rejected := reject_tiling in
  match CoreOpt.infer_tiling_witness_scops mid_scop posttile_scop with
  | Err _ =>
      rejected tt
  | Okk ws =>
      match ValidatorCore.import_canonical_tiled_after_poly pol_mid posttile_scop ws with
      | Err _ =>
          rejected tt
      | Okk pol_posttile =>
          BIND route <-
            TilingSched.checked_tiling_schedule_sourceb_first_runtime_validate_route
              pol_mid pol_posttile ws -;
          match route with
          | TilingSched.DirectBandAccepted | TilingSched.GeneralScheduleAccepted =>
              BIND wf_posttile <-
                ValidatorCore.check_wf_polyprog_general pol_posttile -;
              if wf_posttile then
                let route := observe_tiling_validation_route route in
                match PolyLang.from_openscop_schedule_only
                        pol_posttile after_scop with
                | Err _ => reject_post_tiling_affine route
                | Okk pol_after =>
                    BIND final_ok <-
                      ValidatorCore.validate_general pol_posttile pol_after -;
                    if final_ok then
                      BIND wf_after <-
                        ValidatorCore.check_wf_polyprog_general pol_after -;
                      if wf_after then
                        select_after_tiling_route pol_after route
                      else reject_post_tiling_affine route
                    else reject_post_tiling_affine route
                end
              else rejected tt
          | TilingSched.Rejected =>
              rejected tt
          end
      end
  end.

Definition try_post_tiling_affine_phase_pipeline_from_source_pol_poly
    (pol_source : PolyLang.t)
    (before_scop : OpenScop)
  : imp PolyLang.t :=
  let rejected :=
    reject_tiling in
  match CoreOpt.run_pluto_post_tiling_affine_phase_pipeline before_scop with
  | Err _ =>
      rejected tt
  | Okk (mid_scop, (posttile_scop, after_scop)) =>
      match PolyLang.from_openscop_schedule_only pol_source mid_scop with
      | Err _ =>
          rejected tt
      | Okk pol_mid =>
          BIND affine_ok <- ValidatorCore.validate pol_source pol_mid -;
          if affine_ok then
            try_verified_post_tiling_affine_after_phase_mid_poly
              pol_mid mid_scop posttile_scop after_scop
          else
            rejected tt
      end
  end.

Definition try_post_tiling_affine_phase_pipeline_from_source_pol_poly_with_iss
    (pol_source : PolyLang.t)
    (before_scop : OpenScop)
  : imp PolyLang.t :=
  let rejected :=
    reject_tiling in
  match CoreOpt.run_pluto_post_tiling_affine_phase_pipeline_with_iss before_scop with
  | Err _ =>
      rejected tt
  | Okk (mid_scop, (posttile_scop, after_scop)) =>
      match PolyLang.from_openscop_schedule_only pol_source mid_scop with
      | Err _ =>
          rejected tt
      | Okk pol_mid =>
          BIND affine_ok <- ValidatorCore.validate pol_source pol_mid -;
          if affine_ok then
            try_verified_post_tiling_affine_after_phase_mid_poly
              pol_mid mid_scop posttile_scop after_scop
          else
            rejected tt
      end
  end.

Definition try_checked_iss_phase_pipeline_from_poly_poly
    (pol : PolyLang.t)
    (before_scop : OpenScop)
  : imp PolyLang.t :=
  match CoreOpt.infer_iss_from_source_scop pol before_scop with
  | Okk (Some (pol_iss, w)) =>
      if ValidatorCore.checked_iss_complete_cut_shape_validate pol pol_iss w then
        BIND iss_wf <- ValidatorCore.check_wf_polyprog pol_iss -;
        if iss_wf then
          match CoreOpt.export_for_phase_scheduler pol_iss with
          | Some iss_scop =>
              try_phase_pipeline_from_source_pol_poly
                pol_iss CoreOpt.run_pluto_phase_pipeline iss_scop
          | None => reject_tiling tt
          end
        else
          try_phase_pipeline_from_source_pol_poly
            pol
            CoreOpt.run_pluto_phase_pipeline
            before_scop
      else
        try_phase_pipeline_from_source_pol_poly
          pol
          CoreOpt.run_pluto_phase_pipeline
          before_scop
  | _ =>
      try_phase_pipeline_from_source_pol_poly
        pol
        CoreOpt.run_pluto_phase_pipeline
        before_scop
  end.

Definition try_checked_iss_post_tiling_affine_phase_pipeline_from_poly_poly
    (pol : PolyLang.t)
    (before_scop : OpenScop)
  : imp PolyLang.t :=
  match CoreOpt.infer_iss_from_source_scop pol before_scop with
  | Okk (Some (pol_iss, w)) =>
      if ValidatorCore.checked_iss_complete_cut_shape_validate pol pol_iss w then
        BIND iss_wf <- ValidatorCore.check_wf_polyprog pol_iss -;
        if iss_wf then
          match CoreOpt.export_for_phase_scheduler pol_iss with
          | Some iss_scop =>
              try_post_tiling_affine_phase_pipeline_from_source_pol_poly
                pol_iss iss_scop
          | None => reject_tiling tt
          end
        else
          try_post_tiling_affine_phase_pipeline_from_source_pol_poly
            pol
            before_scop
      else
        try_post_tiling_affine_phase_pipeline_from_source_pol_poly
          pol
          before_scop
  | _ =>
      try_post_tiling_affine_phase_pipeline_from_source_pol_poly
        pol
        before_scop
  end.

Definition iss_only_prepared_from_poly
    (pol : PolyLang.t)
  : imp PolyLang.t :=
  match CoreOpt.export_for_phase_scheduler pol with
  | None =>
      pure pol
  | Some before_scop =>
      match CoreOpt.infer_iss_from_source_scop pol before_scop with
      | Okk (Some (pol_iss, w)) =>
          if ValidatorCore.checked_iss_complete_cut_shape_validate pol pol_iss w then
            BIND iss_wf <- ValidatorCore.check_wf_polyprog pol_iss -;
            if iss_wf then pure pol_iss else pure pol
          else
            pure pol
      | _ =>
          pure pol
      end
  end.

Definition iss_affine_prepared_from_poly
    (pol : PolyLang.t)
  : imp PolyLang.t :=
  BIND pol_iss <- iss_only_prepared_from_poly pol -;
  CoreOpt.checked_affine_schedule pol_iss.

Definition phase_pipeline_opt_prepared_from_poly_no_iss_poly
    (pol : PolyLang.t)
  : imp PolyLang.t :=
  if CoreOpt.has_nonscalar_stmt pol then
    match CoreOpt.export_for_phase_scheduler pol with
    | None =>
        reject_tiling tt
    | Some before_scop =>
        try_phase_pipeline_from_source_pol_poly
          pol
          CoreOpt.run_pluto_phase_pipeline
          before_scop
    end
  else
    reject_tiling tt.

Definition phase_pipeline_opt_prepared_from_poly_with_iss_poly
    (pol : PolyLang.t)
  : imp PolyLang.t :=
  if CoreOpt.has_nonscalar_stmt pol then
    match CoreOpt.export_for_phase_scheduler pol with
    | None =>
        reject_tiling tt
    | Some before_scop =>
        try_checked_iss_phase_pipeline_from_poly_poly pol before_scop
    end
  else
    reject_tiling tt.

Definition identity_tiling_opt_prepared_from_poly_no_iss_poly
    (pol : PolyLang.t)
  : imp PolyLang.t :=
  if CoreOpt.has_nonscalar_stmt pol then
    match CoreOpt.export_for_phase_scheduler pol with
    | None =>
        reject_tiling tt
    | Some before_scop =>
        try_identity_tiling_phase_pipeline_from_source_pol_poly
          pol before_scop
    end
  else
    reject_tiling tt.

Definition identity_tiling_opt_prepared_from_poly_with_iss_poly
    (pol : SPolIRs.PolyLang.t)
  : imp SPolIRs.PolyLang.t :=
  BIND pol_iss <- iss_only_prepared_from_poly pol -;
  identity_tiling_opt_prepared_from_poly_no_iss_poly pol_iss.

Definition post_tiling_affine_phase_pipeline_opt_prepared_from_poly_no_iss_poly
    (pol : PolyLang.t)
  : imp PolyLang.t :=
  if CoreOpt.has_nonscalar_stmt pol then
    match CoreOpt.export_for_phase_scheduler pol with
    | None =>
        reject_tiling tt
    | Some before_scop =>
        try_post_tiling_affine_phase_pipeline_from_source_pol_poly pol before_scop
    end
  else
    reject_tiling tt.

Definition post_tiling_affine_phase_pipeline_opt_prepared_from_poly_with_iss_poly
    (pol : PolyLang.t)
  : imp PolyLang.t :=
  if CoreOpt.has_nonscalar_stmt pol then
    match CoreOpt.export_for_phase_scheduler pol with
    | None =>
        reject_tiling tt
    | Some before_scop =>
        try_checked_iss_post_tiling_affine_phase_pipeline_from_poly_poly pol before_scop
    end
  else
    reject_tiling tt.

Definition parallel_current_prepared_from_poly
    (pol : PolyLang.t)
    (d : nat)
  : imp (result ParallelLoop.t) :=
  BIND pol' <- phase_pipeline_opt_prepared_from_poly_no_iss_poly pol -;
  checked_parallel_current_annotated_codegen_at pol' d.

Definition parallel_current_identity_tiled_prepared_from_poly
    (pol : PolyLang.t)
    (d : nat)
  : imp (result ParallelLoop.t) :=
  BIND pol' <- identity_tiling_opt_prepared_from_poly_no_iss_poly pol -;
  checked_parallel_current_annotated_codegen_at pol' d.

Definition parallel_current_identity_tiled_prepared_from_poly_with_iss
    (pol : SPolIRs.PolyLang.t)
    (d : nat)
  : imp (result ParallelCodegenCore.ParallelLoop.t) :=
  BIND pol' <- identity_tiling_opt_prepared_from_poly_with_iss_poly pol -;
  checked_parallel_current_annotated_codegen_at pol' d.

Definition parallel_current_post_tiling_affine_prepared_from_poly
    (pol : PolyLang.t)
    (d : nat)
  : imp (result ParallelLoop.t) :=
  BIND pol' <- post_tiling_affine_phase_pipeline_opt_prepared_from_poly_no_iss_poly pol -;
  checked_parallel_current_annotated_codegen_at pol' d.

Definition parallel_current_post_tiling_affine_prepared_from_poly_with_iss
    (pol : PolyLang.t)
    (d : nat)
  : imp (result ParallelLoop.t) :=
  BIND pol' <- post_tiling_affine_phase_pipeline_opt_prepared_from_poly_with_iss_poly pol -;
  checked_parallel_current_annotated_codegen_at pol' d.

Definition parallel_current_many_post_tiling_affine_prepared_from_poly
    (pol : PolyLang.t)
    (dims : list nat)
  : imp (result ParallelLoop.t) :=
  BIND pol' <- post_tiling_affine_phase_pipeline_opt_prepared_from_poly_no_iss_poly pol -;
  checked_parallel_current_many_annotated_codegen_at pol' dims.

Definition parallel_current_many_post_tiling_affine_prepared_from_poly_with_iss
    (pol : PolyLang.t)
    (dims : list nat)
  : imp (result ParallelLoop.t) :=
  BIND pol' <- post_tiling_affine_phase_pipeline_opt_prepared_from_poly_with_iss_poly pol -;
  checked_parallel_current_many_annotated_codegen_at pol' dims.

Definition parallel_current_identity_prepared_from_poly_with_iss
    (pol : PolyLang.t)
    (d : nat)
  : imp (result ParallelLoop.t) :=
  BIND pol' <- iss_only_prepared_from_poly pol -;
  checked_parallel_current_annotated_codegen_at pol' d.

Definition parallel_current_affine_prepared_from_poly_with_iss
    (pol : PolyLang.t)
    (d : nat)
  : imp (result ParallelLoop.t) :=
  BIND pol' <- iss_affine_prepared_from_poly pol -;
  checked_parallel_current_annotated_codegen_at pol' d.

Definition parallel_current_prepared_from_poly_with_iss
    (pol : PolyLang.t)
    (d : nat)
  : imp (result ParallelLoop.t) :=
  BIND pol' <- phase_pipeline_opt_prepared_from_poly_with_iss_poly pol -;
  checked_parallel_current_annotated_codegen_at pol' d.

Definition parallel_current_many_identity_prepared_from_poly
    (pol : PolyLang.t)
    (dims : list nat)
  : imp (result ParallelLoop.t) :=
  checked_parallel_current_many_annotated_codegen_at pol dims.

Definition parallel_current_many_identity_tiled_prepared_from_poly
    (pol : PolyLang.t)
    (dims : list nat)
  : imp (result ParallelLoop.t) :=
  BIND pol' <- identity_tiling_opt_prepared_from_poly_no_iss_poly pol -;
  checked_parallel_current_many_annotated_codegen_at pol' dims.

Definition parallel_current_many_identity_tiled_prepared_from_poly_with_iss
    (pol : SPolIRs.PolyLang.t)
    (dims : list nat)
  : imp (result ParallelCodegenCore.ParallelLoop.t) :=
  BIND pol' <- identity_tiling_opt_prepared_from_poly_with_iss_poly pol -;
  checked_parallel_current_many_annotated_codegen_at pol' dims.

Definition parallel_current_many_affine_prepared_from_poly
    (pol : PolyLang.t)
    (dims : list nat)
  : imp (result ParallelLoop.t) :=
  BIND pol' <- CoreOpt.checked_affine_schedule pol -;
  checked_parallel_current_many_annotated_codegen_at pol' dims.

Definition parallel_current_many_prepared_from_poly
    (pol : PolyLang.t)
    (dims : list nat)
  : imp (result ParallelLoop.t) :=
  BIND pol' <- phase_pipeline_opt_prepared_from_poly_no_iss_poly pol -;
  checked_parallel_current_many_annotated_codegen_at pol' dims.

Definition parallel_current_many_identity_prepared_from_poly_with_iss
    (pol : PolyLang.t)
    (dims : list nat)
  : imp (result ParallelLoop.t) :=
  BIND pol' <- iss_only_prepared_from_poly pol -;
  checked_parallel_current_many_annotated_codegen_at pol' dims.

Definition parallel_current_many_affine_prepared_from_poly_with_iss
    (pol : PolyLang.t)
    (dims : list nat)
  : imp (result ParallelLoop.t) :=
  BIND pol' <- iss_affine_prepared_from_poly pol -;
  checked_parallel_current_many_annotated_codegen_at pol' dims.

Definition parallel_current_many_prepared_from_poly_with_iss
    (pol : PolyLang.t)
    (dims : list nat)
  : imp (result ParallelLoop.t) :=
  BIND pol' <- phase_pipeline_opt_prepared_from_poly_with_iss_poly pol -;
  checked_parallel_current_many_annotated_codegen_at pol' dims.

Definition vector_current_identity_prepared_from_poly
    (pol : PolyLang.t)
    (d : nat)
  : imp (result ParallelLoop.t) :=
  checked_vector_current_annotated_codegen_at pol d.

Definition vector_current_affine_prepared_from_poly
    (pol : PolyLang.t)
    (d : nat)
  : imp (result ParallelLoop.t) :=
  BIND pol' <- CoreOpt.checked_affine_schedule pol -;
  checked_vector_current_annotated_codegen_at pol' d.

Definition vector_current_prepared_from_poly
    (pol : PolyLang.t)
    (d : nat)
  : imp (result ParallelLoop.t) :=
  BIND pol' <- phase_pipeline_opt_prepared_from_poly_no_iss_poly pol -;
  checked_vector_current_annotated_codegen_at pol' d.

Definition vector_current_identity_tiled_prepared_from_poly
    (pol : PolyLang.t)
    (d : nat)
  : imp (result ParallelLoop.t) :=
  BIND pol' <- identity_tiling_opt_prepared_from_poly_no_iss_poly pol -;
  checked_vector_current_annotated_codegen_at pol' d.

Definition vector_current_identity_tiled_prepared_from_poly_with_iss
    (pol : SPolIRs.PolyLang.t)
    (d : nat)
  : imp (result ParallelCodegenCore.ParallelLoop.t) :=
  BIND pol' <- identity_tiling_opt_prepared_from_poly_with_iss_poly pol -;
  checked_vector_current_annotated_codegen_at pol' d.

Definition vector_current_post_tiling_affine_prepared_from_poly
    (pol : PolyLang.t)
    (d : nat)
  : imp (result ParallelLoop.t) :=
  BIND pol' <- post_tiling_affine_phase_pipeline_opt_prepared_from_poly_no_iss_poly pol -;
  checked_vector_current_annotated_codegen_at pol' d.

Definition vector_current_post_tiling_affine_prepared_from_poly_with_iss
    (pol : PolyLang.t)
    (d : nat)
  : imp (result ParallelLoop.t) :=
  BIND pol' <- post_tiling_affine_phase_pipeline_opt_prepared_from_poly_with_iss_poly pol -;
  checked_vector_current_annotated_codegen_at pol' d.

Definition vector_current_identity_prepared_from_poly_with_iss
    (pol : PolyLang.t)
    (d : nat)
  : imp (result ParallelLoop.t) :=
  BIND pol' <- iss_only_prepared_from_poly pol -;
  checked_vector_current_annotated_codegen_at pol' d.

Definition vector_current_affine_prepared_from_poly_with_iss
    (pol : PolyLang.t)
    (d : nat)
  : imp (result ParallelLoop.t) :=
  BIND pol' <- iss_affine_prepared_from_poly pol -;
  checked_vector_current_annotated_codegen_at pol' d.

Definition vector_current_prepared_from_poly_with_iss
    (pol : PolyLang.t)
    (d : nat)
  : imp (result ParallelLoop.t) :=
  BIND pol' <- phase_pipeline_opt_prepared_from_poly_with_iss_poly pol -;
  checked_vector_current_annotated_codegen_at pol' d.

Definition parallel_dummy : ParallelLoop.t :=
  ParallelCodegenCore.tag_loop LoopIR.dummy.

Definition opt_parallel_current_identity
    (loop : LoopIR.t)
    (d : nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- parallel_current_identity_prepared_from_poly pol d -;
  res_to_alarm parallel_dummy res.
Definition opt_parallel_current_identity_tiled
    (loop : LoopIR.t)
    (d : nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- parallel_current_identity_tiled_prepared_from_poly pol d -;
  res_to_alarm parallel_dummy res.

Definition opt_parallel_current_identity_tiled_with_iss
    (loop : LoopIR.t)
    (d : nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- parallel_current_identity_tiled_prepared_from_poly_with_iss pol d -;
  res_to_alarm parallel_dummy res.

Definition opt_parallel_current_affine
    (loop : LoopIR.t)
    (d : nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- parallel_current_affine_prepared_from_poly pol d -;
  res_to_alarm parallel_dummy res.

Definition opt_parallel_current
    (loop : LoopIR.t)
    (d : nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- parallel_current_prepared_from_poly pol d -;
  res_to_alarm parallel_dummy res.

Definition opt_parallel_current_post_tiling_affine
    (loop : LoopIR.t)
    (d : nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- parallel_current_post_tiling_affine_prepared_from_poly pol d -;
  res_to_alarm parallel_dummy res.

Definition opt_parallel_current_post_tiling_affine_with_iss
    (loop : LoopIR.t)
    (d : nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- parallel_current_post_tiling_affine_prepared_from_poly_with_iss pol d -;
  res_to_alarm parallel_dummy res.

Definition opt_parallel_current_many_post_tiling_affine
    (loop : LoopIR.t)
    (dims : list nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- parallel_current_many_post_tiling_affine_prepared_from_poly pol dims -;
  res_to_alarm parallel_dummy res.

Definition opt_parallel_current_many_post_tiling_affine_with_iss
    (loop : LoopIR.t)
    (dims : list nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- parallel_current_many_post_tiling_affine_prepared_from_poly_with_iss pol dims -;
  res_to_alarm parallel_dummy res.

Definition opt_parallel_current_many_identity
    (loop : LoopIR.t)
    (dims : list nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- parallel_current_many_identity_prepared_from_poly pol dims -;
  res_to_alarm parallel_dummy res.

Definition opt_parallel_current_many_identity_tiled
    (loop : LoopIR.t)
    (dims : list nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- parallel_current_many_identity_tiled_prepared_from_poly pol dims -;
  res_to_alarm parallel_dummy res.

Definition opt_parallel_current_many_identity_tiled_with_iss
    (loop : LoopIR.t)
    (dims : list nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- parallel_current_many_identity_tiled_prepared_from_poly_with_iss pol dims -;
  res_to_alarm parallel_dummy res.

Definition opt_parallel_current_many_affine
    (loop : LoopIR.t)
    (dims : list nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- parallel_current_many_affine_prepared_from_poly pol dims -;
  res_to_alarm parallel_dummy res.

Definition opt_parallel_current_many
    (loop : LoopIR.t)
    (dims : list nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- parallel_current_many_prepared_from_poly pol dims -;
  res_to_alarm parallel_dummy res.

Definition opt_parallel_current_many_identity_with_iss
    (loop : LoopIR.t)
    (dims : list nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- parallel_current_many_identity_prepared_from_poly_with_iss pol dims -;
  res_to_alarm parallel_dummy res.

Definition opt_parallel_current_many_affine_with_iss
    (loop : LoopIR.t)
    (dims : list nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- parallel_current_many_affine_prepared_from_poly_with_iss pol dims -;
  res_to_alarm parallel_dummy res.

Definition opt_parallel_current_many_with_iss
    (loop : LoopIR.t)
    (dims : list nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- parallel_current_many_prepared_from_poly_with_iss pol dims -;
  res_to_alarm parallel_dummy res.

Definition opt_parallel_current_identity_with_iss
    (loop : LoopIR.t)
    (d : nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- parallel_current_identity_prepared_from_poly_with_iss pol d -;
  res_to_alarm parallel_dummy res.

Definition opt_parallel_current_affine_with_iss
    (loop : LoopIR.t)
    (d : nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- parallel_current_affine_prepared_from_poly_with_iss pol d -;
  res_to_alarm parallel_dummy res.

Definition opt_parallel_current_with_iss
    (loop : LoopIR.t)
    (d : nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- parallel_current_prepared_from_poly_with_iss pol d -;
  res_to_alarm parallel_dummy res.

Definition opt_vector_current_identity
    (loop : LoopIR.t)
    (d : nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- vector_current_identity_prepared_from_poly pol d -;
  res_to_alarm parallel_dummy res.

Definition opt_vector_current_identity_tiled
    (loop : LoopIR.t)
    (d : nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- vector_current_identity_tiled_prepared_from_poly pol d -;
  res_to_alarm parallel_dummy res.

Definition opt_vector_current_identity_tiled_with_iss
    (loop : LoopIR.t)
    (d : nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- vector_current_identity_tiled_prepared_from_poly_with_iss pol d -;
  res_to_alarm parallel_dummy res.

Definition opt_vector_current_affine
    (loop : LoopIR.t)
    (d : nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- vector_current_affine_prepared_from_poly pol d -;
  res_to_alarm parallel_dummy res.

Definition opt_vector_current
    (loop : LoopIR.t)
    (d : nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- vector_current_prepared_from_poly pol d -;
  res_to_alarm parallel_dummy res.

Definition opt_vector_current_post_tiling_affine
    (loop : LoopIR.t)
    (d : nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- vector_current_post_tiling_affine_prepared_from_poly pol d -;
  res_to_alarm parallel_dummy res.

Definition opt_vector_current_post_tiling_affine_with_iss
    (loop : LoopIR.t)
    (d : nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- vector_current_post_tiling_affine_prepared_from_poly_with_iss pol d -;
  res_to_alarm parallel_dummy res.

Definition opt_vector_current_identity_with_iss
    (loop : LoopIR.t)
    (d : nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- vector_current_identity_prepared_from_poly_with_iss pol d -;
  res_to_alarm parallel_dummy res.

Definition opt_vector_current_affine_with_iss
    (loop : LoopIR.t)
    (d : nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- vector_current_affine_prepared_from_poly_with_iss pol d -;
  res_to_alarm parallel_dummy res.

Definition opt_vector_current_with_iss
    (loop : LoopIR.t)
    (d : nat)
  : imp ParallelLoop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  BIND res <- vector_current_prepared_from_poly_with_iss pol d -;
  res_to_alarm parallel_dummy res.

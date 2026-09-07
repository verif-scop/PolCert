Require Import SPolIRs.
Require Import STilingBandSched.
Require Import SBandTilingOptShared.
Require Import OpenScop.
Require Import Result.
Require Import String.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Open Scope impure_scope.
Open Scope opt_scop.
Local Open Scope string_scope.

Module CoreOpt := SBandTilingOptShared.BandGeneric.BaseOpt.
Module PolyLang := SBandTilingOptShared.BandGeneric.PolyLang.
Module TilingSched := SBandTilingOptShared.BandGeneric.TilingSched.

Definition tiling_validation_route_label
    (route: TilingSched.tiling_band_validation_route) : string :=
  match route with
  | TilingSched.DirectBandAccepted => "permutable-band"
  | TilingSched.GeneralScheduleAccepted => "actual-schedule"
  | TilingSched.Rejected => "rejected"
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
Proof.
  reflexivity.
Qed.

Definition reject_tiling (_: unit) : imp SPolIRs.Loop.t :=
  match observe_tiling_validation_route TilingSched.Rejected with
  | TilingSched.Rejected =>
      res_to_alarm SPolIRs.Loop.dummy
        (Err "Tiling validation rejected or unavailable.")
  | TilingSched.DirectBandAccepted | TilingSched.GeneralScheduleAccepted =>
      res_to_alarm SPolIRs.Loop.dummy
        (Err "Impossible accepted result while recording tiling rejection.")
  end.

Definition prepared_codegen_after_tiling_route
    (pol_after: PolyLang.t)
    (route: TilingSched.tiling_band_validation_route)
  : imp SPolIRs.Loop.t :=
  match route with
  | TilingSched.DirectBandAccepted | TilingSched.GeneralScheduleAccepted =>
      CoreOpt.PrepareCore.prepared_codegen
        (PolyLang.current_view_pprog pol_after)
  | TilingSched.Rejected =>
      res_to_alarm SPolIRs.Loop.dummy
        (Err "Tiling validation rejected.")
  end.

Definition reject_post_tiling_affine
    (route: TilingSched.tiling_band_validation_route)
    (_: unit) : imp SPolIRs.Loop.t :=
  match route with
  | TilingSched.DirectBandAccepted | TilingSched.GeneralScheduleAccepted =>
      res_to_alarm SPolIRs.Loop.dummy
        (Err "Post-tiling affine validation failed.")
  | TilingSched.Rejected =>
      res_to_alarm SPolIRs.Loop.dummy
        (Err "Post-tiling affine validation failed.")
  end.

Definition try_verified_tiling_after_phase_mid_band
    (pol_mid: PolyLang.t)
    (mid_scop after_scop: OpenScop) : imp SPolIRs.Loop.t :=
  let rejected :=
    reject_tiling in
  match CoreOpt.infer_tiling_witness_scops mid_scop after_scop with
  | Err _ =>
      rejected tt
  | Okk ws =>
      match CoreOpt.ValidatorCore.import_canonical_tiled_after_poly pol_mid after_scop ws with
      | Err _ =>
          rejected tt
      | Okk pol_after =>
          BIND route <-
            TilingSched
              .checked_tiling_schedule_sourceb_first_runtime_validate_route
              pol_mid pol_after ws -;
          match route with
          | TilingSched.DirectBandAccepted | TilingSched.GeneralScheduleAccepted =>
              BIND wf_after <-
                CoreOpt.ValidatorCore.check_wf_polyprog_general
                  pol_after -;
              if wf_after then
                prepared_codegen_after_tiling_route
                  pol_after
                  (observe_tiling_validation_route route)
              else
                rejected tt
          | TilingSched.Rejected =>
              rejected tt
          end
      end
  end.
Definition try_phase_pipeline_from_source_pol_band
    (pol_source: PolyLang.t)
    (phase_runner: OpenScop -> result (OpenScop * OpenScop))
    (before_scop: OpenScop) : imp SPolIRs.Loop.t :=
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
          BIND affine_ok <- CoreOpt.ValidatorCore.validate pol_source pol_mid -;
          if affine_ok then
            try_verified_tiling_after_phase_mid_band pol_mid mid_scop after_scop
          else
            rejected tt
      end
  end.

Definition try_identity_phase_pipeline_from_source_pol_band
    (pol_source: PolyLang.t)
    (phase_runner: OpenScop -> result (OpenScop * OpenScop))
    (before_scop: OpenScop) : imp SPolIRs.Loop.t :=
  let rejected :=
    reject_tiling in
  match phase_runner before_scop with
  | Err _ =>
      rejected tt
  | Okk (mid_scop, after_scop) =>
      match PolyLang.from_openscop_like_source pol_source mid_scop with
      | Err _ =>
          rejected tt
      | Okk pol_mid =>
          BIND affine_ok <- CoreOpt.ValidatorCore.validate pol_source pol_mid -;
          if affine_ok then
            try_verified_tiling_after_phase_mid_band pol_mid mid_scop after_scop
          else
            rejected tt
      end
  end.

Definition try_verified_post_tiling_affine_after_phase_mid_band
    (pol_mid: PolyLang.t)
    (mid_scop posttile_scop after_scop: OpenScop) : imp SPolIRs.Loop.t :=
  let rejected :=
    reject_tiling in
  match CoreOpt.infer_tiling_witness_scops mid_scop posttile_scop with
  | Err _ =>
      rejected tt
  | Okk ws =>
      match CoreOpt.ValidatorCore.import_canonical_tiled_after_poly pol_mid posttile_scop ws with
      | Err _ =>
          rejected tt
      | Okk pol_posttile =>
          BIND route <-
            TilingSched
              .checked_tiling_schedule_sourceb_first_runtime_validate_route
              pol_mid pol_posttile ws -;
          match route with
          | TilingSched.DirectBandAccepted | TilingSched.GeneralScheduleAccepted =>
              BIND wf_posttile <-
                CoreOpt.ValidatorCore.check_wf_polyprog_general
                  pol_posttile -;
              if wf_posttile then
                let route := observe_tiling_validation_route route in
                match PolyLang.from_openscop_schedule_only
                        pol_posttile after_scop with
                | Err _ =>
                    reject_post_tiling_affine route tt
                | Okk pol_after =>
                    BIND final_ok <-
                      CoreOpt.ValidatorCore.validate_general
                        pol_posttile pol_after -;
                    if final_ok then
                      BIND wf_after <-
                        CoreOpt.ValidatorCore.check_wf_polyprog_general
                          pol_after -;
                      if wf_after then
                        prepared_codegen_after_tiling_route
                          pol_after route
                      else
                        reject_post_tiling_affine route tt
                    else
                      reject_post_tiling_affine route tt
                end
              else
                rejected tt
          | TilingSched.Rejected =>
              rejected tt
          end
      end
  end.

Definition try_post_tiling_affine_phase_pipeline_from_source_pol_band
    (pol_source: PolyLang.t)
    (before_scop: OpenScop) : imp SPolIRs.Loop.t :=
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
          BIND affine_ok <- CoreOpt.ValidatorCore.validate pol_source pol_mid -;
          if affine_ok then
            try_verified_post_tiling_affine_after_phase_mid_band
              pol_mid mid_scop posttile_scop after_scop
          else
            rejected tt
      end
  end.

Definition try_post_tiling_affine_phase_pipeline_from_source_pol_band_with_iss
    (pol_source: PolyLang.t)
    (before_scop: OpenScop) : imp SPolIRs.Loop.t :=
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
          BIND affine_ok <- CoreOpt.ValidatorCore.validate pol_source pol_mid -;
          if affine_ok then
            try_verified_post_tiling_affine_after_phase_mid_band
              pol_mid mid_scop posttile_scop after_scop
          else
            rejected tt
      end
  end.

Definition try_checked_iss_post_tiling_affine_phase_pipeline_from_poly_band
    (pol: PolyLang.t)
    (before_scop: OpenScop) : imp SPolIRs.Loop.t :=
  match CoreOpt.infer_iss_from_source_scop pol before_scop with
  | Okk (Some (pol_iss, w)) =>
      if CoreOpt.ValidatorCore.checked_iss_complete_cut_shape_validate pol pol_iss w then
        BIND iss_wf <- CoreOpt.ValidatorCore.check_wf_polyprog pol_iss -;
        if iss_wf then
          match CoreOpt.export_for_phase_scheduler pol_iss with
          | Some iss_scop =>
              try_post_tiling_affine_phase_pipeline_from_source_pol_band
                pol_iss iss_scop
          | None => reject_tiling tt
          end
        else
          try_post_tiling_affine_phase_pipeline_from_source_pol_band pol before_scop
      else
        try_post_tiling_affine_phase_pipeline_from_source_pol_band pol before_scop
  | _ =>
      try_post_tiling_affine_phase_pipeline_from_source_pol_band pol before_scop
  end.

Definition try_checked_iss_phase_pipeline_from_poly_band
    (pol: PolyLang.t)
    (before_scop: OpenScop) : imp SPolIRs.Loop.t :=
  match CoreOpt.infer_iss_from_source_scop pol before_scop with
  | Okk (Some (pol_iss, w)) =>
      if CoreOpt.ValidatorCore.checked_iss_complete_cut_shape_validate pol pol_iss w then
        BIND iss_wf <- CoreOpt.ValidatorCore.check_wf_polyprog pol_iss -;
        if iss_wf then
          match CoreOpt.export_for_phase_scheduler pol_iss with
          | Some iss_scop =>
              try_phase_pipeline_from_source_pol_band
                pol_iss CoreOpt.run_pluto_phase_pipeline iss_scop
          | None => reject_tiling tt
          end
        else
          try_phase_pipeline_from_source_pol_band
            pol
            CoreOpt.run_pluto_phase_pipeline
            before_scop
      else
        try_phase_pipeline_from_source_pol_band
          pol
          CoreOpt.run_pluto_phase_pipeline
          before_scop
  | _ =>
      try_phase_pipeline_from_source_pol_band
        pol
        CoreOpt.run_pluto_phase_pipeline
        before_scop
  end.

Definition opt (loop : SPolIRs.Loop.t) : imp SPolIRs.Loop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  if CoreOpt.has_nonscalar_stmt pol then
    match CoreOpt.export_for_phase_scheduler pol with
    | Some before_scop =>
        try_phase_pipeline_from_source_pol_band
          pol
          CoreOpt.run_pluto_phase_pipeline
          before_scop
    | None =>
        reject_tiling tt
    end
  else
    reject_tiling tt.

Definition opt_with_iss (loop : SPolIRs.Loop.t) : imp SPolIRs.Loop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  if CoreOpt.has_nonscalar_stmt pol then
    match CoreOpt.export_for_phase_scheduler pol with
    | Some before_scop =>
        try_checked_iss_phase_pipeline_from_poly_band pol before_scop
    | None =>
        reject_tiling tt
    end
  else
    reject_tiling tt.

Definition opt_identity_tiled_from_poly
    (pol: PolyLang.t) : imp SPolIRs.Loop.t :=
  if CoreOpt.has_nonscalar_stmt pol then
    match CoreOpt.export_for_phase_scheduler pol with
    | Some before_scop =>
        try_identity_phase_pipeline_from_source_pol_band
          pol
          CoreOpt.run_pluto_identity_tiling_pipeline
          before_scop
    | None =>
        reject_tiling tt
    end
  else
    reject_tiling tt.

Definition opt_identity_tiled (loop : SPolIRs.Loop.t) : imp SPolIRs.Loop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  opt_identity_tiled_from_poly pol.

Definition try_checked_iss_identity_tiling_phase_pipeline_from_poly_band
    (pol: PolyLang.t)
    (before_scop: OpenScop) : imp SPolIRs.Loop.t :=
  match CoreOpt.infer_iss_from_source_scop pol before_scop with
  | Okk (Some (pol_iss, w)) =>
      if CoreOpt.ValidatorCore.checked_iss_complete_cut_shape_validate pol pol_iss w then
        BIND iss_wf <- CoreOpt.ValidatorCore.check_wf_polyprog pol_iss -;
        if iss_wf then
          match CoreOpt.export_for_phase_scheduler pol_iss with
          | Some iss_scop =>
              try_identity_phase_pipeline_from_source_pol_band
                pol_iss
                CoreOpt.run_pluto_identity_tiling_pipeline
                iss_scop
          | None =>
              reject_tiling tt
          end
        else
          opt_identity_tiled_from_poly pol
      else
        opt_identity_tiled_from_poly pol
  | _ =>
      opt_identity_tiled_from_poly pol
  end.

Definition opt_identity_tiled_with_iss (loop : SPolIRs.Loop.t) : imp SPolIRs.Loop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  if CoreOpt.has_nonscalar_stmt pol then
    match CoreOpt.export_for_phase_scheduler pol with
    | Some before_scop =>
        try_checked_iss_identity_tiling_phase_pipeline_from_poly_band
          pol before_scop
    | None =>
        reject_tiling tt
    end
  else
    reject_tiling tt.

Definition opt_post_tiling_affine (loop : SPolIRs.Loop.t) : imp SPolIRs.Loop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  if CoreOpt.has_nonscalar_stmt pol then
    match CoreOpt.export_for_phase_scheduler pol with
    | Some before_scop =>
        try_post_tiling_affine_phase_pipeline_from_source_pol_band pol before_scop
    | None =>
        reject_tiling tt
    end
  else
    reject_tiling tt.

Definition opt_post_tiling_affine_with_iss (loop : SPolIRs.Loop.t) : imp SPolIRs.Loop.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
  let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
  if CoreOpt.has_nonscalar_stmt pol then
    match CoreOpt.export_for_phase_scheduler pol with
    | Some before_scop =>
        try_checked_iss_post_tiling_affine_phase_pipeline_from_poly_band pol before_scop
    | None =>
        reject_tiling tt
    end
  else
    reject_tiling tt.

Definition opt_prepared (loop : SPolIRs.Loop.t) : imp SPolIRs.Loop.t :=
  opt loop.

Definition opt_post_tiling_affine_prepared (loop : SPolIRs.Loop.t) : imp SPolIRs.Loop.t :=
  opt_post_tiling_affine loop.

Definition opt_post_tiling_affine_with_iss_prepared (loop : SPolIRs.Loop.t) : imp SPolIRs.Loop.t :=
  opt_post_tiling_affine_with_iss loop.

Definition opt_poly (pol : PolyLang.t) : imp SPolIRs.Loop.t :=
  let pol' := CoreOpt.Strengthen.strengthen_pprog pol in
  if CoreOpt.has_nonscalar_stmt pol' then
    match CoreOpt.export_for_phase_scheduler pol' with
    | Some before_scop =>
        try_phase_pipeline_from_source_pol_band
          pol'
          CoreOpt.run_pluto_phase_pipeline
          before_scop
    | None =>
        reject_tiling tt
    end
  else
    reject_tiling tt.

Definition opt_post_tiling_affine_poly (pol : PolyLang.t) : imp SPolIRs.Loop.t :=
  let pol' := CoreOpt.Strengthen.strengthen_pprog pol in
  if CoreOpt.has_nonscalar_stmt pol' then
    match CoreOpt.export_for_phase_scheduler pol' with
    | Some before_scop =>
        try_post_tiling_affine_phase_pipeline_from_source_pol_band pol' before_scop
    | None =>
        reject_tiling tt
    end
  else
    reject_tiling tt.

Definition opt_scop (scop : OpenScop) : imp SPolIRs.Loop.t :=
  match PolyLang.from_openscop_complete scop with
  | Okk pol => opt_poly pol
  | Err msg => res_to_alarm SPolIRs.Loop.dummy (Err msg)
  end.

Definition opt_post_tiling_affine_scop (scop : OpenScop) : imp SPolIRs.Loop.t :=
  match PolyLang.from_openscop_complete scop with
  | Okk pol => opt_post_tiling_affine_poly pol
  | Err msg => res_to_alarm SPolIRs.Loop.dummy (Err msg)
  end.

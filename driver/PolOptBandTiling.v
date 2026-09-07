Require Import TilingBandDirectRuntime.
Require Import TilingWitness.
Require Import PolIRs.
Require Import OpenScop.
Require Import Result.
Require Import String.
Require Import PolOpt.
Require Import ISSValidatorCorrect.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Module PolOptBandTiling (PolIRs: POLIRS).

Module BaseOpt := PolOpt PolIRs.
Module ValidatorCore := BaseOpt.ValidatorCore.
Module PrepareCore := BaseOpt.PrepareCore.
Module TilingSched : TILING_BAND_DIRECT_RUNTIME_API PolIRs :=
  TilingBandDirectRuntime PolIRs.
Module ISSValidatorCorrectCore := ISSValidatorCorrect PolIRs.
Module PolyLang := PolIRs.PolyLang.
Module LoopIR := PolIRs.Loop.
Module State := PolIRs.State.

Open Scope impure_scope.
Open Scope opt_scop.
Local Open Scope string_scope.

(** * Proof map

    The definitions first build verified affine, ISS, tiling, and post_tiling_affine
    routes over polyhedral programs.  Their [*_from_poly_*_correct] lemmas
    compose the corresponding validators with code generation.  The public
    loop-to-loop theorems finally undo strengthening and invoke the extractor
    theorem; [lift_frontend_correct] packages that common typed closure.

    Rejection branches are fail-closed: a [mayReturn] premise for an alarm is
    contradictory.  Only accepted branches carry semantic obligations. *)

Definition reject_tiling (_: unit): imp LoopIR.t :=
  res_to_alarm LoopIR.dummy
    (Err "Tiling validation rejected or unavailable.").

Definition prepared_codegen_after_tiling_route
    (pol_after: PolyLang.t)
    (route: TilingSched.tiling_band_validation_route): imp LoopIR.t :=
  match route with
  | TilingSched.DirectBandAccepted | TilingSched.GeneralScheduleAccepted =>
      PrepareCore.prepared_codegen
        (PolyLang.current_view_pprog pol_after)
  | TilingSched.Rejected =>
      res_to_alarm LoopIR.dummy
        (Err "Tiling validation rejected.")
  end.

Definition reject_post_tiling_affine
    (route: TilingSched.tiling_band_validation_route)
    (_: unit): imp LoopIR.t :=
  match route with
  | TilingSched.DirectBandAccepted | TilingSched.GeneralScheduleAccepted =>
      res_to_alarm LoopIR.dummy
        (Err "Post-tiling affine validation failed.")
  | TilingSched.Rejected =>
      res_to_alarm LoopIR.dummy
        (Err "Post-tiling affine validation failed.")
  end.

Local Lemma reject_tiling_impossible:
  forall (loop': LoopIR.t),
    mayReturn (reject_tiling tt) loop' -> False.
Proof.
  intros loop' Hret.
  unfold reject_tiling, res_to_alarm in Hret.
  eapply mayReturn_alarm in Hret.
  exact Hret.
Qed.

Local Lemma reject_post_tiling_affine_impossible:
  forall route (loop': LoopIR.t),
    mayReturn (reject_post_tiling_affine route tt) loop' -> False.
Proof.
  intros route loop' Hret.
  destruct route;
    unfold reject_post_tiling_affine, res_to_alarm in Hret;
    eapply mayReturn_alarm in Hret;
    exact Hret.
Qed.

Definition try_verified_tiling_after_phase_mid_band
    (pol_mid: PolyLang.t)
    (mid_scop after_scop: OpenScop): imp LoopIR.t :=
  let rejected := reject_tiling in
  match BaseOpt.infer_tiling_witness_scops mid_scop after_scop with
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
                prepared_codegen_after_tiling_route pol_after route
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
    (before_scop: OpenScop): imp LoopIR.t :=
  let rejected := reject_tiling in
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
            try_verified_tiling_after_phase_mid_band pol_mid mid_scop after_scop
          else
            rejected tt
      end
  end.

Definition try_identity_phase_pipeline_from_source_pol_band
    (pol_source: PolyLang.t)
    (phase_runner: OpenScop -> result (OpenScop * OpenScop))
    (before_scop: OpenScop): imp LoopIR.t :=
  let rejected := reject_tiling in
  match phase_runner before_scop with
  | Err _ =>
      rejected tt
  | Okk (mid_scop, after_scop) =>
      match PolyLang.from_openscop_like_source pol_source mid_scop with
      | Err _ =>
          rejected tt
      | Okk pol_mid =>
          BIND affine_ok <- ValidatorCore.validate pol_source pol_mid -;
          if affine_ok then
            try_verified_tiling_after_phase_mid_band pol_mid mid_scop after_scop
          else
            rejected tt
      end
  end.

Definition try_verified_post_tiling_affine_after_phase_mid_band
    (pol_mid: PolyLang.t)
    (mid_scop posttile_scop after_scop: OpenScop): imp LoopIR.t :=
  let rejected := reject_tiling in
  match BaseOpt.infer_tiling_witness_scops mid_scop posttile_scop with
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
                match PolyLang.from_openscop_schedule_only pol_posttile after_scop with
                | Err _ =>
                    reject_post_tiling_affine route tt
                | Okk pol_after =>
                    BIND final_ok <-
                      ValidatorCore.validate_general pol_posttile pol_after -;
                    if final_ok then
                      BIND wf_after <-
                        ValidatorCore.check_wf_polyprog_general pol_after -;
                      if wf_after then
                        prepared_codegen_after_tiling_route pol_after route
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
    (before_scop: OpenScop): imp LoopIR.t :=
  let rejected := reject_tiling in
  match BaseOpt.run_pluto_post_tiling_affine_phase_pipeline before_scop with
  | Err _ =>
      rejected tt
  | Okk (mid_scop, (posttile_scop, after_scop)) =>
      match PolyLang.from_openscop_schedule_only pol_source mid_scop with
      | Err _ =>
          rejected tt
      | Okk pol_mid =>
          BIND affine_ok <- ValidatorCore.validate pol_source pol_mid -;
          if affine_ok then
            try_verified_post_tiling_affine_after_phase_mid_band
              pol_mid mid_scop posttile_scop after_scop
          else
            rejected tt
      end
  end.

Definition try_post_tiling_affine_phase_pipeline_from_source_pol_band_with_iss
    (pol_source: PolyLang.t)
    (before_scop: OpenScop): imp LoopIR.t :=
  let rejected := reject_tiling in
  match BaseOpt.run_pluto_post_tiling_affine_phase_pipeline_with_iss before_scop with
  | Err _ =>
      rejected tt
  | Okk (mid_scop, (posttile_scop, after_scop)) =>
      match PolyLang.from_openscop_schedule_only pol_source mid_scop with
      | Err _ =>
          rejected tt
      | Okk pol_mid =>
          BIND affine_ok <- ValidatorCore.validate pol_source pol_mid -;
          if affine_ok then
            try_verified_post_tiling_affine_after_phase_mid_band
              pol_mid mid_scop posttile_scop after_scop
          else
            rejected tt
      end
  end.

Definition try_checked_iss_post_tiling_affine_phase_pipeline_from_poly_band
    (pol: PolyLang.t)
    (before_scop: OpenScop): imp LoopIR.t :=
  match BaseOpt.infer_iss_from_source_scop pol before_scop with
  | Okk (Some (pol_iss, w)) =>
      if ValidatorCore.checked_iss_complete_cut_shape_validate pol pol_iss w then
        BIND iss_wf <- ValidatorCore.check_wf_polyprog pol_iss -;
        if iss_wf then
          match BaseOpt.export_for_phase_scheduler pol_iss with
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
    (before_scop: OpenScop): imp LoopIR.t :=
  match BaseOpt.infer_iss_from_source_scop pol before_scop with
  | Okk (Some (pol_iss, w)) =>
      if ValidatorCore.checked_iss_complete_cut_shape_validate pol pol_iss w then
        BIND iss_wf <- ValidatorCore.check_wf_polyprog pol_iss -;
        if iss_wf then
          match BaseOpt.export_for_phase_scheduler pol_iss with
          | Some iss_scop =>
              try_phase_pipeline_from_source_pol_band
                pol_iss BaseOpt.run_pluto_phase_pipeline iss_scop
          | None => reject_tiling tt
          end
        else
          try_phase_pipeline_from_source_pol_band
            pol
            BaseOpt.run_pluto_phase_pipeline
            before_scop
      else
        try_phase_pipeline_from_source_pol_band
          pol
          BaseOpt.run_pluto_phase_pipeline
          before_scop
  | _ =>
      try_phase_pipeline_from_source_pol_band
        pol
        BaseOpt.run_pluto_phase_pipeline
        before_scop
  end.

Definition phase_pipeline_opt_prepared_from_poly_no_iss_band
    (pol: PolyLang.t): imp LoopIR.t :=
  if BaseOpt.has_nonscalar_stmt pol then
    match BaseOpt.export_for_phase_scheduler pol with
    | Some before_scop =>
        try_phase_pipeline_from_source_pol_band
          pol
          BaseOpt.run_pluto_phase_pipeline
          before_scop
    | None =>
        reject_tiling tt
    end
  else
    reject_tiling tt.

Definition phase_pipeline_opt_prepared_from_poly_with_iss_band
    (pol: PolyLang.t): imp LoopIR.t :=
  if BaseOpt.has_nonscalar_stmt pol then
    match BaseOpt.export_for_phase_scheduler pol with
    | Some before_scop =>
        try_checked_iss_phase_pipeline_from_poly_band pol before_scop
    | None =>
        reject_tiling tt
    end
  else
    reject_tiling tt.

Definition identity_tiling_opt_prepared_from_poly_band
    (pol: PolyLang.t): imp LoopIR.t :=
  if BaseOpt.has_nonscalar_stmt pol then
    match BaseOpt.export_for_phase_scheduler pol with
    | Some before_scop =>
        try_identity_phase_pipeline_from_source_pol_band
          pol
          BaseOpt.run_pluto_identity_tiling_pipeline
          before_scop
    | None =>
        reject_tiling tt
    end
  else
    reject_tiling tt.

Definition try_checked_iss_identity_tiling_phase_pipeline_from_poly_band
    (pol: PolyLang.t)
    (before_scop: OpenScop): imp LoopIR.t :=
  match BaseOpt.infer_iss_from_source_scop pol before_scop with
  | Okk (Some (pol_iss, w)) =>
      if ValidatorCore.checked_iss_complete_cut_shape_validate pol pol_iss w then
        BIND iss_wf <- ValidatorCore.check_wf_polyprog pol_iss -;
        if iss_wf then
          match BaseOpt.export_for_phase_scheduler pol_iss with
          | Some iss_scop =>
              try_identity_phase_pipeline_from_source_pol_band
                pol_iss
                BaseOpt.run_pluto_identity_tiling_pipeline
                iss_scop
          | None =>
              reject_tiling tt
          end
        else
          identity_tiling_opt_prepared_from_poly_band pol
      else
        identity_tiling_opt_prepared_from_poly_band pol
  | _ =>
      identity_tiling_opt_prepared_from_poly_band pol
  end.

Definition identity_tiling_opt_prepared_from_poly_with_iss_band
    (pol: PolyLang.t): imp LoopIR.t :=
  if BaseOpt.has_nonscalar_stmt pol then
    match BaseOpt.export_for_phase_scheduler pol with
    | Some before_scop =>
        try_checked_iss_identity_tiling_phase_pipeline_from_poly_band
          pol before_scop
    | None =>
        reject_tiling tt
    end
  else
    reject_tiling tt.

Definition phase_post_tiling_affine_opt_prepared_from_poly_no_iss_band
    (pol: PolyLang.t): imp LoopIR.t :=
  if BaseOpt.has_nonscalar_stmt pol then
    match BaseOpt.export_for_phase_scheduler pol with
    | Some before_scop =>
        try_post_tiling_affine_phase_pipeline_from_source_pol_band pol before_scop
    | None =>
        reject_tiling tt
    end
  else
    reject_tiling tt.

Definition phase_post_tiling_affine_opt_prepared_from_poly_with_iss_band
    (pol: PolyLang.t): imp LoopIR.t :=
  if BaseOpt.has_nonscalar_stmt pol then
    match BaseOpt.export_for_phase_scheduler pol with
    | Some before_scop =>
        try_checked_iss_post_tiling_affine_phase_pipeline_from_poly_band pol before_scop
    | None =>
        reject_tiling tt
    end
  else
    reject_tiling tt.

Definition phase_pipeline_opt_prepared_band
    (loop: LoopIR.t): imp LoopIR.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (BaseOpt.Extractor.extractor loop) -;
  let pol := BaseOpt.Strengthen.strengthen_pprog pol0 in
  phase_pipeline_opt_prepared_from_poly_no_iss_band pol.

Definition phase_pipeline_opt_prepared_with_iss_band
    (loop: LoopIR.t): imp LoopIR.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (BaseOpt.Extractor.extractor loop) -;
  let pol := BaseOpt.Strengthen.strengthen_pprog pol0 in
  phase_pipeline_opt_prepared_from_poly_with_iss_band pol.

Definition identity_tiling_opt_prepared_band
    (loop: LoopIR.t): imp LoopIR.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (BaseOpt.Extractor.extractor loop) -;
  let pol := BaseOpt.Strengthen.strengthen_pprog pol0 in
  identity_tiling_opt_prepared_from_poly_band pol.

Definition identity_tiling_opt_prepared_with_iss_band
    (loop: LoopIR.t): imp LoopIR.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (BaseOpt.Extractor.extractor loop) -;
  let pol := BaseOpt.Strengthen.strengthen_pprog pol0 in
  identity_tiling_opt_prepared_from_poly_with_iss_band pol.

Definition phase_post_tiling_affine_opt_prepared_band
    (loop: LoopIR.t): imp LoopIR.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (BaseOpt.Extractor.extractor loop) -;
  let pol := BaseOpt.Strengthen.strengthen_pprog pol0 in
  phase_post_tiling_affine_opt_prepared_from_poly_no_iss_band pol.

Definition phase_post_tiling_affine_opt_prepared_with_iss_band
    (loop: LoopIR.t): imp LoopIR.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (BaseOpt.Extractor.extractor loop) -;
  let pol := BaseOpt.Strengthen.strengthen_pprog pol0 in
  phase_post_tiling_affine_opt_prepared_from_poly_with_iss_band pol.

Lemma try_verified_tiling_after_phase_mid_band_correct:
  forall pol_mid mid_scop after_scop st st',
    PolyLang.wf_pprog_affine pol_mid ->
    WHEN loop' <- try_verified_tiling_after_phase_mid_band pol_mid mid_scop after_scop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol_mid st st'' /\
      State.eq st' st''.
Proof.
  intros pol_mid mid_scop after_scop st st' Hwf_mid loop' Hopt Hloop.
  unfold try_verified_tiling_after_phase_mid_band in Hopt.
  destruct (BaseOpt.infer_tiling_witness_scops mid_scop after_scop) as [ws|msg] eqn:Hws.
  - destruct
      (ValidatorCore.import_canonical_tiled_after_poly pol_mid after_scop ws)
      as [pol_after|msg_after] eqn:Hafter.
    + bind_imp_destruct Hopt route Hroute.
      destruct route.
      * simpl in Hopt.
        bind_imp_destruct Hopt wf_after_ok Hwf_check.
        destruct wf_after_ok.
        -- pose proof
             (ValidatorCore.check_wf_polyprog_general_correct
                pol_after true Hwf_check eq_refl)
             as Hwf_after.
           pose proof
             (PrepareCore.prepared_codegen_correct_general
                pol_after st st' loop' Hopt Hwf_after Hloop)
             as Hsem_after.
           eapply
             (TilingSched.checked_tiling_schedule_sourceb_first_runtime_validate_route_correct
                pol_mid pol_after ws st st'
                TilingSched.DirectBandAccepted); eauto.
        -- elim (reject_tiling_impossible loop' Hopt).
      * simpl in Hopt.
        bind_imp_destruct Hopt wf_after_ok Hwf_check.
        destruct wf_after_ok.
        -- pose proof
             (ValidatorCore.check_wf_polyprog_general_correct
                pol_after true Hwf_check eq_refl)
             as Hwf_after.
           pose proof
             (PrepareCore.prepared_codegen_correct_general
                pol_after st st' loop' Hopt Hwf_after Hloop)
             as Hsem_after.
           eapply
             (TilingSched.checked_tiling_schedule_sourceb_first_runtime_validate_route_correct
                pol_mid pol_after ws st st'
                TilingSched.GeneralScheduleAccepted); eauto.
        -- elim (reject_tiling_impossible loop' Hopt).
      * simpl in Hopt.
        elim (reject_tiling_impossible loop' Hopt).
    + elim (reject_tiling_impossible loop' Hopt).
  - elim (reject_tiling_impossible loop' Hopt).
Qed.

Lemma try_phase_pipeline_from_source_pol_band_correct:
  forall pol_source phase_runner before_scop st st',
    PolyLang.wf_pprog_affine pol_source ->
    WHEN loop' <-
      try_phase_pipeline_from_source_pol_band pol_source phase_runner before_scop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol_source st st'' /\
      State.eq st' st''.
Proof.
  intros pol_source phase_runner before_scop st st' Hwf_source loop' Hopt Hloop.
  unfold try_phase_pipeline_from_source_pol_band in Hopt.
  destruct (phase_runner before_scop) as [[mid_scop after_scop]|msg] eqn:Hphase.
  - destruct (PolyLang.from_openscop_schedule_only pol_source mid_scop)
      as [pol_mid|msg_mid] eqn:Hmid.
    + bind_imp_destruct Hopt affine_ok Haff.
      destruct affine_ok.
      * pose proof
          (ValidatorCore.validate_preserve_wf_pprog
             pol_source pol_mid _ Haff eq_refl)
          as [_ Hwf_mid].
        pose proof
          (try_verified_tiling_after_phase_mid_band_correct
             pol_mid mid_scop after_scop st st' Hwf_mid loop' Hopt Hloop)
          as Hmid_corr.
        destruct Hmid_corr as [st_mid [Hmid_sem Heq_mid]].
        pose proof
          (ValidatorCore.validate_correct
             pol_source pol_mid st st_mid true Haff eq_refl Hmid_sem)
          as Haff_corr.
        destruct Haff_corr as [st_src [Hsrc_sem Heq_src]].
        exists st_src.
        split; auto.
        eapply State.eq_trans; eauto.
      * elim (reject_tiling_impossible loop' Hopt).
    + elim (reject_tiling_impossible loop' Hopt).
  - elim (reject_tiling_impossible loop' Hopt).
Qed.

Lemma try_identity_phase_pipeline_from_source_pol_band_correct:
  forall pol_source phase_runner before_scop st st',
    PolyLang.wf_pprog_affine pol_source ->
    WHEN loop' <-
      try_identity_phase_pipeline_from_source_pol_band
        pol_source phase_runner before_scop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol_source st st'' /\
      State.eq st' st''.
Proof.
  intros pol_source phase_runner before_scop st st' Hwf_source loop' Hopt Hloop.
  unfold try_identity_phase_pipeline_from_source_pol_band in Hopt.
  destruct (phase_runner before_scop) as [[mid_scop after_scop]|msg] eqn:Hphase.
  - destruct (PolyLang.from_openscop_like_source pol_source mid_scop)
      as [pol_mid|msg_mid] eqn:Hmid.
    + bind_imp_destruct Hopt affine_ok Haff.
      destruct affine_ok.
      * pose proof
          (ValidatorCore.validate_preserve_wf_pprog
             pol_source pol_mid _ Haff eq_refl)
          as [_ Hwf_mid].
        pose proof
          (try_verified_tiling_after_phase_mid_band_correct
             pol_mid mid_scop after_scop st st' Hwf_mid loop' Hopt Hloop)
          as Hmid_corr.
        destruct Hmid_corr as [st_mid [Hmid_sem Heq_mid]].
        pose proof
          (ValidatorCore.validate_correct
             pol_source pol_mid st st_mid true Haff eq_refl Hmid_sem)
          as Haff_corr.
        destruct Haff_corr as [st_src [Hsrc_sem Heq_src]].
        exists st_src.
        split; auto.
        eapply State.eq_trans; eauto.
      * elim (reject_tiling_impossible loop' Hopt).
    + elim (reject_tiling_impossible loop' Hopt).
  - elim (reject_tiling_impossible loop' Hopt).
Qed.

Lemma try_checked_iss_phase_pipeline_from_poly_band_correct:
  forall pol before_scop st st',
    PolyLang.wf_pprog_affine pol ->
    WHEN loop' <-
      try_checked_iss_phase_pipeline_from_poly_band pol before_scop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\
      State.eq st' st''.
Proof.
  intros pol before_scop st st' Hwf loop' Hopt Hloop.
  unfold try_checked_iss_phase_pipeline_from_poly_band in Hopt.
  destruct (BaseOpt.infer_iss_from_source_scop pol before_scop) as [iss_opt|msg]
    eqn:Hiss_infer.
  - destruct iss_opt as [[pol_iss w]|].
    + destruct (ValidatorCore.checked_iss_complete_cut_shape_validate pol pol_iss w)
        eqn:Hiss_check.
      * bind_imp_destruct Hopt iss_wf Hiss_wf.
        destruct iss_wf.
        -- pose proof
             (BaseOpt.check_wf_polyprog_affine_correct
                pol_iss _ Hiss_wf eq_refl)
             as Hwf_iss.
           destruct (BaseOpt.export_for_phase_scheduler pol_iss) as [iss_scop|].
           2:{ elim (reject_tiling_impossible loop' Hopt). }
           pose proof
             (try_phase_pipeline_from_source_pol_band_correct
                pol_iss
                BaseOpt.run_pluto_phase_pipeline
                iss_scop st st' Hwf_iss loop' Hopt Hloop)
             as Hiss_corr.
           destruct Hiss_corr as [st_iss [Hiss_sem Heq_iss]].
           pose proof
             (ISSValidatorCorrectCore
                .checked_iss_complete_cut_shape_validate_semantics_correct
                pol pol_iss w st st_iss Hiss_check Hiss_sem)
             as Hback.
           destruct Hback as [st_src [Hsrc_sem Heq_src]].
           exists st_src.
           split; auto.
           eapply State.eq_trans; eauto.
        -- eapply try_phase_pipeline_from_source_pol_band_correct; eauto.
      * eapply try_phase_pipeline_from_source_pol_band_correct; eauto.
    + eapply try_phase_pipeline_from_source_pol_band_correct; eauto.
  - eapply try_phase_pipeline_from_source_pol_band_correct; eauto.
Qed.

Lemma phase_pipeline_opt_prepared_from_poly_no_iss_band_correct:
  forall pol st st',
    PolyLang.wf_pprog_affine pol ->
    WHEN loop' <- phase_pipeline_opt_prepared_from_poly_no_iss_band pol THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\
      State.eq st' st''.
Proof.
  intros pol st st' Hwf loop' Hopt Hloop.
  unfold phase_pipeline_opt_prepared_from_poly_no_iss_band in Hopt.
  destruct (BaseOpt.has_nonscalar_stmt pol) eqn:Hnonscalar.
  - destruct (BaseOpt.export_for_phase_scheduler pol) as [before_scop|] eqn:Hscop.
    + eapply try_phase_pipeline_from_source_pol_band_correct; eauto.
    + elim (reject_tiling_impossible loop' Hopt).
  - elim (reject_tiling_impossible loop' Hopt).
Qed.

Lemma phase_pipeline_opt_prepared_from_poly_with_iss_band_correct:
  forall pol st st',
    PolyLang.wf_pprog_affine pol ->
    WHEN loop' <- phase_pipeline_opt_prepared_from_poly_with_iss_band pol THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\
      State.eq st' st''.
Proof.
  intros pol st st' Hwf loop' Hopt Hloop.
  unfold phase_pipeline_opt_prepared_from_poly_with_iss_band in Hopt.
  destruct (BaseOpt.has_nonscalar_stmt pol) eqn:Hnonscalar.
  - destruct (BaseOpt.export_for_phase_scheduler pol) as [before_scop|] eqn:Hscop.
    + eapply try_checked_iss_phase_pipeline_from_poly_band_correct; eauto.
    + elim (reject_tiling_impossible loop' Hopt).
  - elim (reject_tiling_impossible loop' Hopt).
Qed.

Lemma identity_tiling_opt_prepared_from_poly_band_correct:
  forall pol st st',
    PolyLang.wf_pprog_affine pol ->
    WHEN loop' <- identity_tiling_opt_prepared_from_poly_band pol THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\
      State.eq st' st''.
Proof.
  intros pol st st' Hwf loop' Hopt Hloop.
  unfold identity_tiling_opt_prepared_from_poly_band in Hopt.
  destruct (BaseOpt.has_nonscalar_stmt pol) eqn:Hnonscalar.
  - destruct (BaseOpt.export_for_phase_scheduler pol) as [before_scop|] eqn:Hscop.
    + eapply try_identity_phase_pipeline_from_source_pol_band_correct; eauto.
    + elim (reject_tiling_impossible loop' Hopt).
  - elim (reject_tiling_impossible loop' Hopt).
Qed.

Lemma try_checked_iss_identity_tiling_phase_pipeline_from_poly_band_correct:
  forall pol before_scop st st',
    PolyLang.wf_pprog_affine pol ->
    WHEN loop' <-
      try_checked_iss_identity_tiling_phase_pipeline_from_poly_band
        pol before_scop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\
      State.eq st' st''.
Proof.
  intros pol before_scop st st' Hwf loop' Hopt Hloop.
  unfold try_checked_iss_identity_tiling_phase_pipeline_from_poly_band in Hopt.
  destruct (BaseOpt.infer_iss_from_source_scop pol before_scop) as [iss_opt|msg]
    eqn:Hiss_infer.
  - destruct iss_opt as [[pol_iss w]|].
    + destruct (ValidatorCore.checked_iss_complete_cut_shape_validate pol pol_iss w)
        eqn:Hiss_check.
      * bind_imp_destruct Hopt iss_wf Hiss_wf.
        destruct iss_wf.
        -- pose proof
             (BaseOpt.check_wf_polyprog_affine_correct
                pol_iss _ Hiss_wf eq_refl)
             as Hwf_iss.
           destruct (BaseOpt.export_for_phase_scheduler pol_iss)
             as [iss_scop|] eqn:Hiss_scop.
           ++ pose proof
                (try_identity_phase_pipeline_from_source_pol_band_correct
                   pol_iss
                   BaseOpt.run_pluto_identity_tiling_pipeline
                   iss_scop st st' Hwf_iss loop' Hopt Hloop)
                as Hiss_corr.
              destruct Hiss_corr as [st_iss [Hiss_sem Heq_iss]].
              pose proof
                (ISSValidatorCorrectCore
                   .checked_iss_complete_cut_shape_validate_semantics_correct
                   pol pol_iss w st st_iss Hiss_check Hiss_sem)
                as Hback.
              destruct Hback as [st_src [Hsrc_sem Heq_src]].
              exists st_src.
              split; auto.
              eapply State.eq_trans; eauto.
           ++ elim (reject_tiling_impossible loop' Hopt).
        -- eapply identity_tiling_opt_prepared_from_poly_band_correct; eauto.
      * eapply identity_tiling_opt_prepared_from_poly_band_correct; eauto.
    + eapply identity_tiling_opt_prepared_from_poly_band_correct; eauto.
  - eapply identity_tiling_opt_prepared_from_poly_band_correct; eauto.
Qed.

Lemma identity_tiling_opt_prepared_from_poly_with_iss_band_correct:
  forall pol st st',
    PolyLang.wf_pprog_affine pol ->
    WHEN loop' <- identity_tiling_opt_prepared_from_poly_with_iss_band pol THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\
      State.eq st' st''.
Proof.
  intros pol st st' Hwf loop' Hopt Hloop.
  unfold identity_tiling_opt_prepared_from_poly_with_iss_band in Hopt.
  destruct (BaseOpt.has_nonscalar_stmt pol) eqn:Hnonscalar.
  - destruct (BaseOpt.export_for_phase_scheduler pol) as [before_scop|] eqn:Hscop.
    + eapply try_checked_iss_identity_tiling_phase_pipeline_from_poly_band_correct; eauto.
    + elim (reject_tiling_impossible loop' Hopt).
  - elim (reject_tiling_impossible loop' Hopt).
Qed.

Local Lemma lift_frontend_correct:
  forall (from_poly: PolyLang.t -> imp LoopIR.t) loop st st',
    (forall pol st0 st1,
      PolyLang.wf_pprog_affine pol ->
      WHEN loop' <- from_poly pol THEN
      LoopIR.semantics loop' st0 st1 ->
      exists st2,
        PolyLang.instance_list_semantics pol st0 st2 /\
        State.eq st1 st2) ->
    WHEN loop' <-
      (BIND pol0 <-
         res_to_alarm PolyLang.dummy (BaseOpt.Extractor.extractor loop) -;
       from_poly (BaseOpt.Strengthen.strengthen_pprog pol0)) THEN
    LoopIR.semantics loop' st st' ->
    exists st_src,
      LoopIR.semantics loop st st_src /\ State.eq st' st_src.
Proof.
  intros from_poly loop st st' Hfrom_poly loop' Hopt Hloop.
  bind_imp_destruct Hopt pol0 Hextract_imp.
  pose proof Hextract_imp as Hextract.
  apply res_to_alarm_correct in Hextract.
  pose proof
    (BaseOpt.Strengthen.strengthen_pprog_wf_affine pol0
       (BaseOpt.extractor_success_wf_pprog_affine loop pol0 Hextract))
    as Hwf.
  destruct
    (Hfrom_poly
       (BaseOpt.Strengthen.strengthen_pprog pol0)
       st st' Hwf loop' Hopt Hloop)
    as [st_str [Hstrengthened Heq_strengthened]].
  eapply BaseOpt.Strengthen.instance_list_semantics_unstrengthen
    in Hstrengthened.
  destruct
    (BaseOpt.Extractor.extractor_correct
       loop pol0 st st_str Hextract Hstrengthened)
    as [st_src [Hsource Heq_source]].
  exists st_src.
  split.
  - exact Hsource.
  - eapply State.eq_trans.
    + exact Heq_strengthened.
    + exact Heq_source.
Qed.

Definition Opt_prepared_band := phase_pipeline_opt_prepared_band.
Definition Opt_band := Opt_prepared_band.
Definition Opt_prepared_band_with_iss := phase_pipeline_opt_prepared_with_iss_band.
Definition Opt_band_with_iss := Opt_prepared_band_with_iss.
Definition Opt_prepared_identity_tiled_band := identity_tiling_opt_prepared_band.
Definition Opt_identity_tiled_band := Opt_prepared_identity_tiled_band.
Definition Opt_prepared_identity_tiled_band_with_iss :=
  identity_tiling_opt_prepared_with_iss_band.
Definition Opt_identity_tiled_band_with_iss :=
  Opt_prepared_identity_tiled_band_with_iss.

Theorem Opt_prepared_band_correct:
  forall loop st st',
    WHEN loop' <- Opt_prepared_band loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\
      State.eq st' st''.
Proof.
  intros loop st st' loop' Hopt Hloop.
  unfold Opt_prepared_band, phase_pipeline_opt_prepared_band in Hopt.
  exact
    (lift_frontend_correct
       phase_pipeline_opt_prepared_from_poly_no_iss_band loop st st'
       phase_pipeline_opt_prepared_from_poly_no_iss_band_correct
       loop' Hopt Hloop).
Qed.

Theorem Opt_prepared_band_with_iss_correct:
  forall loop st st',
    WHEN loop' <- Opt_prepared_band_with_iss loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\
      State.eq st' st''.
Proof.
  intros loop st st' loop' Hopt Hloop.
  unfold Opt_prepared_band_with_iss,
    phase_pipeline_opt_prepared_with_iss_band in Hopt.
  exact
    (lift_frontend_correct
       phase_pipeline_opt_prepared_from_poly_with_iss_band loop st st'
       phase_pipeline_opt_prepared_from_poly_with_iss_band_correct
       loop' Hopt Hloop).
Qed.

Theorem Opt_band_with_iss_correct:
  forall loop st st',
    WHEN loop' <- Opt_band_with_iss loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\
      State.eq st' st''.
Proof.
  intros.
  eapply Opt_prepared_band_with_iss_correct; eauto.
Qed.

Theorem Opt_prepared_identity_tiled_band_correct:
  forall loop st st',
    WHEN loop' <- Opt_prepared_identity_tiled_band loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\
      State.eq st' st''.
Proof.
  intros loop st st' loop' Hopt Hloop.
  unfold Opt_prepared_identity_tiled_band, identity_tiling_opt_prepared_band in Hopt.
  exact
    (lift_frontend_correct
       identity_tiling_opt_prepared_from_poly_band loop st st'
       identity_tiling_opt_prepared_from_poly_band_correct
       loop' Hopt Hloop).
Qed.

Theorem Opt_identity_tiled_band_correct:
  forall loop st st',
    WHEN loop' <- Opt_identity_tiled_band loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\
      State.eq st' st''.
Proof.
  intros.
  eapply Opt_prepared_identity_tiled_band_correct; eauto.
Qed.

Theorem Opt_prepared_identity_tiled_band_with_iss_correct:
  forall loop st st',
    WHEN loop' <- Opt_prepared_identity_tiled_band_with_iss loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\
      State.eq st' st''.
Proof.
  intros loop st st' loop' Hopt Hloop.
  unfold Opt_prepared_identity_tiled_band_with_iss,
    identity_tiling_opt_prepared_with_iss_band in Hopt.
  exact
    (lift_frontend_correct
       identity_tiling_opt_prepared_from_poly_with_iss_band loop st st'
       identity_tiling_opt_prepared_from_poly_with_iss_band_correct
       loop' Hopt Hloop).
Qed.

Theorem Opt_identity_tiled_band_with_iss_correct:
  forall loop st st',
    WHEN loop' <- Opt_identity_tiled_band_with_iss loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\
      State.eq st' st''.
Proof.
  intros.
  eapply Opt_prepared_identity_tiled_band_with_iss_correct; eauto.
Qed.

Local Lemma post_tiling_affine_accepted_tail_correct:
  forall pol_mid pol_posttile pol_after ws st st' loop' route,
    PolyLang.wf_pprog_affine pol_mid ->
    PolyLang.wf_pprog_general pol_posttile ->
    PolyLang.wf_pprog_general pol_after ->
    TilingSched.tiling_band_validation_route_acceptsb route = true ->
    mayReturn
      (TilingSched.checked_tiling_schedule_sourceb_first_runtime_validate_route
         pol_mid pol_posttile ws)
      route ->
    mayReturn
      (ValidatorCore.validate_general pol_posttile pol_after)
      true ->
    mayReturn
      (prepared_codegen_after_tiling_route
         pol_after route)
      loop' ->
    LoopIR.semantics loop' st st' ->
    exists st_mid,
      PolyLang.instance_list_semantics pol_mid st st_mid /\
      State.eq st' st_mid.
Proof.
  intros pol_mid pol_posttile pol_after ws st st' loop' route
         Hwf_mid Hwf_posttile Hwf_after Haccept Hroute Hfinal Hcodegen Hloop.
  assert (Hprepared : mayReturn
    (PrepareCore.prepared_codegen (PolyLang.current_view_pprog pol_after)) loop').
  { destruct route; try discriminate Haccept; exact Hcodegen. }
  pose proof
    (PrepareCore.prepared_codegen_correct_general
       pol_after st st' loop' Hprepared Hwf_after Hloop)
    as Hsem_after.
  destruct
    (ValidatorCore.validate_general_correct
       pol_posttile pol_after st st'
       true Hfinal eq_refl Hsem_after)
    as [st_post [Hpost_sem Heq_post]].
  destruct
    (TilingSched.checked_tiling_schedule_sourceb_first_runtime_validate_route_correct
       pol_mid pol_posttile ws st st_post
       route Hwf_mid Hwf_posttile Hroute Haccept Hpost_sem)
    as [st_mid [Hmid_sem Heq_mid]].
  exists st_mid.
  split.
  - exact Hmid_sem.
  - eapply State.eq_trans.
    + exact Heq_post.
    + exact Heq_mid.
Qed.

Lemma try_verified_post_tiling_affine_after_phase_mid_band_correct:
  forall pol_mid mid_scop posttile_scop after_scop st st',
    PolyLang.wf_pprog_affine pol_mid ->
    WHEN loop' <-
      try_verified_post_tiling_affine_after_phase_mid_band
        pol_mid mid_scop posttile_scop after_scop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol_mid st st'' /\
      State.eq st' st''.
Proof.
  intros pol_mid mid_scop posttile_scop after_scop st st'
         Hwf_mid loop' Hopt Hloop.
  unfold try_verified_post_tiling_affine_after_phase_mid_band in Hopt.
  destruct (BaseOpt.infer_tiling_witness_scops mid_scop posttile_scop)
    as [ws|msg] eqn:Hws.
  - destruct
      (ValidatorCore.import_canonical_tiled_after_poly pol_mid posttile_scop ws)
      as [pol_posttile|msg_after] eqn:Hposttile.
    + bind_imp_destruct Hopt route Hroute.
      destruct route.
      * simpl in Hopt.
        bind_imp_destruct Hopt wf_posttile_ok Hwf_posttile_check.
        destruct wf_posttile_ok.
        -- pose proof
             (ValidatorCore.check_wf_polyprog_general_correct
                pol_posttile true Hwf_posttile_check eq_refl)
             as Hwf_posttile.
           destruct (PolyLang.from_openscop_schedule_only
                       pol_posttile after_scop)
             as [pol_after|msg_final] eqn:Hafter.
           ++ bind_imp_destruct Hopt final_ok Hfinal.
              destruct final_ok.
              ** bind_imp_destruct Hopt wf_after_ok Hwf_check.
                 destruct wf_after_ok.
                 --- pose proof
                       (ValidatorCore.check_wf_polyprog_general_correct
                          pol_after true Hwf_check eq_refl)
                       as Hwf_after.
                     exact
                       (post_tiling_affine_accepted_tail_correct
                          pol_mid pol_posttile pol_after ws st st' loop'
                          TilingSched.DirectBandAccepted
                          Hwf_mid Hwf_posttile Hwf_after eq_refl
                          Hroute Hfinal Hopt Hloop).
                 --- elim
                       (reject_post_tiling_affine_impossible
                          TilingSched.DirectBandAccepted loop' Hopt).
              ** elim
                   (reject_post_tiling_affine_impossible
                      TilingSched.DirectBandAccepted loop' Hopt).
           ++ elim
                (reject_post_tiling_affine_impossible
                   TilingSched.DirectBandAccepted loop' Hopt).
        -- elim (reject_tiling_impossible loop' Hopt).
      * simpl in Hopt.
        bind_imp_destruct Hopt wf_posttile_ok Hwf_posttile_check.
        destruct wf_posttile_ok.
        -- pose proof
             (ValidatorCore.check_wf_polyprog_general_correct
                pol_posttile true Hwf_posttile_check eq_refl)
             as Hwf_posttile.
           destruct (PolyLang.from_openscop_schedule_only
                       pol_posttile after_scop)
             as [pol_after|msg_final] eqn:Hafter.
           ++ bind_imp_destruct Hopt final_ok Hfinal.
              destruct final_ok.
              ** bind_imp_destruct Hopt wf_after_ok Hwf_check.
                 destruct wf_after_ok.
                 --- pose proof
                       (ValidatorCore.check_wf_polyprog_general_correct
                          pol_after true Hwf_check eq_refl)
                       as Hwf_after.
                     exact
                       (post_tiling_affine_accepted_tail_correct
                          pol_mid pol_posttile pol_after ws st st' loop'
                          TilingSched.GeneralScheduleAccepted
                          Hwf_mid Hwf_posttile Hwf_after eq_refl
                          Hroute Hfinal Hopt Hloop).
                 --- elim
                       (reject_post_tiling_affine_impossible
                          TilingSched.GeneralScheduleAccepted loop' Hopt).
              ** elim
                   (reject_post_tiling_affine_impossible
                      TilingSched.GeneralScheduleAccepted loop' Hopt).
           ++ elim
                (reject_post_tiling_affine_impossible
                   TilingSched.GeneralScheduleAccepted loop' Hopt).
        -- elim (reject_tiling_impossible loop' Hopt).
      * simpl in Hopt.
        elim (reject_tiling_impossible loop' Hopt).
    + elim (reject_tiling_impossible loop' Hopt).
  - elim (reject_tiling_impossible loop' Hopt).
Qed.

Lemma try_post_tiling_affine_phase_pipeline_from_source_pol_band_correct:
  forall pol_source before_scop st st',
    PolyLang.wf_pprog_affine pol_source ->
    WHEN loop' <-
      try_post_tiling_affine_phase_pipeline_from_source_pol_band
        pol_source before_scop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol_source st st'' /\
      State.eq st' st''.
Proof.
  intros pol_source before_scop st st' Hwf_source loop' Hopt Hloop.
  unfold try_post_tiling_affine_phase_pipeline_from_source_pol_band in Hopt.
  destruct (BaseOpt.run_pluto_post_tiling_affine_phase_pipeline before_scop)
    as [[mid_scop [posttile_scop after_scop]]|msg] eqn:Hphase.
  - destruct (PolyLang.from_openscop_schedule_only pol_source mid_scop)
      as [pol_mid|msg_mid] eqn:Hmid.
    + bind_imp_destruct Hopt affine_ok Haff.
      destruct affine_ok.
      * pose proof
          (ValidatorCore.validate_preserve_wf_pprog
             pol_source pol_mid _ Haff eq_refl)
          as [_ Hwf_mid].
        pose proof
          (try_verified_post_tiling_affine_after_phase_mid_band_correct
             pol_mid mid_scop posttile_scop after_scop
             st st' Hwf_mid loop' Hopt Hloop)
          as Hmid_corr.
        destruct Hmid_corr as [st_mid [Hmid_sem Heq_mid]].
        pose proof
          (ValidatorCore.validate_correct
             pol_source pol_mid st st_mid true Haff eq_refl Hmid_sem)
          as Haff_corr.
        destruct Haff_corr as [st_src [Hsrc_sem Heq_src]].
        exists st_src.
        split; auto.
        eapply State.eq_trans; eauto.
      * elim (reject_tiling_impossible loop' Hopt).
    + elim (reject_tiling_impossible loop' Hopt).
  - elim (reject_tiling_impossible loop' Hopt).
Qed.

Lemma try_post_tiling_affine_phase_pipeline_from_source_pol_band_with_iss_correct:
  forall pol_source before_scop st st',
    PolyLang.wf_pprog_affine pol_source ->
    WHEN loop' <-
      try_post_tiling_affine_phase_pipeline_from_source_pol_band_with_iss
        pol_source before_scop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol_source st st'' /\
      State.eq st' st''.
Proof.
  intros pol_source before_scop st st' Hwf_source loop' Hopt Hloop.
  unfold try_post_tiling_affine_phase_pipeline_from_source_pol_band_with_iss in Hopt.
  destruct (BaseOpt.run_pluto_post_tiling_affine_phase_pipeline_with_iss before_scop)
    as [[mid_scop [posttile_scop after_scop]]|msg] eqn:Hphase.
  - destruct (PolyLang.from_openscop_schedule_only pol_source mid_scop)
      as [pol_mid|msg_mid] eqn:Hmid.
    + bind_imp_destruct Hopt affine_ok Haff.
      destruct affine_ok.
      * pose proof
          (ValidatorCore.validate_preserve_wf_pprog
             pol_source pol_mid _ Haff eq_refl)
          as [_ Hwf_mid].
        pose proof
          (try_verified_post_tiling_affine_after_phase_mid_band_correct
             pol_mid mid_scop posttile_scop after_scop
             st st' Hwf_mid loop' Hopt Hloop)
          as Hmid_corr.
        destruct Hmid_corr as [st_mid [Hmid_sem Heq_mid]].
        pose proof
          (ValidatorCore.validate_correct
             pol_source pol_mid st st_mid true Haff eq_refl Hmid_sem)
          as Haff_corr.
        destruct Haff_corr as [st_src [Hsrc_sem Heq_src]].
        exists st_src.
        split; auto.
        eapply State.eq_trans; eauto.
      * elim (reject_tiling_impossible loop' Hopt).
    + elim (reject_tiling_impossible loop' Hopt).
  - elim (reject_tiling_impossible loop' Hopt).
Qed.

Lemma try_checked_iss_post_tiling_affine_phase_pipeline_from_poly_band_correct:
  forall pol before_scop st st',
    PolyLang.wf_pprog_affine pol ->
    WHEN loop' <-
      try_checked_iss_post_tiling_affine_phase_pipeline_from_poly_band
        pol before_scop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\
      State.eq st' st''.
Proof.
  intros pol before_scop st st' Hwf loop' Hopt Hloop.
  unfold try_checked_iss_post_tiling_affine_phase_pipeline_from_poly_band in Hopt.
  destruct (BaseOpt.infer_iss_from_source_scop pol before_scop) as [iss_opt|msg]
    eqn:Hiss_infer.
  - destruct iss_opt as [[pol_iss w]|].
    + destruct (ValidatorCore.checked_iss_complete_cut_shape_validate pol pol_iss w)
        eqn:Hiss_check.
      * bind_imp_destruct Hopt iss_wf Hiss_wf.
        destruct iss_wf.
        -- pose proof
             (BaseOpt.check_wf_polyprog_affine_correct
                pol_iss _ Hiss_wf eq_refl)
             as Hwf_iss.
           destruct (BaseOpt.export_for_phase_scheduler pol_iss) as [iss_scop|].
           2:{ elim (reject_tiling_impossible loop' Hopt). }
           pose proof
             (try_post_tiling_affine_phase_pipeline_from_source_pol_band_correct
                pol_iss iss_scop st st' Hwf_iss loop' Hopt Hloop)
             as Hiss_corr.
           destruct Hiss_corr as [st_iss [Hiss_sem Heq_iss]].
           pose proof
             (ISSValidatorCorrectCore
                .checked_iss_complete_cut_shape_validate_semantics_correct
                pol pol_iss w st st_iss Hiss_check Hiss_sem)
             as Hback.
           destruct Hback as [st_src [Hsrc_sem Heq_src]].
           exists st_src.
           split; auto.
           eapply State.eq_trans; eauto.
        -- eapply try_post_tiling_affine_phase_pipeline_from_source_pol_band_correct; eauto.
      * eapply try_post_tiling_affine_phase_pipeline_from_source_pol_band_correct; eauto.
    + eapply try_post_tiling_affine_phase_pipeline_from_source_pol_band_correct; eauto.
  - eapply try_post_tiling_affine_phase_pipeline_from_source_pol_band_correct; eauto.
Qed.

Lemma phase_post_tiling_affine_opt_prepared_from_poly_no_iss_band_correct:
  forall pol st st',
    PolyLang.wf_pprog_affine pol ->
    WHEN loop' <- phase_post_tiling_affine_opt_prepared_from_poly_no_iss_band pol THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\
      State.eq st' st''.
Proof.
  intros pol st st' Hwf loop' Hopt Hloop.
  unfold phase_post_tiling_affine_opt_prepared_from_poly_no_iss_band in Hopt.
  destruct (BaseOpt.has_nonscalar_stmt pol) eqn:Hnonscalar.
  - destruct (BaseOpt.export_for_phase_scheduler pol) as [before_scop|] eqn:Hscop.
    + eapply try_post_tiling_affine_phase_pipeline_from_source_pol_band_correct; eauto.
    + elim (reject_tiling_impossible loop' Hopt).
  - elim (reject_tiling_impossible loop' Hopt).
Qed.

Lemma phase_post_tiling_affine_opt_prepared_from_poly_with_iss_band_correct:
  forall pol st st',
    PolyLang.wf_pprog_affine pol ->
    WHEN loop' <- phase_post_tiling_affine_opt_prepared_from_poly_with_iss_band pol THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\
      State.eq st' st''.
Proof.
  intros pol st st' Hwf loop' Hopt Hloop.
  unfold phase_post_tiling_affine_opt_prepared_from_poly_with_iss_band in Hopt.
  destruct (BaseOpt.has_nonscalar_stmt pol) eqn:Hnonscalar.
  - destruct (BaseOpt.export_for_phase_scheduler pol) as [before_scop|] eqn:Hscop.
    + eapply try_checked_iss_post_tiling_affine_phase_pipeline_from_poly_band_correct; eauto.
    + elim (reject_tiling_impossible loop' Hopt).
  - elim (reject_tiling_impossible loop' Hopt).
Qed.

Definition Opt_prepared_post_tiling_affine_band := phase_post_tiling_affine_opt_prepared_band.
Definition Opt_post_tiling_affine_band := Opt_prepared_post_tiling_affine_band.
Definition Opt_prepared_post_tiling_affine_band_with_iss :=
  phase_post_tiling_affine_opt_prepared_with_iss_band.
Definition Opt_post_tiling_affine_band_with_iss := Opt_prepared_post_tiling_affine_band_with_iss.

Theorem Opt_prepared_post_tiling_affine_band_correct:
  forall loop st st',
    WHEN loop' <- Opt_prepared_post_tiling_affine_band loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\
      State.eq st' st''.
Proof.
  intros loop st st' loop' Hopt Hloop.
  unfold Opt_prepared_post_tiling_affine_band, phase_post_tiling_affine_opt_prepared_band in Hopt.
  exact
    (lift_frontend_correct
       phase_post_tiling_affine_opt_prepared_from_poly_no_iss_band loop st st'
       phase_post_tiling_affine_opt_prepared_from_poly_no_iss_band_correct
       loop' Hopt Hloop).
Qed.

Theorem Opt_post_tiling_affine_band_correct:
  forall loop st st',
    WHEN loop' <- Opt_post_tiling_affine_band loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\
      State.eq st' st''.
Proof.
  intros.
  eapply Opt_prepared_post_tiling_affine_band_correct; eauto.
Qed.

Theorem Opt_prepared_post_tiling_affine_band_with_iss_correct:
  forall loop st st',
    WHEN loop' <- Opt_prepared_post_tiling_affine_band_with_iss loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\
      State.eq st' st''.
Proof.
  intros loop st st' loop' Hopt Hloop.
  unfold Opt_prepared_post_tiling_affine_band_with_iss,
    phase_post_tiling_affine_opt_prepared_with_iss_band in Hopt.
  exact
    (lift_frontend_correct
       phase_post_tiling_affine_opt_prepared_from_poly_with_iss_band loop st st'
       phase_post_tiling_affine_opt_prepared_from_poly_with_iss_band_correct
       loop' Hopt Hloop).
Qed.

Theorem Opt_post_tiling_affine_band_with_iss_correct:
  forall loop st st',
    WHEN loop' <- Opt_post_tiling_affine_band_with_iss loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\
      State.eq st' st''.
Proof.
  intros.
  eapply Opt_prepared_post_tiling_affine_band_with_iss_correct; eauto.
Qed.

Theorem Opt_band_correct:
  forall loop st st',
    WHEN loop' <- Opt_band loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\
      State.eq st' st''.
Proof.
  intros.
  eapply Opt_prepared_band_correct; eauto.
Qed.

End PolOptBandTiling.

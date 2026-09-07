Require Import ImpureAlarmConfig.
Require Import Result.
Require Import Vpl.Impure.

Require Import ISSValidatorCorrect.
Require Import PolIRs.
Require Import PolOpt.

Local Open Scope impure_scope.

Module Type POL_OPT_CORE (P : POLIRS).
  Include PolOpt.PolOpt P.
End POL_OPT_CORE.

Module PolOptCorrect
    (PolIRs: POLIRS)
    (ExecutableCore: POL_OPT_CORE PolIRs).

Module Core := ExecutableCore.
Module ISSValidatorCorrectCore := ISSValidatorCorrect PolIRs.
Module LoopIR := PolIRs.Loop.
Module PolyLang := PolIRs.PolyLang.
Module State := PolIRs.State.

(** * Proof map

    The [*_from_poly_correct] lemmas establish correctness after extraction.
    Each public loop-to-loop theorem then performs the same closure: remove
    domain strengthening, apply [Extractor.extractor_correct], and compose the
    two [State.eq] results.  [lift_frontend_correct] packages that typed
    lifting step while leaving each route-specific theorem explicit. *)

Lemma identity_opt_prepared_from_poly_correct:
  forall pol st st',
    PolyLang.wf_pprog_affine pol ->
    WHEN loop' <- Core.identity_opt_prepared_from_poly pol THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol st st' Hwf loop' Hopt Hloop.
  unfold Core.identity_opt_prepared_from_poly in Hopt.
  pose proof
    (Core.PrepareCore.prepared_codegen_correct
       pol st st' loop' Hopt Hwf Hloop)
    as Hsem.
  exists st'. split; auto. eapply State.eq_refl.
Qed.

Lemma try_checked_iss_phase_pipeline_from_poly_correct:
  forall pol before_scop st st',
    PolyLang.wf_pprog_affine pol ->
    WHEN loop' <- Core.try_checked_iss_phase_pipeline_from_poly pol before_scop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol before_scop st st' Hwf loop' Hopt Hloop.
  unfold Core.try_checked_iss_phase_pipeline_from_poly in Hopt.
  destruct (Core.infer_iss_from_source_scop pol before_scop) as [iss_opt|msg]
    eqn:Hiss_infer.
  - destruct iss_opt as [[pol_iss w]|].
    + destruct (Core.ValidatorCore.checked_iss_complete_cut_shape_validate pol pol_iss w)
        eqn:Hiss_check.
      * bind_imp_destruct Hopt iss_wf Hiss_wf.
        destruct iss_wf.
        -- pose proof
             (Core.check_wf_polyprog_affine_correct pol_iss _ Hiss_wf eq_refl)
             as Hwf_iss.
           destruct (Core.export_for_phase_scheduler pol_iss) as [iss_scop|].
           2:{ apply res_to_alarm_correct in Hopt. discriminate. }
           pose proof
             (Core.try_phase_pipeline_from_source_pol_correct
                pol_iss
                Core.run_pluto_phase_pipeline
                iss_scop
                st st'
                Hwf_iss
                loop'
                Hopt
                Hloop)
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
        -- eapply Core.try_phase_pipeline_from_source_pol_correct; eauto.
      * eapply Core.try_phase_pipeline_from_source_pol_correct; eauto.
    + eapply Core.try_phase_pipeline_from_source_pol_correct; eauto.
  - eapply Core.try_phase_pipeline_from_source_pol_correct; eauto.
Qed.

Lemma phase_opt_prepared_from_poly_correct:
  forall pol st st',
    PolyLang.wf_pprog_affine pol ->
    WHEN loop' <- Core.phase_opt_prepared_from_poly pol THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol st st' Hwf loop' Hopt Hloop.
  unfold Core.phase_opt_prepared_from_poly,
    Core.phase_pipeline_opt_prepared_from_poly,
    Core.phase_pipeline_opt_prepared_from_poly_no_iss in Hopt.
  destruct (Core.has_nonscalar_stmt pol) eqn:Hnonscalar.
  - destruct (Core.export_for_phase_scheduler pol) as [before_scop|] eqn:Hbefore.
    + eapply Core.try_phase_pipeline_from_source_pol_correct; eauto.
    + eapply Core.affine_opt_prepared_from_poly_correct; eauto.
  - eapply Core.PrepareCore.prepared_codegen_correct in Hopt; eauto.
    exists st'. split; auto. eapply State.eq_refl.
Qed.

Lemma phase_opt_prepared_from_poly_with_iss_correct:
  forall pol st st',
    PolyLang.wf_pprog_affine pol ->
    WHEN loop' <- Core.phase_opt_prepared_from_poly_with_iss pol THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol st st' Hwf loop' Hopt Hloop.
  unfold Core.phase_opt_prepared_from_poly_with_iss,
    Core.phase_pipeline_opt_prepared_from_poly_with_iss in Hopt.
  destruct (Core.has_nonscalar_stmt pol) eqn:Hnonscalar.
  - destruct (Core.export_for_phase_scheduler pol) as [before_scop|] eqn:Hbefore.
    + eapply try_checked_iss_phase_pipeline_from_poly_correct; eauto.
    + eapply Core.affine_opt_prepared_from_poly_correct; eauto.
  - eapply Core.PrepareCore.prepared_codegen_correct in Hopt; eauto.
    exists st'. split; auto. eapply State.eq_refl.
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
         res_to_alarm PolyLang.dummy (Core.Extractor.extractor loop) -;
       from_poly (Core.Strengthen.strengthen_pprog pol0)) THEN
    LoopIR.semantics loop' st st' ->
    exists st_src,
      LoopIR.semantics loop st st_src /\ State.eq st' st_src.
Proof.
  intros from_poly loop st st' Hfrom_poly loop' Hopt Hloop.
  bind_imp_destruct Hopt pol0 Hextract_imp.
  pose proof Hextract_imp as Hextract.
  apply res_to_alarm_correct in Hextract.
  pose proof
    (Core.Strengthen.strengthen_pprog_wf_affine pol0
       (Core.extractor_success_wf_pprog_affine loop pol0 Hextract))
    as Hwf.
  destruct
    (Hfrom_poly
       (Core.Strengthen.strengthen_pprog pol0)
       st st' Hwf loop' Hopt Hloop)
    as [st_str [Hstrengthened Heq_strengthened]].
  eapply Core.Strengthen.instance_list_semantics_unstrengthen
    in Hstrengthened.
  destruct
    (Core.Extractor.extractor_correct
       loop pol0 st st_str Hextract Hstrengthened)
    as [st_src [Hsource Heq_source]].
  exists st_src.
  split.
  - exact Hsource.
  - eapply State.eq_trans.
    + exact Heq_strengthened.
    + exact Heq_source.
Qed.

Theorem Opt_prepared_correct:
  forall loop st st',
    WHEN loop' <- Core.Opt_prepared loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop st st' loop' Hopt Hloop.
  unfold Core.Opt_prepared, Core.phase_opt_prepared,
    Core.phase_pipeline_opt_prepared in Hopt.
  exact
    (lift_frontend_correct
       Core.phase_opt_prepared_from_poly loop st st'
       phase_opt_prepared_from_poly_correct loop' Hopt Hloop).
Qed.

Theorem Identity_opt_prepared_correct:
  forall loop st st',
    WHEN loop' <- Core.identity_opt_prepared loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop st st' loop' Hopt Hloop.
  unfold Core.identity_opt_prepared in Hopt.
  exact
    (lift_frontend_correct
       Core.identity_opt_prepared_from_poly loop st st'
       identity_opt_prepared_from_poly_correct loop' Hopt Hloop).
Qed.

Theorem Identity_tiling_generic_opt_prepared_correct:
  forall loop st st',
    WHEN loop' <- Core.identity_tiling_generic_opt_prepared loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop st st' loop' Hopt Hloop.
  unfold Core.identity_tiling_generic_opt_prepared in Hopt.
  exact
    (lift_frontend_correct
       Core.identity_tiling_generic_opt_prepared_from_poly loop st st'
       Core.identity_tiling_generic_opt_prepared_from_poly_correct
       loop' Hopt Hloop).
Qed.

Theorem Affine_opt_prepared_correct:
  forall loop st st',
    WHEN loop' <- Core.affine_opt_prepared loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop st st' loop' Hopt Hloop.
  unfold Core.affine_opt_prepared, Core.affine_only_opt_prepared in Hopt.
  exact
    (lift_frontend_correct
       Core.affine_opt_prepared_from_poly loop st st'
       Core.affine_opt_prepared_from_poly_correct loop' Hopt Hloop).
Qed.

Theorem Opt_prepared_with_iss_correct:
  forall loop st st',
    WHEN loop' <- Core.Opt_prepared_with_iss loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop st st' loop' Hopt Hloop.
  unfold Core.Opt_prepared_with_iss, Core.phase_opt_prepared_with_iss,
    Core.phase_pipeline_opt_prepared_with_iss in Hopt.
  exact
    (lift_frontend_correct
       Core.phase_opt_prepared_from_poly_with_iss loop st st'
       phase_opt_prepared_from_poly_with_iss_correct loop' Hopt Hloop).
Qed.

Theorem Opt_correct:
  forall loop st st',
    WHEN loop' <- Core.Opt loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  exact Opt_prepared_correct.
Qed.

Theorem Opt_with_iss_correct:
  forall loop st st',
    WHEN loop' <- Core.Opt_with_iss loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  exact Opt_prepared_with_iss_correct.
Qed.

End PolOptCorrect.

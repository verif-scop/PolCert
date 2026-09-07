Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Require Import ISSValidatorCorrect.
Require Import PolIRs.
Require Import PolOpt.
Require Import ParallelPolOpt.
Require Import Result.
Require Import List.

Local Open Scope impure_scope.

Module Type PARALLEL_POL_OPT_CORE (P : POLIRS).
  Include ParallelPolOpt.ParallelPolOpt P.
End PARALLEL_POL_OPT_CORE.

Module ParallelPolOptCorrect
    (PolIRs: POLIRS)
    (ExecutableCore: PARALLEL_POL_OPT_CORE PolIRs).

Module Core := ExecutableCore.
Module CoreOpt := Core.CoreOpt.
Module ISSValidatorCorrectCore := ISSValidatorCorrect PolIRs.
Module LoopIR := PolIRs.Loop.
Module PolyLang := PolIRs.PolyLang.
Module State := PolIRs.State.
Module ParallelLoop := Core.ParallelCodegenCore.ParallelLoop.

(** * Proof map

    The first half proves the polyhedral preprocessing routes: optional ISS,
    affine scheduling, tiling, and post_tiling_affine compositions.  The prepared-route
    lemmas then append checked parallel or vector annotation and codegen.  The
    final [Opt_*_correct] families add strengthening and extraction to recover
    source loop semantics.  Route variants instantiate this same composition;
    they do not introduce new semantic arguments. *)

Lemma reject_tiling_no_return :
  forall pol_out, ~ mayReturn (Core.reject_tiling tt) pol_out.
Proof.
  intros pol_out Hret.
  unfold Core.reject_tiling, Core.observe_tiling_validation_route in Hret.
  cbn in Hret.
  unfold res_to_alarm in Hret.
  eapply mayReturn_alarm in Hret.
  contradiction.
Qed.

Lemma reject_post_tiling_affine_no_return :
  forall route pol_out,
    ~ mayReturn (Core.reject_post_tiling_affine route) pol_out.
Proof.
  intros route pol_out Hret.
  destruct route;
    unfold Core.reject_post_tiling_affine in Hret;
    cbn in Hret;
    unfold res_to_alarm in Hret;
    eapply mayReturn_alarm in Hret;
    contradiction.
Qed.

Ltac reject_tiling_contradiction H :=
  exfalso; eapply reject_tiling_no_return; exact H.

Ltac reject_post_tiling_affine_contradiction H :=
  exfalso; eapply reject_post_tiling_affine_no_return; exact H.

Lemma checked_parallel_current_annotated_codegen_at_correct :
  forall pol d pl st st',
    mayReturn (Core.checked_parallel_current_annotated_codegen_at pol d) (Okk pl) ->
    PolyLang.wf_pprog_general pol ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol d pl st st' Hopt Hwf Hsem.
  unfold Core.checked_parallel_current_annotated_codegen_at in Hopt.
  eapply Core.checked_parallel_current_annotated_codegen_correct; eauto.
Qed.

Lemma checked_vector_current_annotated_codegen_at_correct :
  forall pol d pl st st',
    mayReturn (Core.checked_vector_current_annotated_codegen_at pol d) (Okk pl) ->
    PolyLang.wf_pprog_general pol ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol d pl st st' Hopt Hwf Hsem.
  unfold Core.checked_vector_current_annotated_codegen_at in Hopt.
  eapply Core.checked_vector_current_annotated_codegen_correct; eauto.
Qed.

Lemma checked_parallel_current_many_annotated_codegen_at_correct :
  forall pol dims pl st st',
    mayReturn (Core.checked_parallel_current_many_annotated_codegen_at pol dims) (Okk pl) ->
    PolyLang.wf_pprog_general pol ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol dims pl st st' Hopt Hwf Hsem.
  unfold Core.checked_parallel_current_many_annotated_codegen_at in Hopt.
  bind_imp_destruct Hopt certs Hcerts.
  pose proof
    (Core.collect_parallel_current_codegen_certs_sound
       (PolyLang.current_view_pprog pol) dims certs Hcerts) as Hcerts_sound.
  destruct certs as [|cert certs].
  - apply mayReturn_pure in Hopt.
    discriminate Hopt.
  - eapply Core.ParallelCodegenCore.checked_annotated_codegen_many_correct_general;
      eauto.
Qed.

(** * Polyhedral preprocessing routes *)

Lemma try_verified_tiling_after_phase_mid_poly_correct :
  forall pol_mid mid_scop after_scop pol_out st st',
    PolyLang.wf_pprog_affine pol_mid ->
    mayReturn
      (Core.try_verified_tiling_after_phase_mid_poly pol_mid mid_scop after_scop)
      pol_out ->
    PolyLang.instance_list_semantics pol_out st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol_mid st st'' /\ State.eq st' st''.
Proof.
  intros pol_mid mid_scop after_scop pol_out st st' Hwf_mid Hopt Hsem_out.
  unfold Core.try_verified_tiling_after_phase_mid_poly in Hopt.
  remember (Core.CoreOpt.infer_tiling_witness_scops mid_scop after_scop) as wsres
    eqn:Hws.
  destruct wsres as [ws|msg].
  { remember (Core.ValidatorCore.import_canonical_tiled_after_poly pol_mid after_scop ws)
      as after_res eqn:Hafter.
    destruct after_res as [pol_after|msg_after].
    { cbn beta iota zeta in Hopt.
      bind_imp_destruct Hopt route Hroute.
      destruct route.
      { bind_imp_destruct Hopt wf_after_ok Hwf_check.
        destruct wf_after_ok.
        { apply mayReturn_pure in Hopt. subst pol_out.
          pose proof
            (Core.ValidatorCore.check_wf_polyprog_general_correct
               pol_after true Hwf_check eq_refl)
            as Hwf_after.
          pose proof
            (proj1 (PolyLang.instance_list_semantics_current_view_iff
                      pol_after st st' Hwf_after) Hsem_out)
            as Hsem_after.
          destruct
            (Core.TilingSched.checked_tiling_schedule_sourceb_first_runtime_validate_route_correct
               pol_mid pol_after ws st st'
               Core.TilingSched.DirectBandAccepted
               Hwf_mid Hwf_after Hroute eq_refl Hsem_after)
            as [st_mid [Hmid_sem Heq_mid]].
          exists st_mid. split; assumption. }
        { reject_tiling_contradiction Hopt. } }
      { bind_imp_destruct Hopt wf_after_ok Hwf_check.
        destruct wf_after_ok.
        { apply mayReturn_pure in Hopt. subst pol_out.
          pose proof
            (Core.ValidatorCore.check_wf_polyprog_general_correct
               pol_after true Hwf_check eq_refl)
            as Hwf_after.
          pose proof
            (proj1 (PolyLang.instance_list_semantics_current_view_iff
                      pol_after st st' Hwf_after) Hsem_out)
            as Hsem_after.
          destruct
            (Core.TilingSched.checked_tiling_schedule_sourceb_first_runtime_validate_route_correct
               pol_mid pol_after ws st st'
               Core.TilingSched.GeneralScheduleAccepted
               Hwf_mid Hwf_after Hroute eq_refl Hsem_after)
            as [st_mid [Hmid_sem Heq_mid]].
          exists st_mid. split; assumption. }
        { reject_tiling_contradiction Hopt. } }
      { reject_tiling_contradiction Hopt. } }
    { reject_tiling_contradiction Hopt. } }
  { reject_tiling_contradiction Hopt. }
Qed.

Lemma try_verified_tiling_after_phase_mid_poly_wf :
  forall pol_mid mid_scop after_scop pol_out,
    PolyLang.wf_pprog_affine pol_mid ->
    mayReturn
      (Core.try_verified_tiling_after_phase_mid_poly pol_mid mid_scop after_scop)
      pol_out ->
    PolyLang.wf_pprog_general pol_out.
Proof.
  intros pol_mid mid_scop after_scop pol_out Hwf_mid Hopt.
  unfold Core.try_verified_tiling_after_phase_mid_poly in Hopt.
  remember (Core.CoreOpt.infer_tiling_witness_scops mid_scop after_scop) as wsres
    eqn:Hws.
  destruct wsres as [ws|msg].
  { remember (Core.ValidatorCore.import_canonical_tiled_after_poly pol_mid after_scop ws)
      as after_res eqn:Hafter.
    destruct after_res as [pol_after|msg_after].
    { cbn beta iota zeta in Hopt.
      bind_imp_destruct Hopt route Hroute.
      destruct route.
      { bind_imp_destruct Hopt wf_after_ok Hwf_check.
        destruct wf_after_ok.
        { apply mayReturn_pure in Hopt. subst pol_out.
          pose proof
            (Core.ValidatorCore.check_wf_polyprog_general_correct
               pol_after true Hwf_check eq_refl)
            as Hwf_after.
          pose proof
            (PolyLang.wf_pprog_general_current_view_affine pol_after Hwf_after)
            as Hwf_cur_aff.
          eapply PolyLang.wf_pprog_affine_implies_wf_pprog_general; eauto. }
        { reject_tiling_contradiction Hopt. } }
      { bind_imp_destruct Hopt wf_after_ok Hwf_check.
        destruct wf_after_ok.
        { apply mayReturn_pure in Hopt. subst pol_out.
          pose proof
            (Core.ValidatorCore.check_wf_polyprog_general_correct
               pol_after true Hwf_check eq_refl)
            as Hwf_after.
          pose proof
            (PolyLang.wf_pprog_general_current_view_affine pol_after Hwf_after)
            as Hwf_cur_aff.
          eapply PolyLang.wf_pprog_affine_implies_wf_pprog_general; eauto. }
        { reject_tiling_contradiction Hopt. } }
      { reject_tiling_contradiction Hopt. } }
    { reject_tiling_contradiction Hopt. } }
  { reject_tiling_contradiction Hopt. }
Qed.

Lemma try_phase_pipeline_from_source_pol_poly_correct :
  forall pol_source phase_runner before_scop pol_out st st',
    PolyLang.wf_pprog_affine pol_source ->
    mayReturn
      (Core.try_phase_pipeline_from_source_pol_poly
         pol_source phase_runner before_scop)
      pol_out ->
    PolyLang.instance_list_semantics pol_out st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol_source st st'' /\ State.eq st' st''.
Proof.
  intros pol_source phase_runner before_scop pol_out st st'
         Hwf_source Hopt Hsem_out.
  unfold Core.try_phase_pipeline_from_source_pol_poly in Hopt.
  destruct (phase_runner before_scop) as [[mid_scop after_scop]|msg] eqn:Hphase.
  - destruct (Core.PolyLang.from_openscop_schedule_only pol_source mid_scop)
      as [pol_mid|msg_mid] eqn:Hmid.
    + bind_imp_destruct Hopt affine_ok Haff.
      destruct affine_ok.
      * pose proof
          (Core.ValidatorCore.validate_preserve_wf_pprog
             pol_source pol_mid _ Haff eq_refl)
          as [_ Hwf_mid].
        pose proof
          (try_verified_tiling_after_phase_mid_poly_correct
             pol_mid mid_scop after_scop pol_out st st'
             Hwf_mid Hopt Hsem_out)
          as Hmid_corr.
        destruct Hmid_corr as [st_mid [Hmid_sem Heq_mid]].
        pose proof
          (Core.ValidatorCore.validate_correct
             pol_source pol_mid st st_mid true Haff eq_refl Hmid_sem)
          as Haff_corr.
        destruct Haff_corr as [st_src [Hsrc_sem Heq_src]].
        exists st_src.
        split; auto.
        eapply State.eq_trans; eauto.
      * reject_tiling_contradiction Hopt.
    + reject_tiling_contradiction Hopt.
  - reject_tiling_contradiction Hopt.
Qed.

Lemma try_phase_pipeline_from_source_pol_poly_wf :
  forall pol_source phase_runner before_scop pol_out,
    PolyLang.wf_pprog_affine pol_source ->
    mayReturn
      (Core.try_phase_pipeline_from_source_pol_poly
         pol_source phase_runner before_scop)
      pol_out ->
    PolyLang.wf_pprog_general pol_out.
Proof.
  intros pol_source phase_runner before_scop pol_out Hwf_source Hopt.
  unfold Core.try_phase_pipeline_from_source_pol_poly in Hopt.
  destruct (phase_runner before_scop) as [[mid_scop after_scop]|msg] eqn:Hphase.
  - destruct (Core.PolyLang.from_openscop_schedule_only pol_source mid_scop)
      as [pol_mid|msg_mid] eqn:Hmid.
    + bind_imp_destruct Hopt affine_ok Haff.
      destruct affine_ok.
      * pose proof
          (Core.ValidatorCore.validate_preserve_wf_pprog
             pol_source pol_mid _ Haff eq_refl)
          as [_ Hwf_mid].
        eapply try_verified_tiling_after_phase_mid_poly_wf; eauto.
      * reject_tiling_contradiction Hopt.
    + reject_tiling_contradiction Hopt.
  - reject_tiling_contradiction Hopt.
Qed.

Lemma try_identity_tiling_phase_pipeline_from_source_pol_poly_correct :
  forall pol_source before_scop pol_out st st',
    PolyLang.wf_pprog_affine pol_source ->
    mayReturn
      (Core.try_identity_tiling_phase_pipeline_from_source_pol_poly
         pol_source before_scop)
      pol_out ->
    PolyLang.instance_list_semantics pol_out st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol_source st st'' /\ State.eq st' st''.
Proof.
  intros pol_source before_scop pol_out st st'
         Hwf_source Hopt Hsem_out.
  unfold Core.try_identity_tiling_phase_pipeline_from_source_pol_poly in Hopt.
  destruct (Core.CoreOpt.run_pluto_identity_tiling_pipeline before_scop)
    as [[mid_scop after_scop]|msg] eqn:Hphase.
  - destruct (Core.PolyLang.from_openscop_like_source pol_source mid_scop)
      as [pol_mid|msg_mid] eqn:Hmid.
    + bind_imp_destruct Hopt affine_ok Haff.
      destruct affine_ok.
      * pose proof
          (Core.ValidatorCore.validate_preserve_wf_pprog
             pol_source pol_mid _ Haff eq_refl)
          as [_ Hwf_mid].
        pose proof
          (try_verified_tiling_after_phase_mid_poly_correct
             pol_mid mid_scop after_scop pol_out st st'
             Hwf_mid Hopt Hsem_out)
          as Hmid_corr.
        destruct Hmid_corr as [st_mid [Hmid_sem Heq_mid]].
        pose proof
          (Core.ValidatorCore.validate_correct
             pol_source pol_mid st st_mid true Haff eq_refl Hmid_sem)
          as Haff_corr.
        destruct Haff_corr as [st_src [Hsrc_sem Heq_src]].
        exists st_src.
        split; auto.
        eapply State.eq_trans; eauto.
      * reject_tiling_contradiction Hopt.
    + reject_tiling_contradiction Hopt.
  - reject_tiling_contradiction Hopt.
Qed.

Lemma try_identity_tiling_phase_pipeline_from_source_pol_poly_wf :
  forall pol_source before_scop pol_out,
    PolyLang.wf_pprog_affine pol_source ->
    mayReturn
      (Core.try_identity_tiling_phase_pipeline_from_source_pol_poly
         pol_source before_scop)
      pol_out ->
    PolyLang.wf_pprog_general pol_out.
Proof.
  intros pol_source before_scop pol_out Hwf_source Hopt.
  unfold Core.try_identity_tiling_phase_pipeline_from_source_pol_poly in Hopt.
  destruct (Core.CoreOpt.run_pluto_identity_tiling_pipeline before_scop)
    as [[mid_scop after_scop]|msg] eqn:Hphase.
  - destruct (Core.PolyLang.from_openscop_like_source pol_source mid_scop)
      as [pol_mid|msg_mid] eqn:Hmid.
    + bind_imp_destruct Hopt affine_ok Haff.
      destruct affine_ok.
      * pose proof
          (Core.ValidatorCore.validate_preserve_wf_pprog
             pol_source pol_mid _ Haff eq_refl)
          as [_ Hwf_mid].
        eapply try_verified_tiling_after_phase_mid_poly_wf; eauto.
      * reject_tiling_contradiction Hopt.
    + reject_tiling_contradiction Hopt.
  - reject_tiling_contradiction Hopt.
Qed.

Lemma try_verified_post_tiling_affine_after_phase_mid_poly_correct :
  forall pol_mid mid_scop posttile_scop after_scop pol_out st st',
    PolyLang.wf_pprog_affine pol_mid ->
    mayReturn
      (Core.try_verified_post_tiling_affine_after_phase_mid_poly
         pol_mid mid_scop posttile_scop after_scop)
      pol_out ->
    PolyLang.instance_list_semantics pol_out st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol_mid st st'' /\ State.eq st' st''.
Proof.
  intros pol_mid mid_scop posttile_scop after_scop pol_out st st'
         Hwf_mid Hopt Hsem_out.
  unfold Core.try_verified_post_tiling_affine_after_phase_mid_poly in Hopt.
  destruct (Core.CoreOpt.infer_tiling_witness_scops mid_scop posttile_scop)
    as [ws|msg] eqn:Hws.
  - destruct
      (Core.ValidatorCore.import_canonical_tiled_after_poly pol_mid posttile_scop ws)
      as [pol_posttile|msg_after] eqn:Hposttile.
    + cbn beta iota zeta in Hopt.
      bind_imp_destruct Hopt route Hroute.
      destruct route.
      * bind_imp_destruct Hopt wf_posttile_ok Hwf_posttile_check.
        destruct wf_posttile_ok.
        -- pose proof
             (Core.ValidatorCore.check_wf_polyprog_general_correct
                pol_posttile true Hwf_posttile_check eq_refl)
             as Hwf_posttile.
           destruct (PolyLang.from_openscop_schedule_only pol_posttile after_scop)
             as [pol_after|msg_final] eqn:Hafter.
           ++ bind_imp_destruct Hopt final_ok Hfinal.
              destruct final_ok.
              ** bind_imp_destruct Hopt wf_after_ok Hwf_check.
                 destruct wf_after_ok.
                 --- apply mayReturn_pure in Hopt. subst pol_out.
                     pose proof
                       (Core.ValidatorCore.check_wf_polyprog_general_correct
                          pol_after true Hwf_check eq_refl)
                       as Hwf_after.
                     pose proof
                       (proj1
                          (PolyLang.instance_list_semantics_current_view_iff
                             pol_after st st' Hwf_after)
                          Hsem_out)
                       as Hsem_after.
                     destruct
                       (Core.ValidatorCore.validate_general_correct
                          pol_posttile pol_after st st'
                          true Hfinal eq_refl Hsem_after)
                       as [st_post [Hpost_sem Heq_post]].
                     destruct
                       (Core.TilingSched.checked_tiling_schedule_sourceb_first_runtime_validate_route_correct
                          pol_mid pol_posttile ws st st_post
                          Core.TilingSched.DirectBandAccepted
                          Hwf_mid Hwf_posttile Hroute eq_refl Hpost_sem)
                       as [st_mid [Hmid_sem Heq_mid]].
                     exists st_mid. split; auto.
                     eapply State.eq_trans; eauto.
                 --- reject_post_tiling_affine_contradiction Hopt.
              ** reject_post_tiling_affine_contradiction Hopt.
           ++ reject_post_tiling_affine_contradiction Hopt.
        -- reject_tiling_contradiction Hopt.
      * bind_imp_destruct Hopt wf_posttile_ok Hwf_posttile_check.
        destruct wf_posttile_ok.
        -- pose proof
             (Core.ValidatorCore.check_wf_polyprog_general_correct
                pol_posttile true Hwf_posttile_check eq_refl)
             as Hwf_posttile.
           destruct (PolyLang.from_openscop_schedule_only pol_posttile after_scop)
             as [pol_after|msg_final] eqn:Hafter.
           ++ bind_imp_destruct Hopt final_ok Hfinal.
              destruct final_ok.
              ** bind_imp_destruct Hopt wf_after_ok Hwf_check.
                 destruct wf_after_ok.
                 --- apply mayReturn_pure in Hopt. subst pol_out.
                     pose proof
                       (Core.ValidatorCore.check_wf_polyprog_general_correct
                          pol_after true Hwf_check eq_refl)
                       as Hwf_after.
                     pose proof
                       (proj1
                          (PolyLang.instance_list_semantics_current_view_iff
                             pol_after st st' Hwf_after)
                          Hsem_out)
                       as Hsem_after.
                     destruct
                       (Core.ValidatorCore.validate_general_correct
                          pol_posttile pol_after st st'
                          true Hfinal eq_refl Hsem_after)
                       as [st_post [Hpost_sem Heq_post]].
                     destruct
                       (Core.TilingSched.checked_tiling_schedule_sourceb_first_runtime_validate_route_correct
                          pol_mid pol_posttile ws st st_post
                          Core.TilingSched.GeneralScheduleAccepted
                          Hwf_mid Hwf_posttile Hroute eq_refl Hpost_sem)
                       as [st_mid [Hmid_sem Heq_mid]].
                     exists st_mid. split; auto.
                     eapply State.eq_trans; eauto.
                 --- reject_post_tiling_affine_contradiction Hopt.
              ** reject_post_tiling_affine_contradiction Hopt.
           ++ reject_post_tiling_affine_contradiction Hopt.
        -- reject_tiling_contradiction Hopt.
      * reject_tiling_contradiction Hopt.
    + reject_tiling_contradiction Hopt.
  - reject_tiling_contradiction Hopt.
Qed.

Lemma try_verified_post_tiling_affine_after_phase_mid_poly_wf :
  forall pol_mid mid_scop posttile_scop after_scop pol_out,
    PolyLang.wf_pprog_affine pol_mid ->
    mayReturn
      (Core.try_verified_post_tiling_affine_after_phase_mid_poly
         pol_mid mid_scop posttile_scop after_scop)
      pol_out ->
    PolyLang.wf_pprog_general pol_out.
Proof.
  intros pol_mid mid_scop posttile_scop after_scop pol_out Hwf_mid Hopt.
  unfold Core.try_verified_post_tiling_affine_after_phase_mid_poly in Hopt.
  destruct (Core.CoreOpt.infer_tiling_witness_scops mid_scop posttile_scop)
    as [ws|msg] eqn:Hws.
  - destruct
      (Core.ValidatorCore.import_canonical_tiled_after_poly pol_mid posttile_scop ws)
      as [pol_posttile|msg_after] eqn:Hposttile.
    + cbn beta iota zeta in Hopt.
      bind_imp_destruct Hopt route Hroute.
      destruct route.
      * bind_imp_destruct Hopt wf_posttile_ok Hwf_posttile_check.
        destruct wf_posttile_ok.
        -- destruct (PolyLang.from_openscop_schedule_only pol_posttile after_scop)
             as [pol_after|msg_final] eqn:Hafter.
           ++ bind_imp_destruct Hopt final_ok Hfinal.
              destruct final_ok.
              ** bind_imp_destruct Hopt wf_after_ok Hwf_check.
                 destruct wf_after_ok.
                 --- apply mayReturn_pure in Hopt. subst pol_out.
                     pose proof
                       (Core.ValidatorCore.check_wf_polyprog_general_correct
                          pol_after true Hwf_check eq_refl)
                       as Hwf_after.
                     pose proof
                       (PolyLang.wf_pprog_general_current_view_affine
                          pol_after Hwf_after)
                       as Hwf_cur_aff.
                     eapply PolyLang.wf_pprog_affine_implies_wf_pprog_general;
                       eauto.
                 --- reject_post_tiling_affine_contradiction Hopt.
              ** reject_post_tiling_affine_contradiction Hopt.
           ++ reject_post_tiling_affine_contradiction Hopt.
        -- reject_tiling_contradiction Hopt.
      * bind_imp_destruct Hopt wf_posttile_ok Hwf_posttile_check.
        destruct wf_posttile_ok.
        -- destruct (PolyLang.from_openscop_schedule_only pol_posttile after_scop)
             as [pol_after|msg_final] eqn:Hafter.
           ++ bind_imp_destruct Hopt final_ok Hfinal.
              destruct final_ok.
              ** bind_imp_destruct Hopt wf_after_ok Hwf_check.
                 destruct wf_after_ok.
                 --- apply mayReturn_pure in Hopt. subst pol_out.
                     pose proof
                       (Core.ValidatorCore.check_wf_polyprog_general_correct
                          pol_after true Hwf_check eq_refl)
                       as Hwf_after.
                     pose proof
                       (PolyLang.wf_pprog_general_current_view_affine
                          pol_after Hwf_after)
                       as Hwf_cur_aff.
                     eapply PolyLang.wf_pprog_affine_implies_wf_pprog_general;
                       eauto.
                 --- reject_post_tiling_affine_contradiction Hopt.
              ** reject_post_tiling_affine_contradiction Hopt.
           ++ reject_post_tiling_affine_contradiction Hopt.
        -- reject_tiling_contradiction Hopt.
      * reject_tiling_contradiction Hopt.
    + reject_tiling_contradiction Hopt.
  - reject_tiling_contradiction Hopt.
Qed.

Lemma try_post_tiling_affine_phase_pipeline_from_source_pol_poly_correct :
  forall pol_source before_scop pol_out st st',
    PolyLang.wf_pprog_affine pol_source ->
    mayReturn
      (Core.try_post_tiling_affine_phase_pipeline_from_source_pol_poly
         pol_source before_scop)
      pol_out ->
    PolyLang.instance_list_semantics pol_out st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol_source st st'' /\ State.eq st' st''.
Proof.
  intros pol_source before_scop pol_out st st'
         Hwf_source Hopt Hsem_out.
  unfold Core.try_post_tiling_affine_phase_pipeline_from_source_pol_poly in Hopt.
  destruct (Core.CoreOpt.run_pluto_post_tiling_affine_phase_pipeline before_scop)
    as [[mid_scop [posttile_scop after_scop]]|msg] eqn:Hphase.
  - destruct (Core.PolyLang.from_openscop_schedule_only pol_source mid_scop)
      as [pol_mid|msg_mid] eqn:Hmid.
    + bind_imp_destruct Hopt affine_ok Haff.
      destruct affine_ok.
      * pose proof
          (Core.ValidatorCore.validate_preserve_wf_pprog
             pol_source pol_mid _ Haff eq_refl)
          as [_ Hwf_mid].
        pose proof
          (try_verified_post_tiling_affine_after_phase_mid_poly_correct
             pol_mid mid_scop posttile_scop after_scop pol_out st st'
             Hwf_mid Hopt Hsem_out)
          as Hmid_corr.
        destruct Hmid_corr as [st_mid [Hmid_sem Heq_mid]].
        pose proof
          (Core.ValidatorCore.validate_correct
             pol_source pol_mid st st_mid true Haff eq_refl Hmid_sem)
          as Haff_corr.
        destruct Haff_corr as [st_src [Hsrc_sem Heq_src]].
        exists st_src.
        split; auto.
        eapply State.eq_trans; eauto.
      * reject_tiling_contradiction Hopt.
    + reject_tiling_contradiction Hopt.
  - reject_tiling_contradiction Hopt.
Qed.

Lemma try_post_tiling_affine_phase_pipeline_from_source_pol_poly_wf :
  forall pol_source before_scop pol_out,
    PolyLang.wf_pprog_affine pol_source ->
    mayReturn
      (Core.try_post_tiling_affine_phase_pipeline_from_source_pol_poly
         pol_source before_scop)
      pol_out ->
    PolyLang.wf_pprog_general pol_out.
Proof.
  intros pol_source before_scop pol_out Hwf_source Hopt.
  unfold Core.try_post_tiling_affine_phase_pipeline_from_source_pol_poly in Hopt.
  destruct (Core.CoreOpt.run_pluto_post_tiling_affine_phase_pipeline before_scop)
    as [[mid_scop [posttile_scop after_scop]]|msg] eqn:Hphase.
  - destruct (Core.PolyLang.from_openscop_schedule_only pol_source mid_scop)
      as [pol_mid|msg_mid] eqn:Hmid.
    + bind_imp_destruct Hopt affine_ok Haff.
      destruct affine_ok.
      * pose proof
          (Core.ValidatorCore.validate_preserve_wf_pprog
             pol_source pol_mid _ Haff eq_refl)
          as [_ Hwf_mid].
        eapply try_verified_post_tiling_affine_after_phase_mid_poly_wf; eauto.
      * reject_tiling_contradiction Hopt.
    + reject_tiling_contradiction Hopt.
  - reject_tiling_contradiction Hopt.
Qed.

Lemma post_tiling_affine_phase_pipeline_opt_prepared_from_poly_no_iss_poly_correct :
  forall pol pol_out st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.post_tiling_affine_phase_pipeline_opt_prepared_from_poly_no_iss_poly pol) pol_out ->
    PolyLang.instance_list_semantics pol_out st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol pol_out st st' Hwf Hopt Hsem_out.
  unfold Core.post_tiling_affine_phase_pipeline_opt_prepared_from_poly_no_iss_poly in Hopt.
  destruct (Core.CoreOpt.has_nonscalar_stmt pol) eqn:Hnonscalar.
  { destruct (Core.CoreOpt.export_for_phase_scheduler pol) as [before_scop|] eqn:Hbefore.
    { simpl in Hopt.
      eapply try_post_tiling_affine_phase_pipeline_from_source_pol_poly_correct.
      - exact Hwf.
      - exact Hopt.
      - exact Hsem_out. }
    { reject_tiling_contradiction Hopt. } }
  { reject_tiling_contradiction Hopt. }
Qed.

Lemma post_tiling_affine_phase_pipeline_opt_prepared_from_poly_no_iss_poly_wf :
  forall pol pol_out,
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.post_tiling_affine_phase_pipeline_opt_prepared_from_poly_no_iss_poly pol) pol_out ->
    PolyLang.wf_pprog_general pol_out.
Proof.
  intros pol pol_out Hwf Hopt.
  unfold Core.post_tiling_affine_phase_pipeline_opt_prepared_from_poly_no_iss_poly in Hopt.
  destruct (Core.CoreOpt.has_nonscalar_stmt pol) eqn:Hnonscalar.
  { destruct (Core.CoreOpt.export_for_phase_scheduler pol) as [before_scop|] eqn:Hbefore.
    { simpl in Hopt.
      eapply try_post_tiling_affine_phase_pipeline_from_source_pol_poly_wf.
      - exact Hwf.
      - exact Hopt. }
    { reject_tiling_contradiction Hopt. } }
  { reject_tiling_contradiction Hopt. }
Qed.

Lemma try_post_tiling_affine_phase_pipeline_from_source_pol_poly_with_iss_correct :
  forall pol_source before_scop pol_out st st',
    PolyLang.wf_pprog_affine pol_source ->
    mayReturn
      (Core.try_post_tiling_affine_phase_pipeline_from_source_pol_poly_with_iss
         pol_source before_scop)
      pol_out ->
    PolyLang.instance_list_semantics pol_out st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol_source st st'' /\ State.eq st' st''.
Proof.
  intros pol_source before_scop pol_out st st'
         Hwf_source Hopt Hsem_out.
  unfold Core.try_post_tiling_affine_phase_pipeline_from_source_pol_poly_with_iss in Hopt.
  destruct (Core.CoreOpt.run_pluto_post_tiling_affine_phase_pipeline_with_iss before_scop)
    as [[mid_scop [posttile_scop after_scop]]|msg] eqn:Hphase.
  - destruct (Core.PolyLang.from_openscop_schedule_only pol_source mid_scop)
      as [pol_mid|msg_mid] eqn:Hmid.
    + bind_imp_destruct Hopt affine_ok Haff.
      destruct affine_ok.
      * pose proof
          (Core.ValidatorCore.validate_preserve_wf_pprog
             pol_source pol_mid _ Haff eq_refl)
          as [_ Hwf_mid].
        pose proof
          (try_verified_post_tiling_affine_after_phase_mid_poly_correct
             pol_mid mid_scop posttile_scop after_scop pol_out st st'
             Hwf_mid Hopt Hsem_out)
          as Hmid_corr.
        destruct Hmid_corr as [st_mid [Hmid_sem Heq_mid]].
        pose proof
          (Core.ValidatorCore.validate_correct
             pol_source pol_mid st st_mid true Haff eq_refl Hmid_sem)
          as Haff_corr.
        destruct Haff_corr as [st_src [Hsrc_sem Heq_src]].
        exists st_src.
        split; auto.
        eapply State.eq_trans; eauto.
      * reject_tiling_contradiction Hopt.
    + reject_tiling_contradiction Hopt.
  - reject_tiling_contradiction Hopt.
Qed.

Lemma try_post_tiling_affine_phase_pipeline_from_source_pol_poly_with_iss_wf :
  forall pol_source before_scop pol_out,
    PolyLang.wf_pprog_affine pol_source ->
    mayReturn
      (Core.try_post_tiling_affine_phase_pipeline_from_source_pol_poly_with_iss
         pol_source before_scop)
      pol_out ->
    PolyLang.wf_pprog_general pol_out.
Proof.
  intros pol_source before_scop pol_out Hwf_source Hopt.
  unfold Core.try_post_tiling_affine_phase_pipeline_from_source_pol_poly_with_iss in Hopt.
  destruct (Core.CoreOpt.run_pluto_post_tiling_affine_phase_pipeline_with_iss before_scop)
    as [[mid_scop [posttile_scop after_scop]]|msg] eqn:Hphase.
  - destruct (Core.PolyLang.from_openscop_schedule_only pol_source mid_scop)
      as [pol_mid|msg_mid] eqn:Hmid.
    + bind_imp_destruct Hopt affine_ok Haff.
      destruct affine_ok.
      * pose proof
          (Core.ValidatorCore.validate_preserve_wf_pprog
             pol_source pol_mid _ Haff eq_refl)
          as [_ Hwf_mid].
        eapply try_verified_post_tiling_affine_after_phase_mid_poly_wf; eauto.
      * reject_tiling_contradiction Hopt.
    + reject_tiling_contradiction Hopt.
  - reject_tiling_contradiction Hopt.
Qed.

Lemma try_checked_iss_post_tiling_affine_phase_pipeline_from_poly_poly_correct :
  forall pol before_scop pol_out st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn
      (Core.try_checked_iss_post_tiling_affine_phase_pipeline_from_poly_poly
         pol before_scop)
      pol_out ->
    PolyLang.instance_list_semantics pol_out st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol before_scop pol_out st st' Hwf Hopt Hsem_out.
  unfold Core.try_checked_iss_post_tiling_affine_phase_pipeline_from_poly_poly in Hopt.
  destruct (Core.CoreOpt.infer_iss_from_source_scop pol before_scop) as [iss_opt|msg]
    eqn:Hiss_infer.
  - destruct iss_opt as [[pol_iss w]|].
    + destruct (Core.ValidatorCore.checked_iss_complete_cut_shape_validate pol pol_iss w)
        eqn:Hiss_check.
      * bind_imp_destruct Hopt iss_wf Hiss_wf.
        destruct iss_wf.
        -- pose proof
             (CoreOpt.check_wf_polyprog_affine_correct pol_iss _ Hiss_wf eq_refl)
             as Hwf_iss.
           destruct (Core.CoreOpt.export_for_phase_scheduler pol_iss) as [iss_scop|].
           2:{ reject_tiling_contradiction Hopt. }
           pose proof
             (try_post_tiling_affine_phase_pipeline_from_source_pol_poly_correct
                pol_iss iss_scop pol_out st st' Hwf_iss Hopt Hsem_out)
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
        -- eapply try_post_tiling_affine_phase_pipeline_from_source_pol_poly_correct; eauto.
      * eapply try_post_tiling_affine_phase_pipeline_from_source_pol_poly_correct; eauto.
    + eapply try_post_tiling_affine_phase_pipeline_from_source_pol_poly_correct; eauto.
  - eapply try_post_tiling_affine_phase_pipeline_from_source_pol_poly_correct; eauto.
Qed.

Lemma try_checked_iss_post_tiling_affine_phase_pipeline_from_poly_poly_wf :
  forall pol before_scop pol_out,
    PolyLang.wf_pprog_affine pol ->
    mayReturn
      (Core.try_checked_iss_post_tiling_affine_phase_pipeline_from_poly_poly
         pol before_scop)
      pol_out ->
    PolyLang.wf_pprog_general pol_out.
Proof.
  intros pol before_scop pol_out Hwf Hopt.
  unfold Core.try_checked_iss_post_tiling_affine_phase_pipeline_from_poly_poly in Hopt.
  destruct (Core.CoreOpt.infer_iss_from_source_scop pol before_scop) as [iss_opt|msg]
    eqn:Hiss_infer.
  - destruct iss_opt as [[pol_iss w]|].
    + destruct (Core.ValidatorCore.checked_iss_complete_cut_shape_validate pol pol_iss w)
        eqn:Hiss_check.
      * bind_imp_destruct Hopt iss_wf Hiss_wf.
        destruct iss_wf.
        -- pose proof
             (CoreOpt.check_wf_polyprog_affine_correct pol_iss _ Hiss_wf eq_refl)
             as Hwf_iss.
           destruct (Core.CoreOpt.export_for_phase_scheduler pol_iss) as [iss_scop|].
           2:{ reject_tiling_contradiction Hopt. }
           eapply try_post_tiling_affine_phase_pipeline_from_source_pol_poly_wf; eauto.
        -- eapply try_post_tiling_affine_phase_pipeline_from_source_pol_poly_wf; eauto.
      * eapply try_post_tiling_affine_phase_pipeline_from_source_pol_poly_wf; eauto.
    + eapply try_post_tiling_affine_phase_pipeline_from_source_pol_poly_wf; eauto.
  - eapply try_post_tiling_affine_phase_pipeline_from_source_pol_poly_wf; eauto.
Qed.

Lemma post_tiling_affine_phase_pipeline_opt_prepared_from_poly_with_iss_poly_correct :
  forall pol pol_out st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.post_tiling_affine_phase_pipeline_opt_prepared_from_poly_with_iss_poly pol) pol_out ->
    PolyLang.instance_list_semantics pol_out st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol pol_out st st' Hwf Hopt Hsem_out.
  unfold Core.post_tiling_affine_phase_pipeline_opt_prepared_from_poly_with_iss_poly in Hopt.
  destruct (Core.CoreOpt.has_nonscalar_stmt pol) eqn:Hnonscalar.
  { destruct (Core.CoreOpt.export_for_phase_scheduler pol) as [before_scop|] eqn:Hbefore.
    { simpl in Hopt.
      eapply try_checked_iss_post_tiling_affine_phase_pipeline_from_poly_poly_correct.
      - exact Hwf.
      - exact Hopt.
      - exact Hsem_out. }
    { reject_tiling_contradiction Hopt. } }
  { reject_tiling_contradiction Hopt. }
Qed.

Lemma post_tiling_affine_phase_pipeline_opt_prepared_from_poly_with_iss_poly_wf :
  forall pol pol_out,
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.post_tiling_affine_phase_pipeline_opt_prepared_from_poly_with_iss_poly pol) pol_out ->
    PolyLang.wf_pprog_general pol_out.
Proof.
  intros pol pol_out Hwf Hopt.
  unfold Core.post_tiling_affine_phase_pipeline_opt_prepared_from_poly_with_iss_poly in Hopt.
  destruct (Core.CoreOpt.has_nonscalar_stmt pol) eqn:Hnonscalar.
  { destruct (Core.CoreOpt.export_for_phase_scheduler pol) as [before_scop|] eqn:Hbefore.
    { simpl in Hopt.
      eapply try_checked_iss_post_tiling_affine_phase_pipeline_from_poly_poly_wf.
      - exact Hwf.
      - exact Hopt. }
    { reject_tiling_contradiction Hopt. } }
  { reject_tiling_contradiction Hopt. }
Qed.

Lemma phase_pipeline_opt_prepared_from_poly_no_iss_poly_correct :
  forall pol pol_out st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.phase_pipeline_opt_prepared_from_poly_no_iss_poly pol) pol_out ->
    PolyLang.instance_list_semantics pol_out st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol pol_out st st' Hwf Hopt Hsem_out.
  unfold Core.phase_pipeline_opt_prepared_from_poly_no_iss_poly in Hopt.
  destruct (Core.CoreOpt.has_nonscalar_stmt pol) eqn:Hnonscalar.
  { destruct (Core.CoreOpt.export_for_phase_scheduler pol) as [before_scop|] eqn:Hbefore.
    { simpl in Hopt.
      eapply try_phase_pipeline_from_source_pol_poly_correct.
      - exact Hwf.
      - exact Hopt.
      - exact Hsem_out. }
    { reject_tiling_contradiction Hopt. } }
  { reject_tiling_contradiction Hopt. }
Qed.

Lemma phase_pipeline_opt_prepared_from_poly_no_iss_poly_wf :
  forall pol pol_out,
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.phase_pipeline_opt_prepared_from_poly_no_iss_poly pol) pol_out ->
    PolyLang.wf_pprog_general pol_out.
Proof.
  intros pol pol_out Hwf Hopt.
  unfold Core.phase_pipeline_opt_prepared_from_poly_no_iss_poly in Hopt.
  destruct (Core.CoreOpt.has_nonscalar_stmt pol) eqn:Hnonscalar.
  { destruct (Core.CoreOpt.export_for_phase_scheduler pol) as [before_scop|] eqn:Hbefore.
    { simpl in Hopt.
      eapply try_phase_pipeline_from_source_pol_poly_wf.
      - exact Hwf.
      - exact Hopt. }
    { reject_tiling_contradiction Hopt. } }
  { reject_tiling_contradiction Hopt. }
Qed.

Lemma identity_tiling_opt_prepared_from_poly_no_iss_poly_correct :
  forall pol pol_out st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.identity_tiling_opt_prepared_from_poly_no_iss_poly pol) pol_out ->
    PolyLang.instance_list_semantics pol_out st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol pol_out st st' Hwf Hopt Hsem_out.
  unfold Core.identity_tiling_opt_prepared_from_poly_no_iss_poly in Hopt.
  destruct (Core.CoreOpt.has_nonscalar_stmt pol) eqn:Hnonscalar.
  { destruct (Core.CoreOpt.export_for_phase_scheduler pol) as [before_scop|] eqn:Hbefore.
    { simpl in Hopt.
      eapply try_identity_tiling_phase_pipeline_from_source_pol_poly_correct.
      - exact Hwf.
      - exact Hopt.
      - exact Hsem_out. }
    { reject_tiling_contradiction Hopt. } }
  { reject_tiling_contradiction Hopt. }
Qed.

Lemma identity_tiling_opt_prepared_from_poly_no_iss_poly_wf :
  forall pol pol_out,
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.identity_tiling_opt_prepared_from_poly_no_iss_poly pol) pol_out ->
    PolyLang.wf_pprog_general pol_out.
Proof.
  intros pol pol_out Hwf Hopt.
  unfold Core.identity_tiling_opt_prepared_from_poly_no_iss_poly in Hopt.
  destruct (Core.CoreOpt.has_nonscalar_stmt pol) eqn:Hnonscalar.
  { destruct (Core.CoreOpt.export_for_phase_scheduler pol) as [before_scop|] eqn:Hbefore.
    { simpl in Hopt.
      eapply try_identity_tiling_phase_pipeline_from_source_pol_poly_wf.
      - exact Hwf.
      - exact Hopt. }
    { reject_tiling_contradiction Hopt. } }
  { reject_tiling_contradiction Hopt. }
Qed.

Lemma try_checked_iss_phase_pipeline_from_poly_poly_correct :
  forall pol before_scop pol_out st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn
      (Core.try_checked_iss_phase_pipeline_from_poly_poly pol before_scop)
      pol_out ->
    PolyLang.instance_list_semantics pol_out st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol before_scop pol_out st st' Hwf Hopt Hsem_out.
  unfold Core.try_checked_iss_phase_pipeline_from_poly_poly in Hopt.
  destruct (Core.CoreOpt.infer_iss_from_source_scop pol before_scop) as [iss_opt|msg]
    eqn:Hiss_infer.
  - destruct iss_opt as [[pol_iss w]|].
    + destruct (Core.ValidatorCore.checked_iss_complete_cut_shape_validate pol pol_iss w)
        eqn:Hiss_check.
      * bind_imp_destruct Hopt iss_wf Hiss_wf.
        destruct iss_wf.
        -- pose proof
             (CoreOpt.check_wf_polyprog_affine_correct pol_iss _ Hiss_wf eq_refl)
             as Hwf_iss.
           destruct (Core.CoreOpt.export_for_phase_scheduler pol_iss) as [iss_scop|].
           2:{ reject_tiling_contradiction Hopt. }
           pose proof
             (try_phase_pipeline_from_source_pol_poly_correct
                pol_iss
                CoreOpt.run_pluto_phase_pipeline
                iss_scop
                pol_out st st' Hwf_iss Hopt Hsem_out)
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
        -- eapply try_phase_pipeline_from_source_pol_poly_correct; eauto.
      * eapply try_phase_pipeline_from_source_pol_poly_correct; eauto.
    + eapply try_phase_pipeline_from_source_pol_poly_correct; eauto.
  - eapply try_phase_pipeline_from_source_pol_poly_correct; eauto.
Qed.

Lemma try_checked_iss_phase_pipeline_from_poly_poly_wf :
  forall pol before_scop pol_out,
    PolyLang.wf_pprog_affine pol ->
    mayReturn
      (Core.try_checked_iss_phase_pipeline_from_poly_poly pol before_scop)
      pol_out ->
    PolyLang.wf_pprog_general pol_out.
Proof.
  intros pol before_scop pol_out Hwf Hopt.
  unfold Core.try_checked_iss_phase_pipeline_from_poly_poly in Hopt.
  destruct (Core.CoreOpt.infer_iss_from_source_scop pol before_scop) as [iss_opt|msg]
    eqn:Hiss_infer.
  - destruct iss_opt as [[pol_iss w]|].
    + destruct (Core.ValidatorCore.checked_iss_complete_cut_shape_validate pol pol_iss w)
        eqn:Hiss_check.
      * bind_imp_destruct Hopt iss_wf Hiss_wf.
        destruct iss_wf.
        -- pose proof
             (CoreOpt.check_wf_polyprog_affine_correct pol_iss _ Hiss_wf eq_refl)
             as Hwf_iss.
           destruct (Core.CoreOpt.export_for_phase_scheduler pol_iss) as [iss_scop|].
           2:{ reject_tiling_contradiction Hopt. }
           eapply try_phase_pipeline_from_source_pol_poly_wf; eauto.
        -- eapply try_phase_pipeline_from_source_pol_poly_wf; eauto.
      * eapply try_phase_pipeline_from_source_pol_poly_wf; eauto.
    + eapply try_phase_pipeline_from_source_pol_poly_wf; eauto.
  - eapply try_phase_pipeline_from_source_pol_poly_wf; eauto.
Qed.

Lemma phase_pipeline_opt_prepared_from_poly_with_iss_poly_correct :
  forall pol pol_out st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.phase_pipeline_opt_prepared_from_poly_with_iss_poly pol) pol_out ->
    PolyLang.instance_list_semantics pol_out st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol pol_out st st' Hwf Hopt Hsem_out.
  unfold Core.phase_pipeline_opt_prepared_from_poly_with_iss_poly in Hopt.
  destruct (Core.CoreOpt.has_nonscalar_stmt pol) eqn:Hnonscalar.
  { destruct (Core.CoreOpt.export_for_phase_scheduler pol) as [before_scop|] eqn:Hbefore.
    { simpl in Hopt.
      eapply try_checked_iss_phase_pipeline_from_poly_poly_correct.
      - exact Hwf.
      - exact Hopt.
      - exact Hsem_out. }
    { reject_tiling_contradiction Hopt. } }
  { reject_tiling_contradiction Hopt. }
Qed.

Lemma phase_pipeline_opt_prepared_from_poly_with_iss_poly_wf :
  forall pol pol_out,
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.phase_pipeline_opt_prepared_from_poly_with_iss_poly pol) pol_out ->
    PolyLang.wf_pprog_general pol_out.
Proof.
  intros pol pol_out Hwf Hopt.
  unfold Core.phase_pipeline_opt_prepared_from_poly_with_iss_poly in Hopt.
  destruct (Core.CoreOpt.has_nonscalar_stmt pol) eqn:Hnonscalar.
  { destruct (Core.CoreOpt.export_for_phase_scheduler pol) as [before_scop|] eqn:Hbefore.
    { simpl in Hopt.
      eapply try_checked_iss_phase_pipeline_from_poly_poly_wf.
      - exact Hwf.
      - exact Hopt. }
    { reject_tiling_contradiction Hopt. } }
  { reject_tiling_contradiction Hopt. }
Qed.

Lemma iss_only_prepared_from_poly_correct :
  forall pol pol_out st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.iss_only_prepared_from_poly pol) pol_out ->
    PolyLang.instance_list_semantics pol_out st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol pol_out st st' Hwf Hopt Hsem_out.
  unfold Core.iss_only_prepared_from_poly in Hopt.
  destruct (Core.CoreOpt.export_for_phase_scheduler pol) as [before_scop|] eqn:Hbefore.
  - destruct (Core.CoreOpt.infer_iss_from_source_scop pol before_scop) as [iss_opt|msg]
      eqn:Hiss_infer.
    + destruct iss_opt as [[pol_iss w]|].
      * destruct (Core.ValidatorCore.checked_iss_complete_cut_shape_validate pol pol_iss w)
          eqn:Hiss_check.
        -- bind_imp_destruct Hopt iss_wf Hiss_wf.
           destruct iss_wf.
           ++ eapply mayReturn_pure in Hopt. subst pol_out.
              eapply ISSValidatorCorrectCore.checked_iss_complete_cut_shape_validate_semantics_correct;
                eauto.
           ++ eapply mayReturn_pure in Hopt. subst pol_out.
              exists st'. split; auto. eapply State.eq_refl.
        -- eapply mayReturn_pure in Hopt. subst pol_out.
           exists st'. split; auto. eapply State.eq_refl.
      * eapply mayReturn_pure in Hopt. subst pol_out.
        exists st'. split; auto. eapply State.eq_refl.
    + eapply mayReturn_pure in Hopt. subst pol_out.
      exists st'. split; auto. eapply State.eq_refl.
  - eapply mayReturn_pure in Hopt. subst pol_out.
    exists st'. split; auto. eapply State.eq_refl.
Qed.

Lemma iss_only_prepared_from_poly_wf_affine :
  forall pol pol_out,
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.iss_only_prepared_from_poly pol) pol_out ->
    PolyLang.wf_pprog_affine pol_out.
Proof.
  intros pol pol_out Hwf Hopt.
  unfold Core.iss_only_prepared_from_poly in Hopt.
  destruct (Core.CoreOpt.export_for_phase_scheduler pol) as [before_scop|] eqn:Hbefore.
  - destruct (Core.CoreOpt.infer_iss_from_source_scop pol before_scop) as [iss_opt|msg]
      eqn:Hiss_infer.
    + destruct iss_opt as [[pol_iss w]|].
      * destruct (Core.ValidatorCore.checked_iss_complete_cut_shape_validate pol pol_iss w)
          eqn:Hiss_check.
        -- bind_imp_destruct Hopt iss_wf Hiss_wf.
           destruct iss_wf.
           ++ eapply mayReturn_pure in Hopt. subst pol_out.
              eapply CoreOpt.check_wf_polyprog_affine_correct.
              ** exact Hiss_wf.
              ** reflexivity.
           ++ eapply mayReturn_pure in Hopt. subst pol_out. exact Hwf.
        -- eapply mayReturn_pure in Hopt. subst pol_out. exact Hwf.
      * eapply mayReturn_pure in Hopt. subst pol_out. exact Hwf.
    + eapply mayReturn_pure in Hopt. subst pol_out. exact Hwf.
  - eapply mayReturn_pure in Hopt. subst pol_out. exact Hwf.
Qed.

Lemma identity_tiling_opt_prepared_from_poly_with_iss_poly_correct :
  forall pol pol_out st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.identity_tiling_opt_prepared_from_poly_with_iss_poly pol) pol_out ->
    PolyLang.instance_list_semantics pol_out st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol pol_out st st' Hwf Hopt Hsem_out.
  unfold Core.identity_tiling_opt_prepared_from_poly_with_iss_poly in Hopt.
  bind_imp_destruct Hopt pol_iss Hiss.
  pose proof
    (iss_only_prepared_from_poly_wf_affine pol pol_iss Hwf Hiss)
    as Hwf_iss.
  pose proof
    (identity_tiling_opt_prepared_from_poly_no_iss_poly_correct
       pol_iss pol_out st st' Hwf_iss Hopt Hsem_out)
    as Hidentity_corr.
  destruct Hidentity_corr as [st_iss [Hiss_sem Heq_iss]].
  pose proof
    (iss_only_prepared_from_poly_correct
       pol pol_iss st st_iss Hwf Hiss Hiss_sem)
    as Hiss_corr.
  destruct Hiss_corr as [st_src [Hsrc_sem Heq_src]].
  exists st_src.
  split; auto.
  eapply State.eq_trans; eauto.
Qed.

Lemma identity_tiling_opt_prepared_from_poly_with_iss_poly_wf :
  forall pol pol_out,
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.identity_tiling_opt_prepared_from_poly_with_iss_poly pol) pol_out ->
    PolyLang.wf_pprog_general pol_out.
Proof.
  intros pol pol_out Hwf Hopt.
  unfold Core.identity_tiling_opt_prepared_from_poly_with_iss_poly in Hopt.
  bind_imp_destruct Hopt pol_iss Hiss.
  pose proof
    (iss_only_prepared_from_poly_wf_affine pol pol_iss Hwf Hiss)
    as Hwf_iss.
  eapply identity_tiling_opt_prepared_from_poly_no_iss_poly_wf; eauto.
Qed.

Lemma iss_affine_prepared_from_poly_correct :
  forall pol pol_out st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.iss_affine_prepared_from_poly pol) pol_out ->
    PolyLang.instance_list_semantics pol_out st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol pol_out st st' Hwf Hopt Hsem_out.
  unfold Core.iss_affine_prepared_from_poly in Hopt.
  bind_imp_destruct Hopt pol_iss Hiss.
  pose proof
    (iss_only_prepared_from_poly_wf_affine pol pol_iss Hwf Hiss)
    as Hwf_iss.
  pose proof
    (CoreOpt.scheduler'_correct pol_iss st st' pol_out Hopt Hsem_out)
    as Haff_corr.
  destruct Haff_corr as [st_iss [Hiss_sem Heq_iss]].
  pose proof
    (iss_only_prepared_from_poly_correct pol pol_iss st st_iss Hwf Hiss Hiss_sem)
    as Hsrc_corr.
  destruct Hsrc_corr as [st_src [Hsrc_sem Heq_src]].
  exists st_src.
  split; auto.
  eapply State.eq_trans; eauto.
Qed.

Lemma iss_affine_prepared_from_poly_wf_affine :
  forall pol pol_out,
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.iss_affine_prepared_from_poly pol) pol_out ->
    PolyLang.wf_pprog_affine pol_out.
Proof.
  intros pol pol_out Hwf Hopt.
  unfold Core.iss_affine_prepared_from_poly in Hopt.
  bind_imp_destruct Hopt pol_iss Hiss.
  pose proof
    (iss_only_prepared_from_poly_wf_affine pol pol_iss Hwf Hiss)
    as Hwf_iss.
  eapply CoreOpt.scheduler'_preserve_wf; eauto.
Qed.

(** Every prepared parallel or vector route has the same semantic shape.
    First, a checked polyhedral transformation produces [pol_after].  Second,
    annotation and code generation relate the target execution to
    [pol_after].  This typed local lemma exposes the two semantic premises and
    the single [State.eq] composition instead of recovering them from the goal
    shape with Ltac. *)
Local Lemma checked_annotation_after_preparation_correct
    {A : Type}
    {prepare : PolyLang.t -> imp PolyLang.t}
    {annotate : PolyLang.t -> A ->
      imp (result Core.ParallelCodegenCore.ParallelLoop.t)}
    (prepare_wf :
      forall pol pol_after,
        PolyLang.wf_pprog_affine pol ->
        mayReturn (prepare pol) pol_after ->
        PolyLang.wf_pprog_general pol_after)
    (prepare_correct :
      forall pol pol_after st st',
        PolyLang.wf_pprog_affine pol ->
        mayReturn (prepare pol) pol_after ->
        PolyLang.instance_list_semantics pol_after st st' ->
        exists st_src,
          PolyLang.instance_list_semantics pol st st_src /\
          State.eq st' st_src)
    (annotate_correct :
      forall pol_after arg pl st st',
        mayReturn (annotate pol_after arg) (Okk pl) ->
        PolyLang.wf_pprog_general pol_after ->
        ParallelLoop.semantics pl st st' ->
        exists st_src,
          PolyLang.instance_list_semantics pol_after st st_src /\
          State.eq st' st_src) :
  forall pol arg pl st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn
      (BIND pol_after <- prepare pol -; annotate pol_after arg)
      (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st_src,
      PolyLang.instance_list_semantics pol st st_src /\
      State.eq st' st_src.
Proof.
  intros pol arg pl st st' Hwf Hopt Hsem.
  bind_imp_destruct Hopt pol_after Hprepare.
  pose proof (prepare_wf pol pol_after Hwf Hprepare) as Hwf_after.
  destruct
    (annotate_correct pol_after arg pl st st' Hopt Hwf_after Hsem)
    as [st_after [Hsem_after Heq_after]].
  destruct
    (prepare_correct pol pol_after st st_after Hwf Hprepare Hsem_after)
    as [st_src [Hsem_src Heq_src]].
  exists st_src.
  split; [exact Hsem_src|].
  eapply State.eq_trans; [exact Heq_after|exact Heq_src].
Qed.

Local Lemma checked_affine_schedule_wf_general :
  forall pol pol_after,
    PolyLang.wf_pprog_affine pol ->
    mayReturn (CoreOpt.checked_affine_schedule pol) pol_after ->
    PolyLang.wf_pprog_general pol_after.
Proof.
  intros pol pol_after Hwf Hschedule.
  pose proof
    (CoreOpt.scheduler'_preserve_wf
       pol pol_after Hwf pol_after Hschedule eq_refl)
    as Hwf_after.
  eapply PolyLang.wf_pprog_affine_implies_wf_pprog_general; eauto.
Qed.

Local Lemma checked_affine_schedule_correct :
  forall pol pol_after st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (CoreOpt.checked_affine_schedule pol) pol_after ->
    PolyLang.instance_list_semantics pol_after st st' ->
    exists st_src,
      PolyLang.instance_list_semantics pol st st_src /\
      State.eq st' st_src.
Proof.
  intros pol pol_after st st' _ Hschedule Hsem.
  eapply CoreOpt.scheduler'_correct; eauto.
Qed.

Local Lemma iss_only_prepared_from_poly_wf_general :
  forall pol pol_after,
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.iss_only_prepared_from_poly pol) pol_after ->
    PolyLang.wf_pprog_general pol_after.
Proof.
  intros pol pol_after Hwf Hprepare.
  eapply PolyLang.wf_pprog_affine_implies_wf_pprog_general.
  eapply iss_only_prepared_from_poly_wf_affine; eauto.
Qed.

Local Lemma iss_affine_prepared_from_poly_wf_general :
  forall pol pol_after,
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.iss_affine_prepared_from_poly pol) pol_after ->
    PolyLang.wf_pprog_general pol_after.
Proof.
  intros pol pol_after Hwf Hprepare.
  eapply PolyLang.wf_pprog_affine_implies_wf_pprog_general.
  eapply iss_affine_prepared_from_poly_wf_affine; eauto.
Qed.

(** * Prepared parallel routes *)

Lemma parallel_current_identity_prepared_from_poly_correct :
  forall pol d pl st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.parallel_current_identity_prepared_from_poly pol d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol d pl st st' Hwf Hopt Hsem.
  unfold Core.parallel_current_identity_prepared_from_poly in Hopt.
  eapply checked_parallel_current_annotated_codegen_at_correct; eauto.
  eapply PolyLang.wf_pprog_affine_implies_wf_pprog_general; eauto.
Qed.

Lemma parallel_current_affine_prepared_from_poly_correct :
  forall pol d pl st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.parallel_current_affine_prepared_from_poly pol d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol d pl st st' Hwf Hopt Hsem.
  unfold Core.parallel_current_affine_prepared_from_poly in Hopt.
  eapply (checked_annotation_after_preparation_correct
            checked_affine_schedule_wf_general
            checked_affine_schedule_correct
            checked_parallel_current_annotated_codegen_at_correct); eauto.
Qed.

Lemma parallel_current_prepared_from_poly_correct :
  forall pol d pl st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.parallel_current_prepared_from_poly pol d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol d pl st st' Hwf Hopt Hsem.
  unfold Core.parallel_current_prepared_from_poly in Hopt.
  eapply (checked_annotation_after_preparation_correct
            phase_pipeline_opt_prepared_from_poly_no_iss_poly_wf
            phase_pipeline_opt_prepared_from_poly_no_iss_poly_correct
            checked_parallel_current_annotated_codegen_at_correct); eauto.
Qed.

Lemma parallel_current_identity_tiled_prepared_from_poly_correct :
  forall pol d pl st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.parallel_current_identity_tiled_prepared_from_poly pol d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol d pl st st' Hwf Hopt Hsem.
  unfold Core.parallel_current_identity_tiled_prepared_from_poly in Hopt.
  eapply (checked_annotation_after_preparation_correct
            identity_tiling_opt_prepared_from_poly_no_iss_poly_wf
            identity_tiling_opt_prepared_from_poly_no_iss_poly_correct
            checked_parallel_current_annotated_codegen_at_correct); eauto.
Qed.

Lemma parallel_current_identity_tiled_prepared_from_poly_with_iss_correct :
  forall pol d pl st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn
      (Core.parallel_current_identity_tiled_prepared_from_poly_with_iss pol d)
      (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol d pl st st' Hwf Hopt Hsem.
  unfold Core.parallel_current_identity_tiled_prepared_from_poly_with_iss in Hopt.
  eapply (checked_annotation_after_preparation_correct
            identity_tiling_opt_prepared_from_poly_with_iss_poly_wf
            identity_tiling_opt_prepared_from_poly_with_iss_poly_correct
            checked_parallel_current_annotated_codegen_at_correct); eauto.
Qed.

Lemma parallel_current_post_tiling_affine_prepared_from_poly_correct :
  forall pol d pl st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.parallel_current_post_tiling_affine_prepared_from_poly pol d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol d pl st st' Hwf Hopt Hsem.
  unfold Core.parallel_current_post_tiling_affine_prepared_from_poly in Hopt.
  eapply (checked_annotation_after_preparation_correct
            post_tiling_affine_phase_pipeline_opt_prepared_from_poly_no_iss_poly_wf
            post_tiling_affine_phase_pipeline_opt_prepared_from_poly_no_iss_poly_correct
            checked_parallel_current_annotated_codegen_at_correct); eauto.
Qed.

Lemma parallel_current_post_tiling_affine_prepared_from_poly_with_iss_correct :
  forall pol d pl st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn
      (Core.parallel_current_post_tiling_affine_prepared_from_poly_with_iss pol d)
      (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol d pl st st' Hwf Hopt Hsem.
  unfold Core.parallel_current_post_tiling_affine_prepared_from_poly_with_iss in Hopt.
  eapply (checked_annotation_after_preparation_correct
            post_tiling_affine_phase_pipeline_opt_prepared_from_poly_with_iss_poly_wf
            post_tiling_affine_phase_pipeline_opt_prepared_from_poly_with_iss_poly_correct
            checked_parallel_current_annotated_codegen_at_correct); eauto.
Qed.

Lemma parallel_current_identity_prepared_from_poly_with_iss_correct :
  forall pol d pl st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.parallel_current_identity_prepared_from_poly_with_iss pol d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol d pl st st' Hwf Hopt Hsem.
  unfold Core.parallel_current_identity_prepared_from_poly_with_iss in Hopt.
  eapply (checked_annotation_after_preparation_correct
            iss_only_prepared_from_poly_wf_general
            iss_only_prepared_from_poly_correct
            checked_parallel_current_annotated_codegen_at_correct); eauto.
Qed.

Lemma parallel_current_affine_prepared_from_poly_with_iss_correct :
  forall pol d pl st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.parallel_current_affine_prepared_from_poly_with_iss pol d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol d pl st st' Hwf Hopt Hsem.
  unfold Core.parallel_current_affine_prepared_from_poly_with_iss in Hopt.
  eapply (checked_annotation_after_preparation_correct
            iss_affine_prepared_from_poly_wf_general
            iss_affine_prepared_from_poly_correct
            checked_parallel_current_annotated_codegen_at_correct); eauto.
Qed.

Lemma parallel_current_prepared_from_poly_with_iss_correct :
  forall pol d pl st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.parallel_current_prepared_from_poly_with_iss pol d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol d pl st st' Hwf Hopt Hsem.
  unfold Core.parallel_current_prepared_from_poly_with_iss in Hopt.
  eapply (checked_annotation_after_preparation_correct
            phase_pipeline_opt_prepared_from_poly_with_iss_poly_wf
            phase_pipeline_opt_prepared_from_poly_with_iss_poly_correct
            checked_parallel_current_annotated_codegen_at_correct); eauto.
Qed.

Lemma parallel_current_many_identity_prepared_from_poly_correct :
  forall pol dims pl st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.parallel_current_many_identity_prepared_from_poly pol dims) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol dims pl st st' Hwf Hopt Hsem.
  unfold Core.parallel_current_many_identity_prepared_from_poly in Hopt.
  eapply checked_parallel_current_many_annotated_codegen_at_correct; eauto.
  eapply PolyLang.wf_pprog_affine_implies_wf_pprog_general; eauto.
Qed.

Lemma parallel_current_many_affine_prepared_from_poly_correct :
  forall pol dims pl st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.parallel_current_many_affine_prepared_from_poly pol dims) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol dims pl st st' Hwf Hopt Hsem.
  unfold Core.parallel_current_many_affine_prepared_from_poly in Hopt.
  eapply (checked_annotation_after_preparation_correct
            checked_affine_schedule_wf_general
            checked_affine_schedule_correct
            checked_parallel_current_many_annotated_codegen_at_correct); eauto.
Qed.

Lemma parallel_current_many_prepared_from_poly_correct :
  forall pol dims pl st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.parallel_current_many_prepared_from_poly pol dims) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol dims pl st st' Hwf Hopt Hsem.
  unfold Core.parallel_current_many_prepared_from_poly in Hopt.
  eapply (checked_annotation_after_preparation_correct
            phase_pipeline_opt_prepared_from_poly_no_iss_poly_wf
            phase_pipeline_opt_prepared_from_poly_no_iss_poly_correct
            checked_parallel_current_many_annotated_codegen_at_correct); eauto.
Qed.

Lemma parallel_current_many_identity_tiled_prepared_from_poly_correct :
  forall pol dims pl st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.parallel_current_many_identity_tiled_prepared_from_poly pol dims) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol dims pl st st' Hwf Hopt Hsem.
  unfold Core.parallel_current_many_identity_tiled_prepared_from_poly in Hopt.
  eapply (checked_annotation_after_preparation_correct
            identity_tiling_opt_prepared_from_poly_no_iss_poly_wf
            identity_tiling_opt_prepared_from_poly_no_iss_poly_correct
            checked_parallel_current_many_annotated_codegen_at_correct); eauto.
Qed.

Lemma parallel_current_many_identity_tiled_prepared_from_poly_with_iss_correct :
  forall pol dims pl st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn
      (Core.parallel_current_many_identity_tiled_prepared_from_poly_with_iss
         pol dims)
      (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol dims pl st st' Hwf Hopt Hsem.
  unfold Core.parallel_current_many_identity_tiled_prepared_from_poly_with_iss
    in Hopt.
  eapply (checked_annotation_after_preparation_correct
            identity_tiling_opt_prepared_from_poly_with_iss_poly_wf
            identity_tiling_opt_prepared_from_poly_with_iss_poly_correct
            checked_parallel_current_many_annotated_codegen_at_correct); eauto.
Qed.

Lemma parallel_current_many_post_tiling_affine_prepared_from_poly_correct :
  forall pol dims pl st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.parallel_current_many_post_tiling_affine_prepared_from_poly pol dims) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol dims pl st st' Hwf Hopt Hsem.
  unfold Core.parallel_current_many_post_tiling_affine_prepared_from_poly in Hopt.
  eapply (checked_annotation_after_preparation_correct
            post_tiling_affine_phase_pipeline_opt_prepared_from_poly_no_iss_poly_wf
            post_tiling_affine_phase_pipeline_opt_prepared_from_poly_no_iss_poly_correct
            checked_parallel_current_many_annotated_codegen_at_correct); eauto.
Qed.

Lemma parallel_current_many_post_tiling_affine_prepared_from_poly_with_iss_correct :
  forall pol dims pl st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn
      (Core.parallel_current_many_post_tiling_affine_prepared_from_poly_with_iss pol dims)
      (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol dims pl st st' Hwf Hopt Hsem.
  unfold Core.parallel_current_many_post_tiling_affine_prepared_from_poly_with_iss in Hopt.
  eapply (checked_annotation_after_preparation_correct
            post_tiling_affine_phase_pipeline_opt_prepared_from_poly_with_iss_poly_wf
            post_tiling_affine_phase_pipeline_opt_prepared_from_poly_with_iss_poly_correct
            checked_parallel_current_many_annotated_codegen_at_correct); eauto.
Qed.

Lemma parallel_current_many_identity_prepared_from_poly_with_iss_correct :
  forall pol dims pl st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.parallel_current_many_identity_prepared_from_poly_with_iss pol dims) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol dims pl st st' Hwf Hopt Hsem.
  unfold Core.parallel_current_many_identity_prepared_from_poly_with_iss in Hopt.
  eapply (checked_annotation_after_preparation_correct
            iss_only_prepared_from_poly_wf_general
            iss_only_prepared_from_poly_correct
            checked_parallel_current_many_annotated_codegen_at_correct); eauto.
Qed.

Lemma parallel_current_many_affine_prepared_from_poly_with_iss_correct :
  forall pol dims pl st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.parallel_current_many_affine_prepared_from_poly_with_iss pol dims) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol dims pl st st' Hwf Hopt Hsem.
  unfold Core.parallel_current_many_affine_prepared_from_poly_with_iss in Hopt.
  eapply (checked_annotation_after_preparation_correct
            iss_affine_prepared_from_poly_wf_general
            iss_affine_prepared_from_poly_correct
            checked_parallel_current_many_annotated_codegen_at_correct); eauto.
Qed.

Lemma parallel_current_many_prepared_from_poly_with_iss_correct :
  forall pol dims pl st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.parallel_current_many_prepared_from_poly_with_iss pol dims) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol dims pl st st' Hwf Hopt Hsem.
  unfold Core.parallel_current_many_prepared_from_poly_with_iss in Hopt.
  eapply (checked_annotation_after_preparation_correct
            phase_pipeline_opt_prepared_from_poly_with_iss_poly_wf
            phase_pipeline_opt_prepared_from_poly_with_iss_poly_correct
            checked_parallel_current_many_annotated_codegen_at_correct); eauto.
Qed.

(** Result-level routes all cross the same frontend boundary.  Extraction
    produces [pol0], strengthening produces the affine program consumed by a
    prepared route, and the two semantic results are composed after
    unstrengthening.  The local lemma makes that composition explicit while
    route-specific public theorems remain thin specializations. *)
Local Lemma extracted_result_from_prepared_correct
    {A : Type}
    {prepared : PolyLang.t -> A ->
      imp (result Core.ParallelCodegenCore.ParallelLoop.t)}
    (prepared_correct :
      forall pol arg pl st st',
        PolyLang.wf_pprog_affine pol ->
        mayReturn (prepared pol arg) (Okk pl) ->
        ParallelLoop.semantics pl st st' ->
        exists st'',
          PolyLang.instance_list_semantics pol st st'' /\
          State.eq st' st'') :
  forall loop arg pl st st',
    mayReturn
      (BIND pol0 <-
         res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
       let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
       prepared pol arg)
      (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st_src,
      LoopIR.semantics loop st st_src /\ State.eq st' st_src.
Proof.
  intros loop arg pl st st' Hopt Hsem.
  bind_imp_destruct Hopt pol0 Hextract.
  set (pol := CoreOpt.Strengthen.strengthen_pprog pol0) in *.
  pose proof Hextract as Hextract_ok.
  apply res_to_alarm_correct in Hextract_ok.
  pose proof
    (CoreOpt.Strengthen.strengthen_pprog_wf_affine
       pol0
       (CoreOpt.extractor_success_wf_pprog_affine
          loop pol0 Hextract_ok))
    as Hwf_pol.
  destruct
    (prepared_correct pol arg pl st st' Hwf_pol Hopt Hsem)
    as [st_strengthened [Hsem_strengthened Heq_strengthened]].
  eapply CoreOpt.Strengthen.instance_list_semantics_unstrengthen
    in Hsem_strengthened.
  destruct
    (CoreOpt.Extractor.extractor_correct
       loop pol0 st st_strengthened Hextract_ok Hsem_strengthened)
    as [st_src [Hsem_src Heq_src]].
  exists st_src.
  split; [exact Hsem_src|].
  eapply State.eq_trans; [exact Heq_strengthened|exact Heq_src].
Qed.

(** * Extraction and strengthening for parallel results *)

Theorem Opt_parallel_current_identity_result_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_parallel_current_identity_result loop d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_parallel_current_identity_result in Hopt.
  eapply (extracted_result_from_prepared_correct
            parallel_current_identity_prepared_from_poly_correct); eauto.
Qed.

Theorem Opt_parallel_current_identity_tiled_result_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_parallel_current_identity_tiled_result loop d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_parallel_current_identity_tiled_result in Hopt.
  eapply (extracted_result_from_prepared_correct
            parallel_current_identity_tiled_prepared_from_poly_correct); eauto.
Qed.

Theorem Opt_parallel_current_identity_tiled_with_iss_result_correct :
  forall loop d pl st st',
    mayReturn
      (Core.Opt_parallel_current_identity_tiled_with_iss_result loop d)
      (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_parallel_current_identity_tiled_with_iss_result in Hopt.
  eapply (extracted_result_from_prepared_correct
            parallel_current_identity_tiled_prepared_from_poly_with_iss_correct); eauto.
Qed.

Theorem Opt_parallel_current_affine_result_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_parallel_current_affine_result loop d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_parallel_current_affine_result in Hopt.
  eapply (extracted_result_from_prepared_correct
            parallel_current_affine_prepared_from_poly_correct); eauto.
Qed.

Theorem Opt_parallel_current_result_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_parallel_current_result loop d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_parallel_current_result in Hopt.
  eapply (extracted_result_from_prepared_correct
            parallel_current_prepared_from_poly_correct); eauto.
Qed.

Theorem Opt_parallel_current_post_tiling_affine_result_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_parallel_current_post_tiling_affine_result loop d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_parallel_current_post_tiling_affine_result in Hopt.
  eapply (extracted_result_from_prepared_correct
            parallel_current_post_tiling_affine_prepared_from_poly_correct); eauto.
Qed.

Theorem Opt_parallel_current_post_tiling_affine_with_iss_result_correct :
  forall loop d pl st st',
    mayReturn
      (Core.Opt_parallel_current_post_tiling_affine_with_iss_result loop d)
      (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_parallel_current_post_tiling_affine_with_iss_result in Hopt.
  eapply (extracted_result_from_prepared_correct
            parallel_current_post_tiling_affine_prepared_from_poly_with_iss_correct); eauto.
Qed.

Theorem Opt_parallel_current_identity_with_iss_result_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_parallel_current_identity_with_iss_result loop d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_parallel_current_identity_with_iss_result in Hopt.
  eapply (extracted_result_from_prepared_correct
            parallel_current_identity_prepared_from_poly_with_iss_correct); eauto.
Qed.

Theorem Opt_parallel_current_affine_with_iss_result_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_parallel_current_affine_with_iss_result loop d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_parallel_current_affine_with_iss_result in Hopt.
  eapply (extracted_result_from_prepared_correct
            parallel_current_affine_prepared_from_poly_with_iss_correct); eauto.
Qed.

Theorem Opt_parallel_current_with_iss_result_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_parallel_current_with_iss_result loop d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_parallel_current_with_iss_result in Hopt.
  eapply (extracted_result_from_prepared_correct
            parallel_current_prepared_from_poly_with_iss_correct); eauto.
Qed.

Theorem Opt_parallel_current_many_identity_result_correct :
  forall loop dims pl st st',
    mayReturn (Core.Opt_parallel_current_many_identity_result loop dims) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop dims pl st st' Hopt Hsem.
  unfold Core.Opt_parallel_current_many_identity_result in Hopt.
  eapply (extracted_result_from_prepared_correct
            parallel_current_many_identity_prepared_from_poly_correct); eauto.
Qed.

Theorem Opt_parallel_current_many_identity_tiled_result_correct :
  forall loop dims pl st st',
    mayReturn (Core.Opt_parallel_current_many_identity_tiled_result loop dims) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop dims pl st st' Hopt Hsem.
  unfold Core.Opt_parallel_current_many_identity_tiled_result in Hopt.
  eapply (extracted_result_from_prepared_correct
            parallel_current_many_identity_tiled_prepared_from_poly_correct); eauto.
Qed.

Theorem Opt_parallel_current_many_identity_tiled_with_iss_result_correct :
  forall loop dims pl st st',
    mayReturn
      (Core.Opt_parallel_current_many_identity_tiled_with_iss_result loop dims)
      (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop dims pl st st' Hopt Hsem.
  unfold Core.Opt_parallel_current_many_identity_tiled_with_iss_result in Hopt.
  eapply (extracted_result_from_prepared_correct
            parallel_current_many_identity_tiled_prepared_from_poly_with_iss_correct); eauto.
Qed.

Theorem Opt_parallel_current_many_affine_result_correct :
  forall loop dims pl st st',
    mayReturn (Core.Opt_parallel_current_many_affine_result loop dims) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop dims pl st st' Hopt Hsem.
  unfold Core.Opt_parallel_current_many_affine_result in Hopt.
  eapply (extracted_result_from_prepared_correct
            parallel_current_many_affine_prepared_from_poly_correct); eauto.
Qed.

Theorem Opt_parallel_current_many_result_correct :
  forall loop dims pl st st',
    mayReturn (Core.Opt_parallel_current_many_result loop dims) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop dims pl st st' Hopt Hsem.
  unfold Core.Opt_parallel_current_many_result in Hopt.
  eapply (extracted_result_from_prepared_correct
            parallel_current_many_prepared_from_poly_correct); eauto.
Qed.

Theorem Opt_parallel_current_many_post_tiling_affine_result_correct :
  forall loop dims pl st st',
    mayReturn (Core.Opt_parallel_current_many_post_tiling_affine_result loop dims) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop dims pl st st' Hopt Hsem.
  unfold Core.Opt_parallel_current_many_post_tiling_affine_result in Hopt.
  eapply (extracted_result_from_prepared_correct
            parallel_current_many_post_tiling_affine_prepared_from_poly_correct); eauto.
Qed.

Theorem Opt_parallel_current_many_post_tiling_affine_with_iss_result_correct :
  forall loop dims pl st st',
    mayReturn (Core.Opt_parallel_current_many_post_tiling_affine_with_iss_result loop dims) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop dims pl st st' Hopt Hsem.
  unfold Core.Opt_parallel_current_many_post_tiling_affine_with_iss_result in Hopt.
  eapply (extracted_result_from_prepared_correct
            parallel_current_many_post_tiling_affine_prepared_from_poly_with_iss_correct); eauto.
Qed.

Theorem Opt_parallel_current_many_identity_with_iss_result_correct :
  forall loop dims pl st st',
    mayReturn (Core.Opt_parallel_current_many_identity_with_iss_result loop dims) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop dims pl st st' Hopt Hsem.
  unfold Core.Opt_parallel_current_many_identity_with_iss_result in Hopt.
  eapply (extracted_result_from_prepared_correct
            parallel_current_many_identity_prepared_from_poly_with_iss_correct); eauto.
Qed.

Theorem Opt_parallel_current_many_affine_with_iss_result_correct :
  forall loop dims pl st st',
    mayReturn (Core.Opt_parallel_current_many_affine_with_iss_result loop dims) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop dims pl st st' Hopt Hsem.
  unfold Core.Opt_parallel_current_many_affine_with_iss_result in Hopt.
  eapply (extracted_result_from_prepared_correct
            parallel_current_many_affine_prepared_from_poly_with_iss_correct); eauto.
Qed.

Theorem Opt_parallel_current_many_with_iss_result_correct :
  forall loop dims pl st st',
    mayReturn (Core.Opt_parallel_current_many_with_iss_result loop dims) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop dims pl st st' Hopt Hsem.
  unfold Core.Opt_parallel_current_many_with_iss_result in Hopt.
  eapply (extracted_result_from_prepared_correct
            parallel_current_many_prepared_from_poly_with_iss_correct); eauto.
Qed.

(** * Alarm-free parallel entry points *)

Local Lemma alarm_free_from_result_correct
    {A : Type}
    (result_route : LoopIR.t -> A ->
      imp (result Core.ParallelCodegenCore.ParallelLoop.t)) :
  forall loop arg pl st st',
    (forall loop arg pl st st',
      mayReturn (result_route loop arg) (Okk pl) ->
      ParallelLoop.semantics pl st st' ->
      exists st'', LoopIR.semantics loop st st'' /\ State.eq st' st'') ->
    mayReturn
      (BIND res <- result_route loop arg -;
       res_to_alarm Core.parallel_dummy res)
      pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'', LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop arg pl st st' Hresult Hopt Hsem.
  bind_imp_destruct Hopt res Hres.
  pose proof Hopt as Hopt_ok.
  apply res_to_alarm_correct in Hopt_ok.
  subst res.
  eapply Hresult; eauto.
Qed.

Theorem Opt_parallel_current_identity_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_parallel_current_identity loop d) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop arg pl st st2 Hopt Hsem.
  unfold Core.Opt_parallel_current_identity in Hopt.
  eapply (alarm_free_from_result_correct Core.Opt_parallel_current_identity_result); eauto.
  exact Opt_parallel_current_identity_result_correct.
Qed.

Theorem Opt_parallel_current_identity_tiled_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_parallel_current_identity_tiled loop d) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop arg pl st st2 Hopt Hsem.
  unfold Core.Opt_parallel_current_identity_tiled in Hopt.
  eapply (alarm_free_from_result_correct Core.Opt_parallel_current_identity_tiled_result); eauto.
  exact Opt_parallel_current_identity_tiled_result_correct.
Qed.

Theorem Opt_parallel_current_identity_tiled_with_iss_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_parallel_current_identity_tiled_with_iss loop d) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop arg pl st st2 Hopt Hsem.
  unfold Core.Opt_parallel_current_identity_tiled_with_iss in Hopt.
  eapply (alarm_free_from_result_correct Core.Opt_parallel_current_identity_tiled_with_iss_result); eauto.
  exact Opt_parallel_current_identity_tiled_with_iss_result_correct.
Qed.

Theorem Opt_parallel_current_affine_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_parallel_current_affine loop d) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop arg pl st st2 Hopt Hsem.
  unfold Core.Opt_parallel_current_affine in Hopt.
  eapply (alarm_free_from_result_correct Core.Opt_parallel_current_affine_result); eauto.
  exact Opt_parallel_current_affine_result_correct.
Qed.

Theorem Opt_parallel_current_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_parallel_current loop d) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop arg pl st st2 Hopt Hsem.
  unfold Core.Opt_parallel_current in Hopt.
  eapply (alarm_free_from_result_correct Core.Opt_parallel_current_result); eauto.
  exact Opt_parallel_current_result_correct.
Qed.

Theorem Opt_parallel_current_post_tiling_affine_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_parallel_current_post_tiling_affine loop d) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop arg pl st st2 Hopt Hsem.
  unfold Core.Opt_parallel_current_post_tiling_affine in Hopt.
  eapply (alarm_free_from_result_correct Core.Opt_parallel_current_post_tiling_affine_result); eauto.
  exact Opt_parallel_current_post_tiling_affine_result_correct.
Qed.

Theorem Opt_parallel_current_post_tiling_affine_with_iss_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_parallel_current_post_tiling_affine_with_iss loop d) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop arg pl st st2 Hopt Hsem.
  unfold Core.Opt_parallel_current_post_tiling_affine_with_iss in Hopt.
  eapply (alarm_free_from_result_correct Core.Opt_parallel_current_post_tiling_affine_with_iss_result); eauto.
  exact Opt_parallel_current_post_tiling_affine_with_iss_result_correct.
Qed.

Theorem Opt_parallel_current_identity_with_iss_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_parallel_current_identity_with_iss loop d) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop arg pl st st2 Hopt Hsem.
  unfold Core.Opt_parallel_current_identity_with_iss in Hopt.
  eapply (alarm_free_from_result_correct Core.Opt_parallel_current_identity_with_iss_result); eauto.
  exact Opt_parallel_current_identity_with_iss_result_correct.
Qed.

Theorem Opt_parallel_current_affine_with_iss_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_parallel_current_affine_with_iss loop d) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop arg pl st st2 Hopt Hsem.
  unfold Core.Opt_parallel_current_affine_with_iss in Hopt.
  eapply (alarm_free_from_result_correct Core.Opt_parallel_current_affine_with_iss_result); eauto.
  exact Opt_parallel_current_affine_with_iss_result_correct.
Qed.

Theorem Opt_parallel_current_with_iss_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_parallel_current_with_iss loop d) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop arg pl st st2 Hopt Hsem.
  unfold Core.Opt_parallel_current_with_iss in Hopt.
  eapply (alarm_free_from_result_correct Core.Opt_parallel_current_with_iss_result); eauto.
  exact Opt_parallel_current_with_iss_result_correct.
Qed.

Theorem Opt_parallel_current_many_identity_correct :
  forall loop dims pl st st',
    mayReturn (Core.Opt_parallel_current_many_identity loop dims) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop arg pl st st2 Hopt Hsem.
  unfold Core.Opt_parallel_current_many_identity in Hopt.
  eapply (alarm_free_from_result_correct Core.Opt_parallel_current_many_identity_result); eauto.
  exact Opt_parallel_current_many_identity_result_correct.
Qed.

Theorem Opt_parallel_current_many_identity_tiled_correct :
  forall loop dims pl st st',
    mayReturn (Core.Opt_parallel_current_many_identity_tiled loop dims) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop arg pl st st2 Hopt Hsem.
  unfold Core.Opt_parallel_current_many_identity_tiled in Hopt.
  eapply (alarm_free_from_result_correct Core.Opt_parallel_current_many_identity_tiled_result); eauto.
  exact Opt_parallel_current_many_identity_tiled_result_correct.
Qed.

Theorem Opt_parallel_current_many_identity_tiled_with_iss_correct :
  forall loop dims pl st st',
    mayReturn
      (Core.Opt_parallel_current_many_identity_tiled_with_iss loop dims)
      pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop arg pl st st2 Hopt Hsem.
  unfold Core.Opt_parallel_current_many_identity_tiled_with_iss in Hopt.
  eapply (alarm_free_from_result_correct Core.Opt_parallel_current_many_identity_tiled_with_iss_result); eauto.
  exact Opt_parallel_current_many_identity_tiled_with_iss_result_correct.
Qed.

Theorem Opt_parallel_current_many_affine_correct :
  forall loop dims pl st st',
    mayReturn (Core.Opt_parallel_current_many_affine loop dims) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop arg pl st st2 Hopt Hsem.
  unfold Core.Opt_parallel_current_many_affine in Hopt.
  eapply (alarm_free_from_result_correct Core.Opt_parallel_current_many_affine_result); eauto.
  exact Opt_parallel_current_many_affine_result_correct.
Qed.

Theorem Opt_parallel_current_many_correct :
  forall loop dims pl st st',
    mayReturn (Core.Opt_parallel_current_many loop dims) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop arg pl st st2 Hopt Hsem.
  unfold Core.Opt_parallel_current_many in Hopt.
  eapply (alarm_free_from_result_correct Core.Opt_parallel_current_many_result); eauto.
  exact Opt_parallel_current_many_result_correct.
Qed.

Theorem Opt_parallel_current_many_post_tiling_affine_correct :
  forall loop dims pl st st',
    mayReturn (Core.Opt_parallel_current_many_post_tiling_affine loop dims) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop arg pl st st2 Hopt Hsem.
  unfold Core.Opt_parallel_current_many_post_tiling_affine in Hopt.
  eapply (alarm_free_from_result_correct Core.Opt_parallel_current_many_post_tiling_affine_result); eauto.
  exact Opt_parallel_current_many_post_tiling_affine_result_correct.
Qed.

Theorem Opt_parallel_current_many_post_tiling_affine_with_iss_correct :
  forall loop dims pl st st',
    mayReturn (Core.Opt_parallel_current_many_post_tiling_affine_with_iss loop dims) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop arg pl st st2 Hopt Hsem.
  unfold Core.Opt_parallel_current_many_post_tiling_affine_with_iss in Hopt.
  eapply (alarm_free_from_result_correct Core.Opt_parallel_current_many_post_tiling_affine_with_iss_result); eauto.
  exact Opt_parallel_current_many_post_tiling_affine_with_iss_result_correct.
Qed.

Theorem Opt_parallel_current_many_identity_with_iss_correct :
  forall loop dims pl st st',
    mayReturn (Core.Opt_parallel_current_many_identity_with_iss loop dims) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop arg pl st st2 Hopt Hsem.
  unfold Core.Opt_parallel_current_many_identity_with_iss in Hopt.
  eapply (alarm_free_from_result_correct Core.Opt_parallel_current_many_identity_with_iss_result); eauto.
  exact Opt_parallel_current_many_identity_with_iss_result_correct.
Qed.

Theorem Opt_parallel_current_many_affine_with_iss_correct :
  forall loop dims pl st st',
    mayReturn (Core.Opt_parallel_current_many_affine_with_iss loop dims) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop arg pl st st2 Hopt Hsem.
  unfold Core.Opt_parallel_current_many_affine_with_iss in Hopt.
  eapply (alarm_free_from_result_correct Core.Opt_parallel_current_many_affine_with_iss_result); eauto.
  exact Opt_parallel_current_many_affine_with_iss_result_correct.
Qed.

Theorem Opt_parallel_current_many_with_iss_correct :
  forall loop dims pl st st',
    mayReturn (Core.Opt_parallel_current_many_with_iss loop dims) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop arg pl st st2 Hopt Hsem.
  unfold Core.Opt_parallel_current_many_with_iss in Hopt.
  eapply (alarm_free_from_result_correct Core.Opt_parallel_current_many_with_iss_result); eauto.
  exact Opt_parallel_current_many_with_iss_result_correct.
Qed.

(** * Vector routes *)

Lemma vector_current_identity_prepared_from_poly_correct :
  forall pol d pl st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.vector_current_identity_prepared_from_poly pol d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol d pl st st' Hwf Hopt Hsem.
  unfold Core.vector_current_identity_prepared_from_poly in Hopt.
  eapply checked_vector_current_annotated_codegen_at_correct; eauto.
  eapply PolyLang.wf_pprog_affine_implies_wf_pprog_general; eauto.
Qed.

Lemma vector_current_affine_prepared_from_poly_correct :
  forall pol d pl st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.vector_current_affine_prepared_from_poly pol d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol d pl st st' Hwf Hopt Hsem.
  unfold Core.vector_current_affine_prepared_from_poly in Hopt.
  eapply (checked_annotation_after_preparation_correct
            checked_affine_schedule_wf_general
            checked_affine_schedule_correct
            checked_vector_current_annotated_codegen_at_correct); eauto.
Qed.

Lemma vector_current_prepared_from_poly_correct :
  forall pol d pl st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.vector_current_prepared_from_poly pol d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol d pl st st' Hwf Hopt Hsem.
  unfold Core.vector_current_prepared_from_poly in Hopt.
  eapply (checked_annotation_after_preparation_correct
            phase_pipeline_opt_prepared_from_poly_no_iss_poly_wf
            phase_pipeline_opt_prepared_from_poly_no_iss_poly_correct
            checked_vector_current_annotated_codegen_at_correct); eauto.
Qed.

Lemma vector_current_identity_tiled_prepared_from_poly_correct :
  forall pol d pl st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn
      (Core.vector_current_identity_tiled_prepared_from_poly pol d)
      (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol d pl st st' Hwf Hopt Hsem.
  unfold Core.vector_current_identity_tiled_prepared_from_poly in Hopt.
  eapply (checked_annotation_after_preparation_correct
            identity_tiling_opt_prepared_from_poly_no_iss_poly_wf
            identity_tiling_opt_prepared_from_poly_no_iss_poly_correct
            checked_vector_current_annotated_codegen_at_correct); eauto.
Qed.

Lemma vector_current_identity_tiled_prepared_from_poly_with_iss_correct :
  forall pol d pl st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn
      (Core.vector_current_identity_tiled_prepared_from_poly_with_iss pol d)
      (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol d pl st st' Hwf Hopt Hsem.
  unfold Core.vector_current_identity_tiled_prepared_from_poly_with_iss in Hopt.
  eapply (checked_annotation_after_preparation_correct
            identity_tiling_opt_prepared_from_poly_with_iss_poly_wf
            identity_tiling_opt_prepared_from_poly_with_iss_poly_correct
            checked_vector_current_annotated_codegen_at_correct); eauto.
Qed.

Lemma vector_current_post_tiling_affine_prepared_from_poly_correct :
  forall pol d pl st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.vector_current_post_tiling_affine_prepared_from_poly pol d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol d pl st st' Hwf Hopt Hsem.
  unfold Core.vector_current_post_tiling_affine_prepared_from_poly in Hopt.
  eapply (checked_annotation_after_preparation_correct
            post_tiling_affine_phase_pipeline_opt_prepared_from_poly_no_iss_poly_wf
            post_tiling_affine_phase_pipeline_opt_prepared_from_poly_no_iss_poly_correct
            checked_vector_current_annotated_codegen_at_correct); eauto.
Qed.

Lemma vector_current_post_tiling_affine_prepared_from_poly_with_iss_correct :
  forall pol d pl st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn
      (Core.vector_current_post_tiling_affine_prepared_from_poly_with_iss pol d)
      (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol d pl st st' Hwf Hopt Hsem.
  unfold Core.vector_current_post_tiling_affine_prepared_from_poly_with_iss in Hopt.
  eapply (checked_annotation_after_preparation_correct
            post_tiling_affine_phase_pipeline_opt_prepared_from_poly_with_iss_poly_wf
            post_tiling_affine_phase_pipeline_opt_prepared_from_poly_with_iss_poly_correct
            checked_vector_current_annotated_codegen_at_correct); eauto.
Qed.

Lemma vector_current_identity_prepared_from_poly_with_iss_correct :
  forall pol d pl st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn
      (Core.vector_current_identity_prepared_from_poly_with_iss pol d)
      (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol d pl st st' Hwf Hopt Hsem.
  unfold Core.vector_current_identity_prepared_from_poly_with_iss in Hopt.
  eapply (checked_annotation_after_preparation_correct
            iss_only_prepared_from_poly_wf_general
            iss_only_prepared_from_poly_correct
            checked_vector_current_annotated_codegen_at_correct); eauto.
Qed.

Lemma vector_current_affine_prepared_from_poly_with_iss_correct :
  forall pol d pl st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn
      (Core.vector_current_affine_prepared_from_poly_with_iss pol d)
      (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol d pl st st' Hwf Hopt Hsem.
  unfold Core.vector_current_affine_prepared_from_poly_with_iss in Hopt.
  eapply (checked_annotation_after_preparation_correct
            iss_affine_prepared_from_poly_wf_general
            iss_affine_prepared_from_poly_correct
            checked_vector_current_annotated_codegen_at_correct); eauto.
Qed.

Lemma vector_current_prepared_from_poly_with_iss_correct :
  forall pol d pl st st',
    PolyLang.wf_pprog_affine pol ->
    mayReturn (Core.vector_current_prepared_from_poly_with_iss pol d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol d pl st st' Hwf Hopt Hsem.
  unfold Core.vector_current_prepared_from_poly_with_iss in Hopt.
  eapply (checked_annotation_after_preparation_correct
            phase_pipeline_opt_prepared_from_poly_with_iss_poly_wf
            phase_pipeline_opt_prepared_from_poly_with_iss_poly_correct
            checked_vector_current_annotated_codegen_at_correct); eauto.
Qed.

Lemma opt_vector_current_result_from_prepared_correct :
  forall
    (prepared : PolyLang.t -> nat ->
      imp (result Core.ParallelCodegenCore.ParallelLoop.t))
    loop d pl st st',
    (forall pol d pl st st',
      PolyLang.wf_pprog_affine pol ->
      mayReturn (prepared pol d) (Okk pl) ->
      ParallelLoop.semantics pl st st' ->
      exists st'',
        PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st'') ->
    mayReturn
      (BIND pol0 <-
         res_to_alarm PolyLang.dummy (CoreOpt.Extractor.extractor loop) -;
       let pol := CoreOpt.Strengthen.strengthen_pprog pol0 in
       prepared pol d)
      (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'', LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros prepared loop d pl st st' Hprepared Hopt Hsem.
  eapply (extracted_result_from_prepared_correct Hprepared); eauto.
Qed.

Theorem Opt_vector_current_identity_result_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_vector_current_identity_result loop d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'', LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_vector_current_identity_result in Hopt.
  eapply opt_vector_current_result_from_prepared_correct; eauto.
  exact vector_current_identity_prepared_from_poly_correct.
Qed.

Theorem Opt_vector_current_identity_tiled_result_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_vector_current_identity_tiled_result loop d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'', LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_vector_current_identity_tiled_result in Hopt.
  eapply opt_vector_current_result_from_prepared_correct; eauto.
  exact vector_current_identity_tiled_prepared_from_poly_correct.
Qed.

Theorem Opt_vector_current_identity_tiled_with_iss_result_correct :
  forall loop d pl st st',
    mayReturn
      (Core.Opt_vector_current_identity_tiled_with_iss_result loop d)
      (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'', LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_vector_current_identity_tiled_with_iss_result in Hopt.
  eapply opt_vector_current_result_from_prepared_correct; eauto.
  exact vector_current_identity_tiled_prepared_from_poly_with_iss_correct.
Qed.

Theorem Opt_vector_current_affine_result_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_vector_current_affine_result loop d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'', LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_vector_current_affine_result in Hopt.
  eapply opt_vector_current_result_from_prepared_correct; eauto.
  exact vector_current_affine_prepared_from_poly_correct.
Qed.

Theorem Opt_vector_current_result_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_vector_current_result loop d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'', LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_vector_current_result in Hopt.
  eapply opt_vector_current_result_from_prepared_correct; eauto.
  exact vector_current_prepared_from_poly_correct.
Qed.

Theorem Opt_vector_current_post_tiling_affine_result_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_vector_current_post_tiling_affine_result loop d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'', LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_vector_current_post_tiling_affine_result in Hopt.
  eapply opt_vector_current_result_from_prepared_correct; eauto.
  exact vector_current_post_tiling_affine_prepared_from_poly_correct.
Qed.

Theorem Opt_vector_current_post_tiling_affine_with_iss_result_correct :
  forall loop d pl st st',
    mayReturn
      (Core.Opt_vector_current_post_tiling_affine_with_iss_result loop d)
      (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'', LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_vector_current_post_tiling_affine_with_iss_result in Hopt.
  eapply opt_vector_current_result_from_prepared_correct; eauto.
  exact vector_current_post_tiling_affine_prepared_from_poly_with_iss_correct.
Qed.

Theorem Opt_vector_current_identity_with_iss_result_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_vector_current_identity_with_iss_result loop d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'', LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_vector_current_identity_with_iss_result in Hopt.
  eapply opt_vector_current_result_from_prepared_correct; eauto.
  exact vector_current_identity_prepared_from_poly_with_iss_correct.
Qed.

Theorem Opt_vector_current_affine_with_iss_result_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_vector_current_affine_with_iss_result loop d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'', LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_vector_current_affine_with_iss_result in Hopt.
  eapply opt_vector_current_result_from_prepared_correct; eauto.
  exact vector_current_affine_prepared_from_poly_with_iss_correct.
Qed.

Theorem Opt_vector_current_with_iss_result_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_vector_current_with_iss_result loop d) (Okk pl) ->
    ParallelLoop.semantics pl st st' ->
    exists st'', LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_vector_current_with_iss_result in Hopt.
  eapply opt_vector_current_result_from_prepared_correct; eauto.
  exact vector_current_prepared_from_poly_with_iss_correct.
Qed.

Lemma opt_vector_current_from_result_correct :
  forall
    (result_route : LoopIR.t -> nat ->
      imp (result Core.ParallelCodegenCore.ParallelLoop.t))
    loop d pl st st',
    (forall loop d pl st st',
      mayReturn (result_route loop d) (Okk pl) ->
      ParallelLoop.semantics pl st st' ->
      exists st'', LoopIR.semantics loop st st'' /\ State.eq st' st'') ->
    mayReturn
      (BIND res <- result_route loop d -;
       res_to_alarm Core.parallel_dummy res)
      pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'', LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros result_route loop d pl st st' Hresult Hopt Hsem.
  eapply (alarm_free_from_result_correct result_route); eauto.
Qed.

Theorem Opt_vector_current_identity_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_vector_current_identity loop d) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'', LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_vector_current_identity in Hopt.
  eapply opt_vector_current_from_result_correct; eauto.
  exact Opt_vector_current_identity_result_correct.
Qed.

Theorem Opt_vector_current_identity_tiled_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_vector_current_identity_tiled loop d) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'', LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_vector_current_identity_tiled in Hopt.
  eapply opt_vector_current_from_result_correct; eauto.
  exact Opt_vector_current_identity_tiled_result_correct.
Qed.

Theorem Opt_vector_current_identity_tiled_with_iss_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_vector_current_identity_tiled_with_iss loop d) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'', LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_vector_current_identity_tiled_with_iss in Hopt.
  eapply opt_vector_current_from_result_correct; eauto.
  exact Opt_vector_current_identity_tiled_with_iss_result_correct.
Qed.

Theorem Opt_vector_current_affine_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_vector_current_affine loop d) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'', LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_vector_current_affine in Hopt.
  eapply opt_vector_current_from_result_correct; eauto.
  exact Opt_vector_current_affine_result_correct.
Qed.

Theorem Opt_vector_current_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_vector_current loop d) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'', LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_vector_current in Hopt.
  eapply opt_vector_current_from_result_correct; eauto.
  exact Opt_vector_current_result_correct.
Qed.

Theorem Opt_vector_current_post_tiling_affine_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_vector_current_post_tiling_affine loop d) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'', LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_vector_current_post_tiling_affine in Hopt.
  eapply opt_vector_current_from_result_correct; eauto.
  exact Opt_vector_current_post_tiling_affine_result_correct.
Qed.

Theorem Opt_vector_current_post_tiling_affine_with_iss_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_vector_current_post_tiling_affine_with_iss loop d) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'', LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_vector_current_post_tiling_affine_with_iss in Hopt.
  eapply opt_vector_current_from_result_correct; eauto.
  exact Opt_vector_current_post_tiling_affine_with_iss_result_correct.
Qed.

Theorem Opt_vector_current_identity_with_iss_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_vector_current_identity_with_iss loop d) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'', LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_vector_current_identity_with_iss in Hopt.
  eapply opt_vector_current_from_result_correct; eauto.
  exact Opt_vector_current_identity_with_iss_result_correct.
Qed.

Theorem Opt_vector_current_affine_with_iss_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_vector_current_affine_with_iss loop d) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'', LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_vector_current_affine_with_iss in Hopt.
  eapply opt_vector_current_from_result_correct; eauto.
  exact Opt_vector_current_affine_with_iss_result_correct.
Qed.

Theorem Opt_vector_current_with_iss_correct :
  forall loop d pl st st',
    mayReturn (Core.Opt_vector_current_with_iss loop d) pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'', LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop d pl st st' Hopt Hsem.
  unfold Core.Opt_vector_current_with_iss in Hopt.
  eapply opt_vector_current_from_result_correct; eauto.
  exact Opt_vector_current_with_iss_result_correct.
Qed.

End ParallelPolOptCorrect.

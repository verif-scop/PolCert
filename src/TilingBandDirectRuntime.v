Require Import Bool.
Require Import List.
Require Import Lia.
Import ListNotations.

Require Import PolIRs.
Require Import TilingWitness.
Require Import TilingBandScheduleValidator.
Require Import TilingBandMixedSecondValidator.
Require Import TilingBandPhaseScalarValidator.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Module Type TILING_BAND_DIRECT_RUNTIME_API (P: POLIRS).

Inductive tiling_band_validation_route : Type :=
| DirectBandAccepted
| GeneralScheduleAccepted
| Rejected.

Definition tiling_band_validation_route_acceptsb
    (route: tiling_band_validation_route) : bool :=
  match route with
  | DirectBandAccepted => true
  | GeneralScheduleAccepted => true
  | Rejected => false
  end.

Parameter checked_tiling_schedule_sourceb_first_runtime_validate_route :
  P.PolyLang.t ->
  P.PolyLang.t ->
  list statement_tiling_witness ->
  imp tiling_band_validation_route.

Parameter checked_tiling_schedule_sourceb_first_runtime_validate_route_correct :
  forall before after ws st1 st2 route,
    P.PolyLang.wf_pprog_affine before ->
    P.PolyLang.wf_pprog_general after ->
    mayReturn
      (checked_tiling_schedule_sourceb_first_runtime_validate_route
         before after ws)
      route ->
    tiling_band_validation_route_acceptsb route = true ->
    P.PolyLang.instance_list_semantics after st1 st2 ->
    exists st2',
      P.PolyLang.instance_list_semantics before st1 st2' /\
      P.State.eq st2 st2'.

End TILING_BAND_DIRECT_RUNTIME_API.

Module TilingBandDirectRuntime (PolIRs: POLIRS).

Module PhaseScalar := TilingBandPhaseScalarValidator PolIRs.
Module Mixed := PhaseScalar.Mixed.
Module Legacy := Mixed.Core.
Module PolyLang := PolIRs.PolyLang.
Module State := PolIRs.State.

Open Scope impure_scope.

(** * Proof map

    Specialized layout checks provide a semantic band certificate and a
    layout-specific reversal bridge.  When these sufficient conditions fail,
    the generic tiling validator checks the actual old and new schedules over
    the witnessed domain correspondence.  The two successful proof paths have
    distinct route tags; either check may reject, and alarms remain failures. *)

Inductive tiling_band_validation_route : Type :=
| DirectBandAccepted
| GeneralScheduleAccepted
| Rejected.

Definition tiling_band_validation_route_acceptsb
    (route: tiling_band_validation_route) : bool :=
  match route with
  | DirectBandAccepted => true
  | GeneralScheduleAccepted => true
  | Rejected => false
  end.

(** The direct source-first layer recognizes ordinary common-band strip mining
    with target-side trailing-zero padding, and uniform grouped or interleaved
    second-level schedules with either symmetric trailing-zero equivalence or
    program-wide strict-zero-row erasure. *)
Definition checked_tiling_sourceb_first_direct_band_check
    (before after: Legacy.Tiling.PL.t)
    (ws: list statement_tiling_witness) : imp bool :=
  let '(before_pis, before_ctxt, _) := before in
  let '(after_pis, _, _) := after in
  if Legacy.TilingCheck.check_pprog_tiling_sourceb before after ws then
    let ordinary_check :=
      if Legacy.check_pprog_tiling_schedule_stripminedb before after ws then
        match Legacy.infer_pprog_tiling_bands before ws with
        | Some bands =>
            Legacy.check_pprog_pluto_permutable_tiling_bands_direct
              before after ws bands
        | None => pure false
        end
      else pure false in
    BIND ordinary_ok <- ordinary_check -;
    if ordinary_ok then pure true
    else
      match Legacy.check_pprog_second_level_schedule_directb before after ws with
      | Some (bands, _, _) =>
          Legacy.check_pinstr_list_pluto_componentwise_permutable_bands_direct
            (List.length before_ctxt) before_pis after_pis ws bands
      | None => pure false
      end
  else pure false.

(** The complete direct-only candidate checker.  Each branch independently
    validates the source/witness boundary and proves a permutable-band
    condition for the layout it recognizes. *)
Definition checked_tiling_sourceb_complete_direct_band_check
    (before after: Legacy.Tiling.PL.t)
    (ws: list statement_tiling_witness) : imp bool :=
  BIND common_ok <-
    checked_tiling_sourceb_first_direct_band_check before after ws -;
  if common_ok then pure true
  else
    (* Rejecting a non-scalar-aware shape is a cheap structural check.  Trying
       this route first avoids repeated permutability queries for scalar-aware
       candidates. *)
    BIND scalar_aware_ok <-
      Legacy.checked_tiling_sourceb_scalar_aware_direct before after ws -;
    if scalar_aware_ok then pure true
    else
      BIND phase_semantic_ok <-
        Legacy.checked_tiling_sourceb_phase_semantic_extended_direct
          before after ws -;
      if phase_semantic_ok then pure true
      else
        BIND phase_ordinary_ok <-
          Mixed.check_pprog_phase_separated_ordinary_direct before after ws -;
        if phase_ordinary_ok then pure true
        else
          BIND phase_scalar_ok <-
            PhaseScalar.checked_tiling_sourceb_phase_scalar_extended_direct
              before after ws -;
          if phase_scalar_ok then pure true
          else
            BIND semantic_ok <-
              Legacy.checked_tiling_sourceb_semantic_band_direct
                before after ws -;
            if semantic_ok then pure true
            else Mixed.check_pprog_mixed_second_level_direct before after ws.

Lemma checked_tiling_sourceb_first_direct_band_check_sourceb_true :
  forall before after ws,
    mayReturn
      (checked_tiling_sourceb_first_direct_band_check before after ws)
      true ->
    Legacy.TilingCheck.check_pprog_tiling_sourceb before after ws = true.
Proof.
  intros [[before_pis before_ctxt] before_vars]
         [[after_pis after_ctxt] after_vars] ws Hcheck.
  unfold checked_tiling_sourceb_first_direct_band_check in Hcheck.
  cbn beta iota zeta in Hcheck.
  destruct
    (Legacy.TilingCheck.check_pprog_tiling_sourceb
       (before_pis, before_ctxt, before_vars)
       (after_pis, after_ctxt, after_vars) ws)
    eqn:Hsource.
  - reflexivity.
  - apply mayReturn_pure in Hcheck.
    discriminate.
Qed.

Lemma checked_tiling_sourceb_complete_direct_band_check_sourceb_true :
  forall before after ws,
    mayReturn
      (checked_tiling_sourceb_complete_direct_band_check before after ws)
      true ->
    Legacy.TilingCheck.check_pprog_tiling_sourceb before after ws = true.
Proof.
  intros before after ws Hcheck.
  unfold checked_tiling_sourceb_complete_direct_band_check in Hcheck.
  bind_imp_destruct Hcheck common_ok Hcommon.
  destruct common_ok.
  - eapply checked_tiling_sourceb_first_direct_band_check_sourceb_true.
    exact Hcommon.
  - bind_imp_destruct Hcheck scalar_aware_ok Hscalar_aware.
    destruct scalar_aware_ok.
    + destruct
        (Legacy.checked_tiling_sourceb_scalar_aware_direct_true_inv
           before after ws Hscalar_aware)
        as [layout [Hsource _]].
      exact Hsource.
    + bind_imp_destruct Hcheck phase_semantic_ok Hphase_semantic.
      destruct phase_semantic_ok.
      * eapply
          Legacy.checked_tiling_sourceb_phase_semantic_extended_direct_sourceb_true.
        exact Hphase_semantic.
      * bind_imp_destruct Hcheck phase_ordinary_ok Hphase_ordinary.
        destruct phase_ordinary_ok.
        -- destruct before as [[before_pis before_ctxt] before_vars].
           destruct after as [[after_pis after_ctxt] after_vars].
           destruct
             (Mixed.check_pprog_phase_separated_ordinary_direct_true_inv
                before_pis before_ctxt before_vars
                after_pis after_ctxt after_vars ws Hphase_ordinary)
             as [bands [Hsource _]].
           exact Hsource.
        -- bind_imp_destruct Hcheck phase_scalar_ok Hphase_scalar.
           destruct phase_scalar_ok.
           ++ eapply PhaseScalar.checked_tiling_sourceb_phase_scalar_extended_direct_sourceb_true.
              exact Hphase_scalar.
           ++ bind_imp_destruct Hcheck semantic_ok Hsemantic.
              destruct semantic_ok.
              ** destruct
                   (Legacy.checked_tiling_sourceb_semantic_band_direct_true_inv
                      before after ws Hsemantic)
                   as [lifted_rows [Hshape _]].
                 inversion Hshape; assumption.
              ** destruct before as [[before_pis before_ctxt] before_vars].
                 destruct after as [[after_pis after_ctxt] after_vars].
                 destruct
                   (Mixed.check_pprog_mixed_second_level_direct_true_inv
                      before_pis before_ctxt before_vars
                      after_pis after_ctxt after_vars ws Hcheck)
                   as [bands [recipes [Hsource _]]].
                 exact Hsource.
Qed.

Lemma checked_second_level_direct_band_check_correct :
  forall layout before_pis before_ctxt before_vars after_pis ws
         bands recipes st1 st2,
    Forall
      (Legacy.Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    Forall
      (Legacy.Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      after_pis ->
    Legacy.TilingCheck.check_pprog_tiling_sourceb
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars) ws = true ->
    Legacy.infer_pinstr_list_second_level_bands before_pis ws =
      Some (bands, recipes) ->
    Legacy.check_pinstr_list_second_level_schedule_directb
      layout (List.length before_ctxt) before_pis after_pis bands = true ->
    Legacy.common_second_level_recipe_sizes recipes ->
    Legacy.common_band_start bands ->
    mayReturn
      (Legacy.check_pinstr_list_pluto_componentwise_permutable_bands_direct
         (List.length before_ctxt) before_pis after_pis ws bands)
      true ->
    Legacy.Tiling.PL.instance_list_semantics
      (after_pis, before_ctxt, before_vars) st1 st2 ->
    exists st2',
      Legacy.Tiling.PL.instance_list_semantics
        (before_pis, before_ctxt, before_vars) st1 st2' /\
      State.eq st2 st2'.
Proof.
  intros layout before_pis before_ctxt before_vars after_pis ws
         bands recipes st1 st2 Hwf_before Hwf_after Hsource Hinfer
         Hsched Hrecipe_sizes Hcommon_start Hcomponent_check Hsem.
  pose proof
    (Legacy.TilingCheck.check_pprog_tiling_sourceb_sound
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars) ws Hsource)
    as [Hprog [Hbefore_ids [Hwf_ws [Hsizes_ws Hdepths]]]].
  assert (Hwits :
    Forall2 Legacy.Tiling.after_matches_tiling_witness after_pis ws).
  {
    eapply
      (Legacy.tiling_rel_pprog_structure_source_after_matches
         before_pis before_ctxt before_vars
         after_pis before_ctxt before_vars ws); eauto.
  }
  eapply
    (Legacy.tiling_sourceb_validate_correct_with_reordering
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars)
       ws bands st1 st2); [exact Hsource| |exact Hsem].
  simpl.
  intros envv Hlen_env.
  assert (Hcomposed_wf :
    Forall
      (Legacy.Tiling.PL.wf_pinstr_ext_tiling before_ctxt)
      (Legacy.Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length before_ctxt) before_pis after_pis ws)).
  {
    eapply Legacy.compose_tiling_pinstrs_ext_from_after_wf_tiling; eauto.
  }
  assert (Hcomponentwise :
    Legacy.pprog_pluto_componentwise_permutable_bands
      envv before_pis after_pis ws bands).
  {
    eapply
      (Legacy.check_pinstr_list_pluto_componentwise_permutable_bands_direct_sound
         before_ctxt envv before_pis after_pis ws bands); eauto.
  }
  assert (Hsched_lex :
    Legacy.second_level_schedule_layout_lex_equivalent
      layout (List.length before_ctxt) before_pis after_pis bands).
  {
    eapply Legacy.check_pinstr_list_second_level_schedule_directb_sound.
    exact Hsched.
  }
  eapply
    (Legacy.pprog_pluto_componentwise_permutable_bands_implies_reordering_safe_if_local_bridge
       envv before_pis after_pis ws bands); [exact Hcomponentwise|].
  intros flat ip1 ip2 Hflat Hin1 Hin2 Hold Hnew.
  eapply
    (Legacy.second_level_local_reversal_bridge_by_layout_wf_with_env_len
       layout before_pis before_ctxt before_vars
       after_pis ws bands recipes envv); eauto.
Qed.

Lemma checked_tiling_sourceb_first_direct_band_check_correct :
  forall before_pis before_ctxt before_vars after_pis ws st1 st2,
    Forall
      (Legacy.Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    Forall
      (Legacy.Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      after_pis ->
    mayReturn
      (checked_tiling_sourceb_first_direct_band_check
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars)
         ws)
      true ->
    Legacy.Tiling.PL.instance_list_semantics
      (after_pis, before_ctxt, before_vars) st1 st2 ->
    exists st2',
      Legacy.Tiling.PL.instance_list_semantics
        (before_pis, before_ctxt, before_vars) st1 st2' /\
      State.eq st2 st2'.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws st1 st2
         Hwf_before Hwf_after Hcheck Hsem.
  unfold checked_tiling_sourceb_first_direct_band_check in Hcheck.
  destruct
    (Legacy.TilingCheck.check_pprog_tiling_sourceb
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars) ws)
    eqn:Hsource.
  2:{ apply mayReturn_pure in Hcheck. discriminate. }
  cbn beta iota zeta in Hcheck.
  bind_imp_destruct Hcheck ordinary_ok Hordinary.
  destruct ordinary_ok.
  - apply mayReturn_pure in Hcheck.
    destruct
      (Legacy.check_pprog_tiling_schedule_stripminedb
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars) ws)
      eqn:Hschedule.
    2:{ apply mayReturn_pure in Hordinary. discriminate. }
    destruct
      (Legacy.infer_pprog_tiling_bands
         (before_pis, before_ctxt, before_vars) ws)
      as [bands|] eqn:Hinfer.
    2:{ apply mayReturn_pure in Hordinary. discriminate. }
    simpl in Hordinary.
    pose proof
      (Legacy.TilingCheck.check_pprog_tiling_sourceb_sound
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars) ws Hsource)
      as [Hprog [Hbefore_ids [Hwf_ws [Hsizes_ws Hdepths]]]].
    assert (Hwits :
      Forall2 Legacy.Tiling.after_matches_tiling_witness after_pis ws).
    {
      eapply
        (Legacy.tiling_rel_pprog_structure_source_after_matches
           before_pis before_ctxt before_vars
           after_pis before_ctxt before_vars ws); eauto.
    }
    destruct
      (Legacy.check_pprog_tiling_schedule_stripminedb_sound_flat
         before_pis before_ctxt before_vars
         after_pis before_ctxt before_vars ws Hschedule)
      as [bands' [Hinfer' [Hbands [_ _]]]].
    unfold Legacy.infer_pprog_tiling_bands in Hinfer.
    simpl in Hinfer.
    rewrite Hinfer in Hinfer'.
    inversion Hinfer'; subst bands'; clear Hinfer'.
    eapply
      (Legacy.tiling_sourceb_validate_correct_with_reordering
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars)
         ws bands st1 st2); [exact Hsource| |exact Hsem].
    simpl.
    intros envv Hlen_env.
    destruct
      (Legacy.check_pprog_pluto_permutable_tiling_bands_direct_sound_with_env_len
         before_pis before_ctxt before_vars after_pis ws bands envv
         Hlen_env Hinfer Hwf_before Hwf_after Hdepths Hwits Hordinary)
      as [Hstrong Harity].
    eapply
      (Legacy.pprog_pluto_permutable_tiling_bands_strong_implies_reordering_safe_wf_with_env_len
         before_pis before_ctxt before_vars after_pis ws bands envv); eauto.
  - destruct
      (Legacy.check_pprog_second_level_schedule_directb
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars) ws)
      as [shape|] eqn:Hshape.
    2:{ apply mayReturn_pure in Hcheck. discriminate. }
    destruct shape as [[bands recipes] layout].
    simpl in Hcheck.
    destruct
      (Legacy.check_pprog_second_level_schedule_directb_sound
         before_pis before_ctxt before_vars
         after_pis before_ctxt before_vars ws bands recipes layout Hshape)
      as [Hinfer [Hsched [Hrecipe_sizes Hcommon_start]]].
    eapply
      (checked_second_level_direct_band_check_correct
         layout before_pis before_ctxt before_vars
         after_pis ws bands recipes st1 st2); eauto.
Qed.

Lemma checked_tiling_sourceb_complete_direct_band_check_correct :
  forall before_pis before_ctxt before_vars after_pis ws st1 st2,
    Forall
      (Legacy.Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    Forall
      (Legacy.Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      after_pis ->
    mayReturn
      (checked_tiling_sourceb_complete_direct_band_check
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars)
         ws)
      true ->
    Legacy.Tiling.PL.instance_list_semantics
      (after_pis, before_ctxt, before_vars) st1 st2 ->
    exists st2',
      Legacy.Tiling.PL.instance_list_semantics
        (before_pis, before_ctxt, before_vars) st1 st2' /\
      State.eq st2 st2'.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws st1 st2
         Hwf_before Hwf_after Hcheck Hsem.
  unfold checked_tiling_sourceb_complete_direct_band_check in Hcheck.
  bind_imp_destruct Hcheck common_ok Hcommon.
  destruct common_ok.
  - eapply checked_tiling_sourceb_first_direct_band_check_correct; eauto.
  - bind_imp_destruct Hcheck scalar_aware_ok Hscalar_aware.
    destruct scalar_aware_ok.
    + eapply
        Legacy.checked_tiling_sourceb_scalar_aware_direct_correct_same_ctxt;
        eauto.
    + bind_imp_destruct Hcheck phase_semantic_ok Hphase_semantic.
      destruct phase_semantic_ok.
      * eapply
          Legacy
            .checked_tiling_sourceb_phase_semantic_extended_direct_correct_same_ctxt;
          eauto.
      * bind_imp_destruct Hcheck phase_ordinary_ok Hphase_ordinary.
        destruct phase_ordinary_ok.
        -- eapply
             Mixed.check_pprog_phase_separated_ordinary_direct_correct_same_ctxt;
             eauto.
        -- bind_imp_destruct Hcheck phase_scalar_ok Hphase_scalar.
           destruct phase_scalar_ok.
           ++ eapply
                PhaseScalar
                  .checked_tiling_sourceb_phase_scalar_extended_direct_correct_same_ctxt;
                eauto.
           ++ bind_imp_destruct Hcheck semantic_ok Hsemantic.
              destruct semantic_ok.
              ** eapply
                   Legacy
                     .checked_tiling_sourceb_semantic_band_direct_correct_same_ctxt;
                   eauto.
              ** eapply
                   Mixed.check_pprog_mixed_second_level_direct_correct_same_ctxt;
                   eauto.
Qed.

Lemma checked_tiling_sourceb_complete_direct_band_check_outer_correct :
  forall before after ws st1 st2,
    PolyLang.wf_pprog_affine before ->
    PolyLang.wf_pprog_general after ->
    mayReturn
      (checked_tiling_sourceb_complete_direct_band_check
         (Legacy.Base.outer_to_tiling_pprog before)
         (Legacy.Base.outer_to_tiling_pprog after)
         ws)
      true ->
    PolyLang.instance_list_semantics after st1 st2 ->
    exists st2',
      PolyLang.instance_list_semantics before st1 st2' /\
      State.eq st2 st2'.
Proof.
  intros before after ws st1 st2 Hwf_before Hwf_after Hcheck Hsem_after.
  remember (Legacy.Base.outer_to_tiling_pprog before)
    as before_tiling eqn:Hbefore_tiling_eq.
  remember (Legacy.Base.outer_to_tiling_pprog after)
    as after_tiling eqn:Hafter_tiling_eq.
  destruct before_tiling as [[before_pis before_ctxt] before_vars].
  destruct after_tiling as [[after_pis after_ctxt] after_vars].
  simpl in Hbefore_tiling_eq, Hafter_tiling_eq.
  assert (Hsource :
    Legacy.TilingCheck.check_pprog_tiling_sourceb
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      ws = true).
  {
    eapply checked_tiling_sourceb_complete_direct_band_check_sourceb_true.
    exact Hcheck.
  }
  pose proof
    (Legacy.TilingCheck.check_pprog_tiling_sourceb_sound
       (before_pis, before_ctxt, before_vars)
       (after_pis, after_ctxt, after_vars) ws Hsource)
    as [Hprog _].
  unfold Legacy.Tiling.tiling_rel_pprog_structure_source in Hprog.
  simpl in Hprog.
  destruct Hprog as [Hctxt_eq [Hvars_eq _]].
  subst after_ctxt after_vars.
  pose proof
    (Legacy.Base.outer_to_tiling_wf_pprog_affine before Hwf_before)
    as Hwf_before_tiling.
  rewrite <- Hbefore_tiling_eq in Hwf_before_tiling.
  destruct Hwf_before_tiling as [_ Hwf_before_tiling].
  assert (Hwfbefore_pis :
    Forall
      (Legacy.Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis).
  {
    eapply Forall_forall.
    intros pi Hin.
    eapply Legacy.Tiling.PL.wf_pinstr_affine_implies_wf_pinstr_tiling.
    eapply Hwf_before_tiling; eauto.
  }
  pose proof
    (Legacy.Base.outer_to_tiling_wf_pprog_general after Hwf_after)
    as Hwf_after_tiling.
  rewrite <- Hafter_tiling_eq in Hwf_after_tiling.
  destruct Hwf_after_tiling as [_ Hwf_after_tiling].
  assert (Hwfafter_pis :
    Forall
      (Legacy.Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      after_pis).
  {
    eapply Forall_forall.
    intros pi Hin.
    eapply Hwf_after_tiling; eauto.
  }
  pose proof
    (checked_tiling_sourceb_complete_direct_band_check_correct
       before_pis before_ctxt before_vars after_pis ws st1 st2
       Hwfbefore_pis Hwfafter_pis Hcheck) as Hcorr.
  apply Legacy.Base.outer_to_tiling_instance_list_semantics_iff in Hsem_after.
  rewrite <- Hafter_tiling_eq in Hsem_after.
  specialize (Hcorr Hsem_after).
  destruct Hcorr as [st2' [Hbefore_tiling Heq]].
  rewrite Hbefore_tiling_eq in Hbefore_tiling.
  apply Legacy.Base.outer_to_tiling_instance_list_semantics_iff in Hbefore_tiling.
  exists st2'. split; assumption.
Qed.

Definition checked_tiling_schedule_sourceb_first_direct_runtime_validate_route
    (before after: PolyLang.t)
    (ws: list statement_tiling_witness) : imp tiling_band_validation_route :=
  BIND direct_ok <-
    checked_tiling_sourceb_complete_direct_band_check
      (Legacy.Base.outer_to_tiling_pprog before)
      (Legacy.Base.outer_to_tiling_pprog after)
      ws -;
  pure (if direct_ok then DirectBandAccepted else Rejected).

Lemma checked_tiling_schedule_sourceb_first_direct_runtime_validate_route_correct :
  forall before after ws st1 st2 route,
    PolyLang.wf_pprog_affine before ->
    PolyLang.wf_pprog_general after ->
    mayReturn
      (checked_tiling_schedule_sourceb_first_direct_runtime_validate_route
         before after ws)
      route ->
    tiling_band_validation_route_acceptsb route = true ->
    PolyLang.instance_list_semantics after st1 st2 ->
    exists st2',
      PolyLang.instance_list_semantics before st1 st2' /\
      State.eq st2 st2'.
Proof.
  intros before after ws st1 st2 route Hwf_before Hwf_after
         Hroute Haccept Hsem_after.
  unfold checked_tiling_schedule_sourceb_first_direct_runtime_validate_route
    in Hroute.
  bind_imp_destruct Hroute direct_ok Hdirect.
  destruct direct_ok.
  - apply mayReturn_pure in Hroute.
    subst route.
    eapply checked_tiling_sourceb_complete_direct_band_check_outer_correct;
      eauto.
  - apply mayReturn_pure in Hroute.
    subst route.
    simpl in Haccept.
    discriminate.
Qed.

(** A requested tiling must introduce at least one witnessed tile coordinate.
    In particular, the general checker must not turn an unchanged program into
    a successful tiling route merely because identity is a refinement. *)
Definition has_tiling_coordinatesb (ws: list statement_tiling_witness) : bool :=
  existsb (fun w => match stw_links w with [] => false | _ :: _ => true end) ws.

Definition checked_tiling_schedule_sourceb_first_runtime_validate_route
    (before after: PolyLang.t)
    (ws: list statement_tiling_witness) : imp tiling_band_validation_route :=
  BIND direct_ok <-
    checked_tiling_sourceb_complete_direct_band_check
      (Legacy.Base.outer_to_tiling_pprog before)
      (Legacy.Base.outer_to_tiling_pprog after)
      ws -;
  if direct_ok then pure DirectBandAccepted
  else
    if has_tiling_coordinatesb ws then
      BIND schedule_ok <- Legacy.Base.checked_tiling_validate_outer before after ws -;
      pure (if schedule_ok then GeneralScheduleAccepted else Rejected)
    else pure Rejected.

Lemma checked_tiling_schedule_sourceb_first_runtime_validate_route_correct :
  forall before after ws st1 st2 route,
    PolyLang.wf_pprog_affine before ->
    PolyLang.wf_pprog_general after ->
    mayReturn
      (checked_tiling_schedule_sourceb_first_runtime_validate_route
         before after ws)
      route ->
    tiling_band_validation_route_acceptsb route = true ->
    PolyLang.instance_list_semantics after st1 st2 ->
    exists st2',
      PolyLang.instance_list_semantics before st1 st2' /\
      State.eq st2 st2'.
Proof.
  intros before after ws st1 st2 route Hwf_before Hwf_after
         Hroute Haccept Hsem_after.
  unfold checked_tiling_schedule_sourceb_first_runtime_validate_route in Hroute.
  bind_imp_destruct Hroute direct_ok Hdirect.
  destruct direct_ok.
  - apply mayReturn_pure in Hroute. subst route.
    eapply checked_tiling_sourceb_complete_direct_band_check_outer_correct;
      eauto.
  - destruct (has_tiling_coordinatesb ws).
    + bind_imp_destruct Hroute schedule_ok Hschedule.
      destruct schedule_ok.
      * apply mayReturn_pure in Hroute. subst route.
        eapply Legacy.Base.checked_tiling_validate_outer_correct; eauto.
      * apply mayReturn_pure in Hroute. subst route.
        discriminate Haccept.
    + apply mayReturn_pure in Hroute. subst route. discriminate Haccept.
Qed.

End TilingBandDirectRuntime.

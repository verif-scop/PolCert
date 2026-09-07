Require Import Bool.
Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Require Import Linalg.
Require Import Misc.
Require Import PolyBase.
Require Import PolIRs.
Require Import TilingWitness.
Require Import TilingBandScheduleValidator.
Require Import TilingBandMixedSecondValidator.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Module TilingBandPhaseScalarValidator (PolIRs: POLIRS).

Module Mixed := TilingBandMixedSecondValidator PolIRs.
Module Core := Mixed.Core.
Module State := PolIRs.State.
Import Core.

Open Scope impure_scope.

(** * Proof map

    This validator extends phase separation to classes containing either an
    identity schedule or a scalar-aware tiled schedule.  It checks consistency
    within each phase class, applies the corresponding class-local semantic
    bridge, and exposes the same reordering-safety premise used by the common
    tiling theorem. *)

Definition schedule_head_constant
    (sched: Schedule) : option Z :=
  Mixed.schedule_head_constant sched.

Definition pinstr_head_constant
    (pi: Core.Tiling.PL.PolyInstr) : option Z :=
  Mixed.pinstr_head_constant pi.

Record phase_scalar_entry := {
  pse_phase : Z;
  pse_identity : bool;
  pse_layout : Core.scalar_aware_band_layout;
  pse_sizes : list Z
}.

Definition identity_phase_scalar_layout
    : Core.scalar_aware_band_layout :=
  {| Core.sabl_start := O;
     Core.sabl_loop_mask := [] |}.

Definition phase_scalar_entry_compatibleb
    (entry1 entry2: phase_scalar_entry) : bool :=
  if Z.eqb (pse_phase entry1) (pse_phase entry2) then
    Bool.eqb (pse_identity entry1) (pse_identity entry2) &&
    if pse_identity entry1 then true
    else
      Core.scalar_aware_band_layout_eqb
        (pse_layout entry1) (pse_layout entry2) &&
      Core.listz_strict_eqb (pse_sizes entry1) (pse_sizes entry2)
  else true.

Fixpoint check_phase_scalar_entry_againstb
    (entry: phase_scalar_entry)
    (entries: list phase_scalar_entry) : bool :=
  match entries with
  | [] => true
  | entry' :: entries' =>
      phase_scalar_entry_compatibleb entry entry' &&
      check_phase_scalar_entry_againstb entry entries'
  end.

Fixpoint check_phase_scalar_entries_consistentb
    (entries: list phase_scalar_entry) : bool :=
  match entries with
  | [] => true
  | entry :: entries' =>
      check_phase_scalar_entry_againstb entry entries' &&
      check_phase_scalar_entries_consistentb entries'
  end.

Definition phase_scalar_entries_consistent
    (entries: list phase_scalar_entry) : Prop :=
  forall entry1 entry2,
    In entry1 entries ->
    In entry2 entries ->
    pse_phase entry1 = pse_phase entry2 ->
    pse_identity entry1 = pse_identity entry2 /\
    (pse_identity entry1 = false ->
     pse_layout entry1 = pse_layout entry2 /\
     pse_sizes entry1 = pse_sizes entry2).

Inductive phase_scalar_entry_shape
    (env_size: nat)
    (before_pi after_pi: Core.Tiling.PL.PolyInstr)
    (w: statement_tiling_witness)
    (entry: phase_scalar_entry) : Prop :=
| PhaseScalarEntryShapeTiled :
    pinstr_head_constant before_pi = Some (pse_phase entry) ->
    pse_identity entry = false ->
    Core.sabl_start (pse_layout entry) = 1%nat ->
    Core.scalar_aware_entry_shape
      env_size (pse_layout entry) before_pi after_pi w ->
    pse_sizes entry = Core.tile_sizes_of_witness w ->
    phase_scalar_entry_shape env_size before_pi after_pi w entry
| PhaseScalarEntryShapeIdentity :
    pinstr_head_constant before_pi = Some (pse_phase entry) ->
    pse_identity entry = true ->
    stw_links w = [] ->
    Core.schedule_matches_with_trailing_zero_padding
      (Core.Tiling.lift_schedule_after_env
         O env_size (Core.Tiling.PL.pi_schedule before_pi))
      (Core.Tiling.PL.pi_schedule after_pi) ->
    pse_sizes entry = [] ->
    phase_scalar_entry_shape env_size before_pi after_pi w entry.

Inductive phase_scalar_shape_entries
    (env_size: nat)
    : list Core.Tiling.PL.PolyInstr ->
      list Core.Tiling.PL.PolyInstr ->
      list statement_tiling_witness ->
      list phase_scalar_entry -> Prop :=
| PhaseScalarShapeEntriesNil :
    phase_scalar_shape_entries env_size [] [] [] []
| PhaseScalarShapeEntriesCons :
    forall before_pi after_pi w entry
           before_pis after_pis ws entries,
      phase_scalar_entry_shape env_size before_pi after_pi w entry ->
      phase_scalar_shape_entries
        env_size before_pis after_pis ws entries ->
      phase_scalar_shape_entries
        env_size
        (before_pi :: before_pis)
        (after_pi :: after_pis)
        (w :: ws)
        (entry :: entries).

Fixpoint infer_phase_scalar_shape_entries
    (env_size: nat)
    (before_pis after_pis: list Core.Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    : option (list phase_scalar_entry) :=
  match before_pis, after_pis, ws with
  | [], [], [] => Some []
  | before_pi :: before_pis',
    after_pi :: after_pis',
    w :: ws' =>
      match pinstr_head_constant before_pi with
      | None => None
      | Some phase =>
          match stw_links w with
          | [] =>
              if
                Core.check_schedule_with_trailing_zero_paddingb
                  (Core.Tiling.lift_schedule_after_env
                     O env_size (Core.Tiling.PL.pi_schedule before_pi))
                  (Core.Tiling.PL.pi_schedule after_pi)
              then
                match
                  infer_phase_scalar_shape_entries
                    env_size before_pis' after_pis' ws'
                with
                | Some entries =>
                    Some
                      ({| pse_phase := phase;
                          pse_identity := true;
                          pse_layout := identity_phase_scalar_layout;
                          pse_sizes := [] |}
                       :: entries)
                | None => None
                end
              else None
          | _ :: _ =>
              match
                Core.infer_scalar_aware_band_layout env_size before_pi w
              with
              | Some layout =>
                  if Nat.eqb (Core.sabl_start layout) 1%nat then
                    if
                      Core.check_scalar_aware_band_selectionb
                        before_pi w layout
                    then
                      match
                        Core.scalar_aware_stripmine_schedule_after_env
                          env_size (List.length (stw_links w))
                          (Core.Tiling.PL.pi_schedule before_pi) layout,
                        infer_phase_scalar_shape_entries
                          env_size before_pis' after_pis' ws'
                      with
                      | Some expected, Some entries =>
                          if
                            Core.check_schedule_with_trailing_zero_paddingb
                              expected
                              (Core.Tiling.PL.pi_schedule after_pi)
                          then
                            Some
                              ({| pse_phase := phase;
                                  pse_identity := false;
                                  pse_layout := layout;
                                  pse_sizes :=
                                    Core.tile_sizes_of_witness w |}
                               :: entries)
                          else None
                      | _, _ => None
                      end
                    else None
                  else None
              | None => None
              end
          end
      end
  | _, _, _ => None
  end.

Definition infer_pprog_phase_scalar_shape
    (before after: Core.Tiling.PL.t)
    (ws: list statement_tiling_witness)
    : option (list phase_scalar_entry) :=
  let '(before_pis, before_ctxt, before_vars) := before in
  let '(after_pis, after_ctxt, after_vars) := after in
  if Core.TilingCheck.ctxt_eqb before_ctxt after_ctxt &&
     Core.TilingCheck.ctxt_ty_eqb before_vars after_vars
  then
    match
      infer_phase_scalar_shape_entries
        (List.length before_ctxt) before_pis after_pis ws
    with
    | Some entries =>
        if check_phase_scalar_entries_consistentb entries
        then Some entries
        else None
    | None => None
    end
  else None.

Lemma phase_scalar_entry_compatibleb_sound :
  forall entry1 entry2,
    phase_scalar_entry_compatibleb entry1 entry2 = true ->
    pse_phase entry1 = pse_phase entry2 ->
    pse_identity entry1 = pse_identity entry2 /\
    (pse_identity entry1 = false ->
     pse_layout entry1 = pse_layout entry2 /\
     pse_sizes entry1 = pse_sizes entry2).
Proof.
  intros entry1 entry2 Hcheck Hphase.
  unfold phase_scalar_entry_compatibleb in Hcheck.
  rewrite Hphase, Z.eqb_refl in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hkind Hdata].
  assert (Hkind_eq : pse_identity entry1 = pse_identity entry2).
  {
    destruct (pse_identity entry1), (pse_identity entry2);
      simpl in Hkind; try discriminate; reflexivity.
  }
  split.
  - exact Hkind_eq.
  - intro Hidentity.
    rewrite Hidentity in Hdata.
    apply andb_true_iff in Hdata.
    destruct Hdata as [Hlayout Hsizes].
    split.
    + eapply Core.scalar_aware_band_layout_eqb_sound.
      exact Hlayout.
    + eapply Core.listz_strict_eqb_eq.
      exact Hsizes.
Qed.

Lemma check_phase_scalar_entry_againstb_sound :
  forall entry entries,
    check_phase_scalar_entry_againstb entry entries = true ->
    forall entry',
      In entry' entries ->
      pse_phase entry = pse_phase entry' ->
      pse_identity entry = pse_identity entry' /\
      (pse_identity entry = false ->
       pse_layout entry = pse_layout entry' /\
       pse_sizes entry = pse_sizes entry').
Proof.
  intros entry entries.
  induction entries as [|entry' entries IH];
    intros Hcheck target Hin Hphase.
  - inversion Hin.
  - simpl in Hcheck.
    apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    destruct Hin as [Heq | Hin].
    + subst target.
      eapply phase_scalar_entry_compatibleb_sound; eauto.
    + eapply IH; eauto.
Qed.

Lemma check_phase_scalar_entries_consistentb_sound :
  forall entries,
    check_phase_scalar_entries_consistentb entries = true ->
    phase_scalar_entries_consistent entries.
Proof.
  intros entries.
  induction entries as [|entry entries IH]; intros Hcheck.
  - unfold phase_scalar_entries_consistent.
    intros. contradiction.
  - simpl in Hcheck.
    apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    unfold phase_scalar_entries_consistent in *.
    intros entry1 entry2 Hin1 Hin2 Hphase.
    destruct Hin1 as [Heq1 | Hin1];
    destruct Hin2 as [Heq2 | Hin2].
    + subst entry1 entry2.
      split; [reflexivity|].
      intro. split; reflexivity.
    + subst entry1.
      eapply check_phase_scalar_entry_againstb_sound; eauto.
    + subst entry2.
      destruct
        (check_phase_scalar_entry_againstb_sound
           entry entries Hhead entry1 Hin1 (eq_sym Hphase))
        as [Hkind Hdata].
      split.
      * symmetry. exact Hkind.
      * intro Hentry1_identity.
        assert (Hentry_identity : pse_identity entry = false).
        { rewrite Hkind. exact Hentry1_identity. }
        destruct (Hdata Hentry_identity) as [Hlayout Hsizes].
        split; symmetry; assumption.
    + eapply IH; eauto.
Qed.

Lemma infer_phase_scalar_shape_entries_sound :
  forall env_size before_pis after_pis ws entries,
    infer_phase_scalar_shape_entries
      env_size before_pis after_pis ws = Some entries ->
    phase_scalar_shape_entries
      env_size before_pis after_pis ws entries.
Proof.
  intros env_size before_pis.
  induction before_pis as [|before_pi before_pis IH];
    intros after_pis ws entries Hinfer.
  - destruct after_pis as [|after_pi after_pis].
    + destruct ws as [|w ws].
      * simpl in Hinfer. inversion Hinfer. constructor.
      * simpl in Hinfer. discriminate.
    + destruct ws as [|w ws]; simpl in Hinfer; discriminate.
  - destruct after_pis as [|after_pi after_pis].
    { destruct ws; simpl in Hinfer; discriminate. }
    destruct ws as [|w ws].
    { simpl in Hinfer. discriminate. }
    simpl in Hinfer.
    destruct (pinstr_head_constant before_pi)
      as [phase|] eqn:Hphase; [|discriminate].
    destruct (stw_links w) as [|link links] eqn:Hlinks.
    + destruct
        (Core.check_schedule_with_trailing_zero_paddingb
           (Core.Tiling.lift_schedule_after_env
              O env_size (Core.Tiling.PL.pi_schedule before_pi))
           (Core.Tiling.PL.pi_schedule after_pi))
        eqn:Hschedule; [|discriminate].
      destruct
        (infer_phase_scalar_shape_entries
           env_size before_pis after_pis ws)
        as [tail_entries|] eqn:Htail; [|discriminate].
      inversion Hinfer; subst.
      constructor.
      * apply PhaseScalarEntryShapeIdentity.
        -- exact Hphase.
        -- reflexivity.
        -- exact Hlinks.
        -- eapply
             Core.check_schedule_with_trailing_zero_paddingb_sound.
           exact Hschedule.
        -- reflexivity.
      * eapply IH. exact Htail.
    + destruct
        (Core.infer_scalar_aware_band_layout env_size before_pi w)
        as [layout|] eqn:Hlayout; [|discriminate].
      destruct (Nat.eqb (Core.sabl_start layout) 1%nat)
        eqn:Hstart; [|discriminate].
      destruct
        (Core.check_scalar_aware_band_selectionb before_pi w layout)
        eqn:Hselection; [|discriminate].
      destruct
        (Core.scalar_aware_stripmine_schedule_after_env
           env_size (List.length (link :: links))
           (Core.Tiling.PL.pi_schedule before_pi) layout)
        as [expected|] eqn:Hexpected; [|discriminate].
      destruct
        (infer_phase_scalar_shape_entries
           env_size before_pis after_pis ws)
        as [tail_entries|] eqn:Htail; [|discriminate].
      destruct
        (Core.check_schedule_with_trailing_zero_paddingb
           expected (Core.Tiling.PL.pi_schedule after_pi))
        eqn:Hschedule; [|discriminate].
      inversion Hinfer; subst.
      constructor.
      * apply PhaseScalarEntryShapeTiled.
        -- exact Hphase.
        -- reflexivity.
        -- apply Nat.eqb_eq. exact Hstart.
        -- destruct
             (Core.check_scalar_aware_band_selectionb_sound
                before_pi w layout Hselection)
             as [link_rows
                 [Hlink_rows [Hnonempty [Hband_len Hselected]]]].
           exists link_rows, expected.
           split; [exact Hlink_rows|].
           split; [exact Hnonempty|].
           split; [exact Hband_len|].
           split; [exact Hselected|].
           split.
           ++ rewrite Hlinks. exact Hexpected.
           ++ eapply
                Core.check_schedule_with_trailing_zero_paddingb_sound.
              exact Hschedule.
        -- reflexivity.
      * eapply IH. exact Htail.
Qed.

Lemma phase_scalar_shape_entries_lengths :
  forall env_size before_pis after_pis ws entries,
    phase_scalar_shape_entries
      env_size before_pis after_pis ws entries ->
    List.length before_pis = List.length after_pis /\
    List.length before_pis = List.length ws /\
    List.length before_pis = List.length entries.
Proof.
  intros env_size before_pis after_pis ws entries Hshape.
  induction Hshape; simpl; lia.
Qed.

Lemma phase_scalar_shape_entries_nth_error :
  forall env_size before_pis after_pis ws entries
         n before_pi after_pi w entry,
    phase_scalar_shape_entries
      env_size before_pis after_pis ws entries ->
    nth_error before_pis n = Some before_pi ->
    nth_error after_pis n = Some after_pi ->
    nth_error ws n = Some w ->
    nth_error entries n = Some entry ->
    phase_scalar_entry_shape env_size before_pi after_pi w entry.
Proof.
  intros env_size before_pis after_pis ws entries n.
  revert before_pis after_pis ws entries.
  induction n as [|n IH];
    intros before_pis after_pis ws entries
           before_pi after_pi w entry
           Hshape Hbefore Hafter Hw Hentry;
    inversion Hshape; subst; simpl in *; try discriminate.
  - inversion Hbefore; inversion Hafter; inversion Hw; inversion Hentry;
      subst.
    assumption.
  - eapply IH; eauto.
Qed.

Lemma infer_pprog_phase_scalar_shape_sound :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws entries,
    infer_pprog_phase_scalar_shape
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars) ws = Some entries ->
    before_ctxt = after_ctxt /\
    before_vars = after_vars /\
    phase_scalar_shape_entries
      (List.length before_ctxt)
      before_pis after_pis ws entries /\
    phase_scalar_entries_consistent entries.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws entries Hinfer.
  unfold infer_pprog_phase_scalar_shape in Hinfer.
  cbn beta iota zeta in Hinfer.
  destruct (Core.TilingCheck.ctxt_eqb before_ctxt after_ctxt)
    eqn:Hctxt; try discriminate.
  destruct (Core.TilingCheck.ctxt_ty_eqb before_vars after_vars)
    eqn:Hvars; try discriminate.
  destruct
    (infer_phase_scalar_shape_entries
       (List.length before_ctxt) before_pis after_pis ws)
    as [inferred|] eqn:Hentries; try discriminate.
  destruct (check_phase_scalar_entries_consistentb inferred)
    eqn:Hconsistent; try discriminate.
  inversion Hinfer; subst inferred.
  split.
  - apply Core.TilingCheck.ctxt_eqb_eq. exact Hctxt.
  - split.
    + apply Core.TilingCheck.ctxt_ty_eqb_eq. exact Hvars.
    + split.
      * eapply infer_phase_scalar_shape_entries_sound. exact Hentries.
      * eapply check_phase_scalar_entries_consistentb_sound.
        exact Hconsistent.
Qed.

Lemma forallb_zeqb_zero_dot_product :
  forall coeffs point,
    forallb (fun x => Z.eqb x 0%Z) coeffs = true ->
    Linalg.dot_product coeffs point = 0%Z.
Proof.
  exact Mixed.forallb_zeqb_zero_dot_product.
Qed.

Lemma schedule_head_constant_sound :
  forall sched phase,
    schedule_head_constant sched = Some phase ->
    forall point,
      firstn 1 (affine_product sched point) = [phase].
Proof.
  exact Mixed.schedule_head_constant_sound.
Qed.

Lemma forallb_skipn_true :
  forall (A: Type) (f: A -> bool) n xs,
    forallb f xs = true ->
    forallb f (skipn n xs) = true.
Proof.
  exact Mixed.forallb_skipn_true.
Qed.

Lemma schedule_head_constant_lift :
  forall sched phase added_dims env_size,
    schedule_head_constant sched = Some phase ->
    schedule_head_constant
      (Core.Tiling.lift_schedule_after_env
         added_dims env_size sched) = Some phase.
Proof.
  exact Mixed.schedule_head_constant_lift.
Qed.

Lemma schedule_head_constant_lift_sound :
  forall sched phase added_dims env_size point,
    schedule_head_constant sched = Some phase ->
    firstn 1
      (affine_product
         (Core.Tiling.lift_schedule_after_env
            added_dims env_size sched)
         point) = [phase].
Proof.
  exact Mixed.schedule_head_constant_lift_sound.
Qed.

Lemma scalar_aware_stripmine_expected_timestamp_prefix :
  forall env_size added_dims before_sched layout expected point,
    Core.sabl_start layout = 1%nat ->
    Core.scalar_aware_stripmine_schedule_after_env
      env_size added_dims before_sched layout = Some expected ->
    exists rest,
      affine_product expected point =
      firstn 1
        (affine_product
           (Core.Tiling.lift_schedule_after_env
              added_dims env_size before_sched)
           point) ++
      rest.
Proof.
  intros env_size added_dims before_sched layout expected point
         Hstart Hexpected.
  unfold Core.scalar_aware_stripmine_schedule_after_env in Hexpected.
  set
    (lifted :=
       Core.Tiling.lift_schedule_after_env
         added_dims env_size before_sched)
    in *.
  set
    (total_cols :=
       match lifted with
       | [] => (env_size + added_dims)%nat
       | (coeffs, _) :: _ => List.length coeffs
       end)
    in *.
  set (band := Core.scalar_aware_band layout) in *.
  set (prefix := firstn (Core.ptb_start band) lifted) in *.
  set
    (band_rows :=
       firstn (Core.ptb_len band)
         (skipn (Core.ptb_start band) lifted))
    in *.
  set
    (suffix :=
       skipn (Core.ptb_start band + Core.ptb_len band)%nat lifted)
    in *.
  destruct
    (Core.render_scalar_aware_tile_prefix
       (Core.sabl_loop_mask layout) band_rows
       (Core.Tiling.identity_affine_rows_from
          total_cols env_size added_dims))
    as [rendered|] eqn:Hrender; try discriminate.
  inversion Hexpected; subst expected; clear Hexpected.
  subst prefix band_rows suffix band.
  unfold Core.scalar_aware_band.
  cbn.
  rewrite Hstart.
  cbn.
  destruct lifted as [|row lifted]; simpl.
  - eexists. reflexivity.
  - eexists. reflexivity.
Qed.

Lemma phase_scalar_entry_shape_head :
  forall env_size before_pi after_pi w entry,
    phase_scalar_entry_shape env_size before_pi after_pi w entry ->
    pinstr_head_constant before_pi = Some (pse_phase entry).
Proof.
  intros env_size before_pi after_pi w entry Hshape.
  inversion Hshape; assumption.
Qed.

Lemma phase_scalar_entry_shape_tiled_inv :
  forall env_size before_pi after_pi w entry,
    phase_scalar_entry_shape env_size before_pi after_pi w entry ->
    pse_identity entry = false ->
    Core.sabl_start (pse_layout entry) = 1%nat /\
    Core.scalar_aware_entry_shape
      env_size (pse_layout entry) before_pi after_pi w /\
    pse_sizes entry = Core.tile_sizes_of_witness w.
Proof.
  intros env_size before_pi after_pi w entry Hshape Hidentity.
  inversion Hshape; subst.
  - split; [assumption|].
    split; assumption.
  - congruence.
Qed.

Lemma phase_scalar_entry_target_phase_decomposition :
  forall env_size before_pi after_pi w entry point,
    phase_scalar_entry_shape env_size before_pi after_pi w entry ->
    exists rest,
      is_eq
        (affine_product (Core.Tiling.PL.pi_schedule after_pi) point)
        (firstn 1
           (affine_product
              (Core.Tiling.lift_schedule_after_env
                 (List.length (stw_links w)) env_size
                 (Core.Tiling.PL.pi_schedule before_pi))
              point) ++
         rest) =
      true.
Proof.
  intros env_size before_pi after_pi w entry point Hshape.
  inversion Hshape as
    [Hhead Hidentity Hstart Hscalar Hsizes
    |Hhead Hidentity Hlinks Hschedule Hsizes];
    subst.
  - destruct Hscalar as
      [link_rows [expected
       [Hlink_rows [Hnonempty [Hband_len [Hselected
       [Hexpected Htarget]]]]]]].
    destruct
      (scalar_aware_stripmine_expected_timestamp_prefix
         env_size (List.length (stw_links w))
         (Core.Tiling.PL.pi_schedule before_pi)
         (pse_layout entry) expected point Hstart Hexpected)
      as [rest Hprefix].
    exists rest.
    rewrite <- Hprefix.
    eapply
      Core.schedule_matches_with_symmetric_trailing_zero_padding_affine_product_is_eq.
    left.
    exact Htarget.
  - exists
      (skipn 1
         (affine_product
            (Core.Tiling.lift_schedule_after_env
               (List.length (stw_links w)) env_size
               (Core.Tiling.PL.pi_schedule before_pi))
            point)).
    rewrite Hlinks.
    rewrite firstn_skipn.
    eapply
      Core.schedule_matches_with_symmetric_trailing_zero_padding_affine_product_is_eq.
    left.
    exact Hschedule.
Qed.

Lemma phase_scalar_identity_entry_timestamp_eq :
  forall env_size before_pi after_pi w entry point,
    phase_scalar_entry_shape env_size before_pi after_pi w entry ->
    pse_identity entry = true ->
    is_eq
      (affine_product (Core.Tiling.PL.pi_schedule after_pi) point)
      (affine_product
         (Core.Tiling.lift_schedule_after_env
            (List.length (stw_links w)) env_size
            (Core.Tiling.PL.pi_schedule before_pi))
         point) =
    true.
Proof.
  intros env_size before_pi after_pi w entry point
         Hshape Hidentity.
  inversion Hshape as
    [Hhead Htiled Hstart Hscalar Hsizes
    |Hhead Hidentity0 Hlinks Hschedule Hsizes];
    subst.
  - congruence.
  - rewrite Hlinks.
    eapply
      Core.schedule_matches_with_symmetric_trailing_zero_padding_affine_product_is_eq.
    left.
    exact Hschedule.
Qed.

Definition scalar_layout_entry :=
  (Core.Tiling.PL.PolyInstr_ext * Core.scalar_aware_band_layout)%type.

Definition validate_two_instr_scalar_layout_entries_component_direct
    (entry1 entry2: scalar_layout_entry)
    (dim env_size: nat) : imp bool :=
  let '(pi1, layout1) := entry1 in
  let '(pi2, layout2) := entry2 in
  if Core.scalar_aware_band_layout_eqb layout1 layout2 then
    if Nat.ltb dim (List.length (Core.sabl_loop_mask layout1)) then
      Core.validate_two_instrs_scalar_aware_band_component_direct
        pi1 pi2 layout1 dim env_size
    else pure true
  else pure true.

Fixpoint validate_scalar_layout_entry_and_list_component_direct
    (entry: scalar_layout_entry)
    (entries: list scalar_layout_entry)
    (dim env_size: nat) : imp bool :=
  match entries with
  | [] => pure true
  | entry' :: entries' =>
      BIND forward <-
        validate_two_instr_scalar_layout_entries_component_direct
          entry entry' dim env_size -;
      if forward then
        BIND backward <-
          validate_two_instr_scalar_layout_entries_component_direct
            entry' entry dim env_size -;
        if backward then
          validate_scalar_layout_entry_and_list_component_direct
            entry entries' dim env_size
        else pure false
      else pure false
  end.

Fixpoint validate_scalar_layout_entry_list_component_direct
    (entries: list scalar_layout_entry)
    (dim env_size: nat) : imp bool :=
  match entries with
  | [] => pure true
  | entry :: entries' =>
      BIND self <-
        validate_two_instr_scalar_layout_entries_component_direct
          entry entry dim env_size -;
      if self then
        BIND cross <-
          validate_scalar_layout_entry_and_list_component_direct
            entry entries' dim env_size -;
        if cross then
          validate_scalar_layout_entry_list_component_direct
            entries' dim env_size
        else pure false
      else pure false
  end.

Fixpoint validate_scalar_layout_entry_list_components_direct_from
    (entries: list scalar_layout_entry)
    (remaining dim env_size: nat) : imp bool :=
  match remaining with
  | O => pure true
  | S remaining' =>
      BIND component_ok <-
        validate_scalar_layout_entry_list_component_direct
          entries dim env_size -;
      if component_ok then
        validate_scalar_layout_entry_list_components_direct_from
          entries remaining' (S dim) env_size
      else pure false
  end.

Fixpoint max_scalar_layout_length
    (layouts: list Core.scalar_aware_band_layout) : nat :=
  match layouts with
  | [] => O
  | layout :: layouts' =>
      Nat.max
        (List.length (Core.sabl_loop_mask layout))
        (max_scalar_layout_length layouts')
  end.

Definition check_pprog_phase_scalar_components_direct
    (env_size: nat)
    (before_pis after_pis: list Core.Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (layouts: list Core.scalar_aware_band_layout) : imp bool :=
  let pis :=
    Core.Tiling.compose_tiling_pinstrs_ext_from_after
      env_size before_pis after_pis ws in
  let aligned :=
    Nat.eqb (List.length before_pis) (List.length after_pis) &&
    Nat.eqb (List.length before_pis) (List.length ws) &&
    Nat.eqb (List.length before_pis) (List.length pis) &&
    Nat.eqb (List.length before_pis) (List.length layouts) in
  let valid_access := Core.BandAffine.check_valid_access pis in
  if aligned then
    BIND res <-
      validate_scalar_layout_entry_list_components_direct_from
        (combine pis layouts)
        (max_scalar_layout_length layouts) O env_size -;
    pure (res && valid_access)
  else pure false.

Lemma validate_scalar_layout_entry_and_list_component_true_pair :
  forall entry entries dim env_size,
    mayReturn
      (validate_scalar_layout_entry_and_list_component_direct
         entry entries dim env_size)
      true ->
    forall entry',
      In entry' entries ->
      mayReturn
        (validate_two_instr_scalar_layout_entries_component_direct
           entry entry' dim env_size)
        true /\
      mayReturn
        (validate_two_instr_scalar_layout_entries_component_direct
           entry' entry dim env_size)
        true.
Proof.
  intros entry entries.
  induction entries as [|entry' entries IH];
    intros dim env_size Hcheck target Hin.
  - inversion Hin.
  - simpl in Hcheck.
    bind_imp_destruct Hcheck forward Hforward.
    destruct forward.
    + bind_imp_destruct Hcheck backward Hbackward.
      destruct backward.
      * destruct Hin as [Heq | Hin].
        -- subst target. split; assumption.
        -- eapply IH; eauto.
      * apply mayReturn_pure in Hcheck. discriminate.
    + apply mayReturn_pure in Hcheck. discriminate.
Qed.

Lemma validate_scalar_layout_entry_list_component_true_pair :
  forall entries dim env_size,
    mayReturn
      (validate_scalar_layout_entry_list_component_direct
         entries dim env_size)
      true ->
    forall entry1 entry2,
      In entry1 entries ->
      In entry2 entries ->
      mayReturn
        (validate_two_instr_scalar_layout_entries_component_direct
           entry1 entry2 dim env_size)
        true.
Proof.
  intros entries.
  induction entries as [|entry entries IH];
    intros dim env_size Hcheck entry1 entry2 Hin1 Hin2.
  - inversion Hin1.
  - simpl in Hcheck.
    bind_imp_destruct Hcheck self Hself.
    destruct self.
    + bind_imp_destruct Hcheck cross Hcross.
      destruct cross.
      * destruct Hin1 as [Heq1 | Hin1];
        destruct Hin2 as [Heq2 | Hin2].
        -- subst entry1 entry2. exact Hself.
        -- subst entry1.
           eapply
             (proj1
                (validate_scalar_layout_entry_and_list_component_true_pair
                   entry entries dim env_size Hcross entry2 Hin2)).
        -- subst entry2.
           eapply
             (proj2
                (validate_scalar_layout_entry_and_list_component_true_pair
                   entry entries dim env_size Hcross entry1 Hin1)).
        -- eapply IH; eauto.
      * apply mayReturn_pure in Hcheck. discriminate.
    + apply mayReturn_pure in Hcheck. discriminate.
Qed.

Lemma validate_scalar_layout_entry_list_components_true_component :
  forall entries remaining start env_size,
    mayReturn
      (validate_scalar_layout_entry_list_components_direct_from
         entries remaining start env_size)
      true ->
    forall dim,
      (start <= dim < start + remaining)%nat ->
      mayReturn
        (validate_scalar_layout_entry_list_component_direct
           entries dim env_size)
        true.
Proof.
  intros entries remaining.
  induction remaining as [|remaining IH];
    intros start env_size Hcheck dim Hrange.
  - lia.
  - simpl in Hcheck.
    bind_imp_destruct Hcheck component_ok Hcomponent.
    destruct component_ok.
    + destruct (Nat.eq_dec dim start) as [Heq | Hneq].
      * subst dim. exact Hcomponent.
      * eapply IH.
        -- exact Hcheck.
        -- lia.
    + apply mayReturn_pure in Hcheck. discriminate.
Qed.

Lemma max_scalar_layout_length_ge_nth_error :
  forall layouts n layout,
    nth_error layouts n = Some layout ->
    (List.length (Core.sabl_loop_mask layout) <=
     max_scalar_layout_length layouts)%nat.
Proof.
  intros layouts.
  induction layouts as [|layout0 layouts IH];
    intros n layout Hnth; destruct n as [|n]; simpl in *;
    try discriminate.
  - inversion Hnth; subst. apply Nat.le_max_l.
  - eapply Nat.le_trans.
    + eapply IH. exact Hnth.
    + apply Nat.le_max_r.
Qed.

Lemma scalar_aware_band_layout_eqb_refl :
  forall layout,
    Core.scalar_aware_band_layout_eqb layout layout = true.
Proof.
  intros [start mask].
  unfold Core.scalar_aware_band_layout_eqb.
  simpl.
  rewrite Nat.eqb_refl.
  induction mask as [|value mask IH]; simpl; auto.
  destruct value; simpl; exact IH.
Qed.

Definition pinstr_list_phase_scalar_componentwise_permutable
    (envv: list Z)
    (before_pis after_pis: list Core.Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (layouts: list Core.scalar_aware_band_layout) : Prop :=
  let pis :=
    Core.Tiling.compose_tiling_pinstrs_ext_from_after
      (List.length envv) before_pis after_pis ws in
  forall flat ip1 ip2 pi1 pi2 layout dim,
    Core.Tiling.PL.flatten_instrs_ext envv pis flat ->
    In ip1 flat ->
    In ip2 flat ->
    nth_error pis (Core.Tiling.PL.ip_nth_ext ip1) = Some pi1 ->
    nth_error pis (Core.Tiling.PL.ip_nth_ext ip2) = Some pi2 ->
    nth_error layouts (Core.Tiling.PL.ip_nth_ext ip1) = Some layout ->
    nth_error layouts (Core.Tiling.PL.ip_nth_ext ip2) = Some layout ->
    (dim < List.length (Core.sabl_loop_mask layout))%nat ->
    Core.Tiling.PL.instr_point_ext_old_sched_lt ip1 ip2 ->
    Core.scalar_aware_component_active layout dim pi1 pi2 ip1 ip2 ->
    Core.Tiling.PL.Permutable_ext ip1 ip2.

Local Definition phase_scalar_component_endpoint_facts
    (env : list Core.Tiling.PL.ident)
    (envv : list Z)
    (pis : list Core.Tiling.PL.PolyInstr_ext)
    (flat : list Core.Tiling.PL.InstrPoint_ext)
    (ip : Core.Tiling.PL.InstrPoint_ext)
    (pi : Core.Tiling.PL.PolyInstr_ext) : Prop :=
  exists slice,
    Core.Tiling.PL.flatten_instr_nth_ext
      envv (Core.Tiling.PL.ip_nth_ext ip) pi slice /\
    In ip slice /\
    Core.Tiling.PL.wf_pinstr_ext_tiling env pi /\
    Core.Instr.valid_access_function
      (Core.Tiling.PL.pi_waccess_ext pi)
      (Core.Tiling.PL.pi_raccess_ext pi)
      (Core.Tiling.PL.pi_instr_ext pi).

Local Lemma phase_scalar_component_endpoint_facts_of_member :
  forall env envv pis flat ip pi,
    Core.Tiling.PL.flatten_instrs_ext envv pis flat ->
    In ip flat ->
    nth_error pis (Core.Tiling.PL.ip_nth_ext ip) = Some pi ->
    Forall (Core.Tiling.PL.wf_pinstr_ext_tiling env) pis ->
    Forall
      (fun candidate =>
         Core.Instr.valid_access_function
           (Core.Tiling.PL.pi_waccess_ext candidate)
           (Core.Tiling.PL.pi_raccess_ext candidate)
           (Core.Tiling.PL.pi_instr_ext candidate))
      pis ->
    phase_scalar_component_endpoint_facts env envv pis flat ip pi.
Proof.
  intros env envv pis flat ip pi Hflat Hin Hnth Hwf Hvalid.
  destruct
    (Core.flatten_instrs_ext_member_slice_local
      envv pis flat ip pi Hflat Hin Hnth)
    as [slice [Hslice Hin_slice]].
  exists slice.
  split; [exact Hslice|].
  split; [exact Hin_slice|].
  split.
  - exact
      (Core.Tiling.Forall_nth_error
         Core.Tiling.PL.PolyInstr_ext
         (Core.Tiling.PL.wf_pinstr_ext_tiling env)
         pis (Core.Tiling.PL.ip_nth_ext ip) pi Hwf Hnth).
  - exact
      (Core.Tiling.Forall_nth_error
         Core.Tiling.PL.PolyInstr_ext
         (fun candidate =>
            Core.Instr.valid_access_function
              (Core.Tiling.PL.pi_waccess_ext candidate)
              (Core.Tiling.PL.pi_raccess_ext candidate)
              (Core.Tiling.PL.pi_instr_ext candidate))
         pis (Core.Tiling.PL.ip_nth_ext ip) pi Hvalid Hnth).
Qed.

Lemma check_pprog_phase_scalar_components_direct_sound :
  forall env envv before_pis after_pis ws layouts,
    List.length env = List.length envv ->
    Forall
      (Core.Tiling.PL.wf_pinstr_ext_tiling env)
      (Core.Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length env) before_pis after_pis ws) ->
    mayReturn
      (check_pprog_phase_scalar_components_direct
         (List.length env) before_pis after_pis ws layouts)
      true ->
    pinstr_list_phase_scalar_componentwise_permutable
      envv before_pis after_pis ws layouts.
Proof.
  intros env envv before_pis after_pis ws layouts Henv Hwf Hcheck.
  (* Recover the executable alignment and program-wide access checks. *)
  unfold check_pprog_phase_scalar_components_direct in Hcheck.
  destruct
    (Nat.eqb (List.length before_pis) (List.length after_pis) &&
     Nat.eqb (List.length before_pis) (List.length ws) &&
     Nat.eqb
       (List.length before_pis)
       (List.length
          (Core.Tiling.compose_tiling_pinstrs_ext_from_after
             (List.length env) before_pis after_pis ws)) &&
     Nat.eqb (List.length before_pis) (List.length layouts))
    eqn:Haligned.
  2:{ apply mayReturn_pure in Hcheck. discriminate. }
  bind_imp_destruct Hcheck components_ok Hcomponents.
  apply mayReturn_pure in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hcomponents_true Hvalid_true].
  subst components_ok.
  set (pis :=
    Core.Tiling.compose_tiling_pinstrs_ext_from_after
      (List.length env) before_pis after_pis ws).
  assert (Hvalid :
    Forall
      (fun pi =>
         Core.Instr.valid_access_function
           (Core.Tiling.PL.pi_waccess_ext pi)
           (Core.Tiling.PL.pi_raccess_ext pi)
           (Core.Tiling.PL.pi_instr_ext pi))
      pis).
  {
    unfold pis.
    eapply Core.BandAffine.check_valid_access_correct.
    exact Hvalid_true.
  }
  (* Specialize the certificate to one active component of one point pair. *)
  unfold pinstr_list_phase_scalar_componentwise_permutable.
  intros flat ip1 ip2 pi1 pi2 layout dim
         Hflat Hin1 Hin2 Hnth1 Hnth2 Hlayout1 Hlayout2
         Hdim Hold Hactive.
  assert (Hflat_pis : Core.Tiling.PL.flatten_instrs_ext envv pis flat).
  {
    unfold pis.
    rewrite Henv.
    exact Hflat.
  }
  assert
    (Hnth1_pis :
       nth_error pis (Core.Tiling.PL.ip_nth_ext ip1) = Some pi1).
  {
    unfold pis.
    rewrite Henv.
    exact Hnth1.
  }
  assert
    (Hnth2_pis :
       nth_error pis (Core.Tiling.PL.ip_nth_ext ip2) = Some pi2).
  {
    unfold pis.
    rewrite Henv.
    exact Hnth2.
  }
  (* Select the pair from the all-layout, all-component traversal. *)
  assert (Hentry1 : In (pi1, layout) (combine pis layouts)).
  {
    eapply Core.nth_error_combine_some_in_local.
    - exact Hnth1_pis.
    - exact Hlayout1.
  }
  assert (Hentry2 : In (pi2, layout) (combine pis layouts)).
  {
    eapply Core.nth_error_combine_some_in_local.
    - exact Hnth2_pis.
    - exact Hlayout2.
  }
  assert (Hcomponent_check :
    mayReturn
      (validate_scalar_layout_entry_list_component_direct
         (combine pis layouts) dim (List.length env))
      true).
  {
    eapply
      validate_scalar_layout_entry_list_components_true_component.
    - exact Hcomponents.
    - split; [lia|].
      eapply Nat.lt_le_trans.
      + exact Hdim.
      + eapply max_scalar_layout_length_ge_nth_error.
        exact Hlayout1.
  }
  assert (Hpair :
    mayReturn
      (validate_two_instr_scalar_layout_entries_component_direct
         (pi1, layout) (pi2, layout) dim (List.length env))
      true).
  {
    eapply validate_scalar_layout_entry_list_component_true_pair;
      eauto.
  }
  unfold
    validate_two_instr_scalar_layout_entries_component_direct
    in Hpair.
  rewrite scalar_aware_band_layout_eqb_refl in Hpair.
  assert
    (Hdim_bool :
       Nat.ltb dim (List.length (Core.sabl_loop_mask layout)) = true).
  { apply Nat.ltb_lt. exact Hdim. }
  rewrite Hdim_bool in Hpair.
  (* Package each endpoint for the Core pairwise checker. *)
  destruct
    (phase_scalar_component_endpoint_facts_of_member
       env envv pis flat ip1 pi1
       Hflat_pis Hin1 Hnth1_pis Hwf Hvalid)
    as [slice1 [Hslice1 [Hin_slice1 [Hwf1 Hvalid1]]]].
  destruct
    (phase_scalar_component_endpoint_facts_of_member
       env envv pis flat ip2 pi2
       Hflat_pis Hin2 Hnth2_pis Hwf Hvalid)
    as [slice2 [Hslice2 [Hin_slice2 [Hwf2 Hvalid2]]]].
  (* Delegate the collision and permutability argument to Core. *)
  eapply
    (Core.validate_two_instrs_scalar_aware_band_component_direct_sound
       env envv
       (Core.Tiling.PL.ip_nth_ext ip1)
       (Core.Tiling.PL.ip_nth_ext ip2)
       pi1 pi2 slice1 slice2 layout dim ip1 ip2);
    eauto.
Qed.

Definition phase_scalar_layouts
    (entries: list phase_scalar_entry)
    : list Core.scalar_aware_band_layout :=
  List.map pse_layout entries.

Lemma nth_error_phase_scalar_layouts :
  forall entries n entry,
    nth_error entries n = Some entry ->
    nth_error (phase_scalar_layouts entries) n =
      Some (pse_layout entry).
Proof.
  intros entries.
  induction entries as [|entry0 entries IH];
    intros n entry Hnth; destruct n; simpl in *; try discriminate.
  - inversion Hnth. reflexivity.
  - eapply IH. exact Hnth.
Qed.

(** Phase classification only needs a preserved head, exact identity classes,
    and consistent recipes.  Keeping these facts separate from the local
    tiling shape lets ordinary and two-level bridges share the same argument. *)
Record phase_scalar_classification_shape
    (env_size: nat)
    (before_pi after_pi: Core.Tiling.PL.PolyInstr)
    (w: statement_tiling_witness)
    (entry: phase_scalar_entry) : Prop := {
  pscs_head : pinstr_head_constant before_pi = Some (pse_phase entry);
  pscs_target_prefix : forall point, exists rest,
    is_eq (affine_product (Core.Tiling.PL.pi_schedule after_pi) point)
      (firstn 1 (affine_product
        (Core.Tiling.lift_schedule_after_env (List.length (stw_links w))
          env_size (Core.Tiling.PL.pi_schedule before_pi)) point) ++ rest) = true;
  pscs_identity : pse_identity entry = true -> forall point,
    is_eq (affine_product (Core.Tiling.PL.pi_schedule after_pi) point)
      (affine_product
        (Core.Tiling.lift_schedule_after_env (List.length (stw_links w))
          env_size (Core.Tiling.PL.pi_schedule before_pi)) point) = true;
  pscs_sizes : pse_identity entry = false ->
    pse_sizes entry = Core.tile_sizes_of_witness w
}.

Definition phase_scalar_classification_shapes
    (env_size: nat)
    (before_pis after_pis: list Core.Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (entries: list phase_scalar_entry) : Prop :=
  List.length before_pis = List.length entries /\
  forall n before_pi after_pi w entry,
    nth_error before_pis n = Some before_pi ->
    nth_error after_pis n = Some after_pi ->
    nth_error ws n = Some w ->
    nth_error entries n = Some entry ->
    phase_scalar_classification_shape env_size before_pi after_pi w entry.

Lemma phase_scalar_shape_classification :
  forall env_size before_pis after_pis ws entries,
    phase_scalar_shape_entries env_size before_pis after_pis ws entries ->
    phase_scalar_classification_shapes env_size before_pis after_pis ws entries.
Proof.
  intros env_size before_pis after_pis ws entries Hshape.
  split.
  - destruct (phase_scalar_shape_entries_lengths
      env_size before_pis after_pis ws entries Hshape) as [_ [_ Hlen]].
    exact Hlen.
  - intros n before_pi after_pi w entry Hbefore Hafter Hw Hentry.
    pose proof (phase_scalar_shape_entries_nth_error
      env_size before_pis after_pis ws entries n before_pi after_pi w entry
      Hshape Hbefore Hafter Hw Hentry) as Hlocal.
    constructor.
    + eapply phase_scalar_entry_shape_head; eauto.
    + intro point. eapply phase_scalar_entry_target_phase_decomposition; eauto.
    + intros Hidentity point. eapply phase_scalar_identity_entry_timestamp_eq; eauto.
    + intro Hidentity.
      destruct (phase_scalar_entry_shape_tiled_inv
        env_size before_pi after_pi w entry Hlocal Hidentity) as [_ [_ Hsizes]].
      exact Hsizes.
Qed.

Lemma phase_scalar_reversal_same_class_abstract :
  forall before_pis before_ctxt before_vars
         after_pis ws entries envv flat ip1 ip2,
    List.length before_ctxt = List.length envv ->
    Core.TilingCheck.check_pprog_tiling_sourceb
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars) ws = true ->
    phase_scalar_classification_shapes
      (List.length before_ctxt)
      before_pis after_pis ws entries ->
    phase_scalar_entries_consistent entries ->
    Core.Tiling.PL.flatten_instrs_ext
      envv
      (Core.Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length envv) before_pis after_pis ws)
      flat ->
    In ip1 flat ->
    In ip2 flat ->
    Core.Tiling.PL.instr_point_ext_old_sched_lt ip1 ip2 ->
    Core.Tiling.PL.instr_point_ext_new_sched_ge ip1 ip2 ->
    exists layout w1 w2 entry1 entry2,
      nth_error entries (Core.Tiling.PL.ip_nth_ext ip1) = Some entry1 /\
      nth_error entries (Core.Tiling.PL.ip_nth_ext ip2) = Some entry2 /\
      pse_identity entry1 = false /\
      pse_identity entry2 = false /\
      nth_error
        (phase_scalar_layouts entries)
        (Core.Tiling.PL.ip_nth_ext ip1) = Some layout /\
      nth_error
        (phase_scalar_layouts entries)
        (Core.Tiling.PL.ip_nth_ext ip2) = Some layout /\
      nth_error ws (Core.Tiling.PL.ip_nth_ext ip1) = Some w1 /\
      nth_error ws (Core.Tiling.PL.ip_nth_ext ip2) = Some w2 /\
      Core.tile_sizes_of_witness w1 =
      Core.tile_sizes_of_witness w2.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis ws entries envv flat ip1 ip2
         Hlen_env Hsource Hshape Hconsistent
         Hflat Hin1 Hin2 Hold Hnew.
  (* Recover the source relation and witness invariants. *)
  pose proof
    (Core.TilingCheck.check_pprog_tiling_sourceb_sound
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars) ws Hsource)
    as [Hprog [_ [Hwf_ws [Hpositive_ws Hdepths]]]].
  assert
    (Hwf_ws_env :
       Forall
         (Core.Tiling.wf_statement_tiling_witness_with_param_dim
            (List.length envv))
         ws).
  {
    rewrite <- Hlen_env.
    exact Hwf_ws.
  }
  (* Recover source, target, and witness data for both endpoints. *)
  destruct
    (Core.flatten_instrs_ext_from_after_member_nth_data_source
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       ws envv flat ip1
       Hprog Hwf_ws_env Hpositive_ws Hdepths Hflat Hin1)
    as [before_pi1 [after_pi1 [w1
         [Hbefore1 [Hafter1 [Hw1
         [Hwf_stmt1 [Hpositive1 [Hpoint_depth1
         [Hpref1 [Hbel1 Hidx_len1]]]]]]]]]]].
  destruct
    (Core.flatten_instrs_ext_from_after_member_nth_data_source
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       ws envv flat ip2
       Hprog Hwf_ws_env Hpositive_ws Hdepths Hflat Hin2)
    as [before_pi2 [after_pi2 [w2
         [Hbefore2 [Hafter2 [Hw2
         [Hwf_stmt2 [Hpositive2 [Hpoint_depth2
         [Hpref2 [Hbel2 Hidx_len2]]]]]]]]]]].
  (* Select the aligned phase entry for each endpoint. *)
  destruct Hshape as [Hentries_len Hshape].
  destruct
    (nth_error entries (Core.Tiling.PL.ip_nth_ext ip1))
    as [entry1|] eqn:Hentry1.
  2:{
    apply nth_error_None in Hentry1.
    assert
      (Hlt :
         (Core.Tiling.PL.ip_nth_ext ip1 <
          List.length before_pis)%nat).
    {
      apply nth_error_Some.
      rewrite Hbefore1.
      discriminate.
    }
    lia.
  }
  destruct
    (nth_error entries (Core.Tiling.PL.ip_nth_ext ip2))
    as [entry2|] eqn:Hentry2.
  2:{
    apply nth_error_None in Hentry2.
    assert
      (Hlt :
         (Core.Tiling.PL.ip_nth_ext ip2 <
          List.length before_pis)%nat).
    {
      apply nth_error_Some.
      rewrite Hbefore2.
      discriminate.
    }
    lia.
  }
  (* Derive each statement-local phase shape and constant head. *)
  pose proof
    (Hshape (Core.Tiling.PL.ip_nth_ext ip1)
       before_pi1 after_pi1 w1 entry1
       Hbefore1 Hafter1 Hw1 Hentry1)
    as Hentry_shape1.
  pose proof
    (Hshape (Core.Tiling.PL.ip_nth_ext ip2)
       before_pi2 after_pi2 w2 entry2
       Hbefore2 Hafter2 Hw2 Hentry2)
    as Hentry_shape2.
  pose proof
    (pscs_head
       (List.length before_ctxt)
       before_pi1 after_pi1 w1 entry1 Hentry_shape1)
    as Hhead1.
  pose proof
    (pscs_head
       (List.length before_ctxt)
       before_pi2 after_pi2 w2 entry2 Hentry_shape2)
    as Hhead2.
  (* Recover source and target timestamps from the composed points. *)
  unfold Core.Tiling.compose_tiling_pinstr_ext in Hbel1, Hbel2.
  destruct Hbel1 as [_ [_ [_ [Hts11 [Hts21 [_ _]]]]]].
  destruct Hbel2 as [_ [_ [_ [Hts12 [Hts22 [_ _]]]]]].
  assert
    (Hts11_lift :
       Core.Tiling.PL.ip_time_stamp1_ext ip1 =
       affine_product
         (Core.Tiling.lift_schedule_after_env
            (List.length (stw_links w1)) (List.length envv)
            (Core.Tiling.PL.pi_schedule before_pi1))
         (Core.Tiling.PL.ip_index_ext ip1)).
  { rewrite Hts11. reflexivity. }
  assert
    (Hts12_lift :
       Core.Tiling.PL.ip_time_stamp1_ext ip2 =
       affine_product
         (Core.Tiling.lift_schedule_after_env
            (List.length (stw_links w2)) (List.length envv)
            (Core.Tiling.PL.pi_schedule before_pi2))
         (Core.Tiling.PL.ip_index_ext ip2)).
  { rewrite Hts12. reflexivity. }
  assert
    (Hts21_after :
       Core.Tiling.PL.ip_time_stamp2_ext ip1 =
       affine_product
         (Core.Tiling.PL.pi_schedule after_pi1)
         (Core.Tiling.PL.ip_index_ext ip1)).
  { rewrite Hts21. reflexivity. }
  assert
    (Hts22_after :
       Core.Tiling.PL.ip_time_stamp2_ext ip2 =
       affine_product
         (Core.Tiling.PL.pi_schedule after_pi2)
         (Core.Tiling.PL.ip_index_ext ip2)).
  { rewrite Hts22. reflexivity. }
  (* Expose the scalar prefix preserved by both target timestamps. *)
  destruct
    (pscs_target_prefix
       (List.length before_ctxt)
       before_pi1 after_pi1 w1 entry1
       Hentry_shape1 (Core.Tiling.PL.ip_index_ext ip1))
    as [rest1 Htime_eq1_raw].
  destruct
    (pscs_target_prefix
       (List.length before_ctxt)
       before_pi2 after_pi2 w2 entry2
       Hentry_shape2 (Core.Tiling.PL.ip_index_ext ip2))
    as [rest2 Htime_eq2_raw].
  assert
    (Htime_eq1 :
       is_eq
         (Core.Tiling.PL.ip_time_stamp2_ext ip1)
         (firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext ip1) ++ rest1) =
       true).
  {
    rewrite Hts21_after, Hts11_lift.
    rewrite <- Hlen_env.
    exact Htime_eq1_raw.
  }
  assert
    (Htime_eq2 :
       is_eq
         (Core.Tiling.PL.ip_time_stamp2_ext ip2)
         (firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext ip2) ++ rest2) =
       true).
  {
    rewrite Hts22_after, Hts12_lift.
    rewrite <- Hlen_env.
    exact Htime_eq2_raw.
  }
  (* A reversal across equal-length preserved prefixes forces equal phases. *)
  assert
    (Hnew_not_lt :
       lex_compare
         (Core.Tiling.PL.ip_time_stamp2_ext ip1)
         (Core.Tiling.PL.ip_time_stamp2_ext ip2) <> Lt).
  {
    intro Hlt.
    unfold Core.Tiling.PL.instr_point_ext_new_sched_ge in Hnew.
    destruct Hnew; congruence.
  }
  assert
    (Hnew_expected_not_lt :
       lex_compare
         (firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext ip1) ++ rest1)
         (firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext ip2) ++ rest2) <>
       Lt).
  {
    assert
      (Hcompare :
         lex_compare
           (Core.Tiling.PL.ip_time_stamp2_ext ip1)
           (Core.Tiling.PL.ip_time_stamp2_ext ip2) =
         lex_compare
           (firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext ip1) ++ rest1)
           (firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext ip2) ++ rest2)).
    {
      transitivity
        (lex_compare
           (firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext ip1) ++ rest1)
           (Core.Tiling.PL.ip_time_stamp2_ext ip2)).
      - apply lex_compare_left_eq. exact Htime_eq1.
      - apply lex_compare_right_eq. exact Htime_eq2.
    }
    rewrite Hcompare in Hnew_not_lt.
    exact Hnew_not_lt.
  }
  assert
    (Hphase_eval1 :
       firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext ip1) =
       [pse_phase entry1]).
  {
    rewrite Hts11_lift.
    eapply schedule_head_constant_lift_sound.
    exact Hhead1.
  }
  assert
    (Hphase_eval2 :
       firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext ip2) =
       [pse_phase entry2]).
  {
    rewrite Hts12_lift.
    eapply schedule_head_constant_lift_sound.
    exact Hhead2.
  }
  assert
    (Hprefix_len :
       List.length
         (firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext ip1)) =
       List.length
         (firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext ip2))).
  {
    rewrite Hphase_eval1, Hphase_eval2.
    reflexivity.
  }
  assert
    (Hprefix :
       firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext ip1) =
       firstn 1 (Core.Tiling.PL.ip_time_stamp1_ext ip2)).
  {
    unfold Core.Tiling.PL.instr_point_ext_old_sched_lt in Hold.
    rewrite <-
      (firstn_skipn 1 (Core.Tiling.PL.ip_time_stamp1_ext ip1)) in Hold.
    rewrite <-
      (firstn_skipn 1 (Core.Tiling.PL.ip_time_stamp1_ext ip2)) in Hold.
    eapply Core.preserved_equal_length_prefix_reversal_implies_prefix_eq;
      eauto.
  }
  assert (Hphase : pse_phase entry1 = pse_phase entry2).
  {
    rewrite Hphase_eval1, Hphase_eval2 in Hprefix.
    inversion Hprefix.
    reflexivity.
  }
  (* Class consistency rules out identity reversal or aligns tiled entries. *)
  destruct
    (Hconsistent entry1 entry2
       (nth_error_In entries _ Hentry1)
       (nth_error_In entries _ Hentry2)
       Hphase)
    as [Hsame_kind Hsame_tiled_data].
  destruct (pse_identity entry1) eqn:Hidentity1.
  - assert (Hidentity2 : pse_identity entry2 = true).
    { symmetry. exact Hsame_kind. }
    pose proof
      (pscs_identity
         (List.length before_ctxt)
         before_pi1 after_pi1 w1 entry1
         Hentry_shape1 Hidentity1 (Core.Tiling.PL.ip_index_ext ip1))
      as Hidentity_time1_raw.
    pose proof
      (pscs_identity
         (List.length before_ctxt)
         before_pi2 after_pi2 w2 entry2
         Hentry_shape2 Hidentity2 (Core.Tiling.PL.ip_index_ext ip2))
      as Hidentity_time2_raw.
    assert
      (Hidentity_time1 :
         is_eq
           (Core.Tiling.PL.ip_time_stamp2_ext ip1)
           (Core.Tiling.PL.ip_time_stamp1_ext ip1) = true).
    {
      rewrite Hts21_after, Hts11_lift.
      rewrite <- Hlen_env.
      exact Hidentity_time1_raw.
    }
    assert
      (Hidentity_time2 :
         is_eq
           (Core.Tiling.PL.ip_time_stamp2_ext ip2)
           (Core.Tiling.PL.ip_time_stamp1_ext ip2) = true).
    {
      rewrite Hts22_after, Hts12_lift.
      rewrite <- Hlen_env.
      exact Hidentity_time2_raw.
    }
    assert
      (Hcompare :
         lex_compare
           (Core.Tiling.PL.ip_time_stamp2_ext ip1)
           (Core.Tiling.PL.ip_time_stamp2_ext ip2) =
         lex_compare
           (Core.Tiling.PL.ip_time_stamp1_ext ip1)
           (Core.Tiling.PL.ip_time_stamp1_ext ip2)).
    {
      transitivity
        (lex_compare
           (Core.Tiling.PL.ip_time_stamp1_ext ip1)
           (Core.Tiling.PL.ip_time_stamp2_ext ip2)).
      + apply lex_compare_left_eq. exact Hidentity_time1.
      + apply lex_compare_right_eq. exact Hidentity_time2.
    }
    unfold Core.Tiling.PL.instr_point_ext_old_sched_lt in Hold.
    rewrite Hcompare in Hnew_not_lt.
    contradiction.
  (* Return the common tiled layout and equal tile-size recipe. *)
  - assert (Hidentity2 : pse_identity entry2 = false).
    { symmetry. exact Hsame_kind. }
    destruct (Hsame_tiled_data eq_refl)
      as [Hsame_layout Hsame_sizes].
    pose proof
      (pscs_sizes
         (List.length before_ctxt)
         before_pi1 after_pi1 w1 entry1
         Hentry_shape1 Hidentity1)
      as Hentry_sizes1.
    pose proof
      (pscs_sizes
         (List.length before_ctxt)
         before_pi2 after_pi2 w2 entry2
         Hentry_shape2 Hidentity2)
      as Hentry_sizes2.
    rewrite Hentry_sizes1, Hentry_sizes2 in Hsame_sizes.
    exists (pse_layout entry1), w1, w2, entry1, entry2.
    split; [reflexivity|].
    split; [reflexivity|].
    split; [exact Hidentity1|].
    split; [exact Hidentity2|].
    split.
    + eapply nth_error_phase_scalar_layouts. exact Hentry1.
    + split.
      * rewrite Hsame_layout.
        eapply nth_error_phase_scalar_layouts. exact Hentry2.
      * split; [exact Hw1|].
        split; [exact Hw2|].
        exact Hsame_sizes.
Qed.

Lemma phase_scalar_reversal_same_class :
  forall before_pis before_ctxt before_vars after_pis ws entries envv flat ip1 ip2,
    List.length before_ctxt = List.length envv ->
    Core.TilingCheck.check_pprog_tiling_sourceb
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars) ws = true ->
    phase_scalar_shape_entries (List.length before_ctxt)
      before_pis after_pis ws entries ->
    phase_scalar_entries_consistent entries ->
    Core.Tiling.PL.flatten_instrs_ext envv
      (Core.Tiling.compose_tiling_pinstrs_ext_from_after
        (List.length envv) before_pis after_pis ws) flat ->
    In ip1 flat -> In ip2 flat ->
    Core.Tiling.PL.instr_point_ext_old_sched_lt ip1 ip2 ->
    Core.Tiling.PL.instr_point_ext_new_sched_ge ip1 ip2 ->
    exists layout w1 w2 entry1 entry2,
      nth_error entries (Core.Tiling.PL.ip_nth_ext ip1) = Some entry1 /\
      nth_error entries (Core.Tiling.PL.ip_nth_ext ip2) = Some entry2 /\
      pse_identity entry1 = false /\ pse_identity entry2 = false /\
      nth_error (phase_scalar_layouts entries)
        (Core.Tiling.PL.ip_nth_ext ip1) = Some layout /\
      nth_error (phase_scalar_layouts entries)
        (Core.Tiling.PL.ip_nth_ext ip2) = Some layout /\
      nth_error ws (Core.Tiling.PL.ip_nth_ext ip1) = Some w1 /\
      nth_error ws (Core.Tiling.PL.ip_nth_ext ip2) = Some w2 /\
      Core.tile_sizes_of_witness w1 = Core.tile_sizes_of_witness w2.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws entries envv flat ip1 ip2
    Henv Hsource Hshape Hconsistent Hflat Hin1 Hin2 Hold Hnew.
  eapply phase_scalar_reversal_same_class_abstract; eauto.
  eapply phase_scalar_shape_classification; eauto.
Qed.

Definition checked_tiling_sourceb_phase_scalar_direct
    (before after: Core.Tiling.PL.t)
    (ws: list statement_tiling_witness) : imp bool :=
  let '(before_pis, before_ctxt, _) := before in
  let '(after_pis, _, _) := after in
  if Core.TilingCheck.check_pprog_tiling_sourceb before after ws then
    match infer_pprog_phase_scalar_shape before after ws with
    | Some entries =>
        check_pprog_phase_scalar_components_direct
          (List.length before_ctxt)
          before_pis after_pis ws
          (phase_scalar_layouts entries)
    | None => pure false
    end
  else pure false.

Lemma checked_tiling_sourceb_phase_scalar_direct_true_inv :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws,
    mayReturn
      (checked_tiling_sourceb_phase_scalar_direct
         (before_pis, before_ctxt, before_vars)
         (after_pis, after_ctxt, after_vars) ws)
      true ->
    exists entries,
      Core.TilingCheck.check_pprog_tiling_sourceb
        (before_pis, before_ctxt, before_vars)
        (after_pis, after_ctxt, after_vars) ws = true /\
      infer_pprog_phase_scalar_shape
        (before_pis, before_ctxt, before_vars)
        (after_pis, after_ctxt, after_vars) ws = Some entries /\
      mayReturn
        (check_pprog_phase_scalar_components_direct
           (List.length before_ctxt)
           before_pis after_pis ws
           (phase_scalar_layouts entries))
        true.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws Hcheck.
  unfold checked_tiling_sourceb_phase_scalar_direct in Hcheck.
  destruct
    (Core.TilingCheck.check_pprog_tiling_sourceb
       (before_pis, before_ctxt, before_vars)
       (after_pis, after_ctxt, after_vars) ws)
    eqn:Hsource.
  2:{ apply mayReturn_pure in Hcheck. discriminate. }
  destruct
    (infer_pprog_phase_scalar_shape
       (before_pis, before_ctxt, before_vars)
       (after_pis, after_ctxt, after_vars) ws)
    as [entries|] eqn:Hshape.
  2:{ apply mayReturn_pure in Hcheck. discriminate. }
  exists entries.
  split; [reflexivity|].
  split; [reflexivity|exact Hcheck].
Qed.

Local Lemma phase_scalar_tiled_shape_at :
  forall env_size before_pis after_pis ws entries n entry class_layout,
    phase_scalar_shape_entries
      env_size before_pis after_pis ws entries ->
    nth_error entries n = Some entry ->
    pse_identity entry = false ->
    nth_error (phase_scalar_layouts entries) n = Some class_layout ->
    forall before_pi after_pi w layout,
      nth_error before_pis n = Some before_pi ->
      nth_error after_pis n = Some after_pi ->
      nth_error ws n = Some w ->
      nth_error (phase_scalar_layouts entries) n = Some layout ->
      Core.scalar_aware_entry_shape
        env_size layout before_pi after_pi w.
Proof.
  intros env_size before_pis after_pis ws entries n entry class_layout
         Hshapes Hentry Hidentity Hclass_layout
         before_pi after_pi w layout Hbefore Hafter Hw Hlayout.
  pose proof
    (phase_scalar_shape_entries_nth_error
       env_size before_pis after_pis ws entries n
       before_pi after_pi w entry
       Hshapes Hbefore Hafter Hw Hentry)
    as Hentry_shape.
  destruct
    (phase_scalar_entry_shape_tiled_inv
       env_size before_pi after_pi w entry Hentry_shape Hidentity)
    as [_ [Htiled_shape _]].
  assert (Hlayout_eq : layout = class_layout).
  { rewrite Hclass_layout in Hlayout. congruence. }
  assert (Hentry_layout : pse_layout entry = class_layout).
  {
    pose proof
      (nth_error_phase_scalar_layouts entries n entry Hentry)
      as Hentry_layout_nth.
    rewrite Hclass_layout in Hentry_layout_nth.
    congruence.
  }
  subst layout.
  rewrite <- Hentry_layout.
  exact Htiled_shape.
Qed.

Lemma checked_tiling_sourceb_phase_scalar_direct_reordering_safe :
  forall before_pis before_ctxt before_vars after_pis ws envv,
    List.length before_ctxt = List.length envv ->
    Forall
      (Core.Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    Forall
      (Core.Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      after_pis ->
    mayReturn
      (checked_tiling_sourceb_phase_scalar_direct
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars) ws)
      true ->
    Core.pprog_tiling_reordering_safe
      envv before_pis after_pis ws [].
Proof.
  intros before_pis before_ctxt before_vars after_pis ws envv
         Hlen_env Hwf_before Hwf_after Hcheck.
  (* Invert the three executable checks and recover their semantic facts. *)
  destruct
    (checked_tiling_sourceb_phase_scalar_direct_true_inv
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars ws Hcheck)
    as [entries [Hsource [Hshape Hcomponents]]].
  destruct
    (infer_pprog_phase_scalar_shape_sound
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars ws entries Hshape)
    as [_ [_ [Hshape_entries Hconsistent]]].
  destruct
    (phase_scalar_shape_entries_lengths
       (List.length before_ctxt)
       before_pis after_pis ws entries Hshape_entries)
    as [_ [_ Hentries_len]].
  assert
    (Hlayouts_len :
       List.length (phase_scalar_layouts entries) =
       List.length before_pis).
  {
    unfold phase_scalar_layouts.
    rewrite map_length.
    symmetry.
    exact Hentries_len.
  }
  (* Establish the source relation and well-formed composed instructions. *)
  pose proof
    (Core.TilingCheck.check_pprog_tiling_sourceb_sound
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars) ws Hsource)
    as [Hprog [_ [Hwf_ws [_ Hdepths]]]].
  assert
    (Hwits :
       Forall2 Core.Tiling.after_matches_tiling_witness after_pis ws).
  {
    eapply
      (Core.tiling_rel_pprog_structure_source_after_matches
         before_pis before_ctxt before_vars
         after_pis before_ctxt before_vars ws);
      eauto.
  }
  assert
    (Hcomposed_wf :
       Forall
         (Core.Tiling.PL.wf_pinstr_ext_tiling before_ctxt)
         (Core.Tiling.compose_tiling_pinstrs_ext_from_after
            (List.length before_ctxt) before_pis after_pis ws)).
  {
    eapply Core.compose_tiling_pinstrs_ext_from_after_wf_tiling;
      eauto.
  }
  assert
    (Hcomponentwise :
       pinstr_list_phase_scalar_componentwise_permutable
         envv before_pis after_pis ws
         (phase_scalar_layouts entries)).
  {
    eapply
      (check_pprog_phase_scalar_components_direct_sound
         before_ctxt envv before_pis after_pis ws
         (phase_scalar_layouts entries)).
    - exact Hlen_env.
    - exact Hcomposed_wf.
    - exact Hcomponents.
  }
  (* Classify an arbitrary target reversal by its preserved scalar phase. *)
  unfold Core.pprog_tiling_reordering_safe,
         Core.pprog_permutable_tiling_bands.
  intros flat ip1 ip2 Hflat Hin1 Hin2 Hold Hnew.
  destruct
    (phase_scalar_reversal_same_class
       before_pis before_ctxt before_vars after_pis ws entries
       envv flat ip1 ip2
       Hlen_env Hsource Hshape_entries Hconsistent
       Hflat Hin1 Hin2 Hold Hnew)
    as [class_layout [w1 [w2 [entry1 [entry2
         [Hentry1 [Hentry2 [Hidentity1 [Hidentity2
         [Hclass_layout1 [Hclass_layout2
         [Hw1 [Hw2 Hclass_sizes]]]]]]]]]]]]].
  (* Build the two tiled-shape callbacks from their selected phase entries. *)
  pose proof
    (phase_scalar_tiled_shape_at
       (List.length before_ctxt) before_pis after_pis ws entries
       (Core.Tiling.PL.ip_nth_ext ip1) entry1 class_layout
       Hshape_entries Hentry1 Hidentity1 Hclass_layout1)
    as Hshape_at1.
  pose proof
    (phase_scalar_tiled_shape_at
       (List.length before_ctxt) before_pis after_pis ws entries
       (Core.Tiling.PL.ip_nth_ext ip2) entry2 class_layout
       Hshape_entries Hentry2 Hidentity2 Hclass_layout2)
    as Hshape_at2.
  (* Supply common-layout and common-recipe callbacks to the Core bridge. *)
  assert
    (Hsame_layout :
       forall layout1 layout2,
         nth_error
           (phase_scalar_layouts entries)
           (Core.Tiling.PL.ip_nth_ext ip1) = Some layout1 ->
         nth_error
           (phase_scalar_layouts entries)
           (Core.Tiling.PL.ip_nth_ext ip2) = Some layout2 ->
         layout1 = layout2).
  {
    intros layout1 layout2 Hlayout1 Hlayout2.
    rewrite Hclass_layout1 in Hlayout1.
    rewrite Hclass_layout2 in Hlayout2.
    congruence.
  }
  assert
    (Hsame_recipe :
       forall witness1 witness2,
         nth_error ws (Core.Tiling.PL.ip_nth_ext ip1) = Some witness1 ->
         nth_error ws (Core.Tiling.PL.ip_nth_ext ip2) = Some witness2 ->
         Core.tile_sizes_of_witness witness1 =
         Core.tile_sizes_of_witness witness2).
  {
    intros witness1 witness2 Hwitness1 Hwitness2.
    rewrite Hw1 in Hwitness1.
    rewrite Hw2 in Hwitness2.
    inversion Hwitness1; inversion Hwitness2; subst.
    exact Hclass_sizes.
  }
  (* Core identifies the decreasing active component; the checker certifies it. *)
  destruct
    (Core.scalar_aware_pair_local_reversal_bridge_wf_with_env_len
       before_pis before_ctxt before_vars after_pis ws
       (phase_scalar_layouts entries) envv
       flat ip1 ip2
       Hlen_env Hsource Hwf_before Hlayouts_len
       Hflat Hin1 Hin2 Hold Hnew
       Hshape_at1 Hshape_at2 Hsame_layout Hsame_recipe)
    as [layout [pi1 [pi2 [dim
         [Hlayout1 [Hlayout2
         [Hpi1 [Hpi2 [Hdim Hactive]]]]]]]]].
  unfold pinstr_list_phase_scalar_componentwise_permutable
    in Hcomponentwise.
  eapply
    (Hcomponentwise
       flat ip1 ip2 pi1 pi2 layout dim);
    eauto.
Qed.

Lemma checked_tiling_sourceb_phase_scalar_direct_correct_same_ctxt :
  forall before_pis before_ctxt before_vars after_pis ws st1 st2,
    Forall
      (Core.Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    Forall
      (Core.Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      after_pis ->
    mayReturn
      (checked_tiling_sourceb_phase_scalar_direct
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars) ws)
      true ->
    Core.Tiling.PL.instance_list_semantics
      (after_pis, before_ctxt, before_vars) st1 st2 ->
    exists st2',
      Core.Tiling.PL.instance_list_semantics
        (before_pis, before_ctxt, before_vars) st1 st2' /\
      State.eq st2 st2'.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws st1 st2
         Hwf_before Hwf_after Hcheck Hsem.
  destruct
    (checked_tiling_sourceb_phase_scalar_direct_true_inv
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars ws Hcheck)
    as [entries [Hsource _]].
  eapply
    (Core.tiling_sourceb_validate_correct_with_reordering
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars)
       ws [] st1 st2).
  - exact Hsource.
  - simpl.
    intros envv Hlen_env.
    eapply
      (checked_tiling_sourceb_phase_scalar_direct_reordering_safe
         before_pis before_ctxt before_vars after_pis ws envv);
      eauto.
  - exact Hsem.
Qed.

(** Recipe-size equality is class-local.  Two-level witnesses store root and
    child links alternately, so the existing flat size key identifies both
    quotient stages without strengthening equality across different phases. *)
Fixpoint phase_second_root_sizes (sizes: list Z) : list Z :=
  match sizes with
  | root :: _ :: rest => root :: phase_second_root_sizes rest
  | _ => []
  end.

Fixpoint phase_second_child_sizes (sizes: list Z) : list Z :=
  match sizes with
  | _ :: child :: rest => child :: phase_second_child_sizes rest
  | _ => []
  end.

Lemma phase_second_recipe_sizes_of_spec :
  forall point_dim prefix_len links recipe,
    Core.second_level_band_recipe_spec point_dim prefix_len links recipe ->
    Core.slbr_root_sizes recipe =
      phase_second_root_sizes (List.map tl_tile_size links) /\
    Core.slbr_child_sizes recipe =
      phase_second_child_sizes (List.map tl_tile_size links).
Proof.
  intros point_dim prefix_len links recipe Hspec.
  induction Hspec; cbn.
  - split; reflexivity.
  - destruct IHHspec as [Hroot Hchild].
    rewrite Hroot, Hchild. split; reflexivity.
Qed.

Lemma phase_second_recipe_sizes_eq :
  forall w1 w2 recipe1 recipe2,
    Core.second_level_band_recipe_of_witness w1 = Some recipe1 ->
    Core.second_level_band_recipe_of_witness w2 = Some recipe2 ->
    Core.tile_sizes_of_witness w1 = Core.tile_sizes_of_witness w2 ->
    Core.slbr_root_sizes recipe1 = Core.slbr_root_sizes recipe2 /\
    Core.slbr_child_sizes recipe1 = Core.slbr_child_sizes recipe2.
Proof.
  intros w1 w2 recipe1 recipe2 Hparse1 Hparse2 Hsizes.
  destruct (Core.second_level_band_recipe_of_witness_sound _ _ Hparse1)
    as [_ Hspec1].
  destruct (Core.second_level_band_recipe_of_witness_sound _ _ Hparse2)
    as [_ Hspec2].
  destruct (phase_second_recipe_sizes_of_spec _ _ _ _ Hspec1)
    as [Hroot1 Hchild1].
  destruct (phase_second_recipe_sizes_of_spec _ _ _ _ Hspec2)
    as [Hroot2 Hchild2].
  unfold Core.tile_sizes_of_witness in Hsizes.
  rewrite Hroot1, Hroot2, Hchild1, Hchild2, Hsizes.
  split; reflexivity.
Qed.

Record phase_second_entry_shape
    (env_size: nat) (before_pi after_pi: Core.Tiling.PL.PolyInstr)
    (w: statement_tiling_witness) (entry: phase_scalar_entry) : Prop := {
  pses_before_head : pinstr_head_constant before_pi = Some (pse_phase entry);
  pses_after_head : pinstr_head_constant after_pi = Some (pse_phase entry);
  pses_tiled : pse_identity entry = false ->
    Core.sabl_start (pse_layout entry) = 1%nat /\
    Core.scalar_aware_second_level_entry_shape
      env_size (pse_layout entry) before_pi after_pi w;
  pses_identity : pse_identity entry = true ->
    stw_links w = [] /\
    Core.schedule_matches_with_trailing_zero_padding
      (Core.Tiling.lift_schedule_after_env O env_size
        (Core.Tiling.PL.pi_schedule before_pi))
      (Core.Tiling.PL.pi_schedule after_pi);
  pses_sizes : pse_sizes entry = Core.tile_sizes_of_witness w
}.

Definition infer_phase_second_entry
    (env_size: nat) (before_pi after_pi: Core.Tiling.PL.PolyInstr)
    (w: statement_tiling_witness) : option phase_scalar_entry :=
  match pinstr_head_constant before_pi, pinstr_head_constant after_pi with
  | Some phase, Some after_phase =>
    if Z.eqb phase after_phase then
      match stw_links w with
      | [] =>
        if Core.check_schedule_with_trailing_zero_paddingb
          (Core.Tiling.lift_schedule_after_env O env_size
            (Core.Tiling.PL.pi_schedule before_pi))
          (Core.Tiling.PL.pi_schedule after_pi)
        then Some {| pse_phase := phase; pse_identity := true;
                     pse_layout := identity_phase_scalar_layout; pse_sizes := [] |}
        else None
      | _ :: _ =>
        match Core.infer_scalar_aware_second_level_band_layout env_size before_pi w with
        | Some layout =>
          if Nat.eqb (Core.sabl_start layout) 1%nat &&
             Core.check_scalar_aware_second_level_entry_shapeb
               env_size layout before_pi after_pi w
          then Some {| pse_phase := phase; pse_identity := false;
                       pse_layout := layout; pse_sizes := Core.tile_sizes_of_witness w |}
          else None
        | None => None
        end
      end
    else None
  | _, _ => None
  end.

Lemma infer_phase_second_entry_sound :
  forall env_size before_pi after_pi w entry,
    infer_phase_second_entry env_size before_pi after_pi w = Some entry ->
    phase_second_entry_shape env_size before_pi after_pi w entry.
Proof.
  intros env_size before_pi after_pi w entry H.
  unfold infer_phase_second_entry in H.
  destruct (pinstr_head_constant before_pi) as [phase|] eqn:Hbefore;
    [|discriminate].
  destruct (pinstr_head_constant after_pi) as [after_phase|] eqn:Hafter;
    [|discriminate].
  destruct (Z.eqb phase after_phase) eqn:Hphase; [|discriminate].
  apply Z.eqb_eq in Hphase. subst after_phase.
  destruct (stw_links w) as [|link links] eqn:Hlinks.
  - destruct (Core.check_schedule_with_trailing_zero_paddingb _ _) eqn:Hschedule;
      [|discriminate].
    inversion H; subst entry. constructor; cbn.
    + exact Hbefore.
    + exact Hafter.
    + discriminate.
    + intros _. split; [exact Hlinks|].
      eapply Core.check_schedule_with_trailing_zero_paddingb_sound; eauto.
    + unfold Core.tile_sizes_of_witness. rewrite Hlinks. reflexivity.
  - destruct (Core.infer_scalar_aware_second_level_band_layout env_size before_pi w)
      as [layout|] eqn:Hlayout; [|discriminate].
    destruct (Nat.eqb (Core.sabl_start layout) 1%nat &&
      Core.check_scalar_aware_second_level_entry_shapeb
        env_size layout before_pi after_pi w) eqn:Hcheck; [|discriminate].
    apply andb_true_iff in Hcheck. destruct Hcheck as [Hstart Hshape].
    inversion H; subst entry. constructor; cbn.
    + exact Hbefore.
    + exact Hafter.
    + intros _. split.
      * apply Nat.eqb_eq. exact Hstart.
      * eapply Core.check_scalar_aware_second_level_entry_shapeb_sound; eauto.
    + discriminate.
    + reflexivity.
Qed.

Lemma phase_second_entry_classification :
  forall env_size before_pi after_pi w entry,
    phase_second_entry_shape env_size before_pi after_pi w entry ->
    phase_scalar_classification_shape env_size before_pi after_pi w entry.
Proof.
  intros env_size before_pi after_pi w entry Hshape.
  destruct Hshape as [Hbefore Hafter Htiled Hidentity Hsizes].
  constructor.
  - exact Hbefore.
  - intro point.
    exists (skipn 1 (affine_product (Core.Tiling.PL.pi_schedule after_pi) point)).
    rewrite (Mixed.schedule_head_constant_lift_sound _ _ _ _ _ Hbefore).
    rewrite <- (Mixed.schedule_head_constant_sound _ _ Hafter point).
    rewrite firstn_skipn. apply is_eq_reflexive.
  - intros Hid point. destruct (Hidentity Hid) as [Hlinks Hschedule].
    rewrite Hlinks. cbn.
    eapply Core.schedule_matches_with_symmetric_trailing_zero_padding_affine_product_is_eq.
    left. exact Hschedule.
  - intros _. exact Hsizes.
Qed.

Inductive phase_second_shape_entries (env_size: nat) :
    list Core.Tiling.PL.PolyInstr -> list Core.Tiling.PL.PolyInstr ->
    list statement_tiling_witness -> list phase_scalar_entry -> Prop :=
| PhaseSecondShapeEntriesNil : phase_second_shape_entries env_size [] [] [] []
| PhaseSecondShapeEntriesCons : forall bp ap w entry bps aps ws entries,
    phase_second_entry_shape env_size bp ap w entry ->
    phase_second_shape_entries env_size bps aps ws entries ->
    phase_second_shape_entries env_size (bp :: bps) (ap :: aps)
      (w :: ws) (entry :: entries).

Fixpoint infer_phase_second_shape_entries
    (env_size: nat) (before_pis after_pis: list Core.Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness) : option (list phase_scalar_entry) :=
  match before_pis, after_pis, ws with
  | [], [], [] => Some []
  | bp :: bps, ap :: aps, w :: ws' =>
    match infer_phase_second_entry env_size bp ap w,
          infer_phase_second_shape_entries env_size bps aps ws' with
    | Some entry, Some entries => Some (entry :: entries)
    | _, _ => None
    end
  | _, _, _ => None
  end.

Lemma infer_phase_second_shape_entries_sound :
  forall env_size bps aps ws entries,
    infer_phase_second_shape_entries env_size bps aps ws = Some entries ->
    phase_second_shape_entries env_size bps aps ws entries.
Proof.
  intros env_size bps. induction bps as [|bp bps IH];
    intros aps ws entries H; destruct aps as [|ap aps];
    destruct ws as [|w ws]; cbn in H; try discriminate.
  - inversion H; constructor.
  - destruct (infer_phase_second_entry env_size bp ap w) as [entry|] eqn:Hentry;
      [|discriminate].
    destruct (infer_phase_second_shape_entries env_size bps aps ws)
      as [rest|] eqn:Hrest; [|discriminate].
    inversion H; subst entries. constructor.
    + eapply infer_phase_second_entry_sound; eauto.
    + eapply IH; eauto.
Qed.

Lemma phase_second_shape_entries_lengths :
  forall env_size bps aps ws entries,
    phase_second_shape_entries env_size bps aps ws entries ->
    List.length bps = List.length aps /\
    List.length bps = List.length ws /\ List.length bps = List.length entries.
Proof.
  intros env_size bps aps ws entries H. induction H; cbn; lia.
Qed.

Lemma phase_second_shape_entries_nth :
  forall env_size bps aps ws entries n bp ap w entry,
    phase_second_shape_entries env_size bps aps ws entries ->
    nth_error bps n = Some bp -> nth_error aps n = Some ap ->
    nth_error ws n = Some w -> nth_error entries n = Some entry ->
    phase_second_entry_shape env_size bp ap w entry.
Proof.
  intros env_size bps aps ws entries n bp ap w entry H.
  revert n bp ap w entry. induction H; intros n bp' ap' w' entry' Hb Ha Hw He;
    destruct n; cbn in *; try discriminate.
  - inversion Hb; inversion Ha; inversion Hw; inversion He; subst. assumption.
  - eapply IHphase_second_shape_entries; eauto.
Qed.

Lemma phase_second_shape_classification :
  forall env_size bps aps ws entries,
    phase_second_shape_entries env_size bps aps ws entries ->
    phase_scalar_classification_shapes env_size bps aps ws entries.
Proof.
  intros env_size bps aps ws entries H. split.
  - destruct (phase_second_shape_entries_lengths _ _ _ _ _ H) as [_ [_ Hlen]].
    exact Hlen.
  - intros n bp ap w entry Hb Ha Hw He.
    eapply phase_second_entry_classification.
    eapply phase_second_shape_entries_nth; eauto.
Qed.

Definition infer_pprog_phase_second_shape
    (before after: Core.Tiling.PL.t) (ws: list statement_tiling_witness)
    : option (list phase_scalar_entry) :=
  let '(bps, bc, bv) := before in let '(aps, ac, av) := after in
  if Core.TilingCheck.ctxt_eqb bc ac && Core.TilingCheck.ctxt_ty_eqb bv av then
    match infer_phase_second_shape_entries (List.length bc) bps aps ws with
    | Some entries =>
      if check_phase_scalar_entries_consistentb entries then Some entries else None
    | None => None
    end
  else None.

Lemma infer_pprog_phase_second_shape_sound :
  forall bps bc bv aps ac av ws entries,
    infer_pprog_phase_second_shape (bps, bc, bv) (aps, ac, av) ws = Some entries ->
    phase_second_shape_entries (List.length bc) bps aps ws entries /\
    phase_scalar_entries_consistent entries.
Proof.
  intros bps bc bv aps ac av ws entries H.
  unfold infer_pprog_phase_second_shape in H.
  destruct (Core.TilingCheck.ctxt_eqb bc ac && Core.TilingCheck.ctxt_ty_eqb bv av);
    [|discriminate].
  destruct (infer_phase_second_shape_entries (List.length bc) bps aps ws)
    as [found|] eqn:Hfound; [|discriminate].
  destruct (check_phase_scalar_entries_consistentb found) eqn:Hconsistent;
    [|discriminate].
  inversion H; subst entries. split.
  - eapply infer_phase_second_shape_entries_sound; eauto.
  - eapply check_phase_scalar_entries_consistentb_sound; eauto.
Qed.

Definition checked_tiling_sourceb_phase_second_direct
    (before after: Core.Tiling.PL.t) (ws: list statement_tiling_witness) : imp bool :=
  let '(bps, bc, _) := before in let '(aps, _, _) := after in
  if Core.TilingCheck.check_pprog_tiling_sourceb before after ws then
    match infer_pprog_phase_second_shape before after ws with
    | Some entries => check_pprog_phase_scalar_components_direct
        (List.length bc) bps aps ws (phase_scalar_layouts entries)
    | None => pure false
    end
  else pure false.

Lemma checked_tiling_sourceb_phase_second_direct_true_inv :
  forall bps bc bv aps ac av ws,
    mayReturn (checked_tiling_sourceb_phase_second_direct
      (bps, bc, bv) (aps, ac, av) ws) true ->
    exists entries,
      Core.TilingCheck.check_pprog_tiling_sourceb
        (bps, bc, bv) (aps, ac, av) ws = true /\
      infer_pprog_phase_second_shape (bps, bc, bv) (aps, ac, av) ws = Some entries /\
      mayReturn (check_pprog_phase_scalar_components_direct
        (List.length bc) bps aps ws (phase_scalar_layouts entries)) true.
Proof.
  intros bps bc bv aps ac av ws H.
  unfold checked_tiling_sourceb_phase_second_direct in H.
  destruct (Core.TilingCheck.check_pprog_tiling_sourceb _ _ ws) eqn:Hsource;
    [|apply mayReturn_pure in H; discriminate].
  destruct (infer_pprog_phase_second_shape _ _ ws) as [entries|] eqn:Hshape;
    [|apply mayReturn_pure in H; discriminate].
  exists entries. split; [reflexivity|]. split; [reflexivity|exact H].
Qed.

Local Lemma phase_second_tiled_shape_at :
  forall env_size bps aps ws entries n entry,
    phase_second_shape_entries env_size bps aps ws entries ->
    nth_error entries n = Some entry -> pse_identity entry = false ->
    forall bp ap w layout,
      nth_error bps n = Some bp -> nth_error aps n = Some ap ->
      nth_error ws n = Some w ->
      nth_error (phase_scalar_layouts entries) n = Some layout ->
      Core.scalar_aware_second_level_entry_shape env_size layout bp ap w.
Proof.
  intros env_size bps aps ws entries n entry Hshapes Hentry Hid
    bp ap w layout Hb Ha Hw Hlayout.
  pose proof (phase_second_shape_entries_nth
    _ _ _ _ _ _ _ _ _ _ Hshapes Hb Ha Hw Hentry) as Hshape.
  destruct (pses_tiled _ _ _ _ _ Hshape Hid) as [_ Htiled].
  pose proof (nth_error_phase_scalar_layouts _ _ _ Hentry) as Hentry_layout.
  rewrite Hlayout in Hentry_layout. inversion Hentry_layout; subst layout.
  exact Htiled.
Qed.

Lemma checked_tiling_sourceb_phase_second_direct_reordering_safe :
  forall bps bc bv aps ws envv,
    List.length bc = List.length envv ->
    Forall (Core.Tiling.PL.wf_pinstr_tiling bc bv) bps ->
    Forall (Core.Tiling.PL.wf_pinstr_tiling bc bv) aps ->
    mayReturn (checked_tiling_sourceb_phase_second_direct
      (bps, bc, bv) (aps, bc, bv) ws) true ->
    Core.pprog_tiling_reordering_safe envv bps aps ws [].
Proof.
  intros bps bc bv aps ws envv Henv Hwf_before Hwf_after Hcheck.
  destruct (checked_tiling_sourceb_phase_second_direct_true_inv
    _ _ _ _ _ _ _ Hcheck) as [entries [Hsource [Hinfer Hcomponents]]].
  destruct (infer_pprog_phase_second_shape_sound _ _ _ _ _ _ _ _ Hinfer)
    as [Hshapes Hconsistent].
  destruct (phase_second_shape_entries_lengths _ _ _ _ _ Hshapes)
    as [_ [_ Hentries_len]].
  assert (Hlayouts_len : List.length (phase_scalar_layouts entries) = List.length bps).
  { unfold phase_scalar_layouts. rewrite map_length. symmetry. exact Hentries_len. }
  pose proof (Core.TilingCheck.check_pprog_tiling_sourceb_sound
    _ _ _ Hsource) as [Hprog [_ [Hwf_ws [_ Hdepths]]]].
  assert (Hwits : Forall2 Core.Tiling.after_matches_tiling_witness aps ws).
  { eapply Core.tiling_rel_pprog_structure_source_after_matches; eauto. }
  assert (Hcomposed_wf : Forall (Core.Tiling.PL.wf_pinstr_ext_tiling bc)
    (Core.Tiling.compose_tiling_pinstrs_ext_from_after (List.length bc) bps aps ws)).
  { eapply Core.compose_tiling_pinstrs_ext_from_after_wf_tiling; eauto. }
  assert (Hcomponentwise : pinstr_list_phase_scalar_componentwise_permutable
    envv bps aps ws (phase_scalar_layouts entries)).
  { eapply (check_pprog_phase_scalar_components_direct_sound
      bc envv bps aps ws (phase_scalar_layouts entries)); eauto. }
  unfold Core.pprog_tiling_reordering_safe, Core.pprog_permutable_tiling_bands.
  intros flat ip1 ip2 Hflat Hin1 Hin2 Hold Hnew.
  destruct (phase_scalar_reversal_same_class_abstract
    bps bc bv aps ws entries envv flat ip1 ip2 Henv Hsource
    (phase_second_shape_classification _ _ _ _ _ Hshapes)
    Hconsistent Hflat Hin1 Hin2 Hold Hnew)
    as [class_layout [w1 [w2 [entry1 [entry2
      [He1 [He2 [Hid1 [Hid2 [Hl1 [Hl2 [Hw1 [Hw2 Hsizes]]]]]]]]]]]]].
  pose proof (phase_second_tiled_shape_at
    _ _ _ _ _ _ _ Hshapes He1 Hid1) as Hshape1.
  pose proof (phase_second_tiled_shape_at
    _ _ _ _ _ _ _ Hshapes He2 Hid2) as Hshape2.
  assert (Hsame_layout : forall layout1 layout2,
    nth_error (phase_scalar_layouts entries) (Core.Tiling.PL.ip_nth_ext ip1) = Some layout1 ->
    nth_error (phase_scalar_layouts entries) (Core.Tiling.PL.ip_nth_ext ip2) = Some layout2 ->
    layout1 = layout2).
  { intros layout1 layout2 H1 H2. rewrite Hl1 in H1. rewrite Hl2 in H2. congruence. }
  assert (Hsame_recipe : forall witness1 witness2 recipe1 recipe2,
    nth_error ws (Core.Tiling.PL.ip_nth_ext ip1) = Some witness1 ->
    nth_error ws (Core.Tiling.PL.ip_nth_ext ip2) = Some witness2 ->
    Core.second_level_band_recipe_of_witness witness1 = Some recipe1 ->
    Core.second_level_band_recipe_of_witness witness2 = Some recipe2 ->
    Core.slbr_root_sizes recipe1 = Core.slbr_root_sizes recipe2 /\
    Core.slbr_child_sizes recipe1 = Core.slbr_child_sizes recipe2).
  { intros witness1 witness2 recipe1 recipe2 H1 H2 Hparse1 Hparse2.
    rewrite Hw1 in H1. rewrite Hw2 in H2. inversion H1; inversion H2; subst.
    eapply phase_second_recipe_sizes_eq; eauto. }
  destruct (Core.scalar_aware_second_level_pair_local_reversal_bridge_wf_with_env_len
    bps bc bv aps ws (phase_scalar_layouts entries) envv flat ip1 ip2
    Henv Hsource Hwf_before Hlayouts_len Hflat Hin1 Hin2 Hold Hnew
    Hshape1 Hshape2 Hsame_layout Hsame_recipe)
    as [layout [pi1 [pi2 [dim [Hlayout1 [Hlayout2 [Hpi1 [Hpi2 [Hdim Hactive]]]]]]]]].
  eapply (Hcomponentwise flat ip1 ip2 pi1 pi2 layout dim); eauto.
Qed.

Lemma checked_tiling_sourceb_phase_second_direct_correct_same_ctxt :
  forall bps bc bv aps ws st1 st2,
    Forall (Core.Tiling.PL.wf_pinstr_tiling bc bv) bps ->
    Forall (Core.Tiling.PL.wf_pinstr_tiling bc bv) aps ->
    mayReturn (checked_tiling_sourceb_phase_second_direct
      (bps, bc, bv) (aps, bc, bv) ws) true ->
    Core.Tiling.PL.instance_list_semantics (aps, bc, bv) st1 st2 ->
    exists st2', Core.Tiling.PL.instance_list_semantics (bps, bc, bv) st1 st2' /\
      State.eq st2 st2'.
Proof.
  intros bps bc bv aps ws st1 st2 Hwf_before Hwf_after Hcheck Hsem.
  destruct (checked_tiling_sourceb_phase_second_direct_true_inv
    _ _ _ _ _ _ _ Hcheck) as [entries [Hsource _]].
  eapply (Core.tiling_sourceb_validate_correct_with_reordering
    (bps, bc, bv) (aps, bc, bv) ws [] st1 st2).
  - exact Hsource.
  - cbn. intros envv Henv.
    eapply checked_tiling_sourceb_phase_second_direct_reordering_safe; eauto.
  - exact Hsem.
Qed.

Definition checked_tiling_sourceb_phase_scalar_extended_direct
    (before after: Core.Tiling.PL.t) (ws: list statement_tiling_witness) : imp bool :=
  BIND second_ok <- checked_tiling_sourceb_phase_second_direct before after ws -;
  if second_ok then pure true
  else checked_tiling_sourceb_phase_scalar_direct before after ws.

Lemma checked_tiling_sourceb_phase_scalar_extended_direct_sourceb_true :
  forall before after ws,
    mayReturn (checked_tiling_sourceb_phase_scalar_extended_direct before after ws) true ->
    Core.TilingCheck.check_pprog_tiling_sourceb before after ws = true.
Proof.
  intros [[bps bc] bv] [[aps ac] av] ws H.
  unfold checked_tiling_sourceb_phase_scalar_extended_direct in H.
  bind_imp_destruct H second_ok Hsecond. destruct second_ok.
  - destruct (checked_tiling_sourceb_phase_second_direct_true_inv
      _ _ _ _ _ _ _ Hsecond) as [entries [Hsource _]]. exact Hsource.
  - destruct (checked_tiling_sourceb_phase_scalar_direct_true_inv
      _ _ _ _ _ _ _ H) as [entries [Hsource _]]. exact Hsource.
Qed.

Lemma checked_tiling_sourceb_phase_scalar_extended_direct_correct_same_ctxt :
  forall bps bc bv aps ws st1 st2,
    Forall (Core.Tiling.PL.wf_pinstr_tiling bc bv) bps ->
    Forall (Core.Tiling.PL.wf_pinstr_tiling bc bv) aps ->
    mayReturn (checked_tiling_sourceb_phase_scalar_extended_direct
      (bps, bc, bv) (aps, bc, bv) ws) true ->
    Core.Tiling.PL.instance_list_semantics (aps, bc, bv) st1 st2 ->
    exists st2', Core.Tiling.PL.instance_list_semantics (bps, bc, bv) st1 st2' /\
      State.eq st2 st2'.
Proof.
  intros bps bc bv aps ws st1 st2 Hwf_before Hwf_after Hcheck Hsem.
  unfold checked_tiling_sourceb_phase_scalar_extended_direct in Hcheck.
  bind_imp_destruct Hcheck second_ok Hsecond. destruct second_ok.
  - eapply checked_tiling_sourceb_phase_second_direct_correct_same_ctxt; eauto.
  - eapply checked_tiling_sourceb_phase_scalar_direct_correct_same_ctxt; eauto.
Qed.

End TilingBandPhaseScalarValidator.

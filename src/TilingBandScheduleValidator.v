Require Import Bool.
Require Import List.
Require Import ZArith.
Require Import Lia.
Require Import Sorting.Sorted.
Import ListNotations.

Require Import Linalg.
Require Import Misc.
Require Import PolyBase.
Require Import PolyLang.
Require Import PolyOperations.
Require Import TilingRelation.
Require Import TilingBoolChecker.
Require Import TilingWitness.
Require Import PointWitness.
Require Import ParallelValidator.
Require Import TilingValidator.
Require Import TilingCanonicalScheduleValidator.
Require Import PolIRs.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Module TilingBandScheduleValidator (PolIRs: POLIRS).

Module Base := TilingValidator PolIRs.
Module Canonical := TilingCanonicalScheduleValidator PolIRs.
Module Instr := PolIRs.Instr.
Module State := PolIRs.State.
Module TilingCheck := Base.TilingCheck.
Module Tiling := Base.Tiling.
Module TilingPolIRs := Base.TilingPolIRs.
Module ParallelCore := ParallelValidator PolIRs.
(** [BandAffine] supplies the integer guard and access-conflict kernel used by
    the direct band checker.  No call to [validate] or [validate_tiling] is
    part of the runtime direct-band route. *)
Module BandAffine := Base.TilingVal.

(** This file proves one implication in several increasingly general layout
    classes:

      accepted component checks + recognized target layout
        -> every target reversal decreases a checked band component
        -> the reversed pair is permutable
        -> tiling preserves the source semantics.

    The sections below follow that proof from the affine rows named by a
    witness, through executable bad-pair checks, to layout-specific reversal
    bridges.  The final correctness lemmas merely compose those two halves
    with [TilingValidator]. *)

(** Band permutability and scalar phases.

    A plain loop band requires nonnegative dependence distances in every
    component.  Pluto's scalar-aware detector also permits negative distances
    when an earlier scalar phase already carries the dependence.  The guarded
    checks below preserve that distinction: they restrict pairs to an equal
    outer prefix and account for the preceding scalar coordinates.

    Each layout proof shows that every target reversal activates one of these
    checked component decreases.  Phase-local composition additionally proves
    that different phases retain their order and that untiled entries retain
    their complete schedules.  Dependencies across bands or untiled entries
    are therefore covered by the proof, rather than silently omitted.

    These are sufficient band conditions, not a completeness theorem for every
    legal fixed tiling schedule. *)

(** * Reader map

    The main direct route is organized as follows:

    - [CommonBandInfrastructure] and [SecondLevelShapeRecognition] recognize
      ordinary and nested strip-mined layouts.
    - [ProjectedScheduleBridge] relates witness rows to extended instruction
      points.
    - [CommonBandDirectChecker] proves the executable affine conflict checks.
      Its subsection "Compatibility reduction through the affine checker" is
      a legacy route; the current direct proof resumes at "Direct checker
      soundness".
    - [PerStatementBandChecker] lifts pair checks to statement lists.
    - [SemanticBandKernel] defines
      [pinstr_list_semantic_componentwise_permutable], the central semantic
      component property.
    - [ProgramWideSemanticReconstruction] uses
      [semantic_componentwise_permutable_implies_reordering_safe] and finishes
      at [checked_tiling_sourceb_semantic_band_direct_correct_same_ctxt].
    - [ScalarAwareBands] and [PhaseAwareSemanticBands] generalize the same
      route; their final endpoints are
      [checked_tiling_sourceb_scalar_aware_direct_correct_same_ctxt] and
      [checked_tiling_sourceb_phase_semantic_band_direct_correct_same_ctxt].

    The early aliases [pprog_permutable_tiling_bands] and
    [pprog_tiling_reordering_safe] describe the projected-schedule bridge, not
    the later semantic-component property. *)

(** * Common band witnesses and row arithmetic *)

Section CommonBandInfrastructure.

Record pinstr_tiling_band := {
  ptb_start : nat;
  ptb_len : nat;
}.

Definition pinstr_tiling_band_eqb
    (b1 b2: pinstr_tiling_band) : bool :=
  Nat.eqb (ptb_start b1) (ptb_start b2) &&
  Nat.eqb (ptb_len b1) (ptb_len b2).

Lemma pinstr_tiling_band_eqb_eq :
  forall b1 b2,
    pinstr_tiling_band_eqb b1 b2 = true ->
    b1 = b2.
Proof.
  intros [s1 l1] [s2 l2] Heq.
  unfold pinstr_tiling_band_eqb in Heq.
  apply andb_true_iff in Heq.
  destruct Heq as [Hs Hl].
  apply Nat.eqb_eq in Hs.
  apply Nat.eqb_eq in Hl.
  simpl in *.
  subst s2 l2.
  reflexivity.
Qed.

Definition common_tiling_band
    (bands: list pinstr_tiling_band)
    (band: pinstr_tiling_band) : Prop :=
  Forall (fun b => b = band) bands.

Definition infer_common_tiling_band
    (bands: list pinstr_tiling_band) : option pinstr_tiling_band :=
  match bands with
  | [] => None
  | band :: bands' =>
      if forallb (pinstr_tiling_band_eqb band) bands'
      then Some band
      else None
  end.

Lemma infer_common_tiling_band_sound :
  forall bands band,
    infer_common_tiling_band bands = Some band ->
    common_tiling_band bands band.
Proof.
  intros bands band Hinfer.
  unfold infer_common_tiling_band in Hinfer.
  destruct bands as [|band0 bands']; try discriminate.
  destruct (forallb (pinstr_tiling_band_eqb band0) bands') eqn:Hforall;
    inversion Hinfer; subst; clear Hinfer.
  constructor; [reflexivity|].
  eapply Forall_forall.
  intros b Hb.
  eapply forallb_forall with (x := b) in Hforall; eauto.
  symmetry.
  eapply pinstr_tiling_band_eqb_eq; exact Hforall.
Qed.

Lemma common_tiling_band_nth_error :
  forall bands band n b,
    common_tiling_band bands band ->
    nth_error bands n = Some b ->
    b = band.
Proof.
  intros bands band n.
  revert bands band.
  induction n as [|n IH]; intros bands band b Hcommon Hnth.
  - destruct bands as [|b0 bands']; simpl in Hnth; try discriminate.
    inversion Hcommon; subst.
    inversion Hnth; subst.
    reflexivity.
  - destruct bands as [|b0 bands']; simpl in Hnth; try discriminate.
    inversion Hcommon; subst.
    eapply IH; eauto.
Qed.

Fixpoint listz_strict_eqb (xs ys: list Z) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => Z.eqb x y && listz_strict_eqb xs' ys'
  | _, _ => false
  end.

Lemma listz_strict_eqb_eq :
  forall xs ys,
    listz_strict_eqb xs ys = true ->
    xs = ys.
Proof.
  induction xs as [|x xs IH]; intros ys Heq.
  - destruct ys; simpl in Heq; try discriminate; reflexivity.
  - destruct ys as [|y ys]; simpl in Heq; try discriminate.
    apply andb_true_iff in Heq.
    destruct Heq as [Hxy Hrest].
    apply Z.eqb_eq in Hxy.
    f_equal.
    + exact Hxy.
    + eapply IH.
      exact Hrest.
Qed.

Definition schedule_row_of_tile_link_base
    (prefix_len: nat) (link: tile_link) : list Z * Z :=
  let expr := tl_expr link in
  (ae_param_coeffs expr ++ skipn prefix_len (ae_var_coeffs expr), ae_const expr).

Fixpoint schedule_rows_of_links_aux
    (prefix_len: nat)
    (links: list tile_link) : option Schedule :=
  match links with
  | [] => Some []
  | link :: links' =>
      if listz_strict_eqb
           (firstn prefix_len (ae_var_coeffs (tl_expr link)))
           (repeat 0%Z prefix_len)
      then
        match schedule_rows_of_links_aux (S prefix_len) links' with
        | Some rows =>
            Some (schedule_row_of_tile_link_base prefix_len link :: rows)
        | None => None
        end
      else None
  end.

Definition schedule_rows_of_links
    (w: statement_tiling_witness) : option Schedule :=
  schedule_rows_of_links_aux 0 (stw_links w).

Definition pinstr_tiling_band_matches
    (before: Tiling.PL.PolyInstr)
    (w: statement_tiling_witness)
    (band: pinstr_tiling_band) : Prop :=
  match schedule_rows_of_links w with
  | Some rows =>
      ptb_len band = List.length (stw_links w) /\
      firstn (ptb_len band)
        (skipn (ptb_start band) (Tiling.PL.pi_schedule before)) =
      rows
  | None => False
  end.

Definition stripmine_schedule_after_env
    (env_size: nat)
    (before_sched: Schedule)
    (band: pinstr_tiling_band) : Schedule :=
  let added_dims := ptb_len band in
  let lifted :=
    Tiling.lift_schedule_after_env added_dims env_size before_sched in
  let total_cols :=
    match lifted with
    | [] => (env_size + added_dims)%nat
    | (coeffs, _) :: _ => List.length coeffs
    end in
  let prefix := firstn (ptb_start band) lifted in
  let lifted_band := firstn added_dims (skipn (ptb_start band) lifted) in
  let suffix := skipn (ptb_start band + added_dims)%nat lifted in
  prefix ++
  Tiling.identity_affine_rows_from total_cols env_size added_dims ++
  lifted_band ++
  suffix.

Definition zero_schedule_row (cols: nat) : (list Z * Z) :=
  (repeat 0%Z cols, 0%Z).

Definition pad_schedule_with_zero_rows
    (sched: Schedule) (cols extra_rows: nat) : Schedule :=
  sched ++ repeat (zero_schedule_row cols) extra_rows.

Definition check_schedule_with_trailing_zero_paddingb
    (expected actual: Schedule) : bool :=
  if Nat.leb (List.length expected) (List.length actual) then
    let cols :=
      match actual with
      | [] => 0%nat
      | (coeffs, _) :: _ => List.length coeffs
      end in
    listzzs_strict_eqb
      actual
      (pad_schedule_with_zero_rows
         expected cols (List.length actual - List.length expected))
  else false.

Definition schedule_matches_with_trailing_zero_padding
    (expected actual: Schedule) : Prop :=
  exists cols extra_rows,
    actual = pad_schedule_with_zero_rows expected cols extra_rows.

Definition check_schedule_with_symmetric_trailing_zero_paddingb
    (expected actual: Schedule) : bool :=
  check_schedule_with_trailing_zero_paddingb expected actual ||
  check_schedule_with_trailing_zero_paddingb actual expected.

Definition schedule_matches_with_symmetric_trailing_zero_padding
    (expected actual: Schedule) : Prop :=
  schedule_matches_with_trailing_zero_padding expected actual \/
  schedule_matches_with_trailing_zero_padding actual expected.

Definition tile_sizes_of_witness
    (w: statement_tiling_witness) : list Z :=
  List.map tl_tile_size (stw_links w).

Fixpoint check_common_tiling_band_recipe_withb
    (sizes: list Z)
    (ws: list statement_tiling_witness) : bool :=
  match ws with
  | [] => true
  | w :: ws' =>
      listz_strict_eqb sizes (tile_sizes_of_witness w) &&
      check_common_tiling_band_recipe_withb sizes ws'
  end.

Definition check_common_tiling_band_recipeb
    (ws: list statement_tiling_witness) : bool :=
  match ws with
  | [] => true
  | w :: ws' =>
      check_common_tiling_band_recipe_withb (tile_sizes_of_witness w) ws'
  end.

Fixpoint max_tiling_band_len (bands: list pinstr_tiling_band) : nat :=
  match bands with
  | [] => O
  | band :: bands' => Nat.max (ptb_len band) (max_tiling_band_len bands')
  end.


Lemma affine_product_firstn_local :
  forall n m p,
    affine_product (firstn n m) p = firstn n (affine_product m p).
Proof.
  induction n as [|n IH]; intros m p.
  - destruct m; reflexivity.
  - destruct m as [|x m]; simpl.
    + reflexivity.
    + rewrite IH.
      reflexivity.
Qed.

Lemma affine_product_app_local_component :
  forall m1 m2 p,
    affine_product (m1 ++ m2) p =
    affine_product m1 p ++ affine_product m2 p.
Proof.
  intros m1 m2 p.
  unfold affine_product.
  rewrite List.map_app.
  reflexivity.
Qed.

Lemma affine_product_skipn_local_component :
  forall n m p,
    affine_product (skipn n m) p = skipn n (affine_product m p).
Proof.
  induction n as [|n IH]; intros m p.
  - reflexivity.
  - destruct m as [|x m]; simpl; auto.
Qed.



































Fixpoint find_schedule_block_start_aux
    (fuel start: nat)
    (sched block: Schedule) : option nat :=
  match fuel with
  | O => None
  | S fuel' =>
      if listzzs_strict_eqb block (firstn (List.length block) (skipn start sched))
      then Some start
      else find_schedule_block_start_aux fuel' (S start) sched block
  end.

Definition find_schedule_block_start
    (sched block: Schedule) : option nat :=
  find_schedule_block_start_aux (S (List.length sched)) O sched block.

Record second_level_band_recipe := {
  slbr_root_rows : Schedule;
  slbr_root_sizes : list Z;
  slbr_child_sizes : list Z;
}.

Definition second_level_child_coeffs
    (prefix_len point_dim: nat) : list Z :=
  repeat 0%Z prefix_len ++ [1%Z] ++ repeat 0%Z point_dim.

Fixpoint second_level_band_recipe_of_links_aux
    (point_dim prefix_len: nat)
    (links: list tile_link) : option second_level_band_recipe :=
  match links with
  | [] =>
      Some
        {| slbr_root_rows := [];
           slbr_root_sizes := [];
           slbr_child_sizes := [] |}
  | root :: child :: links' =>
      let root_expr := tl_expr root in
      let child_expr := tl_expr child in
      if listz_strict_eqb
           (firstn prefix_len (ae_var_coeffs root_expr))
           (repeat 0%Z prefix_len) &&
         listz_strict_eqb
           (ae_var_coeffs child_expr)
           (second_level_child_coeffs prefix_len point_dim) &&
         listz_strict_eqb
           (ae_param_coeffs child_expr)
           (repeat 0%Z (List.length (ae_param_coeffs child_expr))) &&
         Z.eqb (ae_const child_expr) 0%Z
      then
        match
          second_level_band_recipe_of_links_aux
            point_dim (prefix_len + 2)%nat links'
        with
        | Some rest =>
            Some
              {| slbr_root_rows :=
                   schedule_row_of_tile_link_base prefix_len root ::
                   slbr_root_rows rest;
                 slbr_root_sizes :=
                   tl_tile_size root :: slbr_root_sizes rest;
                 slbr_child_sizes :=
                   tl_tile_size child :: slbr_child_sizes rest |}
        | None => None
        end
      else None
  | _ => None
  end.

Definition second_level_band_recipe_of_witness
    (w: statement_tiling_witness) : option second_level_band_recipe :=
  match stw_links w with
  | [] => None
  | links => second_level_band_recipe_of_links_aux (stw_point_dim w) O links
  end.

End CommonBandInfrastructure.

(** * Ordinary and second-level layout recognition

    This section ends at [check_pprog_second_level_schedule_directb_sound] and
    the program-level ordinary layout facts. *)

Section SecondLevelShapeRecognition.

Inductive second_level_band_recipe_spec (point_dim: nat) :
    nat -> list tile_link -> second_level_band_recipe -> Prop :=
| second_level_band_recipe_spec_nil :
    forall prefix_len,
      second_level_band_recipe_spec point_dim prefix_len []
        {| slbr_root_rows := [];
           slbr_root_sizes := [];
           slbr_child_sizes := [] |}
| second_level_band_recipe_spec_cons :
    forall prefix_len root child links rest,
      firstn prefix_len (ae_var_coeffs (tl_expr root)) =
        repeat 0%Z prefix_len ->
      ae_var_coeffs (tl_expr child) =
        second_level_child_coeffs prefix_len point_dim ->
      ae_param_coeffs (tl_expr child) =
        repeat 0%Z (List.length (ae_param_coeffs (tl_expr child))) ->
      ae_const (tl_expr child) = 0%Z ->
      second_level_band_recipe_spec
        point_dim (prefix_len + 2)%nat links rest ->
      second_level_band_recipe_spec
        point_dim prefix_len (root :: child :: links)
        {| slbr_root_rows :=
             schedule_row_of_tile_link_base prefix_len root ::
             slbr_root_rows rest;
           slbr_root_sizes := tl_tile_size root :: slbr_root_sizes rest;
           slbr_child_sizes := tl_tile_size child :: slbr_child_sizes rest |}.

Lemma second_level_band_recipe_of_links_aux_sound :
  forall point_dim prefix_len links recipe,
    second_level_band_recipe_of_links_aux point_dim prefix_len links =
      Some recipe ->
    second_level_band_recipe_spec point_dim prefix_len links recipe.
Proof.
  fix IH 3.
  intros point_dim prefix_len links recipe Hparse.
  destruct links as [|root links].
  - simpl in Hparse.
    inversion Hparse; subst recipe.
    constructor.
  - destruct links as [|child links].
    { simpl in Hparse. discriminate. }
    simpl in Hparse.
    destruct
      (listz_strict_eqb
         (firstn prefix_len (ae_var_coeffs (tl_expr root)))
         (repeat 0%Z prefix_len)) eqn:Hroot; try discriminate.
    destruct
      (listz_strict_eqb
         (ae_var_coeffs (tl_expr child))
         (second_level_child_coeffs prefix_len point_dim)) eqn:Hchild_vars;
      try discriminate.
    destruct
      (listz_strict_eqb
         (ae_param_coeffs (tl_expr child))
         (repeat 0%Z (List.length (ae_param_coeffs (tl_expr child)))))
      eqn:Hchild_params; try discriminate.
    destruct (Z.eqb (ae_const (tl_expr child)) 0%Z) eqn:Hchild_const;
      try discriminate.
    destruct
      (second_level_band_recipe_of_links_aux
         point_dim (prefix_len + 2)%nat links) as [rest|] eqn:Hrest;
      try discriminate.
    inversion Hparse; subst recipe; clear Hparse.
    constructor.
    + eapply listz_strict_eqb_eq; exact Hroot.
    + eapply listz_strict_eqb_eq; exact Hchild_vars.
    + eapply listz_strict_eqb_eq; exact Hchild_params.
    + eapply Z.eqb_eq; exact Hchild_const.
    + eapply IH; exact Hrest.
Qed.

Lemma second_level_band_recipe_of_witness_sound :
  forall w recipe,
    second_level_band_recipe_of_witness w = Some recipe ->
    stw_links w <> [] /\
    second_level_band_recipe_spec (stw_point_dim w) O (stw_links w) recipe.
Proof.
  intros w recipe Hparse.
  unfold second_level_band_recipe_of_witness in Hparse.
  destruct (stw_links w) as [|link links] eqn:Hlinks.
  - discriminate.
  - split; [congruence|].
    eapply second_level_band_recipe_of_links_aux_sound.
    exact Hparse.
Qed.


Fixpoint interleave_root_child_tiles
    (roots children: list Z) : list Z :=
  match roots, children with
  | root :: roots', child :: children' =>
      root :: child :: interleave_root_child_tiles roots' children'
  | _, _ => []
  end.

Definition second_level_root_tiles
    (recipe: second_level_band_recipe)
    (params point: list Z) : list Z :=
  List.map
    (fun '(v, sz) => Z.div v sz)
    (List.combine
       (affine_product (slbr_root_rows recipe) (params ++ point))
       (slbr_root_sizes recipe)).

Definition second_level_child_tiles
    (recipe: second_level_band_recipe)
    (params point: list Z) : list Z :=
  List.map
    (fun '(v, sz) => Z.div v sz)
    (List.combine
       (second_level_root_tiles recipe params point)
       (slbr_child_sizes recipe)).

Definition second_level_schedule_tile_block
    (recipe: second_level_band_recipe)
    (params point: list Z) : list Z :=
  second_level_child_tiles recipe params point ++
  second_level_root_tiles recipe params point.

Definition second_level_schedule_interleaved_tile_block
    (recipe: second_level_band_recipe)
    (params point: list Z) : list Z :=
  interleave_root_child_tiles
    (second_level_root_tiles recipe params point)
    (second_level_child_tiles recipe params point).

Lemma affine_product_schedule_row_of_tile_link_base_second_level :
  forall prefix_len prefix point params link,
    List.length prefix = prefix_len ->
    List.length (ae_var_coeffs (tl_expr link)) =
      (prefix_len + List.length point)%nat ->
    List.length (ae_param_coeffs (tl_expr link)) = List.length params ->
    firstn prefix_len (ae_var_coeffs (tl_expr link)) =
      repeat 0%Z prefix_len ->
    affine_product [schedule_row_of_tile_link_base prefix_len link]
      (params ++ point) =
    [eval_affine (tl_expr link) (prefix ++ point) params].
Proof.
  intros prefix_len prefix point params link Hprefix Hvars Hparams Hzero.
  unfold affine_product, schedule_row_of_tile_link_base, eval_affine.
  simpl.
  rewrite <-
    (Tiling.tiling_dot_product_eq_linalg_dot_product
       (ae_param_coeffs (tl_expr link) ++
        skipn prefix_len (ae_var_coeffs (tl_expr link)))
       (params ++ point)).
  rewrite TilingWitness.dot_product_app_exact by exact Hparams.
  rewrite (TilingWitness.dot_product_split_firstn_skipn
             (ae_var_coeffs (tl_expr link)) prefix point).
  2:{ rewrite Hprefix. exact Hvars. }
  rewrite Hprefix.
  rewrite Hzero.
  rewrite TilingWitness.dot_product_repeat_zero_exact by exact Hprefix.
  simpl.
  f_equal.
  lia.
Qed.

Lemma dot_product_second_level_child_coeffs :
  forall prefix point root_value,
    dot_product
      (second_level_child_coeffs (List.length prefix) (List.length point))
      ((prefix ++ [root_value]) ++ point) = root_value.
Proof.
  induction prefix as [|x prefix IH]; intros point root_value.
  - unfold second_level_child_coeffs.
    simpl.
    rewrite TilingWitness.dot_product_repeat_zero_exact by reflexivity.
    lia.
  - unfold second_level_child_coeffs in *.
    simpl.
    eapply IH.
Qed.

Lemma eval_affine_second_level_child :
  forall child prefix point params root_value,
    ae_var_coeffs (tl_expr child) =
      second_level_child_coeffs (List.length prefix) (List.length point) ->
    ae_param_coeffs (tl_expr child) =
      repeat 0%Z (List.length params) ->
    ae_const (tl_expr child) = 0%Z ->
    eval_affine (tl_expr child) ((prefix ++ [root_value]) ++ point) params =
      root_value.
Proof.
  intros child prefix point params root_value Hvars Hparams Hconst.
  unfold eval_affine.
  rewrite Hvars, Hparams, Hconst.
  rewrite dot_product_second_level_child_coeffs.
  rewrite TilingWitness.dot_product_repeat_zero_exact by reflexivity.
  lia.
Qed.

Lemma eval_tile_links_from_second_level_recipe_spec :
  forall point_dim prefix_len links recipe,
    second_level_band_recipe_spec point_dim prefix_len links recipe ->
    forall prefix point params,
      List.length prefix = prefix_len ->
      List.length point = point_dim ->
      well_formed_tile_links prefix_len point_dim links ->
      Forall
        (fun link =>
           List.length (ae_param_coeffs (tl_expr link)) = List.length params)
        links ->
      eval_tile_links prefix point params links =
      prefix ++
      interleave_root_child_tiles
        (second_level_root_tiles recipe params point)
        (second_level_child_tiles recipe params point).
Proof.
  fix IH 3.
  intros point_dim prefix_len links recipe Hspec
         prefix point params Hprefix_len Hpoint_len Hwf Hparams.
  destruct links as [|root links].
  - inversion Hspec; subst recipe.
    simpl. now rewrite app_nil_r.
  - destruct links as [|child links].
    { inversion Hspec. }
    inversion Hspec as
      [|prefix_len0 root0 child0 links0 rest
         Hroot_zero Hchild_vars Hchild_params Hchild_const Hrest];
      subst root0 child0 links0 recipe.
    simpl in Hwf.
    destruct Hwf as [Hroot_vars [Hchild_vars_len Hwf_rest]].
    inversion Hparams as [|root0 links0 Hroot_params Hparams_tail]; subst.
    inversion Hparams_tail as
      [|child0 links0 Hchild_params_len Hparams_rest]; subst.
    set (root_tile := eval_tile_parent root (prefix ++ point) params).
    assert (Hroot_eval :
      affine_product
        [schedule_row_of_tile_link_base (List.length prefix) root]
        (params ++ point) =
      [eval_affine (tl_expr root) (prefix ++ point) params]).
    {
      eapply affine_product_schedule_row_of_tile_link_base_second_level.
      - reflexivity.
      - exact Hroot_vars.
      - exact Hroot_params.
      - exact Hroot_zero.
    }
    assert (Hchild_eval :
      eval_tile_parent child ((prefix ++ [root_tile]) ++ point) params =
      Z.div root_tile (tl_tile_size child)).
    {
      unfold eval_tile_parent.
      f_equal.
      eapply eval_affine_second_level_child.
      - exact Hchild_vars.
      - rewrite <- Hchild_params_len.
        exact Hchild_params.
      - exact Hchild_const.
    }
    assert (Hprefix_rest :
      List.length (prefix ++ [root_tile; Z.div root_tile (tl_tile_size child)]) =
      (List.length prefix + 2)%nat).
    {
      rewrite app_length.
      simpl. lia.
    }
    assert (Hwf_rest' :
      well_formed_tile_links
        (List.length prefix + 2)%nat (List.length point) links).
    {
      replace (List.length prefix + 2)%nat
        with (S (S (List.length prefix))) by lia.
      exact Hwf_rest.
    }
    pose proof
      (IH _ _ links rest Hrest
         (prefix ++ [root_tile; Z.div root_tile (tl_tile_size child)])
         point params Hprefix_rest eq_refl Hwf_rest' Hparams_rest)
      as IHrest.
    cbn [eval_tile_links].
    fold root_tile.
    rewrite Hchild_eval.
    replace
      ((prefix ++ [root_tile]) ++ [Z.div root_tile (tl_tile_size child)])
      with
      (prefix ++ [root_tile; Z.div root_tile (tl_tile_size child)]) by
      exact (app_assoc prefix [root_tile]
               [Z.div root_tile (tl_tile_size child)]).
    rewrite IHrest.
    unfold second_level_root_tiles,
           second_level_child_tiles in *.
    simpl.
    simpl in Hroot_eval.
    injection Hroot_eval as Hroot_eval_value.
    unfold root_tile, eval_tile_parent.
    rewrite <- Hroot_eval_value.
    rewrite <- app_assoc.
    reflexivity.
Qed.

Definition infer_pinstr_second_level_band
    (before: Tiling.PL.PolyInstr)
    (w: statement_tiling_witness)
    : option (pinstr_tiling_band * second_level_band_recipe) :=
  match second_level_band_recipe_of_witness w with
  | Some recipe =>
      match
        find_schedule_block_start
          (Tiling.PL.pi_schedule before)
          (slbr_root_rows recipe)
      with
      | Some start =>
          Some
            ({| ptb_start := start;
                ptb_len := List.length (slbr_root_rows recipe) |},
             recipe)
      | None => None
      end
  | None => None
  end.

Fixpoint infer_pinstr_list_second_level_bands
    (before_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    : option (list pinstr_tiling_band * list second_level_band_recipe) :=
  match before_pis, ws with
  | [], [] => Some ([], [])
  | before_pi :: before_pis', w :: ws' =>
      match infer_pinstr_second_level_band before_pi w,
            infer_pinstr_list_second_level_bands before_pis' ws' with
      | Some (band, recipe), Some (bands, recipes) =>
          Some (band :: bands, recipe :: recipes)
      | _, _ => None
      end
  | _, _ => None
  end.

Fixpoint check_band_starts_eqb
    (start: nat) (bands: list pinstr_tiling_band) : bool :=
  match bands with
  | [] => true
  | band :: bands' =>
      Nat.eqb (ptb_start band) start && check_band_starts_eqb start bands'
  end.

Definition check_common_band_startb
    (bands: list pinstr_tiling_band) : bool :=
  match bands with
  | [] => true
  | band :: bands' => check_band_starts_eqb (ptb_start band) bands'
  end.

Definition common_band_start (bands: list pinstr_tiling_band) : Prop :=
  exists start, Forall (fun band => ptb_start band = start) bands.

Fixpoint check_second_level_recipe_sizes_eqb
    (root_sizes child_sizes: list Z)
    (recipes: list second_level_band_recipe) : bool :=
  match recipes with
  | [] => true
  | recipe :: recipes' =>
      listz_strict_eqb (slbr_root_sizes recipe) root_sizes &&
      listz_strict_eqb (slbr_child_sizes recipe) child_sizes &&
      check_second_level_recipe_sizes_eqb root_sizes child_sizes recipes'
  end.

Definition check_common_second_level_recipe_sizesb
    (recipes: list second_level_band_recipe) : bool :=
  match recipes with
  | [] => true
  | recipe :: recipes' =>
      check_second_level_recipe_sizes_eqb
        (slbr_root_sizes recipe) (slbr_child_sizes recipe) recipes'
  end.

Definition common_second_level_recipe_sizes
    (recipes: list second_level_band_recipe) : Prop :=
  exists root_sizes child_sizes,
    Forall
      (fun recipe =>
         slbr_root_sizes recipe = root_sizes /\
         slbr_child_sizes recipe = child_sizes)
      recipes.

Lemma check_band_starts_eqb_sound :
  forall start bands,
    check_band_starts_eqb start bands = true ->
    Forall (fun band => ptb_start band = start) bands.
Proof.
  intros start bands Hcheck.
  induction bands as [|band bands IH]; simpl in *.
  - constructor.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    constructor.
    + apply Nat.eqb_eq. exact Hhead.
    + eapply IH. exact Htail.
Qed.

Lemma check_common_band_startb_sound :
  forall bands,
    check_common_band_startb bands = true ->
    common_band_start bands.
Proof.
  intros bands Hcheck.
  destruct bands as [|band bands].
  - exists O. constructor.
  - exists (ptb_start band).
    constructor; [reflexivity|].
    eapply check_band_starts_eqb_sound.
    exact Hcheck.
Qed.

Lemma check_second_level_recipe_sizes_eqb_sound :
  forall root_sizes child_sizes recipes,
    check_second_level_recipe_sizes_eqb
      root_sizes child_sizes recipes = true ->
    Forall
      (fun recipe =>
         slbr_root_sizes recipe = root_sizes /\
         slbr_child_sizes recipe = child_sizes)
      recipes.
Proof.
  intros root_sizes child_sizes recipes Hcheck.
  induction recipes as [|recipe recipes IH]; simpl in *.
  - constructor.
  - repeat rewrite andb_true_iff in Hcheck.
    destruct Hcheck as [[Hroot Hchild] Htail].
    constructor.
    + split; eapply listz_strict_eqb_eq; eauto.
    + eapply IH. exact Htail.
Qed.

Lemma check_common_second_level_recipe_sizesb_sound :
  forall recipes,
    check_common_second_level_recipe_sizesb recipes = true ->
    common_second_level_recipe_sizes recipes.
Proof.
  intros recipes Hcheck.
  destruct recipes as [|recipe recipes].
  - exists [], []. constructor.
  - exists (slbr_root_sizes recipe), (slbr_child_sizes recipe).
    constructor.
    + auto.
    + eapply check_second_level_recipe_sizes_eqb_sound.
      exact Hcheck.
Qed.

Lemma common_second_level_recipe_sizes_nth_error_equal :
  forall recipes i j recipe1 recipe2,
    common_second_level_recipe_sizes recipes ->
    nth_error recipes i = Some recipe1 ->
    nth_error recipes j = Some recipe2 ->
    slbr_root_sizes recipe1 = slbr_root_sizes recipe2 /\
    slbr_child_sizes recipe1 = slbr_child_sizes recipe2.
Proof.
  intros recipes i j recipe1 recipe2
         [root_sizes [child_sizes Hsizes]] Hrecipe1 Hrecipe2.
  pose proof
    (Tiling.Forall_nth_error
       _ _ recipes i recipe1 Hsizes Hrecipe1) as Hsizes1.
  pose proof
    (Tiling.Forall_nth_error
       _ _ recipes j recipe2 Hsizes Hrecipe2) as Hsizes2.
  destruct Hsizes1, Hsizes2.
  split; congruence.
Qed.

Fixpoint second_level_root_positions (count: nat) : list nat :=
  match count with
  | O => []
  | S count' =>
      O :: List.map (fun pos => S (S pos)) (second_level_root_positions count')
  end.

Definition second_level_child_positions (count: nat) : list nat :=
  List.map S (second_level_root_positions count).

Definition identity_affine_rows_at
    (total_cols env_size: nat)
    (positions: list nat) : Schedule :=
  List.map
    (fun pos => Tiling.identity_affine_row total_cols (env_size + pos)%nat)
    positions.

Definition stripmine_second_level_schedule_after_env
    (env_size: nat)
    (before_sched: Schedule)
    (band: pinstr_tiling_band) : Schedule :=
  let root_count := ptb_len band in
  let added_dims := (2 * root_count)%nat in
  let lifted :=
    Tiling.lift_schedule_after_env added_dims env_size before_sched in
  let total_cols :=
    match lifted with
    | [] => (env_size + added_dims)%nat
    | (coeffs, _) :: _ => List.length coeffs
    end in
  let prefix := firstn (ptb_start band) lifted in
  let lifted_band := firstn root_count (skipn (ptb_start band) lifted) in
  let suffix := skipn (ptb_start band + root_count)%nat lifted in
  prefix ++
  identity_affine_rows_at
    total_cols env_size (second_level_child_positions root_count) ++
  identity_affine_rows_at
    total_cols env_size (second_level_root_positions root_count) ++
  lifted_band ++ suffix.

Definition stripmine_second_level_schedule_interleaved_after_env
    (env_size: nat)
    (before_sched: Schedule)
    (band: pinstr_tiling_band) : Schedule :=
  let root_count := ptb_len band in
  let added_dims := (2 * root_count)%nat in
  let lifted :=
    Tiling.lift_schedule_after_env added_dims env_size before_sched in
  let total_cols :=
    match lifted with
    | [] => (env_size + added_dims)%nat
    | (coeffs, _) :: _ => List.length coeffs
    end in
  let prefix := firstn (ptb_start band) lifted in
  let lifted_band := firstn root_count (skipn (ptb_start band) lifted) in
  let suffix := skipn (ptb_start band + root_count)%nat lifted in
  prefix ++
  Tiling.identity_affine_rows_from total_cols env_size added_dims ++
  lifted_band ++ suffix.

Inductive second_level_schedule_layout : Type :=
| SecondLevelGrouped
| SecondLevelInterleaved.

Definition stripmine_second_level_schedule_after_env_by_layout
    (layout: second_level_schedule_layout)
    (env_size: nat)
    (before_sched: Schedule)
    (band: pinstr_tiling_band) : Schedule :=
  match layout with
  | SecondLevelGrouped =>
      stripmine_second_level_schedule_after_env env_size before_sched band
  | SecondLevelInterleaved =>
      stripmine_second_level_schedule_interleaved_after_env
        env_size before_sched band
  end.

Definition strict_zero_schedule_mask (sched: Schedule) : list bool :=
  List.map Tiling.PL.affine_function_is_zero sched.

Fixpoint list_bool_strict_eqb (xs ys: list bool) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' =>
      Bool.eqb x y && list_bool_strict_eqb xs' ys'
  | _, _ => false
  end.

Fixpoint check_schedule_masks_eqb
    (mask: list bool) (schedules: list Schedule) : bool :=
  match schedules with
  | [] => true
  | sched :: schedules' =>
      list_bool_strict_eqb mask (strict_zero_schedule_mask sched) &&
      check_schedule_masks_eqb mask schedules'
  end.

Fixpoint check_schedule_lists_after_zero_erasureb
    (expected actual: list Schedule) : bool :=
  match expected, actual with
  | [], [] => true
  | expected_sched :: expected',
    actual_sched :: actual' =>
      listzzs_strict_eqb
        (Tiling.PL.remove_zero_schedule_dims expected_sched)
        (Tiling.PL.remove_zero_schedule_dims actual_sched) &&
      check_schedule_lists_after_zero_erasureb expected' actual'
  | _, _ => false
  end.

Fixpoint second_level_expected_schedules
    (layout: second_level_schedule_layout)
    (env_size: nat)
    (before_pis: list Tiling.PL.PolyInstr)
    (bands: list pinstr_tiling_band) : option (list Schedule) :=
  match before_pis, bands with
  | [], [] => Some []
  | before_pi :: before_pis', band :: bands' =>
      match
        second_level_expected_schedules
          layout env_size before_pis' bands'
      with
      | Some schedules =>
          Some
            (stripmine_second_level_schedule_after_env_by_layout
               layout env_size (Tiling.PL.pi_schedule before_pi) band
             :: schedules)
      | None => None
      end
  | _, _ => None
  end.

Definition check_pinstr_list_second_level_schedule_zero_erasureb
    (layout: second_level_schedule_layout)
    (env_size: nat)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (bands: list pinstr_tiling_band) : bool :=
  match
    second_level_expected_schedules layout env_size before_pis bands
  with
  | Some (expected0 :: expected') =>
      match List.map Tiling.PL.pi_schedule after_pis with
      | actual0 :: actual' =>
          check_schedule_masks_eqb
            (strict_zero_schedule_mask expected0) expected' &&
          check_schedule_masks_eqb
            (strict_zero_schedule_mask actual0) actual' &&
          check_schedule_lists_after_zero_erasureb
            (expected0 :: expected') (actual0 :: actual')
      | [] => false
      end
  | Some [] =>
      match after_pis with
      | [] => true
      | _ => false
      end
  | None => false
  end.

Definition second_level_schedule_tile_block_by_layout
    (layout: second_level_schedule_layout)
    (recipe: second_level_band_recipe)
    (params point: list Z) : list Z :=
  match layout with
  | SecondLevelGrouped =>
      second_level_schedule_tile_block recipe params point
  | SecondLevelInterleaved =>
      second_level_schedule_interleaved_tile_block recipe params point
  end.

Definition check_pinstr_second_level_schedule_symmetricb
    (layout: second_level_schedule_layout)
    (env_size: nat)
    (before after: Tiling.PL.PolyInstr)
    (band: pinstr_tiling_band) : bool :=
  check_schedule_with_symmetric_trailing_zero_paddingb
    (stripmine_second_level_schedule_after_env_by_layout
       layout env_size (Tiling.PL.pi_schedule before) band)
    (Tiling.PL.pi_schedule after).

Fixpoint check_pinstr_list_second_level_schedule_symmetricb
    (layout: second_level_schedule_layout)
    (env_size: nat)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (bands: list pinstr_tiling_band) : bool :=
  match before_pis, after_pis, bands with
  | [], [], [] => true
  | before_pi :: before_pis', after_pi :: after_pis', band :: bands' =>
      check_pinstr_second_level_schedule_symmetricb
        layout env_size before_pi after_pi band &&
      check_pinstr_list_second_level_schedule_symmetricb
        layout env_size before_pis' after_pis' bands'
  | _, _, _ => false
  end.

Definition check_pinstr_list_second_level_schedule_directb
    (layout: second_level_schedule_layout)
    (env_size: nat)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (bands: list pinstr_tiling_band) : bool :=
  check_pinstr_list_second_level_schedule_symmetricb
    layout env_size before_pis after_pis bands ||
  check_pinstr_list_second_level_schedule_zero_erasureb
    layout env_size before_pis after_pis bands.

Definition check_pprog_second_level_schedule_directb
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness)
    : option
        (list pinstr_tiling_band *
         list second_level_band_recipe *
         second_level_schedule_layout) :=
  let '(before_pis, before_ctxt, before_vars) := before in
  let '(after_pis, after_ctxt, after_vars) := after in
  if TilingCheck.ctxt_eqb before_ctxt after_ctxt &&
     TilingCheck.ctxt_ty_eqb before_vars after_vars
  then
    match infer_pinstr_list_second_level_bands before_pis ws with
    | Some (bands, recipes) =>
        if check_common_second_level_recipe_sizesb recipes &&
           check_common_band_startb bands
        then
          if
            check_pinstr_list_second_level_schedule_directb
              SecondLevelGrouped (List.length before_ctxt)
              before_pis after_pis bands
          then Some (bands, recipes, SecondLevelGrouped)
          else if
            check_pinstr_list_second_level_schedule_directb
              SecondLevelInterleaved (List.length before_ctxt)
              before_pis after_pis bands
          then Some (bands, recipes, SecondLevelInterleaved)
          else None
        else None
    | None => None
    end
  else None.

Lemma affine_product_app :
  forall m1 m2 p,
    affine_product (m1 ++ m2) p = affine_product m1 p ++ affine_product m2 p.
Proof.
  intros m1 m2 p.
  unfold affine_product.
  rewrite List.map_app.
  reflexivity.
Qed.

Lemma schedule_rows_of_links_aux_length :
  forall prefix links rows,
    schedule_rows_of_links_aux prefix links = Some rows ->
    List.length rows = List.length links.
Proof.
  intros prefix links.
  revert prefix.
  induction links as [|link links IH]; intros prefix rows Hrows.
  - simpl in Hrows. inversion Hrows. reflexivity.
  - simpl in Hrows.
    destruct (listz_strict_eqb
                (firstn prefix (ae_var_coeffs (tl_expr link)))
                (repeat 0%Z prefix)) eqn:Hprefix.
    + destruct (schedule_rows_of_links_aux (S prefix) links) as [rows'|] eqn:Hrest.
      * inversion Hrows; subst; clear Hrows.
        simpl.
        f_equal.
        apply (IH (S prefix) rows').
        exact Hrest.
      * discriminate.
    + discriminate.
Qed.

Lemma schedule_rows_of_links_length :
  forall w rows,
    schedule_rows_of_links w = Some rows ->
    List.length rows = List.length (stw_links w).
Proof.
  intros w rows Hrows.
  unfold schedule_rows_of_links in Hrows.
  eapply schedule_rows_of_links_aux_length; eauto.
Qed.

Lemma affine_product_schedule_row_of_tile_link_base :
  forall prefix_len prefix point params link,
    List.length prefix = prefix_len ->
    List.length (ae_var_coeffs (tl_expr link)) = (prefix_len + List.length point)%nat ->
    List.length (ae_param_coeffs (tl_expr link)) = List.length params ->
    firstn prefix_len (ae_var_coeffs (tl_expr link)) = repeat 0%Z prefix_len ->
    affine_product [schedule_row_of_tile_link_base prefix_len link] (params ++ point) =
    [eval_affine (tl_expr link) (prefix ++ point) params].
Proof.
  intros prefix_len prefix point params link Hprefix Hvars Hparams Hzero.
  unfold affine_product, schedule_row_of_tile_link_base, eval_affine.
  simpl.
  rewrite <-
    (Tiling.tiling_dot_product_eq_linalg_dot_product
       (ae_param_coeffs (tl_expr link) ++
        skipn prefix_len (ae_var_coeffs (tl_expr link)))
       (params ++ point)).
  rewrite TilingWitness.dot_product_app_exact by exact Hparams.
  rewrite (TilingWitness.dot_product_split_firstn_skipn
             (ae_var_coeffs (tl_expr link)) prefix point).
  2:{ rewrite Hprefix. exact Hvars. }
  rewrite Hprefix.
  rewrite Hzero.
  rewrite TilingWitness.dot_product_repeat_zero_exact by exact Hprefix.
  simpl.
  f_equal.
  lia.
Qed.

Lemma eval_tile_links_from_schedule_rows_aux :
  forall prefix prefix_len point params links rows sizes,
    List.length prefix = prefix_len ->
    schedule_rows_of_links_aux prefix_len links = Some rows ->
    List.map tl_tile_size links = sizes ->
    well_formed_tile_links prefix_len (List.length point) links ->
    Forall
      (fun link =>
         List.length (ae_param_coeffs (tl_expr link)) = List.length params)
      links ->
    eval_tile_links prefix point params links =
    prefix ++
    List.map
      (fun '(v, sz) => Z.div v sz)
      (List.combine (affine_product rows (params ++ point)) sizes).
Proof.
  intros prefix prefix_len point params links.
  revert prefix prefix_len.
  induction links as [|link links IH]; intros prefix prefix_len rows sizes
         Hprefix Hrows Hsizes Hwf Hparams.
  - simpl in Hrows. inversion Hrows; subst rows.
    simpl in Hsizes. inversion Hsizes; subst sizes.
    simpl. now rewrite app_nil_r.
  - simpl in Hrows.
    destruct (listz_strict_eqb
                (firstn prefix_len (ae_var_coeffs (tl_expr link)))
                (repeat 0%Z prefix_len)) eqn:Hzero_b; try discriminate.
    destruct (schedule_rows_of_links_aux (S prefix_len) links) as [rows'|] eqn:Hrows';
      try discriminate.
    inversion Hrows; subst rows; clear Hrows.
    simpl in Hsizes.
    destruct sizes as [|size sizes']; try discriminate.
    inversion Hsizes; subst size sizes'; clear Hsizes.
    destruct Hwf as [Hvars Hwf].
    inversion Hparams as [|link0 links0 Hparam Hparams']; subst link0 links0.
    apply listz_strict_eqb_eq in Hzero_b.
    simpl.
    specialize
      (IH (prefix ++ [eval_tile_parent link (prefix ++ point) params])
          (S prefix_len) rows' (List.map tl_tile_size links))
      as IH'.
    assert
      (Hprefix' :
         List.length (prefix ++ [eval_tile_parent link (prefix ++ point) params]) =
         S prefix_len).
    { rewrite app_length; simpl. lia. }
    specialize (IH' Hprefix' Hrows' eq_refl Hwf Hparams').
    rewrite IH'.
    rewrite <- app_assoc.
    simpl.
    f_equal.
    assert
      (Hrow :
         Linalg.dot_product
           (ae_param_coeffs (tl_expr link) ++
            skipn prefix_len (ae_var_coeffs (tl_expr link)))
           (params ++ point) + ae_const (tl_expr link) =
         eval_affine (tl_expr link) (prefix ++ point) params).
    {
      pose proof
        (affine_product_schedule_row_of_tile_link_base
           prefix_len prefix point params link Hprefix Hvars Hparam Hzero_b)
        as Htmp.
      simpl in Htmp.
      injection Htmp as Htmp'.
      exact Htmp'.
    }
    unfold eval_tile_parent.
    rewrite <- Hrow.
    reflexivity.
Qed.

Lemma eval_tile_links_from_schedule_rows :
  forall w point params rows sizes,
    List.length point = stw_point_dim w ->
    schedule_rows_of_links w = Some rows ->
    List.map tl_tile_size (stw_links w) = sizes ->
    well_formed_statement_tiling_witness w ->
    Forall
      (fun link =>
         List.length (ae_param_coeffs (tl_expr link)) = List.length params)
      (stw_links w) ->
    eval_tile_links [] point params (stw_links w) =
    List.map
      (fun '(v, sz) => Z.div v sz)
      (List.combine (affine_product rows (params ++ point)) sizes).
Proof.
  intros w point params rows sizes Hpoint_dim Hrows Hsizes Hwf Hparams.
  unfold well_formed_statement_tiling_witness in Hwf.
  assert (Hwf' : well_formed_tile_links 0 (List.length point) (stw_links w)).
  { rewrite Hpoint_dim. exact Hwf. }
  specialize
    (eval_tile_links_from_schedule_rows_aux
       [] 0 point params (stw_links w) rows sizes eq_refl Hrows Hsizes Hwf' Hparams)
    as Haux.
  simpl in Haux.
  exact Haux.
Qed.

Lemma insert_zeros_length_exact_local :
  forall d i l,
    (i <= length l)%nat ->
    length (Tiling.PL.insert_zeros d i l) = (d + length l)%nat.
Proof.
  intros d i l Hle.
  unfold Tiling.PL.insert_zeros.
  rewrite app_length, app_length.
  rewrite repeat_length.
  rewrite resize_length.
  rewrite skipn_length.
  lia.
Qed.

Lemma lift_schedule_after_env_exact_cols :
  forall cols added env_size sched,
    exact_listzzs_cols cols sched ->
    (env_size <= cols)%nat ->
    exact_listzzs_cols (added + cols)%nat
      (Tiling.lift_schedule_after_env added env_size sched).
Proof.
  intros cols added env_size sched Hcols Henv listz z listzz Hin Heq.
  unfold Tiling.lift_schedule_after_env, Tiling.lift_affine_function_after_env in Hin.
  rewrite in_map_iff in Hin.
  destruct Hin as [[coeffs rhs] [Hmap Hin0]].
  rewrite Heq in Hmap.
  unfold Tiling.lift_constraint_after_env in Hmap.
  simpl in Hmap.
  inversion Hmap; subst listz z.
  specialize (Hcols coeffs rhs (coeffs, rhs) Hin0 eq_refl).
  unfold Tiling.lift_constraint_after_env.
  simpl.
  rewrite insert_zeros_length_exact_local by lia.
  rewrite Hcols.
  reflexivity.
Qed.

Lemma affine_product_firstn :
  forall n m p,
    affine_product (firstn n m) p = firstn n (affine_product m p).
Proof.
  induction n as [|n IH]; intros m p.
  - destruct m; reflexivity.
  - destruct m as [|x m]; simpl.
    + reflexivity.
    + rewrite IH.
      reflexivity.
Qed.

Lemma in_firstn_local :
  forall {A} n (xs: list A) x,
    In x (firstn n xs) ->
    In x xs.
Proof.
  induction n as [|n IH]; intros xs x Hin.
  - destruct xs; simpl in Hin; contradiction.
  - destruct xs as [|y ys]; simpl in Hin.
    + contradiction.
    + destruct Hin as [Hin | Hin].
      * subst. left. reflexivity.
      * right. eapply IH. exact Hin.
Qed.

Lemma exact_listzzs_cols_firstn_local :
  forall cols n rows,
    exact_listzzs_cols cols rows ->
    exact_listzzs_cols cols (firstn n rows).
Proof.
  intros cols n rows Hcols listz z listzz Hin Heq.
  eapply Hcols; eauto.
  eapply in_firstn_local; eauto.
Qed.

Lemma exact_listzzs_cols_skipn_local_component :
  forall cols n rows,
    exact_listzzs_cols cols rows ->
    exact_listzzs_cols cols (skipn n rows).
Proof.
  intros cols n rows Hcols listz z listzz Hin Heq.
  eapply Hcols; eauto.
  clear Hcols Heq.
  revert rows Hin.
  induction n as [|n IH]; intros rows Hin.
  - exact Hin.
  - destruct rows as [|row rows]; simpl in Hin.
    + contradiction.
    + right. eapply IH; exact Hin.
Qed.

Lemma exact_listzzs_cols_app_local_component :
  forall cols rows1 rows2,
    exact_listzzs_cols cols rows1 ->
    exact_listzzs_cols cols rows2 ->
    exact_listzzs_cols cols (rows1 ++ rows2).
Proof.
  exact Linalg.exact_listzzs_cols_app.
Qed.




Lemma exact_listzzs_cols_lift_schedule_after_env_local :
  forall cols added env_size sched,
    exact_listzzs_cols cols sched ->
    (env_size <= cols)%nat ->
    exact_listzzs_cols (cols + added)%nat
      (Tiling.lift_schedule_after_env added env_size sched).
Proof.
  intros cols added env_size sched Hcols Henv.
  unfold Tiling.lift_schedule_after_env, Tiling.lift_affine_function_after_env.
  eapply Tiling.PL.exact_listzzs_cols_current_insert_zeros_constraint; eauto.
Qed.

Lemma compose_tiling_pinstr_ext_wf_tiling_local :
  forall env vars before after w,
    Tiling.PL.wf_pinstr_tiling env vars before ->
    Tiling.PL.wf_pinstr_tiling env vars after ->
    stw_point_dim w = Tiling.PL.pi_depth before ->
    Tiling.after_matches_tiling_witness after w ->
    Tiling.PL.wf_pinstr_ext_tiling env
      (Tiling.compose_tiling_pinstr_ext (List.length env) before after w).
Proof.
  intros env vars before after w Hwf_before Hwf_after Hpoint_dim Hafter_wit.
  destruct Hafter_wit as [Hwitness_after Hwitdim_after].
  unfold Tiling.PL.wf_pinstr_ext_tiling, Tiling.PL.wf_pinstr_ext.
  unfold Tiling.compose_tiling_pinstr_ext, Tiling.current_src_transformation_of_pinstr.
  simpl.
  destruct Hwf_before as [Hwf_before_core _].
  destruct Hwf_after as [Hwf_after_core Htf_eq_after].
  destruct Hwf_before_core as
      [Hwit_before [Hcols_before [Hpoly_nrl_before [Hsched_nrl_before
       [Hpoly_before [Htf_before [Hacc_before [Hsched_before
       [Hw_before Hr_before]]]]]]]]].
  destruct Hwf_after_core as
      [Hwit_after [Hcols_after [Hpoly_nrl_after [Hsched_nrl_after
       [Hpoly_after [Htf_after [Hacc_after [Hsched_after
       [Hw_after Hr_after]]]]]]]]].
  split.
  - repeat split.
    + exact Hwitdim_after.
    + exact Hpoly_after.
    + rewrite <- Hwit_after.
      eapply Tiling.PL.exact_listzzs_cols_current_transformation_at.
      exact Htf_after.
    + rewrite <- Hwit_after.
      eapply Tiling.PL.exact_listzzs_cols_current_transformation_at.
      exact Htf_after.
    + replace
        (length env + Tiling.PL.pi_depth after)%nat
        with
          (length env + Tiling.PL.pi_depth before + List.length (stw_links w))%nat.
      * eapply exact_listzzs_cols_lift_schedule_after_env_local.
        -- exact Hsched_before.
        -- lia.
      * rewrite <- Hpoint_dim.
        rewrite <- Hwitdim_after.
        rewrite Hwitness_after.
        unfold witness_current_point_dim, witness_base_point_dim, witness_added_dims.
        simpl.
        lia.
    + exact Hsched_after.
    + rewrite Tiling.PL.current_transformation_at_preserve_length.
      exact Hw_after.
    + rewrite Tiling.PL.current_transformation_at_preserve_length.
      exact Hr_after.
  - reflexivity.
Qed.








Lemma identity_affine_rows_from_length :
  forall total_cols pos count,
    List.length (Tiling.identity_affine_rows_from total_cols pos count) = count.
Proof.
  intros total_cols pos count.
  revert total_cols pos.
  induction count as [|count IH]; intros total_cols pos; simpl.
  - reflexivity.
  - rewrite IH.
    reflexivity.
Qed.

Lemma stripmine_schedule_after_env_length :
  forall env_size before_sched band,
    List.length (stripmine_schedule_after_env env_size before_sched band) =
    (List.length before_sched + ptb_len band)%nat.
Proof.
  intros env_size before_sched band.
  unfold stripmine_schedule_after_env.
  set (added_dims := ptb_len band).
  set (lifted := Tiling.lift_schedule_after_env added_dims env_size before_sched).
  set (prefix := firstn (ptb_start band) lifted).
  set (lifted_band := firstn added_dims (skipn (ptb_start band) lifted)).
  set (suffix := skipn (ptb_start band + added_dims)%nat lifted).
  assert (Hlifted_len : List.length lifted = List.length before_sched).
  {
    subst lifted.
    unfold Tiling.lift_schedule_after_env, Tiling.lift_affine_function_after_env.
    rewrite List.map_length.
    reflexivity.
  }
  assert (Hsplit :
    (List.length prefix + List.length lifted_band + List.length suffix)%nat =
    List.length lifted).
  {
    subst prefix lifted_band suffix.
    rewrite !firstn_length.
    rewrite !skipn_length.
    lia.
  }
  rewrite !app_length.
  rewrite identity_affine_rows_from_length.
  lia.
Qed.



Lemma affine_product_zero_schedule_rows :
  forall cols extra_rows idx,
    affine_product (repeat (zero_schedule_row cols) extra_rows) idx =
    repeat 0%Z extra_rows.
Proof.
  intros cols extra_rows idx.
  unfold affine_product.
  induction extra_rows as [|extra_rows IH]; simpl.
  - reflexivity.
  - unfold zero_schedule_row.
    simpl.
    rewrite dot_product_repeat_zero_left.
    f_equal.
    exact IH.
Qed.

Lemma affine_product_pad_schedule_with_zero_rows :
  forall sched cols extra_rows idx,
    affine_product
      (pad_schedule_with_zero_rows sched cols extra_rows)
      idx =
    affine_product sched idx ++ repeat 0%Z extra_rows.
Proof.
  intros sched cols extra_rows idx.
  unfold pad_schedule_with_zero_rows.
  rewrite affine_product_app.
  rewrite affine_product_zero_schedule_rows.
  reflexivity.
Qed.


Lemma compose_tiling_pinstrs_ext_from_after_wf_tiling :
  forall env vars before_pis after_pis ws,
    Forall (Tiling.PL.wf_pinstr_tiling env vars) before_pis ->
    Forall (Tiling.PL.wf_pinstr_tiling env vars) after_pis ->
    Forall2
      (fun before_pi w => stw_point_dim w = Tiling.PL.pi_depth before_pi)
      before_pis ws ->
    Forall2 Tiling.after_matches_tiling_witness after_pis ws ->
    Forall
      (Tiling.PL.wf_pinstr_ext_tiling env)
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length env) before_pis after_pis ws).
Proof.
  intros env vars before_pis.
  induction before_pis as [|before_pi before_pis' IH];
    intros after_pis ws Hwf_before Hwf_after Hdepths Hwits.
  - destruct after_pis as [|after_pi after_pis'];
      destruct ws as [|w ws']; inversion Hwf_before; inversion Hwf_after;
      inversion Hdepths; inversion Hwits; subst; constructor.
  - destruct after_pis as [|after_pi after_pis'];
      destruct ws as [|w ws']; inversion Hwf_before; inversion Hwf_after;
      inversion Hdepths; inversion Hwits; subst; simpl.
    all: try solve [inversion Hdepths | inversion Hwits].
    constructor.
    + eapply compose_tiling_pinstr_ext_wf_tiling_local; eauto.
    + eapply IH; eauto.
Qed.







Lemma affine_product_skipn :
  forall n m p,
    affine_product (skipn n m) p = skipn n (affine_product m p).
Proof.
  induction n as [|n IH]; intros m p.
  - reflexivity.
  - destruct m as [|x m]; simpl; auto.
Qed.

Lemma affine_product_identity_affine_row :
  forall total_cols pos idx,
    (S pos <= total_cols)%nat ->
    affine_product [Tiling.identity_affine_row total_cols pos] idx =
    [nth pos idx 0%Z].
Proof.
  intros total_cols pos idx Hle.
  unfold Tiling.identity_affine_row.
  simpl.
  assert (Hrow :
    repeat 0%Z pos ++ 1%Z :: repeat 0%Z (total_cols - pos - 1) =
    resize total_cols (V0 pos ++ [1%Z])).
  {
    rewrite resize_app_le.
    2: {
      unfold V0.
      rewrite repeat_length.
      lia.
    }
    replace (Datatypes.length (V0 pos)) with pos.
    2: {
      unfold V0.
      rewrite repeat_length.
      reflexivity.
    }
    replace (total_cols - pos)%nat with (S (total_cols - pos - 1)) by lia.
    simpl.
    rewrite resize_null_repeat by reflexivity.
    unfold V0.
    replace (total_cols - pos - 1 - 0)%nat with (total_cols - pos - 1)%nat by lia.
    reflexivity.
  }
  rewrite Hrow.
  rewrite ParallelCore.dot_product_select_coord by exact Hle.
  f_equal.
  lia.
Qed.

Lemma affine_product_identity_affine_rows_at :
  forall total_cols env_size positions idx,
    Forall (fun pos => (S (env_size + pos) <= total_cols)%nat) positions ->
    affine_product (identity_affine_rows_at total_cols env_size positions) idx =
    List.map (fun pos => nth (env_size + pos)%nat idx 0%Z) positions.
Proof.
  intros total_cols env_size positions idx Hpositions.
  induction Hpositions as [|pos positions Hpos Hpositions IH].
  - reflexivity.
  - unfold identity_affine_rows_at in *.
    simpl in *.
    change
      (affine_product
         ([Tiling.identity_affine_row total_cols (env_size + pos)%nat] ++
          List.map
            (fun pos0 =>
               Tiling.identity_affine_row total_cols (env_size + pos0)%nat)
            positions) idx =
       nth (env_size + pos)%nat idx 0%Z ::
       List.map (fun pos0 => nth (env_size + pos0)%nat idx 0%Z) positions).
    rewrite affine_product_app.
    rewrite affine_product_identity_affine_row by exact Hpos.
    rewrite IH.
    reflexivity.
Qed.

Lemma second_level_root_positions_bound :
  forall count pos,
    In pos (second_level_root_positions count) ->
    (S pos < 2 * count)%nat.
Proof.
  induction count as [|count IH]; intros pos Hin; simpl in Hin.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst pos. lia.
    + apply in_map_iff in Hin.
      destruct Hin as [pos0 [Heq Hin0]].
      subst pos.
      specialize (IH pos0 Hin0).
      lia.
Qed.

Lemma second_level_child_positions_bound :
  forall count pos,
    In pos (second_level_child_positions count) ->
    (pos < 2 * count)%nat.
Proof.
  intros count pos Hin.
  unfold second_level_child_positions in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [pos0 [Heq Hin0]].
  subst pos.
  pose proof (second_level_root_positions_bound _ _ Hin0).
  lia.
Qed.

Lemma map_nth_root_positions_interleave :
  forall roots children,
    List.length roots = List.length children ->
    List.map
      (fun pos => nth pos (interleave_root_child_tiles roots children) 0%Z)
      (second_level_root_positions (List.length roots)) = roots.
Proof.
  induction roots as [|root roots IH]; intros children Hlen.
  - destruct children; [reflexivity|discriminate].
  - destruct children as [|child children]; [discriminate|].
    simpl in Hlen.
    simpl.
    f_equal.
    rewrite List.map_map.
    change
      (List.map
         (fun pos => nth pos (interleave_root_child_tiles roots children) 0%Z)
         (second_level_root_positions (List.length roots)) = roots).
    eapply IH.
    lia.
Qed.

Lemma map_nth_child_positions_interleave :
  forall roots children,
    List.length roots = List.length children ->
    List.map
      (fun pos => nth pos (interleave_root_child_tiles roots children) 0%Z)
      (second_level_child_positions (List.length roots)) = children.
Proof.
  induction roots as [|root roots IH]; intros children Hlen.
  - destruct children; [reflexivity|discriminate].
  - destruct children as [|child children]; [discriminate|].
    simpl in Hlen.
    unfold second_level_child_positions.
    simpl.
    rewrite List.map_map.
    simpl.
    f_equal.
    rewrite List.map_map.
    assert (Hlen_tail : List.length roots = List.length children) by lia.
    pose proof (IH children Hlen_tail) as IHchildren.
    unfold second_level_child_positions in IHchildren.
    rewrite List.map_map in IHchildren.
    exact IHchildren.
Qed.

Lemma interleave_root_child_tiles_length :
  forall roots children,
    List.length roots = List.length children ->
    List.length (interleave_root_child_tiles roots children) =
      (2 * List.length roots)%nat.
Proof.
  induction roots as [|root roots IH]; intros children Hlen.
  - destruct children; simpl in *; try discriminate; lia.
  - destruct children; simpl in *; try discriminate.
    rewrite IH by lia.
    lia.
Qed.

Lemma nth_app_left_local_second_level :
  forall (A: Type) (xs ys: list A) n d,
    (n < List.length xs)%nat ->
    nth n (xs ++ ys) d = nth n xs d.
Proof.
  intros A xs.
  induction xs as [|x xs IH]; intros ys n d Hlt.
  - exfalso. simpl in Hlt. lia.
  - destruct n as [|n]; simpl; auto.
    eapply IH. simpl in Hlt. lia.
Qed.

Lemma nth_app_offset_local_second_level :
  forall (A: Type) (xs ys: list A) n d,
    nth (List.length xs + n)%nat (xs ++ ys) d = nth n ys d.
Proof.
  intros A xs.
  induction xs as [|x xs IH]; intros ys n d; simpl.
  - reflexivity.
  - exact (IH ys n d).
Qed.

Lemma nth_env_added_app :
  forall env_size env added point pos,
    List.length env = env_size ->
    (pos < List.length added)%nat ->
    nth (env_size + pos)%nat (env ++ added ++ point) 0%Z =
      nth pos added 0%Z.
Proof.
  intros env_size env added point pos Henv Hpos.
  replace (env_size + pos)%nat with (List.length env + pos)%nat by lia.
  rewrite nth_app_offset_local_second_level.
  eapply nth_app_left_local_second_level.
  exact Hpos.
Qed.

Lemma affine_product_second_level_root_rows_at :
  forall total_cols env_size env roots children point,
    List.length env = env_size ->
    List.length roots = List.length children ->
    (env_size + 2 * List.length roots <= total_cols)%nat ->
    affine_product
      (identity_affine_rows_at
         total_cols env_size
         (second_level_root_positions (List.length roots)))
      (env ++ interleave_root_child_tiles roots children ++ point) = roots.
Proof.
  intros total_cols env_size env roots children point
         Henv Hlen Hcols.
  rewrite affine_product_identity_affine_rows_at.
  2:{
    apply Forall_forall.
    intros pos Hin.
    pose proof (second_level_root_positions_bound _ _ Hin).
    lia.
  }
  erewrite List.map_ext_in.
  2:{
    intros pos Hin.
    eapply nth_env_added_app.
    - exact Henv.
    - rewrite interleave_root_child_tiles_length by exact Hlen.
      pose proof (second_level_root_positions_bound _ _ Hin).
      lia.
  }
  eapply map_nth_root_positions_interleave.
  exact Hlen.
Qed.

Lemma affine_product_second_level_child_rows_at :
  forall total_cols env_size env roots children point,
    List.length env = env_size ->
    List.length roots = List.length children ->
    (env_size + 2 * List.length roots <= total_cols)%nat ->
    affine_product
      (identity_affine_rows_at
         total_cols env_size
         (second_level_child_positions (List.length roots)))
      (env ++ interleave_root_child_tiles roots children ++ point) = children.
Proof.
  intros total_cols env_size env roots children point
         Henv Hlen Hcols.
  rewrite affine_product_identity_affine_rows_at.
  2:{
    apply Forall_forall.
    intros pos Hin.
    pose proof (second_level_child_positions_bound _ _ Hin).
    lia.
  }
  erewrite List.map_ext_in.
  2:{
    intros pos Hin.
    eapply nth_env_added_app.
    - exact Henv.
    - rewrite interleave_root_child_tiles_length by exact Hlen.
      pose proof (second_level_child_positions_bound _ _ Hin).
      lia.
  }
  eapply map_nth_child_positions_interleave.
  exact Hlen.
Qed.

Lemma affine_product_identity_affine_rows_from :
  forall total_cols pos count idx,
    (pos + count <= total_cols)%nat ->
    (pos + count <= List.length idx)%nat ->
    affine_product (Tiling.identity_affine_rows_from total_cols pos count) idx =
    firstn count (skipn pos idx).
Proof.
  intros total_cols pos count.
  revert pos.
  induction count as [|count IH]; intros pos idx Hle Hlen.
  - simpl. reflexivity.
  - simpl Tiling.identity_affine_rows_from.
    replace
      (Tiling.identity_affine_row total_cols pos ::
       Tiling.identity_affine_rows_from total_cols (S pos) count)
      with
      ([Tiling.identity_affine_row total_cols pos] ++
       Tiling.identity_affine_rows_from total_cols (S pos) count)
      by reflexivity.
    rewrite affine_product_app.
    rewrite affine_product_identity_affine_row by lia.
    rewrite IH by lia.
    destruct (skipn pos idx) as [|x xs] eqn:Hskip.
    + assert (Hskip_len : List.length (skipn pos idx) = 0%nat).
      { rewrite Hskip. reflexivity. }
      rewrite skipn_length in Hskip_len.
      lia.
    + assert (Hnth : nth pos idx 0%Z = x).
      {
        assert (Hplus : (pos + 0)%nat = pos) by lia.
        rewrite <- Hplus.
        rewrite <- Misc.nth_skipn with (m := pos) (n := 0%nat) (d := 0%Z).
        rewrite Hskip.
        reflexivity.
      }
      assert (Htail : skipn (S pos) idx = xs).
      {
        replace (S pos) with (1 + pos)%nat by lia.
        rewrite <- skipn_skipn with (n := 1%nat) (m := pos) (l := idx).
        rewrite Hskip.
        simpl.
        reflexivity.
      }
      simpl.
      rewrite Hnth.
      replace match idx with
              | [] => []
              | _ :: l => skipn pos l
              end
        with (skipn (S pos) idx).
      2:{
        destruct idx as [|y ys]; reflexivity.
      }
      rewrite Htail.
      reflexivity.
Qed.

Lemma stripmine_schedule_after_env_eval :
  forall env_size before_sched band cols env tiles iters,
    exact_listzzs_cols cols before_sched ->
    (env_size <= cols)%nat ->
    length env = env_size ->
    length tiles = ptb_len band ->
    affine_product
      (stripmine_schedule_after_env env_size before_sched band)
      (env ++ tiles ++ iters) =
    let old_ts := affine_product before_sched (env ++ iters) in
    firstn (ptb_start band) old_ts ++
    tiles ++
    firstn (ptb_len band) (skipn (ptb_start band) old_ts) ++
    skipn (ptb_start band + ptb_len band)%nat old_ts.
Proof.
  intros env_size before_sched band cols env tiles iters Hsched_cols Henv_cols Henv Htiles.
  unfold stripmine_schedule_after_env.
  set (added_dims := ptb_len band).
  set (lifted := Tiling.lift_schedule_after_env added_dims env_size before_sched).
  set (total_cols :=
    match lifted with
    | [] => (env_size + added_dims)%nat
    | (coeffs, _) :: _ => List.length coeffs
    end).
  set (old_ts := affine_product before_sched (env ++ iters)).
  assert (Hlift :
    affine_product lifted (env ++ tiles ++ iters) = old_ts).
  {
    subst lifted old_ts added_dims.
    apply Tiling.lift_affine_function_after_env_eval; assumption.
  }
  rewrite affine_product_app.
  rewrite affine_product_app.
  rewrite affine_product_app.
  rewrite affine_product_firstn.
  rewrite affine_product_firstn.
  rewrite !affine_product_skipn.
  rewrite (affine_product_identity_affine_rows_from total_cols env_size added_dims
            (env ++ tiles ++ iters)).
  2:{
    subst total_cols.
    pose proof (lift_schedule_after_env_exact_cols cols added_dims env_size before_sched
                 Hsched_cols Henv_cols) as Hlift_cols.
    subst lifted.
    destruct (Tiling.lift_schedule_after_env added_dims env_size before_sched) as [|[coeffs rhs] rows].
    - lia.
    - assert (length coeffs = (added_dims + cols)%nat).
      {
        eapply Hlift_cols.
        - left. reflexivity.
        - reflexivity.
      }
      lia.
  }
  2:{
    subst added_dims.
    repeat rewrite app_length.
    lia.
  }
  rewrite Hlift.
  rewrite <- Henv.
  assert (Hskip_mid :
    skipn (length env) (env ++ tiles ++ iters) = tiles ++ iters).
  {
    replace (env ++ tiles ++ iters) with (env ++ (tiles ++ iters)) by reflexivity.
    rewrite skipn_app_le by lia.
    replace (length env - length env)%nat with 0%nat by lia.
    simpl.
    reflexivity.
  }
  rewrite Hskip_mid.
  rewrite firstn_app.
  replace (firstn added_dims tiles) with tiles.
  2:{
    subst added_dims.
    symmetry.
    rewrite <- Htiles.
    apply firstn_all.
  }
  subst added_dims.
  rewrite Htiles.
  rewrite Nat.sub_diag.
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma stripmine_second_level_schedule_after_env_eval :
  forall env_size before_sched band cols env roots children iters,
    exact_listzzs_cols cols before_sched ->
    (env_size <= cols)%nat ->
    List.length env = env_size ->
    List.length roots = ptb_len band ->
    List.length roots = List.length children ->
    affine_product
      (stripmine_second_level_schedule_after_env env_size before_sched band)
      (env ++ interleave_root_child_tiles roots children ++ iters) =
    let old_ts := affine_product before_sched (env ++ iters) in
    firstn (ptb_start band) old_ts ++
    children ++ roots ++
    firstn (ptb_len band) (skipn (ptb_start band) old_ts) ++
    skipn (ptb_start band + ptb_len band)%nat old_ts.
Proof.
  intros env_size before_sched band cols env roots children iters
         Hsched_cols Henv_cols Henv Hroots Hlen.
  unfold stripmine_second_level_schedule_after_env.
  set (root_count := ptb_len band).
  set (added_dims := (2 * root_count)%nat).
  set (lifted :=
    Tiling.lift_schedule_after_env added_dims env_size before_sched).
  set (total_cols :=
    match lifted with
    | [] => (env_size + added_dims)%nat
    | (coeffs, _) :: _ => List.length coeffs
    end).
  set (old_ts := affine_product before_sched (env ++ iters)).
  assert (Hlift :
    affine_product lifted
      (env ++ interleave_root_child_tiles roots children ++ iters) = old_ts).
  {
    subst lifted old_ts added_dims root_count.
    apply Tiling.lift_affine_function_after_env_eval; try assumption.
    rewrite interleave_root_child_tiles_length by exact Hlen.
    lia.
  }
  assert (Htotal_cols : (env_size + added_dims <= total_cols)%nat).
  {
    subst total_cols.
    pose proof
      (lift_schedule_after_env_exact_cols
         cols added_dims env_size before_sched Hsched_cols Henv_cols)
      as Hlift_cols.
    subst lifted.
    destruct
      (Tiling.lift_schedule_after_env added_dims env_size before_sched)
      as [|[coeffs rhs] rows].
    - lia.
    - assert (Hcoeffs : List.length coeffs = (added_dims + cols)%nat).
      {
        eapply Hlift_cols.
        - left. reflexivity.
        - reflexivity.
      }
      lia.
  }
  rewrite affine_product_app.
  rewrite affine_product_app.
  rewrite affine_product_app.
  rewrite affine_product_app.
  rewrite affine_product_firstn.
  rewrite affine_product_firstn.
  rewrite !affine_product_skipn.
  assert (Hroot_count : root_count = List.length roots).
  { subst root_count. lia. }
  rewrite Hroot_count.
  rewrite
    (affine_product_second_level_child_rows_at
       total_cols env_size env roots children iters Henv Hlen).
  2:{ subst added_dims root_count. rewrite Hroots. exact Htotal_cols. }
  rewrite
    (affine_product_second_level_root_rows_at
       total_cols env_size env roots children iters Henv Hlen).
  2:{ subst added_dims root_count. rewrite Hroots. exact Htotal_cols. }
  rewrite Hlift.
  reflexivity.
Qed.

Lemma stripmine_second_level_schedule_interleaved_after_env_eval :
  forall env_size before_sched band cols env roots children iters,
    exact_listzzs_cols cols before_sched ->
    (env_size <= cols)%nat ->
    List.length env = env_size ->
    List.length roots = ptb_len band ->
    List.length roots = List.length children ->
    affine_product
      (stripmine_second_level_schedule_interleaved_after_env
         env_size before_sched band)
      (env ++ interleave_root_child_tiles roots children ++ iters) =
    let old_ts := affine_product before_sched (env ++ iters) in
    firstn (ptb_start band) old_ts ++
    interleave_root_child_tiles roots children ++
    firstn (ptb_len band) (skipn (ptb_start band) old_ts) ++
    skipn (ptb_start band + ptb_len band)%nat old_ts.
Proof.
  intros env_size before_sched band cols env roots children iters
         Hsched_cols Henv_cols Henv Hroots Hlen.
  unfold stripmine_second_level_schedule_interleaved_after_env.
  set (root_count := ptb_len band).
  set (added_dims := (2 * root_count)%nat).
  set (lifted :=
    Tiling.lift_schedule_after_env added_dims env_size before_sched).
  set (total_cols :=
    match lifted with
    | [] => (env_size + added_dims)%nat
    | (coeffs, _) :: _ => List.length coeffs
    end).
  set (old_ts := affine_product before_sched (env ++ iters)).
  assert (Hlift :
    affine_product lifted
      (env ++ interleave_root_child_tiles roots children ++ iters) = old_ts).
  {
    subst lifted old_ts added_dims root_count.
    apply Tiling.lift_affine_function_after_env_eval; try assumption.
    rewrite interleave_root_child_tiles_length by exact Hlen.
    lia.
  }
  assert (Htotal_cols : (env_size + added_dims <= total_cols)%nat).
  {
    subst total_cols.
    pose proof
      (lift_schedule_after_env_exact_cols
         cols added_dims env_size before_sched Hsched_cols Henv_cols)
      as Hlift_cols.
    subst lifted.
    destruct
      (Tiling.lift_schedule_after_env added_dims env_size before_sched)
      as [|[coeffs rhs] rows].
    - lia.
    - assert (Hcoeffs : List.length coeffs = (added_dims + cols)%nat).
      {
        eapply Hlift_cols.
        - left. reflexivity.
        - reflexivity.
      }
      lia.
  }
  rewrite affine_product_app.
  rewrite affine_product_app.
  rewrite affine_product_app.
  rewrite affine_product_firstn.
  rewrite affine_product_firstn.
  rewrite !affine_product_skipn.
  rewrite
    (affine_product_identity_affine_rows_from
       total_cols env_size added_dims
       (env ++ interleave_root_child_tiles roots children ++ iters)).
  2:{ exact Htotal_cols. }
  2:{
    subst added_dims root_count.
    repeat rewrite app_length.
    rewrite interleave_root_child_tiles_length by exact Hlen.
    rewrite Henv, Hroots.
    lia.
  }
  rewrite Hlift.
  rewrite <- Henv.
  assert (Hskip_mid :
    skipn (List.length env)
      (env ++ interleave_root_child_tiles roots children ++ iters) =
    interleave_root_child_tiles roots children ++ iters).
  {
    replace
      (env ++ interleave_root_child_tiles roots children ++ iters)
      with
      (env ++ (interleave_root_child_tiles roots children ++ iters))
      by reflexivity.
    rewrite skipn_app_le by lia.
    replace (List.length env - List.length env)%nat with 0%nat by lia.
    simpl.
    reflexivity.
  }
  rewrite Hskip_mid.
  rewrite firstn_app.
  assert (Hadded_len :
    List.length (interleave_root_child_tiles roots children) = added_dims).
  {
    subst added_dims root_count.
    rewrite interleave_root_child_tiles_length by exact Hlen.
    rewrite Hroots.
    reflexivity.
  }
  replace
    (firstn added_dims (interleave_root_child_tiles roots children))
    with (interleave_root_child_tiles roots children).
  2:{
    rewrite <- Hadded_len.
    symmetry.
    apply firstn_all.
  }
  rewrite Hadded_len, Nat.sub_diag.
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma stripmine_second_level_schedule_after_env_by_layout_eval :
  forall layout env_size before_sched band cols env roots children iters,
    exact_listzzs_cols cols before_sched ->
    (env_size <= cols)%nat ->
    List.length env = env_size ->
    List.length roots = ptb_len band ->
    List.length roots = List.length children ->
    affine_product
      (stripmine_second_level_schedule_after_env_by_layout
         layout env_size before_sched band)
      (env ++ interleave_root_child_tiles roots children ++ iters) =
    let old_ts := affine_product before_sched (env ++ iters) in
    firstn (ptb_start band) old_ts ++
    match layout with
    | SecondLevelGrouped => children ++ roots
    | SecondLevelInterleaved => interleave_root_child_tiles roots children
    end ++
    firstn (ptb_len band) (skipn (ptb_start band) old_ts) ++
    skipn (ptb_start band + ptb_len band)%nat old_ts.
Proof.
  intros layout.
  destruct layout; simpl.
  - intros.
    pose proof
      (stripmine_second_level_schedule_after_env_eval
         env_size before_sched band cols env roots children iters
         H H0 H1 H2 H3) as Heval.
    repeat rewrite app_assoc in Heval.
    repeat rewrite app_assoc.
    exact Heval.
  - intros.
    pose proof
      (stripmine_second_level_schedule_interleaved_after_env_eval
         env_size before_sched band cols env roots children iters
         H H0 H1 H2 H3) as Heval.
    repeat rewrite app_assoc in Heval.
    repeat rewrite app_assoc.
    exact Heval.
Qed.

Lemma find_schedule_block_start_aux_sound :
  forall fuel start sched block found,
    find_schedule_block_start_aux fuel start sched block = Some found ->
    firstn (List.length block) (skipn found sched) = block.
Proof.
  induction fuel as [|fuel IH]; intros start sched block found Hfind.
  - simpl in Hfind. discriminate.
  - simpl in Hfind.
    destruct (listzzs_strict_eqb block (firstn (List.length block) (skipn start sched)))
      eqn:Hhere.
    + inversion Hfind; subst.
      apply listzzs_strict_eqb_eq in Hhere.
      symmetry. exact Hhere.
    + eapply IH; eauto.
Qed.

Lemma find_schedule_block_start_aux_bound :
  forall fuel start sched block found,
    find_schedule_block_start_aux fuel start sched block = Some found ->
    (found < start + fuel)%nat.
Proof.
  induction fuel as [|fuel IH]; intros start sched block found Hfind.
  - simpl in Hfind. discriminate.
  - simpl in Hfind.
    destruct (listzzs_strict_eqb block (firstn (List.length block) (skipn start sched)))
      eqn:Hhere.
    + inversion Hfind; subst. lia.
    + specialize (IH (S start) sched block found Hfind).
      lia.
Qed.

Lemma find_schedule_block_start_sound :
  forall sched block found,
    find_schedule_block_start sched block = Some found ->
    firstn (List.length block) (skipn found sched) = block.
Proof.
  intros sched block found Hfind.
  unfold find_schedule_block_start in Hfind.
  eapply find_schedule_block_start_aux_sound; eauto.
Qed.

Lemma find_schedule_block_start_bound :
  forall sched block found,
    find_schedule_block_start sched block = Some found ->
    (found <= List.length sched)%nat.
Proof.
  intros sched block found Hfind.
  unfold find_schedule_block_start in Hfind.
  pose proof (find_schedule_block_start_aux_bound _ _ _ _ _ Hfind) as Hbound.
  lia.
Qed.

Local Lemma find_schedule_block_start_fit :
  forall sched block found,
    find_schedule_block_start sched block = Some found ->
    (found + List.length block <= List.length sched)%nat.
Proof.
  intros sched block found Hfind.
  pose proof (find_schedule_block_start_bound _ _ _ Hfind) as Hstart.
  pose proof (find_schedule_block_start_sound _ _ _ Hfind) as Hblock.
  assert (Hblock_length :
    List.length (firstn (List.length block) (skipn found sched)) =
    List.length block).
  { rewrite Hblock. reflexivity. }
  rewrite firstn_length, skipn_length in Hblock_length.
  destruct
    (le_gt_dec (List.length block) (List.length sched - found)%nat).
  - lia.
  - rewrite Nat.min_r in Hblock_length by lia.
    lia.
Qed.

Definition infer_pinstr_tiling_band
    (before: Tiling.PL.PolyInstr)
    (w: statement_tiling_witness) : option pinstr_tiling_band :=
  match schedule_rows_of_links w with
  | Some rows =>
      match find_schedule_block_start
              (Tiling.PL.pi_schedule before)
              rows with
      | Some start =>
          Some {| ptb_start := start; ptb_len := List.length (stw_links w) |}
      | None => None
      end
  | None => None
  end.


Lemma infer_pinstr_tiling_band_bound :
  forall before w band,
    infer_pinstr_tiling_band before w = Some band ->
    (ptb_start band + ptb_len band <= List.length (Tiling.PL.pi_schedule before))%nat.
Proof.
  intros before w band Hinfer.
  unfold infer_pinstr_tiling_band in Hinfer.
  destruct (schedule_rows_of_links w) as [rows|] eqn:Hrows; try discriminate.
  destruct (find_schedule_block_start (Tiling.PL.pi_schedule before) rows)
    as [start|] eqn:Hstart; try discriminate.
  inversion Hinfer; subst; clear Hinfer.
  pose proof (schedule_rows_of_links_length _ _ Hrows) as Hrows_len.
  rewrite <- Hrows_len.
  eapply find_schedule_block_start_fit.
  exact Hstart.
Qed.

Definition check_pinstr_tiling_schedule_stripminedb
    (env_size: nat)
    (before after: Tiling.PL.PolyInstr)
    (w: statement_tiling_witness) : bool :=
  match infer_pinstr_tiling_band before w with
  | Some band =>
      check_schedule_with_trailing_zero_paddingb
        (stripmine_schedule_after_env env_size (Tiling.PL.pi_schedule before) band)
        (Tiling.PL.pi_schedule after)
  | None => false
  end.

Lemma check_schedule_with_trailing_zero_paddingb_sound :
  forall expected actual,
    check_schedule_with_trailing_zero_paddingb expected actual = true ->
    schedule_matches_with_trailing_zero_padding expected actual.
Proof.
  intros expected actual Hcheck.
  unfold check_schedule_with_trailing_zero_paddingb in Hcheck.
  destruct (Nat.leb (List.length expected) (List.length actual)) eqn:Hlen;
    try discriminate.
  exists
    (match actual with
     | [] => 0%nat
     | (coeffs, _) :: _ => List.length coeffs
     end).
  exists (List.length actual - List.length expected)%nat.
  apply listzzs_strict_eqb_eq in Hcheck.
  exact Hcheck.
Qed.

Lemma check_schedule_with_symmetric_trailing_zero_paddingb_sound :
  forall expected actual,
    check_schedule_with_symmetric_trailing_zero_paddingb expected actual = true ->
    schedule_matches_with_symmetric_trailing_zero_padding expected actual.
Proof.
  intros expected actual Hcheck.
  unfold check_schedule_with_symmetric_trailing_zero_paddingb in Hcheck.
  apply orb_true_iff in Hcheck.
  destruct Hcheck as [Hforward | Hreverse].
  - left.
    eapply check_schedule_with_trailing_zero_paddingb_sound.
    exact Hforward.
  - right.
    eapply check_schedule_with_trailing_zero_paddingb_sound.
    exact Hreverse.
Qed.

Lemma check_pinstr_tiling_schedule_stripminedb_sound :
  forall env_size before after w,
    check_pinstr_tiling_schedule_stripminedb env_size before after w = true ->
    exists band,
      infer_pinstr_tiling_band before w = Some band /\
      pinstr_tiling_band_matches before w band /\
      schedule_matches_with_trailing_zero_padding
        (stripmine_schedule_after_env env_size (Tiling.PL.pi_schedule before) band)
        (Tiling.PL.pi_schedule after).
Proof.
  intros env_size before after w Hcheck.
  unfold check_pinstr_tiling_schedule_stripminedb in Hcheck.
  destruct (infer_pinstr_tiling_band before w) as [band|] eqn:Hband;
    try discriminate.
  exists band.
  split.
  - reflexivity.
  - split.
    + unfold infer_pinstr_tiling_band in Hband.
      destruct (schedule_rows_of_links w) as [rows|] eqn:Hrows;
        try discriminate.
      destruct (find_schedule_block_start
                  (Tiling.PL.pi_schedule before)
                  rows) as [start|] eqn:Hstart;
        inversion Hband; subst; clear Hband.
      unfold pinstr_tiling_band_matches.
      rewrite Hrows.
      split.
      * reflexivity.
      * replace (List.length (stw_links w)) with (List.length rows).
        2:{ eapply schedule_rows_of_links_length; eauto. }
        eapply find_schedule_block_start_sound; eauto.
    + eapply check_schedule_with_trailing_zero_paddingb_sound.
      exact Hcheck.
Qed.

Lemma infer_pinstr_second_level_band_sound :
  forall before w band recipe,
    infer_pinstr_second_level_band before w = Some (band, recipe) ->
    second_level_band_recipe_spec
      (stw_point_dim w) O (stw_links w) recipe /\
    ptb_len band = List.length (slbr_root_rows recipe) /\
    firstn (ptb_len band)
      (skipn (ptb_start band) (Tiling.PL.pi_schedule before)) =
      slbr_root_rows recipe.
Proof.
  intros before w band recipe Hinfer.
  unfold infer_pinstr_second_level_band in Hinfer.
  destruct (second_level_band_recipe_of_witness w)
    as [recipe0|] eqn:Hrecipe; try discriminate.
  destruct
    (find_schedule_block_start
       (Tiling.PL.pi_schedule before) (slbr_root_rows recipe0))
    as [start|] eqn:Hstart; try discriminate.
  inversion Hinfer; subst band recipe0; clear Hinfer.
  destruct (second_level_band_recipe_of_witness_sound _ _ Hrecipe)
    as [_ Hspec].
  split; [exact Hspec|].
  split; [reflexivity|].
  eapply find_schedule_block_start_sound; exact Hstart.
Qed.

Lemma infer_pinstr_second_level_band_bound :
  forall before w band recipe,
    infer_pinstr_second_level_band before w = Some (band, recipe) ->
    (ptb_start band + ptb_len band <=
     List.length (Tiling.PL.pi_schedule before))%nat.
Proof.
  intros before w band recipe Hinfer.
  unfold infer_pinstr_second_level_band in Hinfer.
  destruct (second_level_band_recipe_of_witness w)
    as [recipe0|] eqn:Hrecipe; try discriminate.
  destruct
    (find_schedule_block_start
       (Tiling.PL.pi_schedule before) (slbr_root_rows recipe0))
    as [start|] eqn:Hstart; try discriminate.
  inversion Hinfer; subst band recipe0; clear Hinfer.
  simpl.
  eapply find_schedule_block_start_fit.
  exact Hstart.
Qed.



Lemma common_band_start_nth_error_equal :
  forall bands i j band1 band2,
    common_band_start bands ->
    nth_error bands i = Some band1 ->
    nth_error bands j = Some band2 ->
    ptb_start band1 = ptb_start band2.
Proof.
  intros bands i j band1 band2 [start Hstarts] Hband1 Hband2.
  pose proof
    (Tiling.Forall_nth_error
       _ (fun band => ptb_start band = start)
       bands i band1 Hstarts Hband1) as Hstart1.
  pose proof
    (Tiling.Forall_nth_error
       _ (fun band => ptb_start band = start)
       bands j band2 Hstarts Hband2) as Hstart2.
  congruence.
Qed.

Lemma infer_pinstr_list_second_level_bands_nth_error :
  forall before_pis ws bands recipes n before_pi w band recipe,
    infer_pinstr_list_second_level_bands before_pis ws =
      Some (bands, recipes) ->
    nth_error before_pis n = Some before_pi ->
    nth_error ws n = Some w ->
    nth_error bands n = Some band ->
    nth_error recipes n = Some recipe ->
    infer_pinstr_second_level_band before_pi w = Some (band, recipe).
Proof.
  induction before_pis as [|before_pi0 before_pis IH];
    intros ws bands recipes n before_pi w band recipe
           Hinfer Hbefore Hw Hband Hrecipe.
  - destruct n; discriminate.
  - destruct ws as [|w0 ws]; simpl in Hinfer; try discriminate.
    destruct (infer_pinstr_second_level_band before_pi0 w0)
      as [[band0 recipe0]|] eqn:Hhead; try discriminate.
    destruct (infer_pinstr_list_second_level_bands before_pis ws)
      as [[bands0 recipes0]|] eqn:Htail; try discriminate.
    inversion Hinfer; subst bands recipes; clear Hinfer.
    destruct n as [|n].
    + inversion Hbefore; inversion Hw; inversion Hband; inversion Hrecipe; subst.
      exact Hhead.
    + eapply IH; eauto.
Qed.

Lemma infer_pinstr_list_second_level_bands_lengths :
  forall before_pis ws bands recipes,
    infer_pinstr_list_second_level_bands before_pis ws =
      Some (bands, recipes) ->
    List.length before_pis = List.length ws /\
    List.length before_pis = List.length bands /\
    List.length before_pis = List.length recipes.
Proof.
  induction before_pis as [|before_pi before_pis IH];
    intros ws bands recipes Hinfer.
  - destruct ws; simpl in Hinfer; try discriminate.
    inversion Hinfer; subst. auto.
  - destruct ws as [|w ws]; simpl in Hinfer; try discriminate.
    destruct (infer_pinstr_second_level_band before_pi w); try discriminate.
    destruct p as [band recipe].
    destruct (infer_pinstr_list_second_level_bands before_pis ws)
      as [[bands' recipes']|] eqn:Htail; try discriminate.
    inversion Hinfer; subst bands recipes.
    specialize (IH ws bands' recipes' Htail).
    simpl. lia.
Qed.




Lemma check_pinstr_list_second_level_schedule_symmetricb_nth_error :
  forall layout env_size before_pis after_pis bands n
         before_pi after_pi band,
    check_pinstr_list_second_level_schedule_symmetricb
      layout env_size before_pis after_pis bands = true ->
    nth_error before_pis n = Some before_pi ->
    nth_error after_pis n = Some after_pi ->
    nth_error bands n = Some band ->
    schedule_matches_with_symmetric_trailing_zero_padding
      (stripmine_second_level_schedule_after_env_by_layout
         layout env_size (Tiling.PL.pi_schedule before_pi) band)
      (Tiling.PL.pi_schedule after_pi).
Proof.
  intros layout env_size before_pis.
  induction before_pis as [|before_pi0 before_pis IH];
    intros after_pis bands n before_pi after_pi band
           Hcheck Hbefore Hafter Hband.
  - destruct n; discriminate.
  - destruct after_pis as [|after_pi0 after_pis];
      destruct bands as [|band0 bands]; simpl in Hcheck; try discriminate.
    apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    destruct n as [|n].
    + inversion Hbefore; inversion Hafter; inversion Hband; subst.
      eapply check_schedule_with_symmetric_trailing_zero_paddingb_sound.
      exact Hhead.
    + eapply IH; eauto.
Qed.





Lemma list_bool_strict_eqb_eq :
  forall xs ys,
    list_bool_strict_eqb xs ys = true ->
    xs = ys.
Proof.
  induction xs as [|x xs IH]; intros ys Hcheck;
    destruct ys as [|y ys]; simpl in Hcheck; try discriminate.
  - reflexivity.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    destruct x, y; simpl in Hhead; try discriminate;
      f_equal; eapply IH; exact Htail.
Qed.

Lemma check_schedule_masks_eqb_sound :
  forall mask schedules,
    check_schedule_masks_eqb mask schedules = true ->
    Forall
      (fun sched => strict_zero_schedule_mask sched = mask)
      schedules.
Proof.
  intros mask schedules.
  induction schedules as [|sched schedules IH]; intros Hcheck.
  - constructor.
  - simpl in Hcheck.
    apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    constructor.
    + symmetry.
      eapply list_bool_strict_eqb_eq.
      exact Hhead.
    + eapply IH.
      exact Htail.
Qed.

Lemma check_schedule_lists_after_zero_erasureb_sound :
  forall expected actual,
    check_schedule_lists_after_zero_erasureb expected actual = true ->
    Forall2
      (fun expected_sched actual_sched =>
         Tiling.PL.remove_zero_schedule_dims expected_sched =
         Tiling.PL.remove_zero_schedule_dims actual_sched)
      expected actual.
Proof.
  intros expected.
  induction expected as [|expected_sched expected IH];
    intros actual Hcheck;
    destruct actual as [|actual_sched actual];
    simpl in Hcheck; try discriminate.
  - constructor.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    constructor.
    + eapply listzzs_strict_eqb_eq.
      exact Hhead.
    + eapply IH.
      exact Htail.
Qed.

Definition second_level_schedule_zero_erasure_match
    (layout: second_level_schedule_layout)
    (env_size: nat)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (bands: list pinstr_tiling_band) : Prop :=
  exists expected expected_mask actual_mask,
    second_level_expected_schedules
      layout env_size before_pis bands = Some expected /\
    Forall
      (fun sched => strict_zero_schedule_mask sched = expected_mask)
      expected /\
    Forall
      (fun sched => strict_zero_schedule_mask sched = actual_mask)
      (List.map Tiling.PL.pi_schedule after_pis) /\
    Forall2
      (fun expected_sched actual_sched =>
         Tiling.PL.remove_zero_schedule_dims expected_sched =
         Tiling.PL.remove_zero_schedule_dims actual_sched)
      expected (List.map Tiling.PL.pi_schedule after_pis).

Lemma check_pinstr_list_second_level_schedule_zero_erasureb_sound :
  forall layout env_size before_pis after_pis bands,
    check_pinstr_list_second_level_schedule_zero_erasureb
      layout env_size before_pis after_pis bands = true ->
    second_level_schedule_zero_erasure_match
      layout env_size before_pis after_pis bands.
Proof.
  intros layout env_size before_pis after_pis bands Hcheck.
  unfold check_pinstr_list_second_level_schedule_zero_erasureb in Hcheck.
  destruct
    (second_level_expected_schedules
       layout env_size before_pis bands)
    as [expected|] eqn:Hexpected; try discriminate.
  destruct expected as [|expected0 expected'].
  - destruct after_pis as [|after_pi after_pis]; try discriminate.
    exists [], [], [].
    repeat split; try constructor.
    exact Hexpected.
  - destruct after_pis as [|after0 after_pis]; try discriminate.
    simpl in Hcheck.
    repeat rewrite andb_true_iff in Hcheck.
    destruct Hcheck as [[Hexpected_masks Hactual_masks] Hpairs].
    exists
      (expected0 :: expected'),
      (strict_zero_schedule_mask expected0),
      (strict_zero_schedule_mask (Tiling.PL.pi_schedule after0)).
    repeat split.
    + exact Hexpected.
    + constructor.
      * reflexivity.
      * eapply check_schedule_masks_eqb_sound.
        exact Hexpected_masks.
    + constructor.
      * reflexivity.
      * eapply check_schedule_masks_eqb_sound.
        exact Hactual_masks.
    + eapply check_schedule_lists_after_zero_erasureb_sound.
      simpl.
      apply andb_true_iff.
      exact Hpairs.
Qed.

Lemma second_level_expected_schedules_nth_error :
  forall layout env_size before_pis bands expected
         n before_pi band,
    second_level_expected_schedules
      layout env_size before_pis bands = Some expected ->
    nth_error before_pis n = Some before_pi ->
    nth_error bands n = Some band ->
    nth_error expected n =
      Some
        (stripmine_second_level_schedule_after_env_by_layout
           layout env_size (Tiling.PL.pi_schedule before_pi) band).
Proof.
  intros layout env_size before_pis.
  induction before_pis as [|before0 before_pis IH];
    intros bands expected n before_pi band
           Hexpected Hbefore Hband.
  - destruct n; discriminate.
  - destruct bands as [|band0 bands]; simpl in Hexpected; try discriminate.
    destruct
      (second_level_expected_schedules
         layout env_size before_pis bands)
      as [expected'|] eqn:Htail; try discriminate.
    inversion Hexpected; subst expected; clear Hexpected.
    destruct n as [|n].
    + inversion Hbefore; inversion Hband; subst.
      reflexivity.
    + simpl in Hbefore, Hband.
      eapply IH with (expected := expected'); eauto.
Qed.

Lemma affine_function_is_zero_eval_for_erasure :
  forall row idx,
    Tiling.PL.affine_function_is_zero row = true ->
    (Linalg.dot_product (fst row) idx + snd row)%Z = 0%Z.
Proof.
  intros [coeffs c] idx Hzero.
  unfold Tiling.PL.affine_function_is_zero in Hzero.
  simpl in Hzero.
  apply andb_true_iff in Hzero.
  destruct Hzero as [Hcoeffs Hc].
  apply Z.eqb_eq in Hc.
  subst c.
  change (Linalg.dot_product coeffs idx + 0 = 0)%Z.
  revert idx.
  induction coeffs as [|x coeffs IH]; intros idx.
  - rewrite Linalg.dot_product_nil_left. reflexivity.
  - change
      (Z.eqb 0%Z x && forallb (Z.eqb 0%Z) coeffs = true)
      in Hcoeffs.
    apply andb_true_iff in Hcoeffs.
    destruct Hcoeffs as [Hx Htail].
    apply Z.eqb_eq in Hx.
    subst x.
    destruct idx as [|value idx].
    + reflexivity.
    + cbn.
      eapply IH.
      exact Htail.
Qed.

Lemma lex_compare_affine_product_remove_zero_same_mask :
  forall sched1 sched2 idx1 idx2,
    strict_zero_schedule_mask sched1 =
      strict_zero_schedule_mask sched2 ->
    lex_compare
      (affine_product sched1 idx1)
      (affine_product sched2 idx2) =
    lex_compare
      (affine_product
         (Tiling.PL.remove_zero_schedule_dims sched1) idx1)
      (affine_product
         (Tiling.PL.remove_zero_schedule_dims sched2) idx2).
Proof.
  intros sched1.
  induction sched1 as [|row1 sched1 IH];
    intros sched2 idx1 idx2 Hmask;
    destruct sched2 as [|row2 sched2]; simpl in Hmask; try discriminate.
  - reflexivity.
  - injection Hmask as Hhead Htail.
    destruct (Tiling.PL.affine_function_is_zero row1)
      eqn:Hzero1;
      destruct (Tiling.PL.affine_function_is_zero row2)
      eqn:Hzero2;
      try discriminate.
    + unfold Tiling.PL.remove_zero_schedule_dims.
      simpl.
      rewrite Hzero1, Hzero2.
      unfold affine_product at 1 2.
      simpl.
      rewrite
        (affine_function_is_zero_eval_for_erasure
           row1 idx1 Hzero1).
      rewrite
        (affine_function_is_zero_eval_for_erasure
           row2 idx2 Hzero2).
      simpl.
      eapply IH.
      exact Htail.
    + unfold Tiling.PL.remove_zero_schedule_dims.
      simpl.
      rewrite Hzero1, Hzero2.
      unfold affine_product.
      simpl.
      destruct
        ((Linalg.dot_product (fst row1) idx1 + snd row1)%Z
           ?=
         (Linalg.dot_product (fst row2) idx2 + snd row2)%Z);
        try reflexivity.
      eapply IH.
      exact Htail.
Qed.

Definition second_level_schedule_layout_lex_equivalent
    (layout: second_level_schedule_layout)
    (env_size: nat)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (bands: list pinstr_tiling_band) : Prop :=
  forall i j before_i after_i band_i before_j after_j band_j idx_i idx_j,
    nth_error before_pis i = Some before_i ->
    nth_error after_pis i = Some after_i ->
    nth_error bands i = Some band_i ->
    nth_error before_pis j = Some before_j ->
    nth_error after_pis j = Some after_j ->
    nth_error bands j = Some band_j ->
    lex_compare
      (affine_product (Tiling.PL.pi_schedule after_i) idx_i)
      (affine_product (Tiling.PL.pi_schedule after_j) idx_j) =
    lex_compare
      (affine_product
         (stripmine_second_level_schedule_after_env_by_layout
            layout env_size (Tiling.PL.pi_schedule before_i) band_i)
         idx_i)
      (affine_product
         (stripmine_second_level_schedule_after_env_by_layout
            layout env_size (Tiling.PL.pi_schedule before_j) band_j)
         idx_j).

Lemma zero_erasure_second_level_schedule_layout_lex_equivalent :
  forall layout env_size before_pis after_pis bands,
    second_level_schedule_zero_erasure_match
      layout env_size before_pis after_pis bands ->
    second_level_schedule_layout_lex_equivalent
      layout env_size before_pis after_pis bands.
Proof.
  intros layout env_size before_pis after_pis bands
         [expected [expected_mask [actual_mask
          [Hexpected [Hexpected_masks [Hactual_masks Hpairs]]]]]].
  unfold second_level_schedule_layout_lex_equivalent.
  intros i j before_i after_i band_i before_j after_j band_j idx_i idx_j
         Hbefore_i Hafter_i Hband_i Hbefore_j Hafter_j Hband_j.
  pose proof
    (second_level_expected_schedules_nth_error
       layout env_size before_pis bands expected
       i before_i band_i Hexpected Hbefore_i Hband_i)
    as Hexpected_i.
  pose proof
    (second_level_expected_schedules_nth_error
       layout env_size before_pis bands expected
       j before_j band_j Hexpected Hbefore_j Hband_j)
    as Hexpected_j.
  pose proof
    (Tiling.nth_error_map_some
       _ _ Tiling.PL.pi_schedule after_pis
       i after_i Hafter_i) as Hactual_i.
  pose proof
    (Tiling.nth_error_map_some
       _ _ Tiling.PL.pi_schedule after_pis
       j after_j Hafter_j) as Hactual_j.
  pose proof
    (Tiling.Forall_nth_error
       _ _ expected i
       (stripmine_second_level_schedule_after_env_by_layout
          layout env_size (Tiling.PL.pi_schedule before_i) band_i)
       Hexpected_masks Hexpected_i) as Hexpected_mask_i.
  pose proof
    (Tiling.Forall_nth_error
       _ _ expected j
       (stripmine_second_level_schedule_after_env_by_layout
          layout env_size (Tiling.PL.pi_schedule before_j) band_j)
       Hexpected_masks Hexpected_j) as Hexpected_mask_j.
  pose proof
    (Tiling.Forall_nth_error
       _ _ (List.map Tiling.PL.pi_schedule after_pis) i
       (Tiling.PL.pi_schedule after_i)
       Hactual_masks Hactual_i) as Hactual_mask_i.
  pose proof
    (Tiling.Forall_nth_error
       _ _ (List.map Tiling.PL.pi_schedule after_pis) j
       (Tiling.PL.pi_schedule after_j)
       Hactual_masks Hactual_j) as Hactual_mask_j.
  pose proof
    (Tiling.Forall2_nth_error
       _ _
       (fun expected_sched actual_sched =>
          Tiling.PL.remove_zero_schedule_dims expected_sched =
          Tiling.PL.remove_zero_schedule_dims actual_sched)
       expected (List.map Tiling.PL.pi_schedule after_pis)
       i
       (stripmine_second_level_schedule_after_env_by_layout
          layout env_size (Tiling.PL.pi_schedule before_i) band_i)
       (Tiling.PL.pi_schedule after_i)
       Hpairs Hexpected_i Hactual_i) as Hpair_i.
  pose proof
    (Tiling.Forall2_nth_error
       _ _
       (fun expected_sched actual_sched =>
          Tiling.PL.remove_zero_schedule_dims expected_sched =
          Tiling.PL.remove_zero_schedule_dims actual_sched)
       expected (List.map Tiling.PL.pi_schedule after_pis)
       j
       (stripmine_second_level_schedule_after_env_by_layout
          layout env_size (Tiling.PL.pi_schedule before_j) band_j)
       (Tiling.PL.pi_schedule after_j)
       Hpairs Hexpected_j Hactual_j) as Hpair_j.
  pose proof
    (lex_compare_affine_product_remove_zero_same_mask
       (Tiling.PL.pi_schedule after_i)
       (Tiling.PL.pi_schedule after_j)
       idx_i idx_j
       (eq_trans Hactual_mask_i (eq_sym Hactual_mask_j)))
    as Hactual_compact.
  pose proof
    (lex_compare_affine_product_remove_zero_same_mask
       (stripmine_second_level_schedule_after_env_by_layout
          layout env_size (Tiling.PL.pi_schedule before_i) band_i)
       (stripmine_second_level_schedule_after_env_by_layout
          layout env_size (Tiling.PL.pi_schedule before_j) band_j)
       idx_i idx_j
       (eq_trans Hexpected_mask_i (eq_sym Hexpected_mask_j)))
    as Hexpected_compact.
  rewrite Hactual_compact.
  rewrite <- Hpair_i, <- Hpair_j.
  symmetry.
  exact Hexpected_compact.
Qed.

Lemma check_pprog_second_level_schedule_directb_sound :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws bands recipes layout,
    check_pprog_second_level_schedule_directb
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      ws = Some (bands, recipes, layout) ->
    infer_pinstr_list_second_level_bands before_pis ws =
      Some (bands, recipes) /\
    check_pinstr_list_second_level_schedule_directb
      layout (List.length before_ctxt) before_pis after_pis bands = true /\
    common_second_level_recipe_sizes recipes /\
    common_band_start bands.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws bands recipes layout Hcheck.
  unfold check_pprog_second_level_schedule_directb in Hcheck.
  destruct
    (TilingCheck.ctxt_eqb before_ctxt after_ctxt &&
     TilingCheck.ctxt_ty_eqb before_vars after_vars) eqn:Hctxt;
    try discriminate.
  destruct (infer_pinstr_list_second_level_bands before_pis ws)
    as [[bands0 recipes0]|] eqn:Hinfer; try discriminate.
  destruct (check_common_second_level_recipe_sizesb recipes0)
    eqn:Hsizes; try discriminate.
  destruct (check_common_band_startb bands0) eqn:Hstart; try discriminate.
  destruct
    (check_pinstr_list_second_level_schedule_directb
       SecondLevelGrouped (List.length before_ctxt)
       before_pis after_pis bands0)
    eqn:Hgrouped.
  - inversion Hcheck; subst bands recipes layout.
    repeat split; auto.
    + eapply check_common_second_level_recipe_sizesb_sound. exact Hsizes.
    + eapply check_common_band_startb_sound. exact Hstart.
  - destruct
      (check_pinstr_list_second_level_schedule_directb
         SecondLevelInterleaved (List.length before_ctxt)
         before_pis after_pis bands0)
      eqn:Hinterleaved; try discriminate.
    inversion Hcheck; subst bands recipes layout.
    repeat split; auto.
    + eapply check_common_second_level_recipe_sizesb_sound. exact Hsizes.
    + eapply check_common_band_startb_sound. exact Hstart.
Qed.

Fixpoint check_pinstr_list_tiling_schedule_stripminedb
    (env_size: nat)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness) : bool :=
  match before_pis, after_pis, ws with
  | [], [], [] => true
  | before_pi :: before_pis', after_pi :: after_pis', w :: ws' =>
      check_pinstr_tiling_schedule_stripminedb env_size before_pi after_pi w &&
      check_pinstr_list_tiling_schedule_stripminedb
        env_size before_pis' after_pis' ws'
  | _, _, _ => false
  end.

Fixpoint infer_pinstr_list_tiling_bands
    (before_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    : option (list pinstr_tiling_band) :=
  match before_pis, ws with
  | [], [] => Some []
  | before_pi :: before_pis', w :: ws' =>
      match infer_pinstr_tiling_band before_pi w,
            infer_pinstr_list_tiling_bands before_pis' ws' with
      | Some band, Some bands' => Some (band :: bands')
      | _, _ => None
      end
  | _, _ => None
  end.

Definition check_pprog_tiling_schedule_stripminedb
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness) : bool :=
  let '(before_pis, before_ctxt, before_vars) := before in
  let '(after_pis, after_ctxt, after_vars) := after in
  TilingCheck.ctxt_eqb before_ctxt after_ctxt &&
  TilingCheck.ctxt_ty_eqb before_vars after_vars &&
  check_pinstr_list_tiling_schedule_stripminedb
    (List.length before_ctxt) before_pis after_pis ws.

Definition infer_pprog_tiling_bands
    (before: Tiling.PL.t)
    (ws: list statement_tiling_witness)
    : option (list pinstr_tiling_band) :=
  let '(before_pis, _, _) := before in
  infer_pinstr_list_tiling_bands before_pis ws.

Lemma infer_pinstr_list_tiling_bands_lengths :
  forall before_pis ws bands,
    infer_pinstr_list_tiling_bands before_pis ws = Some bands ->
    List.length before_pis = List.length ws /\
    List.length before_pis = List.length bands.
Proof.
  induction before_pis as [|before_pi before_pis' IH];
    intros ws bands Hinfer.
  - destruct ws, bands; simpl in Hinfer; inversion Hinfer; subst; auto.
  - destruct ws as [|w ws']; simpl in Hinfer; try discriminate.
    destruct (infer_pinstr_tiling_band before_pi w) as [band|] eqn:Hband;
      try discriminate.
    destruct (infer_pinstr_list_tiling_bands before_pis' ws') as [bands'|] eqn:Hbands;
      try discriminate.
    inversion Hinfer; subst; clear Hinfer.
    destruct (IH _ _ Hbands) as [Hlen_ws Hlen_bands].
    split; simpl; lia.
Qed.

Lemma infer_pinstr_list_tiling_bands_nth_error :
  forall before_pis ws bands n before_pi w band,
    infer_pinstr_list_tiling_bands before_pis ws = Some bands ->
    nth_error before_pis n = Some before_pi ->
    nth_error ws n = Some w ->
    nth_error bands n = Some band ->
    infer_pinstr_tiling_band before_pi w = Some band.
Proof.
  induction before_pis as [|before_pi0 before_pis' IH];
    intros ws bands n before_pi w band Hinfer Hbefore Hw Hband.
  - destruct n; simpl in Hbefore; discriminate.
  - destruct ws as [|w0 ws']; simpl in Hinfer; try discriminate.
    destruct (infer_pinstr_tiling_band before_pi0 w0) as [band0|] eqn:Hhd; try discriminate.
    destruct (infer_pinstr_list_tiling_bands before_pis' ws') as [bands'|] eqn:Htl;
      try discriminate.
    inversion Hinfer; subst; clear Hinfer.
    destruct n as [|n']; simpl in *.
    + now inversion Hbefore; inversion Hw; inversion Hband; subst.
    + eapply IH; eauto.
Qed.

Fixpoint rel_list4
    {A B C D: Type}
    (R: A -> B -> C -> D -> Prop)
    (la: list A) (lb: list B) (lc: list C) (ld: list D) : Prop :=
  match la, lb, lc, ld with
  | [], [], [], [] => True
  | a :: la', b :: lb', c :: lc', d :: ld' =>
      R a b c d /\ rel_list4 R la' lb' lc' ld'
  | _, _, _, _ => False
  end.

Definition pinstr_tiling_band_cert
    (env_size: nat)
    (before after: Tiling.PL.PolyInstr)
    (w: statement_tiling_witness)
    (band: pinstr_tiling_band) : Prop :=
  pinstr_tiling_band_matches before w band /\
  schedule_matches_with_trailing_zero_padding
    (stripmine_schedule_after_env env_size (Tiling.PL.pi_schedule before) band)
    (Tiling.PL.pi_schedule after).

Definition pprog_tiling_bands_cert
    (env_size: nat)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (bands: list pinstr_tiling_band) : Prop :=
  rel_list4
    (pinstr_tiling_band_cert env_size)
    before_pis after_pis ws bands.


Lemma pprog_tiling_bands_cert_lengths :
  forall env_size before_pis after_pis ws bands,
    pprog_tiling_bands_cert env_size before_pis after_pis ws bands ->
    List.length before_pis = List.length after_pis /\
    List.length before_pis = List.length ws /\
    List.length before_pis = List.length bands.
Proof.
  induction before_pis as [|before_pi before_pis' IH];
    intros after_pis ws bands Hcert.
  - destruct after_pis, ws, bands; simpl in *; try contradiction; repeat split; reflexivity.
  - destruct after_pis as [|after_pi after_pis']; simpl in *; try contradiction.
    destruct ws as [|w ws']; simpl in *; try contradiction.
    destruct bands as [|band bands']; simpl in *; try contradiction.
    destruct Hcert as [_ Hcert'].
    destruct (IH _ _ _ Hcert') as [Hlen_after [Hlen_ws Hlen_bands]].
    repeat split; simpl; lia.
Qed.

Lemma pprog_tiling_bands_cert_nth_error :
  forall env_size before_pis after_pis ws bands
         n before_pi after_pi w band,
    pprog_tiling_bands_cert env_size before_pis after_pis ws bands ->
    nth_error before_pis n = Some before_pi ->
    nth_error after_pis n = Some after_pi ->
    nth_error ws n = Some w ->
    nth_error bands n = Some band ->
    pinstr_tiling_band_cert env_size before_pi after_pi w band.
Proof.
  induction before_pis as [|before_pi0 before_pis' IH];
    intros after_pis ws bands n before_pi after_pi w band
           Hcert Hbefore Hafter Hw Hband.
  - destruct n; simpl in Hbefore; discriminate.
  - destruct after_pis as [|after_pi0 after_pis']; [destruct n; simpl in Hafter; discriminate|].
    destruct ws as [|w0 ws']; [destruct n; simpl in Hw; discriminate|].
    destruct bands as [|band0 bands']; [destruct n; simpl in Hband; discriminate|].
    simpl in *.
    destruct n as [|n']; simpl in *.
    + unfold pprog_tiling_bands_cert in Hcert.
      simpl in Hcert.
      inversion Hbefore; inversion Hafter; inversion Hw; inversion Hband; subst.
      exact (proj1 Hcert).
    + destruct Hcert as [_ Hcert'].
      eapply IH; eauto.
Qed.


End SecondLevelShapeRecognition.

(** * Projected schedules and composed-point witnesses

    The endpoint package [composed_point_facts] is reused by each later layout
    reversal bridge. *)

Section ProjectedScheduleBridge.





Definition pprog_permutable_tiling_bands
    (envv: list Z)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (_bands: list pinstr_tiling_band) : Prop :=
  forall ipl_ext tau1 tau2,
    Tiling.PL.flatten_instrs_ext
      envv
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length envv) before_pis after_pis ws)
      ipl_ext ->
    In tau1 ipl_ext ->
      In tau2 ipl_ext ->
    Tiling.PL.instr_point_ext_old_sched_lt tau1 tau2 ->
    Tiling.PL.instr_point_ext_new_sched_ge tau1 tau2 ->
    Tiling.PL.Permutable_ext tau1 tau2.

Definition pprog_tiling_reordering_safe :=
  pprog_permutable_tiling_bands.

Definition uniform_schedule_arity
    (pis: list Tiling.PL.PolyInstr) : Prop :=
  exists len,
    Forall (fun pi => List.length (Tiling.PL.pi_schedule pi) = len) pis.

Fixpoint check_pinstr_list_schedule_len_eq
    (pis: list Tiling.PL.PolyInstr)
    (len: nat) : bool :=
  match pis with
  | [] => true
  | pi :: pis' =>
      Nat.eqb (List.length (Tiling.PL.pi_schedule pi)) len &&
      check_pinstr_list_schedule_len_eq pis' len
  end.

Definition check_uniform_schedule_arityb
    (pis: list Tiling.PL.PolyInstr) : bool :=
  match pis with
  | [] => true
  | pi :: pis' =>
      check_pinstr_list_schedule_len_eq
        pis' (List.length (Tiling.PL.pi_schedule pi))
  end.

Lemma check_pinstr_list_schedule_len_eq_sound :
  forall pis len,
    check_pinstr_list_schedule_len_eq pis len = true ->
    Forall (fun pi => List.length (Tiling.PL.pi_schedule pi) = len) pis.
Proof.
  induction pis as [|pi pis IH]; intros len Hcheck; simpl in *.
  - constructor.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    constructor.
    + apply Nat.eqb_eq. exact Hhead.
    + eapply IH. exact Htail.
Qed.

Lemma check_uniform_schedule_arityb_sound :
  forall pis,
    check_uniform_schedule_arityb pis = true ->
    uniform_schedule_arity pis.
Proof.
  intros pis Hcheck.
  destruct pis as [|pi pis].
  - exists 0%nat. constructor.
  - exists (List.length (Tiling.PL.pi_schedule pi)).
    constructor.
    + reflexivity.
    + eapply check_pinstr_list_schedule_len_eq_sound.
      exact Hcheck.
Qed.

Lemma uniform_schedule_arity_nth_error :
  forall pis len n pi,
    Forall (fun pi0 => List.length (Tiling.PL.pi_schedule pi0) = len) pis ->
    nth_error pis n = Some pi ->
    List.length (Tiling.PL.pi_schedule pi) = len.
Proof.
  intros pis len n pi Hlen Hnth.
  eapply Forall_forall in Hlen.
  - exact Hlen.
  - eapply nth_error_In; eauto.
Qed.

Definition instr_point_ext_band_prefix_ts
    (band: pinstr_tiling_band)
    (tau: Tiling.PL.InstrPoint_ext) : list Z :=
  firstn (ptb_start band) (Tiling.PL.ip_time_stamp1_ext tau).

Definition instr_point_ext_band_block_ts
    (band: pinstr_tiling_band)
    (tau: Tiling.PL.InstrPoint_ext) : list Z :=
  firstn (ptb_len band)
    (skipn (ptb_start band) (Tiling.PL.ip_time_stamp1_ext tau)).

Definition instr_point_ext_same_band_slice
    (band: pinstr_tiling_band)
    (tau1 tau2: Tiling.PL.InstrPoint_ext) : Prop :=
  instr_point_ext_band_prefix_ts band tau1 =
  instr_point_ext_band_prefix_ts band tau2.

Definition instr_point_ext_band_component_decreases_at
    (band: pinstr_tiling_band)
    (dim: nat)
    (tau1 tau2: Tiling.PL.InstrPoint_ext) : Prop :=
  exists x y,
    (dim < ptb_len band)%nat /\
    nth_error
      (Tiling.PL.ip_time_stamp1_ext tau1)
      (ptb_start band + dim)%nat = Some x /\
    nth_error
      (Tiling.PL.ip_time_stamp1_ext tau2)
      (ptb_start band + dim)%nat = Some y /\
    (x > y)%Z.

Definition instr_point_ext_band_component_decreases
    (band: pinstr_tiling_band)
    (tau1 tau2: Tiling.PL.InstrPoint_ext) : Prop :=
  exists dim,
    instr_point_ext_band_component_decreases_at band dim tau1 tau2.


Lemma nth_error_firstn_local :
  forall (A: Type) limit (xs: list A) n,
    (n < limit)%nat ->
    nth_error (firstn limit xs) n = nth_error xs n.
Proof.
  intros A limit.
  induction limit as [|limit IH]; intros xs n Hlt; [lia|].
  destruct xs as [|x xs]; [destruct n; reflexivity|].
  destruct n as [|n]; [reflexivity|].
  simpl.
  eapply IH.
  lia.
Qed.

Lemma nth_error_skipn_local :
  forall (A: Type) start (xs: list A) n,
    nth_error (skipn start xs) n = nth_error xs (start + n)%nat.
Proof.
  intros A start.
  induction start as [|start IH]; intros xs n.
  - reflexivity.
  - destruct xs as [|x xs].
    + rewrite skipn_nil. destruct n; reflexivity.
    + simpl. rewrite IH. reflexivity.
Qed.

Lemma nth_error_band_block_to_full :
  forall band (ts: list Z) dim x,
    (dim < ptb_len band)%nat ->
    nth_error
      (firstn (ptb_len band) (skipn (ptb_start band) ts))
      dim = Some x ->
    nth_error ts (ptb_start band + dim)%nat = Some x.
Proof.
  intros band ts dim x Hdim Hnth.
  rewrite nth_error_firstn_local in Hnth by exact Hdim.
  rewrite nth_error_skipn_local in Hnth.
  exact Hnth.
Qed.






Lemma firstn_add_local :
  forall (A: Type) n m (xs: list A),
    firstn (n + m) xs =
    firstn n xs ++ firstn m (skipn n xs).
Proof.
  intros A n.
  induction n as [|n IH]; intros m xs.
  - reflexivity.
  - destruct xs as [|x xs]; simpl.
    + destruct m; reflexivity.
    + rewrite IH. reflexivity.
Qed.



Definition pprog_pluto_permutable_band
    (envv: list Z)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (band: pinstr_tiling_band) : Prop :=
  forall ipl_ext tau1 tau2,
    Tiling.PL.flatten_instrs_ext
      envv
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length envv) before_pis after_pis ws)
      ipl_ext ->
    In tau1 ipl_ext ->
    In tau2 ipl_ext ->
    Tiling.PL.instr_point_ext_old_sched_lt tau1 tau2 ->
    instr_point_ext_same_band_slice band tau1 tau2 ->
    instr_point_ext_band_component_decreases band tau1 tau2 ->
    Tiling.PL.Permutable_ext tau1 tau2.

Definition pprog_pluto_componentwise_permutable_band
    (envv: list Z)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (band: pinstr_tiling_band) : Prop :=
  pprog_pluto_permutable_band envv before_pis after_pis ws band.

Definition pprog_pluto_componentwise_permutable_bands
    (envv: list Z)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (bands: list pinstr_tiling_band) : Prop :=
  forall ipl_ext tau1 tau2 band,
    Tiling.PL.flatten_instrs_ext
      envv
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length envv) before_pis after_pis ws)
      ipl_ext ->
    In tau1 ipl_ext ->
    In tau2 ipl_ext ->
    nth_error bands (Tiling.PL.ip_nth_ext tau1) = Some band ->
    nth_error bands (Tiling.PL.ip_nth_ext tau2) = Some band ->
    Tiling.PL.instr_point_ext_old_sched_lt tau1 tau2 ->
    instr_point_ext_same_band_slice band tau1 tau2 ->
    instr_point_ext_band_component_decreases band tau1 tau2 ->
    Tiling.PL.Permutable_ext tau1 tau2.

Lemma pprog_pluto_componentwise_permutable_bands_implies_reordering_safe_if_local_bridge :
  forall envv before_pis after_pis ws bands,
    pprog_pluto_componentwise_permutable_bands
      envv before_pis after_pis ws bands ->
    (forall ipl_ext tau1 tau2,
       Tiling.PL.flatten_instrs_ext
         envv
         (Tiling.compose_tiling_pinstrs_ext_from_after
            (List.length envv) before_pis after_pis ws)
         ipl_ext ->
       In tau1 ipl_ext ->
       In tau2 ipl_ext ->
       Tiling.PL.instr_point_ext_old_sched_lt tau1 tau2 ->
       Tiling.PL.instr_point_ext_new_sched_ge tau1 tau2 ->
       exists band,
         nth_error bands (Tiling.PL.ip_nth_ext tau1) = Some band /\
         nth_error bands (Tiling.PL.ip_nth_ext tau2) = Some band /\
         instr_point_ext_same_band_slice band tau1 tau2 /\
         instr_point_ext_band_component_decreases band tau1 tau2) ->
    pprog_tiling_reordering_safe envv before_pis after_pis ws bands.
Proof.
  intros envv before_pis after_pis ws bands Hperm Hlocal.
  unfold pprog_tiling_reordering_safe, pprog_permutable_tiling_bands.
  intros ipl_ext tau1 tau2 Hflat Hin1 Hin2 Hold Hnew.
  destruct (Hlocal ipl_ext tau1 tau2 Hflat Hin1 Hin2 Hold Hnew)
    as [band [Hband1 [Hband2 [Hprefix Hcomponent]]]].
  eapply Hperm; eauto.
Qed.

Definition common_tiling_band_recipe_with
    (sizes: list Z)
    (ws: list statement_tiling_witness) : Prop :=
  Forall (fun w => List.map tl_tile_size (stw_links w) = sizes) ws.

Definition common_tiling_band_recipe
    (ws: list statement_tiling_witness) : Prop :=
  exists sizes, common_tiling_band_recipe_with sizes ws.

Lemma check_common_tiling_band_recipe_withb_sound :
  forall sizes ws,
    check_common_tiling_band_recipe_withb sizes ws = true ->
    common_tiling_band_recipe_with sizes ws.
Proof.
  intros sizes ws.
  induction ws as [|w ws IH]; intros Hcheck; simpl in *.
  - constructor.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    constructor.
    + unfold tile_sizes_of_witness in Hhead.
      symmetry.
      eapply listz_strict_eqb_eq; exact Hhead.
    + eapply IH; exact Htail.
Qed.

Lemma check_common_tiling_band_recipeb_sound :
  forall ws,
    check_common_tiling_band_recipeb ws = true ->
    common_tiling_band_recipe ws.
Proof.
  intros ws Hcheck.
  destruct ws as [|w ws].
  - exists []; constructor.
  - exists (tile_sizes_of_witness w).
    constructor.
    + reflexivity.
    + eapply check_common_tiling_band_recipe_withb_sound.
      exact Hcheck.
Qed.

Definition pprog_pluto_permutable_tiling_bands_strong
    (envv: list Z)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (bands: list pinstr_tiling_band) : Prop :=
  exists band sizes,
    common_tiling_band bands band /\
    common_tiling_band_recipe_with sizes ws /\
    pprog_pluto_permutable_band envv before_pis after_pis ws band.

Lemma lex_compare_eq_same_length_implies_eq_local_band :
  forall t1 t2,
    lex_compare t1 t2 = Eq ->
    List.length t1 = List.length t2 ->
    t1 = t2.
Proof.
  induction t1 as [|x t1 IH]; intros t2 Hcmp Hlen.
  - destruct t2 as [|y t2].
    + reflexivity.
    + simpl in Hlen. discriminate.
  - destruct t2 as [|y t2].
    + simpl in Hlen. discriminate.
    + simpl in Hcmp.
      destruct (Z.compare x y) eqn:Hxy; try discriminate.
      apply Z.compare_eq_iff in Hxy.
      subst y.
      f_equal.
      eapply IH.
      * exact Hcmp.
      * simpl in Hlen. lia.
Qed.

Lemma preserved_equal_length_prefix_reversal_implies_prefix_eq :
  forall prefix1 prefix2 old_rest1 old_rest2 new_rest1 new_rest2,
    List.length prefix1 = List.length prefix2 ->
    lex_compare (prefix1 ++ old_rest1) (prefix2 ++ old_rest2) = Lt ->
    lex_compare (prefix1 ++ new_rest1) (prefix2 ++ new_rest2) <> Lt ->
    prefix1 = prefix2.
Proof.
  intros prefix1 prefix2 old_rest1 old_rest2 new_rest1 new_rest2
         Hlen Hold Hnew.
  destruct (lex_compare prefix1 prefix2) eqn:Hprefix.
  - eapply lex_compare_eq_same_length_implies_eq_local_band; eauto.
  - exfalso. apply Hnew.
    rewrite lex_compare_app by exact Hlen.
    rewrite Hprefix.
    reflexivity.
  - exfalso. rewrite lex_compare_app in Hold by exact Hlen.
    rewrite Hprefix in Hold.
    discriminate.
Qed.

(** The synthetic component schedule characterizes exactly the local Pluto
    band obligation when the selected component exists in both timestamps.
    The length hypotheses are essential because [lex_compare] zero-extends
    lists of different lengths. *)

Lemma stripmined_reversal_implies_prefix_eq_and_band_lt :
  forall prefix1 prefix2 tiles1 tiles2 band1 band2 suffix1 suffix2,
    List.length prefix1 = List.length prefix2 ->
    List.length band1 = List.length band2 ->
    (band1 = band2 -> tiles1 = tiles2) ->
    lex_compare
      (prefix1 ++ band1 ++ suffix1)
      (prefix2 ++ band2 ++ suffix2) = Lt ->
    lex_compare
      (prefix1 ++ tiles1 ++ band1 ++ suffix1)
      (prefix2 ++ tiles2 ++ band2 ++ suffix2) <> Lt ->
    prefix1 = prefix2 /\ lex_compare band1 band2 = Lt.
Proof.
  intros prefix1 prefix2 tiles1 tiles2 band1 band2 suffix1 suffix2
         Hprefix_len Hband_len Htiles_eq Hold Hnew.
  destruct (lex_compare prefix1 prefix2) eqn:Hprefix_cmp.
  - assert (prefix1 = prefix2).
    {
      eapply lex_compare_eq_same_length_implies_eq_local_band; eauto.
    }
    subst prefix2.
    destruct (lex_compare band1 band2) eqn:Hband_cmp.
    + assert (band1 = band2).
      {
        eapply lex_compare_eq_same_length_implies_eq_local_band; eauto.
      }
      subst band2.
      assert (tiles1 = tiles2) by auto.
      subst tiles2.
      assert (Hsuffix_lt : lex_compare suffix1 suffix2 = Lt).
      {
        rewrite lex_compare_app in Hold by exact Hprefix_len.
        rewrite lex_compare_reflexive in Hold.
        rewrite lex_compare_app in Hold by exact Hband_len.
        rewrite lex_compare_reflexive in Hold.
        exact Hold.
      }
      rewrite lex_compare_app in Hnew by exact Hprefix_len.
      rewrite lex_compare_reflexive in Hnew.
      rewrite lex_compare_app in Hnew.
      2:{ reflexivity. }
      rewrite lex_compare_reflexive in Hnew.
      rewrite lex_compare_app in Hnew by exact Hband_len.
      rewrite lex_compare_reflexive in Hnew.
      exfalso.
      apply Hnew.
      exact Hsuffix_lt.
    + split; auto.
    + exfalso.
      rewrite lex_compare_app in Hold by exact Hprefix_len.
      rewrite lex_compare_reflexive in Hold.
      rewrite lex_compare_app in Hold by exact Hband_len.
      rewrite Hband_cmp in Hold.
      discriminate.
  - exfalso.
    rewrite lex_compare_app in Hnew by exact Hprefix_len.
    rewrite Hprefix_cmp in Hnew.
    exact (Hnew eq_refl).
  - rewrite lex_compare_app in Hold by exact Hprefix_len.
    rewrite Hprefix_cmp in Hold.
    discriminate.
Qed.

Definition listz_pointwise_le (xs ys: list Z) : Prop :=
  Forall2 Z.le xs ys.

Lemma listz_pointwise_le_length :
  forall xs ys,
    listz_pointwise_le xs ys ->
    List.length xs = List.length ys.
Proof.
  intros xs ys Hle.
  unfold listz_pointwise_le in Hle.
  eapply Forall2_length; exact Hle.
Qed.

Lemma listz_pointwise_le_lex_compare_eq_or_lt :
  forall xs ys,
    listz_pointwise_le xs ys ->
    lex_compare xs ys = Eq \/ lex_compare xs ys = Lt.
Proof.
  intros xs ys Hle.
  unfold listz_pointwise_le in Hle.
  induction Hle as [|x y xs ys Hxy Htail IH].
  - left. reflexivity.
  - simpl.
    destruct (Z.compare x y) eqn:Hcmp.
    + destruct IH as [Heq | Hlt].
      * left. exact Heq.
      * right. exact Hlt.
    + right. reflexivity.
    + apply Z.compare_gt_iff in Hcmp.
      lia.
Qed.


Lemma listz_component_decrease_or_pointwise_le :
  forall xs ys,
    List.length xs = List.length ys ->
    (exists dim x y,
       nth_error xs dim = Some x /\
       nth_error ys dim = Some y /\
       (x > y)%Z) \/
    listz_pointwise_le xs ys.
Proof.
  induction xs as [|x xs IH]; intros ys Hlen.
  - destruct ys; [right; constructor|discriminate].
  - destruct ys as [|y ys]; [discriminate|].
    destruct (Z_gt_dec x y) as [Hgt|Hnot_gt].
    + left. exists O, x, y. simpl. repeat split; assumption.
    + specialize (IH ys ltac:(simpl in Hlen; lia)).
      destruct IH as [Hdecrease|Htail].
      * left.
        destruct Hdecrease as [dim [x' [y' [Hx [Hy Hgt]]]]].
        exists (S dim), x', y'. simpl. repeat split; assumption.
      * right. constructor; [lia|exact Htail].
Qed.

Lemma stripmined_reversal_implies_decreasing_band_component :
  forall prefix1 prefix2 tiles1 tiles2 band1 band2 suffix1 suffix2,
    List.length prefix1 = List.length prefix2 ->
    List.length band1 = List.length band2 ->
    (band1 = band2 -> tiles1 = tiles2) ->
    (listz_pointwise_le band1 band2 ->
     listz_pointwise_le tiles1 tiles2) ->
    lex_compare
      (prefix1 ++ band1 ++ suffix1)
      (prefix2 ++ band2 ++ suffix2) = Lt ->
    lex_compare
      (prefix1 ++ tiles1 ++ band1 ++ suffix1)
      (prefix2 ++ tiles2 ++ band2 ++ suffix2) <> Lt ->
    prefix1 = prefix2 /\
    exists dim x y,
      nth_error band1 dim = Some x /\
      nth_error band2 dim = Some y /\
      (x > y)%Z.
Proof.
  intros prefix1 prefix2 tiles1 tiles2 band1 band2 suffix1 suffix2
         Hprefix_len Hband_len Htiles_eq Htiles_mono Hold Hnew.
  destruct
    (stripmined_reversal_implies_prefix_eq_and_band_lt
       prefix1 prefix2 tiles1 tiles2 band1 band2 suffix1 suffix2
       Hprefix_len Hband_len Htiles_eq Hold Hnew)
    as [Hprefix_eq Hband_lt].
  split; [exact Hprefix_eq|].
  destruct
    (listz_component_decrease_or_pointwise_le band1 band2 Hband_len)
    as [Hdecrease | Hband_le].
  - exact Hdecrease.
  - exfalso.
    pose proof (Htiles_mono Hband_le) as Htiles_le.
    pose proof
      (listz_pointwise_le_lex_compare_eq_or_lt
         tiles1 tiles2 Htiles_le) as Htiles_cmp.
    pose proof (listz_pointwise_le_length _ _ Htiles_le) as Htiles_len.
    apply Hnew.
    subst prefix2.
    rewrite lex_compare_app by reflexivity.
    rewrite lex_compare_reflexive.
    rewrite lex_compare_app by exact Htiles_len.
    destruct Htiles_cmp as [Htiles_cmp | Htiles_cmp];
      rewrite Htiles_cmp.
    + rewrite lex_compare_app by exact Hband_len.
      rewrite Hband_lt.
      reflexivity.
    + reflexivity.
Qed.


Lemma common_recipe_equal_band_block_implies_equal_tiles :
  forall w1 w2 point1 point2 params rows1 rows2 sizes,
    List.length point1 = stw_point_dim w1 ->
    List.length point2 = stw_point_dim w2 ->
    schedule_rows_of_links w1 = Some rows1 ->
    schedule_rows_of_links w2 = Some rows2 ->
    List.map tl_tile_size (stw_links w1) = sizes ->
    List.map tl_tile_size (stw_links w2) = sizes ->
    well_formed_statement_tiling_witness w1 ->
    well_formed_statement_tiling_witness w2 ->
    Forall
      (fun link =>
         List.length (ae_param_coeffs (tl_expr link)) = List.length params)
      (stw_links w1) ->
    Forall
      (fun link =>
         List.length (ae_param_coeffs (tl_expr link)) = List.length params)
      (stw_links w2) ->
    affine_product rows1 (params ++ point1) =
    affine_product rows2 (params ++ point2) ->
    eval_tile_links [] point1 params (stw_links w1) =
    eval_tile_links [] point2 params (stw_links w2).
Proof.
  intros w1 w2 point1 point2 params rows1 rows2 sizes
         Hpoint1 Hpoint2 Hrows1 Hrows2 Hsizes1 Hsizes2
         Hwf1 Hwf2 Hparams1 Hparams2 Heq_aff.
  rewrite (eval_tile_links_from_schedule_rows
             w1 point1 params rows1 sizes
             Hpoint1 Hrows1 Hsizes1 Hwf1 Hparams1).
  rewrite (eval_tile_links_from_schedule_rows
             w2 point2 params rows2 sizes
             Hpoint2 Hrows2 Hsizes2 Hwf2 Hparams2).
  now rewrite Heq_aff.
Qed.

Lemma positive_tile_sizes_map :
  forall links,
    Forall (fun link => (0 < tl_tile_size link)%Z) links ->
    Forall (fun size => (0 < size)%Z) (List.map tl_tile_size links).
Proof.
  intros links Hpositive.
  induction Hpositive; simpl; constructor; auto.
Qed.

Lemma map_div_combine_preserves_pointwise_le :
  forall xs ys sizes,
    listz_pointwise_le xs ys ->
    Forall (fun size => (0 < size)%Z) sizes ->
    List.length xs = List.length sizes ->
    listz_pointwise_le
      (List.map
         (fun '(v, sz) => Z.div v sz)
         (List.combine xs sizes))
      (List.map
         (fun '(v, sz) => Z.div v sz)
         (List.combine ys sizes)).
Proof.
  intros xs ys sizes Hle.
  unfold listz_pointwise_le in *.
  revert sizes.
  induction Hle as [|x y xs ys Hxy Htail IH];
    intros sizes Hpositive Hlen.
  - destruct sizes; [constructor|discriminate].
  - destruct sizes as [|size sizes]; [discriminate|].
    inversion Hpositive as [|size0 sizes0 Hsize Hsizes]; subst.
    simpl.
    constructor.
    + apply Z.div_le_mono; assumption.
    + eapply IH.
      * exact Hsizes.
      * simpl in Hlen. lia.
Qed.

Lemma listz_pointwise_le_app :
  forall xs1 xs2 ys1 ys2,
    listz_pointwise_le xs1 ys1 ->
    listz_pointwise_le xs2 ys2 ->
    listz_pointwise_le (xs1 ++ xs2) (ys1 ++ ys2).
Proof.
  intros xs1 xs2 ys1 ys2 Hle1 Hle2.
  unfold listz_pointwise_le in *.
  induction Hle1; simpl.
  - exact Hle2.
  - constructor; auto.
Qed.

Lemma second_level_band_recipe_spec_lengths :
  forall point_dim prefix_len links recipe,
    second_level_band_recipe_spec point_dim prefix_len links recipe ->
    List.length (slbr_root_rows recipe) =
      List.length (slbr_root_sizes recipe) /\
    List.length (slbr_root_rows recipe) =
      List.length (slbr_child_sizes recipe).
Proof.
  intros point_dim prefix_len links recipe Hspec.
  induction Hspec; simpl; intuition lia.
Qed.

Lemma second_level_band_recipe_spec_positive_sizes :
  forall point_dim prefix_len links recipe,
    second_level_band_recipe_spec point_dim prefix_len links recipe ->
    Forall (fun link => (0 < tl_tile_size link)%Z) links ->
    Forall (fun size => (0 < size)%Z) (slbr_root_sizes recipe) /\
    Forall (fun size => (0 < size)%Z) (slbr_child_sizes recipe).
Proof.
  intros point_dim prefix_len links recipe Hspec Hpositive.
  induction Hspec.
  - split; constructor.
  - inversion Hpositive as [|root0 links0 Hroot_pos Hpositive_tail]; subst.
    inversion Hpositive_tail as
      [|child0 links0 Hchild_pos Hpositive_rest]; subst.
    specialize (IHHspec Hpositive_rest).
    destruct IHHspec as [Hroots Hchildren].
    split; constructor; assumption.
Qed.

Lemma second_level_root_tiles_length :
  forall recipe params point,
    List.length (slbr_root_rows recipe) =
      List.length (slbr_root_sizes recipe) ->
    List.length (second_level_root_tiles recipe params point) =
      List.length (slbr_root_sizes recipe).
Proof.
  intros recipe params point Hlen.
  unfold second_level_root_tiles, affine_product.
  rewrite List.map_length, combine_length, List.map_length, Hlen.
  apply Nat.min_id.
Qed.





Lemma second_level_schedule_tile_block_eq_common_sizes :
  forall recipe1 recipe2 params point1 point2,
    slbr_root_sizes recipe1 = slbr_root_sizes recipe2 ->
    slbr_child_sizes recipe1 = slbr_child_sizes recipe2 ->
    affine_product (slbr_root_rows recipe1) (params ++ point1) =
      affine_product (slbr_root_rows recipe2) (params ++ point2) ->
    second_level_schedule_tile_block recipe1 params point1 =
      second_level_schedule_tile_block recipe2 params point2.
Proof.
  intros recipe1 recipe2 params point1 point2
         Hroot_sizes Hchild_sizes Hroots.
  unfold second_level_schedule_tile_block,
         second_level_child_tiles,
         second_level_root_tiles.
  rewrite Hroots, Hroot_sizes, Hchild_sizes.
  reflexivity.
Qed.

Lemma second_level_schedule_tile_block_pointwise_le_common_sizes :
  forall point_dim1 prefix_len1 links1 recipe1
         recipe2 params point1 point2,
    second_level_band_recipe_spec
      point_dim1 prefix_len1 links1 recipe1 ->
    Forall (fun link => (0 < tl_tile_size link)%Z) links1 ->
    slbr_root_sizes recipe1 = slbr_root_sizes recipe2 ->
    slbr_child_sizes recipe1 = slbr_child_sizes recipe2 ->
    listz_pointwise_le
      (affine_product (slbr_root_rows recipe1) (params ++ point1))
      (affine_product (slbr_root_rows recipe2) (params ++ point2)) ->
    listz_pointwise_le
      (second_level_schedule_tile_block recipe1 params point1)
      (second_level_schedule_tile_block recipe2 params point2).
Proof.
  intros point_dim1 prefix_len1 links1 recipe1 recipe2
         params point1 point2 Hspec1 Hpositive1
         Hroot_sizes Hchild_sizes Hband_le.
  destruct (second_level_band_recipe_spec_lengths _ _ _ _ Hspec1)
    as [Hroot_len1 Hchild_len1].
  destruct
    (second_level_band_recipe_spec_positive_sizes
       _ _ _ _ Hspec1 Hpositive1)
    as [Hroot_positive1 Hchild_positive1].
  assert (Hroot_le :
    listz_pointwise_le
      (second_level_root_tiles recipe1 params point1)
      (second_level_root_tiles recipe2 params point2)).
  {
    unfold second_level_root_tiles.
    rewrite <- Hroot_sizes.
    eapply map_div_combine_preserves_pointwise_le; eauto.
    unfold affine_product.
    rewrite List.map_length.
    exact Hroot_len1.
  }
  assert (Hchild_le :
    listz_pointwise_le
      (second_level_child_tiles recipe1 params point1)
      (second_level_child_tiles recipe2 params point2)).
  {
    unfold second_level_child_tiles.
    rewrite <- Hchild_sizes.
    eapply map_div_combine_preserves_pointwise_le; eauto.
    rewrite second_level_root_tiles_length by exact Hroot_len1.
    lia.
  }
  unfold second_level_schedule_tile_block.
  eapply listz_pointwise_le_app; eauto.
Qed.

Lemma interleave_root_child_tiles_pointwise_le :
  forall roots1 roots2 children1 children2,
    listz_pointwise_le roots1 roots2 ->
    listz_pointwise_le children1 children2 ->
    listz_pointwise_le
      (interleave_root_child_tiles roots1 children1)
      (interleave_root_child_tiles roots2 children2).
Proof.
  intros roots1 roots2 children1 children2 Hroots.
  unfold listz_pointwise_le in *.
  revert children1 children2.
  induction Hroots as [|root1 root2 roots1 roots2 Hroot Hroots IH];
    intros children1 children2 Hchildren.
  - inversion Hchildren; subst; constructor.
  - destruct Hchildren as [|child1 child2 children1 children2
                            Hchild Hchildren].
    + simpl. constructor.
    + simpl.
      constructor; [exact Hroot|].
      constructor; [exact Hchild|].
      eapply IH. exact Hchildren.
Qed.

Lemma second_level_schedule_interleaved_tile_block_eq_common_sizes :
  forall recipe1 recipe2 params point1 point2,
    slbr_root_sizes recipe1 = slbr_root_sizes recipe2 ->
    slbr_child_sizes recipe1 = slbr_child_sizes recipe2 ->
    affine_product (slbr_root_rows recipe1) (params ++ point1) =
      affine_product (slbr_root_rows recipe2) (params ++ point2) ->
    second_level_schedule_interleaved_tile_block recipe1 params point1 =
      second_level_schedule_interleaved_tile_block recipe2 params point2.
Proof.
  intros recipe1 recipe2 params point1 point2
         Hroot_sizes Hchild_sizes Hroots.
  unfold second_level_schedule_interleaved_tile_block,
         second_level_child_tiles,
         second_level_root_tiles.
  rewrite Hroots, Hroot_sizes, Hchild_sizes.
  reflexivity.
Qed.

Lemma second_level_schedule_interleaved_tile_block_pointwise_le_common_sizes :
  forall point_dim1 prefix_len1 links1 recipe1
         recipe2 params point1 point2,
    second_level_band_recipe_spec
      point_dim1 prefix_len1 links1 recipe1 ->
    Forall (fun link => (0 < tl_tile_size link)%Z) links1 ->
    slbr_root_sizes recipe1 = slbr_root_sizes recipe2 ->
    slbr_child_sizes recipe1 = slbr_child_sizes recipe2 ->
    listz_pointwise_le
      (affine_product (slbr_root_rows recipe1) (params ++ point1))
      (affine_product (slbr_root_rows recipe2) (params ++ point2)) ->
    listz_pointwise_le
      (second_level_schedule_interleaved_tile_block recipe1 params point1)
      (second_level_schedule_interleaved_tile_block recipe2 params point2).
Proof.
  intros point_dim1 prefix_len1 links1 recipe1 recipe2
         params point1 point2 Hspec1 Hpositive1
         Hroot_sizes Hchild_sizes Hband_le.
  destruct (second_level_band_recipe_spec_lengths _ _ _ _ Hspec1)
    as [Hroot_len1 Hchild_len1].
  destruct
    (second_level_band_recipe_spec_positive_sizes
       _ _ _ _ Hspec1 Hpositive1)
    as [Hroot_positive1 Hchild_positive1].
  assert (Hroot_le :
    listz_pointwise_le
      (second_level_root_tiles recipe1 params point1)
      (second_level_root_tiles recipe2 params point2)).
  {
    unfold second_level_root_tiles.
    rewrite <- Hroot_sizes.
    eapply map_div_combine_preserves_pointwise_le; eauto.
    unfold affine_product.
    rewrite List.map_length.
    exact Hroot_len1.
  }
  assert (Hchild_le :
    listz_pointwise_le
      (second_level_child_tiles recipe1 params point1)
      (second_level_child_tiles recipe2 params point2)).
  {
    unfold second_level_child_tiles.
    rewrite <- Hchild_sizes.
    eapply map_div_combine_preserves_pointwise_le; eauto.
    rewrite second_level_root_tiles_length by exact Hroot_len1.
    lia.
  }
  unfold second_level_schedule_interleaved_tile_block.
  eapply interleave_root_child_tiles_pointwise_le; eauto.
Qed.

Lemma second_level_schedule_tile_block_by_layout_eq_common_sizes :
  forall layout recipe1 recipe2 params point1 point2,
    slbr_root_sizes recipe1 = slbr_root_sizes recipe2 ->
    slbr_child_sizes recipe1 = slbr_child_sizes recipe2 ->
    affine_product (slbr_root_rows recipe1) (params ++ point1) =
      affine_product (slbr_root_rows recipe2) (params ++ point2) ->
    second_level_schedule_tile_block_by_layout
      layout recipe1 params point1 =
    second_level_schedule_tile_block_by_layout
      layout recipe2 params point2.
Proof.
  intros layout.
  destruct layout; simpl; intros.
  - eapply second_level_schedule_tile_block_eq_common_sizes; eauto.
  - eapply second_level_schedule_interleaved_tile_block_eq_common_sizes; eauto.
Qed.

Lemma second_level_schedule_tile_block_by_layout_pointwise_le_common_sizes :
  forall layout point_dim1 prefix_len1 links1 recipe1
         recipe2 params point1 point2,
    second_level_band_recipe_spec
      point_dim1 prefix_len1 links1 recipe1 ->
    Forall (fun link => (0 < tl_tile_size link)%Z) links1 ->
    slbr_root_sizes recipe1 = slbr_root_sizes recipe2 ->
    slbr_child_sizes recipe1 = slbr_child_sizes recipe2 ->
    listz_pointwise_le
      (affine_product (slbr_root_rows recipe1) (params ++ point1))
      (affine_product (slbr_root_rows recipe2) (params ++ point2)) ->
    listz_pointwise_le
      (second_level_schedule_tile_block_by_layout
         layout recipe1 params point1)
      (second_level_schedule_tile_block_by_layout
         layout recipe2 params point2).
Proof.
  intros layout.
  destruct layout; simpl; intros.
  - eapply second_level_schedule_tile_block_pointwise_le_common_sizes; eauto.
  - eapply
      second_level_schedule_interleaved_tile_block_pointwise_le_common_sizes;
      eauto.
Qed.

Lemma common_recipe_band_pointwise_le_implies_tiles_pointwise_le :
  forall w1 w2 point1 point2 params rows1 rows2 sizes,
    List.length point1 = stw_point_dim w1 ->
    List.length point2 = stw_point_dim w2 ->
    schedule_rows_of_links w1 = Some rows1 ->
    schedule_rows_of_links w2 = Some rows2 ->
    List.map tl_tile_size (stw_links w1) = sizes ->
    List.map tl_tile_size (stw_links w2) = sizes ->
    well_formed_statement_tiling_witness w1 ->
    well_formed_statement_tiling_witness w2 ->
    Forall
      (fun link =>
         List.length (ae_param_coeffs (tl_expr link)) = List.length params)
      (stw_links w1) ->
    Forall
      (fun link =>
         List.length (ae_param_coeffs (tl_expr link)) = List.length params)
      (stw_links w2) ->
    Forall (fun link => (0 < tl_tile_size link)%Z) (stw_links w1) ->
    listz_pointwise_le
      (affine_product rows1 (params ++ point1))
      (affine_product rows2 (params ++ point2)) ->
    listz_pointwise_le
      (eval_tile_links [] point1 params (stw_links w1))
      (eval_tile_links [] point2 params (stw_links w2)).
Proof.
  intros w1 w2 point1 point2 params rows1 rows2 sizes
         Hpoint1 Hpoint2 Hrows1 Hrows2 Hsizes1 Hsizes2
         Hwf1 Hwf2 Hparams1 Hparams2 Hpositive Hle.
  rewrite (eval_tile_links_from_schedule_rows
             w1 point1 params rows1 sizes
             Hpoint1 Hrows1 Hsizes1 Hwf1 Hparams1).
  rewrite (eval_tile_links_from_schedule_rows
             w2 point2 params rows2 sizes
             Hpoint2 Hrows2 Hsizes2 Hwf2 Hparams2).
  eapply map_div_combine_preserves_pointwise_le.
  - exact Hle.
  - rewrite <- Hsizes1.
    eapply positive_tile_sizes_map; exact Hpositive.
  - unfold affine_product.
    rewrite List.map_length.
    pose proof (schedule_rows_of_links_length _ _ Hrows1) as Hrows_len.
    rewrite Hrows_len.
    rewrite <- Hsizes1.
    rewrite List.map_length.
    reflexivity.
Qed.

Lemma lex_compare_app_preserves_lt_local :
  forall (xs ys zs1 zs2: list Z),
    List.length xs = List.length ys ->
    lex_compare xs ys = Lt ->
    lex_compare (xs ++ zs1) (ys ++ zs2) = Lt.
Proof.
  intros xs ys zs1 zs2 Hlen Hlt.
  rewrite lex_compare_app by exact Hlen.
  now rewrite Hlt.
Qed.

Lemma lex_compare_app_preserves_not_lt_backward_local :
  forall (xs ys zs1 zs2: list Z),
    List.length xs = List.length ys ->
    lex_compare (xs ++ zs1) (ys ++ zs2) <> Lt ->
    lex_compare xs ys <> Lt.
Proof.
  intros xs ys zs1 zs2 Hlen Hnot Hlt.
  apply Hnot.
  eapply lex_compare_app_preserves_lt_local; eauto.
Qed.

Lemma is_eq_app_repeat_zero :
  forall xs n,
    is_eq (xs ++ repeat 0%Z n) xs = true.
Proof.
  intros xs n.
  rewrite <- (app_nil_r xs) at 2.
  rewrite is_eq_app by reflexivity.
  rewrite is_eq_reflexive.
  simpl.
  rewrite is_eq_nil_right.
  apply repeat_zero_is_null.
Qed.

Lemma schedule_matches_with_symmetric_trailing_zero_padding_affine_product_is_eq :
  forall expected actual idx,
    schedule_matches_with_symmetric_trailing_zero_padding expected actual ->
    is_eq (affine_product actual idx) (affine_product expected idx) = true.
Proof.
  intros expected actual idx [Hforward | Hreverse].
  - destruct Hforward as [cols [extra_rows Hactual]].
    subst actual.
    rewrite affine_product_pad_schedule_with_zero_rows.
    apply is_eq_app_repeat_zero.
  - destruct Hreverse as [cols [extra_rows Hexpected]].
    subst expected.
    rewrite affine_product_pad_schedule_with_zero_rows.
    rewrite is_eq_commutative.
    apply is_eq_app_repeat_zero.
Qed.

Lemma symmetric_second_level_schedule_layout_lex_equivalent :
  forall layout env_size before_pis after_pis bands,
    check_pinstr_list_second_level_schedule_symmetricb
      layout env_size before_pis after_pis bands = true ->
    second_level_schedule_layout_lex_equivalent
      layout env_size before_pis after_pis bands.
Proof.
  intros layout env_size before_pis after_pis bands Hcheck.
  unfold second_level_schedule_layout_lex_equivalent.
  intros i j before_i after_i band_i before_j after_j band_j idx_i idx_j
         Hbefore_i Hafter_i Hband_i Hbefore_j Hafter_j Hband_j.
  pose proof
    (check_pinstr_list_second_level_schedule_symmetricb_nth_error
       layout env_size before_pis after_pis bands
       i before_i after_i band_i
       Hcheck Hbefore_i Hafter_i Hband_i) as Hmatch_i.
  pose proof
    (check_pinstr_list_second_level_schedule_symmetricb_nth_error
       layout env_size before_pis after_pis bands
       j before_j after_j band_j
       Hcheck Hbefore_j Hafter_j Hband_j) as Hmatch_j.
  pose proof
    (schedule_matches_with_symmetric_trailing_zero_padding_affine_product_is_eq
       _ _ idx_i Hmatch_i) as Heq_i.
  pose proof
    (schedule_matches_with_symmetric_trailing_zero_padding_affine_product_is_eq
       _ _ idx_j Hmatch_j) as Heq_j.
  transitivity
    (lex_compare
       (affine_product
          (stripmine_second_level_schedule_after_env_by_layout
             layout env_size (Tiling.PL.pi_schedule before_i) band_i)
          idx_i)
       (affine_product (Tiling.PL.pi_schedule after_j) idx_j)).
  - apply lex_compare_left_eq.
    exact Heq_i.
  - apply lex_compare_right_eq.
    exact Heq_j.
Qed.

Lemma check_pinstr_list_second_level_schedule_directb_sound :
  forall layout env_size before_pis after_pis bands,
    check_pinstr_list_second_level_schedule_directb
      layout env_size before_pis after_pis bands = true ->
    second_level_schedule_layout_lex_equivalent
      layout env_size before_pis after_pis bands.
Proof.
  intros layout env_size before_pis after_pis bands Hcheck.
  unfold check_pinstr_list_second_level_schedule_directb in Hcheck.
  apply orb_true_iff in Hcheck.
  destruct Hcheck as [Hsymmetric | Herasure].
  - eapply symmetric_second_level_schedule_layout_lex_equivalent.
    exact Hsymmetric.
  - eapply zero_erasure_second_level_schedule_layout_lex_equivalent.
    eapply check_pinstr_list_second_level_schedule_zero_erasureb_sound.
    exact Herasure.
Qed.

Lemma lex_compare_app_repeat_zero :
  forall xs ys n m,
    lex_compare
      (xs ++ repeat 0%Z n)
      (ys ++ repeat 0%Z m) =
    lex_compare xs ys.
Proof.
  intros xs ys n m.
  transitivity (lex_compare xs (ys ++ repeat 0%Z m)).
  - apply lex_compare_left_eq.
    apply is_eq_app_repeat_zero.
  - apply lex_compare_right_eq.
    apply is_eq_app_repeat_zero.
Qed.



Lemma common_tiling_band_recipe_nth_error :
  forall ws sizes n w,
    common_tiling_band_recipe_with sizes ws ->
    nth_error ws n = Some w ->
    List.map tl_tile_size (stw_links w) = sizes.
Proof.
  intros ws sizes n.
  revert ws.
  induction n as [|n IH]; intros ws w Hforall Hnth.
  - destruct ws as [|w0 ws']; simpl in Hnth; [discriminate|].
    inversion Hforall; subst.
    inversion Hnth; subst.
    reflexivity.
  - destruct ws as [|w0 ws']; simpl in Hnth; [discriminate|].
    inversion Hforall; subst.
    eapply IH; eauto.
Qed.











Lemma check_pinstr_list_tiling_schedule_stripminedb_sound_infer :
  forall env_size before_pis after_pis ws,
    check_pinstr_list_tiling_schedule_stripminedb
      env_size before_pis after_pis ws = true ->
    exists bands,
      infer_pinstr_list_tiling_bands before_pis ws = Some bands /\
      pprog_tiling_bands_cert env_size before_pis after_pis ws bands.
Proof.
  induction before_pis as [|before_pi before_pis' IH];
    intros after_pis ws Hcheck;
    destruct after_pis as [|after_pi after_pis'];
    destruct ws as [|w ws'];
    simpl in *; try discriminate.
  - exists [].
    split; reflexivity.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhd Htl].
    destruct (check_pinstr_tiling_schedule_stripminedb_sound
                env_size before_pi after_pi w Hhd)
      as [band [Hinfer_hd [Hband_match Hband_sched]]].
    destruct (IH _ _ Htl) as [bands' [Hinfer_tl Hcert_tl]].
    exists (band :: bands').
    split.
    + simpl. rewrite Hinfer_hd, Hinfer_tl. reflexivity.
    + simpl. split.
      * exact (conj Hband_match Hband_sched).
      * exact Hcert_tl.
Qed.

Lemma check_pprog_tiling_schedule_stripminedb_ctxt_sound :
  forall before after ws,
    check_pprog_tiling_schedule_stripminedb before after ws = true ->
    let '(_, before_ctxt, before_vars) := before in
    let '(_, after_ctxt, after_vars) := after in
    before_ctxt = after_ctxt /\ before_vars = after_vars.
Proof.
  intros before after ws Hcheck.
  destruct before as [[before_pis before_ctxt] before_vars].
  destruct after as [[after_pis after_ctxt] after_vars].
  unfold check_pprog_tiling_schedule_stripminedb in Hcheck.
  simpl in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as [[Hctxt Hvars] _].
  split.
  - apply TilingCheck.ctxt_eqb_eq. exact Hctxt.
  - apply TilingCheck.ctxt_ty_eqb_eq. exact Hvars.
Qed.

Lemma check_pprog_tiling_schedule_stripminedb_sound_flat :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws,
    check_pprog_tiling_schedule_stripminedb
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      ws = true ->
    exists bands,
      infer_pinstr_list_tiling_bands before_pis ws = Some bands /\
      pprog_tiling_bands_cert
        (List.length before_ctxt) before_pis after_pis ws bands /\
      before_ctxt = after_ctxt /\ before_vars = after_vars.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws Hcheck.
  simpl in *.
  pose proof
    (check_pprog_tiling_schedule_stripminedb_ctxt_sound
       (before_pis, before_ctxt, before_vars)
       (after_pis, after_ctxt, after_vars) ws Hcheck)
    as [Hctxt Hvars].
  unfold check_pprog_tiling_schedule_stripminedb in Hcheck.
  simpl in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as [[_ _] Hsched].
  destruct
    (check_pinstr_list_tiling_schedule_stripminedb_sound_infer
       (List.length before_ctxt) before_pis after_pis ws Hsched)
    as [bands [Hinfer Hcert]].
  exists bands.
  repeat split; auto.
Qed.

Lemma tiling_rel_pinstr_structure_source_after_matches :
  forall env_size before after w,
    Tiling.tiling_rel_pinstr_structure_source
      env_size before after (Tiling.compiled_pinstr_tiling_witness w) ->
    stw_point_dim w = Tiling.PL.pi_depth before ->
    Tiling.after_matches_tiling_witness after w.
Proof.
  intros env_size before after w Hrel Hpoint_dim.
  unfold Tiling.after_matches_tiling_witness.
  unfold Tiling.tiling_rel_pinstr_structure_source in Hrel.
  simpl in Hrel.
  destruct Hrel as [_ [Hdepth [Hpw _]]].
  assert (Hsum :
    (List.length (stw_links w) + stw_point_dim w = Tiling.PL.pi_depth after)%nat).
  {
    cbn [Tiling.compiled_pinstr_tiling_witness Tiling.ptw_added_dims Tiling.ptw_statement_witness] in Hdepth.
    rewrite <- Hpoint_dim in Hdepth.
    lia.
  }
  split.
  - exact Hpw.
  - rewrite Hpw.
    unfold witness_current_point_dim, witness_base_point_dim, witness_added_dims.
    simpl.
    rewrite Nat.add_comm.
    exact Hsum.
Qed.

Lemma tiling_rel_pinstr_list_source_after_matches :
  forall env_size before_pis after_pis ws,
    Tiling.tiling_rel_pinstr_list_source
      env_size before_pis after_pis (List.map Tiling.compiled_pinstr_tiling_witness ws) ->
    Forall2 (fun before_pi w => stw_point_dim w = Tiling.PL.pi_depth before_pi)
      before_pis ws ->
    Forall2 Tiling.after_matches_tiling_witness after_pis ws.
Proof.
  induction before_pis as [|before_pi before_pis' IH];
    intros after_pis ws Hrel Hdepths;
    destruct after_pis as [|after_pi after_pis'];
    destruct ws as [|w ws'];
    simpl in *; try contradiction; constructor.
  - destruct Hrel as [Hhd _].
    inversion Hdepths; subst.
    eapply tiling_rel_pinstr_structure_source_after_matches; eauto.
  - destruct Hrel as [_ Htl].
    inversion Hdepths; subst.
    eapply IH; eauto.
Qed.

Lemma tiling_rel_pprog_structure_source_after_matches :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws,
    Tiling.tiling_rel_pprog_structure_source
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      (List.map Tiling.compiled_pinstr_tiling_witness ws) ->
    Forall2 (fun before_pi w => stw_point_dim w = Tiling.PL.pi_depth before_pi)
      before_pis ws ->
    Forall2 Tiling.after_matches_tiling_witness after_pis ws.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws Hprog Hdepths.
  unfold Tiling.tiling_rel_pprog_structure_source in Hprog.
  simpl in Hprog.
  destruct Hprog as [_ [_ Hrel]].
  eapply tiling_rel_pinstr_list_source_after_matches; eauto.
Qed.

Lemma flatten_instrs_ext_from_after_member_nth_data_source :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws envv ipl_ext tau,
    Tiling.tiling_rel_pprog_structure_source
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      (List.map Tiling.compiled_pinstr_tiling_witness ws) ->
    Forall
      (Tiling.wf_statement_tiling_witness_with_param_dim (List.length envv))
      ws ->
    Forall
      (fun w => Forall (fun link => 0 < tl_tile_size link) (stw_links w))
      ws ->
    Forall2 (fun before_pi w => stw_point_dim w = Tiling.PL.pi_depth before_pi)
      before_pis ws ->
    Tiling.PL.flatten_instrs_ext
      envv
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length envv) before_pis after_pis ws)
      ipl_ext ->
    In tau ipl_ext ->
    exists before_pi after_pi w,
      List.nth_error before_pis (Tiling.PL.ip_nth_ext tau) = Some before_pi /\
      List.nth_error after_pis (Tiling.PL.ip_nth_ext tau) = Some after_pi /\
      List.nth_error ws (Tiling.PL.ip_nth_ext tau) = Some w /\
      Tiling.wf_statement_tiling_witness_with_param_dim (List.length envv) w /\
      Forall (fun link => 0 < tl_tile_size link) (stw_links w) /\
      stw_point_dim w = Tiling.PL.pi_depth before_pi /\
      firstn (List.length envv) (Tiling.PL.ip_index_ext tau) = envv /\
      Tiling.PL.belongs_to_ext
        tau
        (Tiling.compose_tiling_pinstr_ext
           (List.length envv) before_pi after_pi w) /\
      List.length (Tiling.PL.ip_index_ext tau) =
        (List.length envv + Tiling.PL.pi_depth after_pi)%nat.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws envv ipl_ext tau
         Hprog Hwf_ws Hsizes_ws Hdepths
         Hflat Hin_tau.
  pose proof
    (Tiling.tiling_rel_pprog_structure_source_lengths
       before_pis before_ctxt before_vars
       after_pis after_ctxt after_vars
       (List.map Tiling.compiled_pinstr_tiling_witness ws) Hprog)
    as [Hlen_after Hlen_ws_map].
  rewrite List.map_length in Hlen_ws_map.
  assert (Hcomp_len :
    List.length
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length envv) before_pis after_pis ws) =
    List.length before_pis).
  {
    eapply Tiling.compose_tiling_pinstrs_ext_from_after_preserve_length.
    - exact Hlen_after.
    - rewrite Hlen_after.
      exact Hlen_ws_map.
  }
  destruct Hflat as [_ [Hmem _]].
  destruct (proj1 (Hmem tau) Hin_tau)
    as [pi_ext [Hnth_ext [Hpref_tau [Hbel_tau Hlen_tau]]]].
  assert (Hn_lt_comp :
    (Tiling.PL.ip_nth_ext tau <
     List.length
       (Tiling.compose_tiling_pinstrs_ext_from_after
          (List.length envv) before_pis after_pis ws))%nat).
  {
    eapply Tiling.PL.nth_error_Some'.
    exact Hnth_ext.
  }
  assert (Hn_lt_before :
    (Tiling.PL.ip_nth_ext tau < List.length before_pis)%nat).
  {
    rewrite <- Hcomp_len.
    exact Hn_lt_comp.
  }
  destruct (List.nth_error before_pis (Tiling.PL.ip_nth_ext tau)) eqn:Hbefore_nth.
  2:{
    exfalso.
    eapply List.nth_error_None in Hbefore_nth.
    lia.
  }
  destruct (List.nth_error after_pis (Tiling.PL.ip_nth_ext tau)) eqn:Hafter_nth.
  2:{
    exfalso.
    eapply List.nth_error_None in Hafter_nth.
    rewrite <- Hlen_after in Hafter_nth.
    lia.
  }
  destruct (List.nth_error ws (Tiling.PL.ip_nth_ext tau)) eqn:Hw_nth.
  2:{
    exfalso.
    eapply List.nth_error_None in Hw_nth.
    rewrite <- Hlen_ws_map in Hw_nth.
    rewrite <- Hlen_after in Hw_nth.
    lia.
  }
  pose proof
    (Tiling.nth_error_compose_tiling_pinstrs_ext_from_after
       (List.length envv) before_pis after_pis ws (Tiling.PL.ip_nth_ext tau)
       p p0 s Hbefore_nth Hafter_nth Hw_nth)
    as Hnth_expected.
  rewrite Hnth_ext in Hnth_expected.
  inversion Hnth_expected; subst pi_ext.
  pose proof
    (Tiling.Forall_nth_error _ _ _ _ _ Hwf_ws Hw_nth)
    as Hwf_w.
  pose proof
    (Tiling.Forall_nth_error _ _ _ _ _ Hsizes_ws Hw_nth)
    as Hsizes_w.
  pose proof
    (Tiling.Forall2_nth_error
       _ _ _
       before_pis ws (Tiling.PL.ip_nth_ext tau) p s
       Hdepths Hbefore_nth Hw_nth)
    as Hpoint_depth.
  exists p, p0, s.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  destruct Hwf_w as [Hwf_core Hparams_w].
  split.
  - split; [exact Hwf_core|exact Hparams_w].
  - split; [exact Hsizes_w|].
  split; [exact Hpoint_depth|].
  split; [exact Hpref_tau|].
  split; [exact Hbel_tau|].
  cbn [Tiling.compose_tiling_pinstr_ext] in Hlen_tau.
  exact Hlen_tau.
Qed.

Definition composed_point_facts
    (before_pis after_pis : list Tiling.PL.PolyInstr)
    (ws : list statement_tiling_witness)
    (envv : list Z)
    (tau : Tiling.PL.InstrPoint_ext) : Prop :=
  exists before_pi after_pi w,
    List.nth_error before_pis (Tiling.PL.ip_nth_ext tau) = Some before_pi /\
    List.nth_error after_pis (Tiling.PL.ip_nth_ext tau) = Some after_pi /\
    List.nth_error ws (Tiling.PL.ip_nth_ext tau) = Some w /\
    Tiling.wf_statement_tiling_witness_with_param_dim
      (List.length envv) w /\
    Forall (fun link => 0 < tl_tile_size link) (stw_links w) /\
    stw_point_dim w = Tiling.PL.pi_depth before_pi /\
    firstn (List.length envv) (Tiling.PL.ip_index_ext tau) = envv /\
    Tiling.PL.belongs_to_ext
      tau
      (Tiling.compose_tiling_pinstr_ext
        (List.length envv) before_pi after_pi w) /\
    List.length (Tiling.PL.ip_index_ext tau) =
      (List.length envv + Tiling.PL.pi_depth after_pi)%nat.

Lemma composed_point_pair_facts_of_members :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws envv ipl_ext tau1 tau2,
    Tiling.tiling_rel_pprog_structure_source
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      (List.map Tiling.compiled_pinstr_tiling_witness ws) ->
    Forall
      (Tiling.wf_statement_tiling_witness_with_param_dim (List.length envv))
      ws ->
    Forall
      (fun w => Forall (fun link => 0 < tl_tile_size link) (stw_links w))
      ws ->
    Forall2
      (fun before_pi w => stw_point_dim w = Tiling.PL.pi_depth before_pi)
      before_pis ws ->
    Tiling.PL.flatten_instrs_ext
      envv
      (Tiling.compose_tiling_pinstrs_ext_from_after
        (List.length envv) before_pis after_pis ws)
      ipl_ext ->
    In tau1 ipl_ext ->
    In tau2 ipl_ext ->
    composed_point_facts before_pis after_pis ws envv tau1 /\
    composed_point_facts before_pis after_pis ws envv tau2.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws envv ipl_ext tau1 tau2
         Hprog Hwf_ws Hsizes_ws Hdepths Hflat Hin1 Hin2.
  split; unfold composed_point_facts.
  - eapply flatten_instrs_ext_from_after_member_nth_data_source;
      eassumption.
  - eapply flatten_instrs_ext_from_after_member_nth_data_source;
      eassumption.
Qed.


End ProjectedScheduleBridge.

(** * Direct affine conflict checker for a common band

    The historical whole-validator reduction is explicitly marked below.  For
    the current route, jump to "Direct checker soundness". *)

Section CommonBandDirectChecker.

Definition make_pluto_band_component_guard_polys
    (pi1 pi2: Tiling.PL.PolyInstr_ext)
    (band: pinstr_tiling_band)
    (dim env_size: nat)
    : option (list polyhedron * list polyhedron) :=
  let dom_dim1 := (env_size + Tiling.PL.pi_depth_ext pi1)%nat in
  let dom_dim2 := (env_size + Tiling.PL.pi_depth_ext pi2)%nat in
  let sched1 := Tiling.PL.pi_schedule1_ext pi1 in
  let sched2 := Tiling.PL.pi_schedule1_ext pi2 in
  match nth_error sched1 (ptb_start band + dim),
        nth_error sched2 (ptb_start band + dim) with
  | Some row1, Some row2 =>
      let old_order := make_poly_lt sched1 sched2 dom_dim1 dom_dim2 [] in
      let same_prefix :=
        make_poly_eq
          (firstn (ptb_start band) sched1)
          (firstn (ptb_start band) sched2)
          dom_dim1 dom_dim2 [] in
      let component_decreases := make_constr_gt row1 row2 in
      Some (old_order, [[component_decreases] ++ same_prefix])
  | _, _ => None
  end.

Lemma wf_pinstr_ext_tiling_schedule1_exact_cols :
  forall env pi,
    Tiling.PL.wf_pinstr_ext_tiling env pi ->
    exact_listzzs_cols
      (List.length env + Tiling.PL.pi_depth_ext pi)%nat
      (Tiling.PL.pi_schedule1_ext pi).
Proof.
  intros env pi Hwf.
  unfold Tiling.PL.wf_pinstr_ext_tiling in Hwf.
  destruct Hwf as [Hwf _].
  unfold Tiling.PL.wf_pinstr_ext in Hwf.
  destruct Hwf as [_ [_ [_ [_ [Hsched1 _]]]]].
  exact Hsched1.
Qed.

Lemma make_pluto_band_component_guard_polys_old_order_sound :
  forall pi1 pi2 band dim env_size old_order bad_component p1 p2,
    make_pluto_band_component_guard_polys
      pi1 pi2 band dim env_size = Some (old_order, bad_component) ->
    List.length p1 =
      (env_size + Tiling.PL.pi_depth_ext pi1)%nat ->
    List.length p2 =
      (env_size + Tiling.PL.pi_depth_ext pi2)%nat ->
    exact_listzzs_cols
      (env_size + Tiling.PL.pi_depth_ext pi1)%nat
      (Tiling.PL.pi_schedule1_ext pi1) ->
    lex_compare
      (affine_product (Tiling.PL.pi_schedule1_ext pi1) p1)
      (affine_product (Tiling.PL.pi_schedule1_ext pi2) p2) = Lt ->
    Exists
      (fun pol => in_poly (p1 ++ p2) pol = true)
      old_order.
Proof.
  intros pi1 pi2 band dim env_size old_order bad_component p1 p2
         Hmake Hlen1 Hlen2 Hcols Hold.
  unfold make_pluto_band_component_guard_polys in Hmake.
  destruct
    (nth_error
       (Tiling.PL.pi_schedule1_ext pi1) (ptb_start band + dim));
    try discriminate.
  destruct
    (nth_error
       (Tiling.PL.pi_schedule1_ext pi2) (ptb_start band + dim));
    try discriminate.
  inversion Hmake; subst old_order bad_component; clear Hmake.
  eapply make_poly_lt_correct; eauto.
Qed.

Lemma make_pluto_band_component_guard_polys_bad_component_sound :
  forall pi1 pi2 band dim env_size old_order bad_component p1 p2,
    make_pluto_band_component_guard_polys
      pi1 pi2 band dim env_size = Some (old_order, bad_component) ->
    List.length p1 =
      (env_size + Tiling.PL.pi_depth_ext pi1)%nat ->
    List.length p2 =
      (env_size + Tiling.PL.pi_depth_ext pi2)%nat ->
    exact_listzzs_cols
      (env_size + Tiling.PL.pi_depth_ext pi1)%nat
      (Tiling.PL.pi_schedule1_ext pi1) ->
    exact_listzzs_cols
      (env_size + Tiling.PL.pi_depth_ext pi2)%nat
      (Tiling.PL.pi_schedule1_ext pi2) ->
    affine_product
      (firstn (ptb_start band) (Tiling.PL.pi_schedule1_ext pi1)) p1 =
    affine_product
      (firstn (ptb_start band) (Tiling.PL.pi_schedule1_ext pi2)) p2 ->
    (exists row1 row2,
       nth_error
         (Tiling.PL.pi_schedule1_ext pi1)
         (ptb_start band + dim) = Some row1 /\
       nth_error
         (Tiling.PL.pi_schedule1_ext pi2)
         (ptb_start band + dim) = Some row2 /\
       (Linalg.dot_product (fst row1) p1 + snd row1 >
        Linalg.dot_product (fst row2) p2 + snd row2)%Z) ->
    Exists
      (fun pol => in_poly (p1 ++ p2) pol = true)
      bad_component.
Proof.
  intros pi1 pi2 band dim env_size old_order bad_component p1 p2
         Hmake Hlen1 Hlen2 Hcols1 Hcols2 Hprefix
         [row1 [row2 [Hrow1 [Hrow2 Hcomponent]]]].
  unfold make_pluto_band_component_guard_polys in Hmake.
  rewrite Hrow1, Hrow2 in Hmake.
  inversion Hmake; subst old_order bad_component; clear Hmake.
  destruct row1 as [v1 c1].
  destruct row2 as [v2 c2].
  simpl in Hcomponent.
  assert (Hv1 :
    List.length v1 =
      (env_size + Tiling.PL.pi_depth_ext pi1)%nat).
  {
    eapply Hcols1.
    - eapply nth_error_In. exact Hrow1.
    - reflexivity.
  }
  assert (Hprefix_poly :
    in_poly (p1 ++ p2)
      (make_poly_eq
         (firstn (ptb_start band) (Tiling.PL.pi_schedule1_ext pi1))
         (firstn (ptb_start band) (Tiling.PL.pi_schedule1_ext pi2))
         (env_size + Tiling.PL.pi_depth_ext pi1)%nat
         (env_size + Tiling.PL.pi_depth_ext pi2)%nat []) = true).
  {
    apply
      (proj2
         (make_poly_eq_correct_true
            (firstn (ptb_start band) (Tiling.PL.pi_schedule1_ext pi1))
            (firstn (ptb_start band) (Tiling.PL.pi_schedule1_ext pi2))
            (env_size + Tiling.PL.pi_depth_ext pi1)%nat
            (env_size + Tiling.PL.pi_depth_ext pi2)%nat
            p1 p2 Hlen1 Hlen2
            (exact_listzzs_cols_firstn_local
               _ _ _ Hcols1))).
    rewrite Hprefix.
    apply veq_refl.
  }
  assert (Hcomponent_poly :
    satisfies_constraint
      (p1 ++ p2)
      (make_constr_gt (v1, c1) (v2, c2)) = true).
  {
    apply
      (proj2
         (make_constr_gt_correct p1 p2 v1 v2 c1 c2
            (eq_trans Hlen1 (eq_sym Hv1)))).
    exact Hcomponent.
  }
  apply Exists_cons_hd.
  change
    (satisfies_constraint
       (p1 ++ p2) (make_constr_gt (v1, c1) (v2, c2)) &&
     in_poly
       (p1 ++ p2)
       (make_poly_eq
          (firstn (ptb_start band) (Tiling.PL.pi_schedule1_ext pi1))
          (firstn (ptb_start band) (Tiling.PL.pi_schedule1_ext pi2))
          (env_size + Tiling.PL.pi_depth_ext pi1)%nat
          (env_size + Tiling.PL.pi_depth_ext pi2)%nat []) = true).
  rewrite Hcomponent_poly, Hprefix_poly.
  reflexivity.
Qed.

Lemma make_pluto_band_component_guard_polys_point_sound :
  forall env envv nth1 nth2 pi1 pi2 ipl1 ipl2 band dim
         old_order bad_component ip1 ip2,
    make_pluto_band_component_guard_polys
      pi1 pi2 band dim (List.length env) =
      Some (old_order, bad_component) ->
    Tiling.PL.wf_pinstr_ext_tiling env pi1 ->
    Tiling.PL.wf_pinstr_ext_tiling env pi2 ->
    List.length env = List.length envv ->
    Tiling.PL.flatten_instr_nth_ext envv nth1 pi1 ipl1 ->
    Tiling.PL.flatten_instr_nth_ext envv nth2 pi2 ipl2 ->
    In ip1 ipl1 ->
    In ip2 ipl2 ->
    Tiling.PL.instr_point_ext_old_sched_lt ip1 ip2 ->
    instr_point_ext_same_band_slice band ip1 ip2 ->
    instr_point_ext_band_component_decreases_at band dim ip1 ip2 ->
    Exists
      (fun pol =>
         in_poly
           (Tiling.PL.ip_index_ext ip1 ++ Tiling.PL.ip_index_ext ip2)
           pol = true)
      old_order /\
    Exists
      (fun pol =>
         in_poly
           (Tiling.PL.ip_index_ext ip1 ++ Tiling.PL.ip_index_ext ip2)
           pol = true)
      bad_component.
Proof.
  intros env envv nth1 nth2 pi1 pi2 ipl1 ipl2 band dim
         old_order bad_component ip1 ip2
         Hmake Hwf1 Hwf2 Henv Hflat1 Hflat2 Hin1 Hin2
         Hold Hprefix Hcomponent.
  pose proof
    (Tiling.PL.expand_ts1_eq_sched_index_product_ext
       envv nth1 pi1 ipl1 ip1 Hflat1 Hin1) as Hts1.
  pose proof
    (Tiling.PL.expand_ts1_eq_sched_index_product_ext
       envv nth2 pi2 ipl2 ip2 Hflat2 Hin2) as Hts2.
  assert (Hidx1 :
    List.length (Tiling.PL.ip_index_ext ip1) =
      (List.length env + Tiling.PL.pi_depth_ext pi1)%nat).
  {
    rewrite Henv.
    eapply Tiling.PL.ip_index_size_eq_pi_dom_size_ext; eauto.
  }
  assert (Hidx2 :
    List.length (Tiling.PL.ip_index_ext ip2) =
      (List.length env + Tiling.PL.pi_depth_ext pi2)%nat).
  {
    rewrite Henv.
    eapply Tiling.PL.ip_index_size_eq_pi_dom_size_ext; eauto.
  }
  assert (Hcols1 :
    exact_listzzs_cols
      (List.length env + Tiling.PL.pi_depth_ext pi1)%nat
      (Tiling.PL.pi_schedule1_ext pi1)).
  {
    exact (wf_pinstr_ext_tiling_schedule1_exact_cols env pi1 Hwf1).
  }
  assert (Hcols2 :
    exact_listzzs_cols
      (List.length env + Tiling.PL.pi_depth_ext pi2)%nat
      (Tiling.PL.pi_schedule1_ext pi2)).
  {
    exact (wf_pinstr_ext_tiling_schedule1_exact_cols env pi2 Hwf2).
  }
  split.
  - eapply make_pluto_band_component_guard_polys_old_order_sound;
      eauto.
    unfold Tiling.PL.instr_point_ext_old_sched_lt in Hold.
    rewrite Hts1, Hts2 in Hold.
    exact Hold.
  - eapply make_pluto_band_component_guard_polys_bad_component_sound;
      eauto.
    + unfold instr_point_ext_same_band_slice,
             instr_point_ext_band_prefix_ts in Hprefix.
      rewrite Hts1, Hts2 in Hprefix.
      rewrite !affine_product_firstn_local.
      exact Hprefix.
    + destruct Hcomponent as [x [y [Hdim [Hx [Hy Hgt]]]]].
      rewrite Hts1 in Hx.
      rewrite Hts2 in Hy.
      unfold affine_product in Hx, Hy.
      rewrite nth_error_map_iff in Hx, Hy.
      destruct Hx as [row1 [Hrow1 Hx]].
      destruct Hy as [row2 [Hrow2 Hy]].
      subst x y.
      exists row1, row2.
      repeat split; assumption.
Qed.

Definition validate_two_instrs_pluto_band_component_direct
    (pi1 pi2: Tiling.PL.PolyInstr_ext)
    (band: pinstr_tiling_band)
    (dim env_size: nat) : imp bool :=
  match
    make_pluto_band_component_guard_polys pi1 pi2 band dim env_size
  with
  | None => pure false
  | Some (old_order, bad_component) =>
      BandAffine.validate_two_instrs_under_guards_integer
        pi1 pi2 env_size old_order bad_component
  end.

Fixpoint validate_instr_and_list_pluto_band_component_direct
    (pi: Tiling.PL.PolyInstr_ext)
    (pis: list Tiling.PL.PolyInstr_ext)
    (band: pinstr_tiling_band)
    (dim env_size: nat) : imp bool :=
  match pis with
  | [] => pure true
  | pi' :: pis' =>
      BIND forward <-
        validate_two_instrs_pluto_band_component_direct
          pi pi' band dim env_size -;
      if forward then
        BIND backward <-
          validate_two_instrs_pluto_band_component_direct
            pi' pi band dim env_size -;
        if backward then
          validate_instr_and_list_pluto_band_component_direct
            pi pis' band dim env_size
        else pure false
      else pure false
  end.

Fixpoint validate_instr_list_pluto_band_component_direct
    (pis: list Tiling.PL.PolyInstr_ext)
    (band: pinstr_tiling_band)
    (dim env_size: nat) : imp bool :=
  match pis with
  | [] => pure true
  | pi :: pis' =>
      BIND self <-
        validate_two_instrs_pluto_band_component_direct
          pi pi band dim env_size -;
      if self then
        BIND cross <-
          validate_instr_and_list_pluto_band_component_direct
            pi pis' band dim env_size -;
        if cross then
          validate_instr_list_pluto_band_component_direct
            pis' band dim env_size
        else pure false
      else pure false
  end.

Fixpoint validate_instr_list_pluto_band_components_direct_from
    (pis: list Tiling.PL.PolyInstr_ext)
    (band: pinstr_tiling_band)
    (remaining dim env_size: nat) : imp bool :=
  match remaining with
  | O => pure true
  | S remaining' =>
      BIND component_ok <-
        validate_instr_list_pluto_band_component_direct
          pis band dim env_size -;
      if component_ok then
        validate_instr_list_pluto_band_components_direct_from
          pis band remaining' (S dim) env_size
      else pure false
  end.

Definition check_pinstr_list_pluto_permutable_band_direct
    (env_size: nat)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (band: pinstr_tiling_band) : imp bool :=
  let pis :=
    Tiling.compose_tiling_pinstrs_ext_from_after
      env_size before_pis after_pis ws in
  let aligned :=
    Nat.eqb (List.length before_pis) (List.length after_pis) &&
    Nat.eqb (List.length before_pis) (List.length ws) &&
    Nat.eqb (List.length before_pis) (List.length pis) in
  let valid_access := BandAffine.check_valid_access pis in
  BIND res <-
    validate_instr_list_pluto_band_components_direct_from
      pis band (ptb_len band) O env_size -;
  pure (aligned && res && valid_access).

(** * Compatibility reduction through the affine checker

    The following [*_via_validate_tiling] declarations encode an older proof
    route by synthesizing schedules for the affine validator.  They remain
    available for compatibility and comparison.  The runtime dispatcher uses
    the direct definitions above and the direct soundness chain below. *)

Definition check_pprog_pluto_permutable_tiling_bands_direct
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness)
    (bands: list pinstr_tiling_band) : imp bool :=
  let '(before_pis, before_ctxt, before_vars) := before in
  let '(after_pis, after_ctxt, after_vars) := after in
  if TilingCheck.ctxt_eqb before_ctxt after_ctxt &&
     TilingCheck.ctxt_ty_eqb before_vars after_vars then
    if Nat.eqb (List.length bands) (List.length before_pis) then
      if check_uniform_schedule_arityb before_pis then
        match infer_common_tiling_band bands with
        | Some band =>
            if check_common_tiling_band_recipeb ws then
              check_pinstr_list_pluto_permutable_band_direct
                (List.length before_ctxt) before_pis after_pis ws band
            else pure false
        | None => pure false
        end
      else pure false
    else pure false
  else pure false.


Lemma ctxt_ty_eqb_refl_local :
  forall before_vars,
    TilingCheck.ctxt_ty_eqb before_vars before_vars = true.
Proof.
  induction before_vars as [|(v, ty) before_vars IH]; simpl.
  - reflexivity.
  - repeat rewrite andb_true_iff.
    split.
    + split.
      * apply Instr.ident_eqb_eq. reflexivity.
      * apply Tiling.PL.Ty.eqb_eq. reflexivity.
    + exact IH.
Qed.






Lemma max_tiling_band_len_ge_nth_error :
  forall bands n band,
    nth_error bands n = Some band ->
    (ptb_len band <= max_tiling_band_len bands)%nat.
Proof.
  induction bands as [|band0 bands IH]; intros n band Hnth.
  - destruct n; discriminate.
  - destruct n as [|n].
    + inversion Hnth; subst.
      simpl. apply Nat.le_max_l.
    + simpl in Hnth.
      simpl.
      eapply Nat.le_trans.
      * eapply IH; exact Hnth.
      * apply Nat.le_max_r.
Qed.








Lemma pprog_pluto_permutable_tiling_bands_strong_implies_reordering_safe_if_local_bridge :
  forall envv before_pis after_pis ws bands,
    pprog_pluto_permutable_tiling_bands_strong
      envv before_pis after_pis ws bands ->
    (forall ipl_ext tau1 tau2 band sizes,
       common_tiling_band bands band ->
       common_tiling_band_recipe_with sizes ws ->
       Tiling.PL.flatten_instrs_ext
         envv
         (Tiling.compose_tiling_pinstrs_ext_from_after
            (List.length envv) before_pis after_pis ws)
         ipl_ext ->
       In tau1 ipl_ext ->
       In tau2 ipl_ext ->
       Tiling.PL.instr_point_ext_old_sched_lt tau1 tau2 ->
       Tiling.PL.instr_point_ext_new_sched_ge tau1 tau2 ->
       instr_point_ext_same_band_slice band tau1 tau2 /\
       instr_point_ext_band_component_decreases band tau1 tau2) ->
    pprog_tiling_reordering_safe envv before_pis after_pis ws bands.
Proof.
  intros envv before_pis after_pis ws bands
         Hpluto Hlocal.
  destruct Hpluto as [band [sizes [Hcommon [Hrecipe Hperm]]]].
  unfold pprog_tiling_reordering_safe, pprog_permutable_tiling_bands.
  intros ipl_ext tau1 tau2 Hflat Hin1 Hin2 Hold Hnew.
  destruct (Hlocal ipl_ext tau1 tau2 band sizes
              Hcommon Hrecipe Hflat Hin1 Hin2 Hold Hnew)
    as [Hslice Hcomponent].
  eapply Hperm; eauto.
Qed.


Lemma ordinary_pair_local_reversal_bridge_by_schedule_len_wf_with_env_len :
  forall before_pis before_ctxt before_vars after_pis ws bands envv
         ipl_ext tau1 tau2,
    List.length before_ctxt = List.length envv ->
    infer_pinstr_list_tiling_bands before_pis ws = Some bands ->
    pprog_tiling_bands_cert
      (List.length before_ctxt) before_pis after_pis ws bands ->
    Tiling.tiling_rel_pprog_structure_source
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars)
      (List.map Tiling.compiled_pinstr_tiling_witness ws) ->
    Forall
      (Tiling.wf_statement_tiling_witness_with_param_dim
         (List.length before_ctxt))
      ws ->
    Forall
      (fun w => Forall (fun link => 0 < tl_tile_size link) (stw_links w))
      ws ->
    Forall2
      (fun before_pi w => stw_point_dim w = Tiling.PL.pi_depth before_pi)
      before_pis ws ->
    (forall before_pi1 before_pi2,
       nth_error before_pis (Tiling.PL.ip_nth_ext tau1) = Some before_pi1 ->
       nth_error before_pis (Tiling.PL.ip_nth_ext tau2) = Some before_pi2 ->
       List.length (Tiling.PL.pi_schedule before_pi1) =
       List.length (Tiling.PL.pi_schedule before_pi2)) ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    Tiling.PL.flatten_instrs_ext
      envv
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length envv) before_pis after_pis ws)
      ipl_ext ->
    In tau1 ipl_ext ->
    In tau2 ipl_ext ->
    Tiling.PL.instr_point_ext_old_sched_lt tau1 tau2 ->
    Tiling.PL.instr_point_ext_new_sched_ge tau1 tau2 ->
    (forall band1 band2,
       nth_error bands (Tiling.PL.ip_nth_ext tau1) = Some band1 ->
       nth_error bands (Tiling.PL.ip_nth_ext tau2) = Some band2 ->
       band1 = band2) ->
    (forall w1 w2,
       nth_error ws (Tiling.PL.ip_nth_ext tau1) = Some w1 ->
       nth_error ws (Tiling.PL.ip_nth_ext tau2) = Some w2 ->
       tile_sizes_of_witness w1 = tile_sizes_of_witness w2) ->
    exists band,
      nth_error bands (Tiling.PL.ip_nth_ext tau1) = Some band /\
      nth_error bands (Tiling.PL.ip_nth_ext tau2) = Some band /\
      instr_point_ext_same_band_slice band tau1 tau2 /\
      instr_point_ext_band_component_decreases band tau1 tau2.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws bands envv
         ipl_ext tau1 tau2
         Hlen_env Hinfer_bands Hbands Hprog_full Hwf_ws Hsizes_ws Hdepths
         Hsame_schedule_len Hwf_before_pis
         Hflat Hin1 Hin2 Hold Hnew
         Hsame_band Hsame_recipe.
  assert (Hwf_ws_env :
    Forall
      (Tiling.wf_statement_tiling_witness_with_param_dim (List.length envv))
      ws).
  {
    rewrite <- Hlen_env.
    exact Hwf_ws.
  }
  destruct (pprog_tiling_bands_cert_lengths _ _ _ _ _ Hbands)
    as [Hlen_after [Hlen_ws Hlen_bands]].
  destruct
    (composed_point_pair_facts_of_members
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       ws envv ipl_ext tau1 tau2
       Hprog_full Hwf_ws_env Hsizes_ws Hdepths Hflat Hin1 Hin2)
    as [Hpoint1 Hpoint2].
  unfold composed_point_facts in Hpoint1, Hpoint2.
  destruct Hpoint1 as [before_pi1 [after_pi1 [w1
    [Hbefore1 [Hafter1 [Hw1
    [Hwf_stmt1 [Hsizes1 [Hpoint_depth1 [Hpref1 [Hbel1 Hlen1]]]]]]]]]]].
  assert (Hbefore1_some :
    nth_error before_pis (Tiling.PL.ip_nth_ext tau1) <> None).
  {
    rewrite Hbefore1.
    discriminate.
  }
  destruct (nth_error bands (Tiling.PL.ip_nth_ext tau1))
    as [band1|] eqn:Hband1.
  2:{
    exfalso.
    apply nth_error_None in Hband1.
    apply nth_error_Some in Hbefore1_some.
    lia.
  }
  destruct Hpoint2 as [before_pi2 [after_pi2 [w2
    [Hbefore2 [Hafter2 [Hw2
    [Hwf_stmt2 [Hsizes2 [Hpoint_depth2 [Hpref2 [Hbel2 Hlen2]]]]]]]]]]].
  assert (Hbefore2_some :
    nth_error before_pis (Tiling.PL.ip_nth_ext tau2) <> None).
  {
    rewrite Hbefore2.
    discriminate.
  }
  destruct (nth_error bands (Tiling.PL.ip_nth_ext tau2))
    as [band2|] eqn:Hband2.
  2:{
    exfalso.
    apply nth_error_None in Hband2.
    apply nth_error_Some in Hbefore2_some.
    lia.
  }
  pose proof (Hsame_recipe w1 w2 Hw1 Hw2) as Hselected_sizes.
  pose proof (Hsame_band band1 band2 eq_refl eq_refl) as Hband_eq.
  subst band2.
  rename band1 into band.
  pose proof
    (pprog_tiling_bands_cert_nth_error
       (List.length before_ctxt) before_pis after_pis ws bands
       (Tiling.PL.ip_nth_ext tau1)
       before_pi1 after_pi1 w1 band
       Hbands Hbefore1 Hafter1 Hw1 Hband1)
    as Hcert1.
  pose proof
    (pprog_tiling_bands_cert_nth_error
       (List.length before_ctxt) before_pis after_pis ws bands
       (Tiling.PL.ip_nth_ext tau2)
       before_pi2 after_pi2 w2 band
       Hbands Hbefore2 Hafter2 Hw2 Hband2)
    as Hcert2.
  pose proof
    (infer_pinstr_list_tiling_bands_nth_error
       before_pis ws bands
       (Tiling.PL.ip_nth_ext tau1)
       before_pi1 w1 band
       Hinfer_bands Hbefore1 Hw1 Hband1)
    as Hinfer1.
  pose proof
    (infer_pinstr_list_tiling_bands_nth_error
       before_pis ws bands
       (Tiling.PL.ip_nth_ext tau2)
       before_pi2 w2 band
       Hinfer_bands Hbefore2 Hw2 Hband2)
    as Hinfer2.
  pose proof
    (Tiling.tiling_rel_pprog_structure_source_nth
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       (List.map Tiling.compiled_pinstr_tiling_witness ws)
       (Tiling.PL.ip_nth_ext tau1)
       before_pi1 after_pi1 (Tiling.compiled_pinstr_tiling_witness w1)
       Hprog_full Hbefore1 Hafter1
       (Tiling.nth_error_map_some
          _ _ Tiling.compiled_pinstr_tiling_witness
          ws (Tiling.PL.ip_nth_ext tau1) w1 Hw1))
    as Hstmt1.
  pose proof
    (Tiling.tiling_rel_pprog_structure_source_nth
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       (List.map Tiling.compiled_pinstr_tiling_witness ws)
       (Tiling.PL.ip_nth_ext tau2)
       before_pi2 after_pi2 (Tiling.compiled_pinstr_tiling_witness w2)
       Hprog_full Hbefore2 Hafter2
       (Tiling.nth_error_map_some
          _ _ Tiling.compiled_pinstr_tiling_witness
          ws (Tiling.PL.ip_nth_ext tau2) w2 Hw2))
    as Hstmt2.
  pose proof
    (Tiling.Forall_nth_error
       _ _
       before_pis (Tiling.PL.ip_nth_ext tau1) before_pi1
       Hwf_before_pis Hbefore1)
    as Hwf_before1.
  pose proof
    (Tiling.Forall_nth_error
       _ _
       before_pis (Tiling.PL.ip_nth_ext tau2) before_pi2
       Hwf_before_pis Hbefore2)
    as Hwf_before2.
  pose proof
    (tiling_rel_pinstr_structure_source_after_matches
       (List.length before_ctxt) before_pi1 after_pi1 w1 Hstmt1 Hpoint_depth1)
    as Hafter_wit1.
  pose proof
    (tiling_rel_pinstr_structure_source_after_matches
       (List.length before_ctxt) before_pi2 after_pi2 w2 Hstmt2 Hpoint_depth2)
    as Hafter_wit2.
  assert (Hafter_depth_eq1 :
    Tiling.PL.pi_depth after_pi1 =
    (Tiling.PL.pi_depth before_pi1 + List.length (stw_links w1))%nat).
  {
    unfold Tiling.tiling_rel_pinstr_structure_source in Hstmt1.
    destruct Hstmt1 as [_ [Hdepth_eq1 _]].
    exact Hdepth_eq1.
  }
  assert (Hafter_depth_eq2 :
    Tiling.PL.pi_depth after_pi2 =
    (Tiling.PL.pi_depth before_pi2 + List.length (stw_links w2))%nat).
  {
    unfold Tiling.tiling_rel_pinstr_structure_source in Hstmt2.
    destruct Hstmt2 as [_ [Hdepth_eq2 _]].
    exact Hdepth_eq2.
  }
  assert (Hstmt1_env :
    Tiling.tiling_rel_pinstr_structure_source
      (List.length envv) before_pi1 after_pi1
      (Tiling.compiled_pinstr_tiling_witness w1)).
  {
    rewrite <- Hlen_env.
    exact Hstmt1.
  }
  assert (Hstmt2_env :
    Tiling.tiling_rel_pinstr_structure_source
      (List.length envv) before_pi2 after_pi2
      (Tiling.compiled_pinstr_tiling_witness w2)).
  {
    rewrite <- Hlen_env.
    exact Hstmt2.
  }
  unfold Tiling.compose_tiling_pinstr_ext in Hbel1, Hbel2.
  destruct Hbel1 as [Hafter_dom1 [_ [_ [Hts11 [Hts21 [_ Hbel_len1]]]]]].
  destruct Hbel2 as [Hafter_dom2 [_ [_ [Hts12 [Hts22 [_ Hbel_len2]]]]]].
  destruct Hafter_wit1 as [Hafter_pw1 Hafter_depth1].
  destruct Hafter_wit2 as [Hafter_pw2 Hafter_depth2].
  destruct Hwf_stmt1 as [Hwf_stmt1 Hparams1].
  destruct Hwf_stmt2 as [Hwf_stmt2 Hparams2].
  destruct Hwf_before1 as [Hwf_before1_core _].
  destruct Hwf_before2 as [Hwf_before2_core _].
  destruct Hwf_before1_core as
      [_ [Hcols_before1 [_ [_ [_ [_ [_ [Hsched_before1 _]]]]]]]].
  destruct Hwf_before2_core as
      [_ [Hcols_before2 [_ [_ [_ [_ [_ [Hsched_before2 _]]]]]]]].
  set (added1 :=
    Tiling.tiled_added_part
      (List.length envv) (List.length (stw_links w1))
      (Tiling.PL.ip_index_ext tau1)).
  set (point1 :=
    Tiling.tiled_point_part
      (List.length envv) (List.length (stw_links w1))
      (Tiling.PL.ip_index_ext tau1)).
  set (added2 :=
    Tiling.tiled_added_part
      (List.length envv) (List.length (stw_links w2))
      (Tiling.PL.ip_index_ext tau2)).
  set (point2 :=
    Tiling.tiled_point_part
      (List.length envv) (List.length (stw_links w2))
      (Tiling.PL.ip_index_ext tau2)).
  assert (Hadded_len1 : List.length added1 = List.length (stw_links w1)).
  {
    subst added1.
    assert (Hlen1_split :
      List.length (Tiling.PL.ip_index_ext tau1) =
      (List.length envv + List.length (stw_links w1) + stw_point_dim w1)%nat).
    {
      rewrite <- Hafter_depth1 in Hlen1.
      rewrite Hafter_pw1 in Hlen1.
      unfold witness_current_point_dim, witness_base_point_dim, witness_added_dims in Hlen1.
      simpl in Hlen1.
      lia.
    }
    eapply Tiling.tiled_added_part_length with (point_dim := stw_point_dim w1).
    exact Hlen1_split.
  }
  assert (Hadded_len2 : List.length added2 = List.length (stw_links w2)).
  {
    subst added2.
    assert (Hlen2_split :
      List.length (Tiling.PL.ip_index_ext tau2) =
      (List.length envv + List.length (stw_links w2) + stw_point_dim w2)%nat).
    {
      rewrite <- Hafter_depth2 in Hlen2.
      rewrite Hafter_pw2 in Hlen2.
      unfold witness_current_point_dim, witness_base_point_dim, witness_added_dims in Hlen2.
      simpl in Hlen2.
      lia.
    }
    eapply Tiling.tiled_added_part_length with (point_dim := stw_point_dim w2).
    exact Hlen2_split.
  }
  assert (Hpoint_len1 : List.length point1 = stw_point_dim w1).
  {
    subst point1.
    assert (Hlen1_split :
      List.length (Tiling.PL.ip_index_ext tau1) =
      (List.length envv + List.length (stw_links w1) + stw_point_dim w1)%nat).
    {
      rewrite <- Hafter_depth1 in Hlen1.
      rewrite Hafter_pw1 in Hlen1.
      unfold witness_current_point_dim, witness_base_point_dim, witness_added_dims in Hlen1.
      simpl in Hlen1.
      lia.
    }
    eapply Tiling.tiled_point_part_length
      with (added_dims := List.length (stw_links w1)).
    exact Hlen1_split.
  }
  assert (Hpoint_len2 : List.length point2 = stw_point_dim w2).
  {
    subst point2.
    assert (Hlen2_split :
      List.length (Tiling.PL.ip_index_ext tau2) =
      (List.length envv + List.length (stw_links w2) + stw_point_dim w2)%nat).
    {
      rewrite <- Hafter_depth2 in Hlen2.
      rewrite Hafter_pw2 in Hlen2.
      unfold witness_current_point_dim, witness_base_point_dim, witness_added_dims in Hlen2.
      simpl in Hlen2.
      lia.
    }
    eapply Tiling.tiled_point_part_length
      with (added_dims := List.length (stw_links w2)).
    exact Hlen2_split.
  }
  assert (Hidx_split1 :
    Tiling.PL.ip_index_ext tau1 = envv ++ added1 ++ point1).
  {
    subst added1 point1.
    transitivity
      (firstn (List.length envv) (Tiling.PL.ip_index_ext tau1) ++
       Tiling.tiled_added_part
         (List.length envv) (List.length (stw_links w1))
         (Tiling.PL.ip_index_ext tau1) ++
       Tiling.tiled_point_part
         (List.length envv) (List.length (stw_links w1))
         (Tiling.PL.ip_index_ext tau1)).
    - apply Tiling.tiled_index_split.
    - replace
        (firstn (List.length envv) (Tiling.PL.ip_index_ext tau1))
        with envv by exact Hpref1.
      reflexivity.
  }
  assert (Hidx_split2 :
    Tiling.PL.ip_index_ext tau2 = envv ++ added2 ++ point2).
  {
    subst added2 point2.
    transitivity
      (firstn (List.length envv) (Tiling.PL.ip_index_ext tau2) ++
       Tiling.tiled_added_part
         (List.length envv) (List.length (stw_links w2))
         (Tiling.PL.ip_index_ext tau2) ++
       Tiling.tiled_point_part
         (List.length envv) (List.length (stw_links w2))
         (Tiling.PL.ip_index_ext tau2)).
    - apply Tiling.tiled_index_split.
    - replace
        (firstn (List.length envv) (Tiling.PL.ip_index_ext tau2))
        with envv by exact Hpref2.
      reflexivity.
  }
  assert (Hts11_old :
    Tiling.PL.ip_time_stamp1_ext tau1 =
    affine_product (Tiling.PL.pi_schedule before_pi1) (envv ++ point1)).
  {
    rewrite Hts11.
    cbn [Tiling.compose_tiling_pinstr_ext].
    rewrite Hidx_split1.
    unfold Tiling.lift_schedule_after_env.
    eapply Tiling.lift_affine_function_after_env_eval.
    - reflexivity.
    - exact Hadded_len1.
  }
  assert (Hts12_old :
    Tiling.PL.ip_time_stamp1_ext tau2 =
    affine_product (Tiling.PL.pi_schedule before_pi2) (envv ++ point2)).
  {
    rewrite Hts12.
    cbn [Tiling.compose_tiling_pinstr_ext].
    rewrite Hidx_split2.
    unfold Tiling.lift_schedule_after_env.
    eapply Tiling.lift_affine_function_after_env_eval.
    - reflexivity.
    - exact Hadded_len2.
  }
  assert (Hts21_after :
    Tiling.PL.ip_time_stamp2_ext tau1 =
    affine_product (Tiling.PL.pi_schedule after_pi1) (Tiling.PL.ip_index_ext tau1)).
  {
    rewrite Hts21.
    cbn [Tiling.compose_tiling_pinstr_ext].
    reflexivity.
  }
  assert (Hts22_after :
    Tiling.PL.ip_time_stamp2_ext tau2 =
    affine_product (Tiling.PL.pi_schedule after_pi2) (Tiling.PL.ip_index_ext tau2)).
  {
    rewrite Hts22.
    cbn [Tiling.compose_tiling_pinstr_ext].
    reflexivity.
  }
  assert (Hadded_eq1 :
    added1 = eval_tile_links [] point1 envv (stw_links w1)).
  {
    pose proof
      (Tiling.tiling_rel_pinstr_structure_source_domain_complete
         envv before_pi1 after_pi1 (Tiling.compiled_pinstr_tiling_witness w1)
         added1 point1
         Hstmt1_env
         (Tiling.wf_compiled_pinstr_tiling_witness w1)
         (Tiling.compiled_pinstr_tiling_witness_matches w1)
         Hadded_len1 Hpoint_len1 (conj Hwf_stmt1 Hparams1) Hsizes1)
      as Hcomplete1.
    rewrite Hidx_split1 in Hafter_dom1.
    specialize (Hcomplete1 Hafter_dom1).
    tauto.
  }
  assert (Hadded_eq2 :
    added2 = eval_tile_links [] point2 envv (stw_links w2)).
  {
    pose proof
      (Tiling.tiling_rel_pinstr_structure_source_domain_complete
         envv before_pi2 after_pi2 (Tiling.compiled_pinstr_tiling_witness w2)
         added2 point2
         Hstmt2_env
         (Tiling.wf_compiled_pinstr_tiling_witness w2)
         (Tiling.compiled_pinstr_tiling_witness_matches w2)
         Hadded_len2 Hpoint_len2 (conj Hwf_stmt2 Hparams2) Hsizes2)
      as Hcomplete2.
    rewrite Hidx_split2 in Hafter_dom2.
    specialize (Hcomplete2 Hafter_dom2).
    tauto.
  }
  unfold pinstr_tiling_band_cert in Hcert1, Hcert2.
  destruct Hcert1 as [Hmatch1 Hsched_match1].
  destruct Hcert2 as [Hmatch2 Hsched_match2].
  unfold pinstr_tiling_band_matches in Hmatch1, Hmatch2.
  destruct (schedule_rows_of_links w1) as [rows1|] eqn:Hrows1; try contradiction.
  destruct (schedule_rows_of_links w2) as [rows2|] eqn:Hrows2; try contradiction.
  destruct Hmatch1 as [Hband_len1 Hrows_match1].
  destruct Hmatch2 as [Hband_len2 Hrows_match2].
  assert (Hadded_len1_band : List.length added1 = ptb_len band).
  {
    rewrite Hadded_len1.
    symmetry.
    exact Hband_len1.
  }
  assert (Hadded_len2_band : List.length added2 = ptb_len band).
  {
    rewrite Hadded_len2.
    symmetry.
    exact Hband_len2.
  }
  assert (Hband_rows1 :
    instr_point_ext_band_block_ts band tau1 =
    affine_product rows1 (envv ++ point1)).
  {
    unfold instr_point_ext_band_block_ts.
    rewrite Hts11_old.
    rewrite <- affine_product_skipn.
    rewrite <- affine_product_firstn.
    rewrite Hrows_match1.
    reflexivity.
  }
  assert (Hband_rows2 :
    instr_point_ext_band_block_ts band tau2 =
    affine_product rows2 (envv ++ point2)).
  {
    unfold instr_point_ext_band_block_ts.
    rewrite Hts12_old.
    rewrite <- affine_product_skipn.
    rewrite <- affine_product_firstn.
    rewrite Hrows_match2.
    reflexivity.
  }
  set (prefix1 := instr_point_ext_band_prefix_ts band tau1).
  set (prefix2 := instr_point_ext_band_prefix_ts band tau2).
  set (band_ts1 := instr_point_ext_band_block_ts band tau1).
  set (band_ts2 := instr_point_ext_band_block_ts band tau2).
  set (suffix1 :=
    skipn (ptb_start band + ptb_len band)%nat
      (Tiling.PL.ip_time_stamp1_ext tau1)).
  set (suffix2 :=
    skipn (ptb_start band + ptb_len band)%nat
      (Tiling.PL.ip_time_stamp1_ext tau2)).
  assert (Hprefix_len :
    List.length prefix1 = List.length prefix2).
  {
    subst prefix1 prefix2.
    unfold instr_point_ext_band_prefix_ts.
    rewrite !firstn_length.
    pose proof (infer_pinstr_tiling_band_bound _ _ _ Hinfer1) as Hbound1.
    pose proof (infer_pinstr_tiling_band_bound _ _ _ Hinfer2) as Hbound2.
    try rewrite Hts11_old.
    try rewrite Hts12_old.
    unfold affine_product.
    rewrite !map_length.
    lia.
  }
  assert (Hband_len :
    List.length band_ts1 = List.length band_ts2).
  {
    subst band_ts1 band_ts2.
    unfold instr_point_ext_band_block_ts.
    rewrite !firstn_length, !skipn_length.
    pose proof (infer_pinstr_tiling_band_bound _ _ _ Hinfer1) as Hbound1.
    pose proof (infer_pinstr_tiling_band_bound _ _ _ Hinfer2) as Hbound2.
    try rewrite Hts11_old.
    try rewrite Hts12_old.
    unfold affine_product.
    rewrite !map_length.
    lia.
  }
  assert (Hold_split1 :
    Tiling.PL.ip_time_stamp1_ext tau1 = prefix1 ++ band_ts1 ++ suffix1).
  {
    subst prefix1 band_ts1 suffix1.
    rewrite <- firstn_skipn with (n := ptb_start band)
      (l := Tiling.PL.ip_time_stamp1_ext tau1) at 1.
    f_equal.
    rewrite <- firstn_skipn with (n := ptb_len band)
      (l := skipn (ptb_start band) (Tiling.PL.ip_time_stamp1_ext tau1)) at 1.
    f_equal.
    rewrite skipn_skipn.
    rewrite Nat.add_comm.
    reflexivity.
  }
  assert (Hold_split2 :
    Tiling.PL.ip_time_stamp1_ext tau2 = prefix2 ++ band_ts2 ++ suffix2).
  {
    subst prefix2 band_ts2 suffix2.
    rewrite <- firstn_skipn with (n := ptb_start band)
      (l := Tiling.PL.ip_time_stamp1_ext tau2) at 1.
    f_equal.
    rewrite <- firstn_skipn with (n := ptb_len band)
      (l := skipn (ptb_start band) (Tiling.PL.ip_time_stamp1_ext tau2)) at 1.
    f_equal.
    rewrite skipn_skipn.
    rewrite Nat.add_comm.
    reflexivity.
  }
  assert (Hcols_before1_local :
    (List.length envv <= List.length envv + Tiling.PL.pi_depth before_pi1)%nat).
  { lia. }
  assert (Hcols_before2_local :
    (List.length envv <= List.length envv + Tiling.PL.pi_depth before_pi2)%nat).
  { lia. }
  assert (Hsched_before1_env :
    exact_listzzs_cols
      (List.length envv + Tiling.PL.pi_depth before_pi1)
      (Tiling.PL.pi_schedule before_pi1)).
  {
    rewrite <- Hlen_env.
    exact Hsched_before1.
  }
  assert (Hsched_before2_env :
    exact_listzzs_cols
      (List.length envv + Tiling.PL.pi_depth before_pi2)
      (Tiling.PL.pi_schedule before_pi2)).
  {
    rewrite <- Hlen_env.
    exact Hsched_before2.
  }
  assert (Hexpected_ts1 :
    affine_product
      (stripmine_schedule_after_env
         (List.length envv) (Tiling.PL.pi_schedule before_pi1) band)
      (Tiling.PL.ip_index_ext tau1) =
    prefix1 ++ added1 ++ band_ts1 ++ suffix1).
  {
    subst prefix1 band_ts1 suffix1.
    rewrite Hidx_split1.
    pose proof
      (stripmine_schedule_after_env_eval
         (List.length envv) (Tiling.PL.pi_schedule before_pi1) band
         (List.length envv + Tiling.PL.pi_depth before_pi1)
         envv added1 point1
         Hsched_before1_env Hcols_before1_local eq_refl
         (eq_trans Hadded_len1 (eq_sym Hband_len1)))
      as Heval1.
    rewrite <- Hts11_old in Heval1.
    exact Heval1.
  }
  assert (Hexpected_ts2 :
    affine_product
      (stripmine_schedule_after_env
         (List.length envv) (Tiling.PL.pi_schedule before_pi2) band)
      (Tiling.PL.ip_index_ext tau2) =
    prefix2 ++ added2 ++ band_ts2 ++ suffix2).
  {
    subst prefix2 band_ts2 suffix2.
    rewrite Hidx_split2.
    pose proof
      (stripmine_schedule_after_env_eval
         (List.length envv) (Tiling.PL.pi_schedule before_pi2) band
         (List.length envv + Tiling.PL.pi_depth before_pi2)
         envv added2 point2
         Hsched_before2_env Hcols_before2_local eq_refl
         (eq_trans Hadded_len2 (eq_sym Hband_len2)))
      as Heval2.
    rewrite <- Hts12_old in Heval2.
    exact Heval2.
  }
  destruct Hsched_match1 as [cols1 [extra1 Hafter_sched1]].
  destruct Hsched_match2 as [cols2 [extra2 Hafter_sched2]].
  assert (Hactual_ts1 :
    Tiling.PL.ip_time_stamp2_ext tau1 =
    (prefix1 ++ added1 ++ band_ts1 ++ suffix1) ++ repeat 0%Z extra1).
  {
    rewrite Hts21_after.
    rewrite Hafter_sched1.
    rewrite affine_product_pad_schedule_with_zero_rows.
    replace
      (affine_product
         (stripmine_schedule_after_env
            (List.length before_ctxt) (Tiling.PL.pi_schedule before_pi1) band)
         (Tiling.PL.ip_index_ext tau1))
      with (prefix1 ++ added1 ++ band_ts1 ++ suffix1).
    2:{
      symmetry.
      rewrite Hlen_env.
      exact Hexpected_ts1.
    }
    reflexivity.
  }
  assert (Hactual_ts2 :
    Tiling.PL.ip_time_stamp2_ext tau2 =
    (prefix2 ++ added2 ++ band_ts2 ++ suffix2) ++ repeat 0%Z extra2).
  {
    rewrite Hts22_after.
    rewrite Hafter_sched2.
    rewrite affine_product_pad_schedule_with_zero_rows.
    replace
      (affine_product
         (stripmine_schedule_after_env
            (List.length before_ctxt) (Tiling.PL.pi_schedule before_pi2) band)
         (Tiling.PL.ip_index_ext tau2))
      with (prefix2 ++ added2 ++ band_ts2 ++ suffix2).
    2:{
      symmetry.
      rewrite Hlen_env.
      exact Hexpected_ts2.
    }
    reflexivity.
  }
  assert (Hexpected_len_eq :
    List.length (prefix1 ++ added1 ++ band_ts1 ++ suffix1) =
    List.length (prefix2 ++ added2 ++ band_ts2 ++ suffix2)).
  {
    pose proof
      (Hsame_schedule_len before_pi1 before_pi2 Hbefore1 Hbefore2)
      as Hsched_len.
    rewrite <- Hexpected_ts1, <- Hexpected_ts2.
    unfold affine_product.
    rewrite !map_length.
    rewrite !stripmine_schedule_after_env_length.
    rewrite Hsched_len.
    reflexivity.
  }
  assert (Hnew_expected_not_lt :
    lex_compare
      (prefix1 ++ added1 ++ band_ts1 ++ suffix1)
      (prefix2 ++ added2 ++ band_ts2 ++ suffix2) <> Lt).
  {
    unfold Tiling.PL.instr_point_ext_new_sched_ge in Hnew.
    rewrite Hactual_ts1 in Hnew.
    rewrite Hactual_ts2 in Hnew.
    eapply
      (lex_compare_app_preserves_not_lt_backward_local
         (prefix1 ++ added1 ++ band_ts1 ++ suffix1)
         (prefix2 ++ added2 ++ band_ts2 ++ suffix2)
         (repeat 0%Z extra1) (repeat 0%Z extra2)); eauto.
    intro Hlt.
    destruct Hnew as [Heq | Hgt]; congruence.
  }
  assert (Htiles_eq :
    band_ts1 = band_ts2 -> added1 = added2).
  {
    intro Hband_eq_ts.
    assert (Hsizes_recipe1 :
      List.map tl_tile_size (stw_links w1) =
      tile_sizes_of_witness w1) by reflexivity.
    assert (Hsizes_recipe2 :
      List.map tl_tile_size (stw_links w2) =
      tile_sizes_of_witness w1).
    {
      unfold tile_sizes_of_witness in Hselected_sizes.
      symmetry.
      exact Hselected_sizes.
    }
    rewrite Hadded_eq1, Hadded_eq2.
    eapply common_recipe_equal_band_block_implies_equal_tiles.
    - exact Hpoint_len1.
    - exact Hpoint_len2.
    - exact Hrows1.
    - exact Hrows2.
    - exact Hsizes_recipe1.
    - exact Hsizes_recipe2.
    - exact Hwf_stmt1.
    - exact Hwf_stmt2.
    - exact Hparams1.
    - exact Hparams2.
    - rewrite <- Hband_rows1, <- Hband_rows2.
      exact Hband_eq_ts.
  }
  assert (Htiles_mono :
    listz_pointwise_le band_ts1 band_ts2 ->
    listz_pointwise_le added1 added2).
  {
    intro Hband_le.
    assert (Hsizes_recipe1 :
      List.map tl_tile_size (stw_links w1) =
      tile_sizes_of_witness w1) by reflexivity.
    assert (Hsizes_recipe2 :
      List.map tl_tile_size (stw_links w2) =
      tile_sizes_of_witness w1).
    {
      unfold tile_sizes_of_witness in Hselected_sizes.
      symmetry.
      exact Hselected_sizes.
    }
    rewrite Hadded_eq1, Hadded_eq2.
    eapply common_recipe_band_pointwise_le_implies_tiles_pointwise_le.
    - exact Hpoint_len1.
    - exact Hpoint_len2.
    - exact Hrows1.
    - exact Hrows2.
    - exact Hsizes_recipe1.
    - exact Hsizes_recipe2.
    - exact Hwf_stmt1.
    - exact Hwf_stmt2.
    - exact Hparams1.
    - exact Hparams2.
    - exact Hsizes1.
    - rewrite <- Hband_rows1, <- Hband_rows2.
      exact Hband_le.
  }
  unfold Tiling.PL.instr_point_ext_old_sched_lt in Hold.
  rewrite Hold_split1, Hold_split2 in Hold.
  destruct
    (stripmined_reversal_implies_decreasing_band_component
       prefix1 prefix2 added1 added2 band_ts1 band_ts2 suffix1 suffix2
       Hprefix_len Hband_len Htiles_eq Htiles_mono
       Hold Hnew_expected_not_lt)
    as [Hprefix_eq [dim [x [y [Hx [Hy Hgt]]]]]].
  assert (Hband_ts1_len : List.length band_ts1 = ptb_len band).
  {
    change
      (List.length (instr_point_ext_band_block_ts band tau1) =
       ptb_len band).
    rewrite Hband_rows1.
    unfold affine_product.
    rewrite List.map_length.
    pose proof (schedule_rows_of_links_length _ _ Hrows1) as Hrows_len.
    lia.
  }
  assert (Hdim : (dim < ptb_len band)%nat).
  {
    rewrite <- Hband_ts1_len.
    apply nth_error_Some.
    rewrite Hx.
    discriminate.
  }
  assert (Hx_full :
    nth_error
      (Tiling.PL.ip_time_stamp1_ext tau1)
      (ptb_start band + dim)%nat = Some x).
  {
    eapply nth_error_band_block_to_full; [exact Hdim|].
    change (nth_error band_ts1 dim = Some x).
    exact Hx.
  }
  assert (Hy_full :
    nth_error
      (Tiling.PL.ip_time_stamp1_ext tau2)
      (ptb_start band + dim)%nat = Some y).
  {
    eapply nth_error_band_block_to_full; [exact Hdim|].
    change (nth_error band_ts2 dim = Some y).
    exact Hy.
  }
  exists band.
  split; [reflexivity|].
  split; [reflexivity|].
  split.
  - exact Hprefix_eq.
  - exists dim, x, y.
    repeat split; assumption.
Qed.

Lemma ordinary_pair_local_reversal_bridge_wf_with_env_len :
  forall before_pis before_ctxt before_vars after_pis ws bands envv
         ipl_ext tau1 tau2,
    List.length before_ctxt = List.length envv ->
    infer_pinstr_list_tiling_bands before_pis ws = Some bands ->
    pprog_tiling_bands_cert
      (List.length before_ctxt) before_pis after_pis ws bands ->
    Tiling.tiling_rel_pprog_structure_source
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars)
      (List.map Tiling.compiled_pinstr_tiling_witness ws) ->
    Forall
      (Tiling.wf_statement_tiling_witness_with_param_dim
         (List.length before_ctxt))
      ws ->
    Forall
      (fun w => Forall (fun link => 0 < tl_tile_size link) (stw_links w))
      ws ->
    Forall2
      (fun before_pi w => stw_point_dim w = Tiling.PL.pi_depth before_pi)
      before_pis ws ->
    uniform_schedule_arity before_pis ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    Tiling.PL.flatten_instrs_ext
      envv
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length envv) before_pis after_pis ws)
      ipl_ext ->
    In tau1 ipl_ext ->
    In tau2 ipl_ext ->
    Tiling.PL.instr_point_ext_old_sched_lt tau1 tau2 ->
    Tiling.PL.instr_point_ext_new_sched_ge tau1 tau2 ->
    (forall band1 band2,
       nth_error bands (Tiling.PL.ip_nth_ext tau1) = Some band1 ->
       nth_error bands (Tiling.PL.ip_nth_ext tau2) = Some band2 ->
       band1 = band2) ->
    (forall w1 w2,
       nth_error ws (Tiling.PL.ip_nth_ext tau1) = Some w1 ->
       nth_error ws (Tiling.PL.ip_nth_ext tau2) = Some w2 ->
       tile_sizes_of_witness w1 = tile_sizes_of_witness w2) ->
    exists band,
      nth_error bands (Tiling.PL.ip_nth_ext tau1) = Some band /\
      nth_error bands (Tiling.PL.ip_nth_ext tau2) = Some band /\
      instr_point_ext_same_band_slice band tau1 tau2 /\
      instr_point_ext_band_component_decreases band tau1 tau2.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws bands envv
         ipl_ext tau1 tau2
         Hlen_env Hinfer Hbands Hprog Hwf_ws Hsizes_ws Hdepths
         [schedule_len Hschedule_len] Hwf_before
         Hflat Hin1 Hin2 Hold Hnew Hsame_band Hsame_recipe.
  eapply
    (ordinary_pair_local_reversal_bridge_by_schedule_len_wf_with_env_len
       before_pis before_ctxt before_vars after_pis ws bands envv
       ipl_ext tau1 tau2); eauto.
  intros before_pi1 before_pi2 Hbefore1 Hbefore2.
  rewrite
    (uniform_schedule_arity_nth_error
       before_pis schedule_len _ _ Hschedule_len Hbefore1),
    (uniform_schedule_arity_nth_error
       before_pis schedule_len _ _ Hschedule_len Hbefore2).
  reflexivity.
Qed.

Lemma pprog_pluto_permutable_tiling_bands_strong_implies_reordering_safe_wf_with_env_len :
  forall before_pis before_ctxt before_vars after_pis ws bands envv,
    List.length before_ctxt = List.length envv ->
    infer_pinstr_list_tiling_bands before_pis ws = Some bands ->
    pprog_tiling_bands_cert
      (List.length before_ctxt) before_pis after_pis ws bands ->
    Tiling.tiling_rel_pprog_structure_source
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars)
      (List.map Tiling.compiled_pinstr_tiling_witness ws) ->
    Forall
      (Tiling.wf_statement_tiling_witness_with_param_dim
         (List.length before_ctxt))
      ws ->
    Forall
      (fun w => Forall (fun link => 0 < tl_tile_size link) (stw_links w))
      ws ->
    Forall2
      (fun before_pi w => stw_point_dim w = Tiling.PL.pi_depth before_pi)
      before_pis ws ->
    uniform_schedule_arity before_pis ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    pprog_pluto_permutable_tiling_bands_strong
      envv before_pis after_pis ws bands ->
    pprog_tiling_reordering_safe envv before_pis after_pis ws bands.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws bands envv
         Hlen_env Hinfer Hbands Hprog Hwf_ws Hsizes_ws Hdepths
         Harity Hwf_before Hpluto.
  eapply
    (pprog_pluto_permutable_tiling_bands_strong_implies_reordering_safe_if_local_bridge
       envv before_pis after_pis ws bands); [exact Hpluto|].
  intros ipl_ext tau1 tau2 band sizes
         Hcommon Hrecipe Hflat Hin1 Hin2 Hold Hnew.
  assert (Hsame_band :
    forall band1 band2,
      nth_error bands (Tiling.PL.ip_nth_ext tau1) = Some band1 ->
      nth_error bands (Tiling.PL.ip_nth_ext tau2) = Some band2 ->
      band1 = band2).
  {
    intros band1 band2 Hband1 Hband2.
    pose proof
      (common_tiling_band_nth_error
         bands band (Tiling.PL.ip_nth_ext tau1) band1
         Hcommon Hband1) as Hband1_eq.
    pose proof
      (common_tiling_band_nth_error
         bands band (Tiling.PL.ip_nth_ext tau2) band2
         Hcommon Hband2) as Hband2_eq.
    congruence.
  }
  assert (Hsame_recipe :
    forall w1 w2,
      nth_error ws (Tiling.PL.ip_nth_ext tau1) = Some w1 ->
      nth_error ws (Tiling.PL.ip_nth_ext tau2) = Some w2 ->
      tile_sizes_of_witness w1 = tile_sizes_of_witness w2).
  {
    intros w1 w2 Hw1 Hw2.
    pose proof
      (common_tiling_band_recipe_nth_error
         ws sizes (Tiling.PL.ip_nth_ext tau1) w1 Hrecipe Hw1)
      as Hsizes1.
    pose proof
      (common_tiling_band_recipe_nth_error
         ws sizes (Tiling.PL.ip_nth_ext tau2) w2 Hrecipe Hw2)
      as Hsizes2.
    unfold tile_sizes_of_witness.
    congruence.
  }
  destruct
    (ordinary_pair_local_reversal_bridge_wf_with_env_len
       before_pis before_ctxt before_vars after_pis ws bands envv
       ipl_ext tau1 tau2
       Hlen_env Hinfer Hbands Hprog Hwf_ws Hsizes_ws Hdepths
       Harity Hwf_before Hflat Hin1 Hin2 Hold Hnew
       Hsame_band Hsame_recipe)
    as [band' [Hband1 [_ [Hslice Hcomponent]]]].
  pose proof
    (common_tiling_band_nth_error
       bands band (Tiling.PL.ip_nth_ext tau1) band'
       Hcommon Hband1) as Hband_eq.
  subst band'.
  split; assumption.
Qed.

Lemma second_level_pair_local_reversal_bridge_by_layout_wf_with_env_len :
  forall layout before_pis before_ctxt before_vars
         after_pis ws bands recipes envv,
    List.length before_ctxt = List.length envv ->
    infer_pinstr_list_second_level_bands before_pis ws =
      Some (bands, recipes) ->
    second_level_schedule_layout_lex_equivalent
      layout (List.length before_ctxt) before_pis after_pis bands ->
    Tiling.tiling_rel_pprog_structure_source
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars)
      (List.map Tiling.compiled_pinstr_tiling_witness ws) ->
    Forall
      (Tiling.wf_statement_tiling_witness_with_param_dim
         (List.length before_ctxt))
      ws ->
    Forall
      (fun w => Forall (fun link => 0 < tl_tile_size link) (stw_links w))
      ws ->
    Forall2
      (fun before_pi w => stw_point_dim w = Tiling.PL.pi_depth before_pi)
      before_pis ws ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    forall ipl_ext tau1 tau2,
      Tiling.PL.flatten_instrs_ext
        envv
        (Tiling.compose_tiling_pinstrs_ext_from_after
           (List.length envv) before_pis after_pis ws)
        ipl_ext ->
      In tau1 ipl_ext ->
      In tau2 ipl_ext ->
      Tiling.PL.instr_point_ext_old_sched_lt tau1 tau2 ->
      Tiling.PL.instr_point_ext_new_sched_ge tau1 tau2 ->
      (forall recipe1 recipe2,
         nth_error recipes (Tiling.PL.ip_nth_ext tau1) = Some recipe1 ->
         nth_error recipes (Tiling.PL.ip_nth_ext tau2) = Some recipe2 ->
         slbr_root_sizes recipe1 = slbr_root_sizes recipe2 /\
         slbr_child_sizes recipe1 = slbr_child_sizes recipe2) ->
      (forall band1 band2,
         nth_error bands (Tiling.PL.ip_nth_ext tau1) = Some band1 ->
         nth_error bands (Tiling.PL.ip_nth_ext tau2) = Some band2 ->
         ptb_start band1 = ptb_start band2) ->
      exists band,
        nth_error bands (Tiling.PL.ip_nth_ext tau1) = Some band /\
        nth_error bands (Tiling.PL.ip_nth_ext tau2) = Some band /\
        instr_point_ext_same_band_slice band tau1 tau2 /\
        instr_point_ext_band_component_decreases band tau1 tau2.
Proof.
  intros layout before_pis before_ctxt before_vars
         after_pis ws bands recipes envv
         Hlen_env Hinfer Hsched Hprog Hwf_ws Hsizes_ws Hdepths Hwf_before
         ipl_ext tau1 tau2 Hflat Hin1 Hin2 Hold Hnew
         Hsame_recipe_sizes Hsame_band_start.
  assert (Hwf_ws_env :
    Forall
      (Tiling.wf_statement_tiling_witness_with_param_dim (List.length envv))
      ws).
  {
    rewrite <- Hlen_env.
    exact Hwf_ws.
  }
  destruct (infer_pinstr_list_second_level_bands_lengths _ _ _ _ Hinfer)
    as [Hlen_ws [Hlen_bands Hlen_recipes]].
  destruct
    (composed_point_pair_facts_of_members
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       ws envv ipl_ext tau1 tau2
       Hprog Hwf_ws_env Hsizes_ws Hdepths Hflat Hin1 Hin2)
    as [Hpoint1 Hpoint2].
  unfold composed_point_facts in Hpoint1, Hpoint2.
  destruct Hpoint1 as [before_pi1 [after_pi1 [w1
    [Hbefore1 [Hafter1 [Hw1
    [Hwf_stmt1 [Hsizes1 [Hpoint_depth1
    [Hpref1 [Hbel1 Hlen1]]]]]]]]]]].
  destruct Hpoint2 as [before_pi2 [after_pi2 [w2
    [Hbefore2 [Hafter2 [Hw2
    [Hwf_stmt2 [Hsizes2 [Hpoint_depth2
    [Hpref2 [Hbel2 Hlen2]]]]]]]]]]].
  destruct (nth_error bands (Tiling.PL.ip_nth_ext tau1))
    as [band1|] eqn:Hband1.
  2:{
    apply nth_error_None in Hband1.
    assert (Hlt :
      (Tiling.PL.ip_nth_ext tau1 < List.length before_pis)%nat).
    { apply nth_error_Some. rewrite Hbefore1. discriminate. }
    lia.
  }
  destruct (nth_error bands (Tiling.PL.ip_nth_ext tau2))
    as [band2|] eqn:Hband2.
  2:{
    apply nth_error_None in Hband2.
    assert (Hlt :
      (Tiling.PL.ip_nth_ext tau2 < List.length before_pis)%nat).
    { apply nth_error_Some. rewrite Hbefore2. discriminate. }
    lia.
  }
  destruct (nth_error recipes (Tiling.PL.ip_nth_ext tau1))
    as [recipe1|] eqn:Hrecipe1.
  2:{
    apply nth_error_None in Hrecipe1.
    assert (Hlt :
      (Tiling.PL.ip_nth_ext tau1 < List.length before_pis)%nat).
    { apply nth_error_Some. rewrite Hbefore1. discriminate. }
    lia.
  }
  destruct (nth_error recipes (Tiling.PL.ip_nth_ext tau2))
    as [recipe2|] eqn:Hrecipe2.
  2:{
    apply nth_error_None in Hrecipe2.
    assert (Hlt :
      (Tiling.PL.ip_nth_ext tau2 < List.length before_pis)%nat).
    { apply nth_error_Some. rewrite Hbefore2. discriminate. }
    lia.
  }
  pose proof
    (infer_pinstr_list_second_level_bands_nth_error
       before_pis ws bands recipes (Tiling.PL.ip_nth_ext tau1)
       before_pi1 w1 band1 recipe1
       Hinfer Hbefore1 Hw1 Hband1 Hrecipe1) as Hinfer1.
  pose proof
    (infer_pinstr_list_second_level_bands_nth_error
       before_pis ws bands recipes (Tiling.PL.ip_nth_ext tau2)
       before_pi2 w2 band2 recipe2
       Hinfer Hbefore2 Hw2 Hband2 Hrecipe2) as Hinfer2.
  destruct (infer_pinstr_second_level_band_sound _ _ _ _ Hinfer1)
    as [Hspec1 [Hband_len1 Hrows_match1]].
  destruct (infer_pinstr_second_level_band_sound _ _ _ _ Hinfer2)
    as [Hspec2 [Hband_len2 Hrows_match2]].
  destruct
    (Hsame_recipe_sizes recipe1 recipe2 eq_refl eq_refl)
    as [Hroot_sizes_eq Hchild_sizes_eq].
  pose proof
    (Hsame_band_start band1 band2 eq_refl eq_refl) as Hstart_eq.
  destruct (second_level_band_recipe_spec_lengths _ _ _ _ Hspec1)
    as [Hroot_size_len1 Hchild_size_len1].
  destruct (second_level_band_recipe_spec_lengths _ _ _ _ Hspec2)
    as [Hroot_size_len2 Hchild_size_len2].
  assert (Hband_len_eq_nat : ptb_len band1 = ptb_len band2).
  {
    rewrite Hband_len1, Hband_len2.
    rewrite Hroot_size_len1, Hroot_size_len2, Hroot_sizes_eq.
    reflexivity.
  }
  assert (Hband_eq : band1 = band2).
  {
    destruct band1 as [start1 len1], band2 as [start2 len2].
    simpl in Hstart_eq, Hband_len_eq_nat.
    subst start2 len2.
    reflexivity.
  }
  pose proof
    (Tiling.tiling_rel_pprog_structure_source_nth
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       (List.map Tiling.compiled_pinstr_tiling_witness ws)
       (Tiling.PL.ip_nth_ext tau1)
       before_pi1 after_pi1 (Tiling.compiled_pinstr_tiling_witness w1)
       Hprog Hbefore1 Hafter1
       (Tiling.nth_error_map_some
          _ _ Tiling.compiled_pinstr_tiling_witness
          ws (Tiling.PL.ip_nth_ext tau1) w1 Hw1)) as Hstmt1.
  pose proof
    (Tiling.tiling_rel_pprog_structure_source_nth
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       (List.map Tiling.compiled_pinstr_tiling_witness ws)
       (Tiling.PL.ip_nth_ext tau2)
       before_pi2 after_pi2 (Tiling.compiled_pinstr_tiling_witness w2)
       Hprog Hbefore2 Hafter2
       (Tiling.nth_error_map_some
          _ _ Tiling.compiled_pinstr_tiling_witness
          ws (Tiling.PL.ip_nth_ext tau2) w2 Hw2)) as Hstmt2.
  pose proof
    (tiling_rel_pinstr_structure_source_after_matches
       (List.length before_ctxt) before_pi1 after_pi1 w1
       Hstmt1 Hpoint_depth1) as Hafter_wit1.
  pose proof
    (tiling_rel_pinstr_structure_source_after_matches
       (List.length before_ctxt) before_pi2 after_pi2 w2
       Hstmt2 Hpoint_depth2) as Hafter_wit2.
  pose proof
    (Tiling.Forall_nth_error
       _ _ before_pis (Tiling.PL.ip_nth_ext tau1) before_pi1
       Hwf_before Hbefore1) as Hwf_before1.
  pose proof
    (Tiling.Forall_nth_error
       _ _ before_pis (Tiling.PL.ip_nth_ext tau2) before_pi2
       Hwf_before Hbefore2) as Hwf_before2.
  assert (Hstmt1_env :
    Tiling.tiling_rel_pinstr_structure_source
      (List.length envv) before_pi1 after_pi1
      (Tiling.compiled_pinstr_tiling_witness w1)).
  { rewrite <- Hlen_env. exact Hstmt1. }
  assert (Hstmt2_env :
    Tiling.tiling_rel_pinstr_structure_source
      (List.length envv) before_pi2 after_pi2
      (Tiling.compiled_pinstr_tiling_witness w2)).
  { rewrite <- Hlen_env. exact Hstmt2. }
  unfold Tiling.compose_tiling_pinstr_ext in Hbel1, Hbel2.
  destruct Hbel1 as [Hafter_dom1 [_ [_ [Hts11 [Hts21 [_ _]]]]]].
  destruct Hbel2 as [Hafter_dom2 [_ [_ [Hts12 [Hts22 [_ _]]]]]].
  destruct Hafter_wit1 as [Hafter_pw1 Hafter_depth1].
  destruct Hafter_wit2 as [Hafter_pw2 Hafter_depth2].
  destruct Hwf_stmt1 as [Hwf_stmt1 Hparams1].
  destruct Hwf_stmt2 as [Hwf_stmt2 Hparams2].
  destruct Hwf_before1 as [Hwf_before1_core _].
  destruct Hwf_before2 as [Hwf_before2_core _].
  destruct Hwf_before1_core as
      [_ [Hcols_before1 [_ [_ [_ [_ [_ [Hsched_before1 _]]]]]]]].
  destruct Hwf_before2_core as
      [_ [Hcols_before2 [_ [_ [_ [_ [_ [Hsched_before2 _]]]]]]]].
  set (added1 :=
    Tiling.tiled_added_part
      (List.length envv) (List.length (stw_links w1))
      (Tiling.PL.ip_index_ext tau1)).
  set (point1 :=
    Tiling.tiled_point_part
      (List.length envv) (List.length (stw_links w1))
      (Tiling.PL.ip_index_ext tau1)).
  set (added2 :=
    Tiling.tiled_added_part
      (List.length envv) (List.length (stw_links w2))
      (Tiling.PL.ip_index_ext tau2)).
  set (point2 :=
    Tiling.tiled_point_part
      (List.length envv) (List.length (stw_links w2))
      (Tiling.PL.ip_index_ext tau2)).
  assert (Hadded_len1 : List.length added1 = List.length (stw_links w1)).
  {
    subst added1.
    eapply Tiling.tiled_added_part_length with (point_dim := stw_point_dim w1).
    rewrite <- Hafter_depth1 in Hlen1.
    rewrite Hafter_pw1 in Hlen1.
    unfold witness_current_point_dim, witness_base_point_dim, witness_added_dims in Hlen1.
    simpl in Hlen1. lia.
  }
  assert (Hadded_len2 : List.length added2 = List.length (stw_links w2)).
  {
    subst added2.
    eapply Tiling.tiled_added_part_length with (point_dim := stw_point_dim w2).
    rewrite <- Hafter_depth2 in Hlen2.
    rewrite Hafter_pw2 in Hlen2.
    unfold witness_current_point_dim, witness_base_point_dim, witness_added_dims in Hlen2.
    simpl in Hlen2. lia.
  }
  assert (Hpoint_len1 : List.length point1 = stw_point_dim w1).
  {
    subst point1.
    eapply Tiling.tiled_point_part_length
      with (added_dims := List.length (stw_links w1)).
    rewrite <- Hafter_depth1 in Hlen1.
    rewrite Hafter_pw1 in Hlen1.
    unfold witness_current_point_dim, witness_base_point_dim, witness_added_dims in Hlen1.
    simpl in Hlen1. lia.
  }
  assert (Hpoint_len2 : List.length point2 = stw_point_dim w2).
  {
    subst point2.
    eapply Tiling.tiled_point_part_length
      with (added_dims := List.length (stw_links w2)).
    rewrite <- Hafter_depth2 in Hlen2.
    rewrite Hafter_pw2 in Hlen2.
    unfold witness_current_point_dim, witness_base_point_dim, witness_added_dims in Hlen2.
    simpl in Hlen2. lia.
  }
  assert (Hidx_split1 :
    Tiling.PL.ip_index_ext tau1 = envv ++ added1 ++ point1).
  {
    subst added1 point1.
    transitivity
      (firstn (List.length envv) (Tiling.PL.ip_index_ext tau1) ++
       Tiling.tiled_added_part
         (List.length envv) (List.length (stw_links w1))
         (Tiling.PL.ip_index_ext tau1) ++
       Tiling.tiled_point_part
         (List.length envv) (List.length (stw_links w1))
         (Tiling.PL.ip_index_ext tau1)).
    - apply Tiling.tiled_index_split.
    - rewrite Hpref1. reflexivity.
  }
  assert (Hidx_split2 :
    Tiling.PL.ip_index_ext tau2 = envv ++ added2 ++ point2).
  {
    subst added2 point2.
    transitivity
      (firstn (List.length envv) (Tiling.PL.ip_index_ext tau2) ++
       Tiling.tiled_added_part
         (List.length envv) (List.length (stw_links w2))
         (Tiling.PL.ip_index_ext tau2) ++
       Tiling.tiled_point_part
         (List.length envv) (List.length (stw_links w2))
         (Tiling.PL.ip_index_ext tau2)).
    - apply Tiling.tiled_index_split.
    - rewrite Hpref2. reflexivity.
  }
  assert (Hts11_old :
    Tiling.PL.ip_time_stamp1_ext tau1 =
    affine_product (Tiling.PL.pi_schedule before_pi1) (envv ++ point1)).
  {
    rewrite Hts11. cbn [Tiling.compose_tiling_pinstr_ext].
    rewrite Hidx_split1.
    unfold Tiling.lift_schedule_after_env.
    eapply Tiling.lift_affine_function_after_env_eval; eauto.
  }
  assert (Hts12_old :
    Tiling.PL.ip_time_stamp1_ext tau2 =
    affine_product (Tiling.PL.pi_schedule before_pi2) (envv ++ point2)).
  {
    rewrite Hts12. cbn [Tiling.compose_tiling_pinstr_ext].
    rewrite Hidx_split2.
    unfold Tiling.lift_schedule_after_env.
    eapply Tiling.lift_affine_function_after_env_eval; eauto.
  }
  assert (Hts21_after :
    Tiling.PL.ip_time_stamp2_ext tau1 =
    affine_product (Tiling.PL.pi_schedule after_pi1)
      (Tiling.PL.ip_index_ext tau1)).
  { rewrite Hts21. cbn [Tiling.compose_tiling_pinstr_ext]. reflexivity. }
  assert (Hts22_after :
    Tiling.PL.ip_time_stamp2_ext tau2 =
    affine_product (Tiling.PL.pi_schedule after_pi2)
      (Tiling.PL.ip_index_ext tau2)).
  { rewrite Hts22. cbn [Tiling.compose_tiling_pinstr_ext]. reflexivity. }
  assert (Hadded_eq1 :
    added1 = eval_tile_links [] point1 envv (stw_links w1)).
  {
    pose proof
      (Tiling.tiling_rel_pinstr_structure_source_domain_complete
         envv before_pi1 after_pi1 (Tiling.compiled_pinstr_tiling_witness w1)
         added1 point1 Hstmt1_env
         (Tiling.wf_compiled_pinstr_tiling_witness w1)
         (Tiling.compiled_pinstr_tiling_witness_matches w1)
         Hadded_len1 Hpoint_len1 (conj Hwf_stmt1 Hparams1) Hsizes1)
      as Hcomplete1.
    rewrite Hidx_split1 in Hafter_dom1.
    specialize (Hcomplete1 Hafter_dom1). tauto.
  }
  assert (Hadded_eq2 :
    added2 = eval_tile_links [] point2 envv (stw_links w2)).
  {
    pose proof
      (Tiling.tiling_rel_pinstr_structure_source_domain_complete
         envv before_pi2 after_pi2 (Tiling.compiled_pinstr_tiling_witness w2)
         added2 point2 Hstmt2_env
         (Tiling.wf_compiled_pinstr_tiling_witness w2)
         (Tiling.compiled_pinstr_tiling_witness_matches w2)
         Hadded_len2 Hpoint_len2 (conj Hwf_stmt2 Hparams2) Hsizes2)
      as Hcomplete2.
    rewrite Hidx_split2 in Hafter_dom2.
    specialize (Hcomplete2 Hafter_dom2). tauto.
  }
  set (roots1 := second_level_root_tiles recipe1 envv point1).
  set (children1 := second_level_child_tiles recipe1 envv point1).
  set (roots2 := second_level_root_tiles recipe2 envv point2).
  set (children2 := second_level_child_tiles recipe2 envv point2).
  assert (Hadded_tiles1 :
    added1 = interleave_root_child_tiles roots1 children1).
  {
    rewrite Hadded_eq1.
    subst roots1 children1.
    change
      (eval_tile_links [] point1 envv (stw_links w1) =
       [] ++
       interleave_root_child_tiles
         (second_level_root_tiles recipe1 envv point1)
         (second_level_child_tiles recipe1 envv point1)).
    exact
      (eval_tile_links_from_second_level_recipe_spec
         _ _ _ _ Hspec1 [] point1 envv eq_refl Hpoint_len1
         Hwf_stmt1 Hparams1).
  }
  assert (Hadded_tiles2 :
    added2 = interleave_root_child_tiles roots2 children2).
  {
    rewrite Hadded_eq2.
    subst roots2 children2.
    change
      (eval_tile_links [] point2 envv (stw_links w2) =
       [] ++
       interleave_root_child_tiles
         (second_level_root_tiles recipe2 envv point2)
         (second_level_child_tiles recipe2 envv point2)).
    exact
      (eval_tile_links_from_second_level_recipe_spec
         _ _ _ _ Hspec2 [] point2 envv eq_refl Hpoint_len2
         Hwf_stmt2 Hparams2).
  }
  assert (Hroots_len1 : List.length roots1 = ptb_len band1).
  {
    subst roots1.
    rewrite second_level_root_tiles_length by exact Hroot_size_len1.
    lia.
  }
  assert (Hroots_len2 : List.length roots2 = ptb_len band2).
  {
    subst roots2.
    rewrite second_level_root_tiles_length by exact Hroot_size_len2.
    lia.
  }
  assert (Hroots_children1 : List.length roots1 = List.length children1).
  {
    subst roots1 children1.
    unfold second_level_child_tiles.
    rewrite List.map_length, combine_length.
    rewrite second_level_root_tiles_length by exact Hroot_size_len1.
    lia.
  }
  assert (Hroots_children2 : List.length roots2 = List.length children2).
  {
    subst roots2 children2.
    unfold second_level_child_tiles.
    rewrite List.map_length, combine_length.
    rewrite second_level_root_tiles_length by exact Hroot_size_len2.
    lia.
  }
  assert (Hband_rows1 :
    instr_point_ext_band_block_ts band1 tau1 =
    affine_product (slbr_root_rows recipe1) (envv ++ point1)).
  {
    unfold instr_point_ext_band_block_ts.
    rewrite Hts11_old, <- affine_product_skipn, <- affine_product_firstn.
    rewrite Hrows_match1. reflexivity.
  }
  assert (Hband_rows2 :
    instr_point_ext_band_block_ts band2 tau2 =
    affine_product (slbr_root_rows recipe2) (envv ++ point2)).
  {
    unfold instr_point_ext_band_block_ts.
    rewrite Hts12_old, <- affine_product_skipn, <- affine_product_firstn.
    rewrite Hrows_match2. reflexivity.
  }
  set (prefix1 := instr_point_ext_band_prefix_ts band1 tau1).
  set (prefix2 := instr_point_ext_band_prefix_ts band2 tau2).
  set (band_ts1 := instr_point_ext_band_block_ts band1 tau1).
  set (band_ts2 := instr_point_ext_band_block_ts band2 tau2).
  set (tiles1 :=
    second_level_schedule_tile_block_by_layout layout recipe1 envv point1).
  set (tiles2 :=
    second_level_schedule_tile_block_by_layout layout recipe2 envv point2).
  set (suffix1 :=
    skipn (ptb_start band1 + ptb_len band1)%nat
      (Tiling.PL.ip_time_stamp1_ext tau1)).
  set (suffix2 :=
    skipn (ptb_start band2 + ptb_len band2)%nat
      (Tiling.PL.ip_time_stamp1_ext tau2)).
  assert (Hprefix_len : List.length prefix1 = List.length prefix2).
  {
    subst prefix1 prefix2.
    unfold instr_point_ext_band_prefix_ts.
    rewrite !firstn_length, Hts11_old, Hts12_old.
    unfold affine_product. rewrite !map_length.
    pose proof (infer_pinstr_second_level_band_bound _ _ _ _ Hinfer1).
    pose proof (infer_pinstr_second_level_band_bound _ _ _ _ Hinfer2).
    lia.
  }
  assert (Hold_split1 :
    Tiling.PL.ip_time_stamp1_ext tau1 = prefix1 ++ band_ts1 ++ suffix1).
  {
    subst prefix1 band_ts1 suffix1.
    rewrite <- firstn_skipn with (n := ptb_start band1)
      (l := Tiling.PL.ip_time_stamp1_ext tau1) at 1.
    f_equal.
    rewrite <- firstn_skipn with (n := ptb_len band1)
      (l := skipn (ptb_start band1) (Tiling.PL.ip_time_stamp1_ext tau1)) at 1.
    f_equal. rewrite skipn_skipn. rewrite Nat.add_comm. reflexivity.
  }
  assert (Hold_split2 :
    Tiling.PL.ip_time_stamp1_ext tau2 = prefix2 ++ band_ts2 ++ suffix2).
  {
    subst prefix2 band_ts2 suffix2.
    rewrite <- firstn_skipn with (n := ptb_start band2)
      (l := Tiling.PL.ip_time_stamp1_ext tau2) at 1.
    f_equal.
    rewrite <- firstn_skipn with (n := ptb_len band2)
      (l := skipn (ptb_start band2) (Tiling.PL.ip_time_stamp1_ext tau2)) at 1.
    f_equal. rewrite skipn_skipn. rewrite Nat.add_comm. reflexivity.
  }
  assert (Hsched_before1_env :
    exact_listzzs_cols
      (List.length envv + Tiling.PL.pi_depth before_pi1)
      (Tiling.PL.pi_schedule before_pi1)).
  { rewrite <- Hlen_env. exact Hsched_before1. }
  assert (Hsched_before2_env :
    exact_listzzs_cols
      (List.length envv + Tiling.PL.pi_depth before_pi2)
      (Tiling.PL.pi_schedule before_pi2)).
  { rewrite <- Hlen_env. exact Hsched_before2. }
  assert (Hexpected_ts1 :
    affine_product
      (stripmine_second_level_schedule_after_env_by_layout
         layout (List.length envv) (Tiling.PL.pi_schedule before_pi1) band1)
      (Tiling.PL.ip_index_ext tau1) =
    prefix1 ++ tiles1 ++ band_ts1 ++ suffix1).
  {
    subst prefix1 band_ts1 suffix1 tiles1.
    unfold instr_point_ext_band_prefix_ts,
           instr_point_ext_band_block_ts,
           second_level_schedule_tile_block_by_layout.
    rewrite Hidx_split1, Hadded_tiles1.
    assert (Henv_cols1 :
      (List.length envv <=
       List.length envv + Tiling.PL.pi_depth before_pi1)%nat) by lia.
    pose proof
      (stripmine_second_level_schedule_after_env_by_layout_eval
         layout (List.length envv) (Tiling.PL.pi_schedule before_pi1) band1
         (List.length envv + Tiling.PL.pi_depth before_pi1)
         envv roots1 children1 point1 Hsched_before1_env Henv_cols1
         eq_refl Hroots_len1 Hroots_children1) as Heval1.
    rewrite <- Hts11_old in Heval1.
    subst roots1 children1.
    repeat rewrite app_assoc in Heval1.
    repeat rewrite app_assoc.
    exact Heval1.
  }
  assert (Hexpected_ts2 :
    affine_product
      (stripmine_second_level_schedule_after_env_by_layout
         layout (List.length envv) (Tiling.PL.pi_schedule before_pi2) band2)
      (Tiling.PL.ip_index_ext tau2) =
    prefix2 ++ tiles2 ++ band_ts2 ++ suffix2).
  {
    subst prefix2 band_ts2 suffix2 tiles2.
    unfold instr_point_ext_band_prefix_ts,
           instr_point_ext_band_block_ts,
           second_level_schedule_tile_block_by_layout.
    rewrite Hidx_split2, Hadded_tiles2.
    assert (Henv_cols2 :
      (List.length envv <=
       List.length envv + Tiling.PL.pi_depth before_pi2)%nat) by lia.
    pose proof
      (stripmine_second_level_schedule_after_env_by_layout_eval
         layout (List.length envv) (Tiling.PL.pi_schedule before_pi2) band2
         (List.length envv + Tiling.PL.pi_depth before_pi2)
         envv roots2 children2 point2 Hsched_before2_env Henv_cols2
         eq_refl Hroots_len2 Hroots_children2) as Heval2.
    rewrite <- Hts12_old in Heval2.
    subst roots2 children2.
    repeat rewrite app_assoc in Heval2.
    repeat rewrite app_assoc.
    exact Heval2.
  }
  pose proof
    (Hsched
       (Tiling.PL.ip_nth_ext tau1)
       (Tiling.PL.ip_nth_ext tau2)
       before_pi1 after_pi1 band1
       before_pi2 after_pi2 band2
       (Tiling.PL.ip_index_ext tau1)
       (Tiling.PL.ip_index_ext tau2)
       Hbefore1 Hafter1 Hband1 Hbefore2 Hafter2 Hband2)
    as Hschedule_compare.
  rewrite <- Hts21_after, <- Hts22_after in Hschedule_compare.
  rewrite Hlen_env, Hexpected_ts1, Hexpected_ts2 in Hschedule_compare.
  assert (Hnew_not_lt :
    lex_compare
      (Tiling.PL.ip_time_stamp2_ext tau1)
      (Tiling.PL.ip_time_stamp2_ext tau2) <> Lt).
  {
    intro Hlt.
    unfold Tiling.PL.instr_point_ext_new_sched_ge in Hnew.
    destruct Hnew; congruence.
  }
  assert (Hnew_expected_not_lt :
    lex_compare
      (prefix1 ++ tiles1 ++ band_ts1 ++ suffix1)
      (prefix2 ++ tiles2 ++ band_ts2 ++ suffix2) <> Lt).
  {
    rewrite Hschedule_compare in Hnew_not_lt.
    exact Hnew_not_lt.
  }
  assert (Hprefix_eq : prefix1 = prefix2).
  {
    unfold Tiling.PL.instr_point_ext_old_sched_lt in Hold.
    rewrite Hold_split1, Hold_split2 in Hold.
    repeat rewrite <- app_assoc in Hnew_expected_not_lt.
    eapply preserved_equal_length_prefix_reversal_implies_prefix_eq;
      eauto.
  }
  assert (Hband_len : List.length band_ts1 = List.length band_ts2).
  {
    subst band_ts1 band_ts2.
    rewrite Hband_rows1, Hband_rows2.
    unfold affine_product. rewrite !map_length.
    rewrite Hroot_size_len1, Hroot_size_len2, Hroot_sizes_eq.
    reflexivity.
  }
  assert (Htiles_eq : band_ts1 = band_ts2 -> tiles1 = tiles2).
  {
    intro Hband_eq_ts.
    subst tiles1 tiles2 band_ts1 band_ts2.
    eapply second_level_schedule_tile_block_by_layout_eq_common_sizes; eauto.
    rewrite <- Hband_rows1, <- Hband_rows2.
    exact Hband_eq_ts.
  }
  assert (Htiles_mono :
    listz_pointwise_le band_ts1 band_ts2 ->
    listz_pointwise_le tiles1 tiles2).
  {
    intro Hband_le.
    subst tiles1 tiles2 band_ts1 band_ts2.
    eapply
      second_level_schedule_tile_block_by_layout_pointwise_le_common_sizes;
      eauto.
    rewrite <- Hband_rows1, <- Hband_rows2.
    exact Hband_le.
  }
  unfold Tiling.PL.instr_point_ext_old_sched_lt in Hold.
  rewrite Hold_split1, Hold_split2 in Hold.
  destruct
    (stripmined_reversal_implies_decreasing_band_component
       prefix1 prefix2 tiles1 tiles2 band_ts1 band_ts2 suffix1 suffix2
       Hprefix_len Hband_len Htiles_eq Htiles_mono Hold Hnew_expected_not_lt)
    as [Hslice [dim [x [y [Hx [Hy Hgt]]]]]].
  assert (Hband_ts1_len : List.length band_ts1 = ptb_len band1).
  {
    subst band_ts1. rewrite Hband_rows1.
    unfold affine_product. rewrite List.map_length. lia.
  }
  assert (Hdim : (dim < ptb_len band1)%nat).
  {
    rewrite <- Hband_ts1_len.
    apply nth_error_Some. rewrite Hx. discriminate.
  }
  subst band2.
  exists band1.
  split; [reflexivity|].
  split; [reflexivity|].
  split.
  - unfold instr_point_ext_same_band_slice. exact Hslice.
  - exists dim, x, y.
    repeat split; try assumption.
    + eapply nth_error_band_block_to_full; eauto.
    + eapply nth_error_band_block_to_full; eauto.
Qed.

Lemma second_level_local_reversal_bridge_by_layout_wf_with_env_len :
  forall layout before_pis before_ctxt before_vars
         after_pis ws bands recipes envv,
    List.length before_ctxt = List.length envv ->
    infer_pinstr_list_second_level_bands before_pis ws =
      Some (bands, recipes) ->
    second_level_schedule_layout_lex_equivalent
      layout (List.length before_ctxt) before_pis after_pis bands ->
    common_second_level_recipe_sizes recipes ->
    common_band_start bands ->
    Tiling.tiling_rel_pprog_structure_source
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars)
      (List.map Tiling.compiled_pinstr_tiling_witness ws) ->
    Forall
      (Tiling.wf_statement_tiling_witness_with_param_dim
         (List.length before_ctxt))
      ws ->
    Forall
      (fun w => Forall (fun link => 0 < tl_tile_size link) (stw_links w))
      ws ->
    Forall2
      (fun before_pi w => stw_point_dim w = Tiling.PL.pi_depth before_pi)
      before_pis ws ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    forall ipl_ext tau1 tau2,
      Tiling.PL.flatten_instrs_ext
        envv
        (Tiling.compose_tiling_pinstrs_ext_from_after
           (List.length envv) before_pis after_pis ws)
        ipl_ext ->
      In tau1 ipl_ext ->
      In tau2 ipl_ext ->
      Tiling.PL.instr_point_ext_old_sched_lt tau1 tau2 ->
      Tiling.PL.instr_point_ext_new_sched_ge tau1 tau2 ->
      exists band,
        nth_error bands (Tiling.PL.ip_nth_ext tau1) = Some band /\
        nth_error bands (Tiling.PL.ip_nth_ext tau2) = Some band /\
        instr_point_ext_same_band_slice band tau1 tau2 /\
        instr_point_ext_band_component_decreases band tau1 tau2.
Proof.
  intros layout before_pis before_ctxt before_vars
         after_pis ws bands recipes envv
         Hlen_env Hinfer Hsched Hrecipe_sizes Hcommon
         Hprog Hwf_ws Hsizes_ws Hdepths Hwf_before
         ipl_ext tau1 tau2 Hflat Hin1 Hin2 Hold Hnew.
  eapply
    (second_level_pair_local_reversal_bridge_by_layout_wf_with_env_len
       layout before_pis before_ctxt before_vars
       after_pis ws bands recipes envv); eauto.
  - intros recipe1 recipe2 Hrecipe1 Hrecipe2.
    eapply common_second_level_recipe_sizes_nth_error_equal; eauto.
  - intros band1 band2 Hband1 Hband2.
    eapply common_band_start_nth_error_equal; eauto.
Qed.






Lemma tiling_sourceb_validate_correct_with_reordering :
  forall before after ws bands st1 st2,
    TilingCheck.check_pprog_tiling_sourceb before after ws = true ->
    (let '(before_pis, before_ctxt, _) := before in
     let '(after_pis, _, _) := after in
     forall envv,
       List.length before_ctxt = List.length envv ->
       pprog_tiling_reordering_safe envv before_pis after_pis ws bands) ->
    Tiling.PL.instance_list_semantics after st1 st2 ->
    exists st2',
      Tiling.PL.instance_list_semantics before st1 st2' /\
      TilingPolIRs.State.eq st2 st2'.
Proof.
  intros before after ws bands st1 st2 Hsource Hperm Hsem_after.
  destruct before as [[before_pis before_ctxt] before_vars].
  destruct after as [[after_pis after_ctxt] after_vars].
  simpl in *.
  pose proof
    (TilingCheck.check_pprog_tiling_sourceb_sound
       (before_pis, before_ctxt, before_vars)
       (after_pis, after_ctxt, after_vars) ws Hsource)
    as [Hprog [Hbefore_ids [Hwf [Hsizes Hdepths]]]].
  unfold Tiling.tiling_rel_pprog_structure_source in Hprog.
  simpl in Hprog.
  destruct Hprog as [Hctxt [Hvars Hrel]].
  subst after_ctxt after_vars.
  assert (Hprog_full :
    Tiling.tiling_rel_pprog_structure_source
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars)
      (List.map Tiling.compiled_pinstr_tiling_witness ws)).
  {
    unfold Tiling.tiling_rel_pprog_structure_source.
    simpl. repeat split; auto.
  }
  pose proof
    (Tiling.tiling_rel_pinstr_list_source_lengths
       (List.length before_ctxt) before_pis after_pis
       (List.map Tiling.compiled_pinstr_tiling_witness ws) Hrel)
    as [Hlen_after Hlen_ws_map].
  assert (Hlen_ws : List.length after_pis = List.length ws).
  { rewrite List.map_length in Hlen_ws_map. exact Hlen_ws_map. }
  inversion Hsem_after as
    [pprog pis varctxt vars envv st1' st2'
     Hpprog Hcompat Halias Hinit Hpoly];
    subst.
  pose proof Hpprog as Hpprog_eq.
  inversion Hpprog_eq; subst pis varctxt vars; clear Hpprog_eq Hpprog.
  pose proof (Instr.init_env_samelen before_ctxt envv st1 Hinit) as Hlen_env.
  assert (Hwf_env :
    Forall
      (Tiling.wf_statement_tiling_witness_with_param_dim (List.length envv))
      ws).
  { rewrite <- Hlen_env. exact Hwf. }
  assert (Hwits :
    Forall2 Tiling.after_matches_tiling_witness after_pis ws).
  {
    eapply
      (tiling_rel_pprog_structure_source_after_matches
         before_pis before_ctxt before_vars
         after_pis before_ctxt before_vars ws); eauto.
  }
  assert (Hlayer :
    Tiling.tiling_retiled_old_to_before_poly_layer
      envv before_pis after_pis ws before_ctxt before_vars).
  {
    intros stx stmid Hretiled.
    eapply Tiling.tiling_retiled_old_to_before_poly_correct_with_env_len_source.
    - exact Hprog_full.
    - symmetry. exact Hlen_env.
    - exact Hbefore_ids.
    - exact Hwf_env.
    - exact Hsizes.
    - exact Hdepths.
    - exact Hretiled.
  }
  destruct
    (Tiling.tiling_after_to_before_poly_correct_via_retiled_old
       envv before_pis after_pis ws before_ctxt before_vars st1 st2
       Hlen_after Hlen_ws Hwits (Hperm envv Hlen_env)
       Hlayer Halias Hpoly)
    as [st2' [Hpoly_before Heq]].
  exists st2'.
  split.
  - refine
      (Tiling.PL.PIPSemaIntro
         (before_pis, before_ctxt, before_vars)
         before_pis before_ctxt before_vars envv st1 st2'
         _ _ _ _ _).
    + reflexivity.
    + exact Hcompat.
    + exact Halias.
    + exact Hinit.
    + exact Hpoly_before.
  - exact Heq.
Qed.








(** * Direct checker soundness

    This chain turns successful direct bad-pair checks into the semantic
    componentwise permutable-band property used by the runtime route. *)

Lemma validate_instr_and_list_pluto_band_component_direct_true_pair :
  forall pi pis band dim env_size,
    mayReturn
      (validate_instr_and_list_pluto_band_component_direct
         pi pis band dim env_size)
      true ->
    forall pi',
      In pi' pis ->
      mayReturn
        (validate_two_instrs_pluto_band_component_direct
           pi pi' band dim env_size)
        true /\
      mayReturn
        (validate_two_instrs_pluto_band_component_direct
           pi' pi band dim env_size)
        true.
Proof.
  intros pi pis.
  induction pis as [|pi' pis IH];
    intros band dim env_size Hcheck target Hin.
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

Lemma validate_instr_list_pluto_band_component_direct_true_pair :
  forall pis band dim env_size,
    mayReturn
      (validate_instr_list_pluto_band_component_direct
         pis band dim env_size)
      true ->
    forall pi1 pi2,
      In pi1 pis ->
      In pi2 pis ->
      mayReturn
        (validate_two_instrs_pluto_band_component_direct
           pi1 pi2 band dim env_size)
        true.
Proof.
  intros pis.
  induction pis as [|pi pis IH];
    intros band dim env_size Hcheck pi1 pi2 Hin1 Hin2.
  - inversion Hin1.
  - simpl in Hcheck.
    bind_imp_destruct Hcheck self Hself.
    destruct self.
    + bind_imp_destruct Hcheck cross Hcross.
      destruct cross.
      * destruct Hin1 as [Heq1 | Hin1];
        destruct Hin2 as [Heq2 | Hin2].
        -- subst pi1 pi2. exact Hself.
        -- subst pi1.
           eapply
             (proj1
                (validate_instr_and_list_pluto_band_component_direct_true_pair
                   pi pis band dim env_size Hcross pi2 Hin2)).
        -- subst pi2.
           eapply
             (proj2
                (validate_instr_and_list_pluto_band_component_direct_true_pair
                   pi pis band dim env_size Hcross pi1 Hin1)).
        -- eapply IH; eauto.
      * apply mayReturn_pure in Hcheck. discriminate.
    + apply mayReturn_pure in Hcheck. discriminate.
Qed.

Lemma validate_instr_list_pluto_band_components_direct_from_true_component :
  forall pis band remaining start env_size,
    mayReturn
      (validate_instr_list_pluto_band_components_direct_from
         pis band remaining start env_size)
      true ->
    forall dim,
      (start <= dim < start + remaining)%nat ->
      mayReturn
        (validate_instr_list_pluto_band_component_direct
           pis band dim env_size)
        true.
Proof.
  intros pis band remaining.
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

Lemma HdRel_filter_trans_local :
  forall (A: Type) (R: A -> A -> Prop) (keep: A -> bool) xs,
    Relations_1.Transitive R ->
    Sorted R xs ->
    forall x,
      HdRel R x xs ->
      HdRel R x (filter keep xs).
Proof.
  intros A R keep xs Htrans Hsorted.
  induction Hsorted as [|head xs Hsorted IH Hhead].
  - intros x Hbefore. constructor.
  - intros x Hbefore.
    inversion Hbefore as [|? ? Hx_head]; subst.
    simpl.
    destruct (keep head) eqn:Hkeep.
    + constructor. exact Hx_head.
    + eapply IH.
      destruct xs as [|next rest].
      * constructor.
      * inversion Hhead as [|? ? Hhead_next]; subst.
        constructor.
        eapply Htrans; eauto.
Qed.

Lemma Sorted_filter_trans_local :
  forall (A: Type) (R: A -> A -> Prop) (keep: A -> bool) xs,
    Relations_1.Transitive R ->
    Sorted R xs ->
    Sorted R (filter keep xs).
Proof.
  intros A R keep xs Htrans Hsorted.
  induction Hsorted as [|x xs Hsorted IH Hhead].
  - constructor.
  - simpl.
    destruct (keep x) eqn:Hkeep.
    + constructor.
      * exact IH.
      * eapply HdRel_filter_trans_local; eauto.
    + exact IH.
Qed.

Lemma flatten_instrs_ext_member_slice_local :
  forall envv pis ipl ip pi,
    Tiling.PL.flatten_instrs_ext envv pis ipl ->
    In ip ipl ->
    nth_error pis (Tiling.PL.ip_nth_ext ip) = Some pi ->
    exists ipli,
      Tiling.PL.flatten_instr_nth_ext
        envv (Tiling.PL.ip_nth_ext ip) pi ipli /\
      In ip ipli.
Proof.
  intros envv pis ipl ip pi Hflat Hin Hnth.
  destruct Hflat as [Henv [Hmem [Hnodup Hsorted]]].
  exists
    (filter
       (fun candidate =>
          Nat.eqb
            (Tiling.PL.ip_nth_ext candidate)
            (Tiling.PL.ip_nth_ext ip))
       ipl).
  split.
  - split.
    + intros candidate Hcandidate.
      apply filter_In in Hcandidate.
      destruct Hcandidate as [Hcandidate _].
      eapply Henv; eauto.
    + split.
      * intros candidate.
        split; intro Hcandidate.
        -- apply filter_In in Hcandidate.
           destruct Hcandidate as [Hcandidate Hsame].
           apply Nat.eqb_eq in Hsame.
           apply Hmem in Hcandidate.
           destruct Hcandidate as
             [pi' [Hnth' [Hprefix [Hbelongs Hlength]]]].
           rewrite Hsame in Hnth'.
           rewrite Hnth in Hnth'.
           inversion Hnth'; subst pi'.
           split; [exact Hprefix|].
           split; [exact Hbelongs|].
           split; [exact Hsame|exact Hlength].
        -- destruct Hcandidate as
             [Hprefix [Hbelongs [Hsame Hlength]]].
           apply filter_In.
           split.
           ++ apply Hmem.
              exists pi.
              rewrite Hsame.
              split; [exact Hnth|].
              split; [exact Hprefix|].
              split; [exact Hbelongs|exact Hlength].
           ++ apply Nat.eqb_eq. exact Hsame.
      * split.
        -- eapply NoDup_filter; eauto.
        -- eapply Sorted_filter_trans_local; eauto.
           eapply Tiling.PL.np_lt_ext_trans.
  - apply filter_In.
    split; [exact Hin|].
    apply Nat.eqb_refl.
Qed.

Lemma validate_two_instrs_pluto_band_component_direct_sound :
  forall env envv nth1 nth2 pi1 pi2 ipl1 ipl2 band dim ip1 ip2,
    mayReturn
      (validate_two_instrs_pluto_band_component_direct
         pi1 pi2 band dim (List.length env))
      true ->
    Tiling.PL.wf_pinstr_ext_tiling env pi1 ->
    Tiling.PL.wf_pinstr_ext_tiling env pi2 ->
    List.length env = List.length envv ->
    Tiling.PL.flatten_instr_nth_ext envv nth1 pi1 ipl1 ->
    Tiling.PL.flatten_instr_nth_ext envv nth2 pi2 ipl2 ->
    In ip1 ipl1 ->
    In ip2 ipl2 ->
    Instr.valid_access_function
      (Tiling.PL.pi_waccess_ext pi1)
      (Tiling.PL.pi_raccess_ext pi1)
      (Tiling.PL.pi_instr_ext pi1) ->
    Instr.valid_access_function
      (Tiling.PL.pi_waccess_ext pi2)
      (Tiling.PL.pi_raccess_ext pi2)
      (Tiling.PL.pi_instr_ext pi2) ->
    Tiling.PL.instr_point_ext_old_sched_lt ip1 ip2 ->
    instr_point_ext_same_band_slice band ip1 ip2 ->
    instr_point_ext_band_component_decreases_at band dim ip1 ip2 ->
    Tiling.PL.Permutable_ext ip1 ip2.
Proof.
  intros env envv nth1 nth2 pi1 pi2 ipl1 ipl2 band dim ip1 ip2
         Hcheck Hwf1 Hwf2 Henv Hflat1 Hflat2 Hin1 Hin2
         Hvalid1 Hvalid2 Hold Hprefix Hcomponent.
  unfold validate_two_instrs_pluto_band_component_direct in Hcheck.
  destruct
    (make_pluto_band_component_guard_polys
       pi1 pi2 band dim (List.length env))
    as [[old_order bad_component]|] eqn:Hguards.
  - pose proof
      (make_pluto_band_component_guard_polys_point_sound
         env envv nth1 nth2 pi1 pi2 ipl1 ipl2 band dim
         old_order bad_component ip1 ip2 Hguards Hwf1 Hwf2 Henv
         Hflat1 Hflat2 Hin1 Hin2 Hold Hprefix Hcomponent)
      as [Horder Hbad].
    assert (Hcollision :
      BandAffine.no_write_collision
        (Tiling.PL.pi_waccess_ext pi1)
        (Tiling.PL.pi_waccess_ext pi2)
        (Tiling.PL.pi_raccess_ext pi1)
        (Tiling.PL.pi_raccess_ext pi2)
        ip1 ip2).
    {
      eapply
        (BandAffine.validate_two_instrs_under_guards_integer_implies_no_write_collision
           pi1 pi2 env nth1 nth2 envv ipl1 ipl2
           old_order bad_component true Hcheck eq_refl);
        eauto.
    }
    assert (Hinstr1 :
      Tiling.PL.ip_instruction_ext ip1 =
      Tiling.PL.pi_instr_ext pi1).
    {
      eapply Tiling.PL.expand_ip_instr_eq_pi_instr_ext; eauto.
    }
    assert (Hinstr2 :
      Tiling.PL.ip_instruction_ext ip2 =
      Tiling.PL.pi_instr_ext pi2).
    {
      eapply Tiling.PL.expand_ip_instr_eq_pi_instr_ext; eauto.
    }
    assert (Htf1 :
      Tiling.PL.ip_access_transformation_ext ip1 =
      Tiling.PL.ip_transformation_ext ip1).
    {
      assert (Haccess :
        Tiling.PL.ip_access_transformation_ext ip1 =
        Tiling.PL.pi_access_transformation_ext pi1).
      { eapply Tiling.PL.expand_ip_instr_eq_pi_access_tf_ext; eauto. }
      assert (Hcurrent :
        Tiling.PL.ip_transformation_ext ip1 =
        Tiling.PL.pi_transformation_ext pi1).
      { eapply Tiling.PL.expand_ip_instr_eq_pi_tf_ext; eauto. }
      destruct Hwf1 as [_ Hpi_eq].
      rewrite Haccess, Hcurrent, Hpi_eq.
      reflexivity.
    }
    assert (Htf2 :
      Tiling.PL.ip_access_transformation_ext ip2 =
      Tiling.PL.ip_transformation_ext ip2).
    {
      assert (Haccess :
        Tiling.PL.ip_access_transformation_ext ip2 =
        Tiling.PL.pi_access_transformation_ext pi2).
      { eapply Tiling.PL.expand_ip_instr_eq_pi_access_tf_ext; eauto. }
      assert (Hcurrent :
        Tiling.PL.ip_transformation_ext ip2 =
        Tiling.PL.pi_transformation_ext pi2).
      { eapply Tiling.PL.expand_ip_instr_eq_pi_tf_ext; eauto. }
      destruct Hwf2 as [_ Hpi_eq].
      rewrite Haccess, Hcurrent, Hpi_eq.
      reflexivity.
    }
    eapply BandAffine.no_write_collision_implies_permutable; eauto.
    + rewrite Hinstr1. exact Hvalid1.
    + rewrite Hinstr2. exact Hvalid2.
  - apply mayReturn_pure in Hcheck.
    discriminate.
Qed.

Lemma validate_instr_list_pluto_band_component_direct_sound :
  forall env envv pis band dim flat ip1 ip2,
    List.length env = List.length envv ->
    Forall (Tiling.PL.wf_pinstr_ext_tiling env) pis ->
    Forall
      (fun pi =>
         Instr.valid_access_function
           (Tiling.PL.pi_waccess_ext pi)
           (Tiling.PL.pi_raccess_ext pi)
           (Tiling.PL.pi_instr_ext pi))
      pis ->
    mayReturn
      (validate_instr_list_pluto_band_component_direct
         pis band dim (List.length env))
      true ->
    Tiling.PL.flatten_instrs_ext envv pis flat ->
    In ip1 flat ->
    In ip2 flat ->
    Tiling.PL.instr_point_ext_old_sched_lt ip1 ip2 ->
    instr_point_ext_same_band_slice band ip1 ip2 ->
    instr_point_ext_band_component_decreases_at band dim ip1 ip2 ->
    Tiling.PL.Permutable_ext ip1 ip2.
Proof.
  intros env envv pis band dim flat ip1 ip2 Henv Hwf Hvalid Hcheck
         Hflat Hin1 Hin2 Hold Hprefix Hcomponent.
  pose proof Hflat as Hflat_membership.
  destruct Hflat_membership as [_ [Hmem _]].
  apply Hmem in Hin1 as Hmember1.
  apply Hmem in Hin2 as Hmember2.
  destruct Hmember1 as
    [pi1 [Hnth1 [Henv1 [Hbelongs1 Hlen1]]]].
  destruct Hmember2 as
    [pi2 [Hnth2 [Henv2 [Hbelongs2 Hlen2]]]].
  assert (Hin_pi1 : In pi1 pis).
  { eapply nth_error_In; eauto. }
  assert (Hin_pi2 : In pi2 pis).
  { eapply nth_error_In; eauto. }
  destruct
    (flatten_instrs_ext_member_slice_local
       envv pis flat ip1 pi1 Hflat Hin1 Hnth1)
    as [slice1 [Hslice1 Hin_slice1]].
  destruct
    (flatten_instrs_ext_member_slice_local
       envv pis flat ip2 pi2 Hflat Hin2 Hnth2)
    as [slice2 [Hslice2 Hin_slice2]].
  assert (Hpair :
    mayReturn
      (validate_two_instrs_pluto_band_component_direct
         pi1 pi2 band dim (List.length env))
      true).
  {
    eapply validate_instr_list_pluto_band_component_direct_true_pair;
      eauto.
  }
  assert (Hwf1 : Tiling.PL.wf_pinstr_ext_tiling env pi1).
  {
    eapply Tiling.Forall_nth_error;
      eauto.
  }
  assert (Hwf2 : Tiling.PL.wf_pinstr_ext_tiling env pi2).
  {
    eapply Tiling.Forall_nth_error;
      eauto.
  }
  assert (Hvalid1 :
    Instr.valid_access_function
      (Tiling.PL.pi_waccess_ext pi1)
      (Tiling.PL.pi_raccess_ext pi1)
      (Tiling.PL.pi_instr_ext pi1)).
  {
    exact
      (Tiling.Forall_nth_error
         _
         (fun pi =>
            Instr.valid_access_function
              (Tiling.PL.pi_waccess_ext pi)
              (Tiling.PL.pi_raccess_ext pi)
              (Tiling.PL.pi_instr_ext pi))
         pis (Tiling.PL.ip_nth_ext ip1) pi1 Hvalid Hnth1).
  }
  assert (Hvalid2 :
    Instr.valid_access_function
      (Tiling.PL.pi_waccess_ext pi2)
      (Tiling.PL.pi_raccess_ext pi2)
      (Tiling.PL.pi_instr_ext pi2)).
  {
    exact
      (Tiling.Forall_nth_error
         _
         (fun pi =>
            Instr.valid_access_function
              (Tiling.PL.pi_waccess_ext pi)
              (Tiling.PL.pi_raccess_ext pi)
              (Tiling.PL.pi_instr_ext pi))
         pis (Tiling.PL.ip_nth_ext ip2) pi2 Hvalid Hnth2).
  }
  eapply
    (validate_two_instrs_pluto_band_component_direct_sound
       env envv
       (Tiling.PL.ip_nth_ext ip1)
       (Tiling.PL.ip_nth_ext ip2)
       pi1 pi2 slice1 slice2 band dim ip1 ip2);
    eauto.
Qed.

Lemma check_pinstr_list_pluto_permutable_band_direct_sound :
  forall env envv before_pis after_pis ws band,
    List.length env = List.length envv ->
    Forall
      (Tiling.PL.wf_pinstr_ext_tiling env)
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length env) before_pis after_pis ws) ->
    mayReturn
      (check_pinstr_list_pluto_permutable_band_direct
         (List.length env) before_pis after_pis ws band)
      true ->
    pprog_pluto_componentwise_permutable_band
      envv before_pis after_pis ws band.
Proof.
  intros env envv before_pis after_pis ws band Henv Hwf Hcheck.
  unfold check_pinstr_list_pluto_permutable_band_direct in Hcheck.
  bind_imp_destruct Hcheck components_ok Hcomponents.
  apply mayReturn_pure in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as [[_ Hcomponents_true] Hvalid_true].
  subst components_ok.
  set (pis :=
    Tiling.compose_tiling_pinstrs_ext_from_after
      (List.length env) before_pis after_pis ws).
  assert (Hvalid :
    Forall
      (fun pi =>
         Instr.valid_access_function
           (Tiling.PL.pi_waccess_ext pi)
           (Tiling.PL.pi_raccess_ext pi)
           (Tiling.PL.pi_instr_ext pi))
      pis).
  {
    unfold pis.
    eapply BandAffine.check_valid_access_correct.
    exact Hvalid_true.
  }
  unfold pprog_pluto_componentwise_permutable_band,
         pprog_pluto_permutable_band.
  intros flat ip1 ip2 Hflat Hin1 Hin2 Hold Hprefix Hdecreases.
  destruct Hdecreases as [dim Hcomponent].
  assert (Hcomponent_check :
    mayReturn
      (validate_instr_list_pluto_band_component_direct
         pis band dim (List.length env))
      true).
  {
    eapply
      validate_instr_list_pluto_band_components_direct_from_true_component.
    - exact Hcomponents.
    - destruct Hcomponent as
        [x [y [Hdim [Hx [Hy Hgt]]]]].
      lia.
  }
  assert (Hflat_env : Tiling.PL.flatten_instrs_ext envv pis flat).
  {
    unfold pis.
    rewrite Henv.
    exact Hflat.
  }
  eapply
    (validate_instr_list_pluto_band_component_direct_sound
       env envv pis band dim flat ip1 ip2);
    eauto.
Qed.

Lemma check_pprog_pluto_permutable_tiling_bands_direct_sound_with_env_len :
  forall before_pis before_ctxt before_vars after_pis ws bands envv,
    List.length before_ctxt = List.length envv ->
    infer_pinstr_list_tiling_bands before_pis ws = Some bands ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      after_pis ->
    Forall2
      (fun before_pi w => stw_point_dim w = Tiling.PL.pi_depth before_pi)
      before_pis ws ->
    Forall2 Tiling.after_matches_tiling_witness after_pis ws ->
    mayReturn
      (check_pprog_pluto_permutable_tiling_bands_direct
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars)
         ws bands)
      true ->
    pprog_pluto_permutable_tiling_bands_strong
      envv before_pis after_pis ws bands /\
    uniform_schedule_arity before_pis.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws bands envv
         Henv Hinfer Hwf_before Hwf_after Hdepths Hwits Hcheck.
  unfold check_pprog_pluto_permutable_tiling_bands_direct in Hcheck.
  assert (Hctxt_refl :
    TilingCheck.ctxt_eqb before_ctxt before_ctxt = true).
  {
    apply (proj2 (TilingCheck.ctxt_eqb_eq before_ctxt before_ctxt)).
    reflexivity.
  }
  assert (Hvars_refl :
    TilingCheck.ctxt_ty_eqb before_vars before_vars = true).
  { apply ctxt_ty_eqb_refl_local. }
  rewrite Hctxt_refl, Hvars_refl in Hcheck.
  destruct (infer_pinstr_list_tiling_bands_lengths _ _ _ Hinfer)
    as [_ Hlen_bands].
  rewrite <- Hlen_bands, Nat.eqb_refl in Hcheck.
  destruct (check_uniform_schedule_arityb before_pis) eqn:Huniform.
  2:{
    simpl in Hcheck.
    apply mayReturn_pure in Hcheck.
    discriminate.
  }
  destruct (infer_common_tiling_band bands) as [band|] eqn:Hcommon.
  2:{
    simpl in Hcheck.
    apply mayReturn_pure in Hcheck.
    discriminate.
  }
  destruct (check_common_tiling_band_recipeb ws) eqn:Hrecipe.
  2:{
    simpl in Hcheck.
    apply mayReturn_pure in Hcheck.
    discriminate.
  }
  simpl in Hcheck.
  split.
  - destruct (check_common_tiling_band_recipeb_sound _ Hrecipe)
      as [sizes Hrecipe_sound].
    exists band, sizes.
    split.
    + eapply infer_common_tiling_band_sound; exact Hcommon.
    + split.
      * exact Hrecipe_sound.
      * eapply
          (check_pinstr_list_pluto_permutable_band_direct_sound
             before_ctxt envv before_pis after_pis ws band);
          eauto.
        eapply compose_tiling_pinstrs_ext_from_after_wf_tiling; eauto.
  - eapply check_uniform_schedule_arityb_sound.
    exact Huniform.
Qed.

End CommonBandDirectChecker.

(** * Lifting component checks across statement lists *)

Section PerStatementBandChecker.

(** Direct componentwise checking for statement-specific bands.  The
    componentwise semantic property only relates instruction points whose
    statements have the same inferred band.  Pairs with distinct bands, and
    components outside that shared band, therefore introduce no obligation.
    The independent structural bridge proves that the endpoints of every
    relevant target reversal have the same inferred band. *)
Definition validate_two_instr_band_entries_component_direct
    (entry1 entry2: Tiling.PL.PolyInstr_ext * pinstr_tiling_band)
    (dim env_size: nat) : imp bool :=
  let '(pi1, band1) := entry1 in
  let '(pi2, band2) := entry2 in
  if pinstr_tiling_band_eqb band1 band2 then
    if Nat.ltb dim (ptb_len band1) then
      validate_two_instrs_pluto_band_component_direct
        pi1 pi2 band1 dim env_size
    else pure true
  else pure true.

Fixpoint validate_instr_band_entry_and_list_component_direct
    (entry: Tiling.PL.PolyInstr_ext * pinstr_tiling_band)
    (entries: list (Tiling.PL.PolyInstr_ext * pinstr_tiling_band))
    (dim env_size: nat) : imp bool :=
  match entries with
  | [] => pure true
  | entry' :: entries' =>
      BIND forward <-
        validate_two_instr_band_entries_component_direct
          entry entry' dim env_size -;
      if forward then
        BIND backward <-
          validate_two_instr_band_entries_component_direct
            entry' entry dim env_size -;
        if backward then
          validate_instr_band_entry_and_list_component_direct
            entry entries' dim env_size
        else pure false
      else pure false
  end.

Fixpoint validate_instr_band_entry_list_component_direct
    (entries: list (Tiling.PL.PolyInstr_ext * pinstr_tiling_band))
    (dim env_size: nat) : imp bool :=
  match entries with
  | [] => pure true
  | entry :: entries' =>
      BIND self <-
        validate_two_instr_band_entries_component_direct
          entry entry dim env_size -;
      if self then
        BIND cross <-
          validate_instr_band_entry_and_list_component_direct
            entry entries' dim env_size -;
        if cross then
          validate_instr_band_entry_list_component_direct
            entries' dim env_size
        else pure false
      else pure false
  end.

Fixpoint validate_instr_band_entry_list_components_direct_from
    (entries: list (Tiling.PL.PolyInstr_ext * pinstr_tiling_band))
    (remaining dim env_size: nat) : imp bool :=
  match remaining with
  | O => pure true
  | S remaining' =>
      BIND component_ok <-
        validate_instr_band_entry_list_component_direct
          entries dim env_size -;
      if component_ok then
        validate_instr_band_entry_list_components_direct_from
          entries remaining' (S dim) env_size
      else pure false
  end.

Definition check_pinstr_list_pluto_componentwise_permutable_bands_direct
    (env_size: nat)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (bands: list pinstr_tiling_band) : imp bool :=
  let pis :=
    Tiling.compose_tiling_pinstrs_ext_from_after
      env_size before_pis after_pis ws in
  let aligned :=
    Nat.eqb (List.length before_pis) (List.length after_pis) &&
    Nat.eqb (List.length before_pis) (List.length ws) &&
    Nat.eqb (List.length before_pis) (List.length pis) &&
    Nat.eqb (List.length before_pis) (List.length bands) in
  let valid_access := BandAffine.check_valid_access pis in
  let entries := combine pis bands in
  if aligned then
    BIND res <-
      validate_instr_band_entry_list_components_direct_from
        entries (max_tiling_band_len bands) O env_size -;
    pure (res && valid_access)
  else pure false.

Lemma validate_instr_band_entry_and_list_component_direct_true_pair :
  forall entry entries dim env_size,
    mayReturn
      (validate_instr_band_entry_and_list_component_direct
         entry entries dim env_size)
      true ->
    forall entry',
      In entry' entries ->
      mayReturn
        (validate_two_instr_band_entries_component_direct
           entry entry' dim env_size)
        true /\
      mayReturn
        (validate_two_instr_band_entries_component_direct
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

Lemma validate_instr_band_entry_list_component_direct_true_pair :
  forall entries dim env_size,
    mayReturn
      (validate_instr_band_entry_list_component_direct
         entries dim env_size)
      true ->
    forall entry1 entry2,
      In entry1 entries ->
      In entry2 entries ->
      mayReturn
        (validate_two_instr_band_entries_component_direct
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
                (validate_instr_band_entry_and_list_component_direct_true_pair
                   entry entries dim env_size Hcross entry2 Hin2)).
        -- subst entry2.
           eapply
             (proj2
                (validate_instr_band_entry_and_list_component_direct_true_pair
                   entry entries dim env_size Hcross entry1 Hin1)).
        -- eapply IH; eauto.
      * apply mayReturn_pure in Hcheck. discriminate.
    + apply mayReturn_pure in Hcheck. discriminate.
Qed.

Lemma validate_instr_band_entry_list_components_direct_from_true_component :
  forall entries remaining start env_size,
    mayReturn
      (validate_instr_band_entry_list_components_direct_from
         entries remaining start env_size)
      true ->
    forall dim,
      (start <= dim < start + remaining)%nat ->
      mayReturn
        (validate_instr_band_entry_list_component_direct
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

Lemma nth_error_combine_some_in_local :
  forall (A B: Type) (xs: list A) (ys: list B) n x y,
    nth_error xs n = Some x ->
    nth_error ys n = Some y ->
    In (x, y) (combine xs ys).
Proof.
  intros A B xs.
  induction xs as [|x0 xs IH]; intros ys n x y Hx Hy.
  - destruct n; discriminate.
  - destruct ys as [|y0 ys]; [destruct n; discriminate|].
    destruct n as [|n].
    + inversion Hx; inversion Hy; subst. simpl. auto.
    + simpl in Hx, Hy. simpl. right. eapply IH; eauto.
Qed.

Lemma pinstr_tiling_band_eqb_refl_local :
  forall band, pinstr_tiling_band_eqb band band = true.
Proof.
  intros [start len].
  unfold pinstr_tiling_band_eqb.
  simpl.
  rewrite !Nat.eqb_refl.
  reflexivity.
Qed.

Lemma check_pinstr_list_pluto_componentwise_permutable_bands_direct_sound :
  forall env envv before_pis after_pis ws bands,
    List.length env = List.length envv ->
    Forall
      (Tiling.PL.wf_pinstr_ext_tiling env)
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length env) before_pis after_pis ws) ->
    mayReturn
      (check_pinstr_list_pluto_componentwise_permutable_bands_direct
         (List.length env) before_pis after_pis ws bands)
      true ->
    pprog_pluto_componentwise_permutable_bands
      envv before_pis after_pis ws bands.
Proof.
  intros env envv before_pis after_pis ws bands Henv Hwf Hcheck.
  unfold check_pinstr_list_pluto_componentwise_permutable_bands_direct
    in Hcheck.
  destruct
    (Nat.eqb (List.length before_pis) (List.length after_pis) &&
     Nat.eqb (List.length before_pis) (List.length ws) &&
     Nat.eqb
       (List.length before_pis)
       (List.length
          (Tiling.compose_tiling_pinstrs_ext_from_after
             (List.length env) before_pis after_pis ws)) &&
     Nat.eqb (List.length before_pis) (List.length bands))
    eqn:Haligned.
  2:{ apply mayReturn_pure in Hcheck. discriminate. }
  bind_imp_destruct Hcheck components_ok Hcomponents.
  apply mayReturn_pure in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hcomponents_true Hvalid_true].
  subst components_ok.
  set (pis :=
    Tiling.compose_tiling_pinstrs_ext_from_after
      (List.length env) before_pis after_pis ws).
  assert (Hvalid :
    Forall
      (fun pi =>
         Instr.valid_access_function
           (Tiling.PL.pi_waccess_ext pi)
           (Tiling.PL.pi_raccess_ext pi)
           (Tiling.PL.pi_instr_ext pi))
      pis).
  {
    unfold pis.
    eapply BandAffine.check_valid_access_correct.
    exact Hvalid_true.
  }
  unfold pprog_pluto_componentwise_permutable_bands.
  intros flat ip1 ip2 band Hflat Hin1 Hin2 Hband1 Hband2
         Hold Hprefix Hdecreases.
  assert (Hflat_pis : Tiling.PL.flatten_instrs_ext envv pis flat).
  {
    unfold pis.
    rewrite Henv.
    exact Hflat.
  }
  pose proof Hflat_pis as Hflat_membership.
  destruct Hflat_membership as [_ [Hmem _]].
  apply Hmem in Hin1 as Hmember1.
  apply Hmem in Hin2 as Hmember2.
  destruct Hmember1 as
    [pi1 [Hnth1 [Henv1 [Hbelongs1 Hpoint_len1]]]].
  destruct Hmember2 as
    [pi2 [Hnth2 [Henv2 [Hbelongs2 Hpoint_len2]]]].
  assert (Hin_pi1 : In pi1 pis).
  { eapply nth_error_In; eauto. }
  assert (Hin_pi2 : In pi2 pis).
  { eapply nth_error_In; eauto. }
  destruct
    (flatten_instrs_ext_member_slice_local
       envv pis flat ip1 pi1 Hflat_pis Hin1 Hnth1)
    as [slice1 [Hslice1 Hin_slice1]].
  destruct
    (flatten_instrs_ext_member_slice_local
       envv pis flat ip2 pi2 Hflat_pis Hin2 Hnth2)
    as [slice2 [Hslice2 Hin_slice2]].
  destruct Hdecreases as [dim Hcomponent].
  destruct Hcomponent as [x [y [Hdim [Hx [Hy Hgt]]]]].
  assert (Hcomponent_check :
    mayReturn
      (validate_instr_band_entry_list_component_direct
         (combine pis bands) dim (List.length env))
      true).
  {
    eapply
      validate_instr_band_entry_list_components_direct_from_true_component.
    - exact Hcomponents.
    - split; [lia|].
      eapply Nat.lt_le_trans.
      + exact Hdim.
      + eapply max_tiling_band_len_ge_nth_error; exact Hband1.
  }
  assert (Hentry1 : In (pi1, band) (combine pis bands)).
  {
    eapply nth_error_combine_some_in_local; eauto.
  }
  assert (Hentry2 : In (pi2, band) (combine pis bands)).
  {
    eapply nth_error_combine_some_in_local; eauto.
  }
  assert (Hpair_entry :
    mayReturn
      (validate_two_instr_band_entries_component_direct
         (pi1, band) (pi2, band) dim (List.length env))
      true).
  {
    eapply validate_instr_band_entry_list_component_direct_true_pair;
      eauto.
  }
  unfold validate_two_instr_band_entries_component_direct in Hpair_entry.
  rewrite pinstr_tiling_band_eqb_refl_local in Hpair_entry.
  assert (Hdim_bool : Nat.ltb dim (ptb_len band) = true).
  { apply Nat.ltb_lt. exact Hdim. }
  rewrite Hdim_bool in Hpair_entry.
  assert (Hwf1 : Tiling.PL.wf_pinstr_ext_tiling env pi1).
  { eapply Tiling.Forall_nth_error; eauto. }
  assert (Hwf2 : Tiling.PL.wf_pinstr_ext_tiling env pi2).
  { eapply Tiling.Forall_nth_error; eauto. }
  assert (Hvalid1 :
    Instr.valid_access_function
      (Tiling.PL.pi_waccess_ext pi1)
      (Tiling.PL.pi_raccess_ext pi1)
      (Tiling.PL.pi_instr_ext pi1)).
  {
    exact
      (Tiling.Forall_nth_error
         _
         (fun pi =>
            Instr.valid_access_function
              (Tiling.PL.pi_waccess_ext pi)
              (Tiling.PL.pi_raccess_ext pi)
              (Tiling.PL.pi_instr_ext pi))
         pis (Tiling.PL.ip_nth_ext ip1) pi1 Hvalid Hnth1).
  }
  assert (Hvalid2 :
    Instr.valid_access_function
      (Tiling.PL.pi_waccess_ext pi2)
      (Tiling.PL.pi_raccess_ext pi2)
      (Tiling.PL.pi_instr_ext pi2)).
  {
    exact
      (Tiling.Forall_nth_error
         _
         (fun pi =>
            Instr.valid_access_function
              (Tiling.PL.pi_waccess_ext pi)
              (Tiling.PL.pi_raccess_ext pi)
              (Tiling.PL.pi_instr_ext pi))
         pis (Tiling.PL.ip_nth_ext ip2) pi2 Hvalid Hnth2).
  }
  eapply
    (validate_two_instrs_pluto_band_component_direct_sound
       env envv
       (Tiling.PL.ip_nth_ext ip1)
       (Tiling.PL.ip_nth_ext ip2)
       pi1 pi2 slice1 slice2 band dim ip1 ip2);
    eauto.
  exists x, y.
  repeat split; assumption.
Qed.

End PerStatementBandChecker.

(** * Semantic componentwise permutability kernel

    [pinstr_list_semantic_componentwise_permutable] is the representation-free
    property passed from the executable checker to layout reconstruction. *)

Section SemanticBandKernel.

(** A semantic band is represented by explicit affine rows reconstructed from
    the tiling witness.  Different statements may omit trailing global slots;
    an omitted slot denotes the constant-zero row. *)
Definition semantic_band_row
    (dom_dim dim: nat) (rows: Schedule) : list Z * Z :=
  match nth_error rows dim with
  | Some row => row
  | None => zero_schedule_row dom_dim
  end.

Definition semantic_band_value
    (dom_dim dim: nat) (rows: Schedule) (idx: list Z) : Z :=
  let row := semantic_band_row dom_dim dim rows in
  Linalg.dot_product (fst row) idx + snd row.

Definition make_semantic_band_component_guard_polys
    (pi1 pi2: Tiling.PL.PolyInstr_ext)
    (rows1 rows2: Schedule)
    (dim env_size: nat) : list polyhedron * list polyhedron :=
  let dom_dim1 := (env_size + Tiling.PL.pi_depth_ext pi1)%nat in
  let dom_dim2 := (env_size + Tiling.PL.pi_depth_ext pi2)%nat in
  let row1 := semantic_band_row dom_dim1 dim rows1 in
  let row2 := semantic_band_row dom_dim2 dim rows2 in
  let old_order :=
    make_poly_lt
      (Tiling.PL.pi_schedule1_ext pi1)
      (Tiling.PL.pi_schedule1_ext pi2)
      dom_dim1 dom_dim2 [] in
  let component_decreases := make_constr_gt row1 row2 in
  (old_order, [[component_decreases]]).

Definition validate_two_instrs_semantic_band_component_direct
    (pi1 pi2: Tiling.PL.PolyInstr_ext)
    (rows1 rows2: Schedule)
    (dim env_size: nat) : imp bool :=
  let '(old_order, bad_component) :=
    make_semantic_band_component_guard_polys
      pi1 pi2 rows1 rows2 dim env_size in
  BandAffine.validate_two_instrs_under_guards_integer
    pi1 pi2 env_size old_order bad_component.

Definition semantic_band_entry :=
  (Tiling.PL.PolyInstr_ext * Schedule)%type.

Fixpoint validate_semantic_band_entry_and_list_component_direct
    (entry: semantic_band_entry)
    (entries: list semantic_band_entry)
    (dim env_size: nat) : imp bool :=
  match entries with
  | [] => pure true
  | entry' :: entries' =>
      let '(pi, rows) := entry in
      let '(pi', rows') := entry' in
      BIND forward <-
        validate_two_instrs_semantic_band_component_direct
          pi pi' rows rows' dim env_size -;
      if forward then
        BIND backward <-
          validate_two_instrs_semantic_band_component_direct
            pi' pi rows' rows dim env_size -;
        if backward then
          validate_semantic_band_entry_and_list_component_direct
            entry entries' dim env_size
        else pure false
      else pure false
  end.

Fixpoint validate_semantic_band_entry_list_component_direct
    (entries: list semantic_band_entry)
    (dim env_size: nat) : imp bool :=
  match entries with
  | [] => pure true
  | entry :: entries' =>
      let '(pi, rows) := entry in
      BIND self <-
        validate_two_instrs_semantic_band_component_direct
          pi pi rows rows dim env_size -;
      if self then
        BIND cross <-
          validate_semantic_band_entry_and_list_component_direct
            entry entries' dim env_size -;
        if cross then
          validate_semantic_band_entry_list_component_direct
            entries' dim env_size
        else pure false
      else pure false
  end.

Fixpoint validate_semantic_band_entry_list_components_direct_from
    (entries: list semantic_band_entry)
    (remaining dim env_size: nat) : imp bool :=
  match remaining with
  | O => pure true
  | S remaining' =>
      BIND component_ok <-
        validate_semantic_band_entry_list_component_direct
          entries dim env_size -;
      if component_ok then
        validate_semantic_band_entry_list_components_direct_from
          entries remaining' (S dim) env_size
      else pure false
  end.

Fixpoint max_schedule_length (rows: list Schedule) : nat :=
  match rows with
  | [] => O
  | schedule :: rows' =>
      Nat.max (List.length schedule) (max_schedule_length rows')
  end.

Definition check_semantic_band_components_direct_aligned
    (pis: list Tiling.PL.PolyInstr_ext)
    (rows: list Schedule)
    (env_size: nat) : imp bool :=
  let valid_access := BandAffine.check_valid_access pis in
  BIND res <-
    validate_semantic_band_entry_list_components_direct_from
      (combine pis rows) (max_schedule_length rows) O env_size -;
  pure (res && valid_access).

Definition check_semantic_band_components_direct
    (pis: list Tiling.PL.PolyInstr_ext)
    (rows: list Schedule)
    (env_size: nat) : imp bool :=
  if Nat.eqb (List.length pis) (List.length rows)
  then check_semantic_band_components_direct_aligned pis rows env_size
  else pure false.

Lemma semantic_band_row_exact_cols :
  forall dom_dim dim rows,
    exact_listzzs_cols dom_dim rows ->
    List.length (fst (semantic_band_row dom_dim dim rows)) = dom_dim.
Proof.
  intros dom_dim dim rows Hcols.
  unfold semantic_band_row.
  destruct (nth_error rows dim) as [row|] eqn:Hrow.
  - destruct row as [coeffs c]. simpl.
    eapply Hcols.
    + eapply nth_error_In. exact Hrow.
    + reflexivity.
  - unfold zero_schedule_row. simpl. apply repeat_length.
Qed.

Lemma make_semantic_band_component_guard_polys_old_order_sound :
  forall pi1 pi2 rows1 rows2 dim env_size
         old_order bad_component p1 p2,
    make_semantic_band_component_guard_polys
      pi1 pi2 rows1 rows2 dim env_size =
      (old_order, bad_component) ->
    List.length p1 =
      (env_size + Tiling.PL.pi_depth_ext pi1)%nat ->
    List.length p2 =
      (env_size + Tiling.PL.pi_depth_ext pi2)%nat ->
    exact_listzzs_cols
      (env_size + Tiling.PL.pi_depth_ext pi1)%nat
      (Tiling.PL.pi_schedule1_ext pi1) ->
    lex_compare
      (affine_product (Tiling.PL.pi_schedule1_ext pi1) p1)
      (affine_product (Tiling.PL.pi_schedule1_ext pi2) p2) = Lt ->
    Exists
      (fun pol => in_poly (p1 ++ p2) pol = true)
      old_order.
Proof.
  intros pi1 pi2 rows1 rows2 dim env_size
         old_order bad_component p1 p2
         Hmake Hlen1 Hlen2 Hcols Hold.
  unfold make_semantic_band_component_guard_polys in Hmake.
  inversion Hmake; subst old_order bad_component; clear Hmake.
  eapply make_poly_lt_correct; eauto.
Qed.

Lemma make_semantic_band_component_guard_polys_bad_component_sound :
  forall pi1 pi2 rows1 rows2 dim env_size
         old_order bad_component p1 p2,
    make_semantic_band_component_guard_polys
      pi1 pi2 rows1 rows2 dim env_size =
      (old_order, bad_component) ->
    List.length p1 =
      (env_size + Tiling.PL.pi_depth_ext pi1)%nat ->
    List.length p2 =
      (env_size + Tiling.PL.pi_depth_ext pi2)%nat ->
    exact_listzzs_cols
      (env_size + Tiling.PL.pi_depth_ext pi1)%nat rows1 ->
    exact_listzzs_cols
      (env_size + Tiling.PL.pi_depth_ext pi2)%nat rows2 ->
    (semantic_band_value
       (env_size + Tiling.PL.pi_depth_ext pi1) dim rows1 p1 >
     semantic_band_value
       (env_size + Tiling.PL.pi_depth_ext pi2) dim rows2 p2)%Z ->
    Exists
      (fun pol => in_poly (p1 ++ p2) pol = true)
      bad_component.
Proof.
  intros pi1 pi2 rows1 rows2 dim env_size
         old_order bad_component p1 p2
         Hmake Hlen1 Hlen2 Hcols1 Hcols2 Hcomponent.
  unfold make_semantic_band_component_guard_polys in Hmake.
  inversion Hmake; subst old_order bad_component; clear Hmake.
  unfold semantic_band_value in Hcomponent.
  remember
    (semantic_band_row
       (env_size + Tiling.PL.pi_depth_ext pi1) dim rows1)
    as row1 eqn:Hrow1.
  remember
    (semantic_band_row
       (env_size + Tiling.PL.pi_depth_ext pi2) dim rows2)
    as row2 eqn:Hrow2.
  pose proof
    (semantic_band_row_exact_cols
       (env_size + Tiling.PL.pi_depth_ext pi1) dim rows1 Hcols1)
    as Hrow1_cols.
  rewrite <- Hrow1 in Hrow1_cols.
  destruct row1 as [v1 c1], row2 as [v2 c2].
  simpl in Hcomponent.
  assert (Hv1 :
    List.length v1 =
      (env_size + Tiling.PL.pi_depth_ext pi1)%nat).
  {
    exact Hrow1_cols.
  }
  assert (Hcomponent_poly :
    satisfies_constraint
      (p1 ++ p2)
      (make_constr_gt (v1, c1) (v2, c2)) = true).
  {
    apply
      (proj2
         (make_constr_gt_correct p1 p2 v1 v2 c1 c2
            (eq_trans Hlen1 (eq_sym Hv1)))).
    exact Hcomponent.
  }
  apply Exists_cons_hd.
  change
    (satisfies_constraint
       (p1 ++ p2) (make_constr_gt (v1, c1) (v2, c2)) &&
     true = true).
  rewrite Hcomponent_poly.
  reflexivity.
Qed.

Lemma validate_two_instrs_semantic_band_component_direct_sound :
  forall env envv nth1 nth2 pi1 pi2 ipl1 ipl2 rows1 rows2 dim ip1 ip2,
    mayReturn
      (validate_two_instrs_semantic_band_component_direct
         pi1 pi2 rows1 rows2 dim (List.length env))
      true ->
    Tiling.PL.wf_pinstr_ext_tiling env pi1 ->
    Tiling.PL.wf_pinstr_ext_tiling env pi2 ->
    exact_listzzs_cols
      (List.length env + Tiling.PL.pi_depth_ext pi1)%nat rows1 ->
    exact_listzzs_cols
      (List.length env + Tiling.PL.pi_depth_ext pi2)%nat rows2 ->
    List.length env = List.length envv ->
    Tiling.PL.flatten_instr_nth_ext envv nth1 pi1 ipl1 ->
    Tiling.PL.flatten_instr_nth_ext envv nth2 pi2 ipl2 ->
    In ip1 ipl1 ->
    In ip2 ipl2 ->
    Instr.valid_access_function
      (Tiling.PL.pi_waccess_ext pi1)
      (Tiling.PL.pi_raccess_ext pi1)
      (Tiling.PL.pi_instr_ext pi1) ->
    Instr.valid_access_function
      (Tiling.PL.pi_waccess_ext pi2)
      (Tiling.PL.pi_raccess_ext pi2)
      (Tiling.PL.pi_instr_ext pi2) ->
    Tiling.PL.instr_point_ext_old_sched_lt ip1 ip2 ->
    (semantic_band_value
       (List.length env + Tiling.PL.pi_depth_ext pi1)
       dim rows1 (Tiling.PL.ip_index_ext ip1) >
     semantic_band_value
       (List.length env + Tiling.PL.pi_depth_ext pi2)
       dim rows2 (Tiling.PL.ip_index_ext ip2))%Z ->
    Tiling.PL.Permutable_ext ip1 ip2.
Proof.
  intros env envv nth1 nth2 pi1 pi2 ipl1 ipl2 rows1 rows2 dim ip1 ip2
         Hcheck Hwf1 Hwf2 Hrows1 Hrows2 Henv Hflat1 Hflat2 Hin1 Hin2
         Hvalid1 Hvalid2 Hold Hcomponent.
  unfold validate_two_instrs_semantic_band_component_direct in Hcheck.
  destruct
    (make_semantic_band_component_guard_polys
       pi1 pi2 rows1 rows2 dim (List.length env))
    as [old_order bad_component] eqn:Hguards.
  pose proof
    (Tiling.PL.expand_ts1_eq_sched_index_product_ext
       envv nth1 pi1 ipl1 ip1 Hflat1 Hin1) as Hts1.
  pose proof
    (Tiling.PL.expand_ts1_eq_sched_index_product_ext
       envv nth2 pi2 ipl2 ip2 Hflat2 Hin2) as Hts2.
  assert (Hidx1 :
    List.length (Tiling.PL.ip_index_ext ip1) =
      (List.length env + Tiling.PL.pi_depth_ext pi1)%nat).
  {
    rewrite Henv.
    eapply Tiling.PL.ip_index_size_eq_pi_dom_size_ext; eauto.
  }
  assert (Hidx2 :
    List.length (Tiling.PL.ip_index_ext ip2) =
      (List.length env + Tiling.PL.pi_depth_ext pi2)%nat).
  {
    rewrite Henv.
    eapply Tiling.PL.ip_index_size_eq_pi_dom_size_ext; eauto.
  }
  assert (Hcols1 :
    exact_listzzs_cols
      (List.length env + Tiling.PL.pi_depth_ext pi1)%nat
      (Tiling.PL.pi_schedule1_ext pi1)).
  {
    exact (wf_pinstr_ext_tiling_schedule1_exact_cols env pi1 Hwf1).
  }
  assert (Horder :
    Exists
      (fun pol =>
         in_poly
           (Tiling.PL.ip_index_ext ip1 ++ Tiling.PL.ip_index_ext ip2)
           pol = true)
      old_order).
  {
    eapply make_semantic_band_component_guard_polys_old_order_sound;
      eauto.
    unfold Tiling.PL.instr_point_ext_old_sched_lt in Hold.
    rewrite Hts1, Hts2 in Hold.
    exact Hold.
  }
  assert (Hbad :
    Exists
      (fun pol =>
         in_poly
           (Tiling.PL.ip_index_ext ip1 ++ Tiling.PL.ip_index_ext ip2)
           pol = true)
      bad_component).
  {
    eapply make_semantic_band_component_guard_polys_bad_component_sound;
      eauto.
  }
  assert (Hcollision :
    BandAffine.no_write_collision
      (Tiling.PL.pi_waccess_ext pi1)
      (Tiling.PL.pi_waccess_ext pi2)
      (Tiling.PL.pi_raccess_ext pi1)
      (Tiling.PL.pi_raccess_ext pi2)
      ip1 ip2).
  {
    eapply
      (BandAffine.validate_two_instrs_under_guards_integer_implies_no_write_collision
         pi1 pi2 env nth1 nth2 envv ipl1 ipl2
         old_order bad_component true Hcheck eq_refl);
      eauto.
  }
  assert (Hinstr1 :
    Tiling.PL.ip_instruction_ext ip1 =
    Tiling.PL.pi_instr_ext pi1).
  { eapply Tiling.PL.expand_ip_instr_eq_pi_instr_ext; eauto. }
  assert (Hinstr2 :
    Tiling.PL.ip_instruction_ext ip2 =
    Tiling.PL.pi_instr_ext pi2).
  { eapply Tiling.PL.expand_ip_instr_eq_pi_instr_ext; eauto. }
  assert (Htf1 :
    Tiling.PL.ip_access_transformation_ext ip1 =
    Tiling.PL.ip_transformation_ext ip1).
  {
    assert (Haccess :
      Tiling.PL.ip_access_transformation_ext ip1 =
      Tiling.PL.pi_access_transformation_ext pi1).
    { eapply Tiling.PL.expand_ip_instr_eq_pi_access_tf_ext; eauto. }
    assert (Hcurrent :
      Tiling.PL.ip_transformation_ext ip1 =
      Tiling.PL.pi_transformation_ext pi1).
    { eapply Tiling.PL.expand_ip_instr_eq_pi_tf_ext; eauto. }
    destruct Hwf1 as [_ Hpi_eq].
    rewrite Haccess, Hcurrent, Hpi_eq.
    reflexivity.
  }
  assert (Htf2 :
    Tiling.PL.ip_access_transformation_ext ip2 =
    Tiling.PL.ip_transformation_ext ip2).
  {
    assert (Haccess :
      Tiling.PL.ip_access_transformation_ext ip2 =
      Tiling.PL.pi_access_transformation_ext pi2).
    { eapply Tiling.PL.expand_ip_instr_eq_pi_access_tf_ext; eauto. }
    assert (Hcurrent :
      Tiling.PL.ip_transformation_ext ip2 =
      Tiling.PL.pi_transformation_ext pi2).
    { eapply Tiling.PL.expand_ip_instr_eq_pi_tf_ext; eauto. }
    destruct Hwf2 as [_ Hpi_eq].
    rewrite Haccess, Hcurrent, Hpi_eq.
    reflexivity.
  }
  eapply BandAffine.no_write_collision_implies_permutable; eauto.
  - rewrite Hinstr1. exact Hvalid1.
  - rewrite Hinstr2. exact Hvalid2.
Qed.

Lemma validate_semantic_band_entry_and_list_component_direct_true_pair :
  forall entry entries dim env_size,
    mayReturn
      (validate_semantic_band_entry_and_list_component_direct
         entry entries dim env_size)
      true ->
    forall entry',
      In entry' entries ->
      mayReturn
        (let '(pi, rows) := entry in
         let '(pi', rows') := entry' in
         validate_two_instrs_semantic_band_component_direct
           pi pi' rows rows' dim env_size)
        true /\
      mayReturn
        (let '(pi, rows) := entry in
         let '(pi', rows') := entry' in
         validate_two_instrs_semantic_band_component_direct
           pi' pi rows' rows dim env_size)
        true.
Proof.
  intros entry entries.
  induction entries as [|entry' entries IH];
    intros dim env_size Hcheck target Hin.
  - inversion Hin.
  - simpl in Hcheck.
    destruct entry as [pi rows].
    destruct entry' as [pi' rows'].
    simpl in Hcheck.
    bind_imp_destruct Hcheck forward Hforward.
    destruct forward.
    + bind_imp_destruct Hcheck backward Hbackward.
      destruct backward.
      * destruct Hin as [Heq | Hin].
        -- inversion Heq; subst target. simpl. split; assumption.
        -- eapply IH; eauto.
      * apply mayReturn_pure in Hcheck. discriminate.
    + apply mayReturn_pure in Hcheck. discriminate.
Qed.

Lemma validate_semantic_band_entry_list_component_direct_true_pair :
  forall entries dim env_size,
    mayReturn
      (validate_semantic_band_entry_list_component_direct
         entries dim env_size)
      true ->
    forall entry1 entry2,
      In entry1 entries ->
      In entry2 entries ->
      mayReturn
        (let '(pi1, rows1) := entry1 in
         let '(pi2, rows2) := entry2 in
         validate_two_instrs_semantic_band_component_direct
           pi1 pi2 rows1 rows2 dim env_size)
        true.
Proof.
  intros entries.
  induction entries as [|entry entries IH];
    intros dim env_size Hcheck entry1 entry2 Hin1 Hin2.
  - inversion Hin1.
  - simpl in Hcheck.
    destruct entry as [pi rows].
    simpl in Hcheck.
    bind_imp_destruct Hcheck self Hself.
    destruct self.
    + bind_imp_destruct Hcheck cross Hcross.
      destruct cross.
      * destruct Hin1 as [Heq1 | Hin1];
        destruct Hin2 as [Heq2 | Hin2].
        -- inversion Heq1; inversion Heq2; subst. simpl. exact Hself.
        -- subst entry1.
           eapply
             (proj1
                (validate_semantic_band_entry_and_list_component_direct_true_pair
                   (pi, rows) entries dim env_size Hcross entry2 Hin2)).
        -- subst entry2.
           eapply
             (proj2
                (validate_semantic_band_entry_and_list_component_direct_true_pair
                   (pi, rows) entries dim env_size Hcross entry1 Hin1)).
        -- eapply IH; eauto.
      * apply mayReturn_pure in Hcheck. discriminate.
    + apply mayReturn_pure in Hcheck. discriminate.
Qed.

Lemma validate_semantic_band_entry_list_components_direct_from_true_component :
  forall entries remaining start env_size,
    mayReturn
      (validate_semantic_band_entry_list_components_direct_from
         entries remaining start env_size)
      true ->
    forall dim,
      (start <= dim < start + remaining)%nat ->
      mayReturn
        (validate_semantic_band_entry_list_component_direct
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

Lemma max_schedule_length_ge_nth_error :
  forall schedules n schedule,
    nth_error schedules n = Some schedule ->
    (List.length schedule <= max_schedule_length schedules)%nat.
Proof.
  intros schedules.
  induction schedules as [|schedule0 schedules IH];
    intros n schedule Hnth.
  - destruct n; discriminate.
  - destruct n as [|n].
    + inversion Hnth; subst schedule.
      simpl. apply Nat.le_max_l.
    + simpl in Hnth.
      simpl.
      eapply Nat.le_trans.
      * eapply IH. exact Hnth.
      * apply Nat.le_max_r.
Qed.

Definition pinstr_list_semantic_componentwise_permutable
    (envv: list Z)
    (pis: list Tiling.PL.PolyInstr_ext)
    (rows: list Schedule) : Prop :=
  forall flat ip1 ip2 pi1 pi2 rows1 rows2 dim,
    Tiling.PL.flatten_instrs_ext envv pis flat ->
    In ip1 flat ->
    In ip2 flat ->
    nth_error pis (Tiling.PL.ip_nth_ext ip1) = Some pi1 ->
    nth_error pis (Tiling.PL.ip_nth_ext ip2) = Some pi2 ->
    nth_error rows (Tiling.PL.ip_nth_ext ip1) = Some rows1 ->
    nth_error rows (Tiling.PL.ip_nth_ext ip2) = Some rows2 ->
    (dim < max_schedule_length rows)%nat ->
    Tiling.PL.instr_point_ext_old_sched_lt ip1 ip2 ->
    (semantic_band_value
       (List.length envv + Tiling.PL.pi_depth_ext pi1)
       dim rows1 (Tiling.PL.ip_index_ext ip1) >
     semantic_band_value
       (List.length envv + Tiling.PL.pi_depth_ext pi2)
       dim rows2 (Tiling.PL.ip_index_ext ip2))%Z ->
    Tiling.PL.Permutable_ext ip1 ip2.

Lemma check_semantic_band_components_direct_sound :
  forall env envv pis rows,
    List.length env = List.length envv ->
    Forall (Tiling.PL.wf_pinstr_ext_tiling env) pis ->
    Forall2
      (fun pi schedule =>
         exact_listzzs_cols
           (List.length env + Tiling.PL.pi_depth_ext pi)%nat
           schedule)
      pis rows ->
    mayReturn
      (check_semantic_band_components_direct pis rows (List.length env))
      true ->
    pinstr_list_semantic_componentwise_permutable envv pis rows.
Proof.
  intros env envv pis rows Henv Hwf Hrows_cols Hcheck.
  assert (Haligned :
    Nat.eqb (List.length pis) (List.length rows) = true).
  {
    apply Nat.eqb_eq.
    eapply Forall2_length.
    exact Hrows_cols.
  }
  assert (Hchecker_eq :
    check_semantic_band_components_direct pis rows (List.length env) =
    check_semantic_band_components_direct_aligned
      pis rows (List.length env)).
  {
    change
      ((if Nat.eqb (List.length pis) (List.length rows)
        then check_semantic_band_components_direct_aligned
               pis rows (List.length env)
        else pure false) =
       check_semantic_band_components_direct_aligned
         pis rows (List.length env)).
    rewrite Haligned.
    reflexivity.
  }
  rewrite Hchecker_eq in Hcheck.
  unfold check_semantic_band_components_direct_aligned in Hcheck.
  bind_imp_destruct Hcheck components_ok Hcomponents.
  apply mayReturn_pure in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hcomponents_true Hvalid_true].
  subst components_ok.
  assert (Hvalid :
    Forall
      (fun pi =>
         Instr.valid_access_function
           (Tiling.PL.pi_waccess_ext pi)
           (Tiling.PL.pi_raccess_ext pi)
           (Tiling.PL.pi_instr_ext pi))
      pis).
  {
    eapply BandAffine.check_valid_access_correct.
    exact Hvalid_true.
  }
  unfold pinstr_list_semantic_componentwise_permutable.
  intros flat ip1 ip2 pi1 pi2 rows1 rows2 dim
         Hflat Hin1 Hin2 Hnth1 Hnth2 Hrows1 Hrows2
         Hdim Hold Hcomponent.
  destruct
    (flatten_instrs_ext_member_slice_local
       envv pis flat ip1 pi1 Hflat Hin1 Hnth1)
    as [slice1 [Hslice1 Hin_slice1]].
  destruct
    (flatten_instrs_ext_member_slice_local
       envv pis flat ip2 pi2 Hflat Hin2 Hnth2)
    as [slice2 [Hslice2 Hin_slice2]].
  assert (Hcomponent_check :
    mayReturn
      (validate_semantic_band_entry_list_component_direct
         (combine pis rows) dim (List.length env))
      true).
  {
    eapply
      validate_semantic_band_entry_list_components_direct_from_true_component.
    - exact Hcomponents.
    - lia.
  }
  assert (Hentry1 : In (pi1, rows1) (combine pis rows)).
  { eapply nth_error_combine_some_in_local; eauto. }
  assert (Hentry2 : In (pi2, rows2) (combine pis rows)).
  { eapply nth_error_combine_some_in_local; eauto. }
  assert (Hpair_check :
    mayReturn
      (validate_two_instrs_semantic_band_component_direct
         pi1 pi2 rows1 rows2 dim (List.length env))
      true).
  {
    exact
      (validate_semantic_band_entry_list_component_direct_true_pair
         (combine pis rows) dim (List.length env) Hcomponent_check
         (pi1, rows1) (pi2, rows2) Hentry1 Hentry2).
  }
  assert (Hwf1 : Tiling.PL.wf_pinstr_ext_tiling env pi1).
  { eapply Tiling.Forall_nth_error; eauto. }
  assert (Hwf2 : Tiling.PL.wf_pinstr_ext_tiling env pi2).
  { eapply Tiling.Forall_nth_error; eauto. }
  assert (Hrows_cols1 :
    exact_listzzs_cols
      (List.length env + Tiling.PL.pi_depth_ext pi1)%nat rows1).
  {
    exact
      (Tiling.Forall2_nth_error
         _ _
         (fun pi schedule =>
            exact_listzzs_cols
              (List.length env + Tiling.PL.pi_depth_ext pi)%nat
              schedule)
         pis rows (Tiling.PL.ip_nth_ext ip1) pi1 rows1
         Hrows_cols Hnth1 Hrows1).
  }
  assert (Hrows_cols2 :
    exact_listzzs_cols
      (List.length env + Tiling.PL.pi_depth_ext pi2)%nat rows2).
  {
    exact
      (Tiling.Forall2_nth_error
         _ _
         (fun pi schedule =>
            exact_listzzs_cols
              (List.length env + Tiling.PL.pi_depth_ext pi)%nat
              schedule)
         pis rows (Tiling.PL.ip_nth_ext ip2) pi2 rows2
         Hrows_cols Hnth2 Hrows2).
  }
  assert (Hvalid1 :
    Instr.valid_access_function
      (Tiling.PL.pi_waccess_ext pi1)
      (Tiling.PL.pi_raccess_ext pi1)
      (Tiling.PL.pi_instr_ext pi1)).
  {
    exact
      (Tiling.Forall_nth_error
         _
         (fun pi =>
            Instr.valid_access_function
              (Tiling.PL.pi_waccess_ext pi)
              (Tiling.PL.pi_raccess_ext pi)
              (Tiling.PL.pi_instr_ext pi))
         pis (Tiling.PL.ip_nth_ext ip1) pi1 Hvalid Hnth1).
  }
  assert (Hvalid2 :
    Instr.valid_access_function
      (Tiling.PL.pi_waccess_ext pi2)
      (Tiling.PL.pi_raccess_ext pi2)
      (Tiling.PL.pi_instr_ext pi2)).
  {
    exact
      (Tiling.Forall_nth_error
         _
         (fun pi =>
            Instr.valid_access_function
              (Tiling.PL.pi_waccess_ext pi)
              (Tiling.PL.pi_raccess_ext pi)
              (Tiling.PL.pi_instr_ext pi))
         pis (Tiling.PL.ip_nth_ext ip2) pi2 Hvalid Hnth2).
  }
  assert (Hcomponent_env :
    (semantic_band_value
       (List.length env + Tiling.PL.pi_depth_ext pi1)
       dim rows1 (Tiling.PL.ip_index_ext ip1) >
     semantic_band_value
       (List.length env + Tiling.PL.pi_depth_ext pi2)
       dim rows2 (Tiling.PL.ip_index_ext ip2))%Z).
  {
    rewrite Henv.
    exact Hcomponent.
  }
  eapply
    (validate_two_instrs_semantic_band_component_direct_sound
       env envv
       (Tiling.PL.ip_nth_ext ip1)
       (Tiling.PL.ip_nth_ext ip2)
       pi1 pi2 slice1 slice2 rows1 rows2 dim ip1 ip2);
    eauto.
Qed.

End SemanticBandKernel.

(** * Program-wide layout bridges and ordinary correctness endpoint

    The central implication is
    [semantic_componentwise_permutable_implies_reordering_safe]; the ordinary
    checked endpoint is
    [checked_tiling_sourceb_semantic_band_direct_correct_same_ctxt]. *)

Section ProgramWideSemanticReconstruction.

(** Program-wide reconstruction for source-like and mixed-depth tiling.
    Slots are removed only when every statement has a strict zero row there.
    This preserves cross-statement schedule coordinates. *)
Definition listz_prefixb (xs ys: list Z) : bool :=
  Nat.leb (List.length xs) (List.length ys) &&
  listz_strict_eqb xs (firstn (List.length xs) ys).

Definition merge_prefix_sizes
    (xs ys: list Z) : option (list Z) :=
  if listz_prefixb xs ys then Some ys
  else if listz_prefixb ys xs then Some xs
       else None.

Fixpoint infer_global_prefix_sizes
    (sizes: list (list Z)) : option (list Z) :=
  match sizes with
  | [] => Some []
  | sizes0 :: sizes' =>
      match infer_global_prefix_sizes sizes' with
      | Some global => merge_prefix_sizes sizes0 global
      | None => None
      end
  end.

Fixpoint parse_ordinary_semantic_data
    (ws: list statement_tiling_witness)
    : option (list (Schedule * list Z)) :=
  match ws with
  | [] => Some []
  | w :: ws' =>
      match schedule_rows_of_links w,
            parse_ordinary_semantic_data ws' with
      | Some rows, Some rest =>
          Some ((rows, tile_sizes_of_witness w) :: rest)
      | _, _ => None
      end
  end.

Fixpoint parse_second_level_semantic_recipes
    (ws: list statement_tiling_witness)
    : option (list second_level_band_recipe) :=
  match ws with
  | [] => Some []
  | w :: ws' =>
      match second_level_band_recipe_of_witness w,
            parse_second_level_semantic_recipes ws' with
      | Some recipe, Some rest => Some (recipe :: rest)
      | _, _ => None
      end
  end.

Fixpoint select_by_mask {A: Type}
    (mask: list bool) (xs: list A) : list A :=
  match mask, xs with
  | keep :: mask', x :: xs' =>
      if keep
      then x :: select_by_mask mask' xs'
      else select_by_mask mask' xs'
  | _, _ => []
  end.

Definition semantic_schedule_slot_zerob
    (slot: nat) (raw_schedules: list Schedule) : bool :=
  forallb
    (fun rows =>
       match nth_error rows slot with
       | Some row => Tiling.PL.affine_function_is_zero row
       | None => true
       end)
    raw_schedules.

Definition global_semantic_schedule_mask
    (raw_schedules: list Schedule) : list bool :=
  List.map
    (fun slot => negb (semantic_schedule_slot_zerob slot raw_schedules))
    (List.seq O (max_schedule_length raw_schedules)).

Definition compact_semantic_schedule
    (dom_dim: nat) (mask: list bool) (raw: Schedule) : Schedule :=
  select_by_mask mask
    (Tiling.PL.pad_schedule_to_len dom_dim (List.length mask) raw).

Fixpoint compact_semantic_schedules
    (env_size: nat)
    (before_pis: list Tiling.PL.PolyInstr)
    (raw_schedules: list Schedule)
    (mask: list bool) : option (list Schedule) :=
  match before_pis, raw_schedules with
  | [], [] => Some []
  | before_pi :: before_pis', raw :: raw_schedules' =>
      match
        compact_semantic_schedules
          env_size before_pis' raw_schedules' mask
      with
      | Some rest =>
          Some
            (compact_semantic_schedule
               (env_size + Tiling.PL.pi_depth before_pi)%nat
               mask raw :: rest)
      | None => None
      end
  | _, _ => None
  end.

Fixpoint lift_semantic_schedules_for_tiling
    (env_size: nat)
    (ws: list statement_tiling_witness)
    (semantic_rows: list Schedule) : option (list Schedule) :=
  match ws, semantic_rows with
  | [], [] => Some []
  | w :: ws', rows :: semantic_rows' =>
      match
        lift_semantic_schedules_for_tiling
          env_size ws' semantic_rows'
      with
      | Some rest =>
          Some
            (Tiling.lift_schedule_after_env
               (List.length (stw_links w)) env_size rows :: rest)
      | None => None
      end
  | _, _ => None
  end.

Definition semantic_ordinary_target_schedule
    (env_size global_width: nat)
    (semantic_rows: Schedule)
    (w: statement_tiling_witness) : Schedule :=
  let local_width := List.length (stw_links w) in
  let total_cols := (env_size + local_width + stw_point_dim w)%nat in
  Tiling.identity_affine_rows_from total_cols env_size local_width ++
  repeat (zero_schedule_row total_cols) (global_width - local_width) ++
  Tiling.lift_schedule_after_env local_width env_size semantic_rows.

Definition semantic_second_level_grouped_target_schedule
    (env_size global_width: nat)
    (semantic_rows: Schedule)
    (w: statement_tiling_witness)
    (recipe: second_level_band_recipe) : Schedule :=
  let local_width := List.length (slbr_root_rows recipe) in
  let added_dims := (2 * local_width)%nat in
  let total_cols := (env_size + added_dims + stw_point_dim w)%nat in
  identity_affine_rows_at
    total_cols env_size (second_level_child_positions local_width) ++
  repeat (zero_schedule_row total_cols) (global_width - local_width) ++
  identity_affine_rows_at
    total_cols env_size (second_level_root_positions local_width) ++
  repeat (zero_schedule_row total_cols) (global_width - local_width) ++
  Tiling.lift_schedule_after_env added_dims env_size semantic_rows.

Definition semantic_second_level_interleaved_target_schedule
    (env_size global_width: nat)
    (semantic_rows: Schedule)
    (w: statement_tiling_witness)
    (recipe: second_level_band_recipe) : Schedule :=
  let local_width := List.length (slbr_root_rows recipe) in
  let added_dims := (2 * local_width)%nat in
  let total_cols := (env_size + added_dims + stw_point_dim w)%nat in
  Tiling.identity_affine_rows_from total_cols env_size added_dims ++
  repeat (zero_schedule_row total_cols)
    (2 * (global_width - local_width)) ++
  Tiling.lift_schedule_after_env added_dims env_size semantic_rows.

Definition semantic_second_level_target_schedule
    (layout: second_level_schedule_layout)
    (env_size global_width: nat)
    (semantic_rows: Schedule)
    (w: statement_tiling_witness)
    (recipe: second_level_band_recipe) : Schedule :=
  match layout with
  | SecondLevelGrouped =>
      semantic_second_level_grouped_target_schedule
        env_size global_width semantic_rows w recipe
  | SecondLevelInterleaved =>
      semantic_second_level_interleaved_target_schedule
        env_size global_width semantic_rows w recipe
  end.

Fixpoint check_ordinary_semantic_schedulesb
    (env_size global_width: nat)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (semantic_rows: list Schedule) : bool :=
  match before_pis, after_pis, ws, semantic_rows with
  | [], [], [], [] => true
  | before_pi :: before_pis', after_pi :: after_pis',
    w :: ws', rows :: semantic_rows' =>
      check_schedule_with_symmetric_trailing_zero_paddingb
        rows (Tiling.PL.pi_schedule before_pi) &&
      check_schedule_with_symmetric_trailing_zero_paddingb
        (semantic_ordinary_target_schedule
           env_size global_width rows w)
        (Tiling.PL.pi_schedule after_pi) &&
      check_ordinary_semantic_schedulesb
        env_size global_width before_pis' after_pis' ws' semantic_rows'
  | _, _, _, _ => false
  end.

Fixpoint check_second_level_semantic_schedulesb
    (layout: second_level_schedule_layout)
    (env_size global_width: nat)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (recipes: list second_level_band_recipe)
    (semantic_rows: list Schedule) : bool :=
  match before_pis, after_pis, ws, recipes, semantic_rows with
  | [], [], [], [], [] => true
  | before_pi :: before_pis', after_pi :: after_pis',
    w :: ws', recipe :: recipes', rows :: semantic_rows' =>
      check_schedule_with_symmetric_trailing_zero_paddingb
        rows (Tiling.PL.pi_schedule before_pi) &&
      check_schedule_with_symmetric_trailing_zero_paddingb
        (semantic_second_level_target_schedule
           layout env_size global_width rows w recipe)
        (Tiling.PL.pi_schedule after_pi) &&
      check_second_level_semantic_schedulesb
        layout env_size global_width
        before_pis' after_pis' ws' recipes' semantic_rows'
  | _, _, _, _, _ => false
  end.

Definition check_schedule_lists_zero_erasure_same_masksb
    (expected actual: list Schedule) : bool :=
  match expected, actual with
  | [], [] => true
  | expected0 :: expected', actual0 :: actual' =>
      check_schedule_masks_eqb
        (strict_zero_schedule_mask expected0) expected' &&
      check_schedule_masks_eqb
        (strict_zero_schedule_mask actual0) actual' &&
      check_schedule_lists_after_zero_erasureb expected actual
  | _, _ => false
  end.




Record ordinary_semantic_band_shape := {
  osbs_rows : list Schedule;
  osbs_global_sizes : list Z;
  osbs_mask : list bool;
}.

Record second_level_semantic_band_shape := {
  slsbs_rows : list Schedule;
  slsbs_recipes : list second_level_band_recipe;
  slsbs_global_root_sizes : list Z;
  slsbs_global_child_sizes : list Z;
  slsbs_mask : list bool;
  slsbs_layout : second_level_schedule_layout;
}.

Definition infer_pprog_ordinary_semantic_band_shape
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness)
    : option ordinary_semantic_band_shape :=
  let '(before_pis, before_ctxt, before_vars) := before in
  let '(after_pis, after_ctxt, after_vars) := after in
  if TilingCheck.ctxt_eqb before_ctxt after_ctxt &&
     TilingCheck.ctxt_ty_eqb before_vars after_vars
  then
    match parse_ordinary_semantic_data ws with
    | Some data =>
        let raw_schedules := List.map fst data in
        let local_sizes := List.map snd data in
        let mask := global_semantic_schedule_mask raw_schedules in
        let global_width := List.length mask in
        match
          infer_global_prefix_sizes local_sizes,
          compact_semantic_schedules
            (List.length before_ctxt) before_pis raw_schedules mask
        with
        | Some global_sizes, Some semantic_rows =>
            if Nat.ltb O global_width &&
               Nat.eqb (List.length global_sizes) global_width &&
               check_ordinary_semantic_schedulesb
                 (List.length before_ctxt) global_width
                 before_pis after_pis ws semantic_rows
            then
              Some
                {| osbs_rows := semantic_rows;
                   osbs_global_sizes := global_sizes;
                   osbs_mask := mask |}
            else None
        | _, _ => None
        end
    | None => None
    end
  else None.

Definition infer_pprog_second_level_semantic_band_shape
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness)
    : option second_level_semantic_band_shape :=
  let '(before_pis, before_ctxt, before_vars) := before in
  let '(after_pis, after_ctxt, after_vars) := after in
  if TilingCheck.ctxt_eqb before_ctxt after_ctxt &&
     TilingCheck.ctxt_ty_eqb before_vars after_vars
  then
    match parse_second_level_semantic_recipes ws with
    | Some recipes =>
        let raw_schedules := List.map slbr_root_rows recipes in
        let root_sizes := List.map slbr_root_sizes recipes in
        let child_sizes := List.map slbr_child_sizes recipes in
        let mask := global_semantic_schedule_mask raw_schedules in
        let global_width := List.length mask in
        match
          infer_global_prefix_sizes root_sizes,
          infer_global_prefix_sizes child_sizes,
          compact_semantic_schedules
            (List.length before_ctxt) before_pis raw_schedules mask
        with
        | Some global_root_sizes,
          Some global_child_sizes,
          Some semantic_rows =>
            if Nat.ltb O global_width &&
               Nat.eqb (List.length global_root_sizes) global_width &&
               Nat.eqb (List.length global_child_sizes) global_width
            then
              if check_second_level_semantic_schedulesb
                   SecondLevelGrouped
                   (List.length before_ctxt) global_width
                   before_pis after_pis ws recipes semantic_rows
              then
                Some
                  {| slsbs_rows := semantic_rows;
                     slsbs_recipes := recipes;
                     slsbs_global_root_sizes := global_root_sizes;
                     slsbs_global_child_sizes := global_child_sizes;
                     slsbs_mask := mask;
                     slsbs_layout := SecondLevelGrouped |}
              else
                if check_second_level_semantic_schedulesb
                     SecondLevelInterleaved
                     (List.length before_ctxt) global_width
                     before_pis after_pis ws recipes semantic_rows
                then
                  Some
                    {| slsbs_rows := semantic_rows;
                       slsbs_recipes := recipes;
                       slsbs_global_root_sizes := global_root_sizes;
                       slsbs_global_child_sizes := global_child_sizes;
                       slsbs_mask := mask;
                       slsbs_layout := SecondLevelInterleaved |}
                else None
            else None
        | _, _, _ => None
        end
    | None => None
    end
  else None.

Definition checked_tiling_sourceb_semantic_band_direct
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness) : imp bool :=
  let '(before_pis, before_ctxt, _) := before in
  let '(after_pis, _, _) := after in
  let pis :=
    Tiling.compose_tiling_pinstrs_ext_from_after
      (List.length before_ctxt) before_pis after_pis ws in
  if TilingCheck.check_pprog_tiling_sourceb before after ws then
    match infer_pprog_ordinary_semantic_band_shape before after ws with
    | Some shape =>
        match
          lift_semantic_schedules_for_tiling
            (List.length before_ctxt) ws (osbs_rows shape)
        with
        | Some lifted_rows =>
            check_semantic_band_components_direct
              pis lifted_rows (List.length before_ctxt)
        | None => pure false
        end
    | None =>
        match infer_pprog_second_level_semantic_band_shape before after ws with
        | Some shape =>
            match
              lift_semantic_schedules_for_tiling
                (List.length before_ctxt) ws (slsbs_rows shape)
            with
            | Some lifted_rows =>
                check_semantic_band_components_direct
                  pis lifted_rows (List.length before_ctxt)
            | None => pure false
            end
        | None => pure false
        end
    end
  else pure false.

Lemma select_by_mask_map :
  forall (A B: Type) (f: A -> B) mask xs,
    List.map f (select_by_mask mask xs) =
    select_by_mask mask (List.map f xs).
Proof.
  intros A B f mask.
  induction mask as [|keep mask IH]; intros xs; destruct xs as [|x xs];
    simpl; try reflexivity.
  destruct keep; simpl; rewrite IH; reflexivity.
Qed.

Lemma affine_product_select_by_mask :
  forall mask rows idx,
    affine_product (select_by_mask mask rows) idx =
    select_by_mask mask (affine_product rows idx).
Proof.
  intros mask rows idx.
  unfold affine_product.
  apply select_by_mask_map.
Qed.

Lemma select_by_mask_length_same :
  forall (A B: Type) mask (xs: list A) (ys: list B),
    List.length xs = List.length mask ->
    List.length ys = List.length mask ->
    List.length (select_by_mask mask xs) =
    List.length (select_by_mask mask ys).
Proof.
  intros A B mask.
  induction mask as [|keep mask IH]; intros xs ys Hxs Hys;
    destruct xs as [|x xs]; destruct ys as [|y ys];
    simpl in *; try discriminate; try reflexivity.
  destruct keep; simpl; f_equal; eapply IH; lia.
Qed.

Lemma select_by_mask_in :
  forall (A: Type) mask (xs: list A) x,
    In x (select_by_mask mask xs) ->
    In x xs.
Proof.
  intros A mask.
  induction mask as [|keep mask IH]; intros xs x Hin;
    destruct xs as [|head xs]; simpl in *; try contradiction.
  destruct keep.
  - destruct Hin as [Hin | Hin].
    + left. exact Hin.
    + right. eapply IH. exact Hin.
  - right. eapply IH. exact Hin.
Qed.

Lemma exact_listzzs_cols_select_by_mask :
  forall cols mask rows,
    exact_listzzs_cols cols rows ->
    exact_listzzs_cols cols (select_by_mask mask rows).
Proof.
  intros cols mask rows Hcols coeffs c row Hin Heq.
  eapply Hcols.
  - eapply select_by_mask_in.
    exact Hin.
  - exact Heq.
Qed.

Lemma exact_listzzs_cols_repeat_zero_schedule_row :
  forall cols n,
    exact_listzzs_cols cols
      (repeat (zero_schedule_row cols) n).
Proof.
  intros cols n coeffs c row Hin Heq.
  apply repeat_spec in Hin.
  subst row.
  inversion Heq; subst coeffs c.
  unfold zero_schedule_row.
  simpl.
  apply repeat_length.
Qed.

Lemma exact_listzzs_cols_pad_schedule_to_len :
  forall cols len rows,
    exact_listzzs_cols cols rows ->
    exact_listzzs_cols cols
      (Tiling.PL.pad_schedule_to_len cols len rows).
Proof.
  intros cols len rows Hcols.
  unfold Tiling.PL.pad_schedule_to_len.
  eapply exact_listzzs_cols_app_local_component.
  - exact Hcols.
  - eapply exact_listzzs_cols_repeat_zero_schedule_row.
Qed.

Lemma compact_semantic_schedule_exact_cols :
  forall cols mask raw,
    exact_listzzs_cols cols raw ->
    exact_listzzs_cols cols
      (compact_semantic_schedule cols mask raw).
Proof.
  intros cols mask raw Hcols.
  unfold compact_semantic_schedule.
  eapply exact_listzzs_cols_select_by_mask.
  eapply exact_listzzs_cols_pad_schedule_to_len.
  exact Hcols.
Qed.

Lemma schedule_rows_of_links_aux_exact_cols :
  forall prefix_len point_dim param_dim links rows,
    schedule_rows_of_links_aux prefix_len links = Some rows ->
    well_formed_tile_links prefix_len point_dim links ->
    Forall
      (fun link =>
         List.length (ae_param_coeffs (tl_expr link)) = param_dim)
      links ->
    exact_listzzs_cols (param_dim + point_dim)%nat rows.
Proof.
  intros prefix_len point_dim param_dim links.
  revert prefix_len.
  induction links as [|link links IH];
    intros prefix_len rows Hrows Hwf Hparams.
  - simpl in Hrows.
    inversion Hrows; subst rows.
    unfold exact_listzzs_cols.
    intros coeffs c row Hin.
    contradiction.
  - simpl in Hrows.
    destruct
      (listz_strict_eqb
         (firstn prefix_len (ae_var_coeffs (tl_expr link)))
         (repeat 0%Z prefix_len))
      eqn:Hzero; try discriminate.
    destruct
      (schedule_rows_of_links_aux (S prefix_len) links)
      as [rest|] eqn:Hrest; try discriminate.
    inversion Hrows; subst rows; clear Hrows.
    destruct Hwf as [Hvars Hwf].
    inversion Hparams as [|link0 links0 Hparam Hparams'];
      subst link0 links0.
    assert
      (Hrest_cols :
         exact_listzzs_cols (param_dim + point_dim)%nat rest).
    {
      eapply IH; eauto.
    }
    unfold exact_listzzs_cols.
    intros coeffs c row Hin Heq.
    destruct Hin as [Hin | Hin].
    + subst row.
      inversion Heq; subst coeffs c.
      unfold schedule_row_of_tile_link_base.
      simpl.
      rewrite app_length, Hparam, skipn_length, Hvars.
      lia.
    + eapply Hrest_cols; eauto.
Qed.

Lemma schedule_rows_of_links_exact_cols :
  forall param_dim w rows,
    schedule_rows_of_links w = Some rows ->
    Tiling.wf_statement_tiling_witness_with_param_dim param_dim w ->
    exact_listzzs_cols
      (param_dim + stw_point_dim w)%nat rows.
Proof.
  intros param_dim w rows Hrows Hwf.
  destruct Hwf as [Hlinks Hparams].
  unfold schedule_rows_of_links in Hrows.
  unfold well_formed_statement_tiling_witness in Hlinks.
  eapply schedule_rows_of_links_aux_exact_cols; eauto.
Qed.

Lemma affine_function_is_zero_sound_local :
  forall coeffs c,
    Tiling.PL.affine_function_is_zero (coeffs, c) = true ->
    coeffs = repeat 0%Z (List.length coeffs) /\ c = 0%Z.
Proof.
  intros coeffs c Hzero.
  unfold Tiling.PL.affine_function_is_zero in Hzero.
  apply andb_true_iff in Hzero.
  destruct Hzero as [Hcoeffs Hc].
  apply Z.eqb_eq in Hc.
  split; [|exact Hc].
  induction coeffs as [|x coeffs IH].
  - reflexivity.
  - change
      (Z.eqb 0%Z x && forallb (Z.eqb 0%Z) coeffs = true)
      in Hcoeffs.
    apply andb_true_iff in Hcoeffs.
    destruct Hcoeffs as [Hx Hcoeffs].
    apply Z.eqb_eq in Hx.
    subst x.
    change
      (0%Z :: coeffs =
       0%Z :: repeat 0%Z (List.length coeffs)).
    f_equal.
    apply IH.
    exact Hcoeffs.
Qed.

Lemma affine_function_is_zero_eval_local :
  forall row idx,
    Tiling.PL.affine_function_is_zero row = true ->
    (dot_product (fst row) idx + snd row)%Z = 0%Z.
Proof.
  intros [coeffs c] idx Hzero.
  simpl.
  destruct
    (affine_function_is_zero_sound_local coeffs c Hzero)
    as [Hcoeffs Hc].
  rewrite Hcoeffs, Hc.
  rewrite Tiling.tiling_dot_product_eq_linalg_dot_product.
  rewrite dot_product_repeat_zero_left.
  lia.
Qed.

Lemma lift_semantic_schedules_for_tiling_length :
  forall env_size ws rows lifted_rows,
    lift_semantic_schedules_for_tiling env_size ws rows =
      Some lifted_rows ->
    List.length lifted_rows = List.length ws /\
    List.length rows = List.length ws.
Proof.
  intros env_size ws.
  induction ws as [|w ws IH]; intros rows lifted_rows Hlift;
    destruct rows as [|row rows]; simpl in Hlift; try discriminate.
  - inversion Hlift.
    split; reflexivity.
  - destruct
      (lift_semantic_schedules_for_tiling env_size ws rows)
      as [rest|] eqn:Hrest; try discriminate.
    inversion Hlift; subst lifted_rows.
    destruct (IH rows rest Hrest) as [Hrest_len Hrows_len].
    simpl.
    split; lia.
Qed.

Lemma lift_semantic_schedules_for_tiling_exact_cols :
  forall env_size ws rows lifted_rows,
    lift_semantic_schedules_for_tiling env_size ws rows =
      Some lifted_rows ->
    Forall2
      (fun w semantic_rows =>
         exact_listzzs_cols
           (env_size + stw_point_dim w)%nat semantic_rows)
      ws rows ->
    Forall2
      (fun w lifted =>
         exact_listzzs_cols
           (env_size + List.length (stw_links w) + stw_point_dim w)%nat
           lifted)
      ws lifted_rows.
Proof.
  intros env_size ws.
  induction ws as [|w ws IH]; intros rows lifted_rows Hlift Hcols;
    destruct rows as [|row rows]; simpl in Hlift; try discriminate.
  - inversion Hlift; subst lifted_rows.
    constructor.
  - inversion Hcols as [|w0 ws0 row0 rows0 Hrow_cols Hrows_cols];
      subst w0 ws0 row0 rows0.
    destruct
      (lift_semantic_schedules_for_tiling env_size ws rows)
      as [rest|] eqn:Hrest; try discriminate.
    inversion Hlift; subst lifted_rows.
    constructor.
    + replace
        (env_size + List.length (stw_links w) + stw_point_dim w)%nat
        with
        (List.length (stw_links w) +
         (env_size + stw_point_dim w))%nat
        by lia.
      eapply lift_schedule_after_env_exact_cols.
      * exact Hrow_cols.
      * lia.
    + eapply IH; eauto.
Qed.

Inductive ordinary_semantic_schedules_match
    (env_size global_width: nat)
    : list Tiling.PL.PolyInstr ->
      list Tiling.PL.PolyInstr ->
      list statement_tiling_witness ->
      list Schedule -> Prop :=
| ordinary_semantic_schedules_match_nil :
    ordinary_semantic_schedules_match env_size global_width [] [] [] []
| ordinary_semantic_schedules_match_cons :
    forall before_pi before_pis after_pi after_pis w ws rows semantic_rows,
      schedule_matches_with_symmetric_trailing_zero_padding
        rows (Tiling.PL.pi_schedule before_pi) ->
      schedule_matches_with_symmetric_trailing_zero_padding
        (semantic_ordinary_target_schedule
           env_size global_width rows w)
        (Tiling.PL.pi_schedule after_pi) ->
      ordinary_semantic_schedules_match
        env_size global_width before_pis after_pis ws semantic_rows ->
      ordinary_semantic_schedules_match
        env_size global_width
        (before_pi :: before_pis) (after_pi :: after_pis)
        (w :: ws) (rows :: semantic_rows).

Lemma check_ordinary_semantic_schedulesb_sound :
  forall env_size global_width before_pis after_pis ws semantic_rows,
    check_ordinary_semantic_schedulesb
      env_size global_width before_pis after_pis ws semantic_rows = true ->
    ordinary_semantic_schedules_match
      env_size global_width before_pis after_pis ws semantic_rows.
Proof.
  intros env_size global_width before_pis.
  induction before_pis as [|before_pi before_pis IH];
    intros after_pis ws semantic_rows Hcheck;
    destruct after_pis as [|after_pi after_pis];
    destruct ws as [|w ws];
    destruct semantic_rows as [|rows semantic_rows];
    simpl in Hcheck; try discriminate.
  - constructor.
  - repeat rewrite andb_true_iff in Hcheck.
    destruct Hcheck as [[Hbefore Hafter] Hrest].
    constructor.
    + eapply check_schedule_with_symmetric_trailing_zero_paddingb_sound.
      exact Hbefore.
    + eapply check_schedule_with_symmetric_trailing_zero_paddingb_sound.
      exact Hafter.
    + eapply IH.
      exact Hrest.
Qed.

Inductive second_level_semantic_schedules_match
    (layout: second_level_schedule_layout)
    (env_size global_width: nat)
    : list Tiling.PL.PolyInstr ->
      list Tiling.PL.PolyInstr ->
      list statement_tiling_witness ->
      list second_level_band_recipe ->
      list Schedule -> Prop :=
| second_level_semantic_schedules_match_nil :
    second_level_semantic_schedules_match
      layout env_size global_width [] [] [] [] []
| second_level_semantic_schedules_match_cons :
    forall before_pi before_pis after_pi after_pis
           w ws recipe recipes rows semantic_rows,
      schedule_matches_with_symmetric_trailing_zero_padding
        rows (Tiling.PL.pi_schedule before_pi) ->
      schedule_matches_with_symmetric_trailing_zero_padding
        (semantic_second_level_target_schedule
           layout env_size global_width rows w recipe)
        (Tiling.PL.pi_schedule after_pi) ->
      second_level_semantic_schedules_match
        layout env_size global_width
        before_pis after_pis ws recipes semantic_rows ->
      second_level_semantic_schedules_match
        layout env_size global_width
        (before_pi :: before_pis) (after_pi :: after_pis)
        (w :: ws) (recipe :: recipes) (rows :: semantic_rows).

Lemma check_second_level_semantic_schedulesb_sound :
  forall layout env_size global_width
         before_pis after_pis ws recipes semantic_rows,
    check_second_level_semantic_schedulesb
      layout env_size global_width
      before_pis after_pis ws recipes semantic_rows = true ->
    second_level_semantic_schedules_match
      layout env_size global_width
      before_pis after_pis ws recipes semantic_rows.
Proof.
  intros layout env_size global_width before_pis.
  induction before_pis as [|before_pi before_pis IH];
    intros after_pis ws recipes semantic_rows Hcheck;
    destruct after_pis as [|after_pi after_pis];
    destruct ws as [|w ws];
    destruct recipes as [|recipe recipes];
    destruct semantic_rows as [|rows semantic_rows];
    simpl in Hcheck; try discriminate.
  - constructor.
  - repeat rewrite andb_true_iff in Hcheck.
    destruct Hcheck as [[Hbefore Hafter] Hrest].
    constructor.
    + eapply check_schedule_with_symmetric_trailing_zero_paddingb_sound.
      exact Hbefore.
    + eapply check_schedule_with_symmetric_trailing_zero_paddingb_sound.
      exact Hafter.
    + eapply IH.
      exact Hrest.
Qed.

Definition schedule_lists_zero_erasure_match
    (expected actual: list Schedule) : Prop :=
  exists expected_mask actual_mask,
    Forall
      (fun sched => strict_zero_schedule_mask sched = expected_mask)
      expected /\
    Forall
      (fun sched => strict_zero_schedule_mask sched = actual_mask)
      actual /\
    Forall2
      (fun expected_sched actual_sched =>
         Tiling.PL.remove_zero_schedule_dims expected_sched =
         Tiling.PL.remove_zero_schedule_dims actual_sched)
      expected actual.

Lemma check_schedule_lists_zero_erasure_same_masksb_sound :
  forall expected actual,
    check_schedule_lists_zero_erasure_same_masksb expected actual = true ->
    schedule_lists_zero_erasure_match expected actual.
Proof.
  intros expected actual Hcheck.
  unfold check_schedule_lists_zero_erasure_same_masksb in Hcheck.
  destruct expected as [|expected0 expected'];
    destruct actual as [|actual0 actual']; try discriminate.
  - exists [], [].
    repeat split; constructor.
  - repeat rewrite andb_true_iff in Hcheck.
    destruct Hcheck as [[Hexpected_mask Hactual_mask] Hpairs].
    exists
      (strict_zero_schedule_mask expected0),
      (strict_zero_schedule_mask actual0).
    repeat split.
    + constructor.
      * reflexivity.
      * eapply check_schedule_masks_eqb_sound.
        exact Hexpected_mask.
    + constructor.
      * reflexivity.
      * eapply check_schedule_masks_eqb_sound.
        exact Hactual_mask.
    + eapply check_schedule_lists_after_zero_erasureb_sound.
      exact Hpairs.
Qed.

Lemma schedule_lists_zero_erasure_match_pair_lex :
  forall expected actual i j
         expected_i actual_i expected_j actual_j idx_i idx_j,
    schedule_lists_zero_erasure_match expected actual ->
    nth_error expected i = Some expected_i ->
    nth_error actual i = Some actual_i ->
    nth_error expected j = Some expected_j ->
    nth_error actual j = Some actual_j ->
    lex_compare
      (affine_product actual_i idx_i)
      (affine_product actual_j idx_j) =
    lex_compare
      (affine_product expected_i idx_i)
      (affine_product expected_j idx_j).
Proof.
  intros expected actual i j
         expected_i actual_i expected_j actual_j idx_i idx_j
         [expected_mask [actual_mask
          [Hexpected_masks [Hactual_masks Hpairs]]]]
         Hexpected_i Hactual_i Hexpected_j Hactual_j.
  pose proof
    (Tiling.Forall_nth_error
       _ _ expected i expected_i Hexpected_masks Hexpected_i)
    as Hexpected_mask_i.
  pose proof
    (Tiling.Forall_nth_error
       _ _ expected j expected_j Hexpected_masks Hexpected_j)
    as Hexpected_mask_j.
  pose proof
    (Tiling.Forall_nth_error
       _ _ actual i actual_i Hactual_masks Hactual_i)
    as Hactual_mask_i.
  pose proof
    (Tiling.Forall_nth_error
       _ _ actual j actual_j Hactual_masks Hactual_j)
    as Hactual_mask_j.
  pose proof
    (Tiling.Forall2_nth_error
       _ _
       (fun expected_sched actual_sched =>
          Tiling.PL.remove_zero_schedule_dims expected_sched =
          Tiling.PL.remove_zero_schedule_dims actual_sched)
       expected actual i expected_i actual_i
       Hpairs Hexpected_i Hactual_i)
    as Hpair_i.
  pose proof
    (Tiling.Forall2_nth_error
       _ _
       (fun expected_sched actual_sched =>
          Tiling.PL.remove_zero_schedule_dims expected_sched =
          Tiling.PL.remove_zero_schedule_dims actual_sched)
       expected actual j expected_j actual_j
       Hpairs Hexpected_j Hactual_j)
    as Hpair_j.
  pose proof
    (lex_compare_affine_product_remove_zero_same_mask
       actual_i actual_j idx_i idx_j
       (eq_trans Hactual_mask_i (eq_sym Hactual_mask_j)))
    as Hactual_compact.
  pose proof
    (lex_compare_affine_product_remove_zero_same_mask
       expected_i expected_j idx_i idx_j
       (eq_trans Hexpected_mask_i (eq_sym Hexpected_mask_j)))
    as Hexpected_compact.
  rewrite Hactual_compact.
  rewrite <- Hpair_i, <- Hpair_j.
  symmetry.
  exact Hexpected_compact.
Qed.

Lemma option_if_some_inv_local :
  forall (A: Type) (b: bool) (x y: A),
    (if b then Some x else None) = Some y ->
    b = true /\ x = y.
Proof.
  intros A b x y H.
  destruct b; simpl in H; try discriminate.
  inversion H.
  split; reflexivity.
Qed.

Lemma option_if_then_some_inv_local :
  forall (A: Type) (b: bool) (then_branch: option A) (y: A),
    (if b then then_branch else None) = Some y ->
    b = true /\ then_branch = Some y.
Proof.
  intros A b then_branch y H.
  destruct b; simpl in H; try discriminate.
  split; [reflexivity|exact H].
Qed.

Lemma option_if_some_else_inv_local :
  forall (A: Type) (b: bool) (x y: A) (else_branch: option A),
    (if b then Some x else else_branch) = Some y ->
    (b = true /\ x = y) \/
    (b = false /\ else_branch = Some y).
Proof.
  intros A b x y else_branch H.
  destruct b; simpl in H.
  - left. inversion H. split; reflexivity.
  - right. split; [reflexivity|exact H].
Qed.

Definition ordinary_semantic_band_shape_property_with_witness
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness)
    (shape: ordinary_semantic_band_shape) : Prop :=
  let '(before_pis, before_ctxt, before_vars) := before in
  let '(after_pis, after_ctxt, after_vars) := after in
  before_ctxt = after_ctxt /\
  before_vars = after_vars /\
  exists data,
    parse_ordinary_semantic_data ws = Some data /\
    infer_global_prefix_sizes (List.map snd data) =
      Some (osbs_global_sizes shape) /\
    osbs_mask shape =
      global_semantic_schedule_mask (List.map fst data) /\
    compact_semantic_schedules
      (List.length before_ctxt) before_pis
      (List.map fst data) (osbs_mask shape) =
      Some (osbs_rows shape) /\
    (O < List.length (osbs_mask shape))%nat /\
    List.length (osbs_global_sizes shape) =
      List.length (osbs_mask shape) /\
    ordinary_semantic_schedules_match
      (List.length before_ctxt)
      (List.length (osbs_mask shape))
      before_pis after_pis ws (osbs_rows shape).

Lemma infer_pprog_ordinary_semantic_band_shape_sound :
  forall before after ws shape,
    infer_pprog_ordinary_semantic_band_shape before after ws = Some shape ->
    ordinary_semantic_band_shape_property_with_witness
      before after ws shape.
Proof.
  intros [[before_pis before_ctxt] before_vars]
         [[after_pis after_ctxt] after_vars] ws shape Hinfer.
  cbn in Hinfer.
  destruct
    (TilingCheck.ctxt_eqb before_ctxt after_ctxt &&
     TilingCheck.ctxt_ty_eqb before_vars after_vars)
    eqn:Hctxt; try discriminate.
  apply andb_true_iff in Hctxt.
  destruct Hctxt as [Hctxt Hvars].
  destruct (parse_ordinary_semantic_data ws) as [data|] eqn:Hdata;
    try discriminate.
  destruct
    (infer_global_prefix_sizes (List.map snd data))
    as [global_sizes|] eqn:Hsizes; try discriminate.
  destruct
    (compact_semantic_schedules
       (List.length before_ctxt) before_pis
       (List.map fst data)
       (global_semantic_schedule_mask (List.map fst data)))
    as [semantic_rows|] eqn:Hrows; try discriminate.
  pose proof
    (option_if_some_inv_local
       ordinary_semantic_band_shape
       (Nat.ltb O
          (List.length
             (global_semantic_schedule_mask (List.map fst data))) &&
        Nat.eqb (List.length global_sizes)
          (List.length
             (global_semantic_schedule_mask (List.map fst data))) &&
        check_ordinary_semantic_schedulesb
          (List.length before_ctxt)
          (List.length
             (global_semantic_schedule_mask (List.map fst data)))
          before_pis after_pis ws semantic_rows)
       {| osbs_rows := semantic_rows;
          osbs_global_sizes := global_sizes;
          osbs_mask :=
            global_semantic_schedule_mask (List.map fst data) |}
       shape
       Hinfer)
    as [Hchecks Hshape].
  subst shape.
  repeat rewrite andb_true_iff in Hchecks.
  destruct Hchecks as [[Hpositive Hwidth] Hschedules].
  unfold ordinary_semantic_band_shape_property_with_witness.
  cbn.
  split.
  - apply TilingCheck.ctxt_eqb_eq. exact Hctxt.
  - split.
    + apply TilingCheck.ctxt_ty_eqb_eq. exact Hvars.
    + exists data.
      repeat split.
      * exact Hdata.
      * exact Hsizes.
      * exact Hrows.
      * apply Nat.ltb_lt. exact Hpositive.
      * apply Nat.eqb_eq. exact Hwidth.
      * eapply check_ordinary_semantic_schedulesb_sound.
        exact Hschedules.
Qed.

Definition second_level_semantic_band_shape_property_with_witness
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness)
    (shape: second_level_semantic_band_shape) : Prop :=
  let '(before_pis, before_ctxt, before_vars) := before in
  let '(after_pis, after_ctxt, after_vars) := after in
  before_ctxt = after_ctxt /\
  before_vars = after_vars /\
  parse_second_level_semantic_recipes ws =
    Some (slsbs_recipes shape) /\
  infer_global_prefix_sizes
    (List.map slbr_root_sizes (slsbs_recipes shape)) =
    Some (slsbs_global_root_sizes shape) /\
  infer_global_prefix_sizes
    (List.map slbr_child_sizes (slsbs_recipes shape)) =
    Some (slsbs_global_child_sizes shape) /\
  slsbs_mask shape =
    global_semantic_schedule_mask
      (List.map slbr_root_rows (slsbs_recipes shape)) /\
  compact_semantic_schedules
    (List.length before_ctxt) before_pis
    (List.map slbr_root_rows (slsbs_recipes shape))
    (slsbs_mask shape) =
    Some (slsbs_rows shape) /\
  (O < List.length (slsbs_mask shape))%nat /\
  List.length (slsbs_global_root_sizes shape) =
    List.length (slsbs_mask shape) /\
  List.length (slsbs_global_child_sizes shape) =
    List.length (slsbs_mask shape) /\
  second_level_semantic_schedules_match
    (slsbs_layout shape)
    (List.length before_ctxt)
    (List.length (slsbs_mask shape))
    before_pis after_pis ws
    (slsbs_recipes shape) (slsbs_rows shape).

Lemma infer_pprog_second_level_semantic_band_shape_sound :
  forall before after ws shape,
    infer_pprog_second_level_semantic_band_shape before after ws = Some shape ->
    second_level_semantic_band_shape_property_with_witness
      before after ws shape.
Proof.
  intros [[before_pis before_ctxt] before_vars]
         [[after_pis after_ctxt] after_vars] ws shape Hinfer.
  cbn in Hinfer.
  destruct
    (TilingCheck.ctxt_eqb before_ctxt after_ctxt &&
     TilingCheck.ctxt_ty_eqb before_vars after_vars)
    eqn:Hctxt; try discriminate.
  apply andb_true_iff in Hctxt.
  destruct Hctxt as [Hctxt Hvars].
  destruct (parse_second_level_semantic_recipes ws)
    as [recipes|] eqn:Hrecipes; try discriminate.
  destruct
    (infer_global_prefix_sizes (List.map slbr_root_sizes recipes))
    as [global_root_sizes|] eqn:Hroot_sizes; try discriminate.
  destruct
    (infer_global_prefix_sizes (List.map slbr_child_sizes recipes))
    as [global_child_sizes|] eqn:Hchild_sizes; try discriminate.
  destruct
    (compact_semantic_schedules
       (List.length before_ctxt) before_pis
       (List.map slbr_root_rows recipes)
       (global_semantic_schedule_mask
          (List.map slbr_root_rows recipes)))
    as [semantic_rows|] eqn:Hrows; try discriminate.
  set
    (mask :=
       global_semantic_schedule_mask
         (List.map slbr_root_rows recipes)).
  set
    (widths_ok :=
       Nat.ltb O (List.length mask) &&
       Nat.eqb (List.length global_root_sizes) (List.length mask) &&
       Nat.eqb (List.length global_child_sizes) (List.length mask)).
  set
    (grouped_ok :=
       check_second_level_semantic_schedulesb
         SecondLevelGrouped
         (List.length before_ctxt) (List.length mask)
         before_pis after_pis ws recipes semantic_rows).
  set
    (interleaved_ok :=
       check_second_level_semantic_schedulesb
         SecondLevelInterleaved
         (List.length before_ctxt) (List.length mask)
         before_pis after_pis ws recipes semantic_rows).
  assert
    (Hinfer' :
       (if widths_ok
        then
          if grouped_ok
          then
            Some
              {| slsbs_rows := semantic_rows;
                 slsbs_recipes := recipes;
                 slsbs_global_root_sizes := global_root_sizes;
                 slsbs_global_child_sizes := global_child_sizes;
                 slsbs_mask := mask;
                 slsbs_layout := SecondLevelGrouped |}
          else
            if interleaved_ok
            then
              Some
                {| slsbs_rows := semantic_rows;
                   slsbs_recipes := recipes;
                   slsbs_global_root_sizes := global_root_sizes;
                   slsbs_global_child_sizes := global_child_sizes;
                   slsbs_mask := mask;
                   slsbs_layout := SecondLevelInterleaved |}
            else None
        else None) = Some shape).
  {
    unfold widths_ok, grouped_ok, interleaved_ok, mask.
    exact Hinfer.
  }
  destruct
    (option_if_then_some_inv_local
       second_level_semantic_band_shape widths_ok
       (if grouped_ok
        then
          Some
            {| slsbs_rows := semantic_rows;
               slsbs_recipes := recipes;
               slsbs_global_root_sizes := global_root_sizes;
               slsbs_global_child_sizes := global_child_sizes;
               slsbs_mask := mask;
               slsbs_layout := SecondLevelGrouped |}
        else
          if interleaved_ok
          then
            Some
              {| slsbs_rows := semantic_rows;
                 slsbs_recipes := recipes;
                 slsbs_global_root_sizes := global_root_sizes;
                 slsbs_global_child_sizes := global_child_sizes;
                 slsbs_mask := mask;
                 slsbs_layout := SecondLevelInterleaved |}
          else None)
       shape Hinfer')
    as [Hwidths Hlayout].
  unfold widths_ok in Hwidths.
  repeat rewrite andb_true_iff in Hwidths.
  destruct Hwidths as [[Hpositive Hroot_width] Hchild_width].
  destruct
    (option_if_some_else_inv_local
       second_level_semantic_band_shape grouped_ok
       {| slsbs_rows := semantic_rows;
          slsbs_recipes := recipes;
          slsbs_global_root_sizes := global_root_sizes;
          slsbs_global_child_sizes := global_child_sizes;
          slsbs_mask := mask;
          slsbs_layout := SecondLevelGrouped |}
       shape
       (if interleaved_ok
        then
          Some
            {| slsbs_rows := semantic_rows;
               slsbs_recipes := recipes;
               slsbs_global_root_sizes := global_root_sizes;
               slsbs_global_child_sizes := global_child_sizes;
               slsbs_mask := mask;
               slsbs_layout := SecondLevelInterleaved |}
        else None)
       Hlayout)
    as [[Hgrouped Hshape] | [Hnot_grouped Hinterleaved]].
  - subst shape.
    unfold second_level_semantic_band_shape_property_with_witness.
    cbn.
    repeat split.
    + apply TilingCheck.ctxt_eqb_eq. exact Hctxt.
    + apply TilingCheck.ctxt_ty_eqb_eq. exact Hvars.
    + exact Hrecipes.
    + exact Hroot_sizes.
    + exact Hchild_sizes.
    + exact Hrows.
    + apply Nat.ltb_lt. exact Hpositive.
    + apply Nat.eqb_eq. exact Hroot_width.
    + apply Nat.eqb_eq. exact Hchild_width.
    + eapply check_second_level_semantic_schedulesb_sound.
      unfold grouped_ok in Hgrouped.
      exact Hgrouped.
  - destruct
      (option_if_some_inv_local
         second_level_semantic_band_shape interleaved_ok
         {| slsbs_rows := semantic_rows;
            slsbs_recipes := recipes;
            slsbs_global_root_sizes := global_root_sizes;
            slsbs_global_child_sizes := global_child_sizes;
            slsbs_mask := mask;
            slsbs_layout := SecondLevelInterleaved |}
         shape Hinterleaved)
      as [Hinterleaved_ok Hshape].
    subst shape.
    unfold second_level_semantic_band_shape_property_with_witness.
    cbn.
    repeat split.
    + apply TilingCheck.ctxt_eqb_eq. exact Hctxt.
    + apply TilingCheck.ctxt_ty_eqb_eq. exact Hvars.
    + exact Hrecipes.
    + exact Hroot_sizes.
    + exact Hchild_sizes.
    + exact Hrows.
    + apply Nat.ltb_lt. exact Hpositive.
    + apply Nat.eqb_eq. exact Hroot_width.
    + apply Nat.eqb_eq. exact Hchild_width.
    + eapply check_second_level_semantic_schedulesb_sound.
      unfold interleaved_ok in Hinterleaved_ok.
      exact Hinterleaved_ok.
Qed.

Inductive semantic_band_direct_shape
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness)
    : list Schedule -> Prop :=
| semantic_band_direct_shape_ordinary :
    forall shape lifted_rows,
      TilingCheck.check_pprog_tiling_sourceb before after ws = true ->
      infer_pprog_ordinary_semantic_band_shape before after ws =
        Some shape ->
      lift_semantic_schedules_for_tiling
        (let '(_, before_ctxt, _) := before in List.length before_ctxt)
        ws (osbs_rows shape) = Some lifted_rows ->
      ordinary_semantic_band_shape_property_with_witness
        before after ws shape ->
      semantic_band_direct_shape before after ws lifted_rows
| semantic_band_direct_shape_second_level :
    forall shape lifted_rows,
      TilingCheck.check_pprog_tiling_sourceb before after ws = true ->
      infer_pprog_ordinary_semantic_band_shape before after ws = None ->
      infer_pprog_second_level_semantic_band_shape before after ws =
        Some shape ->
      lift_semantic_schedules_for_tiling
        (let '(_, before_ctxt, _) := before in List.length before_ctxt)
        ws (slsbs_rows shape) = Some lifted_rows ->
      second_level_semantic_band_shape_property_with_witness
        before after ws shape ->
      semantic_band_direct_shape before after ws lifted_rows.

Lemma checked_tiling_sourceb_semantic_band_direct_true_inv :
  forall before after ws,
    mayReturn
      (checked_tiling_sourceb_semantic_band_direct before after ws)
      true ->
    exists lifted_rows,
      semantic_band_direct_shape before after ws lifted_rows /\
      let '(before_pis, before_ctxt, _) := before in
      let '(after_pis, _, _) := after in
      mayReturn
        (check_semantic_band_components_direct
           (Tiling.compose_tiling_pinstrs_ext_from_after
              (List.length before_ctxt) before_pis after_pis ws)
           lifted_rows (List.length before_ctxt))
        true.
Proof.
  intros [[before_pis before_ctxt] before_vars]
         [[after_pis after_ctxt] after_vars] ws Hcheck.
  unfold checked_tiling_sourceb_semantic_band_direct in Hcheck.
  cbn beta iota zeta in Hcheck.
  destruct
    (TilingCheck.check_pprog_tiling_sourceb
       (before_pis, before_ctxt, before_vars)
       (after_pis, after_ctxt, after_vars) ws)
    eqn:Hsource.
  2:{
    apply mayReturn_pure in Hcheck.
    discriminate.
  }
  destruct
    (infer_pprog_ordinary_semantic_band_shape
       (before_pis, before_ctxt, before_vars)
       (after_pis, after_ctxt, after_vars) ws)
    as [ordinary_shape|] eqn:Hordinary.
  - destruct
      (lift_semantic_schedules_for_tiling
         (List.length before_ctxt) ws (osbs_rows ordinary_shape))
      as [lifted_rows|] eqn:Hlift.
    2:{
      apply mayReturn_pure in Hcheck.
      discriminate.
    }
    exists lifted_rows.
    split; [|exact Hcheck].
    eapply semantic_band_direct_shape_ordinary.
    + exact Hsource.
    + exact Hordinary.
    + exact Hlift.
    + eapply infer_pprog_ordinary_semantic_band_shape_sound.
      exact Hordinary.
  - destruct
      (infer_pprog_second_level_semantic_band_shape
         (before_pis, before_ctxt, before_vars)
         (after_pis, after_ctxt, after_vars) ws)
      as [second_shape|] eqn:Hsecond.
    2:{
      apply mayReturn_pure in Hcheck.
      discriminate.
    }
    destruct
      (lift_semantic_schedules_for_tiling
         (List.length before_ctxt) ws (slsbs_rows second_shape))
      as [lifted_rows|] eqn:Hlift.
    2:{
      apply mayReturn_pure in Hcheck.
      discriminate.
    }
    exists lifted_rows.
    split; [|exact Hcheck].
    eapply semantic_band_direct_shape_second_level.
    + exact Hsource.
    + exact Hordinary.
    + exact Hsecond.
    + exact Hlift.
    + eapply infer_pprog_second_level_semantic_band_shape_sound.
      exact Hsecond.
Qed.


Lemma semantic_stripmined_reversal_implies_decreasing_component :
  forall old1 old2 new1 new2 semantic1 semantic2 tiles1 tiles2,
    is_eq old1 semantic1 = true ->
    is_eq old2 semantic2 = true ->
    is_eq new1 (tiles1 ++ semantic1) = true ->
    is_eq new2 (tiles2 ++ semantic2) = true ->
    List.length semantic1 = List.length semantic2 ->
    (semantic1 = semantic2 -> tiles1 = tiles2) ->
    (listz_pointwise_le semantic1 semantic2 ->
     listz_pointwise_le tiles1 tiles2) ->
    lex_compare old1 old2 = Lt ->
    lex_compare new1 new2 <> Lt ->
    exists dim x y,
      nth_error semantic1 dim = Some x /\
      nth_error semantic2 dim = Some y /\
      (x > y)%Z.
Proof.
  intros old1 old2 new1 new2 semantic1 semantic2 tiles1 tiles2
         Hold_eq1 Hold_eq2 Hnew_eq1 Hnew_eq2 Hsemantic_len
         Htiles_eq Htiles_mono Hold Hnew.
  assert (Hold_semantic : lex_compare semantic1 semantic2 = Lt).
  {
    transitivity (lex_compare old1 semantic2).
    - symmetry. apply lex_compare_left_eq. exact Hold_eq1.
    - rewrite <- (lex_compare_right_eq old1 old2 semantic2 Hold_eq2).
      exact Hold.
  }
  assert
    (Hnew_expected :
       lex_compare
         (tiles1 ++ semantic1)
         (tiles2 ++ semantic2) <> Lt).
  {
    intro Hlt.
    apply Hnew.
    transitivity (lex_compare (tiles1 ++ semantic1) new2).
    - apply lex_compare_left_eq. exact Hnew_eq1.
    - rewrite (lex_compare_right_eq
                 (tiles1 ++ semantic1)
                 new2 (tiles2 ++ semantic2) Hnew_eq2).
      exact Hlt.
  }
  assert
    (Hold_expanded :
       lex_compare
         ([] ++ semantic1 ++ [])
         ([] ++ semantic2 ++ []) = Lt).
  {
    simpl.
    rewrite !app_nil_r.
    exact Hold_semantic.
  }
  assert
    (Hnew_expanded :
       lex_compare
         ([] ++ tiles1 ++ semantic1 ++ [])
         ([] ++ tiles2 ++ semantic2 ++ []) <> Lt).
  {
    simpl.
    rewrite !app_nil_r.
    exact Hnew_expected.
  }
  destruct
    (stripmined_reversal_implies_decreasing_band_component
       [] [] tiles1 tiles2 semantic1 semantic2 [] []
       eq_refl Hsemantic_len Htiles_eq Htiles_mono
       Hold_expanded Hnew_expanded)
    as [_ Hdecrease].
  exact Hdecrease.
Qed.

Lemma semantic_stripmined_reversal_implies_decreasing_component_lex :
  forall old1 old2 new1 new2 semantic1 semantic2 tiles1 tiles2,
    lex_compare old1 old2 =
      lex_compare semantic1 semantic2 ->
    lex_compare new1 new2 =
      lex_compare
        (tiles1 ++ semantic1)
        (tiles2 ++ semantic2) ->
    List.length semantic1 = List.length semantic2 ->
    (semantic1 = semantic2 -> tiles1 = tiles2) ->
    (listz_pointwise_le semantic1 semantic2 ->
     listz_pointwise_le tiles1 tiles2) ->
    lex_compare old1 old2 = Lt ->
    lex_compare new1 new2 <> Lt ->
    exists dim x y,
      nth_error semantic1 dim = Some x /\
      nth_error semantic2 dim = Some y /\
      (x > y)%Z.
Proof.
  intros old1 old2 new1 new2 semantic1 semantic2 tiles1 tiles2
         Hold_lex Hnew_lex Hsemantic_len Htiles_eq Htiles_mono
         Hold Hnew.
  assert (Hold_semantic : lex_compare semantic1 semantic2 = Lt).
  {
    rewrite <- Hold_lex.
    exact Hold.
  }
  assert
    (Hnew_expected :
       lex_compare
         (tiles1 ++ semantic1)
         (tiles2 ++ semantic2) <> Lt).
  {
    intro Hlt.
    apply Hnew.
    rewrite Hnew_lex.
    exact Hlt.
  }
  assert
    (Hold_expanded :
       lex_compare
         ([] ++ semantic1 ++ [])
         ([] ++ semantic2 ++ []) = Lt).
  {
    simpl.
    rewrite !app_nil_r.
    exact Hold_semantic.
  }
  assert
    (Hnew_expanded :
       lex_compare
         ([] ++ tiles1 ++ semantic1 ++ [])
         ([] ++ tiles2 ++ semantic2 ++ []) <> Lt).
  {
    simpl.
    rewrite !app_nil_r.
    exact Hnew_expected.
  }
  destruct
    (stripmined_reversal_implies_decreasing_band_component
       [] [] tiles1 tiles2 semantic1 semantic2 [] []
       eq_refl Hsemantic_len Htiles_eq Htiles_mono
       Hold_expanded Hnew_expanded)
    as [_ Hdecrease].
  exact Hdecrease.
Qed.

Lemma listz_prefixb_sound :
  forall xs ys,
    listz_prefixb xs ys = true ->
    (List.length xs <= List.length ys)%nat /\
    firstn (List.length xs) ys = xs.
Proof.
  intros xs ys Hprefix.
  unfold listz_prefixb in Hprefix.
  apply andb_true_iff in Hprefix.
  destruct Hprefix as [Hlen Heq].
  split.
  - apply Nat.leb_le. exact Hlen.
  - apply listz_strict_eqb_eq in Heq.
    symmetry.
    exact Heq.
Qed.

Definition prefix_sizes (xs ys: list Z) : Prop :=
  (List.length xs <= List.length ys)%nat /\
  firstn (List.length xs) ys = xs.

Lemma prefix_sizes_refl :
  forall xs, prefix_sizes xs xs.
Proof.
  intros xs.
  split; [lia|].
  apply firstn_all.
Qed.

Lemma prefix_sizes_trans :
  forall xs ys zs,
    prefix_sizes xs ys ->
    prefix_sizes ys zs ->
    prefix_sizes xs zs.
Proof.
  intros xs ys zs [Hxy_len Hxy] [Hyz_len Hyz].
  split; [lia|].
  rewrite <- Hxy at 2.
  rewrite <- Hyz.
  rewrite firstn_firstn.
  replace (Nat.min (List.length xs) (List.length ys))
    with (List.length xs) by lia.
  reflexivity.
Qed.

Lemma merge_prefix_sizes_sound :
  forall xs ys merged,
    merge_prefix_sizes xs ys = Some merged ->
    prefix_sizes xs merged /\ prefix_sizes ys merged.
Proof.
  intros xs ys merged Hmerge.
  unfold merge_prefix_sizes in Hmerge.
  destruct (listz_prefixb xs ys) eqn:Hxy.
  - inversion Hmerge; subst merged.
    split.
    + apply listz_prefixb_sound. exact Hxy.
    + apply prefix_sizes_refl.
  - destruct (listz_prefixb ys xs) eqn:Hyx; try discriminate.
    inversion Hmerge; subst merged.
    split.
    + apply prefix_sizes_refl.
    + apply listz_prefixb_sound. exact Hyx.
Qed.

Lemma infer_global_prefix_sizes_sound :
  forall sizes global,
    infer_global_prefix_sizes sizes = Some global ->
    Forall (fun local => prefix_sizes local global) sizes.
Proof.
  intros sizes.
  induction sizes as [|local sizes IH]; intros global Hinfer.
  - simpl in Hinfer.
    inversion Hinfer.
    constructor.
  - simpl in Hinfer.
    destruct (infer_global_prefix_sizes sizes)
      as [rest_global|] eqn:Hrest; try discriminate.
    pose proof
      (merge_prefix_sizes_sound local rest_global global Hinfer)
      as [Hlocal Hrest_prefix].
    constructor.
    + exact Hlocal.
    + eapply Forall_forall.
      intros sizes0 Hin.
      pose proof (IH rest_global eq_refl) as Hall.
      eapply Forall_forall in Hall; [|exact Hin].
      eapply prefix_sizes_trans; eauto.
Qed.

Fixpoint zero_on_false
    (mask: list bool) (values: list Z) : Prop :=
  match mask, values with
  | [], [] => True
  | keep :: mask', value :: values' =>
      (keep = false -> value = 0%Z) /\
      zero_on_false mask' values'
  | _, _ => False
  end.

Lemma zero_on_false_length :
  forall mask values,
    zero_on_false mask values ->
    List.length mask = List.length values.
Proof.
  intros mask.
  induction mask as [|keep mask IH]; intros values Hzero;
    destruct values as [|value values]; simpl in *; try contradiction.
  - reflexivity.
  - destruct Hzero as [_ Hzero].
    simpl.
    f_equal.
    eapply IH.
    exact Hzero.
Qed.

Lemma zero_on_false_from_nth_error :
  forall mask values,
    List.length mask = List.length values ->
    (forall n,
       nth_error mask n = Some false ->
       nth_error values n = Some 0%Z) ->
    zero_on_false mask values.
Proof.
  induction mask as [|keep mask IH]; intros values Hlen Hzero;
    destruct values as [|value values]; simpl in *; try discriminate.
  - exact I.
  - split.
    + intro Hkeep.
      specialize (Hzero O).
      simpl in Hzero.
      pose proof (Hzero (f_equal (@Some bool) Hkeep)) as Hvalue.
      inversion Hvalue.
      reflexivity.
    + eapply IH.
      * lia.
      * intros n Hmask.
        specialize (Hzero (S n)).
        simpl in Hzero.
        eapply Hzero.
        exact Hmask.
Qed.

Lemma nth_error_seq_local :
  forall start len n,
    (n < len)%nat ->
    nth_error (List.seq start len) n = Some (start + n)%nat.
Proof.
  intros start len.
  revert start.
  induction len as [|len IH]; intros start n Hlt.
  - lia.
  - destruct n as [|n].
    + simpl. f_equal. lia.
    + simpl.
      rewrite IH by lia.
      f_equal.
      lia.
Qed.

Lemma nth_error_pad_schedule_to_len_local :
  forall cols len rows n,
    (List.length rows <= len)%nat ->
    (n < len)%nat ->
    nth_error (Tiling.PL.pad_schedule_to_len cols len rows) n =
    match nth_error rows n with
    | Some row => Some row
    | None => Some (zero_schedule_row cols)
    end.
Proof.
  intros cols len rows n Hrows Hn.
  unfold Tiling.PL.pad_schedule_to_len.
  destruct (lt_dec n (List.length rows)) as [Hin|Hout].
  - rewrite nth_error_app1 by exact Hin.
    assert (Hsome : nth_error rows n <> None).
    {
      apply nth_error_Some.
      exact Hin.
    }
    destruct (nth_error rows n); [reflexivity|contradiction].
  - rewrite nth_error_app2 by lia.
    assert (Hnone : nth_error rows n = None).
    {
      apply nth_error_None.
      lia.
    }
    rewrite Hnone.
    rewrite nth_error_repeat by lia.
    unfold zero_schedule_row, Tiling.PL.zero_affine_function.
    reflexivity.
Qed.

Lemma global_semantic_schedule_mask_zero_on_false :
  forall raw_schedules raw dom_dim idx,
    In raw raw_schedules ->
    zero_on_false
      (global_semantic_schedule_mask raw_schedules)
      (affine_product
         (Tiling.PL.pad_schedule_to_len
            dom_dim (max_schedule_length raw_schedules) raw)
         idx).
Proof.
  intros raw_schedules raw dom_dim idx Hin.
  set (width := max_schedule_length raw_schedules).
  apply zero_on_false_from_nth_error.
  - unfold global_semantic_schedule_mask.
    rewrite List.map_length, seq_length.
    unfold affine_product.
    rewrite List.map_length.
    unfold Tiling.PL.pad_schedule_to_len.
    rewrite app_length, repeat_length.
    assert (Hraw : (List.length raw <= width)%nat).
    {
      subst width.
      apply In_nth_error in Hin.
      destruct Hin as [n Hnth].
      eapply max_schedule_length_ge_nth_error.
      exact Hnth.
    }
    lia.
  - intros n Hmask.
    unfold global_semantic_schedule_mask in Hmask.
    assert (Hn : (n < width)%nat).
    {
      assert
        (Hnmask :
           (n <
            List.length
              (List.map
                 (fun slot =>
                    negb
                      (semantic_schedule_slot_zerob
                         slot raw_schedules))
                 (List.seq O
                    (max_schedule_length raw_schedules))))%nat).
      {
        apply nth_error_Some.
        rewrite Hmask.
        discriminate.
      }
      rewrite List.map_length, seq_length in Hnmask.
      exact Hnmask.
    }
    pose proof (nth_error_seq_local O width n Hn) as Hseq.
    pose proof
      (Tiling.nth_error_map_some
         _ _
         (fun slot =>
            negb (semantic_schedule_slot_zerob slot raw_schedules))
         (List.seq O width) n n Hseq)
      as Hmask_expected.
    simpl in Hmask_expected.
    unfold width in Hmask_expected.
    rewrite Hmask in Hmask_expected.
    injection Hmask_expected as Hmask_slot.
    clear Hseq.
    clear Hmask.
    simpl in Hmask_slot.
    rename Hmask_slot into Hmask.
    symmetry in Hmask.
    apply Bool.negb_false_iff in Hmask.
    unfold semantic_schedule_slot_zerob in Hmask.
    apply forallb_forall with (x := raw) in Hmask; [|exact Hin].
    unfold affine_product.
    assert (Hraw_width : (List.length raw <= width)%nat).
    {
      subst width.
      apply In_nth_error in Hin.
      destruct Hin as [slot Hslot].
      eapply max_schedule_length_ge_nth_error.
      exact Hslot.
    }
    pose proof
      (nth_error_pad_schedule_to_len_local
         dom_dim width raw n Hraw_width Hn)
      as Hpad.
    destruct (nth_error raw n) as [row|] eqn:Hrow.
    + simpl in Hmask.
      assert
        (Heval :
           (dot_product (fst row) idx + snd row)%Z = 0%Z).
      {
        eapply affine_function_is_zero_eval_local.
        exact Hmask.
      }
      assert
        (Heval_linalg :
           (Linalg.dot_product (fst row) idx + snd row)%Z = 0%Z).
      {
        rewrite <-
          (Tiling.tiling_dot_product_eq_linalg_dot_product
             (fst row) idx).
        exact Heval.
      }
      pose proof
        (Tiling.nth_error_map_some
           _ _
           (fun row0 =>
              (Linalg.dot_product (fst row0) idx + snd row0)%Z)
           (Tiling.PL.pad_schedule_to_len dom_dim width raw)
           n row Hpad)
        as Hvalue.
      cbn beta iota zeta in Hvalue.
      rewrite Heval_linalg in Hvalue.
      exact Hvalue.
    + pose proof
        (Tiling.nth_error_map_some
           _ _
           (fun row0 =>
              (Linalg.dot_product (fst row0) idx + snd row0)%Z)
           (Tiling.PL.pad_schedule_to_len dom_dim width raw)
           n (zero_schedule_row dom_dim) Hpad)
        as Hvalue.
      assert
        (Hzero :
           Tiling.PL.affine_function_is_zero
             (zero_schedule_row dom_dim) = true).
      {
        unfold zero_schedule_row,
               Tiling.PL.affine_function_is_zero.
        simpl.
        rewrite repeat_zero_is_null.
        reflexivity.
      }
      pose proof
        (affine_function_is_zero_eval_local
           (zero_schedule_row dom_dim) idx Hzero)
        as Heval.
      assert
        (Heval_linalg :
           (Linalg.dot_product
              (fst (zero_schedule_row dom_dim)) idx +
            snd (zero_schedule_row dom_dim))%Z = 0%Z).
      {
        rewrite <-
          (Tiling.tiling_dot_product_eq_linalg_dot_product
             (fst (zero_schedule_row dom_dim)) idx).
        exact Heval.
      }
      cbn beta iota zeta in Hvalue.
      rewrite Heval_linalg in Hvalue.
      exact Hvalue.
Qed.

Lemma affine_product_pad_schedule_to_len :
  forall cols len rows idx,
    (List.length rows <= len)%nat ->
    affine_product
      (Tiling.PL.pad_schedule_to_len cols len rows) idx =
    affine_product rows idx ++
    repeat 0%Z (len - List.length rows).
Proof.
  intros cols len rows idx Hlen.
  unfold Tiling.PL.pad_schedule_to_len.
  rewrite affine_product_app.
  replace
    (repeat (Tiling.PL.zero_affine_function cols)
       (len - List.length rows))
    with
    (repeat (zero_schedule_row cols)
       (len - List.length rows)).
  2:{
    unfold Tiling.PL.zero_affine_function, zero_schedule_row.
    reflexivity.
  }
  rewrite affine_product_zero_schedule_rows.
  reflexivity.
Qed.

Lemma combine_app_exact_local :
  forall (A B: Type)
         (xs1 xs2: list A) (ys1 ys2: list B),
    List.length xs1 = List.length ys1 ->
    combine (xs1 ++ xs2) (ys1 ++ ys2) =
    combine xs1 ys1 ++ combine xs2 ys2.
Proof.
  intros A B xs1.
  induction xs1 as [|x xs1 IH]; intros xs2 ys1 ys2 Hlen.
  - destruct ys1; simpl in *; [reflexivity|discriminate].
  - destruct ys1 as [|y ys1]; simpl in *; [discriminate|].
    f_equal.
    eapply IH.
    lia.
Qed.

Lemma map_div_combine_repeat_zero :
  forall sizes,
    List.map
      (fun '(v, sz) => Z.div v sz)
      (combine (repeat 0%Z (List.length sizes)) sizes) =
    repeat 0%Z (List.length sizes).
Proof.
  induction sizes as [|size sizes IH]; simpl.
  - reflexivity.
  - destruct (Z.eq_dec size 0%Z) as [Heq|Hneq].
    + subst size. simpl. f_equal. exact IH.
    + rewrite Z.div_0_l by exact Hneq.
      f_equal.
      exact IH.
Qed.

Lemma prefix_sizes_decompose :
  forall local global,
    prefix_sizes local global ->
    exists extra,
      global = local ++ extra /\
      List.length extra =
        (List.length global - List.length local)%nat.
Proof.
  intros local global [Hlen Hprefix].
  exists (skipn (List.length local) global).
  split.
  - rewrite <- Hprefix at 1.
    symmetry.
    apply firstn_skipn.
  - rewrite skipn_length.
    reflexivity.
Qed.

Lemma tile_values_pad_prefix :
  forall values local_sizes global_sizes,
    List.length values = List.length local_sizes ->
    prefix_sizes local_sizes global_sizes ->
    List.map
      (fun '(v, sz) => Z.div v sz)
      (combine
         (values ++
          repeat 0%Z
            (List.length global_sizes - List.length values))
         global_sizes) =
    List.map
      (fun '(v, sz) => Z.div v sz)
      (combine values local_sizes) ++
    repeat 0%Z
      (List.length global_sizes - List.length local_sizes).
Proof.
  intros values local_sizes global_sizes Hvalues Hprefix.
  destruct (prefix_sizes_decompose _ _ Hprefix)
    as [extra [Hglobal Hextra]].
  subst global_sizes.
  rewrite !app_length.
  replace
    (List.length local_sizes + List.length extra -
     List.length values)%nat
    with (List.length extra) by lia.
  replace
    (List.length local_sizes + List.length extra -
     List.length local_sizes)%nat
    with (List.length extra) by lia.
  rewrite combine_app_exact_local by exact Hvalues.
  rewrite List.map_app.
  rewrite map_div_combine_repeat_zero.
  reflexivity.
Qed.

Lemma infer_global_prefix_sizes_positive :
  forall sizes global,
    infer_global_prefix_sizes sizes = Some global ->
    Forall (fun local => Forall (fun size => (0 < size)%Z) local)
      sizes ->
    Forall (fun size => (0 < size)%Z) global.
Proof.
  intros sizes.
  induction sizes as [|local sizes IH]; intros global Hinfer Hpositive.
  - simpl in Hinfer.
    inversion Hinfer; constructor.
  - inversion Hpositive as
      [|local0 sizes0 Hlocal Hrest]; subst local0 sizes0.
    simpl in Hinfer.
    destruct (infer_global_prefix_sizes sizes)
      as [rest_global|] eqn:Hrest_global; try discriminate.
    unfold merge_prefix_sizes in Hinfer.
    destruct (listz_prefixb local rest_global) eqn:Hlocal_prefix.
    + inversion Hinfer; subst global.
      eapply IH; eauto.
    + destruct (listz_prefixb rest_global local);
        try discriminate.
      inversion Hinfer; subst global.
      exact Hlocal.
Qed.

Lemma parse_ordinary_semantic_data_positive :
  forall ws data,
    parse_ordinary_semantic_data ws = Some data ->
    Forall
      (fun w =>
         Forall (fun link => (0 < tl_tile_size link)%Z)
           (stw_links w))
      ws ->
    Forall
      (fun entry =>
         Forall (fun size => (0 < size)%Z) (snd entry))
      data.
Proof.
  intros ws.
  induction ws as [|w ws IH]; intros data Hparse Hpositive.
  - simpl in Hparse.
    inversion Hparse.
    constructor.
  - inversion Hpositive as [|w0 ws0 Hw Hws]; subst w0 ws0.
    simpl in Hparse.
    destruct (schedule_rows_of_links w) as [rows|] eqn:Hrows;
      try discriminate.
    destruct (parse_ordinary_semantic_data ws)
      as [rest|] eqn:Hrest; try discriminate.
    inversion Hparse; subst data.
    constructor.
    + unfold tile_sizes_of_witness.
      eapply positive_tile_sizes_map.
      exact Hw.
    + eapply IH; eauto.
Qed.

Lemma semantic_ordinary_target_schedule_eval :
  forall env_size global_width semantic_rows w envv added point,
    List.length envv = env_size ->
    List.length added = List.length (stw_links w) ->
    List.length point = stw_point_dim w ->
    (List.length (stw_links w) <= global_width)%nat ->
    affine_product
      (semantic_ordinary_target_schedule
         env_size global_width semantic_rows w)
      (envv ++ added ++ point) =
    added ++
    repeat 0%Z
      (global_width - List.length (stw_links w)) ++
    affine_product semantic_rows (envv ++ point).
Proof.
  intros env_size global_width semantic_rows w envv added point
         Henv Hadded Hpoint Hwidth.
  unfold semantic_ordinary_target_schedule.
  rewrite affine_product_app, affine_product_app.
  rewrite affine_product_identity_affine_rows_from.
  2:{ lia. }
  2:{ rewrite !app_length. lia. }
  rewrite affine_product_zero_schedule_rows.
  rewrite Tiling.lift_affine_function_after_env_eval.
  2:{ exact Henv. }
  2:{ exact Hadded. }
  rewrite <- Henv.
  replace
    (skipn (List.length envv) (envv ++ added ++ point))
    with (added ++ point).
  2:{
    rewrite skipn_app_le by lia.
    replace (List.length envv - List.length envv)%nat with O by lia.
    reflexivity.
  }
  rewrite firstn_app.
  replace
    (List.length (stw_links w) - List.length added)%nat
    with O by lia.
  rewrite <- Hadded.
  rewrite firstn_all.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma semantic_band_value_of_nth_error :
  forall dom_dim dim rows idx value,
    nth_error (affine_product rows idx) dim = Some value ->
    semantic_band_value dom_dim dim rows idx = value.
Proof.
  intros dom_dim dim rows idx value Hvalue.
  unfold affine_product in Hvalue.
  apply Base.nth_error_map_inv in Hvalue.
  destruct Hvalue as [row [Hrow Hvalue]].
  unfold semantic_band_value, semantic_band_row.
  rewrite Hrow.
  symmetry.
  exact Hvalue.
Qed.

Lemma select_by_mask_eq_reflect :
  forall mask xs ys,
    zero_on_false mask xs ->
    zero_on_false mask ys ->
    select_by_mask mask xs = select_by_mask mask ys ->
    xs = ys.
Proof.
  intros mask.
  induction mask as [|keep mask IH]; intros xs ys Hzx Hzy Hselect;
    destruct xs as [|x xs]; destruct ys as [|y ys];
    simpl in *; try contradiction; try reflexivity.
  destruct Hzx as [Hzx_head Hzx].
  destruct Hzy as [Hzy_head Hzy].
  destruct keep.
  - simpl in Hselect.
    inversion Hselect.
    f_equal.
    eapply IH; eauto.
  - assert (Hx : x = 0%Z) by (apply Hzx_head; reflexivity).
    assert (Hy : y = 0%Z) by (apply Hzy_head; reflexivity).
    subst x y.
    f_equal.
    eapply IH; eauto.
Qed.

Lemma select_by_mask_le_reflect :
  forall mask xs ys,
    zero_on_false mask xs ->
    zero_on_false mask ys ->
    listz_pointwise_le
      (select_by_mask mask xs)
      (select_by_mask mask ys) ->
    listz_pointwise_le xs ys.
Proof.
  intros mask.
  induction mask as [|keep mask IH]; intros xs ys Hzx Hzy Hselect;
    destruct xs as [|x xs]; destruct ys as [|y ys];
    simpl in *; try contradiction.
  - constructor.
  - destruct Hzx as [Hzx_head Hzx].
    destruct Hzy as [Hzy_head Hzy].
    destruct keep.
    + inversion Hselect; subst.
      constructor.
      * assumption.
      * eapply IH; eauto.
    + assert (Hx : x = 0%Z) by (apply Hzx_head; reflexivity).
      assert (Hy : y = 0%Z) by (apply Hzy_head; reflexivity).
      subst x y.
      constructor; [lia|].
      eapply IH; eauto.
Qed.

Definition semantic_rows_reversal_bridge
    (envv: list Z)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (rows: list Schedule) : Prop :=
  let pis :=
    Tiling.compose_tiling_pinstrs_ext_from_after
      (List.length envv) before_pis after_pis ws in
  forall flat ip1 ip2,
    Tiling.PL.flatten_instrs_ext envv pis flat ->
    In ip1 flat ->
    In ip2 flat ->
    Tiling.PL.instr_point_ext_old_sched_lt ip1 ip2 ->
    Tiling.PL.instr_point_ext_new_sched_ge ip1 ip2 ->
    exists pi1 pi2 rows1 rows2 dim,
      nth_error pis (Tiling.PL.ip_nth_ext ip1) = Some pi1 /\
      nth_error pis (Tiling.PL.ip_nth_ext ip2) = Some pi2 /\
      nth_error rows (Tiling.PL.ip_nth_ext ip1) = Some rows1 /\
      nth_error rows (Tiling.PL.ip_nth_ext ip2) = Some rows2 /\
      (dim < max_schedule_length rows)%nat /\
      (semantic_band_value
         (List.length envv + Tiling.PL.pi_depth_ext pi1)
         dim rows1 (Tiling.PL.ip_index_ext ip1) >
       semantic_band_value
         (List.length envv + Tiling.PL.pi_depth_ext pi2)
         dim rows2 (Tiling.PL.ip_index_ext ip2))%Z.

Lemma semantic_componentwise_permutable_implies_reordering_safe :
  forall envv before_pis after_pis ws rows,
    pinstr_list_semantic_componentwise_permutable
      envv
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length envv) before_pis after_pis ws)
      rows ->
    semantic_rows_reversal_bridge
      envv before_pis after_pis ws rows ->
    pprog_tiling_reordering_safe
      envv before_pis after_pis ws [].
Proof.
  intros envv before_pis after_pis ws rows Hcomponents Hbridge.
  unfold pprog_tiling_reordering_safe,
         pprog_permutable_tiling_bands.
  intros flat ip1 ip2 Hflat Hin1 Hin2 Hold Hnew.
  destruct
    (Hbridge flat ip1 ip2 Hflat Hin1 Hin2 Hold Hnew)
    as [pi1 [pi2 [rows1 [rows2 [dim
         [Hpi1 [Hpi2 [Hrows1 [Hrows2 [Hdim Hdecrease]]]]]]]]]].
  eapply
    (Hcomponents flat ip1 ip2 pi1 pi2 rows1 rows2 dim);
    eauto.
Qed.

Lemma parse_ordinary_semantic_data_nth_error :
  forall ws data n w rows sizes,
    parse_ordinary_semantic_data ws = Some data ->
    nth_error ws n = Some w ->
    nth_error data n = Some (rows, sizes) ->
    schedule_rows_of_links w = Some rows /\
    tile_sizes_of_witness w = sizes.
Proof.
  intros ws.
  induction ws as [|w0 ws IH];
    intros data n w rows sizes Hparse Hw Hdata.
  - destruct n; discriminate.
  - simpl in Hparse.
    destruct (schedule_rows_of_links w0) as [rows0|] eqn:Hrows0;
      try discriminate.
    destruct (parse_ordinary_semantic_data ws) as [rest|] eqn:Hrest;
      try discriminate.
    inversion Hparse; subst data; clear Hparse.
    destruct n as [|n].
    + simpl in Hw, Hdata.
      inversion Hw; inversion Hdata; subst.
      split; [exact Hrows0|reflexivity].
    + simpl in Hw, Hdata.
      eapply IH; eauto using eq_refl.
Qed.

Lemma parse_ordinary_semantic_data_length :
  forall ws data,
    parse_ordinary_semantic_data ws = Some data ->
    List.length data = List.length ws.
Proof.
  intros ws.
  induction ws as [|w ws IH]; intros data Hparse.
  - simpl in Hparse.
    inversion Hparse.
    reflexivity.
  - simpl in Hparse.
    destruct (schedule_rows_of_links w) as [rows|] eqn:Hrows;
      try discriminate.
    destruct (parse_ordinary_semantic_data ws)
      as [rest|] eqn:Hrest; try discriminate.
    inversion Hparse; subst data.
    simpl.
    f_equal.
    eapply IH.
    reflexivity.
Qed.

Lemma compact_semantic_schedules_nth_error :
  forall env_size before_pis raw_schedules mask semantic_rows
         n before_pi raw rows,
    compact_semantic_schedules
      env_size before_pis raw_schedules mask = Some semantic_rows ->
    nth_error before_pis n = Some before_pi ->
    nth_error raw_schedules n = Some raw ->
    nth_error semantic_rows n = Some rows ->
    rows =
      compact_semantic_schedule
        (env_size + Tiling.PL.pi_depth before_pi)%nat mask raw.
Proof.
  intros env_size before_pis.
  induction before_pis as [|before0 before_pis IH];
    intros raw_schedules mask semantic_rows n before_pi raw rows
           Hcompact Hbefore Hraw Hrows.
  - destruct n; discriminate.
  - destruct raw_schedules as [|raw0 raw_schedules]; simpl in Hcompact;
      try discriminate.
    destruct
      (compact_semantic_schedules
         env_size before_pis raw_schedules mask)
      as [rest|] eqn:Hrest; try discriminate.
    inversion Hcompact; subst semantic_rows; clear Hcompact.
    destruct n as [|n].
    + simpl in Hbefore, Hraw, Hrows.
      inversion Hbefore; inversion Hraw; inversion Hrows; subst.
      reflexivity.
    + simpl in Hbefore, Hraw, Hrows.
      eapply IH; eauto.
Qed.


Lemma lift_semantic_schedules_for_tiling_nth_error :
  forall env_size ws semantic_rows lifted_rows n w rows lifted,
    lift_semantic_schedules_for_tiling env_size ws semantic_rows =
      Some lifted_rows ->
    nth_error ws n = Some w ->
    nth_error semantic_rows n = Some rows ->
    nth_error lifted_rows n = Some lifted ->
    lifted =
      Tiling.lift_schedule_after_env
        (List.length (stw_links w)) env_size rows.
Proof.
  intros env_size ws.
  induction ws as [|w0 ws IH];
    intros semantic_rows lifted_rows n w rows lifted
           Hlift Hw Hrows Hlifted.
  - destruct n; discriminate.
  - destruct semantic_rows as [|rows0 semantic_rows]; simpl in Hlift;
      try discriminate.
    destruct
      (lift_semantic_schedules_for_tiling env_size ws semantic_rows)
      as [rest|] eqn:Hrest; try discriminate.
    inversion Hlift; subst lifted_rows; clear Hlift.
    destruct n as [|n].
    + simpl in Hw, Hrows, Hlifted.
      inversion Hw; inversion Hrows; inversion Hlifted; subst.
      reflexivity.
    + simpl in Hw, Hrows, Hlifted.
      eapply IH; eauto.
Qed.

Lemma ordinary_semantic_schedules_match_nth_error :
  forall env_size global_width before_pis after_pis ws semantic_rows
         n before_pi after_pi w rows,
    ordinary_semantic_schedules_match
      env_size global_width before_pis after_pis ws semantic_rows ->
    nth_error before_pis n = Some before_pi ->
    nth_error after_pis n = Some after_pi ->
    nth_error ws n = Some w ->
    nth_error semantic_rows n = Some rows ->
    schedule_matches_with_symmetric_trailing_zero_padding
      rows (Tiling.PL.pi_schedule before_pi) /\
    schedule_matches_with_symmetric_trailing_zero_padding
      (semantic_ordinary_target_schedule
         env_size global_width rows w)
      (Tiling.PL.pi_schedule after_pi).
Proof.
  intros env_size global_width before_pis after_pis ws semantic_rows
         n.
  revert before_pis after_pis ws semantic_rows.
  induction n as [|n IH];
    intros before_pis after_pis ws semantic_rows
           before_pi after_pi w rows Hmatch Hbefore Hafter Hw Hrows;
    inversion Hmatch; subst; simpl in *; try discriminate.
  - inversion Hbefore; inversion Hafter; inversion Hw; inversion Hrows;
      subst.
    split; assumption.
  - eapply IH; eauto.
Qed.

(** Proof roadmap for the ordinary semantic bridge:

    1. recover the source instruction, target instruction, and tiling witness
       for each endpoint of the reversed pair;
    2. reconstruct the compact semantic rows and their lifted rows;
    3. rewrite the old and target timestamps into a common prefix, tile
       prefix, point band, and suffix;
    4. use positivity of tile sizes to show that componentwise
       nondecreasing source bands could not reverse the target order;
    5. return the decreasing semantic row required by
       [semantic_rows_reversal_bridge].

    The endpoint setup is intentionally symmetric.  The argument after the
    timestamp rewrites is the mathematical core of the proof. *)
Lemma ordinary_semantic_band_shape_reversal_bridge :
  forall before_pis before_ctxt before_vars after_pis ws
         shape lifted_rows envv,
    List.length before_ctxt = List.length envv ->
    TilingCheck.check_pprog_tiling_sourceb
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars) ws = true ->
    ordinary_semantic_band_shape_property_with_witness
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars) ws shape ->
    lift_semantic_schedules_for_tiling
      (List.length before_ctxt) ws (osbs_rows shape) =
      Some lifted_rows ->
    semantic_rows_reversal_bridge
      envv before_pis after_pis ws lifted_rows.
Proof.
  (* Stage 1: unpack the recognized layout and derive global witness facts. *)
  intros before_pis before_ctxt before_vars after_pis ws
         shape lifted_rows envv Hlen_env Hsource Hshape Hlift.
  unfold ordinary_semantic_band_shape_property_with_witness in Hshape.
  cbn in Hshape.
  destruct Hshape as
    [_ [_ [data
      [Hdata [Hglobal_sizes [Hmask
      [Hcompact [_ [Hglobal_width Hschedules]]]]]]]]].
  pose proof
    (TilingCheck.check_pprog_tiling_sourceb_sound
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars) ws Hsource)
    as [Hprog [_ [Hwf_ws [Hpositive_ws Hdepths]]]].
  assert
    (Hwf_ws_env :
       Forall
         (Tiling.wf_statement_tiling_witness_with_param_dim
            (List.length envv))
         ws).
  {
    rewrite <- Hlen_env.
    exact Hwf_ws.
  }
  assert
    (Hglobal_prefix :
       Forall
         (fun local => prefix_sizes local (osbs_global_sizes shape))
         (List.map snd data)).
  {
    eapply infer_global_prefix_sizes_sound.
    exact Hglobal_sizes.
  }
  assert
    (Hglobal_positive :
       Forall (fun size => (0 < size)%Z)
         (osbs_global_sizes shape)).
  {
    eapply infer_global_prefix_sizes_positive.
    - exact Hglobal_sizes.
    - pose proof
        (parse_ordinary_semantic_data_positive
           ws data Hdata Hpositive_ws)
        as Hdata_positive.
      apply Forall_forall.
      intros local Hin.
      apply in_map_iff in Hin.
      destruct Hin as [entry [Heq Hin]].
      subst local.
      eapply Forall_forall in Hdata_positive; eauto.
  }
  destruct
    (lift_semantic_schedules_for_tiling_length
       (List.length before_ctxt) ws (osbs_rows shape)
       lifted_rows Hlift)
    as [Hlifted_len Hsemantic_rows_len].
  assert (Hdata_len : List.length data = List.length ws).
  {
    eapply parse_ordinary_semantic_data_length.
    exact Hdata.
  }
  (* Stage 2: choose an arbitrary reversed pair and recover its two source
     statements, target statements, witnesses, and semantic schedule rows. *)
  unfold semantic_rows_reversal_bridge.
  intros flat ip1 ip2 Hflat Hin1 Hin2 Hold Hnew.
  destruct
    (composed_point_pair_facts_of_members
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       ws envv flat ip1 ip2
       Hprog Hwf_ws_env Hpositive_ws Hdepths Hflat Hin1 Hin2)
    as [Hpoint1 Hpoint2].
  unfold composed_point_facts in Hpoint1, Hpoint2.
  destruct Hpoint1 as [before_pi1 [after_pi1 [w1
    [Hbefore1 [Hafter1 [Hw1
    [Hwf_stmt1 [Hpositive1 [Hpoint_depth1
    [Hpref1 [Hbel1 Hidx_len1]]]]]]]]]]].
  destruct Hpoint2 as [before_pi2 [after_pi2 [w2
    [Hbefore2 [Hafter2 [Hw2
    [Hwf_stmt2 [Hpositive2 [Hpoint_depth2
    [Hpref2 [Hbel2 Hidx_len2]]]]]]]]]]].
  assert
    (Hn1 : (Tiling.PL.ip_nth_ext ip1 < List.length ws)%nat).
  {
    apply nth_error_Some.
    rewrite Hw1.
    discriminate.
  }
  assert
    (Hn2 : (Tiling.PL.ip_nth_ext ip2 < List.length ws)%nat).
  {
    apply nth_error_Some.
    rewrite Hw2.
    discriminate.
  }
  destruct
    (nth_error data (Tiling.PL.ip_nth_ext ip1))
    as [[raw1 local_sizes1]|] eqn:Hdata1.
  2:{
    exfalso.
    apply nth_error_None in Hdata1.
    lia.
  }
  destruct
    (nth_error data (Tiling.PL.ip_nth_ext ip2))
    as [[raw2 local_sizes2]|] eqn:Hdata2.
  2:{
    exfalso.
    apply nth_error_None in Hdata2.
    lia.
  }
  destruct
    (parse_ordinary_semantic_data_nth_error
       ws data (Tiling.PL.ip_nth_ext ip1)
       w1 raw1 local_sizes1 Hdata Hw1 Hdata1)
    as [Hraw1 Hlocal_sizes1].
  destruct
    (parse_ordinary_semantic_data_nth_error
       ws data (Tiling.PL.ip_nth_ext ip2)
       w2 raw2 local_sizes2 Hdata Hw2 Hdata2)
    as [Hraw2 Hlocal_sizes2].
  assert
    (Hraw_map1 :
       nth_error (List.map fst data) (Tiling.PL.ip_nth_ext ip1) =
       Some raw1).
  {
    pose proof
      (Tiling.nth_error_map_some
         _ _ (@fst Schedule (list Z)) data
         (Tiling.PL.ip_nth_ext ip1)
         (raw1, local_sizes1) Hdata1)
      as Hnth.
    cbn in Hnth.
    exact Hnth.
  }
  assert
    (Hraw_map2 :
       nth_error (List.map fst data) (Tiling.PL.ip_nth_ext ip2) =
       Some raw2).
  {
    pose proof
      (Tiling.nth_error_map_some
         _ _ (@fst Schedule (list Z)) data
         (Tiling.PL.ip_nth_ext ip2)
         (raw2, local_sizes2) Hdata2)
      as Hnth.
    cbn in Hnth.
    exact Hnth.
  }
  assert
    (Hsizes_map1 :
       nth_error (List.map snd data) (Tiling.PL.ip_nth_ext ip1) =
       Some local_sizes1).
  {
    pose proof
      (Tiling.nth_error_map_some
         _ _ (@snd Schedule (list Z)) data
         (Tiling.PL.ip_nth_ext ip1)
         (raw1, local_sizes1) Hdata1)
      as Hnth.
    cbn in Hnth.
    exact Hnth.
  }
  assert
    (Hsizes_map2 :
       nth_error (List.map snd data) (Tiling.PL.ip_nth_ext ip2) =
       Some local_sizes2).
  {
    pose proof
      (Tiling.nth_error_map_some
         _ _ (@snd Schedule (list Z)) data
         (Tiling.PL.ip_nth_ext ip2)
         (raw2, local_sizes2) Hdata2)
      as Hnth.
    cbn in Hnth.
    exact Hnth.
  }
  pose proof
    (Tiling.Forall_nth_error
       _ _
       (List.map snd data) (Tiling.PL.ip_nth_ext ip1)
       local_sizes1 Hglobal_prefix Hsizes_map1)
    as Hlocal_prefix1.
  pose proof
    (Tiling.Forall_nth_error
       _ _
       (List.map snd data) (Tiling.PL.ip_nth_ext ip2)
       local_sizes2 Hglobal_prefix Hsizes_map2)
    as Hlocal_prefix2.
  destruct
    (nth_error (osbs_rows shape) (Tiling.PL.ip_nth_ext ip1))
    as [semantic_rows1|] eqn:Hsemantic_rows1.
  2:{
    exfalso.
    apply nth_error_None in Hsemantic_rows1.
    lia.
  }
  destruct
    (nth_error (osbs_rows shape) (Tiling.PL.ip_nth_ext ip2))
    as [semantic_rows2|] eqn:Hsemantic_rows2.
  2:{
    exfalso.
    apply nth_error_None in Hsemantic_rows2.
    lia.
  }
  destruct
    (nth_error lifted_rows (Tiling.PL.ip_nth_ext ip1))
    as [lifted1|] eqn:Hlifted1.
  2:{
    exfalso.
    apply nth_error_None in Hlifted1.
    lia.
  }
  destruct
    (nth_error lifted_rows (Tiling.PL.ip_nth_ext ip2))
    as [lifted2|] eqn:Hlifted2.
  2:{
    exfalso.
    apply nth_error_None in Hlifted2.
    lia.
  }
  pose proof
    (compact_semantic_schedules_nth_error
       (List.length before_ctxt) before_pis (List.map fst data)
       (osbs_mask shape) (osbs_rows shape)
       (Tiling.PL.ip_nth_ext ip1) before_pi1 raw1 semantic_rows1
       Hcompact Hbefore1 Hraw_map1 Hsemantic_rows1)
    as Hsemantic_rows_def1.
  pose proof
    (compact_semantic_schedules_nth_error
       (List.length before_ctxt) before_pis (List.map fst data)
       (osbs_mask shape) (osbs_rows shape)
       (Tiling.PL.ip_nth_ext ip2) before_pi2 raw2 semantic_rows2
       Hcompact Hbefore2 Hraw_map2 Hsemantic_rows2)
    as Hsemantic_rows_def2.
  pose proof
    (lift_semantic_schedules_for_tiling_nth_error
       (List.length before_ctxt) ws (osbs_rows shape) lifted_rows
       (Tiling.PL.ip_nth_ext ip1) w1 semantic_rows1 lifted1
       Hlift Hw1 Hsemantic_rows1 Hlifted1)
    as Hlifted_def1.
  pose proof
    (lift_semantic_schedules_for_tiling_nth_error
       (List.length before_ctxt) ws (osbs_rows shape) lifted_rows
       (Tiling.PL.ip_nth_ext ip2) w2 semantic_rows2 lifted2
       Hlift Hw2 Hsemantic_rows2 Hlifted2)
    as Hlifted_def2.
  destruct
    (ordinary_semantic_schedules_match_nth_error
       (List.length before_ctxt)
       (List.length (osbs_mask shape))
       before_pis after_pis ws (osbs_rows shape)
       (Tiling.PL.ip_nth_ext ip1)
       before_pi1 after_pi1 w1 semantic_rows1
       Hschedules Hbefore1 Hafter1 Hw1 Hsemantic_rows1)
    as [Hbefore_match1 Hafter_match1].
  destruct
    (ordinary_semantic_schedules_match_nth_error
       (List.length before_ctxt)
       (List.length (osbs_mask shape))
       before_pis after_pis ws (osbs_rows shape)
       (Tiling.PL.ip_nth_ext ip2)
       before_pi2 after_pi2 w2 semantic_rows2
       Hschedules Hbefore2 Hafter2 Hw2 Hsemantic_rows2)
    as [Hbefore_match2 Hafter_match2].
  pose proof
    (Tiling.nth_error_compose_tiling_pinstrs_ext_from_after
       (List.length envv) before_pis after_pis ws
       (Tiling.PL.ip_nth_ext ip1)
       before_pi1 after_pi1 w1 Hbefore1 Hafter1 Hw1)
    as Hcomposed1.
  pose proof
    (Tiling.nth_error_compose_tiling_pinstrs_ext_from_after
       (List.length envv) before_pis after_pis ws
       (Tiling.PL.ip_nth_ext ip2)
       before_pi2 after_pi2 w2 Hbefore2 Hafter2 Hw2)
    as Hcomposed2.
  pose proof
    (Tiling.tiling_rel_pprog_structure_source_nth
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       (List.map Tiling.compiled_pinstr_tiling_witness ws)
       (Tiling.PL.ip_nth_ext ip1)
       before_pi1 after_pi1
       (Tiling.compiled_pinstr_tiling_witness w1)
       Hprog Hbefore1 Hafter1
       (Tiling.nth_error_map_some
          _ _ Tiling.compiled_pinstr_tiling_witness
          ws (Tiling.PL.ip_nth_ext ip1) w1 Hw1))
    as Hstmt1.
  pose proof
    (Tiling.tiling_rel_pprog_structure_source_nth
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       (List.map Tiling.compiled_pinstr_tiling_witness ws)
       (Tiling.PL.ip_nth_ext ip2)
       before_pi2 after_pi2
       (Tiling.compiled_pinstr_tiling_witness w2)
       Hprog Hbefore2 Hafter2
       (Tiling.nth_error_map_some
          _ _ Tiling.compiled_pinstr_tiling_witness
          ws (Tiling.PL.ip_nth_ext ip2) w2 Hw2))
    as Hstmt2.
  pose proof
    (tiling_rel_pinstr_structure_source_after_matches
       (List.length before_ctxt) before_pi1 after_pi1 w1
       Hstmt1 Hpoint_depth1)
    as Hafter_wit1.
  pose proof
    (tiling_rel_pinstr_structure_source_after_matches
       (List.length before_ctxt) before_pi2 after_pi2 w2
       Hstmt2 Hpoint_depth2)
    as Hafter_wit2.
  destruct Hafter_wit1 as [Hafter_pw1 Hafter_wit_depth1].
  destruct Hafter_wit2 as [Hafter_pw2 Hafter_wit_depth2].
  assert
    (Hafter_depth1 :
       Tiling.PL.pi_depth after_pi1 =
       (Tiling.PL.pi_depth before_pi1 +
        List.length (stw_links w1))%nat).
  {
    unfold Tiling.tiling_rel_pinstr_structure_source in Hstmt1.
    destruct Hstmt1 as [_ [Hdepth _]].
    exact Hdepth.
  }
  assert
    (Hafter_depth2 :
       Tiling.PL.pi_depth after_pi2 =
       (Tiling.PL.pi_depth before_pi2 +
        List.length (stw_links w2))%nat).
  {
    unfold Tiling.tiling_rel_pinstr_structure_source in Hstmt2.
    destruct Hstmt2 as [_ [Hdepth _]].
    exact Hdepth.
  }
  (* Stage 3: split each target point into parameters, added tile coordinates,
     and the represented source point, then evaluate both schedules. *)
  set
    (added1 :=
       Tiling.tiled_added_part
         (List.length envv) (List.length (stw_links w1))
         (Tiling.PL.ip_index_ext ip1)).
  set
    (point1 :=
       Tiling.tiled_point_part
         (List.length envv) (List.length (stw_links w1))
         (Tiling.PL.ip_index_ext ip1)).
  set
    (added2 :=
       Tiling.tiled_added_part
         (List.length envv) (List.length (stw_links w2))
         (Tiling.PL.ip_index_ext ip2)).
  set
    (point2 :=
       Tiling.tiled_point_part
         (List.length envv) (List.length (stw_links w2))
         (Tiling.PL.ip_index_ext ip2)).
  assert (Hadded_len1 : List.length added1 = List.length (stw_links w1)).
  {
    subst added1.
    eapply Tiling.tiled_added_part_length
      with (point_dim := stw_point_dim w1).
    rewrite Hidx_len1, Hafter_depth1, <- Hpoint_depth1.
    lia.
  }
  assert (Hadded_len2 : List.length added2 = List.length (stw_links w2)).
  {
    subst added2.
    eapply Tiling.tiled_added_part_length
      with (point_dim := stw_point_dim w2).
    rewrite Hidx_len2, Hafter_depth2, <- Hpoint_depth2.
    lia.
  }
  assert (Hpoint_len1 : List.length point1 = stw_point_dim w1).
  {
    subst point1.
    eapply Tiling.tiled_point_part_length
      with (added_dims := List.length (stw_links w1)).
    rewrite Hidx_len1, Hafter_depth1, <- Hpoint_depth1.
    lia.
  }
  assert (Hpoint_len2 : List.length point2 = stw_point_dim w2).
  {
    subst point2.
    eapply Tiling.tiled_point_part_length
      with (added_dims := List.length (stw_links w2)).
    rewrite Hidx_len2, Hafter_depth2, <- Hpoint_depth2.
    lia.
  }
  assert
    (Hidx_split1 :
       Tiling.PL.ip_index_ext ip1 = envv ++ added1 ++ point1).
  {
    subst added1 point1.
    transitivity
      (firstn (List.length envv) (Tiling.PL.ip_index_ext ip1) ++
       Tiling.tiled_added_part
         (List.length envv) (List.length (stw_links w1))
         (Tiling.PL.ip_index_ext ip1) ++
       Tiling.tiled_point_part
         (List.length envv) (List.length (stw_links w1))
         (Tiling.PL.ip_index_ext ip1)).
    - apply Tiling.tiled_index_split.
    - rewrite Hpref1.
      reflexivity.
  }
  assert
    (Hidx_split2 :
       Tiling.PL.ip_index_ext ip2 = envv ++ added2 ++ point2).
  {
    subst added2 point2.
    transitivity
      (firstn (List.length envv) (Tiling.PL.ip_index_ext ip2) ++
       Tiling.tiled_added_part
         (List.length envv) (List.length (stw_links w2))
         (Tiling.PL.ip_index_ext ip2) ++
       Tiling.tiled_point_part
         (List.length envv) (List.length (stw_links w2))
         (Tiling.PL.ip_index_ext ip2)).
    - apply Tiling.tiled_index_split.
    - rewrite Hpref2.
      reflexivity.
  }
  unfold Tiling.compose_tiling_pinstr_ext in Hbel1, Hbel2.
  destruct Hbel1 as
    [Hafter_dom1 [_ [_ [Hts11 [Hts21 [_ _]]]]]].
  destruct Hbel2 as
    [Hafter_dom2 [_ [_ [Hts12 [Hts22 [_ _]]]]]].
  assert
    (Hts11_old :
       Tiling.PL.ip_time_stamp1_ext ip1 =
       affine_product (Tiling.PL.pi_schedule before_pi1)
         (envv ++ point1)).
  {
    rewrite Hts11.
    cbn [Tiling.compose_tiling_pinstr_ext].
    rewrite Hidx_split1.
    unfold Tiling.lift_schedule_after_env.
    eapply Tiling.lift_affine_function_after_env_eval.
    - reflexivity.
    - exact Hadded_len1.
  }
  assert
    (Hts12_old :
       Tiling.PL.ip_time_stamp1_ext ip2 =
       affine_product (Tiling.PL.pi_schedule before_pi2)
         (envv ++ point2)).
  {
    rewrite Hts12.
    cbn [Tiling.compose_tiling_pinstr_ext].
    rewrite Hidx_split2.
    unfold Tiling.lift_schedule_after_env.
    eapply Tiling.lift_affine_function_after_env_eval.
    - reflexivity.
    - exact Hadded_len2.
  }
  assert
    (Hts21_after :
       Tiling.PL.ip_time_stamp2_ext ip1 =
       affine_product (Tiling.PL.pi_schedule after_pi1)
         (Tiling.PL.ip_index_ext ip1)).
  {
    rewrite Hts21.
    cbn [Tiling.compose_tiling_pinstr_ext].
    reflexivity.
  }
  assert
    (Hts22_after :
       Tiling.PL.ip_time_stamp2_ext ip2 =
       affine_product (Tiling.PL.pi_schedule after_pi2)
         (Tiling.PL.ip_index_ext ip2)).
  {
    rewrite Hts22.
    cbn [Tiling.compose_tiling_pinstr_ext].
    reflexivity.
  }
  assert
    (Hstmt1_env :
       Tiling.tiling_rel_pinstr_structure_source
         (List.length envv) before_pi1 after_pi1
         (Tiling.compiled_pinstr_tiling_witness w1)).
  {
    rewrite <- Hlen_env.
    exact Hstmt1.
  }
  assert
    (Hstmt2_env :
       Tiling.tiling_rel_pinstr_structure_source
         (List.length envv) before_pi2 after_pi2
         (Tiling.compiled_pinstr_tiling_witness w2)).
  {
    rewrite <- Hlen_env.
    exact Hstmt2.
  }
  destruct Hwf_stmt1 as [Hwf_stmt1 Hparams1].
  destruct Hwf_stmt2 as [Hwf_stmt2 Hparams2].
  assert
    (Hadded_eq1 :
       added1 = eval_tile_links [] point1 envv (stw_links w1)).
  {
    pose proof
      (Tiling.tiling_rel_pinstr_structure_source_domain_complete
         envv before_pi1 after_pi1
         (Tiling.compiled_pinstr_tiling_witness w1)
         added1 point1 Hstmt1_env
         (Tiling.wf_compiled_pinstr_tiling_witness w1)
         (Tiling.compiled_pinstr_tiling_witness_matches w1)
         Hadded_len1 Hpoint_len1
         (conj Hwf_stmt1 Hparams1) Hpositive1)
      as Hcomplete.
    rewrite Hidx_split1 in Hafter_dom1.
    specialize (Hcomplete Hafter_dom1).
    tauto.
  }
  assert
    (Hadded_eq2 :
       added2 = eval_tile_links [] point2 envv (stw_links w2)).
  {
    pose proof
      (Tiling.tiling_rel_pinstr_structure_source_domain_complete
         envv before_pi2 after_pi2
         (Tiling.compiled_pinstr_tiling_witness w2)
         added2 point2 Hstmt2_env
         (Tiling.wf_compiled_pinstr_tiling_witness w2)
         (Tiling.compiled_pinstr_tiling_witness_matches w2)
         Hadded_len2 Hpoint_len2
         (conj Hwf_stmt2 Hparams2) Hpositive2)
      as Hcomplete.
    rewrite Hidx_split2 in Hafter_dom2.
    specialize (Hcomplete Hafter_dom2).
    tauto.
  }
  set
    (raw_values1 :=
       affine_product
         (Tiling.PL.pad_schedule_to_len
            (List.length envv + stw_point_dim w1)
            (List.length (osbs_mask shape)) raw1)
         (envv ++ point1)).
  set
    (raw_values2 :=
       affine_product
         (Tiling.PL.pad_schedule_to_len
            (List.length envv + stw_point_dim w2)
            (List.length (osbs_mask shape)) raw2)
         (envv ++ point2)).
  set
    (semantic_values1 :=
       affine_product semantic_rows1 (envv ++ point1)).
  set
    (semantic_values2 :=
       affine_product semantic_rows2 (envv ++ point2)).
  set
    (global_tiles1 :=
       List.map
         (fun '(v, sz) => Z.div v sz)
         (combine raw_values1 (osbs_global_sizes shape))).
  set
    (global_tiles2 :=
       List.map
         (fun '(v, sz) => Z.div v sz)
         (combine raw_values2 (osbs_global_sizes shape))).
  assert
    (Hraw_bound1 :
       (List.length raw1 <= List.length (osbs_mask shape))%nat).
  {
    rewrite Hmask.
    unfold global_semantic_schedule_mask.
    rewrite List.map_length, seq_length.
    eapply max_schedule_length_ge_nth_error.
    exact Hraw_map1.
  }
  assert
    (Hraw_bound2 :
       (List.length raw2 <= List.length (osbs_mask shape))%nat).
  {
    rewrite Hmask.
    unfold global_semantic_schedule_mask.
    rewrite List.map_length, seq_length.
    eapply max_schedule_length_ge_nth_error.
    exact Hraw_map2.
  }
  assert
    (Hsemantic_eval1 :
       semantic_values1 =
       select_by_mask (osbs_mask shape) raw_values1).
  {
    subst semantic_values1 raw_values1.
    rewrite Hsemantic_rows_def1.
    unfold compact_semantic_schedule.
    rewrite affine_product_select_by_mask.
    rewrite Hlen_env.
    rewrite <- Hpoint_depth1.
    reflexivity.
  }
  assert
    (Hsemantic_eval2 :
       semantic_values2 =
       select_by_mask (osbs_mask shape) raw_values2).
  {
    subst semantic_values2 raw_values2.
    rewrite Hsemantic_rows_def2.
    unfold compact_semantic_schedule.
    rewrite affine_product_select_by_mask.
    rewrite Hlen_env.
    rewrite <- Hpoint_depth2.
    reflexivity.
  }
  assert
    (Hzero1 :
       zero_on_false (osbs_mask shape) raw_values1).
  {
    subst raw_values1.
    rewrite Hmask.
    assert
      (Hmask_len :
         List.length
           (global_semantic_schedule_mask (List.map fst data)) =
         max_schedule_length (List.map fst data)).
    {
      unfold global_semantic_schedule_mask.
      rewrite List.map_length, seq_length.
      reflexivity.
    }
    rewrite Hmask_len.
    eapply global_semantic_schedule_mask_zero_on_false.
    eapply nth_error_In.
    exact Hraw_map1.
  }
  assert
    (Hzero2 :
       zero_on_false (osbs_mask shape) raw_values2).
  {
    subst raw_values2.
    rewrite Hmask.
    assert
      (Hmask_len :
         List.length
           (global_semantic_schedule_mask (List.map fst data)) =
         max_schedule_length (List.map fst data)).
    {
      unfold global_semantic_schedule_mask.
      rewrite List.map_length, seq_length.
      reflexivity.
    }
    rewrite Hmask_len.
    eapply global_semantic_schedule_mask_zero_on_false.
    eapply nth_error_In.
    exact Hraw_map2.
  }
  assert
    (Hraw_len1 :
       List.length raw1 = List.length local_sizes1).
  {
    rewrite (schedule_rows_of_links_length _ _ Hraw1).
    rewrite <- Hlocal_sizes1.
    unfold tile_sizes_of_witness.
    rewrite List.map_length.
    reflexivity.
  }
  assert
    (Hraw_len2 :
       List.length raw2 = List.length local_sizes2).
  {
    rewrite (schedule_rows_of_links_length _ _ Hraw2).
    rewrite <- Hlocal_sizes2.
    unfold tile_sizes_of_witness.
    rewrite List.map_length.
    reflexivity.
  }
  assert
    (Hraw_values_eval1 :
       raw_values1 =
       affine_product raw1 (envv ++ point1) ++
       repeat 0%Z
         (List.length (osbs_mask shape) - List.length raw1)).
  {
    subst raw_values1.
    eapply affine_product_pad_schedule_to_len.
    exact Hraw_bound1.
  }
  assert
    (Hraw_values_eval2 :
       raw_values2 =
       affine_product raw2 (envv ++ point2) ++
       repeat 0%Z
         (List.length (osbs_mask shape) - List.length raw2)).
  {
    subst raw_values2.
    eapply affine_product_pad_schedule_to_len.
    exact Hraw_bound2.
  }
  assert
    (Hglobal_tiles_local1 :
       added1 ++
       repeat 0%Z
         (List.length (osbs_mask shape) -
          List.length (stw_links w1)) =
       global_tiles1).
  {
    subst global_tiles1.
    rewrite Hraw_values_eval1.
    pose proof
      (tile_values_pad_prefix
         (affine_product raw1 (envv ++ point1))
         local_sizes1 (osbs_global_sizes shape))
      as Hpad.
    assert
      (Haffine_len :
         List.length (affine_product raw1 (envv ++ point1)) =
         List.length raw1).
    {
      unfold affine_product.
      rewrite List.map_length.
      reflexivity.
    }
    rewrite Haffine_len in Hpad.
    specialize (Hpad Hraw_len1 Hlocal_prefix1).
    rewrite <- Hraw_len1 in Hpad.
    rewrite Hglobal_width in Hpad.
    rewrite Hpad.
    rewrite Hadded_eq1.
    rewrite
      (eval_tile_links_from_schedule_rows
         w1 point1 envv raw1 local_sizes1
         Hpoint_len1 Hraw1 Hlocal_sizes1
         Hwf_stmt1 Hparams1).
    rewrite (schedule_rows_of_links_length _ _ Hraw1).
    reflexivity.
  }
  assert
    (Hglobal_tiles_local2 :
       added2 ++
       repeat 0%Z
         (List.length (osbs_mask shape) -
          List.length (stw_links w2)) =
       global_tiles2).
  {
    subst global_tiles2.
    rewrite Hraw_values_eval2.
    pose proof
      (tile_values_pad_prefix
         (affine_product raw2 (envv ++ point2))
         local_sizes2 (osbs_global_sizes shape))
      as Hpad.
    assert
      (Haffine_len :
         List.length (affine_product raw2 (envv ++ point2)) =
         List.length raw2).
    {
      unfold affine_product.
      rewrite List.map_length.
      reflexivity.
    }
    rewrite Haffine_len in Hpad.
    specialize (Hpad Hraw_len2 Hlocal_prefix2).
    rewrite <- Hraw_len2 in Hpad.
    rewrite Hglobal_width in Hpad.
    rewrite Hpad.
    rewrite Hadded_eq2.
    rewrite
      (eval_tile_links_from_schedule_rows
         w2 point2 envv raw2 local_sizes2
         Hpoint_len2 Hraw2 Hlocal_sizes2
         Hwf_stmt2 Hparams2).
    rewrite (schedule_rows_of_links_length _ _ Hraw2).
    reflexivity.
  }
  assert
    (Hsemantic_len :
       List.length semantic_values1 = List.length semantic_values2).
  {
    subst semantic_values1 semantic_values2.
    unfold affine_product.
    rewrite !List.map_length.
    rewrite Hsemantic_rows_def1, Hsemantic_rows_def2.
    unfold compact_semantic_schedule.
    eapply select_by_mask_length_same.
    - unfold Tiling.PL.pad_schedule_to_len.
      rewrite app_length, repeat_length.
      lia.
    - unfold Tiling.PL.pad_schedule_to_len.
      rewrite app_length, repeat_length.
      lia.
  }
  assert
    (Htiles_eq :
       semantic_values1 = semantic_values2 ->
       global_tiles1 = global_tiles2).
  {
    intro Hsemantic_eq.
    assert
      (Hselect :
         select_by_mask (osbs_mask shape) raw_values1 =
         select_by_mask (osbs_mask shape) raw_values2).
    {
      rewrite <- Hsemantic_eval1, <- Hsemantic_eval2.
      exact Hsemantic_eq.
    }
    pose proof
      (select_by_mask_eq_reflect
         (osbs_mask shape) raw_values1 raw_values2
         Hzero1 Hzero2 Hselect)
      as Hraw_eq.
    subst global_tiles1 global_tiles2.
    now rewrite Hraw_eq.
  }
  assert
    (Htiles_mono :
       listz_pointwise_le semantic_values1 semantic_values2 ->
       listz_pointwise_le global_tiles1 global_tiles2).
  {
    intro Hsemantic_le.
    assert
      (Hraw_le : listz_pointwise_le raw_values1 raw_values2).
    {
      eapply select_by_mask_le_reflect; [exact Hzero1|exact Hzero2|].
      rewrite <- Hsemantic_eval1, <- Hsemantic_eval2.
      exact Hsemantic_le.
    }
    subst global_tiles1 global_tiles2.
    eapply map_div_combine_preserves_pointwise_le.
    - exact Hraw_le.
    - exact Hglobal_positive.
    - pose proof (zero_on_false_length _ _ Hzero1) as Hraw_values_len.
      rewrite Hglobal_width.
      symmetry.
      exact Hraw_values_len.
  }
  assert
    (Hold_eq1 :
       is_eq
         (Tiling.PL.ip_time_stamp1_ext ip1)
         semantic_values1 = true).
  {
    rewrite Hts11_old.
    subst semantic_values1.
    eapply
      schedule_matches_with_symmetric_trailing_zero_padding_affine_product_is_eq.
    exact Hbefore_match1.
  }
  assert
    (Hold_eq2 :
       is_eq
         (Tiling.PL.ip_time_stamp1_ext ip2)
         semantic_values2 = true).
  {
    rewrite Hts12_old.
    subst semantic_values2.
    eapply
      schedule_matches_with_symmetric_trailing_zero_padding_affine_product_is_eq.
    exact Hbefore_match2.
  }
  assert
    (Hnew_eq1 :
       is_eq
         (Tiling.PL.ip_time_stamp2_ext ip1)
         (global_tiles1 ++ semantic_values1) = true).
  {
    rewrite Hts21_after, Hidx_split1.
    pose proof
      (schedule_matches_with_symmetric_trailing_zero_padding_affine_product_is_eq
         (semantic_ordinary_target_schedule
            (List.length before_ctxt)
            (List.length (osbs_mask shape))
            semantic_rows1 w1)
         (Tiling.PL.pi_schedule after_pi1)
         (envv ++ added1 ++ point1) Hafter_match1)
      as Hmatch.
    rewrite
      (semantic_ordinary_target_schedule_eval
         (List.length before_ctxt)
         (List.length (osbs_mask shape))
         semantic_rows1 w1 envv added1 point1)
      in Hmatch.
    2:{ symmetry. exact Hlen_env. }
    2:{ exact Hadded_len1. }
    2:{ exact Hpoint_len1. }
    2:{
      rewrite <-
        (schedule_rows_of_links_length _ _ Hraw1).
      exact Hraw_bound1.
    }
    subst semantic_values1.
    rewrite <- Hglobal_tiles_local1.
    rewrite <- !app_assoc.
    exact Hmatch.
  }
  assert
    (Hnew_eq2 :
       is_eq
         (Tiling.PL.ip_time_stamp2_ext ip2)
         (global_tiles2 ++ semantic_values2) = true).
  {
    rewrite Hts22_after, Hidx_split2.
    pose proof
      (schedule_matches_with_symmetric_trailing_zero_padding_affine_product_is_eq
         (semantic_ordinary_target_schedule
            (List.length before_ctxt)
            (List.length (osbs_mask shape))
            semantic_rows2 w2)
         (Tiling.PL.pi_schedule after_pi2)
         (envv ++ added2 ++ point2) Hafter_match2)
      as Hmatch.
    rewrite
      (semantic_ordinary_target_schedule_eval
         (List.length before_ctxt)
         (List.length (osbs_mask shape))
         semantic_rows2 w2 envv added2 point2)
      in Hmatch.
    2:{ symmetry. exact Hlen_env. }
    2:{ exact Hadded_len2. }
    2:{ exact Hpoint_len2. }
    2:{
      rewrite <-
        (schedule_rows_of_links_length _ _ Hraw2).
      exact Hraw_bound2.
    }
    subst semantic_values2.
    rewrite <- Hglobal_tiles_local2.
    rewrite <- !app_assoc.
    exact Hmatch.
  }
  (* Stage 4: a target reversal cannot coexist with componentwise monotone
     tile and source-band values, so one semantic band component decreases. *)
  unfold Tiling.PL.instr_point_ext_old_sched_lt in Hold.
  assert
    (Hnew_not_lt :
       lex_compare
         (Tiling.PL.ip_time_stamp2_ext ip1)
         (Tiling.PL.ip_time_stamp2_ext ip2) <> Lt).
  {
    unfold Tiling.PL.instr_point_ext_new_sched_ge in Hnew.
    destruct Hnew; congruence.
  }
  destruct
    (semantic_stripmined_reversal_implies_decreasing_component
       (Tiling.PL.ip_time_stamp1_ext ip1)
       (Tiling.PL.ip_time_stamp1_ext ip2)
       (Tiling.PL.ip_time_stamp2_ext ip1)
       (Tiling.PL.ip_time_stamp2_ext ip2)
       semantic_values1 semantic_values2
       global_tiles1 global_tiles2
       Hold_eq1 Hold_eq2 Hnew_eq1 Hnew_eq2
       Hsemantic_len Htiles_eq Htiles_mono Hold Hnew_not_lt)
    as [dim [x [y [Hvalue1 [Hvalue2 Hdecrease]]]]].
  (* Stage 5: return that component together with the two composed points and
     connect its abstract values to the lifted executable checker rows. *)
  exists
    (Tiling.compose_tiling_pinstr_ext
       (List.length envv) before_pi1 after_pi1 w1),
    (Tiling.compose_tiling_pinstr_ext
       (List.length envv) before_pi2 after_pi2 w2),
    lifted1, lifted2, dim.
  repeat split; try assumption.
  - eapply Nat.lt_le_trans.
    + apply nth_error_Some.
      rewrite Hvalue1.
      discriminate.
    + eapply Nat.le_trans with (m := List.length lifted1).
      * subst semantic_values1.
        unfold affine_product.
        rewrite List.map_length.
        rewrite Hlifted_def1.
        unfold Tiling.lift_schedule_after_env,
               Tiling.lift_affine_function_after_env.
        rewrite List.map_length.
        reflexivity.
      *
      eapply max_schedule_length_ge_nth_error.
      exact Hlifted1.
  - assert
      (Hlift_eval1 :
         affine_product lifted1 (Tiling.PL.ip_index_ext ip1) =
         semantic_values1).
    {
      rewrite Hlifted_def1, Hidx_split1.
      eapply Tiling.lift_affine_function_after_env_eval.
      - symmetry. exact Hlen_env.
      - exact Hadded_len1.
    }
    assert
      (Hlift_eval2 :
         affine_product lifted2 (Tiling.PL.ip_index_ext ip2) =
         semantic_values2).
    {
      rewrite Hlifted_def2, Hidx_split2.
      eapply Tiling.lift_affine_function_after_env_eval.
      - symmetry. exact Hlen_env.
      - exact Hadded_len2.
    }
    assert
      (Hsemantic_value1 :
         semantic_band_value
           (List.length envv +
            Tiling.PL.pi_depth_ext
              (Tiling.compose_tiling_pinstr_ext
                 (List.length envv) before_pi1 after_pi1 w1))
           dim lifted1 (Tiling.PL.ip_index_ext ip1) = x).
    {
      eapply semantic_band_value_of_nth_error.
      rewrite Hlift_eval1.
      exact Hvalue1.
    }
    assert
      (Hsemantic_value2 :
         semantic_band_value
           (List.length envv +
            Tiling.PL.pi_depth_ext
              (Tiling.compose_tiling_pinstr_ext
                 (List.length envv) before_pi2 after_pi2 w2))
           dim lifted2 (Tiling.PL.ip_index_ext ip2) = y).
    {
      eapply semantic_band_value_of_nth_error.
      rewrite Hlift_eval2.
      exact Hvalue2.
    }
    rewrite Hsemantic_value1, Hsemantic_value2.
    exact Hdecrease.
Qed.

Definition semantic_quotient_tiles
    (values sizes: list Z) : list Z :=
  List.map
    (fun '(value, size) => Z.div value size)
    (combine values sizes).

Definition semantic_second_level_global_tile_block
    (layout: second_level_schedule_layout)
    (root_values root_sizes child_sizes: list Z) : list Z :=
  let roots := semantic_quotient_tiles root_values root_sizes in
  let children := semantic_quotient_tiles roots child_sizes in
  match layout with
  | SecondLevelGrouped => children ++ roots
  | SecondLevelInterleaved =>
      interleave_root_child_tiles roots children
  end.

Lemma interleave_root_child_tiles_app :
  forall roots1 roots2 children1 children2,
    List.length roots1 = List.length children1 ->
    interleave_root_child_tiles
      (roots1 ++ roots2) (children1 ++ children2) =
    interleave_root_child_tiles roots1 children1 ++
    interleave_root_child_tiles roots2 children2.
Proof.
  induction roots1 as [|root roots IH];
    intros roots2 children1 children2 Hlen.
  - destruct children1; [reflexivity|discriminate].
  - destruct children1 as [|child children]; [discriminate|].
    simpl in Hlen.
    simpl.
    f_equal.
    f_equal.
    eapply IH.
    lia.
Qed.

Lemma interleave_root_child_tiles_repeat_zero :
  forall n,
    interleave_root_child_tiles
      (repeat 0%Z n) (repeat 0%Z n) =
    repeat 0%Z (2 * n).
Proof.
  induction n as [|n IH].
  - reflexivity.
  - replace (2 * S n)%nat with (S (S (2 * n))) by lia.
    simpl.
    f_equal.
    f_equal.
    exact IH.
Qed.

Lemma semantic_quotient_tiles_pad_prefix :
  forall values local_sizes global_sizes,
    List.length values = List.length local_sizes ->
    prefix_sizes local_sizes global_sizes ->
    semantic_quotient_tiles
      (values ++
       repeat 0%Z
         (List.length global_sizes - List.length values))
      global_sizes =
    semantic_quotient_tiles values local_sizes ++
    repeat 0%Z
      (List.length global_sizes - List.length local_sizes).
Proof.
  intros values local_sizes global_sizes Hlen Hprefix.
  unfold semantic_quotient_tiles.
  eapply tile_values_pad_prefix; eauto.
Qed.

Lemma semantic_second_level_global_tile_block_local :
  forall layout root_values local_root_sizes local_child_sizes
         global_root_sizes global_child_sizes,
    List.length root_values = List.length local_root_sizes ->
    List.length root_values = List.length local_child_sizes ->
    prefix_sizes local_root_sizes global_root_sizes ->
    prefix_sizes local_child_sizes global_child_sizes ->
    List.length global_root_sizes = List.length global_child_sizes ->
    semantic_second_level_global_tile_block
      layout
      (root_values ++
       repeat 0%Z
         (List.length global_root_sizes - List.length root_values))
      global_root_sizes global_child_sizes =
    match layout with
    | SecondLevelGrouped =>
        semantic_quotient_tiles
          (semantic_quotient_tiles root_values local_root_sizes)
          local_child_sizes ++
        repeat 0%Z
          (List.length global_child_sizes -
           List.length local_child_sizes) ++
        semantic_quotient_tiles root_values local_root_sizes ++
        repeat 0%Z
          (List.length global_root_sizes -
           List.length local_root_sizes)
    | SecondLevelInterleaved =>
        interleave_root_child_tiles
          (semantic_quotient_tiles root_values local_root_sizes)
          (semantic_quotient_tiles
             (semantic_quotient_tiles root_values local_root_sizes)
             local_child_sizes) ++
        repeat 0%Z
          (2 *
           (List.length global_root_sizes -
            List.length local_root_sizes))
    end.
Proof.
  intros layout root_values local_root_sizes local_child_sizes
         global_root_sizes global_child_sizes
         Hroot_len Hchild_len Hroot_prefix Hchild_prefix Hglobal_len.
  unfold semantic_second_level_global_tile_block.
  rewrite
    (semantic_quotient_tiles_pad_prefix
       root_values local_root_sizes global_root_sizes
       Hroot_len Hroot_prefix).
  assert
    (Hlocal_sizes :
       List.length local_root_sizes =
       List.length local_child_sizes) by lia.
  assert
    (Hlocal_roots_len :
       List.length
         (semantic_quotient_tiles root_values local_root_sizes) =
       List.length local_child_sizes).
  {
    unfold semantic_quotient_tiles.
    rewrite List.map_length, combine_length, Hroot_len.
    rewrite Nat.min_id.
    lia.
  }
  assert
    (Hextra :
       (List.length global_root_sizes -
        List.length local_root_sizes =
        List.length global_child_sizes -
        List.length local_child_sizes)%nat) by lia.
  rewrite Hextra.
  replace
    (List.length global_child_sizes -
     List.length local_child_sizes)%nat
    with
    (List.length global_child_sizes -
     List.length
       (semantic_quotient_tiles root_values local_root_sizes))%nat
    by lia.
  rewrite
    (semantic_quotient_tiles_pad_prefix
       (semantic_quotient_tiles root_values local_root_sizes)
       local_child_sizes global_child_sizes
       Hlocal_roots_len Hchild_prefix).
  assert
    (Hlocal_children_len :
       List.length
         (semantic_quotient_tiles
            (semantic_quotient_tiles root_values local_root_sizes)
            local_child_sizes) =
       List.length local_child_sizes).
  {
    unfold semantic_quotient_tiles at 1.
    rewrite List.map_length, combine_length, Hlocal_roots_len.
    rewrite Nat.min_id.
    reflexivity.
  }
  assert
    (Hroot_child_tiles_len :
       List.length
         (semantic_quotient_tiles root_values local_root_sizes) =
       List.length
         (semantic_quotient_tiles
            (semantic_quotient_tiles root_values local_root_sizes)
            local_child_sizes)) by lia.
  rewrite Hlocal_roots_len.
  destruct layout.
  - repeat rewrite app_assoc.
    reflexivity.
  - rewrite interleave_root_child_tiles_app
      by exact Hroot_child_tiles_len.
    rewrite interleave_root_child_tiles_repeat_zero.
    rewrite <- Hextra.
    reflexivity.
Qed.


Lemma semantic_second_level_global_tile_block_pointwise_le :
  forall layout root_values1 root_values2 root_sizes child_sizes,
    listz_pointwise_le root_values1 root_values2 ->
    Forall (fun size => (0 < size)%Z) root_sizes ->
    Forall (fun size => (0 < size)%Z) child_sizes ->
    List.length root_values1 = List.length root_sizes ->
    List.length root_sizes = List.length child_sizes ->
    listz_pointwise_le
      (semantic_second_level_global_tile_block
         layout root_values1 root_sizes child_sizes)
      (semantic_second_level_global_tile_block
         layout root_values2 root_sizes child_sizes).
Proof.
  intros layout root_values1 root_values2 root_sizes child_sizes
         Hvalues Hroot_positive Hchild_positive
         Hvalues_len Hsizes_len.
  assert
    (Hroots :
       listz_pointwise_le
         (semantic_quotient_tiles root_values1 root_sizes)
         (semantic_quotient_tiles root_values2 root_sizes)).
  {
    unfold semantic_quotient_tiles.
    eapply map_div_combine_preserves_pointwise_le; eauto.
  }
  assert
    (Hroots_len :
       List.length
         (semantic_quotient_tiles root_values1 root_sizes) =
       List.length child_sizes).
  {
    unfold semantic_quotient_tiles.
    rewrite List.map_length, combine_length, Hvalues_len.
    rewrite Nat.min_id.
    lia.
  }
  assert
    (Hchildren :
       listz_pointwise_le
         (semantic_quotient_tiles
            (semantic_quotient_tiles root_values1 root_sizes)
            child_sizes)
         (semantic_quotient_tiles
            (semantic_quotient_tiles root_values2 root_sizes)
            child_sizes)).
  {
    unfold semantic_quotient_tiles.
    eapply map_div_combine_preserves_pointwise_le; eauto.
  }
  unfold semantic_second_level_global_tile_block.
  destruct layout.
  - eapply listz_pointwise_le_app; eauto.
  - eapply interleave_root_child_tiles_pointwise_le; eauto.
Qed.

Lemma semantic_second_level_target_schedule_eval :
  forall layout env_size global_width semantic_rows w recipe
         envv added point,
    List.length envv = env_size ->
    List.length added = (2 * List.length (slbr_root_rows recipe))%nat ->
    List.length point = stw_point_dim w ->
    (List.length (slbr_root_rows recipe) <= global_width)%nat ->
    affine_product
      (semantic_second_level_target_schedule
         layout env_size global_width semantic_rows w recipe)
      (envv ++ added ++ point) =
    match layout with
    | SecondLevelGrouped =>
        List.map
          (fun pos => nth pos added 0%Z)
          (second_level_child_positions
             (List.length (slbr_root_rows recipe))) ++
        repeat 0%Z
          (global_width - List.length (slbr_root_rows recipe)) ++
        List.map
          (fun pos => nth pos added 0%Z)
          (second_level_root_positions
             (List.length (slbr_root_rows recipe))) ++
        repeat 0%Z
          (global_width - List.length (slbr_root_rows recipe)) ++
        affine_product semantic_rows (envv ++ point)
    | SecondLevelInterleaved =>
        added ++
        repeat 0%Z
          (2 * (global_width - List.length (slbr_root_rows recipe))) ++
        affine_product semantic_rows (envv ++ point)
    end.
Proof.
  intros layout env_size global_width semantic_rows w recipe
         envv added point Henv Hadded Hpoint Hwidth.
  unfold semantic_second_level_target_schedule.
  destruct layout.
  - unfold semantic_second_level_grouped_target_schedule.
    rewrite !affine_product_app.
    rewrite affine_product_identity_affine_rows_at.
    2:{
      apply Forall_forall.
      intros pos Hin.
      pose proof (second_level_child_positions_bound _ _ Hin).
      lia.
    }
    assert
      (Hchild_projection :
         List.map
           (fun pos =>
              nth (env_size + pos)%nat
                (envv ++ added ++ point) 0%Z)
           (second_level_child_positions
              (List.length (slbr_root_rows recipe))) =
         List.map
           (fun pos => nth pos added 0%Z)
           (second_level_child_positions
              (List.length (slbr_root_rows recipe)))).
    {
      apply List.map_ext_in.
      intros pos Hin.
      eapply nth_env_added_app.
      - exact Henv.
      - pose proof (second_level_child_positions_bound _ _ Hin).
        rewrite Hadded.
        exact H.
    }
    rewrite Hchild_projection.
    rewrite affine_product_zero_schedule_rows.
    rewrite affine_product_identity_affine_rows_at.
    2:{
      apply Forall_forall.
      intros pos Hin.
      pose proof (second_level_root_positions_bound _ _ Hin).
      lia.
    }
    assert
      (Hroot_projection :
         List.map
           (fun pos =>
              nth (env_size + pos)%nat
                (envv ++ added ++ point) 0%Z)
           (second_level_root_positions
              (List.length (slbr_root_rows recipe))) =
         List.map
           (fun pos => nth pos added 0%Z)
           (second_level_root_positions
              (List.length (slbr_root_rows recipe)))).
    {
      apply List.map_ext_in.
      intros pos Hin.
      eapply nth_env_added_app.
      - exact Henv.
      - pose proof (second_level_root_positions_bound _ _ Hin).
        rewrite Hadded.
        lia.
    }
    rewrite Hroot_projection.
    rewrite Tiling.lift_affine_function_after_env_eval.
    2:{ exact Henv. }
    2:{ exact Hadded. }
    reflexivity.
  - unfold semantic_second_level_interleaved_target_schedule.
    rewrite !affine_product_app.
    rewrite affine_product_identity_affine_rows_from.
    2:{ lia. }
    2:{ rewrite !app_length. lia. }
    rewrite affine_product_zero_schedule_rows.
    rewrite Tiling.lift_affine_function_after_env_eval.
    2:{ exact Henv. }
    2:{ exact Hadded. }
    rewrite <- Henv.
    replace
      (skipn (List.length envv) (envv ++ added ++ point))
      with (added ++ point).
    2:{
      rewrite skipn_app_le by lia.
      replace (List.length envv - List.length envv)%nat with O by lia.
      reflexivity.
    }
    rewrite firstn_app.
    replace
      (2 * List.length (slbr_root_rows recipe) -
       List.length added)%nat
      with O by lia.
    rewrite <- Hadded.
    rewrite firstn_all.
    rewrite app_nil_r.
    reflexivity.
Qed.

Lemma parse_second_level_semantic_recipes_nth_error :
  forall ws recipes n w recipe,
    parse_second_level_semantic_recipes ws = Some recipes ->
    nth_error ws n = Some w ->
    nth_error recipes n = Some recipe ->
    second_level_band_recipe_of_witness w = Some recipe.
Proof.
  intros ws.
  induction ws as [|w0 ws IH];
    intros recipes n w recipe Hparse Hw Hrecipe.
  - destruct n; discriminate.
  - simpl in Hparse.
    destruct (second_level_band_recipe_of_witness w0)
      as [recipe0|] eqn:Hrecipe0; try discriminate.
    destruct (parse_second_level_semantic_recipes ws)
      as [rest|] eqn:Hrest; try discriminate.
    inversion Hparse; subst recipes; clear Hparse.
    destruct n as [|n].
    + simpl in Hw, Hrecipe.
      inversion Hw; inversion Hrecipe; subst.
      exact Hrecipe0.
    + simpl in Hw, Hrecipe.
      eapply IH; eauto.
Qed.

Lemma parse_second_level_semantic_recipes_length :
  forall ws recipes,
    parse_second_level_semantic_recipes ws = Some recipes ->
    List.length recipes = List.length ws.
Proof.
  intros ws.
  induction ws as [|w ws IH]; intros recipes Hparse.
  - simpl in Hparse. inversion Hparse. reflexivity.
  - simpl in Hparse.
    destruct (second_level_band_recipe_of_witness w)
      as [recipe|] eqn:Hrecipe; try discriminate.
    destruct (parse_second_level_semantic_recipes ws)
      as [rest|] eqn:Hrest; try discriminate.
    inversion Hparse; subst recipes.
    simpl.
    f_equal.
    eapply IH.
    reflexivity.
Qed.

Lemma second_level_band_recipe_spec_links_length :
  forall point_dim prefix_len links recipe,
    second_level_band_recipe_spec
      point_dim prefix_len links recipe ->
    List.length links =
      (2 * List.length (slbr_root_rows recipe))%nat.
Proof.
  intros point_dim prefix_len links recipe Hspec.
  induction Hspec; simpl; lia.
Qed.

Lemma parse_second_level_semantic_recipes_positive :
  forall ws recipes,
    parse_second_level_semantic_recipes ws = Some recipes ->
    Forall
      (fun w =>
         Forall (fun link => (0 < tl_tile_size link)%Z)
           (stw_links w))
      ws ->
    Forall
      (fun recipe =>
         Forall (fun size => (0 < size)%Z)
           (slbr_root_sizes recipe) /\
         Forall (fun size => (0 < size)%Z)
           (slbr_child_sizes recipe))
      recipes.
Proof.
  intros ws.
  induction ws as [|w ws IH]; intros recipes Hparse Hpositive.
  - simpl in Hparse. inversion Hparse. constructor.
  - inversion Hpositive as [|w0 ws0 Hw Hws]; subst w0 ws0.
    simpl in Hparse.
    destruct (second_level_band_recipe_of_witness w)
      as [recipe|] eqn:Hrecipe; try discriminate.
    destruct (parse_second_level_semantic_recipes ws)
      as [rest|] eqn:Hrest; try discriminate.
    inversion Hparse; subst recipes.
    constructor.
    + destruct
        (second_level_band_recipe_of_witness_sound _ _ Hrecipe)
        as [_ Hspec].
      eapply second_level_band_recipe_spec_positive_sizes; eauto.
    + eapply IH; eauto.
Qed.

Lemma second_level_semantic_schedules_match_nth_error :
  forall layout env_size global_width
         before_pis after_pis ws recipes semantic_rows
         n before_pi after_pi w recipe rows,
    second_level_semantic_schedules_match
      layout env_size global_width
      before_pis after_pis ws recipes semantic_rows ->
    nth_error before_pis n = Some before_pi ->
    nth_error after_pis n = Some after_pi ->
    nth_error ws n = Some w ->
    nth_error recipes n = Some recipe ->
    nth_error semantic_rows n = Some rows ->
    schedule_matches_with_symmetric_trailing_zero_padding
      rows (Tiling.PL.pi_schedule before_pi) /\
    schedule_matches_with_symmetric_trailing_zero_padding
      (semantic_second_level_target_schedule
         layout env_size global_width rows w recipe)
      (Tiling.PL.pi_schedule after_pi).
Proof.
  intros layout env_size global_width
         before_pis after_pis ws recipes semantic_rows n.
  revert before_pis after_pis ws recipes semantic_rows.
  induction n as [|n IH];
    intros before_pis after_pis ws recipes semantic_rows
           before_pi after_pi w recipe rows
           Hmatch Hbefore Hafter Hw Hrecipe Hrows;
    inversion Hmatch; subst; simpl in *; try discriminate.
  - inversion Hbefore; inversion Hafter; inversion Hw;
      inversion Hrecipe; inversion Hrows; subst.
    split; assumption.
  - eapply IH; eauto.
Qed.

Lemma second_level_band_recipe_root_rows_exact_cols :
  forall point_dim prefix_len param_dim links recipe,
    second_level_band_recipe_spec
      point_dim prefix_len links recipe ->
    well_formed_tile_links prefix_len point_dim links ->
    Forall
      (fun link =>
         List.length (ae_param_coeffs (tl_expr link)) = param_dim)
      links ->
    exact_listzzs_cols
      (param_dim + point_dim)%nat
      (slbr_root_rows recipe).
Proof.
  intros point_dim prefix_len param_dim links recipe Hspec.
  induction Hspec;
    intros Hwf Hparams.
  - unfold exact_listzzs_cols.
    intros coeffs c row Hin.
    contradiction.
  - simpl in Hwf.
    destruct Hwf as [Hroot_vars [Hchild_vars Hwf_rest]].
    inversion Hparams as
      [|root0 links0 Hroot_param Hparams_tail];
      subst root0 links0.
    inversion Hparams_tail as
      [|child0 links0 Hchild_param Hparams_rest];
      subst child0 links0.
    unfold exact_listzzs_cols.
    intros coeffs c row Hin Heq.
    simpl in Hin.
    destruct Hin as [Hin | Hin].
    + subst row.
      inversion Heq; subst coeffs c.
      unfold schedule_row_of_tile_link_base.
      simpl.
      rewrite app_length, Hroot_param, skipn_length, Hroot_vars.
      lia.
    + eapply IHHspec.
      * replace (prefix_len + 2)%nat
          with (S (S prefix_len)) by lia.
        exact Hwf_rest.
      * exact Hparams_rest.
      * exact Hin.
      * exact Heq.
Qed.

Lemma second_level_semantic_rows_exact_cols :
  forall env_size before_pis ws recipes mask semantic_rows,
    parse_second_level_semantic_recipes ws = Some recipes ->
    compact_semantic_schedules
      env_size before_pis (List.map slbr_root_rows recipes) mask =
      Some semantic_rows ->
    Forall
      (Tiling.wf_statement_tiling_witness_with_param_dim env_size)
      ws ->
    Forall2
      (fun before_pi w =>
         stw_point_dim w = Tiling.PL.pi_depth before_pi)
      before_pis ws ->
    Forall2
      (fun w rows =>
         exact_listzzs_cols
           (env_size + stw_point_dim w)%nat rows)
      ws semantic_rows.
Proof.
  intros env_size before_pis ws.
  revert before_pis.
  induction ws as [|w ws IH];
    intros before_pis recipes mask semantic_rows
           Hrecipes Hcompact Hwf Hdepths.
  - simpl in Hrecipes.
    inversion Hrecipes; subst recipes.
    inversion Hdepths; subst before_pis.
    simpl in Hcompact.
    inversion Hcompact; constructor.
  - destruct before_pis as [|before_pi before_pis].
    { inversion Hdepths. }
    inversion Hwf as [|w0 ws0 Hwf_w Hwf_ws]; subst w0 ws0.
    inversion Hdepths as
      [|before_pi0 w0 before_pis0 ws0 Hdepth Hdepths_rest];
      subst before_pi0 w0 before_pis0 ws0.
    simpl in Hrecipes.
    destruct (second_level_band_recipe_of_witness w)
      as [recipe|] eqn:Hrecipe; try discriminate.
    destruct (parse_second_level_semantic_recipes ws)
      as [rest_recipes|] eqn:Hrest_recipes; try discriminate.
    inversion Hrecipes; subst recipes.
    simpl in Hcompact.
    destruct
      (compact_semantic_schedules
         env_size before_pis
         (List.map slbr_root_rows rest_recipes) mask)
      as [rest_rows|] eqn:Hrest_rows; try discriminate.
    inversion Hcompact; subst semantic_rows.
    constructor.
    + destruct Hwf_w as [Hwf_links Hparams].
      destruct
        (second_level_band_recipe_of_witness_sound _ _ Hrecipe)
        as [_ Hspec].
      rewrite Hdepth.
      eapply compact_semantic_schedule_exact_cols.
      rewrite <- Hdepth.
      eapply second_level_band_recipe_root_rows_exact_cols
        with (prefix_len := O)
             (links := stw_links w).
      * exact Hspec.
      * exact Hwf_links.
      * exact Hparams.
    + eapply IH; eauto using eq_refl.
Qed.

Lemma ordinary_semantic_rows_exact_cols :
  forall env_size before_pis ws data mask semantic_rows,
    parse_ordinary_semantic_data ws = Some data ->
    compact_semantic_schedules
      env_size before_pis (List.map fst data) mask =
      Some semantic_rows ->
    Forall
      (Tiling.wf_statement_tiling_witness_with_param_dim env_size)
      ws ->
    Forall2
      (fun before_pi w =>
         stw_point_dim w = Tiling.PL.pi_depth before_pi)
      before_pis ws ->
    Forall2
      (fun w rows =>
         exact_listzzs_cols
           (env_size + stw_point_dim w)%nat rows)
      ws semantic_rows.
Proof.
  intros env_size before_pis ws.
  revert before_pis.
  induction ws as [|w ws IH];
    intros before_pis data mask semantic_rows
           Hdata Hcompact Hwf Hdepths.
  - simpl in Hdata.
    inversion Hdata; subst data.
    inversion Hdepths; subst before_pis.
    simpl in Hcompact.
    inversion Hcompact; constructor.
  - destruct before_pis as [|before_pi before_pis].
    { inversion Hdepths. }
    inversion Hwf as [|w0 ws0 Hwf_w Hwf_ws]; subst w0 ws0.
    inversion Hdepths as
      [|before_pi0 w0 before_pis0 ws0 Hdepth Hdepths_rest];
      subst before_pi0 w0 before_pis0 ws0.
    simpl in Hdata.
    destruct (schedule_rows_of_links w) as [raw|] eqn:Hraw;
      try discriminate.
    destruct (parse_ordinary_semantic_data ws)
      as [rest_data|] eqn:Hrest_data; try discriminate.
    inversion Hdata; subst data.
    simpl in Hcompact.
    destruct
      (compact_semantic_schedules
         env_size before_pis (List.map fst rest_data) mask)
      as [rest_rows|] eqn:Hrest_rows; try discriminate.
    inversion Hcompact; subst semantic_rows.
    constructor.
    + pose proof
        (schedule_rows_of_links_exact_cols
           env_size w raw Hraw Hwf_w)
        as Hraw_cols.
      rewrite Hdepth in Hraw_cols.
      rewrite Hdepth.
      eapply compact_semantic_schedule_exact_cols.
      exact Hraw_cols.
    + eapply IH; eauto using eq_refl.
Qed.

Lemma composed_semantic_rows_exact_cols :
  forall env_size before_pis after_pis ws lifted_rows,
    Forall2 Tiling.after_matches_tiling_witness after_pis ws ->
    Forall2
      (fun before_pi w =>
         stw_point_dim w = Tiling.PL.pi_depth before_pi)
      before_pis ws ->
    Forall2
      (fun w lifted =>
         exact_listzzs_cols
           (env_size + List.length (stw_links w) +
            stw_point_dim w)%nat
           lifted)
      ws lifted_rows ->
    Forall2
      (fun pi lifted =>
         exact_listzzs_cols
           (env_size + Tiling.PL.pi_depth_ext pi)%nat
           lifted)
      (Tiling.compose_tiling_pinstrs_ext_from_after
         env_size before_pis after_pis ws)
      lifted_rows.
Proof.
  intros env_size before_pis.
  induction before_pis as [|before_pi before_pis IH];
    intros after_pis ws lifted_rows Hwits Hdepths Hcols.
  - inversion Hdepths; subst ws.
    inversion Hwits; subst after_pis.
    inversion Hcols; subst lifted_rows.
    constructor.
  - destruct ws as [|w ws].
    + inversion Hdepths.
    + destruct after_pis as [|after_pi after_pis].
      * inversion Hwits.
      * inversion Hdepths as
          [|before_pi0 w0 before_pis0 ws0 Hdepth Hdepths_tail].
        inversion Hwits as
          [|after_pi0 w1 after_pis0 ws1 Hwit Hwits_tail].
        subst.
        inversion Hcols as
          [|w0 lifted0 ws0 lifted_rows0 Hcols_head Hcols_tail].
        subst.
        simpl.
        constructor.
        -- unfold Tiling.after_matches_tiling_witness in Hwit.
           destruct Hwit as [Hpw Hafter_depth].
           simpl.
           rewrite <- Hafter_depth, Hpw.
           unfold witness_current_point_dim,
                  witness_base_point_dim, witness_added_dims.
           simpl.
           replace
             (env_size +
              (stw_point_dim w + List.length (stw_links w)))%nat
             with
             (env_size + List.length (stw_links w) +
              stw_point_dim w)%nat by lia.
           exact Hcols_head.
        -- eapply IH; eauto.
Qed.

(** The second-level bridge follows the same five-step argument as
    [ordinary_semantic_band_shape_reversal_bridge].  Its extra work is to
    evaluate the second tile prefix and prove monotonicity first from point
    coordinates to level-one tiles, then from level-one to level-two tiles. *)
Lemma second_level_semantic_band_shape_reversal_bridge :
  forall before_pis before_ctxt before_vars after_pis ws
         shape lifted_rows envv,
    List.length before_ctxt = List.length envv ->
    TilingCheck.check_pprog_tiling_sourceb
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars) ws = true ->
    second_level_semantic_band_shape_property_with_witness
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars) ws shape ->
    lift_semantic_schedules_for_tiling
      (List.length before_ctxt) ws (slsbs_rows shape) =
      Some lifted_rows ->
    semantic_rows_reversal_bridge
      envv before_pis after_pis ws lifted_rows.
Proof.
  (* Stage 1: unpack the two-level layout and establish positive, globally
     aligned root and child tile sizes. *)
  intros before_pis before_ctxt before_vars after_pis ws
         shape lifted_rows envv Hlen_env Hsource Hshape Hlift.
  unfold second_level_semantic_band_shape_property_with_witness in Hshape.
  cbn in Hshape.
  destruct Hshape as
    [_ [_ [Hrecipes [Hglobal_root_sizes
      [Hglobal_child_sizes [Hmask [Hcompact
      [_ [Hglobal_root_width
      [Hglobal_child_width Hschedules]]]]]]]]]].
  pose proof
    (TilingCheck.check_pprog_tiling_sourceb_sound
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars) ws Hsource)
    as [Hprog [_ [Hwf_ws [Hpositive_ws Hdepths]]]].
  assert
    (Hwf_ws_env :
       Forall
         (Tiling.wf_statement_tiling_witness_with_param_dim
            (List.length envv))
         ws).
  {
    rewrite <- Hlen_env.
    exact Hwf_ws.
  }
  assert
    (Hroot_prefixes :
       Forall
         (fun local =>
            prefix_sizes local (slsbs_global_root_sizes shape))
         (List.map slbr_root_sizes (slsbs_recipes shape))).
  {
    eapply infer_global_prefix_sizes_sound.
    exact Hglobal_root_sizes.
  }
  assert
    (Hchild_prefixes :
       Forall
         (fun local =>
            prefix_sizes local (slsbs_global_child_sizes shape))
         (List.map slbr_child_sizes (slsbs_recipes shape))).
  {
    eapply infer_global_prefix_sizes_sound.
    exact Hglobal_child_sizes.
  }
  pose proof
    (parse_second_level_semantic_recipes_positive
       ws (slsbs_recipes shape) Hrecipes Hpositive_ws)
    as Hrecipes_positive.
  assert
    (Hglobal_root_positive :
       Forall (fun size => (0 < size)%Z)
         (slsbs_global_root_sizes shape)).
  {
    eapply infer_global_prefix_sizes_positive.
    - exact Hglobal_root_sizes.
    - apply Forall_forall.
      intros local Hin.
      apply in_map_iff in Hin.
      destruct Hin as [recipe [Heq Hin]].
      subst local.
      eapply Forall_forall in Hrecipes_positive; eauto.
      tauto.
  }
  assert
    (Hglobal_child_positive :
       Forall (fun size => (0 < size)%Z)
         (slsbs_global_child_sizes shape)).
  {
    eapply infer_global_prefix_sizes_positive.
    - exact Hglobal_child_sizes.
    - apply Forall_forall.
      intros local Hin.
      apply in_map_iff in Hin.
      destruct Hin as [recipe [Heq Hin]].
      subst local.
      eapply Forall_forall in Hrecipes_positive; eauto.
      tauto.
  }
  destruct
    (lift_semantic_schedules_for_tiling_length
       (List.length before_ctxt) ws (slsbs_rows shape)
       lifted_rows Hlift)
    as [Hlifted_len Hsemantic_rows_len].
  assert
    (Hrecipes_len :
       List.length (slsbs_recipes shape) = List.length ws).
  {
    eapply parse_second_level_semantic_recipes_length.
    exact Hrecipes.
  }
  (* Stage 2: recover both endpoints of an arbitrary target reversal and the
     statement-local recipes used to interpret their added coordinates. *)
  unfold semantic_rows_reversal_bridge.
  intros flat ip1 ip2 Hflat Hin1 Hin2 Hold Hnew.
  destruct
    (composed_point_pair_facts_of_members
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       ws envv flat ip1 ip2
       Hprog Hwf_ws_env Hpositive_ws Hdepths Hflat Hin1 Hin2)
    as [Hpoint1 Hpoint2].
  unfold composed_point_facts in Hpoint1, Hpoint2.
  destruct Hpoint1 as [before_pi1 [after_pi1 [w1
    [Hbefore1 [Hafter1 [Hw1
    [Hwf_stmt1 [Hpositive1 [Hpoint_depth1
    [Hpref1 [Hbel1 Hidx_len1]]]]]]]]]]].
  destruct Hpoint2 as [before_pi2 [after_pi2 [w2
    [Hbefore2 [Hafter2 [Hw2
    [Hwf_stmt2 [Hpositive2 [Hpoint_depth2
    [Hpref2 [Hbel2 Hidx_len2]]]]]]]]]]].
  assert
    (Hn1 : (Tiling.PL.ip_nth_ext ip1 < List.length ws)%nat).
  {
    apply nth_error_Some. rewrite Hw1. discriminate.
  }
  assert
    (Hn2 : (Tiling.PL.ip_nth_ext ip2 < List.length ws)%nat).
  {
    apply nth_error_Some. rewrite Hw2. discriminate.
  }
  destruct
    (nth_error (slsbs_recipes shape) (Tiling.PL.ip_nth_ext ip1))
    as [recipe1|] eqn:Hrecipe1.
  2:{ exfalso. apply nth_error_None in Hrecipe1. lia. }
  destruct
    (nth_error (slsbs_recipes shape) (Tiling.PL.ip_nth_ext ip2))
    as [recipe2|] eqn:Hrecipe2.
  2:{ exfalso. apply nth_error_None in Hrecipe2. lia. }
  pose proof
    (parse_second_level_semantic_recipes_nth_error
       ws (slsbs_recipes shape) (Tiling.PL.ip_nth_ext ip1)
       w1 recipe1 Hrecipes Hw1 Hrecipe1)
    as Hrecipe_parse1.
  pose proof
    (parse_second_level_semantic_recipes_nth_error
       ws (slsbs_recipes shape) (Tiling.PL.ip_nth_ext ip2)
       w2 recipe2 Hrecipes Hw2 Hrecipe2)
    as Hrecipe_parse2.
  destruct
    (second_level_band_recipe_of_witness_sound
       w1 recipe1 Hrecipe_parse1)
    as [Hlinks_nonempty1 Hspec1].
  destruct
    (second_level_band_recipe_of_witness_sound
       w2 recipe2 Hrecipe_parse2)
    as [Hlinks_nonempty2 Hspec2].
  destruct (second_level_band_recipe_spec_lengths _ _ _ _ Hspec1)
    as [Hroot_len1 Hchild_len1].
  destruct (second_level_band_recipe_spec_lengths _ _ _ _ Hspec2)
    as [Hroot_len2 Hchild_len2].
  destruct
    (second_level_band_recipe_spec_positive_sizes
       _ _ _ _ Hspec1 Hpositive1)
    as [Hroot_positive1 Hchild_positive1].
  destruct
    (second_level_band_recipe_spec_positive_sizes
       _ _ _ _ Hspec2 Hpositive2)
    as [Hroot_positive2 Hchild_positive2].
  assert
    (Hraw_map1 :
       nth_error
         (List.map slbr_root_rows (slsbs_recipes shape))
         (Tiling.PL.ip_nth_ext ip1) =
       Some (slbr_root_rows recipe1)).
  {
    eapply Tiling.nth_error_map_some.
    exact Hrecipe1.
  }
  assert
    (Hraw_map2 :
       nth_error
         (List.map slbr_root_rows (slsbs_recipes shape))
         (Tiling.PL.ip_nth_ext ip2) =
       Some (slbr_root_rows recipe2)).
  {
    eapply Tiling.nth_error_map_some.
    exact Hrecipe2.
  }
  assert
    (Hroot_sizes_map1 :
       nth_error
         (List.map slbr_root_sizes (slsbs_recipes shape))
         (Tiling.PL.ip_nth_ext ip1) =
       Some (slbr_root_sizes recipe1)).
  {
    eapply Tiling.nth_error_map_some.
    exact Hrecipe1.
  }
  assert
    (Hroot_sizes_map2 :
       nth_error
         (List.map slbr_root_sizes (slsbs_recipes shape))
         (Tiling.PL.ip_nth_ext ip2) =
       Some (slbr_root_sizes recipe2)).
  {
    eapply Tiling.nth_error_map_some.
    exact Hrecipe2.
  }
  assert
    (Hchild_sizes_map1 :
       nth_error
         (List.map slbr_child_sizes (slsbs_recipes shape))
         (Tiling.PL.ip_nth_ext ip1) =
       Some (slbr_child_sizes recipe1)).
  {
    eapply Tiling.nth_error_map_some.
    exact Hrecipe1.
  }
  assert
    (Hchild_sizes_map2 :
       nth_error
         (List.map slbr_child_sizes (slsbs_recipes shape))
         (Tiling.PL.ip_nth_ext ip2) =
       Some (slbr_child_sizes recipe2)).
  {
    eapply Tiling.nth_error_map_some.
    exact Hrecipe2.
  }
  pose proof
    (Tiling.Forall_nth_error
       _ _
       (List.map slbr_root_sizes (slsbs_recipes shape))
       (Tiling.PL.ip_nth_ext ip1)
       (slbr_root_sizes recipe1)
       Hroot_prefixes Hroot_sizes_map1)
    as Hroot_prefix1.
  pose proof
    (Tiling.Forall_nth_error
       _ _
       (List.map slbr_root_sizes (slsbs_recipes shape))
       (Tiling.PL.ip_nth_ext ip2)
       (slbr_root_sizes recipe2)
       Hroot_prefixes Hroot_sizes_map2)
    as Hroot_prefix2.
  pose proof
    (Tiling.Forall_nth_error
       _ _
       (List.map slbr_child_sizes (slsbs_recipes shape))
       (Tiling.PL.ip_nth_ext ip1)
       (slbr_child_sizes recipe1)
       Hchild_prefixes Hchild_sizes_map1)
    as Hchild_prefix1.
  pose proof
    (Tiling.Forall_nth_error
       _ _
       (List.map slbr_child_sizes (slsbs_recipes shape))
       (Tiling.PL.ip_nth_ext ip2)
       (slbr_child_sizes recipe2)
       Hchild_prefixes Hchild_sizes_map2)
    as Hchild_prefix2.
  destruct
    (nth_error (slsbs_rows shape) (Tiling.PL.ip_nth_ext ip1))
    as [semantic_rows1|] eqn:Hsemantic_rows1.
  2:{ exfalso. apply nth_error_None in Hsemantic_rows1. lia. }
  destruct
    (nth_error (slsbs_rows shape) (Tiling.PL.ip_nth_ext ip2))
    as [semantic_rows2|] eqn:Hsemantic_rows2.
  2:{ exfalso. apply nth_error_None in Hsemantic_rows2. lia. }
  destruct
    (nth_error lifted_rows (Tiling.PL.ip_nth_ext ip1))
    as [lifted1|] eqn:Hlifted1.
  2:{ exfalso. apply nth_error_None in Hlifted1. lia. }
  destruct
    (nth_error lifted_rows (Tiling.PL.ip_nth_ext ip2))
    as [lifted2|] eqn:Hlifted2.
  2:{ exfalso. apply nth_error_None in Hlifted2. lia. }
  pose proof
    (compact_semantic_schedules_nth_error
       (List.length before_ctxt) before_pis
       (List.map slbr_root_rows (slsbs_recipes shape))
       (slsbs_mask shape) (slsbs_rows shape)
       (Tiling.PL.ip_nth_ext ip1)
       before_pi1 (slbr_root_rows recipe1) semantic_rows1
       Hcompact Hbefore1 Hraw_map1 Hsemantic_rows1)
    as Hsemantic_rows_def1.
  pose proof
    (compact_semantic_schedules_nth_error
       (List.length before_ctxt) before_pis
       (List.map slbr_root_rows (slsbs_recipes shape))
       (slsbs_mask shape) (slsbs_rows shape)
       (Tiling.PL.ip_nth_ext ip2)
       before_pi2 (slbr_root_rows recipe2) semantic_rows2
       Hcompact Hbefore2 Hraw_map2 Hsemantic_rows2)
    as Hsemantic_rows_def2.
  pose proof
    (lift_semantic_schedules_for_tiling_nth_error
       (List.length before_ctxt) ws (slsbs_rows shape) lifted_rows
       (Tiling.PL.ip_nth_ext ip1) w1 semantic_rows1 lifted1
       Hlift Hw1 Hsemantic_rows1 Hlifted1)
    as Hlifted_def1.
  pose proof
    (lift_semantic_schedules_for_tiling_nth_error
       (List.length before_ctxt) ws (slsbs_rows shape) lifted_rows
       (Tiling.PL.ip_nth_ext ip2) w2 semantic_rows2 lifted2
       Hlift Hw2 Hsemantic_rows2 Hlifted2)
    as Hlifted_def2.
  destruct
    (second_level_semantic_schedules_match_nth_error
       (slsbs_layout shape)
       (List.length before_ctxt)
       (List.length (slsbs_mask shape))
       before_pis after_pis ws (slsbs_recipes shape)
       (slsbs_rows shape)
       (Tiling.PL.ip_nth_ext ip1)
       before_pi1 after_pi1 w1 recipe1 semantic_rows1
       Hschedules Hbefore1 Hafter1 Hw1 Hrecipe1 Hsemantic_rows1)
    as [Hbefore_match1 Hafter_match1].
  destruct
    (second_level_semantic_schedules_match_nth_error
       (slsbs_layout shape)
       (List.length before_ctxt)
       (List.length (slsbs_mask shape))
       before_pis after_pis ws (slsbs_recipes shape)
       (slsbs_rows shape)
       (Tiling.PL.ip_nth_ext ip2)
       before_pi2 after_pi2 w2 recipe2 semantic_rows2
       Hschedules Hbefore2 Hafter2 Hw2 Hrecipe2 Hsemantic_rows2)
    as [Hbefore_match2 Hafter_match2].
  pose proof
    (Tiling.nth_error_compose_tiling_pinstrs_ext_from_after
       (List.length envv) before_pis after_pis ws
       (Tiling.PL.ip_nth_ext ip1)
       before_pi1 after_pi1 w1 Hbefore1 Hafter1 Hw1)
    as Hcomposed1.
  pose proof
    (Tiling.nth_error_compose_tiling_pinstrs_ext_from_after
       (List.length envv) before_pis after_pis ws
       (Tiling.PL.ip_nth_ext ip2)
       before_pi2 after_pi2 w2 Hbefore2 Hafter2 Hw2)
    as Hcomposed2.
  pose proof
    (Tiling.tiling_rel_pprog_structure_source_nth
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       (List.map Tiling.compiled_pinstr_tiling_witness ws)
       (Tiling.PL.ip_nth_ext ip1)
       before_pi1 after_pi1
       (Tiling.compiled_pinstr_tiling_witness w1)
       Hprog Hbefore1 Hafter1
       (Tiling.nth_error_map_some
          _ _ Tiling.compiled_pinstr_tiling_witness
          ws (Tiling.PL.ip_nth_ext ip1) w1 Hw1))
    as Hstmt1.
  pose proof
    (Tiling.tiling_rel_pprog_structure_source_nth
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       (List.map Tiling.compiled_pinstr_tiling_witness ws)
       (Tiling.PL.ip_nth_ext ip2)
       before_pi2 after_pi2
       (Tiling.compiled_pinstr_tiling_witness w2)
       Hprog Hbefore2 Hafter2
       (Tiling.nth_error_map_some
          _ _ Tiling.compiled_pinstr_tiling_witness
          ws (Tiling.PL.ip_nth_ext ip2) w2 Hw2))
    as Hstmt2.
  pose proof
    (tiling_rel_pinstr_structure_source_after_matches
       (List.length before_ctxt) before_pi1 after_pi1 w1
       Hstmt1 Hpoint_depth1)
    as Hafter_wit1.
  pose proof
    (tiling_rel_pinstr_structure_source_after_matches
       (List.length before_ctxt) before_pi2 after_pi2 w2
       Hstmt2 Hpoint_depth2)
    as Hafter_wit2.
  destruct Hafter_wit1 as [Hafter_pw1 Hafter_wit_depth1].
  destruct Hafter_wit2 as [Hafter_pw2 Hafter_wit_depth2].
  assert
    (Hafter_depth1 :
       Tiling.PL.pi_depth after_pi1 =
       (Tiling.PL.pi_depth before_pi1 +
        List.length (stw_links w1))%nat).
  {
    unfold Tiling.tiling_rel_pinstr_structure_source in Hstmt1.
    tauto.
  }
  assert
    (Hafter_depth2 :
       Tiling.PL.pi_depth after_pi2 =
       (Tiling.PL.pi_depth before_pi2 +
        List.length (stw_links w2))%nat).
  {
    unfold Tiling.tiling_rel_pinstr_structure_source in Hstmt2.
    tauto.
  }
  (* Stage 3: decompose each target point and evaluate root tiles, child tiles,
     and the represented source band under the selected layout. *)
  set
    (added1 :=
       Tiling.tiled_added_part
         (List.length envv) (List.length (stw_links w1))
         (Tiling.PL.ip_index_ext ip1)).
  set
    (point1 :=
       Tiling.tiled_point_part
         (List.length envv) (List.length (stw_links w1))
         (Tiling.PL.ip_index_ext ip1)).
  set
    (added2 :=
       Tiling.tiled_added_part
         (List.length envv) (List.length (stw_links w2))
         (Tiling.PL.ip_index_ext ip2)).
  set
    (point2 :=
       Tiling.tiled_point_part
         (List.length envv) (List.length (stw_links w2))
         (Tiling.PL.ip_index_ext ip2)).
  assert (Hadded_len1 : List.length added1 = List.length (stw_links w1)).
  {
    subst added1.
    eapply Tiling.tiled_added_part_length
      with (point_dim := stw_point_dim w1).
    rewrite Hidx_len1, Hafter_depth1, <- Hpoint_depth1.
    lia.
  }
  assert (Hadded_len2 : List.length added2 = List.length (stw_links w2)).
  {
    subst added2.
    eapply Tiling.tiled_added_part_length
      with (point_dim := stw_point_dim w2).
    rewrite Hidx_len2, Hafter_depth2, <- Hpoint_depth2.
    lia.
  }
  assert (Hpoint_len1 : List.length point1 = stw_point_dim w1).
  {
    subst point1.
    eapply Tiling.tiled_point_part_length
      with (added_dims := List.length (stw_links w1)).
    rewrite Hidx_len1, Hafter_depth1, <- Hpoint_depth1.
    lia.
  }
  assert (Hpoint_len2 : List.length point2 = stw_point_dim w2).
  {
    subst point2.
    eapply Tiling.tiled_point_part_length
      with (added_dims := List.length (stw_links w2)).
    rewrite Hidx_len2, Hafter_depth2, <- Hpoint_depth2.
    lia.
  }
  assert
    (Hidx_split1 :
       Tiling.PL.ip_index_ext ip1 = envv ++ added1 ++ point1).
  {
    subst added1 point1.
    transitivity
      (firstn (List.length envv) (Tiling.PL.ip_index_ext ip1) ++
       Tiling.tiled_added_part
         (List.length envv) (List.length (stw_links w1))
         (Tiling.PL.ip_index_ext ip1) ++
       Tiling.tiled_point_part
         (List.length envv) (List.length (stw_links w1))
         (Tiling.PL.ip_index_ext ip1)).
    - apply Tiling.tiled_index_split.
    - rewrite Hpref1. reflexivity.
  }
  assert
    (Hidx_split2 :
       Tiling.PL.ip_index_ext ip2 = envv ++ added2 ++ point2).
  {
    subst added2 point2.
    transitivity
      (firstn (List.length envv) (Tiling.PL.ip_index_ext ip2) ++
       Tiling.tiled_added_part
         (List.length envv) (List.length (stw_links w2))
         (Tiling.PL.ip_index_ext ip2) ++
       Tiling.tiled_point_part
         (List.length envv) (List.length (stw_links w2))
         (Tiling.PL.ip_index_ext ip2)).
    - apply Tiling.tiled_index_split.
    - rewrite Hpref2. reflexivity.
  }
  unfold Tiling.compose_tiling_pinstr_ext in Hbel1, Hbel2.
  destruct Hbel1 as
    [Hafter_dom1 [_ [_ [Hts11 [Hts21 [_ _]]]]]].
  destruct Hbel2 as
    [Hafter_dom2 [_ [_ [Hts12 [Hts22 [_ _]]]]]].
  assert
    (Hts11_old :
       Tiling.PL.ip_time_stamp1_ext ip1 =
       affine_product (Tiling.PL.pi_schedule before_pi1)
         (envv ++ point1)).
  {
    rewrite Hts11.
    cbn [Tiling.compose_tiling_pinstr_ext].
    rewrite Hidx_split1.
    unfold Tiling.lift_schedule_after_env.
    eapply Tiling.lift_affine_function_after_env_eval.
    - reflexivity.
    - exact Hadded_len1.
  }
  assert
    (Hts12_old :
       Tiling.PL.ip_time_stamp1_ext ip2 =
       affine_product (Tiling.PL.pi_schedule before_pi2)
         (envv ++ point2)).
  {
    rewrite Hts12.
    cbn [Tiling.compose_tiling_pinstr_ext].
    rewrite Hidx_split2.
    unfold Tiling.lift_schedule_after_env.
    eapply Tiling.lift_affine_function_after_env_eval.
    - reflexivity.
    - exact Hadded_len2.
  }
  assert
    (Hts21_after :
       Tiling.PL.ip_time_stamp2_ext ip1 =
       affine_product (Tiling.PL.pi_schedule after_pi1)
         (Tiling.PL.ip_index_ext ip1)).
  {
    rewrite Hts21.
    cbn [Tiling.compose_tiling_pinstr_ext].
    reflexivity.
  }
  assert
    (Hts22_after :
       Tiling.PL.ip_time_stamp2_ext ip2 =
       affine_product (Tiling.PL.pi_schedule after_pi2)
         (Tiling.PL.ip_index_ext ip2)).
  {
    rewrite Hts22.
    cbn [Tiling.compose_tiling_pinstr_ext].
    reflexivity.
  }
  assert
    (Hstmt1_env :
       Tiling.tiling_rel_pinstr_structure_source
         (List.length envv) before_pi1 after_pi1
         (Tiling.compiled_pinstr_tiling_witness w1)).
  {
    rewrite <- Hlen_env. exact Hstmt1.
  }
  assert
    (Hstmt2_env :
       Tiling.tiling_rel_pinstr_structure_source
         (List.length envv) before_pi2 after_pi2
         (Tiling.compiled_pinstr_tiling_witness w2)).
  {
    rewrite <- Hlen_env. exact Hstmt2.
  }
  destruct Hwf_stmt1 as [Hwf_stmt1 Hparams1].
  destruct Hwf_stmt2 as [Hwf_stmt2 Hparams2].
  assert
    (Hadded_eq1 :
       added1 = eval_tile_links [] point1 envv (stw_links w1)).
  {
    pose proof
      (Tiling.tiling_rel_pinstr_structure_source_domain_complete
         envv before_pi1 after_pi1
         (Tiling.compiled_pinstr_tiling_witness w1)
         added1 point1 Hstmt1_env
         (Tiling.wf_compiled_pinstr_tiling_witness w1)
         (Tiling.compiled_pinstr_tiling_witness_matches w1)
         Hadded_len1 Hpoint_len1
         (conj Hwf_stmt1 Hparams1) Hpositive1)
      as Hcomplete.
    rewrite Hidx_split1 in Hafter_dom1.
    specialize (Hcomplete Hafter_dom1).
    tauto.
  }
  assert
    (Hadded_eq2 :
       added2 = eval_tile_links [] point2 envv (stw_links w2)).
  {
    pose proof
      (Tiling.tiling_rel_pinstr_structure_source_domain_complete
         envv before_pi2 after_pi2
         (Tiling.compiled_pinstr_tiling_witness w2)
         added2 point2 Hstmt2_env
         (Tiling.wf_compiled_pinstr_tiling_witness w2)
         (Tiling.compiled_pinstr_tiling_witness_matches w2)
         Hadded_len2 Hpoint_len2
         (conj Hwf_stmt2 Hparams2) Hpositive2)
      as Hcomplete.
    rewrite Hidx_split2 in Hafter_dom2.
    specialize (Hcomplete Hafter_dom2).
    tauto.
  }
  set (roots1 := second_level_root_tiles recipe1 envv point1).
  set (children1 := second_level_child_tiles recipe1 envv point1).
  set (roots2 := second_level_root_tiles recipe2 envv point2).
  set (children2 := second_level_child_tiles recipe2 envv point2).
  assert
    (Hadded_tiles1 :
       added1 = interleave_root_child_tiles roots1 children1).
  {
    rewrite Hadded_eq1.
    subst roots1 children1.
    change
      (eval_tile_links [] point1 envv (stw_links w1) =
       [] ++
       interleave_root_child_tiles
         (second_level_root_tiles recipe1 envv point1)
         (second_level_child_tiles recipe1 envv point1)).
    exact
      (eval_tile_links_from_second_level_recipe_spec
         _ _ _ _ Hspec1 [] point1 envv eq_refl Hpoint_len1
         Hwf_stmt1 Hparams1).
  }
  assert
    (Hadded_tiles2 :
       added2 = interleave_root_child_tiles roots2 children2).
  {
    rewrite Hadded_eq2.
    subst roots2 children2.
    change
      (eval_tile_links [] point2 envv (stw_links w2) =
       [] ++
       interleave_root_child_tiles
         (second_level_root_tiles recipe2 envv point2)
         (second_level_child_tiles recipe2 envv point2)).
    exact
      (eval_tile_links_from_second_level_recipe_spec
         _ _ _ _ Hspec2 [] point2 envv eq_refl Hpoint_len2
         Hwf_stmt2 Hparams2).
  }
  assert
    (Hlinks_len1 :
       List.length (stw_links w1) =
       (2 * List.length (slbr_root_rows recipe1))%nat).
  {
    eapply second_level_band_recipe_spec_links_length.
    exact Hspec1.
  }
  assert
    (Hlinks_len2 :
       List.length (stw_links w2) =
       (2 * List.length (slbr_root_rows recipe2))%nat).
  {
    eapply second_level_band_recipe_spec_links_length.
    exact Hspec2.
  }
  assert
    (Hroots_children1 :
       List.length roots1 = List.length children1).
  {
    subst roots1 children1.
    unfold second_level_child_tiles.
    rewrite List.map_length, combine_length.
    rewrite second_level_root_tiles_length by exact Hroot_len1.
    lia.
  }
  assert
    (Hroots_children2 :
       List.length roots2 = List.length children2).
  {
    subst roots2 children2.
    unfold second_level_child_tiles.
    rewrite List.map_length, combine_length.
    rewrite second_level_root_tiles_length by exact Hroot_len2.
    lia.
  }
  assert
    (Hroots_len_rows1 :
       List.length roots1 =
       List.length (slbr_root_rows recipe1)).
  {
    subst roots1.
    rewrite second_level_root_tiles_length by exact Hroot_len1.
    lia.
  }
  assert
    (Hroots_len_rows2 :
       List.length roots2 =
       List.length (slbr_root_rows recipe2)).
  {
    subst roots2.
    rewrite second_level_root_tiles_length by exact Hroot_len2.
    lia.
  }
  set
    (raw_values1 :=
       affine_product
         (Tiling.PL.pad_schedule_to_len
            (List.length envv + stw_point_dim w1)
            (List.length (slsbs_mask shape))
            (slbr_root_rows recipe1))
         (envv ++ point1)).
  set
    (raw_values2 :=
       affine_product
         (Tiling.PL.pad_schedule_to_len
            (List.length envv + stw_point_dim w2)
            (List.length (slsbs_mask shape))
            (slbr_root_rows recipe2))
         (envv ++ point2)).
  set
    (semantic_values1 :=
       affine_product semantic_rows1 (envv ++ point1)).
  set
    (semantic_values2 :=
       affine_product semantic_rows2 (envv ++ point2)).
  set
    (global_tiles1 :=
       semantic_second_level_global_tile_block
         (slsbs_layout shape) raw_values1
         (slsbs_global_root_sizes shape)
         (slsbs_global_child_sizes shape)).
  set
    (global_tiles2 :=
       semantic_second_level_global_tile_block
         (slsbs_layout shape) raw_values2
         (slsbs_global_root_sizes shape)
         (slsbs_global_child_sizes shape)).
  assert
    (Hraw_bound1 :
       (List.length (slbr_root_rows recipe1) <=
        List.length (slsbs_mask shape))%nat).
  {
    rewrite Hmask.
    unfold global_semantic_schedule_mask.
    rewrite List.map_length, seq_length.
    eapply max_schedule_length_ge_nth_error.
    exact Hraw_map1.
  }
  assert
    (Hraw_bound2 :
       (List.length (slbr_root_rows recipe2) <=
        List.length (slsbs_mask shape))%nat).
  {
    rewrite Hmask.
    unfold global_semantic_schedule_mask.
    rewrite List.map_length, seq_length.
    eapply max_schedule_length_ge_nth_error.
    exact Hraw_map2.
  }
  assert
    (Hsemantic_eval1 :
       semantic_values1 =
       select_by_mask (slsbs_mask shape) raw_values1).
  {
    subst semantic_values1 raw_values1.
    rewrite Hsemantic_rows_def1.
    unfold compact_semantic_schedule.
    rewrite affine_product_select_by_mask.
    rewrite Hlen_env.
    rewrite <- Hpoint_depth1.
    reflexivity.
  }
  assert
    (Hsemantic_eval2 :
       semantic_values2 =
       select_by_mask (slsbs_mask shape) raw_values2).
  {
    subst semantic_values2 raw_values2.
    rewrite Hsemantic_rows_def2.
    unfold compact_semantic_schedule.
    rewrite affine_product_select_by_mask.
    rewrite Hlen_env.
    rewrite <- Hpoint_depth2.
    reflexivity.
  }
  assert
    (Hzero1 :
       zero_on_false (slsbs_mask shape) raw_values1).
  {
    subst raw_values1.
    rewrite Hmask.
    assert
      (Hmask_len :
         List.length
           (global_semantic_schedule_mask
              (List.map slbr_root_rows (slsbs_recipes shape))) =
         max_schedule_length
           (List.map slbr_root_rows (slsbs_recipes shape))).
    {
      unfold global_semantic_schedule_mask.
      rewrite List.map_length, seq_length.
      reflexivity.
    }
    rewrite Hmask_len.
    eapply global_semantic_schedule_mask_zero_on_false.
    eapply nth_error_In.
    exact Hraw_map1.
  }
  assert
    (Hzero2 :
       zero_on_false (slsbs_mask shape) raw_values2).
  {
    subst raw_values2.
    rewrite Hmask.
    assert
      (Hmask_len :
         List.length
           (global_semantic_schedule_mask
              (List.map slbr_root_rows (slsbs_recipes shape))) =
         max_schedule_length
           (List.map slbr_root_rows (slsbs_recipes shape))).
    {
      unfold global_semantic_schedule_mask.
      rewrite List.map_length, seq_length.
      reflexivity.
    }
    rewrite Hmask_len.
    eapply global_semantic_schedule_mask_zero_on_false.
    eapply nth_error_In.
    exact Hraw_map2.
  }
  assert
    (Hraw_values_eval1 :
       raw_values1 =
       affine_product (slbr_root_rows recipe1) (envv ++ point1) ++
       repeat 0%Z
         (List.length (slsbs_mask shape) -
          List.length (slbr_root_rows recipe1))).
  {
    subst raw_values1.
    eapply affine_product_pad_schedule_to_len.
    exact Hraw_bound1.
  }
  assert
    (Hraw_values_eval2 :
       raw_values2 =
       affine_product (slbr_root_rows recipe2) (envv ++ point2) ++
       repeat 0%Z
         (List.length (slsbs_mask shape) -
          List.length (slbr_root_rows recipe2))).
  {
    subst raw_values2.
    eapply affine_product_pad_schedule_to_len.
    exact Hraw_bound2.
  }
  assert
    (Hglobal_tiles_local1 :
       global_tiles1 =
       match slsbs_layout shape with
       | SecondLevelGrouped =>
           children1 ++
           repeat 0%Z
             (List.length (slsbs_global_child_sizes shape) -
              List.length (slbr_child_sizes recipe1)) ++
           roots1 ++
           repeat 0%Z
             (List.length (slsbs_global_root_sizes shape) -
              List.length (slbr_root_sizes recipe1))
       | SecondLevelInterleaved =>
           added1 ++
           repeat 0%Z
             (2 *
              (List.length (slsbs_global_root_sizes shape) -
               List.length (slbr_root_sizes recipe1)))
       end).
  {
    subst global_tiles1.
    rewrite Hraw_values_eval1.
    assert
      (Haffine_len :
         List.length
           (affine_product
              (slbr_root_rows recipe1) (envv ++ point1)) =
         List.length (slbr_root_rows recipe1)).
    {
      unfold affine_product.
      rewrite List.map_length.
      reflexivity.
    }
    assert
      (Haffine_root_size_len1 :
         List.length
           (affine_product
              (slbr_root_rows recipe1) (envv ++ point1)) =
         List.length (slbr_root_sizes recipe1)) by lia.
    assert
      (Haffine_child_size_len1 :
         List.length
           (affine_product
              (slbr_root_rows recipe1) (envv ++ point1)) =
         List.length (slbr_child_sizes recipe1)) by lia.
    assert
      (Hglobal_sizes_len1 :
         List.length (slsbs_global_root_sizes shape) =
         List.length (slsbs_global_child_sizes shape)) by lia.
    replace
      (List.length (slsbs_mask shape) -
       List.length (slbr_root_rows recipe1))%nat
      with
      (List.length (slsbs_global_root_sizes shape) -
       List.length
         (affine_product
            (slbr_root_rows recipe1) (envv ++ point1)))%nat
      by lia.
    pose proof
      (semantic_second_level_global_tile_block_local
         (slsbs_layout shape)
         (affine_product
            (slbr_root_rows recipe1) (envv ++ point1))
         (slbr_root_sizes recipe1)
         (slbr_child_sizes recipe1)
         (slsbs_global_root_sizes shape)
         (slsbs_global_child_sizes shape)
         Haffine_root_size_len1 Haffine_child_size_len1
         Hroot_prefix1 Hchild_prefix1 Hglobal_sizes_len1)
      as Hlocal.
    destruct (slsbs_layout shape); simpl in *.
    - subst roots1 children1.
      unfold second_level_root_tiles,
             second_level_child_tiles,
             semantic_quotient_tiles in *.
      exact Hlocal.
    - rewrite Hadded_tiles1.
      subst roots1 children1.
      unfold second_level_root_tiles,
             second_level_child_tiles,
             semantic_quotient_tiles in *.
      exact Hlocal.
  }
  assert
    (Hglobal_tiles_local2 :
       global_tiles2 =
       match slsbs_layout shape with
       | SecondLevelGrouped =>
           children2 ++
           repeat 0%Z
             (List.length (slsbs_global_child_sizes shape) -
              List.length (slbr_child_sizes recipe2)) ++
           roots2 ++
           repeat 0%Z
             (List.length (slsbs_global_root_sizes shape) -
              List.length (slbr_root_sizes recipe2))
       | SecondLevelInterleaved =>
           added2 ++
           repeat 0%Z
             (2 *
              (List.length (slsbs_global_root_sizes shape) -
               List.length (slbr_root_sizes recipe2)))
       end).
  {
    subst global_tiles2.
    rewrite Hraw_values_eval2.
    assert
      (Haffine_len :
         List.length
           (affine_product
              (slbr_root_rows recipe2) (envv ++ point2)) =
         List.length (slbr_root_rows recipe2)).
    {
      unfold affine_product.
      rewrite List.map_length.
      reflexivity.
    }
    assert
      (Haffine_root_size_len :
         List.length
           (affine_product
              (slbr_root_rows recipe2) (envv ++ point2)) =
         List.length (slbr_root_sizes recipe2)) by lia.
    assert
      (Haffine_child_size_len :
         List.length
           (affine_product
              (slbr_root_rows recipe2) (envv ++ point2)) =
         List.length (slbr_child_sizes recipe2)) by lia.
    assert
      (Hglobal_sizes_len2 :
         List.length (slsbs_global_root_sizes shape) =
         List.length (slsbs_global_child_sizes shape)) by lia.
    replace
      (List.length (slsbs_mask shape) -
       List.length (slbr_root_rows recipe2))%nat
      with
      (List.length (slsbs_global_root_sizes shape) -
       List.length
         (affine_product
            (slbr_root_rows recipe2) (envv ++ point2)))%nat
      by lia.
    pose proof
      (semantic_second_level_global_tile_block_local
         (slsbs_layout shape)
         (affine_product
            (slbr_root_rows recipe2) (envv ++ point2))
         (slbr_root_sizes recipe2)
         (slbr_child_sizes recipe2)
         (slsbs_global_root_sizes shape)
         (slsbs_global_child_sizes shape)
         Haffine_root_size_len Haffine_child_size_len
         Hroot_prefix2 Hchild_prefix2 Hglobal_sizes_len2)
      as Hlocal.
    destruct (slsbs_layout shape); simpl in *.
    - subst roots2 children2.
      unfold second_level_root_tiles,
             second_level_child_tiles,
             semantic_quotient_tiles in *.
      exact Hlocal.
    - rewrite Hadded_tiles2.
      subst roots2 children2.
      unfold second_level_root_tiles,
             second_level_child_tiles,
             semantic_quotient_tiles in *.
      exact Hlocal.
  }
  assert
    (Hsemantic_len :
       List.length semantic_values1 =
       List.length semantic_values2).
  {
    subst semantic_values1 semantic_values2.
    unfold affine_product.
    rewrite !List.map_length.
    rewrite Hsemantic_rows_def1, Hsemantic_rows_def2.
    unfold compact_semantic_schedule.
    eapply select_by_mask_length_same.
    - unfold Tiling.PL.pad_schedule_to_len.
      rewrite app_length, repeat_length.
      lia.
    - unfold Tiling.PL.pad_schedule_to_len.
      rewrite app_length, repeat_length.
      lia.
  }
  assert
    (Htiles_eq :
       semantic_values1 = semantic_values2 ->
       global_tiles1 = global_tiles2).
  {
    intro Hsemantic_eq.
    assert
      (Hselect :
         select_by_mask (slsbs_mask shape) raw_values1 =
         select_by_mask (slsbs_mask shape) raw_values2).
    {
      rewrite <- Hsemantic_eval1, <- Hsemantic_eval2.
      exact Hsemantic_eq.
    }
    pose proof
      (select_by_mask_eq_reflect
         (slsbs_mask shape) raw_values1 raw_values2
         Hzero1 Hzero2 Hselect)
      as Hraw_eq.
    subst global_tiles1 global_tiles2.
    now rewrite Hraw_eq.
  }
  assert
    (Htiles_mono :
       listz_pointwise_le semantic_values1 semantic_values2 ->
       listz_pointwise_le global_tiles1 global_tiles2).
  {
    intro Hsemantic_le.
    assert
      (Hraw_le : listz_pointwise_le raw_values1 raw_values2).
    {
      eapply select_by_mask_le_reflect; [exact Hzero1|exact Hzero2|].
      rewrite <- Hsemantic_eval1, <- Hsemantic_eval2.
      exact Hsemantic_le.
    }
    subst global_tiles1 global_tiles2.
    eapply semantic_second_level_global_tile_block_pointwise_le.
    - exact Hraw_le.
    - exact Hglobal_root_positive.
    - exact Hglobal_child_positive.
    - pose proof (zero_on_false_length _ _ Hzero1) as Hraw_values_len.
      rewrite Hglobal_root_width.
      symmetry.
      exact Hraw_values_len.
    - lia.
  }
  assert
    (Hold_eq1 :
       is_eq
         (Tiling.PL.ip_time_stamp1_ext ip1)
         semantic_values1 = true).
  {
    rewrite Hts11_old.
    subst semantic_values1.
    eapply
      schedule_matches_with_symmetric_trailing_zero_padding_affine_product_is_eq.
    exact Hbefore_match1.
  }
  assert
    (Hold_eq2 :
       is_eq
         (Tiling.PL.ip_time_stamp1_ext ip2)
         semantic_values2 = true).
  {
    rewrite Hts12_old.
    subst semantic_values2.
    eapply
      schedule_matches_with_symmetric_trailing_zero_padding_affine_product_is_eq.
    exact Hbefore_match2.
  }
  assert
    (Htarget_eval1 :
       affine_product
         (semantic_second_level_target_schedule
            (slsbs_layout shape)
            (List.length before_ctxt)
            (List.length (slsbs_mask shape))
            semantic_rows1 w1 recipe1)
         (envv ++ added1 ++ point1) =
       match slsbs_layout shape with
       | SecondLevelGrouped =>
           children1 ++
           repeat 0%Z
             (List.length (slsbs_global_child_sizes shape) -
              List.length (slbr_child_sizes recipe1)) ++
           roots1 ++
           repeat 0%Z
             (List.length (slsbs_global_root_sizes shape) -
              List.length (slbr_root_sizes recipe1)) ++
           semantic_values1
       | SecondLevelInterleaved =>
           added1 ++
           repeat 0%Z
             (2 *
              (List.length (slsbs_global_root_sizes shape) -
               List.length (slbr_root_sizes recipe1))) ++
           semantic_values1
       end).
  {
    rewrite
      (semantic_second_level_target_schedule_eval
         (slsbs_layout shape)
         (List.length before_ctxt)
         (List.length (slsbs_mask shape))
         semantic_rows1 w1 recipe1 envv added1 point1).
    2:{ symmetry. exact Hlen_env. }
    2:{ rewrite Hadded_len1, Hlinks_len1. reflexivity. }
    2:{ exact Hpoint_len1. }
    2:{ exact Hraw_bound1. }
    subst semantic_values1.
    destruct (slsbs_layout shape); simpl.
    - rewrite Hadded_tiles1.
      rewrite <- Hroots_len_rows1.
      rewrite map_nth_child_positions_interleave
        by exact Hroots_children1.
      rewrite map_nth_root_positions_interleave
        by exact Hroots_children1.
      rewrite Hglobal_child_width, Hglobal_root_width.
      rewrite <- Hchild_len1, <- Hroot_len1.
      rewrite <- Hroots_len_rows1.
      reflexivity.
    - rewrite Hglobal_root_width, <- Hroot_len1.
      reflexivity.
  }
  assert
    (Htarget_eval2 :
       affine_product
         (semantic_second_level_target_schedule
            (slsbs_layout shape)
            (List.length before_ctxt)
            (List.length (slsbs_mask shape))
            semantic_rows2 w2 recipe2)
         (envv ++ added2 ++ point2) =
       match slsbs_layout shape with
       | SecondLevelGrouped =>
           children2 ++
           repeat 0%Z
             (List.length (slsbs_global_child_sizes shape) -
              List.length (slbr_child_sizes recipe2)) ++
           roots2 ++
           repeat 0%Z
             (List.length (slsbs_global_root_sizes shape) -
              List.length (slbr_root_sizes recipe2)) ++
           semantic_values2
       | SecondLevelInterleaved =>
           added2 ++
           repeat 0%Z
             (2 *
              (List.length (slsbs_global_root_sizes shape) -
               List.length (slbr_root_sizes recipe2))) ++
           semantic_values2
       end).
  {
    rewrite
      (semantic_second_level_target_schedule_eval
         (slsbs_layout shape)
         (List.length before_ctxt)
         (List.length (slsbs_mask shape))
         semantic_rows2 w2 recipe2 envv added2 point2).
    2:{ symmetry. exact Hlen_env. }
    2:{ rewrite Hadded_len2, Hlinks_len2. reflexivity. }
    2:{ exact Hpoint_len2. }
    2:{ exact Hraw_bound2. }
    subst semantic_values2.
    destruct (slsbs_layout shape); simpl.
    - rewrite Hadded_tiles2.
      rewrite <- Hroots_len_rows2.
      rewrite map_nth_child_positions_interleave
        by exact Hroots_children2.
      rewrite map_nth_root_positions_interleave
        by exact Hroots_children2.
      rewrite Hglobal_child_width, Hglobal_root_width.
      rewrite <- Hchild_len2, <- Hroot_len2.
      rewrite <- Hroots_len_rows2.
      reflexivity.
    - rewrite Hglobal_root_width, <- Hroot_len2.
      reflexivity.
  }
  assert
    (Hnew_eq1 :
       is_eq
         (Tiling.PL.ip_time_stamp2_ext ip1)
         (global_tiles1 ++ semantic_values1) = true).
  {
    rewrite Hts21_after, Hidx_split1.
    pose proof
      (schedule_matches_with_symmetric_trailing_zero_padding_affine_product_is_eq
         (semantic_second_level_target_schedule
            (slsbs_layout shape)
            (List.length before_ctxt)
            (List.length (slsbs_mask shape))
            semantic_rows1 w1 recipe1)
         (Tiling.PL.pi_schedule after_pi1)
         (envv ++ added1 ++ point1) Hafter_match1)
      as Hmatch.
    rewrite Htarget_eval1 in Hmatch.
    rewrite Hglobal_tiles_local1.
    destruct (slsbs_layout shape); simpl in *;
      repeat rewrite app_assoc in *;
      exact Hmatch.
  }
  assert
    (Hnew_eq2 :
       is_eq
         (Tiling.PL.ip_time_stamp2_ext ip2)
         (global_tiles2 ++ semantic_values2) = true).
  {
    rewrite Hts22_after, Hidx_split2.
    pose proof
      (schedule_matches_with_symmetric_trailing_zero_padding_affine_product_is_eq
         (semantic_second_level_target_schedule
            (slsbs_layout shape)
            (List.length before_ctxt)
            (List.length (slsbs_mask shape))
            semantic_rows2 w2 recipe2)
         (Tiling.PL.pi_schedule after_pi2)
         (envv ++ added2 ++ point2) Hafter_match2)
      as Hmatch.
    rewrite Htarget_eval2 in Hmatch.
    rewrite Hglobal_tiles_local2.
    destruct (slsbs_layout shape); simpl in *;
      repeat rewrite app_assoc in *;
      exact Hmatch.
  }
  (* Stage 4: quotient monotonicity at both tile levels rules out a reversal
     unless some checked source-band component decreases. *)
  unfold Tiling.PL.instr_point_ext_old_sched_lt in Hold.
  assert
    (Hnew_not_lt :
       lex_compare
         (Tiling.PL.ip_time_stamp2_ext ip1)
         (Tiling.PL.ip_time_stamp2_ext ip2) <> Lt).
  {
    unfold Tiling.PL.instr_point_ext_new_sched_ge in Hnew.
    destruct Hnew; congruence.
  }
  destruct
    (semantic_stripmined_reversal_implies_decreasing_component
       (Tiling.PL.ip_time_stamp1_ext ip1)
       (Tiling.PL.ip_time_stamp1_ext ip2)
       (Tiling.PL.ip_time_stamp2_ext ip1)
       (Tiling.PL.ip_time_stamp2_ext ip2)
       semantic_values1 semantic_values2
       global_tiles1 global_tiles2
       Hold_eq1 Hold_eq2 Hnew_eq1 Hnew_eq2
       Hsemantic_len Htiles_eq Htiles_mono Hold Hnew_not_lt)
    as [dim [x [y [Hvalue1 [Hvalue2 Hdecrease]]]]].
  (* Stage 5: expose the decreasing component in the lifted rows consumed by
     the direct component checker. *)
  exists
    (Tiling.compose_tiling_pinstr_ext
       (List.length envv) before_pi1 after_pi1 w1),
    (Tiling.compose_tiling_pinstr_ext
       (List.length envv) before_pi2 after_pi2 w2),
    lifted1, lifted2, dim.
  repeat split; try assumption.
  - eapply Nat.lt_le_trans.
    + apply nth_error_Some.
      rewrite Hvalue1.
      discriminate.
    + eapply Nat.le_trans with (m := List.length lifted1).
      * subst semantic_values1.
        unfold affine_product.
        rewrite List.map_length.
        rewrite Hlifted_def1.
        unfold Tiling.lift_schedule_after_env,
               Tiling.lift_affine_function_after_env.
        rewrite List.map_length.
        reflexivity.
      * eapply max_schedule_length_ge_nth_error.
        exact Hlifted1.
  - assert
      (Hlift_eval1 :
         affine_product lifted1 (Tiling.PL.ip_index_ext ip1) =
         semantic_values1).
    {
      rewrite Hlifted_def1, Hidx_split1.
      eapply Tiling.lift_affine_function_after_env_eval.
      - symmetry. exact Hlen_env.
      - exact Hadded_len1.
    }
    assert
      (Hlift_eval2 :
         affine_product lifted2 (Tiling.PL.ip_index_ext ip2) =
         semantic_values2).
    {
      rewrite Hlifted_def2, Hidx_split2.
      eapply Tiling.lift_affine_function_after_env_eval.
      - symmetry. exact Hlen_env.
      - exact Hadded_len2.
    }
    assert
      (Hsemantic_value1 :
         semantic_band_value
           (List.length envv +
            Tiling.PL.pi_depth_ext
              (Tiling.compose_tiling_pinstr_ext
                 (List.length envv) before_pi1 after_pi1 w1))
           dim lifted1 (Tiling.PL.ip_index_ext ip1) = x).
    {
      eapply semantic_band_value_of_nth_error.
      rewrite Hlift_eval1.
      exact Hvalue1.
    }
    assert
      (Hsemantic_value2 :
         semantic_band_value
           (List.length envv +
            Tiling.PL.pi_depth_ext
              (Tiling.compose_tiling_pinstr_ext
                 (List.length envv) before_pi2 after_pi2 w2))
           dim lifted2 (Tiling.PL.ip_index_ext ip2) = y).
    {
      eapply semantic_band_value_of_nth_error.
      rewrite Hlift_eval2.
      exact Hvalue2.
    }
    rewrite Hsemantic_value1, Hsemantic_value2.
    exact Hdecrease.
Qed.

Lemma ordinary_semantic_band_direct_reordering_safe :
  forall before_pis before_ctxt before_vars after_pis ws
         shape lifted_rows envv,
    List.length before_ctxt = List.length envv ->
    TilingCheck.check_pprog_tiling_sourceb
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars) ws = true ->
    ordinary_semantic_band_shape_property_with_witness
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars) ws shape ->
    lift_semantic_schedules_for_tiling
      (List.length before_ctxt) ws (osbs_rows shape) =
      Some lifted_rows ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      after_pis ->
    mayReturn
      (check_semantic_band_components_direct
         (Tiling.compose_tiling_pinstrs_ext_from_after
            (List.length before_ctxt) before_pis after_pis ws)
         lifted_rows (List.length before_ctxt))
      true ->
    pprog_tiling_reordering_safe
      envv before_pis after_pis ws [].
Proof.
  intros before_pis before_ctxt before_vars after_pis ws
         shape lifted_rows envv Hlen_env Hsource Hshape Hlift
         Hwf_before Hwf_after Hcomponents.
  pose proof
    (TilingCheck.check_pprog_tiling_sourceb_sound
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars) ws Hsource)
    as [Hprog [_ [Hwf_ws [_ Hdepths]]]].
  assert
    (Hwits :
       Forall2 Tiling.after_matches_tiling_witness after_pis ws).
  {
    eapply
      (tiling_rel_pprog_structure_source_after_matches
         before_pis before_ctxt before_vars
         after_pis before_ctxt before_vars ws); eauto.
  }
  assert
    (Hcomposed_wf :
       Forall
         (Tiling.PL.wf_pinstr_ext_tiling before_ctxt)
         (Tiling.compose_tiling_pinstrs_ext_from_after
            (List.length before_ctxt) before_pis after_pis ws)).
  {
    eapply compose_tiling_pinstrs_ext_from_after_wf_tiling; eauto.
  }
  pose proof Hshape as Hshape_bridge.
  unfold ordinary_semantic_band_shape_property_with_witness in Hshape.
  cbn in Hshape.
  destruct Hshape as
    [_ [_ [data
      [Hdata [_ [_
      [Hcompact [_ [_ Hschedules]]]]]]]]].
  assert
    (Hsemantic_cols :
       Forall2
         (fun w rows =>
            exact_listzzs_cols
              (List.length before_ctxt + stw_point_dim w)%nat
              rows)
         ws (osbs_rows shape)).
  {
    eapply ordinary_semantic_rows_exact_cols; eauto.
  }
  pose proof
    (lift_semantic_schedules_for_tiling_exact_cols
       (List.length before_ctxt) ws (osbs_rows shape)
       lifted_rows Hlift Hsemantic_cols)
    as Hlifted_cols.
  assert
    (Hcomposed_cols :
       Forall2
         (fun pi rows =>
            exact_listzzs_cols
              (List.length before_ctxt +
               Tiling.PL.pi_depth_ext pi)%nat rows)
         (Tiling.compose_tiling_pinstrs_ext_from_after
            (List.length before_ctxt) before_pis after_pis ws)
         lifted_rows).
  {
    eapply composed_semantic_rows_exact_cols; eauto.
  }
  assert
    (Hcomponentwise :
       pinstr_list_semantic_componentwise_permutable
         envv
         (Tiling.compose_tiling_pinstrs_ext_from_after
            (List.length before_ctxt) before_pis after_pis ws)
         lifted_rows).
  {
    eapply
      (check_semantic_band_components_direct_sound
         before_ctxt envv
         (Tiling.compose_tiling_pinstrs_ext_from_after
            (List.length before_ctxt) before_pis after_pis ws)
         lifted_rows); eauto.
  }
  eapply semantic_componentwise_permutable_implies_reordering_safe.
  - rewrite Hlen_env in Hcomponentwise.
    exact Hcomponentwise.
  - eapply ordinary_semantic_band_shape_reversal_bridge; eauto.
Qed.


Lemma second_level_semantic_band_direct_reordering_safe :
  forall before_pis before_ctxt before_vars after_pis ws
         shape lifted_rows envv,
    List.length before_ctxt = List.length envv ->
    TilingCheck.check_pprog_tiling_sourceb
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars) ws = true ->
    second_level_semantic_band_shape_property_with_witness
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars) ws shape ->
    lift_semantic_schedules_for_tiling
      (List.length before_ctxt) ws (slsbs_rows shape) =
      Some lifted_rows ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      after_pis ->
    mayReturn
      (check_semantic_band_components_direct
         (Tiling.compose_tiling_pinstrs_ext_from_after
            (List.length before_ctxt) before_pis after_pis ws)
         lifted_rows (List.length before_ctxt))
      true ->
    pprog_tiling_reordering_safe
      envv before_pis after_pis ws [].
Proof.
  intros before_pis before_ctxt before_vars after_pis ws
         shape lifted_rows envv Hlen_env Hsource Hshape Hlift
         Hwf_before Hwf_after Hcomponents.
  pose proof
    (TilingCheck.check_pprog_tiling_sourceb_sound
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars) ws Hsource)
    as [Hprog [_ [Hwf_ws [_ Hdepths]]]].
  assert
    (Hwits :
       Forall2 Tiling.after_matches_tiling_witness after_pis ws).
  {
    eapply
      (tiling_rel_pprog_structure_source_after_matches
         before_pis before_ctxt before_vars
         after_pis before_ctxt before_vars ws); eauto.
  }
  assert
    (Hcomposed_wf :
       Forall
         (Tiling.PL.wf_pinstr_ext_tiling before_ctxt)
         (Tiling.compose_tiling_pinstrs_ext_from_after
            (List.length before_ctxt) before_pis after_pis ws)).
  {
    eapply compose_tiling_pinstrs_ext_from_after_wf_tiling; eauto.
  }
  pose proof Hshape as Hshape_bridge.
  unfold second_level_semantic_band_shape_property_with_witness
    in Hshape.
  cbn in Hshape.
  destruct Hshape as
    [_ [_ [Hrecipes [_ [_ [_
      [Hcompact [_ [_ [_ Hschedules]]]]]]]]]].
  assert
    (Hsemantic_cols :
       Forall2
         (fun w rows =>
            exact_listzzs_cols
              (List.length before_ctxt + stw_point_dim w)%nat
              rows)
         ws (slsbs_rows shape)).
  {
    eapply second_level_semantic_rows_exact_cols; eauto.
  }
  pose proof
    (lift_semantic_schedules_for_tiling_exact_cols
       (List.length before_ctxt) ws (slsbs_rows shape)
       lifted_rows Hlift Hsemantic_cols)
    as Hlifted_cols.
  assert
    (Hcomposed_cols :
       Forall2
         (fun pi lifted =>
            exact_listzzs_cols
              (List.length before_ctxt +
               Tiling.PL.pi_depth_ext pi)%nat
              lifted)
         (Tiling.compose_tiling_pinstrs_ext_from_after
            (List.length before_ctxt) before_pis after_pis ws)
         lifted_rows).
  {
    eapply composed_semantic_rows_exact_cols; eauto.
  }
  assert
    (Hcomponentwise :
       pinstr_list_semantic_componentwise_permutable
         envv
         (Tiling.compose_tiling_pinstrs_ext_from_after
            (List.length before_ctxt) before_pis after_pis ws)
         lifted_rows).
  {
    eapply
      (check_semantic_band_components_direct_sound
         before_ctxt envv
         (Tiling.compose_tiling_pinstrs_ext_from_after
            (List.length before_ctxt) before_pis after_pis ws)
         lifted_rows); eauto.
  }
  eapply semantic_componentwise_permutable_implies_reordering_safe.
  - rewrite Hlen_env in Hcomponentwise.
    exact Hcomponentwise.
  - eapply second_level_semantic_band_shape_reversal_bridge; eauto.
Qed.


Lemma checked_tiling_sourceb_semantic_band_direct_correct_same_ctxt :
  forall before_pis before_ctxt before_vars after_pis ws st1 st2,
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      after_pis ->
    mayReturn
      (checked_tiling_sourceb_semantic_band_direct
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars) ws)
      true ->
    Tiling.PL.instance_list_semantics
      (after_pis, before_ctxt, before_vars) st1 st2 ->
    exists st2',
      Tiling.PL.instance_list_semantics
        (before_pis, before_ctxt, before_vars) st1 st2' /\
      TilingPolIRs.State.eq st2 st2'.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws st1 st2
         Hwf_before Hwf_after Hcheck Hsem.
  destruct
    (checked_tiling_sourceb_semantic_band_direct_true_inv
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars) ws Hcheck)
    as [lifted_rows [Hshape Hcomponents]].
  destruct Hshape as
    [shape lifted_rows0 Hsource Hinfer Hlift Hproperty
    |shape lifted_rows0 Hsource Hordinary Hsecond Hlift Hproperty].
  - eapply
      (tiling_sourceb_validate_correct_with_reordering
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars)
         ws [] st1 st2); [exact Hsource| |exact Hsem].
    simpl.
    intros envv Hlen_env.
    eapply
      (ordinary_semantic_band_direct_reordering_safe
         before_pis before_ctxt before_vars after_pis ws
         shape lifted_rows0 envv); eauto.
  - eapply
      (tiling_sourceb_validate_correct_with_reordering
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars)
         ws [] st1 st2); [exact Hsource| |exact Hsem].
    simpl.
    intros envv Hlen_env.
    eapply
      (second_level_semantic_band_direct_reordering_safe
         before_pis before_ctxt before_vars after_pis ws
         shape lifted_rows0 envv); eauto.
Qed.

End ProgramWideSemanticReconstruction.

(** * Scalar-aware band layouts *)

Section ScalarAwareBands.

(** Scalar-aware ordinary Pluto bands.

    Pluto permits exact scalar scattering rows inside a permutable band.  The
    tile prefix strip-mines loop rows and copies scalar rows unchanged.  This
    representation records which source-band positions are loop rows. *)
Record scalar_aware_band_layout := {
  sabl_start : nat;
  sabl_loop_mask : list bool;
}.

Definition scalar_aware_band
    (layout: scalar_aware_band_layout) : pinstr_tiling_band :=
  {| ptb_start := sabl_start layout;
     ptb_len := List.length (sabl_loop_mask layout) |}.

Definition schedule_row_strict_eqb
    (row1 row2: list Z * Z) : bool :=
  listzzs_strict_eqb [row1] [row2].

Definition schedule_row_point_scalarb
    (env_size: nat)
    (row: list Z * Z) : bool :=
  forallb
    (fun coeff => Z.eqb coeff 0%Z)
    (skipn env_size (fst row)).

Fixpoint consume_scalar_aware_band_tail
    (env_size: nat)
    (sched links: Schedule) : option (list bool) :=
  match links with
  | [] => Some []
  | link :: links' =>
      match sched with
      | [] => None
      | row :: sched' =>
          if schedule_row_strict_eqb row link then
            if schedule_row_point_scalarb env_size row then None
            else
              match links' with
              | [] => Some [true]
              | _ =>
                  match
                    consume_scalar_aware_band_tail
                      env_size sched' links'
                  with
                  | Some mask => Some (true :: mask)
                  | None => None
                  end
              end
          else if schedule_row_point_scalarb env_size row then
            match
              consume_scalar_aware_band_tail env_size sched' links
            with
            | Some mask => Some (false :: mask)
            | None => None
            end
          else None
      end
  end.

Fixpoint find_scalar_aware_band_aux
    (fuel start env_size: nat)
    (sched links: Schedule) : option scalar_aware_band_layout :=
  match fuel with
  | O => None
  | S fuel' =>
      match sched, links with
      | row :: sched', link :: links' =>
          if schedule_row_strict_eqb row link then
            if schedule_row_point_scalarb env_size row then None
            else
              match links' with
              | [] =>
                  Some
                    {| sabl_start := start;
                       sabl_loop_mask := [true] |}
              | _ =>
                  match
                    consume_scalar_aware_band_tail
                      env_size sched' links'
                  with
                  | Some mask =>
                      Some
                        {| sabl_start := start;
                           sabl_loop_mask := true :: mask |}
                  | None =>
                      find_scalar_aware_band_aux
                        fuel' (S start) env_size sched' links
                  end
              end
          else
            find_scalar_aware_band_aux
              fuel' (S start) env_size sched' links
      | _, _ => None
      end
  end.

Definition infer_scalar_aware_band_layout
    (env_size: nat)
    (before: Tiling.PL.PolyInstr)
    (w: statement_tiling_witness)
    : option scalar_aware_band_layout :=
  match schedule_rows_of_links w with
  | Some ((_ :: _) as links) =>
      find_scalar_aware_band_aux
        (S (List.length (Tiling.PL.pi_schedule before)))
        O env_size (Tiling.PL.pi_schedule before) links
  | _ => None
  end.

Fixpoint render_scalar_aware_tile_prefix
    (mask: list bool)
    (band_rows tile_rows: Schedule) : option Schedule :=
  match mask, band_rows with
  | [], [] =>
      match tile_rows with
      | [] => Some []
      | _ => None
      end
  | is_loop :: mask', row :: band_rows' =>
      if is_loop then
        match tile_rows with
        | tile_row :: tile_rows' =>
            match
              render_scalar_aware_tile_prefix
                mask' band_rows' tile_rows'
            with
            | Some rendered => Some (tile_row :: rendered)
            | None => None
            end
        | [] => None
        end
      else
        match
          render_scalar_aware_tile_prefix mask' band_rows' tile_rows
        with
        | Some rendered => Some (row :: rendered)
        | None => None
        end
  | _, _ => None
  end.

Definition scalar_aware_stripmine_schedule_after_env
    (env_size added_dims: nat)
    (before_sched: Schedule)
    (layout: scalar_aware_band_layout) : option Schedule :=
  let lifted :=
    Tiling.lift_schedule_after_env added_dims env_size before_sched in
  let total_cols :=
    match lifted with
    | [] => (env_size + added_dims)%nat
    | (coeffs, _) :: _ => List.length coeffs
    end in
  let band := scalar_aware_band layout in
  let prefix := firstn (ptb_start band) lifted in
  let band_rows :=
    firstn (ptb_len band) (skipn (ptb_start band) lifted) in
  let suffix := skipn (ptb_start band + ptb_len band)%nat lifted in
  match
    render_scalar_aware_tile_prefix
      (sabl_loop_mask layout)
      band_rows
      (Tiling.identity_affine_rows_from
         total_cols env_size added_dims)
  with
  | Some tile_prefix =>
      Some (prefix ++ tile_prefix ++ band_rows ++ suffix)
  | None => None
  end.

Definition scalar_aware_band_layout_eqb
    (layout1 layout2: scalar_aware_band_layout) : bool :=
  Nat.eqb (sabl_start layout1) (sabl_start layout2) &&
  list_bool_strict_eqb
    (sabl_loop_mask layout1) (sabl_loop_mask layout2).

Definition scalar_aware_layout_band_rows
    (layout: scalar_aware_band_layout)
    (sched: Schedule) : Schedule :=
  firstn (List.length (sabl_loop_mask layout))
    (skipn (sabl_start layout) sched).

Definition check_scalar_aware_band_selectionb
    (before: Tiling.PL.PolyInstr)
    (w: statement_tiling_witness)
    (layout: scalar_aware_band_layout) : bool :=
  match schedule_rows_of_links w with
  | Some link_rows =>
      let band_rows :=
        scalar_aware_layout_band_rows
          layout (Tiling.PL.pi_schedule before) in
      negb (Nat.eqb (List.length (sabl_loop_mask layout)) O) &&
      (Nat.eqb (List.length band_rows)
         (List.length (sabl_loop_mask layout)) &&
       listzzs_strict_eqb
         (select_by_mask (sabl_loop_mask layout) band_rows)
         link_rows)
  | None => false
  end.

Fixpoint select_scalar_rows
    (mask: list bool)
    (rows: Schedule) : Schedule :=
  match mask, rows with
  | is_loop :: mask', row :: rows' =>
      if is_loop
      then select_scalar_rows mask' rows'
      else row :: select_scalar_rows mask' rows'
  | _, _ => []
  end.

Fixpoint select_scalar_values
    (mask: list bool)
    (values: list Z) : list Z :=
  match mask, values with
  | is_loop :: mask', value :: values' =>
      if is_loop
      then select_scalar_values mask' values'
      else value :: select_scalar_values mask' values'
  | _, _ => []
  end.

Fixpoint render_scalar_aware_value_prefix
    (mask: list bool)
    (band_values tile_values: list Z) : option (list Z) :=
  match mask, band_values with
  | [], [] =>
      match tile_values with
      | [] => Some []
      | _ => None
      end
  | is_loop :: mask', band_value :: band_values' =>
      if is_loop then
        match tile_values with
        | tile_value :: tile_values' =>
            match
              render_scalar_aware_value_prefix
                mask' band_values' tile_values'
            with
            | Some rendered => Some (tile_value :: rendered)
            | None => None
            end
        | [] => None
        end
      else
        match
          render_scalar_aware_value_prefix
            mask' band_values' tile_values
        with
        | Some rendered => Some (band_value :: rendered)
        | None => None
        end
  | _, _ => None
  end.

Inductive scalar_aware_loop_tiles_monotone :
  list bool -> list Z -> list Z -> list Z -> list Z -> Prop :=
| ScalarAwareLoopTilesMonotoneNil :
    scalar_aware_loop_tiles_monotone [] [] [] [] []
| ScalarAwareLoopTilesMonotoneLoop :
    forall mask band1 band2 tiles1 tiles2 b1 b2 t1 t2,
      ((b1 <= b2)%Z -> (t1 <= t2)%Z) ->
      scalar_aware_loop_tiles_monotone
        mask band1 band2 tiles1 tiles2 ->
      scalar_aware_loop_tiles_monotone
        (true :: mask) (b1 :: band1) (b2 :: band2)
        (t1 :: tiles1) (t2 :: tiles2)
| ScalarAwareLoopTilesMonotoneScalar :
    forall mask band1 band2 tiles1 tiles2 b1 b2,
      scalar_aware_loop_tiles_monotone
        mask band1 band2 tiles1 tiles2 ->
      scalar_aware_loop_tiles_monotone
        (false :: mask) (b1 :: band1) (b2 :: band2)
        tiles1 tiles2.

Definition scalar_aware_loop_tile_values
    (mask: list bool)
    (band_values sizes: list Z) : list Z :=
  List.map
    (fun '(value, size) => Z.div value size)
    (List.combine (select_by_mask mask band_values) sizes).

Lemma scalar_aware_loop_tile_values_monotone :
  forall mask band1 band2 sizes,
    List.length band1 = List.length mask ->
    List.length band2 = List.length mask ->
    List.length (select_by_mask mask band1) = List.length sizes ->
    Forall (fun size => (0 < size)%Z) sizes ->
    scalar_aware_loop_tiles_monotone
      mask band1 band2
      (scalar_aware_loop_tile_values mask band1 sizes)
      (scalar_aware_loop_tile_values mask band2 sizes).
Proof.
  induction mask as [|is_loop mask IH];
    intros band1 band2 sizes Hlen1 Hlen2 Hsizes Hpositive;
    destruct band1 as [|b1 band1];
    destruct band2 as [|b2 band2];
    simpl in *; try discriminate.
  - destruct sizes; [constructor|discriminate].
  - destruct is_loop.
    + simpl in Hsizes.
      destruct sizes as [|size sizes]; [discriminate|].
      inversion Hpositive as [|size0 sizes0 Hsize Hpositive_tail];
        subst.
      injection Hsizes as Hsizes_tail.
      constructor.
      * intro Hle.
        apply Z.div_le_mono; assumption.
      * eapply IH.
        -- lia.
        -- lia.
        -- exact Hsizes_tail.
        -- exact Hpositive_tail.
    + simpl in Hsizes.
      constructor.
      eapply IH.
      * lia.
      * lia.
      * exact Hsizes.
      * exact Hpositive.
Qed.

Lemma scalar_aware_prefix_gt_implies_active_decrease :
  forall mask band1 band2 tiles1 tiles2,
    scalar_aware_loop_tiles_monotone
      mask band1 band2 tiles1 tiles2 ->
    forall mixed1 mixed2,
      render_scalar_aware_value_prefix
        mask band1 tiles1 = Some mixed1 ->
      render_scalar_aware_value_prefix
        mask band2 tiles2 = Some mixed2 ->
      lex_compare mixed1 mixed2 = Gt ->
      exists dim x y,
        (dim < List.length mask)%nat /\
        nth_error band1 dim = Some x /\
        nth_error band2 dim = Some y /\
        (x > y)%Z /\
        listz_pointwise_le
          (select_scalar_values
             (firstn dim mask) (firstn dim band2))
          (select_scalar_values
             (firstn dim mask) (firstn dim band1)).
Proof.
  intros mask band1 band2 tiles1 tiles2 Hmono.
  induction Hmono as
    [|mask band1 band2 tiles1 tiles2 b1 b2 t1 t2 Htile Hmono IH
     |mask band1 band2 tiles1 tiles2 b1 b2 Hmono IH];
    intros mixed1 mixed2 Hrender1 Hrender2 Hgt.
  - inversion Hrender1; inversion Hrender2; subst.
    discriminate.
  - simpl in Hrender1, Hrender2.
    destruct
      (render_scalar_aware_value_prefix mask band1 tiles1)
      as [tail1|] eqn:Htail1; try discriminate.
    destruct
      (render_scalar_aware_value_prefix mask band2 tiles2)
      as [tail2|] eqn:Htail2; try discriminate.
    inversion Hrender1; inversion Hrender2; subst mixed1 mixed2.
    simpl in Hgt.
    destruct (Z.compare t1 t2) eqn:Hcmp.
    + destruct
        (IH tail1 tail2 eq_refl eq_refl Hgt)
        as [dim [x [y [Hdim [Hx [Hy [Hxy Hprior]]]]]]].
      exists (S dim), x, y.
      simpl.
      repeat split; try assumption; lia.
    + discriminate.
    + assert (Hsource : (b1 > b2)%Z).
      {
        apply Z.compare_gt_iff in Hcmp.
        destruct (Z_gt_dec b1 b2) as [Hsource|Hnot].
        - exact Hsource.
        - specialize (Htile ltac:(lia)).
          lia.
      }
      exists O, b1, b2.
      simpl.
      split; [lia|].
      split; [reflexivity|].
      split; [reflexivity|].
      split; [exact Hsource|].
      constructor.
  - simpl in Hrender1, Hrender2.
    destruct
      (render_scalar_aware_value_prefix mask band1 tiles1)
      as [tail1|] eqn:Htail1; try discriminate.
    destruct
      (render_scalar_aware_value_prefix mask band2 tiles2)
      as [tail2|] eqn:Htail2; try discriminate.
    inversion Hrender1; inversion Hrender2; subst mixed1 mixed2.
    simpl in Hgt.
    destruct (Z.compare b1 b2) eqn:Hcmp.
    + apply Z.compare_eq_iff in Hcmp.
      destruct
        (IH tail1 tail2 eq_refl eq_refl Hgt)
        as [dim [x [y [Hdim [Hx [Hy [Hxy Hprior]]]]]]].
      exists (S dim), x, y.
      simpl.
      repeat split; try assumption; try lia.
      constructor; [lia|exact Hprior].
    + discriminate.
    + apply Z.compare_gt_iff in Hcmp.
      exists O, b1, b2.
      simpl.
      split; [lia|].
      split; [reflexivity|].
      split; [reflexivity|].
      split; [lia|].
      constructor.
Qed.

Lemma affine_product_select_scalar_rows :
  forall mask rows idx,
    affine_product (select_scalar_rows mask rows) idx =
    select_scalar_values mask (affine_product rows idx).
Proof.
  induction mask as [|is_loop mask IH];
    intros rows idx; destruct rows as [|row rows]; simpl; auto.
  destruct is_loop; simpl; rewrite IH; reflexivity.
Qed.

Lemma affine_product_render_scalar_aware_tile_prefix :
  forall mask band_rows tile_rows rendered idx,
    render_scalar_aware_tile_prefix
      mask band_rows tile_rows = Some rendered ->
    render_scalar_aware_value_prefix
      mask
      (affine_product band_rows idx)
      (affine_product tile_rows idx) =
    Some (affine_product rendered idx).
Proof.
  induction mask as [|is_loop mask IH];
    intros band_rows tile_rows rendered idx Hrender;
    destruct band_rows as [|band_row band_rows];
    simpl in Hrender; try discriminate.
  - destruct tile_rows; inversion Hrender; reflexivity.
  - destruct is_loop.
    + destruct tile_rows as [|tile_row tile_rows]; try discriminate.
      destruct
        (render_scalar_aware_tile_prefix mask band_rows tile_rows)
        as [tail|] eqn:Htail; try discriminate.
      inversion Hrender; subst rendered.
      simpl.
      rewrite (IH band_rows tile_rows tail idx Htail).
      reflexivity.
    + destruct
        (render_scalar_aware_tile_prefix mask band_rows tile_rows)
        as [tail|] eqn:Htail; try discriminate.
      inversion Hrender; subst rendered.
      simpl.
      rewrite (IH band_rows tile_rows tail idx Htail).
      reflexivity.
Qed.

Lemma scalar_aware_stripmine_schedule_after_env_eval :
  forall env_size added_dims before_sched layout expected
         cols env tiles iters,
    exact_listzzs_cols cols before_sched ->
    (env_size <= cols)%nat ->
    List.length env = env_size ->
    List.length tiles = added_dims ->
    sabl_loop_mask layout <> [] ->
    scalar_aware_stripmine_schedule_after_env
      env_size added_dims before_sched layout = Some expected ->
    exists band_values mixed_values,
      band_values =
        firstn (List.length (sabl_loop_mask layout))
          (skipn (sabl_start layout)
             (affine_product before_sched (env ++ iters))) /\
      render_scalar_aware_value_prefix
        (sabl_loop_mask layout) band_values tiles =
      Some mixed_values /\
      affine_product expected (env ++ tiles ++ iters) =
        firstn (sabl_start layout)
          (affine_product before_sched (env ++ iters)) ++
        mixed_values ++ band_values ++
        skipn
          (sabl_start layout + List.length (sabl_loop_mask layout))%nat
          (affine_product before_sched (env ++ iters)).
Proof.
  intros env_size added_dims before_sched layout expected
         cols env tiles iters Hcols Henv_cols Henv Htiles
         Hmask_nonempty Hexpected.
  unfold scalar_aware_stripmine_schedule_after_env in Hexpected.
  set
    (lifted :=
       Tiling.lift_schedule_after_env added_dims env_size before_sched)
    in *.
  set
    (total_cols :=
       match lifted with
       | [] => (env_size + added_dims)%nat
       | (coeffs, _) :: _ => List.length coeffs
       end)
    in *.
  set (band := scalar_aware_band layout) in *.
  set (prefix := firstn (ptb_start band) lifted) in *.
  set
    (band_rows :=
       firstn (ptb_len band) (skipn (ptb_start band) lifted))
    in *.
  set
    (suffix := skipn (ptb_start band + ptb_len band)%nat lifted)
    in *.
  destruct
    (render_scalar_aware_tile_prefix
       (sabl_loop_mask layout) band_rows
       (Tiling.identity_affine_rows_from
          total_cols env_size added_dims))
    as [rendered|] eqn:Hrender; try discriminate.
  inversion Hexpected; subst expected; clear Hexpected.
  set (old_ts := affine_product before_sched (env ++ iters)).
  assert (Hlift :
    affine_product lifted (env ++ tiles ++ iters) = old_ts).
  {
    subst lifted old_ts.
    apply Tiling.lift_affine_function_after_env_eval; assumption.
  }
  assert (Hlifted_nonempty : lifted <> []).
  {
    intro Hnil.
    subst band_rows band.
    rewrite Hnil in Hrender.
    rewrite skipn_nil, firstn_nil in Hrender.
    destruct layout as [start mask0].
    cbn in Hrender, Hmask_nonempty.
    destruct mask0 as [|is_loop mask].
    - apply Hmask_nonempty. reflexivity.
    - discriminate.
  }
  assert (Hidentity :
    affine_product
      (Tiling.identity_affine_rows_from
         total_cols env_size added_dims)
      (env ++ tiles ++ iters) = tiles).
  {
    rewrite
      (affine_product_identity_affine_rows_from
         total_cols env_size added_dims (env ++ tiles ++ iters)).
    2:{
      subst total_cols.
      pose proof
        (lift_schedule_after_env_exact_cols
           cols added_dims env_size before_sched Hcols Henv_cols)
        as Hlift_cols.
      subst lifted.
      destruct
        (Tiling.lift_schedule_after_env
           added_dims env_size before_sched)
        as [|[coeffs rhs] rows].
      + exfalso.
        apply Hlifted_nonempty.
        reflexivity.
      + assert (List.length coeffs = (added_dims + cols)%nat).
        {
          eapply Hlift_cols.
          - left. reflexivity.
          - reflexivity.
        }
        repeat rewrite app_length.
        lia.
    }
    2:{
      repeat rewrite app_length.
      lia.
    }
    rewrite <- Henv.
    assert
      (Hskip :
         skipn (List.length env) (env ++ tiles ++ iters) =
         tiles ++ iters).
    {
      replace (env ++ tiles ++ iters)
        with (env ++ (tiles ++ iters)) by reflexivity.
      rewrite skipn_app_le by lia.
      replace (List.length env - List.length env)%nat with O by lia.
      reflexivity.
    }
    rewrite Hskip.
    rewrite firstn_app.
    replace (added_dims - List.length tiles)%nat with O by lia.
    rewrite <- Htiles.
    rewrite firstn_all.
    rewrite app_nil_r.
    reflexivity.
  }
  assert (Hrender_eval :
    render_scalar_aware_value_prefix
      (sabl_loop_mask layout)
      (affine_product band_rows (env ++ tiles ++ iters))
      tiles =
    Some (affine_product rendered (env ++ tiles ++ iters))).
  {
    pose proof
      (affine_product_render_scalar_aware_tile_prefix
         (sabl_loop_mask layout) band_rows
         (Tiling.identity_affine_rows_from
            total_cols env_size added_dims)
         rendered (env ++ tiles ++ iters) Hrender)
      as Heval.
    rewrite Hidentity in Heval.
    exact Heval.
  }
  exists
    (affine_product band_rows (env ++ tiles ++ iters)),
    (affine_product rendered (env ++ tiles ++ iters)).
  split.
  - subst band_rows band.
    rewrite affine_product_firstn_local.
    rewrite affine_product_skipn_local_component.
    unfold scalar_aware_band.
    cbn.
    rewrite Hlift.
    reflexivity.
  - split; [exact Hrender_eval|].
    subst prefix band_rows suffix band.
    rewrite !affine_product_app_local_component.
    rewrite affine_product_firstn_local.
    rewrite affine_product_skipn_local_component.
    rewrite affine_product_firstn_local.
    rewrite affine_product_skipn_local_component.
    unfold scalar_aware_band.
    cbn.
    rewrite Hlift.
    reflexivity.
Qed.

Lemma select_scalar_rows_in :
  forall mask rows row,
    In row (select_scalar_rows mask rows) ->
    In row rows.
Proof.
  induction mask as [|is_loop mask IH];
    intros rows row Hin; destruct rows as [|head rows];
    simpl in *; try contradiction.
  destruct is_loop.
  - right. eapply IH. exact Hin.
  - destruct Hin as [Heq | Hin].
    + left. exact Heq.
    + right. eapply IH. exact Hin.
Qed.

Lemma exact_listzzs_cols_select_scalar_rows :
  forall cols mask rows,
    exact_listzzs_cols cols rows ->
    exact_listzzs_cols cols (select_scalar_rows mask rows).
Proof.
  intros cols mask rows Hcols coeffs c row Hin Heq.
  eapply Hcols.
  - eapply select_scalar_rows_in. exact Hin.
  - exact Heq.
Qed.

Definition make_schedule_rows_nondecreasing_poly
    (rows1 rows2: Schedule) : polyhedron :=
  List.map
    (fun '(row1, row2) =>
       make_constr_gt (fst row1, (snd row1 + 1)%Z) row2)
    (List.combine rows1 rows2).

Lemma make_schedule_rows_nondecreasing_poly_sound :
  forall cols rows1 rows2 idx1 idx2,
    List.length idx1 = cols ->
    exact_listzzs_cols cols rows1 ->
    listz_pointwise_le
      (affine_product rows2 idx2)
      (affine_product rows1 idx1) ->
    in_poly
      (idx1 ++ idx2)
      (make_schedule_rows_nondecreasing_poly rows1 rows2) = true.
Proof.
  intros cols rows1.
  induction rows1 as [|[coeffs1 c1] rows1 IH];
    intros rows2 idx1 idx2 Hidx Hcols Hle;
    destruct rows2 as [|[coeffs2 c2] rows2];
    simpl in *; try reflexivity; try inversion Hle.
  inversion Hle as [|value2 value1 values2 values1 Hhead Htail];
    subst.
  change
    (satisfies_constraint
       (idx1 ++ idx2)
       (make_constr_gt (coeffs1, (c1 + 1)%Z) (coeffs2, c2)) &&
     in_poly
       (idx1 ++ idx2)
       (make_schedule_rows_nondecreasing_poly rows1 rows2) = true).
  apply andb_true_iff.
  split.
  - assert (Hcoeffs1 : List.length idx1 = List.length coeffs1).
    {
      symmetry.
      eapply Hcols.
      - left. reflexivity.
      - reflexivity.
    }
    apply
      (proj2
         (make_constr_gt_correct
            idx1 idx2 coeffs1 coeffs2 (c1 + 1)%Z c2 Hcoeffs1)).
    lia.
  - eapply IH.
    + reflexivity.
    + intros coeffs c row Hin Heq.
      eapply Hcols.
      * right. exact Hin.
      * exact Heq.
    + exact Htail.
Qed.

Definition scalar_aware_component_active
    (layout: scalar_aware_band_layout)
    (dim: nat)
    (pi1 pi2: Tiling.PL.PolyInstr_ext)
    (ip1 ip2: Tiling.PL.InstrPoint_ext) : Prop :=
  let sched1 := Tiling.PL.pi_schedule1_ext pi1 in
  let sched2 := Tiling.PL.pi_schedule1_ext pi2 in
  let idx1 := Tiling.PL.ip_index_ext ip1 in
  let idx2 := Tiling.PL.ip_index_ext ip2 in
  affine_product (firstn (sabl_start layout) sched1) idx1 =
  affine_product (firstn (sabl_start layout) sched2) idx2 /\
  listz_pointwise_le
    (affine_product
       (select_scalar_rows
          (firstn dim (sabl_loop_mask layout))
          (firstn dim (skipn (sabl_start layout) sched2)))
       idx2)
    (affine_product
       (select_scalar_rows
          (firstn dim (sabl_loop_mask layout))
          (firstn dim (skipn (sabl_start layout) sched1)))
       idx1) /\
  (semantic_band_value
     (List.length idx1) (sabl_start layout + dim) sched1 idx1 >
   semantic_band_value
     (List.length idx2) (sabl_start layout + dim) sched2 idx2)%Z.

Definition make_scalar_aware_band_component_guard_polys
    (pi1 pi2: Tiling.PL.PolyInstr_ext)
    (layout: scalar_aware_band_layout)
    (dim env_size: nat)
    : option (list polyhedron * list polyhedron) :=
  let dom_dim1 := (env_size + Tiling.PL.pi_depth_ext pi1)%nat in
  let dom_dim2 := (env_size + Tiling.PL.pi_depth_ext pi2)%nat in
  let sched1 := Tiling.PL.pi_schedule1_ext pi1 in
  let sched2 := Tiling.PL.pi_schedule1_ext pi2 in
  match nth_error sched1 (sabl_start layout + dim),
        nth_error sched2 (sabl_start layout + dim) with
  | Some row1, Some row2 =>
      let old_order := make_poly_lt sched1 sched2 dom_dim1 dom_dim2 [] in
      let same_outer_prefix :=
        make_poly_eq
          (firstn (sabl_start layout) sched1)
          (firstn (sabl_start layout) sched2)
          dom_dim1 dom_dim2 [] in
      let earlier_scalars_not_carry :=
        make_schedule_rows_nondecreasing_poly
          (select_scalar_rows
             (firstn dim (sabl_loop_mask layout))
             (firstn dim (skipn (sabl_start layout) sched1)))
          (select_scalar_rows
             (firstn dim (sabl_loop_mask layout))
             (firstn dim (skipn (sabl_start layout) sched2))) in
      let component_decreases := make_constr_gt row1 row2 in
      Some
        (old_order,
         [[component_decreases] ++
          same_outer_prefix ++ earlier_scalars_not_carry])
  | _, _ => None
  end.

Lemma make_scalar_aware_band_component_guard_polys_old_order_sound :
  forall pi1 pi2 layout dim env_size old_order bad_component idx1 idx2,
    make_scalar_aware_band_component_guard_polys
      pi1 pi2 layout dim env_size = Some (old_order, bad_component) ->
    List.length idx1 =
      (env_size + Tiling.PL.pi_depth_ext pi1)%nat ->
    List.length idx2 =
      (env_size + Tiling.PL.pi_depth_ext pi2)%nat ->
    exact_listzzs_cols
      (env_size + Tiling.PL.pi_depth_ext pi1)%nat
      (Tiling.PL.pi_schedule1_ext pi1) ->
    lex_compare
      (affine_product (Tiling.PL.pi_schedule1_ext pi1) idx1)
      (affine_product (Tiling.PL.pi_schedule1_ext pi2) idx2) = Lt ->
    Exists
      (fun pol => in_poly (idx1 ++ idx2) pol = true)
      old_order.
Proof.
  intros pi1 pi2 layout dim env_size old_order bad_component idx1 idx2
         Hmake Hlen1 Hlen2 Hcols Hold.
  unfold make_scalar_aware_band_component_guard_polys in Hmake.
  destruct
    (nth_error
       (Tiling.PL.pi_schedule1_ext pi1) (sabl_start layout + dim));
    try discriminate.
  destruct
    (nth_error
       (Tiling.PL.pi_schedule1_ext pi2) (sabl_start layout + dim));
    try discriminate.
  inversion Hmake; subst old_order bad_component; clear Hmake.
  eapply make_poly_lt_correct; eauto.
Qed.

Lemma make_scalar_aware_band_component_guard_polys_bad_sound :
  forall pi1 pi2 layout dim env_size old_order bad_component idx1 idx2
         ip1 ip2,
    make_scalar_aware_band_component_guard_polys
      pi1 pi2 layout dim env_size = Some (old_order, bad_component) ->
    List.length idx1 =
      (env_size + Tiling.PL.pi_depth_ext pi1)%nat ->
    List.length idx2 =
      (env_size + Tiling.PL.pi_depth_ext pi2)%nat ->
    exact_listzzs_cols
      (env_size + Tiling.PL.pi_depth_ext pi1)%nat
      (Tiling.PL.pi_schedule1_ext pi1) ->
    exact_listzzs_cols
      (env_size + Tiling.PL.pi_depth_ext pi2)%nat
      (Tiling.PL.pi_schedule1_ext pi2) ->
    scalar_aware_component_active layout dim pi1 pi2 ip1 ip2 ->
    Tiling.PL.ip_index_ext ip1 = idx1 ->
    Tiling.PL.ip_index_ext ip2 = idx2 ->
    Exists
      (fun pol => in_poly (idx1 ++ idx2) pol = true)
      bad_component.
Proof.
  intros pi1 pi2 layout dim env_size old_order bad_component idx1 idx2
         ip1 ip2 Hmake Hlen1 Hlen2 Hcols1 Hcols2
         Hactive Hidx1 Hidx2.
  subst idx1 idx2.
  unfold make_scalar_aware_band_component_guard_polys in Hmake.
  destruct
    (nth_error
       (Tiling.PL.pi_schedule1_ext pi1)
       (sabl_start layout + dim))
    as [[coeffs1 c1]|] eqn:Hrow1; try discriminate.
  destruct
    (nth_error
       (Tiling.PL.pi_schedule1_ext pi2)
       (sabl_start layout + dim))
    as [[coeffs2 c2]|] eqn:Hrow2; try discriminate.
  inversion Hmake; subst old_order bad_component; clear Hmake.
  unfold scalar_aware_component_active in Hactive.
  cbn zeta in Hactive.
  destruct Hactive as [Hprefix [Hscalars Hcomponent]].
  assert (Hprefix_poly :
    in_poly
      (Tiling.PL.ip_index_ext ip1 ++ Tiling.PL.ip_index_ext ip2)
      (make_poly_eq
         (firstn (sabl_start layout)
            (Tiling.PL.pi_schedule1_ext pi1))
         (firstn (sabl_start layout)
            (Tiling.PL.pi_schedule1_ext pi2))
         (env_size + Tiling.PL.pi_depth_ext pi1)%nat
         (env_size + Tiling.PL.pi_depth_ext pi2)%nat []) = true).
  {
    apply
      (proj2
         (make_poly_eq_correct_true
            (firstn (sabl_start layout)
               (Tiling.PL.pi_schedule1_ext pi1))
            (firstn (sabl_start layout)
               (Tiling.PL.pi_schedule1_ext pi2))
            (env_size + Tiling.PL.pi_depth_ext pi1)%nat
            (env_size + Tiling.PL.pi_depth_ext pi2)%nat
            (Tiling.PL.ip_index_ext ip1)
            (Tiling.PL.ip_index_ext ip2)
            Hlen1 Hlen2
            (exact_listzzs_cols_firstn_local
               _ _ _ Hcols1))).
    rewrite Hprefix.
    apply veq_refl.
  }
  assert (Hscalar_poly :
    in_poly
      (Tiling.PL.ip_index_ext ip1 ++ Tiling.PL.ip_index_ext ip2)
      (make_schedule_rows_nondecreasing_poly
         (select_scalar_rows
            (firstn dim (sabl_loop_mask layout))
            (firstn dim
               (skipn (sabl_start layout)
                  (Tiling.PL.pi_schedule1_ext pi1))))
         (select_scalar_rows
            (firstn dim (sabl_loop_mask layout))
            (firstn dim
               (skipn (sabl_start layout)
                  (Tiling.PL.pi_schedule1_ext pi2))))) = true).
  {
    eapply make_schedule_rows_nondecreasing_poly_sound.
    - exact Hlen1.
    - eapply exact_listzzs_cols_select_scalar_rows.
      eapply exact_listzzs_cols_firstn_local.
      eapply exact_listzzs_cols_skipn_local_component.
      exact Hcols1.
    - exact Hscalars.
  }
  assert (Hcoeffs1 :
    List.length (Tiling.PL.ip_index_ext ip1) = List.length coeffs1).
  {
    rewrite Hlen1.
    symmetry.
    eapply Hcols1.
    - eapply nth_error_In. exact Hrow1.
    - reflexivity.
  }
  assert (Hcomponent_poly :
    satisfies_constraint
      (Tiling.PL.ip_index_ext ip1 ++ Tiling.PL.ip_index_ext ip2)
      (make_constr_gt (coeffs1, c1) (coeffs2, c2)) = true).
  {
    apply
      (proj2
         (make_constr_gt_correct
            (Tiling.PL.ip_index_ext ip1)
            (Tiling.PL.ip_index_ext ip2)
            coeffs1 coeffs2 c1 c2 Hcoeffs1)).
    unfold semantic_band_value, semantic_band_row in Hcomponent.
    rewrite Hrow1, Hrow2 in Hcomponent.
    exact Hcomponent.
  }
  apply Exists_cons_hd.
  change
    (satisfies_constraint
       (Tiling.PL.ip_index_ext ip1 ++ Tiling.PL.ip_index_ext ip2)
       (make_constr_gt (coeffs1, c1) (coeffs2, c2)) &&
     in_poly
       (Tiling.PL.ip_index_ext ip1 ++ Tiling.PL.ip_index_ext ip2)
       (make_poly_eq
          (firstn (sabl_start layout)
             (Tiling.PL.pi_schedule1_ext pi1))
          (firstn (sabl_start layout)
             (Tiling.PL.pi_schedule1_ext pi2))
          (env_size + Tiling.PL.pi_depth_ext pi1)%nat
          (env_size + Tiling.PL.pi_depth_ext pi2)%nat [] ++
        make_schedule_rows_nondecreasing_poly
          (select_scalar_rows
             (firstn dim (sabl_loop_mask layout))
             (firstn dim
                (skipn (sabl_start layout)
                   (Tiling.PL.pi_schedule1_ext pi1))))
          (select_scalar_rows
             (firstn dim (sabl_loop_mask layout))
             (firstn dim
                (skipn (sabl_start layout)
                   (Tiling.PL.pi_schedule1_ext pi2))))) = true).
  apply andb_true_iff.
  split; [exact Hcomponent_poly|].
  rewrite in_poly_app, Hprefix_poly, Hscalar_poly.
  reflexivity.
Qed.

Definition validate_two_instrs_scalar_aware_band_component_direct
    (pi1 pi2: Tiling.PL.PolyInstr_ext)
    (layout: scalar_aware_band_layout)
    (dim env_size: nat) : imp bool :=
  match
    make_scalar_aware_band_component_guard_polys
      pi1 pi2 layout dim env_size
  with
  | None => pure false
  | Some (old_order, bad_component) =>
      BandAffine.validate_two_instrs_under_guards_integer
        pi1 pi2 env_size old_order bad_component
  end.

Lemma validate_two_instrs_scalar_aware_band_component_direct_sound :
  forall env envv nth1 nth2 pi1 pi2 ipl1 ipl2 layout dim ip1 ip2,
    mayReturn
      (validate_two_instrs_scalar_aware_band_component_direct
         pi1 pi2 layout dim (List.length env))
      true ->
    Tiling.PL.wf_pinstr_ext_tiling env pi1 ->
    Tiling.PL.wf_pinstr_ext_tiling env pi2 ->
    List.length env = List.length envv ->
    Tiling.PL.flatten_instr_nth_ext envv nth1 pi1 ipl1 ->
    Tiling.PL.flatten_instr_nth_ext envv nth2 pi2 ipl2 ->
    In ip1 ipl1 ->
    In ip2 ipl2 ->
    Instr.valid_access_function
      (Tiling.PL.pi_waccess_ext pi1)
      (Tiling.PL.pi_raccess_ext pi1)
      (Tiling.PL.pi_instr_ext pi1) ->
    Instr.valid_access_function
      (Tiling.PL.pi_waccess_ext pi2)
      (Tiling.PL.pi_raccess_ext pi2)
      (Tiling.PL.pi_instr_ext pi2) ->
    Tiling.PL.instr_point_ext_old_sched_lt ip1 ip2 ->
    scalar_aware_component_active layout dim pi1 pi2 ip1 ip2 ->
    Tiling.PL.Permutable_ext ip1 ip2.
Proof.
  intros env envv nth1 nth2 pi1 pi2 ipl1 ipl2 layout dim ip1 ip2
         Hcheck Hwf1 Hwf2 Henv Hflat1 Hflat2 Hin1 Hin2
         Hvalid1 Hvalid2 Hold Hactive.
  unfold validate_two_instrs_scalar_aware_band_component_direct in Hcheck.
  destruct
    (make_scalar_aware_band_component_guard_polys
       pi1 pi2 layout dim (List.length env))
    as [[old_order bad_component]|] eqn:Hguards.
  2:{ apply mayReturn_pure in Hcheck. discriminate. }
  pose proof
    (Tiling.PL.expand_ts1_eq_sched_index_product_ext
       envv nth1 pi1 ipl1 ip1 Hflat1 Hin1) as Hts1.
  pose proof
    (Tiling.PL.expand_ts1_eq_sched_index_product_ext
       envv nth2 pi2 ipl2 ip2 Hflat2 Hin2) as Hts2.
  assert (Hidx1 :
    List.length (Tiling.PL.ip_index_ext ip1) =
      (List.length env + Tiling.PL.pi_depth_ext pi1)%nat).
  {
    rewrite Henv.
    eapply Tiling.PL.ip_index_size_eq_pi_dom_size_ext; eauto.
  }
  assert (Hidx2 :
    List.length (Tiling.PL.ip_index_ext ip2) =
      (List.length env + Tiling.PL.pi_depth_ext pi2)%nat).
  {
    rewrite Henv.
    eapply Tiling.PL.ip_index_size_eq_pi_dom_size_ext; eauto.
  }
  assert (Hcols1 :
    exact_listzzs_cols
      (List.length env + Tiling.PL.pi_depth_ext pi1)%nat
      (Tiling.PL.pi_schedule1_ext pi1)).
  {
    exact (wf_pinstr_ext_tiling_schedule1_exact_cols env pi1 Hwf1).
  }
  assert (Hcols2 :
    exact_listzzs_cols
      (List.length env + Tiling.PL.pi_depth_ext pi2)%nat
      (Tiling.PL.pi_schedule1_ext pi2)).
  {
    exact (wf_pinstr_ext_tiling_schedule1_exact_cols env pi2 Hwf2).
  }
  assert (Horder :
    Exists
      (fun pol =>
         in_poly
           (Tiling.PL.ip_index_ext ip1 ++ Tiling.PL.ip_index_ext ip2)
           pol = true)
      old_order).
  {
    eapply
      make_scalar_aware_band_component_guard_polys_old_order_sound;
      eauto.
    unfold Tiling.PL.instr_point_ext_old_sched_lt in Hold.
    rewrite Hts1, Hts2 in Hold.
    exact Hold.
  }
  assert (Hbad :
    Exists
      (fun pol =>
         in_poly
           (Tiling.PL.ip_index_ext ip1 ++ Tiling.PL.ip_index_ext ip2)
           pol = true)
      bad_component).
  {
    eapply make_scalar_aware_band_component_guard_polys_bad_sound;
      eauto.
  }
  assert (Hcollision :
    BandAffine.no_write_collision
      (Tiling.PL.pi_waccess_ext pi1)
      (Tiling.PL.pi_waccess_ext pi2)
      (Tiling.PL.pi_raccess_ext pi1)
      (Tiling.PL.pi_raccess_ext pi2)
      ip1 ip2).
  {
    eapply
      (BandAffine.validate_two_instrs_under_guards_integer_implies_no_write_collision
         pi1 pi2 env nth1 nth2 envv ipl1 ipl2
         old_order bad_component true Hcheck eq_refl);
      eauto.
  }
  assert (Hinstr1 :
    Tiling.PL.ip_instruction_ext ip1 =
    Tiling.PL.pi_instr_ext pi1).
  { eapply Tiling.PL.expand_ip_instr_eq_pi_instr_ext; eauto. }
  assert (Hinstr2 :
    Tiling.PL.ip_instruction_ext ip2 =
    Tiling.PL.pi_instr_ext pi2).
  { eapply Tiling.PL.expand_ip_instr_eq_pi_instr_ext; eauto. }
  assert (Htf1 :
    Tiling.PL.ip_access_transformation_ext ip1 =
    Tiling.PL.ip_transformation_ext ip1).
  {
    assert (Haccess :
      Tiling.PL.ip_access_transformation_ext ip1 =
      Tiling.PL.pi_access_transformation_ext pi1).
    { eapply Tiling.PL.expand_ip_instr_eq_pi_access_tf_ext; eauto. }
    assert (Hcurrent :
      Tiling.PL.ip_transformation_ext ip1 =
      Tiling.PL.pi_transformation_ext pi1).
    { eapply Tiling.PL.expand_ip_instr_eq_pi_tf_ext; eauto. }
    destruct Hwf1 as [_ Hpi_eq].
    rewrite Haccess, Hcurrent, Hpi_eq.
    reflexivity.
  }
  assert (Htf2 :
    Tiling.PL.ip_access_transformation_ext ip2 =
    Tiling.PL.ip_transformation_ext ip2).
  {
    assert (Haccess :
      Tiling.PL.ip_access_transformation_ext ip2 =
      Tiling.PL.pi_access_transformation_ext pi2).
    { eapply Tiling.PL.expand_ip_instr_eq_pi_access_tf_ext; eauto. }
    assert (Hcurrent :
      Tiling.PL.ip_transformation_ext ip2 =
      Tiling.PL.pi_transformation_ext pi2).
    { eapply Tiling.PL.expand_ip_instr_eq_pi_tf_ext; eauto. }
    destruct Hwf2 as [_ Hpi_eq].
    rewrite Haccess, Hcurrent, Hpi_eq.
    reflexivity.
  }
  eapply BandAffine.no_write_collision_implies_permutable; eauto.
  - rewrite Hinstr1. exact Hvalid1.
  - rewrite Hinstr2. exact Hvalid2.
Qed.

Fixpoint validate_instr_and_list_scalar_aware_band_component_direct
    (pi: Tiling.PL.PolyInstr_ext)
    (pis: list Tiling.PL.PolyInstr_ext)
    (layout: scalar_aware_band_layout)
    (dim env_size: nat) : imp bool :=
  match pis with
  | [] => pure true
  | pi' :: pis' =>
      BIND forward <-
        validate_two_instrs_scalar_aware_band_component_direct
          pi pi' layout dim env_size -;
      if forward then
        BIND backward <-
          validate_two_instrs_scalar_aware_band_component_direct
            pi' pi layout dim env_size -;
        if backward then
          validate_instr_and_list_scalar_aware_band_component_direct
            pi pis' layout dim env_size
        else pure false
      else pure false
  end.

Fixpoint validate_instr_list_scalar_aware_band_component_direct
    (pis: list Tiling.PL.PolyInstr_ext)
    (layout: scalar_aware_band_layout)
    (dim env_size: nat) : imp bool :=
  match pis with
  | [] => pure true
  | pi :: pis' =>
      BIND self <-
        validate_two_instrs_scalar_aware_band_component_direct
          pi pi layout dim env_size -;
      if self then
        BIND cross <-
          validate_instr_and_list_scalar_aware_band_component_direct
            pi pis' layout dim env_size -;
        if cross then
          validate_instr_list_scalar_aware_band_component_direct
            pis' layout dim env_size
        else pure false
      else pure false
  end.

Fixpoint validate_instr_list_scalar_aware_band_components_direct_from
    (pis: list Tiling.PL.PolyInstr_ext)
    (layout: scalar_aware_band_layout)
    (remaining dim env_size: nat) : imp bool :=
  match remaining with
  | O => pure true
  | S remaining' =>
      BIND component_ok <-
        validate_instr_list_scalar_aware_band_component_direct
          pis layout dim env_size -;
      if component_ok then
        validate_instr_list_scalar_aware_band_components_direct_from
          pis layout remaining' (S dim) env_size
      else pure false
  end.

Definition check_pprog_scalar_aware_permutable_band_direct
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness)
    (layout: scalar_aware_band_layout) : imp bool :=
  let '(before_pis, before_ctxt, _) := before in
  let '(after_pis, _, _) := after in
  let pis :=
    Tiling.compose_tiling_pinstrs_ext_from_after
      (List.length before_ctxt) before_pis after_pis ws in
  let aligned :=
    Nat.eqb (List.length before_pis) (List.length after_pis) &&
    Nat.eqb (List.length before_pis) (List.length ws) &&
    Nat.eqb (List.length before_pis) (List.length pis) in
  let valid_access := BandAffine.check_valid_access pis in
  BIND components_ok <-
    validate_instr_list_scalar_aware_band_components_direct_from
      pis layout (List.length (sabl_loop_mask layout)) O
      (List.length before_ctxt) -;
  pure (aligned && components_ok && valid_access).

Lemma validate_instr_and_list_scalar_aware_band_component_true_pair :
  forall pi pis layout dim env_size,
    mayReturn
      (validate_instr_and_list_scalar_aware_band_component_direct
         pi pis layout dim env_size)
      true ->
    forall pi',
      In pi' pis ->
      mayReturn
        (validate_two_instrs_scalar_aware_band_component_direct
           pi pi' layout dim env_size)
        true /\
      mayReturn
        (validate_two_instrs_scalar_aware_band_component_direct
           pi' pi layout dim env_size)
        true.
Proof.
  intros pi pis.
  induction pis as [|pi' pis IH];
    intros layout dim env_size Hcheck target Hin.
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

Lemma validate_instr_list_scalar_aware_band_component_true_pair :
  forall pis layout dim env_size,
    mayReturn
      (validate_instr_list_scalar_aware_band_component_direct
         pis layout dim env_size)
      true ->
    forall pi1 pi2,
      In pi1 pis ->
      In pi2 pis ->
      mayReturn
        (validate_two_instrs_scalar_aware_band_component_direct
           pi1 pi2 layout dim env_size)
        true.
Proof.
  intros pis.
  induction pis as [|pi pis IH];
    intros layout dim env_size Hcheck pi1 pi2 Hin1 Hin2.
  - inversion Hin1.
  - simpl in Hcheck.
    bind_imp_destruct Hcheck self Hself.
    destruct self.
    + bind_imp_destruct Hcheck cross Hcross.
      destruct cross.
      * destruct Hin1 as [Heq1 | Hin1];
        destruct Hin2 as [Heq2 | Hin2].
        -- subst pi1 pi2. exact Hself.
        -- subst pi1.
           eapply
             (proj1
                (validate_instr_and_list_scalar_aware_band_component_true_pair
                   pi pis layout dim env_size Hcross pi2 Hin2)).
        -- subst pi2.
           eapply
             (proj2
                (validate_instr_and_list_scalar_aware_band_component_true_pair
                   pi pis layout dim env_size Hcross pi1 Hin1)).
        -- eapply IH; eauto.
      * apply mayReturn_pure in Hcheck. discriminate.
    + apply mayReturn_pure in Hcheck. discriminate.
Qed.

Lemma validate_instr_list_scalar_aware_band_components_from_true_component :
  forall pis layout remaining start env_size,
    mayReturn
      (validate_instr_list_scalar_aware_band_components_direct_from
         pis layout remaining start env_size)
      true ->
    forall dim,
      (start <= dim < start + remaining)%nat ->
      mayReturn
        (validate_instr_list_scalar_aware_band_component_direct
           pis layout dim env_size)
        true.
Proof.
  intros pis layout remaining.
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

Definition pinstr_list_scalar_aware_componentwise_permutable
    (envv: list Z)
    (pis: list Tiling.PL.PolyInstr_ext)
    (layout: scalar_aware_band_layout) : Prop :=
  forall flat ip1 ip2 pi1 pi2 dim,
    Tiling.PL.flatten_instrs_ext envv pis flat ->
    In ip1 flat ->
    In ip2 flat ->
    nth_error pis (Tiling.PL.ip_nth_ext ip1) = Some pi1 ->
    nth_error pis (Tiling.PL.ip_nth_ext ip2) = Some pi2 ->
    (dim < List.length (sabl_loop_mask layout))%nat ->
    Tiling.PL.instr_point_ext_old_sched_lt ip1 ip2 ->
    scalar_aware_component_active layout dim pi1 pi2 ip1 ip2 ->
    Tiling.PL.Permutable_ext ip1 ip2.

Lemma check_pprog_scalar_aware_permutable_band_direct_sound :
  forall env envv before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws layout,
    List.length env = List.length envv ->
    Forall
      (Tiling.PL.wf_pinstr_ext_tiling env)
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length env) before_pis after_pis ws) ->
    mayReturn
      (check_pprog_scalar_aware_permutable_band_direct
         (before_pis, before_ctxt, before_vars)
         (after_pis, after_ctxt, after_vars)
         ws layout)
      true ->
    List.length env = List.length before_ctxt ->
    pinstr_list_scalar_aware_componentwise_permutable
      envv
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length env) before_pis after_pis ws)
      layout.
Proof.
  intros env envv before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws layout
         Henv Hwf Hcheck Hbefore_env.
  unfold check_pprog_scalar_aware_permutable_band_direct in Hcheck.
  cbn beta iota zeta in Hcheck.
  bind_imp_destruct Hcheck components_ok Hcomponents.
  apply mayReturn_pure in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as [[_ Hcomponents_true] Hvalid_true].
  subst components_ok.
  set (pis :=
    Tiling.compose_tiling_pinstrs_ext_from_after
      (List.length env) before_pis after_pis ws) in *.
  rewrite <- Hbefore_env in Hcomponents.
  rewrite <- Hbefore_env in Hvalid_true.
  assert (Hvalid :
    Forall
      (fun pi =>
         Instr.valid_access_function
           (Tiling.PL.pi_waccess_ext pi)
           (Tiling.PL.pi_raccess_ext pi)
           (Tiling.PL.pi_instr_ext pi))
      pis).
  {
    eapply BandAffine.check_valid_access_correct.
    exact Hvalid_true.
  }
  unfold pinstr_list_scalar_aware_componentwise_permutable.
  intros flat ip1 ip2 pi1 pi2 dim
         Hflat Hin1 Hin2 Hnth1 Hnth2 Hdim Hold Hactive.
  destruct
    (flatten_instrs_ext_member_slice_local
       envv pis flat ip1 pi1 Hflat Hin1 Hnth1)
    as [slice1 [Hslice1 Hin_slice1]].
  destruct
    (flatten_instrs_ext_member_slice_local
       envv pis flat ip2 pi2 Hflat Hin2 Hnth2)
    as [slice2 [Hslice2 Hin_slice2]].
  assert (Hcomponent_check :
    mayReturn
      (validate_instr_list_scalar_aware_band_component_direct
         pis layout dim (List.length env))
      true).
  {
    eapply
      validate_instr_list_scalar_aware_band_components_from_true_component.
    - exact Hcomponents.
    - lia.
  }
  assert (Hpair_check :
    mayReturn
      (validate_two_instrs_scalar_aware_band_component_direct
         pi1 pi2 layout dim (List.length env))
      true).
  {
    eapply validate_instr_list_scalar_aware_band_component_true_pair;
      eauto using nth_error_In.
  }
  assert (Hwf1 : Tiling.PL.wf_pinstr_ext_tiling env pi1).
  {
    eapply Tiling.Forall_nth_error; eauto.
  }
  assert (Hwf2 : Tiling.PL.wf_pinstr_ext_tiling env pi2).
  {
    eapply Tiling.Forall_nth_error; eauto.
  }
  assert (Hvalid1 :
    Instr.valid_access_function
      (Tiling.PL.pi_waccess_ext pi1)
      (Tiling.PL.pi_raccess_ext pi1)
      (Tiling.PL.pi_instr_ext pi1)).
  {
    exact
      (Tiling.Forall_nth_error
         _
         (fun pi =>
            Instr.valid_access_function
              (Tiling.PL.pi_waccess_ext pi)
              (Tiling.PL.pi_raccess_ext pi)
              (Tiling.PL.pi_instr_ext pi))
         pis (Tiling.PL.ip_nth_ext ip1) pi1 Hvalid Hnth1).
  }
  assert (Hvalid2 :
    Instr.valid_access_function
      (Tiling.PL.pi_waccess_ext pi2)
      (Tiling.PL.pi_raccess_ext pi2)
      (Tiling.PL.pi_instr_ext pi2)).
  {
    exact
      (Tiling.Forall_nth_error
         _
         (fun pi =>
            Instr.valid_access_function
              (Tiling.PL.pi_waccess_ext pi)
              (Tiling.PL.pi_raccess_ext pi)
              (Tiling.PL.pi_instr_ext pi))
         pis (Tiling.PL.ip_nth_ext ip2) pi2 Hvalid Hnth2).
  }
  eapply
    (validate_two_instrs_scalar_aware_band_component_direct_sound
       env envv
       (Tiling.PL.ip_nth_ext ip1)
       (Tiling.PL.ip_nth_ext ip2)
       pi1 pi2 slice1 slice2 layout dim ip1 ip2);
    eauto.
Qed.

Fixpoint check_scalar_aware_common_shape_entries
    (env_size: nat)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (common: scalar_aware_band_layout) : bool :=
  match before_pis, after_pis, ws with
  | [], [], [] => true
  | before_pi :: before_pis',
    after_pi :: after_pis',
    w :: ws' =>
      match infer_scalar_aware_band_layout env_size before_pi w with
      | Some layout =>
          scalar_aware_band_layout_eqb layout common &&
          check_scalar_aware_band_selectionb before_pi w common &&
          match
            scalar_aware_stripmine_schedule_after_env
              env_size (List.length (stw_links w))
              (Tiling.PL.pi_schedule before_pi) layout
          with
          | Some expected =>
              check_schedule_with_trailing_zero_paddingb
                expected (Tiling.PL.pi_schedule after_pi) &&
              check_scalar_aware_common_shape_entries
                env_size before_pis' after_pis' ws' common
          | None => false
          end
      | None => false
      end
  | _, _, _ => false
  end.

Definition scalar_aware_entry_shape
    (env_size: nat)
    (layout: scalar_aware_band_layout)
    (before_pi after_pi: Tiling.PL.PolyInstr)
    (w: statement_tiling_witness) : Prop :=
  exists link_rows expected,
    schedule_rows_of_links w = Some link_rows /\
    sabl_loop_mask layout <> [] /\
    List.length
      (scalar_aware_layout_band_rows
         layout (Tiling.PL.pi_schedule before_pi)) =
    List.length (sabl_loop_mask layout) /\
    select_by_mask
      (sabl_loop_mask layout)
      (scalar_aware_layout_band_rows
         layout (Tiling.PL.pi_schedule before_pi)) =
    link_rows /\
    scalar_aware_stripmine_schedule_after_env
      env_size (List.length (stw_links w))
      (Tiling.PL.pi_schedule before_pi) layout =
    Some expected /\
    schedule_matches_with_trailing_zero_padding
      expected (Tiling.PL.pi_schedule after_pi).

Inductive scalar_aware_shape_entries
    (env_size: nat)
    (layout: scalar_aware_band_layout)
    : list Tiling.PL.PolyInstr ->
      list Tiling.PL.PolyInstr ->
      list statement_tiling_witness -> Prop :=
| ScalarAwareShapeEntriesNil :
    scalar_aware_shape_entries env_size layout [] [] []
| ScalarAwareShapeEntriesCons :
    forall before_pi after_pi w before_pis after_pis ws,
      scalar_aware_entry_shape
        env_size layout before_pi after_pi w ->
      scalar_aware_shape_entries
        env_size layout before_pis after_pis ws ->
      scalar_aware_shape_entries
        env_size layout
        (before_pi :: before_pis)
        (after_pi :: after_pis)
        (w :: ws).

Lemma scalar_aware_shape_entries_nth_error :
  forall env_size layout before_pis after_pis ws
         n before_pi after_pi w,
    scalar_aware_shape_entries
      env_size layout before_pis after_pis ws ->
    nth_error before_pis n = Some before_pi ->
    nth_error after_pis n = Some after_pi ->
    nth_error ws n = Some w ->
    scalar_aware_entry_shape
      env_size layout before_pi after_pi w.
Proof.
  intros env_size layout before_pis after_pis ws n.
  revert before_pis after_pis ws.
  induction n as [|n IH];
    intros before_pis after_pis ws before_pi after_pi w
           Hshape Hbefore Hafter Hw;
    inversion Hshape; subst; simpl in *; try discriminate.
  - inversion Hbefore; inversion Hafter; inversion Hw; subst.
    assumption.
  - eapply IH; eauto.
Qed.

Lemma scalar_aware_band_layout_eqb_sound :
  forall layout1 layout2,
    scalar_aware_band_layout_eqb layout1 layout2 = true ->
    layout1 = layout2.
Proof.
  intros [start1 mask1] [start2 mask2] Hcheck.
  unfold scalar_aware_band_layout_eqb in Hcheck.
  cbn in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hstart Hmask].
  apply Nat.eqb_eq in Hstart.
  apply list_bool_strict_eqb_eq in Hmask.
  subst start2 mask2.
  reflexivity.
Qed.

Lemma check_scalar_aware_band_selectionb_sound :
  forall before_pi w layout,
    check_scalar_aware_band_selectionb before_pi w layout = true ->
    exists link_rows,
      schedule_rows_of_links w = Some link_rows /\
      sabl_loop_mask layout <> [] /\
      List.length
        (scalar_aware_layout_band_rows
           layout (Tiling.PL.pi_schedule before_pi)) =
      List.length (sabl_loop_mask layout) /\
      select_by_mask
        (sabl_loop_mask layout)
        (scalar_aware_layout_band_rows
           layout (Tiling.PL.pi_schedule before_pi)) =
      link_rows.
Proof.
  intros before_pi w layout Hcheck.
  unfold check_scalar_aware_band_selectionb in Hcheck.
  destruct (schedule_rows_of_links w) as [link_rows|] eqn:Hrows;
    try discriminate.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hnonempty Hcheck].
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hlen Hselected].
  exists link_rows.
  split; [reflexivity|].
  split.
  - apply Bool.negb_true_iff in Hnonempty.
    apply Nat.eqb_neq in Hnonempty.
    destruct (sabl_loop_mask layout); [contradiction|discriminate].
  - split.
    + apply Nat.eqb_eq. exact Hlen.
    + apply listzzs_strict_eqb_eq. exact Hselected.
Qed.

Lemma check_scalar_aware_common_shape_entries_sound :
  forall env_size before_pis after_pis ws layout,
    check_scalar_aware_common_shape_entries
      env_size before_pis after_pis ws layout = true ->
    scalar_aware_shape_entries
      env_size layout before_pis after_pis ws.
Proof.
  intros env_size before_pis.
  induction before_pis as [|before_pi before_pis IH];
    intros after_pis ws layout Hcheck;
    destruct after_pis as [|after_pi after_pis];
    destruct ws as [|w ws];
    simpl in Hcheck; try discriminate.
  - constructor.
  - destruct
      (infer_scalar_aware_band_layout env_size before_pi w)
      as [inferred|] eqn:Hinfer; try discriminate.
    apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hlayout Hcheck].
    apply andb_true_iff in Hlayout.
    destruct Hlayout as [Hlayout Hselection].
    pose proof
      (scalar_aware_band_layout_eqb_sound
         inferred layout Hlayout) as Heq.
    subst inferred.
    destruct
      (check_scalar_aware_band_selectionb_sound
         before_pi w layout Hselection)
      as [link_rows
          [Hlink_rows [Hmask_nonempty [Hband_len Hselected]]]].
    destruct
      (scalar_aware_stripmine_schedule_after_env
         env_size (List.length (stw_links w))
         (Tiling.PL.pi_schedule before_pi) layout)
      as [expected|] eqn:Hexpected; try discriminate.
    apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hschedule Hrest].
    constructor.
    + exists link_rows, expected.
      repeat split; try assumption.
      eapply check_schedule_with_trailing_zero_paddingb_sound.
      exact Hschedule.
    + eapply IH. exact Hrest.
Qed.

Definition infer_pprog_scalar_aware_common_shape
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness)
    : option scalar_aware_band_layout :=
  let '(before_pis, before_ctxt, before_vars) := before in
  let '(after_pis, after_ctxt, after_vars) := after in
  if TilingCheck.ctxt_eqb before_ctxt after_ctxt &&
     TilingCheck.ctxt_ty_eqb before_vars after_vars &&
     check_common_tiling_band_recipeb ws then
    match before_pis, ws with
    | before_pi :: _, w :: _ =>
        match
          infer_scalar_aware_band_layout
            (List.length before_ctxt) before_pi w
        with
        | Some layout =>
            if
              check_scalar_aware_common_shape_entries
                (List.length before_ctxt)
                before_pis after_pis ws layout
            then Some layout
            else None
        | None => None
        end
    | _, _ => None
    end
  else None.

Lemma infer_pprog_scalar_aware_common_shape_sound :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws layout,
    infer_pprog_scalar_aware_common_shape
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      ws = Some layout ->
    before_ctxt = after_ctxt /\
    before_vars = after_vars /\
    common_tiling_band_recipe ws /\
    scalar_aware_shape_entries
      (List.length before_ctxt) layout before_pis after_pis ws.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws layout Hinfer.
  unfold infer_pprog_scalar_aware_common_shape in Hinfer.
  cbn beta iota zeta in Hinfer.
  destruct (TilingCheck.ctxt_eqb before_ctxt after_ctxt)
    eqn:Hctxt; try discriminate.
  destruct (TilingCheck.ctxt_ty_eqb before_vars after_vars)
    eqn:Hvars; try discriminate.
  destruct (check_common_tiling_band_recipeb ws)
    eqn:Hrecipe; try discriminate.
  destruct before_pis as [|before_pi before_pis]; try discriminate.
  destruct ws as [|w ws]; try discriminate.
  destruct
    (infer_scalar_aware_band_layout
       (List.length before_ctxt) before_pi w)
    as [inferred|] eqn:Hlayout; try discriminate.
  destruct
    (check_scalar_aware_common_shape_entries
       (List.length before_ctxt)
       (before_pi :: before_pis) after_pis (w :: ws) inferred)
    eqn:Hentries; try discriminate.
  inversion Hinfer; subst inferred.
  repeat split.
  - apply TilingCheck.ctxt_eqb_eq. exact Hctxt.
  - apply TilingCheck.ctxt_ty_eqb_eq. exact Hvars.
  - eapply check_common_tiling_band_recipeb_sound.
    exact Hrecipe.
  - eapply check_scalar_aware_common_shape_entries_sound.
    exact Hentries.
Qed.

Definition scalar_aware_reversal_bridge
    (envv: list Z)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (layout: scalar_aware_band_layout) : Prop :=
  let pis :=
    Tiling.compose_tiling_pinstrs_ext_from_after
      (List.length envv) before_pis after_pis ws in
  forall flat ip1 ip2,
    Tiling.PL.flatten_instrs_ext envv pis flat ->
    In ip1 flat ->
    In ip2 flat ->
    Tiling.PL.instr_point_ext_old_sched_lt ip1 ip2 ->
    Tiling.PL.instr_point_ext_new_sched_ge ip1 ip2 ->
    exists pi1 pi2 dim,
      nth_error pis (Tiling.PL.ip_nth_ext ip1) = Some pi1 /\
      nth_error pis (Tiling.PL.ip_nth_ext ip2) = Some pi2 /\
      (dim < List.length (sabl_loop_mask layout))%nat /\
      scalar_aware_component_active layout dim pi1 pi2 ip1 ip2.

Lemma scalar_aware_componentwise_permutable_implies_reordering_safe :
  forall envv before_pis after_pis ws layout,
    pinstr_list_scalar_aware_componentwise_permutable
      envv
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length envv) before_pis after_pis ws)
      layout ->
    scalar_aware_reversal_bridge
      envv before_pis after_pis ws layout ->
    pprog_tiling_reordering_safe
      envv before_pis after_pis ws [].
Proof.
  intros envv before_pis after_pis ws layout Hcomponents Hbridge.
  unfold pprog_tiling_reordering_safe,
         pprog_permutable_tiling_bands.
  intros flat ip1 ip2 Hflat Hin1 Hin2 Hold Hnew.
  destruct
    (Hbridge flat ip1 ip2 Hflat Hin1 Hin2 Hold Hnew)
    as [pi1 [pi2 [dim [Hpi1 [Hpi2 [Hdim Hactive]]]]]].
  eapply
    (Hcomponents flat ip1 ip2 pi1 pi2 dim);
    eauto.
Qed.

Lemma wf_pinstr_tiling_schedule_exact_cols_local :
  forall env vars pi,
    Tiling.PL.wf_pinstr_tiling env vars pi ->
    exact_listzzs_cols
      (List.length env + Tiling.PL.pi_depth pi)%nat
      (Tiling.PL.pi_schedule pi).
Proof.
  intros env vars pi Hwf.
  destruct Hwf as [Hwf _].
  destruct Hwf as
    [_ [_ [_ [_ [_ [_ [_ [Hsched _]]]]]]]].
  exact Hsched.
Qed.

Lemma firstn_band_skipn_reconstruct :
  forall (A: Type) start len (xs: list A),
    firstn start xs ++
    firstn len (skipn start xs) ++
    skipn (start + len)%nat xs =
    xs.
Proof.
  intros A start len xs.
  transitivity
    (firstn (start + len)%nat xs ++
     skipn (start + len)%nat xs).
  - rewrite firstn_add_local.
    rewrite app_assoc.
    reflexivity.
  - apply firstn_skipn.
Qed.

Lemma render_scalar_aware_value_prefix_length :
  forall mask band_values tile_values mixed_values,
    List.length band_values = List.length mask ->
    render_scalar_aware_value_prefix
      mask band_values tile_values = Some mixed_values ->
    List.length mixed_values = List.length mask.
Proof.
  induction mask as [|is_loop mask IH];
    intros band_values tile_values mixed_values Hband Hrender;
    destruct band_values as [|band_value band_values];
    simpl in *; try discriminate.
  - destruct tile_values; inversion Hrender; reflexivity.
  - injection Hband as Hband_tail.
    destruct is_loop.
    + destruct tile_values as [|tile_value tile_values]; try discriminate.
      destruct
        (render_scalar_aware_value_prefix
           mask band_values tile_values)
        as [mixed_tail|] eqn:Htail; try discriminate.
      inversion Hrender; subst mixed_values.
      simpl.
      f_equal.
      eapply IH.
      * exact Hband_tail.
      * exact Htail.
    + destruct
        (render_scalar_aware_value_prefix
           mask band_values tile_values)
        as [mixed_tail|] eqn:Htail; try discriminate.
      inversion Hrender; subst mixed_values.
      simpl.
      f_equal.
      eapply IH.
      * exact Hband_tail.
      * exact Htail.
Qed.

Lemma scalar_aware_reversal_implies_mixed_gt :
  forall prefix1 prefix2 mixed1 mixed2 band1 band2 suffix1 suffix2,
    List.length prefix1 = List.length prefix2 ->
    List.length mixed1 = List.length mixed2 ->
    lex_compare
      (prefix1 ++ (band1 ++ suffix1))
      (prefix2 ++ (band2 ++ suffix2)) = Lt ->
    lex_compare
      (prefix1 ++ (mixed1 ++ band1 ++ suffix1))
      (prefix2 ++ (mixed2 ++ band2 ++ suffix2)) <> Lt ->
    prefix1 = prefix2 /\
    lex_compare mixed1 mixed2 = Gt.
Proof.
  intros prefix1 prefix2 mixed1 mixed2 band1 band2 suffix1 suffix2
         Hprefix_len Hmixed_len Hold Hnew.
  assert (Hprefix : prefix1 = prefix2).
  {
    eapply preserved_equal_length_prefix_reversal_implies_prefix_eq
      with
        (old_rest1 := band1 ++ suffix1)
        (old_rest2 := band2 ++ suffix2)
        (new_rest1 := mixed1 ++ band1 ++ suffix1)
        (new_rest2 := mixed2 ++ band2 ++ suffix2);
      eauto.
  }
  split; [exact Hprefix|].
  subst prefix2.
  assert
    (Hrest :
       lex_compare (band1 ++ suffix1) (band2 ++ suffix2) = Lt).
  {
    rewrite lex_compare_app in Hold by reflexivity.
    rewrite lex_compare_reflexive in Hold.
    exact Hold.
  }
  destruct (lex_compare mixed1 mixed2) eqn:Hmixed; try reflexivity.
  - pose proof
      (lex_compare_eq_same_length_implies_eq_local_band
         mixed1 mixed2 Hmixed Hmixed_len) as Heq.
    subst mixed2.
    exfalso.
    apply Hnew.
    rewrite lex_compare_app by reflexivity.
    rewrite lex_compare_reflexive.
    rewrite lex_compare_app by reflexivity.
    rewrite lex_compare_reflexive.
    exact Hrest.
  - exfalso.
    apply Hnew.
    rewrite lex_compare_app by reflexivity.
    rewrite lex_compare_reflexive.
    rewrite lex_compare_app by exact Hmixed_len.
    rewrite Hmixed.
    reflexivity.
Qed.

Lemma affine_product_scalar_aware_layout_band_rows :
  forall layout sched idx,
    affine_product
      (scalar_aware_layout_band_rows layout sched) idx =
    firstn (List.length (sabl_loop_mask layout))
      (skipn (sabl_start layout) (affine_product sched idx)).
Proof.
  intros layout sched idx.
  unfold scalar_aware_layout_band_rows.
  rewrite affine_product_firstn_local.
  rewrite affine_product_skipn_local_component.
  reflexivity.
Qed.

Lemma eval_tile_links_eq_scalar_aware_loop_tile_values :
  forall w point params link_rows layout before_sched sizes,
    List.length point = stw_point_dim w ->
    schedule_rows_of_links w = Some link_rows ->
    List.map tl_tile_size (stw_links w) = sizes ->
    well_formed_statement_tiling_witness w ->
    Forall
      (fun link =>
         List.length (ae_param_coeffs (tl_expr link)) =
         List.length params)
      (stw_links w) ->
    select_by_mask
      (sabl_loop_mask layout)
      (scalar_aware_layout_band_rows layout before_sched) =
    link_rows ->
    eval_tile_links [] point params (stw_links w) =
    scalar_aware_loop_tile_values
      (sabl_loop_mask layout)
      (affine_product
         (scalar_aware_layout_band_rows layout before_sched)
         (params ++ point))
      sizes.
Proof.
  intros w point params link_rows layout before_sched sizes
         Hpoint Hrows Hsizes Hwf Hparams Hselected.
  rewrite
    (eval_tile_links_from_schedule_rows
       w point params link_rows sizes
       Hpoint Hrows Hsizes Hwf Hparams).
  unfold scalar_aware_loop_tile_values.
  rewrite <- affine_product_select_by_mask.
  rewrite Hselected.
  reflexivity.
Qed.

Lemma scalar_aware_component_active_from_band_values :
  forall layout dim pi1 pi2 ip1 ip2 old1 old2 band1 band2 x y,
    affine_product
      (Tiling.PL.pi_schedule1_ext pi1)
      (Tiling.PL.ip_index_ext ip1) = old1 ->
    affine_product
      (Tiling.PL.pi_schedule1_ext pi2)
      (Tiling.PL.ip_index_ext ip2) = old2 ->
    band1 =
      firstn (List.length (sabl_loop_mask layout))
        (skipn (sabl_start layout) old1) ->
    band2 =
      firstn (List.length (sabl_loop_mask layout))
        (skipn (sabl_start layout) old2) ->
    firstn (sabl_start layout) old1 =
    firstn (sabl_start layout) old2 ->
    listz_pointwise_le
      (select_scalar_values
         (firstn dim (sabl_loop_mask layout))
         (firstn dim band2))
      (select_scalar_values
         (firstn dim (sabl_loop_mask layout))
         (firstn dim band1)) ->
    nth_error band1 dim = Some x ->
    nth_error band2 dim = Some y ->
    (dim < List.length (sabl_loop_mask layout))%nat ->
    (x > y)%Z ->
    scalar_aware_component_active layout dim pi1 pi2 ip1 ip2.
Proof.
  intros layout dim pi1 pi2 ip1 ip2 old1 old2 band1 band2 x y
         Hfull1 Hfull2 Hband1 Hband2 Hprefix Hprior
         Hx Hy Hdim Hxy.
  unfold scalar_aware_component_active.
  cbn zeta.
  rewrite Hband1, Hband2 in Hprior.
  rewrite !firstn_firstn in Hprior.
  replace
    (Nat.min dim (List.length (sabl_loop_mask layout)))
    with dim in Hprior by lia.
  assert
    (Hfull_nth1 :
       nth_error old1 (sabl_start layout + dim)%nat = Some x).
  {
    rewrite Hband1 in Hx.
    eapply
      (nth_error_band_block_to_full
         (scalar_aware_band layout) old1 dim x).
    - exact Hdim.
    - exact Hx.
  }
  assert
    (Hfull_nth2 :
       nth_error old2 (sabl_start layout + dim)%nat = Some y).
  {
    rewrite Hband2 in Hy.
    eapply
      (nth_error_band_block_to_full
         (scalar_aware_band layout) old2 dim y).
    - exact Hdim.
    - exact Hy.
  }
  split.
  - rewrite !affine_product_firstn_local.
    rewrite Hfull1, Hfull2.
    exact Hprefix.
  - split.
    + rewrite !affine_product_select_scalar_rows.
      rewrite !affine_product_firstn_local.
      rewrite !affine_product_skipn_local_component.
      rewrite Hfull1, Hfull2.
      exact Hprior.
    + assert
        (Hvalue1 :
           semantic_band_value
             (List.length (Tiling.PL.ip_index_ext ip1))
             (sabl_start layout + dim)
             (Tiling.PL.pi_schedule1_ext pi1)
             (Tiling.PL.ip_index_ext ip1) =
           x).
      {
        apply semantic_band_value_of_nth_error.
        rewrite Hfull1.
        exact Hfull_nth1.
      }
      assert
        (Hvalue2 :
           semantic_band_value
             (List.length (Tiling.PL.ip_index_ext ip2))
             (sabl_start layout + dim)
             (Tiling.PL.pi_schedule1_ext pi2)
             (Tiling.PL.ip_index_ext ip2) =
           y).
      {
        apply semantic_band_value_of_nth_error.
        rewrite Hfull2.
        exact Hfull_nth2.
      }
      rewrite Hvalue1, Hvalue2.
      exact Hxy.
Qed.

(** Proof roadmap for one scalar-aware pair:

    - recover and type the two composed instruction points;
    - split each old schedule around the recognized band;
    - evaluate loop rows as tile coordinates while copying scalar rows;
    - show that a target reversal cannot come from the unchanged outer
      prefix or suffix;
    - locate the first decreasing active loop row and return its direct-check
      certificate.

    Scalar rows are not asserted permutable.  They stay fixed in the rendered
    prefix; only positions marked by [sabl_loop_mask] can discharge the final
    component obligation. *)
Lemma scalar_aware_pair_local_reversal_bridge_wf_with_env_len :
  forall before_pis before_ctxt before_vars after_pis ws layouts envv
         flat ip1 ip2,
    List.length before_ctxt = List.length envv ->
    TilingCheck.check_pprog_tiling_sourceb
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars) ws = true ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    List.length layouts = List.length before_pis ->
    Tiling.PL.flatten_instrs_ext envv
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length envv) before_pis after_pis ws) flat ->
    In ip1 flat ->
    In ip2 flat ->
    Tiling.PL.instr_point_ext_old_sched_lt ip1 ip2 ->
    Tiling.PL.instr_point_ext_new_sched_ge ip1 ip2 ->
    (forall before_pi after_pi w layout,
       nth_error before_pis (Tiling.PL.ip_nth_ext ip1) = Some before_pi ->
       nth_error after_pis (Tiling.PL.ip_nth_ext ip1) = Some after_pi ->
       nth_error ws (Tiling.PL.ip_nth_ext ip1) = Some w ->
       nth_error layouts (Tiling.PL.ip_nth_ext ip1) = Some layout ->
       scalar_aware_entry_shape
         (List.length before_ctxt) layout before_pi after_pi w) ->
    (forall before_pi after_pi w layout,
       nth_error before_pis (Tiling.PL.ip_nth_ext ip2) = Some before_pi ->
       nth_error after_pis (Tiling.PL.ip_nth_ext ip2) = Some after_pi ->
       nth_error ws (Tiling.PL.ip_nth_ext ip2) = Some w ->
       nth_error layouts (Tiling.PL.ip_nth_ext ip2) = Some layout ->
       scalar_aware_entry_shape
         (List.length before_ctxt) layout before_pi after_pi w) ->
    (forall layout1 layout2,
       nth_error layouts (Tiling.PL.ip_nth_ext ip1) = Some layout1 ->
       nth_error layouts (Tiling.PL.ip_nth_ext ip2) = Some layout2 ->
       layout1 = layout2) ->
    (forall w1 w2,
       nth_error ws (Tiling.PL.ip_nth_ext ip1) = Some w1 ->
       nth_error ws (Tiling.PL.ip_nth_ext ip2) = Some w2 ->
       tile_sizes_of_witness w1 = tile_sizes_of_witness w2) ->
    exists layout pi1 pi2 dim,
      nth_error layouts (Tiling.PL.ip_nth_ext ip1) = Some layout /\
      nth_error layouts (Tiling.PL.ip_nth_ext ip2) = Some layout /\
      nth_error
        (Tiling.compose_tiling_pinstrs_ext_from_after
           (List.length envv) before_pis after_pis ws)
        (Tiling.PL.ip_nth_ext ip1) = Some pi1 /\
      nth_error
        (Tiling.compose_tiling_pinstrs_ext_from_after
           (List.length envv) before_pis after_pis ws)
        (Tiling.PL.ip_nth_ext ip2) = Some pi2 /\
      (dim < List.length (sabl_loop_mask layout))%nat /\
      scalar_aware_component_active layout dim pi1 pi2 ip1 ip2.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws layouts envv
         flat ip1 ip2 Hlen_env Hsource Hwf_before Hlayouts_len
         Hflat Hin1 Hin2 Hold Hnew Hshape_at1 Hshape_at2
         Hsame_layout Hsame_recipe.
  pose proof
    (TilingCheck.check_pprog_tiling_sourceb_sound
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars) ws Hsource)
    as [Hprog [_ [Hwf_ws [Hpositive_ws Hdepths]]]].
  assert
    (Hwf_ws_env :
       Forall
         (Tiling.wf_statement_tiling_witness_with_param_dim
            (List.length envv))
         ws).
  {
    rewrite <- Hlen_env.
    exact Hwf_ws.
  }
  destruct
    (composed_point_pair_facts_of_members
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       ws envv flat ip1 ip2
       Hprog Hwf_ws_env Hpositive_ws Hdepths Hflat Hin1 Hin2)
    as [Hpoint1 Hpoint2].
  unfold composed_point_facts in Hpoint1, Hpoint2.
  destruct Hpoint1 as [before_pi1 [after_pi1 [w1
    [Hbefore1 [Hafter1 [Hw1
    [Hwf_stmt1 [Hpositive1 [Hpoint_depth1
    [Hpref1 [Hbel1 Hidx_len1]]]]]]]]]]].
  destruct Hpoint2 as [before_pi2 [after_pi2 [w2
    [Hbefore2 [Hafter2 [Hw2
    [Hwf_stmt2 [Hpositive2 [Hpoint_depth2
    [Hpref2 [Hbel2 Hidx_len2]]]]]]]]]]].
  assert
    (Hlayout_idx1 :
       (Tiling.PL.ip_nth_ext ip1 < List.length layouts)%nat).
  {
    rewrite Hlayouts_len.
    apply nth_error_Some.
    rewrite Hbefore1.
    discriminate.
  }
  assert
    (Hlayout_idx2 :
       (Tiling.PL.ip_nth_ext ip2 < List.length layouts)%nat).
  {
    rewrite Hlayouts_len.
    apply nth_error_Some.
    rewrite Hbefore2.
    discriminate.
  }
  destruct
    (nth_error layouts (Tiling.PL.ip_nth_ext ip1))
    as [layout1|] eqn:Hlayout1.
  2:{
    apply nth_error_None in Hlayout1.
    lia.
  }
  destruct
    (nth_error layouts (Tiling.PL.ip_nth_ext ip2))
    as [layout2|] eqn:Hlayout2.
  2:{
    apply nth_error_None in Hlayout2.
    lia.
  }
  pose proof
    (Hsame_layout layout1 layout2 eq_refl eq_refl) as Hlayout_eq.
  subst layout2.
  rename layout1 into layout.
  destruct
    (Hshape_at1 before_pi1 after_pi1 w1 layout
       Hbefore1 Hafter1 Hw1 eq_refl)
    as [link_rows1 [expected1
         [Hlink_rows1 [Hmask_nonempty1
         [Hband_len1 [Hselected1
         [Hexpected1 Htarget1]]]]]]].
  destruct
    (Hshape_at2 before_pi2 after_pi2 w2 layout
       Hbefore2 Hafter2 Hw2 eq_refl)
    as [link_rows2 [expected2
         [Hlink_rows2 [Hmask_nonempty2
         [Hband_len2 [Hselected2
         [Hexpected2 Htarget2]]]]]]].
  set (sizes := tile_sizes_of_witness w1).
  assert
    (Hsizes1 :
       List.map tl_tile_size (stw_links w1) = sizes).
  {
    reflexivity.
  }
  assert
    (Hsizes2 :
       List.map tl_tile_size (stw_links w2) = sizes).
  {
    unfold sizes, tile_sizes_of_witness.
    symmetry.
    eapply Hsame_recipe; eauto.
  }
  pose proof
    (Tiling.nth_error_compose_tiling_pinstrs_ext_from_after
       (List.length envv) before_pis after_pis ws
       (Tiling.PL.ip_nth_ext ip1)
       before_pi1 after_pi1 w1 Hbefore1 Hafter1 Hw1)
    as Hcomposed1.
  pose proof
    (Tiling.nth_error_compose_tiling_pinstrs_ext_from_after
       (List.length envv) before_pis after_pis ws
       (Tiling.PL.ip_nth_ext ip2)
       before_pi2 after_pi2 w2 Hbefore2 Hafter2 Hw2)
    as Hcomposed2.
  pose proof
    (Tiling.tiling_rel_pprog_structure_source_nth
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       (List.map Tiling.compiled_pinstr_tiling_witness ws)
       (Tiling.PL.ip_nth_ext ip1)
       before_pi1 after_pi1
       (Tiling.compiled_pinstr_tiling_witness w1)
       Hprog Hbefore1 Hafter1
       (Tiling.nth_error_map_some
          _ _ Tiling.compiled_pinstr_tiling_witness
          ws (Tiling.PL.ip_nth_ext ip1) w1 Hw1))
    as Hstmt1.
  pose proof
    (Tiling.tiling_rel_pprog_structure_source_nth
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       (List.map Tiling.compiled_pinstr_tiling_witness ws)
       (Tiling.PL.ip_nth_ext ip2)
       before_pi2 after_pi2
       (Tiling.compiled_pinstr_tiling_witness w2)
       Hprog Hbefore2 Hafter2
       (Tiling.nth_error_map_some
          _ _ Tiling.compiled_pinstr_tiling_witness
          ws (Tiling.PL.ip_nth_ext ip2) w2 Hw2))
    as Hstmt2.
  assert
    (Hafter_depth1 :
       Tiling.PL.pi_depth after_pi1 =
       (Tiling.PL.pi_depth before_pi1 +
        List.length (stw_links w1))%nat).
  {
    unfold Tiling.tiling_rel_pinstr_structure_source in Hstmt1.
    destruct Hstmt1 as [_ [Hdepth _]].
    exact Hdepth.
  }
  assert
    (Hafter_depth2 :
       Tiling.PL.pi_depth after_pi2 =
       (Tiling.PL.pi_depth before_pi2 +
        List.length (stw_links w2))%nat).
  {
    unfold Tiling.tiling_rel_pinstr_structure_source in Hstmt2.
    destruct Hstmt2 as [_ [Hdepth _]].
    exact Hdepth.
  }
  set
    (added1 :=
       Tiling.tiled_added_part
         (List.length envv) (List.length (stw_links w1))
         (Tiling.PL.ip_index_ext ip1)).
  set
    (point1 :=
       Tiling.tiled_point_part
         (List.length envv) (List.length (stw_links w1))
         (Tiling.PL.ip_index_ext ip1)).
  set
    (added2 :=
       Tiling.tiled_added_part
         (List.length envv) (List.length (stw_links w2))
         (Tiling.PL.ip_index_ext ip2)).
  set
    (point2 :=
       Tiling.tiled_point_part
         (List.length envv) (List.length (stw_links w2))
         (Tiling.PL.ip_index_ext ip2)).
  assert (Hadded_len1 : List.length added1 = List.length (stw_links w1)).
  {
    subst added1.
    eapply Tiling.tiled_added_part_length
      with (point_dim := stw_point_dim w1).
    rewrite Hidx_len1, Hafter_depth1, <- Hpoint_depth1.
    lia.
  }
  assert (Hadded_len2 : List.length added2 = List.length (stw_links w2)).
  {
    subst added2.
    eapply Tiling.tiled_added_part_length
      with (point_dim := stw_point_dim w2).
    rewrite Hidx_len2, Hafter_depth2, <- Hpoint_depth2.
    lia.
  }
  assert (Hpoint_len1 : List.length point1 = stw_point_dim w1).
  {
    subst point1.
    eapply Tiling.tiled_point_part_length
      with (added_dims := List.length (stw_links w1)).
    rewrite Hidx_len1, Hafter_depth1, <- Hpoint_depth1.
    lia.
  }
  assert (Hpoint_len2 : List.length point2 = stw_point_dim w2).
  {
    subst point2.
    eapply Tiling.tiled_point_part_length
      with (added_dims := List.length (stw_links w2)).
    rewrite Hidx_len2, Hafter_depth2, <- Hpoint_depth2.
    lia.
  }
  assert
    (Hidx_split1 :
       Tiling.PL.ip_index_ext ip1 = envv ++ added1 ++ point1).
  {
    subst added1 point1.
    transitivity
      (firstn (List.length envv) (Tiling.PL.ip_index_ext ip1) ++
       Tiling.tiled_added_part
         (List.length envv) (List.length (stw_links w1))
         (Tiling.PL.ip_index_ext ip1) ++
       Tiling.tiled_point_part
         (List.length envv) (List.length (stw_links w1))
         (Tiling.PL.ip_index_ext ip1)).
    - apply Tiling.tiled_index_split.
    - rewrite Hpref1. reflexivity.
  }
  assert
    (Hidx_split2 :
       Tiling.PL.ip_index_ext ip2 = envv ++ added2 ++ point2).
  {
    subst added2 point2.
    transitivity
      (firstn (List.length envv) (Tiling.PL.ip_index_ext ip2) ++
       Tiling.tiled_added_part
         (List.length envv) (List.length (stw_links w2))
         (Tiling.PL.ip_index_ext ip2) ++
       Tiling.tiled_point_part
         (List.length envv) (List.length (stw_links w2))
         (Tiling.PL.ip_index_ext ip2)).
    - apply Tiling.tiled_index_split.
    - rewrite Hpref2. reflexivity.
  }
  unfold Tiling.compose_tiling_pinstr_ext in Hbel1, Hbel2.
  destruct Hbel1 as
    [Hafter_dom1 [_ [_ [Hts11 [Hts21 [_ _]]]]]].
  destruct Hbel2 as
    [Hafter_dom2 [_ [_ [Hts12 [Hts22 [_ _]]]]]].
  assert
    (Hts11_old :
       Tiling.PL.ip_time_stamp1_ext ip1 =
       affine_product (Tiling.PL.pi_schedule before_pi1)
         (envv ++ point1)).
  {
    rewrite Hts11.
    cbn [Tiling.compose_tiling_pinstr_ext].
    rewrite Hidx_split1.
    unfold Tiling.lift_schedule_after_env.
    eapply Tiling.lift_affine_function_after_env_eval.
    - reflexivity.
    - exact Hadded_len1.
  }
  assert
    (Hts12_old :
       Tiling.PL.ip_time_stamp1_ext ip2 =
       affine_product (Tiling.PL.pi_schedule before_pi2)
         (envv ++ point2)).
  {
    rewrite Hts12.
    cbn [Tiling.compose_tiling_pinstr_ext].
    rewrite Hidx_split2.
    unfold Tiling.lift_schedule_after_env.
    eapply Tiling.lift_affine_function_after_env_eval.
    - reflexivity.
    - exact Hadded_len2.
  }
  assert
    (Hts21_after :
       Tiling.PL.ip_time_stamp2_ext ip1 =
       affine_product (Tiling.PL.pi_schedule after_pi1)
         (Tiling.PL.ip_index_ext ip1)).
  {
    rewrite Hts21.
    cbn [Tiling.compose_tiling_pinstr_ext].
    reflexivity.
  }
  assert
    (Hts22_after :
       Tiling.PL.ip_time_stamp2_ext ip2 =
       affine_product (Tiling.PL.pi_schedule after_pi2)
         (Tiling.PL.ip_index_ext ip2)).
  {
    rewrite Hts22.
    cbn [Tiling.compose_tiling_pinstr_ext].
    reflexivity.
  }
  assert
    (Hstmt1_env :
       Tiling.tiling_rel_pinstr_structure_source
         (List.length envv) before_pi1 after_pi1
         (Tiling.compiled_pinstr_tiling_witness w1)).
  {
    rewrite <- Hlen_env.
    exact Hstmt1.
  }
  assert
    (Hstmt2_env :
       Tiling.tiling_rel_pinstr_structure_source
         (List.length envv) before_pi2 after_pi2
         (Tiling.compiled_pinstr_tiling_witness w2)).
  {
    rewrite <- Hlen_env.
    exact Hstmt2.
  }
  destruct Hwf_stmt1 as [Hwf_stmt1 Hparams1].
  destruct Hwf_stmt2 as [Hwf_stmt2 Hparams2].
  assert
    (Hadded_eq1 :
       added1 = eval_tile_links [] point1 envv (stw_links w1)).
  {
    pose proof
      (Tiling.tiling_rel_pinstr_structure_source_domain_complete
         envv before_pi1 after_pi1
         (Tiling.compiled_pinstr_tiling_witness w1)
         added1 point1 Hstmt1_env
         (Tiling.wf_compiled_pinstr_tiling_witness w1)
         (Tiling.compiled_pinstr_tiling_witness_matches w1)
         Hadded_len1 Hpoint_len1
         (conj Hwf_stmt1 Hparams1) Hpositive1)
      as Hcomplete.
    rewrite Hidx_split1 in Hafter_dom1.
    specialize (Hcomplete Hafter_dom1).
    tauto.
  }
  assert
    (Hadded_eq2 :
       added2 = eval_tile_links [] point2 envv (stw_links w2)).
  {
    pose proof
      (Tiling.tiling_rel_pinstr_structure_source_domain_complete
         envv before_pi2 after_pi2
         (Tiling.compiled_pinstr_tiling_witness w2)
         added2 point2 Hstmt2_env
         (Tiling.wf_compiled_pinstr_tiling_witness w2)
         (Tiling.compiled_pinstr_tiling_witness_matches w2)
         Hadded_len2 Hpoint_len2
         (conj Hwf_stmt2 Hparams2) Hpositive2)
      as Hcomplete.
    rewrite Hidx_split2 in Hafter_dom2.
    specialize (Hcomplete Hafter_dom2).
    tauto.
  }
  pose proof
    (Tiling.Forall_nth_error
       _ _ _ _ _ Hwf_before Hbefore1) as Hwf_before1.
  pose proof
    (Tiling.Forall_nth_error
       _ _ _ _ _ Hwf_before Hbefore2) as Hwf_before2.
  pose proof
    (wf_pinstr_tiling_schedule_exact_cols_local
       before_ctxt before_vars before_pi1 Hwf_before1) as Hcols1.
  pose proof
    (wf_pinstr_tiling_schedule_exact_cols_local
       before_ctxt before_vars before_pi2 Hwf_before2) as Hcols2.
  destruct
    (scalar_aware_stripmine_schedule_after_env_eval
       (List.length before_ctxt)
       (List.length (stw_links w1))
       (Tiling.PL.pi_schedule before_pi1)
       layout expected1
       (List.length before_ctxt + Tiling.PL.pi_depth before_pi1)%nat
       envv added1 point1
       Hcols1 ltac:(lia) ltac:(lia)
       Hadded_len1 Hmask_nonempty1 Hexpected1)
    as [band_values1 [mixed_values1
         [Hband_values1 [Hrender1 Heval1]]]].
  destruct
    (scalar_aware_stripmine_schedule_after_env_eval
       (List.length before_ctxt)
       (List.length (stw_links w2))
       (Tiling.PL.pi_schedule before_pi2)
       layout expected2
       (List.length before_ctxt + Tiling.PL.pi_depth before_pi2)%nat
       envv added2 point2
       Hcols2 ltac:(lia) ltac:(lia)
       Hadded_len2 Hmask_nonempty2 Hexpected2)
    as [band_values2 [mixed_values2
         [Hband_values2 [Hrender2 Heval2]]]].
  assert
    (Hadded_loop1 :
       added1 =
       scalar_aware_loop_tile_values
         (sabl_loop_mask layout) band_values1 sizes).
  {
    rewrite Hadded_eq1.
    rewrite
      (eval_tile_links_eq_scalar_aware_loop_tile_values
         w1 point1 envv link_rows1 layout
         (Tiling.PL.pi_schedule before_pi1) sizes
         Hpoint_len1 Hlink_rows1 Hsizes1
         Hwf_stmt1 Hparams1 Hselected1).
    rewrite Hband_values1.
    rewrite <-
      (affine_product_scalar_aware_layout_band_rows
         layout (Tiling.PL.pi_schedule before_pi1)
         (envv ++ point1)).
    reflexivity.
  }
  assert
    (Hadded_loop2 :
       added2 =
       scalar_aware_loop_tile_values
         (sabl_loop_mask layout) band_values2 sizes).
  {
    rewrite Hadded_eq2.
    rewrite
      (eval_tile_links_eq_scalar_aware_loop_tile_values
         w2 point2 envv link_rows2 layout
         (Tiling.PL.pi_schedule before_pi2) sizes
         Hpoint_len2 Hlink_rows2 Hsizes2
         Hwf_stmt2 Hparams2 Hselected2).
    rewrite Hband_values2.
    rewrite <-
      (affine_product_scalar_aware_layout_band_rows
         layout (Tiling.PL.pi_schedule before_pi2)
         (envv ++ point2)).
    reflexivity.
  }
  assert
    (Hband_values_len1 :
       List.length band_values1 =
       List.length (sabl_loop_mask layout)).
  {
    rewrite Hband_values1.
    rewrite <-
      (affine_product_scalar_aware_layout_band_rows
         layout (Tiling.PL.pi_schedule before_pi1)
         (envv ++ point1)).
    unfold affine_product.
    rewrite map_length.
    exact Hband_len1.
  }
  assert
    (Hband_values_len2 :
       List.length band_values2 =
       List.length (sabl_loop_mask layout)).
  {
    rewrite Hband_values2.
    rewrite <-
      (affine_product_scalar_aware_layout_band_rows
         layout (Tiling.PL.pi_schedule before_pi2)
         (envv ++ point2)).
    unfold affine_product.
    rewrite map_length.
    exact Hband_len2.
  }
  assert
    (Hselected_values_len1 :
       List.length
         (select_by_mask (sabl_loop_mask layout) band_values1) =
       List.length sizes).
  {
    rewrite Hband_values1.
    rewrite <-
      (affine_product_scalar_aware_layout_band_rows
         layout (Tiling.PL.pi_schedule before_pi1)
         (envv ++ point1)).
    rewrite <- affine_product_select_by_mask.
    rewrite Hselected1.
    unfold affine_product.
    rewrite map_length.
    rewrite (schedule_rows_of_links_length w1 link_rows1 Hlink_rows1).
    rewrite <- Hsizes1.
    rewrite map_length.
    reflexivity.
  }
  assert
    (Hpositive_sizes : Forall (fun size => (0 < size)%Z) sizes).
  {
    pose proof (positive_tile_sizes_map (stw_links w1) Hpositive1)
      as Hpositive_sizes1.
    rewrite Hsizes1 in Hpositive_sizes1.
    exact Hpositive_sizes1.
  }
  pose proof
    (scalar_aware_loop_tile_values_monotone
       (sabl_loop_mask layout)
       band_values1 band_values2 sizes
       Hband_values_len1 Hband_values_len2
       Hselected_values_len1 Hpositive_sizes)
    as Hmonotone.
  rewrite <- Hadded_loop1, <- Hadded_loop2 in Hmonotone.
  destruct Htarget1 as [target_cols1 [target_extra1 Htarget_sched1]].
  destruct Htarget2 as [target_cols2 [target_extra2 Htarget_sched2]].
  assert
    (Hactual_target1 :
       Tiling.PL.ip_time_stamp2_ext ip1 =
       (firstn (sabl_start layout)
          (affine_product (Tiling.PL.pi_schedule before_pi1)
             (envv ++ point1)) ++
        mixed_values1 ++ band_values1 ++
        skipn
          (sabl_start layout + List.length (sabl_loop_mask layout))%nat
          (affine_product (Tiling.PL.pi_schedule before_pi1)
             (envv ++ point1))) ++
       repeat 0%Z target_extra1).
  {
    rewrite Hts21_after.
    rewrite Htarget_sched1.
    rewrite affine_product_pad_schedule_with_zero_rows.
    rewrite Hidx_split1.
    rewrite Heval1.
    reflexivity.
  }
  assert
    (Hactual_target2 :
       Tiling.PL.ip_time_stamp2_ext ip2 =
       (firstn (sabl_start layout)
          (affine_product (Tiling.PL.pi_schedule before_pi2)
             (envv ++ point2)) ++
        mixed_values2 ++ band_values2 ++
        skipn
          (sabl_start layout + List.length (sabl_loop_mask layout))%nat
          (affine_product (Tiling.PL.pi_schedule before_pi2)
             (envv ++ point2))) ++
       repeat 0%Z target_extra2).
  {
    rewrite Hts22_after.
    rewrite Htarget_sched2.
    rewrite affine_product_pad_schedule_with_zero_rows.
    rewrite Hidx_split2.
    rewrite Heval2.
    reflexivity.
  }
  assert
    (Hnew_without_padding :
       lex_compare
         (firstn (sabl_start layout)
            (affine_product (Tiling.PL.pi_schedule before_pi1)
               (envv ++ point1)) ++
          mixed_values1 ++ band_values1 ++
          skipn
            (sabl_start layout + List.length (sabl_loop_mask layout))%nat
            (affine_product (Tiling.PL.pi_schedule before_pi1)
               (envv ++ point1)))
         (firstn (sabl_start layout)
            (affine_product (Tiling.PL.pi_schedule before_pi2)
               (envv ++ point2)) ++
          mixed_values2 ++ band_values2 ++
          skipn
            (sabl_start layout + List.length (sabl_loop_mask layout))%nat
            (affine_product (Tiling.PL.pi_schedule before_pi2)
               (envv ++ point2))) <>
       Lt).
  {
    unfold Tiling.PL.instr_point_ext_new_sched_ge in Hnew.
    rewrite Hactual_target1, Hactual_target2 in Hnew.
    rewrite lex_compare_app_repeat_zero in Hnew.
    intro Hlt.
    rewrite Hlt in Hnew.
    destruct Hnew; discriminate.
  }
  assert
    (Hold_decomposed :
       lex_compare
         (firstn (sabl_start layout)
            (affine_product (Tiling.PL.pi_schedule before_pi1)
               (envv ++ point1)) ++
          band_values1 ++
          skipn
            (sabl_start layout + List.length (sabl_loop_mask layout))%nat
            (affine_product (Tiling.PL.pi_schedule before_pi1)
               (envv ++ point1)))
         (firstn (sabl_start layout)
            (affine_product (Tiling.PL.pi_schedule before_pi2)
               (envv ++ point2)) ++
          band_values2 ++
          skipn
            (sabl_start layout + List.length (sabl_loop_mask layout))%nat
            (affine_product (Tiling.PL.pi_schedule before_pi2)
               (envv ++ point2))) =
       Lt).
  {
    unfold Tiling.PL.instr_point_ext_old_sched_lt in Hold.
    rewrite Hts11_old, Hts12_old in Hold.
    pose proof
      (firstn_band_skipn_reconstruct
         Z (sabl_start layout)
         (List.length (sabl_loop_mask layout))
         (affine_product (Tiling.PL.pi_schedule before_pi1)
            (envv ++ point1))) as Hsplit1.
    pose proof
      (firstn_band_skipn_reconstruct
         Z (sabl_start layout)
         (List.length (sabl_loop_mask layout))
         (affine_product (Tiling.PL.pi_schedule before_pi2)
            (envv ++ point2))) as Hsplit2.
    rewrite <- Hband_values1 in Hsplit1.
    rewrite <- Hband_values2 in Hsplit2.
    rewrite <- Hsplit1, <- Hsplit2 in Hold.
    exact Hold.
  }
  assert
    (Hprefix_len :
       List.length
         (firstn (sabl_start layout)
            (affine_product (Tiling.PL.pi_schedule before_pi1)
               (envv ++ point1))) =
       List.length
         (firstn (sabl_start layout)
            (affine_product (Tiling.PL.pi_schedule before_pi2)
               (envv ++ point2)))).
  {
    pose proof Hband_len1 as Hband_sched_len1.
    pose proof Hband_len2 as Hband_sched_len2.
    unfold scalar_aware_layout_band_rows in
      Hband_sched_len1, Hband_sched_len2.
    rewrite !firstn_length, !skipn_length in
      Hband_sched_len1, Hband_sched_len2.
    assert
      (Hmask_fit1 :
         (List.length (sabl_loop_mask layout) <=
         (List.length (Tiling.PL.pi_schedule before_pi1) -
          sabl_start layout))%nat).
    {
      rewrite <- Hband_sched_len1.
      apply Nat.le_min_r.
    }
    assert
      (Hmask_fit2 :
         (List.length (sabl_loop_mask layout) <=
         (List.length (Tiling.PL.pi_schedule before_pi2) -
          sabl_start layout))%nat).
    {
      rewrite <- Hband_sched_len2.
      apply Nat.le_min_r.
    }
    assert
      (Hstart1 :
         (sabl_start layout <=
          List.length (Tiling.PL.pi_schedule before_pi1))%nat).
    {
      destruct (sabl_loop_mask layout); [contradiction|].
      simpl in Hmask_fit1.
      lia.
    }
    assert
      (Hstart2 :
         (sabl_start layout <=
          List.length (Tiling.PL.pi_schedule before_pi2))%nat).
    {
      destruct (sabl_loop_mask layout); [contradiction|].
      simpl in Hmask_fit2.
      lia.
    }
    unfold affine_product.
    rewrite !firstn_length, !map_length.
    rewrite !Nat.min_l by assumption.
    reflexivity.
  }
  assert
    (Hmixed_len :
       List.length mixed_values1 = List.length mixed_values2).
  {
    rewrite
      (render_scalar_aware_value_prefix_length
         (sabl_loop_mask layout)
         band_values1 added1 mixed_values1
         Hband_values_len1 Hrender1).
    rewrite
      (render_scalar_aware_value_prefix_length
         (sabl_loop_mask layout)
         band_values2 added2 mixed_values2
         Hband_values_len2 Hrender2).
    reflexivity.
  }
  destruct
    (scalar_aware_reversal_implies_mixed_gt
       (firstn (sabl_start layout)
          (affine_product (Tiling.PL.pi_schedule before_pi1)
             (envv ++ point1)))
       (firstn (sabl_start layout)
          (affine_product (Tiling.PL.pi_schedule before_pi2)
             (envv ++ point2)))
       mixed_values1 mixed_values2
       band_values1 band_values2
       (skipn
          (sabl_start layout + List.length (sabl_loop_mask layout))%nat
          (affine_product (Tiling.PL.pi_schedule before_pi1)
             (envv ++ point1)))
       (skipn
          (sabl_start layout + List.length (sabl_loop_mask layout))%nat
          (affine_product (Tiling.PL.pi_schedule before_pi2)
             (envv ++ point2)))
       Hprefix_len Hmixed_len Hold_decomposed Hnew_without_padding)
    as [Hprefix_eq Hmixed_gt].
  destruct
    (scalar_aware_prefix_gt_implies_active_decrease
       (sabl_loop_mask layout)
       band_values1 band_values2 added1 added2
       Hmonotone mixed_values1 mixed_values2
       Hrender1 Hrender2 Hmixed_gt)
    as [dim [x [y
         [Hdim [Hx [Hy [Hxy Hprior]]]]]]].
  assert
    (Hfull_composed1 :
       affine_product
         (Tiling.PL.pi_schedule1_ext
            (Tiling.compose_tiling_pinstr_ext
               (List.length envv) before_pi1 after_pi1 w1))
         (Tiling.PL.ip_index_ext ip1) =
       affine_product
         (Tiling.PL.pi_schedule before_pi1) (envv ++ point1)).
  {
    cbn [Tiling.compose_tiling_pinstr_ext].
    rewrite Hidx_split1.
    eapply Tiling.lift_affine_function_after_env_eval.
    - reflexivity.
    - exact Hadded_len1.
  }
  assert
    (Hfull_composed2 :
       affine_product
         (Tiling.PL.pi_schedule1_ext
            (Tiling.compose_tiling_pinstr_ext
               (List.length envv) before_pi2 after_pi2 w2))
         (Tiling.PL.ip_index_ext ip2) =
       affine_product
         (Tiling.PL.pi_schedule before_pi2) (envv ++ point2)).
  {
    cbn [Tiling.compose_tiling_pinstr_ext].
    rewrite Hidx_split2.
    eapply Tiling.lift_affine_function_after_env_eval.
    - reflexivity.
    - exact Hadded_len2.
  }
  exists layout,
    (Tiling.compose_tiling_pinstr_ext
       (List.length envv) before_pi1 after_pi1 w1),
    (Tiling.compose_tiling_pinstr_ext
       (List.length envv) before_pi2 after_pi2 w2),
    dim.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact Hcomposed1|].
  split; [exact Hcomposed2|].
  split; [exact Hdim|].
  eapply scalar_aware_component_active_from_band_values
    with
      (old1 :=
         affine_product
           (Tiling.PL.pi_schedule before_pi1) (envv ++ point1))
      (old2 :=
         affine_product
           (Tiling.PL.pi_schedule before_pi2) (envv ++ point2))
      (band1 := band_values1)
      (band2 := band_values2)
      (x := x) (y := y).
  - exact Hfull_composed1.
  - exact Hfull_composed2.
  - exact Hband_values1.
  - exact Hband_values2.
  - exact Hprefix_eq.
  - exact Hprior.
  - exact Hx.
  - exact Hy.
  - exact Hdim.
  - exact Hxy.
Qed.

Lemma scalar_aware_common_shape_reversal_bridge :
  forall before_pis before_ctxt before_vars after_pis ws
         layout envv,
    List.length before_ctxt = List.length envv ->
    TilingCheck.check_pprog_tiling_sourceb
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars) ws = true ->
    scalar_aware_shape_entries
      (List.length before_ctxt) layout before_pis after_pis ws ->
    common_tiling_band_recipe ws ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    scalar_aware_reversal_bridge
      envv before_pis after_pis ws layout.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws
         layout envv Hlen_env Hsource Hshape
         [sizes Hcommon_sizes] Hwf_before.
  unfold scalar_aware_reversal_bridge.
  intros flat ip1 ip2 Hflat Hin1 Hin2 Hold Hnew.
  assert
    (Hshape_at :
       forall n before_pi after_pi w layout',
         nth_error before_pis n = Some before_pi ->
         nth_error after_pis n = Some after_pi ->
         nth_error ws n = Some w ->
         nth_error (repeat layout (List.length before_pis)) n =
           Some layout' ->
         scalar_aware_entry_shape
           (List.length before_ctxt) layout' before_pi after_pi w).
  {
    intros n before_pi after_pi w layout'
           Hbefore Hafter Hw Hlayout.
    assert (Hn : (n < List.length before_pis)%nat).
    {
      apply nth_error_Some.
      rewrite Hbefore.
      discriminate.
    }
    rewrite nth_error_repeat in Hlayout by exact Hn.
    inversion Hlayout; subst layout'.
    eapply scalar_aware_shape_entries_nth_error; eauto.
  }
  assert
    (Hsame_layout :
       forall layout1 layout2,
         nth_error
           (repeat layout (List.length before_pis))
           (Tiling.PL.ip_nth_ext ip1) = Some layout1 ->
         nth_error
           (repeat layout (List.length before_pis))
           (Tiling.PL.ip_nth_ext ip2) = Some layout2 ->
         layout1 = layout2).
  {
    intros layout1 layout2 Hlayout1 Hlayout2.
    assert
      (Hn1_repeat :
         (Tiling.PL.ip_nth_ext ip1 <
          List.length (repeat layout (List.length before_pis)))%nat).
    {
      apply nth_error_Some.
      rewrite Hlayout1.
      discriminate.
    }
    assert
      (Hn2_repeat :
         (Tiling.PL.ip_nth_ext ip2 <
          List.length (repeat layout (List.length before_pis)))%nat).
    {
      apply nth_error_Some.
      rewrite Hlayout2.
      discriminate.
    }
    rewrite repeat_length in Hn1_repeat, Hn2_repeat.
    rewrite nth_error_repeat in Hlayout1 by exact Hn1_repeat.
    rewrite nth_error_repeat in Hlayout2 by exact Hn2_repeat.
    congruence.
  }
  assert
    (Hsame_recipe :
       forall w1 w2,
         nth_error ws (Tiling.PL.ip_nth_ext ip1) = Some w1 ->
         nth_error ws (Tiling.PL.ip_nth_ext ip2) = Some w2 ->
         tile_sizes_of_witness w1 = tile_sizes_of_witness w2).
  {
    intros w1 w2 Hw1 Hw2.
    pose proof
      (common_tiling_band_recipe_nth_error
         ws sizes (Tiling.PL.ip_nth_ext ip1) w1
         Hcommon_sizes Hw1) as Hsizes1.
    pose proof
      (common_tiling_band_recipe_nth_error
         ws sizes (Tiling.PL.ip_nth_ext ip2) w2
         Hcommon_sizes Hw2) as Hsizes2.
    unfold tile_sizes_of_witness.
    congruence.
  }
  destruct
    (scalar_aware_pair_local_reversal_bridge_wf_with_env_len
       before_pis before_ctxt before_vars after_pis ws
       (repeat layout (List.length before_pis)) envv
       flat ip1 ip2
       Hlen_env Hsource Hwf_before
       ltac:(rewrite repeat_length; reflexivity)
       Hflat Hin1 Hin2 Hold Hnew
       (Hshape_at (Tiling.PL.ip_nth_ext ip1))
       (Hshape_at (Tiling.PL.ip_nth_ext ip2))
       Hsame_layout Hsame_recipe)
    as [pair_layout [pi1 [pi2 [dim
         [Hlayout1 [Hlayout2
         [Hpi1 [Hpi2 [Hdim Hactive]]]]]]]]].
  assert
    (Hn_repeat :
       (Tiling.PL.ip_nth_ext ip1 <
        List.length (repeat layout (List.length before_pis)))%nat).
  {
    apply nth_error_Some.
    rewrite Hlayout1.
    discriminate.
  }
  rewrite repeat_length in Hn_repeat.
  rewrite nth_error_repeat in Hlayout1 by exact Hn_repeat.
  inversion Hlayout1; subst pair_layout.
  exists pi1, pi2, dim.
  split; [exact Hpi1|].
  split; [exact Hpi2|].
  split; [exact Hdim|].
  exact Hactive.
Qed.

Definition checked_tiling_sourceb_scalar_aware_direct
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness) : imp bool :=
  if TilingCheck.check_pprog_tiling_sourceb before after ws then
    match infer_pprog_scalar_aware_common_shape before after ws with
    | Some layout =>
        check_pprog_scalar_aware_permutable_band_direct
          before after ws layout
    | None => pure false
    end
  else pure false.

Lemma checked_tiling_sourceb_scalar_aware_direct_true_inv :
  forall before after ws,
    mayReturn
      (checked_tiling_sourceb_scalar_aware_direct before after ws)
      true ->
    exists layout,
      TilingCheck.check_pprog_tiling_sourceb before after ws = true /\
      infer_pprog_scalar_aware_common_shape before after ws =
        Some layout /\
      mayReturn
        (check_pprog_scalar_aware_permutable_band_direct
           before after ws layout)
        true.
Proof.
  intros before after ws Hcheck.
  unfold checked_tiling_sourceb_scalar_aware_direct in Hcheck.
  destruct (TilingCheck.check_pprog_tiling_sourceb before after ws)
    eqn:Hsource.
  2:{
    apply mayReturn_pure in Hcheck.
    discriminate.
  }
  destruct (infer_pprog_scalar_aware_common_shape before after ws)
    as [layout|] eqn:Hshape.
  2:{
    apply mayReturn_pure in Hcheck.
    discriminate.
  }
  exists layout.
  repeat split; assumption.
Qed.

Lemma checked_tiling_sourceb_scalar_aware_direct_reordering_safe :
  forall before_pis before_ctxt before_vars after_pis ws
         envv,
    List.length before_ctxt = List.length envv ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      after_pis ->
    mayReturn
      (checked_tiling_sourceb_scalar_aware_direct
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars) ws)
      true ->
    pprog_tiling_reordering_safe
      envv before_pis after_pis ws [].
Proof.
  intros before_pis before_ctxt before_vars after_pis ws
         envv Hlen_env Hwf_before Hwf_after Hcheck.
  destruct
    (checked_tiling_sourceb_scalar_aware_direct_true_inv
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars) ws Hcheck)
    as [layout [Hsource [Hshape Hcomponents]]].
  destruct
    (infer_pprog_scalar_aware_common_shape_sound
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars ws layout Hshape)
    as [_ [_ [Hrecipe Hshape_entries]]].
  pose proof
    (TilingCheck.check_pprog_tiling_sourceb_sound
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars) ws Hsource)
    as [Hprog [_ [Hwf_ws [_ Hdepths]]]].
  assert
    (Hwits :
       Forall2 Tiling.after_matches_tiling_witness after_pis ws).
  {
    eapply
      (tiling_rel_pprog_structure_source_after_matches
         before_pis before_ctxt before_vars
         after_pis before_ctxt before_vars ws);
      eauto.
  }
  assert
    (Hcomposed_wf :
       Forall
         (Tiling.PL.wf_pinstr_ext_tiling before_ctxt)
         (Tiling.compose_tiling_pinstrs_ext_from_after
            (List.length before_ctxt) before_pis after_pis ws)).
  {
    eapply compose_tiling_pinstrs_ext_from_after_wf_tiling;
      eauto.
  }
  assert
    (Hcomponentwise :
       pinstr_list_scalar_aware_componentwise_permutable
         envv
         (Tiling.compose_tiling_pinstrs_ext_from_after
            (List.length before_ctxt) before_pis after_pis ws)
         layout).
  {
    eapply
      (check_pprog_scalar_aware_permutable_band_direct_sound
         before_ctxt envv
         before_pis before_ctxt before_vars
         after_pis before_ctxt before_vars ws layout).
    - exact Hlen_env.
    - exact Hcomposed_wf.
    - exact Hcomponents.
    - reflexivity.
  }
  eapply scalar_aware_componentwise_permutable_implies_reordering_safe.
  - rewrite Hlen_env in Hcomponentwise.
    exact Hcomponentwise.
  - eapply
      (scalar_aware_common_shape_reversal_bridge
         before_pis before_ctxt before_vars after_pis ws
         layout envv);
      eauto.
Qed.

Lemma checked_tiling_sourceb_scalar_aware_direct_correct_same_ctxt :
  forall before_pis before_ctxt before_vars after_pis ws st1 st2,
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      after_pis ->
    mayReturn
      (checked_tiling_sourceb_scalar_aware_direct
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars) ws)
      true ->
    Tiling.PL.instance_list_semantics
      (after_pis, before_ctxt, before_vars) st1 st2 ->
    exists st2',
      Tiling.PL.instance_list_semantics
        (before_pis, before_ctxt, before_vars) st1 st2' /\
      TilingPolIRs.State.eq st2 st2'.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws st1 st2
         Hwf_before Hwf_after Hcheck Hsem.
  destruct
    (checked_tiling_sourceb_scalar_aware_direct_true_inv
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars) ws Hcheck)
    as [layout [Hsource _]].
  eapply
    (tiling_sourceb_validate_correct_with_reordering
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars)
       ws [] st1 st2).
  - exact Hsource.
  - simpl.
    intros envv Hlen_env.
    eapply
      (checked_tiling_sourceb_scalar_aware_direct_reordering_safe
         before_pis before_ctxt before_vars after_pis ws envv);
      eauto.
  - exact Hsem.
Qed.

End ScalarAwareBands.

(** * Phase-aware and second-level band layouts *)

Section PhaseAwareSemanticBands.

(** Program-wide phase-preserving semantic bands.

    A source-like OpenScop schedule can contain a scalar phase row between
    loop rows.  Statements of different depths then have different local
    strip-mining recipes, but the phase occupies one common global schedule
    slot.  These definitions retain that slot in every generated stage while
    keeping only loop rows in the semantic band checked for permutability. *)

Fixpoint count_true (mask: list bool) : nat :=
  match mask with
  | [] => O
  | keep :: mask' =>
      (if keep then S (count_true mask') else count_true mask')
  end.

Definition phase_semantic_schedule_slot_scalarb
    (env_size slot: nat)
    (before_pis: list Tiling.PL.PolyInstr) : bool :=
  forallb
    (fun pi =>
       match nth_error (Tiling.PL.pi_schedule pi) slot with
       | Some row => schedule_row_point_scalarb env_size row
       | None => true
       end)
    before_pis.

Definition global_phase_semantic_loop_mask
    (env_size: nat)
    (before_pis: list Tiling.PL.PolyInstr) : list bool :=
  let schedules := List.map Tiling.PL.pi_schedule before_pis in
  List.map
    (fun slot =>
       negb
         (phase_semantic_schedule_slot_scalarb
            env_size slot before_pis))
    (List.seq O (max_schedule_length schedules)).

Definition phase_semantic_has_scalarb (mask: list bool) : bool :=
  existsb negb mask.

Definition phase_semantic_padded_source_schedule
    (env_size band_width: nat)
    (before_pi: Tiling.PL.PolyInstr) : Schedule :=
  Tiling.PL.pad_schedule_to_len
    (env_size + Tiling.PL.pi_depth before_pi)%nat
    band_width
    (Tiling.PL.pi_schedule before_pi).

Definition phase_semantic_lifted_band_rows
    (env_size added_dims: nat)
    (mask: list bool)
    (before_pi: Tiling.PL.PolyInstr) : Schedule :=
  Tiling.lift_schedule_after_env
    added_dims env_size
    (phase_semantic_padded_source_schedule
       env_size (List.length mask) before_pi).

Definition phase_semantic_padded_identity_rows_from
    (total_cols env_size local_width global_width: nat) : Schedule :=
  Tiling.identity_affine_rows_from total_cols env_size local_width ++
  repeat
    (zero_schedule_row total_cols)
    (global_width - local_width).

Definition phase_semantic_padded_identity_rows_at
    (total_cols env_size global_width: nat)
    (positions: list nat) : Schedule :=
  identity_affine_rows_at total_cols env_size positions ++
  repeat
    (zero_schedule_row total_cols)
    (global_width - List.length positions).

Definition phase_semantic_ordinary_target_schedule
    (env_size: nat)
    (mask: list bool)
    (before_pi: Tiling.PL.PolyInstr)
    (w: statement_tiling_witness) : option Schedule :=
  let local_width := List.length (stw_links w) in
  let global_width := count_true mask in
  let added_dims := local_width in
  let total_cols :=
    (env_size + added_dims + stw_point_dim w)%nat in
  let band_rows :=
    phase_semantic_lifted_band_rows
      env_size added_dims mask before_pi in
  let tile_rows :=
    phase_semantic_padded_identity_rows_from
      total_cols env_size local_width global_width in
  match
    render_scalar_aware_tile_prefix mask band_rows tile_rows
  with
  | Some tile_stage => Some (tile_stage ++ band_rows)
  | None => None
  end.

Definition phase_semantic_second_level_target_schedule
    (env_size: nat)
    (mask: list bool)
    (before_pi: Tiling.PL.PolyInstr)
    (w: statement_tiling_witness)
    (recipe: second_level_band_recipe) : option Schedule :=
  let local_width := List.length (slbr_root_rows recipe) in
  let global_width := count_true mask in
  let added_dims := (2 * local_width)%nat in
  let total_cols :=
    (env_size + added_dims + stw_point_dim w)%nat in
  let band_rows :=
    phase_semantic_lifted_band_rows
      env_size added_dims mask before_pi in
  let child_rows :=
    phase_semantic_padded_identity_rows_at
      total_cols env_size global_width
      (second_level_child_positions local_width) in
  let root_rows :=
    phase_semantic_padded_identity_rows_at
      total_cols env_size global_width
      (second_level_root_positions local_width) in
  match
    render_scalar_aware_tile_prefix mask band_rows child_rows,
    render_scalar_aware_tile_prefix mask band_rows root_rows
  with
  | Some child_stage, Some root_stage =>
      Some (child_stage ++ root_stage ++ band_rows)
  | _, _ => None
  end.

Definition check_phase_semantic_source_scheduleb
    (env_size: nat)
    (mask: list bool)
    (before_pi: Tiling.PL.PolyInstr)
    (loop_rows: Schedule) : bool :=
  check_schedule_with_symmetric_trailing_zero_paddingb
    loop_rows
    (select_by_mask mask
       (phase_semantic_padded_source_schedule
          env_size (List.length mask) before_pi)).

Fixpoint check_phase_semantic_ordinary_schedulesb
    (env_size: nat)
    (mask: list bool)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (loop_rows: list Schedule) : bool :=
  match before_pis, after_pis, ws, loop_rows with
  | [], [], [], [] => true
  | before_pi :: before_pis', after_pi :: after_pis',
    w :: ws', rows :: loop_rows' =>
      check_phase_semantic_source_scheduleb
        env_size mask before_pi rows &&
      match
        phase_semantic_ordinary_target_schedule
          env_size mask before_pi w
      with
      | Some expected =>
          check_schedule_with_symmetric_trailing_zero_paddingb
            expected (Tiling.PL.pi_schedule after_pi) &&
          check_phase_semantic_ordinary_schedulesb
            env_size mask before_pis' after_pis' ws' loop_rows'
      | None => false
      end
  | _, _, _, _ => false
  end.

Fixpoint check_phase_semantic_second_level_schedules_symmetricb
    (env_size: nat)
    (mask: list bool)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (recipes: list second_level_band_recipe)
    (loop_rows: list Schedule) : bool :=
  match before_pis, after_pis, ws, recipes, loop_rows with
  | [], [], [], [], [] => true
  | before_pi :: before_pis', after_pi :: after_pis',
    w :: ws', recipe :: recipes', rows :: loop_rows' =>
      check_phase_semantic_source_scheduleb
        env_size mask before_pi rows &&
      match
        phase_semantic_second_level_target_schedule
          env_size mask before_pi w recipe
      with
      | Some expected =>
          check_schedule_with_symmetric_trailing_zero_paddingb
            expected (Tiling.PL.pi_schedule after_pi) &&
          check_phase_semantic_second_level_schedules_symmetricb
            env_size mask before_pis' after_pis' ws'
            recipes' loop_rows'
      | None => false
      end
  | _, _, _, _, _ => false
  end.

Fixpoint check_phase_semantic_second_level_sourcesb
    (env_size: nat)
    (mask: list bool)
    (before_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (recipes: list second_level_band_recipe)
    (loop_rows: list Schedule) : bool :=
  match before_pis, ws, recipes, loop_rows with
  | [], [], [], [] => true
  | before_pi :: before_pis', w :: ws',
    recipe :: recipes', rows :: loop_rows' =>
      check_phase_semantic_source_scheduleb
        env_size mask before_pi rows &&
      check_phase_semantic_second_level_sourcesb
        env_size mask before_pis' ws' recipes' loop_rows'
  | _, _, _, _ => false
  end.

Fixpoint phase_semantic_second_level_expected_schedules
    (env_size: nat)
    (mask: list bool)
    (before_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (recipes: list second_level_band_recipe)
    : option (list Schedule) :=
  match before_pis, ws, recipes with
  | [], [], [] => Some []
  | before_pi :: before_pis', w :: ws', recipe :: recipes' =>
      match
        phase_semantic_second_level_target_schedule
          env_size mask before_pi w recipe,
        phase_semantic_second_level_expected_schedules
          env_size mask before_pis' ws' recipes'
      with
      | Some expected, Some rest => Some (expected :: rest)
      | _, _ => None
      end
  | _, _, _ => None
  end.

Definition check_phase_semantic_second_level_schedules_zero_erasureb
    (env_size: nat)
    (mask: list bool)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (recipes: list second_level_band_recipe)
    (loop_rows: list Schedule) : bool :=
  check_phase_semantic_second_level_sourcesb
    env_size mask before_pis ws recipes loop_rows &&
  match
    phase_semantic_second_level_expected_schedules
      env_size mask before_pis ws recipes
  with
  | Some expected =>
      check_schedule_lists_zero_erasure_same_masksb
        expected (List.map Tiling.PL.pi_schedule after_pis)
  | None => false
  end.

Definition check_phase_semantic_second_level_schedulesb
    (env_size: nat)
    (mask: list bool)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (recipes: list second_level_band_recipe)
    (loop_rows: list Schedule) : bool :=
  check_phase_semantic_second_level_schedules_symmetricb
    env_size mask before_pis after_pis ws recipes loop_rows ||
  check_phase_semantic_second_level_schedules_zero_erasureb
    env_size mask before_pis after_pis ws recipes loop_rows.

Fixpoint phase_semantic_full_schedules_for_tiling
    (env_size: nat)
    (mask: list bool)
    (before_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    : option (list Schedule) :=
  match before_pis, ws with
  | [], [] => Some []
  | before_pi :: before_pis', w :: ws' =>
      match
        phase_semantic_full_schedules_for_tiling
          env_size mask before_pis' ws'
      with
      | Some rest =>
          Some
            (phase_semantic_lifted_band_rows
               env_size (List.length (stw_links w)) mask before_pi ::
             rest)
      | None => None
      end
  | _, _ => None
  end.

Record phase_semantic_ordinary_band_shape := {
  psobs_rows : list Schedule;
  psobs_full_rows : list Schedule;
  psobs_global_sizes : list Z;
  psobs_loop_mask : list bool;
}.

Record phase_semantic_second_level_band_shape := {
  pssbs_rows : list Schedule;
  pssbs_full_rows : list Schedule;
  pssbs_recipes : list second_level_band_recipe;
  pssbs_global_root_sizes : list Z;
  pssbs_global_child_sizes : list Z;
  pssbs_loop_mask : list bool;
}.

Definition infer_pprog_phase_semantic_ordinary_band_shape
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness)
    : option phase_semantic_ordinary_band_shape :=
  let '(before_pis, before_ctxt, before_vars) := before in
  let '(after_pis, after_ctxt, after_vars) := after in
  if TilingCheck.ctxt_eqb before_ctxt after_ctxt &&
     TilingCheck.ctxt_ty_eqb before_vars after_vars
  then
    match parse_ordinary_semantic_data ws with
    | Some data =>
        let raw_schedules := List.map fst data in
        let local_sizes := List.map snd data in
        let semantic_mask :=
          global_semantic_schedule_mask raw_schedules in
        let loop_mask :=
          global_phase_semantic_loop_mask
            (List.length before_ctxt) before_pis in
        match
          infer_global_prefix_sizes local_sizes,
          compact_semantic_schedules
            (List.length before_ctxt) before_pis
            raw_schedules semantic_mask,
          phase_semantic_full_schedules_for_tiling
            (List.length before_ctxt) loop_mask before_pis ws
        with
        | Some global_sizes, Some semantic_rows, Some full_rows =>
            if Nat.ltb O (List.length semantic_mask) &&
               Nat.eqb
                 (List.length global_sizes)
                 (count_true loop_mask) &&
               phase_semantic_has_scalarb loop_mask &&
               check_phase_semantic_ordinary_schedulesb
                 (List.length before_ctxt) loop_mask
                 before_pis after_pis ws raw_schedules
            then
              Some
                {| psobs_rows := raw_schedules;
                   psobs_full_rows := full_rows;
                   psobs_global_sizes := global_sizes;
                   psobs_loop_mask := loop_mask |}
            else None
        | _, _, _ => None
        end
    | None => None
    end
  else None.

Definition infer_pprog_phase_semantic_second_level_band_shape
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness)
    : option phase_semantic_second_level_band_shape :=
  let '(before_pis, before_ctxt, before_vars) := before in
  let '(after_pis, after_ctxt, after_vars) := after in
  if TilingCheck.ctxt_eqb before_ctxt after_ctxt &&
     TilingCheck.ctxt_ty_eqb before_vars after_vars
  then
    match parse_second_level_semantic_recipes ws with
    | Some recipes =>
        let raw_schedules := List.map slbr_root_rows recipes in
        let root_sizes := List.map slbr_root_sizes recipes in
        let child_sizes := List.map slbr_child_sizes recipes in
        let semantic_mask :=
          global_semantic_schedule_mask raw_schedules in
        let loop_mask :=
          global_phase_semantic_loop_mask
            (List.length before_ctxt) before_pis in
        match
          infer_global_prefix_sizes root_sizes,
          infer_global_prefix_sizes child_sizes,
          compact_semantic_schedules
            (List.length before_ctxt) before_pis
            raw_schedules semantic_mask,
          phase_semantic_full_schedules_for_tiling
            (List.length before_ctxt) loop_mask before_pis ws
        with
        | Some global_root_sizes,
          Some global_child_sizes,
          Some semantic_rows,
          Some full_rows =>
            if Nat.ltb O (List.length semantic_mask) &&
               Nat.eqb
                 (List.length global_root_sizes)
                 (count_true loop_mask) &&
               Nat.eqb
                 (List.length global_child_sizes)
                 (count_true loop_mask) &&
               phase_semantic_has_scalarb loop_mask &&
               check_phase_semantic_second_level_schedulesb
                 (List.length before_ctxt) loop_mask
                 before_pis after_pis ws recipes raw_schedules
            then
              Some
                {| pssbs_rows := raw_schedules;
                   pssbs_full_rows := full_rows;
                   pssbs_recipes := recipes;
                   pssbs_global_root_sizes := global_root_sizes;
                   pssbs_global_child_sizes := global_child_sizes;
                   pssbs_loop_mask := loop_mask |}
            else None
        | _, _, _, _ => None
        end
    | None => None
    end
  else None.

Definition checked_tiling_sourceb_phase_semantic_band_direct
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness) : imp bool :=
  let '(before_pis, before_ctxt, _) := before in
  let '(after_pis, _, _) := after in
  let pis :=
    Tiling.compose_tiling_pinstrs_ext_from_after
      (List.length before_ctxt) before_pis after_pis ws in
  if TilingCheck.check_pprog_tiling_sourceb before after ws then
    match
      infer_pprog_phase_semantic_ordinary_band_shape before after ws
    with
    | Some shape =>
        check_semantic_band_components_direct
          pis (psobs_full_rows shape) (List.length before_ctxt)
    | None =>
        match
          infer_pprog_phase_semantic_second_level_band_shape before after ws
        with
        | Some shape =>
            check_semantic_band_components_direct
              pis (pssbs_full_rows shape) (List.length before_ctxt)
        | None => pure false
        end
    end
  else pure false.

Inductive phase_semantic_ordinary_schedules_match
    (env_size: nat)
    (mask: list bool)
    : list Tiling.PL.PolyInstr ->
      list Tiling.PL.PolyInstr ->
      list statement_tiling_witness ->
      list Schedule -> Prop :=
| PhaseSemanticOrdinarySchedulesMatchNil :
    phase_semantic_ordinary_schedules_match
      env_size mask [] [] [] []
| PhaseSemanticOrdinarySchedulesMatchCons :
    forall before_pi before_pis after_pi after_pis
           w ws rows semantic_rows expected,
      schedule_matches_with_symmetric_trailing_zero_padding
        rows
        (select_by_mask mask
           (phase_semantic_padded_source_schedule
              env_size (List.length mask) before_pi)) ->
      phase_semantic_ordinary_target_schedule
        env_size mask before_pi w = Some expected ->
      schedule_matches_with_symmetric_trailing_zero_padding
        expected (Tiling.PL.pi_schedule after_pi) ->
      phase_semantic_ordinary_schedules_match
        env_size mask before_pis after_pis ws semantic_rows ->
      phase_semantic_ordinary_schedules_match
        env_size mask
        (before_pi :: before_pis) (after_pi :: after_pis)
        (w :: ws) (rows :: semantic_rows).

Inductive phase_semantic_second_level_schedules_match
    (env_size: nat)
    (mask: list bool)
    : list Tiling.PL.PolyInstr ->
      list Tiling.PL.PolyInstr ->
      list statement_tiling_witness ->
      list second_level_band_recipe ->
      list Schedule -> Prop :=
| PhaseSemanticSecondSchedulesMatchNil :
    phase_semantic_second_level_schedules_match
      env_size mask [] [] [] [] []
| PhaseSemanticSecondSchedulesMatchCons :
    forall before_pi before_pis after_pi after_pis
           w ws recipe recipes rows semantic_rows expected,
      schedule_matches_with_symmetric_trailing_zero_padding
        rows
        (select_by_mask mask
           (phase_semantic_padded_source_schedule
              env_size (List.length mask) before_pi)) ->
      phase_semantic_second_level_target_schedule
        env_size mask before_pi w recipe = Some expected ->
      schedule_matches_with_symmetric_trailing_zero_padding
        expected (Tiling.PL.pi_schedule after_pi) ->
      phase_semantic_second_level_schedules_match
        env_size mask before_pis after_pis ws recipes semantic_rows ->
      phase_semantic_second_level_schedules_match
        env_size mask
        (before_pi :: before_pis) (after_pi :: after_pis)
        (w :: ws) (recipe :: recipes) (rows :: semantic_rows).

Inductive phase_semantic_second_level_sources_match
    (env_size: nat)
    (mask: list bool)
    : list Tiling.PL.PolyInstr ->
      list statement_tiling_witness ->
      list second_level_band_recipe ->
      list Schedule -> Prop :=
| PhaseSemanticSecondSourcesMatchNil :
    phase_semantic_second_level_sources_match
      env_size mask [] [] [] []
| PhaseSemanticSecondSourcesMatchCons :
    forall before_pi before_pis w ws recipe recipes rows semantic_rows,
      schedule_matches_with_symmetric_trailing_zero_padding
        rows
        (select_by_mask mask
           (phase_semantic_padded_source_schedule
              env_size (List.length mask) before_pi)) ->
      phase_semantic_second_level_sources_match
        env_size mask before_pis ws recipes semantic_rows ->
      phase_semantic_second_level_sources_match
        env_size mask
        (before_pi :: before_pis) (w :: ws)
        (recipe :: recipes) (rows :: semantic_rows).

Definition phase_semantic_second_level_schedules_equivalent
    (env_size: nat)
    (mask: list bool)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (recipes: list second_level_band_recipe)
    (semantic_rows: list Schedule) : Prop :=
  phase_semantic_second_level_schedules_match
    env_size mask before_pis after_pis ws recipes semantic_rows \/
  phase_semantic_second_level_sources_match
    env_size mask before_pis ws recipes semantic_rows /\
  exists expected,
    phase_semantic_second_level_expected_schedules
      env_size mask before_pis ws recipes = Some expected /\
    schedule_lists_zero_erasure_match
      expected (List.map Tiling.PL.pi_schedule after_pis).

Lemma check_phase_semantic_ordinary_schedulesb_sound :
  forall env_size mask before_pis after_pis ws semantic_rows,
    check_phase_semantic_ordinary_schedulesb
      env_size mask before_pis after_pis ws semantic_rows = true ->
    phase_semantic_ordinary_schedules_match
      env_size mask before_pis after_pis ws semantic_rows.
Proof.
  intros env_size mask before_pis.
  induction before_pis as [|before_pi before_pis IH];
    intros after_pis ws semantic_rows Hcheck;
    destruct after_pis as [|after_pi after_pis];
    destruct ws as [|w ws];
    destruct semantic_rows as [|rows semantic_rows];
    simpl in Hcheck; try discriminate.
  - constructor.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hsource Hrest].
    destruct
      (phase_semantic_ordinary_target_schedule
         env_size mask before_pi w)
      as [expected|] eqn:Hexpected; try discriminate.
    apply andb_true_iff in Hrest.
    destruct Hrest as [Htarget Htail].
    econstructor.
    + eapply
        check_schedule_with_symmetric_trailing_zero_paddingb_sound.
      exact Hsource.
    + exact Hexpected.
    + eapply
        check_schedule_with_symmetric_trailing_zero_paddingb_sound.
      exact Htarget.
    + eapply IH.
      exact Htail.
Qed.

Lemma check_phase_semantic_second_level_schedules_symmetricb_sound :
  forall env_size mask before_pis after_pis ws recipes semantic_rows,
    check_phase_semantic_second_level_schedules_symmetricb
      env_size mask before_pis after_pis ws recipes semantic_rows = true ->
    phase_semantic_second_level_schedules_match
      env_size mask before_pis after_pis ws recipes semantic_rows.
Proof.
  intros env_size mask before_pis.
  induction before_pis as [|before_pi before_pis IH];
    intros after_pis ws recipes semantic_rows Hcheck;
    destruct after_pis as [|after_pi after_pis];
    destruct ws as [|w ws];
    destruct recipes as [|recipe recipes];
    destruct semantic_rows as [|rows semantic_rows];
    simpl in Hcheck; try discriminate.
  - constructor.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hsource Hrest].
    destruct
      (phase_semantic_second_level_target_schedule
         env_size mask before_pi w recipe)
      as [expected|] eqn:Hexpected; try discriminate.
    apply andb_true_iff in Hrest.
    destruct Hrest as [Htarget Htail].
    econstructor.
    + eapply
        check_schedule_with_symmetric_trailing_zero_paddingb_sound.
      exact Hsource.
    + exact Hexpected.
    + eapply
        check_schedule_with_symmetric_trailing_zero_paddingb_sound.
      exact Htarget.
    + eapply IH.
      exact Htail.
Qed.

Lemma check_phase_semantic_second_level_sourcesb_sound :
  forall env_size mask before_pis ws recipes semantic_rows,
    check_phase_semantic_second_level_sourcesb
      env_size mask before_pis ws recipes semantic_rows = true ->
    phase_semantic_second_level_sources_match
      env_size mask before_pis ws recipes semantic_rows.
Proof.
  intros env_size mask before_pis.
  induction before_pis as [|before_pi before_pis IH];
    intros ws recipes semantic_rows Hcheck;
    destruct ws as [|w ws];
    destruct recipes as [|recipe recipes];
    destruct semantic_rows as [|rows semantic_rows];
    simpl in Hcheck; try discriminate.
  - constructor.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hsource Htail].
    econstructor.
    + eapply
        check_schedule_with_symmetric_trailing_zero_paddingb_sound.
      exact Hsource.
    + eapply IH.
      exact Htail.
Qed.

Lemma check_phase_semantic_second_level_schedulesb_sound :
  forall env_size mask before_pis after_pis ws recipes semantic_rows,
    check_phase_semantic_second_level_schedulesb
      env_size mask before_pis after_pis ws recipes semantic_rows = true ->
    phase_semantic_second_level_schedules_equivalent
      env_size mask before_pis after_pis ws recipes semantic_rows.
Proof.
  intros env_size mask before_pis after_pis ws recipes semantic_rows Hcheck.
  unfold check_phase_semantic_second_level_schedulesb in Hcheck.
  apply orb_true_iff in Hcheck.
  destruct Hcheck as [Hsymmetric | Herasure].
  - left.
    eapply check_phase_semantic_second_level_schedules_symmetricb_sound.
    exact Hsymmetric.
  - right.
    unfold
      check_phase_semantic_second_level_schedules_zero_erasureb
      in Herasure.
    apply andb_true_iff in Herasure.
    destruct Herasure as [Hsource Htarget].
    split.
    + eapply check_phase_semantic_second_level_sourcesb_sound.
      exact Hsource.
    + destruct
        (phase_semantic_second_level_expected_schedules
           env_size mask before_pis ws recipes)
        as [expected|] eqn:Hexpected; try discriminate.
	      exists expected.
	      split.
	      * reflexivity.
	      * eapply check_schedule_lists_zero_erasure_same_masksb_sound.
	        exact Htarget.
Qed.

Definition phase_semantic_ordinary_band_shape_property
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness)
    (shape: phase_semantic_ordinary_band_shape) : Prop :=
  let '(before_pis, before_ctxt, before_vars) := before in
  let '(after_pis, after_ctxt, after_vars) := after in
  before_ctxt = after_ctxt /\
  before_vars = after_vars /\
  exists data,
    parse_ordinary_semantic_data ws = Some data /\
    infer_global_prefix_sizes (List.map snd data) =
      Some (psobs_global_sizes shape) /\
    psobs_rows shape = List.map fst data /\
    psobs_loop_mask shape =
      global_phase_semantic_loop_mask
        (List.length before_ctxt) before_pis /\
    phase_semantic_full_schedules_for_tiling
      (List.length before_ctxt) (psobs_loop_mask shape)
      before_pis ws =
      Some (psobs_full_rows shape) /\
    (O <
       List.length
         (global_semantic_schedule_mask (List.map fst data)))%nat /\
    List.length (psobs_global_sizes shape) =
      count_true (psobs_loop_mask shape) /\
    phase_semantic_has_scalarb (psobs_loop_mask shape) = true /\
    phase_semantic_ordinary_schedules_match
      (List.length before_ctxt) (psobs_loop_mask shape)
      before_pis after_pis ws (psobs_rows shape).

Definition phase_semantic_second_level_band_shape_property
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness)
    (shape: phase_semantic_second_level_band_shape) : Prop :=
  let '(before_pis, before_ctxt, before_vars) := before in
  let '(after_pis, after_ctxt, after_vars) := after in
  before_ctxt = after_ctxt /\
  before_vars = after_vars /\
  parse_second_level_semantic_recipes ws =
    Some (pssbs_recipes shape) /\
  infer_global_prefix_sizes
    (List.map slbr_root_sizes (pssbs_recipes shape)) =
    Some (pssbs_global_root_sizes shape) /\
  infer_global_prefix_sizes
    (List.map slbr_child_sizes (pssbs_recipes shape)) =
    Some (pssbs_global_child_sizes shape) /\
  pssbs_rows shape =
    List.map slbr_root_rows (pssbs_recipes shape) /\
  pssbs_loop_mask shape =
    global_phase_semantic_loop_mask
      (List.length before_ctxt) before_pis /\
  phase_semantic_full_schedules_for_tiling
    (List.length before_ctxt) (pssbs_loop_mask shape)
    before_pis ws =
    Some (pssbs_full_rows shape) /\
  (O <
     List.length
       (global_semantic_schedule_mask
          (List.map slbr_root_rows (pssbs_recipes shape))))%nat /\
  List.length (pssbs_global_root_sizes shape) =
    count_true (pssbs_loop_mask shape) /\
  List.length (pssbs_global_child_sizes shape) =
    count_true (pssbs_loop_mask shape) /\
  phase_semantic_has_scalarb (pssbs_loop_mask shape) = true /\
  phase_semantic_second_level_schedules_equivalent
    (List.length before_ctxt) (pssbs_loop_mask shape)
    before_pis after_pis ws (pssbs_recipes shape)
    (pssbs_rows shape).

Lemma infer_pprog_phase_semantic_ordinary_band_shape_sound :
  forall before after ws shape,
    infer_pprog_phase_semantic_ordinary_band_shape
      before after ws = Some shape ->
    phase_semantic_ordinary_band_shape_property
      before after ws shape.
Proof.
  intros [[before_pis before_ctxt] before_vars]
         [[after_pis after_ctxt] after_vars] ws shape Hinfer.
  unfold infer_pprog_phase_semantic_ordinary_band_shape in Hinfer.
  cbn beta iota zeta in Hinfer.
  destruct (TilingCheck.ctxt_eqb before_ctxt after_ctxt)
    eqn:Hctxt; try discriminate.
  destruct (TilingCheck.ctxt_ty_eqb before_vars after_vars)
    eqn:Hvars; try discriminate.
  destruct (parse_ordinary_semantic_data ws)
    as [data|] eqn:Hdata; try discriminate.
  set (raw := List.map fst data) in *.
  set (semantic_mask := global_semantic_schedule_mask raw) in *.
  set
    (loop_mask :=
       global_phase_semantic_loop_mask
         (List.length before_ctxt) before_pis)
    in *.
  destruct (infer_global_prefix_sizes (List.map snd data))
    as [global_sizes|] eqn:Hsizes; try discriminate.
  destruct
    (compact_semantic_schedules
       (List.length before_ctxt) before_pis raw semantic_mask)
    as [semantic_rows|] eqn:Hrows; try discriminate.
  destruct
    (phase_semantic_full_schedules_for_tiling
       (List.length before_ctxt) loop_mask before_pis ws)
    as [full_rows|] eqn:Hfull; try discriminate.
  destruct
    (Nat.ltb O (List.length semantic_mask) &&
     Nat.eqb (List.length global_sizes) (count_true loop_mask) &&
     phase_semantic_has_scalarb loop_mask &&
     check_phase_semantic_ordinary_schedulesb
       (List.length before_ctxt) loop_mask
       before_pis after_pis ws raw)
    eqn:Hchecks; try discriminate.
  inversion Hinfer; subst shape; clear Hinfer.
  repeat rewrite andb_true_iff in Hchecks.
  destruct Hchecks as [[[Hpositive Hwidth] Hscalar] Hschedule].
  unfold phase_semantic_ordinary_band_shape_property.
  cbn.
  repeat split.
  - apply TilingCheck.ctxt_eqb_eq. exact Hctxt.
  - apply TilingCheck.ctxt_ty_eqb_eq. exact Hvars.
  - exists data.
    repeat split.
    + exact Hdata.
    + exact Hsizes.
    + exact Hfull.
    + apply Nat.ltb_lt.
      unfold semantic_mask in Hpositive.
      exact Hpositive.
    + apply Nat.eqb_eq.
      exact Hwidth.
    + exact Hscalar.
    + eapply check_phase_semantic_ordinary_schedulesb_sound.
      exact Hschedule.
Qed.

Lemma infer_pprog_phase_semantic_second_level_band_shape_sound :
  forall before after ws shape,
    infer_pprog_phase_semantic_second_level_band_shape
      before after ws = Some shape ->
    phase_semantic_second_level_band_shape_property
      before after ws shape.
Proof.
  intros [[before_pis before_ctxt] before_vars]
         [[after_pis after_ctxt] after_vars] ws shape Hinfer.
  unfold infer_pprog_phase_semantic_second_level_band_shape in Hinfer.
  cbn beta iota zeta in Hinfer.
  destruct (TilingCheck.ctxt_eqb before_ctxt after_ctxt)
    eqn:Hctxt; try discriminate.
  destruct (TilingCheck.ctxt_ty_eqb before_vars after_vars)
    eqn:Hvars; try discriminate.
  destruct (parse_second_level_semantic_recipes ws)
    as [recipes|] eqn:Hrecipes; try discriminate.
  set (raw := List.map slbr_root_rows recipes) in *.
  set (semantic_mask := global_semantic_schedule_mask raw) in *.
  set
    (loop_mask :=
       global_phase_semantic_loop_mask
         (List.length before_ctxt) before_pis)
    in *.
  destruct (infer_global_prefix_sizes (List.map slbr_root_sizes recipes))
    as [root_sizes|] eqn:Hroot_sizes; try discriminate.
  destruct (infer_global_prefix_sizes (List.map slbr_child_sizes recipes))
    as [child_sizes|] eqn:Hchild_sizes; try discriminate.
  destruct
    (compact_semantic_schedules
       (List.length before_ctxt) before_pis raw semantic_mask)
    as [semantic_rows|] eqn:Hrows; try discriminate.
  destruct
    (phase_semantic_full_schedules_for_tiling
       (List.length before_ctxt) loop_mask before_pis ws)
    as [full_rows|] eqn:Hfull; try discriminate.
  destruct
    (Nat.ltb O (List.length semantic_mask) &&
     Nat.eqb (List.length root_sizes) (count_true loop_mask) &&
     Nat.eqb (List.length child_sizes) (count_true loop_mask) &&
     phase_semantic_has_scalarb loop_mask &&
     check_phase_semantic_second_level_schedulesb
       (List.length before_ctxt) loop_mask
       before_pis after_pis ws recipes raw)
    eqn:Hchecks; try discriminate.
  inversion Hinfer; subst shape; clear Hinfer.
  repeat rewrite andb_true_iff in Hchecks.
  destruct Hchecks as
    [[[[Hpositive Hroot_width] Hchild_width] Hscalar] Hschedule].
  unfold phase_semantic_second_level_band_shape_property.
  cbn.
  repeat split.
  - apply TilingCheck.ctxt_eqb_eq. exact Hctxt.
  - apply TilingCheck.ctxt_ty_eqb_eq. exact Hvars.
  - exact Hrecipes.
  - exact Hroot_sizes.
  - exact Hchild_sizes.
  - exact Hfull.
  - apply Nat.ltb_lt.
    unfold semantic_mask in Hpositive.
    exact Hpositive.
  - apply Nat.eqb_eq. exact Hroot_width.
  - apply Nat.eqb_eq. exact Hchild_width.
  - exact Hscalar.
  - eapply check_phase_semantic_second_level_schedulesb_sound.
    exact Hschedule.
Qed.

Lemma phase_semantic_lifted_band_rows_exact_cols :
  forall env vars added_dims mask before_pi,
    Tiling.PL.wf_pinstr_tiling env vars before_pi ->
    exact_listzzs_cols
      (List.length env + added_dims + Tiling.PL.pi_depth before_pi)%nat
      (phase_semantic_lifted_band_rows
         (List.length env) added_dims mask before_pi).
Proof.
  intros env vars added_dims mask before_pi Hwf.
  unfold phase_semantic_lifted_band_rows,
         phase_semantic_padded_source_schedule.
  replace
    (List.length env + added_dims + Tiling.PL.pi_depth before_pi)%nat
    with
    (added_dims +
     (List.length env + Tiling.PL.pi_depth before_pi))%nat
    by lia.
  eapply lift_schedule_after_env_exact_cols.
  - eapply exact_listzzs_cols_pad_schedule_to_len.
    eapply wf_pinstr_tiling_schedule_exact_cols_local.
    exact Hwf.
  - lia.
Qed.

Lemma phase_semantic_full_schedules_for_tiling_exact_cols :
  forall env vars before_pis ws mask full_rows,
    phase_semantic_full_schedules_for_tiling
      (List.length env) mask before_pis ws = Some full_rows ->
    Forall
      (Tiling.PL.wf_pinstr_tiling env vars)
      before_pis ->
    Forall2
      (fun before_pi w =>
         stw_point_dim w = Tiling.PL.pi_depth before_pi)
      before_pis ws ->
    Forall2
      (fun w rows =>
         exact_listzzs_cols
           (List.length env + List.length (stw_links w) +
            stw_point_dim w)%nat
           rows)
      ws full_rows.
Proof.
  intros env vars before_pis.
  induction before_pis as [|before_pi before_pis IH];
    intros ws mask full_rows Hfull Hwf Hdepths.
  - destruct ws as [|w ws]; simpl in Hfull; try discriminate.
    inversion Hfull; constructor.
  - destruct ws as [|w ws]; simpl in Hfull; try discriminate.
    inversion Hwf as
      [|before_pi0 before_pis0 Hwf_head Hwf_tail];
      subst before_pi0 before_pis0.
    inversion Hdepths as
      [|before_pi0 w0 before_pis0 ws0 Hdepth Hdepths_tail];
      subst before_pi0 w0 before_pis0 ws0.
    destruct
      (phase_semantic_full_schedules_for_tiling
         (List.length env) mask before_pis ws)
      as [rest|] eqn:Hrest; try discriminate.
    inversion Hfull; subst full_rows.
    constructor.
    + rewrite Hdepth.
      eapply phase_semantic_lifted_band_rows_exact_cols.
      exact Hwf_head.
    + exact (IH ws mask rest Hrest Hwf_tail Hdepths_tail).
Qed.


Lemma is_eq_zero_extend_right :
  forall xs ys,
    (List.length xs <= List.length ys)%nat ->
    is_eq xs ys = true ->
    ys =
      xs ++ repeat 0%Z (List.length ys - List.length xs).
Proof.
  induction xs as [|x xs IH]; intros ys Hlen Heq.
  - destruct ys as [|y ys]; [reflexivity|].
    simpl in Heq.
    simpl.
    pose proof
      (resize_null_repeat
         (List.length (y :: ys)) (y :: ys) Heq) as Hzero.
    rewrite resize_length_eq in Hzero by reflexivity.
    exact Hzero.
  - destruct ys as [|y ys]; simpl in Hlen; try lia.
    simpl in Heq.
    apply andb_true_iff in Heq.
    destruct Heq as [Hxy Htail].
    apply Z.eqb_eq in Hxy.
    subst y.
    simpl.
    f_equal.
    eapply IH; eauto; lia.
Qed.

Lemma select_by_mask_length_count_true :
  forall (A: Type) mask (xs: list A),
    List.length xs = List.length mask ->
    List.length (select_by_mask mask xs) = count_true mask.
Proof.
  intros A mask.
  induction mask as [|keep mask IH]; intros xs Hlen;
    destruct xs as [|x xs]; simpl in *; try discriminate.
  - reflexivity.
  - destruct keep; simpl; rewrite IH by lia; reflexivity.
Qed.

Lemma render_scalar_aware_value_prefix_pointwise_le :
  forall mask band1 band2 tiles1 tiles2,
    scalar_aware_loop_tiles_monotone
      mask band1 band2 tiles1 tiles2 ->
    listz_pointwise_le band1 band2 ->
    forall mixed1 mixed2,
      render_scalar_aware_value_prefix
        mask band1 tiles1 = Some mixed1 ->
      render_scalar_aware_value_prefix
        mask band2 tiles2 = Some mixed2 ->
      listz_pointwise_le mixed1 mixed2.
Proof.
  intros mask band1 band2 tiles1 tiles2 Hmonotone Hband.
  induction Hmonotone as
    [|mask band1 band2 tiles1 tiles2 b1 b2 t1 t2
       Htile Hmonotone IH
     |mask band1 band2 tiles1 tiles2 b1 b2
       Hmonotone IH];
    intros mixed1 mixed2 Hrender1 Hrender2;
    inversion Hband; subst.
  - simpl in Hrender1, Hrender2.
    inversion Hrender1; inversion Hrender2; constructor.
  - simpl in Hrender1, Hrender2.
    destruct
      (render_scalar_aware_value_prefix mask band1 tiles1)
      as [tail1|] eqn:Htail1; try discriminate.
    destruct
      (render_scalar_aware_value_prefix mask band2 tiles2)
      as [tail2|] eqn:Htail2; try discriminate.
    inversion Hrender1; inversion Hrender2; subst.
    constructor.
    + apply Htile.
      assumption.
    + eapply IH; eauto.
  - simpl in Hrender1, Hrender2.
    destruct
      (render_scalar_aware_value_prefix mask band1 tiles1)
      as [tail1|] eqn:Htail1; try discriminate.
    destruct
      (render_scalar_aware_value_prefix mask band2 tiles2)
      as [tail2|] eqn:Htail2; try discriminate.
    inversion Hrender1; inversion Hrender2; subst.
    constructor.
    + assumption.
    + eapply IH; eauto.
Qed.

Lemma phase_semantic_added_tiles_eq :
  forall env_size mask before_pi w raw global_sizes
         envv point added,
    List.length envv = env_size ->
    List.length point = stw_point_dim w ->
    schedule_rows_of_links w = Some raw ->
    prefix_sizes (tile_sizes_of_witness w) global_sizes ->
    List.length global_sizes = count_true mask ->
    (List.length (Tiling.PL.pi_schedule before_pi) <=
     List.length mask)%nat ->
    well_formed_statement_tiling_witness w ->
    Forall
      (fun link =>
         List.length (ae_param_coeffs (tl_expr link)) =
         List.length envv)
      (stw_links w) ->
    schedule_matches_with_symmetric_trailing_zero_padding
      raw
      (select_by_mask mask
         (phase_semantic_padded_source_schedule
            env_size (List.length mask) before_pi)) ->
    added = eval_tile_links [] point envv (stw_links w) ->
    added ++
    repeat 0%Z
      (count_true mask - List.length (stw_links w)) =
    scalar_aware_loop_tile_values
      mask
      (affine_product
         (phase_semantic_padded_source_schedule
            env_size (List.length mask) before_pi)
         (envv ++ point))
      global_sizes.
Proof.
  intros env_size mask before_pi w raw global_sizes
         envv point added Henv Hpoint Hraw Hprefix Hglobal_len
         Hbefore_bound Hwf Hparams Hmatch Hadded.
  set
    (band_values :=
       affine_product
         (phase_semantic_padded_source_schedule
            env_size (List.length mask) before_pi)
         (envv ++ point)).
  set (loop_values := select_by_mask mask band_values).
  assert
    (Hband_len : List.length band_values = List.length mask).
  {
    subst band_values.
    unfold affine_product,
           phase_semantic_padded_source_schedule,
           Tiling.PL.pad_schedule_to_len.
    rewrite List.map_length, app_length, repeat_length.
    lia.
  }
  assert
    (Hloop_len : List.length loop_values = count_true mask).
  {
    subst loop_values.
    eapply select_by_mask_length_count_true.
    exact Hband_len.
  }
  set (raw_values := affine_product raw (envv ++ point)).
  assert
    (Hraw_len :
       List.length raw_values = List.length (stw_links w)).
  {
    subst raw_values.
    unfold affine_product.
    rewrite List.map_length.
    eapply schedule_rows_of_links_length.
    exact Hraw.
  }
  assert
    (Hsource_eq : is_eq raw_values loop_values = true).
  {
    subst raw_values loop_values band_values.
    pose proof
      (schedule_matches_with_symmetric_trailing_zero_padding_affine_product_is_eq
         raw
         (select_by_mask mask
            (phase_semantic_padded_source_schedule
               env_size (List.length mask) before_pi))
         (envv ++ point) Hmatch)
      as Heq.
    rewrite affine_product_select_by_mask in Heq.
    rewrite is_eq_commutative.
    exact Heq.
  }
  assert
    (Hlocal_len :
       List.length (tile_sizes_of_witness w) =
       List.length (stw_links w)).
  {
    unfold tile_sizes_of_witness.
    rewrite List.map_length.
    reflexivity.
  }
  assert
    (Hraw_le_loop :
       (List.length raw_values <= List.length loop_values)%nat).
  {
    rewrite Hraw_len, Hloop_len, <- Hglobal_len, <- Hlocal_len.
    exact (proj1 Hprefix).
  }
  assert
    (Hloop_values :
       loop_values =
       raw_values ++
       repeat 0%Z
         (List.length loop_values - List.length raw_values)).
  {
    eapply is_eq_zero_extend_right; eauto.
  }
  rewrite Hloop_len, Hraw_len in Hloop_values.
  unfold scalar_aware_loop_tile_values.
  fold band_values loop_values.
  rewrite Hloop_values.
  pose proof
    (tile_values_pad_prefix
       raw_values (tile_sizes_of_witness w) global_sizes)
    as Hpad.
  assert
    (Hraw_sizes :
       List.length raw_values =
       List.length (tile_sizes_of_witness w)).
  {
    rewrite Hraw_len, Hlocal_len.
    reflexivity.
  }
  specialize (Hpad Hraw_sizes Hprefix).
  rewrite Hglobal_len, Hraw_len in Hpad.
  rewrite Hpad.
  rewrite Hadded.
  rewrite
    (eval_tile_links_from_schedule_rows
       w point envv raw (tile_sizes_of_witness w)
       Hpoint Hraw eq_refl Hwf Hparams).
  rewrite Hlocal_len.
  reflexivity.
Qed.

Lemma phase_semantic_padded_identity_rows_from_eval :
  forall total_cols env_size local_width global_width envv added point,
    List.length envv = env_size ->
    List.length added = local_width ->
    List.length (envv ++ added ++ point) = total_cols ->
    (local_width <= global_width)%nat ->
    affine_product
      (phase_semantic_padded_identity_rows_from
         total_cols env_size local_width global_width)
      (envv ++ added ++ point) =
    added ++ repeat 0%Z (global_width - local_width).
Proof.
  intros total_cols env_size local_width global_width
         envv added point Henv Hadded Htotal Hwidth.
  unfold phase_semantic_padded_identity_rows_from.
  rewrite affine_product_app.
  rewrite affine_product_identity_affine_rows_from.
  2:{
    rewrite <- Htotal, !app_length, Henv, Hadded.
    lia.
  }
  2:{
    rewrite !app_length, Henv, Hadded.
    lia.
  }
  rewrite affine_product_zero_schedule_rows.
  rewrite <- Henv.
  replace
    (skipn (List.length envv) (envv ++ added ++ point))
    with (added ++ point).
  2:{
    rewrite skipn_app_le by lia.
    replace (List.length envv - List.length envv)%nat with O by lia.
    reflexivity.
  }
  rewrite firstn_app.
  replace (local_width - List.length added)%nat with O by lia.
  rewrite <- Hadded, firstn_all.
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma phase_semantic_ordinary_target_schedule_eval :
  forall env_size mask before_pi w expected envv added point,
    phase_semantic_ordinary_target_schedule
      env_size mask before_pi w = Some expected ->
    List.length envv = env_size ->
    List.length added = List.length (stw_links w) ->
    List.length point = stw_point_dim w ->
    (List.length (stw_links w) <= count_true mask)%nat ->
    exists band_values mixed_values,
      band_values =
        affine_product
          (phase_semantic_padded_source_schedule
             env_size (List.length mask) before_pi)
          (envv ++ point) /\
      render_scalar_aware_value_prefix
        mask band_values
        (added ++
         repeat 0%Z
           (count_true mask - List.length (stw_links w))) =
        Some mixed_values /\
      affine_product expected (envv ++ added ++ point) =
        mixed_values ++ band_values.
Proof.
  intros env_size mask before_pi w expected envv added point
         Hexpected Henv Hadded Hpoint Hwidth.
  unfold phase_semantic_ordinary_target_schedule in Hexpected.
  set (local_width := List.length (stw_links w)) in *.
  set (global_width := count_true mask) in *.
  set (total_cols :=
    (env_size + local_width + stw_point_dim w)%nat) in *.
  set
    (band_rows :=
       phase_semantic_lifted_band_rows
         env_size local_width mask before_pi)
    in *.
  set
    (tile_rows :=
       phase_semantic_padded_identity_rows_from
         total_cols env_size local_width global_width)
    in *.
  destruct
    (render_scalar_aware_tile_prefix mask band_rows tile_rows)
    as [tile_stage|] eqn:Hrender; try discriminate.
  inversion Hexpected; subst expected; clear Hexpected.
  set
    (band_values :=
       affine_product
         (phase_semantic_padded_source_schedule
            env_size (List.length mask) before_pi)
         (envv ++ point)).
  assert
    (Hband_eval :
       affine_product band_rows (envv ++ added ++ point) =
       band_values).
  {
    subst band_rows band_values.
    unfold phase_semantic_lifted_band_rows.
    eapply Tiling.lift_affine_function_after_env_eval.
    - exact Henv.
    - subst local_width. exact Hadded.
  }
  assert
    (Htile_eval :
       affine_product tile_rows (envv ++ added ++ point) =
       added ++ repeat 0%Z (global_width - local_width)).
  {
    subst tile_rows total_cols.
    eapply phase_semantic_padded_identity_rows_from_eval.
    - exact Henv.
    - subst local_width. exact Hadded.
    - rewrite !app_length, Henv, Hadded, Hpoint.
      lia.
    - exact Hwidth.
  }
  pose proof
    (affine_product_render_scalar_aware_tile_prefix
       mask band_rows tile_rows tile_stage
       (envv ++ added ++ point) Hrender)
    as Hrender_eval.
  rewrite Hband_eval, Htile_eval in Hrender_eval.
  exists band_values, (affine_product tile_stage
    (envv ++ added ++ point)).
  repeat split.
  - exact Hrender_eval.
  - rewrite affine_product_app, Hband_eval.
    reflexivity.
Qed.

Lemma phase_semantic_padded_identity_rows_at_eval :
  forall total_cols env_size global_width positions envv added point,
    List.length envv = env_size ->
    List.length (envv ++ added ++ point) = total_cols ->
    Forall (fun pos => (pos < List.length added)%nat) positions ->
    (List.length positions <= global_width)%nat ->
    affine_product
      (phase_semantic_padded_identity_rows_at
         total_cols env_size global_width positions)
      (envv ++ added ++ point) =
    List.map (fun pos => nth pos added 0%Z) positions ++
    repeat 0%Z (global_width - List.length positions).
Proof.
  intros total_cols env_size global_width positions
         envv added point Henv Htotal Hpositions Hwidth.
  unfold phase_semantic_padded_identity_rows_at.
  rewrite affine_product_app.
  rewrite affine_product_identity_affine_rows_at.
  2:{
    apply Forall_forall.
    intros pos Hin.
    assert (Hpos : (pos < List.length added)%nat).
    { eapply Forall_forall in Hpositions; eauto. }
    rewrite <- Htotal, !app_length, Henv.
    lia.
  }
  assert
    (Hprojection :
       List.map
         (fun pos =>
            nth (env_size + pos)%nat
              (envv ++ added ++ point) 0%Z)
         positions =
       List.map (fun pos => nth pos added 0%Z) positions).
  {
    apply List.map_ext_in.
    intros pos Hin.
    eapply nth_env_added_app.
    - exact Henv.
    - eapply Forall_forall in Hpositions; eauto.
  }
  rewrite Hprojection.
  rewrite affine_product_zero_schedule_rows.
  reflexivity.
Qed.

Lemma second_level_root_positions_length_local :
  forall count,
    List.length (second_level_root_positions count) = count.
Proof.
  induction count as [|count IH]; simpl.
  - reflexivity.
  - rewrite List.map_length, IH.
    reflexivity.
Qed.

Lemma second_level_child_positions_length_local :
  forall count,
    List.length (second_level_child_positions count) = count.
Proof.
  intros count.
  unfold second_level_child_positions.
  rewrite List.map_length.
  apply second_level_root_positions_length_local.
Qed.

Lemma phase_semantic_second_level_target_schedule_eval :
  forall env_size mask before_pi w recipe expected envv added point,
    phase_semantic_second_level_target_schedule
      env_size mask before_pi w recipe = Some expected ->
    List.length envv = env_size ->
    List.length added =
      (2 * List.length (slbr_root_rows recipe))%nat ->
    List.length point = stw_point_dim w ->
    (List.length (slbr_root_rows recipe) <= count_true mask)%nat ->
    exists band_values child_values root_values,
      band_values =
        affine_product
          (phase_semantic_padded_source_schedule
             env_size (List.length mask) before_pi)
          (envv ++ point) /\
      render_scalar_aware_value_prefix
        mask band_values
        (List.map
           (fun pos => nth pos added 0%Z)
           (second_level_child_positions
              (List.length (slbr_root_rows recipe))) ++
         repeat 0%Z
           (count_true mask -
            List.length (slbr_root_rows recipe))) =
        Some child_values /\
      render_scalar_aware_value_prefix
        mask band_values
        (List.map
           (fun pos => nth pos added 0%Z)
           (second_level_root_positions
              (List.length (slbr_root_rows recipe))) ++
         repeat 0%Z
           (count_true mask -
            List.length (slbr_root_rows recipe))) =
        Some root_values /\
      affine_product expected (envv ++ added ++ point) =
        child_values ++ root_values ++ band_values.
Proof.
  intros env_size mask before_pi w recipe expected
         envv added point Hexpected Henv Hadded Hpoint Hwidth.
  unfold phase_semantic_second_level_target_schedule in Hexpected.
  set (local_width := List.length (slbr_root_rows recipe)) in *.
  set (global_width := count_true mask) in *.
  set (added_dims := (2 * local_width)%nat) in *.
  set (total_cols :=
    (env_size + added_dims + stw_point_dim w)%nat) in *.
  set
    (band_rows :=
       phase_semantic_lifted_band_rows
         env_size added_dims mask before_pi)
    in *.
  set
    (child_rows :=
       phase_semantic_padded_identity_rows_at
         total_cols env_size global_width
         (second_level_child_positions local_width))
    in *.
  set
    (root_rows :=
       phase_semantic_padded_identity_rows_at
         total_cols env_size global_width
         (second_level_root_positions local_width))
    in *.
  destruct
    (render_scalar_aware_tile_prefix mask band_rows child_rows)
    as [child_stage|] eqn:Hchild_render; try discriminate.
  destruct
    (render_scalar_aware_tile_prefix mask band_rows root_rows)
    as [root_stage|] eqn:Hroot_render; try discriminate.
  inversion Hexpected; subst expected; clear Hexpected.
  set
    (band_values :=
       affine_product
         (phase_semantic_padded_source_schedule
            env_size (List.length mask) before_pi)
         (envv ++ point)).
  assert
    (Hband_eval :
       affine_product band_rows (envv ++ added ++ point) =
       band_values).
  {
    subst band_rows band_values.
    unfold phase_semantic_lifted_band_rows.
    eapply Tiling.lift_affine_function_after_env_eval.
    - exact Henv.
    - subst added_dims local_width. exact Hadded.
  }
  assert
    (Hchild_eval :
       affine_product child_rows (envv ++ added ++ point) =
       List.map
         (fun pos => nth pos added 0%Z)
         (second_level_child_positions local_width) ++
       repeat 0%Z (global_width - local_width)).
  {
    subst child_rows total_cols.
    assert
      (Htotal :
         List.length (envv ++ added ++ point) =
         (env_size + added_dims + stw_point_dim w)%nat).
    {
      rewrite !app_length, Henv, Hadded, Hpoint.
      lia.
    }
    assert
      (Hpositions :
         Forall
           (fun pos => (pos < List.length added)%nat)
           (second_level_child_positions local_width)).
    {
      apply Forall_forall.
      intros pos Hin.
      pose proof
        (second_level_child_positions_bound local_width pos Hin).
      rewrite Hadded.
      subst added_dims.
      lia.
    }
    assert
      (Hpositions_width :
         (List.length (second_level_child_positions local_width) <=
          global_width)%nat).
    {
      rewrite second_level_child_positions_length_local.
      exact Hwidth.
    }
    pose proof
      (phase_semantic_padded_identity_rows_at_eval
         (env_size + added_dims + stw_point_dim w)%nat
         env_size global_width
         (second_level_child_positions local_width)
         envv added point Henv Htotal Hpositions Hpositions_width)
      as Heval.
    rewrite second_level_child_positions_length_local in Heval.
    exact Heval.
  }
  assert
    (Hroot_eval :
       affine_product root_rows (envv ++ added ++ point) =
       List.map
         (fun pos => nth pos added 0%Z)
         (second_level_root_positions local_width) ++
       repeat 0%Z (global_width - local_width)).
  {
    subst root_rows total_cols.
    assert
      (Htotal :
         List.length (envv ++ added ++ point) =
         (env_size + added_dims + stw_point_dim w)%nat).
    {
      rewrite !app_length, Henv, Hadded, Hpoint.
      lia.
    }
    assert
      (Hpositions :
         Forall
           (fun pos => (pos < List.length added)%nat)
           (second_level_root_positions local_width)).
    {
      apply Forall_forall.
      intros pos Hin.
      pose proof
        (second_level_root_positions_bound local_width pos Hin).
      rewrite Hadded.
      subst added_dims.
      lia.
    }
    assert
      (Hpositions_width :
         (List.length (second_level_root_positions local_width) <=
          global_width)%nat).
    {
      rewrite second_level_root_positions_length_local.
      exact Hwidth.
    }
    pose proof
      (phase_semantic_padded_identity_rows_at_eval
         (env_size + added_dims + stw_point_dim w)%nat
         env_size global_width
         (second_level_root_positions local_width)
         envv added point Henv Htotal Hpositions Hpositions_width)
      as Heval.
    rewrite second_level_root_positions_length_local in Heval.
    exact Heval.
  }
  pose proof
    (affine_product_render_scalar_aware_tile_prefix
       mask band_rows child_rows child_stage
       (envv ++ added ++ point) Hchild_render)
    as Hchild_render_eval.
  pose proof
    (affine_product_render_scalar_aware_tile_prefix
       mask band_rows root_rows root_stage
       (envv ++ added ++ point) Hroot_render)
    as Hroot_render_eval.
  rewrite Hband_eval, Hchild_eval in Hchild_render_eval.
  rewrite Hband_eval, Hroot_eval in Hroot_render_eval.
  exists band_values,
    (affine_product child_stage (envv ++ added ++ point)),
    (affine_product root_stage (envv ++ added ++ point)).
  repeat split.
  - exact Hchild_render_eval.
  - exact Hroot_render_eval.
  - rewrite !affine_product_app, Hband_eval.
    reflexivity.
Qed.

Lemma phase_semantic_ordinary_schedules_match_nth_error :
  forall env_size mask before_pis after_pis ws semantic_rows
         n before_pi after_pi w rows,
    phase_semantic_ordinary_schedules_match
      env_size mask before_pis after_pis ws semantic_rows ->
    nth_error before_pis n = Some before_pi ->
    nth_error after_pis n = Some after_pi ->
    nth_error ws n = Some w ->
    nth_error semantic_rows n = Some rows ->
    schedule_matches_with_symmetric_trailing_zero_padding
      rows
      (select_by_mask mask
         (phase_semantic_padded_source_schedule
            env_size (List.length mask) before_pi)) /\
    exists expected,
      phase_semantic_ordinary_target_schedule
        env_size mask before_pi w = Some expected /\
      schedule_matches_with_symmetric_trailing_zero_padding
        expected (Tiling.PL.pi_schedule after_pi).
Proof.
  intros env_size mask before_pis after_pis ws semantic_rows n.
  revert before_pis after_pis ws semantic_rows.
  induction n as [|n IH];
    intros before_pis after_pis ws semantic_rows
           before_pi after_pi w rows
           Hmatch Hbefore Hafter Hw Hrows;
    inversion Hmatch; subst; simpl in *; try discriminate.
  - inversion Hbefore; inversion Hafter; inversion Hw; inversion Hrows;
      subst.
    split; [assumption|].
    eexists; eauto.
  - eapply IH; eauto.
Qed.

Lemma phase_semantic_second_schedules_match_nth_error :
  forall env_size mask before_pis after_pis ws recipes semantic_rows
         n before_pi after_pi w recipe rows,
    phase_semantic_second_level_schedules_match
      env_size mask before_pis after_pis ws recipes semantic_rows ->
    nth_error before_pis n = Some before_pi ->
    nth_error after_pis n = Some after_pi ->
    nth_error ws n = Some w ->
    nth_error recipes n = Some recipe ->
    nth_error semantic_rows n = Some rows ->
    schedule_matches_with_symmetric_trailing_zero_padding
      rows
      (select_by_mask mask
         (phase_semantic_padded_source_schedule
            env_size (List.length mask) before_pi)) /\
    exists expected,
      phase_semantic_second_level_target_schedule
        env_size mask before_pi w recipe = Some expected /\
      schedule_matches_with_symmetric_trailing_zero_padding
        expected (Tiling.PL.pi_schedule after_pi).
Proof.
  intros env_size mask before_pis after_pis ws recipes semantic_rows n.
  revert before_pis after_pis ws recipes semantic_rows.
  induction n as [|n IH];
    intros before_pis after_pis ws recipes semantic_rows
           before_pi after_pi w recipe rows
           Hmatch Hbefore Hafter Hw Hrecipe Hrows;
    inversion Hmatch; subst; simpl in *; try discriminate.
  - inversion Hbefore; inversion Hafter; inversion Hw;
      inversion Hrecipe; inversion Hrows; subst.
    split; [assumption|].
    eexists; eauto.
  - eapply IH; eauto.
Qed.

Lemma phase_semantic_second_sources_match_nth_error :
  forall env_size mask before_pis ws recipes semantic_rows
         n before_pi w recipe rows,
    phase_semantic_second_level_sources_match
      env_size mask before_pis ws recipes semantic_rows ->
    nth_error before_pis n = Some before_pi ->
    nth_error ws n = Some w ->
    nth_error recipes n = Some recipe ->
    nth_error semantic_rows n = Some rows ->
    schedule_matches_with_symmetric_trailing_zero_padding
      rows
      (select_by_mask mask
         (phase_semantic_padded_source_schedule
            env_size (List.length mask) before_pi)).
Proof.
  intros env_size mask before_pis ws recipes semantic_rows n.
  revert before_pis ws recipes semantic_rows.
  induction n as [|n IH];
    intros before_pis ws recipes semantic_rows before_pi w recipe rows
           Hmatch Hbefore Hw Hrecipe Hrows;
    inversion Hmatch; subst; simpl in *; try discriminate.
  - inversion Hbefore; inversion Hw; inversion Hrecipe; inversion Hrows;
      subst.
    assumption.
  - eapply IH; eauto.
Qed.

Lemma phase_semantic_second_level_expected_schedules_nth_error :
  forall env_size mask before_pis ws recipes expected
         n before_pi w recipe,
    phase_semantic_second_level_expected_schedules
      env_size mask before_pis ws recipes = Some expected ->
    nth_error before_pis n = Some before_pi ->
    nth_error ws n = Some w ->
    nth_error recipes n = Some recipe ->
    exists expected_i,
      phase_semantic_second_level_target_schedule
        env_size mask before_pi w recipe = Some expected_i /\
      nth_error expected n = Some expected_i.
Proof.
  intros env_size mask before_pis.
  induction before_pis as [|before0 before_pis IH].
  - intros ws recipes expected n before_pi w recipe
           Hexpected Hbefore Hw Hrecipe.
    destruct n; discriminate Hbefore.
  - intros ws recipes expected n before_pi w recipe
           Hexpected Hbefore Hw Hrecipe.
    destruct ws as [|w0 ws]; simpl in Hexpected; try discriminate.
    destruct recipes as [|recipe0 recipes]; simpl in Hexpected;
      try discriminate.
    destruct
      (phase_semantic_second_level_target_schedule
         env_size mask before0 w0 recipe0)
      as [expected0|] eqn:Hexpected0; try discriminate.
    destruct
      (phase_semantic_second_level_expected_schedules
         env_size mask before_pis ws recipes)
      as [rest|] eqn:Hrest; try discriminate.
    inversion Hexpected; subst expected; clear Hexpected.
    destruct n as [|n].
    + simpl in Hbefore, Hw, Hrecipe.
      inversion Hbefore; inversion Hw; inversion Hrecipe; subst.
      exists expected0.
      split; [exact Hexpected0|reflexivity].
    + simpl in Hbefore, Hw, Hrecipe.
      simpl.
      eapply (IH ws recipes rest n before_pi w recipe); eauto.
Qed.

Lemma phase_semantic_second_schedules_equivalent_pair_lex :
  forall env_size mask before_pis after_pis ws recipes semantic_rows
         i j
         before_i after_i w_i recipe_i rows_i
         before_j after_j w_j recipe_j rows_j
         after_idx_i after_idx_j,
    phase_semantic_second_level_schedules_equivalent
      env_size mask before_pis after_pis ws recipes semantic_rows ->
    nth_error before_pis i = Some before_i ->
    nth_error after_pis i = Some after_i ->
    nth_error ws i = Some w_i ->
    nth_error recipes i = Some recipe_i ->
    nth_error semantic_rows i = Some rows_i ->
    nth_error before_pis j = Some before_j ->
    nth_error after_pis j = Some after_j ->
    nth_error ws j = Some w_j ->
    nth_error recipes j = Some recipe_j ->
    nth_error semantic_rows j = Some rows_j ->
    schedule_matches_with_symmetric_trailing_zero_padding
      rows_i
      (select_by_mask mask
         (phase_semantic_padded_source_schedule
            env_size (List.length mask) before_i)) /\
    schedule_matches_with_symmetric_trailing_zero_padding
      rows_j
      (select_by_mask mask
         (phase_semantic_padded_source_schedule
            env_size (List.length mask) before_j)) /\
    exists expected_i expected_j,
      phase_semantic_second_level_target_schedule
        env_size mask before_i w_i recipe_i = Some expected_i /\
      phase_semantic_second_level_target_schedule
        env_size mask before_j w_j recipe_j = Some expected_j /\
      lex_compare
        (affine_product (Tiling.PL.pi_schedule after_i) after_idx_i)
        (affine_product (Tiling.PL.pi_schedule after_j) after_idx_j) =
      lex_compare
        (affine_product expected_i after_idx_i)
        (affine_product expected_j after_idx_j).
Proof.
  intros env_size mask before_pis after_pis ws recipes semantic_rows
         i j
         before_i after_i w_i recipe_i rows_i
         before_j after_j w_j recipe_j rows_j
         after_idx_i after_idx_j Hequiv
         Hbefore_i Hafter_i Hw_i Hrecipe_i Hrows_i
         Hbefore_j Hafter_j Hw_j Hrecipe_j Hrows_j.
  destruct Hequiv as [Hsymmetric | [Hsources Herasure]].
  - destruct
      (phase_semantic_second_schedules_match_nth_error
         env_size mask before_pis after_pis ws recipes semantic_rows
         i before_i after_i w_i recipe_i rows_i
         Hsymmetric Hbefore_i Hafter_i Hw_i Hrecipe_i Hrows_i)
      as [Hsource_i [expected_i [Hexpected_i Htarget_i]]].
    destruct
      (phase_semantic_second_schedules_match_nth_error
         env_size mask before_pis after_pis ws recipes semantic_rows
         j before_j after_j w_j recipe_j rows_j
         Hsymmetric Hbefore_j Hafter_j Hw_j Hrecipe_j Hrows_j)
      as [Hsource_j [expected_j [Hexpected_j Htarget_j]]].
    pose proof
      (schedule_matches_with_symmetric_trailing_zero_padding_affine_product_is_eq
         expected_i (Tiling.PL.pi_schedule after_i)
         after_idx_i Htarget_i)
      as Htarget_eq_i.
    pose proof
      (schedule_matches_with_symmetric_trailing_zero_padding_affine_product_is_eq
         expected_j (Tiling.PL.pi_schedule after_j)
         after_idx_j Htarget_j)
      as Htarget_eq_j.
    split; [exact Hsource_i|].
    split; [exact Hsource_j|].
    exists expected_i, expected_j.
    repeat split; try assumption.
    transitivity
      (lex_compare
         (affine_product expected_i after_idx_i)
         (affine_product (Tiling.PL.pi_schedule after_j) after_idx_j)).
    + apply lex_compare_left_eq.
      exact Htarget_eq_i.
    + apply lex_compare_right_eq.
      exact Htarget_eq_j.
  - destruct Herasure as [expected [Hexpected Htarget_match]].
    pose proof
      (phase_semantic_second_sources_match_nth_error
         env_size mask before_pis ws recipes semantic_rows
         i before_i w_i recipe_i rows_i
         Hsources Hbefore_i Hw_i Hrecipe_i Hrows_i)
      as Hsource_i.
    pose proof
      (phase_semantic_second_sources_match_nth_error
         env_size mask before_pis ws recipes semantic_rows
         j before_j w_j recipe_j rows_j
         Hsources Hbefore_j Hw_j Hrecipe_j Hrows_j)
      as Hsource_j.
    destruct
      (phase_semantic_second_level_expected_schedules_nth_error
         env_size mask before_pis ws recipes expected
         i before_i w_i recipe_i
         Hexpected Hbefore_i Hw_i Hrecipe_i)
      as [expected_i [Hexpected_i Hexpected_nth_i]].
    destruct
      (phase_semantic_second_level_expected_schedules_nth_error
         env_size mask before_pis ws recipes expected
         j before_j w_j recipe_j
         Hexpected Hbefore_j Hw_j Hrecipe_j)
      as [expected_j [Hexpected_j Hexpected_nth_j]].
    pose proof
      (Tiling.nth_error_map_some
         _ _ Tiling.PL.pi_schedule after_pis
         i after_i Hafter_i)
      as Hafter_map_i.
    pose proof
      (Tiling.nth_error_map_some
         _ _ Tiling.PL.pi_schedule after_pis
         j after_j Hafter_j)
      as Hafter_map_j.
    split; [exact Hsource_i|].
    split; [exact Hsource_j|].
    exists expected_i, expected_j.
    repeat split; try assumption.
    eapply schedule_lists_zero_erasure_match_pair_lex; eauto.
Qed.

Lemma phase_semantic_full_schedules_nth_error :
  forall env_size mask before_pis ws full_rows
         n before_pi w rows,
    phase_semantic_full_schedules_for_tiling
      env_size mask before_pis ws = Some full_rows ->
    nth_error before_pis n = Some before_pi ->
    nth_error ws n = Some w ->
    nth_error full_rows n = Some rows ->
    rows =
      phase_semantic_lifted_band_rows
        env_size (List.length (stw_links w)) mask before_pi.
Proof.
  intros env_size mask before_pis.
  induction before_pis as [|before0 before_pis IH];
    intros ws full_rows n before_pi w rows
           Hfull Hbefore Hw Hrows.
  - destruct ws; destruct n; discriminate.
  - destruct ws as [|w0 ws]; simpl in Hfull; try discriminate.
    destruct
      (phase_semantic_full_schedules_for_tiling
         env_size mask before_pis ws)
      as [rest|] eqn:Hrest; try discriminate.
    inversion Hfull; subst full_rows.
    destruct n as [|n].
    + simpl in Hbefore, Hw, Hrows.
      inversion Hbefore; inversion Hw; inversion Hrows; subst.
      reflexivity.
    + simpl in Hbefore, Hw, Hrows.
      eapply IH; eauto.
Qed.

Lemma phase_semantic_source_schedule_bound :
  forall env_size before_pis n before_pi,
    nth_error before_pis n = Some before_pi ->
    (List.length (Tiling.PL.pi_schedule before_pi) <=
     List.length
       (global_phase_semantic_loop_mask env_size before_pis))%nat.
Proof.
  intros env_size before_pis n before_pi Hnth.
  unfold global_phase_semantic_loop_mask.
  rewrite List.map_length, seq_length.
  eapply max_schedule_length_ge_nth_error.
  eapply Tiling.nth_error_map_some.
  exact Hnth.
Qed.

Lemma phase_semantic_full_schedules_for_tiling_length :
  forall env_size mask before_pis ws full_rows,
    phase_semantic_full_schedules_for_tiling
      env_size mask before_pis ws = Some full_rows ->
    List.length full_rows = List.length before_pis /\
    List.length ws = List.length before_pis.
Proof.
  intros env_size mask before_pis.
  induction before_pis as [|before_pi before_pis IH];
    intros ws full_rows Hfull.
  - destruct ws as [|w ws]; simpl in Hfull; try discriminate.
    inversion Hfull.
    split; reflexivity.
  - destruct ws as [|w ws]; simpl in Hfull; try discriminate.
    destruct
      (phase_semantic_full_schedules_for_tiling
         env_size mask before_pis ws)
      as [rest|] eqn:Hrest; try discriminate.
    inversion Hfull; subst full_rows.
    destruct (IH ws rest Hrest) as [Hrest_len Hws_len].
    simpl.
    split; lia.
Qed.

Lemma scalar_aware_loop_tiles_monotone_quotient :
  forall mask band1 band2 tiles1 tiles2 sizes,
    scalar_aware_loop_tiles_monotone
      mask band1 band2 tiles1 tiles2 ->
    List.length tiles1 = List.length sizes ->
    Forall (fun size => (0 < size)%Z) sizes ->
    scalar_aware_loop_tiles_monotone
      mask band1 band2
      (semantic_quotient_tiles tiles1 sizes)
      (semantic_quotient_tiles tiles2 sizes).
Proof.
  intros mask band1 band2 tiles1 tiles2 sizes Hmonotone.
  revert sizes.
  induction Hmonotone;
    intros sizes Hlen Hpositive.
  - destruct sizes; [constructor|discriminate].
  - destruct sizes as [|size sizes]; [discriminate|].
    inversion Hpositive as [|size0 sizes0 Hsize Hpositive_tail];
      subst size0 sizes0.
    simpl in Hlen.
    unfold semantic_quotient_tiles in *.
    simpl.
    constructor.
    + intro Hband.
      apply Z.div_le_mono.
      * exact Hsize.
      * apply H.
        exact Hband.
    + eapply IHHmonotone; eauto.
  - unfold semantic_quotient_tiles in *.
    constructor.
    eapply IHHmonotone; eauto.
Qed.

Lemma phase_semantic_second_added_tiles_eq :
  forall env_size mask before_pi w recipe
         global_root_sizes global_child_sizes envv point added,
    List.length envv = env_size ->
    List.length point = stw_point_dim w ->
    second_level_band_recipe_spec
      (stw_point_dim w) O (stw_links w) recipe ->
    prefix_sizes (slbr_root_sizes recipe) global_root_sizes ->
    prefix_sizes (slbr_child_sizes recipe) global_child_sizes ->
    List.length global_root_sizes = count_true mask ->
    List.length global_child_sizes = count_true mask ->
    (List.length (Tiling.PL.pi_schedule before_pi) <=
     List.length mask)%nat ->
    well_formed_statement_tiling_witness w ->
    Forall
      (fun link =>
         List.length (ae_param_coeffs (tl_expr link)) =
         List.length envv)
      (stw_links w) ->
    schedule_matches_with_symmetric_trailing_zero_padding
      (slbr_root_rows recipe)
      (select_by_mask mask
         (phase_semantic_padded_source_schedule
            env_size (List.length mask) before_pi)) ->
    added = eval_tile_links [] point envv (stw_links w) ->
    let band_values :=
      affine_product
        (phase_semantic_padded_source_schedule
           env_size (List.length mask) before_pi)
        (envv ++ point) in
    let global_roots :=
      scalar_aware_loop_tile_values
        mask band_values global_root_sizes in
    List.map
      (fun pos => nth pos added 0%Z)
      (second_level_child_positions
         (List.length (slbr_root_rows recipe))) ++
    repeat 0%Z
      (count_true mask - List.length (slbr_root_rows recipe)) =
    semantic_quotient_tiles global_roots global_child_sizes /\
    List.map
      (fun pos => nth pos added 0%Z)
      (second_level_root_positions
         (List.length (slbr_root_rows recipe))) ++
    repeat 0%Z
      (count_true mask - List.length (slbr_root_rows recipe)) =
    global_roots.
Proof.
  intros env_size mask before_pi w recipe
         global_root_sizes global_child_sizes envv point added
         Henv Hpoint Hspec Hroot_prefix Hchild_prefix
         Hroot_global_len Hchild_global_len Hbefore_bound
         Hwf Hparams Hsource_match Hadded.
  cbn beta iota zeta.
  set
    (band_values :=
       affine_product
         (phase_semantic_padded_source_schedule
            env_size (List.length mask) before_pi)
         (envv ++ point)).
  set (loop_values := select_by_mask mask band_values).
  set
    (raw_values :=
       affine_product (slbr_root_rows recipe) (envv ++ point)).
  set (roots := second_level_root_tiles recipe envv point).
  set (children := second_level_child_tiles recipe envv point).
  destruct
    (second_level_band_recipe_spec_lengths _ _ _ _ Hspec)
    as [Hroot_rows_sizes Hroot_rows_child_sizes].
  assert
    (Hband_len : List.length band_values = List.length mask).
  {
    subst band_values.
    unfold affine_product,
           phase_semantic_padded_source_schedule,
           Tiling.PL.pad_schedule_to_len.
    rewrite List.map_length, app_length, repeat_length.
    lia.
  }
  assert
    (Hloop_len : List.length loop_values = count_true mask).
  {
    subst loop_values.
    eapply select_by_mask_length_count_true.
    exact Hband_len.
  }
  assert
    (Hraw_len :
       List.length raw_values = List.length (slbr_root_rows recipe)).
  {
    subst raw_values.
    unfold affine_product.
    rewrite List.map_length.
    reflexivity.
  }
  assert (Hsource_eq : is_eq raw_values loop_values = true).
  {
    subst raw_values loop_values band_values.
    pose proof
      (schedule_matches_with_symmetric_trailing_zero_padding_affine_product_is_eq
         (slbr_root_rows recipe)
         (select_by_mask mask
            (phase_semantic_padded_source_schedule
               env_size (List.length mask) before_pi))
         (envv ++ point) Hsource_match)
      as Heq.
    rewrite affine_product_select_by_mask in Heq.
    rewrite is_eq_commutative.
    exact Heq.
  }
  assert
    (Hraw_le_loop :
       (List.length raw_values <= List.length loop_values)%nat).
  {
    destruct Hroot_prefix as [Hwidth Hprefix_values].
    rewrite Hraw_len, Hroot_rows_sizes.
    rewrite Hloop_len, <- Hroot_global_len.
    exact Hwidth.
  }
  assert
    (Hloop_values :
       loop_values =
       raw_values ++
       repeat 0%Z
         (List.length loop_values - List.length raw_values)).
  {
    eapply is_eq_zero_extend_right; eauto.
  }
  assert
    (Hadded_tiles :
       added = interleave_root_child_tiles roots children).
  {
    rewrite Hadded.
    subst roots children.
    change
      (eval_tile_links [] point envv (stw_links w) =
       [] ++
       interleave_root_child_tiles
         (second_level_root_tiles recipe envv point)
         (second_level_child_tiles recipe envv point)).
    eapply eval_tile_links_from_second_level_recipe_spec; eauto.
  }
  assert
    (Hroots_len :
       List.length roots = List.length (slbr_root_rows recipe)).
  {
    subst roots.
    rewrite second_level_root_tiles_length by exact Hroot_rows_sizes.
    lia.
  }
  assert
    (Hchildren_len :
       List.length children = List.length (slbr_root_rows recipe)).
  {
    subst children.
    unfold second_level_child_tiles.
    rewrite List.map_length, combine_length.
    rewrite second_level_root_tiles_length by exact Hroot_rows_sizes.
    lia.
  }
  assert
    (Hroots_children :
       List.length roots = List.length children) by lia.
  assert
    (Hroots_def :
       roots =
       semantic_quotient_tiles raw_values (slbr_root_sizes recipe)).
  {
    subst roots raw_values.
    reflexivity.
  }
  assert
    (Hchildren_def :
       children =
       semantic_quotient_tiles roots (slbr_child_sizes recipe)).
  {
    subst children.
    unfold second_level_child_tiles, semantic_quotient_tiles.
    fold roots.
    reflexivity.
  }
  assert
    (Hglobal_roots :
       scalar_aware_loop_tile_values
         mask band_values global_root_sizes =
       roots ++
       repeat 0%Z
         (List.length global_root_sizes -
          List.length (slbr_root_sizes recipe))).
  {
    unfold scalar_aware_loop_tile_values.
    fold loop_values.
    rewrite Hloop_values, Hloop_len, Hraw_len.
    rewrite <- Hroot_global_len.
    pose proof
      (semantic_quotient_tiles_pad_prefix
         raw_values (slbr_root_sizes recipe) global_root_sizes)
      as Hpad.
    specialize (Hpad (eq_trans Hraw_len Hroot_rows_sizes) Hroot_prefix).
    rewrite <- Hroots_def in Hpad.
    rewrite Hraw_len in Hpad.
    exact Hpad.
  }
  assert
    (Hglobal_children :
       semantic_quotient_tiles
         (scalar_aware_loop_tile_values
            mask band_values global_root_sizes)
         global_child_sizes =
       children ++
       repeat 0%Z
         (List.length global_child_sizes -
          List.length (slbr_child_sizes recipe))).
  {
    rewrite Hglobal_roots.
    assert
      (Hglobal_len :
         List.length global_root_sizes =
         List.length global_child_sizes) by lia.
    assert
      (Hlocal_len :
         List.length roots =
         List.length (slbr_child_sizes recipe)) by lia.
    replace
      (List.length global_root_sizes -
       List.length (slbr_root_sizes recipe))%nat
      with
      (List.length global_child_sizes -
       List.length roots)%nat by lia.
    pose proof
      (semantic_quotient_tiles_pad_prefix
         roots (slbr_child_sizes recipe) global_child_sizes)
      as Hpad.
    specialize
      (Hpad
         (eq_trans Hroots_len Hroot_rows_child_sizes)
         Hchild_prefix).
    rewrite <- Hchildren_def in Hpad.
    exact Hpad.
  }
  split.
  - rewrite Hadded_tiles.
    replace
      (List.length (slbr_root_rows recipe))
      with (List.length roots) in * by lia.
    rewrite map_nth_child_positions_interleave
      by exact Hroots_children.
    rewrite Hglobal_children.
    f_equal.
    f_equal.
    lia.
  - rewrite Hadded_tiles.
    replace
      (List.length (slbr_root_rows recipe))
      with (List.length roots) in * by lia.
    rewrite map_nth_root_positions_interleave
      by exact Hroots_children.
    rewrite Hglobal_roots.
    f_equal.
    f_equal.
    lia.
Qed.

(** The phase-aware ordinary bridge first proves that the common scalar phase
    prefix selects one statement class.  Within that class, the remaining
    timestamp argument is the ordinary semantic bridge: reconstruct the band,
    rule out a monotone reversal, and expose a checked decrease. *)
Lemma phase_semantic_ordinary_band_shape_reversal_bridge :
  forall before_pis before_ctxt before_vars after_pis ws shape envv,
    List.length before_ctxt = List.length envv ->
    TilingCheck.check_pprog_tiling_sourceb
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars) ws = true ->
    phase_semantic_ordinary_band_shape_property
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars) ws shape ->
    semantic_rows_reversal_bridge
      envv before_pis after_pis ws (psobs_full_rows shape).
Proof.
  (* Stage 1: recover the phase-aware shape, loop mask, and global tile sizes. *)
  intros before_pis before_ctxt before_vars after_pis ws
         shape envv Hlen_env Hsource Hshape.
  unfold phase_semantic_ordinary_band_shape_property in Hshape.
  cbn in Hshape.
  destruct Hshape as
    [_ [_ [data
      [Hdata [Hglobal_sizes [Hrows_eq
      [Hloop_mask [Hfull [_ [Hglobal_width
      [_ Hschedules]]]]]]]]]]].
  pose proof
    (TilingCheck.check_pprog_tiling_sourceb_sound
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars) ws Hsource)
    as [Hprog [_ [Hwf_ws [Hpositive_ws Hdepths]]]].
  assert
    (Hwf_ws_env :
       Forall
         (Tiling.wf_statement_tiling_witness_with_param_dim
            (List.length envv))
         ws).
  {
    rewrite <- Hlen_env.
    exact Hwf_ws.
  }
  assert
    (Hglobal_prefix :
       Forall
         (fun local => prefix_sizes local (psobs_global_sizes shape))
         (List.map snd data)).
  {
    eapply infer_global_prefix_sizes_sound.
    exact Hglobal_sizes.
  }
  assert
    (Hglobal_positive :
       Forall (fun size => (0 < size)%Z)
         (psobs_global_sizes shape)).
  {
    eapply infer_global_prefix_sizes_positive.
    - exact Hglobal_sizes.
    - pose proof
        (parse_ordinary_semantic_data_positive
           ws data Hdata Hpositive_ws)
        as Hdata_positive.
      apply Forall_forall.
      intros local Hin.
      apply in_map_iff in Hin.
      destruct Hin as [entry [Heq Hin]].
      subst local.
      eapply Forall_forall in Hdata_positive; eauto.
  }
  assert (Hdata_len : List.length data = List.length ws).
  {
    eapply parse_ordinary_semantic_data_length.
    exact Hdata.
  }
  assert
    (Hsemantic_rows_len :
       List.length (psobs_rows shape) = List.length before_pis).
  {
    rewrite Hrows_eq, List.map_length, Hdata_len.
    symmetry.
    eapply Forall2_length.
    exact Hdepths.
  }
  destruct
    (phase_semantic_full_schedules_for_tiling_length
       (List.length before_ctxt) (psobs_loop_mask shape)
       before_pis ws (psobs_full_rows shape) Hfull)
    as [Hfull_rows_len _].
  (* Stage 2: recover both endpoints and their statement-local phase layouts. *)
  unfold semantic_rows_reversal_bridge.
  intros flat ip1 ip2 Hflat Hin1 Hin2 Hold Hnew.
  destruct
    (composed_point_pair_facts_of_members
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       ws envv flat ip1 ip2
       Hprog Hwf_ws_env Hpositive_ws Hdepths Hflat Hin1 Hin2)
    as [Hpoint1 Hpoint2].
  unfold composed_point_facts in Hpoint1, Hpoint2.
  destruct Hpoint1 as [before_pi1 [after_pi1 [w1
    [Hbefore1 [Hafter1 [Hw1
    [Hwf_stmt1 [Hpositive1 [Hpoint_depth1
    [Hpref1 [Hbel1 Hidx_len1]]]]]]]]]]].
  destruct Hpoint2 as [before_pi2 [after_pi2 [w2
    [Hbefore2 [Hafter2 [Hw2
    [Hwf_stmt2 [Hpositive2 [Hpoint_depth2
    [Hpref2 [Hbel2 Hidx_len2]]]]]]]]]]].
  assert
    (Hn1 : (Tiling.PL.ip_nth_ext ip1 < List.length ws)%nat).
  {
    apply nth_error_Some.
    rewrite Hw1.
    discriminate.
  }
  assert
    (Hn2 : (Tiling.PL.ip_nth_ext ip2 < List.length ws)%nat).
  {
    apply nth_error_Some.
    rewrite Hw2.
    discriminate.
  }
  destruct
    (nth_error data (Tiling.PL.ip_nth_ext ip1))
    as [[raw1 local_sizes1]|] eqn:Hdata1.
  2:{
    exfalso.
    apply nth_error_None in Hdata1.
    lia.
  }
  destruct
    (nth_error data (Tiling.PL.ip_nth_ext ip2))
    as [[raw2 local_sizes2]|] eqn:Hdata2.
  2:{
    exfalso.
    apply nth_error_None in Hdata2.
    lia.
  }
  destruct
    (parse_ordinary_semantic_data_nth_error
       ws data (Tiling.PL.ip_nth_ext ip1)
       w1 raw1 local_sizes1 Hdata Hw1 Hdata1)
    as [Hraw1 Hlocal_sizes1].
  destruct
    (parse_ordinary_semantic_data_nth_error
       ws data (Tiling.PL.ip_nth_ext ip2)
       w2 raw2 local_sizes2 Hdata Hw2 Hdata2)
    as [Hraw2 Hlocal_sizes2].
  assert
    (Hraw_map1 :
       nth_error (List.map fst data) (Tiling.PL.ip_nth_ext ip1) =
       Some raw1).
  {
    pose proof
      (Tiling.nth_error_map_some
         _ _ (@fst Schedule (list Z)) data
         (Tiling.PL.ip_nth_ext ip1)
         (raw1, local_sizes1) Hdata1)
      as Hnth.
    cbn in Hnth.
    exact Hnth.
  }
  assert
    (Hraw_map2 :
       nth_error (List.map fst data) (Tiling.PL.ip_nth_ext ip2) =
       Some raw2).
  {
    pose proof
      (Tiling.nth_error_map_some
         _ _ (@fst Schedule (list Z)) data
         (Tiling.PL.ip_nth_ext ip2)
         (raw2, local_sizes2) Hdata2)
      as Hnth.
    cbn in Hnth.
    exact Hnth.
  }
  assert
    (Hsizes_map1 :
       nth_error (List.map snd data) (Tiling.PL.ip_nth_ext ip1) =
       Some local_sizes1).
  {
    pose proof
      (Tiling.nth_error_map_some
         _ _ (@snd Schedule (list Z)) data
         (Tiling.PL.ip_nth_ext ip1)
         (raw1, local_sizes1) Hdata1)
      as Hnth.
    cbn in Hnth.
    exact Hnth.
  }
  assert
    (Hsizes_map2 :
       nth_error (List.map snd data) (Tiling.PL.ip_nth_ext ip2) =
       Some local_sizes2).
  {
    pose proof
      (Tiling.nth_error_map_some
         _ _ (@snd Schedule (list Z)) data
         (Tiling.PL.ip_nth_ext ip2)
         (raw2, local_sizes2) Hdata2)
      as Hnth.
    cbn in Hnth.
    exact Hnth.
  }
  pose proof
    (Tiling.Forall_nth_error
       _ _ (List.map snd data) (Tiling.PL.ip_nth_ext ip1)
       local_sizes1 Hglobal_prefix Hsizes_map1)
    as Hlocal_prefix1.
  pose proof
    (Tiling.Forall_nth_error
       _ _ (List.map snd data) (Tiling.PL.ip_nth_ext ip2)
       local_sizes2 Hglobal_prefix Hsizes_map2)
    as Hlocal_prefix2.
  destruct
    (nth_error (psobs_rows shape) (Tiling.PL.ip_nth_ext ip1))
    as [semantic_rows1|] eqn:Hsemantic_rows1.
  2:{
    exfalso.
    apply nth_error_None in Hsemantic_rows1.
    assert
      (Hlt : (Tiling.PL.ip_nth_ext ip1 < List.length before_pis)%nat).
    {
      apply nth_error_Some.
      rewrite Hbefore1.
      discriminate.
    }
    lia.
  }
  destruct
    (nth_error (psobs_rows shape) (Tiling.PL.ip_nth_ext ip2))
    as [semantic_rows2|] eqn:Hsemantic_rows2.
  2:{
    exfalso.
    apply nth_error_None in Hsemantic_rows2.
    assert
      (Hlt : (Tiling.PL.ip_nth_ext ip2 < List.length before_pis)%nat).
    {
      apply nth_error_Some.
      rewrite Hbefore2.
      discriminate.
    }
    lia.
  }
  destruct
    (nth_error (psobs_full_rows shape) (Tiling.PL.ip_nth_ext ip1))
    as [full_rows1|] eqn:Hfull_rows1.
  2:{
    exfalso.
    apply nth_error_None in Hfull_rows1.
    assert
      (Hlt : (Tiling.PL.ip_nth_ext ip1 < List.length before_pis)%nat).
    {
      apply nth_error_Some.
      rewrite Hbefore1.
      discriminate.
    }
    lia.
  }
  destruct
    (nth_error (psobs_full_rows shape) (Tiling.PL.ip_nth_ext ip2))
    as [full_rows2|] eqn:Hfull_rows2.
  2:{
    exfalso.
    apply nth_error_None in Hfull_rows2.
    assert
      (Hlt : (Tiling.PL.ip_nth_ext ip2 < List.length before_pis)%nat).
    {
      apply nth_error_Some.
      rewrite Hbefore2.
      discriminate.
    }
    lia.
  }
  assert (Hsemantic_raw1 : semantic_rows1 = raw1).
  {
    rewrite Hrows_eq, Hraw_map1 in Hsemantic_rows1.
    inversion Hsemantic_rows1.
    reflexivity.
  }
  assert (Hsemantic_raw2 : semantic_rows2 = raw2).
  {
    rewrite Hrows_eq, Hraw_map2 in Hsemantic_rows2.
    inversion Hsemantic_rows2.
    reflexivity.
  }
  destruct
    (phase_semantic_ordinary_schedules_match_nth_error
       (List.length before_ctxt) (psobs_loop_mask shape)
       before_pis after_pis ws (psobs_rows shape)
       (Tiling.PL.ip_nth_ext ip1)
       before_pi1 after_pi1 w1 semantic_rows1
       Hschedules Hbefore1 Hafter1 Hw1 Hsemantic_rows1)
    as [Hsource_match1
        [expected1 [Hexpected1 Htarget_match1]]].
  destruct
    (phase_semantic_ordinary_schedules_match_nth_error
       (List.length before_ctxt) (psobs_loop_mask shape)
       before_pis after_pis ws (psobs_rows shape)
       (Tiling.PL.ip_nth_ext ip2)
       before_pi2 after_pi2 w2 semantic_rows2
       Hschedules Hbefore2 Hafter2 Hw2 Hsemantic_rows2)
    as [Hsource_match2
        [expected2 [Hexpected2 Htarget_match2]]].
  rewrite Hsemantic_raw1 in Hsource_match1.
  rewrite Hsemantic_raw2 in Hsource_match2.
  pose proof
    (phase_semantic_full_schedules_nth_error
       (List.length before_ctxt) (psobs_loop_mask shape)
       before_pis ws (psobs_full_rows shape)
       (Tiling.PL.ip_nth_ext ip1) before_pi1 w1 full_rows1
       Hfull Hbefore1 Hw1 Hfull_rows1)
    as Hfull_def1.
  pose proof
    (phase_semantic_full_schedules_nth_error
       (List.length before_ctxt) (psobs_loop_mask shape)
       before_pis ws (psobs_full_rows shape)
       (Tiling.PL.ip_nth_ext ip2) before_pi2 w2 full_rows2
       Hfull Hbefore2 Hw2 Hfull_rows2)
    as Hfull_def2.
  pose proof
    (Tiling.nth_error_compose_tiling_pinstrs_ext_from_after
       (List.length envv) before_pis after_pis ws
       (Tiling.PL.ip_nth_ext ip1)
       before_pi1 after_pi1 w1 Hbefore1 Hafter1 Hw1)
    as Hcomposed1.
  pose proof
    (Tiling.nth_error_compose_tiling_pinstrs_ext_from_after
       (List.length envv) before_pis after_pis ws
       (Tiling.PL.ip_nth_ext ip2)
       before_pi2 after_pi2 w2 Hbefore2 Hafter2 Hw2)
    as Hcomposed2.
  pose proof
    (Tiling.tiling_rel_pprog_structure_source_nth
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       (List.map Tiling.compiled_pinstr_tiling_witness ws)
       (Tiling.PL.ip_nth_ext ip1)
       before_pi1 after_pi1
       (Tiling.compiled_pinstr_tiling_witness w1)
       Hprog Hbefore1 Hafter1
       (Tiling.nth_error_map_some
          _ _ Tiling.compiled_pinstr_tiling_witness
          ws (Tiling.PL.ip_nth_ext ip1) w1 Hw1))
    as Hstmt1.
  pose proof
    (Tiling.tiling_rel_pprog_structure_source_nth
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       (List.map Tiling.compiled_pinstr_tiling_witness ws)
       (Tiling.PL.ip_nth_ext ip2)
       before_pi2 after_pi2
       (Tiling.compiled_pinstr_tiling_witness w2)
       Hprog Hbefore2 Hafter2
       (Tiling.nth_error_map_some
          _ _ Tiling.compiled_pinstr_tiling_witness
          ws (Tiling.PL.ip_nth_ext ip2) w2 Hw2))
    as Hstmt2.
  pose proof
    (tiling_rel_pinstr_structure_source_after_matches
       (List.length before_ctxt) before_pi1 after_pi1 w1
       Hstmt1 Hpoint_depth1)
    as Hafter_wit1.
  pose proof
    (tiling_rel_pinstr_structure_source_after_matches
       (List.length before_ctxt) before_pi2 after_pi2 w2
       Hstmt2 Hpoint_depth2)
    as Hafter_wit2.
  destruct Hafter_wit1 as [Hafter_pw1 Hafter_wit_depth1].
  destruct Hafter_wit2 as [Hafter_pw2 Hafter_wit_depth2].
  assert
    (Hafter_depth1 :
       Tiling.PL.pi_depth after_pi1 =
       (Tiling.PL.pi_depth before_pi1 +
        List.length (stw_links w1))%nat).
  {
    unfold Tiling.tiling_rel_pinstr_structure_source in Hstmt1.
    destruct Hstmt1 as [_ [Hdepth _]].
    exact Hdepth.
  }
  assert
    (Hafter_depth2 :
       Tiling.PL.pi_depth after_pi2 =
       (Tiling.PL.pi_depth before_pi2 +
        List.length (stw_links w2))%nat).
  {
    unfold Tiling.tiling_rel_pinstr_structure_source in Hstmt2.
    destruct Hstmt2 as [_ [Hdepth _]].
    exact Hdepth.
  }
  (* Stage 3: split the tiled coordinates and render old and target timestamps
     as phase prefix, tile values, and semantic band values. *)
  set
    (added1 :=
       Tiling.tiled_added_part
         (List.length envv) (List.length (stw_links w1))
         (Tiling.PL.ip_index_ext ip1)).
  set
    (point1 :=
       Tiling.tiled_point_part
         (List.length envv) (List.length (stw_links w1))
         (Tiling.PL.ip_index_ext ip1)).
  set
    (added2 :=
       Tiling.tiled_added_part
         (List.length envv) (List.length (stw_links w2))
         (Tiling.PL.ip_index_ext ip2)).
  set
    (point2 :=
       Tiling.tiled_point_part
         (List.length envv) (List.length (stw_links w2))
         (Tiling.PL.ip_index_ext ip2)).
  assert (Hadded_len1 : List.length added1 = List.length (stw_links w1)).
  {
    subst added1.
    eapply Tiling.tiled_added_part_length
      with (point_dim := stw_point_dim w1).
    rewrite Hidx_len1, Hafter_depth1, <- Hpoint_depth1.
    lia.
  }
  assert (Hadded_len2 : List.length added2 = List.length (stw_links w2)).
  {
    subst added2.
    eapply Tiling.tiled_added_part_length
      with (point_dim := stw_point_dim w2).
    rewrite Hidx_len2, Hafter_depth2, <- Hpoint_depth2.
    lia.
  }
  assert (Hpoint_len1 : List.length point1 = stw_point_dim w1).
  {
    subst point1.
    eapply Tiling.tiled_point_part_length
      with (added_dims := List.length (stw_links w1)).
    rewrite Hidx_len1, Hafter_depth1, <- Hpoint_depth1.
    lia.
  }
  assert (Hpoint_len2 : List.length point2 = stw_point_dim w2).
  {
    subst point2.
    eapply Tiling.tiled_point_part_length
      with (added_dims := List.length (stw_links w2)).
    rewrite Hidx_len2, Hafter_depth2, <- Hpoint_depth2.
    lia.
  }
  assert
    (Hidx_split1 :
       Tiling.PL.ip_index_ext ip1 = envv ++ added1 ++ point1).
  {
    subst added1 point1.
    transitivity
      (firstn (List.length envv) (Tiling.PL.ip_index_ext ip1) ++
       Tiling.tiled_added_part
         (List.length envv) (List.length (stw_links w1))
         (Tiling.PL.ip_index_ext ip1) ++
       Tiling.tiled_point_part
         (List.length envv) (List.length (stw_links w1))
         (Tiling.PL.ip_index_ext ip1)).
    - apply Tiling.tiled_index_split.
    - rewrite Hpref1.
      reflexivity.
  }
  assert
    (Hidx_split2 :
       Tiling.PL.ip_index_ext ip2 = envv ++ added2 ++ point2).
  {
    subst added2 point2.
    transitivity
      (firstn (List.length envv) (Tiling.PL.ip_index_ext ip2) ++
       Tiling.tiled_added_part
         (List.length envv) (List.length (stw_links w2))
         (Tiling.PL.ip_index_ext ip2) ++
       Tiling.tiled_point_part
         (List.length envv) (List.length (stw_links w2))
         (Tiling.PL.ip_index_ext ip2)).
    - apply Tiling.tiled_index_split.
    - rewrite Hpref2.
      reflexivity.
  }
  unfold Tiling.compose_tiling_pinstr_ext in Hbel1, Hbel2.
  destruct Hbel1 as
    [Hafter_dom1 [_ [_ [Hts11 [Hts21 [_ _]]]]]].
  destruct Hbel2 as
    [Hafter_dom2 [_ [_ [Hts12 [Hts22 [_ _]]]]]].
  assert
    (Hts11_old :
       Tiling.PL.ip_time_stamp1_ext ip1 =
       affine_product (Tiling.PL.pi_schedule before_pi1)
         (envv ++ point1)).
  {
    rewrite Hts11.
    cbn [Tiling.compose_tiling_pinstr_ext].
    rewrite Hidx_split1.
    unfold Tiling.lift_schedule_after_env.
    eapply Tiling.lift_affine_function_after_env_eval.
    - reflexivity.
    - exact Hadded_len1.
  }
  assert
    (Hts12_old :
       Tiling.PL.ip_time_stamp1_ext ip2 =
       affine_product (Tiling.PL.pi_schedule before_pi2)
         (envv ++ point2)).
  {
    rewrite Hts12.
    cbn [Tiling.compose_tiling_pinstr_ext].
    rewrite Hidx_split2.
    unfold Tiling.lift_schedule_after_env.
    eapply Tiling.lift_affine_function_after_env_eval.
    - reflexivity.
    - exact Hadded_len2.
  }
  assert
    (Hts21_after :
       Tiling.PL.ip_time_stamp2_ext ip1 =
       affine_product (Tiling.PL.pi_schedule after_pi1)
         (Tiling.PL.ip_index_ext ip1)).
  {
    rewrite Hts21.
    cbn [Tiling.compose_tiling_pinstr_ext].
    reflexivity.
  }
  assert
    (Hts22_after :
       Tiling.PL.ip_time_stamp2_ext ip2 =
       affine_product (Tiling.PL.pi_schedule after_pi2)
         (Tiling.PL.ip_index_ext ip2)).
  {
    rewrite Hts22.
    cbn [Tiling.compose_tiling_pinstr_ext].
    reflexivity.
  }
  assert
    (Hstmt1_env :
       Tiling.tiling_rel_pinstr_structure_source
         (List.length envv) before_pi1 after_pi1
         (Tiling.compiled_pinstr_tiling_witness w1)).
  {
    rewrite <- Hlen_env.
    exact Hstmt1.
  }
  assert
    (Hstmt2_env :
       Tiling.tiling_rel_pinstr_structure_source
         (List.length envv) before_pi2 after_pi2
         (Tiling.compiled_pinstr_tiling_witness w2)).
  {
    rewrite <- Hlen_env.
    exact Hstmt2.
  }
  destruct Hwf_stmt1 as [Hwf_stmt1 Hparams1].
  destruct Hwf_stmt2 as [Hwf_stmt2 Hparams2].
  assert
    (Hadded_eq1 :
       added1 = eval_tile_links [] point1 envv (stw_links w1)).
  {
    pose proof
      (Tiling.tiling_rel_pinstr_structure_source_domain_complete
         envv before_pi1 after_pi1
         (Tiling.compiled_pinstr_tiling_witness w1)
         added1 point1 Hstmt1_env
         (Tiling.wf_compiled_pinstr_tiling_witness w1)
         (Tiling.compiled_pinstr_tiling_witness_matches w1)
         Hadded_len1 Hpoint_len1
         (conj Hwf_stmt1 Hparams1) Hpositive1)
      as Hcomplete.
    rewrite Hidx_split1 in Hafter_dom1.
    specialize (Hcomplete Hafter_dom1).
    tauto.
  }
  assert
    (Hadded_eq2 :
       added2 = eval_tile_links [] point2 envv (stw_links w2)).
  {
    pose proof
      (Tiling.tiling_rel_pinstr_structure_source_domain_complete
         envv before_pi2 after_pi2
         (Tiling.compiled_pinstr_tiling_witness w2)
         added2 point2 Hstmt2_env
         (Tiling.wf_compiled_pinstr_tiling_witness w2)
         (Tiling.compiled_pinstr_tiling_witness_matches w2)
         Hadded_len2 Hpoint_len2
         (conj Hwf_stmt2 Hparams2) Hpositive2)
      as Hcomplete.
    rewrite Hidx_split2 in Hafter_dom2.
    specialize (Hcomplete Hafter_dom2).
    tauto.
  }
  assert
    (Hbefore_bound1 :
       (List.length (Tiling.PL.pi_schedule before_pi1) <=
        List.length (psobs_loop_mask shape))%nat).
  {
    rewrite Hloop_mask.
    eapply phase_semantic_source_schedule_bound.
    exact Hbefore1.
  }
  assert
    (Hbefore_bound2 :
       (List.length (Tiling.PL.pi_schedule before_pi2) <=
        List.length (psobs_loop_mask shape))%nat).
  {
    rewrite Hloop_mask.
    eapply phase_semantic_source_schedule_bound.
    exact Hbefore2.
  }
  rewrite <- Hlocal_sizes1 in Hlocal_prefix1.
  rewrite <- Hlocal_sizes2 in Hlocal_prefix2.
  assert
    (Hlocal_width1 :
       (List.length (stw_links w1) <=
        count_true (psobs_loop_mask shape))%nat).
  {
    destruct Hlocal_prefix1 as [Hwidth Hprefix_values].
    unfold tile_sizes_of_witness in Hwidth.
    rewrite List.map_length, Hglobal_width in Hwidth.
    exact Hwidth.
  }
  assert
    (Hlocal_width2 :
       (List.length (stw_links w2) <=
        count_true (psobs_loop_mask shape))%nat).
  {
    destruct Hlocal_prefix2 as [Hwidth Hprefix_values].
    unfold tile_sizes_of_witness in Hwidth.
    rewrite List.map_length, Hglobal_width in Hwidth.
    exact Hwidth.
  }
  pose proof
    (phase_semantic_added_tiles_eq
       (List.length before_ctxt) (psobs_loop_mask shape)
       before_pi1 w1 raw1 (psobs_global_sizes shape)
       envv point1 added1
       (eq_sym Hlen_env) Hpoint_len1 Hraw1 Hlocal_prefix1
       Hglobal_width Hbefore_bound1 Hwf_stmt1 Hparams1
       Hsource_match1 Hadded_eq1)
    as Hadded_global1.
  pose proof
    (phase_semantic_added_tiles_eq
       (List.length before_ctxt) (psobs_loop_mask shape)
       before_pi2 w2 raw2 (psobs_global_sizes shape)
       envv point2 added2
       (eq_sym Hlen_env) Hpoint_len2 Hraw2 Hlocal_prefix2
       Hglobal_width Hbefore_bound2 Hwf_stmt2 Hparams2
       Hsource_match2 Hadded_eq2)
    as Hadded_global2.
  destruct
    (phase_semantic_ordinary_target_schedule_eval
       (List.length before_ctxt) (psobs_loop_mask shape)
       before_pi1 w1 expected1 envv added1 point1
       Hexpected1 (eq_sym Hlen_env) Hadded_len1 Hpoint_len1
       Hlocal_width1)
    as [band_values1 [mixed_values1
        [Hband_values1 [Hrender1 Htarget_eval1]]]].
  destruct
    (phase_semantic_ordinary_target_schedule_eval
       (List.length before_ctxt) (psobs_loop_mask shape)
       before_pi2 w2 expected2 envv added2 point2
       Hexpected2 (eq_sym Hlen_env) Hadded_len2 Hpoint_len2
       Hlocal_width2)
    as [band_values2 [mixed_values2
        [Hband_values2 [Hrender2 Htarget_eval2]]]].
  rewrite Hadded_global1 in Hrender1.
  rewrite Hadded_global2 in Hrender2.
  rewrite <- Hband_values1 in Hrender1.
  rewrite <- Hband_values2 in Hrender2.
  assert
    (Hband_len1 :
       List.length band_values1 =
       List.length (psobs_loop_mask shape)).
  {
    rewrite Hband_values1.
    unfold affine_product,
           phase_semantic_padded_source_schedule,
           Tiling.PL.pad_schedule_to_len.
    rewrite List.map_length, app_length, repeat_length.
    lia.
  }
  assert
    (Hband_len2 :
       List.length band_values2 =
       List.length (psobs_loop_mask shape)).
  {
    rewrite Hband_values2.
    unfold affine_product,
           phase_semantic_padded_source_schedule,
           Tiling.PL.pad_schedule_to_len.
    rewrite List.map_length, app_length, repeat_length.
    lia.
  }
  assert
    (Hselected_len1 :
       List.length
         (select_by_mask
            (psobs_loop_mask shape) band_values1) =
       List.length (psobs_global_sizes shape)).
  {
    rewrite
      (select_by_mask_length_count_true
         Z (psobs_loop_mask shape) band_values1 Hband_len1).
    symmetry.
    exact Hglobal_width.
  }
  assert
    (Htile_monotone :
       scalar_aware_loop_tiles_monotone
         (psobs_loop_mask shape) band_values1 band_values2
         (scalar_aware_loop_tile_values
            (psobs_loop_mask shape) band_values1
            (psobs_global_sizes shape))
         (scalar_aware_loop_tile_values
            (psobs_loop_mask shape) band_values2
            (psobs_global_sizes shape))).
  {
    eapply scalar_aware_loop_tile_values_monotone.
    - exact Hband_len1.
    - exact Hband_len2.
    - exact Hselected_len1.
    - exact Hglobal_positive.
  }
  assert
    (Hmixed_eq :
       band_values1 = band_values2 ->
       mixed_values1 = mixed_values2).
  {
    intro Hband_eq.
    subst band_values2.
    congruence.
  }
  assert
    (Hmixed_mono :
       listz_pointwise_le band_values1 band_values2 ->
       listz_pointwise_le mixed_values1 mixed_values2).
  {
    intro Hband_le.
    eapply render_scalar_aware_value_prefix_pointwise_le.
    - exact Htile_monotone.
    - exact Hband_le.
    - exact Hrender1.
    - exact Hrender2.
  }
  assert
    (Hold_eq1 :
       is_eq
         (Tiling.PL.ip_time_stamp1_ext ip1)
         band_values1 = true).
  {
    rewrite Hts11_old, Hband_values1.
    unfold phase_semantic_padded_source_schedule.
    rewrite
      (affine_product_pad_schedule_to_len
         (List.length before_ctxt + Tiling.PL.pi_depth before_pi1)
         (List.length (psobs_loop_mask shape))
         (Tiling.PL.pi_schedule before_pi1)
         (envv ++ point1) Hbefore_bound1).
    rewrite is_eq_commutative.
    apply is_eq_app_repeat_zero.
  }
  assert
    (Hold_eq2 :
       is_eq
         (Tiling.PL.ip_time_stamp1_ext ip2)
         band_values2 = true).
  {
    rewrite Hts12_old, Hband_values2.
    unfold phase_semantic_padded_source_schedule.
    rewrite
      (affine_product_pad_schedule_to_len
         (List.length before_ctxt + Tiling.PL.pi_depth before_pi2)
         (List.length (psobs_loop_mask shape))
         (Tiling.PL.pi_schedule before_pi2)
         (envv ++ point2) Hbefore_bound2).
    rewrite is_eq_commutative.
    apply is_eq_app_repeat_zero.
  }
  assert
    (Hnew_eq1 :
       is_eq
         (Tiling.PL.ip_time_stamp2_ext ip1)
         (mixed_values1 ++ band_values1) = true).
  {
    rewrite Hts21_after, Hidx_split1.
    pose proof
      (schedule_matches_with_symmetric_trailing_zero_padding_affine_product_is_eq
         expected1 (Tiling.PL.pi_schedule after_pi1)
         (envv ++ added1 ++ point1) Htarget_match1)
      as Hmatch.
    rewrite Htarget_eval1 in Hmatch.
    exact Hmatch.
  }
  assert
    (Hnew_eq2 :
       is_eq
         (Tiling.PL.ip_time_stamp2_ext ip2)
         (mixed_values2 ++ band_values2) = true).
  {
    rewrite Hts22_after, Hidx_split2.
    pose proof
      (schedule_matches_with_symmetric_trailing_zero_padding_affine_product_is_eq
         expected2 (Tiling.PL.pi_schedule after_pi2)
         (envv ++ added2 ++ point2) Htarget_match2)
      as Hmatch.
    rewrite Htarget_eval2 in Hmatch.
    exact Hmatch.
  }
  (* Stage 4: equal phase classes and monotone tile values force any target
     reversal to decrease one checked semantic band component. *)
  unfold Tiling.PL.instr_point_ext_old_sched_lt in Hold.
  assert
    (Hnew_not_lt :
       lex_compare
         (Tiling.PL.ip_time_stamp2_ext ip1)
         (Tiling.PL.ip_time_stamp2_ext ip2) <> Lt).
  {
    unfold Tiling.PL.instr_point_ext_new_sched_ge in Hnew.
    destruct Hnew; congruence.
  }
  destruct
    (semantic_stripmined_reversal_implies_decreasing_component
       (Tiling.PL.ip_time_stamp1_ext ip1)
       (Tiling.PL.ip_time_stamp1_ext ip2)
       (Tiling.PL.ip_time_stamp2_ext ip1)
       (Tiling.PL.ip_time_stamp2_ext ip2)
       band_values1 band_values2 mixed_values1 mixed_values2
       Hold_eq1 Hold_eq2 Hnew_eq1 Hnew_eq2
       (eq_trans Hband_len1 (eq_sym Hband_len2))
       Hmixed_eq Hmixed_mono Hold Hnew_not_lt)
    as [dim [x [y [Hvalue1 [Hvalue2 Hdecrease]]]]].
  (* Stage 5: relate the decreasing component back to the full lifted rows. *)
  assert
    (Hfull_eval1 :
       affine_product full_rows1 (Tiling.PL.ip_index_ext ip1) =
       band_values1).
  {
    rewrite Hfull_def1, Hidx_split1.
    unfold phase_semantic_lifted_band_rows.
    transitivity
      (affine_product
         (phase_semantic_padded_source_schedule
            (List.length before_ctxt)
            (List.length (psobs_loop_mask shape)) before_pi1)
         (envv ++ point1)).
    - eapply Tiling.lift_affine_function_after_env_eval.
      + exact (eq_sym Hlen_env).
      + exact Hadded_len1.
    - symmetry.
      exact Hband_values1.
  }
  assert
    (Hfull_eval2 :
       affine_product full_rows2 (Tiling.PL.ip_index_ext ip2) =
       band_values2).
  {
    rewrite Hfull_def2, Hidx_split2.
    unfold phase_semantic_lifted_band_rows.
    transitivity
      (affine_product
         (phase_semantic_padded_source_schedule
            (List.length before_ctxt)
            (List.length (psobs_loop_mask shape)) before_pi2)
         (envv ++ point2)).
    - eapply Tiling.lift_affine_function_after_env_eval.
      + exact (eq_sym Hlen_env).
      + exact Hadded_len2.
    - symmetry.
      exact Hband_values2.
  }
  assert
    (Hfull_len1 :
       List.length band_values1 = List.length full_rows1).
  {
    rewrite <- Hfull_eval1.
    unfold affine_product.
    rewrite List.map_length.
    reflexivity.
  }
  exists
    (Tiling.compose_tiling_pinstr_ext
       (List.length envv) before_pi1 after_pi1 w1),
    (Tiling.compose_tiling_pinstr_ext
       (List.length envv) before_pi2 after_pi2 w2),
    full_rows1, full_rows2, dim.
  repeat split; try assumption.
  - eapply Nat.lt_le_trans.
    + apply nth_error_Some.
      rewrite Hvalue1.
      discriminate.
    + rewrite Hfull_len1.
      eapply max_schedule_length_ge_nth_error.
      exact Hfull_rows1.
  - assert
      (Hsemantic_value1 :
         semantic_band_value
           (List.length envv +
            Tiling.PL.pi_depth_ext
              (Tiling.compose_tiling_pinstr_ext
                 (List.length envv) before_pi1 after_pi1 w1))
           dim full_rows1 (Tiling.PL.ip_index_ext ip1) = x).
    {
      eapply semantic_band_value_of_nth_error.
      rewrite Hfull_eval1.
      exact Hvalue1.
    }
    assert
      (Hsemantic_value2 :
         semantic_band_value
           (List.length envv +
            Tiling.PL.pi_depth_ext
              (Tiling.compose_tiling_pinstr_ext
                 (List.length envv) before_pi2 after_pi2 w2))
           dim full_rows2 (Tiling.PL.ip_index_ext ip2) = y).
    {
      eapply semantic_band_value_of_nth_error.
      rewrite Hfull_eval2.
      exact Hvalue2.
    }
    rewrite Hsemantic_value1, Hsemantic_value2.
    exact Hdecrease.
Qed.

(** A two-level phase-preserving tile prefix can reverse a pair only at an
    active scalar-aware component.  Both quotient stages retain the scalar
    slots, so a scalar that already carries the pair protects both stages. *)
Lemma scalar_aware_two_level_reversal_active :
  forall mask band1 band2 child_tiles1 child_tiles2 root_tiles1 root_tiles2
         child1 child2 root1 root2,
    List.length band1 = List.length mask ->
    List.length band2 = List.length mask ->
    scalar_aware_loop_tiles_monotone mask band1 band2 child_tiles1 child_tiles2 ->
    scalar_aware_loop_tiles_monotone mask band1 band2 root_tiles1 root_tiles2 ->
    render_scalar_aware_value_prefix mask band1 child_tiles1 = Some child1 ->
    render_scalar_aware_value_prefix mask band2 child_tiles2 = Some child2 ->
    render_scalar_aware_value_prefix mask band1 root_tiles1 = Some root1 ->
    render_scalar_aware_value_prefix mask band2 root_tiles2 = Some root2 ->
    lex_compare band1 band2 = Lt ->
    lex_compare ((child1 ++ root1) ++ band1)
                ((child2 ++ root2) ++ band2) <> Lt ->
    exists dim x y,
      (dim < List.length mask)%nat /\
      nth_error band1 dim = Some x /\
      nth_error band2 dim = Some y /\
      (x > y)%Z /\
      listz_pointwise_le
        (select_scalar_values (firstn dim mask) (firstn dim band2))
        (select_scalar_values (firstn dim mask) (firstn dim band1)).
Proof.
  intros mask band1 band2 child_tiles1 child_tiles2 root_tiles1 root_tiles2
         child1 child2 root1 root2 Hlen1 Hlen2 Hchild_mono Hroot_mono
         Hchild1 Hchild2 Hroot1 Hroot2 Hold Hnew.
  assert (Hchild_len : List.length child1 = List.length child2).
  { rewrite (render_scalar_aware_value_prefix_length _ _ _ _ Hlen1 Hchild1).
    rewrite (render_scalar_aware_value_prefix_length _ _ _ _ Hlen2 Hchild2).
    reflexivity. }
  assert (Hroot_len : List.length root1 = List.length root2).
  { rewrite (render_scalar_aware_value_prefix_length _ _ _ _ Hlen1 Hroot1).
    rewrite (render_scalar_aware_value_prefix_length _ _ _ _ Hlen2 Hroot2).
    reflexivity. }
  assert (Hmixed : lex_compare (child1 ++ root1) (child2 ++ root2) = Gt).
  { destruct (scalar_aware_reversal_implies_mixed_gt
                [] [] (child1 ++ root1) (child2 ++ root2)
                band1 band2 [] [] eq_refl
                ltac:(rewrite !app_length, Hchild_len, Hroot_len; reflexivity))
      as [_ Hgt].
    - cbn. rewrite !app_nil_r. exact Hold.
    - cbn. rewrite !app_nil_r. exact Hnew.
    - exact Hgt. }
  rewrite lex_compare_app in Hmixed by exact Hchild_len.
  destruct (lex_compare child1 child2) eqn:Hchild_cmp.
  - exact (scalar_aware_prefix_gt_implies_active_decrease
             mask band1 band2 root_tiles1 root_tiles2 Hroot_mono
             root1 root2 Hroot1 Hroot2 Hmixed).
  - discriminate.
  - exact (scalar_aware_prefix_gt_implies_active_decrease
             mask band1 band2 child_tiles1 child_tiles2 Hchild_mono
             child1 child2 Hchild1 Hchild2 Hchild_cmp).
Qed.

Definition semantic_scalar_rows_reversal_bridge
    (mask: list bool) (envv: list Z)
    (before_pis after_pis: list Tiling.PL.PolyInstr)
    (ws: list statement_tiling_witness) (rows: list Schedule) : Prop :=
  let pis := Tiling.compose_tiling_pinstrs_ext_from_after
               (List.length envv) before_pis after_pis ws in
  forall flat ip1 ip2,
    Tiling.PL.flatten_instrs_ext envv pis flat ->
    In ip1 flat -> In ip2 flat ->
    Tiling.PL.instr_point_ext_old_sched_lt ip1 ip2 ->
    Tiling.PL.instr_point_ext_new_sched_ge ip1 ip2 ->
    exists pi1 pi2 rows1 rows2 dim,
      nth_error pis (Tiling.PL.ip_nth_ext ip1) = Some pi1 /\
      nth_error pis (Tiling.PL.ip_nth_ext ip2) = Some pi2 /\
      nth_error rows (Tiling.PL.ip_nth_ext ip1) = Some rows1 /\
      nth_error rows (Tiling.PL.ip_nth_ext ip2) = Some rows2 /\
      (dim < max_schedule_length rows)%nat /\
      (dim < List.length mask)%nat /\
      listz_pointwise_le
        (select_scalar_values (firstn dim mask)
          (firstn dim (affine_product rows2 (Tiling.PL.ip_index_ext ip2))))
        (select_scalar_values (firstn dim mask)
          (firstn dim (affine_product rows1 (Tiling.PL.ip_index_ext ip1)))) /\
      (semantic_band_value (List.length envv + Tiling.PL.pi_depth_ext pi1)
         dim rows1 (Tiling.PL.ip_index_ext ip1) >
       semantic_band_value (List.length envv + Tiling.PL.pi_depth_ext pi2)
         dim rows2 (Tiling.PL.ip_index_ext ip2))%Z.

(** The phase-aware second-level bridge combines phase-class separation with
    the two-level monotonicity argument.  The proof keeps these obligations
    separate: phase equality identifies the local layout; quotient
    monotonicity then reduces any reversal to a decreasing checked row. *)
Lemma phase_semantic_second_level_band_shape_scalar_reversal_bridge :
  forall before_pis before_ctxt before_vars after_pis ws shape envv,
    List.length before_ctxt = List.length envv ->
    TilingCheck.check_pprog_tiling_sourceb
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars) ws = true ->
    phase_semantic_second_level_band_shape_property
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars) ws shape ->
    semantic_scalar_rows_reversal_bridge (pssbs_loop_mask shape)
      envv before_pis after_pis ws (pssbs_full_rows shape).
Proof.
  (* Stage 1: recover the phase mask and globally aligned root/child layouts. *)
  intros before_pis before_ctxt before_vars after_pis ws
         shape envv Hlen_env Hsource Hshape.
  unfold phase_semantic_second_level_band_shape_property in Hshape.
  cbn in Hshape.
  destruct Hshape as [_ [_ Hshape]].
  destruct Hshape as [Hrecipes Hshape].
  destruct Hshape as [Hglobal_root_sizes Hshape].
  destruct Hshape as [Hglobal_child_sizes Hshape].
  destruct Hshape as [Hrows_eq Hshape].
  destruct Hshape as [Hloop_mask Hshape].
  destruct Hshape as [Hfull Hshape].
  destruct Hshape as [_ Hshape].
  destruct Hshape as [Hglobal_root_width Hshape].
  destruct Hshape as [Hglobal_child_width Hshape].
  destruct Hshape as [_ Hschedules].
  pose proof
    (TilingCheck.check_pprog_tiling_sourceb_sound
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars) ws Hsource)
    as [Hprog [_ [Hwf_ws [Hpositive_ws Hdepths]]]].
  assert
    (Hwf_ws_env :
       Forall
         (Tiling.wf_statement_tiling_witness_with_param_dim
            (List.length envv))
         ws).
  {
    rewrite <- Hlen_env.
    exact Hwf_ws.
  }
  assert
    (Hroot_prefixes :
       Forall
         (fun local =>
            prefix_sizes local (pssbs_global_root_sizes shape))
         (List.map slbr_root_sizes (pssbs_recipes shape))).
  {
    eapply infer_global_prefix_sizes_sound.
    exact Hglobal_root_sizes.
  }
  assert
    (Hchild_prefixes :
       Forall
         (fun local =>
            prefix_sizes local (pssbs_global_child_sizes shape))
         (List.map slbr_child_sizes (pssbs_recipes shape))).
  {
    eapply infer_global_prefix_sizes_sound.
    exact Hglobal_child_sizes.
  }
  pose proof
    (parse_second_level_semantic_recipes_positive
       ws (pssbs_recipes shape) Hrecipes Hpositive_ws)
    as Hrecipes_positive.
  assert
    (Hglobal_root_positive :
       Forall (fun size => (0 < size)%Z)
         (pssbs_global_root_sizes shape)).
  {
    eapply infer_global_prefix_sizes_positive.
    - exact Hglobal_root_sizes.
    - apply Forall_forall.
      intros local Hin.
      apply in_map_iff in Hin.
      destruct Hin as [recipe [Heq Hin]].
      subst local.
      eapply Forall_forall in Hrecipes_positive; eauto.
      tauto.
  }
  assert
    (Hglobal_child_positive :
       Forall (fun size => (0 < size)%Z)
         (pssbs_global_child_sizes shape)).
  {
    eapply infer_global_prefix_sizes_positive.
    - exact Hglobal_child_sizes.
    - apply Forall_forall.
      intros local Hin.
      apply in_map_iff in Hin.
      destruct Hin as [recipe [Heq Hin]].
      subst local.
      eapply Forall_forall in Hrecipes_positive; eauto.
      tauto.
  }
  assert
    (Hrecipes_len :
       List.length (pssbs_recipes shape) = List.length ws).
  {
    eapply parse_second_level_semantic_recipes_length.
    exact Hrecipes.
  }
  assert
    (Hsemantic_rows_len :
       List.length (pssbs_rows shape) = List.length before_pis).
  {
    rewrite Hrows_eq, List.map_length, Hrecipes_len.
    symmetry.
    eapply Forall2_length.
    exact Hdepths.
  }
  destruct
    (phase_semantic_full_schedules_for_tiling_length
       (List.length before_ctxt) (pssbs_loop_mask shape)
       before_pis ws (pssbs_full_rows shape) Hfull)
    as [Hfull_rows_len _].
  (* Stage 2: recover the two reversal endpoints and their second-level
     statement recipes. *)
  unfold semantic_scalar_rows_reversal_bridge.
  intros flat ip1 ip2 Hflat Hin1 Hin2 Hold Hnew.
  destruct
    (composed_point_pair_facts_of_members
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       ws envv flat ip1 ip2
       Hprog Hwf_ws_env Hpositive_ws Hdepths Hflat Hin1 Hin2)
    as [Hpoint1 Hpoint2].
  unfold composed_point_facts in Hpoint1, Hpoint2.
  destruct Hpoint1 as [before_pi1 [after_pi1 [w1
    [Hbefore1 [Hafter1 [Hw1
    [Hwf_stmt1 [Hpositive1 [Hpoint_depth1
    [Hpref1 [Hbel1 Hidx_len1]]]]]]]]]]].
  destruct Hpoint2 as [before_pi2 [after_pi2 [w2
    [Hbefore2 [Hafter2 [Hw2
    [Hwf_stmt2 [Hpositive2 [Hpoint_depth2
    [Hpref2 [Hbel2 Hidx_len2]]]]]]]]]]].
  assert
    (Hn1 : (Tiling.PL.ip_nth_ext ip1 < List.length ws)%nat).
  {
    apply nth_error_Some.
    rewrite Hw1.
    discriminate.
  }
  assert
    (Hn2 : (Tiling.PL.ip_nth_ext ip2 < List.length ws)%nat).
  {
    apply nth_error_Some.
    rewrite Hw2.
    discriminate.
  }
  destruct
    (nth_error (pssbs_recipes shape) (Tiling.PL.ip_nth_ext ip1))
    as [recipe1|] eqn:Hrecipe1.
  2:{ exfalso. apply nth_error_None in Hrecipe1. lia. }
  destruct
    (nth_error (pssbs_recipes shape) (Tiling.PL.ip_nth_ext ip2))
    as [recipe2|] eqn:Hrecipe2.
  2:{ exfalso. apply nth_error_None in Hrecipe2. lia. }
  pose proof
    (parse_second_level_semantic_recipes_nth_error
       ws (pssbs_recipes shape) (Tiling.PL.ip_nth_ext ip1)
       w1 recipe1 Hrecipes Hw1 Hrecipe1)
    as Hrecipe_parse1.
  pose proof
    (parse_second_level_semantic_recipes_nth_error
       ws (pssbs_recipes shape) (Tiling.PL.ip_nth_ext ip2)
       w2 recipe2 Hrecipes Hw2 Hrecipe2)
    as Hrecipe_parse2.
  destruct
    (second_level_band_recipe_of_witness_sound
       w1 recipe1 Hrecipe_parse1)
    as [Hlinks_nonempty1 Hspec1].
  destruct
    (second_level_band_recipe_of_witness_sound
       w2 recipe2 Hrecipe_parse2)
    as [Hlinks_nonempty2 Hspec2].
  destruct (second_level_band_recipe_spec_lengths _ _ _ _ Hspec1)
    as [Hroot_len1 Hchild_len1].
  destruct (second_level_band_recipe_spec_lengths _ _ _ _ Hspec2)
    as [Hroot_len2 Hchild_len2].
  assert
    (Hraw_map1 :
       nth_error
         (List.map slbr_root_rows (pssbs_recipes shape))
         (Tiling.PL.ip_nth_ext ip1) =
       Some (slbr_root_rows recipe1)).
  {
    eapply Tiling.nth_error_map_some.
    exact Hrecipe1.
  }
  assert
    (Hraw_map2 :
       nth_error
         (List.map slbr_root_rows (pssbs_recipes shape))
         (Tiling.PL.ip_nth_ext ip2) =
       Some (slbr_root_rows recipe2)).
  {
    eapply Tiling.nth_error_map_some.
    exact Hrecipe2.
  }
  assert
    (Hroot_sizes_map1 :
       nth_error
         (List.map slbr_root_sizes (pssbs_recipes shape))
         (Tiling.PL.ip_nth_ext ip1) =
       Some (slbr_root_sizes recipe1)).
  {
    eapply Tiling.nth_error_map_some.
    exact Hrecipe1.
  }
  assert
    (Hroot_sizes_map2 :
       nth_error
         (List.map slbr_root_sizes (pssbs_recipes shape))
         (Tiling.PL.ip_nth_ext ip2) =
       Some (slbr_root_sizes recipe2)).
  {
    eapply Tiling.nth_error_map_some.
    exact Hrecipe2.
  }
  assert
    (Hchild_sizes_map1 :
       nth_error
         (List.map slbr_child_sizes (pssbs_recipes shape))
         (Tiling.PL.ip_nth_ext ip1) =
       Some (slbr_child_sizes recipe1)).
  {
    eapply Tiling.nth_error_map_some.
    exact Hrecipe1.
  }
  assert
    (Hchild_sizes_map2 :
       nth_error
         (List.map slbr_child_sizes (pssbs_recipes shape))
         (Tiling.PL.ip_nth_ext ip2) =
       Some (slbr_child_sizes recipe2)).
  {
    eapply Tiling.nth_error_map_some.
    exact Hrecipe2.
  }
  pose proof
    (Tiling.Forall_nth_error
       _ _ (List.map slbr_root_sizes (pssbs_recipes shape))
       (Tiling.PL.ip_nth_ext ip1) (slbr_root_sizes recipe1)
       Hroot_prefixes Hroot_sizes_map1)
    as Hroot_prefix1.
  pose proof
    (Tiling.Forall_nth_error
       _ _ (List.map slbr_root_sizes (pssbs_recipes shape))
       (Tiling.PL.ip_nth_ext ip2) (slbr_root_sizes recipe2)
       Hroot_prefixes Hroot_sizes_map2)
    as Hroot_prefix2.
  pose proof
    (Tiling.Forall_nth_error
       _ _ (List.map slbr_child_sizes (pssbs_recipes shape))
       (Tiling.PL.ip_nth_ext ip1) (slbr_child_sizes recipe1)
       Hchild_prefixes Hchild_sizes_map1)
    as Hchild_prefix1.
  pose proof
    (Tiling.Forall_nth_error
       _ _ (List.map slbr_child_sizes (pssbs_recipes shape))
       (Tiling.PL.ip_nth_ext ip2) (slbr_child_sizes recipe2)
       Hchild_prefixes Hchild_sizes_map2)
    as Hchild_prefix2.
  destruct
    (nth_error (pssbs_rows shape) (Tiling.PL.ip_nth_ext ip1))
    as [semantic_rows1|] eqn:Hsemantic_rows1.
  2:{
    exfalso.
    apply nth_error_None in Hsemantic_rows1.
    assert
      (Hlt : (Tiling.PL.ip_nth_ext ip1 < List.length before_pis)%nat).
    { apply nth_error_Some. rewrite Hbefore1. discriminate. }
    lia.
  }
  destruct
    (nth_error (pssbs_rows shape) (Tiling.PL.ip_nth_ext ip2))
    as [semantic_rows2|] eqn:Hsemantic_rows2.
  2:{
    exfalso.
    apply nth_error_None in Hsemantic_rows2.
    assert
      (Hlt : (Tiling.PL.ip_nth_ext ip2 < List.length before_pis)%nat).
    { apply nth_error_Some. rewrite Hbefore2. discriminate. }
    lia.
  }
  destruct
    (nth_error (pssbs_full_rows shape) (Tiling.PL.ip_nth_ext ip1))
    as [full_rows1|] eqn:Hfull_rows1.
  2:{
    exfalso.
    apply nth_error_None in Hfull_rows1.
    assert
      (Hlt : (Tiling.PL.ip_nth_ext ip1 < List.length before_pis)%nat).
    { apply nth_error_Some. rewrite Hbefore1. discriminate. }
    lia.
  }
  destruct
    (nth_error (pssbs_full_rows shape) (Tiling.PL.ip_nth_ext ip2))
    as [full_rows2|] eqn:Hfull_rows2.
  2:{
    exfalso.
    apply nth_error_None in Hfull_rows2.
    assert
      (Hlt : (Tiling.PL.ip_nth_ext ip2 < List.length before_pis)%nat).
    { apply nth_error_Some. rewrite Hbefore2. discriminate. }
    lia.
  }
  assert (Hsemantic_raw1 : semantic_rows1 = slbr_root_rows recipe1).
  {
    rewrite Hrows_eq, Hraw_map1 in Hsemantic_rows1.
    inversion Hsemantic_rows1.
    reflexivity.
  }
  assert (Hsemantic_raw2 : semantic_rows2 = slbr_root_rows recipe2).
  {
    rewrite Hrows_eq, Hraw_map2 in Hsemantic_rows2.
    inversion Hsemantic_rows2.
    reflexivity.
  }
  destruct
    (phase_semantic_second_schedules_equivalent_pair_lex
       (List.length before_ctxt) (pssbs_loop_mask shape)
       before_pis after_pis ws (pssbs_recipes shape)
       (pssbs_rows shape)
       (Tiling.PL.ip_nth_ext ip1) (Tiling.PL.ip_nth_ext ip2)
       before_pi1 after_pi1 w1 recipe1 semantic_rows1
       before_pi2 after_pi2 w2 recipe2 semantic_rows2
       (Tiling.PL.ip_index_ext ip1) (Tiling.PL.ip_index_ext ip2)
       Hschedules
       Hbefore1 Hafter1 Hw1 Hrecipe1 Hsemantic_rows1
       Hbefore2 Hafter2 Hw2 Hrecipe2 Hsemantic_rows2)
    as [Hsource_match1
        [Hsource_match2
        [expected1 [expected2
        [Hexpected1 [Hexpected2 Htarget_lex]]]]]].
  rewrite Hsemantic_raw1 in Hsource_match1.
  rewrite Hsemantic_raw2 in Hsource_match2.
  pose proof
    (phase_semantic_full_schedules_nth_error
       (List.length before_ctxt) (pssbs_loop_mask shape)
       before_pis ws (pssbs_full_rows shape)
       (Tiling.PL.ip_nth_ext ip1) before_pi1 w1 full_rows1
       Hfull Hbefore1 Hw1 Hfull_rows1)
    as Hfull_def1.
  pose proof
    (phase_semantic_full_schedules_nth_error
       (List.length before_ctxt) (pssbs_loop_mask shape)
       before_pis ws (pssbs_full_rows shape)
       (Tiling.PL.ip_nth_ext ip2) before_pi2 w2 full_rows2
       Hfull Hbefore2 Hw2 Hfull_rows2)
    as Hfull_def2.
  pose proof
    (Tiling.nth_error_compose_tiling_pinstrs_ext_from_after
       (List.length envv) before_pis after_pis ws
       (Tiling.PL.ip_nth_ext ip1)
       before_pi1 after_pi1 w1 Hbefore1 Hafter1 Hw1)
    as Hcomposed1.
  pose proof
    (Tiling.nth_error_compose_tiling_pinstrs_ext_from_after
       (List.length envv) before_pis after_pis ws
       (Tiling.PL.ip_nth_ext ip2)
       before_pi2 after_pi2 w2 Hbefore2 Hafter2 Hw2)
    as Hcomposed2.
  pose proof
    (Tiling.tiling_rel_pprog_structure_source_nth
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       (List.map Tiling.compiled_pinstr_tiling_witness ws)
       (Tiling.PL.ip_nth_ext ip1)
       before_pi1 after_pi1
       (Tiling.compiled_pinstr_tiling_witness w1)
       Hprog Hbefore1 Hafter1
       (Tiling.nth_error_map_some
          _ _ Tiling.compiled_pinstr_tiling_witness
          ws (Tiling.PL.ip_nth_ext ip1) w1 Hw1))
    as Hstmt1.
  pose proof
    (Tiling.tiling_rel_pprog_structure_source_nth
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       (List.map Tiling.compiled_pinstr_tiling_witness ws)
       (Tiling.PL.ip_nth_ext ip2)
       before_pi2 after_pi2
       (Tiling.compiled_pinstr_tiling_witness w2)
       Hprog Hbefore2 Hafter2
       (Tiling.nth_error_map_some
          _ _ Tiling.compiled_pinstr_tiling_witness
          ws (Tiling.PL.ip_nth_ext ip2) w2 Hw2))
    as Hstmt2.
  assert
    (Hafter_depth1 :
       Tiling.PL.pi_depth after_pi1 =
       (Tiling.PL.pi_depth before_pi1 +
        List.length (stw_links w1))%nat).
  {
    unfold Tiling.tiling_rel_pinstr_structure_source in Hstmt1.
    destruct Hstmt1 as [_ [Hdepth _]].
    exact Hdepth.
  }
  assert
    (Hafter_depth2 :
       Tiling.PL.pi_depth after_pi2 =
       (Tiling.PL.pi_depth before_pi2 +
        List.length (stw_links w2))%nat).
  {
    unfold Tiling.tiling_rel_pinstr_structure_source in Hstmt2.
    destruct Hstmt2 as [_ [Hdepth _]].
    exact Hdepth.
  }
  (* Stage 3: evaluate the phase prefix, child tiles, root tiles, and source
     band for both endpoints in a common coordinate decomposition. *)
  set
    (added1 :=
       Tiling.tiled_added_part
         (List.length envv) (List.length (stw_links w1))
         (Tiling.PL.ip_index_ext ip1)).
  set
    (point1 :=
       Tiling.tiled_point_part
         (List.length envv) (List.length (stw_links w1))
         (Tiling.PL.ip_index_ext ip1)).
  set
    (added2 :=
       Tiling.tiled_added_part
         (List.length envv) (List.length (stw_links w2))
         (Tiling.PL.ip_index_ext ip2)).
  set
    (point2 :=
       Tiling.tiled_point_part
         (List.length envv) (List.length (stw_links w2))
         (Tiling.PL.ip_index_ext ip2)).
  assert (Hadded_len1 : List.length added1 = List.length (stw_links w1)).
  {
    subst added1.
    eapply Tiling.tiled_added_part_length
      with (point_dim := stw_point_dim w1).
    rewrite Hidx_len1, Hafter_depth1, <- Hpoint_depth1.
    lia.
  }
  assert (Hadded_len2 : List.length added2 = List.length (stw_links w2)).
  {
    subst added2.
    eapply Tiling.tiled_added_part_length
      with (point_dim := stw_point_dim w2).
    rewrite Hidx_len2, Hafter_depth2, <- Hpoint_depth2.
    lia.
  }
  assert (Hpoint_len1 : List.length point1 = stw_point_dim w1).
  {
    subst point1.
    eapply Tiling.tiled_point_part_length
      with (added_dims := List.length (stw_links w1)).
    rewrite Hidx_len1, Hafter_depth1, <- Hpoint_depth1.
    lia.
  }
  assert (Hpoint_len2 : List.length point2 = stw_point_dim w2).
  {
    subst point2.
    eapply Tiling.tiled_point_part_length
      with (added_dims := List.length (stw_links w2)).
    rewrite Hidx_len2, Hafter_depth2, <- Hpoint_depth2.
    lia.
  }
  assert
    (Hidx_split1 :
       Tiling.PL.ip_index_ext ip1 = envv ++ added1 ++ point1).
  {
    subst added1 point1.
    transitivity
      (firstn (List.length envv) (Tiling.PL.ip_index_ext ip1) ++
       Tiling.tiled_added_part
         (List.length envv) (List.length (stw_links w1))
         (Tiling.PL.ip_index_ext ip1) ++
       Tiling.tiled_point_part
         (List.length envv) (List.length (stw_links w1))
         (Tiling.PL.ip_index_ext ip1)).
    - apply Tiling.tiled_index_split.
    - rewrite Hpref1.
      reflexivity.
  }
  assert
    (Hidx_split2 :
       Tiling.PL.ip_index_ext ip2 = envv ++ added2 ++ point2).
  {
    subst added2 point2.
    transitivity
      (firstn (List.length envv) (Tiling.PL.ip_index_ext ip2) ++
       Tiling.tiled_added_part
         (List.length envv) (List.length (stw_links w2))
         (Tiling.PL.ip_index_ext ip2) ++
       Tiling.tiled_point_part
         (List.length envv) (List.length (stw_links w2))
         (Tiling.PL.ip_index_ext ip2)).
    - apply Tiling.tiled_index_split.
    - rewrite Hpref2.
      reflexivity.
  }
  unfold Tiling.compose_tiling_pinstr_ext in Hbel1, Hbel2.
  destruct Hbel1 as
    [Hafter_dom1 [_ [_ [Hts11 [Hts21 [_ _]]]]]].
  destruct Hbel2 as
    [Hafter_dom2 [_ [_ [Hts12 [Hts22 [_ _]]]]]].
  assert
    (Hts11_old :
       Tiling.PL.ip_time_stamp1_ext ip1 =
       affine_product (Tiling.PL.pi_schedule before_pi1)
         (envv ++ point1)).
  {
    rewrite Hts11.
    cbn [Tiling.compose_tiling_pinstr_ext].
    rewrite Hidx_split1.
    unfold Tiling.lift_schedule_after_env.
    eapply Tiling.lift_affine_function_after_env_eval.
    - reflexivity.
    - exact Hadded_len1.
  }
  assert
    (Hts12_old :
       Tiling.PL.ip_time_stamp1_ext ip2 =
       affine_product (Tiling.PL.pi_schedule before_pi2)
         (envv ++ point2)).
  {
    rewrite Hts12.
    cbn [Tiling.compose_tiling_pinstr_ext].
    rewrite Hidx_split2.
    unfold Tiling.lift_schedule_after_env.
    eapply Tiling.lift_affine_function_after_env_eval.
    - reflexivity.
    - exact Hadded_len2.
  }
  assert
    (Hts21_after :
       Tiling.PL.ip_time_stamp2_ext ip1 =
       affine_product (Tiling.PL.pi_schedule after_pi1)
         (Tiling.PL.ip_index_ext ip1)).
  {
    rewrite Hts21.
    cbn [Tiling.compose_tiling_pinstr_ext].
    reflexivity.
  }
  assert
    (Hts22_after :
       Tiling.PL.ip_time_stamp2_ext ip2 =
       affine_product (Tiling.PL.pi_schedule after_pi2)
         (Tiling.PL.ip_index_ext ip2)).
  {
    rewrite Hts22.
    cbn [Tiling.compose_tiling_pinstr_ext].
    reflexivity.
  }
  assert
    (Hstmt1_env :
       Tiling.tiling_rel_pinstr_structure_source
         (List.length envv) before_pi1 after_pi1
         (Tiling.compiled_pinstr_tiling_witness w1)).
  {
    rewrite <- Hlen_env.
    exact Hstmt1.
  }
  assert
    (Hstmt2_env :
       Tiling.tiling_rel_pinstr_structure_source
         (List.length envv) before_pi2 after_pi2
         (Tiling.compiled_pinstr_tiling_witness w2)).
  {
    rewrite <- Hlen_env.
    exact Hstmt2.
  }
  destruct Hwf_stmt1 as [Hwf_stmt1 Hparams1].
  destruct Hwf_stmt2 as [Hwf_stmt2 Hparams2].
  assert
    (Hadded_eq1 :
       added1 = eval_tile_links [] point1 envv (stw_links w1)).
  {
    pose proof
      (Tiling.tiling_rel_pinstr_structure_source_domain_complete
         envv before_pi1 after_pi1
         (Tiling.compiled_pinstr_tiling_witness w1)
         added1 point1 Hstmt1_env
         (Tiling.wf_compiled_pinstr_tiling_witness w1)
         (Tiling.compiled_pinstr_tiling_witness_matches w1)
         Hadded_len1 Hpoint_len1
         (conj Hwf_stmt1 Hparams1) Hpositive1)
      as Hcomplete.
    rewrite Hidx_split1 in Hafter_dom1.
    specialize (Hcomplete Hafter_dom1).
    tauto.
  }
  assert
    (Hadded_eq2 :
       added2 = eval_tile_links [] point2 envv (stw_links w2)).
  {
    pose proof
      (Tiling.tiling_rel_pinstr_structure_source_domain_complete
         envv before_pi2 after_pi2
         (Tiling.compiled_pinstr_tiling_witness w2)
         added2 point2 Hstmt2_env
         (Tiling.wf_compiled_pinstr_tiling_witness w2)
         (Tiling.compiled_pinstr_tiling_witness_matches w2)
         Hadded_len2 Hpoint_len2
         (conj Hwf_stmt2 Hparams2) Hpositive2)
      as Hcomplete.
    rewrite Hidx_split2 in Hafter_dom2.
    specialize (Hcomplete Hafter_dom2).
    tauto.
  }
  assert
    (Hlinks_len1 :
       List.length (stw_links w1) =
       (2 * List.length (slbr_root_rows recipe1))%nat).
  {
    eapply second_level_band_recipe_spec_links_length.
    exact Hspec1.
  }
  assert
    (Hlinks_len2 :
       List.length (stw_links w2) =
       (2 * List.length (slbr_root_rows recipe2))%nat).
  {
    eapply second_level_band_recipe_spec_links_length.
    exact Hspec2.
  }
  assert
    (Hbefore_bound1 :
       (List.length (Tiling.PL.pi_schedule before_pi1) <=
        List.length (pssbs_loop_mask shape))%nat).
  {
    rewrite Hloop_mask.
    eapply phase_semantic_source_schedule_bound.
    exact Hbefore1.
  }
  assert
    (Hbefore_bound2 :
       (List.length (Tiling.PL.pi_schedule before_pi2) <=
        List.length (pssbs_loop_mask shape))%nat).
  {
    rewrite Hloop_mask.
    eapply phase_semantic_source_schedule_bound.
    exact Hbefore2.
  }
  assert
    (Hlocal_width1 :
       (List.length (slbr_root_rows recipe1) <=
        count_true (pssbs_loop_mask shape))%nat).
  {
    destruct Hroot_prefix1 as [Hwidth Hprefix_values].
    rewrite <- Hroot_len1 in Hwidth.
    rewrite Hglobal_root_width in Hwidth.
    exact Hwidth.
  }
  assert
    (Hlocal_width2 :
       (List.length (slbr_root_rows recipe2) <=
        count_true (pssbs_loop_mask shape))%nat).
  {
    destruct Hroot_prefix2 as [Hwidth Hprefix_values].
    rewrite <- Hroot_len2 in Hwidth.
    rewrite Hglobal_root_width in Hwidth.
    exact Hwidth.
  }
  pose proof
    (phase_semantic_second_added_tiles_eq
       (List.length before_ctxt) (pssbs_loop_mask shape)
       before_pi1 w1 recipe1
       (pssbs_global_root_sizes shape)
       (pssbs_global_child_sizes shape)
       envv point1 added1 (eq_sym Hlen_env) Hpoint_len1
       Hspec1 Hroot_prefix1 Hchild_prefix1
       Hglobal_root_width Hglobal_child_width Hbefore_bound1
       Hwf_stmt1 Hparams1 Hsource_match1 Hadded_eq1)
    as [Hchild_added1 Hroot_added1].
  pose proof
    (phase_semantic_second_added_tiles_eq
       (List.length before_ctxt) (pssbs_loop_mask shape)
       before_pi2 w2 recipe2
       (pssbs_global_root_sizes shape)
       (pssbs_global_child_sizes shape)
       envv point2 added2 (eq_sym Hlen_env) Hpoint_len2
       Hspec2 Hroot_prefix2 Hchild_prefix2
       Hglobal_root_width Hglobal_child_width Hbefore_bound2
       Hwf_stmt2 Hparams2 Hsource_match2 Hadded_eq2)
    as [Hchild_added2 Hroot_added2].
  destruct
    (phase_semantic_second_level_target_schedule_eval
       (List.length before_ctxt) (pssbs_loop_mask shape)
       before_pi1 w1 recipe1 expected1 envv added1 point1
       Hexpected1 (eq_sym Hlen_env)
       (eq_trans Hadded_len1 Hlinks_len1) Hpoint_len1 Hlocal_width1)
    as [band_values1 [child_values1 [root_values1
        [Hband_values1 [Hchild_render1
        [Hroot_render1 Htarget_eval1]]]]]].
  destruct
    (phase_semantic_second_level_target_schedule_eval
       (List.length before_ctxt) (pssbs_loop_mask shape)
       before_pi2 w2 recipe2 expected2 envv added2 point2
       Hexpected2 (eq_sym Hlen_env)
       (eq_trans Hadded_len2 Hlinks_len2) Hpoint_len2 Hlocal_width2)
    as [band_values2 [child_values2 [root_values2
        [Hband_values2 [Hchild_render2
        [Hroot_render2 Htarget_eval2]]]]]].
  rewrite Hchild_added1 in Hchild_render1.
  rewrite Hroot_added1 in Hroot_render1.
  rewrite Hchild_added2 in Hchild_render2.
  rewrite Hroot_added2 in Hroot_render2.
  rewrite <- Hband_values1 in Hchild_render1, Hroot_render1.
  rewrite <- Hband_values2 in Hchild_render2, Hroot_render2.
  assert
    (Hband_len1 :
       List.length band_values1 =
       List.length (pssbs_loop_mask shape)).
  {
    rewrite Hband_values1.
    unfold affine_product,
           phase_semantic_padded_source_schedule,
           Tiling.PL.pad_schedule_to_len.
    rewrite List.map_length, app_length, repeat_length.
    lia.
  }
  assert
    (Hband_len2 :
       List.length band_values2 =
       List.length (pssbs_loop_mask shape)).
  {
    rewrite Hband_values2.
    unfold affine_product,
           phase_semantic_padded_source_schedule,
           Tiling.PL.pad_schedule_to_len.
    rewrite List.map_length, app_length, repeat_length.
    lia.
  }
  assert
    (Hselected_len1 :
       List.length
         (select_by_mask
            (pssbs_loop_mask shape) band_values1) =
       List.length (pssbs_global_root_sizes shape)).
  {
    rewrite
      (select_by_mask_length_count_true
         Z (pssbs_loop_mask shape) band_values1 Hband_len1).
    symmetry.
    exact Hglobal_root_width.
  }
  assert
    (Hroot_tile_monotone :
       scalar_aware_loop_tiles_monotone
         (pssbs_loop_mask shape) band_values1 band_values2
         (scalar_aware_loop_tile_values
            (pssbs_loop_mask shape) band_values1
            (pssbs_global_root_sizes shape))
         (scalar_aware_loop_tile_values
            (pssbs_loop_mask shape) band_values2
            (pssbs_global_root_sizes shape))).
  {
    eapply scalar_aware_loop_tile_values_monotone.
    - exact Hband_len1.
    - exact Hband_len2.
    - exact Hselected_len1.
    - exact Hglobal_root_positive.
  }
  assert
    (Hglobal_roots_len1 :
       List.length
         (scalar_aware_loop_tile_values
            (pssbs_loop_mask shape) band_values1
            (pssbs_global_root_sizes shape)) =
       List.length (pssbs_global_child_sizes shape)).
  {
    unfold scalar_aware_loop_tile_values.
    rewrite List.map_length, combine_length,
            Hselected_len1, Nat.min_id.
    lia.
  }
  pose proof
    (scalar_aware_loop_tiles_monotone_quotient
       (pssbs_loop_mask shape) band_values1 band_values2
       (scalar_aware_loop_tile_values
          (pssbs_loop_mask shape) band_values1
          (pssbs_global_root_sizes shape))
       (scalar_aware_loop_tile_values
          (pssbs_loop_mask shape) band_values2
          (pssbs_global_root_sizes shape))
       (pssbs_global_child_sizes shape)
       Hroot_tile_monotone Hglobal_roots_len1 Hglobal_child_positive)
    as Hchild_tile_monotone.
  assert
    (Htiles_eq :
       band_values1 = band_values2 ->
       child_values1 ++ root_values1 =
       child_values2 ++ root_values2).
  {
    intro Hband_eq.
    subst band_values2.
    assert (Hchild_eq : child_values1 = child_values2) by congruence.
    assert (Hroot_eq : root_values1 = root_values2) by congruence.
    subst child_values2 root_values2.
    reflexivity.
  }
  assert
    (Htiles_mono :
       listz_pointwise_le band_values1 band_values2 ->
       listz_pointwise_le
         (child_values1 ++ root_values1)
         (child_values2 ++ root_values2)).
  {
    intro Hband_le.
    apply listz_pointwise_le_app.
    - eapply render_scalar_aware_value_prefix_pointwise_le.
      + exact Hchild_tile_monotone.
      + exact Hband_le.
      + exact Hchild_render1.
      + exact Hchild_render2.
    - eapply render_scalar_aware_value_prefix_pointwise_le.
      + exact Hroot_tile_monotone.
      + exact Hband_le.
      + exact Hroot_render1.
      + exact Hroot_render2.
  }
  assert
    (Hold_eq1 :
       is_eq
         (Tiling.PL.ip_time_stamp1_ext ip1)
         band_values1 = true).
  {
    rewrite Hts11_old, Hband_values1.
    unfold phase_semantic_padded_source_schedule.
    rewrite
      (affine_product_pad_schedule_to_len
         (List.length before_ctxt + Tiling.PL.pi_depth before_pi1)
         (List.length (pssbs_loop_mask shape))
         (Tiling.PL.pi_schedule before_pi1)
         (envv ++ point1) Hbefore_bound1).
    rewrite is_eq_commutative.
    apply is_eq_app_repeat_zero.
  }
  assert
    (Hold_eq2 :
       is_eq
         (Tiling.PL.ip_time_stamp1_ext ip2)
         band_values2 = true).
  {
    rewrite Hts12_old, Hband_values2.
    unfold phase_semantic_padded_source_schedule.
    rewrite
      (affine_product_pad_schedule_to_len
         (List.length before_ctxt + Tiling.PL.pi_depth before_pi2)
         (List.length (pssbs_loop_mask shape))
         (Tiling.PL.pi_schedule before_pi2)
         (envv ++ point2) Hbefore_bound2).
    rewrite is_eq_commutative.
    apply is_eq_app_repeat_zero.
  }
  assert
    (Hold_lex :
       lex_compare
         (Tiling.PL.ip_time_stamp1_ext ip1)
         (Tiling.PL.ip_time_stamp1_ext ip2) =
       lex_compare band_values1 band_values2).
  {
    transitivity
      (lex_compare
         band_values1
         (Tiling.PL.ip_time_stamp1_ext ip2)).
    - apply lex_compare_left_eq.
      exact Hold_eq1.
    - apply lex_compare_right_eq.
      exact Hold_eq2.
  }
  assert
    (Hnew_lex :
       lex_compare
         (Tiling.PL.ip_time_stamp2_ext ip1)
         (Tiling.PL.ip_time_stamp2_ext ip2) =
       lex_compare
         ((child_values1 ++ root_values1) ++ band_values1)
         ((child_values2 ++ root_values2) ++ band_values2)).
  {
    rewrite Hts21_after, Hts22_after.
    rewrite Htarget_lex.
    rewrite Hidx_split1, Hidx_split2.
    rewrite Htarget_eval1, Htarget_eval2.
    repeat rewrite app_assoc.
    reflexivity.
  }
  (* Stage 4: the phase-aware two-level tile prefix is monotone; therefore a
     target reversal exposes a decreasing source-band component. *)
  unfold Tiling.PL.instr_point_ext_old_sched_lt in Hold.
  assert
    (Hnew_not_lt :
       lex_compare
         (Tiling.PL.ip_time_stamp2_ext ip1)
         (Tiling.PL.ip_time_stamp2_ext ip2) <> Lt).
  {
    unfold Tiling.PL.instr_point_ext_new_sched_ge in Hnew.
    destruct Hnew; congruence.
  }
  rewrite Hold_lex in Hold.
  rewrite Hnew_lex in Hnew_not_lt.
  destruct
    (scalar_aware_two_level_reversal_active
       (pssbs_loop_mask shape) band_values1 band_values2
       _ _ _ _ child_values1 child_values2 root_values1 root_values2
       Hband_len1 Hband_len2 Hchild_tile_monotone Hroot_tile_monotone
       Hchild_render1 Hchild_render2 Hroot_render1 Hroot_render2
       Hold Hnew_not_lt)
    as [dim [x [y [Hdim_mask [Hvalue1 [Hvalue2 [Hdecrease Hprior]]]]]]].
  (* Stage 5: transfer that component to the full lifted rows checked by the
     executable direct validator. *)
  assert
    (Hfull_eval1 :
       affine_product full_rows1 (Tiling.PL.ip_index_ext ip1) =
       band_values1).
  {
    rewrite Hfull_def1, Hidx_split1.
    unfold phase_semantic_lifted_band_rows.
    transitivity
      (affine_product
         (phase_semantic_padded_source_schedule
            (List.length before_ctxt)
            (List.length (pssbs_loop_mask shape)) before_pi1)
         (envv ++ point1)).
    - eapply Tiling.lift_affine_function_after_env_eval.
      + exact (eq_sym Hlen_env).
      + exact Hadded_len1.
    - symmetry.
      exact Hband_values1.
  }
  assert
    (Hfull_eval2 :
       affine_product full_rows2 (Tiling.PL.ip_index_ext ip2) =
       band_values2).
  {
    rewrite Hfull_def2, Hidx_split2.
    unfold phase_semantic_lifted_band_rows.
    transitivity
      (affine_product
         (phase_semantic_padded_source_schedule
            (List.length before_ctxt)
            (List.length (pssbs_loop_mask shape)) before_pi2)
         (envv ++ point2)).
    - eapply Tiling.lift_affine_function_after_env_eval.
      + exact (eq_sym Hlen_env).
      + exact Hadded_len2.
    - symmetry.
      exact Hband_values2.
  }
  assert
    (Hfull_len1 :
       List.length band_values1 = List.length full_rows1).
  {
    rewrite <- Hfull_eval1.
    unfold affine_product.
    rewrite List.map_length.
    reflexivity.
  }
  exists
    (Tiling.compose_tiling_pinstr_ext
       (List.length envv) before_pi1 after_pi1 w1),
    (Tiling.compose_tiling_pinstr_ext
       (List.length envv) before_pi2 after_pi2 w2),
    full_rows1, full_rows2, dim.
  repeat split; try assumption.
  - eapply Nat.lt_le_trans.
    + apply nth_error_Some.
      rewrite Hvalue1.
      discriminate.
    + rewrite Hfull_len1.
      eapply max_schedule_length_ge_nth_error.
      exact Hfull_rows1.
  - rewrite Hfull_eval1, Hfull_eval2. exact Hprior.
  - assert
      (Hsemantic_value1 :
         semantic_band_value
           (List.length envv +
            Tiling.PL.pi_depth_ext
              (Tiling.compose_tiling_pinstr_ext
                 (List.length envv) before_pi1 after_pi1 w1))
           dim full_rows1 (Tiling.PL.ip_index_ext ip1) = x).
    {
      eapply semantic_band_value_of_nth_error.
      rewrite Hfull_eval1.
      exact Hvalue1.
    }
    assert
      (Hsemantic_value2 :
         semantic_band_value
           (List.length envv +
            Tiling.PL.pi_depth_ext
              (Tiling.compose_tiling_pinstr_ext
                 (List.length envv) before_pi2 after_pi2 w2))
           dim full_rows2 (Tiling.PL.ip_index_ext ip2) = y).
    {
      eapply semantic_band_value_of_nth_error.
      rewrite Hfull_eval2.
      exact Hvalue2.
    }
    rewrite Hsemantic_value1, Hsemantic_value2.
    exact Hdecrease.
Qed.

Lemma phase_semantic_second_level_band_shape_reversal_bridge :
  forall before_pis before_ctxt before_vars after_pis ws shape envv,
    List.length before_ctxt = List.length envv ->
    TilingCheck.check_pprog_tiling_sourceb
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars) ws = true ->
    phase_semantic_second_level_band_shape_property
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars) ws shape ->
    semantic_rows_reversal_bridge
      envv before_pis after_pis ws (pssbs_full_rows shape).
Proof.
  intros before_pis before_ctxt before_vars after_pis ws shape envv
         Hlen Hsource Hshape flat ip1 ip2 Hflat Hin1 Hin2 Hold Hnew.
  destruct (phase_semantic_second_level_band_shape_scalar_reversal_bridge
              _ _ _ _ _ _ _ Hlen Hsource Hshape
              flat ip1 ip2 Hflat Hin1 Hin2 Hold Hnew)
    as [pi1 [pi2 [rows1 [rows2 [dim
         [Hp1 [Hp2 [Hr1 [Hr2 [Hd [_ [_ Hdec]]]]]]]]]]]].
  exists pi1, pi2, rows1, rows2, dim.
  repeat split; assumption.
Qed.

Lemma phase_semantic_ordinary_band_direct_reordering_safe :
  forall before_pis before_ctxt before_vars after_pis ws shape envv,
    List.length before_ctxt = List.length envv ->
    TilingCheck.check_pprog_tiling_sourceb
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars) ws = true ->
    phase_semantic_ordinary_band_shape_property
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars) ws shape ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      after_pis ->
    mayReturn
      (check_semantic_band_components_direct
         (Tiling.compose_tiling_pinstrs_ext_from_after
            (List.length before_ctxt) before_pis after_pis ws)
         (psobs_full_rows shape) (List.length before_ctxt))
      true ->
    pprog_tiling_reordering_safe envv before_pis after_pis ws [].
Proof.
  intros before_pis before_ctxt before_vars after_pis ws shape envv
         Hlen_env Hsource Hshape Hwf_before Hwf_after Hcomponents.
  pose proof
    (TilingCheck.check_pprog_tiling_sourceb_sound
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars) ws Hsource)
    as [Hprog [_ [Hwf_ws [_ Hdepths]]]].
  assert
    (Hwits :
       Forall2 Tiling.after_matches_tiling_witness after_pis ws).
  {
    eapply
      (tiling_rel_pprog_structure_source_after_matches
         before_pis before_ctxt before_vars
         after_pis before_ctxt before_vars ws);
      eauto.
  }
  assert
    (Hcomposed_wf :
       Forall
         (Tiling.PL.wf_pinstr_ext_tiling before_ctxt)
         (Tiling.compose_tiling_pinstrs_ext_from_after
            (List.length before_ctxt) before_pis after_pis ws)).
  {
    eapply compose_tiling_pinstrs_ext_from_after_wf_tiling; eauto.
  }
  pose proof Hshape as Hshape_bridge.
  unfold phase_semantic_ordinary_band_shape_property in Hshape.
  cbn in Hshape.
  destruct Hshape as
    [_ [_ [data [_ [_ [_ [_ [Hfull _]]]]]]]].
  assert
    (Hfull_cols :
       Forall2
         (fun w rows =>
            exact_listzzs_cols
              (List.length before_ctxt + List.length (stw_links w) +
               stw_point_dim w)%nat rows)
         ws (psobs_full_rows shape)).
  {
    eapply phase_semantic_full_schedules_for_tiling_exact_cols;
      eauto.
  }
  assert
    (Hcomposed_cols :
       Forall2
         (fun pi rows =>
            exact_listzzs_cols
              (List.length before_ctxt +
               Tiling.PL.pi_depth_ext pi)%nat rows)
         (Tiling.compose_tiling_pinstrs_ext_from_after
            (List.length before_ctxt) before_pis after_pis ws)
         (psobs_full_rows shape)).
  {
    eapply composed_semantic_rows_exact_cols; eauto.
  }
  assert
    (Hcomponentwise :
       pinstr_list_semantic_componentwise_permutable
         envv
         (Tiling.compose_tiling_pinstrs_ext_from_after
            (List.length before_ctxt) before_pis after_pis ws)
         (psobs_full_rows shape)).
  {
    eapply
      (check_semantic_band_components_direct_sound
         before_ctxt envv
         (Tiling.compose_tiling_pinstrs_ext_from_after
            (List.length before_ctxt) before_pis after_pis ws)
         (psobs_full_rows shape)); eauto.
  }
  eapply semantic_componentwise_permutable_implies_reordering_safe.
  - rewrite Hlen_env in Hcomponentwise.
    exact Hcomponentwise.
  - eapply phase_semantic_ordinary_band_shape_reversal_bridge; eauto.
Qed.

Lemma phase_semantic_second_level_band_direct_reordering_safe :
  forall before_pis before_ctxt before_vars after_pis ws shape envv,
    List.length before_ctxt = List.length envv ->
    TilingCheck.check_pprog_tiling_sourceb
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars) ws = true ->
    phase_semantic_second_level_band_shape_property
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars) ws shape ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      after_pis ->
    mayReturn
      (check_semantic_band_components_direct
         (Tiling.compose_tiling_pinstrs_ext_from_after
            (List.length before_ctxt) before_pis after_pis ws)
         (pssbs_full_rows shape) (List.length before_ctxt))
      true ->
    pprog_tiling_reordering_safe envv before_pis after_pis ws [].
Proof.
  intros before_pis before_ctxt before_vars after_pis ws shape envv
         Hlen_env Hsource Hshape Hwf_before Hwf_after Hcomponents.
  pose proof
    (TilingCheck.check_pprog_tiling_sourceb_sound
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars) ws Hsource)
    as [Hprog [_ [Hwf_ws [_ Hdepths]]]].
  assert
    (Hwits :
       Forall2 Tiling.after_matches_tiling_witness after_pis ws).
  {
    eapply
      (tiling_rel_pprog_structure_source_after_matches
         before_pis before_ctxt before_vars
         after_pis before_ctxt before_vars ws);
      eauto.
  }
  assert
    (Hcomposed_wf :
       Forall
         (Tiling.PL.wf_pinstr_ext_tiling before_ctxt)
         (Tiling.compose_tiling_pinstrs_ext_from_after
            (List.length before_ctxt) before_pis after_pis ws)).
  {
    eapply compose_tiling_pinstrs_ext_from_after_wf_tiling; eauto.
  }
  pose proof Hshape as Hshape_bridge.
  unfold phase_semantic_second_level_band_shape_property in Hshape.
  cbn in Hshape.
  destruct Hshape as [_ [_ Hshape]].
  destruct Hshape as [_ Hshape].
  destruct Hshape as [_ Hshape].
  destruct Hshape as [_ Hshape].
  destruct Hshape as [_ Hshape].
  destruct Hshape as [_ Hshape].
  destruct Hshape as [Hfull _].
  assert
    (Hfull_cols :
       Forall2
         (fun w rows =>
            exact_listzzs_cols
              (List.length before_ctxt + List.length (stw_links w) +
               stw_point_dim w)%nat rows)
         ws (pssbs_full_rows shape)).
  {
    eapply phase_semantic_full_schedules_for_tiling_exact_cols;
      eauto.
  }
  assert
    (Hcomposed_cols :
       Forall2
         (fun pi rows =>
            exact_listzzs_cols
              (List.length before_ctxt +
               Tiling.PL.pi_depth_ext pi)%nat rows)
         (Tiling.compose_tiling_pinstrs_ext_from_after
            (List.length before_ctxt) before_pis after_pis ws)
         (pssbs_full_rows shape)).
  {
    eapply composed_semantic_rows_exact_cols; eauto.
  }
  assert
    (Hcomponentwise :
       pinstr_list_semantic_componentwise_permutable
         envv
         (Tiling.compose_tiling_pinstrs_ext_from_after
            (List.length before_ctxt) before_pis after_pis ws)
         (pssbs_full_rows shape)).
  {
    eapply
      (check_semantic_band_components_direct_sound
         before_ctxt envv
         (Tiling.compose_tiling_pinstrs_ext_from_after
            (List.length before_ctxt) before_pis after_pis ws)
         (pssbs_full_rows shape)); eauto.
  }
  eapply semantic_componentwise_permutable_implies_reordering_safe.
  - rewrite Hlen_env in Hcomponentwise.
    exact Hcomponentwise.
  - eapply phase_semantic_second_level_band_shape_reversal_bridge; eauto.
Qed.

Lemma checked_tiling_sourceb_phase_semantic_band_direct_correct_same_ctxt :
  forall before_pis before_ctxt before_vars after_pis ws st1 st2,
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      after_pis ->
    mayReturn
      (checked_tiling_sourceb_phase_semantic_band_direct
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars) ws)
      true ->
    Tiling.PL.instance_list_semantics
      (after_pis, before_ctxt, before_vars) st1 st2 ->
    exists st2',
      Tiling.PL.instance_list_semantics
        (before_pis, before_ctxt, before_vars) st1 st2' /\
      TilingPolIRs.State.eq st2 st2'.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws st1 st2
         Hwf_before Hwf_after Hcheck Hsem.
  unfold checked_tiling_sourceb_phase_semantic_band_direct in Hcheck.
  cbn beta iota zeta in Hcheck.
  destruct
    (TilingCheck.check_pprog_tiling_sourceb
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars) ws)
    eqn:Hsource.
  2:{ apply mayReturn_pure in Hcheck. discriminate. }
  destruct
    (infer_pprog_phase_semantic_ordinary_band_shape
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars) ws)
    as [ordinary_shape|] eqn:Hordinary.
  - pose proof
      (infer_pprog_phase_semantic_ordinary_band_shape_sound
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars) ws
         ordinary_shape Hordinary)
      as Hshape.
    eapply
      (tiling_sourceb_validate_correct_with_reordering
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars)
         ws [] st1 st2); [exact Hsource| |exact Hsem].
    simpl.
    intros envv Hlen_env.
    eapply
      (phase_semantic_ordinary_band_direct_reordering_safe
         before_pis before_ctxt before_vars after_pis ws
         ordinary_shape envv); eauto.
  - destruct
      (infer_pprog_phase_semantic_second_level_band_shape
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars) ws)
      as [second_shape|] eqn:Hsecond.
    2:{ apply mayReturn_pure in Hcheck. discriminate. }
    pose proof
      (infer_pprog_phase_semantic_second_level_band_shape_sound
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars) ws
         second_shape Hsecond)
      as Hshape.
    eapply
      (tiling_sourceb_validate_correct_with_reordering
         (before_pis, before_ctxt, before_vars)
         (after_pis, before_ctxt, before_vars)
         ws [] st1 st2); [exact Hsource| |exact Hsem].
    simpl.
    intros envv Hlen_env.
    eapply
      (phase_semantic_second_level_band_direct_reordering_safe
         before_pis before_ctxt before_vars after_pis ws
         second_shape envv); eauto.
Qed.

Lemma checked_tiling_sourceb_phase_semantic_band_direct_sourceb_true :
  forall before after ws,
    mayReturn
      (checked_tiling_sourceb_phase_semantic_band_direct before after ws)
      true ->
    TilingCheck.check_pprog_tiling_sourceb before after ws = true.
Proof.
  intros [[before_pis before_ctxt] before_vars]
         [[after_pis after_ctxt] after_vars] ws Hcheck.
  unfold checked_tiling_sourceb_phase_semantic_band_direct in Hcheck.
  cbn beta iota zeta in Hcheck.
  destruct
    (TilingCheck.check_pprog_tiling_sourceb
       (before_pis, before_ctxt, before_vars)
       (after_pis, after_ctxt, after_vars) ws)
    eqn:Hsource.
  - reflexivity.
  - apply mayReturn_pure in Hcheck.
    discriminate.
Qed.

Fixpoint check_rows_are_source_schedulesb
    (pis: list Tiling.PL.PolyInstr_ext) (rows: list Schedule) : bool :=
  match pis, rows with
  | [], [] => true
  | pi :: pis', row :: rows' =>
      listzzs_strict_eqb (Tiling.PL.pi_schedule1_ext pi) row &&
      check_rows_are_source_schedulesb pis' rows'
  | _, _ => false
  end.

Lemma check_rows_are_source_schedulesb_nth :
  forall pis rows n pi row,
    check_rows_are_source_schedulesb pis rows = true ->
    nth_error pis n = Some pi -> nth_error rows n = Some row ->
    row = Tiling.PL.pi_schedule1_ext pi.
Proof.
  induction pis as [|head pis IH];
    intros rows n pi row Hcheck Hp Hr;
    destruct rows as [|headrow rows]; cbn in Hcheck; try discriminate.
  - destruct n; discriminate.
  - apply andb_true_iff in Hcheck. destruct Hcheck as [Hhead Htail].
    destruct n as [|n]; cbn in Hp, Hr.
    + inversion Hp; inversion Hr; subst.
      symmetry. apply listzzs_strict_eqb_eq. exact Hhead.
    + eapply IH; eauto.
Qed.

Lemma semantic_band_value_dimension_irrelevant :
  forall n m dim rows idx,
    semantic_band_value n dim rows idx = semantic_band_value m dim rows idx.
Proof.
  intros n m dim rows idx.
  unfold semantic_band_value, semantic_band_row.
  destruct (nth_error rows dim); [reflexivity|].
  unfold zero_schedule_row. cbn.
  rewrite !dot_product_repeat_zero_left. reflexivity.
Qed.

Lemma semantic_scalar_rows_to_source_bridge :
  forall mask envv before_pis after_pis ws rows,
    check_rows_are_source_schedulesb
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length envv) before_pis after_pis ws) rows = true ->
    semantic_scalar_rows_reversal_bridge
      mask envv before_pis after_pis ws rows ->
    scalar_aware_reversal_bridge envv before_pis after_pis ws
      {| sabl_start := O; sabl_loop_mask := mask |}.
Proof.
  intros mask envv before_pis after_pis ws rows Hrows Hbridge
         flat ip1 ip2 Hflat Hin1 Hin2 Hold Hnew.
  destruct (Hbridge flat ip1 ip2 Hflat Hin1 Hin2 Hold Hnew)
    as [pi1 [pi2 [rows1 [rows2 [dim
         [Hp1 [Hp2 [Hr1 [Hr2 [_ [Hdim [Hprior Hdec]]]]]]]]]]]].
  pose proof (check_rows_are_source_schedulesb_nth
                _ _ _ _ _ Hrows Hp1 Hr1) as Hrow1.
  pose proof (check_rows_are_source_schedulesb_nth
                _ _ _ _ _ Hrows Hp2 Hr2) as Hrow2.
  subst rows1 rows2.
  exists pi1, pi2, dim.
  split; [exact Hp1|]. split; [exact Hp2|]. split; [exact Hdim|].
  unfold scalar_aware_component_active. cbn.
  split; [reflexivity|]. split.
  - rewrite !affine_product_select_scalar_rows,
            !affine_product_firstn_local. exact Hprior.
  - rewrite (semantic_band_value_dimension_irrelevant
               (List.length (Tiling.PL.ip_index_ext ip1))
               (List.length envv + Tiling.PL.pi_depth_ext pi1)).
    rewrite (semantic_band_value_dimension_irrelevant
               (List.length (Tiling.PL.ip_index_ext ip2))
               (List.length envv + Tiling.PL.pi_depth_ext pi2)).
    exact Hdec.
Qed.

(** This additional direct path retains the already-proved scalar guards.
    The exact-row check excludes source padding that the older semantic path
    alone handles; those cases retain that path as a separate alternative. *)
Definition checked_tiling_sourceb_phase_scalar_second_direct
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness) : imp bool :=
  let '(before_pis, before_ctxt, _) := before in
  let '(after_pis, _, _) := after in
  if TilingCheck.check_pprog_tiling_sourceb before after ws then
    match infer_pprog_phase_semantic_second_level_band_shape before after ws with
    | None => pure false
    | Some shape =>
        if check_rows_are_source_schedulesb
             (Tiling.compose_tiling_pinstrs_ext_from_after
                (List.length before_ctxt) before_pis after_pis ws)
             (pssbs_full_rows shape)
        then check_pprog_scalar_aware_permutable_band_direct before after ws
               {| sabl_start := O; sabl_loop_mask := pssbs_loop_mask shape |}
        else pure false
    end
  else pure false.

Lemma checked_tiling_sourceb_phase_scalar_second_direct_true_inv :
  forall before_pis before_ctxt before_vars after_pis after_ctxt after_vars ws,
    mayReturn
      (checked_tiling_sourceb_phase_scalar_second_direct
         (before_pis, before_ctxt, before_vars)
         (after_pis, after_ctxt, after_vars) ws) true ->
    exists shape,
      TilingCheck.check_pprog_tiling_sourceb
        (before_pis, before_ctxt, before_vars)
        (after_pis, after_ctxt, after_vars) ws = true /\
      infer_pprog_phase_semantic_second_level_band_shape
        (before_pis, before_ctxt, before_vars)
        (after_pis, after_ctxt, after_vars) ws = Some shape /\
      check_rows_are_source_schedulesb
        (Tiling.compose_tiling_pinstrs_ext_from_after
           (List.length before_ctxt) before_pis after_pis ws)
        (pssbs_full_rows shape) = true /\
      mayReturn (check_pprog_scalar_aware_permutable_band_direct
        (before_pis, before_ctxt, before_vars)
        (after_pis, after_ctxt, after_vars) ws
        {| sabl_start := O; sabl_loop_mask := pssbs_loop_mask shape |}) true.
Proof.
  intros before_pis before_ctxt before_vars after_pis after_ctxt after_vars ws H.
  unfold checked_tiling_sourceb_phase_scalar_second_direct in H.
  cbn beta iota zeta in H.
  destruct (TilingCheck.check_pprog_tiling_sourceb _ _ ws) eqn:Hs;
    [|apply mayReturn_pure in H; discriminate].
  destruct (infer_pprog_phase_semantic_second_level_band_shape _ _ ws)
    as [shape|] eqn:Hshape;
    [|apply mayReturn_pure in H; discriminate].
  destruct (check_rows_are_source_schedulesb _ _) eqn:Hr;
    [|apply mayReturn_pure in H; discriminate].
  exists shape. repeat split; assumption.
Qed.

Lemma checked_tiling_sourceb_phase_scalar_second_direct_reordering_safe :
  forall before_pis before_ctxt before_vars after_pis ws envv,
    List.length before_ctxt = List.length envv ->
    Forall (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars) before_pis ->
    Forall (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars) after_pis ->
    mayReturn (checked_tiling_sourceb_phase_scalar_second_direct
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars) ws) true ->
    pprog_tiling_reordering_safe envv before_pis after_pis ws [].
Proof.
  intros before_pis before_ctxt before_vars after_pis ws envv
         Hlen Hwf_before Hwf_after Hcheck.
  destruct (checked_tiling_sourceb_phase_scalar_second_direct_true_inv
              _ _ _ _ _ _ _ Hcheck)
    as [shape [Hsource [Hinfer [Hrows Hcomponents]]]].
  pose proof (infer_pprog_phase_semantic_second_level_band_shape_sound
                _ _ _ _ Hinfer) as Hshape.
  pose proof (TilingCheck.check_pprog_tiling_sourceb_sound
                _ _ _ Hsource)
    as [Hprog [_ [Hwf_ws [_ Hdepths]]]].
  assert (Hwits : Forall2 Tiling.after_matches_tiling_witness after_pis ws).
  { eapply tiling_rel_pprog_structure_source_after_matches; eauto. }
  assert (Hcomposed_wf : Forall (Tiling.PL.wf_pinstr_ext_tiling before_ctxt)
    (Tiling.compose_tiling_pinstrs_ext_from_after
       (List.length before_ctxt) before_pis after_pis ws)).
  { eapply compose_tiling_pinstrs_ext_from_after_wf_tiling; eauto. }
  assert (Hcomponentwise : pinstr_list_scalar_aware_componentwise_permutable
    envv (Tiling.compose_tiling_pinstrs_ext_from_after
            (List.length before_ctxt) before_pis after_pis ws)
    {| sabl_start := O; sabl_loop_mask := pssbs_loop_mask shape |}).
  { eapply (check_pprog_scalar_aware_permutable_band_direct_sound
              before_ctxt envv _ _ _ _ _ _ _ _);
      eauto. }
  eapply scalar_aware_componentwise_permutable_implies_reordering_safe.
  - rewrite Hlen in Hcomponentwise. exact Hcomponentwise.
  - eapply semantic_scalar_rows_to_source_bridge.
    + rewrite <- Hlen. exact Hrows.
    + eapply phase_semantic_second_level_band_shape_scalar_reversal_bridge;
        eauto.
Qed.

Lemma checked_tiling_sourceb_phase_scalar_second_direct_correct_same_ctxt :
  forall before_pis before_ctxt before_vars after_pis ws st1 st2,
    Forall (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars) before_pis ->
    Forall (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars) after_pis ->
    mayReturn (checked_tiling_sourceb_phase_scalar_second_direct
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars) ws) true ->
    Tiling.PL.instance_list_semantics (after_pis, before_ctxt, before_vars) st1 st2 ->
    exists st2', Tiling.PL.instance_list_semantics (before_pis, before_ctxt, before_vars) st1 st2'
                 /\ State.eq st2 st2'.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws st1 st2
         Hwf_before Hwf_after Hcheck Hsem.
  destruct (checked_tiling_sourceb_phase_scalar_second_direct_true_inv
              _ _ _ _ _ _ _ Hcheck) as [shape [Hsource _]].
  eapply (tiling_sourceb_validate_correct_with_reordering
            (before_pis, before_ctxt, before_vars)
            (after_pis, before_ctxt, before_vars) ws [] st1 st2);
    [exact Hsource| |exact Hsem].
  cbn. intros envv Hlen.
  eapply checked_tiling_sourceb_phase_scalar_second_direct_reordering_safe;
    eauto.
Qed.

Definition checked_tiling_sourceb_phase_semantic_extended_direct
    (before after: Tiling.PL.t) (ws: list statement_tiling_witness) : imp bool :=
  BIND scalar_ok <- checked_tiling_sourceb_phase_scalar_second_direct before after ws -;
  if scalar_ok then pure true
  else checked_tiling_sourceb_phase_semantic_band_direct before after ws.

Lemma checked_tiling_sourceb_phase_semantic_extended_direct_sourceb_true :
  forall before after ws,
    mayReturn (checked_tiling_sourceb_phase_semantic_extended_direct before after ws) true ->
    TilingCheck.check_pprog_tiling_sourceb before after ws = true.
Proof.
  intros [[bp bc] bv] [[ap ac] av] ws H.
  unfold checked_tiling_sourceb_phase_semantic_extended_direct in H.
  bind_imp_destruct H scalar_ok Hscalar. destruct scalar_ok.
  - destruct (checked_tiling_sourceb_phase_scalar_second_direct_true_inv
                _ _ _ _ _ _ _ Hscalar) as [shape [Hsource _]]. exact Hsource.
  - eapply checked_tiling_sourceb_phase_semantic_band_direct_sourceb_true; eauto.
Qed.

Lemma checked_tiling_sourceb_phase_semantic_extended_direct_correct_same_ctxt :
  forall before_pis before_ctxt before_vars after_pis ws st1 st2,
    Forall (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars) before_pis ->
    Forall (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars) after_pis ->
    mayReturn (checked_tiling_sourceb_phase_semantic_extended_direct
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars) ws) true ->
    Tiling.PL.instance_list_semantics (after_pis, before_ctxt, before_vars) st1 st2 ->
    exists st2', Tiling.PL.instance_list_semantics (before_pis, before_ctxt, before_vars) st1 st2'
                 /\ State.eq st2 st2'.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws st1 st2
         Hwf_before Hwf_after Hcheck Hsem.
  unfold checked_tiling_sourceb_phase_semantic_extended_direct in Hcheck.
  bind_imp_destruct Hcheck scalar_ok Hscalar. destruct scalar_ok.
  - eapply checked_tiling_sourceb_phase_scalar_second_direct_correct_same_ctxt; eauto.
  - eapply checked_tiling_sourceb_phase_semantic_band_direct_correct_same_ctxt; eauto.
Qed.

(** Local bands use the same second-level arithmetic as the whole-program
    phase shape, but keep the surrounding prefix and suffix exactly once. *)
Definition pinstr_with_schedule
    (pi: Tiling.PL.PolyInstr) (sched: Schedule) : Tiling.PL.PolyInstr :=
  {| Tiling.PL.pi_depth := Tiling.PL.pi_depth pi;
     Tiling.PL.pi_instr := Tiling.PL.pi_instr pi;
     Tiling.PL.pi_poly := Tiling.PL.pi_poly pi;
     Tiling.PL.pi_schedule := sched;
     Tiling.PL.pi_point_witness := Tiling.PL.pi_point_witness pi;
     Tiling.PL.pi_transformation := Tiling.PL.pi_transformation pi;
     Tiling.PL.pi_access_transformation := Tiling.PL.pi_access_transformation pi;
     Tiling.PL.pi_waccess := Tiling.PL.pi_waccess pi;
     Tiling.PL.pi_raccess := Tiling.PL.pi_raccess pi |}.

Definition scalar_aware_second_level_target_schedule
    (env_size: nat) (before_pi: Tiling.PL.PolyInstr)
    (w: statement_tiling_witness) (layout: scalar_aware_band_layout)
    (recipe: second_level_band_recipe) : option Schedule :=
  let local := pinstr_with_schedule before_pi
    (scalar_aware_layout_band_rows layout (Tiling.PL.pi_schedule before_pi)) in
  let lifted := Tiling.lift_schedule_after_env
    (List.length (stw_links w)) env_size (Tiling.PL.pi_schedule before_pi) in
  match phase_semantic_second_level_target_schedule
          env_size (sabl_loop_mask layout) local w recipe with
  | Some middle => Some
      (firstn (sabl_start layout) lifted ++ middle ++
       skipn (sabl_start layout + List.length (sabl_loop_mask layout)) lifted)
  | None => None
  end.

Definition scalar_aware_second_level_entry_shape
    (env_size: nat) (layout: scalar_aware_band_layout)
    (before_pi after_pi: Tiling.PL.PolyInstr)
    (w: statement_tiling_witness) : Prop :=
  exists recipe expected,
    second_level_band_recipe_of_witness w = Some recipe /\
    sabl_loop_mask layout <> [] /\
    List.length (scalar_aware_layout_band_rows layout
      (Tiling.PL.pi_schedule before_pi)) = List.length (sabl_loop_mask layout) /\
    select_by_mask (sabl_loop_mask layout)
      (scalar_aware_layout_band_rows layout (Tiling.PL.pi_schedule before_pi)) =
      slbr_root_rows recipe /\
    scalar_aware_second_level_target_schedule env_size before_pi w layout recipe =
      Some expected /\
    schedule_matches_with_symmetric_trailing_zero_padding expected (Tiling.PL.pi_schedule after_pi).

Definition infer_scalar_aware_second_level_band_layout
    (env_size: nat) (before: Tiling.PL.PolyInstr)
    (w: statement_tiling_witness) : option scalar_aware_band_layout :=
  match second_level_band_recipe_of_witness w with
  | Some recipe => find_scalar_aware_band_aux
      (S (List.length (Tiling.PL.pi_schedule before))) O env_size
      (Tiling.PL.pi_schedule before) (slbr_root_rows recipe)
  | None => None
  end.

Definition check_scalar_aware_second_level_entry_shapeb
    (env_size: nat) (layout: scalar_aware_band_layout)
    (before after: Tiling.PL.PolyInstr) (w: statement_tiling_witness) : bool :=
  match second_level_band_recipe_of_witness w with
  | Some recipe =>
      let rows := scalar_aware_layout_band_rows layout (Tiling.PL.pi_schedule before) in
      negb (Nat.eqb (List.length (sabl_loop_mask layout)) O) &&
      Nat.eqb (List.length rows) (List.length (sabl_loop_mask layout)) &&
      listzzs_strict_eqb (select_by_mask (sabl_loop_mask layout) rows)
                       (slbr_root_rows recipe) &&
      match scalar_aware_second_level_target_schedule env_size before w layout recipe with
      | Some expected => check_schedule_with_symmetric_trailing_zero_paddingb
                           expected (Tiling.PL.pi_schedule after)
      | None => false
      end
  | None => false
  end.

Lemma check_scalar_aware_second_level_entry_shapeb_sound :
  forall env_size layout before after w,
    check_scalar_aware_second_level_entry_shapeb env_size layout before after w = true ->
    scalar_aware_second_level_entry_shape env_size layout before after w.
Proof.
  intros env_size layout before after w H.
  unfold check_scalar_aware_second_level_entry_shapeb in H.
  destruct (second_level_band_recipe_of_witness w) as [recipe|] eqn:Hr;
    try discriminate.
  repeat rewrite andb_true_iff in H.
  destruct H as [[[Hnonempty Hlen] Hselected] Htarget].
  destruct (scalar_aware_second_level_target_schedule env_size before w layout recipe)
    as [expected|] eqn:He; try discriminate.
  exists recipe, expected. repeat split; try assumption.
  - apply negb_true_iff in Hnonempty. apply Nat.eqb_neq in Hnonempty.
    intro Hnil. rewrite Hnil in Hnonempty. contradiction.
  - apply Nat.eqb_eq. exact Hlen.
  - apply listzzs_strict_eqb_eq. exact Hselected.
  - apply check_schedule_with_symmetric_trailing_zero_paddingb_sound. exact Htarget.
Qed.

Lemma scalar_aware_second_level_entry_eval :
  forall env_size layout before w recipe expected envv added point,
    second_level_band_recipe_of_witness w = Some recipe ->
    List.length (scalar_aware_layout_band_rows layout (Tiling.PL.pi_schedule before)) =
      List.length (sabl_loop_mask layout) ->
    select_by_mask (sabl_loop_mask layout)
      (scalar_aware_layout_band_rows layout (Tiling.PL.pi_schedule before)) =
      slbr_root_rows recipe ->
    scalar_aware_second_level_target_schedule env_size before w layout recipe = Some expected ->
    List.length envv = env_size ->
    List.length added = List.length (stw_links w) ->
    List.length point = stw_point_dim w ->
    well_formed_statement_tiling_witness w ->
    Forall (fun link => List.length (ae_param_coeffs (tl_expr link)) = List.length envv)
      (stw_links w) ->
    added = eval_tile_links [] point envv (stw_links w) ->
    exists band child root,
      band = firstn (List.length (sabl_loop_mask layout))
        (skipn (sabl_start layout)
          (affine_product (Tiling.PL.pi_schedule before) (envv ++ point))) /\
      render_scalar_aware_value_prefix (sabl_loop_mask layout) band
        (semantic_quotient_tiles
          (scalar_aware_loop_tile_values (sabl_loop_mask layout) band (slbr_root_sizes recipe))
          (slbr_child_sizes recipe)) = Some child /\
      render_scalar_aware_value_prefix (sabl_loop_mask layout) band
        (scalar_aware_loop_tile_values (sabl_loop_mask layout) band (slbr_root_sizes recipe)) = Some root /\
      affine_product expected (envv ++ added ++ point) =
        firstn (sabl_start layout)
          (affine_product (Tiling.PL.pi_schedule before) (envv ++ point)) ++
        (child ++ root) ++ band ++
        skipn (sabl_start layout + List.length (sabl_loop_mask layout))
          (affine_product (Tiling.PL.pi_schedule before) (envv ++ point)).
Proof.
  intros env_size layout before w recipe expected envv added point
    Hrecipe Hband Hselected Hexpected Henv Hadded_len Hpoint Hwf Hparams Hadded.
  set (local := pinstr_with_schedule before
    (scalar_aware_layout_band_rows layout (Tiling.PL.pi_schedule before))).
  assert (Hpadded : phase_semantic_padded_source_schedule env_size
    (List.length (sabl_loop_mask layout)) local =
    scalar_aware_layout_band_rows layout (Tiling.PL.pi_schedule before)).
  {
    change (scalar_aware_layout_band_rows layout (Tiling.PL.pi_schedule before) ++
      repeat (Tiling.PL.zero_affine_function (env_size + Tiling.PL.pi_depth before))
        (List.length (sabl_loop_mask layout) -
         List.length (scalar_aware_layout_band_rows layout (Tiling.PL.pi_schedule before))) =
      scalar_aware_layout_band_rows layout (Tiling.PL.pi_schedule before)).
    rewrite Hband, Nat.sub_diag. simpl. apply app_nil_r.
  }
  destruct (second_level_band_recipe_of_witness_sound w recipe Hrecipe) as [_ Hspec].
  destruct (second_level_band_recipe_spec_lengths _ _ _ _ Hspec) as [Hrlen Hclen].
  assert (Hwidth : List.length (slbr_root_rows recipe) = count_true (sabl_loop_mask layout)).
  {
    rewrite <- Hselected. apply select_by_mask_length_count_true. exact Hband.
  }
  assert (Hrl : List.length (slbr_root_sizes recipe) = count_true (sabl_loop_mask layout)) by lia.
  assert (Hcl : List.length (slbr_child_sizes recipe) = count_true (sabl_loop_mask layout)) by lia.
  assert (Hmatch : schedule_matches_with_symmetric_trailing_zero_padding
    (slbr_root_rows recipe) (select_by_mask (sabl_loop_mask layout)
      (phase_semantic_padded_source_schedule env_size (List.length (sabl_loop_mask layout)) local))).
  {
    rewrite Hpadded, Hselected. left. exists O, O.
    unfold pad_schedule_with_zero_rows. simpl. symmetry. apply app_nil_r.
  }
  pose proof (phase_semantic_second_added_tiles_eq env_size (sabl_loop_mask layout)
    local w recipe (slbr_root_sizes recipe) (slbr_child_sizes recipe)
    envv point added Henv Hpoint Hspec (prefix_sizes_refl _) (prefix_sizes_refl _)
    Hrl Hcl ltac:(change (List.length (scalar_aware_layout_band_rows layout
      (Tiling.PL.pi_schedule before)) <= List.length (sabl_loop_mask layout))%nat; lia)
    Hwf Hparams Hmatch Hadded) as [Hchild_added Hroot_added].
  unfold scalar_aware_second_level_target_schedule in Hexpected.
  fold local in Hexpected.
  destruct (phase_semantic_second_level_target_schedule env_size (sabl_loop_mask layout)
    local w recipe) as [middle|] eqn:Hmiddle; try discriminate.
  inversion Hexpected; subst expected; clear Hexpected.
  assert (Hlinks : List.length (stw_links w) = (2 * List.length (slbr_root_rows recipe))%nat)
    by (eapply second_level_band_recipe_spec_links_length; exact Hspec).
  destruct (phase_semantic_second_level_target_schedule_eval env_size (sabl_loop_mask layout)
    local w recipe middle envv added point Hmiddle Henv (eq_trans Hadded_len Hlinks)
    Hpoint ltac:(lia)) as [band [child [root [Hb [Hc [Hr Heval]]]]]].
  rewrite Hchild_added in Hc. rewrite Hroot_added in Hr.
  rewrite <- Hb in Hc, Hr.
  rewrite Hpadded, affine_product_scalar_aware_layout_band_rows in Hb.
  exists band, child, root. split; [exact Hb|]. split; [exact Hc|]. split; [exact Hr|].
  rewrite !affine_product_app, affine_product_firstn, affine_product_skipn.
  unfold Tiling.lift_schedule_after_env.
  rewrite (Tiling.lift_affine_function_after_env_eval
    (List.length (stw_links w)) env_size (Tiling.PL.pi_schedule before)
    envv added point Henv Hadded_len).
  rewrite Heval. repeat rewrite app_assoc. reflexivity.
Qed.

Lemma scalar_aware_two_level_prefix_gt_active :
  forall mask band1 band2 child_tiles1 child_tiles2 root_tiles1 root_tiles2
    child1 child2 root1 root2,
    List.length band1 = List.length mask ->
    List.length band2 = List.length mask ->
    scalar_aware_loop_tiles_monotone mask band1 band2 child_tiles1 child_tiles2 ->
    scalar_aware_loop_tiles_monotone mask band1 band2 root_tiles1 root_tiles2 ->
    render_scalar_aware_value_prefix mask band1 child_tiles1 = Some child1 ->
    render_scalar_aware_value_prefix mask band2 child_tiles2 = Some child2 ->
    render_scalar_aware_value_prefix mask band1 root_tiles1 = Some root1 ->
    render_scalar_aware_value_prefix mask band2 root_tiles2 = Some root2 ->
    lex_compare (child1 ++ root1) (child2 ++ root2) = Gt ->
    exists dim x y, (dim < List.length mask)%nat /\
      nth_error band1 dim = Some x /\ nth_error band2 dim = Some y /\ (x > y)%Z /\
      listz_pointwise_le (select_scalar_values (firstn dim mask) (firstn dim band2))
        (select_scalar_values (firstn dim mask) (firstn dim band1)).
Proof.
  intros mask band1 band2 ct1 ct2 rt1 rt2 c1 c2 r1 r2 Hl1 Hl2 Hcm Hrm Hc1 Hc2 Hr1 Hr2 Hgt.
  assert (Hcl : List.length c1 = List.length c2).
  { rewrite (render_scalar_aware_value_prefix_length _ _ _ _ Hl1 Hc1),
      (render_scalar_aware_value_prefix_length _ _ _ _ Hl2 Hc2). reflexivity. }
  rewrite lex_compare_app in Hgt by exact Hcl.
  destruct (lex_compare c1 c2) eqn:Hcc; try discriminate.
  - exact (scalar_aware_prefix_gt_implies_active_decrease mask band1 band2 rt1 rt2
      Hrm r1 r2 Hr1 Hr2 Hgt).
  - exact (scalar_aware_prefix_gt_implies_active_decrease mask band1 band2 ct1 ct2
      Hcm c1 c2 Hc1 Hc2 Hcc).
Qed.

Lemma scalar_aware_second_level_pair_local_reversal_bridge_wf_with_env_len :
  forall before_pis before_ctxt before_vars after_pis ws layouts envv
         flat ip1 ip2,
    List.length before_ctxt = List.length envv ->
    TilingCheck.check_pprog_tiling_sourceb
      (before_pis, before_ctxt, before_vars)
      (after_pis, before_ctxt, before_vars) ws = true ->
    Forall
      (Tiling.PL.wf_pinstr_tiling before_ctxt before_vars)
      before_pis ->
    List.length layouts = List.length before_pis ->
    Tiling.PL.flatten_instrs_ext envv
      (Tiling.compose_tiling_pinstrs_ext_from_after
         (List.length envv) before_pis after_pis ws) flat ->
    In ip1 flat ->
    In ip2 flat ->
    Tiling.PL.instr_point_ext_old_sched_lt ip1 ip2 ->
    Tiling.PL.instr_point_ext_new_sched_ge ip1 ip2 ->
    (forall before_pi after_pi w layout,
       nth_error before_pis (Tiling.PL.ip_nth_ext ip1) = Some before_pi ->
       nth_error after_pis (Tiling.PL.ip_nth_ext ip1) = Some after_pi ->
       nth_error ws (Tiling.PL.ip_nth_ext ip1) = Some w ->
       nth_error layouts (Tiling.PL.ip_nth_ext ip1) = Some layout ->
       scalar_aware_second_level_entry_shape
         (List.length before_ctxt) layout before_pi after_pi w) ->
    (forall before_pi after_pi w layout,
       nth_error before_pis (Tiling.PL.ip_nth_ext ip2) = Some before_pi ->
       nth_error after_pis (Tiling.PL.ip_nth_ext ip2) = Some after_pi ->
       nth_error ws (Tiling.PL.ip_nth_ext ip2) = Some w ->
       nth_error layouts (Tiling.PL.ip_nth_ext ip2) = Some layout ->
       scalar_aware_second_level_entry_shape
         (List.length before_ctxt) layout before_pi after_pi w) ->
    (forall layout1 layout2,
       nth_error layouts (Tiling.PL.ip_nth_ext ip1) = Some layout1 ->
       nth_error layouts (Tiling.PL.ip_nth_ext ip2) = Some layout2 ->
       layout1 = layout2) ->
    (forall w1 w2 recipe1 recipe2,
       nth_error ws (Tiling.PL.ip_nth_ext ip1) = Some w1 ->
       nth_error ws (Tiling.PL.ip_nth_ext ip2) = Some w2 ->
       second_level_band_recipe_of_witness w1 = Some recipe1 ->
       second_level_band_recipe_of_witness w2 = Some recipe2 ->
       slbr_root_sizes recipe1 = slbr_root_sizes recipe2 /\
       slbr_child_sizes recipe1 = slbr_child_sizes recipe2) ->
    exists layout pi1 pi2 dim,
      nth_error layouts (Tiling.PL.ip_nth_ext ip1) = Some layout /\
      nth_error layouts (Tiling.PL.ip_nth_ext ip2) = Some layout /\
      nth_error
        (Tiling.compose_tiling_pinstrs_ext_from_after
           (List.length envv) before_pis after_pis ws)
        (Tiling.PL.ip_nth_ext ip1) = Some pi1 /\
      nth_error
        (Tiling.compose_tiling_pinstrs_ext_from_after
           (List.length envv) before_pis after_pis ws)
        (Tiling.PL.ip_nth_ext ip2) = Some pi2 /\
      (dim < List.length (sabl_loop_mask layout))%nat /\
      scalar_aware_component_active layout dim pi1 pi2 ip1 ip2.
Proof.
  intros before_pis before_ctxt before_vars after_pis ws layouts envv
         flat ip1 ip2 Hlen_env Hsource Hwf_before Hlayouts_len
         Hflat Hin1 Hin2 Hold Hnew Hshape_at1 Hshape_at2
         Hsame_layout Hsame_recipe.
  pose proof
    (TilingCheck.check_pprog_tiling_sourceb_sound
       (before_pis, before_ctxt, before_vars)
       (after_pis, before_ctxt, before_vars) ws Hsource)
    as [Hprog [_ [Hwf_ws [Hpositive_ws Hdepths]]]].
  assert
    (Hwf_ws_env :
       Forall
         (Tiling.wf_statement_tiling_witness_with_param_dim
            (List.length envv))
         ws).
  {
    rewrite <- Hlen_env.
    exact Hwf_ws.
  }
  destruct
    (composed_point_pair_facts_of_members
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       ws envv flat ip1 ip2
       Hprog Hwf_ws_env Hpositive_ws Hdepths Hflat Hin1 Hin2)
    as [Hpoint1 Hpoint2].
  unfold composed_point_facts in Hpoint1, Hpoint2.
  destruct Hpoint1 as [before_pi1 [after_pi1 [w1
    [Hbefore1 [Hafter1 [Hw1
    [Hwf_stmt1 [Hpositive1 [Hpoint_depth1
    [Hpref1 [Hbel1 Hidx_len1]]]]]]]]]]].
  destruct Hpoint2 as [before_pi2 [after_pi2 [w2
    [Hbefore2 [Hafter2 [Hw2
    [Hwf_stmt2 [Hpositive2 [Hpoint_depth2
    [Hpref2 [Hbel2 Hidx_len2]]]]]]]]]]].
  assert
    (Hlayout_idx1 :
       (Tiling.PL.ip_nth_ext ip1 < List.length layouts)%nat).
  {
    rewrite Hlayouts_len.
    apply nth_error_Some.
    rewrite Hbefore1.
    discriminate.
  }
  assert
    (Hlayout_idx2 :
       (Tiling.PL.ip_nth_ext ip2 < List.length layouts)%nat).
  {
    rewrite Hlayouts_len.
    apply nth_error_Some.
    rewrite Hbefore2.
    discriminate.
  }
  destruct
    (nth_error layouts (Tiling.PL.ip_nth_ext ip1))
    as [layout1|] eqn:Hlayout1.
  2:{
    apply nth_error_None in Hlayout1.
    lia.
  }
  destruct
    (nth_error layouts (Tiling.PL.ip_nth_ext ip2))
    as [layout2|] eqn:Hlayout2.
  2:{
    apply nth_error_None in Hlayout2.
    lia.
  }
  pose proof
    (Hsame_layout layout1 layout2 eq_refl eq_refl) as Hlayout_eq.
  subst layout2.
  rename layout1 into layout.
  destruct
    (Hshape_at1 before_pi1 after_pi1 w1 layout
       Hbefore1 Hafter1 Hw1 eq_refl)
    as [recipe1 [expected1
         [Hrecipe1 [Hmask_nonempty1
         [Hband_len1 [Hselected1
         [Hexpected1 Htarget1]]]]]]].
  destruct
    (Hshape_at2 before_pi2 after_pi2 w2 layout
       Hbefore2 Hafter2 Hw2 eq_refl)
    as [recipe2 [expected2
         [Hrecipe2 [Hmask_nonempty2
         [Hband_len2 [Hselected2
         [Hexpected2 Htarget2]]]]]]].
  destruct (Hsame_recipe w1 w2 recipe1 recipe2 Hw1 Hw2 Hrecipe1 Hrecipe2)
    as [Hroots_same Hchildren_same].
  destruct (second_level_band_recipe_of_witness_sound w1 recipe1 Hrecipe1) as [_ Hspec1].
  destruct (second_level_band_recipe_of_witness_sound w2 recipe2 Hrecipe2) as [_ Hspec2].
  pose proof
    (Tiling.nth_error_compose_tiling_pinstrs_ext_from_after
       (List.length envv) before_pis after_pis ws
       (Tiling.PL.ip_nth_ext ip1)
       before_pi1 after_pi1 w1 Hbefore1 Hafter1 Hw1)
    as Hcomposed1.
  pose proof
    (Tiling.nth_error_compose_tiling_pinstrs_ext_from_after
       (List.length envv) before_pis after_pis ws
       (Tiling.PL.ip_nth_ext ip2)
       before_pi2 after_pi2 w2 Hbefore2 Hafter2 Hw2)
    as Hcomposed2.
  pose proof
    (Tiling.tiling_rel_pprog_structure_source_nth
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       (List.map Tiling.compiled_pinstr_tiling_witness ws)
       (Tiling.PL.ip_nth_ext ip1)
       before_pi1 after_pi1
       (Tiling.compiled_pinstr_tiling_witness w1)
       Hprog Hbefore1 Hafter1
       (Tiling.nth_error_map_some
          _ _ Tiling.compiled_pinstr_tiling_witness
          ws (Tiling.PL.ip_nth_ext ip1) w1 Hw1))
    as Hstmt1.
  pose proof
    (Tiling.tiling_rel_pprog_structure_source_nth
       before_pis before_ctxt before_vars
       after_pis before_ctxt before_vars
       (List.map Tiling.compiled_pinstr_tiling_witness ws)
       (Tiling.PL.ip_nth_ext ip2)
       before_pi2 after_pi2
       (Tiling.compiled_pinstr_tiling_witness w2)
       Hprog Hbefore2 Hafter2
       (Tiling.nth_error_map_some
          _ _ Tiling.compiled_pinstr_tiling_witness
          ws (Tiling.PL.ip_nth_ext ip2) w2 Hw2))
    as Hstmt2.
  assert
    (Hafter_depth1 :
       Tiling.PL.pi_depth after_pi1 =
       (Tiling.PL.pi_depth before_pi1 +
        List.length (stw_links w1))%nat).
  {
    unfold Tiling.tiling_rel_pinstr_structure_source in Hstmt1.
    destruct Hstmt1 as [_ [Hdepth _]].
    exact Hdepth.
  }
  assert
    (Hafter_depth2 :
       Tiling.PL.pi_depth after_pi2 =
       (Tiling.PL.pi_depth before_pi2 +
        List.length (stw_links w2))%nat).
  {
    unfold Tiling.tiling_rel_pinstr_structure_source in Hstmt2.
    destruct Hstmt2 as [_ [Hdepth _]].
    exact Hdepth.
  }
  set
    (added1 :=
       Tiling.tiled_added_part
         (List.length envv) (List.length (stw_links w1))
         (Tiling.PL.ip_index_ext ip1)).
  set
    (point1 :=
       Tiling.tiled_point_part
         (List.length envv) (List.length (stw_links w1))
         (Tiling.PL.ip_index_ext ip1)).
  set
    (added2 :=
       Tiling.tiled_added_part
         (List.length envv) (List.length (stw_links w2))
         (Tiling.PL.ip_index_ext ip2)).
  set
    (point2 :=
       Tiling.tiled_point_part
         (List.length envv) (List.length (stw_links w2))
         (Tiling.PL.ip_index_ext ip2)).
  assert (Hadded_len1 : List.length added1 = List.length (stw_links w1)).
  {
    subst added1.
    eapply Tiling.tiled_added_part_length
      with (point_dim := stw_point_dim w1).
    rewrite Hidx_len1, Hafter_depth1, <- Hpoint_depth1.
    lia.
  }
  assert (Hadded_len2 : List.length added2 = List.length (stw_links w2)).
  {
    subst added2.
    eapply Tiling.tiled_added_part_length
      with (point_dim := stw_point_dim w2).
    rewrite Hidx_len2, Hafter_depth2, <- Hpoint_depth2.
    lia.
  }
  assert (Hpoint_len1 : List.length point1 = stw_point_dim w1).
  {
    subst point1.
    eapply Tiling.tiled_point_part_length
      with (added_dims := List.length (stw_links w1)).
    rewrite Hidx_len1, Hafter_depth1, <- Hpoint_depth1.
    lia.
  }
  assert (Hpoint_len2 : List.length point2 = stw_point_dim w2).
  {
    subst point2.
    eapply Tiling.tiled_point_part_length
      with (added_dims := List.length (stw_links w2)).
    rewrite Hidx_len2, Hafter_depth2, <- Hpoint_depth2.
    lia.
  }
  assert
    (Hidx_split1 :
       Tiling.PL.ip_index_ext ip1 = envv ++ added1 ++ point1).
  {
    subst added1 point1.
    transitivity
      (firstn (List.length envv) (Tiling.PL.ip_index_ext ip1) ++
       Tiling.tiled_added_part
         (List.length envv) (List.length (stw_links w1))
         (Tiling.PL.ip_index_ext ip1) ++
       Tiling.tiled_point_part
         (List.length envv) (List.length (stw_links w1))
         (Tiling.PL.ip_index_ext ip1)).
    - apply Tiling.tiled_index_split.
    - rewrite Hpref1. reflexivity.
  }
  assert
    (Hidx_split2 :
       Tiling.PL.ip_index_ext ip2 = envv ++ added2 ++ point2).
  {
    subst added2 point2.
    transitivity
      (firstn (List.length envv) (Tiling.PL.ip_index_ext ip2) ++
       Tiling.tiled_added_part
         (List.length envv) (List.length (stw_links w2))
         (Tiling.PL.ip_index_ext ip2) ++
       Tiling.tiled_point_part
         (List.length envv) (List.length (stw_links w2))
         (Tiling.PL.ip_index_ext ip2)).
    - apply Tiling.tiled_index_split.
    - rewrite Hpref2. reflexivity.
  }
  unfold Tiling.compose_tiling_pinstr_ext in Hbel1, Hbel2.
  destruct Hbel1 as
    [Hafter_dom1 [_ [_ [Hts11 [Hts21 [_ _]]]]]].
  destruct Hbel2 as
    [Hafter_dom2 [_ [_ [Hts12 [Hts22 [_ _]]]]]].
  assert
    (Hts11_old :
       Tiling.PL.ip_time_stamp1_ext ip1 =
       affine_product (Tiling.PL.pi_schedule before_pi1)
         (envv ++ point1)).
  {
    rewrite Hts11.
    cbn [Tiling.compose_tiling_pinstr_ext].
    rewrite Hidx_split1.
    unfold Tiling.lift_schedule_after_env.
    eapply Tiling.lift_affine_function_after_env_eval.
    - reflexivity.
    - exact Hadded_len1.
  }
  assert
    (Hts12_old :
       Tiling.PL.ip_time_stamp1_ext ip2 =
       affine_product (Tiling.PL.pi_schedule before_pi2)
         (envv ++ point2)).
  {
    rewrite Hts12.
    cbn [Tiling.compose_tiling_pinstr_ext].
    rewrite Hidx_split2.
    unfold Tiling.lift_schedule_after_env.
    eapply Tiling.lift_affine_function_after_env_eval.
    - reflexivity.
    - exact Hadded_len2.
  }
  assert
    (Hts21_after :
       Tiling.PL.ip_time_stamp2_ext ip1 =
       affine_product (Tiling.PL.pi_schedule after_pi1)
         (Tiling.PL.ip_index_ext ip1)).
  {
    rewrite Hts21.
    cbn [Tiling.compose_tiling_pinstr_ext].
    reflexivity.
  }
  assert
    (Hts22_after :
       Tiling.PL.ip_time_stamp2_ext ip2 =
       affine_product (Tiling.PL.pi_schedule after_pi2)
         (Tiling.PL.ip_index_ext ip2)).
  {
    rewrite Hts22.
    cbn [Tiling.compose_tiling_pinstr_ext].
    reflexivity.
  }
  assert
    (Hstmt1_env :
       Tiling.tiling_rel_pinstr_structure_source
         (List.length envv) before_pi1 after_pi1
         (Tiling.compiled_pinstr_tiling_witness w1)).
  {
    rewrite <- Hlen_env.
    exact Hstmt1.
  }
  assert
    (Hstmt2_env :
       Tiling.tiling_rel_pinstr_structure_source
         (List.length envv) before_pi2 after_pi2
         (Tiling.compiled_pinstr_tiling_witness w2)).
  {
    rewrite <- Hlen_env.
    exact Hstmt2.
  }
  destruct Hwf_stmt1 as [Hwf_stmt1 Hparams1].
  destruct Hwf_stmt2 as [Hwf_stmt2 Hparams2].
  assert
    (Hadded_eq1 :
       added1 = eval_tile_links [] point1 envv (stw_links w1)).
  {
    pose proof
      (Tiling.tiling_rel_pinstr_structure_source_domain_complete
         envv before_pi1 after_pi1
         (Tiling.compiled_pinstr_tiling_witness w1)
         added1 point1 Hstmt1_env
         (Tiling.wf_compiled_pinstr_tiling_witness w1)
         (Tiling.compiled_pinstr_tiling_witness_matches w1)
         Hadded_len1 Hpoint_len1
         (conj Hwf_stmt1 Hparams1) Hpositive1)
      as Hcomplete.
    rewrite Hidx_split1 in Hafter_dom1.
    specialize (Hcomplete Hafter_dom1).
    tauto.
  }
  assert
    (Hadded_eq2 :
       added2 = eval_tile_links [] point2 envv (stw_links w2)).
  {
    pose proof
      (Tiling.tiling_rel_pinstr_structure_source_domain_complete
         envv before_pi2 after_pi2
         (Tiling.compiled_pinstr_tiling_witness w2)
         added2 point2 Hstmt2_env
         (Tiling.wf_compiled_pinstr_tiling_witness w2)
         (Tiling.compiled_pinstr_tiling_witness_matches w2)
         Hadded_len2 Hpoint_len2
         (conj Hwf_stmt2 Hparams2) Hpositive2)
      as Hcomplete.
    rewrite Hidx_split2 in Hafter_dom2.
    specialize (Hcomplete Hafter_dom2).
    tauto.
  }
  destruct (scalar_aware_second_level_entry_eval
    (List.length before_ctxt) layout before_pi1 w1 recipe1 expected1 envv added1 point1
    Hrecipe1 Hband_len1 Hselected1 Hexpected1 (eq_sym Hlen_env) Hadded_len1
    Hpoint_len1 Hwf_stmt1 Hparams1 Hadded_eq1)
    as [band_values1 [child_values1 [root_values1
      [Hband_values1 [Hchild_render1 [Hroot_render1 Heval1]]]]]].
  destruct (scalar_aware_second_level_entry_eval
    (List.length before_ctxt) layout before_pi2 w2 recipe2 expected2 envv added2 point2
    Hrecipe2 Hband_len2 Hselected2 Hexpected2 (eq_sym Hlen_env) Hadded_len2
    Hpoint_len2 Hwf_stmt2 Hparams2 Hadded_eq2)
    as [band_values2 [child_values2 [root_values2
      [Hband_values2 [Hchild_render2 [Hroot_render2 Heval2]]]]]].
  rewrite <- Hroots_same, <- Hchildren_same in Hchild_render2.
  rewrite <- Hroots_same in Hroot_render2.
  set (mixed_values1 := child_values1 ++ root_values1) in *.
  set (mixed_values2 := child_values2 ++ root_values2) in *.
  assert (Hband_values_len1 : List.length band_values1 = List.length (sabl_loop_mask layout)).
  {
    rewrite Hband_values1, <- affine_product_scalar_aware_layout_band_rows.
    unfold affine_product. rewrite map_length. exact Hband_len1.
  }
  assert (Hband_values_len2 : List.length band_values2 = List.length (sabl_loop_mask layout)).
  {
    rewrite Hband_values2, <- affine_product_scalar_aware_layout_band_rows.
    unfold affine_product. rewrite map_length. exact Hband_len2.
  }
  destruct (second_level_band_recipe_spec_lengths _ _ _ _ Hspec1) as [Hrlen Hclen].
  assert (Hwidth : List.length (slbr_root_rows recipe1) = count_true (sabl_loop_mask layout)).
  { rewrite <- Hselected1. apply select_by_mask_length_count_true. exact Hband_len1. }
  assert (Hselected_values_len1 :
    List.length (select_by_mask (sabl_loop_mask layout) band_values1) =
    List.length (slbr_root_sizes recipe1)).
  { rewrite select_by_mask_length_count_true by exact Hband_values_len1. lia. }
  destruct (second_level_band_recipe_spec_positive_sizes _ _ _ _ Hspec1 Hpositive1)
    as [Hpositive_roots Hpositive_children].
  pose proof (scalar_aware_loop_tile_values_monotone
    (sabl_loop_mask layout) band_values1 band_values2 (slbr_root_sizes recipe1)
    Hband_values_len1 Hband_values_len2 Hselected_values_len1 Hpositive_roots)
    as Hroot_monotone.
  assert (Hroots_len : List.length
    (scalar_aware_loop_tile_values (sabl_loop_mask layout) band_values1 (slbr_root_sizes recipe1)) =
    List.length (slbr_child_sizes recipe1)).
  {
    unfold scalar_aware_loop_tile_values. rewrite map_length, combine_length,
      Hselected_values_len1, Nat.min_id. lia.
  }
  pose proof (scalar_aware_loop_tiles_monotone_quotient
    (sabl_loop_mask layout) band_values1 band_values2
    (scalar_aware_loop_tile_values (sabl_loop_mask layout) band_values1 (slbr_root_sizes recipe1))
    (scalar_aware_loop_tile_values (sabl_loop_mask layout) band_values2 (slbr_root_sizes recipe1))
    (slbr_child_sizes recipe1) Hroot_monotone Hroots_len Hpositive_children)
    as Hchild_monotone.
  assert
    (Hactual_target1 :
       is_eq (Tiling.PL.ip_time_stamp2_ext ip1)
       (firstn (sabl_start layout)
          (affine_product (Tiling.PL.pi_schedule before_pi1)
             (envv ++ point1)) ++
        mixed_values1 ++ band_values1 ++
        skipn
          (sabl_start layout + List.length (sabl_loop_mask layout))%nat
          (affine_product (Tiling.PL.pi_schedule before_pi1)
             (envv ++ point1))) = true).
  {
    rewrite Hts21_after, Hidx_split1.
    pose proof
      (schedule_matches_with_symmetric_trailing_zero_padding_affine_product_is_eq
         expected1 (Tiling.PL.pi_schedule after_pi1)
         (envv ++ added1 ++ point1) Htarget1) as Hmatch.
    rewrite Heval1 in Hmatch.
    exact Hmatch.
  }
  assert
    (Hactual_target2 :
       is_eq (Tiling.PL.ip_time_stamp2_ext ip2)
       (firstn (sabl_start layout)
          (affine_product (Tiling.PL.pi_schedule before_pi2)
             (envv ++ point2)) ++
        mixed_values2 ++ band_values2 ++
        skipn
          (sabl_start layout + List.length (sabl_loop_mask layout))%nat
          (affine_product (Tiling.PL.pi_schedule before_pi2)
             (envv ++ point2))) = true).
  {
    rewrite Hts22_after, Hidx_split2.
    pose proof
      (schedule_matches_with_symmetric_trailing_zero_padding_affine_product_is_eq
         expected2 (Tiling.PL.pi_schedule after_pi2)
         (envv ++ added2 ++ point2) Htarget2) as Hmatch.
    rewrite Heval2 in Hmatch.
    exact Hmatch.
  }
  assert
    (Hnew_without_padding :
       lex_compare
         (firstn (sabl_start layout)
            (affine_product (Tiling.PL.pi_schedule before_pi1)
               (envv ++ point1)) ++
          mixed_values1 ++ band_values1 ++
          skipn
            (sabl_start layout + List.length (sabl_loop_mask layout))%nat
            (affine_product (Tiling.PL.pi_schedule before_pi1)
               (envv ++ point1)))
         (firstn (sabl_start layout)
            (affine_product (Tiling.PL.pi_schedule before_pi2)
               (envv ++ point2)) ++
          mixed_values2 ++ band_values2 ++
          skipn
            (sabl_start layout + List.length (sabl_loop_mask layout))%nat
            (affine_product (Tiling.PL.pi_schedule before_pi2)
               (envv ++ point2))) <>
       Lt).
  {
    unfold Tiling.PL.instr_point_ext_new_sched_ge in Hnew.
    rewrite (lex_compare_left_eq _ _ _ Hactual_target1),
      (lex_compare_right_eq _ _ _ Hactual_target2) in Hnew.
    intro Hlt.
    rewrite Hlt in Hnew.
    destruct Hnew; discriminate.
  }
  assert
    (Hold_decomposed :
       lex_compare
         (firstn (sabl_start layout)
            (affine_product (Tiling.PL.pi_schedule before_pi1)
               (envv ++ point1)) ++
          band_values1 ++
          skipn
            (sabl_start layout + List.length (sabl_loop_mask layout))%nat
            (affine_product (Tiling.PL.pi_schedule before_pi1)
               (envv ++ point1)))
         (firstn (sabl_start layout)
            (affine_product (Tiling.PL.pi_schedule before_pi2)
               (envv ++ point2)) ++
          band_values2 ++
          skipn
            (sabl_start layout + List.length (sabl_loop_mask layout))%nat
            (affine_product (Tiling.PL.pi_schedule before_pi2)
               (envv ++ point2))) =
       Lt).
  {
    unfold Tiling.PL.instr_point_ext_old_sched_lt in Hold.
    rewrite Hts11_old, Hts12_old in Hold.
    pose proof
      (firstn_band_skipn_reconstruct
         Z (sabl_start layout)
         (List.length (sabl_loop_mask layout))
         (affine_product (Tiling.PL.pi_schedule before_pi1)
            (envv ++ point1))) as Hsplit1.
    pose proof
      (firstn_band_skipn_reconstruct
         Z (sabl_start layout)
         (List.length (sabl_loop_mask layout))
         (affine_product (Tiling.PL.pi_schedule before_pi2)
            (envv ++ point2))) as Hsplit2.
    rewrite <- Hband_values1 in Hsplit1.
    rewrite <- Hband_values2 in Hsplit2.
    rewrite <- Hsplit1, <- Hsplit2 in Hold.
    exact Hold.
  }
  assert
    (Hprefix_len :
       List.length
         (firstn (sabl_start layout)
            (affine_product (Tiling.PL.pi_schedule before_pi1)
               (envv ++ point1))) =
       List.length
         (firstn (sabl_start layout)
            (affine_product (Tiling.PL.pi_schedule before_pi2)
               (envv ++ point2)))).
  {
    pose proof Hband_len1 as Hband_sched_len1.
    pose proof Hband_len2 as Hband_sched_len2.
    unfold scalar_aware_layout_band_rows in
      Hband_sched_len1, Hband_sched_len2.
    rewrite !firstn_length, !skipn_length in
      Hband_sched_len1, Hband_sched_len2.
    assert
      (Hmask_fit1 :
         (List.length (sabl_loop_mask layout) <=
         (List.length (Tiling.PL.pi_schedule before_pi1) -
          sabl_start layout))%nat).
    {
      rewrite <- Hband_sched_len1.
      apply Nat.le_min_r.
    }
    assert
      (Hmask_fit2 :
         (List.length (sabl_loop_mask layout) <=
         (List.length (Tiling.PL.pi_schedule before_pi2) -
          sabl_start layout))%nat).
    {
      rewrite <- Hband_sched_len2.
      apply Nat.le_min_r.
    }
    assert
      (Hstart1 :
         (sabl_start layout <=
          List.length (Tiling.PL.pi_schedule before_pi1))%nat).
    {
      destruct (sabl_loop_mask layout); [contradiction|].
      simpl in Hmask_fit1.
      lia.
    }
    assert
      (Hstart2 :
         (sabl_start layout <=
          List.length (Tiling.PL.pi_schedule before_pi2))%nat).
    {
      destruct (sabl_loop_mask layout); [contradiction|].
      simpl in Hmask_fit2.
      lia.
    }
    unfold affine_product.
    rewrite !firstn_length, !map_length.
    rewrite !Nat.min_l by assumption.
    reflexivity.
  }
  assert (Hmixed_len : List.length mixed_values1 = List.length mixed_values2).
  {
    unfold mixed_values1, mixed_values2. rewrite !app_length.
    rewrite (render_scalar_aware_value_prefix_length _ _ _ _ Hband_values_len1 Hchild_render1),
      (render_scalar_aware_value_prefix_length _ _ _ _ Hband_values_len2 Hchild_render2),
      (render_scalar_aware_value_prefix_length _ _ _ _ Hband_values_len1 Hroot_render1),
      (render_scalar_aware_value_prefix_length _ _ _ _ Hband_values_len2 Hroot_render2).
    reflexivity.
  }
  destruct
    (scalar_aware_reversal_implies_mixed_gt
       (firstn (sabl_start layout)
          (affine_product (Tiling.PL.pi_schedule before_pi1)
             (envv ++ point1)))
       (firstn (sabl_start layout)
          (affine_product (Tiling.PL.pi_schedule before_pi2)
             (envv ++ point2)))
       mixed_values1 mixed_values2
       band_values1 band_values2
       (skipn
          (sabl_start layout + List.length (sabl_loop_mask layout))%nat
          (affine_product (Tiling.PL.pi_schedule before_pi1)
             (envv ++ point1)))
       (skipn
          (sabl_start layout + List.length (sabl_loop_mask layout))%nat
          (affine_product (Tiling.PL.pi_schedule before_pi2)
             (envv ++ point2)))
       Hprefix_len Hmixed_len Hold_decomposed Hnew_without_padding)
    as [Hprefix_eq Hmixed_gt].
  destruct (scalar_aware_two_level_prefix_gt_active
    (sabl_loop_mask layout) band_values1 band_values2 _ _ _ _
    child_values1 child_values2 root_values1 root_values2
    Hband_values_len1 Hband_values_len2 Hchild_monotone Hroot_monotone
    Hchild_render1 Hchild_render2 Hroot_render1 Hroot_render2 Hmixed_gt)
    as [dim [x [y [Hdim [Hx [Hy [Hxy Hprior]]]]]]].
  assert
    (Hfull_composed1 :
       affine_product
         (Tiling.PL.pi_schedule1_ext
            (Tiling.compose_tiling_pinstr_ext
               (List.length envv) before_pi1 after_pi1 w1))
         (Tiling.PL.ip_index_ext ip1) =
       affine_product
         (Tiling.PL.pi_schedule before_pi1) (envv ++ point1)).
  {
    cbn [Tiling.compose_tiling_pinstr_ext].
    rewrite Hidx_split1.
    eapply Tiling.lift_affine_function_after_env_eval.
    - reflexivity.
    - exact Hadded_len1.
  }
  assert
    (Hfull_composed2 :
       affine_product
         (Tiling.PL.pi_schedule1_ext
            (Tiling.compose_tiling_pinstr_ext
               (List.length envv) before_pi2 after_pi2 w2))
         (Tiling.PL.ip_index_ext ip2) =
       affine_product
         (Tiling.PL.pi_schedule before_pi2) (envv ++ point2)).
  {
    cbn [Tiling.compose_tiling_pinstr_ext].
    rewrite Hidx_split2.
    eapply Tiling.lift_affine_function_after_env_eval.
    - reflexivity.
    - exact Hadded_len2.
  }
  exists layout,
    (Tiling.compose_tiling_pinstr_ext
       (List.length envv) before_pi1 after_pi1 w1),
    (Tiling.compose_tiling_pinstr_ext
       (List.length envv) before_pi2 after_pi2 w2),
    dim.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact Hcomposed1|].
  split; [exact Hcomposed2|].
  split; [exact Hdim|].
  eapply scalar_aware_component_active_from_band_values
    with
      (old1 :=
         affine_product
           (Tiling.PL.pi_schedule before_pi1) (envv ++ point1))
      (old2 :=
         affine_product
           (Tiling.PL.pi_schedule before_pi2) (envv ++ point2))
      (band1 := band_values1)
      (band2 := band_values2)
      (x := x) (y := y).
  - exact Hfull_composed1.
  - exact Hfull_composed2.
  - exact Hband_values1.
  - exact Hband_values2.
  - exact Hprefix_eq.
  - exact Hprior.
  - exact Hx.
  - exact Hy.
  - exact Hdim.
  - exact Hxy.
Qed.

End PhaseAwareSemanticBands.

Section ExecutableExamples.

End ExecutableExamples.

End TilingBandScheduleValidator.

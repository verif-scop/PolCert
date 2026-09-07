Require Import List.
Require Import ZArith.
Require Import Lia.
Require Import Misc.
Require Import Linalg.
Require Import Result.
Require Import String.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.
Require Import PolIRs.
Require Import PolyBase.
Require Import PrepareCodegen.
Require Import RawCodegenOrigin.
Require Import ParallelLoop.
Require Import ParallelValidator.

Import ListNotations.

Require Import ParallelCodegenCompatibility.

Module ParallelCodegenCorrect (PolIRs : POLIRS).
Include ParallelCodegenCompatibility PolIRs.

(** * Proof map

    - [par_modes_certified_stmt] and the tag lemmas assign every emitted
      [ParMode] loop to a validator certificate.
    - [zrange_family_pair_origin] and
      [certified_sibling_points_permutable] transport a local generated pair
      to the pointwise certificate theorem.
    - [actual_multi_ordered_mutual] follows one concrete target trace and
      constructs the ordered proof companion required for serialization.
    - [annotated_codegen_many_raw_root_origin] connects generated events to
      source instruction points; the following ordered/refinement theorems
      compose that fact with code generation.
    - the final checked endpoints reflect full cleanup back to raw code and
      then use the certified actual-trace argument. *)

(** * Mode ownership and origin tags *)

(** Every syntactic parallel loop in [s] is owned by one certificate in
    [certs].  This property says nothing about execution order. *)
Fixpoint par_modes_certified_stmt
    (certs : list ParallelValidator.parallel_cert) (s : ParallelLoop.stmt) : Prop :=
  match s with
  | ParallelLoop.Loop mode od _ _ body =>
      (match mode with
       | ParallelLoop.ParMode =>
           exists cert,
             In cert certs /\ od = Some cert.(ParallelValidator.certified_dim)
       | _ => True
       end) /\
      par_modes_certified_stmt certs body
  | ParallelLoop.Instr _ _ => True
  | ParallelLoop.Seq ss => par_modes_certified_stmts certs ss
  | ParallelLoop.Guard _ body => par_modes_certified_stmt certs body
  end
with par_modes_certified_stmts
    (certs : list ParallelValidator.parallel_cert) (ss : ParallelLoop.stmt_list) : Prop :=
  match ss with
  | ParallelLoop.SNil => True
  | ParallelLoop.SCons s ss' =>
      par_modes_certified_stmt certs s /\
      par_modes_certified_stmts certs ss'
  end.

Lemma tag_loop_has_no_parallel_modes :
  forall certs depth s,
    par_modes_certified_stmt certs (tag_loop_stmt_at depth s)
with tag_loops_have_no_parallel_modes :
  forall certs depth ss,
    par_modes_certified_stmts certs (tag_loop_stmts_at depth ss).
Proof.
  - intros certs depth s. destruct s; simpl.
    + split; [exact I|]. eapply tag_loop_has_no_parallel_modes.
    + exact I.
    + eapply tag_loops_have_no_parallel_modes.
    + eapply tag_loop_has_no_parallel_modes.
  - intros certs depth ss. destruct ss; simpl.
    + exact I.
    + split.
      * eapply tag_loop_has_no_parallel_modes.
      * eapply tag_loops_have_no_parallel_modes.
Qed.

Definition par_modes_parallelize_stmt_goal (s : ParallelLoop.stmt) : Prop :=
  forall certs cert,
    In cert certs ->
    par_modes_certified_stmt certs s ->
    par_modes_certified_stmt certs
      (ParallelLoop.parallelize_dim_stmt cert.(ParallelValidator.certified_dim) s).

Definition par_modes_parallelize_stmts_goal (ss : ParallelLoop.stmt_list) : Prop :=
  forall certs cert,
    In cert certs ->
    par_modes_certified_stmts certs ss ->
    par_modes_certified_stmts certs
      (ParallelLoop.parallelize_dim_stmts cert.(ParallelValidator.certified_dim) ss).

Lemma par_modes_parallelize_dim_mutual :
  (forall s, par_modes_parallelize_stmt_goal s) /\
  (forall ss, par_modes_parallelize_stmts_goal ss).
Proof.
  apply pl_stmt_stmts_mutind;
    unfold par_modes_parallelize_stmt_goal,
      par_modes_parallelize_stmts_goal.
  - intros mode od lb ub body IH certs cert Hin Hmodes.
    simpl in Hmodes |- *.
    destruct Hmodes as [Hmode Hbody].
    destruct mode; destruct od as [origin|]; simpl.
    + destruct (Nat.eqb (ParallelValidator.certified_dim cert) origin) eqn:Heq.
      * split.
        -- exists cert. split; [exact Hin|].
           apply Nat.eqb_eq in Heq. now rewrite Heq.
        -- eapply IH; eauto.
      * split; [exact I|]. eapply IH; eauto.
    + split; [exact I|]. eapply IH; eauto.
    + split; [exact Hmode|]. eapply IH; eauto.
    + split; [exact Hmode|]. eapply IH; eauto.
    + split; [exact Hmode|]. eapply IH; eauto.
    + split; [exact Hmode|]. eapply IH; eauto.
  - intros i es certs cert Hin Hmodes. exact Hmodes.
  - intros ss IH certs cert Hin Hmodes. simpl in *.
    eapply IH; eauto.
  - intros test body IH certs cert Hin Hmodes. simpl in *.
    eapply IH; eauto.
  - intros certs cert Hin Hmodes. exact I.
  - intros s IHs ss IHss certs cert Hin Hmodes.
    simpl in *.
    destruct Hmodes as [Hs Hss]. split.
    + eapply IHs; eauto.
    + eapply IHss; eauto.
Qed.

Lemma par_modes_parallelize_dim_stmt :
  forall certs cert s,
    In cert certs ->
    par_modes_certified_stmt certs s ->
    par_modes_certified_stmt certs
      (ParallelLoop.parallelize_dim_stmt cert.(ParallelValidator.certified_dim) s).
Proof.
  intros certs cert s.
  exact ((proj1 par_modes_parallelize_dim_mutual) s certs cert).
Qed.

Lemma parallelize_certified_dims_modes_aux :
  forall todo all s ctxt vars,
    (forall cert, In cert todo -> In cert all) ->
    par_modes_certified_stmt all s ->
    par_modes_certified_stmt all
      (let '((s', _), _) :=
         parallelize_certified_dims todo ((s, ctxt), vars)
       in s').
Proof.
  induction todo as [|cert todo IH]; intros all s ctxt vars Hin Hmodes.
  - exact Hmodes.
  - simpl.
    eapply IH.
    + intros cert' Hcert'. apply Hin. right. exact Hcert'.
    + eapply par_modes_parallelize_dim_stmt.
      * apply Hin. left. reflexivity.
      * exact Hmodes.
Qed.

Lemma parallelize_certified_dims_modes :
  forall certs s ctxt vars,
    par_modes_certified_stmt certs
      (let '((s', _), _) :=
         parallelize_certified_dims certs
           ((tag_loop_stmt_at 0 s, ctxt), vars)
       in s').
Proof.
  intros certs s ctxt vars.
  eapply parallelize_certified_dims_modes_aux.
  - auto.
  - eapply tag_loop_has_no_parallel_modes.
Qed.

Definition tagged_parallelize_stmt_goal (s : ParallelLoop.stmt) : Prop :=
  forall target depth,
    tagged_from_depth_stmt depth s ->
    tagged_from_depth_stmt depth
      (ParallelLoop.parallelize_dim_stmt target s).

Definition tagged_parallelize_stmts_goal (ss : ParallelLoop.stmt_list) : Prop :=
  forall target depth,
    tagged_from_depth_stmts depth ss ->
    tagged_from_depth_stmts depth
      (ParallelLoop.parallelize_dim_stmts target ss).

Lemma tagged_parallelize_dim_mutual :
  (forall s, tagged_parallelize_stmt_goal s) /\
  (forall ss, tagged_parallelize_stmts_goal ss).
Proof.
  apply pl_stmt_stmts_mutind;
    unfold tagged_parallelize_stmt_goal, tagged_parallelize_stmts_goal.
  - intros mode od lb ub body IH target depth Htag.
    simpl in Htag |- *.
    destruct Htag as [Horigin Hbody].
    destruct mode; destruct od as [origin|]; simpl;
      try destruct (Nat.eqb target origin);
      split; eauto.
  - intros i es target depth Htag. exact Htag.
  - intros ss IH target depth Htag. simpl in *.
    eapply IH; eauto.
  - intros test body IH target depth Htag. simpl in *.
    eapply IH; eauto.
  - intros target depth Htag. exact I.
  - intros s IHs ss IHss target depth Htag.
    simpl in *.
    destruct Htag as [Hs Hss]. split.
    + eapply IHs; eauto.
    + eapply IHss; eauto.
Qed.

Lemma tagged_parallelize_dim_stmt :
  forall target depth s,
    tagged_from_depth_stmt depth s ->
    tagged_from_depth_stmt depth
      (ParallelLoop.parallelize_dim_stmt target s).
Proof.
  intros target depth s.
  exact ((proj1 tagged_parallelize_dim_mutual) s target depth).
Qed.

Lemma parallelize_certified_dims_tagged_aux :
  forall certs depth s ctxt vars,
    tagged_from_depth_stmt depth s ->
    tagged_from_depth_stmt depth
      (let '((s', _), _) :=
         parallelize_certified_dims certs ((s, ctxt), vars)
       in s').
Proof.
  induction certs as [|cert certs IH]; intros depth s ctxt vars Htag.
  - exact Htag.
  - simpl. eapply IH.
    eapply tagged_parallelize_dim_stmt. exact Htag.
Qed.

Lemma parallelize_certified_dims_tagged :
  forall certs s ctxt vars,
    tagged_from_depth_stmt 0
      (let '((s', _), _) :=
         parallelize_certified_dims certs
           ((tag_loop_stmt_at 0 s, ctxt), vars)
       in s').
Proof.
  intros certs s ctxt vars.
  eapply parallelize_certified_dims_tagged_aux.
  eapply tag_loop_stmt_tagged_from_depth.
Qed.

(** * Certificates order the actual generated trace

    The mutual induction follows the concrete target trace.  At each parallel
    loop it recovers the certificate that owns the loop's origin tag, maps two
    sibling-iteration points back to source instances, and applies pointwise
    certificate soundness.  Sequential, vector, guard, and sequence cases only
    propagate the resulting ordered-trace evidence. *)

Local Lemma zrange_family_pair_origin :
  forall lb ub body env trs pre1 tr1 pre2 tr2 post,
    Forall2
      (fun z tri => ParallelLoop.par_trace body (z :: env) tri)
      (Zrange lb ub) trs ->
    trs = pre1 ++ tr1 :: pre2 ++ tr2 :: post ->
    exists z1 z2,
      z1 <> z2 /\
      ParallelLoop.par_trace body (z1 :: env) tr1 /\
      ParallelLoop.par_trace body (z2 :: env) tr2.
Proof.
  intros lb ub body env trs pre1 tr1 pre2 tr2 post Htraces Hshape.
  set (i := Datatypes.length pre1).
  set (j := (Datatypes.length pre1 + S (Datatypes.length pre2))%nat).
  assert (Hnth1 : nth_error trs i = Some tr1).
  {
    rewrite Hshape.
    unfold i; rewrite nth_error_app2 by lia.
    replace (Datatypes.length pre1 - Datatypes.length pre1)%nat
      with 0%nat by lia.
    reflexivity.
  }
  assert (Hnth2 : nth_error trs j = Some tr2).
  {
    rewrite Hshape.
    unfold j; rewrite nth_error_app2 by lia.
    replace
      (Datatypes.length pre1 + S (Datatypes.length pre2) -
       Datatypes.length pre1)%nat
      with (S (Datatypes.length pre2)) by lia.
    simpl; rewrite nth_error_app2 by lia.
    replace (Datatypes.length pre2 - Datatypes.length pre2)%nat
      with 0%nat by lia.
    reflexivity.
  }
  pose proof (Forall2_sym _ _ _ _ _ Htraces) as Htraces_sym.
  destruct (Forall2_nth_error _ _ _ _ _ _ _ Htraces_sym Hnth1)
    as [z1 [Hz1 Htrace1]].
  destruct (Forall2_nth_error _ _ _ _ _ _ _ Htraces_sym Hnth2)
    as [z2 [Hz2 Htrace2]].
  exists z1, z2.
  refine (conj _ (conj Htrace1 Htrace2)).
  rewrite Zrange_nth_error in Hz1, Hz2.
  destruct Hz1 as [_ ->]; destruct Hz2 as [_ ->].
  intro Heqz.
  assert (Hindices : Z.of_nat i = Z.of_nat j) by lia.
  apply Nat2Z.inj in Hindices.
  unfold i, j in Hindices; lia.
Qed.

Local Lemma certified_sibling_points_permutable :
  forall pp cert depth env z1 z2 suffix1 suffix2
         generated1 generated2 source1 source2,
    parallel_codegen_cert_sound pp cert ->
    depth = cert.(ParallelValidator.certified_dim) ->
    Datatypes.length env =
      (Datatypes.length (ParallelValidator.pprog_varctxt pp) + depth)%nat ->
    z1 <> z2 ->
    generated1.(ParallelLoop.ILSema.ip_index) = suffix1 ++ z1 :: env ->
    generated2.(ParallelLoop.ILSema.ip_index) = suffix2 ++ z2 :: env ->
    generated_source_point_full
      pp (ParallelValidator.schedule_width pp) generated1 source1 ->
    generated_source_point_full
      pp (ParallelValidator.schedule_width pp) generated2 source2 ->
    ParallelLoop.ILSema.Permutable generated1 generated2.
Proof.
  intros pp cert depth env z1 z2 suffix1 suffix2
    generated1 generated2 source1 source2
    [Hpointwise Hbound] Hdepth Henv Hzneq Hindex1 Hindex2
    Hsource1 Hsource2.
  destruct Hsource1 as [Hbasic1 Hprefix1 Hsched1].
  destruct Hsource2 as [Hbasic2 Hprefix2 Hsched2].
  destruct Hbasic1 as [Hequiv1 [pi1 [Hpi1 [Hbelongs1 Hlen1]]]].
  destruct Hbasic2 as [Hequiv2 [pi2 [Hpi2 [Hbelongs2 Hlen2]]]].
  eapply permutable_of_point_sema_equiv; [exact Hequiv1|exact Hequiv2|].
  eapply Hpointwise with (pi1 := pi1) (pi2 := pi2);
    try eassumption.
  rewrite <- Hdepth.
  eapply generated_source_siblings_same_slice
    with (width := ParallelValidator.schedule_width pp)
         (env := env) (z1 := z1) (z2 := z2)
         (suffix1 := suffix1) (suffix2 := suffix2)
         (generated1 := generated1) (generated2 := generated2);
    try eassumption.
  - reflexivity.
  - rewrite Hdepth; exact Hbound.
  - constructor.
    + split; [exact Hequiv1|].
      exists pi1; split; [exact Hpi1|].
      split; [exact Hbelongs1|exact Hlen1].
    + exact Hprefix1.
    + exact Hsched1.
  - constructor.
    + split; [exact Hequiv2|].
      exists pi2; split; [exact Hpi2|].
      split; [exact Hbelongs2|exact Hlen2].
    + exact Hprefix2.
    + exact Hsched2.
Qed.

Definition actual_multi_ordered_stmt_goal (s : ParallelLoop.stmt) : Prop :=
  forall depth pp certs env tr root,
    tagged_from_depth_stmt depth s ->
    par_modes_certified_stmt certs s ->
    Forall (parallel_codegen_cert_sound pp) certs ->
    Datatypes.length env =
      (Datatypes.length (ParallelValidator.pprog_varctxt pp) + depth)%nat ->
    ParallelLoop.trace_safe_stmt s ->
    root_origin_oracle pp root ->
    (forall ip, In ip tr -> In ip root) ->
    ParallelLoop.par_trace s env tr ->
    ParallelLoop.ordered_par_trace s env tr.

Definition actual_multi_ordered_stmts_goal (ss : ParallelLoop.stmt_list) : Prop :=
  forall depth pp certs env tr root,
    tagged_from_depth_stmts depth ss ->
    par_modes_certified_stmts certs ss ->
    Forall (parallel_codegen_cert_sound pp) certs ->
    Datatypes.length env =
      (Datatypes.length (ParallelValidator.pprog_varctxt pp) + depth)%nat ->
    ParallelLoop.trace_safe_stmts ss ->
    root_origin_oracle pp root ->
    (forall ip, In ip tr -> In ip root) ->
    ParallelLoop.par_traces ss env tr ->
    ParallelLoop.ordered_par_traces ss env tr.

Lemma actual_multi_ordered_mutual :
  (forall s, actual_multi_ordered_stmt_goal s) /\
  (forall ss, actual_multi_ordered_stmts_goal ss).
Proof.
  apply pl_stmt_stmts_mutind;
    unfold actual_multi_ordered_stmt_goal,
      actual_multi_ordered_stmts_goal.
  - intros mode od lb ub body IH depth pp certs env tr root
      Htag Hmodes Hcerts Henv Hsafe Horacle Hroot Htrace.
    simpl in Htag, Hmodes, Hsafe.
    destruct Htag as [Horigin Htag_body].
    destruct Hmodes as [Hmode Hmodes_body].
    destruct mode.
    + inversion Htrace as
        [| | | |
         od0 lb0 ub0 body0 env0 zs0 trs0 tr0 Hrange Htraces Hconcat
         | |];
        subst.
      eapply ParallelLoop.OPTLoopSeq.
      * reflexivity.
      * exact Htraces.
      * eapply Forall2_imp_in_right; [exact Htraces|].
        intros z tri Htri_in Htri.
        eapply IH with (depth := S depth) (pp := pp)
          (certs := certs) (root := root).
        -- exact Htag_body.
        -- exact Hmodes_body.
        -- exact Hcerts.
        -- simpl. lia.
        -- exact Hsafe.
        -- exact Horacle.
        -- intros ip Hip. apply Hroot.
           apply in_concat. exists tri. split; assumption.
        -- exact Htri.
      * reflexivity.
    + inversion Htrace as
        [| | | | | |
         d0 lb0 ub0 body0 env0 zs0 trs0 tr0
           Hrange Htraces Hinterleave];
        subst.
      eapply ParallelLoop.OPTLoopPar.
      * reflexivity.
      * exact Htraces.
      * eapply Forall2_imp_in_right; [exact Htraces|].
        intros z tri Htri_in Htri.
        eapply IH with (depth := S depth) (pp := pp)
          (certs := certs) (root := root).
        -- exact Htag_body.
        -- exact Hmodes_body.
        -- exact Hcerts.
        -- simpl. lia.
        -- exact Hsafe.
        -- exact Horacle.
        -- intros ip Hip. apply Hroot.
           eapply interleave_family_concat_member_in_output;
             [exact Hinterleave|].
           apply in_concat. exists tri. split; assumption.
        -- exact Htri.
      * destruct Hmode as [cert [Hcert_in Hcert_origin]].
        (* Recover the certificate that owns this concrete parallel loop. *)
        assert (Hcert_sound : parallel_codegen_cert_sound pp cert).
        {
          rewrite Forall_forall in Hcerts.
          eapply Hcerts. exact Hcert_in.
        }
        assert (Hdepth_cert : depth = cert.(ParallelValidator.certified_dim)).
        { inversion Hcert_origin. reflexivity. }
        intros pre1 tr1 pre2 tr2 post ip1 ip2 Hshape Hin1 Hin2.
        destruct
          (zrange_family_pair_origin
            _ _ _ _ _ _ _ _ _ _ Htraces Hshape)
          as (z1 & z2 & Hzneq & Htrace1 & Htrace2).
        (* Distinct sibling families expose generated points with a shared
           outer environment and different current coordinates. *)
        destruct
          (par_trace_point_extends_env
            _ _ _ _ Hsafe Htrace1 Hin1)
          as [suffix1 Hindex1].
        destruct
          (par_trace_point_extends_env
            _ _ _ _ Hsafe Htrace2 Hin2)
          as [suffix2 Hindex2].
        assert (Hroot1 : In ip1 root).
        {
          apply Hroot.
          eapply interleave_family_concat_member_in_output;
            [exact Hinterleave|].
          apply in_concat. exists tr1. split.
          - rewrite Hshape. apply in_or_app. right. simpl. auto.
          - exact Hin1.
        }
        assert (Hroot2 : In ip2 root).
        {
          apply Hroot.
          eapply interleave_family_concat_member_in_output;
            [exact Hinterleave|].
          apply in_concat. exists tr2. split.
          - rewrite Hshape. apply in_or_app. right. simpl.
            right. apply in_or_app. right. simpl. auto.
          - exact Hin2.
        }
        destruct (Horacle ip1 Hroot1) as [source1 Hsource1].
        destruct (Horacle ip2 Hroot2) as [source2 Hsource2].
        (* Map both points to source schedule slices, consume the owning
           certificate, and transport permutability back to generated points. *)
        eapply certified_sibling_points_permutable; eassumption.
      * exact Hinterleave.
    + inversion Htrace as
        [| | | | |
         od0 lb0 ub0 body0 env0 zs0 trs0 tr0 Hrange Htraces Hconcat
         |];
        subst.
      eapply ParallelLoop.OPTLoopVec.
      * reflexivity.
      * exact Htraces.
      * eapply Forall2_imp_in_right; [exact Htraces|].
        intros z tri Htri_in Htri.
        eapply IH with (depth := S depth) (pp := pp)
          (certs := certs) (root := root).
        -- exact Htag_body.
        -- exact Hmodes_body.
        -- exact Hcerts.
        -- simpl. lia.
        -- exact Hsafe.
        -- exact Horacle.
        -- intros ip Hip. apply Hroot.
           apply in_concat. exists tri. split; assumption.
        -- exact Htri.
      * reflexivity.
  - intros i es depth pp certs env tr root
      Htag Hmodes Hcerts Henv Hsafe Horacle Hroot Htrace.
    inversion Htrace; subst. constructor.
  - intros ss IH depth pp certs env tr root
      Htag Hmodes Hcerts Henv Hsafe Horacle Hroot Htrace.
    inversion Htrace; subst. constructor.
    eapply IH; eauto.
  - intros test body IH depth pp certs env tr root
      Htag Hmodes Hcerts Henv Hsafe Horacle Hroot Htrace.
    inversion Htrace; subst.
    + econstructor; [eassumption|]. eapply IH; eauto.
    + econstructor; eassumption.
  - intros depth pp certs env tr root
      Htag Hmodes Hcerts Henv Hsafe Horacle Hroot Htrace.
    inversion Htrace; subst. constructor.
  - intros s IHs ss IHss depth pp certs env tr root
      Htag Hmodes Hcerts Henv Hsafe Horacle Hroot Htrace.
    simpl in Htag, Hmodes, Hsafe.
    destruct Htag as [Htag_s Htag_ss].
    destruct Hmodes as [Hmodes_s Hmodes_ss].
    destruct Hsafe as [Hsafe_s Hsafe_ss].
    inversion Htrace; subst. constructor.
    + eapply IHs with (root := root); eauto.
      intros ip Hip. apply Hroot. apply in_or_app. left. exact Hip.
    + eapply IHss with (root := root); eauto.
      intros ip Hip. apply Hroot. apply in_or_app. right. exact Hip.
Qed.

Lemma actual_multi_ordered_stmt :
  forall s depth pp certs env tr root,
    tagged_from_depth_stmt depth s ->
    par_modes_certified_stmt certs s ->
    Forall (parallel_codegen_cert_sound pp) certs ->
    Datatypes.length env =
      (Datatypes.length (ParallelValidator.pprog_varctxt pp) + depth)%nat ->
    ParallelLoop.trace_safe_stmt s ->
    root_origin_oracle pp root ->
    (forall ip, In ip tr -> In ip root) ->
    ParallelLoop.par_trace s env tr ->
    ParallelLoop.ordered_par_trace s env tr.
Proof.
  exact (proj1 actual_multi_ordered_mutual).
Qed.

Fixpoint parallelize_certified_dims_stmt
    (certs : list ParallelValidator.parallel_cert) (s : ParallelLoop.stmt) : ParallelLoop.stmt :=
  match certs with
  | [] => s
  | cert :: certs' =>
      parallelize_certified_dims_stmt certs'
        (ParallelLoop.parallelize_dim_stmt cert.(ParallelValidator.certified_dim) s)
  end.

Lemma parallelize_certified_dims_program_eq :
  forall certs s ctxt vars,
    parallelize_certified_dims certs ((s, ctxt), vars) =
      ((parallelize_certified_dims_stmt certs s, ctxt), vars).
Proof.
  induction certs as [|cert certs IH]; intros s ctxt vars; simpl.
  - reflexivity.
  - eapply IH.
Qed.

Lemma seq_trace_parallelize_certified_dims_inv :
  forall certs s env tr,
    ParallelLoop.seq_trace (parallelize_certified_dims_stmt certs s) env tr ->
    ParallelLoop.seq_trace s env tr.
Proof.
  induction certs as [|cert certs IH]; intros s env tr Htrace; simpl in *.
  - exact Htrace.
  - eapply seq_trace_parallelize_dim_stmt_inv.
    eapply IH. exact Htrace.
Qed.

Lemma trace_safe_parallelize_certified_dims_inv :
  forall certs s,
    ParallelLoop.trace_safe_stmt (parallelize_certified_dims_stmt certs s) ->
    ParallelLoop.trace_safe_stmt s.
Proof.
  induction certs as [|cert certs IH]; intros s Hsafe; simpl in *.
  - exact Hsafe.
  - eapply trace_safe_parallelize_dim_stmt_inv.
    eapply IH. exact Hsafe.
Qed.

(** * Raw codegen origin, ordered traces, and certified refinement *)

(** Standard raw code generation first inserts the padded schedule coordinates
    and may simplify the polyhedral loop.  This theorem composes the neutral
    trace reflection from [RawCodegenOrigin] with preparation facts to recover
    an original source instruction point for every generated event. *)
Theorem annotated_codegen_many_raw_root_origin :
  forall pis varctxt vars certs pl env root_tr,
    mayReturn
      (annotated_codegen_many_raw
        ((pis, varctxt), vars) certs) pl ->
    PolyLang.wf_pprog_affine ((pis, varctxt), vars) ->
    ParallelLoop.trace_safe pl ->
    program_par_trace pl env root_tr ->
    Datatypes.length env = Datatypes.length varctxt ->
    forall ip,
      In ip root_tr ->
      exists source_ip,
        generated_source_point_full
          ((pis, varctxt), vars)
          (ParallelValidator.schedule_width ((pis, varctxt), vars))
          ip source_ip.
Proof.
  intros pis varctxt vars certs pl env root_tr
    Hcodegen Hwf Hsafe Htrace Henv ip Hin.
  (* Recover preparation invariants and the exact raw generator result. *)
  pose proof
    (PrepareCore.prepare_codegen_target_dim_preserved
       ((pis, varctxt), vars) Hwf) as Hprepdim.
  pose proof
    (PrepareCore.prepare_codegen_preserves_wf_at
       ((pis, varctxt), vars) Hwf) as Hcgwf.
  destruct Hcgwf as [Hctxt [Hdim Hsched]].
  set (env_dim := Datatypes.length varctxt).
  set (cols := PrepareCore.codegen_target_dim ((pis, varctxt), vars)).
  set (prep_pis :=
    map (PrepareCore.prepare_pi env_dim cols) pis).
  assert (Hsource_dim :
    (PolyLang.pprog_current_dim ((pis, varctxt), vars) <= cols)%nat).
  {
    subst cols.
    apply PrepareCore.wf_pprog_affine_implies_pprog_current_dim_le_target.
    exact Hwf.
  }
  assert (Henvdim :
    forall pi, In pi prep_pis ->
      PolyLang.current_env_dim_in_dim cols
        pi.(PolyLang.pi_point_witness) = env_dim).
  {
    intros prep_pi Hprep_pi.
    subst prep_pis env_dim cols.
    exact
      (PrepareCore.prepared_pi_current_env_dim_for_codegen
        pis varctxt vars prep_pi Hwf Hprep_pi).
  }
  unfold annotated_codegen_many_raw in Hcodegen.
  apply mayReturn_bind in Hcodegen.
  destruct Hcodegen as [tagged [Htagged Hpure]].
  apply mayReturn_pure in Hpure. subst pl.
  unfold tagged_prepared_codegen_raw in Htagged.
  apply mayReturn_bind in Htagged.
  destruct Htagged as [loop [Hprepared Hpure]].
  apply mayReturn_pure in Hpure. subst tagged.
  unfold PrepareCore.prepared_codegen_raw in Hprepared.
  unfold PrepareCore.CodeGen.codegen in Hprepared.
  simpl in Hprepared.
  bind_imp_destruct Hprepared raw_stmt Hgen.
  apply mayReturn_pure in Hprepared. subst loop.
  change
    (ParallelLoop.trace_safe
      (parallelize_certified_dims certs
        ((tag_loop_stmt_at 0 raw_stmt, varctxt), vars))) in Hsafe.
  change
    (program_par_trace
      (parallelize_certified_dims certs
        ((tag_loop_stmt_at 0 raw_stmt, varctxt), vars))
      env root_tr) in Htrace.
  rewrite parallelize_certified_dims_program_eq in Hsafe.
  rewrite parallelize_certified_dims_program_eq in Htrace.
  simpl in Hsafe, Htrace.
  (* Cover the actual interleaving by a sequential trace, then erase the
     annotation passes without changing its instruction points. *)
  destruct
    (par_trace_seq_cover
       (parallelize_certified_dims_stmt certs
         (tag_loop_stmt_at 0 raw_stmt))
       env root_tr Hsafe Htrace)
    as [seq_tr [Hseq Hcover]].
  pose proof
    (seq_trace_parallelize_certified_dims_inv
       certs (tag_loop_stmt_at 0 raw_stmt) env seq_tr Hseq)
    as Htag_seq.
  assert (Htag_safe :
    ParallelLoop.trace_safe_stmt (tag_loop_stmt_at 0 raw_stmt)).
  {
    eapply trace_safe_parallelize_certified_dims_inv.
    exact Hsafe.
  }
  pose proof
    (tagged_seq_trace_origin
       raw_stmt 0 env seq_tr Htag_safe Htag_seq) as Hraw_trace.
  assert (Hevent_in :
    In (generated_event ip) (map generated_event seq_tr)).
  {
    apply in_map. eapply Hcover. exact Hin.
  }
  assert (Hctxt' : (env_dim <= cols)%nat).
  {
    subst env_dim cols. exact Hctxt.
  }
  assert (Hdim' : PrepareCore.ASTGen.pis_have_dimension prep_pis cols).
  {
    subst prep_pis env_dim cols. exact Hdim.
  }
  assert (Hsched' :
    forall pi, In pi prep_pis ->
      (poly_nrl pi.(PolyLang.pi_schedule) <= cols)%nat).
  {
    subst prep_pis env_dim cols. exact Hsched.
  }
  assert (Hgen' :
    mayReturn
      (PrepareCore.CodeGen.complete_generate_many
        env_dim cols prep_pis) raw_stmt).
  {
    subst env_dim cols prep_pis.
    change
      (mayReturn
        (PrepareCore.CodeGen.complete_generate_many
          (Datatypes.length varctxt)
          (PrepareCore.codegen_target_dim
            (PrepareCore.prepare_codegen ((pis, varctxt), vars)))
          (map
            (PrepareCore.prepare_pi
              (Datatypes.length varctxt)
              (PrepareCore.codegen_target_dim
                ((pis, varctxt), vars))) pis))
        raw_stmt) in Hgen.
    rewrite Hprepdim in Hgen.
    exact Hgen.
  }
  pose proof
    (RawOrigin.complete_generate_many_event_source
      env_dim cols prep_pis raw_stmt env
      (map generated_event seq_tr) (generated_event ip)
      Hctxt' Hgen' Henv Hdim' Henvdim Hsched'
      Hraw_trace Hevent_in) as Hsource_event.
  (* Convert the neutral raw event witness to an original source point. *)
  assert (Hwidth :
    list_max
      (map (fun pi => Datatypes.length pi.(PolyLang.pi_schedule))
        prep_pis) =
    ParallelValidator.schedule_width ((pis, varctxt), vars)).
  {
    subst prep_pis env_dim cols.
    apply prepared_schedule_width_eq.
  }
  rewrite Hwidth in Hsource_event.
  eapply prepared_event_to_source_point;
    eauto using generated_event_matches.
Qed.

Theorem annotated_codegen_many_raw_semantics_ordered :
  forall pis varctxt vars certs pl st st',
    mayReturn
      (annotated_codegen_many_raw
        ((pis, varctxt), vars) certs) pl ->
    PolyLang.wf_pprog_affine ((pis, varctxt), vars) ->
    Forall
      (parallel_codegen_cert_sound ((pis, varctxt), vars)) certs ->
    ParallelLoop.trace_safe pl ->
    ParallelLoop.semantics pl st st' ->
    ParallelLoop.ordered_semantics pl st st'.
Proof.
  intros pis varctxt vars certs pl st st'
    Hgen Hwf Hcerts Hsafe Hsem.
  (* Expose the raw statement and the actual root trace admitted by the target
     semantics. *)
  pose proof Hgen as Hgen_root.
  unfold annotated_codegen_many_raw in Hgen.
  apply mayReturn_bind in Hgen.
  destruct Hgen as [tagged [Htagged Hpure]].
  apply mayReturn_pure in Hpure. subst pl.
  unfold tagged_prepared_codegen_raw in Htagged.
  apply mayReturn_bind in Htagged.
  destruct Htagged as [loop [Hloop Hpure]].
  apply mayReturn_pure in Hpure. subst tagged.
  unfold PrepareCore.prepared_codegen_raw in Hloop.
  unfold PrepareCore.CodeGen.codegen in Hloop.
  simpl in Hloop.
  apply mayReturn_bind in Hloop.
  destruct Hloop as [raw_stmt [Hraw Hpure]].
  apply mayReturn_pure in Hpure. subst loop.
  change
    (ParallelLoop.trace_safe
      (parallelize_certified_dims certs
        ((tag_loop_stmt_at 0 raw_stmt, varctxt), vars))) in Hsafe.
  change
    (ParallelLoop.semantics
      (parallelize_certified_dims certs
        ((tag_loop_stmt_at 0 raw_stmt, varctxt), vars)) st st') in Hsem.
  change
    (ParallelLoop.ordered_semantics
      (parallelize_certified_dims certs
        ((tag_loop_stmt_at 0 raw_stmt, varctxt), vars)) st st').
  rewrite parallelize_certified_dims_program_eq in Hsafe.
  rewrite parallelize_certified_dims_program_eq in Hsem.
  rewrite parallelize_certified_dims_program_eq.
  simpl in Hsafe, Hsem |- *.
  inversion Hsem as
    [loop_ext loop ctxt vars' env mem1 mem2
      Heq Hcompat Hna Hinit Hloopsem]; subst.
  inversion Heq; subst.
  destruct Hloopsem as [root_tr [Htrace Htrace_sem]].
  assert (Henv : Datatypes.length env = Datatypes.length ctxt).
  {
    pose proof (Instr.init_env_samelen ctxt (rev env) st Hinit)
      as Hlen.
    rewrite rev_length in Hlen. symmetry. exact Hlen.
  }
  assert (Htagged_final :
    tagged_from_depth_stmt 0
      (parallelize_certified_dims_stmt certs
        (tag_loop_stmt_at 0 raw_stmt))).
  {
    pose proof
      (parallelize_certified_dims_tagged
        certs raw_stmt ctxt vars') as Htagged_program.
    rewrite parallelize_certified_dims_program_eq in Htagged_program.
    exact Htagged_program.
  }
  assert (Hmodes_final :
    par_modes_certified_stmt certs
      (parallelize_certified_dims_stmt certs
        (tag_loop_stmt_at 0 raw_stmt))).
  {
    pose proof
      (parallelize_certified_dims_modes
        certs raw_stmt ctxt vars') as Hmodes_program.
    rewrite parallelize_certified_dims_program_eq in Hmodes_program.
    exact Hmodes_program.
  }
  assert (Hsafe_program :
    ParallelLoop.trace_safe
      (parallelize_certified_dims certs
        ((tag_loop_stmt_at 0 raw_stmt, ctxt), vars'))).
  {
    rewrite parallelize_certified_dims_program_eq.
    exact Hsafe.
  }
  assert (Htrace_program :
    program_par_trace
      (parallelize_certified_dims certs
        ((tag_loop_stmt_at 0 raw_stmt, ctxt), vars'))
      env root_tr).
  {
    rewrite parallelize_certified_dims_program_eq.
    exact Htrace.
  }
  assert (Hroot_origin :
    root_origin_oracle ((pis, ctxt), vars') root_tr).
  {
    intros ip Hin.
    eapply annotated_codegen_many_raw_root_origin
      with
        (pl := parallelize_certified_dims certs
          ((tag_loop_stmt_at 0 raw_stmt, ctxt), vars'))
        (env := env) (root_tr := root_tr).
    - exact Hgen_root.
    - exact Hwf.
    - exact Hsafe_program.
    - exact Htrace_program.
    - exact Henv.
    - exact Hin.
  }
  assert (Henv0 :
    Datatypes.length env =
      (Datatypes.length (ParallelValidator.pprog_varctxt ((pis, ctxt), vars')) + 0)%nat).
  {
    simpl. lia.
  }
  (* Order that same trace recursively.  No restricted target semantics or
     global ordering premise is introduced here. *)
  pose proof
    (actual_multi_ordered_stmt
      (parallelize_certified_dims_stmt certs
        (tag_loop_stmt_at 0 raw_stmt))
      0 ((pis, ctxt), vars') certs env root_tr root_tr
      Htagged_final Hmodes_final Hcerts Henv0 Hsafe Hroot_origin
      (fun ip Hin => Hin) Htrace) as Hordered.
  econstructor.
  - reflexivity.
  - exact Hcompat.
  - exact Hna.
  - exact Hinit.
  - exists root_tr. split; assumption.
Qed.

Theorem annotated_codegen_many_raw_refines_prepared_codegen_certified :
  forall pp certs pl st st',
    mayReturn (annotated_codegen_many_raw pp certs) pl ->
    PolyLang.wf_pprog_affine pp ->
    Forall (parallel_codegen_cert_sound pp) certs ->
    ParallelLoop.trace_safe pl ->
    ParallelLoop.semantics pl st st' ->
    exists loop st'',
      mayReturn (PrepareCore.prepared_codegen_raw pp) loop /\
      Loop.semantics loop st st'' /\
      Instr.State.eq st' st''.
Proof.
  intros [[pis varctxt] vars] certs pl st st'
    Hgen Hwf Hcerts Hsafe Hsem.
  pose proof
    (annotated_codegen_many_raw_semantics_ordered
      pis varctxt vars certs pl st st' Hgen Hwf Hcerts Hsafe Hsem)
    as Hordered.
  destruct
    (annotated_codegen_many_raw_erase_eq
      ((pis, varctxt), vars) certs pl Hgen)
    as [loop [Hprepared Herase]].
  destruct (ParallelLoop.semantics_refines_erased pl st st' Hsafe Hordered)
    as [st'' [Herased Heq]].
  exists loop, st''.
  split; [exact Hprepared|].
  split.
  - rewrite <- Herase.
    eapply erase_to_loop_semantics. exact Herased.
  - exact Heq.
Qed.

(** The single-certificate endpoint is definitionally the singleton instance
    of the multi-certificate endpoint.  Keeping its proof as a wrapper avoids
    maintaining two certificate-to-trace arguments. *)
Lemma annotated_codegen_raw_many_singleton_eq :
  forall pp cert,
    annotated_codegen_raw pp cert =
    annotated_codegen_many_raw pp [cert].
Proof. reflexivity. Qed.

Theorem annotated_codegen_raw_root_origin :
  forall pis varctxt vars cert pl env root_tr,
    mayReturn
      (annotated_codegen_raw ((pis, varctxt), vars) cert) pl ->
    PolyLang.wf_pprog_affine ((pis, varctxt), vars) ->
    ParallelLoop.trace_safe pl ->
    program_par_trace pl env root_tr ->
    Datatypes.length env = Datatypes.length varctxt ->
    forall ip,
      In ip root_tr ->
      exists source_ip,
        generated_source_point_full
          ((pis, varctxt), vars)
          (ParallelValidator.schedule_width ((pis, varctxt), vars))
          ip source_ip.
Proof.
  intros pis varctxt vars cert pl env root_tr
    Hgen Hwf Hsafe Htrace Henv ip Hin.
  rewrite annotated_codegen_raw_many_singleton_eq in Hgen.
  eapply annotated_codegen_many_raw_root_origin; eauto.
Qed.

Theorem annotated_codegen_raw_semantics_ordered :
  forall pis varctxt vars cert pl st st',
    mayReturn (annotated_codegen_raw ((pis, varctxt), vars) cert) pl ->
    PolyLang.wf_pprog_affine ((pis, varctxt), vars) ->
    parallel_codegen_cert_sound ((pis, varctxt), vars) cert ->
    ParallelLoop.trace_safe pl ->
    ParallelLoop.semantics pl st st' ->
    ParallelLoop.ordered_semantics pl st st'.
Proof.
  intros pis varctxt vars cert pl st st' Hgen Hwf Hcert Hsafe Hsem.
  rewrite annotated_codegen_raw_many_singleton_eq in Hgen.
  eapply annotated_codegen_many_raw_semantics_ordered; eauto.
Qed.

Theorem annotated_codegen_raw_refines_prepared_codegen_certified :
  forall pp cert pl st st',
    mayReturn (annotated_codegen_raw pp cert) pl ->
    PolyLang.wf_pprog_affine pp ->
    parallel_codegen_cert_sound pp cert ->
    ParallelLoop.trace_safe pl ->
    ParallelLoop.semantics pl st st' ->
    exists loop st'',
      mayReturn (PrepareCore.prepared_codegen_raw pp) loop /\
      Loop.semantics loop st st'' /\
      Instr.State.eq st' st''.
Proof.
  intros pp cert pl st st' Hgen Hwf Hcert Hsafe Hsem.
  rewrite annotated_codegen_raw_many_singleton_eq in Hgen.
  eapply annotated_codegen_many_raw_refines_prepared_codegen_certified; eauto.
Qed.

(** * Checked cleanup endpoints *)

Theorem checked_annotated_codegen_correct_general :
  forall pol cert pl st st',
    mayReturn
      (checked_annotated_codegen
        (PolyLang.current_view_pprog pol) cert) (Okk pl) ->
    PolyLang.wf_pprog_general pol ->
    parallel_codegen_cert_sound
      (PolyLang.current_view_pprog pol) cert ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\
      Instr.State.eq st' st''.
Proof.
  intros pol cert pl st st' Hchecked Hwf Hcert Hsem.
  pose proof
    (checked_annotated_codegen_ok_inv
      (PolyLang.current_view_pprog pol) cert pl Hchecked)
    as Hchecked_inv.
  assert (Hraw_execution :
    exists pl_raw,
      mayReturn
        (annotated_codegen_raw (PolyLang.current_view_pprog pol) cert)
        pl_raw /\
      ParallelLoop.trace_safe pl_raw /\
      ParallelLoop.semantics pl_raw st st').
  {
    destruct Hchecked_inv
      as [[pl_raw [Hgen [Hclean Hstages]]] | [Hgen Hsafe_raw]].
    - destruct pl_raw as [[s_raw ctxt_raw] vars_raw].
      simpl in Hclean, Hstages. subst pl.
      destruct Hstages as
        [Hsafe0 [Hsafe1 [Hsafe2 [Hsafe3 [Hsafe4 Hsafe5]]]]].
      exists ((s_raw, ctxt_raw), vars_raw). repeat split; auto.
      eapply ParallelLoop.full_cleanup_semantics_reflect; eauto.
    - exists pl. repeat split; auto.
  }
  destruct Hraw_execution as [pl_raw [Hgen [Hsafe Hsem_raw]]].
  pose proof
    (PolyLang.wf_pprog_general_current_view_affine pol Hwf)
    as Hwf_current.
  destruct
    (annotated_codegen_raw_refines_prepared_codegen_certified
      (PolyLang.current_view_pprog pol) cert pl_raw st st'
      Hgen Hwf_current Hcert Hsafe Hsem_raw)
    as [loop [st'' [Hprepared [Hloop Heq]]]].
  exists st''. split.
  - eapply PrepareCore.prepared_codegen_raw_correct_general; eauto.
  - exact Heq.
Qed.

Theorem checked_annotated_codegen_many_correct_general_certified :
  forall pol certs pl st st',
    mayReturn
      (checked_annotated_codegen_many
        (PolyLang.current_view_pprog pol) certs) (Okk pl) ->
    PolyLang.wf_pprog_general pol ->
    Forall
      (parallel_codegen_cert_sound
        (PolyLang.current_view_pprog pol)) certs ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\
      Instr.State.eq st' st''.
Proof.
  intros pol certs pl st st' Hchecked Hwf Hcerts Hsem.
  pose proof
    (checked_annotated_codegen_many_ok_inv
      (PolyLang.current_view_pprog pol) certs pl Hchecked)
    as Hchecked_inv.
  assert (Hraw_execution :
    exists pl_raw,
      mayReturn
        (annotated_codegen_many_raw
          (PolyLang.current_view_pprog pol) certs) pl_raw /\
      ParallelLoop.trace_safe pl_raw /\
      ParallelLoop.semantics pl_raw st st').
  {
    destruct Hchecked_inv
      as [[pl_raw [Hgen [Hclean Hstages]]] | [Hgen Hsafe_raw]].
    - destruct pl_raw as [[s_raw ctxt_raw] vars_raw].
      simpl in Hclean, Hstages. subst pl.
      destruct Hstages as
        [Hsafe0 [Hsafe1 [Hsafe2 [Hsafe3 [Hsafe4 Hsafe5]]]]].
      exists ((s_raw, ctxt_raw), vars_raw). repeat split; auto.
      eapply ParallelLoop.full_cleanup_semantics_reflect; eauto.
    - exists pl. repeat split; auto.
  }
  destruct Hraw_execution as [pl_raw [Hgen [Hsafe Hsem_raw]]].
  pose proof
    (PolyLang.wf_pprog_general_current_view_affine pol Hwf)
    as Hwf_current.
  destruct
    (annotated_codegen_many_raw_refines_prepared_codegen_certified
      (PolyLang.current_view_pprog pol) certs pl_raw st st'
      Hgen Hwf_current Hcerts Hsafe Hsem_raw)
    as [loop [st'' [Hprepared [Hloop Heq]]]].
  exists st''. split.
  - eapply PrepareCore.prepared_codegen_raw_correct_general; eauto.
  - exact Heq.
Qed.

Theorem checked_vector_annotated_codegen_correct_general :
  forall pol cert pl st st',
    mayReturn (checked_vector_annotated_codegen (PolyLang.current_view_pprog pol) cert) (Okk pl) ->
    PolyLang.wf_pprog_general pol ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\
      Instr.State.eq st' st''.
Proof.
  intros pol cert pl st st' Hcodegen Hwf Hsem.
  destruct (checked_vector_annotated_codegen_ok_inv
              (PolyLang.current_view_pprog pol) cert pl Hcodegen)
    as [[pl_raw [Hann [Hclean [Hstages Hinner]]]] | [Hann [Hsafe _]]].
  - destruct pl_raw as [[s_raw ctxt_raw] vars_raw].
    simpl in Hclean, Hstages. subst pl.
    destruct Hstages as
      [Hsafe0 [Hsafe1 [Hsafe2 [Hsafe3 [Hsafe4 Hsafe5]]]]].
    eapply vector_annotated_codegen_raw_correct_general; eauto.
    eapply ParallelLoop.full_cleanup_semantics_reflect; eauto.
  - eapply vector_annotated_codegen_raw_correct_general; eauto.
Qed.

Theorem checked_annotated_codegen_many_correct_general :
  forall pol certs pl st st',
    mayReturn (checked_annotated_codegen_many (PolyLang.current_view_pprog pol) certs) (Okk pl) ->
    PolyLang.wf_pprog_general pol ->
    Forall
      (parallel_codegen_cert_sound
        (PolyLang.current_view_pprog pol)) certs ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\
      Instr.State.eq st' st''.
Proof.
  exact checked_annotated_codegen_many_correct_general_certified.
Qed.


End ParallelCodegenCorrect.

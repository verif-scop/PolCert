Require Import Bool.
Require Import List.
Require Import String.
Import ListNotations.
(* Require Import Errors. *)
Require Import Result.
Require Import Base.
Require Import PolyBase.  
Require Import PolyLang.
Require Import AST.
Require Import BinPos.
Require Import PolyTest.
Require Import Linalg.
Require Import PolyOperations.

Require Import Loop. 
Require Import PolyLoop.
Require Import ZArith.
Require Import Permutation.
Require Import Sorting.Sorted.
Require Import SelectionSort.

Require Import Extractor.
Require Import CodeGen. 
Require Import PrepareCodegen.
Require Import StrengthenDomain.
Require Import TilingRelation.
Require Import TilingBoolChecker.
Require Import TilingWitness.
Require Import PointWitness.
Require Import OpenScop.

Require Import Validator.
Require Import LibTactics.
Require Import sflib.


Require Import Convert.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Definition apply_total (A B: Type) (x: imp A) (f: A -> B) : imp B :=
   BIND x' <- x -;
   pure (f x').

Definition apply_partial (A B: Type)
                         (x: imp A) (f: A -> imp B) : imp B :=
   BIND x' <- x -;
   f x'.

Definition apply_partial_res (A B: Type)
                           (x: imp A) (f: A -> result B) (d: B): imp B := 
   BIND x' <- x -;
   res_to_alarm d (f x').

Declare Scope opt_scop.
                         
Notation "a @@ b" :=
   (apply_total _ _ a b) (at level 50, left associativity): opt_scop.

Notation "a @@@ b" :=
   (apply_partial _ _ a b) (at level 50, left associativity): opt_scop.

Notation "a @@@[ d ] b" :=
   (apply_partial_res _ _ a b d) (at level 50, left associativity): opt_scop.

Definition print {A: Type} (printer: A -> unit) (prog: A) : A :=
    let unused := printer prog in prog.
  
Local Open Scope string_scope.

Local Open Scope opt_scop.

Local Open Scope impure_scope.
Definition time {A B: Type} (name: string) (f: A -> B) : A -> B := f.


(** Pretty-printers (defined in Caml). *)
Parameter print_CompCertC_stmt: Csyntax.statement -> unit.
(* Parameter print_Loop: Loop.t -> unit.
Parameter print_Pol: PolyLang.t -> unit. *)

Require Import StateTy.
Require Import InstrTy.

Require Import PolIRs.
Require Import CInstr.
Module PolOpt (PolIRs: POLIRS).

(** loop -> pol -> pol -> loop *)
(* Module Loop := PolIRs.Loop.
Module Pol := PolIRs.PolyLang. *)

(* Public naming layer: the historical names are kept as compatibility
   aliases, but the optimizer code below uses the clearer names. *)
Definition affine_scheduler := PolIRs.affine_scheduler.
Definition scheduler := PolIRs.scheduler.
Definition export_for_phase_scheduler :=
  PolIRs.export_for_phase_scheduler.
Definition run_pluto_phase_pipeline :=
  PolIRs.run_pluto_phase_pipeline.
Definition run_pluto_identity_tiling_pipeline :=
  PolIRs.run_pluto_identity_tiling_pipeline.
Definition run_pluto_phase_pipeline_with_iss :=
  PolIRs.run_pluto_phase_pipeline_with_iss.
Definition run_pluto_post_tiling_affine_phase_pipeline :=
  PolIRs.run_pluto_post_tiling_affine_phase_pipeline.
Definition run_pluto_post_tiling_affine_phase_pipeline_with_iss :=
  PolIRs.run_pluto_post_tiling_affine_phase_pipeline_with_iss.
Definition infer_iss_from_source_scop :=
  PolIRs.infer_iss_from_source_scop.
Definition phase_scop_scheduler := PolIRs.phase_scop_scheduler.
Definition infer_tiling_witness_scops := PolIRs.infer_tiling_witness_scops.
Module Instr := PolIRs.Instr.
Module State := PolIRs.State.
Module Ty := PolIRs.Ty.
Module LoopIR := PolIRs.Loop.
Module PolyLang := PolIRs.PolyLang.
Definition ident := Instr.ident.

Module Extractor := Extractor PolIRs.
Module CodeGen := CodeGen PolIRs.
Module PrepareCore := PrepareCodegen PolIRs.
Module Strengthen := StrengthenDomain PolIRs.
Module ValidatorCore := Validator PolIRs.
Module Prepare := PrepareCore.
(* Definition codegen (pol: Pol.t): result Loop.t := 
   Okk Loop.dummy. *)

(* Definition validate_cpol (pol1 pol2: PolIRs.PolyLang.t)  *)
  (* :=  *)
  
  (* . * FIXME *)
  
Definition checked_affine_schedule (pol: PolIRs.PolyLang.t): imp PolIRs.PolyLang.t := 
   match affine_scheduler pol with 
   | Okk pol' => 
      BIND res <- (ValidatorCore.validate pol pol') -;
      if res then pure (pol') 
      else res_to_alarm pol (Err "Scheduler validation failed.")
   | Err msg => res_to_alarm pol (Err msg)
   end.

Definition scheduler' := checked_affine_schedule.

Definition affine_only_opt_prepared_from_poly (pol: PolyLang.t): imp LoopIR.t :=
  BIND pol' <- checked_affine_schedule pol -;
  PrepareCore.prepared_codegen pol'.

Definition identity_opt_prepared_from_poly (pol: PolyLang.t): imp LoopIR.t :=
  PrepareCore.prepared_codegen pol.

Definition affine_opt_prepared_from_poly := affine_only_opt_prepared_from_poly.

Definition try_verified_tiling_after_phase_mid
    (pol_mid: PolyLang.t)
    (mid_scop after_scop: OpenScop): imp LoopIR.t :=
  match infer_tiling_witness_scops mid_scop after_scop with
  | Err _ =>
      PrepareCore.prepared_codegen pol_mid
  | Okk ws =>
      match ValidatorCore.import_canonical_tiled_after_poly pol_mid after_scop ws with
      | Err _ =>
          PrepareCore.prepared_codegen pol_mid
      | Okk pol_after =>
          BIND ok <- ValidatorCore.checked_tiling_validate_poly pol_mid pol_after ws -;
          if ok then
            PrepareCore.prepared_codegen (PolyLang.current_view_pprog pol_after)
          else
            PrepareCore.prepared_codegen pol_mid
      end
  end.

Definition try_tiling_prepared_from_phase := try_verified_tiling_after_phase_mid.

Definition try_phase_pipeline_from_source_pol
    (pol_source: PolyLang.t)
    (phase_runner: OpenScop -> result (OpenScop * OpenScop))
    (before_scop: OpenScop): imp LoopIR.t :=
  match phase_runner before_scop with
  | Err _ =>
      affine_only_opt_prepared_from_poly pol_source
  | Okk (mid_scop, after_scop) =>
      match PolyLang.from_openscop_like_source pol_source mid_scop with
      | Err _ =>
          affine_only_opt_prepared_from_poly pol_source
      | Okk pol_mid =>
          BIND affine_ok <- ValidatorCore.validate pol_source pol_mid -;
          if affine_ok then
            try_verified_tiling_after_phase_mid pol_mid mid_scop after_scop
          else
            affine_only_opt_prepared_from_poly pol_source
      end
  end.

Definition has_nonscalar_stmt (pol: PolyLang.t) : bool :=
  let '((pis, _), _) := pol in
  existsb (fun pi => negb (Nat.eqb pi.(PolyLang.pi_depth) O)) pis.

Definition identity_tiling_generic_opt_prepared_from_poly
    (pol: PolyLang.t): imp LoopIR.t :=
  if has_nonscalar_stmt pol then
    match export_for_phase_scheduler pol with
    | None =>
        affine_only_opt_prepared_from_poly pol
    | Some before_scop =>
        try_phase_pipeline_from_source_pol
          pol
          run_pluto_identity_tiling_pipeline
          before_scop
    end
  else
    PrepareCore.prepared_codegen pol.

Definition try_checked_iss_identity_tiling_generic_phase_pipeline_from_poly
    (pol: PolyLang.t)
    (before_scop: OpenScop): imp LoopIR.t :=
  match infer_iss_from_source_scop pol before_scop with
  | Okk (Some (pol_iss, w)) =>
      if ValidatorCore.checked_iss_complete_cut_shape_validate pol pol_iss w then
        BIND iss_wf <- ValidatorCore.check_wf_polyprog pol_iss -;
        if iss_wf then
          match export_for_phase_scheduler pol_iss with
          | Some iss_scop =>
              try_phase_pipeline_from_source_pol
                pol_iss
                run_pluto_identity_tiling_pipeline
                iss_scop
          | None =>
              PrepareCore.prepared_codegen pol_iss
          end
        else
          identity_tiling_generic_opt_prepared_from_poly pol
      else
        identity_tiling_generic_opt_prepared_from_poly pol
  | _ =>
      identity_tiling_generic_opt_prepared_from_poly pol
  end.

Definition identity_tiling_generic_opt_prepared_from_poly_with_iss
    (pol: PolyLang.t): imp LoopIR.t :=
  if has_nonscalar_stmt pol then
    match export_for_phase_scheduler pol with
    | None =>
        affine_only_opt_prepared_from_poly pol
    | Some before_scop =>
        try_checked_iss_identity_tiling_generic_phase_pipeline_from_poly
          pol before_scop
    end
  else
    PrepareCore.prepared_codegen pol.

Definition try_checked_iss_phase_pipeline_from_poly
    (pol: PolyLang.t)
    (before_scop: OpenScop): imp LoopIR.t :=
  match infer_iss_from_source_scop pol before_scop with
  | Okk (Some (pol_iss, w)) =>
      if ValidatorCore.checked_iss_complete_cut_shape_validate pol pol_iss w then
        BIND iss_wf <- ValidatorCore.check_wf_polyprog pol_iss -;
        if iss_wf then
          match export_for_phase_scheduler pol_iss with
          | Some iss_scop =>
              try_phase_pipeline_from_source_pol
                pol_iss run_pluto_phase_pipeline iss_scop
          | None =>
              res_to_alarm LoopIR.dummy (Err "Cannot export checked ISS program.")
          end
        else
          try_phase_pipeline_from_source_pol
            pol
            run_pluto_phase_pipeline
            before_scop
      else
        try_phase_pipeline_from_source_pol
          pol
          run_pluto_phase_pipeline
          before_scop
  | _ =>
      try_phase_pipeline_from_source_pol
        pol
        run_pluto_phase_pipeline
        before_scop
  end.

Definition phase_pipeline_opt_prepared_from_poly_no_iss
    (pol: PolyLang.t): imp LoopIR.t :=
  if has_nonscalar_stmt pol then
    match export_for_phase_scheduler pol with
    | None =>
        affine_only_opt_prepared_from_poly pol
    | Some before_scop =>
        try_phase_pipeline_from_source_pol
          pol
          run_pluto_phase_pipeline
          before_scop
    end
  else
    PrepareCore.prepared_codegen pol.

Definition phase_pipeline_opt_prepared_from_poly_with_iss
    (pol: PolyLang.t): imp LoopIR.t :=
  if has_nonscalar_stmt pol then
    match export_for_phase_scheduler pol with
    | None =>
        affine_only_opt_prepared_from_poly pol
    | Some before_scop =>
        try_checked_iss_phase_pipeline_from_poly pol before_scop
    end
  else
    PrepareCore.prepared_codegen pol.

Definition phase_pipeline_opt_prepared_from_poly :=
  phase_pipeline_opt_prepared_from_poly_no_iss.

Definition phase_opt_prepared_from_poly := phase_pipeline_opt_prepared_from_poly.
Definition phase_opt_prepared_from_poly_with_iss :=
  phase_pipeline_opt_prepared_from_poly_with_iss.

Definition phase_pipeline_opt_prepared (loop: LoopIR.t): imp LoopIR.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (Extractor.extractor loop) -;
  let pol := Strengthen.strengthen_pprog pol0 in
  phase_pipeline_opt_prepared_from_poly pol.

Definition identity_opt_prepared (loop: LoopIR.t): imp LoopIR.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (Extractor.extractor loop) -;
  let pol := Strengthen.strengthen_pprog pol0 in
  identity_opt_prepared_from_poly pol.

Definition identity_tiling_generic_opt_prepared (loop: LoopIR.t): imp LoopIR.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (Extractor.extractor loop) -;
  let pol := Strengthen.strengthen_pprog pol0 in
  identity_tiling_generic_opt_prepared_from_poly pol.

Definition identity_tiling_generic_opt_prepared_with_iss
    (loop: LoopIR.t): imp LoopIR.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (Extractor.extractor loop) -;
  let pol := Strengthen.strengthen_pprog pol0 in
  identity_tiling_generic_opt_prepared_from_poly_with_iss pol.

Definition affine_only_opt_prepared (loop: LoopIR.t): imp LoopIR.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (Extractor.extractor loop) -;
  let pol := Strengthen.strengthen_pprog pol0 in
  affine_only_opt_prepared_from_poly pol.

Definition affine_opt_prepared := affine_only_opt_prepared.

Definition phase_pipeline_opt_prepared_with_iss (loop: LoopIR.t): imp LoopIR.t :=
  BIND pol0 <- res_to_alarm PolyLang.dummy (Extractor.extractor loop) -;
  let pol := Strengthen.strengthen_pprog pol0 in
  phase_opt_prepared_from_poly_with_iss pol.

Definition phase_opt_prepared := phase_pipeline_opt_prepared.
Definition phase_opt_prepared_with_iss := phase_pipeline_opt_prepared_with_iss.


Lemma scheduler'_correct:
   forall pol  st1 st2,
      WHEN pol' <- scheduler' pol THEN
      PolyLang.instance_list_semantics pol' st1 st2 ->
      exists st2',
      PolyLang.instance_list_semantics pol st1 st2' /\ State.eq st2 st2'.
Proof.
   intros. intros pol' SCHE SEM'.
   unfold scheduler', checked_affine_schedule in SCHE.

   destruct (affine_scheduler pol) eqn:SCHE'.
   2: {
      simpls.
      eapply mayReturn_alarm in SCHE; easy.
   }
   bind_imp_destruct SCHE res Hval.
   destruct res; simpls.
   2: {
      eapply mayReturn_alarm in SCHE; easy.
   }
   eapply mayReturn_pure in SCHE. subst.
   eapply ValidatorCore.validate_correct in Hval; eauto.
Qed.

Lemma Extract_Schedule_correct:
   forall loop pol st1 st2,
      Extractor.extractor loop = Okk pol ->
      WHEN pol' <- scheduler' pol THEN
      PolyLang.instance_list_semantics pol' st1 st2 ->
      exists st2',
      LoopIR.semantics loop st1 st2' /\ State.eq st2 st2'.
Proof.
   intros. intros pol' SCHE SEM'.
   eapply scheduler'_correct in SCHE.
   eapply SCHE in SEM'. clear SCHE.
   destruct SEM' as [st2' [SEM' EQ]].

   eapply Extractor.extractor_correct in H. 
   2: { 
      eapply SEM'.
   }
   destruct H as [st2'' [H' EQ']].
   exists st2''.
   split; eauto.
   eapply State.eq_trans; eauto.
Qed.   

Definition Opt_prepared (loop: LoopIR.t): imp LoopIR.t :=
  phase_opt_prepared loop.

Definition Opt_prepared_with_iss (loop: LoopIR.t): imp LoopIR.t :=
  phase_opt_prepared_with_iss loop.

Definition Opt : LoopIR.t -> imp LoopIR.t := Opt_prepared.
Definition Opt_with_iss : LoopIR.t -> imp LoopIR.t := Opt_prepared_with_iss.

Lemma extractor_success_wf_pprog_affine:
  forall loop pol,
    Extractor.extractor loop = Okk pol ->
    PolyLang.wf_pprog_affine pol.
Proof.
  intros loop [[pis varctxt] vars] Hext.
  unfold PolyLang.wf_pprog_affine.
  split.
  - eapply Extractor.extractor_success_implies_varctxt_le_vars; eauto.
  - intros pi Hin.
    pose proof (Extractor.extractor_success_implies_wf_check loop (pis, varctxt, vars) Hext) as Hchk.
    simpl in Hchk.
    eapply Extractor.check_extracted_wf_spec in Hchk.
    destruct Hchk as [_ Hall].
    eapply forallb_forall in Hall; eauto.
    eapply ValidatorCore.check_wf_polyinstr_affine_correct; eauto.
Qed.

Lemma extractor_success_wf_pprog:
  forall loop pol,
    Extractor.extractor loop = Okk pol ->
    PolyLang.wf_pprog pol.
Proof.
  intros loop pol Hext.
  eapply PolyLang.wf_pprog_affine_implies_wf_pprog.
  eapply extractor_success_wf_pprog_affine; eauto.
Qed.

Lemma scheduler'_preserve_wf:
  forall pol pol',
    PolyLang.wf_pprog_affine pol ->
    WHEN pol'' <- scheduler' pol THEN
    pol'' = pol' ->
    PolyLang.wf_pprog_affine pol'.
Proof.
  intros pol pol' Hwf pol'' Hsched Heq.
  subst pol''.
  unfold scheduler', checked_affine_schedule in Hsched.
  destruct (affine_scheduler pol) eqn:Hschedsrc.
  2: {
    exfalso.
    eapply mayReturn_alarm in Hsched.
    exact Hsched.
  }
  bind_imp_destruct Hsched res Hval.
  destruct res.
  2: {
    exfalso.
    eapply mayReturn_alarm in Hsched.
    exact Hsched.
  }
  eapply mayReturn_pure in Hsched. subst.
  pose proof (ValidatorCore.validate_preserve_wf_pprog pol pol' _ Hval eq_refl) as [_ Hwf'].
  exact Hwf'.
Qed.

Theorem Extract_Schedule_Prepared_correct:
  forall loop pol st1 st2,
    Extractor.extractor loop = Okk pol ->
    WHEN pol' <- scheduler' (Strengthen.strengthen_pprog pol) THEN
    PolyLang.wf_pprog_affine pol' ->
    PolyLang.semantics (PrepareCore.prepare_codegen pol') st1 st2 ->
    exists st2',
      LoopIR.semantics loop st1 st2' /\ State.eq st2 st2'.
Proof.
  intros loop pol st1 st2 Hext pol' Hsched Hwf Hsem.
  eapply PrepareCore.prepare_codegen_semantics_correct in Hsem; eauto.
  pose proof (scheduler'_correct (Strengthen.strengthen_pprog pol) st1 st2 pol' Hsched Hsem)
    as Hsched_corr.
  destruct Hsched_corr as [st_mid [Hips Heq]].
  eapply Strengthen.instance_list_semantics_unstrengthen in Hips.
  pose proof (Extractor.extractor_correct loop pol st1 st_mid Hext Hips) as Hext_corr.
  destruct Hext_corr as [st_src [Hloop Heq_src]].
  exists st_src. split; auto.
  eapply State.eq_trans; eauto.
Qed.

Definition checked_tiling_validate := ValidatorCore.checked_tiling_validate_poly.
Definition to_tiling_pprog := ValidatorCore.to_tiling_pprog.
Definition outer_to_tiling_pprog := ValidatorCore.outer_to_tiling_pprog.
Definition check_pprog_tiling_sourceb :=
  ValidatorCore.check_pprog_tiling_sourceb.
Definition check_wf_polyprog := ValidatorCore.check_wf_polyprog.
Definition check_wf_polyprog_affine_correct :=
  ValidatorCore.AffineCore.check_wf_polyprog_affine_correct.
Definition check_wf_polyprog_correct := ValidatorCore.check_wf_polyprog_correct.
Definition check_wf_polyprog_general := ValidatorCore.check_wf_polyprog_general.
Definition EqDom := ValidatorCore.EqDom.
Definition check_valid_access := ValidatorCore.check_valid_access.
Definition validate_instr_list := ValidatorCore.validate_instr_list.
Definition validate := ValidatorCore.validate.
Definition validate_general := ValidatorCore.validate_general.

Lemma checked_tiling_validate_correct :
  forall before after ws st1 st2,
    mayReturn (checked_tiling_validate before after ws) true ->
    PolyLang.instance_list_semantics after st1 st2 ->
    exists st2',
      PolyLang.instance_list_semantics before st1 st2' /\
      State.eq st2 st2'.
Proof.
  exact ValidatorCore.checked_tiling_validate_poly_correct.
Qed.

Lemma checked_tiling_current_view_prepared_codegen_correct :
  forall before after ws st1 st2,
    mayReturn (checked_tiling_validate before after ws) true ->
    PolyLang.wf_pprog_general after ->
    forall loop,
    mayReturn
      (PrepareCore.prepared_codegen (PolyLang.current_view_pprog after))
      loop ->
    LoopIR.semantics loop st1 st2 ->
    exists st2',
      PolyLang.instance_list_semantics before st1 st2' /\
      State.eq st2 st2'.
Proof.
  intros before after ws st1 st2 Hcheck Hwf_after loop Hcodegen Hloop.
  pose proof
    (PrepareCore.prepared_codegen_correct_general
       after st1 st2 loop Hcodegen Hwf_after Hloop)
    as Hsem_after.
  eapply checked_tiling_validate_correct; eauto.
Qed.

Lemma affine_opt_prepared_from_poly_correct:
  forall pol st st',
    PolyLang.wf_pprog_affine pol ->
    WHEN loop' <- affine_opt_prepared_from_poly pol THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol st st' Hwf loop' Hopt Hloop.
  unfold affine_opt_prepared_from_poly in Hopt.
  bind_imp_destruct Hopt pol' Hsched.
  pose proof (scheduler'_preserve_wf pol pol' Hwf pol' Hsched eq_refl) as Hwf'.
  pose proof
    (PrepareCore.prepared_codegen_correct pol' st st' loop' Hopt Hwf' Hloop)
    as Hsem_sched.
  pose proof
    (scheduler'_correct pol st st' pol' Hsched Hsem_sched)
    as Hsched_corr.
  destruct Hsched_corr as [st_src [Hsrc_sem Heq_src]].
  exists st_src.
  split; assumption.
Qed.

Lemma try_tiling_prepared_from_phase_correct:
  forall pol_mid mid_scop after_scop st st',
    PolyLang.wf_pprog_affine pol_mid ->
    WHEN loop' <- try_tiling_prepared_from_phase pol_mid mid_scop after_scop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol_mid st st'' /\ State.eq st' st''.
Proof.
  intros pol_mid mid_scop after_scop st st' Hwf_mid loop' Hopt Hloop.
  unfold try_tiling_prepared_from_phase,
    try_verified_tiling_after_phase_mid in Hopt.
  destruct (infer_tiling_witness_scops mid_scop after_scop) as [ws|msg] eqn:Hws.
  - destruct
      (ValidatorCore.import_canonical_tiled_after_poly pol_mid after_scop ws)
      as [pol_after|msg_after] eqn:Hafter.
    + bind_imp_destruct Hopt ok Hcheck.
      destruct ok.
      * pose proof
          (ValidatorCore.checked_tiling_validate_poly_implies_wf_after
             pol_mid pol_after ws Hcheck)
          as Hwf_after.
        eapply checked_tiling_current_view_prepared_codegen_correct; eauto.
      * pose proof
          (PrepareCore.prepared_codegen_correct
             pol_mid st st' loop' Hopt Hwf_mid Hloop)
          as Hmid_sem.
        exists st'. split; auto. eapply State.eq_refl.
    + pose proof
        (PrepareCore.prepared_codegen_correct
           pol_mid st st' loop' Hopt Hwf_mid Hloop)
        as Hmid_sem.
      exists st'. split; auto. eapply State.eq_refl.
  - pose proof
      (PrepareCore.prepared_codegen_correct
         pol_mid st st' loop' Hopt Hwf_mid Hloop)
      as Hmid_sem.
    exists st'. split; auto. eapply State.eq_refl.
Qed.

Lemma try_phase_pipeline_from_source_pol_correct:
  forall pol_source phase_runner before_scop st st',
    PolyLang.wf_pprog_affine pol_source ->
    WHEN loop' <-
      try_phase_pipeline_from_source_pol pol_source phase_runner before_scop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol_source st st'' /\
      State.eq st' st''.
Proof.
  intros pol_source phase_runner before_scop st st' Hwf_source loop' Hopt Hloop.
  unfold try_phase_pipeline_from_source_pol in Hopt.
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
          (try_tiling_prepared_from_phase_correct
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
      * eapply affine_opt_prepared_from_poly_correct; eauto.
    + eapply affine_opt_prepared_from_poly_correct; eauto.
  - eapply affine_opt_prepared_from_poly_correct; eauto.
Qed.

Lemma identity_tiling_generic_opt_prepared_from_poly_correct:
  forall pol st st',
    PolyLang.wf_pprog_affine pol ->
    WHEN loop' <- identity_tiling_generic_opt_prepared_from_poly pol THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\
      State.eq st' st''.
Proof.
  intros pol st st' Hwf loop' Hopt Hloop.
  unfold identity_tiling_generic_opt_prepared_from_poly in Hopt.
  destruct (has_nonscalar_stmt pol) eqn:Hnonscalar.
  - destruct (export_for_phase_scheduler pol) as [before_scop|] eqn:Hscop.
    + eapply try_phase_pipeline_from_source_pol_correct; eauto.
    + eapply affine_opt_prepared_from_poly_correct; eauto.
  - pose proof
      (PrepareCore.prepared_codegen_correct
         pol st st' loop' Hopt Hwf Hloop)
      as Hsem.
    exists st'. split; auto. apply State.eq_refl.
Qed.

Close Scope impure_scope.
Close Scope opt_scop.

End PolOpt.

(* Require Import CState.
Require Import PolyLoop.
Require Import Loop. *)

(** Instantiate all IRs PolOpt use *)
(* Module CPolIRs <: POLIRS with Module Instr := CInstr.
   Module Instr := CInstr.
   Module State := State.
   Module PolyLang := PolyLang CInstr.
   Module PolyLoop := PolyLoop CInstr.
   Module Loop := Loop CInstr.
End CPolIRs. *)

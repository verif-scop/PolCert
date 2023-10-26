Require Import Bool.
Require Import List.
Import ListNotations.
Require Import Base.
Require Import PolyBase.  
Require Import PolyLang.
Require Import AST.
Require Import BinPos.
Require Import PolyTest.
Require Import Linalg.
Require Import PolyOperations.
Require Import ImpureAlarmConfig.
(* Require Import CLoop. *)
Require Import ZArith.
Require Import Permutation.
Require Import Sorting.Sorted.
Require Import SelectionSort.
Require Import Misc.

Require Import FunctionalExtensionality.
Require Import Lia.
Require Import LibTactics.
Require Import sflib.
(* Require Import Coqlibext. *)

Require Import PolIRs.
Module Validator (PolIRs: POLIRS).

Module Instr := PolIRs.Instr.
Module State := PolIRs.State.
Module Ty := PolIRs.Ty.
Module PolyLang := PolIRs.PolyLang.
Definition ident := Instr.ident.

Definition check_wf_polyinstr (pi: PolyLang.PolyInstr) (env: list ident) (vars: list (ident * Ty.t)) := 
  let env_dim := length env in 
  let iter_dim := (pi.(PolyLang.pi_depth)) in
  let domain := pi.(PolyLang.pi_poly) in
  let domain_len := length domain in 
  let vars_dim := length vars in
  if negb (Instr.check_never_written env pi.(PolyLang.pi_instr)) then false else
  if negb (env_dim + iter_dim <=? vars_dim) then false else 
  (** schedule iterators *)
  if negb (poly_nrl (PolyLang.pi_poly pi) <=? length vars) then false else  
  if negb (poly_nrl (PolyLang.pi_schedule pi) <=? length vars) then false else 
  (* domain cols = env_dim + iter_dim *)
  if negb (check_listzzs_cols domain (env_dim + iter_dim))
  then false else 
  (* transformation cols = env_dim + iter_dim *)
  if negb (check_listzzs_cols (pi.(PolyLang.pi_transformation)) (env_dim + iter_dim))
    then false else 
  (* schedule cols = env_dim + iter_dim *)
  if negb (check_listzzs_cols pi.(PolyLang.pi_schedule) (env_dim + iter_dim)) 
  then false 
  (* waccess/raccess cols = env_dim + iter_dim *)
  else 
  if existsb (fun (waccess: AccessFunction) => 
    let (arrid, waccess_aff_func) := waccess in 
      if negb (check_listzzs_cols waccess_aff_func (env_dim + iter_dim)) 
      then true else false 
    ) pi.(PolyLang.pi_waccess)  
  then false else
  if existsb (fun (raccess: AccessFunction) => 
      let (arrid, raccess_aff_func) := raccess in 
        if negb (check_listzzs_cols raccess_aff_func (env_dim + iter_dim)) 
        then true else false 
    ) pi.(PolyLang.pi_raccess) 
  then false else 
  let tf_len_ok := ((length (pi.(PolyLang.pi_transformation))) =? (env_dim + iter_dim))%nat in 
  tf_len_ok.

Definition check_wf_polyprog (pp: PolyLang.t) := 
  let '(pil, varctxt, vars) := pp in   
  let pil_dim := length pil in
  let varctxt_dim := length varctxt in 
  let vars_dim := length vars in 
  pure (Nat.leb varctxt_dim vars_dim && Nat.ltb 0 pil_dim && forallb (fun pi => check_wf_polyinstr pi varctxt vars) pil).

Definition EqDomInstr (pi1 pi2: PolyLang.PolyInstr) := 
  let iters_eq := Nat.eqb pi1.(PolyLang.pi_depth) pi2.(PolyLang.pi_depth) in 
  let inst_eq := Instr.eqb pi1.(PolyLang.pi_instr) pi2.(PolyLang.pi_instr) in 
  let dom_eq := listzzs_strict_eqb pi1.(PolyLang.pi_poly) pi2.(PolyLang.pi_poly) in 
  let trans_eq := listzzs_strict_eqb pi1.(PolyLang.pi_transformation) pi2.(PolyLang.pi_transformation) in
  let raccess_eq := access_list_strict_eqb pi1.(PolyLang.pi_raccess) pi2.(PolyLang.pi_raccess) in 
  let waccess_eq := access_list_strict_eqb pi1.(PolyLang.pi_waccess) pi2.(PolyLang.pi_waccess) in 
  iters_eq && inst_eq && dom_eq && trans_eq && raccess_eq && waccess_eq.

  Fixpoint ctxt_ty_eqb (vs1 vs2: list (ident * Ty.t)) :=
  match vs1, vs2 with 
  | [], [] => true 
  | (v1, ty1)::vs1', (v2, ty2)::vs2' => 
    Instr.ident_eqb v1 v2 && 
      Ty.eqb ty1 ty2 && ctxt_ty_eqb vs1' vs2' 
  | _, _ => false 
  end.

Lemma ctxt_ty_eqb_eq: 
  forall vs1 vs2, 
    ctxt_ty_eqb vs1 vs2 = true -> 
    vs1 = vs2.
Proof.
  induction vs1.
  - intros. simpls. destruct vs2; tryfalse. trivial.
  - intros. simpls. 
    destruct a.
    destruct vs2; tryfalse. 
    destruct p.
    do 2 rewrite andb_true_iff in H. 
    destruct H as ((H1 & H2) & H3).
    eapply Instr.ident_eqb_eq in H1.
    eapply Ty.eqb_eq in H2.
    eapply IHvs1 in H3.
    subst. econs; eauto.
Qed.

Fixpoint EqDomInstList (pil1 pil2: list PolyLang.PolyInstr) := 
  match pil1, pil2 with 
  | pi1::pil1', pi2::pil2' => 
    if EqDomInstr pi1 pi2 then EqDomInstList pil1' pil2' else false 
  | [], [] => true 
  | _, _ => false
  end .

Fixpoint ctxt_eqb (l1 l2: list ident): bool :=
  match l1, l2 with
  | id1::l1', id2::l2' =>
    Instr.ident_eqb id1 id2 && ctxt_eqb l1' l2'
  | [], [] => true
  | _, _ => false
  end.

Lemma ctxt_eqb_eq:
  forall l1 l2, 
    ctxt_eqb l1 l2 = true <-> l1 = l2.
Proof.
  induction l1.
  - intros. simpls. 
    destruct l2; split; intro; tryfalse; eauto.
  - intros. simpls.
    destruct l2 eqn:Hl2; split; intro; tryfalse.
    +  
    rewrite andb_true_iff in H.
    destruct H. eapply Instr.ident_eqb_eq in H. subst.
    f_equal. eapply IHl1; trivial.
    +
    rewrite andb_true_iff. inv H. split.
    eapply Instr.ident_eqb_eq; trivial.
    eapply IHl1; trivial.
Qed.


Definition EqDom (pp1 pp2: PolyLang.t) := 
  let '(pil1, varctxt1, vars1) := pp1 in 
  let '(pil2, varctxt2, vars2) := pp2 in   
  let varctxt_eq := ctxt_eqb varctxt1 varctxt2 in 
  let vars_eq := ctxt_ty_eqb vars1 vars2 in 
  let instr_len_eq := Nat.eqb (length pil1) (length pil2) in 
  let instrs_eqdom := EqDomInstList pil1 pil2 in
  pure (varctxt_eq && vars_eq && instr_len_eq && instrs_eqdom)  
.

Fixpoint forallb_imp {A} (f: A -> imp bool) (l: list A): (imp bool) :=
  match l with 
  | [] => pure true
  | a::l' => 
    BIND b <- f a -;
    if b then forallb_imp f l' else pure false
  end.

Lemma forallb_imp_true_head_true:
  forall {A} (f: A -> imp bool) (a: A) (l: list A),
  mayReturn (forallb_imp f (a::l)) true -> 
  mayReturn (f a) true.
Proof.
  intros. simpls.
  bind_imp_destruct H b H'.
  destruct b; trivial.
  eapply mayReturn_pure in H; tryfalse.
Qed.

Lemma forallb_imp_true_tail_true:
  forall {A} (f: A -> imp bool) (a: A) (l: list A),
  mayReturn (forallb_imp f (a::l)) true -> 
  mayReturn (forallb_imp f l) true.
Proof.
  intros. 
  simpls. 
  bind_imp_destruct H b H'. 
  destruct b; eauto.
  eapply mayReturn_pure in H; tryfalse.
Qed.

Definition validate_lt_ge_pair (pol_lt pol_ge sameloc_enveq_indom_pol: polyhedron) := 
  BIND sameloc_pol_lt <- poly_inter pol_lt sameloc_enveq_indom_pol -;
  BIND sameloc_pol_lt_ge <- poly_inter sameloc_pol_lt pol_ge -;
  BIND isbot <- isBottom sameloc_pol_lt_ge -;
  pure (isbot).

Definition validate_two_accesses_helper (old_sched_lt_polys new_sched_ge_polys: list polyhedron) (sameloc_enveq_indom_pol: polyhedron) := 
  forallb_imp (
    fun pol_lt =>
    forallb_imp (
      fun pol_ge => 
        validate_lt_ge_pair pol_lt pol_ge sameloc_enveq_indom_pol
    )
    new_sched_ge_polys
  ) old_sched_lt_polys.

Definition validate_two_accesses (a1 a2: AccessFunction) (tf1 tf2: AffineFunction) (env_eq_in_dom_poly: polyhedron) (old_sched_lt_polys new_sched_ge_polys: list polyhedron)
(dim1 dim2: nat):= 
  let (id1, loc1) := a1 in 
  let (id2, loc2) := a2 in 
  if negb (Pos.eqb id1 id2) then pure true else
  (* construct polyhedron for same array-access subscripts *)
  let sameloc := make_poly_eq (matrix_product loc1 tf1) (matrix_product loc2 tf2) dim1 dim2 [] in 
  BIND sameloc_enveq_indom_pol <- poly_inter sameloc env_eq_in_dom_poly -;  
  (* check if lexicographic order is violated for dependent accesses *)
  validate_two_accesses_helper old_sched_lt_polys new_sched_ge_polys sameloc_enveq_indom_pol.


Definition validate_two_instrs (pi1 pi2: PolyLang.PolyInstr_ext) (env_dim: nat) := 
  let iter_dim1 := ((pi1.(PolyLang.pi_depth_ext))) in 
  let iter_dim2 := ((pi2.(PolyLang.pi_depth_ext))) in 
  let dom_dim1 := (env_dim + iter_dim1) % nat in 
  let dom_dim2 := (env_dim + iter_dim2) % nat in 
  (** construct poly(s), for: *)
  (** two instances old timestamp less-than p1 < p2 *)
  (** two instances new timestamp greater-or-equal p1 >= p2 *)
  let old_sched_lt_polys := make_poly_lt (pi1.(PolyLang.pi_schedule1_ext)) (pi2.(PolyLang.pi_schedule1_ext)) dom_dim1 dom_dim2 [] in 
  let new_sched_ge_polys := make_poly_ge (pi1.(PolyLang.pi_schedule2_ext)) (pi2.(PolyLang.pi_schedule2_ext)) dom_dim1 dom_dim2 [] in 
  (** construct poly for equal environment *)
  let env_eq_poly := make_poly_env_eq env_dim iter_dim1 iter_dim2 in
  (** construct poly for two instances in domain *)
  BIND in_domain_poly <- poly_product pi1.(PolyLang.pi_poly_ext) pi2.(PolyLang.pi_poly_ext) dom_dim1 dom_dim2 -; 
  BIND pol <- poly_inter env_eq_poly in_domain_poly -;

  BIND res1 <- forallb_imp (
    fun waccess1 => forallb_imp (fun waccess2 =>
      validate_two_accesses waccess1 waccess2 pi1.(PolyLang.pi_transformation_ext) pi2.(PolyLang.pi_transformation_ext) pol old_sched_lt_polys new_sched_ge_polys dom_dim1 dom_dim2
    ) pi2.(PolyLang.pi_waccess_ext)
  ) pi1.(PolyLang.pi_waccess_ext) -;
  
  BIND res2 <- forallb_imp (
    fun waccess1 => forallb_imp (fun raccess2 =>
      validate_two_accesses waccess1 raccess2 pi1.(PolyLang.pi_transformation_ext) pi2.(PolyLang.pi_transformation_ext) pol old_sched_lt_polys new_sched_ge_polys dom_dim1 dom_dim2
    ) pi2.(PolyLang.pi_raccess_ext) 
  ) pi1.(PolyLang.pi_waccess_ext) -;

  BIND res3 <- forallb_imp (
    fun raccess1 => forallb_imp (fun waccess2 =>
      validate_two_accesses raccess1 waccess2 pi1.(PolyLang.pi_transformation_ext) pi2.(PolyLang.pi_transformation_ext) pol old_sched_lt_polys new_sched_ge_polys dom_dim1 dom_dim2
    ) pi2.(PolyLang.pi_waccess_ext)
  ) pi1.(PolyLang.pi_raccess_ext) -;

  pure (res1 && res2 && res3).

Fixpoint validate_instr_and_list (pi_ext: PolyLang.PolyInstr_ext) (pil_ext: list PolyLang.PolyInstr_ext) (env_dim: nat) := 
  match pil_ext with
    | [] => pure true 
    | pi'_ext :: pil'_ext =>
      BIND res1 <- validate_two_instrs pi_ext pi'_ext env_dim -;
      if eqb res1 false then pure false else 
      BIND res2 <- validate_two_instrs pi'_ext pi_ext env_dim -; 
      if eqb res2 false then pure false else 
      BIND res3 <- validate_instr_and_list pi_ext pil'_ext env_dim -;
      pure (res3)
    end.

Fixpoint validate_instr_list (pil_ext: list PolyLang.PolyInstr_ext) (env_dim: nat):= 
  match pil_ext with
    | [] => pure true 
    | pi_ext :: pil'_ext =>
      BIND res1 <- validate_two_instrs pi_ext pi_ext env_dim -;
      BIND res2 <- validate_instr_and_list pi_ext pil'_ext env_dim -;
      BIND res3 <- validate_instr_list pil'_ext env_dim -; 
      pure (res1 && res2 && res3)
    end.

Definition check_valid_access (pil: list PolyLang.PolyInstr_ext): bool :=
  forallb (
    fun pi => Instr.access_function_checker 
      pi.(PolyLang.pi_waccess_ext) 
      pi.(PolyLang.pi_raccess_ext)
      pi.(PolyLang.pi_instr_ext) 
  ) pil.

Definition validate (pp1 pp2: PolyLang.t) := 
  let '(pil1, varctxt1, vars1) := pp1 in 
  let '(pil2, varctxt2, vars2) := pp2 in 
  BIND wf_pil1 <- check_wf_polyprog pp1 -;
  BIND wf_pil2 <- check_wf_polyprog pp2 -;
  BIND eqdom <- EqDom pp1 pp2 -;
  let env_dim := length varctxt1 in
  let pil_ext := PolyLang.compose_pinstrs_ext pil1 pil2 in
  let valid_access := check_valid_access pil_ext in
  BIND res <- validate_instr_list (rev pil_ext) env_dim -;
  pure (wf_pil1 && wf_pil2 && eqdom && res && valid_access).

Lemma check_valid_access_correct:
  forall pil_ext, 
    check_valid_access pil_ext = true ->
    Forall (fun pi => Instr.valid_access_function 
      pi.(PolyLang.pi_waccess_ext) 
      pi.(PolyLang.pi_raccess_ext)
      pi.(PolyLang.pi_instr_ext)) pil_ext.
Proof.
  intros.
  unfold check_valid_access in H.
  eapply Forall_forall. intros pi_ext Hin.
  eapply forallb_forall in H; eauto.
  eapply Instr.access_function_checker_correct; eauto.
Qed.

Lemma check_wf_polyinstr_correct: 
  forall pi env vars,
    check_wf_polyinstr pi env vars = true -> 
    PolyLang.wf_pinstr env vars pi.
Proof.
  intros.
  unfold check_wf_polyinstr in H.
  unfold PolyLang.wf_pinstr.
  intros.
  folds PolyLang.pi_poly; subst.
  destruct (negb (Instr.check_never_written env (PolyLang.pi_instr pi))); tryfalse.
  destruct (length env + ((PolyLang.pi_depth pi)) <=? length vars) eqn:Henvlen in H; tryfalse.
  split.
  {
    eapply Nat.leb_le; eauto.
  }
  destruct (poly_nrl (PolyLang.pi_poly pi) <=? length vars)%nat eqn:Hdom in H; tryfalse.
  split.
  {
    eapply Nat.leb_le; trivial.
  }
  destruct (poly_nrl (PolyLang.pi_schedule pi) <=? length vars) eqn:Hsched in H; tryfalse.
  split.
  {
    eapply Nat.leb_le; trivial.
  }

  destruct (negb
  (check_listzzs_cols (PolyLang.pi_poly pi)
     (Datatypes.length env + ((PolyLang.pi_depth pi))))) eqn:Hcheckdom; tryfalse.
  split.
  {
    (* dom cols *)
    clear H.
    eapply negb_false_iff in Hcheckdom.
    unfolds check_listzzs_cols.
    unfolds check_listzzs_cols.

    subst.
    eapply check_listzzs_cols_correct; eauto.
  }
  clear Hcheckdom.

  destruct (negb
  (check_listzzs_cols (PolyLang.pi_transformation pi)
     (length env + (PolyLang.pi_depth pi)))) eqn:Hchecktf; tryfalse.
  split.
  {
    (* tf cols *)
    clear H.
    eapply negb_false_iff in Hchecktf.
    unfolds check_listzzs_cols.
    unfolds check_listzzs_cols.

    subst.
    eapply check_listzzs_cols_correct; eauto.
  }
  clear Hchecktf.
  destruct (negb
  (check_listzzs_cols (PolyLang.pi_schedule pi)
     (Datatypes.length env + (PolyLang.pi_depth pi)))) eqn:Hcheckschde; tryfalse.
  split.
  {
    clear H.
    eapply negb_false_iff in Hcheckschde.
    subst.
    eapply check_listzzs_cols_correct; eauto.
  }
  clear Hcheckschde.
  destruct (existsb
  (fun waccess : AccessFunction =>
  let (_, waccess_aff_func) := waccess in
  if
    negb
      (check_listzzs_cols waccess_aff_func
        (Datatypes.length env + (PolyLang.pi_depth pi)))
  then true
  else false) (PolyLang.pi_waccess pi)) eqn:Hcheckw; tryfalse.
  split.
  {
      eapply Forall_forall. intros waccess H1.
      rewrite Misc.existsb_forall in Hcheckw.
      pose proof (Hcheckw waccess H1).
      destruct waccess as (warrid, waccess_func).
      destruct (negb
      (check_listzzs_cols waccess_func
        (Datatypes.length env + (PolyLang.pi_depth pi)))) eqn:Hcheckw'; tryfalse.
      eapply negb_false_iff in Hcheckw'.
      subst.
      eapply check_listzzs_cols_correct; eauto.
  }
  destruct (existsb
  (fun raccess : AccessFunction =>
  let (_, raccess_aff_func) := raccess in
  if
    negb
      (check_listzzs_cols raccess_aff_func
        (Datatypes.length env + (PolyLang.pi_depth pi)))
  then true
  else false) (PolyLang.pi_raccess pi)) eqn:Hcheckr; tryfalse.
  split.
  {
    clear Hcheckw.
    {
      eapply Forall_forall. intros raccess H1.
      rewrite Misc.existsb_forall in Hcheckr.
      pose proof (Hcheckr raccess H1).
      destruct raccess as (rarrid, raccess_func).
      destruct (negb
      (check_listzzs_cols raccess_func
        (Datatypes.length env + (PolyLang.pi_depth pi)))) eqn:Hcheckr'; tryfalse.
      eapply negb_false_iff in Hcheckr'.
      subst.
      eapply check_listzzs_cols_correct; eauto.
    }
  }
  simpl in H.
  rename H into TS.
  eapply Nat.eqb_eq in TS; eauto.
Qed.

Lemma check_wf_polyprog_correct: 
  forall pp, 
    WHEN res <- check_wf_polyprog pp THEN 
    res = true ->
    PolyLang.wf_pprog pp.
Proof.
  intros. intros res Hcheckwf Htrue.
  unfold PolyLang.wf_pprog.
  intros.
  rewrite Htrue in Hcheckwf.
  unfold check_wf_polyprog in Hcheckwf.
  destruct pp as (p & vars).
  destruct p as (pil, varctxt).
  eapply mayReturn_pure in Hcheckwf.
  do 2 rewrite andb_true_iff in Hcheckwf.
  destruct Hcheckwf as ((Hvars & Hlen) & Hcheckwf).
  splits.
  {
    eapply Nat.leb_le in Hvars; try lia.
  }
  {
    clear Hlen.
    intros.
    eapply forallb_forall with (x:=pi) in Hcheckwf; eauto.
    eapply check_wf_polyinstr_correct; eauto.
  }
Qed. 

Lemma check_eqdom_pinstr_correct: 
  forall pi1 pi2, 
  EqDomInstr pi1 pi2 ->
  PolyLang.eqdom_pinstr pi1 pi2.
Proof.
  intros.
  unfold PolyLang.eqdom_pinstr.
  unfold EqDomInstr in H.
  eapply andb_true_iff in H; destruct H. 
  eapply andb_true_iff in H; destruct H. 
  eapply andb_true_iff in H; destruct H. 
  eapply andb_true_iff in H; destruct H. 
  eapply andb_true_iff in H; destruct H. 
  eapply Instr.eqb_eq in H4. 
  eapply listzzs_strict_eqb_eq in H3.
  eapply listzzs_strict_eqb_eq in H2.
  eapply access_list_strict_eqb_eq in H1.
  eapply access_list_strict_eqb_eq in H0.
  eapply Nat.eqb_eq in H.
  splits; trivial.
Qed.

Lemma check_eqdom_pinstrs_correct:
  forall pil1 pil2,
    EqDomInstList pil1 pil2 = true -> 
    rel_list PolyLang.eqdom_pinstr pil1 pil2.
Proof.
  induction pil1.
  {
    intros; simpls.
    destruct pil2; tryfalse; trivial.
  }
  {
    intros; simpls.
    destruct pil2; tryfalse.
    simpls.
    destruct (EqDomInstr a p) eqn:Heqdomi; tryfalse.
    eapply check_eqdom_pinstr_correct in Heqdomi.
    splits; trivial.
    eapply IHpil1 in H; trivial.
  }
Qed.

Lemma check_eqdom_pprog_correct: 
  forall pp1 pp2, 
    WHEN res <- EqDom pp1 pp2 THEN 
    res = true ->
    PolyLang.eqdom_pprog pp1 pp2.
Proof.
  intros. intros res Heqdom Htrue.
  unfold PolyLang.eqdom_pprog.
  intros.
  unfold EqDom in Heqdom.
  rewrite H in Heqdom; rewrite H0 in Heqdom.
  eapply mayReturn_pure in Heqdom.
  rewrite Htrue in Heqdom.
  do 3 rewrite andb_true_iff in Heqdom.
  destruct Heqdom as (((Hctxteq & Hvarseq) & Hpilleneq) & HieqdomT).
  splits.
  {
    eapply ctxt_eqb_eq; eauto.
  }
  {
    eapply ctxt_ty_eqb_eq; eauto.
  }
  {
    eapply Nat.eqb_eq in Hpilleneq; trivial.
  }
  {
    eapply check_eqdom_pinstrs_correct; eauto.
  }
Qed.

Definition compose_ip_ext (ip1 ip2: PolyLang.InstrPoint): PolyLang.InstrPoint_ext := 
    {| 
      PolyLang.ip_nth_ext := ip1.(PolyLang.ip_nth);
      PolyLang.ip_index_ext := ip1.(PolyLang.ip_index);  
      PolyLang.ip_transformation_ext := ip1.(PolyLang.ip_transformation);
      PolyLang.ip_time_stamp1_ext := ip1.(PolyLang.ip_time_stamp);  
      PolyLang.ip_time_stamp2_ext := ip2.(PolyLang.ip_time_stamp);
      PolyLang.ip_instruction_ext := ip1.(PolyLang.ip_instruction);  
      PolyLang.ip_depth_ext := ip1.(PolyLang.ip_depth);  
    |}.

Lemma old_of_compose_ok: 
  forall ip1 ip2 ip_ext,
    compose_ip_ext ip1 ip2 = ip_ext -> 
    PolyLang.old_of_ext ip_ext = ip1.
Proof.
  intros.
  unfold compose_ip_ext in H.
  unfold PolyLang.old_of_ext.
  destruct ip_ext; simpls.
  inv H. destruct ip1; trivial.
Qed.

Lemma new_of_compose_ok: 
  forall ip1 ip2 ip_ext,
    ip1.(PolyLang.ip_nth) = ip2.(PolyLang.ip_nth) -> 
    ip1.(PolyLang.ip_index) = ip2.(PolyLang.ip_index) -> 
    ip1.(PolyLang.ip_transformation) = ip2.(PolyLang.ip_transformation) ->
    ip1.(PolyLang.ip_instruction) = ip2.(PolyLang.ip_instruction) -> 
    ip1.(PolyLang.ip_depth) = ip2.(PolyLang.ip_depth) ->
    compose_ip_ext ip1 ip2 = ip_ext -> 
    PolyLang.new_of_ext ip_ext = ip2.
Proof.
  intros.
  unfold compose_ip_ext in H4.
  unfold PolyLang.new_of_ext. 
  destruct ip_ext; simpls. inv H4.
  destruct ip1; destruct ip2; simpls; subst; trivial.
Qed.

Fixpoint compose_ipl_ext (ipl1 ipl2: list PolyLang.InstrPoint): list PolyLang.InstrPoint_ext := 
  match ipl1, ipl2 with 
  | ip1::ipl1', ip2::ipl2' =>
      compose_ip_ext ip1 ip2 :: compose_ipl_ext ipl1' ipl2'   
  | [], [] => []
  | _, _ => []
  end
.

Lemma old_of_compose_list_ok: 
  forall ipl1 ipl2 ipl_ext,
  length ipl1 = length ipl2 ->
  compose_ipl_ext ipl1 ipl2 = ipl_ext -> 
  PolyLang.old_of_ext_list ipl_ext = ipl1.
Proof.
  induction ipl1.
  {
    intros; simpls.
    destruct ipl2; tryfalse.
    subst; simpls; trivial.
  }
  {
    intros; simpls.
    destruct ipl2; tryfalse.
    simpls.
    inv H.
    unfold PolyLang.old_of_ext_list.
    unfold PolyLang.old_of_ext_list. 
    rewrite map_cons.
    f_equal.
    {
      eapply old_of_compose_ok; trivial.
    }
    {
      eapply IHipl1; eauto.
    }
  }
Qed.

Lemma new_of_compose_list_ok: 
  forall ipl1 ipl2 ipl_ext,
  rel_list PolyLang.eq_except_sched ipl1 ipl2 ->
  compose_ipl_ext ipl1 ipl2 = ipl_ext -> 
  PolyLang.new_of_ext_list ipl_ext = ipl2.
Proof.
  induction ipl1.
  {
    intros; simpls.
    destruct ipl2; tryfalse.
    subst; simpls; trivial.
  }
  {
    intros; simpls.
    destruct ipl2; tryfalse.
    simpls.
    inv H.
    unfold PolyLang.new_of_ext_list.
    rewrite map_cons.
    f_equal.
    {
      unfold PolyLang.eq_except_sched in H1.
      eapply new_of_compose_ok with (ip1:=a); firstorder.
    }
    {
      eapply IHipl1; eauto.
    }
  }
Qed.

Lemma ext_compose_same_length_app: 
  forall iplh1 iplh2 iplh_ext iplt1 iplt2 iplt_ext ipl1 ipl2 ipl_ext,
    compose_ipl_ext iplh1 iplh2 = iplh_ext ->
    compose_ipl_ext iplt1 iplt2 = iplt_ext ->
    ipl1 = iplh1 ++ iplt1 -> 
    ipl2 = iplh2 ++ iplt2 -> 
    length iplh1 = length iplh2 -> 
    length iplt1 = length iplt2 -> 
    ipl_ext = iplh_ext ++ iplt_ext ->
    compose_ipl_ext ipl1 ipl2 = ipl_ext.
Proof.
  induction iplh1.
  {
    intros; simpls.
    destruct iplh2; tryfalse. simpls. subst; trivial.
  }
  {
    intros; simpls.
    destruct ipl2 eqn:Hipl2.
    {
      symmetry in H2.
      eapply app_eq_nil in H2.
      destruct H2.
      subst; simpls; tryfalse. 
    }
    {
      rename a into iph1.
      rename iplh1 into iplh1'.
      destruct iplh2 eqn:Hiplh2; tryfalse.
      rename i0 into iph2.
      rename l0 into iplh2'. 
      simpls.
      inversion H2.
      rename l into ipl2'.
      remember (iplh1' ++ iplt1) as ipl1'.
      remember (compose_ipl_ext iplh1' iplh2') as iplh'_ext.
      remember (compose_ipl_ext ipl1' ipl2') as ipl'_ext.
      subst; trivial.
      simpls.
      f_equal.
      inversion H3.
      eapply IHiplh1; eauto. 
    }
  }
Qed.

Lemma compose_pinstrs_ext_app_singleton:
  forall pil1 pil2 pi1 pi2,
    length pil1 = length pil2 ->
    PolyLang.compose_pinstrs_ext (pil1++[pi1]) (pil2++[pi2]) = 
    PolyLang.compose_pinstrs_ext (pil1) (pil2) 
    ++ [PolyLang.compose_pinstr_ext pi1 pi2].
Proof.
  induction pil1.
  {
    intros; simpls. symmetry in H. rewrite length_zero_iff_nil in H. subst; trivial.
  }
  {
    intros; simpls.
    destruct pil2 eqn:Hpil2; tryfalse. simpls. inv H.
    rewrite IHpil1; eauto.
  }
Qed.

Lemma ext_compose_app:
  forall ipl1 ipl2 ipl_ext iplh1 iplh2 iplh_ext ipl1' ipl2' ipl_ext',
    ipl1 = iplh1 ++ ipl1' -> 
    ipl2 = iplh2 ++ ipl2' -> 
    compose_ipl_ext iplh1 iplh2 = iplh_ext -> 
    (PolyLang.new_of_ext_list iplh_ext = iplh2 /\ PolyLang.old_of_ext_list iplh_ext = iplh1) -> 
    compose_ipl_ext ipl1' ipl2' = ipl_ext' ->
    (PolyLang.new_of_ext_list ipl_ext' = ipl2' /\ PolyLang.old_of_ext_list ipl_ext' = ipl1') -> 
    compose_ipl_ext ipl1 ipl2 = ipl_ext -> 
    (PolyLang.new_of_ext_list ipl_ext = ipl2 /\ PolyLang.old_of_ext_list ipl_ext = ipl1).
Proof.
  intros.
  assert (ipl_ext = iplh_ext ++ ipl_ext'). {
    rewrite <- H5.
    rewrite <- H1.
    rewrite <- H3.
    assert (length iplh1 = length iplh2). {
      clear - H2.
      destruct H2.
      unfolds PolyLang.new_of_ext_list.
      unfolds PolyLang.old_of_ext_list.
      subst.
      do 2 rewrite map_length.
      trivial.
    }
    assert (length ipl1' = length ipl2'). {
      clear - H4.
      destruct H4.
      unfolds PolyLang.new_of_ext_list.
      unfolds PolyLang.old_of_ext_list.
      subst.
      do 2 rewrite map_length.
      trivial.
    }
    eapply ext_compose_same_length_app with (iplh1:=iplh1) (iplh2:=iplh2) (iplt1:=ipl1') (iplt2:=ipl2'); eauto.
  }

  unfolds PolyLang.new_of_ext_list.
  unfolds PolyLang.old_of_ext_list.
  destruct H2. destruct H4.
  split. 
  {
    rewrite H6. 
    rewrite map_app; eauto.
    subst; eauto.  
  }
  {
    rewrite H6.
    rewrite map_app; eauto.
    subst; eauto.
  }
Qed.

Lemma eq_dom_pinstrs_implies_all_nil:
  forall pil1 pil2 envv,
    rel_list PolyLang.eqdom_pinstr pil1 pil2 ->
    PolyLang.flatten_instrs envv pil1 [] <->
    PolyLang.flatten_instrs envv pil2 [].
Proof. 
  induction pil1 using rev_ind.
  - intros. simpls. destruct pil2 eqn:Hpil2; tryfalse; split; trivial.
  - intros. simpls.
    assert (exists pi2 pil2', pil2 = pil2' ++ [pi2]) as Hpil2. {
      clear - H.
      eapply rel_list_implies_eq_length in H.
      destruct pil2.
      - rewrite app_length in H; simpls; try lia.
      - assert (length (p::pil2) > 0). {rewrite app_length in H; simpls; try lia. }
        exists (last (p::pil2) (p)) (removelast (p::pil2)).
        eapply app_removelast_last. intro; tryfalse.
    }
    destruct Hpil2 as (pi2 & pil2' & Hpil2).
    rewrite Hpil2 in H.
    eapply rel_list_app_singleton in H.
    destruct H.
    assert (length pil1 = length pil2') as LENPIL. {
      eapply rel_list_implies_eq_length; eauto.
    }
    eapply IHpil1 in H; eauto.
    rewrite Hpil2. split; intro.
    --
      eapply PolyLang.flatten_instrs_nil_sub_nil in H1.
      destruct H1.
      assert (PolyLang.flatten_instrs envv pil2' []). {
        eapply H in H1; trivial.
      }
      eapply PolyLang.flatten_instrs_app_singleton in H3; eauto.

      pose proof H0 as G0.
      eapply PolyLang.eqdom_pinstr_implies_flatten_instr_nth_exists with (ipl1:=[])in H0; eauto.
      destruct H0 as (ipl2 & FLT2).
      assert (rel_list PolyLang.eq_except_sched [] ipl2) as REL2. {
        eapply PolyLang.eqdom_pinstr_implies_flatten_instr_nth_rel'; eauto.
      } 
      rewrite <- LENPIL; trivial.
      assert (ipl2 = []). {
        eapply rel_list_implies_eq_length in REL2.
        simpls. symmetry in REL2. rewrite length_zero_iff_nil in REL2. trivial.
      }
      subst. trivial.
    --
      eapply PolyLang.flatten_instrs_nil_sub_nil in H1.
      destruct H1.
      assert (PolyLang.flatten_instrs envv pil1 []). {
        eapply H in H1; trivial.
      }
      eapply PolyLang.flatten_instrs_app_singleton in H3; eauto.
      eapply PolyLang.eqdom_pinstr_symm in H0.
      pose proof H0 as G0.
      eapply PolyLang.eqdom_pinstr_implies_flatten_instr_nth_exists with (ipl1:=[]) in H0; eauto.
      destruct H0. 
      assert (rel_list PolyLang.eq_except_sched [] x0) as REL1. {
        eapply PolyLang.eqdom_pinstr_implies_flatten_instr_nth_rel'; eauto.
      } 

      rewrite LENPIL; trivial.
      assert (x0 = []). {
        eapply rel_list_implies_eq_length in REL1.
        simpls. symmetry in REL1. rewrite length_zero_iff_nil in REL1. trivial.
      }
      subst. trivial.
Qed.

Lemma eqdom_pinstr_implies_ext_compose:
  forall pi1 pi2 ipl_ext envv ipl1 ipl2 n, 
    PolyLang.eqdom_pinstr pi1 pi2 -> 
    PolyLang.flatten_instr_nth envv n pi1 ipl1 ->
    PolyLang.flatten_instr_nth envv n pi2 ipl2 ->
    compose_ipl_ext ipl1 ipl2 = ipl_ext -> 
    PolyLang.new_of_ext_list ipl_ext = ipl2 /\ 
    PolyLang.old_of_ext_list ipl_ext = ipl1.
Proof.
  intros.
  pose proof H as G.
  destruct H as (D & I & Dom & T & W & R).
  splits.
  - eapply new_of_compose_list_ok; eauto.
    eapply PolyLang.eqdom_pinstr_implies_flatten_instr_nth_rel' with (pi1:=pi1) in G; eauto.
  - eapply old_of_compose_list_ok with (ipl2:=ipl2); eauto.
    eapply PolyLang.eqdom_pinstr_implies_flatten_instr_nth_rel' with (pi1:=pi1) in G; eauto.
    eapply rel_list_implies_eq_length; eauto.
Qed.

Lemma eqdom_pinstrs_implies_ext_compose: 
  forall pil1 pil2 ipl_ext envv ipl1 ipl2 , 
    rel_list PolyLang.eqdom_pinstr pil1 pil2 -> 
    PolyLang.flatten_instrs envv pil1 ipl1 ->
    PolyLang.flatten_instrs envv pil2 ipl2 ->
    compose_ipl_ext ipl1 ipl2 = ipl_ext -> 
    PolyLang.new_of_ext_list ipl_ext = ipl2 /\ 
    PolyLang.old_of_ext_list ipl_ext = ipl1.
Proof.
  induction pil1 using rev_ind.
  {
    intros; simpls.
    destruct pil2; tryfalse.
    eapply (PolyLang.flatten_instrs_nil_implies_nil envv) in H0.
    eapply (PolyLang.flatten_instrs_nil_implies_nil envv) in H1.
    subst. simpls; trivial. split; trivial.
  }
  {
    intros; simpls.
    assert (exists pi2 pil2', pil2 = pil2' ++ [pi2]) as Hipl2. {
      clear - H.
      eapply rel_list_implies_eq_length in H.
      destruct pil2.
      - rewrite app_length in H; simpls; try lia.
      - assert (length (p::pil2) > 0). {rewrite app_length in H; simpls; try lia. }
        exists (last (p::pil2) (p)) (removelast (p::pil2)).
        eapply app_removelast_last. intro; tryfalse.
    }
    destruct Hipl2 as (pi2 & pil2' & Hipl2).  
    rename x into pi1.
    rename pil1 into pil1'.
    rewrite Hipl2 in H.
    eapply rel_list_app_singleton in H.
    destruct H as (Hrell & Hrel).
    rewrite Hipl2 in H1.
    pose proof Hrell as Grell.
    eapply rel_list_implies_eq_length in Hrell.
    eapply PolyLang.flatten_instrs_app_singleton_inv in H0.
    destruct H0 as (iplh1 & iplt1 & H0 & H1' & H2').
    eapply PolyLang.flatten_instrs_app_singleton_inv in H1.
    destruct H1 as (iplh2 & iplt2 & H1 & H2'' & H3').

    eapply IHpil1 
      with (envv:=envv) (ipl1:=iplh1) (ipl2:=iplh2) (ipl_ext:=compose_ipl_ext iplh1 iplh2) in Grell; eauto.
    eapply ext_compose_app; eauto.

    clear - H1' H2'' Hrel Hrell.
    pose proof Hrel as Grel.
    eapply PolyLang.eqdom_pinstr_implies_flatten_instr_nth_exists in Hrel; eauto. 
    eapply eqdom_pinstr_implies_ext_compose; eauto.
    rewrite Hrell; trivial.
  }
Qed.

Lemma eqdom_implies_ext_compose: 
  forall pis1 env1 vars1 pis2 env2 vars2 ipl1 ipl2 envv, 
    PolyLang.eqdom_pprog (pis1, env1, vars1) (pis2, env2, vars2) -> 
    PolyLang.flatten_instrs envv pis1 ipl1 ->
    PolyLang.flatten_instrs envv pis2 ipl2 ->
    (exists ipl_ext, 
    PolyLang.new_of_ext_list ipl_ext = ipl2 /\ 
    PolyLang.old_of_ext_list ipl_ext = ipl1).
Proof.
  intros.
  exists (compose_ipl_ext ipl1 ipl2).
  unfold PolyLang.eqdom_pprog in H.
  pose proof (H pis1 pis2 env1 env2 vars1 vars2); simpls.
  assert (env1 = env2). {firstorder. }
  assert (Datatypes.length pis1 = Datatypes.length pis2). {firstorder. }
  assert ( rel_list PolyLang.eqdom_pinstr pis1 pis2 ). { eapply H2; trivial. }
  clear H2.
  eapply eqdom_pinstrs_implies_ext_compose with (pil1:=pis1) (pil2:=pis2) ; eauto.
Qed.

Lemma eqdom_to_eqdom_pinstr:
  forall pp1 pp2 varctxt1 varctxt2 vars1 vars2 pil1 pil2 n pi1 pi2,
    PolyLang.eqdom_pprog pp1 pp2 ->
    pp1 = (pil1, varctxt1, vars1) ->
    pp2 = (pil2, varctxt2, vars2) ->
    nth_error pil1 n = Some pi1 ->
    nth_error pil2 n = Some pi2 ->
    PolyLang.eqdom_pinstr pi1 pi2.
Proof.
  intros.
  unfold PolyLang.eqdom_pprog in H.
  pose proof (H pil1 pil2 varctxt1 varctxt2 vars1 vars2 H0 H1).
  destruct H4. destruct H5. destruct H6.
  eapply rel_list_implies_rel_nth; eauto.
Qed.


Lemma eqdom_perserve_finite_forward: 
  forall pis1 env1 vars1 pis2 env2 vars2 envv,
    PolyLang.eqdom_pprog (pis1, env1, vars1) (pis2, env2, vars2)->
    (
      (exists ipl1, 
      PolyLang.flatten_instrs envv pis1 ipl1) 
      -> 
      (exists ipl2,
      PolyLang.flatten_instrs envv pis2 ipl2)       
    ).
Proof.
  intros until envv. intros Heqdom Hflt1.
  destruct Hflt1 as (ipl1, Hflt1).
  assert (env1 = env2). {
    clear - Heqdom.
    unfolds PolyLang.eqdom_pprog.
    eapply Heqdom.
    pose proof (Heqdom pis1 pis2 env1 env2 vars1 vars2).
    firstorder. econs.
  }
  assert (length pis1 = length pis2). {
    clear - Heqdom.
    unfolds PolyLang.eqdom_pprog.
    eapply Heqdom.
    pose proof (Heqdom pis1 pis2 env1 env2 vars1 vars2).
    firstorder. econs.
  } 
  rename H0 into Glen.
  unfold PolyLang.eqdom_pprog in Heqdom.
  pose proof (Heqdom pis1 pis2 env1 env2 vars1 vars2).
  assert (rel_list PolyLang.eqdom_pinstr pis1 pis2). {
    firstorder.
  }
  eapply PolyLang.eqdom_pinstrs_implies_flatten_instrs_exists in H1; eauto.
Qed.

Lemma eqdom_perserve_finite: 
  forall pis1 env1 vars1 pis2 env2 vars2 envv,
    WHEN eqdom <- EqDom (pis1, env1, vars1) (pis2, env2, vars2) THEN
    eqdom = true -> 
    (
      (exists ipl1, 
      PolyLang.flatten_instrs envv pis1 ipl1) 
      <-> 
      (exists ipl2,
      PolyLang.flatten_instrs envv pis2 ipl2)       
    ).
Proof.
  intros. intros res Hval Htrue.
  eapply check_eqdom_pprog_correct in Hval. eapply Hval in Htrue.
  split; intro.
  eapply eqdom_perserve_finite_forward; eauto.
  eapply PolyLang.eqdom_pprog_symm in Htrue.
  eapply eqdom_perserve_finite_forward; eauto.
Qed.

Lemma validate_preserve_finite: 
  forall pis1 env1 vars1 pis2 env2 vars2 envv,
    WHEN res <- validate (pis1, env1, vars1) (pis2, env2, vars2) THEN 
    res = true -> 
    (
      (exists ipl1, 
      PolyLang.flatten_instrs envv pis1 ipl1) 
      <-> 
      (exists ipl2,
      PolyLang.flatten_instrs envv pis2 ipl2)       
    )
  .
Proof. 
  intros. intros res Hval Htrue.
  unfold validate in Hval.
  bind_imp_destruct Hval wfpil1 Hwfpil1.
  bind_imp_destruct Hval wfpil2 Hwfpil2.
  bind_imp_destruct Hval eqdom Heqdom.
  bind_imp_destruct Hval resL HresL.
  eapply mayReturn_pure in Hval.
  rewrite Htrue in Hval.
  do 4 rewrite andb_true_iff in Hval.
  destruct Hval as ((((Hwfpil1T & Hwfpil2T) & HeqdomT) & HresLT) & HvaT).
  clear - Heqdom HeqdomT.
  eapply eqdom_perserve_finite; eauto.
Qed.

Lemma validate_lt_ge_pair_correct: 
  forall pol_old_lt pol_new_ge sameloc_enveq_indom_pol p1 p2,
    WHEN res <- validate_lt_ge_pair pol_old_lt pol_new_ge sameloc_enveq_indom_pol THEN 
    res = true -> 
    in_poly (p1 ++ p2) sameloc_enveq_indom_pol = true ->
    in_poly (p1 ++ p2) pol_old_lt = true ->
    in_poly (p1 ++ p2) pol_new_ge = true ->
    False.
Proof.
  intros. intros res Hval Hres Hin Hlt Hge.
  unfold validate_lt_ge_pair in Hval.
  bind_imp_destruct Hval pol_lt Hpollt.
  bind_imp_destruct Hval pol_ge Hpolge.
  bind_imp_destruct Hval isbot Hisbot.
  subst. eapply mayReturn_pure in Hval.
  subst. 
  eapply isBottom_correct_1 in Hisbot. simpls.
  pose proof (Hisbot (p1 ++ p2)).
  
  eapply poly_inter_def with (p:=(p1++p2)) in Hpolge.
  rewrite poly_inter_pure_def in Hpolge. 
  rewrite Hpolge in H.
  rewrite andb_false_iff in H.
  destruct H; tryfalse.

  eapply poly_inter_def with (p:=(p1++p2)) in Hpollt.
  rewrite poly_inter_pure_def in Hpollt.
  rewrite Hpollt in H.
  rewrite andb_false_iff in H.
  destruct H; tryfalse. 
Qed.

Lemma validate_two_accesses_helper_correct: 
  forall pols_old_lt pols_new_ge sameloc_enveq_indom_pol p1 p2,
    WHEN res <- validate_two_accesses_helper pols_old_lt pols_new_ge sameloc_enveq_indom_pol THEN 
    res = true -> 
    in_poly (p1 ++ p2) sameloc_enveq_indom_pol = true ->
    Exists (fun pol => in_poly (p1 ++ p2) pol = true) pols_old_lt -> 
    Exists (fun pol => in_poly (p1 ++ p2) pol = true) pols_new_ge -> 
    False.
Proof.
  induction pols_old_lt.
  {
    intros. intros res Hval Hres Hin Hlt Hge.   
    eapply Exists_exists in Hlt. 
    simpls. clear - Hlt; firstorder.
  }
  {
    rename a into pol_old_lt.
    intros. intros res Hval Hres Hin Hlt Hge.


    unfolds validate_two_accesses_helper; simpls.

      bind_imp_destruct Hval res1 Hval1.
      destruct res1 eqn:Hres1; subst.
      {
        (* pol_new_ge & pol_old_lt check is true *)
        eapply IHpols_old_lt; eauto.
        eapply Exists_cons in Hlt.
        destruct Hlt as [Hlt|]; trivial. 
        (* now p1, p2 sat pol_old_lt and sameloc, they cannot sat new_ge, contradict with Hge *)
        assert (
          forall pols_new_ge pol_lt sameloc_enveq_indom_pol,
          WHEN res <- (forallb_imp (fun pol_ge : polyhedron => validate_lt_ge_pair pol_lt pol_ge sameloc_enveq_indom_pol) pols_new_ge) THEN 
            res = true -> 
            in_poly (p1 ++ p2) sameloc_enveq_indom_pol = true ->
            in_poly (p1 ++ p2) pol_lt = true ->
            ~Exists (fun pol : list (list Z * Z) => in_poly (p1 ++ p2) pol = true) pols_new_ge
        ) as Hgelst. {
          clear.
          induction pols_new_ge.
          {
            intros. intros res Hval Hres Hin Hlt.
            rewrite Exists_exists. intros [pol Hpol].
            destruct Hpol; tryfalse.
          }
          {
            intros. intros res Hval Hres Hin Hlt.
            simpls.
            bind_imp_destruct Hval res1 Hval1.
            destruct res1 eqn:Hres1; subst.
            {
              rename a into pol_ge.
              assert (in_poly (p1 ++ p2) pol_ge = false). {
                clear - Hval1 Hin Hlt.
                eapply validate_lt_ge_pair_correct with (p1:=p1) (p2:=p2) in Hval1; eauto.
                destruct (in_poly (p1 ++ p2) pol_ge); trivial; tryfalse.
                eapply Hval1 in Hin; eauto; tryfalse.
              }

              intro. eapply Exists_exists in H0.
              destruct H0 as [Hge Hinge].
              destruct Hinge.
              simpl in H0.
              destruct H0 as [EQ | TAIL].
              {
                subst; tryfalse.
              }
              {
                eapply IHpols_new_ge in Hval.
                eapply Hval in Hin; eauto.              
                eapply Hin; eauto.
                eapply Exists_exists; eauto.
              }
            }
            {
              eapply mayReturn_pure in Hval; tryfalse.
            }
          }
        }
        eapply (Hgelst) in Hval1.
        eapply Hval1 in Hge; trivial; tryfalse. 
      }
      {
        eapply mayReturn_pure in Hval; tryfalse.
      }
    }
Qed.

Definition validate_two_accesses_implies_permut_no_collision: 
  forall pols_old_lt pols_new_ge a1 a2 tf1 tf2 p1 p2 pol_dom dom_dim1 dom_dim2,
    WHEN res <- validate_two_accesses a1 a2 tf1 tf2 pol_dom pols_old_lt pols_new_ge dom_dim1 dom_dim2 THEN 
    res = true ->  
    length p1 = dom_dim1 -> 
    length p2 = dom_dim2 ->
    length tf1 = dom_dim1 ->
    (
      exact_listzzs_cols dom_dim1 tf1
    ) ->
    (
      exact_listzzs_cols dom_dim2 tf2
    ) ->
    in_poly (p1 ++ p2) pol_dom = true ->
    Exists (fun pol => in_poly (p1 ++ p2) pol = true) pols_old_lt -> 
    Exists (fun pol => in_poly (p1 ++ p2) pol = true) pols_new_ge ->
    cell_neq (exact_cell a1 (affine_product tf1 p1)) (exact_cell a2 (affine_product tf2 p2)).
Proof.
  intros. intros res Hval Hres Hlen1 Hlen2 Hlentf Hwf1 Hwf2 Hin Hlt Hge.
  unfold validate_two_accesses in Hval.
  destruct a1 as (id1, func1) eqn:Ha1.
  destruct a2 as (id2, func2) eqn:Ha2.
  destruct (Pos.eqb id1 id2) eqn:Hideq; simpls.
  {
    (* id1 = id2 *)
    eapply Pos.eqb_eq in Hideq; subst; simpls.
    bind_imp_destruct Hval sameloc_enveq_indom_pol Hsameloc.
    eapply poly_inter_def with (p:=(p1 ++ p2)) in Hsameloc.

    right; simpls. intro.

    eapply validate_two_accesses_helper_correct 
      with (p1:=p1) (p2:=p2) (pols_old_lt:=pols_old_lt) (pols_new_ge:=pols_new_ge)
           (sameloc_enveq_indom_pol:=sameloc_enveq_indom_pol); trivial; trivial. 

    rewrite Hsameloc.
    rewrite poly_inter_pure_def.
    eapply andb_true_iff. split; trivial.
    eapply make_poly_eq_correct_true; eauto.
    assert (length p1 > 0 \/ length p1 = 0). { lia. }
    destruct H0.
    {
      eapply matrix_product_cols; eauto. rewrite Hlentf. trivial.
    }
    {
      rewrite length_zero_iff_nil in H0. subst. simpls. 
      rewrite length_zero_iff_nil in Hlentf. subst. simpls.
      eapply matrix_product_cols_0; trivial.
    }
    rewrite matrix_product_assoc with (k2:=length p1); trivial.
    rewrite matrix_product_assoc with (k2:=length p2); trivial.
    }
  {
    (* id1 <> id2 *)
    eapply Pos.eqb_neq in Hideq. 
    firstorder. 
  }  
Qed.

Definition validate_access_accesslist_implies_permut_no_collision1: 
  forall ral p1 p2 wa tf1 tf2 pol_dom pols_old_lt pols_new_ge dom_dim1 dom_dim2,
    WHEN res <- forallb_imp (
      fun ra => 
      validate_two_accesses wa ra tf1 tf2 pol_dom pols_old_lt pols_new_ge dom_dim1 dom_dim2
    ) ral THEN 
    res = true -> 
    length p1 = dom_dim1 -> 
    length p2 = dom_dim2 ->
    length tf1 = dom_dim1 ->
    (
      exact_listzzs_cols dom_dim1 tf1
    ) ->
    (
      exact_listzzs_cols dom_dim2 tf2
    ) ->
    in_poly (p1 ++ p2) pol_dom = true ->
    Exists (fun pol => in_poly (p1 ++ p2) pol = true) pols_old_lt -> 
    Exists (fun pol => in_poly (p1 ++ p2) pol = true) pols_new_ge ->
    Forall (fun ra => cell_neq (exact_cell wa (affine_product tf1 p1)) (exact_cell ra (affine_product tf2 p2))) ral.
Proof.
  induction ral.
  {
    intros. intros res Hval Hres Hlen1 Hlen2 Hlentf Hwf1 Hwf2 Hin Hlt Hge.
    eapply Forall_nil; trivial.
  }
  {
    intros. intros res Hval Hres Hlen1 Hlen2 Hlentf Hwf1 Hwf2 Hin Hlt Hge.
    simpls.
    bind_imp_destruct Hval b Hval1. 
    destruct b; subst.
    { 
      eapply Forall_cons.
      {
        eapply validate_two_accesses_implies_permut_no_collision; eauto.
      }
      {
        eapply IHral; eauto.
      }
    }
    {
      eapply mayReturn_pure in Hval; tryfalse.
    }
  }
Qed.

Definition validate_two_accesslist_implies_permut_no_collision1: 
forall al1 al2 p1 p2 tf1 tf2 pol_dom pols_old_lt pols_new_ge dom_dim1 dom_dim2,
  WHEN res <- forallb_imp (
    fun a1 => 
    forallb_imp (
      fun a2 => 
      validate_two_accesses a1 a2 tf1 tf2 pol_dom pols_old_lt pols_new_ge dom_dim1 dom_dim2
    ) al2
  ) al1 THEN 
  res = true -> 
  length p1 = dom_dim1 -> 
  length p2 = dom_dim2 ->
  length tf1 = dom_dim1 ->
  (
    exact_listzzs_cols dom_dim1 tf1
  ) ->
  (
    exact_listzzs_cols dom_dim2 tf2
  ) ->
  in_poly (p1 ++ p2) pol_dom = true ->
  Exists (fun pol => in_poly (p1 ++ p2) pol = true) pols_old_lt -> 
  Exists (fun pol => in_poly (p1 ++ p2) pol = true) pols_new_ge ->
  Forall (fun a1 => 
    Forall (fun a2 => 
      cell_neq (exact_cell a1 (affine_product tf1 p1)) (exact_cell a2 (affine_product tf2 p2))) al2
    ) al1.
Proof.
  induction al1.
  {
    intros. intros res Hval Hres Hlen1 Hlen2 Hlentf Hwf1 Hwf2 Hin Hlt Hge.
    eapply Forall_nil; trivial.
  }
  {
    intros. intros res Hval Hres Hlen1 Hlen2 Hlentf Hwf1 Hwf2 Hin Hlt Hge.
    simpls.
    bind_imp_destruct Hval b Hval1. 
    destruct b; subst.
    { 
      eapply Forall_cons.
      {
        eapply validate_access_accesslist_implies_permut_no_collision1; eauto.
      }
      {
        eapply IHal1; eauto.
      }
    }
    {
      eapply mayReturn_pure in Hval; tryfalse.
    }
  }
Qed.

Definition no_ww_collision (wl1 wl2: list AccessFunction) (ip1 ip2: PolyLang.InstrPoint_ext) := 
  Forall (fun w1 =>
    Forall (fun w2 =>
    cell_neq 
      (exact_cell w1 (affine_product (PolyLang.ip_transformation_ext ip1) (PolyLang.ip_index_ext ip1))) 
      (exact_cell w2 (affine_product (PolyLang.ip_transformation_ext ip2) (PolyLang.ip_index_ext ip2)))
    ) wl2
  ) wl1.

Definition no_wr_collision (wl1 rl2: list AccessFunction) (ip1 ip2: PolyLang.InstrPoint_ext) := 
  Forall ( fun r2 => 
    Forall (
      fun w1 =>
      cell_neq (exact_cell w1 (affine_product (PolyLang.ip_transformation_ext ip1) (PolyLang.ip_index_ext ip1)))
               (exact_cell r2 (affine_product (PolyLang.ip_transformation_ext ip2) (PolyLang.ip_index_ext ip2)))
    ) wl1 
  ) rl2.

Definition no_write_collision (wl1 wl2 rl1 rl2: list AccessFunction) (ip1 ip2: PolyLang.InstrPoint_ext) := 
  no_ww_collision wl1 wl2 ip1 ip2 /\ 
  no_wr_collision wl1 rl2 ip1 ip2 /\ 
  no_wr_collision wl2 rl1 ip2 ip1.


Lemma no_w_collision_implies_permutability:
  forall i1 i2 p1 p2 st1 st2 st3 wl1 wl2 rl1 rl2 wcs1 rcs1 wcs2 rcs2,
            Instr.valid_access_function wl1 rl1 i1 ->
            Instr.valid_access_function wl2 rl2 i2 ->
            (
                Forall (fun w2 => 
                    Forall (fun w1 => cell_neq (exact_cell w1 p1) (exact_cell w2 p2)) wl1
                ) wl2
            )
            /\
            (
                Forall (fun r2 => 
                    Forall (fun w1 => cell_neq (exact_cell w1 p1) (exact_cell r2 p2)) wl1
                ) rl2
            )
            /\
            (
                Forall (fun w2 => 
                    Forall (fun r1 => cell_neq (exact_cell r1 p1) (exact_cell w2 p2)) rl1
                ) wl2
            )
            ->
            Instr.NonAlias st1 ->
            (Instr.instr_semantics i1 p1 wcs1 rcs1 st1 st2 /\ Instr.instr_semantics i2 p2 wcs2 rcs2 st2 st3) ->
            (exists st2' st3', Instr.instr_semantics i2 p2 wcs2 rcs2 st1 st2' /\ Instr.instr_semantics i1 p1 wcs1 rcs1 st2' st3' /\ State.eq st3 st3').
  Proof. 
    intros until rcs2. intros H H0 H1 Halias H2.
    destruct H1 as [Hww [Hwr Hrw]].
    destruct H2 as [Hsema1 Hsema2].
    assert (WW: Forall (fun wc2 => Forall (fun wc1 => cell_neq wc1 wc2) wcs1) wcs2). {
      clear Hwr Hrw.
      eapply Forall_forall. intros wc2 Hwc2.
      eapply Forall_forall. intros wc1 Hwc1.
      unfolds Instr.valid_access_function.
      pose proof H p1 st1 st2 wcs1 rcs1 Hsema1.
      unfolds valid_access_cells.
      destruct H1 as [W1 R1].
      pose proof W1 wc1 Hwc1 as W1. destruct W1 as (w1 & Hw1 & Heqw1).  
      pose proof H0 p2 st2 st3 wcs2 rcs2 Hsema2.
      destruct H1 as [W2 R2].
      pose proof W2 wc2 Hwc2 as W2. destruct W2 as (w2 & Hw2 & Heqw2).
      
      eapply Forall_forall in Hww; eauto. eapply Forall_forall in Hww; eauto.
      clear - Heqw1 Heqw2 Hww.
      eapply cell_neq_proper with (x:=wc1) (x0:=wc2) in Hww; eauto.
      eapply cell_eq_symm; trivial.
      eapply cell_eq_symm; trivial.
    }
    assert (WR: Forall (fun rc2 => Forall (fun wc1 => cell_neq wc1 rc2) wcs1) rcs2). {
      clear Hww Hrw.
      eapply Forall_forall. intros rc2 Hrc2.
      eapply Forall_forall. intros wc1 Hwc1.
      unfolds Instr.valid_access_function.
      pose proof H p1 st1 st2 wcs1 rcs1 Hsema1.
      unfolds valid_access_cells.
      destruct H1 as [W1 R1].
      pose proof W1 wc1 Hwc1 as W1. destruct W1 as (w1 & Hw1 & Heqw1).  
      pose proof H0 p2 st2 st3 wcs2 rcs2 Hsema2.
      destruct H1 as [W2 R2].
      pose proof R2 rc2 Hrc2 as R2. destruct R2 as (r2 & Hr2 & Heqr2).
      
      eapply Forall_forall in Hwr; eauto. eapply Forall_forall in Hwr; eauto.
      clear - Heqw1 Heqr2 Hwr.
      eapply cell_neq_proper with (x:=wc1) (x0:=rc2) in Hwr; eauto.
      eapply cell_eq_symm; trivial.
      eapply cell_eq_symm; trivial.
    }
    assert (RW: Forall (fun wc2 => Forall (fun rc1 => cell_neq rc1 wc2) rcs1) wcs2). {
      clear Hww Hwr.
      eapply Forall_forall. intros wc2 Hwc2.
      eapply Forall_forall. intros rc1 Hrc1.
      unfolds Instr.valid_access_function.
      pose proof H p1 st1 st2 wcs1 rcs1 Hsema1.
      unfolds valid_access_cells.
      destruct H1 as [W1 R1].
      pose proof R1 rc1 Hrc1 as R1. destruct R1 as (r1 & Hr1 & Heqr1).  
      pose proof H0 p2 st2 st3 wcs2 rcs2 Hsema2.
      destruct H1 as [W2 R2].
      pose proof W2 wc2 Hwc2 as W2. destruct W2 as (w2 & Hw2 & Heqw2).
      
      eapply Forall_forall in Hrw; eauto. eapply Forall_forall in Hrw; eauto.
      clear - Heqr1 Heqw2 Hrw.
      eapply cell_neq_proper with (x:=rc1) (x0:=wc2) in Hrw; eauto.
      eapply cell_eq_symm; trivial.
      eapply cell_eq_symm; trivial.
    }
    eapply Instr.bc_condition_implie_permutbility; eauto.
  Qed.

Lemma no_write_collision_implies_permutable:
  forall ip1 ip2 wl1 wl2 rl1 rl2,
    no_write_collision wl1 wl2 rl1 rl2 ip1 ip2 ->
    Instr.valid_access_function wl1 rl1 (ip1.(PolyLang.ip_instruction_ext)) ->
    Instr.valid_access_function wl2 rl2 (ip2.(PolyLang.ip_instruction_ext)) ->
    PolyLang.Permutable_ext ip1 ip2.
Proof.
  intros until rl2. intros H Hwf1 Hwf2.
  destruct ip1 eqn:Hip1; destruct ip2 eqn:Hip2. 
  unfold no_write_collision in H.
  unfold no_wr_collision in H.
  unfold no_ww_collision in H. 
  unfold PolyLang.Permutable_ext. unfold PolyLang.Permutable. 
  unfold PolyLang.old_of_ext.
  simpls. 

  intros st1 Halias. split; intros.
  - rename H0 into Hsem1; rename H1 into Hsem2.
    inv Hsem1. inv Hsem2; simpls.
    rename wcs into wcs1; rename rcs into rcs1.
    rename wcs0 into wcs2; rename rcs0 into rcs2.
    assert (exists st2'' st3', 
      Instr.instr_semantics ip_instruction_ext0 
        (affine_product ip_transformation_ext0 ip_index_ext0) wcs2 rcs2 st1 st2'' /\ 
      Instr.instr_semantics ip_instruction_ext 
        (affine_product ip_transformation_ext ip_index_ext) wcs1 rcs1 st2'' st3'
        /\ Instr.State.eq st3 st3'
        ).
    {
      destruct H as (WW & WR & RW).
      eapply no_w_collision_implies_permutability with (wl1:=wl1) (rl1:=rl1); eauto.
      splits; trivial. 

      - (* WW *)
        clear - WW.
        eapply Forall_forall. intros w2 Hw2. eapply Forall_forall. intros w1 Hw1.
        eapply Forall_forall in WW; eauto.
        eapply Forall_forall in WW; eauto.
      - (* WR *)      
        clear - RW.
        eapply Forall_forall. intros w2 Hw2. eapply Forall_forall. intros r1 Hr1.
        eapply Forall_forall in RW; eauto.
        eapply Forall_forall in RW; eauto.
        eapply cell_neq_symm; trivial.
    } 
    destruct H2 as (st2'' & st3' & Hsem1 & Hsem2 & Heq).
    exists st2'' st3'. splits; try econs; eauto. 
  - 
    rename H0 into Hsem1; rename H1 into Hsem2.
    inv Hsem1. inv Hsem2; simpls.
    rename wcs into wcs1; rename rcs into rcs1.
    rename wcs0 into wcs2; rename rcs0 into rcs2.
    assert (exists st2'' st3', 
      Instr.instr_semantics ip_instruction_ext 
        (affine_product ip_transformation_ext ip_index_ext) wcs2 rcs2 st1 st2'' /\ 
      Instr.instr_semantics ip_instruction_ext0 
        (affine_product ip_transformation_ext0 ip_index_ext0) wcs1 rcs1 st2'' st3' /\ Instr.State.eq st3 st3').
    {
      eapply no_w_collision_implies_permutability; eauto.
      destruct H as (WW & WR & RW).
      splits; trivial. 

      - (* WW *)
        clear - WW.
        eapply Forall_forall. intros w2 Hw2. eapply Forall_forall. intros w1 Hw1.
        eapply Forall_forall in WW; eauto.
        eapply Forall_forall in WW; eauto.
        eapply cell_neq_symm; trivial.
      - (* WR *)      
        clear - WR.
        eapply Forall_forall. intros w2 Hw2. eapply Forall_forall. intros r1 Hr1.
        eapply Forall_forall in WR; eauto.
        eapply Forall_forall in WR; eauto.
        eapply cell_neq_symm; trivial.
    } 
    destruct H2 as (st2'' & st3' & Hsem1 & Hsem2 & Heq).
    exists st2'' st3'. splits; try econs; eauto.
Qed.


Lemma validate_two_instrs_implies_no_write_collision: 
  forall pi1_ext pi2_ext env nth1 nth2 envv ipl1_ext ipl2_ext,
    WHEN res <- validate_two_instrs pi1_ext pi2_ext (length env) THEN 
    res = true ->
    PolyLang.wf_pinstr_ext env pi1_ext ->
    PolyLang.wf_pinstr_ext env pi2_ext ->
    length env = length envv ->
    PolyLang.flatten_instr_nth_ext envv nth1 pi1_ext ipl1_ext ->
    PolyLang.flatten_instr_nth_ext envv nth2 pi2_ext ipl2_ext ->
    forall ip1_ext ip2_ext , 
      In ip1_ext ipl1_ext ->
      In ip2_ext ipl2_ext ->
      PolyLang.instr_point_ext_old_sched_lt ip1_ext ip2_ext -> 
      PolyLang.instr_point_ext_new_sched_ge ip1_ext ip2_ext -> 
      no_write_collision 
        (pi1_ext.(PolyLang.pi_waccess_ext)) 
        (pi2_ext.(PolyLang.pi_waccess_ext)) 
        (pi1_ext.(PolyLang.pi_raccess_ext))
        (pi2_ext.(PolyLang.pi_raccess_ext))
        ip1_ext ip2_ext.
Proof. 
  intros. intros res Hval Hres Hwf1 Hwf2 Henvlen Hext1 Hext2 ip1 ip2 Hip1 Hip2 Hosched Hnsched.
  unfold validate_two_instrs in Hval.
  bind_imp_destruct Hval in_domain_poly Hdomain.
  bind_imp_destruct Hval eq_env_poly Henv.
  bind_imp_destruct Hval ww Hww.
  bind_imp_destruct Hval wr Hwr.
  bind_imp_destruct Hval rw Hrw.
  eapply mayReturn_pure in Hval.
  rewrite Hres in Hval.
  do 2 rewrite andb_true_iff in Hval. 
  destruct Hval as ((HwwT & HwrT) & HrwT); subst.

  assert (NO_WW: no_ww_collision 
                  (pi1_ext.(PolyLang.pi_waccess_ext)) 
                  (pi2_ext.(PolyLang.pi_waccess_ext)) ip1 ip2). {
    clear Hwr Hrw.
    eapply validate_two_accesslist_implies_permut_no_collision1 
      with (p1 := (PolyLang.ip_index_ext ip1)) (p2 := (PolyLang.ip_index_ext ip2)) in Hww; eauto.
    unfold no_ww_collision.
    intros.
    subst.
    assert (PolyLang.ip_transformation_ext ip1 = PolyLang.pi_transformation_ext pi1_ext) as TF1. {
      eapply PolyLang.expand_ip_instr_eq_pi_tf_ext; eauto.
    }
    assert (PolyLang.ip_transformation_ext ip2 = PolyLang.pi_transformation_ext pi2_ext) as TF2. {
      eapply PolyLang.expand_ip_instr_eq_pi_tf_ext; eauto.
    }
    rewrite TF1, TF2.
    eapply Hww; trivial.
    rewrite Henvlen; eapply PolyLang.ip_index_size_eq_pi_dom_size_ext; eauto.
    rewrite Henvlen; eapply PolyLang.ip_index_size_eq_pi_dom_size_ext; eauto.
    {
      clear - Hwf1. firstorder.
    }
    {
      clear - Hwf1. firstorder.
    }
    {
      clear - Hwf2. firstorder.
    }
    { 
      (* two instances in env_eq & in_domain poly *)
      clear - Hdomain Henv Henvlen Hext1 Hext2 Hip1 Hip2 Hwf1 Hwf2.
      eapply poly_inter_def 
        with (p := (PolyLang.ip_index_ext ip1 ++ PolyLang.ip_index_ext ip2)) in Henv.
      rewrite poly_inter_pure_def in Henv. 
      rewrite Henv.
      eapply andb_true_iff; split.
      {
        (* in env_eq *)
        rewrite Henvlen.
        eapply PolyLang.expand_same_env_implies_in_eq_env_pol_ext; eauto.
      }
      {
        (* in domain *)
        eapply PolyLang.expand_same_env_implies_in_domain_product_pol 
          with (env:=env) (envv:=envv) (nth1:=nth1) (nth2:=nth2) (ipl1:=ipl1_ext) (ipl2:=ipl2_ext) (pi1:=pi1_ext) (pi2:=pi2_ext); trivial.
        rewrite <- Henvlen; trivial.
      }
    }
    {
      (* old_sched_lt implies in make_poly_lt ... *)
      eapply PolyLang.ip_old_sched_lt_implies_in_pi_old_sched_lt_pol; eauto.
    }
    {
      eapply PolyLang.ip_new_sched_ge_implies_in_pi_new_sched_ge_pol; eauto.
    }
  }

  assert (NO_WR: no_wr_collision 
              (pi1_ext.(PolyLang.pi_waccess_ext)) 
              (pi2_ext.(PolyLang.pi_raccess_ext)) ip1 ip2). {
    clear Hww Hrw.
    eapply validate_two_accesslist_implies_permut_no_collision1 with (p1 := (PolyLang.ip_index_ext ip1)) (p2 := (PolyLang.ip_index_ext ip2)) in Hwr; eauto.
    unfold no_wr_collision. intros.
    subst.
    assert (PolyLang.ip_transformation_ext ip1 = PolyLang.pi_transformation_ext pi1_ext) as TF1. {
      eapply PolyLang.expand_ip_instr_eq_pi_tf_ext; eauto.
    }
    assert (PolyLang.ip_transformation_ext ip2 = PolyLang.pi_transformation_ext pi2_ext) as TF2. {
      eapply PolyLang.expand_ip_instr_eq_pi_tf_ext; eauto.
    }
    rewrite TF1, TF2.
    cut (Forall
    (fun a1 : AccessFunction =>
     Forall
       (fun a2 : AccessFunction =>
        cell_neq
          (exact_cell a1
             (affine_product (PolyLang.pi_transformation_ext pi1_ext) (PolyLang.ip_index_ext ip1)))
          (exact_cell a2
             (affine_product (PolyLang.pi_transformation_ext pi2_ext) (PolyLang.ip_index_ext ip2))))
       (PolyLang.pi_raccess_ext pi2_ext)) (PolyLang.pi_waccess_ext pi1_ext)). {
        clear. intro.
        eapply Forall_forall. intros. eapply Forall_forall. intros.
        eapply Forall_forall in H; eauto. 
        eapply Forall_forall in H; eauto.
       }
    eapply Hwr; trivial.
    rewrite Henvlen; eapply PolyLang.ip_index_size_eq_pi_dom_size_ext; eauto.
    rewrite Henvlen; eapply PolyLang.ip_index_size_eq_pi_dom_size_ext; eauto.
    {
      clear - Hwf1.
      firstorder.
    }
    {
      clear - Hwf1.
      firstorder.
    }
    {
      clear - Hwf2. firstorder.
    }
    { 
      (* two instances in env_eq & in_domain poly *)
      clear - Hdomain Henv Henvlen Hext1 Hext2 Hip1 Hip2 Hwf1 Hwf2.
      eapply poly_inter_def 
        with (p := (PolyLang.ip_index_ext ip1 ++ PolyLang.ip_index_ext ip2)) in Henv.
      rewrite poly_inter_pure_def in Henv. 
      rewrite Henv.
      eapply andb_true_iff; split.
      {
        (* in env_eq *)
        rewrite Henvlen; eapply PolyLang.expand_same_env_implies_in_eq_env_pol_ext; eauto.
      }
      {
        (* in domain *)
        rewrite Henvlen in Hdomain; eapply PolyLang.expand_same_env_implies_in_domain_product_pol; eauto.
      }
    }
    {
      (* old_sched_lt implies in make_poly_lt ... *)
      eapply PolyLang.ip_old_sched_lt_implies_in_pi_old_sched_lt_pol; eauto.

    }
    {
      eapply PolyLang.ip_new_sched_ge_implies_in_pi_new_sched_ge_pol; eauto.
    }
  }

  assert (NO_RW: no_wr_collision       
              (pi2_ext.(PolyLang.pi_waccess_ext)) 
              (pi1_ext.(PolyLang.pi_raccess_ext)) ip2 ip1). {
    clear Hww Hwr.
    eapply validate_two_accesslist_implies_permut_no_collision1 with (p1 := (PolyLang.ip_index_ext ip1)) (p2 := (PolyLang.ip_index_ext ip2)) in Hrw; eauto.
    unfold no_wr_collision. intros.
    subst.
    assert (PolyLang.ip_transformation_ext ip1 = PolyLang.pi_transformation_ext pi1_ext) as TF1. {
      eapply PolyLang.expand_ip_instr_eq_pi_tf_ext; eauto.
    }
    assert (PolyLang.ip_transformation_ext ip2 = PolyLang.pi_transformation_ext pi2_ext) as TF2. {
      eapply PolyLang.expand_ip_instr_eq_pi_tf_ext; eauto.
    }

    rewrite TF1, TF2.
    cut (Forall
    (fun a1 : AccessFunction =>
     Forall
       (fun a2 : AccessFunction =>
        cell_neq
          (exact_cell a1
             (affine_product (PolyLang.pi_transformation_ext pi1_ext) (PolyLang.ip_index_ext ip1)))
          (exact_cell a2
             (affine_product (PolyLang.pi_transformation_ext pi2_ext) (PolyLang.ip_index_ext ip2))))
       (PolyLang.pi_waccess_ext pi2_ext)) (PolyLang.pi_raccess_ext pi1_ext)).
       {
        clear. intro.
        eapply Forall_forall. intros. eapply Forall_forall. intros.
        eapply Forall_forall in H; eauto. 
        eapply Forall_forall in H; eauto.
        eapply cell_neq_symm; trivial.
       }
    
    eapply Hrw; trivial.
    rewrite Henvlen; eapply PolyLang.ip_index_size_eq_pi_dom_size_ext; eauto.
    rewrite Henvlen; eapply PolyLang.ip_index_size_eq_pi_dom_size_ext; eauto.
    {
      clear - Hwf1.
      firstorder.
    }
    {
      clear - Hwf1.
      firstorder.
    }
    {
      clear - Hwf2. firstorder.
    }
    { 
      (* two instances in env_eq & in_domain poly *)
      clear - Hdomain Henv Henvlen Hext1 Hext2 Hip1 Hip2 Hwf1 Hwf2.
      eapply poly_inter_def 
        with (p := (PolyLang.ip_index_ext ip1 ++ PolyLang.ip_index_ext ip2)) in Henv.
      rewrite poly_inter_pure_def in Henv. 
      rewrite Henv.
      eapply andb_true_iff; split.
      {
        (* in env_eq *)
        rewrite Henvlen; eapply PolyLang.expand_same_env_implies_in_eq_env_pol_ext; eauto.
      }
      {
        (* in domain *)
        rewrite Henvlen in Hdomain; eapply PolyLang.expand_same_env_implies_in_domain_product_pol; eauto.
      }
    }
    {
      (* old_sched_lt implies in make_poly_lt ... *)
      eapply PolyLang.ip_old_sched_lt_implies_in_pi_old_sched_lt_pol; eauto.

    }
    {
      eapply PolyLang.ip_new_sched_ge_implies_in_pi_new_sched_ge_pol; eauto.
    }
  }
  clear - NO_WW NO_WR NO_RW. firstorder.
Qed.


Lemma validate_pinstr_implies_permutability1: 
  forall  env pi1_ext pi2_ext envv nth1 nth2 ipl1_ext ipl2_ext,
    WHEN res <- validate_two_instrs pi1_ext pi2_ext (length env) THEN 
    res = true ->
    PolyLang.wf_pinstr_ext env pi1_ext ->
    PolyLang.wf_pinstr_ext env pi2_ext ->
    length env = length envv ->
    PolyLang.flatten_instr_nth_ext envv nth1 pi1_ext ipl1_ext ->
    PolyLang.flatten_instr_nth_ext envv nth2 pi2_ext ipl2_ext ->
    Instr.valid_access_function 
      (PolyLang.pi_waccess_ext pi1_ext) 
      (PolyLang.pi_raccess_ext pi1_ext) (PolyLang.pi_instr_ext pi1_ext) ->
    Instr.valid_access_function 
      (PolyLang.pi_waccess_ext pi2_ext) 
      (PolyLang.pi_raccess_ext pi2_ext) (PolyLang.pi_instr_ext pi2_ext) ->
    forall ip1_ext ip2_ext, 
      In ip1_ext ipl1_ext ->
      In ip2_ext ipl2_ext ->
      PolyLang.instr_point_ext_old_sched_lt ip1_ext ip2_ext -> 
      PolyLang.instr_point_ext_new_sched_ge ip1_ext ip2_ext -> 
      PolyLang.Permutable_ext ip1_ext ip2_ext.
Proof.
intros. intros res Hval Hres Hwf1 Hwf2 Henvlen Hext1 Hext2 Ha1 Ha2 ip1 ip2 Hip1 Hip2 Hosched Hnsched.
  assert (PolyLang.ip_instruction_ext ip1 = PolyLang.pi_instr_ext pi1_ext). {
    eapply PolyLang.expand_ip_instr_eq_pi_instr_ext; eauto.
  }
  assert (PolyLang.ip_instruction_ext ip2 = PolyLang.pi_instr_ext pi2_ext). {
    eapply PolyLang.expand_ip_instr_eq_pi_instr_ext; eauto.
  }
  
  eapply no_write_collision_implies_permutable; eauto.
  eapply validate_two_instrs_implies_no_write_collision; eauto.
  rewrite H; trivial. 
  rewrite H0; trivial.
Qed.


Lemma compose_pinstrs_ext_nil: 
  forall pil1 pil2, 
    length pil1 = length pil2 ->
    PolyLang.compose_pinstrs_ext pil1 pil2 = nil -> 
    pil1 = nil /\ pil2 = nil.
Proof.
  induction pil1.
  {
    intros; simpls. splits; trivial.
    symmetry in H; rewrite length_zero_iff_nil in H.
    trivial.
  }
  {
    intros; simpls.
    destruct pil2 eqn:Hpil2; trivial.
    simpls. lia.
    simpls. tryfalse.
  }
Qed.

Lemma ip_not_in_compose_not_in:
  forall ip1 ip2 ipl1 ipl2,
    ~ In ip1 ipl1 -> 
    ~ In ip2 ipl2 ->
    ~ In (compose_ip_ext ip1 ip2) (compose_ipl_ext ipl1 ipl2).
Proof.
  induction ipl1.
  {
    intros. destruct ipl2; simpls; trivial.
  }
  {
    intros. simpls. destruct ipl2; simpls; trivial.
    intro. destruct H1.
    -- 
      rename a into ip1'; rename i into ip2'.
      unfold compose_ip_ext in H1. inv H1.
      apply H. destruct ip1; destruct ip2; destruct ip1'; destruct ip2'; simpls; subst; trivial. 
      left; trivial. 
    -- 
    eapply IHipl1; eauto.
  }
Qed.


Lemma ipl_NoDup_implies_compose_NoDup:
  forall ipl1 ipl2,
    NoDup ipl1 ->
    NoDup ipl2 ->
    NoDup (compose_ipl_ext ipl1 ipl2).
Proof.
  induction ipl1.
  {
    intros. 
    destruct ipl2; simpls; trivial; econs.
  }
  {
    intros. simpls. destruct ipl2; simpls; trivial. econs.
    inv H.
    eapply NoDup_cons_iff.
    split.
    {
      intro.
      inv H0.
      assert (~In (compose_ip_ext a i) (compose_ipl_ext ipl1 ipl2)). {
        eapply ip_not_in_compose_not_in; trivial. 
      }
      tryfalse.
    }
    {
      eapply IHipl1; eauto. inv H0; trivial.
    }
  }
Qed.

Lemma ipl_sorted_implies_compose_sorted:
  forall ipl1 ipl2,
    Sorted PolyLang.np_lt ipl1 ->
    Sorted PolyLang.np_lt ipl2 ->
    Sorted PolyLang.np_lt_ext (compose_ipl_ext ipl1 ipl2).
Proof. 
  induction ipl1.
  - intros. simpls. destruct ipl2; simpls; econs.
  - intros. simpls. destruct ipl2; simpls; econs.
    inv H. inv H0.
    eapply IHipl1; eauto.
    inv H; inv H0.
    unfold compose_ip_ext.
    destruct ipl1; destruct ipl2; try solve [econs].
    simpls.
    destruct a; destruct i; subst; simpls.
    econs. unfold PolyLang.np_lt_ext; simpls. 
    inv H4. unfold PolyLang.np_lt in H0. simpls. trivial.
Qed.

Lemma old_new_compose:
  forall ip1 ip2 ip,
    ip1 = PolyLang.old_of_ext ip ->
    ip2 = PolyLang.new_of_ext ip ->
    ip = compose_ip_ext ip1 ip2.
Proof.
  intros.
  unfold compose_ip_ext. 
  unfolds PolyLang.old_of_ext.
  unfolds PolyLang.new_of_ext.
  destruct ip; destruct ip1; destruct ip2; simpls. 
  inv H. inv H0. simpls; trivial.
Qed.

Lemma ipl_in_implies_compose_in:
  forall n ip1 ip2 ipl1 ipl2,
    nth_error ipl1 n = Some ip1 ->
    nth_error ipl2 n = Some ip2 ->
    In (compose_ip_ext ip1 ip2) (compose_ipl_ext ipl1 ipl2).
Proof. 
  induction n.
  - intros. simpls. 
    destruct ipl1; destruct ipl2; simpls; tryfalse.
    inv H; inv H0. left; trivial.
  - intros. simpls. 
    destruct ipl1; destruct ipl2; simpls; tryfalse.
    right.
    eapply IHn; eauto.
Qed.

Lemma expand_pinstr_implies_expand_pinstr_ext: 
  forall envv nth pi1 pi2 ipl1 ipl2 pi_ext ipl_ext,
    PolyLang.eqdom_pinstr pi1 pi2 ->
    PolyLang.flatten_instr_nth envv nth pi1 ipl1 -> 
    PolyLang.flatten_instr_nth envv nth pi2 ipl2 -> 
    PolyLang.compose_pinstr_ext pi1 pi2 = pi_ext ->
    compose_ipl_ext ipl1 ipl2 = ipl_ext ->
    PolyLang.flatten_instr_nth_ext envv nth pi_ext ipl_ext.
Proof.
  intros.
  pose proof H0 as G0. pose proof H1 as G1.
  assert (PolyLang.pi_poly pi1 = PolyLang.pi_poly pi2). {firstorder. }
  assert (PolyLang.pi_depth pi1 = PolyLang.pi_depth pi2) as I. {firstorder. }
  assert (PolyLang.pi_poly_ext pi_ext = PolyLang.pi_poly pi1). {
    unfold PolyLang.compose_pinstr_ext in H2. 
    destruct pi1 eqn:Hpi; subst; eauto.
  }
  assert (PolyLang.pi_depth_ext pi_ext = PolyLang.pi_depth pi1) as SAMEI. {
    unfold PolyLang.compose_pinstr_ext in H2. 
    destruct pi1 eqn:Hpi; subst; eauto.
  }
  assert (PolyLang.new_of_ext_list ipl_ext = ipl2 /\
  PolyLang.old_of_ext_list ipl_ext = ipl1). {
    eapply eqdom_pinstr_implies_ext_compose in H3; eauto.
  }
  destruct H6 as (Hipl2 & Hipl1).
  destruct H0 as (ENV1 & BEL1 & NODUP1 & SORTED1).
  destruct H1 as (ENV2 & BEL2 & NODUP2 & SORTED2).
  splits; eauto.
  - intros.
    remember (PolyLang.old_of_ext ip) as ip1.
    assert (PolyLang.ip_index_ext ip = PolyLang.ip_index ip1). {
      clear - Heqip1.
      unfold PolyLang.old_of_ext in Heqip1; subst; trivial.
    }
    rewrite H1. eapply ENV1.
    rewrite <- Hipl1. rewrite Heqip1.
    eapply in_map. trivial.
  - intros. 
    remember (PolyLang.old_of_ext ip) as ip1.
    remember (PolyLang.new_of_ext ip) as ip2.

    split; intro.
    --
      assert (In ip1 ipl1). {
        rewrite <- Hipl1. rewrite Heqip1.
        eapply in_map.
        subst. trivial.
      }

      assert (PolyLang.ip_nth_ext ip = PolyLang.ip_nth ip1). {
        clear - Heqip1.
        unfold PolyLang.old_of_ext in Heqip1; subst; trivial.
      }
      splits.
      + 
        assert (PolyLang.ip_index_ext ip = PolyLang.ip_index ip1). {
          clear - Heqip1.
          unfold PolyLang.old_of_ext in Heqip1; subst; trivial.
        }
        assert ((PolyLang.pi_poly_ext pi_ext) = (PolyLang.pi_poly pi1)). {
          clear - H2.
          unfold PolyLang.compose_pinstr_ext in H2.
          destruct pi1 eqn:Hpi; subst; eauto.
        }
        assert ((PolyLang.pi_instr_ext pi_ext) = (PolyLang.pi_instr pi1)) as PINSTR. {
          clear - H2.
          unfold PolyLang.compose_pinstr_ext in H2.
          destruct pi1 eqn:Hpi; subst; eauto.
        }
        assert ((PolyLang.pi_schedule1_ext pi_ext) = (PolyLang.pi_schedule pi1)) as PSCHED1. {
          clear - H2.
          unfold PolyLang.compose_pinstr_ext in H2.
          destruct pi1 eqn:Hpi; subst; eauto.
        }
        assert ((PolyLang.pi_schedule2_ext pi_ext) = (PolyLang.pi_schedule pi2)) as PSCHED2. {
          clear - H2.
          unfold PolyLang.compose_pinstr_ext in H2.
          destruct pi1 eqn:Hpi; subst; eauto.
        }
        assert ((PolyLang.pi_transformation_ext pi_ext) = (PolyLang.pi_transformation pi1)) as PTSF. {
          clear - H2.
          unfold PolyLang.compose_pinstr_ext in H2.
          destruct pi1 eqn:Hpi; subst; eauto.
        }
        splits; eauto.
        {
          rewrite H7. rewrite H8. eapply BEL1; eauto.
        }
        {
          assert (PolyLang.ip_transformation_ext ip = PolyLang.ip_transformation ip1). {
            unfold PolyLang.compose_pinstr_ext in SAMEI.
            destruct pi1 eqn:Hpi; simpls; subst; eauto.
          }
          rewrite H9; eauto.
          eapply (BEL1 ip1) in H1.
          destruct H1. destruct H1 as (POL & TSF & TS & INSTR & D). rewrite TSF. eauto.  
        }
        {
          assert (PolyLang.ip_time_stamp1_ext ip = PolyLang.ip_time_stamp ip1). {
            unfold PolyLang.old_of_ext in Heqip1; subst; simpls; trivial.
          }
          rewrite H7. rewrite PSCHED1. 
          rewrite H9; eauto.
          eapply (BEL1 ip1) in H1.
          destruct H1. destruct H1 as (POL & TSF & TS & INSTR & D).  eauto.  
        }
        {
          assert (PolyLang.ip_time_stamp2_ext ip = PolyLang.ip_time_stamp ip2). {
            unfold PolyLang.old_of_ext in Heqip1; subst; simpls; trivial.
          }
          rewrite PSCHED2.
          rewrite H9; eauto.
          assert (In ip2 ipl2). {
            rewrite <- Hipl2. rewrite Heqip2.
            eapply in_map.
            subst. trivial.
          }
          eapply (BEL2 ip2) in H10.
          destruct H10. destruct H10 as (POL & TSF & TS & INSTR & D).  
          assert ((PolyLang.ip_index ip2) = (PolyLang.ip_index_ext ip)). {
            unfold PolyLang.new_of_ext in Heqip2; subst; simpls; trivial.
          }
          rewrite <- H10.
          eauto. 
        }
        {
          assert (PolyLang.ip_instruction_ext ip = PolyLang.ip_instruction ip1). {
            unfold PolyLang.compose_pinstr_ext in SAMEI.
            destruct pi1 eqn:Hpi; simpls; subst; eauto.
          }
          rewrite H9; eauto.
          eapply (BEL1 ip1) in H1.
          destruct H1. destruct H1 as (POL & TSF & TS & INSTR & D). rewrite INSTR. eauto.  
        }
        {
          assert (PolyLang.ip_depth_ext ip = PolyLang.ip_depth ip1). {
            unfold PolyLang.compose_pinstr_ext in SAMEI.
            destruct pi1 eqn:Hpi; simpls; subst; eauto.
          }
          rewrite H9; eauto.
          eapply (BEL1 ip1) in H1.
          destruct H1. destruct H1 as (POL & TSF & TS & INSTR & D). rewrite D. eauto.  
        }
      + rewrite H6. eapply BEL1; eauto.
      + 
        assert (PolyLang.ip_index_ext ip = PolyLang.ip_index ip1). {
          clear - Heqip1.
          unfold PolyLang.old_of_ext in Heqip1; subst; trivial.
        }
        assert (PolyLang.pi_depth_ext pi_ext = PolyLang.pi_depth pi1). {
          clear - SAMEI.
          unfold PolyLang.compose_pinstr_ext in SAMEI.
          destruct pi1 eqn:Hpi; subst; eauto.
        }
        rewrite H7. rewrite H8. eapply BEL1; eauto.
    --
      destruct H0 as (BEL & NTH & LEN).
      assert (exists n, nth_error ipl1 n = Some ip1 /\ nth_error ipl2 n = Some ip2). {
        assert (In ip1 ipl1). {
          eapply BEL1; eauto. 
          unfolds PolyLang.old_of_ext.
          destruct ip. simpls. 
          splits; try solve [subst; simpls; trivial].
          destruct H as (DEPTH & INSTR & DOM & TSF & F & R).
          destruct BEL as (POL & TS & T1 & T2 & Instr & D). simpls.
          splits; simpls; trivial.  
          all: try solve [subst; eauto].
        }
        assert (In ip2 ipl2). {
          eapply BEL2; eauto. 
          unfolds PolyLang.new_of_ext.
          destruct ip. simpls. 
          destruct H as (DEPTH & INSTR & DOM & TSF & F & R).
          destruct BEL as (POL & TS & T1 & T2 & Instr & D). simpls.
          splits; try solve [subst; simpls; trivial].

          splits; simpls; trivial.  
          all: try solve [subst; eauto].
          subst. simpls. 
          rewrite DOM in POL; trivial.

          subst. simpls. 
          rewrite <- DEPTH; trivial.
        }

        pose proof H as G.
        eapply PolyLang.eqdom_pinstr_implies_flatten_same_np_set 
          with (ipl1:=ipl1) (ipl2:=ipl2) in H; eauto.
        eapply PolyLang.ip_ipl_same_np_same_pos; eauto.
        eapply PolyLang.eqdom_pinstr_implies_flatten_instr_same_len; eauto.
        eapply PolyLang.flatten_instr_nth_NoDupA_np; eauto.
        eapply PolyLang.flatten_instr_nth_NoDupA_np; eauto.
        clear - Heqip1 Heqip2.
        unfolds PolyLang.old_of_ext; unfolds PolyLang.new_of_ext. unfold PolyLang.np_eq.
        destruct ip; destruct ip1; destruct ip2; simpls. 
        inv Heqip1. inv Heqip2. split; trivial. eapply lex_compare_reflexive.
      }
      destruct H0 as (n & NTH1 & NTH2).
      rewrite <- H3.
      assert (ip = compose_ip_ext ip1 ip2). {
        eapply old_new_compose; eauto.
      }
      rewrite H0.
      eapply ipl_in_implies_compose_in; eauto.
  -
    rewrite <- H3.
    eapply ipl_NoDup_implies_compose_NoDup; eauto.
  - 
    rewrite <- H3.
    eapply ipl_sorted_implies_compose_sorted; eauto.
Qed.

Lemma rel_pil_implies_rel_ipl: 
  forall pil1 pil2 ipl1 ipl2 envv,
    rel_list PolyLang.eqdom_pinstr pil1 pil2 ->
    PolyLang.flatten_instrs envv pil1 ipl1 -> 
    PolyLang.flatten_instrs envv pil2 ipl2 -> 
    rel_list PolyLang.eq_except_sched ipl1 ipl2.
Proof.
  induction pil1 using rev_ind.
  {
    intros; simpls.
    destruct pil2; simpls; tryfalse.
    eapply PolyLang.flatten_instrs_nil_implies_nil in H0.
    eapply PolyLang.flatten_instrs_nil_implies_nil in H1.
    subst; simpls; trivial.
  }
  {
    intros; simpls.
    assert (exists pi2 pil2', pil2 = pil2' ++ [pi2]) as Hipl2. {
      clear - H.
      eapply rel_list_implies_eq_length in H.
      destruct pil2.
      - rewrite app_length in H; simpls; try lia.
      - assert (length (p::pil2) > 0). {rewrite app_length in H; simpls; try lia. }
        exists (last (p::pil2) (p)) (removelast (p::pil2)).
        eapply app_removelast_last. intro; tryfalse.
    }
    destruct Hipl2 as (pi2 & pil2' & Hipl2).  
    rewrite Hipl2 in H. eapply rel_list_app_singleton in H. 
    destruct H as (Hrell & Hrel).
    
    rename x into pi1; rename pil1 into pil1'.

    rewrite Hipl2 in H1.
    simpls.

    simpls.

    eapply PolyLang.flatten_instrs_app_singleton_inv in H0.
    eapply PolyLang.flatten_instrs_app_singleton_inv in H1.
    destruct H0 as (ipl1'' & ipll1'' & Hpiexpand1 & Hpilexpand1 & APP1).
    destruct H1 as (ipl2'' & ipll2'' & Hpiexpand2 & Hpilexpand2 & APP2).
    subst.

    eapply rel_list_app.
    {
      eapply IHpil1; eauto.
    }
    {
      eapply PolyLang.eqdom_pinstr_implies_flatten_instr_nth_rel'; eauto.
      assert (length pil1' = length pil2'). {
        eapply rel_list_implies_eq_length; eauto.
      }
      rewrite H; trivial.
    }
  }
Qed.

Lemma old_and_new_implies_compose: 
  forall ipl_ext ipl1 ipl2, 
  PolyLang.old_of_ext_list ipl_ext = ipl1 -> 
  PolyLang.new_of_ext_list ipl_ext = ipl2 -> 
    compose_ipl_ext ipl1 ipl2 = ipl_ext.
Proof.
  induction ipl_ext.
  {
    intros; simpls.
    subst; simpls; trivial.
  }
  {
    intros; simpls.
    rewrite <- H; rewrite <- H0.
    simpls.
    f_equal.
    {
      unfold compose_ip_ext. destruct a eqn:Ha; trivial.
    }
    {
      eapply IHipl_ext; eauto.
    }
  }
Qed.

Lemma validate_instr_and_list_implies_permutability1: 
  forall pil_ext pi1_ext env envv nth ipl1_ext ipl_ext,
    WHEN res <- validate_instr_and_list pi1_ext (rev pil_ext) (length env) THEN
    res = true ->
    PolyLang.wf_pinstr_ext env pi1_ext -> 
    Forall (PolyLang.wf_pinstr_ext env) pil_ext ->
    length env = length envv ->
    PolyLang.flatten_instr_nth_ext envv nth pi1_ext ipl1_ext -> 
    PolyLang.flatten_instrs_ext envv pil_ext ipl_ext -> 
    Instr.valid_access_function 
      (PolyLang.pi_waccess_ext pi1_ext) 
      (PolyLang.pi_raccess_ext pi1_ext) (PolyLang.pi_instr_ext pi1_ext) ->  
    Forall (fun pi2_ext => 
      Instr.valid_access_function 
        (PolyLang.pi_waccess_ext pi2_ext) 
        (PolyLang.pi_raccess_ext pi2_ext) (PolyLang.pi_instr_ext pi2_ext)  
    ) pil_ext ->
    forall ip1_ext ip2_ext, 
      In ip1_ext ipl1_ext -> 
      In ip2_ext ipl_ext -> 
      PolyLang.instr_point_ext_old_sched_lt ip1_ext ip2_ext -> 
      PolyLang.instr_point_ext_new_sched_ge ip1_ext ip2_ext -> 
      PolyLang.Permutable_ext ip1_ext ip2_ext.
Proof.
  induction pil_ext using rev_ind.
  {
    intros. intros res Hval Htrue Hwf1 Hwf2 Henvlen. intros.
    simpls.
    eapply PolyLang.flatten_instrs_ext_nil_implies_nil in H0.
    inv H0. tryfalse.
  } 
  {
    intros. intros res Hval Htrue Hwf1 Hwf2 Henvlen. 
    intros H H0 Ha1 Ha2. intros.
    rewrite rev_app_distr in Hval. simpl in Hval.
    rewrite Htrue in Hval.
    bind_imp_destruct Hval res1 Hval1.
    destruct (eqb res1 false) eqn:Hres1.
    eapply mayReturn_pure in Hval; tryfalse.
    bind_imp_destruct Hval res2 Hval2.
    destruct (eqb res2 false) eqn:Hres2.
    eapply mayReturn_pure in Hval; tryfalse.
    bind_imp_destruct Hval res3 Hval3.
    eapply mayReturn_pure in Hval.

    rename x into pi'_ext. rename pil_ext into pil'_ext.
    eapply PolyLang.flatten_instrs_ext_app_singleton_inv in H0.
    destruct H0 as (ipl'_ext & ipll'_ext & Hpiexpand & Hpilexpand & APP).
    
    rewrite APP in H2.
    eapply in_app_or in H2.
    destruct H2.
    {
      eapply IHpil_ext; eauto.
      clear - Hwf2.
      rewrite Forall_app in Hwf2. destruct Hwf2; trivial.
      clear - Ha2. eapply Forall_app in Ha2. destruct Ha2; trivial.
    }
    {
      eapply validate_pinstr_implies_permutability1 with (pi1_ext:=pi1_ext) (pi2_ext:=pi'_ext) (ipl1_ext:=ipl1_ext) (ipl2_ext:=ipll'_ext) (env:=env); eauto.
      {
        clear - Hres1.
        eapply eqb_false_iff in Hres1; destruct res1; tryfalse; trivial.
      } 
      {
        clear - Hwf2.
        eapply Forall_app in Hwf2; eauto. destruct Hwf2.
        inv H0; eauto.
      }
      {
        clear - Ha2.
        eapply Forall_app in Ha2; eauto. destruct Ha2.
        inv H0; eauto.
      }
    }
  }
Qed.

Lemma validate_instr_and_list_implies_permutability2: 
  forall pi1_ext pil_ext env envv nth ipl1_ext ipl_ext,
    WHEN res <- validate_instr_and_list pi1_ext (rev pil_ext) (length env) THEN
    res = true ->
    PolyLang.wf_pinstr_ext env pi1_ext -> 
    Forall (PolyLang.wf_pinstr_ext env) pil_ext ->
    length env = length envv ->
    PolyLang.flatten_instr_nth_ext envv nth pi1_ext ipl1_ext -> 
    PolyLang.flatten_instrs_ext envv pil_ext ipl_ext -> 
    Instr.valid_access_function 
      (PolyLang.pi_waccess_ext pi1_ext) 
      (PolyLang.pi_raccess_ext pi1_ext) (PolyLang.pi_instr_ext pi1_ext) ->  
    Forall (fun pi2_ext => 
      Instr.valid_access_function 
        (PolyLang.pi_waccess_ext pi2_ext) 
        (PolyLang.pi_raccess_ext pi2_ext) (PolyLang.pi_instr_ext pi2_ext)  
    ) pil_ext ->
    forall ip1_ext ip2_ext, 
      In ip1_ext ipl1_ext -> 
      In ip2_ext ipl_ext -> 
      PolyLang.instr_point_ext_old_sched_lt ip2_ext ip1_ext -> 
      PolyLang.instr_point_ext_new_sched_ge ip2_ext ip1_ext -> 
      PolyLang.Permutable_ext ip1_ext ip2_ext.
Proof.
  induction pil_ext using rev_ind.
  {
    intros. intros res Hval Htrue Hwf1 Hwf2 Henvlen. intros.
    simpls.
    eapply PolyLang.flatten_instrs_ext_nil_implies_nil in H0.
    inv H0. tryfalse.
  } 
  {
    intros. intros res Hval Htrue Hwf1 Hwf2 Henvlen. 
    intros H H0 Ha1 Ha2. intros.
    rewrite rev_app_distr in Hval. simpl in Hval.
    rewrite Htrue in Hval.
    bind_imp_destruct Hval res1 Hval1.
    destruct (eqb res1 false) eqn:Hres1.
    eapply mayReturn_pure in Hval; tryfalse.
    bind_imp_destruct Hval res2 Hval2.
    destruct (eqb res2 false) eqn:Hres2.
    eapply mayReturn_pure in Hval; tryfalse.
    bind_imp_destruct Hval res3 Hval3.
    eapply mayReturn_pure in Hval.

    rename x into pi'_ext. rename pil_ext into pil'_ext.
    eapply PolyLang.flatten_instrs_ext_app_singleton_inv in H0.
    destruct H0 as (ipl'_ext & ipll'_ext & Hpiexpand & Hpilexpand & APP).
    
    rewrite APP in H2.
    eapply in_app_or in H2.
    destruct H2.
    {
      eapply IHpil_ext; eauto.
      clear - Hwf2.
      rewrite Forall_app in Hwf2. destruct Hwf2; trivial.
      clear - Ha2. eapply Forall_app in Ha2. destruct Ha2; trivial.
    }
    {
      eapply PolyLang.Permutable_ext_symm.
      eapply validate_pinstr_implies_permutability1 with (pi2_ext:=pi1_ext) (pi1_ext:=pi'_ext) (ipl2_ext:=ipl1_ext) (ipl1_ext:=ipll'_ext) (env:=env); eauto. 
      {
        clear - Hres2.
        eapply eqb_false_iff in Hres2; destruct res2; tryfalse; trivial.
      }
      {
        clear - Hwf2.
        eapply Forall_app in Hwf2; eauto. destruct Hwf2.
        inv H0; eauto.
      } 
      {
        clear - Ha2.
        eapply Forall_app in Ha2; eauto. destruct Ha2.
        inv H0; eauto.
      }
    }
  }
Qed.

Lemma eqdom_pinstrs_implies_flatten_same_length:
  forall pil1 pil2 envv ipl1 ipl2, 
  rel_list PolyLang.eqdom_pinstr pil1 pil2 -> 
  PolyLang.flatten_instrs envv pil1 ipl1 ->
  PolyLang.flatten_instrs envv pil2 ipl2 -> 
  length ipl1 = length ipl2.
Proof. 
  induction pil1 using rev_ind.
  {
    intros. simpls.
    destruct pil2; tryfalse. 
    eapply PolyLang.flatten_instrs_nil_implies_nil in H0. 
    eapply PolyLang.flatten_instrs_nil_implies_nil in H1.
    subst; simpls; trivial. 
  }
  {
    intros. simpls.
    assert (exists pi2 pil2', pil2 = pil2' ++ [pi2]) as Hpil2. {
      clear - H.
      eapply rel_list_implies_eq_length in H.
      destruct pil2.
      - rewrite app_length in H; simpls; try lia.
      - assert (length (p::pil2) > 0). {rewrite app_length in H; simpls; try lia. }
        exists (last (p::pil2) (p)) (removelast (p::pil2)).
        eapply app_removelast_last. intro; tryfalse.
    }
    destruct Hpil2 as (pi2 & pil2' & Hpil2). 
    rename x into pi1; rename pil1 into pil1'.

    eapply PolyLang.flatten_instrs_app_singleton_inv in H0.
    rewrite Hpil2 in H1.
    eapply PolyLang.flatten_instrs_app_singleton_inv in H1.

    destruct H0 as (iplh1 & iplt1 & FLT1 & FLT1' & CONCAT1).
    destruct H1 as (iplh2 & iplt2 & FLT2 & FLT2' & CONCAT2).

    rewrite CONCAT1. rewrite CONCAT2.
    do 2 rewrite app_length.
    f_equal.
    {
      eapply IHpil1; eauto. 
      {
        rewrite Hpil2 in H.
        eapply rel_list_app_singleton in H.
        destruct H as (Hrel & Hrell). eauto.
      }
    }
    {
      eapply PolyLang.eqdom_pinstr_implies_flatten_instr_nth_rel' with (pi1:=pi1) (ipl1:=iplt1) in FLT2'; eauto.
      eapply rel_list_implies_eq_length in FLT2'; eauto.
      subst.
      {
        eapply rel_list_app_singleton in H.
        destruct H as (Hrel & Hrell). eauto.
      }
      assert (length pil1' = length pil2'). {
        subst.
        eapply rel_list_app_singleton in H.
        destruct H as (Hrel & Hrell). eauto.
        eapply rel_list_implies_eq_length; eauto.
      }
      rewrite <- H0.
      eauto.
    } 
  }
Qed. 

Lemma compose_pinstrs_ext_preserve_length: 
  forall pil1 pil2 pil_ext, 
    length pil1 = length pil2 -> 
    PolyLang.compose_pinstrs_ext pil1 pil2 = pil_ext -> 
    length pil1 = length pil_ext.
Proof.
  induction pil1.
  {
    intros; simpls.
    destruct pil2; tryfalse. subst; simpls; reflexivity.
  }
  {
    intros; simpls.
    destruct pil2 eqn:Hpil2; tryfalse. simpls.
    inv H. simpls.
    f_equal.
    eapply IHpil1; eauto.
  }
Qed.


Lemma flatten_instrs_implies_flatten_instrs_ext: 
  forall pil1 pil2 pil_ext ipl1 ipl2 envv,
  rel_list PolyLang.eqdom_pinstr pil1 pil2 ->
  PolyLang.flatten_instrs envv pil1 ipl1 ->
  PolyLang.flatten_instrs envv pil2 ipl2 ->
  PolyLang.compose_pinstrs_ext pil1 pil2 = pil_ext ->
  PolyLang.flatten_instrs_ext envv pil_ext (compose_ipl_ext ipl1 ipl2).
Proof.
  induction pil1 using rev_ind.
  {
    intros; simpls.
    destruct pil2; tryfalse. 
    eapply PolyLang.flatten_instrs_nil_implies_nil in H0.
    eapply PolyLang.flatten_instrs_nil_implies_nil in H1.
    subst; simpls; trivial.
    eapply PolyLang.flatten_instrs_ext_nil; eauto.
  }
  {
    intros; simpls.

    assert (exists pi2 pil2', pil2 = pil2' ++ [pi2]) as Hipl2. {
      clear - H.
      eapply rel_list_implies_eq_length in H.
      destruct pil2.
      - rewrite app_length in H; simpls; try lia.
      - assert (length (p::pil2) > 0). {rewrite app_length in H; simpls; try lia. }
        exists (last (p::pil2) (p)) (removelast (p::pil2)).
        eapply app_removelast_last. intro; tryfalse.
    }
    destruct Hipl2 as (pi2 & pil2' & Hipl2).  

    rename x into pi1; rename pil1 into pil1'.
    rewrite Hipl2 in H.
    
    eapply rel_list_app_singleton in H.
    destruct H as (Hrell & Hrel). 
    pose proof Hrel as Grel. pose proof Hrell as Grell.

    rewrite <- H2.
    rewrite Hipl2.
    rewrite compose_pinstrs_ext_app_singleton. 2: {eapply rel_list_implies_eq_length; eauto. }
    assert (length pil1' = length pil2'). {eapply rel_list_implies_eq_length; eauto. }
    rewrite Hipl2 in H1.

    eapply PolyLang.flatten_instrs_app_singleton_inv in H0.
    destruct H0 as (iplh1 & iplt1 & FLT1 & FLT1' & CONCAT1).
    eapply PolyLang.flatten_instrs_app_singleton_inv in H1.
    destruct H1 as (iplh2 & iplt2 & FLT2 & FLT2' & CONCAT2).

    rewrite CONCAT1. rewrite CONCAT2.

    assert ((compose_ipl_ext (iplh1 ++ iplt1) (iplh2 ++ iplt2)) = compose_ipl_ext iplh1 iplh2 ++ compose_ipl_ext iplt1 iplt2 ). {
      eapply ext_compose_same_length_app; eauto.
      eapply PolyLang.eqdom_pinstrs_implies_flatten_instr_nth_rel' with (ipl1:=iplh1) in FLT2; eauto.
      eapply rel_list_implies_eq_length in FLT2; trivial.
      eapply PolyLang.eqdom_pinstr_implies_flatten_instr_nth_rel' with (ipl1:=iplt1) in FLT2'; eauto.
      eapply rel_list_implies_eq_length in FLT2'; trivial.
      rewrite <- H. trivial.
    }

    rewrite H0.
    eapply PolyLang.flatten_instrs_ext_app_singleton; eauto.
    assert (length (PolyLang.compose_pinstrs_ext pil1' pil2') = length pil1'). {
      eapply compose_pinstrs_ext_preserve_length in H; eauto.
    }
    rewrite H1.
    eapply expand_pinstr_implies_expand_pinstr_ext; eauto.
    
    assert (length pil1' = length pil2'). {
      eapply rel_list_implies_eq_length in Hrell; trivial.
    }
    rewrite H3; trivial.
  }
Qed.

Lemma validate_pinstrs_implies_permutability:
  forall pil_ext pil1 pil2  env envv ipl1 ipl2 ipl_ext,   
    WHEN res <- (validate_instr_list (rev pil_ext) (length env)) THEN 
    res = true -> 
    Forall (PolyLang.wf_pinstr_ext env) pil_ext ->
    length env = length envv ->
    Forall (fun pi2_ext => 
      Instr.valid_access_function 
        (PolyLang.pi_waccess_ext pi2_ext) 
        (PolyLang.pi_raccess_ext pi2_ext) (PolyLang.pi_instr_ext pi2_ext)  
    ) pil_ext ->
    rel_list PolyLang.eqdom_pinstr pil1 pil2 ->
    PolyLang.compose_pinstrs_ext pil1 pil2 = pil_ext ->
    PolyLang.flatten_instrs envv pil1 ipl1 -> 
    PolyLang.flatten_instrs envv pil2 ipl2 ->  
    PolyLang.old_of_ext_list ipl_ext = ipl1 -> 
    PolyLang.new_of_ext_list ipl_ext = ipl2 -> 
    (
      forall ip1_ext ip2_ext, 
            In ip1_ext ipl_ext -> 
            In ip2_ext ipl_ext -> 
            PolyLang.instr_point_ext_old_sched_lt ip1_ext ip2_ext -> 
            PolyLang.instr_point_ext_new_sched_ge ip1_ext ip2_ext -> 
            PolyLang.Permutable_ext ip1_ext ip2_ext 
    ).
Proof.
  induction pil_ext using rev_ind.
  {
    intros. intros res Hval Htrue Hwf Henvlen Ha. intros.
    eapply rel_list_implies_eq_length in H.

    eapply compose_pinstrs_ext_nil in H0; trivial.
    destruct H0.
    subst.

    assert (PolyLang.old_of_ext_list ipl_ext = nil) as H3. {  
      eapply (PolyLang.flatten_instrs_nil_implies_nil envv); trivial.
    }

    eapply PolyLang.flatten_instrs_nil_implies_nil in H2.

    inv H1; inv H2. 
    unfold PolyLang.old_of_ext_list in H3.
    eapply map_eq_nil in H3.
    subst.
    tryfalse.
  }
  {
    intros. intros res Hval Htrue Hwf Henvlen Ha. intros. 
    rename x into pih_ext; rename pil_ext into pil'_ext.
    rewrite rev_app_distr in Hval; simpl in Hval.
    bind_imp_destruct Hval res1 Hres1.
    bind_imp_destruct Hval res2 Hres2.
    bind_imp_destruct Hval res3 Hres3.

    assert (exists pi1 pil1', pil1 = pil1' ++ [pi1]) as Hpil1. {
      clear - H0 H.
      eapply rel_list_implies_eq_length in H.
      assert (length (pil1) > 0). {
        eapply compose_pinstrs_ext_preserve_length in H0; trivial.
        rewrite app_length in H0. simpls. try lia.
      }
      exists (last (pil1) (PolyLang.dummy_pi)) (removelast (pil1)).
      eapply app_removelast_last. intro; subst; simpls; try lia.
    }

    assert (exists pi2 pil2', pil2 = pil2' ++ [pi2]) as Hpil2. {
      clear - H0 H.
      eapply rel_list_implies_eq_length in H.
      assert (length (pil2) > 0). {
        eapply compose_pinstrs_ext_preserve_length in H0; trivial.
        rewrite app_length in H0. simpls. try lia.
      }
      exists (last (pil2) (PolyLang.dummy_pi)) (removelast (pil2)).
      eapply app_removelast_last. intro; subst; simpls; try lia.
    }

    destruct Hpil1 as (pi1 & pil1' & Gpil1).
    destruct Hpil2 as (pi2 & pil2' & Gpil2).

    rewrite Gpil1 in H1.
    eapply PolyLang.flatten_instrs_app_singleton_inv in H1.
    destruct H1 as (iplh1 & ipl1' & Hfltpil1' & Hfltpih1 & Hipl1).
    rewrite Gpil2 in H2.
    eapply PolyLang.flatten_instrs_app_singleton_inv in H2.
    destruct H2 as (iplh2 & ipl2' & Hfltpil2' & Hfltpih2 & Hipl2).

    assert (length ipl1' = length ipl2') as G4. {
      eapply rel_list_implies_eq_length; eauto.
      rewrite Gpil1 in H; rewrite Gpil2 in H. eapply rel_list_app_singleton in H.
      destruct H as (Hrell & Hrel).
      eapply PolyLang.eqdom_pinstr_implies_flatten_instr_nth_rel' with (ipl1:=ipl1') (ipl2:=ipl2') in Hrel; eauto.
      eapply rel_list_implies_eq_length in Hrell.
      rewrite Hrell; trivial.
    }
    assert (length iplh1 = length iplh2) as G5. {
      rewrite Gpil1 in H; rewrite Gpil2 in H. eapply rel_list_app_singleton in H.
      destruct H as (Hrell & Hrel); trivial.
      eapply rel_pil_implies_rel_ipl 
      with (ipl1:=iplh1) (ipl2:=iplh2) in Hrell; eauto.
      eapply rel_list_implies_eq_length in Hrell; rewrite Hrell; trivial.
    }

    assert (length pil1' = length pil2') as Gpillen. {
      eapply rel_list_implies_eq_length; eauto.
      rewrite Gpil1 in H; rewrite Gpil2 in H. eapply rel_list_app_singleton in H.
      destruct H as (Hrell & Hrel); eauto.
    }

    remember (compose_ipl_ext iplh1 iplh2) as iplh_ext; symmetry in Heqiplh_ext.
    remember (compose_ipl_ext ipl1' ipl2') as ipl'_ext; symmetry in Heqipl'_ext.
    assert (ipl_ext = iplh_ext ++ ipl'_ext). {
      assert (compose_ipl_ext ipl1 ipl2 = ipl_ext). {
        eapply old_and_new_implies_compose; eauto.
      }
      rewrite Hipl1 in H1.
      rewrite Hipl2 in H1.
      rewrite <- H1.
      eapply ext_compose_same_length_app 
        with (iplh1:=iplh1) (iplh2:=iplh2) 
             (iplt1:=ipl1') (iplt2:=ipl2')
             (iplh_ext:=iplh_ext) (iplt_ext:=ipl'_ext); eauto.
    }

    rewrite H1 in H5; rewrite H1 in H6.
    eapply in_app_or in H5. 
    eapply in_app_or in H6.

    assert (PolyLang.compose_pinstr_ext pi1 pi2 = pih_ext). {
      rewrite Gpil1 in H0; rewrite Gpil2 in H0.
      rewrite compose_pinstrs_ext_app_singleton in H0; eauto.
      eapply app_inv_singleton in H0. destruct H0; trivial.
    }
    assert (PolyLang.compose_pinstrs_ext pil1' pil2' = pil'_ext). {
      rewrite Gpil1 in H0; rewrite Gpil2 in H0.
      rewrite compose_pinstrs_ext_app_singleton in H0; eauto.
      eapply app_inv_singleton in H0. destruct H0; trivial.
    }

    assert (res1 = true) as G1. { 
      clear - Hval Htrue.
      eapply mayReturn_pure in Hval. 
      rewrite Htrue in Hval.
      do 2 rewrite andb_true_iff in Hval; firstorder.  
    }

    assert (res2 = true) as G2. { 
      clear - Hval Htrue.
      eapply mayReturn_pure in Hval. 
      rewrite Htrue in Hval.
      do 2 rewrite andb_true_iff in Hval; firstorder.  
    }

    assert (res3 = true) as G3. { 
      clear - Hval Htrue.
      eapply mayReturn_pure in Hval. 
      rewrite Htrue in Hval.
      do 2 rewrite andb_true_iff in Hval; firstorder.  
    }

    rewrite Gpil1 in H; rewrite Gpil2 in H. 
    eapply rel_list_app_singleton in H.
    destruct H as (Hrell & Hrel).
    (* ipl = iplt ++ iplh *)
    destruct H5; destruct H6.
    {
      (* 1. ip1, ip2 in iplt *)
      eapply IHpil_ext with (pil1:=pil1') (pil2:=pil2'); eauto.
      { 
        clear - Hwf.
        eapply Forall_app in Hwf; eauto. destruct Hwf.
        eapply Forall_inv in H0; trivial.
      } 
      {
        clear - Ha.
        eapply Forall_app in Ha; eauto. destruct Ha; trivial.
      }
      eapply old_of_compose_list_ok with (ipl2:=iplh2); eauto.
      eapply new_of_compose_list_ok with (ipl2:=iplh2); eauto.
      eapply rel_pil_implies_rel_ipl; eauto.
    }
    
    {
      (* 2. ip1 in iplt, ip2 in iplh *)
      eapply PolyLang.Permutable_ext_symm.
      eapply validate_instr_and_list_implies_permutability2; eauto.
      { 
        clear - Hwf. 
        eapply Forall_app in Hwf; eauto. destruct Hwf.
        eapply Forall_inv in H0; trivial.
      }
      { 
        clear - Hwf.
        eapply Forall_app in Hwf; eauto. destruct Hwf.
        eapply Forall_inv in H0; trivial.
      } 
      eapply expand_pinstr_implies_expand_pinstr_ext 
        with (pi1:=pi1) (pi2:=pi2) (ipl1:=ipl1') (ipl2:=ipl2'); eauto.
      rewrite Gpillen; trivial.
      rewrite <- Heqiplh_ext.
      rewrite <- H9.
      eapply flatten_instrs_implies_flatten_instrs_ext; eauto.
      {
        clear - Ha.
        eapply Forall_app in Ha; eauto. destruct Ha; trivial.
        inv H0. trivial.
      }
      {
        clear - Ha.
        eapply Forall_app in Ha; eauto. destruct Ha; trivial.
      }
    }
    {
      (* 3. ip1 in iplh, ip2 in iplt *)
      eapply validate_instr_and_list_implies_permutability1; eauto.
      { 
        clear - Hwf.
        eapply Forall_app in Hwf; eauto. destruct Hwf.
        eapply Forall_inv in H0; trivial.
      }
      { 
        clear - Hwf.
        eapply Forall_app in Hwf; eauto. destruct Hwf.
        eapply Forall_inv in H0; trivial.
      } 
      eapply expand_pinstr_implies_expand_pinstr_ext 
        with (pi1:=pi1) (pi2:=pi2) (ipl1:=ipl1') (ipl2:=ipl2'); eauto.
      rewrite Gpillen; trivial.
      rewrite <- Heqiplh_ext.
      rewrite <- H9.
      eapply flatten_instrs_implies_flatten_instrs_ext; eauto.
      {
        clear - Ha.
        eapply Forall_app in Ha; eauto. destruct Ha; trivial.
        inv H0. trivial.
      }
      {
        clear - Ha.
        eapply Forall_app in Ha; eauto. destruct Ha; trivial.
      }
    }
    { 
      (* 4. ip1, ip2 in iplh *)
      eapply validate_pinstr_implies_permutability1; eauto.
      { 
        clear - Hwf.
        eapply Forall_app in Hwf; eauto. destruct Hwf.
        eapply Forall_inv in H0; trivial.
      } 
      { 
        clear - Hwf.
        eapply Forall_app in Hwf; eauto. destruct Hwf.
        eapply Forall_inv in H0; trivial.      
      } 
      eapply expand_pinstr_implies_expand_pinstr_ext 
        with (pi1:=pi1) (pi2:=pi2) (ipl1:=ipl1') (ipl2:=ipl2'); eauto.
      rewrite Gpillen; trivial.
      rewrite <- Heqiplh_ext.
      rewrite <- H9.
      eapply expand_pinstr_implies_expand_pinstr_ext 
        with (pi1:=pi1) (pi2:=pi2) (ipl1:=ipl1') (ipl2:=ipl2'); eauto.
      rewrite Gpillen; trivial.
      {
        clear - Ha.
        eapply Forall_app in Ha; eauto. destruct Ha; trivial.
        inv H0. trivial.
      }
      {
        clear - Ha.
        eapply Forall_app in Ha; eauto. destruct Ha; trivial.
        inv H0; trivial.
      }
    }
  }
Qed.

Lemma validate_implies_correspondence: 
  forall pp1 pp2 env1 env2 vars1 vars2 poly_instrs1 poly_instrs2, 
    WHEN res <- validate pp1 pp2 THEN 
    pp1 = (poly_instrs1, env1, vars1) -> 
    pp2 = (poly_instrs2, env2, vars2) ->
    res = true -> 
    PolyLang.eqdom_pprog pp1 pp2.
Proof.
  intros. intros res Hval Hpp1 Hpp2 Hres.
  eapply check_eqdom_pprog_correct; eauto.
  unfold validate in Hval.
  rewrite Hpp1 in Hval.
  rewrite Hpp2 in Hval.
  bind_imp_destruct Hval wfpil1 Hwfpil1.
  bind_imp_destruct Hval wfpil2 Hwfpil2.
  bind_imp_destruct Hval eqdom Heqdom.
  bind_imp_destruct Hval resL HresL.

  assert (eqdom = true). {
    eapply mayReturn_pure in Hval.
    subst; eauto.
    do 3 rewrite andb_true_iff in Hres.
    clear - Hres. firstorder.
  }
  subst; eauto.
Qed.

Lemma validate_implies_permutability:
  forall pp1 pp2 env1 env2 envv vars1 vars2 poly_instrs1 poly_instrs2 ipl1 ipl2, 
    WHEN res <- validate pp1 pp2 THEN 
    pp1 = (poly_instrs1, env1, vars1) -> 
    pp2 = (poly_instrs2, env2, vars2) ->
    res = true -> 
    length env1 = length envv ->
    (
      PolyLang.flatten_instrs envv poly_instrs1 ipl1 -> 
      PolyLang.flatten_instrs envv poly_instrs2 ipl2 -> 
      (exists ipl_ext, 
      PolyLang.new_of_ext_list ipl_ext = ipl2 /\ 
      PolyLang.old_of_ext_list ipl_ext = ipl1 /\ 
        (
          forall ip1_ext ip2_ext, 
            In ip1_ext ipl_ext -> 
            In ip2_ext ipl_ext -> 
            PolyLang.instr_point_ext_old_sched_lt ip1_ext ip2_ext -> 
            PolyLang.instr_point_ext_new_sched_ge ip1_ext ip2_ext -> 
            PolyLang.Permutable_ext ip1_ext ip2_ext
        )
      )
    )
.
Proof.
  intros. intros res Hval Hpp1 Hpp2 Hres Henvlen Hflt1 Hflt2.
  
  rewrite Hres in Hval.
  unfold validate in Hval.
  rewrite Hpp1 in Hval.
  rewrite Hpp2 in Hval.
  bind_imp_destruct Hval wfpil1 Hwfpil1.
  bind_imp_destruct Hval wfpil2 Hwfpil2.
  bind_imp_destruct Hval eqdom Heqdom.
  bind_imp_destruct Hval resL HresL.
  eapply mayReturn_pure in Hval.
  do 4 rewrite andb_true_iff in Hval.
  destruct Hval as ((((Hwfpil1T & Hwfpil2T) & HeqdomT) & HresLT) & HvaT).
  eapply check_eqdom_pprog_correct in Heqdom.
  eapply Heqdom in HeqdomT.
  pose proof HeqdomT as Geqdom.
  eapply eqdom_implies_ext_compose with (ipl1:=ipl1) (ipl2:=ipl2) in HeqdomT; subst; eauto.
  destruct HeqdomT as (ipl_ext & NEW & OLD) .
  
  assert (env1 = env2).
  {
    unfold PolyLang.eqdom_pprog in Geqdom.
    pose proof (Geqdom poly_instrs1 poly_instrs2 env1 env2 vars1 vars2).
    eapply H; trivial.
  }

  assert (vars1 = vars2) as EQVARS. {
    unfold PolyLang.eqdom_pprog in Geqdom.
    pose proof (Geqdom poly_instrs1 poly_instrs2 env1 env2 vars1 vars2).
    eapply H0; trivial.
  }

  eexists; splits; subst; eauto.
  eapply validate_pinstrs_implies_permutability with (pil1:=poly_instrs1) (pil2:=poly_instrs2); eauto.
  {
    eapply check_wf_polyprog_correct in Hwfpil1.
    eapply check_wf_polyprog_correct in Hwfpil2.
    clear - Hwfpil1 Hwfpil2 Geqdom. firstorder.

    assert (forall pis env vars, 
      PolyLang.wf_pprog (pis, env, vars) -> 
      Forall (PolyLang.wf_pinstr env vars) pis
    ) as WF.
    {
      clear.
      intros. unfold PolyLang.wf_pprog in H.
      eapply Forall_forall.
      eapply H; eauto.
    }
    eapply PolyLang.wf_pil_implies_wf_pil_ext; eauto.
    eapply Forall_forall; eauto. 
    eapply Forall_forall; eauto.
    eapply Geqdom; eauto.
  }
  {
    clear - HvaT.
    eapply check_valid_access_correct; trivial.
  }
  {
    unfold PolyLang.eqdom_pprog in Geqdom.
    pose proof (Geqdom poly_instrs1 poly_instrs2 env2 env2 vars2 vars2).
    eapply H; trivial.
  }
Qed.


Theorem validate_correct':
  forall pp1 pp2 env1 env2 poly_instrs1 poly_instrs2 vars1 vars2 envv st1 st2, 
    WHEN res <- validate pp1 pp2 THEN 
    pp1 = (poly_instrs1, env1, vars1) -> 
    pp2 = (poly_instrs2, env2, vars2) ->
    res = true ->
    length env1 = length envv -> 
    PolyLang.NonAlias st1 ->
    PolyLang.poly_instance_list_semantics envv pp2 st1 st2 -> 
    exists st2',
    PolyLang.poly_instance_list_semantics envv pp1 st1 st2' /\ Instr.State.eq st2 st2'.
Proof.
  intros. intros res Hval Hpp1 Hpp2 Htrue Henvlen Halias Hsem.
  inversion Hsem.
  rename ipl into ipl2.
  rename sorted_ipl into sorted_ipl2.
  pose proof Hval as G.
  rewrite Hpp1 in G. rewrite Hpp2 in G.

  eapply validate_preserve_finite with (envv:=envv) in G. 
  assert (exists ipl1, PolyLang.flatten_instrs envv poly_instrs1 ipl1). {
    subst. inv H.
    eapply G; eexists; eauto.
  } 
  clear G.
  destruct H8 as (ipl1 & Heqipl1).
  eapply validate_implies_permutability with (ipl1:=ipl1) in Hval.
  eapply Hval in Htrue; eauto.
  destruct Htrue as (ipl_ext & Hipl2 & Hipl1 & Hpermut); clear Hval.
  
  eapply PolyLang.permut_implies_ext_permut_new with (ipl_ext := ipl_ext) in H1; eauto.
  destruct H1 as (sorted_new_ipl_ext & Hpermut_ext & Hnew_ext).

  (*
    pp2 -> ipl2 -> sorted_ipl2     (Permutation, Sorted, Sema)
            ||          ||
            \/          \/
          ipl_ext sorted_new_(sched)_ipl_ext
            /\          ||
            ||  SelectionSort & map to old 
            ||          \/
    pp1 -> ipl1 -> sorted_ipl1 (Permutation_trans, SelectionSort ,StablePermut)
  *)

  remember (SelectionSort PolyLang.instr_point_ext_old_sched_ltb PolyLang.instr_point_ext_old_sched_eqb sorted_new_ipl_ext) as sorted_old_ipl_ext.
  remember (PolyLang.old_of_ext_list sorted_old_ipl_ext) as sorted_ipl1.
  symmetry in Heqsorted_old_ipl_ext.
  pose proof Heqsorted_old_ipl_ext.
  eapply PolyLang.selection_sort_instance_list_ext_implies_old_normal in H1.
  eapply PolyLang.selection_sort_instance_list_is_correct in H1.
  destruct H1 as (Hpermut_old_ext & Hsort_old_ext); eauto.
  
  eapply PolyLang.selection_sort_instance_list_ext_is_stable_permut in Heqsorted_old_ipl_ext.

  assert ((forall tau1 tau2 : PolyLang.InstrPoint_ext,
  In tau1 sorted_new_ipl_ext ->
  In tau2 sorted_new_ipl_ext ->
  PolyLang.instr_point_ext_old_sched_lt tau1 tau2 ->
  PolyLang.instr_point_ext_new_sched_ge tau1 tau2 -> PolyLang.Permutable_ext tau1 tau2)) as Hpermut'. {
    clear - Hpermut Hpermut_ext.
    eapply Permutation_sym in Hpermut_ext.
    intros; eapply Hpermut; eauto. 
    eapply Permutation_in; eauto.
    eapply Permutation_in; eauto.
  }

  pose proof PolyLang.stable_permut_ext_lists_are_equivalent sorted_new_ipl_ext sorted_old_ipl_ext Hpermut' Heqsorted_old_ipl_ext st1 Halias.
  
  destruct H1 as (F & B).
  rewrite <- Hnew_ext in H3.
  rewrite <- PolyLang.list_ext_old_new_equivalence in H3.
  pose proof F st2 H3.

  destruct H1 as (st2' & Hsem' & EQ).
  exists st2'.
  split; trivial.
  eapply PolyLang.PolyPointListSema with (sorted_ipl := sorted_ipl1) (ipl := ipl1); try solve [subst; eauto].
  { 
    (* permut list for old schedule *)
    rewrite <- Heqsorted_ipl1 in Hpermut_old_ext.
    remember (PolyLang.old_of_ext_list sorted_new_ipl_ext) as sorted_new_old_ipl1.
    eapply Permutation_trans in Hpermut_old_ext; eauto.
    clear - Hpermut_ext Hipl1 Heqsorted_new_old_ipl1.
    rewrite <- Hipl1.
    rewrite Heqsorted_new_old_ipl1.
    eapply PolyLang.ext_permut_implies_permut_old; eauto.
  }
  { (* sorted instance list for old schedule *)
    rewrite Heqsorted_ipl1.
    clear - Hsort_old_ext.
    eapply PolyLang.sortedb_lexorder_implies_sorted_lexorder; eauto.
  }
  {
    rewrite <- Hnew_ext in H2.
    eapply PolyLang.sorted_ge_implies_ext_sorted_ge; eauto.
  }
Qed.

Lemma validate_preserve_wf_pprog: 
  forall pp1 pp2,
    WHEN res <- validate pp1 pp2 THEN 
    res = true ->
    PolyLang.wf_pprog pp1 /\ PolyLang.wf_pprog pp2. 
Proof.
  intros pp1 pp2 res Hval Hres.
  unfold validate in Hval.
  destruct pp1; destruct p. destruct pp2; destruct p.
  bind_imp_destruct Hval wf1 Hwf1.
  bind_imp_destruct Hval wf2 Hwf2.
  bind_imp_destruct Hval eqdom Heqdom.
  bind_imp_destruct Hval resL HresL.
  eapply mayReturn_pure in Hval. subst.
  do 4 rewrite andb_true_iff in Hres.
  assert (wf1 = true). {
    clear - Hres.
    firstorder.
  }
  assert (wf2 = true). {
    clear - Hres.
    firstorder.
  }
  split; eapply check_wf_polyprog_correct; eauto.
Qed.

Theorem validate_correct: 
  forall pp1 pp2 st1 st2, 
    WHEN res <- validate pp1 pp2 THEN 
    res = true ->
    PolyLang.instance_list_semantics pp2 st1 st2 -> 
    exists st2',
    PolyLang.instance_list_semantics pp1 st1 st2' /\ State.eq st2 st2'.
Proof.
  intros. intros res Hval Htrue Hsem.

  inv Hsem.
  rename pis into poly_instr2; rename varctxt into env2; rename vars into vars2. 
  destruct pp1 as ((poly_instr1, env1), vars1) eqn:Hpp1.

  assert (PolIRs.Instr.NonAlias st1). {
    subst; eauto. 
  }
  assert (env1 = env2). {
    eapply validate_implies_correspondence in Hval.
    firstorder.
    eapply H3 with (varctxt1:=env1) (varctxt2:=env2) (vars3:=vars1) (vars4:=vars2); eauto.
  }

  assert (PolIRs.Instr.InitEnv env1 envv st1). {
    subst; eauto.
  }

  assert (length env1 = length envv) as Henvlen. {
    eapply PolIRs.Instr.init_env_samelen; eauto.
  }
  eapply validate_correct' with (env1:=env1) (poly_instrs1:=poly_instr1) in H2; eauto. 
  destruct H2 as (st2' & Hsem & EQ). exists st2'.
  split; trivial. econs; eauto.
  Unshelve.
Qed.

End Validator.

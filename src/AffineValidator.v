Require Import Bool.
Require Import List.
Import ListNotations.
Require Import Base.
Require Import PolyBase.  
Require Import PolyLang.
Require Import PointWitness.
Require Import TilingWitness.
Require Import AST.
Require Import BinPos.
Require Import PolyTest.
Require Import Linalg.
Require Import Canonizer.
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
Module AffineValidator (PolIRs: POLIRS).

Module Instr := PolIRs.Instr.
Module State := PolIRs.State.
Module Ty := PolIRs.Ty.
Module PolyLang := PolIRs.PolyLang.
Definition ident := Instr.ident.

(** * Proof map

    The affine validator handles a fixed set of statement instances with new
    schedules.  It pairs old and new views of each instance, rules out a
    conflicting pair whose order is reversed, derives pairwise permutability,
    and finally applies stable sorting to preserve list semantics.

    The existing section headings follow this chain: executable checks;
    paired-instance construction; collision exclusion; lifting to flattened
    lists; and [validate_correct] at the program boundary. *)






Definition point_space_witness_eqb
    : point_space_witness -> point_space_witness -> bool :=
  PointWitness.point_space_witness_eqb.






Lemma point_space_witness_eqb_eq :
  forall pw1 pw2,
    point_space_witness_eqb pw1 pw2 = true ->
    pw1 = pw2.
Proof.
  exact PointWitness.point_space_witness_eqb_eq.
Qed.


Local Lemma existsb_access_cols_eta :
  forall accesses cols,
    existsb
      (fun access : AccessFunction =>
         let (_, access_func) := access in
         if negb (check_listzzs_cols access_func cols) then true else false)
      accesses =
    existsb
      (fun access : AccessFunction =>
         let (_, access_func) := access in
         negb (check_listzzs_cols access_func cols))
      accesses.
Proof.
  intros accesses cols.
  induction accesses as [|[id access_func] accesses IH];
    simpl; [reflexivity|].
  rewrite IH.
  destruct (check_listzzs_cols access_func cols); reflexivity.
Qed.

Local Lemma false_guard_preserves_conjunction:
  forall (condition affine_result general_result route_check : bool),
    affine_result = general_result && route_check ->
    (if condition then false else affine_result) =
      (if condition then false else general_result) && route_check.
Proof.
  intros [] affine_result general_result route_check Hresults;
    simpl; [reflexivity|exact Hresults].
Qed.

Definition check_wf_polyinstr (pi: PolyLang.PolyInstr) (env: list ident) (vars: list (ident * Ty.t)) := 
  let env_dim := length env in 
  let iter_dim := (pi.(PolyLang.pi_depth)) in
  let domain := pi.(PolyLang.pi_poly) in
  let domain_len := length domain in 
  let current_dim := PolyLang.pinstr_current_dim env pi in
  let base_dim := env_dim + witness_base_point_dim (pi.(PolyLang.pi_point_witness)) in
  let arg_dim := length (pi.(PolyLang.pi_transformation)) in
  let witness_dim_ok := Nat.eqb
    (witness_current_point_dim (pi.(PolyLang.pi_point_witness)))
    iter_dim in
  if negb (Instr.check_never_written env pi.(PolyLang.pi_instr)) then false else
  if negb witness_dim_ok then false else
  if negb (env_dim + iter_dim <=? current_dim) then false else 
  (** schedule iterators *)
  if negb (poly_nrl (PolyLang.pi_poly pi) <=? current_dim) then false else  
  if negb (poly_nrl (PolyLang.pi_schedule pi) <=? current_dim) then false else 
  (* domain cols = env_dim + iter_dim *)
  if negb (check_listzzs_cols domain (env_dim + iter_dim))
  then false else 
  (* transformation cols = env_dim + base_point_dim *)
  if negb (check_listzzs_cols (pi.(PolyLang.pi_transformation)) base_dim)
    then false else 
  if negb (check_listzzs_cols (pi.(PolyLang.pi_access_transformation)) base_dim)
    then false else 
  (* schedule cols = env_dim + iter_dim *)
  if negb (check_listzzs_cols pi.(PolyLang.pi_schedule) (env_dim + iter_dim)) 
  then false 
  (* waccess/raccess cols = source-argument dimension *)
  else 
  if existsb (fun (waccess: AccessFunction) => 
    let (arrid, waccess_aff_func) := waccess in 
      if negb (check_listzzs_cols waccess_aff_func arg_dim) 
      then true else false 
    ) pi.(PolyLang.pi_waccess)  
  then false else
  if existsb (fun (raccess: AccessFunction) => 
      let (arrid, raccess_aff_func) := raccess in 
        if negb (check_listzzs_cols raccess_aff_func arg_dim) 
        then true else false 
    ) pi.(PolyLang.pi_raccess) 
  then false else 
  let witness_id_ok :=
    point_space_witness_eqb
      pi.(PolyLang.pi_point_witness)
      (PSWIdentity iter_dim) in
  let tf_eq_ok := listzzs_strict_eqb pi.(PolyLang.pi_transformation) pi.(PolyLang.pi_access_transformation) in
  witness_id_ok && tf_eq_ok.

Definition check_wf_polyprog (pp: PolyLang.t) := 
  let '(pil, varctxt, vars) := pp in   
  let pil_dim := length pil in
  let varctxt_dim := length varctxt in 
  let vars_dim := length vars in 
  pure (Nat.leb varctxt_dim vars_dim && Nat.ltb 0 pil_dim && forallb (fun pi => check_wf_polyinstr pi varctxt vars) pil).

Definition check_wf_polyinstr_tiling
    (pi: PolyLang.PolyInstr) (env: list ident) (vars: list (ident * Ty.t)) :=
  let env_dim := length env in
  let iter_dim := pi.(PolyLang.pi_depth) in
  let current_dim := PolyLang.pinstr_current_dim env pi in
  let vars_dim := length vars in
  let base_dim := env_dim + witness_base_point_dim (pi.(PolyLang.pi_point_witness)) in
  let arg_dim := length (pi.(PolyLang.pi_transformation)) in
  let witness_dim_ok := Nat.eqb
    (witness_current_point_dim (pi.(PolyLang.pi_point_witness)))
    iter_dim in
  if negb (Instr.check_never_written env pi.(PolyLang.pi_instr)) then false else
  if negb witness_dim_ok then false else
  if negb ((env_dim + iter_dim) <=? current_dim) then false else
  if negb (poly_nrl (PolyLang.pi_poly pi) <=? current_dim) then false else
  if negb (poly_nrl (PolyLang.pi_schedule pi) <=? current_dim) then false else
  if negb (check_listzzs_cols (PolyLang.pi_poly pi) (env_dim + iter_dim))
  then false else
  if negb (check_listzzs_cols (PolyLang.pi_transformation pi) base_dim)
  then false else
  if negb (check_listzzs_cols (PolyLang.pi_access_transformation pi) base_dim)
  then false else
  if negb (check_listzzs_cols (PolyLang.pi_schedule pi) (env_dim + iter_dim))
  then false else
  if existsb
      (fun (waccess: AccessFunction) =>
         let (_, waccess_aff_func) := waccess in
         negb (check_listzzs_cols waccess_aff_func arg_dim))
      pi.(PolyLang.pi_waccess)
  then false else
  if existsb
      (fun (raccess: AccessFunction) =>
         let (_, raccess_aff_func) := raccess in
         negb (check_listzzs_cols raccess_aff_func arg_dim))
      pi.(PolyLang.pi_raccess)
  then false else
  listzzs_strict_eqb
    pi.(PolyLang.pi_transformation)
    pi.(PolyLang.pi_access_transformation).

Definition check_wf_polyprog_tiling (pp: PolyLang.t) :=
  let '(pil, varctxt, vars) := pp in
  let pil_dim := length pil in
  let varctxt_dim := length varctxt in
  let vars_dim := length vars in
  pure
    (Nat.leb varctxt_dim vars_dim &&
     Nat.ltb 0 pil_dim &&
     forallb (fun pi => check_wf_polyinstr_tiling pi varctxt vars) pil).

(** Historical `*_tiling` names are compatibility aliases; this checker is the
    general witness-aware wf checker used by the shared schedule validator. *)
Definition check_wf_polyinstr_general := check_wf_polyinstr_tiling.
Definition check_wf_polyprog_general := check_wf_polyprog_tiling.

Definition EqDomInstr (pi1 pi2: PolyLang.PolyInstr) := 
  let iters_eq := Nat.eqb pi1.(PolyLang.pi_depth) pi2.(PolyLang.pi_depth) in 
  let inst_eq := Instr.eqb pi1.(PolyLang.pi_instr) pi2.(PolyLang.pi_instr) in 
  let dom_eq := listzzs_strict_eqb pi1.(PolyLang.pi_poly) pi2.(PolyLang.pi_poly) in 
  let witness_eq := point_space_witness_eqb pi1.(PolyLang.pi_point_witness) pi2.(PolyLang.pi_point_witness) in
  let trans_eq := listzzs_strict_eqb pi1.(PolyLang.pi_transformation) pi2.(PolyLang.pi_transformation) in
  let access_trans_eq := listzzs_strict_eqb pi1.(PolyLang.pi_access_transformation) pi2.(PolyLang.pi_access_transformation) in
  let raccess_eq := access_list_strict_eqb pi1.(PolyLang.pi_raccess) pi2.(PolyLang.pi_raccess) in 
  let waccess_eq := access_list_strict_eqb pi1.(PolyLang.pi_waccess) pi2.(PolyLang.pi_waccess) in 
  iters_eq && inst_eq && dom_eq && witness_eq && trans_eq && access_trans_eq && raccess_eq && waccess_eq.

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



(** Keep the rational-empty path unchanged.  On failure, integer
    canonicalization can rule out fractional witnesses. *)
Definition isBottom_integer_fallback (pol: polyhedron) :=
  BIND empty <- isBottom pol -;
  if empty then pure true else
  BIND integer_pol <- VplCanonizerZ.canonize pol -;
  isBottom integer_pol.

Lemma isBottom_integer_fallback_correct:
  forall pol, If isBottom_integer_fallback pol THEN
    forall p, in_poly p pol = false.
Proof.
  intros pol [] Hcheck; simpl; [|auto].
  unfold isBottom_integer_fallback in Hcheck.
  bind_imp_destruct Hcheck empty Hempty.
  destruct empty.
  - exact (isBottom_correct_1 pol true Hempty).
  - bind_imp_destruct Hcheck integer_pol Hinteger.
    apply isBottom_correct_1 in Hcheck.
    intros p.
    rewrite <- (VplCanonizerZ.canonize_correct pol integer_pol Hinteger p).
    exact (Hcheck p).
Qed.

Definition validate_lt_ge_pair (pol_lt pol_ge sameloc_enveq_indom_pol: polyhedron) := 
  BIND sameloc_pol_lt <- poly_inter pol_lt sameloc_enveq_indom_pol -;
  BIND sameloc_pol_lt_ge <- poly_inter sameloc_pol_lt pol_ge -;
  BIND isbot <- isBottom_integer_fallback sameloc_pol_lt_ge -;
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

Definition access_matches_tf (tf: AffineFunction) (a: AccessFunction) : Prop :=
  let '(_, loc) := a in
  exact_listzzs_cols (length tf) loc.

Definition compose_access_function_at
    (dom_dim: nat) (a: AccessFunction) (tf: AffineFunction) : AccessFunction :=
  let '(id, loc) := a in
  let loc' :=
    if (length tf =? 0)%nat
    then List.map (fun '(_, c) => (repeat 0%Z dom_dim, c)) loc
    else matrix_product loc tf in
  (id, loc').

Lemma affine_product_zero_padded_access :
  forall dom_dim p loc,
    length p = dom_dim ->
    exact_listzzs_cols 0 loc ->
    affine_product
      (List.map (fun '(_, c) => (repeat 0%Z dom_dim, c)) loc) p =
    affine_product loc [].
Proof.
  intros dom_dim p loc Hlen Hloc.
  induction loc as [|[v c] loc IH]; simpl.
  - reflexivity.
  - assert (Hv : length v = 0).
    { eapply Hloc; [left; reflexivity|reflexivity]. }
    assert (Htail : exact_listzzs_cols 0 loc).
    { intros listz z listzz Hin Heq.
      eapply Hloc; [right; exact Hin|exact Heq]. }
    rewrite dot_product_repeat_zero_left by exact Hlen.
    destruct v as [|x xs].
    + simpl. f_equal. eapply IH; eauto.
    + simpl in Hv. discriminate.
Qed.

Lemma compose_access_function_at_exact_cols :
  forall dom_dim a tf,
    exact_listzzs_cols dom_dim tf ->
    access_matches_tf tf a ->
    exact_listzzs_cols dom_dim (snd (compose_access_function_at dom_dim a tf)).
Proof.
  intros dom_dim [id loc] tf Htf Hloc.
  unfold compose_access_function_at, access_matches_tf in *; simpl in *.
  destruct (length tf =? 0)%nat eqn:Htf0.
  - intros listz z listzz Hin Heq.
    rewrite in_map_iff in Hin.
    destruct Hin as [[v c] [Hmap Hin0]].
    rewrite Heq in Hmap.
    inversion Hmap; subst listzz listz z.
    rewrite repeat_length. reflexivity.
  - eapply matrix_product_cols.
    + eapply Nat.eqb_neq in Htf0. lia.
    + exact Htf.
Qed.

Lemma compose_access_function_at_correct :
  forall dom_dim a tf p,
    length p = dom_dim ->
    exact_listzzs_cols dom_dim tf ->
    access_matches_tf tf a ->
    affine_product (snd (compose_access_function_at dom_dim a tf)) p =
    affine_product (snd a) (affine_product tf p).
Proof.
  intros dom_dim [id loc] tf p Hlen Htf Hloc.
  unfold compose_access_function_at, access_matches_tf in *; simpl in *.
  destruct (length tf =? 0)%nat eqn:Htf0.
  - apply Nat.eqb_eq in Htf0.
    destruct tf as [|row tf']; simpl in *; [|discriminate].
    rewrite affine_product_zero_padded_access with (p:=p) (dom_dim:=dom_dim); auto.
  - eapply matrix_product_assoc; eauto.
Qed.

Definition validate_two_accesses (a1 a2: AccessFunction) (tf1 tf2: AffineFunction) (env_eq_in_dom_poly: polyhedron) (old_sched_lt_polys new_sched_ge_polys: list polyhedron)
(dim1 dim2: nat):= 
  let (id1, loc1) := a1 in 
  let (id2, loc2) := a2 in 
  if negb (Pos.eqb id1 id2) then pure true else
  (* construct polyhedron for same array-access subscripts *)
  let sameloc :=
    make_poly_eq
      (snd (compose_access_function_at dim1 a1 tf1))
      (snd (compose_access_function_at dim2 a2 tf2))
      dim1 dim2 [] in 
  BIND sameloc_enveq_indom_pol <- poly_inter sameloc env_eq_in_dom_poly -;  
  (* check if lexicographic order is violated for dependent accesses *)
  validate_two_accesses_helper old_sched_lt_polys new_sched_ge_polys sameloc_enveq_indom_pol.


Definition schedules_unchanged (pi1 pi2: PolyLang.PolyInstr_ext) :=
  listzzs_strict_eqb pi1.(PolyLang.pi_schedule1_ext) pi1.(PolyLang.pi_schedule2_ext)
  && listzzs_strict_eqb pi2.(PolyLang.pi_schedule1_ext) pi2.(PolyLang.pi_schedule2_ext).

Definition validate_two_instrs (pi1 pi2: PolyLang.PolyInstr_ext) (env_dim: nat) :=
  if schedules_unchanged pi1 pi2 then pure true else
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
      validate_two_accesses waccess1 waccess2 pi1.(PolyLang.pi_access_transformation_ext) pi2.(PolyLang.pi_access_transformation_ext) pol old_sched_lt_polys new_sched_ge_polys dom_dim1 dom_dim2
    ) pi2.(PolyLang.pi_waccess_ext)
  ) pi1.(PolyLang.pi_waccess_ext) -;
  
  BIND res2 <- forallb_imp (
    fun waccess1 => forallb_imp (fun raccess2 =>
      validate_two_accesses waccess1 raccess2 pi1.(PolyLang.pi_access_transformation_ext) pi2.(PolyLang.pi_access_transformation_ext) pol old_sched_lt_polys new_sched_ge_polys dom_dim1 dom_dim2
    ) pi2.(PolyLang.pi_raccess_ext) 
  ) pi1.(PolyLang.pi_waccess_ext) -;

  BIND res3 <- forallb_imp (
    fun raccess1 => forallb_imp (fun waccess2 =>
      validate_two_accesses raccess1 waccess2 pi1.(PolyLang.pi_access_transformation_ext) pi2.(PolyLang.pi_access_transformation_ext) pol old_sched_lt_polys new_sched_ge_polys dom_dim1 dom_dim2
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

Definition compose_pinstr_ext_at
    (env_dim: nat)
    (pi1 pi2: PolyLang.PolyInstr) : PolyLang.PolyInstr_ext := {|
  PolyLang.pi_depth_ext := pi1.(PolyLang.pi_depth);
  PolyLang.pi_instr_ext := pi1.(PolyLang.pi_instr);
  PolyLang.pi_poly_ext := pi1.(PolyLang.pi_poly);
  PolyLang.pi_point_witness_ext := pi1.(PolyLang.pi_point_witness);
  PolyLang.pi_transformation_ext :=
    PolyLang.current_transformation_at env_dim pi1;
  PolyLang.pi_access_transformation_ext :=
    PolyLang.current_access_transformation_at env_dim pi1;
  PolyLang.pi_schedule1_ext := pi1.(PolyLang.pi_schedule);
  PolyLang.pi_schedule2_ext := pi2.(PolyLang.pi_schedule);
  PolyLang.pi_waccess_ext := pi1.(PolyLang.pi_waccess);
  PolyLang.pi_raccess_ext := pi1.(PolyLang.pi_raccess);
|}.

Fixpoint compose_pinstrs_ext_at
    (env_dim: nat)
    (pil1 pil2: list PolyLang.PolyInstr) : list PolyLang.PolyInstr_ext :=
  match pil1, pil2 with
  | pi1 :: pil1', pi2 :: pil2' =>
      compose_pinstr_ext_at env_dim pi1 pi2 ::
      compose_pinstrs_ext_at env_dim pil1' pil2'
  | [], [] => []
  | _, _ => []
  end.

Definition validate (pp1 pp2: PolyLang.t) := 
  let '(pil1, varctxt1, vars1) := pp1 in 
  let '(pil2, varctxt2, vars2) := pp2 in 
  BIND wf_pil1 <- check_wf_polyprog pp1 -;
  BIND wf_pil2 <- check_wf_polyprog pp2 -;
  BIND eqdom <- EqDom pp1 pp2 -;
  let env_dim := length varctxt1 in
  let pil_ext := compose_pinstrs_ext_at env_dim pil1 pil2 in
  let valid_access := check_valid_access pil_ext in
  BIND res <- validate_instr_list (rev pil_ext) env_dim -;
  pure (wf_pil1 && wf_pil2 && eqdom && res && valid_access).

Definition validate_tiling (pp1 pp2: PolyLang.t) :=
  let '(pil1, varctxt1, vars1) := pp1 in
  let '(pil2, varctxt2, vars2) := pp2 in
  BIND wf_pil1 <- check_wf_polyprog_tiling pp1 -;
  BIND wf_pil2 <- check_wf_polyprog_tiling pp2 -;
  BIND eqdom <- EqDom pp1 pp2 -;
  let env_dim := length varctxt1 in
  let pil_ext := compose_pinstrs_ext_at env_dim pil1 pil2 in
  let valid_access := check_valid_access pil_ext in
  BIND res <- validate_instr_list (rev pil_ext) env_dim -;
  pure (wf_pil1 && wf_pil2 && eqdom && res && valid_access).

(** Historical compatibility name: this is the general witness-aware schedule
    validator reused inside the checked tiling validator after structure/witness
    checks have already succeeded. *)
Definition validate_general := validate_tiling.

(** * Soundness of the Boolean validation checks *)

Local Lemma check_wf_polyinstr_affine_as_general:
  forall pi env vars,
    check_wf_polyinstr pi env vars =
      check_wf_polyinstr_tiling pi env vars &&
      point_space_witness_eqb
        pi.(PolyLang.pi_point_witness)
        (PSWIdentity pi.(PolyLang.pi_depth)).
Proof.
  intros pi env vars.
  unfold check_wf_polyinstr, check_wf_polyinstr_tiling.
  rewrite
    (existsb_access_cols_eta
       (PolyLang.pi_waccess pi)
       (length (PolyLang.pi_transformation pi))).
  rewrite
    (existsb_access_cols_eta
       (PolyLang.pi_raccess pi)
       (length (PolyLang.pi_transformation pi))).
  repeat apply false_guard_preserves_conjunction.
  apply andb_comm.
Qed.

Local Lemma check_wf_polyinstr_common_correct:
  forall pi env vars,
    check_wf_polyinstr_tiling pi env vars = true ->
    PolyLang.wf_pinstr env vars pi /\
    pi.(PolyLang.pi_transformation) =
      pi.(PolyLang.pi_access_transformation).
Proof.
  intros pi env vars Hcheck.
  unfold check_wf_polyinstr_tiling in Hcheck.
  destruct
    (negb (Instr.check_never_written env (PolyLang.pi_instr pi)))
    eqn:Hnever_written; tryfalse.
  destruct
    (negb
       (witness_current_point_dim (PolyLang.pi_point_witness pi) =?
        PolyLang.pi_depth pi))
    eqn:Hwitness_dim; tryfalse.
  destruct
    ((length env + PolyLang.pi_depth pi <=?
      PolyLang.pinstr_current_dim env pi)%nat)
    eqn:Henvlen; tryfalse.
  destruct
    ((poly_nrl (PolyLang.pi_poly pi) <=?
      PolyLang.pinstr_current_dim env pi)%nat)
    eqn:Hdom; tryfalse.
  destruct
    ((poly_nrl (PolyLang.pi_schedule pi) <=?
      PolyLang.pinstr_current_dim env pi)%nat)
    eqn:Hsched; tryfalse.
  destruct
    (negb
       (check_listzzs_cols
          (PolyLang.pi_poly pi)
          (length env + PolyLang.pi_depth pi)))
    eqn:Hcheckdom; tryfalse.
  destruct
    (negb
       (check_listzzs_cols
          (PolyLang.pi_transformation pi)
          (length env +
           witness_base_point_dim (PolyLang.pi_point_witness pi))))
    eqn:Hchecktf; tryfalse.
  destruct
    (negb
       (check_listzzs_cols
          (PolyLang.pi_access_transformation pi)
          (length env +
           witness_base_point_dim (PolyLang.pi_point_witness pi))))
    eqn:Hcheckacc_tf; tryfalse.
  destruct
    (negb
       (check_listzzs_cols
          (PolyLang.pi_schedule pi)
          (length env + PolyLang.pi_depth pi)))
    eqn:Hchecksched; tryfalse.
  destruct
    (existsb
       (fun waccess : AccessFunction =>
          let (_, waccess_aff_func) := waccess in
          negb
            (check_listzzs_cols
               waccess_aff_func
               (length (PolyLang.pi_transformation pi))))
       (PolyLang.pi_waccess pi))
    eqn:Hcheckw; tryfalse.
  destruct
    (existsb
       (fun raccess : AccessFunction =>
          let (_, raccess_aff_func) := raccess in
          negb
            (check_listzzs_cols
               raccess_aff_func
               (length (PolyLang.pi_transformation pi))))
       (PolyLang.pi_raccess pi))
    eqn:Hcheckr; tryfalse.
  eapply negb_false_iff in Hwitness_dim.
  eapply Nat.eqb_eq in Hwitness_dim.
  eapply Nat.leb_le in Henvlen.
  eapply Nat.leb_le in Hdom.
  eapply Nat.leb_le in Hsched.
  eapply negb_false_iff in Hcheckdom.
  eapply check_listzzs_cols_correct in Hcheckdom.
  eapply negb_false_iff in Hchecktf.
  eapply check_listzzs_cols_correct in Hchecktf.
  eapply negb_false_iff in Hcheckacc_tf.
  eapply check_listzzs_cols_correct in Hcheckacc_tf.
  eapply negb_false_iff in Hchecksched.
  eapply check_listzzs_cols_correct in Hchecksched.
  assert
    (Hwaccesses:
      Forall
        (fun waccess : AccessFunction =>
           let (_, waccess_func) := waccess in
           exact_listzzs_cols
             (length (PolyLang.pi_transformation pi))
             waccess_func)
        (PolyLang.pi_waccess pi)).
  {
    eapply Forall_forall. intros [warrid waccess_func] Hin.
    rewrite Misc.existsb_forall in Hcheckw.
    specialize (Hcheckw (warrid, waccess_func) Hin).
    simpl in Hcheckw.
    eapply negb_false_iff in Hcheckw.
    eapply check_listzzs_cols_correct; exact Hcheckw.
  }
  assert
    (Hraccesses:
      Forall
        (fun raccess : AccessFunction =>
           let (_, raccess_func) := raccess in
           exact_listzzs_cols
             (length (PolyLang.pi_transformation pi))
             raccess_func)
        (PolyLang.pi_raccess pi)).
  {
    eapply Forall_forall. intros [rarrid raccess_func] Hin.
    rewrite Misc.existsb_forall in Hcheckr.
    specialize (Hcheckr (rarrid, raccess_func) Hin).
    simpl in Hcheckr.
    eapply negb_false_iff in Hcheckr.
    eapply check_listzzs_cols_correct; exact Hcheckr.
  }
  eapply listzzs_strict_eqb_eq in Hcheck.
  split.
  - unfold PolyLang.wf_pinstr.
    repeat split; assumption.
  - exact Hcheck.
Qed.

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

Lemma check_wf_polyinstr_affine_correct: 
  forall pi env vars,
    check_wf_polyinstr pi env vars = true -> 
    PolyLang.wf_pinstr_affine env vars pi.
Proof.
  intros pi env vars Hcheck.
  rewrite check_wf_polyinstr_affine_as_general in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hcommon Hwitness_id].
  destruct
    (check_wf_polyinstr_common_correct pi env vars Hcommon)
    as [Hwf Htransformation].
  unfold PolyLang.wf_pinstr_affine.
  split.
  - exact Hwf.
  - split.
    + eapply point_space_witness_eqb_eq; exact Hwitness_id.
    + exact Htransformation.
Qed.

Lemma check_wf_polyinstr_correct: 
  forall pi env vars,
    check_wf_polyinstr pi env vars = true -> 
    PolyLang.wf_pinstr env vars pi.
Proof.
  intros pi env vars Hwf.
  eapply PolyLang.wf_pinstr_affine_implies_wf_pinstr.
  eapply check_wf_polyinstr_affine_correct; eauto.
Qed.

Lemma check_wf_polyinstr_tiling_correct :
  forall pi env vars,
    check_wf_polyinstr_tiling pi env vars = true ->
    PolyLang.wf_pinstr_tiling env vars pi.
Proof.
  intros pi env vars Hcheck.
  unfold PolyLang.wf_pinstr_tiling.
  eapply check_wf_polyinstr_common_correct; eauto.
Qed.

Local Lemma forallb_wf_polyprog_correct:
  forall
    (check : PolyLang.PolyInstr -> bool)
    (wf : PolyLang.PolyInstr -> Prop)
    (pil : list PolyLang.PolyInstr)
    (env : list ident)
    (vars : list (ident * Ty.t)),
    (forall pi, check pi = true -> wf pi) ->
    (Nat.leb (length env) (length vars) &&
     Nat.ltb 0 (length pil) &&
     forallb check pil) = true ->
    length env <= length vars /\
    forall pi, In pi pil -> wf pi.
Proof.
  intros check wf pil env vars Hcheck Hprogram.
  do 2 rewrite andb_true_iff in Hprogram.
  destruct Hprogram as ((Henv & _) & Hforall).
  split.
  - eapply Nat.leb_le; exact Henv.
  - intros pi Hin.
    eapply Hcheck.
    eapply forallb_forall with (x:=pi) in Hforall; eauto.
Qed.

Lemma check_wf_polyprog_affine_correct: 
  forall pp, 
    WHEN res <- check_wf_polyprog pp THEN 
    res = true ->
    PolyLang.wf_pprog_affine pp.
Proof.
  intros pp res Hcheckwf Htrue.
  rewrite Htrue in Hcheckwf.
  unfold check_wf_polyprog in Hcheckwf.
  destruct pp as (p & vars).
  destruct p as (pil, varctxt).
  eapply mayReturn_pure in Hcheckwf.
  unfold PolyLang.wf_pprog_affine.
  eapply
    (forallb_wf_polyprog_correct
       (fun pi => check_wf_polyinstr pi varctxt vars)
       (fun pi => PolyLang.wf_pinstr_affine varctxt vars pi)
       pil varctxt vars).
  - intros pi Hcheck.
    eapply check_wf_polyinstr_affine_correct; eauto.
  - exact Hcheckwf.
Qed. 

Lemma check_wf_polyprog_correct: 
  forall pp, 
    WHEN res <- check_wf_polyprog pp THEN 
    res = true ->
    PolyLang.wf_pprog pp.
Proof.
  intros pp res Hcheck Htrue.
  eapply PolyLang.wf_pprog_affine_implies_wf_pprog.
  eapply check_wf_polyprog_affine_correct; eauto.
Qed. 

Lemma check_wf_polyprog_tiling_correct :
  forall pp,
    WHEN res <- check_wf_polyprog_tiling pp THEN
    res = true ->
    PolyLang.wf_pprog_tiling pp.
Proof.
  intros pp res Hcheckwf Htrue.
  rewrite Htrue in Hcheckwf.
  unfold check_wf_polyprog_tiling in Hcheckwf.
  destruct pp as (p & vars).
  destruct p as (pil, varctxt).
  eapply mayReturn_pure in Hcheckwf.
  unfold PolyLang.wf_pprog_tiling, PolyLang.wf_pprog_general.
  eapply
    (forallb_wf_polyprog_correct
       (fun pi => check_wf_polyinstr_tiling pi varctxt vars)
       (fun pi => PolyLang.wf_pinstr_tiling varctxt vars pi)
       pil varctxt vars).
  - intros pi Hcheck.
    eapply check_wf_polyinstr_tiling_correct; eauto.
  - exact Hcheckwf.
Qed.

Lemma check_eqdom_pinstr_correct: 
  forall pi1 pi2, 
  EqDomInstr pi1 pi2 ->
  PolyLang.eqdom_pinstr pi1 pi2.
Proof.
  intros pi1 pi2 H.
  unfold PolyLang.eqdom_pinstr.
  unfold EqDomInstr in H.
  apply andb_true_iff in H. destruct H as [H Hwaccess].
  apply andb_true_iff in H. destruct H as [H Hraccess].
  apply andb_true_iff in H. destruct H as [H Haccess_tf].
  apply andb_true_iff in H. destruct H as [H Htf].
  apply andb_true_iff in H. destruct H as [H Hwitness].
  apply andb_true_iff in H. destruct H as [H Hdom].
  apply andb_true_iff in H. destruct H as [Hiters Hinst].
  apply Nat.eqb_eq in Hiters.
  apply Instr.eqb_eq in Hinst.
  apply listzzs_strict_eqb_eq in Hdom.
  apply point_space_witness_eqb_eq in Hwitness.
  apply listzzs_strict_eqb_eq in Htf.
  apply listzzs_strict_eqb_eq in Haccess_tf.
  apply access_list_strict_eqb_eq in Hraccess.
  apply access_list_strict_eqb_eq in Hwaccess.
  repeat split; assumption.
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

(** * Construction and projection of paired instruction instances *)


Definition compose_ip_ext_at
  (access_tf: Transformation)
  (ip1 ip2: PolyLang.InstrPoint): PolyLang.InstrPoint_ext :=
    {|
      PolyLang.ip_nth_ext := ip1.(PolyLang.ip_nth);
      PolyLang.ip_index_ext := ip1.(PolyLang.ip_index);
      PolyLang.ip_transformation_ext := ip1.(PolyLang.ip_transformation);
      PolyLang.ip_access_transformation_ext := access_tf;
      PolyLang.ip_time_stamp1_ext := ip1.(PolyLang.ip_time_stamp);
      PolyLang.ip_time_stamp2_ext := ip2.(PolyLang.ip_time_stamp);
      PolyLang.ip_instruction_ext := ip1.(PolyLang.ip_instruction);
      PolyLang.ip_depth_ext := ip1.(PolyLang.ip_depth);
    |}.


Lemma old_of_compose_at_ok:
  forall access_tf ip1 ip2 ip_ext,
    compose_ip_ext_at access_tf ip1 ip2 = ip_ext ->
    PolyLang.old_of_ext ip_ext = ip1.
Proof.
  intros.
  unfold compose_ip_ext_at in H.
  unfold PolyLang.old_of_ext.
  destruct ip_ext; simpls.
  inv H. destruct ip1; trivial.
Qed.


Lemma new_of_compose_at_ok:
  forall access_tf ip1 ip2 ip_ext,
    ip1.(PolyLang.ip_nth) = ip2.(PolyLang.ip_nth) ->
    ip1.(PolyLang.ip_index) = ip2.(PolyLang.ip_index) ->
    ip1.(PolyLang.ip_transformation) = ip2.(PolyLang.ip_transformation) ->
    ip1.(PolyLang.ip_instruction) = ip2.(PolyLang.ip_instruction) ->
    ip1.(PolyLang.ip_depth) = ip2.(PolyLang.ip_depth) ->
    compose_ip_ext_at access_tf ip1 ip2 = ip_ext ->
    PolyLang.new_of_ext ip_ext = ip2.
Proof.
  intros.
  unfold compose_ip_ext_at in H4.
  unfold PolyLang.new_of_ext.
  destruct ip_ext; simpls. inv H4.
  destruct ip1; destruct ip2; simpls; subst; trivial.
Qed.


Fixpoint compose_ipl_ext_at
  (access_tf: Transformation)
  (ipl1 ipl2: list PolyLang.InstrPoint): list PolyLang.InstrPoint_ext :=
  match ipl1, ipl2 with
  | ip1 :: ipl1', ip2 :: ipl2' =>
      compose_ip_ext_at access_tf ip1 ip2 :: compose_ipl_ext_at access_tf ipl1' ipl2'
  | [], [] => []
  | _, _ => []
  end.

Lemma current_env_dim_of_eq:
  forall pw current env_dim,
    length current = (env_dim + witness_current_point_dim pw)%nat ->
    PolyLang.current_env_dim_of pw current = env_dim.
Proof.
  intros pw current env_dim Hlen.
  unfold PolyLang.current_env_dim_of.
  lia.
Qed.

Lemma current_transformation_of_eq_at:
  forall pi current env_dim,
    witness_current_point_dim (PolyLang.pi_point_witness pi) =
      PolyLang.pi_depth pi ->
    length current = (env_dim + PolyLang.pi_depth pi)%nat ->
    PolyLang.current_transformation_of pi current =
    PolyLang.current_transformation_at env_dim pi.
Proof.
  intros pi current env_dim Hwitness Hlen.
  unfold PolyLang.current_transformation_of.
  rewrite (current_env_dim_of_eq (PolyLang.pi_point_witness pi) current env_dim).
  - reflexivity.
  - rewrite Hwitness. exact Hlen.
Qed.


Lemma eqdom_pinstr_implies_current_transformation_at_eq:
  forall env_dim pi1 pi2,
    PolyLang.eqdom_pinstr pi1 pi2 ->
    PolyLang.current_transformation_at env_dim pi1 =
    PolyLang.current_transformation_at env_dim pi2.
Proof.
  intros env_dim pi1 pi2 Heq.
  destruct Heq as (_ & _ & _ & Hwit & Htf & _ & _ & _).
  unfold PolyLang.current_transformation_at.
  rewrite Hwit, Htf.
  reflexivity.
Qed.





Lemma exact_listzzs_cols_current_transformation_at :
  forall (env: list ident) (pi: PolyLang.PolyInstr),
    exact_listzzs_cols
      (length env + witness_base_point_dim (PolyLang.pi_point_witness pi))%nat
      (PolyLang.pi_transformation pi) ->
    exact_listzzs_cols
      (length env + witness_current_point_dim (PolyLang.pi_point_witness pi))%nat
      (PolyLang.current_transformation_at (length env) pi).
Proof.
  intros env pi Htf.
  eapply PolyLang.exact_listzzs_cols_current_transformation_at.
  exact Htf.
Qed.

Lemma exact_listzzs_cols_current_access_transformation_at :
  forall (env: list ident) (pi: PolyLang.PolyInstr),
    exact_listzzs_cols
      (length env + witness_base_point_dim (PolyLang.pi_point_witness pi))%nat
      (PolyLang.pi_access_transformation pi) ->
    exact_listzzs_cols
      (length env + witness_current_point_dim (PolyLang.pi_point_witness pi))%nat
      (PolyLang.current_access_transformation_at (length env) pi).
Proof.
  intros env pi Htf.
  eapply PolyLang.exact_listzzs_cols_current_access_transformation_at.
  exact Htf.
Qed.

Lemma current_transformation_at_preserve_length :
  forall (env: list ident) (pi: PolyLang.PolyInstr),
    length (PolyLang.current_transformation_at (length env) pi) =
    length (PolyLang.pi_transformation pi).
Proof.
  intros env pi.
  eapply PolyLang.current_transformation_at_preserve_length.
Qed.


Lemma wf_pinstr_tiling_implies_wf_pinstr_ext_tiling_at :
  forall env vars pi pi',
    PolyLang.wf_pinstr_tiling env vars pi ->
    PolyLang.wf_pinstr_tiling env vars pi' ->
    PolyLang.eqdom_pinstr pi pi' ->
    PolyLang.wf_pinstr_ext_tiling env
      (compose_pinstr_ext_at (length env) pi pi').
Proof.
  intros env vars pi pi' Hwf1 Hwf2 Heqdom.
  unfold PolyLang.wf_pinstr_tiling in *.
  destruct Hwf1 as [Hwf1 Heq1].
  destruct Hwf2 as [Hwf2 Heq2].
  unfold PolyLang.wf_pinstr_ext_tiling.
  split.
  - unfold PolyLang.wf_pinstr_ext.
    unfold compose_pinstr_ext_at; simpl.
    destruct Hwf1 as [Hwitness1 Hwf1].
    destruct Hwf1 as [Hcols_le Hwf1].
    destruct Hwf1 as [Hpoly_nrl Hwf1].
    destruct Hwf1 as [Hsched_nrl Hwf1].
    destruct Hwf1 as [Hpoly_exact Hwf1].
    destruct Hwf1 as [Htf_exact Hwf1].
    destruct Hwf1 as [Hacc_tf_exact Hwf1].
    destruct Hwf1 as [Hsched1_exact Hwf1].
    destruct Hwf1 as [Hw1 Hr1].
    destruct Hwf2 as [_ Hwf2].
    destruct Hwf2 as [_ Hwf2].
    destruct Hwf2 as [_ Hwf2].
    destruct Hwf2 as [_ Hwf2].
    destruct Hwf2 as [_ Hwf2].
    destruct Hwf2 as [_ Hwf2].
    destruct Hwf2 as [_ Hwf2].
    destruct Hwf2 as [Hsched2_exact _].
    destruct Heqdom as [Hdepth _].
    rewrite <- Hdepth in Hsched2_exact.
    repeat split.
    + exact Hwitness1.
    + exact Hpoly_exact.
    + rewrite <- Hwitness1.
      exact (exact_listzzs_cols_current_transformation_at env pi Htf_exact).
    + rewrite <- Hwitness1.
      exact (exact_listzzs_cols_current_access_transformation_at env pi Hacc_tf_exact).
    + exact Hsched1_exact.
    + exact Hsched2_exact.
    + induction Hw1 as [|[arrid waccess_func] rest Hcols HForall IH]; constructor.
      * simpl in *.
        rewrite current_transformation_at_preserve_length.
        exact Hcols.
      * exact IH.
    + induction Hr1 as [|[arrid raccess_func] rest Hcols HForall IH]; constructor.
      * simpl in *.
        rewrite current_transformation_at_preserve_length.
        exact Hcols.
      * exact IH.
  - unfold compose_pinstr_ext_at; simpl.
    unfold PolyLang.current_transformation_at, PolyLang.current_access_transformation_at.
    rewrite Heq1.
    reflexivity.
Qed.

Lemma wf_pinstr_ext_tiling_implies_waccess_matches :
  forall env pi_ext,
    PolyLang.wf_pinstr_ext_tiling env pi_ext ->
    Forall
      (access_matches_tf (PolyLang.pi_access_transformation_ext pi_ext))
      (PolyLang.pi_waccess_ext pi_ext).
Proof.
  intros env pi_ext Hwf.
  destruct Hwf as [Hwf Heq].
  unfold PolyLang.wf_pinstr_ext in Hwf.
  destruct Hwf as [_ [_ [_ [_ [_ [_ [Hw _]]]]]]].
  unfold access_matches_tf.
  rewrite <- Heq.
  exact Hw.
Qed.

Lemma wf_pinstr_ext_tiling_implies_raccess_matches :
  forall env pi_ext,
    PolyLang.wf_pinstr_ext_tiling env pi_ext ->
    Forall
      (access_matches_tf (PolyLang.pi_access_transformation_ext pi_ext))
      (PolyLang.pi_raccess_ext pi_ext).
Proof.
  intros env pi_ext Hwf.
  destruct Hwf as [Hwf Heq].
  unfold PolyLang.wf_pinstr_ext in Hwf.
  destruct Hwf as [_ [_ [_ [_ [_ [_ [_ Hr]]]]]]].
  unfold access_matches_tf.
  rewrite <- Heq.
  exact Hr.
Qed.

Lemma expand_ip_instr_eq_current_tf_at:
  forall env vars envv nth pi ipl ip,
    PolyLang.wf_pinstr env vars pi ->
    length env = length envv ->
    PolyLang.flatten_instr_nth envv nth pi ipl ->
    In ip ipl ->
    PolyLang.ip_transformation ip =
      PolyLang.current_transformation_at (length env) pi.
Proof.
  intros env vars envv nth pi ipl ip Hwf Henvlen Hflat Hin.
  destruct Hwf as [Hwitness _].
  destruct Hflat as [_ [HBEL _]].
  destruct (HBEL ip) as [Hfwd _].
  destruct (Hfwd Hin) as [_ [Hbel [_ Hlen]]].
  destruct Hbel as [_ [Htf _]].
  rewrite Htf.
  rewrite Henvlen.
  eapply current_transformation_of_eq_at; eauto.
Qed.




Lemma in_compose_ipl_ext_at_inv:
  forall access_tf ip_ext ipl1 ipl2,
    In ip_ext (compose_ipl_ext_at access_tf ipl1 ipl2) ->
    exists ip1 ip2,
      In ip1 ipl1 /\
      In ip2 ipl2 /\
      ip_ext = compose_ip_ext_at access_tf ip1 ip2.
Proof.
  intros access_tf ip_ext ipl1.
  revert access_tf ip_ext.
  induction ipl1 as [|ip1 ipl1 IH]; intros acc_tf ip_ext ipl2 Hip.
  - destruct ipl2; simpl in Hip; contradiction.
  - destruct ipl2 as [|ip2 ipl2].
    * simpl in Hip. contradiction.
    * simpl in Hip.
      refine (
        match Hip with
        | or_introl Heq =>
            ex_intro _ ip1
              (ex_intro _ ip2
                (conj (or_introl eq_refl)
                  (conj (or_introl eq_refl) (eq_sym Heq))))
        | or_intror Hin =>
            match IH acc_tf ip_ext ipl2 Hin with
            | ex_intro _ ip1'
                (ex_intro _ ip2' (conj Hin1 (conj Hin2 Heq'))) =>
                ex_intro _ ip1'
                  (ex_intro _ ip2'
                    (conj (or_intror Hin1) (conj (or_intror Hin2) Heq')))
            end
        end).
Qed.


Lemma nth_error_compose_ipl_ext_at_inv_local:
  forall n access_tf ipl1 ipl2 ip_ext,
    nth_error (compose_ipl_ext_at access_tf ipl1 ipl2) n = Some ip_ext ->
    exists ip1 ip2,
      nth_error ipl1 n = Some ip1 /\
      nth_error ipl2 n = Some ip2 /\
      ip_ext = compose_ip_ext_at access_tf ip1 ip2.
Proof.
  induction n; intros acc_tf ipl1 ipl2 ip_ext Hnth.
  - destruct ipl1 as [|ip1 ipl1']; destruct ipl2 as [|ip2 ipl2'];
      simpl in Hnth; try discriminate.
    inversion Hnth; subst.
    exists ip1. exists ip2. repeat split; reflexivity.
  - destruct ipl1 as [|ip1 ipl1']; destruct ipl2 as [|ip2 ipl2'];
      simpl in Hnth; try discriminate.
    eapply IHn in Hnth.
    destruct Hnth as (ip1' & ip2' & Hnth1 & Hnth2 & Heq).
    exists ip1'. exists ip2'. repeat split; eauto.
Qed.


Lemma nth_error_compose_ipl_ext_at:
  forall n access_tf ipl1 ipl2 ip1 ip2,
    nth_error ipl1 n = Some ip1 ->
    nth_error ipl2 n = Some ip2 ->
    nth_error (compose_ipl_ext_at access_tf ipl1 ipl2) n =
      Some (compose_ip_ext_at access_tf ip1 ip2).
Proof.
  induction n; intros acc_tf ipl1 ipl2 ip1 ip2 Hnth1 Hnth2.
  - destruct ipl1 as [|ip1' ipl1']; destruct ipl2 as [|ip2' ipl2'];
      simpl in *; try discriminate.
    inversion Hnth1; inversion Hnth2; subst.
    reflexivity.
  - destruct ipl1 as [|ip1' ipl1']; destruct ipl2 as [|ip2' ipl2'];
      simpl in *; try discriminate.
    eapply IHn; eauto.
Qed.


Lemma old_of_compose_list_at_ok:
  forall access_tf ipl1 ipl2 ipl_ext,
  length ipl1 = length ipl2 ->
  compose_ipl_ext_at access_tf ipl1 ipl2 = ipl_ext ->
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
    rewrite map_cons.
    f_equal.
    {
      eapply old_of_compose_at_ok; trivial.
    }
    {
      eapply IHipl1; eauto.
    }
  }
Qed.


Lemma new_of_compose_list_at_ok:
  forall access_tf ipl1 ipl2 ipl_ext,
  rel_list PolyLang.eq_except_sched ipl1 ipl2 ->
  compose_ipl_ext_at access_tf ipl1 ipl2 = ipl_ext ->
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
      eapply new_of_compose_at_ok with (ip1:=a); firstorder.
    }
    {
      eapply IHipl1; eauto.
    }
  }
Qed.



Lemma compose_pinstrs_ext_at_app_singleton:
  forall env_dim pil1 pil2 pi1 pi2,
    length pil1 = length pil2 ->
    compose_pinstrs_ext_at env_dim (pil1 ++ [pi1]) (pil2 ++ [pi2]) =
    compose_pinstrs_ext_at env_dim pil1 pil2 ++
    [compose_pinstr_ext_at env_dim pi1 pi2].
Proof.
  induction pil1.
  {
    intros; simpls.
    symmetry in H. rewrite length_zero_iff_nil in H. subst; trivial.
  }
  {
    intros; simpls.
    destruct pil2 eqn:Hpil2; tryfalse. simpls. inv H.
    rewrite IHpil1; eauto.
  }
Qed.







(** * Finiteness and pairwise access-dependence exclusion *)

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
  eapply isBottom_integer_fallback_correct in Hisbot. simpls.
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
    (
      exact_listzzs_cols dom_dim1 tf1
    ) ->
    (
      exact_listzzs_cols dom_dim2 tf2
    ) ->
    access_matches_tf tf1 a1 ->
    access_matches_tf tf2 a2 ->
    in_poly (p1 ++ p2) pol_dom = true ->
    Exists (fun pol => in_poly (p1 ++ p2) pol = true) pols_old_lt -> 
    Exists (fun pol => in_poly (p1 ++ p2) pol = true) pols_new_ge ->
    cell_neq (exact_cell a1 (affine_product tf1 p1)) (exact_cell a2 (affine_product tf2 p2)).
Proof.
  intros. intros res Hval Hres Hlen1 Hlen2 Hwf1 Hwf2 Hacc1 Hacc2 Hin Hlt Hge.
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
    - change
        (exact_listzzs_cols
           (length p1)
           (snd (compose_access_function_at (length p1) (id2, func1) tf1))).
      eapply compose_access_function_at_exact_cols; eauto.
    - change
        ((affine_product
            (snd (compose_access_function_at (length p1) (id2, func1) tf1))
            p1)
         =v=
         (affine_product
            (snd (compose_access_function_at (length p2) (id2, func2) tf2))
            p2)).
      rewrite
        (compose_access_function_at_correct
           (length p1) (id2, func1) tf1 p1); eauto.
      rewrite
        (compose_access_function_at_correct
           (length p2) (id2, func2) tf2 p2); eauto.
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
    (
      exact_listzzs_cols dom_dim1 tf1
    ) ->
    (
      exact_listzzs_cols dom_dim2 tf2
    ) ->
    access_matches_tf tf1 wa ->
    Forall (access_matches_tf tf2) ral ->
    in_poly (p1 ++ p2) pol_dom = true ->
    Exists (fun pol => in_poly (p1 ++ p2) pol = true) pols_old_lt -> 
    Exists (fun pol => in_poly (p1 ++ p2) pol = true) pols_new_ge ->
    Forall (fun ra => cell_neq (exact_cell wa (affine_product tf1 p1)) (exact_cell ra (affine_product tf2 p2))) ral.
Proof.
  induction ral.
  {
    intros. intros res Hval Hres Hlen1 Hlen2 Hwf1 Hwf2 Hacc1 Haccs Hin Hlt Hge.
    eapply Forall_nil; trivial.
  }
  {
    intros. intros res Hval Hres Hlen1 Hlen2 Hwf1 Hwf2 Hacc1 Haccs Hin Hlt Hge.
    simpls.
    inversion Haccs; subst.
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
  (
    exact_listzzs_cols dom_dim1 tf1
  ) ->
  (
    exact_listzzs_cols dom_dim2 tf2
  ) ->
  Forall (access_matches_tf tf1) al1 ->
  Forall (access_matches_tf tf2) al2 ->
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
    intros. intros res Hval Hres Hlen1 Hlen2 Hwf1 Hwf2 Hacc1 Hacc2 Hin Hlt Hge.
    eapply Forall_nil; trivial.
  }
  {
    intros. intros res Hval Hres Hlen1 Hlen2 Hwf1 Hwf2 Hacc1 Hacc2 Hin Hlt Hge.
    simpls.
    inversion Hacc1; subst.
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
      (exact_cell w1 (affine_product (PolyLang.ip_access_transformation_ext ip1) (PolyLang.ip_index_ext ip1))) 
      (exact_cell w2 (affine_product (PolyLang.ip_access_transformation_ext ip2) (PolyLang.ip_index_ext ip2)))
    ) wl2
  ) wl1.

Definition no_wr_collision (wl1 rl2: list AccessFunction) (ip1 ip2: PolyLang.InstrPoint_ext) := 
  Forall ( fun r2 => 
    Forall (
      fun w1 =>
      cell_neq (exact_cell w1 (affine_product (PolyLang.ip_access_transformation_ext ip1) (PolyLang.ip_index_ext ip1)))
               (exact_cell r2 (affine_product (PolyLang.ip_access_transformation_ext ip2) (PolyLang.ip_index_ext ip2)))
    ) wl1 
  ) rl2.

Definition no_write_collision (wl1 wl2 rl1 rl2: list AccessFunction) (ip1 ip2: PolyLang.InstrPoint_ext) := 
  no_ww_collision wl1 wl2 ip1 ip2 /\ 
  no_wr_collision wl1 rl2 ip1 ip2 /\ 
  no_wr_collision wl2 rl1 ip2 ip1.

Local Lemma lift_access_noncollision_to_cells:
  forall p1 p2 cells1 cells2 accesses1 accesses2,
    valid_access_cells p1 cells1 accesses1 ->
    valid_access_cells p2 cells2 accesses2 ->
    Forall
      (fun access2 =>
        Forall
          (fun access1 =>
            cell_neq (exact_cell access1 p1) (exact_cell access2 p2))
          accesses1)
      accesses2 ->
    Forall (fun cell2 => Forall (fun cell1 => cell_neq cell1 cell2) cells1) cells2.
Proof.
  intros p1 p2 cells1 cells2 accesses1 accesses2
    Hvalid1 Hvalid2 Hnoncollision.
  eapply Forall_forall. intros cell2 Hcell2.
  eapply Forall_forall. intros cell1 Hcell1.
  destruct (Hvalid1 cell1 Hcell1) as
    (access1 & Haccess1 & Haccess1_cell1).
  destruct (Hvalid2 cell2 Hcell2) as
    (access2 & Haccess2 & Haccess2_cell2).
  eapply Forall_forall in Hnoncollision; [|exact Haccess2].
  eapply Forall_forall in Hnoncollision; [|exact Haccess1].
  eapply cell_neq_proper with (x:=cell1) (x0:=cell2) in Hnoncollision.
  - exact Hnoncollision.
  - eapply cell_eq_symm. exact Haccess1_cell1.
  - eapply cell_eq_symm. exact Haccess2_cell2.
Qed.

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
  intros until rcs2.
  intros Hvalid1 Hvalid2 [Hww [Hwr Hrw]] Halias [Hsema1 Hsema2].
  pose proof (Hvalid1 p1 st1 st2 wcs1 rcs1 Hsema1) as [Hwrites1 Hreads1].
  pose proof (Hvalid2 p2 st2 st3 wcs2 rcs2 Hsema2) as [Hwrites2 Hreads2].
  eapply Instr.bc_condition_implie_permutbility.
  - exact Halias.
  - split.
    + exact Hsema1.
    + exact Hsema2.
  - repeat split.
    + exact (lift_access_noncollision_to_cells
        p1 p2 wcs1 wcs2 wl1 wl2 Hwrites1 Hwrites2 Hww).
    + exact (lift_access_noncollision_to_cells
        p1 p2 wcs1 rcs2 wl1 rl2 Hwrites1 Hreads2 Hwr).
    + exact (lift_access_noncollision_to_cells
        p1 p2 rcs1 wcs2 rl1 wl2 Hreads1 Hwrites2 Hrw).
Qed.

Lemma no_write_collision_implies_permutable:
  forall ip1 ip2 wl1 wl2 rl1 rl2,
    no_write_collision wl1 wl2 rl1 rl2 ip1 ip2 ->
    PolyLang.ip_access_transformation_ext ip1 = PolyLang.ip_transformation_ext ip1 ->
    PolyLang.ip_access_transformation_ext ip2 = PolyLang.ip_transformation_ext ip2 ->
    Instr.valid_access_function wl1 rl1 (ip1.(PolyLang.ip_instruction_ext)) ->
    Instr.valid_access_function wl2 rl2 (ip2.(PolyLang.ip_instruction_ext)) ->
    PolyLang.Permutable_ext ip1 ip2.
Proof.
  intros until rl2. intros H Htf1eq Htf2eq Hwf1 Hwf2.
  destruct ip1 eqn:Hip1; destruct ip2 eqn:Hip2. 
  unfold no_write_collision in H.
  unfold no_wr_collision in H.
  unfold no_ww_collision in H. 
  unfold PolyLang.Permutable_ext. unfold PolyLang.Permutable. 
  unfold PolyLang.old_of_ext.
  simpls. 
  rewrite Htf1eq in H.
  rewrite Htf2eq in H.

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
      eapply (no_w_collision_implies_permutability
                ip_instruction_ext ip_instruction_ext0
                (affine_product ip_transformation_ext ip_index_ext)
                (affine_product ip_transformation_ext0 ip_index_ext0)
                st1 _ _ wl1 wl2 rl1 rl2 wcs1 rcs1 wcs2 rcs2); eauto.
      assert (HWW' :
        Forall
          (fun w2 : AccessFunction =>
             Forall
               (fun w1 : AccessFunction =>
                  cell_neq
                    (exact_cell w1 (affine_product ip_transformation_ext ip_index_ext))
                    (exact_cell w2 (affine_product ip_transformation_ext0 ip_index_ext0)))
               wl1)
          wl2).
      {
        clear - WW.
        eapply Forall_forall. intros w2 Hw2.
        eapply Forall_forall. intros w1 Hw1.
        eapply Forall_forall in WW; eauto.
        eapply Forall_forall in WW; eauto.
      }
      assert (HRW' :
        Forall
          (fun w2 : AccessFunction =>
             Forall
               (fun r1 : AccessFunction =>
                  cell_neq
                    (exact_cell r1 (affine_product ip_transformation_ext ip_index_ext))
                    (exact_cell w2 (affine_product ip_transformation_ext0 ip_index_ext0)))
               rl1)
          wl2).
      {
        clear - RW.
        eapply Forall_forall. intros w2 Hw2.
        eapply Forall_forall. intros r1 Hr1.
        eapply Forall_forall in RW; eauto.
        eapply Forall_forall in RW; eauto.
        eapply cell_neq_symm; exact RW.
      }
      exact (conj HWW' (conj WR HRW')).
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
      destruct H as (WW & WR & RW).
      eapply (no_w_collision_implies_permutability
                ip_instruction_ext0 ip_instruction_ext
                (affine_product ip_transformation_ext0 ip_index_ext0)
                (affine_product ip_transformation_ext ip_index_ext)
                st1 _ _ wl2 wl1 rl2 rl1 wcs1 rcs1 wcs2 rcs2); eauto.
      assert (HWW' :
        Forall
          (fun w2 : AccessFunction =>
             Forall
               (fun w1 : AccessFunction =>
                  cell_neq
                    (exact_cell w1 (affine_product ip_transformation_ext0 ip_index_ext0))
                    (exact_cell w2 (affine_product ip_transformation_ext ip_index_ext)))
               wl2)
          wl1).
      {
        clear - WW.
        eapply Forall_forall. intros w2 Hw2.
        eapply Forall_forall. intros w1 Hw1.
        eapply Forall_forall in WW; eauto.
        eapply Forall_forall in WW; eauto.
        eapply cell_neq_symm; exact WW.
      }
      assert (HWR' :
        Forall
          (fun w2 : AccessFunction =>
             Forall
               (fun r1 : AccessFunction =>
                  cell_neq
                    (exact_cell r1 (affine_product ip_transformation_ext0 ip_index_ext0))
                    (exact_cell w2 (affine_product ip_transformation_ext ip_index_ext)))
               rl2)
          wl1).
      {
        clear - WR.
        eapply Forall_forall. intros w2 Hw2.
        eapply Forall_forall. intros r1 Hr1.
        eapply Forall_forall in WR; eauto.
        eapply Forall_forall in WR; eauto.
        eapply cell_neq_symm; exact WR.
      }
      exact (conj HWW' (conj RW HWR')).
    } 
    destruct H2 as (st2'' & st3' & Hsem1 & Hsem2 & Heq).
    exists st2'' st3'. splits; try econs; eauto.
Qed.


Local Lemma wf_pinstr_ext_tiling_access_transformation_cols:
  forall env pi_ext,
    PolyLang.wf_pinstr_ext_tiling env pi_ext ->
    exact_listzzs_cols
      (length env + PolyLang.pi_depth_ext pi_ext)
      (PolyLang.pi_access_transformation_ext pi_ext).
Proof.
  intros env pi_ext [Hwf _].
  unfold PolyLang.wf_pinstr_ext in Hwf.
  destruct Hwf as (_ & _ & _ & Hcols & _).
  exact Hcols.
Qed.

Local Lemma transpose_access_noncollision:
  forall accesses1 accesses2 point1 point2,
    Forall
      (fun access1 =>
        Forall
          (fun access2 =>
            cell_neq
              (exact_cell access1 point1)
              (exact_cell access2 point2))
          accesses2)
      accesses1 ->
    Forall
      (fun access2 =>
        Forall
          (fun access1 =>
            cell_neq
              (exact_cell access1 point1)
              (exact_cell access2 point2))
          accesses1)
      accesses2.
Proof.
  intros accesses1 accesses2 point1 point2 Hnoncollision.
  eapply Forall_forall. intros access2 Haccess2.
  eapply Forall_forall. intros access1 Haccess1.
  eapply Forall_forall in Hnoncollision; [|exact Haccess1].
  eapply Forall_forall in Hnoncollision; [|exact Haccess2].
  exact Hnoncollision.
Qed.

Local Lemma symmetrize_access_noncollision:
  forall accesses1 accesses2 point1 point2,
    Forall
      (fun access1 =>
        Forall
          (fun access2 =>
            cell_neq
              (exact_cell access1 point1)
              (exact_cell access2 point2))
          accesses2)
      accesses1 ->
    Forall
      (fun access1 =>
        Forall
          (fun access2 =>
            cell_neq
              (exact_cell access2 point2)
              (exact_cell access1 point1))
          accesses2)
      accesses1.
Proof.
  intros accesses1 accesses2 point1 point2 Hnoncollision.
  eapply Forall_forall. intros access1 Haccess1.
  eapply Forall_forall. intros access2 Haccess2.
  eapply Forall_forall in Hnoncollision; [|exact Haccess1].
  eapply Forall_forall in Hnoncollision; [|exact Haccess2].
  eapply cell_neq_symm. exact Hnoncollision.
Qed.

Lemma forallb_imp_true_forall :
  forall {A} (f: A -> imp bool) xs,
    mayReturn (forallb_imp f xs) true ->
    forall x, In x xs -> mayReturn (f x) true.
Proof.
  intros A f xs.
  induction xs as [|a xs IH]; intros Hcheck x Hin.
  - inversion Hin.
  - simpl in Hcheck.
    bind_imp_destruct Hcheck head_ok Hhead.
    destruct head_ok.
    + destruct Hin as [Heq | Hin].
      * subst x. exact Hhead.
      * eapply IH; eauto.
    + apply mayReturn_pure in Hcheck.
      discriminate.
Qed.

Local Definition access_pair_checker :=
  AccessFunction -> AccessFunction ->
  AffineFunction -> AffineFunction ->
  polyhedron -> list polyhedron -> list polyhedron ->
  nat -> nat -> imp bool.

Local Definition access_pair_checker_sound
    (checker: access_pair_checker) : Prop :=
  forall pols_old_lt pols_new_ge a1 a2 tf1 tf2 p1 p2 pol_dom
         dom_dim1 dom_dim2,
    WHEN res <-
      checker a1 a2 tf1 tf2 pol_dom
        pols_old_lt pols_new_ge dom_dim1 dom_dim2
    THEN
    res = true ->
    length p1 = dom_dim1 ->
    length p2 = dom_dim2 ->
    exact_listzzs_cols dom_dim1 tf1 ->
    exact_listzzs_cols dom_dim2 tf2 ->
    access_matches_tf tf1 a1 ->
    access_matches_tf tf2 a2 ->
    in_poly (p1 ++ p2) pol_dom = true ->
    Exists (fun pol => in_poly (p1 ++ p2) pol = true) pols_old_lt ->
    Exists (fun pol => in_poly (p1 ++ p2) pol = true) pols_new_ge ->
    cell_neq
      (exact_cell a1 (affine_product tf1 p1))
      (exact_cell a2 (affine_product tf2 p2)).

Local Lemma validate_two_accesses_checker_sound :
  access_pair_checker_sound validate_two_accesses.
Proof.
  exact validate_two_accesses_implies_permut_no_collision.
Qed.

Local Lemma validated_access_pair_lists_imply_noncollision:
  forall checker,
    access_pair_checker_sound checker ->
    forall accesses1 accesses2 tf1 tf2 p1 p2 pol_dom
           pols_old_lt pols_new_ge dom_dim1 dom_dim2,
      mayReturn
        (forallb_imp
          (fun access1 =>
             forallb_imp
               (fun access2 =>
                  checker access1 access2 tf1 tf2 pol_dom
                    pols_old_lt pols_new_ge dom_dim1 dom_dim2)
               accesses2)
          accesses1)
        true ->
      length p1 = dom_dim1 ->
      length p2 = dom_dim2 ->
      exact_listzzs_cols dom_dim1 tf1 ->
      exact_listzzs_cols dom_dim2 tf2 ->
      Forall (access_matches_tf tf1) accesses1 ->
      Forall (access_matches_tf tf2) accesses2 ->
      in_poly (p1 ++ p2) pol_dom = true ->
      Exists (fun pol => in_poly (p1 ++ p2) pol = true) pols_old_lt ->
      Exists (fun pol => in_poly (p1 ++ p2) pol = true) pols_new_ge ->
      Forall
        (fun access1 =>
           Forall
             (fun access2 =>
                cell_neq
                  (exact_cell access1 (affine_product tf1 p1))
                  (exact_cell access2 (affine_product tf2 p2)))
             accesses2)
        accesses1.
Proof.
  intros checker Hchecker accesses1 accesses2 tf1 tf2 p1 p2 pol_dom
    pols_old_lt pols_new_ge dom_dim1 dom_dim2 Hchecks
    Hlen1 Hlen2 Htf1 Htf2 Haccesses1 Haccesses2 Hdom Hlt Hge.
  apply Forall_forall. intros access1 Haccess1.
  apply Forall_forall. intros access2 Haccess2.
  pose proof
    (forallb_imp_true_forall _ _ Hchecks access1 Haccess1)
    as Hchecks2.
  pose proof
    (forallb_imp_true_forall _ _ Hchecks2 access2 Haccess2)
    as Hcheck.
  eapply (Hchecker pols_old_lt pols_new_ge access1 access2
    tf1 tf2 p1 p2 pol_dom dom_dim1 dom_dim2 true Hcheck eq_refl).
  - exact Hlen1.
  - exact Hlen2.
  - exact Htf1.
  - exact Htf2.
  - rewrite Forall_forall in Haccesses1.
    exact (Haccesses1 access1 Haccess1).
  - rewrite Forall_forall in Haccesses2.
    exact (Haccesses2 access2 Haccess2).
  - exact Hdom.
  - exact Hlt.
  - exact Hge.
Qed.

Local Lemma validated_access_checks_imply_no_write_collision:
  forall checker,
    access_pair_checker_sound checker ->
    forall pi1_ext pi2_ext env nth1 nth2 envv ipl1_ext ipl2_ext
         in_domain_poly env_eq_in_domain order_guards bad_guards ip1 ip2,
    mayReturn
      (poly_product
        pi1_ext.(PolyLang.pi_poly_ext)
        pi2_ext.(PolyLang.pi_poly_ext)
        (length env + pi1_ext.(PolyLang.pi_depth_ext))
        (length env + pi2_ext.(PolyLang.pi_depth_ext)))
      in_domain_poly ->
    mayReturn
      (poly_inter
        (make_poly_env_eq
          (length env)
          pi1_ext.(PolyLang.pi_depth_ext)
          pi2_ext.(PolyLang.pi_depth_ext))
        in_domain_poly)
      env_eq_in_domain ->
    mayReturn
      (forallb_imp
        (fun waccess1 => forallb_imp (fun waccess2 =>
          checker
            waccess1 waccess2
            pi1_ext.(PolyLang.pi_access_transformation_ext)
            pi2_ext.(PolyLang.pi_access_transformation_ext)
            env_eq_in_domain order_guards bad_guards
            (length env + pi1_ext.(PolyLang.pi_depth_ext))
            (length env + pi2_ext.(PolyLang.pi_depth_ext)))
          pi2_ext.(PolyLang.pi_waccess_ext))
        pi1_ext.(PolyLang.pi_waccess_ext))
      true ->
    mayReturn
      (forallb_imp
        (fun waccess1 => forallb_imp (fun raccess2 =>
          checker
            waccess1 raccess2
            pi1_ext.(PolyLang.pi_access_transformation_ext)
            pi2_ext.(PolyLang.pi_access_transformation_ext)
            env_eq_in_domain order_guards bad_guards
            (length env + pi1_ext.(PolyLang.pi_depth_ext))
            (length env + pi2_ext.(PolyLang.pi_depth_ext)))
          pi2_ext.(PolyLang.pi_raccess_ext))
        pi1_ext.(PolyLang.pi_waccess_ext))
      true ->
    mayReturn
      (forallb_imp
        (fun raccess1 => forallb_imp (fun waccess2 =>
          checker
            raccess1 waccess2
            pi1_ext.(PolyLang.pi_access_transformation_ext)
            pi2_ext.(PolyLang.pi_access_transformation_ext)
            env_eq_in_domain order_guards bad_guards
            (length env + pi1_ext.(PolyLang.pi_depth_ext))
            (length env + pi2_ext.(PolyLang.pi_depth_ext)))
          pi2_ext.(PolyLang.pi_waccess_ext))
        pi1_ext.(PolyLang.pi_raccess_ext))
      true ->
    PolyLang.wf_pinstr_ext_tiling env pi1_ext ->
    PolyLang.wf_pinstr_ext_tiling env pi2_ext ->
    length env = length envv ->
    PolyLang.flatten_instr_nth_ext envv nth1 pi1_ext ipl1_ext ->
    PolyLang.flatten_instr_nth_ext envv nth2 pi2_ext ipl2_ext ->
    In ip1 ipl1_ext ->
    In ip2 ipl2_ext ->
    Exists
      (fun pol =>
        in_poly
          (PolyLang.ip_index_ext ip1 ++ PolyLang.ip_index_ext ip2)
          pol = true)
      order_guards ->
    Exists
      (fun pol =>
        in_poly
          (PolyLang.ip_index_ext ip1 ++ PolyLang.ip_index_ext ip2)
          pol = true)
      bad_guards ->
    no_write_collision
      pi1_ext.(PolyLang.pi_waccess_ext)
      pi2_ext.(PolyLang.pi_waccess_ext)
      pi1_ext.(PolyLang.pi_raccess_ext)
      pi2_ext.(PolyLang.pi_raccess_ext)
      ip1 ip2.
Proof.
  intros checker Hchecker
    pi1_ext pi2_ext env nth1 nth2 envv ipl1_ext ipl2_ext
    in_domain_poly env_eq_in_domain order_guards bad_guards ip1 ip2
    Hdomain Henv Hww Hwr Hrw Hwf1 Hwf2 Henvlen
    Hext1 Hext2 Hip1 Hip2 Horder Hbad.
  assert (Hidx1 :
    length (PolyLang.ip_index_ext ip1) =
      (length env + PolyLang.pi_depth_ext pi1_ext)%nat).
  {
    rewrite Henvlen.
    eapply PolyLang.ip_index_size_eq_pi_dom_size_ext; eauto.
  }
  assert (Hidx2 :
    length (PolyLang.ip_index_ext ip2) =
      (length env + PolyLang.pi_depth_ext pi2_ext)%nat).
  {
    rewrite Henvlen.
    eapply PolyLang.ip_index_size_eq_pi_dom_size_ext; eauto.
  }
  assert (HTF1 :
    exact_listzzs_cols
      (length env + PolyLang.pi_depth_ext pi1_ext)
      (PolyLang.pi_access_transformation_ext pi1_ext)).
  { eapply wf_pinstr_ext_tiling_access_transformation_cols; exact Hwf1. }
  assert (HTF2 :
    exact_listzzs_cols
      (length env + PolyLang.pi_depth_ext pi2_ext)
      (PolyLang.pi_access_transformation_ext pi2_ext)).
  { eapply wf_pinstr_ext_tiling_access_transformation_cols; exact Hwf2. }
  assert (HTFIP1 :
    PolyLang.ip_access_transformation_ext ip1 =
      PolyLang.pi_access_transformation_ext pi1_ext).
  { eapply PolyLang.expand_ip_instr_eq_pi_access_tf_ext; eauto. }
  assert (HTFIP2 :
    PolyLang.ip_access_transformation_ext ip2 =
      PolyLang.pi_access_transformation_ext pi2_ext).
  { eapply PolyLang.expand_ip_instr_eq_pi_access_tf_ext; eauto. }
  assert (HW1 :
    Forall
      (access_matches_tf (PolyLang.pi_access_transformation_ext pi1_ext))
      (PolyLang.pi_waccess_ext pi1_ext)).
  { eapply wf_pinstr_ext_tiling_implies_waccess_matches; eauto. }
  assert (HR1 :
    Forall
      (access_matches_tf (PolyLang.pi_access_transformation_ext pi1_ext))
      (PolyLang.pi_raccess_ext pi1_ext)).
  { eapply wf_pinstr_ext_tiling_implies_raccess_matches; eauto. }
  assert (HW2 :
    Forall
      (access_matches_tf (PolyLang.pi_access_transformation_ext pi2_ext))
      (PolyLang.pi_waccess_ext pi2_ext)).
  { eapply wf_pinstr_ext_tiling_implies_waccess_matches; eauto. }
  assert (HR2 :
    Forall
      (access_matches_tf (PolyLang.pi_access_transformation_ext pi2_ext))
      (PolyLang.pi_raccess_ext pi2_ext)).
  { eapply wf_pinstr_ext_tiling_implies_raccess_matches; eauto. }
  assert (Hbase :
    in_poly
      (PolyLang.ip_index_ext ip1 ++ PolyLang.ip_index_ext ip2)
      env_eq_in_domain = true).
  {
    eapply poly_inter_def
      with (p := PolyLang.ip_index_ext ip1 ++ PolyLang.ip_index_ext ip2)
      in Henv.
    rewrite poly_inter_pure_def in Henv.
    rewrite Henv.
    apply andb_true_intro; split.
    - rewrite Henvlen.
      eapply PolyLang.expand_same_env_implies_in_eq_env_pol_ext; eauto.
    - rewrite Henvlen in Hdomain.
      eapply PolyLang.expand_same_env_implies_in_domain_product_pol;
        eauto using PolyLang.wf_pinstr_ext_tiling_implies_wf_pinstr_ext.
  }
  pose proof
    (validated_access_pair_lists_imply_noncollision checker Hchecker
       (PolyLang.pi_waccess_ext pi1_ext)
       (PolyLang.pi_waccess_ext pi2_ext)
       (PolyLang.pi_access_transformation_ext pi1_ext)
       (PolyLang.pi_access_transformation_ext pi2_ext)
       (PolyLang.ip_index_ext ip1) (PolyLang.ip_index_ext ip2)
       env_eq_in_domain order_guards bad_guards
       (length env + PolyLang.pi_depth_ext pi1_ext)
       (length env + PolyLang.pi_depth_ext pi2_ext)
       Hww
       Hidx1 Hidx2 HTF1 HTF2 HW1 HW2 Hbase Horder Hbad)
    as Hww_no_collision.
  pose proof
    (validated_access_pair_lists_imply_noncollision checker Hchecker
       (PolyLang.pi_waccess_ext pi1_ext)
       (PolyLang.pi_raccess_ext pi2_ext)
       (PolyLang.pi_access_transformation_ext pi1_ext)
       (PolyLang.pi_access_transformation_ext pi2_ext)
       (PolyLang.ip_index_ext ip1) (PolyLang.ip_index_ext ip2)
       env_eq_in_domain order_guards bad_guards
       (length env + PolyLang.pi_depth_ext pi1_ext)
       (length env + PolyLang.pi_depth_ext pi2_ext)
       Hwr
       Hidx1 Hidx2 HTF1 HTF2 HW1 HR2 Hbase Horder Hbad)
    as Hwr_no_collision.
  pose proof
    (validated_access_pair_lists_imply_noncollision checker Hchecker
       (PolyLang.pi_raccess_ext pi1_ext)
       (PolyLang.pi_waccess_ext pi2_ext)
       (PolyLang.pi_access_transformation_ext pi1_ext)
       (PolyLang.pi_access_transformation_ext pi2_ext)
       (PolyLang.ip_index_ext ip1) (PolyLang.ip_index_ext ip2)
       env_eq_in_domain order_guards bad_guards
       (length env + PolyLang.pi_depth_ext pi1_ext)
       (length env + PolyLang.pi_depth_ext pi2_ext)
       Hrw
       Hidx1 Hidx2 HTF1 HTF2 HR1 HW2 Hbase Horder Hbad)
    as Hrw_no_collision.
  unfold no_write_collision, no_ww_collision, no_wr_collision.
  rewrite HTFIP1, HTFIP2.
  repeat split.
  - exact Hww_no_collision.
  - eapply transpose_access_noncollision. exact Hwr_no_collision.
  - eapply symmetrize_access_noncollision. exact Hrw_no_collision.
Qed.

Lemma unchanged_schedules_no_reversal:
  forall pi1 pi2 ip1 ip2,
    schedules_unchanged pi1 pi2 = true ->
    PolyLang.belongs_to_ext ip1 pi1 ->
    PolyLang.belongs_to_ext ip2 pi2 ->
    PolyLang.instr_point_ext_old_sched_lt ip1 ip2 ->
    PolyLang.instr_point_ext_new_sched_ge ip1 ip2 -> False.
Proof.
  intros pi1 pi2 ip1 ip2 Hsame
    (_ & _ & _ & Hts11 & Hts12 & _)
    (_ & _ & _ & Hts21 & Hts22 & _) Hold Hnew.
  unfold schedules_unchanged in Hsame.
  apply andb_true_iff in Hsame. destruct Hsame as [Hsame1 Hsame2].
  apply listzzs_strict_eqb_eq in Hsame1.
  apply listzzs_strict_eqb_eq in Hsame2.
  unfold PolyLang.instr_point_ext_old_sched_lt in Hold.
  unfold PolyLang.instr_point_ext_new_sched_ge in Hnew.
  rewrite Hts11, Hts21, Hsame1, Hsame2 in Hold.
  rewrite Hts12, Hts22, Hold in Hnew.
  destruct Hnew; discriminate.
Qed.

Lemma validate_two_instrs_implies_no_write_collision:
  forall pi1_ext pi2_ext env nth1 nth2 envv ipl1_ext ipl2_ext,
    WHEN res <- validate_two_instrs pi1_ext pi2_ext (length env) THEN
    res = true ->
    PolyLang.wf_pinstr_ext_tiling env pi1_ext ->
    PolyLang.wf_pinstr_ext_tiling env pi2_ext ->
    length env = length envv ->
    PolyLang.flatten_instr_nth_ext envv nth1 pi1_ext ipl1_ext ->
    PolyLang.flatten_instr_nth_ext envv nth2 pi2_ext ipl2_ext ->
    forall ip1_ext ip2_ext,
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
  intros pi1_ext pi2_ext env nth1 nth2 envv ipl1_ext ipl2_ext
    res Hval Hres Hwf1 Hwf2 Henvlen Hext1 Hext2
    ip1 ip2 Hip1 Hip2 Hosched Hnsched.
  unfold validate_two_instrs in Hval.
  destruct (schedules_unchanged pi1_ext pi2_ext) eqn:Hsame_sched.
  { exfalso. eapply unchanged_schedules_no_reversal; eauto.
    - destruct Hext1 as (_ & Hbelongs & _).
      apply Hbelongs in Hip1. tauto.
    - destruct Hext2 as (_ & Hbelongs & _).
      apply Hbelongs in Hip2. tauto. }
  bind_imp_destruct Hval in_domain_poly Hdomain.
  bind_imp_destruct Hval eq_env_poly Henv.
  bind_imp_destruct Hval ww Hww.
  bind_imp_destruct Hval wr Hwr.
  bind_imp_destruct Hval rw Hrw.
  eapply mayReturn_pure in Hval.
  rewrite Hres in Hval.
  do 2 rewrite andb_true_iff in Hval.
  destruct Hval as ((HwwT & HwrT) & HrwT); subst.
  assert (Horder :
    Exists
      (fun pol =>
        in_poly
          (PolyLang.ip_index_ext ip1 ++ PolyLang.ip_index_ext ip2)
          pol = true)
      (make_poly_lt
        pi1_ext.(PolyLang.pi_schedule1_ext)
        pi2_ext.(PolyLang.pi_schedule1_ext)
        (length env + pi1_ext.(PolyLang.pi_depth_ext))
        (length env + pi2_ext.(PolyLang.pi_depth_ext))
        [])).
  {
    eapply PolyLang.ip_old_sched_lt_implies_in_pi_old_sched_lt_pol;
      eauto using PolyLang.wf_pinstr_ext_tiling_implies_wf_pinstr_ext.
  }
  assert (Hbad :
    Exists
      (fun pol =>
        in_poly
          (PolyLang.ip_index_ext ip1 ++ PolyLang.ip_index_ext ip2)
          pol = true)
      (make_poly_ge
        pi1_ext.(PolyLang.pi_schedule2_ext)
        pi2_ext.(PolyLang.pi_schedule2_ext)
        (length env + pi1_ext.(PolyLang.pi_depth_ext))
        (length env + pi2_ext.(PolyLang.pi_depth_ext))
        [])).
  {
    eapply PolyLang.ip_new_sched_ge_implies_in_pi_new_sched_ge_pol;
      eauto using PolyLang.wf_pinstr_ext_tiling_implies_wf_pinstr_ext.
  }
  eapply
    (validated_access_checks_imply_no_write_collision
       validate_two_accesses validate_two_accesses_checker_sound)
    with
      (in_domain_poly:=in_domain_poly)
      (env_eq_in_domain:=eq_env_poly)
      (order_guards:=
        make_poly_lt
          pi1_ext.(PolyLang.pi_schedule1_ext)
          pi2_ext.(PolyLang.pi_schedule1_ext)
          (length env + pi1_ext.(PolyLang.pi_depth_ext))
          (length env + pi2_ext.(PolyLang.pi_depth_ext))
          [])
      (bad_guards:=
        make_poly_ge
          pi1_ext.(PolyLang.pi_schedule2_ext)
          pi2_ext.(PolyLang.pi_schedule2_ext)
          (length env + pi1_ext.(PolyLang.pi_depth_ext))
          (length env + pi2_ext.(PolyLang.pi_depth_ext))
          []); eauto.
Qed.

Local Lemma validated_access_checks_imply_no_write_collision_pointwise:
  forall pi1_ext pi2_ext env in_domain_poly env_eq_in_domain
         order_guards bad_guards ip1 ip2,
    mayReturn
      (poly_product
        pi1_ext.(PolyLang.pi_poly_ext)
        pi2_ext.(PolyLang.pi_poly_ext)
        (length env + pi1_ext.(PolyLang.pi_depth_ext))
        (length env + pi2_ext.(PolyLang.pi_depth_ext)))
      in_domain_poly ->
    mayReturn
      (poly_inter
        (make_poly_env_eq
          (length env)
          pi1_ext.(PolyLang.pi_depth_ext)
          pi2_ext.(PolyLang.pi_depth_ext))
        in_domain_poly)
      env_eq_in_domain ->
    mayReturn
      (forallb_imp
        (fun waccess1 => forallb_imp (fun waccess2 =>
          validate_two_accesses
            waccess1 waccess2
            pi1_ext.(PolyLang.pi_access_transformation_ext)
            pi2_ext.(PolyLang.pi_access_transformation_ext)
            env_eq_in_domain order_guards bad_guards
            (length env + pi1_ext.(PolyLang.pi_depth_ext))
            (length env + pi2_ext.(PolyLang.pi_depth_ext)))
          pi2_ext.(PolyLang.pi_waccess_ext))
        pi1_ext.(PolyLang.pi_waccess_ext)) true ->
    mayReturn
      (forallb_imp
        (fun waccess1 => forallb_imp (fun raccess2 =>
          validate_two_accesses
            waccess1 raccess2
            pi1_ext.(PolyLang.pi_access_transformation_ext)
            pi2_ext.(PolyLang.pi_access_transformation_ext)
            env_eq_in_domain order_guards bad_guards
            (length env + pi1_ext.(PolyLang.pi_depth_ext))
            (length env + pi2_ext.(PolyLang.pi_depth_ext)))
          pi2_ext.(PolyLang.pi_raccess_ext))
        pi1_ext.(PolyLang.pi_waccess_ext)) true ->
    mayReturn
      (forallb_imp
        (fun raccess1 => forallb_imp (fun waccess2 =>
          validate_two_accesses
            raccess1 waccess2
            pi1_ext.(PolyLang.pi_access_transformation_ext)
            pi2_ext.(PolyLang.pi_access_transformation_ext)
            env_eq_in_domain order_guards bad_guards
            (length env + pi1_ext.(PolyLang.pi_depth_ext))
            (length env + pi2_ext.(PolyLang.pi_depth_ext)))
          pi2_ext.(PolyLang.pi_waccess_ext))
        pi1_ext.(PolyLang.pi_raccess_ext)) true ->
    PolyLang.wf_pinstr_ext_tiling env pi1_ext ->
    PolyLang.wf_pinstr_ext_tiling env pi2_ext ->
    length (PolyLang.ip_index_ext ip1) =
      (length env + PolyLang.pi_depth_ext pi1_ext)%nat ->
    length (PolyLang.ip_index_ext ip2) =
      (length env + PolyLang.pi_depth_ext pi2_ext)%nat ->
    firstn (length env) (PolyLang.ip_index_ext ip1) =
      firstn (length env) (PolyLang.ip_index_ext ip2) ->
    PolyLang.belongs_to_ext ip1 pi1_ext ->
    PolyLang.belongs_to_ext ip2 pi2_ext ->
    Exists
      (fun pol =>
        in_poly (PolyLang.ip_index_ext ip1 ++ PolyLang.ip_index_ext ip2) pol = true)
      order_guards ->
    Exists
      (fun pol =>
        in_poly (PolyLang.ip_index_ext ip1 ++ PolyLang.ip_index_ext ip2) pol = true)
      bad_guards ->
    no_write_collision
      pi1_ext.(PolyLang.pi_waccess_ext)
      pi2_ext.(PolyLang.pi_waccess_ext)
      pi1_ext.(PolyLang.pi_raccess_ext)
      pi2_ext.(PolyLang.pi_raccess_ext) ip1 ip2.
Proof.
  intros pi1 pi2 env in_domain env_domain order bad ip1 ip2
    Hdomain Henv Hww Hwr Hrw Hwf1 Hwf2 Hidx1 Hidx2 Hsame
    Hbel1 Hbel2 Horder Hbad.
  assert (HTF1 : exact_listzzs_cols
    (length env + PolyLang.pi_depth_ext pi1)
    (PolyLang.pi_access_transformation_ext pi1)).
  { eapply wf_pinstr_ext_tiling_access_transformation_cols; exact Hwf1. }
  assert (HTF2 : exact_listzzs_cols
    (length env + PolyLang.pi_depth_ext pi2)
    (PolyLang.pi_access_transformation_ext pi2)).
  { eapply wf_pinstr_ext_tiling_access_transformation_cols; exact Hwf2. }
  assert (HW1 := wf_pinstr_ext_tiling_implies_waccess_matches _ _ Hwf1).
  assert (HR1 := wf_pinstr_ext_tiling_implies_raccess_matches _ _ Hwf1).
  assert (HW2 := wf_pinstr_ext_tiling_implies_waccess_matches _ _ Hwf2).
  assert (HR2 := wf_pinstr_ext_tiling_implies_raccess_matches _ _ Hwf2).
  destruct Hbel1 as
    (Hdom1 & _ & Hacc1 & _ & _ & _ & _).
  destruct Hbel2 as
    (Hdom2 & _ & Hacc2 & _ & _ & _ & _).
  assert (HDOM1 : exact_listzzs_cols
    (length env + PolyLang.pi_depth_ext pi1) (PolyLang.pi_poly_ext pi1)).
  { destruct Hwf1 as [Hwf1 _]. unfold PolyLang.wf_pinstr_ext in Hwf1. tauto. }
  assert (HDOM1' : exact_listzzs_cols
    (length (PolyLang.ip_index_ext ip1)) (PolyLang.pi_poly_ext pi1)).
  { rewrite Hidx1. exact HDOM1. }
  assert (Hbase :
    in_poly (PolyLang.ip_index_ext ip1 ++ PolyLang.ip_index_ext ip2)
      env_domain = true).
  {
    eapply poly_inter_def
      with (p := PolyLang.ip_index_ext ip1 ++ PolyLang.ip_index_ext ip2) in Henv.
    rewrite poly_inter_pure_def in Henv. rewrite Henv.
    apply andb_true_intro; split.
    - eapply make_poly_env_eq_correct; eauto.
    - eapply (proj2
        (poly_product_correct
          (PolyLang.pi_poly_ext pi1) (PolyLang.pi_poly_ext pi2)
          (length env + PolyLang.pi_depth_ext pi1)
          (length env + PolyLang.pi_depth_ext pi2)
          (PolyLang.ip_index_ext ip1) (PolyLang.ip_index_ext ip2)
          in_domain Hdomain Hidx1 Hidx2 HDOM1')).
      split; assumption.
  }
  pose proof Hww as Hww'.
  eapply validate_two_accesslist_implies_permut_no_collision1
    with (p1 := PolyLang.ip_index_ext ip1)
         (p2 := PolyLang.ip_index_ext ip2) in Hww'.
  specialize (Hww' eq_refl Hidx1 Hidx2 HTF1 HTF2 HW1 HW2 Hbase Horder Hbad).
  pose proof Hwr as Hwr'.
  eapply validate_two_accesslist_implies_permut_no_collision1
    with (p1 := PolyLang.ip_index_ext ip1)
         (p2 := PolyLang.ip_index_ext ip2) in Hwr'.
  specialize (Hwr' eq_refl Hidx1 Hidx2 HTF1 HTF2 HW1 HR2 Hbase Horder Hbad).
  pose proof Hrw as Hrw'.
  eapply validate_two_accesslist_implies_permut_no_collision1
    with (p1 := PolyLang.ip_index_ext ip1)
         (p2 := PolyLang.ip_index_ext ip2) in Hrw'.
  specialize (Hrw' eq_refl Hidx1 Hidx2 HTF1 HTF2 HR1 HW2 Hbase Horder Hbad).
  unfold no_write_collision, no_ww_collision, no_wr_collision.
  rewrite Hacc1, Hacc2.
  repeat split.
  - exact Hww'.
  - eapply transpose_access_noncollision; exact Hwr'.
  - eapply symmetrize_access_noncollision; exact Hrw'.
Qed.

(** Pointwise form of the pairwise validator theorem.  Unlike the historical
    flattened-list theorem above, this statement records exactly the facts
    about the two concrete instances that the access proof consumes. *)
Lemma validate_two_instrs_pointwise_implies_permutability:
  forall pi1_ext pi2_ext env ip1 ip2,
    mayReturn
      (validate_two_instrs pi1_ext pi2_ext (length env)) true ->
    PolyLang.wf_pinstr_ext_tiling env pi1_ext ->
    PolyLang.wf_pinstr_ext_tiling env pi2_ext ->
    length (PolyLang.ip_index_ext ip1) =
      (length env + PolyLang.pi_depth_ext pi1_ext)%nat ->
    length (PolyLang.ip_index_ext ip2) =
      (length env + PolyLang.pi_depth_ext pi2_ext)%nat ->
    firstn (length env) (PolyLang.ip_index_ext ip1) =
      firstn (length env) (PolyLang.ip_index_ext ip2) ->
    PolyLang.belongs_to_ext ip1 pi1_ext ->
    PolyLang.belongs_to_ext ip2 pi2_ext ->
    Instr.valid_access_function
      (PolyLang.pi_waccess_ext pi1_ext)
      (PolyLang.pi_raccess_ext pi1_ext)
      (PolyLang.pi_instr_ext pi1_ext) ->
    Instr.valid_access_function
      (PolyLang.pi_waccess_ext pi2_ext)
      (PolyLang.pi_raccess_ext pi2_ext)
      (PolyLang.pi_instr_ext pi2_ext) ->
    PolyLang.instr_point_ext_old_sched_lt ip1 ip2 ->
    PolyLang.instr_point_ext_new_sched_ge ip1 ip2 ->
    PolyLang.Permutable_ext ip1 ip2.
Proof.
  intros pi1 pi2 env ip1 ip2 Hval Hwf1 Hwf2 Hidx1 Hidx2 Hsame
    Hbel1 Hbel2 Haccess1 Haccess2 Hold Hnew.
  pose proof Hbel1 as Hbel1_full.
  pose proof Hbel2 as Hbel2_full.
  unfold validate_two_instrs in Hval.
  destruct (schedules_unchanged pi1 pi2) eqn:Hsame_sched.
  { exfalso. eapply unchanged_schedules_no_reversal; eauto. }
  bind_imp_destruct Hval in_domain_poly Hdomain.
  bind_imp_destruct Hval env_eq_in_domain Henv.
  bind_imp_destruct Hval ww Hww.
  bind_imp_destruct Hval wr Hwr.
  bind_imp_destruct Hval rw Hrw.
  apply mayReturn_pure in Hval.
  do 2 rewrite andb_true_iff in Hval.
  destruct Hval as ((HwwT & HwrT) & HrwT).
  subst ww wr rw.
  destruct Hbel1 as
    (Hdom1 & Htf1 & Hacc_tf1 & Hts11 & Hts12 & Hinstr1 & Hdepth1).
  destruct Hbel2 as
    (Hdom2 & Htf2 & Hacc_tf2 & Hts21 & Hts22 & Hinstr2 & Hdepth2).
  assert (Horder :
    Exists
      (fun pol =>
        in_poly
          (PolyLang.ip_index_ext ip1 ++ PolyLang.ip_index_ext ip2) pol = true)
      (make_poly_lt
        (PolyLang.pi_schedule1_ext pi1) (PolyLang.pi_schedule1_ext pi2)
        (length env + PolyLang.pi_depth_ext pi1)
        (length env + PolyLang.pi_depth_ext pi2) [])).
  {
    eapply make_poly_lt_correct; eauto.
    - destruct Hwf1 as [Hwf1 _].
      unfold PolyLang.wf_pinstr_ext in Hwf1. tauto.
    - unfold PolyLang.instr_point_ext_old_sched_lt in Hold.
      rewrite Hts11, Hts21 in Hold. exact Hold.
  }
  assert (Hbad :
    Exists
      (fun pol =>
        in_poly
          (PolyLang.ip_index_ext ip1 ++ PolyLang.ip_index_ext ip2) pol = true)
      (make_poly_ge
        (PolyLang.pi_schedule2_ext pi1) (PolyLang.pi_schedule2_ext pi2)
        (length env + PolyLang.pi_depth_ext pi1)
        (length env + PolyLang.pi_depth_ext pi2) [])).
  {
    eapply make_poly_ge_correct; eauto.
    - destruct Hwf1 as [Hwf1 _]. unfold PolyLang.wf_pinstr_ext in Hwf1. tauto.
    - unfold PolyLang.instr_point_ext_new_sched_ge in Hnew.
      rewrite Hts12, Hts22 in Hnew. exact Hnew.
  }
  assert (Hnocollision :
    no_write_collision
      (PolyLang.pi_waccess_ext pi1) (PolyLang.pi_waccess_ext pi2)
      (PolyLang.pi_raccess_ext pi1) (PolyLang.pi_raccess_ext pi2)
      ip1 ip2).
  {
    exact
      (validated_access_checks_imply_no_write_collision_pointwise
        pi1 pi2 env in_domain_poly env_eq_in_domain
        (make_poly_lt
          (PolyLang.pi_schedule1_ext pi1) (PolyLang.pi_schedule1_ext pi2)
          (length env + PolyLang.pi_depth_ext pi1)
          (length env + PolyLang.pi_depth_ext pi2) [])
        (make_poly_ge
          (PolyLang.pi_schedule2_ext pi1) (PolyLang.pi_schedule2_ext pi2)
          (length env + PolyLang.pi_depth_ext pi1)
          (length env + PolyLang.pi_depth_ext pi2) [])
        ip1 ip2 Hdomain Henv Hww Hwr Hrw Hwf1 Hwf2 Hidx1 Hidx2 Hsame
        Hbel1_full Hbel2_full Horder Hbad).
  }
  assert (Hacc_eq1 :
    PolyLang.ip_access_transformation_ext ip1 =
    PolyLang.ip_transformation_ext ip1).
  {
    rewrite Hacc_tf1, Htf1.
    symmetry. exact (proj2 Hwf1).
  }
  assert (Hacc_eq2 :
    PolyLang.ip_access_transformation_ext ip2 =
    PolyLang.ip_transformation_ext ip2).
  {
    rewrite Hacc_tf2, Htf2.
    symmetry. exact (proj2 Hwf2).
  }
  eapply no_write_collision_implies_permutable; eauto.
  - now rewrite Hinstr1.
  - now rewrite Hinstr2.
Qed.

Local Lemma validate_instr_and_list_pointwise:
  forall pi rest env_dim pi',
    mayReturn (validate_instr_and_list pi rest env_dim) true ->
    In pi' rest ->
    mayReturn (validate_two_instrs pi pi' env_dim) true /\
    mayReturn (validate_two_instrs pi' pi env_dim) true.
Proof.
  intros pi rest.
  induction rest as [|head tail IH]; intros env_dim pi' Hval Hin.
  - inversion Hin.
  - simpl in Hval.
    bind_imp_destruct Hval res1 Hval1.
    destruct (eqb res1 false) eqn:Hres1.
    { apply mayReturn_pure in Hval. discriminate. }
    bind_imp_destruct Hval res2 Hval2.
    destruct (eqb res2 false) eqn:Hres2.
    { apply mayReturn_pure in Hval. discriminate. }
    bind_imp_destruct Hval res3 Hval3.
    apply mayReturn_pure in Hval.
    subst res3.
    apply eqb_false_iff in Hres1.
    apply eqb_false_iff in Hres2.
    destruct res1; [|contradiction].
    destruct res2; [|contradiction].
    destruct Hin as [Heq | Hin].
    + subst pi'. split; assumption.
    + eapply IH; eauto.
Qed.

Local Lemma validate_instr_list_pointwise:
  forall pil env_dim pi1 pi2,
    mayReturn (validate_instr_list pil env_dim) true ->
    In pi1 pil ->
    In pi2 pil ->
    mayReturn (validate_two_instrs pi1 pi2 env_dim) true.
Proof.
  intros pil.
  induction pil as [|head tail IH]; intros env_dim pi1 pi2 Hval Hin1 Hin2.
  - inversion Hin1.
  - simpl in Hval.
    bind_imp_destruct Hval res1 Hself.
    bind_imp_destruct Hval res2 Hhead_tail.
    bind_imp_destruct Hval res3 Htail.
    apply mayReturn_pure in Hval.
    do 2 rewrite andb_true_iff in Hval.
    destruct Hval as ((Hres1 & Hres2) & Hres3).
    subst res1 res2 res3.
    destruct Hin1 as [Heq1 | Hin1]; destruct Hin2 as [Heq2 | Hin2].
    + subst pi1 pi2. exact Hself.
    + subst pi1.
      exact (proj1 (validate_instr_and_list_pointwise head tail env_dim pi2
        Hhead_tail Hin2)).
    + subst pi2.
      exact (proj2 (validate_instr_and_list_pointwise head tail env_dim pi1
        Hhead_tail Hin1)).
    + eapply IH; eauto.
Qed.

(** Pairwise consequence of a successful whole-program validation.  It avoids
    introducing a finite enumeration of all instruction instances. *)
Lemma validate_pointwise_implies_permutability:
  forall pp1 pp2 env1 env2 vars1 vars2 pil1 pil2 pi1_ext pi2_ext ip1 ip2,
    mayReturn (validate pp1 pp2) true ->
    pp1 = (pil1, env1, vars1) ->
    pp2 = (pil2, env2, vars2) ->
    In pi1_ext (compose_pinstrs_ext_at (length env1) pil1 pil2) ->
    In pi2_ext (compose_pinstrs_ext_at (length env1) pil1 pil2) ->
    length (PolyLang.ip_index_ext ip1) =
      (length env1 + PolyLang.pi_depth_ext pi1_ext)%nat ->
    length (PolyLang.ip_index_ext ip2) =
      (length env1 + PolyLang.pi_depth_ext pi2_ext)%nat ->
    firstn (length env1) (PolyLang.ip_index_ext ip1) =
      firstn (length env1) (PolyLang.ip_index_ext ip2) ->
    PolyLang.belongs_to_ext ip1 pi1_ext ->
    PolyLang.belongs_to_ext ip2 pi2_ext ->
    PolyLang.instr_point_ext_old_sched_lt ip1 ip2 ->
    PolyLang.instr_point_ext_new_sched_ge ip1 ip2 ->
    PolyLang.Permutable_ext ip1 ip2.
Proof.
  intros pp1 pp2 env1 env2 vars1 vars2 pil1 pil2 pi1 pi2 ip1 ip2
    Hval Hpp1 Hpp2 Hin1 Hin2 Hidx1 Hidx2 Hsame Hbel1 Hbel2 Hold Hnew.
  unfold validate in Hval.
  rewrite Hpp1, Hpp2 in Hval.
  bind_imp_destruct Hval wfpil1 Hwfpil1.
  bind_imp_destruct Hval wfpil2 Hwfpil2.
  bind_imp_destruct Hval eqdom Heqdom.
  bind_imp_destruct Hval resL HresL.
  apply mayReturn_pure in Hval.
  do 4 rewrite andb_true_iff in Hval.
  destruct Hval as ((((Hwfpil1T & Hwfpil2T) & HeqdomT) & HresLT) & HvaT).
  subst resL.
  eapply check_eqdom_pprog_correct in Heqdom.
  eapply Heqdom in HeqdomT.
  pose proof HeqdomT as Geqdom.
  assert (Hwf_ext :
    Forall (PolyLang.wf_pinstr_ext_tiling env1)
      (compose_pinstrs_ext_at (length env1) pil1 pil2)).
  {
    pose proof (check_wf_polyprog_affine_correct _ _ Hwfpil1 Hwfpil1T) as Hwfpp1.
    pose proof (check_wf_polyprog_affine_correct _ _ Hwfpil2 Hwfpil2T) as Hwfpp2.
    unfold PolyLang.wf_pprog_affine in *.
    destruct Hwfpp1 as [_ Hwfpp1].
    destruct Hwfpp2 as [_ Hwfpp2].
    destruct (Geqdom pil1 pil2 env1 env2 vars1 vars2 eq_refl eq_refl)
      as (Henv_eq & Hvars_eq & _ & Hrel).
    assert (Hwf1_forall : Forall (PolyLang.wf_pinstr_tiling env1 vars1) pil1).
    {
      apply Forall_forall. intros pi Hin.
      eapply PolyLang.wf_pinstr_affine_implies_wf_pinstr_tiling.
      eapply Hwfpp1; eauto.
    }
    assert (Hwf2_forall : Forall (PolyLang.wf_pinstr_tiling env1 vars1) pil2).
    {
      rewrite Henv_eq, Hvars_eq.
      apply Forall_forall. intros pi Hin.
      eapply PolyLang.wf_pinstr_affine_implies_wf_pinstr_tiling.
      eapply Hwfpp2; eauto.
    }
    clear - Hwf1_forall Hwf2_forall Hrel.
    revert pil2 Hwf2_forall Hrel.
    induction pil1 as [|pi1 pil1 IH]; intros [|pi2 pil2] Hwf2 Hrel.
    - simpl. constructor.
    - inversion Hrel.
    - inversion Hrel.
    - simpl.
    inversion Hwf1_forall; subst.
    inversion Hwf2; subst.
    destruct Hrel as [Heq Hrel].
    apply Forall_cons.
    + exact
        (wf_pinstr_tiling_implies_wf_pinstr_ext_tiling_at
          env1 vars1 pi1 pi2 H1 H3 Heq).
    + exact (IH H2 pil2 H4 Hrel).
  }
  assert (Hvalid_ext :
    Forall (fun pi_ext =>
      Instr.valid_access_function
        (PolyLang.pi_waccess_ext pi_ext)
        (PolyLang.pi_raccess_ext pi_ext)
        (PolyLang.pi_instr_ext pi_ext))
      (compose_pinstrs_ext_at (length env1) pil1 pil2)).
  { eapply check_valid_access_correct. exact HvaT. }
  assert (Hpair : mayReturn (validate_two_instrs pi1 pi2 (length env1)) true).
  {
    eapply validate_instr_list_pointwise
      with (pil := rev (compose_pinstrs_ext_at (length env1) pil1 pil2)); eauto.
    - exact (proj1 (@in_rev _ _ pi1) Hin1).
    - exact (proj1 (@in_rev _ _ pi2) Hin2).
  }
  eapply validate_two_instrs_pointwise_implies_permutability; eauto.
  - eapply Forall_forall in Hwf_ext; eauto.
  - eapply Forall_forall in Hwf_ext; eauto.
  - eapply Forall_forall in Hvalid_ext; eauto.
  - eapply Forall_forall in Hvalid_ext; eauto.
Qed.


Lemma validate_pinstr_implies_permutability1: 
  forall  env pi1_ext pi2_ext envv nth1 nth2 ipl1_ext ipl2_ext,
    WHEN res <- validate_two_instrs pi1_ext pi2_ext (length env) THEN 
    res = true ->
    PolyLang.wf_pinstr_ext_tiling env pi1_ext ->
    PolyLang.wf_pinstr_ext_tiling env pi2_ext ->
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
  assert (PolyLang.ip_access_transformation_ext ip1 = PolyLang.ip_transformation_ext ip1) as HTF1EQ. {
    assert (PolyLang.ip_access_transformation_ext ip1 = PolyLang.pi_access_transformation_ext pi1_ext) as HACC1. {
      eapply PolyLang.expand_ip_instr_eq_pi_access_tf_ext; eauto.
    }
    assert (PolyLang.ip_transformation_ext ip1 = PolyLang.pi_transformation_ext pi1_ext) as HTF1. {
      eapply PolyLang.expand_ip_instr_eq_pi_tf_ext; eauto.
    }
    destruct Hwf1 as [_ HPIEQ].
    rewrite HACC1, HTF1, HPIEQ; reflexivity.
  }
  assert (PolyLang.ip_access_transformation_ext ip2 = PolyLang.ip_transformation_ext ip2) as HTF2EQ. {
    assert (PolyLang.ip_access_transformation_ext ip2 = PolyLang.pi_access_transformation_ext pi2_ext) as HACC2. {
      eapply PolyLang.expand_ip_instr_eq_pi_access_tf_ext; eauto.
    }
    assert (PolyLang.ip_transformation_ext ip2 = PolyLang.pi_transformation_ext pi2_ext) as HTF2. {
      eapply PolyLang.expand_ip_instr_eq_pi_tf_ext; eauto.
    }
    destruct Hwf2 as [_ HPIEQ].
    rewrite HACC2, HTF2, HPIEQ; reflexivity.
  }
  
  eapply no_write_collision_implies_permutable; eauto.
  eapply validate_two_instrs_implies_no_write_collision; eauto.
  rewrite H; trivial. 
  rewrite H0; trivial.
Qed.


(** * Lifting instruction proofs to flattened instance lists *)






Lemma ipl_sorted_implies_compose_sorted_at:
  forall access_tf ipl1 ipl2,
    Sorted PolyLang.np_lt ipl1 ->
    Sorted PolyLang.np_lt ipl2 ->
    Sorted PolyLang.np_lt_ext (compose_ipl_ext_at access_tf ipl1 ipl2).
Proof.
  induction ipl1.
  - intros. simpls. destruct ipl2; simpls; econs.
  - intros. simpls. destruct ipl2; simpls; econs.
    inv H. inv H0.
    eapply IHipl1; eauto.
    inv H; inv H0.
    unfold compose_ip_ext_at.
    destruct ipl1; destruct ipl2; try solve [econs].
    simpls.
    destruct a; destruct i; subst; simpls.
    econs. unfold PolyLang.np_lt_ext; simpls.
    inv H4. unfold PolyLang.np_lt in H0. simpls. trivial.
Qed.


Lemma old_new_compose_at:
  forall access_tf ip1 ip2 ip,
    ip1 = PolyLang.old_of_ext ip ->
    ip2 = PolyLang.new_of_ext ip ->
    PolyLang.ip_access_transformation_ext ip = access_tf ->
    ip = compose_ip_ext_at access_tf ip1 ip2.
Proof.
  intros access_tf ip1 ip2 ip Hold Hnew Hacc.
  subst ip1 ip2.
  destruct ip; simpl in *.
  subst.
  reflexivity.
Qed.




Local Lemma validate_instr_and_list_implies_pointwise:
  forall
    (P : PolyLang.InstrPoint_ext -> Prop)
    (R : PolyLang.InstrPoint_ext -> PolyLang.InstrPoint_ext -> Prop)
    pil_ext pi1_ext env envv ipl_ext,
    WHEN res <- validate_instr_and_list pi1_ext (rev pil_ext) (length env) THEN
    res = true ->
    Forall (PolyLang.wf_pinstr_ext_tiling env) pil_ext ->
    PolyLang.flatten_instrs_ext envv pil_ext ipl_ext ->
    Forall (fun pi2_ext =>
      Instr.valid_access_function
        (PolyLang.pi_waccess_ext pi2_ext)
        (PolyLang.pi_raccess_ext pi2_ext)
        (PolyLang.pi_instr_ext pi2_ext)) pil_ext ->
    (forall pi2_ext nth2 ipl2_ext,
      PolyLang.wf_pinstr_ext_tiling env pi2_ext ->
      PolyLang.flatten_instr_nth_ext envv nth2 pi2_ext ipl2_ext ->
      Instr.valid_access_function
        (PolyLang.pi_waccess_ext pi2_ext)
        (PolyLang.pi_raccess_ext pi2_ext)
        (PolyLang.pi_instr_ext pi2_ext) ->
      mayReturn (validate_two_instrs pi1_ext pi2_ext (length env)) true ->
      mayReturn (validate_two_instrs pi2_ext pi1_ext (length env)) true ->
      forall ip1_ext ip2_ext,
        P ip1_ext ->
        In ip2_ext ipl2_ext ->
        R ip1_ext ip2_ext) ->
    forall ip1_ext ip2_ext,
      P ip1_ext ->
      In ip2_ext ipl_ext ->
      R ip1_ext ip2_ext.
Proof.
  intros P R pil_ext.
  induction pil_ext using rev_ind.
  {
    intros. intros res Hval Htrue Hwf Hflat Hacc Hpointwise ip1_ext ip2_ext Hip1 Hin.
    simpls.
    eapply PolyLang.flatten_instrs_ext_nil_implies_nil in Hflat.
    subst; tryfalse.
  }
  {
    intros. intros res Hval Htrue Hwf Hflat Hacc Hpointwise ip1_ext ip2_ext Hip1 Hin.
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

    rename x into pi2_ext.
    rename pil_ext into pil_head.
    eapply PolyLang.flatten_instrs_ext_app_singleton_inv in Hflat.
    destruct Hflat as
      (ipl_head & ipl_tail & Hflat_tail & Hflat_head & Hipl_app).
    rewrite Hipl_app in Hin.
    eapply in_app_or in Hin.
    destruct Hin as [Hin_head | Hin_tail].
    {
      eapply IHpil_ext; eauto.
      clear - Hwf.
      rewrite Forall_app in Hwf. destruct Hwf; trivial.
      clear - Hacc.
      rewrite Forall_app in Hacc. destruct Hacc; trivial.
    }
    {
      eapply Hpointwise with
        (pi2_ext:=pi2_ext)
        (nth2:=length pil_head)
        (ipl2_ext:=ipl_tail); eauto.
      {
        clear - Hwf.
        rewrite Forall_app in Hwf. destruct Hwf.
        inv H0; eauto.
      }
      {
        clear - Hacc.
        rewrite Forall_app in Hacc. destruct Hacc.
        inv H0; eauto.
      }
      {
        clear - Hres1 Hval1.
        eapply eqb_false_iff in Hres1.
        destruct res1; tryfalse; trivial.
      }
      {
        clear - Hres2 Hval2.
        eapply eqb_false_iff in Hres2.
        destruct res2; tryfalse; trivial.
      }
    }
  }
Qed.

Lemma validate_instr_and_list_implies_permutability1:
  forall pil_ext pi1_ext env envv nth ipl1_ext ipl_ext,
    WHEN res <- validate_instr_and_list pi1_ext (rev pil_ext) (length env) THEN
    res = true ->
    PolyLang.wf_pinstr_ext_tiling env pi1_ext ->
    Forall (PolyLang.wf_pinstr_ext_tiling env) pil_ext ->
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
  intros pil_ext pi1_ext env envv nth ipl1_ext ipl_ext.
  intros res Hval Htrue Hwf1 Hwf2 Henvlen Hflat1 Hflat Ha1 Ha2.
  eapply
    (@validate_instr_and_list_implies_pointwise
      (fun ip1_ext => In ip1_ext ipl1_ext)
      (fun ip1_ext ip2_ext =>
        PolyLang.instr_point_ext_old_sched_lt ip1_ext ip2_ext ->
        PolyLang.instr_point_ext_new_sched_ge ip1_ext ip2_ext ->
        PolyLang.Permutable_ext ip1_ext ip2_ext)
      pil_ext pi1_ext env envv ipl_ext res); eauto.
  intros pi2_ext nth2 ipl2_ext Hwf2' Hflat2 Ha2' Hforward Hreverse.
  intros ip1_ext ip2_ext Hin1 Hin2 Hold Hnew.
  eapply validate_pinstr_implies_permutability1
    with
      (env:=env) (envv:=envv)
      (pi1_ext:=pi1_ext) (pi2_ext:=pi2_ext)
      (nth1:=nth) (nth2:=nth2)
      (ipl1_ext:=ipl1_ext) (ipl2_ext:=ipl2_ext); eauto.
Qed.



Lemma compose_ipl_ext_at_nodup:
  forall access_tf ipl1 ipl2,
    NoDup ipl1 ->
    length ipl1 = length ipl2 ->
    NoDup (compose_ipl_ext_at access_tf ipl1 ipl2).
Proof.
  intros access_tf ipl1.
  revert access_tf.
  induction ipl1 as [|ip1 ipl1 IH]; intros acc_tf ipl2 Hnd Hlen.
  - destruct ipl2; simpl in *; constructor.
  - destruct ipl2 as [|ip2 ipl2]; simpl in Hlen; try discriminate.
    inversion Hnd as [|? ? Hnin Hnd']; subst.
    constructor.
    + intro Hin.
      eapply in_compose_ipl_ext_at_inv in Hin.
      destruct Hin as (ip1' & ip2' & Hin1 & _ & Heq).
      apply (f_equal PolyLang.old_of_ext) in Heq.
      revert Hnin Hin1 Heq.
      destruct ip1 as [n1 idx1 tf1 ts1 ins1 d1].
      destruct ip1' as [n1' idx1' tf1' ts1' ins1' d1'].
      simpl.
      intros Hnin Hin1 Heq.
      inversion Heq; subst.
      exact (Hnin Hin1).
    + eapply IH.
      * exact Hnd'.
      * lia.
Qed.


Lemma eq_except_sched_trans :
  forall ip1 ip2 ip3,
    PolyLang.eq_except_sched ip1 ip2 ->
    PolyLang.eq_except_sched ip2 ip3 ->
    PolyLang.eq_except_sched ip1 ip3.
Proof.
  exact PolyLang.ILSema.eq_except_sched_trans.
Qed.

Lemma new_of_ext_eq_except_old_of_ext :
  forall ip_ext,
    PolyLang.eq_except_sched
      (PolyLang.old_of_ext ip_ext)
      (PolyLang.new_of_ext ip_ext).
Proof.
  intros ip_ext.
  unfold PolyLang.eq_except_sched.
  destruct ip_ext; simpl.
  repeat split; reflexivity.
Qed.

Lemma eq_except_sched_in_flatten_instr_nth_implies_eq :
  forall envv nth pi ipl ip1 ip2,
    PolyLang.flatten_instr_nth envv nth pi ipl ->
    In ip1 ipl ->
    In ip2 ipl ->
    PolyLang.eq_except_sched ip1 ip2 ->
    ip1 = ip2.
Proof.
  intros envv nth pi ipl ip1 ip2 Hflat Hin1 Hin2 Heq.
  destruct Hflat as [_ [HBEL _]].
  destruct (HBEL ip1) as [Hfwd1 _].
  destruct (HBEL ip2) as [Hfwd2 _].
  destruct (Hfwd1 Hin1) as [_ [Hbel1 [_ _]]].
  destruct (Hfwd2 Hin2) as [_ [Hbel2 [_ _]]].
  destruct Hbel1 as [_ [Htf1 [Hts1 [Hins1 Hdepth1]]]].
  destruct Hbel2 as [_ [Htf2 [Hts2 [Hins2 Hdepth2]]]].
  unfold PolyLang.eq_except_sched in Heq.
  destruct Heq as (Hnth & Hidx & Htf & Hins & Hdepth).
  destruct ip1 as [nth1 idx1 tf1 ts1 ins1 d1].
  destruct ip2 as [nth2 idx2 tf2 ts2 ins2 d2].
  simpl in *.
  subst nth2 idx2 tf2 ins2 d2.
  rewrite Hts1.
  f_equal.
  symmetry.
  exact Hts2.
Qed.

Lemma wf_pil_tiling_implies_wf_pil_ext_tiling_at:
  forall pil pil' env vars,
    Forall (PolyLang.wf_pinstr_tiling env vars) pil ->
    Forall (PolyLang.wf_pinstr_tiling env vars) pil' ->
    rel_list PolyLang.eqdom_pinstr pil pil' ->
    Forall (PolyLang.wf_pinstr_ext_tiling env)
      (compose_pinstrs_ext_at (length env) pil pil').
Proof.
  induction pil.
  - intros; simpls. destruct pil'; econs.
  - intros; simpls. destruct pil'; simpls; [econs|].
    inv H. inv H0.
    econs.
    + eapply wf_pinstr_tiling_implies_wf_pinstr_ext_tiling_at; eauto.
      destruct H1; trivial.
    + destruct H1. eapply IHpil; eauto.
Qed.

Lemma expand_pinstr_implies_expand_pinstr_ext_at:
  forall env vars envv nth pi1 pi2 ipl1 ipl2 pi_ext ipl_ext,
    PolyLang.wf_pinstr_tiling env vars pi1 ->
    PolyLang.wf_pinstr_tiling env vars pi2 ->
    PolyLang.eqdom_pinstr pi1 pi2 ->
    length env = length envv ->
    PolyLang.flatten_instr_nth envv nth pi1 ipl1 ->
    PolyLang.flatten_instr_nth envv nth pi2 ipl2 ->
    compose_pinstr_ext_at (length env) pi1 pi2 = pi_ext ->
    compose_ipl_ext_at
      (PolyLang.current_access_transformation_at (length env) pi1)
      ipl1 ipl2 = ipl_ext ->
    PolyLang.flatten_instr_nth_ext envv nth pi_ext ipl_ext.
Proof.
  intros env vars envv nth pi1 pi2 ipl1 ipl2 pi_ext ipl_ext
    Hwf1 Hwf2 Heq Henvlen Hflat1 Hflat2 Hpiext Hiplex.
  symmetry in Hpiext; subst pi_ext.
  symmetry in Hiplex; subst ipl_ext.
  assert (Hwfext :
    PolyLang.wf_pinstr_ext_tiling env
      (compose_pinstr_ext_at (length env) pi1 pi2)).
  {
    eapply wf_pinstr_tiling_implies_wf_pinstr_ext_tiling_at; eauto.
  }
  assert (Hwf1_base : PolyLang.wf_pinstr env vars pi1)
    by (exact (proj1 Hwf1)).
  assert (Hwf2_base : PolyLang.wf_pinstr env vars pi2)
    by (exact (proj1 Hwf2)).
  assert (Hwitdim1 :
    witness_current_point_dim (PolyLang.pi_point_witness pi1) =
    PolyLang.pi_depth pi1)
    by (exact (proj1 Hwf1_base)).
  assert (Hwitdim2 :
    witness_current_point_dim (PolyLang.pi_point_witness pi2) =
    PolyLang.pi_depth pi2)
    by (exact (proj1 Hwf2_base)).
  assert (Hrel :
    rel_list PolyLang.eq_except_sched ipl1 ipl2).
  {
    eapply PolyLang.eqdom_pinstr_implies_flatten_instr_nth_rel'; eauto.
  }
  pose proof Heq as Heqdom_full.
  pose proof Hflat1 as Hflat1_full.
  pose proof Hflat2 as Hflat2_full.
  destruct Heq as
    (Hdepth_eq & Hinstr_eq & Hpoly_eq & Hwit_eq &
     Htf_eqdom & Hacc_tf_eqdom & Hw_eqdom & Hr_eqdom).
  destruct Hflat1 as [Henv1 [Hbel1 [Hnd1 Hsorted1]]].
  destruct Hflat2 as [Henv2 [Hbel2 [Hnd2 Hsorted2]]].
  split.
  - intros ip_ext Hinext.
    eapply in_compose_ipl_ext_at_inv in Hinext.
    destruct Hinext as (ip1 & ip2 & Hin1 & Hin2 & Heqip).
    subst ip_ext.
    simpl.
    eapply Henv1; eauto.
  - split.
    + intros ip_ext.
      split.
      * intros Hinext.
        eapply In_nth_error in Hinext.
        destruct Hinext as [k Hnth_ext].
        eapply nth_error_compose_ipl_ext_at_inv_local in Hnth_ext.
        destruct Hnth_ext as (ip1 & ip2 & Hnth1 & Hnth2 & Heqip).
        assert (Hin1 : In ip1 ipl1) by (apply nth_error_In in Hnth1; exact Hnth1).
        assert (Hin2 : In ip2 ipl2) by (apply nth_error_In in Hnth2; exact Hnth2).
        assert (Heqip12 : PolyLang.eq_except_sched ip1 ip2)
          by (eapply rel_list_implies_rel_nth; eauto).
        destruct Heqip12 as (_ & Hidx_eq & _ & _ & _).
        destruct (Hbel1 ip1) as [Hfwd1 _].
        destruct (Hbel2 ip2) as [Hfwd2 _].
        destruct (Hfwd1 Hin1) as [Hpref1 [Hbelongs1 [Hnth_eq1 Hlen1]]].
        destruct (Hfwd2 Hin2) as [Hpref2 [Hbelongs2 [Hnth_eq2 Hlen2]]].
        subst ip_ext.
        assert (Hbel_ext_compose :
          PolyLang.belongs_to_ext
            (compose_ip_ext_at
               (PolyLang.current_access_transformation_at (length env) pi1)
               ip1 ip2)
            (compose_pinstr_ext_at (length env) pi1 pi2)).
        {
          unfold PolyLang.belongs_to_ext, compose_ip_ext_at, compose_pinstr_ext_at; simpl.
          destruct Hbelongs1 as [Hdom1 [_ [Hts1 [Hins1 Hdepth1]]]].
          destruct Hbelongs2 as [_ [_ [Hts2 [_ _]]]].
          pose proof
            (expand_ip_instr_eq_current_tf_at
               env vars envv nth pi1 ipl1 ip1
               Hwf1_base Henvlen Hflat1_full Hin1)
            as Hcur_tf1.
          split; [exact Hdom1|].
          split.
          - exact Hcur_tf1.
          - split.
            + reflexivity.
            + split.
              * exact Hts1.
              * split.
                -- rewrite Hidx_eq. exact Hts2.
                -- split; [exact Hins1 | exact Hdepth1].
        }
        split.
        -- exact Hpref1.
        -- split.
           ++ exact Hbel_ext_compose.
           ++ split; [exact Hnth_eq1 | exact Hlen1].
      * intros [Hpref [Hbel_ext [Hnth_eq Hlen]]].
      pose (ip_old := PolyLang.old_of_ext ip_ext).
      pose (ip_new := PolyLang.new_of_ext ip_ext).
      assert (Hold_in : In ip_old ipl1).
      {
        destruct (Hbel1 ip_old) as [_ Hbwd1].
        apply Hbwd1.
        split; [exact Hpref|].
        split.
        {
          destruct Hbel_ext as
              [Hdom_ext [Htf_ext [_ [Hts1_ext [_ [Hins_ext Hdepth_ext]]]]]].
          unfold ip_old, PolyLang.old_of_ext; simpl.
          assert (Hcur_old_tf :
            PolyLang.current_transformation_of pi1
              (PolyLang.ILSema.ip_index
                 (PolyLang.old_of_ext ip_ext)) =
            PolyLang.current_transformation_at (length env) pi1).
          {
            unfold ip_old, PolyLang.old_of_ext; simpl.
            eapply current_transformation_of_eq_at.
            - exact Hwitdim1.
            - cbn in Hlen.
              rewrite Henvlen.
              exact Hlen.
          }
          split; [exact Hdom_ext|].
          split; [rewrite Htf_ext; symmetry; exact Hcur_old_tf|].
          split; [exact Hts1_ext|].
          split; [exact Hins_ext| exact Hdepth_ext].
        }
        {
          split; assumption.
        }
      }
      assert (Hnew_in : In ip_new ipl2).
      {
        destruct (Hbel2 ip_new) as [_ Hbwd2].
        apply Hbwd2.
        split; [exact Hpref|].
        split.
        {
          destruct Hbel_ext as
              [Hdom_ext [Htf_ext [_ [_ [Hts2_ext [Hins_ext Hdepth_ext]]]]]].
          unfold ip_new, PolyLang.new_of_ext; simpl.
          assert (Hcur_new_tf :
            PolyLang.current_transformation_of pi2
              (PolyLang.ILSema.ip_index
                 (PolyLang.new_of_ext ip_ext)) =
            PolyLang.current_transformation_at (length env) pi2).
          {
            unfold ip_new, PolyLang.new_of_ext; simpl.
            cbn in Hlen.
            rewrite Hdepth_eq in Hlen.
            eapply current_transformation_of_eq_at.
            - exact Hwitdim2.
            - rewrite Henvlen.
              exact Hlen.
          }
          split.
          {
            rewrite <- Hpoly_eq.
            exact Hdom_ext.
          }
          split.
          {
            rewrite Htf_ext.
            cbn.
            rewrite
              (eqdom_pinstr_implies_current_transformation_at_eq
                 (length env) pi1 pi2 Heqdom_full).
            symmetry. exact Hcur_new_tf.
          }
          split; [exact Hts2_ext|].
          split.
          {
            rewrite Hins_ext.
            exact Hinstr_eq.
          }
          {
            rewrite Hdepth_ext.
            exact Hdepth_eq.
          }
        }
        {
          split; [exact Hnth_eq | rewrite <- Hdepth_eq; exact Hlen].
        }
      }
      apply In_nth_error in Hold_in.
      destruct Hold_in as [k Hnth_old].
      assert (exists ip2',
        nth_error ipl2 k = Some ip2' /\
        PolyLang.eq_except_sched ip_old ip2').
      {
        assert (Hlen12 : length ipl1 = length ipl2).
        {
          eapply PolyLang.eqdom_pinstr_implies_flatten_instr_same_len; eauto.
        }
        assert (k < length ipl2)%nat.
        {
          rewrite <- Hlen12.
          eapply PolyLang.nth_error_Some'; eauto.
        }
        destruct (nth_error ipl2 k) eqn:Hnth2k.
        2: {
          eapply nth_error_None in Hnth2k.
          lia.
        }
        exists i.
        split.
        - reflexivity.
        - eapply rel_list_implies_rel_nth; eauto.
      }
      destruct H as [ip2' [Hnth_new_eq Heq_old_new']].
      assert (Heq_new : PolyLang.eq_except_sched ip_new ip2').
      {
        eapply eq_except_sched_trans.
        - apply new_of_ext_eq_except_old_of_ext.
        - exact Heq_old_new'.
      }
      assert (Hin_new_eq : In ip2' ipl2).
      {
        eapply nth_error_In.
        exact Hnth_new_eq.
      }
      eapply eq_except_sched_in_flatten_instr_nth_implies_eq in Heq_new; eauto.
      subst ip2'.
      assert (Hnth_compose :
        nth_error
          (compose_ipl_ext_at
             (PolyLang.current_access_transformation_at (length env) pi1)
             ipl1 ipl2) k = Some ip_ext).
      {
        rewrite
          (nth_error_compose_ipl_ext_at
             k
             (PolyLang.current_access_transformation_at (length env) pi1)
             ipl1 ipl2 ip_old ip_new); eauto.
        f_equal.
        unfold ip_old, ip_new.
        destruct Hbel_ext as [_ [_ [Hacc_tf_ext [_ [_ [_ _]]]]]].
        assert (Hacc_eq :
          PolyLang.ip_access_transformation_ext ip_ext =
          PolyLang.current_access_transformation_at (length env) pi1).
        {
          rewrite Hacc_tf_ext. reflexivity.
        }
        exact
          (eq_sym
             (old_new_compose_at
                (PolyLang.current_access_transformation_at (length env) pi1)
                (PolyLang.old_of_ext ip_ext)
                (PolyLang.new_of_ext ip_ext)
                ip_ext eq_refl eq_refl Hacc_eq)).
      }
      eapply nth_error_In; exact Hnth_compose.
    + split.
      * eapply compose_ipl_ext_at_nodup.
        -- exact Hnd1.
        -- eapply PolyLang.eqdom_pinstr_implies_flatten_instr_same_len; eauto.
      * eapply ipl_sorted_implies_compose_sorted_at; eauto.
Qed.

Local Lemma compose_pinstrs_ext_at_length_left :
  forall env_dim pil1 pil2,
    length pil1 = length pil2 ->
    length (compose_pinstrs_ext_at env_dim pil1 pil2) = length pil1.
Proof.
  intros env_dim pil1.
  induction pil1 as [|pi1 pil1 IH]; intros [|pi2 pil2] Hlength;
    simpl in *; try lia.
  f_equal.
  apply IH.
  lia.
Qed.

Lemma flatten_instrs_implies_flatten_instrs_ext_at:
  forall env vars envv pil1 pil2 pil_ext ipl1 ipl2,
    Forall (PolyLang.wf_pinstr_tiling env vars) pil1 ->
    Forall (PolyLang.wf_pinstr_tiling env vars) pil2 ->
    rel_list PolyLang.eqdom_pinstr pil1 pil2 ->
    length env = length envv ->
    PolyLang.flatten_instrs envv pil1 ipl1 ->
    PolyLang.flatten_instrs envv pil2 ipl2 ->
    compose_pinstrs_ext_at (length env) pil1 pil2 = pil_ext ->
    exists ipl_ext,
      PolyLang.flatten_instrs_ext envv pil_ext ipl_ext /\
      PolyLang.old_of_ext_list ipl_ext = ipl1 /\
      PolyLang.new_of_ext_list ipl_ext = ipl2.
Proof.
  intros env vars envv pil1.
  induction pil1 using rev_ind;
    intros pil2 pil_ext ipl1 ipl2 Hwf1 Hwf2 Hrel Henvlen Hflat1 Hflat2 Hpil_ext.
  - 
    destruct pil2; simpls; tryfalse.
    eapply PolyLang.flatten_instrs_nil_implies_nil in Hflat1.
    eapply PolyLang.flatten_instrs_nil_implies_nil in Hflat2.
    subst.
    exists ([] : list PolyLang.InstrPoint_ext).
    split.
    + subst. apply PolyLang.flatten_instrs_ext_nil.
    + split; reflexivity.
  - 
    assert (exists pi2 pil2', pil2 = pil2' ++ [pi2]) as Hpil2.
    {
      clear - Hrel.
      eapply rel_list_implies_eq_length in Hrel.
      destruct pil2.
      - rewrite app_length in Hrel; simpls; lia.
      - assert (length (p :: pil2) > 0)%nat by (rewrite app_length in Hrel; simpls; lia).
        exists (last (p :: pil2) p).
        exists (removelast (p :: pil2)).
        eapply app_removelast_last. intro; tryfalse.
    }
    destruct Hpil2 as (pi2 & pil2' & Hpil2).
    rename x into pi1.
    rename pil1 into pil1'.
    assert (Hwf_pi1 : PolyLang.wf_pinstr_tiling env vars pi1).
    {
      eapply Forall_forall; [exact Hwf1 |].
      apply in_or_app. right. simpl. auto.
    }
    rewrite Hpil2 in Hwf2.
    assert (Hwf_pi2 : PolyLang.wf_pinstr_tiling env vars pi2).
    {
      eapply Forall_forall; [exact Hwf2 |].
      apply in_or_app. right. simpl. auto.
    }
    rewrite Hpil2 in Hrel.
    rewrite Hpil2 in Hpil_ext.
    eapply rel_list_app_singleton in Hrel.
    destruct Hrel as (Hrel_head & Heq_last).
    rewrite Hpil2 in Hflat2.
    eapply PolyLang.flatten_instrs_app_singleton_inv in Hflat1.
    eapply PolyLang.flatten_instrs_app_singleton_inv in Hflat2.
    destruct Hflat1 as (iplh1 & iplt1 & Hflat_h1 & Hflat_t1 & Happ1).
    destruct Hflat2 as (iplh2 & iplt2 & Hflat_h2 & Hflat_t2 & Happ2).
    rewrite Forall_app in Hwf1.
    rewrite Forall_app in Hwf2.
    destruct Hwf1 as (Hwf1_head & Hwf1_last).
    destruct Hwf2 as (Hwf2_head & Hwf2_last).
    assert (Hlen_heads : length pil1' = length pil2').
    {
      eapply rel_list_implies_eq_length; eauto.
    }
    assert (Hflat_t2_eq :
      PolyLang.flatten_instr_nth envv (length pil1') pi2 iplt2).
    {
      rewrite Hlen_heads.
      exact Hflat_t2.
    }
    assert (Hpilext_head :
      compose_pinstrs_ext_at (length env) pil1' pil2' =
      firstn (length pil1') pil_ext).
    {
      rewrite <- Hpil_ext.
      rewrite compose_pinstrs_ext_at_app_singleton.
      - assert (Hlen_ext :
            length pil1' =
            length (compose_pinstrs_ext_at (length env) pil1' pil2')).
        {
          symmetry.
          apply compose_pinstrs_ext_at_length_left.
          eapply rel_list_implies_eq_length; eauto.
        }
        rewrite firstn_app.
        rewrite Hlen_ext.
        rewrite firstn_all.
        rewrite Nat.sub_diag.
        simpl.
        rewrite app_nil_r.
        reflexivity.
      - eapply rel_list_implies_eq_length; eauto.
    }
    destruct (IHpil1 pil2' (firstn (length pil1') pil_ext) iplh1 iplh2
                Hwf1_head Hwf2_head Hrel_head Henvlen Hflat_h1 Hflat_h2 Hpilext_head)
      as (iplh_ext & Hflat_h_ext & Hold_h_ext & Hnew_h_ext).
    set (pi_ext_t :=
      compose_pinstr_ext_at (length env) pi1 pi2).
    set (iplt_ext :=
      compose_ipl_ext_at
        (PolyLang.current_access_transformation_at (length env) pi1)
        iplt1 iplt2).
    assert (Hflat_t_ext :
      PolyLang.flatten_instr_nth_ext envv (length pil1') pi_ext_t iplt_ext).
    {
      unfold pi_ext_t, iplt_ext.
      eapply
        (expand_pinstr_implies_expand_pinstr_ext_at
           env vars envv (length pil1') pi1 pi2 iplt1 iplt2 pi_ext_t iplt_ext).
      - exact Hwf_pi1.
      - exact Hwf_pi2.
      - exact Heq_last.
      - exact Henvlen.
      - exact Hflat_t1.
      - exact Hflat_t2_eq.
      - reflexivity.
      - reflexivity.
    }
    exists (iplh_ext ++ iplt_ext).
    split.
    + rewrite <- Hpil_ext.
      assert (Hlen_ext_head :
        length (compose_pinstrs_ext_at (length env) pil1' pil2') = length pil1').
      {
        apply compose_pinstrs_ext_at_length_left.
        exact Hlen_heads.
      }
      rewrite compose_pinstrs_ext_at_app_singleton.
      * eapply PolyLang.flatten_instrs_ext_app_singleton.
        -- rewrite <- Hpilext_head in Hflat_h_ext. exact Hflat_h_ext.
        -- rewrite <- Hlen_ext_head in Hflat_t_ext. exact Hflat_t_ext.
      * eapply rel_list_implies_eq_length; eauto.
    + split.
      * subst iplt_ext.
        unfold PolyLang.old_of_ext_list.
        rewrite List.map_app.
        unfold PolyLang.old_of_ext_list in Hold_h_ext.
        rewrite Hold_h_ext.
        rewrite Happ1.
        f_equal.
        assert (Hlen_tail : length iplt1 = length iplt2).
        {
          eapply (PolyLang.eqdom_pinstr_implies_flatten_instr_same_len
                    pi1 pi2 envv iplt1 iplt2 (length pil1')).
          - exact Heq_last.
          - exact Hflat_t1.
          - exact Hflat_t2_eq.
        }
        eapply old_of_compose_list_at_ok; [exact Hlen_tail | reflexivity].
      * subst iplt_ext.
        unfold PolyLang.new_of_ext_list.
        rewrite List.map_app.
        unfold PolyLang.new_of_ext_list in Hnew_h_ext.
        rewrite Hnew_h_ext.
        rewrite Happ2.
        f_equal.
        assert (Hrel_tail : rel_list PolyLang.eq_except_sched iplt1 iplt2).
        {
          eapply (PolyLang.eqdom_pinstr_implies_flatten_instr_nth_rel'
                    iplt1 pi1 pi2 envv (length pil1') iplt2).
          - exact Heq_last.
          - exact Hflat_t1.
          - exact Hflat_t2_eq.
        }
        eapply new_of_compose_list_at_ok; [exact Hrel_tail | reflexivity].
Qed.

Lemma validate_instr_and_list_implies_permutability2:
  forall pi1_ext pil_ext env envv nth ipl1_ext ipl_ext,
    WHEN res <- validate_instr_and_list pi1_ext (rev pil_ext) (length env) THEN
    res = true ->
    PolyLang.wf_pinstr_ext_tiling env pi1_ext ->
    Forall (PolyLang.wf_pinstr_ext_tiling env) pil_ext ->
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
  intros pi1_ext pil_ext env envv nth ipl1_ext ipl_ext.
  intros res Hval Htrue Hwf1 Hwf2 Henvlen Hflat1 Hflat Ha1 Ha2.
  eapply
    (@validate_instr_and_list_implies_pointwise
      (fun ip1_ext => In ip1_ext ipl1_ext)
      (fun ip1_ext ip2_ext =>
        PolyLang.instr_point_ext_old_sched_lt ip2_ext ip1_ext ->
        PolyLang.instr_point_ext_new_sched_ge ip2_ext ip1_ext ->
        PolyLang.Permutable_ext ip1_ext ip2_ext)
      pil_ext pi1_ext env envv ipl_ext res); eauto.
  intros pi2_ext nth2 ipl2_ext Hwf2' Hflat2 Ha2' Hforward Hreverse.
  intros ip1_ext ip2_ext Hin1 Hin2 Hold Hnew.
  eapply PolyLang.Permutable_ext_symm.
  eapply validate_pinstr_implies_permutability1
    with
      (env:=env) (envv:=envv)
      (pi1_ext:=pi2_ext) (pi2_ext:=pi1_ext)
      (nth1:=nth2) (nth2:=nth)
      (ipl1_ext:=ipl2_ext) (ipl2_ext:=ipl1_ext); eauto.
Qed.





Lemma validate_pinstrs_ext_implies_permutability:
  forall pil_ext env envv ipl_ext,
    WHEN res <- (validate_instr_list (rev pil_ext) (length env)) THEN
    res = true ->
    Forall (PolyLang.wf_pinstr_ext_tiling env) pil_ext ->
    length env = length envv ->
    PolyLang.flatten_instrs_ext envv pil_ext ipl_ext ->
    Forall (fun pi_ext =>
      Instr.valid_access_function
        (PolyLang.pi_waccess_ext pi_ext)
        (PolyLang.pi_raccess_ext pi_ext)
        (PolyLang.pi_instr_ext pi_ext)) pil_ext ->
    forall ip1_ext ip2_ext,
      In ip1_ext ipl_ext ->
      In ip2_ext ipl_ext ->
      PolyLang.instr_point_ext_old_sched_lt ip1_ext ip2_ext ->
      PolyLang.instr_point_ext_new_sched_ge ip1_ext ip2_ext ->
      PolyLang.Permutable_ext ip1_ext ip2_ext.
Proof.
  induction pil_ext using rev_ind.
  - intros env envv ipl_ext res Hval Htrue Hwf Henvlen Hflat Hacc ip1_ext ip2_ext Hin1.
    eapply PolyLang.flatten_instrs_ext_nil_implies_nil in Hflat.
    subst. intros Hin2. inversion Hin1.
  - intros env envv ipl_ext res Hval Htrue Hwf Henvlen Hflat Hacc ip1_ext ip2_ext Hin1 Hin2 Hold Hnew.
    rename x into pi_tail.
    rename pil_ext into pil_head.
    assert (Hwf_tail : PolyLang.wf_pinstr_ext_tiling env pi_tail).
    {
      eapply Forall_forall; [exact Hwf |].
      apply in_or_app. right. simpl. auto.
    }
    rewrite Forall_app in Hwf.
    rewrite Forall_app in Hacc.
    destruct Hwf as (Hwf_head & Hwf_last).
    destruct Hacc as (Hacc_head & Hacc_last).
    assert (Hacc_tail :
      Instr.valid_access_function
        (PolyLang.pi_waccess_ext pi_tail)
        (PolyLang.pi_raccess_ext pi_tail)
        (PolyLang.pi_instr_ext pi_tail)).
    {
      inversion Hacc_last as [|? ? Hacc_tail0 Hacc_nil]; subst.
      inversion Hacc_nil; subst.
      exact Hacc_tail0.
    }
    rewrite rev_app_distr in Hval.
    simpl in Hval.
    rewrite Htrue in Hval.
    bind_imp_destruct Hval res1 Hval1.
    bind_imp_destruct Hval res2 Hval2.
    bind_imp_destruct Hval res3 Hval3.
    eapply mayReturn_pure in Hval.
    repeat rewrite andb_true_iff in Hval.
    destruct Hval as ((Hres1T & Hres2T) & Hres3T).
    eapply PolyLang.flatten_instrs_ext_app_singleton_inv in Hflat.
    destruct Hflat as (ipl_head & ipl_tail & Hflat_head & Hflat_tail & Hipl_app).
    rewrite Hipl_app in Hin1.
    rewrite Hipl_app in Hin2.
    eapply in_app_or in Hin1.
    eapply in_app_or in Hin2.
    destruct Hin1 as [Hin1_head | Hin1_tail];
    destruct Hin2 as [Hin2_head | Hin2_tail].
    + eapply IHpil_ext; eauto.
    + eapply PolyLang.Permutable_ext_symm.
      eapply validate_instr_and_list_implies_permutability2
        with (pi1_ext:=pi_tail) (pil_ext:=pil_head)
             (env:=env) (envv:=envv)
             (nth:=length pil_head) (ipl1_ext:=ipl_tail) (ipl_ext:=ipl_head); eauto.
    + eapply validate_instr_and_list_implies_permutability1
        with (pi1_ext:=pi_tail) (pil_ext:=pil_head)
             (env:=env) (envv:=envv)
             (nth:=length pil_head) (ipl1_ext:=ipl_tail) (ipl_ext:=ipl_head); eauto.
    + eapply validate_pinstr_implies_permutability1
        with (env:=env) (envv:=envv)
             (pi1_ext:=pi_tail) (pi2_ext:=pi_tail)
             (nth1:=length pil_head) (nth2:=length pil_head)
             (ipl1_ext:=ipl_tail) (ipl2_ext:=ipl_tail); eauto.
Qed.

(** * End-to-end schedule-validation correctness *)

Lemma validate_tiling_implies_correspondence:
  forall pp1 pp2 env1 env2 vars1 vars2 poly_instrs1 poly_instrs2,
    WHEN res <- validate_tiling pp1 pp2 THEN
    pp1 = (poly_instrs1, env1, vars1) ->
    pp2 = (poly_instrs2, env2, vars2) ->
    res = true ->
    PolyLang.eqdom_pprog pp1 pp2.
Proof.
  intros. intros res Hval Hpp1 Hpp2 Hres.
  eapply check_eqdom_pprog_correct; eauto.
  unfold validate_tiling in Hval.
  rewrite Hpp1 in Hval.
  rewrite Hpp2 in Hval.
  bind_imp_destruct Hval wfpil1 Hwfpil1.
  bind_imp_destruct Hval wfpil2 Hwfpil2.
  bind_imp_destruct Hval eqdom Heqdom.
  bind_imp_destruct Hval resL HresL.
  assert (eqdom = true).
  {
    eapply mayReturn_pure in Hval.
    subst.
    do 4 rewrite andb_true_iff in Hres.
    clear - Hres. firstorder.
  }
  subst; eauto.
Qed.

Lemma validate_tiling_preserve_finite:
  forall pis1 env1 vars1 pis2 env2 vars2 envv,
    WHEN res <- validate_tiling (pis1, env1, vars1) (pis2, env2, vars2) THEN
    res = true ->
    ((exists ipl1, PolyLang.flatten_instrs envv pis1 ipl1) <->
     (exists ipl2, PolyLang.flatten_instrs envv pis2 ipl2)).
Proof.
  intros. intros res Hval Htrue.
  unfold validate_tiling in Hval.
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

Lemma validate_tiling_implies_permutability:
  forall pp1 pp2 env1 env2 envv vars1 vars2 poly_instrs1 poly_instrs2 ipl1 ipl2,
    WHEN res <- validate_tiling pp1 pp2 THEN
    pp1 = (poly_instrs1, env1, vars1) ->
    pp2 = (poly_instrs2, env2, vars2) ->
    res = true ->
    length env1 = length envv ->
    PolyLang.flatten_instrs envv poly_instrs1 ipl1 ->
    PolyLang.flatten_instrs envv poly_instrs2 ipl2 ->
    exists ipl_ext,
      PolyLang.new_of_ext_list ipl_ext = ipl2 /\
      PolyLang.old_of_ext_list ipl_ext = ipl1 /\
      (forall ip1_ext ip2_ext,
        In ip1_ext ipl_ext ->
        In ip2_ext ipl_ext ->
        PolyLang.instr_point_ext_old_sched_lt ip1_ext ip2_ext ->
        PolyLang.instr_point_ext_new_sched_ge ip1_ext ip2_ext ->
        PolyLang.Permutable_ext ip1_ext ip2_ext).
Proof.
  intros. intros res Hval Hpp1 Hpp2 Hres Henvlen Hflt1 Hflt2.
  rewrite Hres in Hval.
  unfold validate_tiling in Hval.
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
  destruct (Geqdom poly_instrs1 poly_instrs2 env1 env2 vars1 vars2 eq_refl eq_refl)
    as (Henv_eq0 & Hvars_eq0 & _ & Hrel_pil).
  destruct
    (flatten_instrs_implies_flatten_instrs_ext_at
       env1 vars1 envv poly_instrs1 poly_instrs2
       (compose_pinstrs_ext_at (length env1) poly_instrs1 poly_instrs2)
       ipl1 ipl2)
    as (ipl_ext & Hflat_ext & Hold_ext & Hnew_ext).
  {
    pose proof (check_wf_polyprog_tiling_correct _ _ Hwfpil1 Hwfpil1T) as Hwfpp1.
    unfold PolyLang.wf_pprog_tiling in Hwfpp1.
    destruct Hwfpp1 as [_ Hwfpp1].
    eapply Forall_forall.
    intros pi Hin.
    eapply Hwfpp1; eauto.
  }
  {
    pose proof (check_wf_polyprog_tiling_correct _ _ Hwfpil2 Hwfpil2T) as Hwfpp2.
    unfold PolyLang.wf_pprog_tiling in Hwfpp2.
    destruct Hwfpp2 as [_ Hwfpp2].
    rewrite Henv_eq0, Hvars_eq0.
    eapply Forall_forall.
    intros pi Hin.
    eapply Hwfpp2; eauto.
  }
  {
    exact Hrel_pil.
  }
  {
    exact Henvlen.
  }
  {
    exact Hflt1.
  }
  {
    exact Hflt2.
  }
  {
    reflexivity.
  }
  exists ipl_ext.
  split.
  - exact Hnew_ext.
  - split.
    + exact Hold_ext.
    + clear Hnew_ext Hold_ext.
      assert (Hwf_ext :
        Forall (PolyLang.wf_pinstr_ext_tiling env1)
          (compose_pinstrs_ext_at (length env1) poly_instrs1 poly_instrs2)).
      {
        pose proof (check_wf_polyprog_tiling_correct _ _ Hwfpil1 Hwfpil1T) as Hwfpp1.
        pose proof (check_wf_polyprog_tiling_correct _ _ Hwfpil2 Hwfpil2T) as Hwfpp2.
        clear - Hwfpp1 Hwfpp2 Geqdom.
        unfold PolyLang.wf_pprog_tiling in *.
        destruct Hwfpp1 as [_ Hwfpp1].
        destruct Hwfpp2 as [_ Hwfpp2].
        destruct (Geqdom poly_instrs1 poly_instrs2 env1 env2 vars1 vars2 eq_refl eq_refl)
          as (Henv_eq & Hvars_eq & _ & Hrel).
        assert (Hwf1_forall : Forall (PolyLang.wf_pinstr_tiling env1 vars1) poly_instrs1).
        {
          eapply Forall_forall.
          intros pi Hin.
          eapply Hwfpp1; eauto.
        }
        assert (Hwf2_forall : Forall (PolyLang.wf_pinstr_tiling env1 vars1) poly_instrs2).
        {
          rewrite Henv_eq, Hvars_eq.
          eapply Forall_forall.
          intros pi Hin.
          eapply Hwfpp2; eauto.
        }
        eapply wf_pil_tiling_implies_wf_pil_ext_tiling_at.
        -- exact Hwf1_forall.
        -- exact Hwf2_forall.
        -- exact Hrel.
      }
      assert (Hvalid_ext :
        Forall (fun pi_ext =>
          Instr.valid_access_function
            (PolyLang.pi_waccess_ext pi_ext)
            (PolyLang.pi_raccess_ext pi_ext)
            (PolyLang.pi_instr_ext pi_ext))
          (compose_pinstrs_ext_at (length env1) poly_instrs1 poly_instrs2)).
      {
        eapply check_valid_access_correct.
        exact HvaT.
      }
      eapply (validate_pinstrs_ext_implies_permutability
                (compose_pinstrs_ext_at (length env1) poly_instrs1 poly_instrs2)
                env1 envv ipl_ext); eauto.
Qed.

Local Lemma permutable_instance_lists_preserve_semantics:
  forall
    (pp1 : PolyLang.t)
    (poly_instrs1 : list PolyLang.PolyInstr)
    (env1 : list ident)
    (vars1 : list (ident * Ty.t))
    (envv : list Z)
    (st1 st2 : State.t)
    (ipl1 ipl2 sorted_ipl2 : list PolyLang.InstrPoint)
    (ipl_ext : list PolyLang.InstrPoint_ext),
    pp1 = (poly_instrs1, env1, vars1) ->
    PolyLang.flatten_instrs envv poly_instrs1 ipl1 ->
    Permutation ipl2 sorted_ipl2 ->
    Sorted PolyLang.instr_point_sched_le sorted_ipl2 ->
    PolyLang.instr_point_list_semantics sorted_ipl2 st1 st2 ->
    PolyLang.new_of_ext_list ipl_ext = ipl2 ->
    PolyLang.old_of_ext_list ipl_ext = ipl1 ->
    (forall ip1_ext ip2_ext,
      In ip1_ext ipl_ext ->
      In ip2_ext ipl_ext ->
      PolyLang.instr_point_ext_old_sched_lt ip1_ext ip2_ext ->
      PolyLang.instr_point_ext_new_sched_ge ip1_ext ip2_ext ->
      PolyLang.Permutable_ext ip1_ext ip2_ext) ->
    PolyLang.NonAlias st1 ->
    exists st2',
      PolyLang.poly_instance_list_semantics envv pp1 st1 st2' /\
      Instr.State.eq st2 st2'.
Proof.
  intros pp1 poly_instrs1 env1 vars1 envv st1 st2
    ipl1 ipl2 sorted_ipl2 ipl_ext
    Hpp1 Hflat1 Htarget_permutation Htarget_sorted Htarget_semantics
    Hnew Hold Hpermutable Halias.
  destruct
    (PolyLang.permut_implies_ext_permut_new
       ipl_ext ipl2 sorted_ipl2 Htarget_permutation Hnew)
    as (sorted_new_ipl_ext & Hpermut_ext & Hnew_ext).
  remember
    (SelectionSort
       PolyLang.instr_point_ext_old_sched_ltb
       PolyLang.instr_point_ext_old_sched_eqb
       sorted_new_ipl_ext)
    as sorted_old_ipl_ext.
  remember (PolyLang.old_of_ext_list sorted_old_ipl_ext) as sorted_ipl1.
  symmetry in Heqsorted_old_ipl_ext.
  pose proof Heqsorted_old_ipl_ext as Hselection_sort.
  assert
    (Sorted_b PolyLang.instr_point_ext_new_sched_leb sorted_new_ipl_ext)
    as Hsorted_new_ext.
  {
    rewrite <- Hnew_ext in Htarget_sorted.
    eapply PolyLang.sorted_ge_implies_ext_sorted_ge; eauto.
  }
  eapply PolyLang.selection_sort_instance_list_ext_implies_old_normal
    in Hselection_sort.
  eapply PolyLang.selection_sort_instance_list_is_correct in Hselection_sort.
  destruct Hselection_sort as (Hpermut_old_ext & Hsort_old_ext); eauto.
  eapply PolyLang.selection_sort_instance_list_ext_is_stable_permut
    in Heqsorted_old_ipl_ext; eauto.
  assert
    (forall tau1 tau2 : PolyLang.InstrPoint_ext,
      In tau1 sorted_new_ipl_ext ->
      In tau2 sorted_new_ipl_ext ->
      PolyLang.instr_point_ext_old_sched_lt tau1 tau2 ->
      PolyLang.instr_point_ext_new_sched_ge tau1 tau2 ->
      PolyLang.Permutable_ext tau1 tau2)
    as Hpermutable_sorted.
  {
    clear - Hpermutable Hpermut_ext.
    eapply Permutation_sym in Hpermut_ext.
    intros.
    eapply Hpermutable; eauto;
      eapply Permutation_in; eauto.
  }
  pose proof
    (PolyLang.stable_permut_ext_lists_are_equivalent
       sorted_new_ipl_ext sorted_old_ipl_ext
       Hpermutable_sorted Heqsorted_old_ipl_ext st1 Halias)
    as Hequivalent.
  destruct Hequivalent as (Hforward & _).
  rewrite <- Hnew_ext in Htarget_semantics.
  rewrite <- PolyLang.list_ext_old_new_equivalence in Htarget_semantics.
  destruct (Hforward st2 Htarget_semantics) as (st2' & Hsem' & Heq).
  exists st2'. split; trivial.
  rewrite Hpp1.
  eapply PolyLang.PolyPointListSema
    with (sorted_ipl:=sorted_ipl1) (ipl:=ipl1).
  - reflexivity.
  - exact Hflat1.
  - rewrite <- Heqsorted_ipl1 in Hpermut_old_ext.
    remember
      (PolyLang.old_of_ext_list sorted_new_ipl_ext)
      as sorted_new_old_ipl1.
    eapply Permutation_trans in Hpermut_old_ext; eauto.
    clear - Hpermut_ext Hold Heqsorted_new_old_ipl1.
    rewrite <- Hold.
    rewrite Heqsorted_new_old_ipl1.
    eapply PolyLang.ext_permut_implies_permut_old; eauto.
  - rewrite Heqsorted_ipl1.
    clear - Hsort_old_ext.
    eapply PolyLang.sortedb_lexorder_implies_sorted_lexorder; eauto.
  - rewrite Heqsorted_ipl1.
    exact Hsem'.
Qed.

Theorem validate_tiling_correct':
  forall pp1 pp2 env1 env2 poly_instrs1 poly_instrs2 vars1 vars2 envv st1 st2,
    WHEN res <- validate_tiling pp1 pp2 THEN
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
  rename H into Hpp2_sem.
  rename H0 into Hflat2.
  rename H1 into Htarget_permutation.
  rename H2 into Htarget_sorted.
  rename H3 into Htarget_semantics.
  pose proof Hval as G.
  rewrite Hpp1 in G. rewrite Hpp2 in G.
  assert (pis = poly_instrs2) as Hpis.
  { rewrite Hpp2 in Hpp2_sem. inversion Hpp2_sem. reflexivity. }
  rewrite Hpis in Hflat2.
  pose proof
    (validate_tiling_preserve_finite
       poly_instrs1 env1 vars1 poly_instrs2 env2 vars2 envv res G Htrue)
    as Hfinite.
  destruct Hfinite as [_ Hfinite].
  specialize (Hfinite (ex_intro _ ipl2 Hflat2)).
  destruct Hfinite as (ipl1 & Heqipl1).
  pose proof
    (validate_tiling_implies_permutability
       pp1 pp2 env1 env2 envv vars1 vars2 poly_instrs1 poly_instrs2
       ipl1 ipl2 res Hval Hpp1 Hpp2 Htrue Henvlen Heqipl1 Hflat2)
    as Hperm.
  destruct Hperm as (ipl_ext & Hipl2 & Hipl1 & Hpermut).
  eapply permutable_instance_lists_preserve_semantics
    with
      (poly_instrs1:=poly_instrs1)
      (env1:=env1)
      (vars1:=vars1)
      (ipl1:=ipl1)
      (ipl2:=ipl2)
      (sorted_ipl2:=sorted_ipl2)
      (ipl_ext:=ipl_ext); eauto.
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
  destruct (Geqdom poly_instrs1 poly_instrs2 env1 env2 vars1 vars2 eq_refl eq_refl)
    as (Henv_eq0 & Hvars_eq0 & _ & Hrel_pil).
  destruct
    (flatten_instrs_implies_flatten_instrs_ext_at
       env1 vars1 envv poly_instrs1 poly_instrs2
       (compose_pinstrs_ext_at (length env1) poly_instrs1 poly_instrs2)
       ipl1 ipl2)
    as (ipl_ext & Hflat_ext & Hold_ext & Hnew_ext).
  {
    pose proof (check_wf_polyprog_affine_correct _ _ Hwfpil1 Hwfpil1T) as Hwfpp1.
    unfold PolyLang.wf_pprog_affine in Hwfpp1.
    destruct Hwfpp1 as [_ Hwfpp1].
    eapply Forall_forall.
    intros pi Hin.
    eapply PolyLang.wf_pinstr_affine_implies_wf_pinstr_tiling.
    eapply Hwfpp1; eauto.
  }
  {
    pose proof (check_wf_polyprog_affine_correct _ _ Hwfpil2 Hwfpil2T) as Hwfpp2.
    unfold PolyLang.wf_pprog_affine in Hwfpp2.
    destruct Hwfpp2 as [_ Hwfpp2].
    rewrite Henv_eq0, Hvars_eq0.
    eapply Forall_forall.
    intros pi Hin.
    eapply PolyLang.wf_pinstr_affine_implies_wf_pinstr_tiling.
    eapply Hwfpp2; eauto.
  }
  {
    exact Hrel_pil.
  }
  {
    exact Henvlen.
  }
  {
    exact Hflt1.
  }
  {
    exact Hflt2.
  }
  {
    reflexivity.
  }
  exists ipl_ext.
  split.
  - exact Hnew_ext.
  - split.
    + exact Hold_ext.
    + clear Hnew_ext Hold_ext.
      assert (Hwf_ext :
        Forall (PolyLang.wf_pinstr_ext_tiling env1)
          (compose_pinstrs_ext_at (length env1) poly_instrs1 poly_instrs2)).
      {
        pose proof (check_wf_polyprog_affine_correct _ _ Hwfpil1 Hwfpil1T) as Hwfpp1.
        pose proof (check_wf_polyprog_affine_correct _ _ Hwfpil2 Hwfpil2T) as Hwfpp2.
        clear - Hwfpp1 Hwfpp2 Geqdom.
        unfold PolyLang.wf_pprog_affine in *.
        destruct Hwfpp1 as [_ Hwfpp1].
        destruct Hwfpp2 as [_ Hwfpp2].
        destruct (Geqdom poly_instrs1 poly_instrs2 env1 env2 vars1 vars2 eq_refl eq_refl)
          as (Henv_eq & Hvars_eq & _ & Hrel).
        assert (Hwf1_forall : Forall (PolyLang.wf_pinstr_tiling env1 vars1) poly_instrs1).
        {
          eapply Forall_forall.
          intros pi Hin.
          eapply PolyLang.wf_pinstr_affine_implies_wf_pinstr_tiling.
          eapply Hwfpp1; eauto.
        }
        assert (Hwf2_forall : Forall (PolyLang.wf_pinstr_tiling env1 vars1) poly_instrs2).
        {
          rewrite Henv_eq, Hvars_eq.
          eapply Forall_forall.
          intros pi Hin.
          eapply PolyLang.wf_pinstr_affine_implies_wf_pinstr_tiling.
          eapply Hwfpp2; eauto.
        }
        eapply wf_pil_tiling_implies_wf_pil_ext_tiling_at.
        -- exact Hwf1_forall.
        -- exact Hwf2_forall.
        -- exact Hrel.
      }
      assert (Hvalid_ext :
        Forall (fun pi_ext =>
          Instr.valid_access_function
            (PolyLang.pi_waccess_ext pi_ext)
            (PolyLang.pi_raccess_ext pi_ext)
            (PolyLang.pi_instr_ext pi_ext))
          (compose_pinstrs_ext_at (length env1) poly_instrs1 poly_instrs2)).
      {
        eapply check_valid_access_correct.
        exact HvaT.
      }
      eapply (validate_pinstrs_ext_implies_permutability
                (compose_pinstrs_ext_at (length env1) poly_instrs1 poly_instrs2)
                env1 envv ipl_ext); eauto.
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
  rename H into Hpp2_sem.
  rename H0 into Hflat2.
  rename H1 into Htarget_permutation.
  rename H2 into Htarget_sorted.
  rename H3 into Htarget_semantics.
  pose proof Hval as G.
  rewrite Hpp1 in G. rewrite Hpp2 in G.
  assert (pis = poly_instrs2) as Hpis.
  { rewrite Hpp2 in Hpp2_sem. inversion Hpp2_sem. reflexivity. }
  rewrite Hpis in Hflat2.
  pose proof
    (validate_preserve_finite
       poly_instrs1 env1 vars1 poly_instrs2 env2 vars2 envv res G Htrue)
    as Hfinite.
  destruct Hfinite as [_ Hfinite].
  specialize (Hfinite (ex_intro _ ipl2 Hflat2)).
  destruct Hfinite as (ipl1 & Heqipl1).
  pose proof
    (validate_implies_permutability
       pp1 pp2 env1 env2 envv vars1 vars2 poly_instrs1 poly_instrs2
       ipl1 ipl2 res Hval Hpp1 Hpp2 Htrue Henvlen Heqipl1 Hflat2)
    as Hperm.
  destruct Hperm as (ipl_ext & Hipl2 & Hipl1 & Hpermut).
  eapply permutable_instance_lists_preserve_semantics
    with
      (poly_instrs1:=poly_instrs1)
      (env1:=env1)
      (vars1:=vars1)
      (ipl1:=ipl1)
      (ipl2:=ipl2)
      (sorted_ipl2:=sorted_ipl2)
      (ipl_ext:=ipl_ext); eauto.
Qed.

Lemma validate_preserve_wf_pprog: 
  forall pp1 pp2,
    WHEN res <- validate pp1 pp2 THEN 
    res = true ->
    PolyLang.wf_pprog_affine pp1 /\ PolyLang.wf_pprog_affine pp2. 
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
  split; eapply check_wf_polyprog_affine_correct; eauto.
Qed.

(** Lift a correctness theorem for a fixed parameter environment to complete
    program semantics.  Equal domains provide the shared context and variable
    declarations; [InitEnv] supplies the environment length required by the
    polyhedral theorem. *)
Local Lemma lift_poly_instance_correct :
  forall pis1 env1 vars1 pis2 env2 vars2 st1 st2,
    PolyLang.eqdom_pprog
      (pis1, env1, vars1) (pis2, env2, vars2) ->
    (forall envv,
       length env1 = length envv ->
       Instr.NonAlias st1 ->
       PolyLang.poly_instance_list_semantics
         envv (pis2, env2, vars2) st1 st2 ->
       exists st2',
         PolyLang.poly_instance_list_semantics
           envv (pis1, env1, vars1) st1 st2' /\
         State.eq st2 st2') ->
    PolyLang.instance_list_semantics (pis2, env2, vars2) st1 st2 ->
    exists st2',
      PolyLang.instance_list_semantics (pis1, env1, vars1) st1 st2' /\
      State.eq st2 st2'.
Proof.
  intros pis1 env1 vars1 pis2 env2 vars2 st1 st2
         Heqdom Hpoly_correct Htarget.
  inversion Htarget as
    [pprog pis varctxt vars envv st1' st2'
       Hpprog Hcompat Hnonalias Hinit Hpoly]; subst.
  inversion Hpprog; subst pis varctxt vars.
  destruct
    (Heqdom pis1 pis2 env1 env2 vars1 vars2 eq_refl eq_refl)
    as [Henv [Hvars [_ _]]].
  assert (Henvlen : length env1 = length envv).
  {
    rewrite Henv.
    eapply Instr.init_env_samelen.
    exact Hinit.
  }
  destruct (Hpoly_correct envv Henvlen Hnonalias Hpoly)
    as [st_source [Hsource Heq_source]].
  exists st_source.
  split.
  - eapply PolyLang.PIPSemaIntro
      with (pis:=pis1) (varctxt:=env1) (vars:=vars1) (envv:=envv).
    + reflexivity.
    + rewrite Hvars. exact Hcompat.
    + exact Hnonalias.
    + rewrite Henv. exact Hinit.
    + exact Hsource.
  - exact Heq_source.
Qed.

Theorem validate_correct: 
  forall pp1 pp2 st1 st2, 
    WHEN res <- validate pp1 pp2 THEN 
    res = true ->
    PolyLang.instance_list_semantics pp2 st1 st2 -> 
    exists st2',
    PolyLang.instance_list_semantics pp1 st1 st2' /\ State.eq st2 st2'.
Proof.
  intros pp1 pp2 st1 st2 res Hval Htrue Htarget.
  destruct pp1 as [[pis1 env1] vars1].
  destruct pp2 as [[pis2 env2] vars2].
  pose proof
    (validate_implies_correspondence
       (pis1, env1, vars1) (pis2, env2, vars2)
       env1 env2 vars1 vars2 pis1 pis2
       res Hval eq_refl eq_refl Htrue)
    as Heqdom.
  eapply lift_poly_instance_correct; [exact Heqdom| |exact Htarget].
  intros envv Henvlen Hnonalias Hpoly.
  eapply validate_correct'
    with (env1:=env1) (env2:=env2)
         (poly_instrs1:=pis1) (poly_instrs2:=pis2)
         (vars1:=vars1) (vars2:=vars2); eauto.
Qed.

Theorem validate_tiling_correct:
  forall pp1 pp2 st1 st2,
    WHEN res <- validate_tiling pp1 pp2 THEN
    res = true ->
    PolyLang.instance_list_semantics pp2 st1 st2 ->
    exists st2',
      PolyLang.instance_list_semantics pp1 st1 st2' /\ State.eq st2 st2'.
Proof.
  intros pp1 pp2 st1 st2 res Hval Htrue Htarget.
  destruct pp1 as [[pis1 env1] vars1].
  destruct pp2 as [[pis2 env2] vars2].
  pose proof
    (validate_tiling_implies_correspondence
       (pis1, env1, vars1) (pis2, env2, vars2)
       env1 env2 vars1 vars2 pis1 pis2
       res Hval eq_refl eq_refl Htrue)
    as Heqdom.
  eapply lift_poly_instance_correct; [exact Heqdom| |exact Htarget].
  intros envv Henvlen Hnonalias Hpoly.
  eapply validate_tiling_correct'
    with (env1:=env1) (env2:=env2)
         (poly_instrs1:=pis1) (poly_instrs2:=pis2)
         (vars1:=vars1) (vars2:=vars2); eauto.
Qed.

(** The direct permutable-band checker reasons about integer iteration
    points.  VPL's emptiness check is over rationals, so canonicalize the
    final guard intersection with [VplCanonizerZ] before asking VPL whether
    it is empty.  Construct the conjunction with [poly_inter_pure] so that
    only the final integer polyhedron is canonicalized.  Unlike the ordinary
    affine checker, this path normalizes before its first emptiness query. *)

Definition validate_lt_ge_pair_integer
    (pol_lt pol_ge sameloc_enveq_indom_pol: polyhedron) :=
  let combined :=
    poly_inter_pure
      (poly_inter_pure pol_lt sameloc_enveq_indom_pol)
      pol_ge in
  BIND integer_pol <-
    VplCanonizerZ.canonize combined -;
  BIND isbot <- isBottom integer_pol -;
  pure isbot.

Lemma validate_lt_ge_pair_integer_correct:
  forall pol_old_lt pol_new_ge sameloc_enveq_indom_pol p1 p2,
    WHEN res <-
      validate_lt_ge_pair_integer
        pol_old_lt pol_new_ge sameloc_enveq_indom_pol
    THEN
    res = true ->
    in_poly (p1 ++ p2) sameloc_enveq_indom_pol = true ->
    in_poly (p1 ++ p2) pol_old_lt = true ->
    in_poly (p1 ++ p2) pol_new_ge = true ->
    False.
Proof.
  intros pol_old_lt pol_new_ge sameloc_enveq_indom_pol p1 p2
         res Hval Hres Hin Hlt Hge.
  unfold validate_lt_ge_pair_integer in Hval.
  bind_imp_destruct Hval integer_pol Hinteger.
  bind_imp_destruct Hval isbot Hisbot.
  subst res.
  apply mayReturn_pure in Hval.
  subst isbot.
  apply isBottom_correct_1 in Hisbot.
  specialize (Hisbot (p1 ++ p2)).
  rewrite VplCanonizerZ.canonize_correct in Hisbot; [|exact Hinteger].
  repeat rewrite poly_inter_pure_def in Hisbot.
  rewrite Hlt, Hin, Hge in Hisbot.
  discriminate.
Qed.

Definition validate_two_accesses_helper_integer
    (old_sched_lt_polys new_sched_ge_polys: list polyhedron)
    (sameloc_enveq_indom_pol: polyhedron) :=
  forallb_imp
    (fun pol_lt =>
       forallb_imp
         (fun pol_ge =>
            validate_lt_ge_pair_integer
              pol_lt pol_ge sameloc_enveq_indom_pol)
         new_sched_ge_polys)
    old_sched_lt_polys.

Lemma validate_two_accesses_helper_integer_correct:
  forall pols_old_lt pols_new_ge sameloc_enveq_indom_pol p1 p2,
    WHEN res <-
      validate_two_accesses_helper_integer
        pols_old_lt pols_new_ge sameloc_enveq_indom_pol
    THEN
    res = true ->
    in_poly (p1 ++ p2) sameloc_enveq_indom_pol = true ->
    Exists
      (fun pol => in_poly (p1 ++ p2) pol = true)
      pols_old_lt ->
    Exists
      (fun pol => in_poly (p1 ++ p2) pol = true)
      pols_new_ge ->
    False.
Proof.
  intros pols_old_lt pols_new_ge sameloc_enveq_indom_pol p1 p2
         res Hval Hres Hin Hlt Hge.
  subst res.
  apply Exists_exists in Hlt.
  destruct Hlt as [pol_lt [Hin_lt Hsat_lt]].
  apply Exists_exists in Hge.
  destruct Hge as [pol_ge [Hin_ge Hsat_ge]].
  pose proof
    (forallb_imp_true_forall
       (fun pol_lt =>
          forallb_imp
            (fun pol_ge =>
               validate_lt_ge_pair_integer
                 pol_lt pol_ge sameloc_enveq_indom_pol)
            pols_new_ge)
       pols_old_lt Hval pol_lt Hin_lt)
    as Hchecks_ge.
  pose proof
    (forallb_imp_true_forall
       (fun pol_ge =>
          validate_lt_ge_pair_integer
            pol_lt pol_ge sameloc_enveq_indom_pol)
       pols_new_ge Hchecks_ge pol_ge Hin_ge)
    as Hpair.
  eapply
    (validate_lt_ge_pair_integer_correct
       pol_lt pol_ge sameloc_enveq_indom_pol p1 p2
       true Hpair eq_refl);
    eauto.
Qed.

Definition validate_two_accesses_integer
    (a1 a2: AccessFunction)
    (tf1 tf2: AffineFunction)
    (env_eq_in_dom_poly: polyhedron)
    (old_sched_lt_polys new_sched_ge_polys: list polyhedron)
    (dim1 dim2: nat) :=
  let '(id1, loc1) := a1 in
  let '(id2, loc2) := a2 in
  if negb (Pos.eqb id1 id2) then pure true else
  let sameloc :=
    make_poly_eq
      (snd (compose_access_function_at dim1 a1 tf1))
      (snd (compose_access_function_at dim2 a2 tf2))
      dim1 dim2 [] in
  BIND sameloc_enveq_indom_pol <-
    poly_inter sameloc env_eq_in_dom_poly -;
  validate_two_accesses_helper_integer
    old_sched_lt_polys new_sched_ge_polys sameloc_enveq_indom_pol.

Lemma validate_two_accesses_integer_implies_permut_no_collision:
  forall pols_old_lt pols_new_ge a1 a2 tf1 tf2 p1 p2 pol_dom
         dom_dim1 dom_dim2,
    WHEN res <-
      validate_two_accesses_integer
        a1 a2 tf1 tf2 pol_dom
        pols_old_lt pols_new_ge dom_dim1 dom_dim2
    THEN
    res = true ->
    length p1 = dom_dim1 ->
    length p2 = dom_dim2 ->
    exact_listzzs_cols dom_dim1 tf1 ->
    exact_listzzs_cols dom_dim2 tf2 ->
    access_matches_tf tf1 a1 ->
    access_matches_tf tf2 a2 ->
    in_poly (p1 ++ p2) pol_dom = true ->
    Exists (fun pol => in_poly (p1 ++ p2) pol = true) pols_old_lt ->
    Exists (fun pol => in_poly (p1 ++ p2) pol = true) pols_new_ge ->
    cell_neq
      (exact_cell a1 (affine_product tf1 p1))
      (exact_cell a2 (affine_product tf2 p2)).
Proof.
  intros.
  intros res Hval Hres Hlen1 Hlen2 Hwf1 Hwf2
         Hacc1 Hacc2 Hin Hlt Hge.
  unfold validate_two_accesses_integer in Hval.
  destruct a1 as (id1, func1) eqn:Ha1.
  destruct a2 as (id2, func2) eqn:Ha2.
  destruct (Pos.eqb id1 id2) eqn:Hideq; simpls.
  {
    eapply Pos.eqb_eq in Hideq; subst; simpls.
    bind_imp_destruct Hval sameloc_enveq_indom_pol Hsameloc.
    eapply poly_inter_def with (p:=(p1 ++ p2)) in Hsameloc.
    right; simpls. intro.
    eapply validate_two_accesses_helper_integer_correct
      with (p1:=p1) (p2:=p2)
           (pols_old_lt:=pols_old_lt)
           (pols_new_ge:=pols_new_ge)
           (sameloc_enveq_indom_pol:=sameloc_enveq_indom_pol);
      trivial; trivial.
    rewrite Hsameloc.
    rewrite poly_inter_pure_def.
    eapply andb_true_iff. split; trivial.
    eapply make_poly_eq_correct_true; eauto.
    - change
        (exact_listzzs_cols
           (length p1)
           (snd (compose_access_function_at (length p1) (id2, func1) tf1))).
      eapply compose_access_function_at_exact_cols; eauto.
    - change
        ((affine_product
            (snd (compose_access_function_at (length p1) (id2, func1) tf1))
            p1)
         =v=
         (affine_product
            (snd (compose_access_function_at (length p2) (id2, func2) tf2))
            p2)).
      rewrite
        (compose_access_function_at_correct
           (length p1) (id2, func1) tf1 p1); eauto.
      rewrite
        (compose_access_function_at_correct
           (length p2) (id2, func2) tf2 p2); eauto.
  }
  {
    eapply Pos.eqb_neq in Hideq.
    firstorder.
  }
Qed.

Local Lemma validate_two_accesses_integer_checker_sound :
  access_pair_checker_sound validate_two_accesses_integer.
Proof.
  exact validate_two_accesses_integer_implies_permut_no_collision.
Qed.

Definition validate_two_instrs_under_guards_integer
    (pi1 pi2: PolyLang.PolyInstr_ext)
    (env_dim: nat)
    (order_guards bad_guards: list polyhedron) :=
  let iter_dim1 := pi1.(PolyLang.pi_depth_ext) in
  let iter_dim2 := pi2.(PolyLang.pi_depth_ext) in
  let dom_dim1 := (env_dim + iter_dim1)%nat in
  let dom_dim2 := (env_dim + iter_dim2)%nat in
  let env_eq_poly := make_poly_env_eq env_dim iter_dim1 iter_dim2 in
  BIND in_domain_poly <-
    poly_product
      pi1.(PolyLang.pi_poly_ext)
      pi2.(PolyLang.pi_poly_ext)
      dom_dim1 dom_dim2 -;
  BIND env_eq_in_domain <- poly_inter env_eq_poly in_domain_poly -;
  BIND ww <- forallb_imp (
    fun waccess1 => forallb_imp (fun waccess2 =>
      validate_two_accesses_integer
        waccess1 waccess2
        pi1.(PolyLang.pi_access_transformation_ext)
        pi2.(PolyLang.pi_access_transformation_ext)
        env_eq_in_domain order_guards bad_guards dom_dim1 dom_dim2
    ) pi2.(PolyLang.pi_waccess_ext)
  ) pi1.(PolyLang.pi_waccess_ext) -;
  BIND wr <- forallb_imp (
    fun waccess1 => forallb_imp (fun raccess2 =>
      validate_two_accesses_integer
        waccess1 raccess2
        pi1.(PolyLang.pi_access_transformation_ext)
        pi2.(PolyLang.pi_access_transformation_ext)
        env_eq_in_domain order_guards bad_guards dom_dim1 dom_dim2
    ) pi2.(PolyLang.pi_raccess_ext)
  ) pi1.(PolyLang.pi_waccess_ext) -;
  BIND rw <- forallb_imp (
    fun raccess1 => forallb_imp (fun waccess2 =>
      validate_two_accesses_integer
        raccess1 waccess2
        pi1.(PolyLang.pi_access_transformation_ext)
        pi2.(PolyLang.pi_access_transformation_ext)
        env_eq_in_domain order_guards bad_guards dom_dim1 dom_dim2
    ) pi2.(PolyLang.pi_waccess_ext)
  ) pi1.(PolyLang.pi_raccess_ext) -;
  pure (ww && wr && rw).

Lemma validate_two_instrs_under_guards_integer_implies_no_write_collision:
  forall pi1_ext pi2_ext env nth1 nth2 envv ipl1_ext ipl2_ext
         order_guards bad_guards,
    WHEN res <-
      validate_two_instrs_under_guards_integer
        pi1_ext pi2_ext (length env) order_guards bad_guards
    THEN
    res = true ->
    PolyLang.wf_pinstr_ext_tiling env pi1_ext ->
    PolyLang.wf_pinstr_ext_tiling env pi2_ext ->
    length env = length envv ->
    PolyLang.flatten_instr_nth_ext envv nth1 pi1_ext ipl1_ext ->
    PolyLang.flatten_instr_nth_ext envv nth2 pi2_ext ipl2_ext ->
    forall ip1_ext ip2_ext,
      In ip1_ext ipl1_ext ->
      In ip2_ext ipl2_ext ->
      Exists
        (fun pol =>
           in_poly
             (PolyLang.ip_index_ext ip1_ext ++
              PolyLang.ip_index_ext ip2_ext) pol = true)
        order_guards ->
      Exists
        (fun pol =>
           in_poly
             (PolyLang.ip_index_ext ip1_ext ++
              PolyLang.ip_index_ext ip2_ext) pol = true)
        bad_guards ->
      no_write_collision
        pi1_ext.(PolyLang.pi_waccess_ext)
        pi2_ext.(PolyLang.pi_waccess_ext)
        pi1_ext.(PolyLang.pi_raccess_ext)
        pi2_ext.(PolyLang.pi_raccess_ext)
        ip1_ext ip2_ext.
Proof.
  intros pi1_ext pi2_ext env nth1 nth2 envv ipl1_ext ipl2_ext
    order_guards bad_guards res Hval Hres Hwf1 Hwf2 Henvlen
    Hext1 Hext2 ip1 ip2 Hip1 Hip2 Horder Hbad.
  unfold validate_two_instrs_under_guards_integer in Hval.
  bind_imp_destruct Hval in_domain_poly Hdomain.
  bind_imp_destruct Hval env_eq_in_domain Henv.
  bind_imp_destruct Hval ww Hww.
  bind_imp_destruct Hval wr Hwr.
  bind_imp_destruct Hval rw Hrw.
  apply mayReturn_pure in Hval.
  rewrite Hres in Hval.
  do 2 rewrite andb_true_iff in Hval.
  destruct Hval as ((HwwT & HwrT) & HrwT).
  subst ww wr rw.
  eapply
    (validated_access_checks_imply_no_write_collision
       validate_two_accesses_integer
       validate_two_accesses_integer_checker_sound)
    with
      (in_domain_poly:=in_domain_poly)
      (env_eq_in_domain:=env_eq_in_domain)
      (order_guards:=order_guards)
      (bad_guards:=bad_guards); eauto.
Qed.

End AffineValidator.

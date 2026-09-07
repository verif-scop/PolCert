Require Import ZArith.
Require Import Lia.
Require Import List.
Require Import Bool.
Require Import String.
Require Import Base.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.

Require Import AffineValidator.
Require Import Linalg.
Require Import ListExt.
Require Import Misc.
Require Import PolyBase.
Require Import PointWitness.
Require Import Result.
Require Import PolIRs.

Module ParallelValidator (PolIRs : POLIRS).

Module PolyLang := PolIRs.PolyLang.
Module ILSema := PolyLang.ILSema.
Module Instr := PolIRs.Instr.
Module AffineCore := AffineValidator PolIRs.

(** * Proof map

    A certificate for dimension [d] states that instances with the same
    environment and canonical schedule prefix, but different schedule
    coordinates at [d], commute.  All statement schedules are padded to their
    program-wide maximum width, matching the coordinates introduced before
    code generation.  The checker expresses a violation as an affine schedule
    reversal from [prefix(d) ++ [d]] to [prefix(d)].  Thus only instances
    in the same schedule prefix can form a reversed pair; sequentially
    ordered prefixes do not impose an extra independence obligation.
    Affine-validator soundness
    yields [parallel_safe_dim_pointwise]; the historical flattened-list
    property [parallel_safe_dim] follows as a compatibility corollary. *)

Record parallel_plan := {
  target_dim : nat
}.

Record parallel_cert := {
  certified_dim : nat
}.

(** A local hint names statements as well as a schedule coordinate.  Its
    lowering reserves a sequential and a parallel slot for each original
    coordinate.  Only selected statements vary in the parallel slot.

    This is a schedule proposal, not an unchecked parallel certificate:
    affine validation must establish its order preservation before the
    existing dimension validator and code-generation theorem apply. *)
Record scoped_parallel_plan := {
  scoped_dim : nat;
  scoped_statements : list nat
}.

Definition scoped_parallel_memberb
    (plans : list scoped_parallel_plan) (stmt dim : nat) : bool :=
  existsb (fun plan => Nat.eqb dim plan.(scoped_dim) &&
    existsb (Nat.eqb stmt) plan.(scoped_statements)) plans.

Definition scoped_parallel_row
    (selected : bool) (zero row : list Z * Z) : list (list Z * Z) :=
  if selected then [zero; row] else [row; zero].

Fixpoint scoped_parallel_rows_from
    (plans : list scoped_parallel_plan) (stmt dim : nat)
    (zero : list Z * Z) (rows : list (list Z * Z))
    : list (list Z * Z) :=
  match rows with
  | [] => []
  | row :: tail =>
      scoped_parallel_row (scoped_parallel_memberb plans stmt dim) zero row ++
      scoped_parallel_rows_from plans stmt (S dim) zero tail
  end.

Lemma scoped_parallel_rows_length :
  forall rows plans stmt dim zero,
    Datatypes.length (scoped_parallel_rows_from plans stmt dim zero rows) =
    (2 * Datatypes.length rows)%nat.
Proof.
  induction rows as [|row rows IH]; intros; simpl; [reflexivity|].
  rewrite app_length, IH.
  unfold scoped_parallel_row.
  destruct (scoped_parallel_memberb plans stmt dim); simpl; lia.
Qed.

Lemma scoped_parallel_rows_parallel_slot :
  forall rows plans stmt dim zero k row,
    nth_error rows k = Some row ->
    nth_error (scoped_parallel_rows_from plans stmt dim zero rows) (2*k+1) =
      Some (if scoped_parallel_memberb plans stmt (dim+k) then row else zero).
Proof.
  induction rows as [|head rows IH]; intros plans stmt dim zero k row Hnth;
    destruct k; simpl in Hnth; try discriminate.
  - inversion Hnth; subst. simpl.
    replace (dim+0)%nat with dim by lia.
    unfold scoped_parallel_row.
    destruct (scoped_parallel_memberb plans stmt dim); reflexivity.
  - replace (2 * S k + 1)%nat with (S (S (2*k+1))) by lia.
    simpl scoped_parallel_rows_from.
    unfold scoped_parallel_row.
    pose proof (IH plans stmt (S dim) zero k row Hnth) as Htail.
    replace (dim+S k)%nat with (S dim+k)%nat by lia.
    destruct (scoped_parallel_memberb plans stmt dim); simpl; exact Htail.
Qed.

Lemma scoped_parallel_rows_sequential_slot :
  forall rows plans stmt dim zero k row,
    nth_error rows k = Some row ->
    nth_error (scoped_parallel_rows_from plans stmt dim zero rows) (2*k) =
      Some (if scoped_parallel_memberb plans stmt (dim+k) then zero else row).
Proof.
  induction rows as [|head rows IH]; intros plans stmt dim zero k row Hnth;
    destruct k; simpl in Hnth; try discriminate.
  - inversion Hnth; subst. simpl.
    replace (dim+0)%nat with dim by lia.
    unfold scoped_parallel_row.
    destruct (scoped_parallel_memberb plans stmt dim); reflexivity.
  - replace (2 * S k)%nat with (S (S (2*k))) by lia.
    simpl scoped_parallel_rows_from.
    unfold scoped_parallel_row.
    pose proof (IH plans stmt (S dim) zero k row Hnth) as Htail.
    replace (dim+S k)%nat with (S dim+k)%nat by lia.
    destruct (scoped_parallel_memberb plans stmt dim); simpl; exact Htail.
Qed.

Definition pprog_pis (pp : PolyLang.t) : list PolyLang.PolyInstr :=
  let '(pis, _, _) := pp in pis.

Definition pprog_varctxt (pp : PolyLang.t) : list Instr.ident :=
  let '(_, varctxt, _) := pp in varctxt.

Definition current_coord_schedule_row
  (env_dim depth i : nat) : list Z * Z :=
  (resize (env_dim + depth) (V0 (env_dim + i) ++ [1%Z]), 0%Z).


Definition current_coord_prefix_schedule
  (env_dim depth d : nat) : list (list Z * Z) :=
  map (current_coord_schedule_row env_dim depth) (seq 0 d).

Definition schedule_width_of_pis (pis : list PolyLang.PolyInstr) : nat :=
  list_max
    (List.map (fun pi => Datatypes.length pi.(PolyLang.pi_schedule)) pis).

Definition schedule_width (pp : PolyLang.t) : nat :=
  schedule_width_of_pis (pprog_pis pp).

Definition padded_pi_schedule
  (env_dim width : nat) (pi : PolyLang.PolyInstr) : list (list Z * Z) :=
  PolyLang.pad_schedule_to_len
    (env_dim + pi.(PolyLang.pi_depth)) width pi.(PolyLang.pi_schedule).

Definition schedule_coord_old_schedule
  (env_dim width d : nat) (pi : PolyLang.PolyInstr) : list (list Z * Z) :=
  firstn d (padded_pi_schedule env_dim width pi) ++
  [nth d (padded_pi_schedule env_dim width pi)
     (PolyLang.zero_affine_function (env_dim + pi.(PolyLang.pi_depth)))].

Definition schedule_coord_prefix_schedule
  (env_dim width d : nat) (pi : PolyLang.PolyInstr) : list (list Z * Z) :=
  firstn d (padded_pi_schedule env_dim width pi).

Definition parallel_old_pi
  (env_dim width d : nat) (pi : PolyLang.PolyInstr) : PolyLang.PolyInstr :=
  {|
    PolyLang.pi_depth := pi.(PolyLang.pi_depth);
    PolyLang.pi_instr := pi.(PolyLang.pi_instr);
    PolyLang.pi_poly := pi.(PolyLang.pi_poly);
    PolyLang.pi_schedule :=
      schedule_coord_old_schedule env_dim width d pi;
    PolyLang.pi_point_witness := pi.(PolyLang.pi_point_witness);
    PolyLang.pi_transformation := pi.(PolyLang.pi_transformation);
    PolyLang.pi_access_transformation := pi.(PolyLang.pi_access_transformation);
    PolyLang.pi_waccess := pi.(PolyLang.pi_waccess);
    PolyLang.pi_raccess := pi.(PolyLang.pi_raccess)
  |}.

Definition parallel_new_pi
  (env_dim width d : nat) (pi : PolyLang.PolyInstr) : PolyLang.PolyInstr :=
  {|
    PolyLang.pi_depth := pi.(PolyLang.pi_depth);
    PolyLang.pi_instr := pi.(PolyLang.pi_instr);
    PolyLang.pi_poly := pi.(PolyLang.pi_poly);
    PolyLang.pi_schedule :=
      schedule_coord_prefix_schedule env_dim width d pi;
    PolyLang.pi_point_witness := pi.(PolyLang.pi_point_witness);
    PolyLang.pi_transformation := pi.(PolyLang.pi_transformation);
    PolyLang.pi_access_transformation := pi.(PolyLang.pi_access_transformation);
    PolyLang.pi_waccess := pi.(PolyLang.pi_waccess);
    PolyLang.pi_raccess := pi.(PolyLang.pi_raccess)
  |}.

Definition parallel_old_pprog
  (pp : PolyLang.t) (d : nat) : PolyLang.t :=
  let '(pis, varctxt, vars) := pp in
  let width := schedule_width_of_pis pis in
  ((List.map (parallel_old_pi (Datatypes.length varctxt) width d) pis,
    varctxt), vars).

Definition parallel_new_pprog
  (pp : PolyLang.t) (d : nat) : PolyLang.t :=
  let '(pis, varctxt, vars) := pp in
  let width := schedule_width_of_pis pis in
  ((List.map (parallel_new_pi (Datatypes.length varctxt) width d) pis,
    varctxt), vars).

Local Definition parallel_point_ext
  (pp : PolyLang.t) (d : nat)
  (pi : PolyLang.PolyInstr) (tau : PolyLang.InstrPoint) :
  PolyLang.InstrPoint_ext :=
  let env_dim := Datatypes.length (pprog_varctxt pp) in
  let width := schedule_width pp in
  let old_pi := parallel_old_pi env_dim width d pi in
  {|
    PolyLang.ip_nth_ext := tau.(PolyLang.ip_nth);
    PolyLang.ip_index_ext := tau.(PolyLang.ip_index);
    PolyLang.ip_transformation_ext := tau.(PolyLang.ip_transformation);
    PolyLang.ip_access_transformation_ext :=
      PolyLang.current_access_transformation_at env_dim old_pi;
    PolyLang.ip_time_stamp1_ext :=
      firstn d (resize width tau.(PolyLang.ip_time_stamp)) ++
      [nth d (resize width tau.(PolyLang.ip_time_stamp)) 0%Z];
    PolyLang.ip_time_stamp2_ext :=
      firstn d (resize width tau.(PolyLang.ip_time_stamp));
    PolyLang.ip_instruction_ext := tau.(PolyLang.ip_instruction);
    PolyLang.ip_depth_ext := tau.(PolyLang.ip_depth)
  |}.

Local Definition parallel_pinstr_ext
    (pp : PolyLang.t) (d : nat) (pi : PolyLang.PolyInstr) :
    PolyLang.PolyInstr_ext :=
  let env_dim := Datatypes.length (pprog_varctxt pp) in
  let width := schedule_width pp in
  AffineCore.compose_pinstr_ext_at env_dim
    (parallel_old_pi env_dim width d pi)
    (parallel_new_pi env_dim width d pi).

Local Definition parallel_pinstrs_ext
    (pp : PolyLang.t) (d : nat) : list PolyLang.PolyInstr_ext :=
  let '((pis, varctxt), _) := pp in
  let env_dim := Datatypes.length varctxt in
  let width := schedule_width_of_pis pis in
  AffineCore.compose_pinstrs_ext_at env_dim
    (List.map (parallel_old_pi env_dim width d) pis)
    (List.map (parallel_new_pi env_dim width d) pis).

Definition check_current_view_pinstrb (pi : PolyLang.PolyInstr) : bool :=
  match pi.(PolyLang.pi_point_witness) with
  | PSWIdentity d' => Nat.eqb d' pi.(PolyLang.pi_depth)
  | _ => false
  end.

Definition check_current_view_pprogb (pp : PolyLang.t) : bool :=
  forallb check_current_view_pinstrb (pprog_pis pp).

Definition all_pinstrs_cover_dimb (d : nat) (pp : PolyLang.t) : bool :=
  forallb (fun pi => Nat.ltb d pi.(PolyLang.pi_depth)) (pprog_pis pp).

Definition env_dim_of (ip : PolyLang.InstrPoint) : nat :=
  Nat.sub (Datatypes.length ip.(PolyLang.ip_index)) ip.(PolyLang.ip_depth).

Definition env_prefix_of (ip : PolyLang.InstrPoint) : list Z :=
  firstn (env_dim_of ip) ip.(PolyLang.ip_index).

Definition current_coords_of (ip : PolyLang.InstrPoint) : list Z :=
  skipn (env_dim_of ip) ip.(PolyLang.ip_index).

Definition same_env_of (ip1 ip2 : PolyLang.InstrPoint) : Prop :=
  env_prefix_of ip1 = env_prefix_of ip2.

Definition padded_timestamp
  (pp : PolyLang.t) (ip : PolyLang.InstrPoint) : list Z :=
  resize (schedule_width pp) ip.(PolyLang.ip_time_stamp).

Definition same_prefix_before
  (pp : PolyLang.t) (d : nat) (ip1 ip2 : PolyLang.InstrPoint) : Prop :=
  firstn d (padded_timestamp pp ip1) =
  firstn d (padded_timestamp pp ip2).

Definition different_dim_at
  (pp : PolyLang.t) (d : nat) (ip1 ip2 : PolyLang.InstrPoint) : Prop :=
  nth_error (padded_timestamp pp ip1) d <>
  nth_error (padded_timestamp pp ip2) d.

Definition same_parallel_slice
  (pp : PolyLang.t) (d : nat) (ip1 ip2 : PolyLang.InstrPoint) : Prop :=
  same_env_of ip1 ip2 /\
  same_prefix_before pp d ip1 ip2 /\
  different_dim_at pp d ip1 ip2.



Lemma permutable_eq_except_sched :
  forall ip1 ip1' ip2 ip2',
    PolyLang.eq_except_sched ip1 ip1' ->
    PolyLang.eq_except_sched ip2 ip2' ->
    ILSema.Permutable ip1 ip2 ->
    ILSema.Permutable ip1' ip2'.
Proof.
  exact ILSema.permutable_eq_except_sched.
Qed.

(** * Declarative doall property *)

Definition parallel_safe_dim (pp : PolyLang.t) (d : nat) : Prop :=
  forall envv ipl tau1 tau2,
    Datatypes.length envv = Datatypes.length (pprog_varctxt pp) ->
    PolyLang.flatten_instrs envv (pprog_pis pp) ipl ->
    In tau1 ipl ->
    In tau2 ipl ->
    same_parallel_slice pp d tau1 tau2 ->
    ILSema.Permutable tau1 tau2.

Definition parallel_safe_dim_pointwise (pp : PolyLang.t) (d : nat) : Prop :=
  forall tau1 tau2 pi1 pi2,
    nth_error (pprog_pis pp) tau1.(PolyLang.ip_nth) = Some pi1 ->
    nth_error (pprog_pis pp) tau2.(PolyLang.ip_nth) = Some pi2 ->
    PolyLang.belongs_to tau1 pi1 ->
    PolyLang.belongs_to tau2 pi2 ->
    Datatypes.length tau1.(PolyLang.ip_index) =
      (Datatypes.length (pprog_varctxt pp) + pi1.(PolyLang.pi_depth))%nat ->
    Datatypes.length tau2.(PolyLang.ip_index) =
      (Datatypes.length (pprog_varctxt pp) + pi2.(PolyLang.pi_depth))%nat ->
    same_parallel_slice pp d tau1 tau2 ->
    ILSema.Permutable tau1 tau2.

Definition parallel_cert_sound
  (pp : PolyLang.t) (cert : parallel_cert) : Prop :=
  parallel_safe_dim pp cert.(certified_dim).

Definition parallel_cert_pointwise_sound
  (pp : PolyLang.t) (cert : parallel_cert) : Prop :=
  parallel_safe_dim_pointwise pp cert.(certified_dim).




Lemma schedule_width_ge_pinstr :
  forall pis varctxt vars pi,
    In pi pis ->
    (Datatypes.length pi.(PolyLang.pi_schedule) <=
     schedule_width ((pis, varctxt), vars))%nat.
Proof.
  intros pis varctxt vars pi Hin.
  unfold schedule_width, schedule_width_of_pis, pprog_pis.
  simpl.
  apply list_max_ge.
  rewrite in_map_iff.
  exists pi.
  split; [reflexivity | exact Hin].
Qed.

Lemma padded_pi_schedule_length :
  forall env_dim width pi,
    (Datatypes.length pi.(PolyLang.pi_schedule) <= width)%nat ->
    Datatypes.length (padded_pi_schedule env_dim width pi) = width.
Proof.
  intros env_dim width pi Hlen.
  unfold padded_pi_schedule, PolyLang.pad_schedule_to_len.
  rewrite app_length, repeat_length.
  lia.
Qed.











Lemma check_current_view_pinstrb_sound :
  forall pi,
    check_current_view_pinstrb pi = true ->
    pi.(PolyLang.pi_point_witness) = PSWIdentity pi.(PolyLang.pi_depth).
Proof.
  intros pi Hcheck.
  unfold check_current_view_pinstrb in Hcheck.
  destruct (PolyLang.pi_point_witness pi); simpl in Hcheck; try discriminate.
  apply Nat.eqb_eq in Hcheck.
  subst.
  reflexivity.
Qed.






Lemma flatten_instrs_member_inv :
  forall envv pis ipl ip,
    PolyLang.flatten_instrs envv pis ipl ->
    In ip ipl ->
    exists pi,
      nth_error pis ip.(PolyLang.ip_nth) = Some pi /\
      PolyLang.belongs_to ip pi /\
      Datatypes.length ip.(PolyLang.ip_index) =
        (Datatypes.length envv + pi.(PolyLang.pi_depth))%nat.
Proof.
  intros envv pis ipl ip Hflat Hin.
  destruct Hflat as [_ [Hmem _]].
  specialize (Hmem ip).
  destruct ((proj1 Hmem) Hin) as [pi [Hnth [_ [Hbel Hlen]]]].
  exists pi.
  split; [exact Hnth |].
  split; [exact Hbel | exact Hlen].
Qed.


Lemma dot_product_select_coord :
  forall cols n xs,
    (S n <= cols)%nat ->
    dot_product (resize cols (V0 n ++ [1%Z])) xs = nth n xs 0%Z.
Proof.
  exact LinalgExt.dot_product_select_coordinate.
Qed.





Lemma affine_product_repeat_zero_affine_function :
  forall cols n idx,
    affine_product (repeat (PolyLang.zero_affine_function cols) n) idx =
    repeat 0%Z n.
Proof.
  intros cols n idx.
  induction n as [|n IH]; simpl.
  - reflexivity.
  - unfold PolyLang.zero_affine_function.
    simpl.
    rewrite dot_product_repeat_zero_left.
    f_equal.
    exact IH.
Qed.

Lemma affine_product_app :
  forall rows1 rows2 idx,
    affine_product (rows1 ++ rows2) idx =
    affine_product rows1 idx ++ affine_product rows2 idx.
Proof.
  intros rows1 rows2 idx.
  unfold affine_product.
  rewrite map_app.
  reflexivity.
Qed.

Lemma affine_product_padded_pi_schedule :
  forall env_dim width pi idx,
    (Datatypes.length pi.(PolyLang.pi_schedule) <= width)%nat ->
    affine_product (padded_pi_schedule env_dim width pi) idx =
    resize width (affine_product pi.(PolyLang.pi_schedule) idx).
Proof.
  intros env_dim width pi idx Hlen.
  unfold padded_pi_schedule, PolyLang.pad_schedule_to_len.
  rewrite affine_product_app.
  rewrite affine_product_repeat_zero_affine_function.
  rewrite <- (app_nil_r (affine_product pi.(PolyLang.pi_schedule) idx)) at 2.
  rewrite resize_app_le.
  - rewrite resize_null_repeat by reflexivity.
    unfold affine_product.
    rewrite map_length.
    reflexivity.
  - unfold affine_product.
    rewrite map_length.
    exact Hlen.
Qed.

Lemma affine_product_firstn :
  forall d rows idx,
    affine_product (firstn d rows) idx =
    firstn d (affine_product rows idx).
Proof.
  induction d as [|d IH]; intros rows idx; destruct rows; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma affine_product_schedule_coord_old_schedule :
  forall env_dim width d pi idx,
    (Datatypes.length pi.(PolyLang.pi_schedule) <= width)%nat ->
    (d < width)%nat ->
    affine_product (schedule_coord_old_schedule env_dim width d pi) idx =
    firstn d (resize width (affine_product pi.(PolyLang.pi_schedule) idx)) ++
    [nth d (resize width (affine_product pi.(PolyLang.pi_schedule) idx)) 0%Z].
Proof.
  intros env_dim width d pi idx Hlen Hd.
  unfold schedule_coord_old_schedule.
  rewrite affine_product_app, affine_product_firstn.
  rewrite affine_product_padded_pi_schedule by exact Hlen.
  f_equal.
  simpl.
  rewrite <- (affine_product_padded_pi_schedule env_dim) by exact Hlen.
  unfold affine_product.
  assert
    (Hrow :
       nth_error (padded_pi_schedule env_dim width pi) d =
       Some
         (nth d (padded_pi_schedule env_dim width pi)
            (PolyLang.zero_affine_function
               (env_dim + pi.(PolyLang.pi_depth))))).
  {
    apply nth_error_nth'.
    rewrite padded_pi_schedule_length by exact Hlen.
    exact Hd.
  }
  pose proof
    (map_nth_error
       (fun t => dot_product (fst t) idx + snd t)
       d (padded_pi_schedule env_dim width pi)
       Hrow) as Hmap.
  apply nth_error_nth with (d := 0%Z) in Hmap.
  now rewrite Hmap.
Qed.

Lemma affine_product_schedule_coord_prefix_schedule :
  forall env_dim width d pi idx,
    (Datatypes.length pi.(PolyLang.pi_schedule) <= width)%nat ->
    affine_product (schedule_coord_prefix_schedule env_dim width d pi) idx =
    firstn d (resize width (affine_product pi.(PolyLang.pi_schedule) idx)).
Proof.
  intros env_dim width d pi idx Hlen.
  unfold schedule_coord_prefix_schedule.
  rewrite affine_product_firstn.
  rewrite affine_product_padded_pi_schedule by exact Hlen.
  reflexivity.
Qed.

Local Lemma parallel_point_ext_eq_except_sched :
  forall pp d pi tau,
    PolyLang.eq_except_sched
      (PolyLang.old_of_ext (parallel_point_ext pp d pi tau)) tau.
Proof.
  intros pp d pi tau.
  unfold PolyLang.eq_except_sched, PolyLang.old_of_ext, parallel_point_ext.
  simpl. repeat split; reflexivity.
Qed.

Local Lemma parallel_ext_pi_in :
  forall pis env_dim width d n pi,
    nth_error pis n = Some pi ->
    In
      (AffineCore.compose_pinstr_ext_at env_dim
        (parallel_old_pi env_dim width d pi)
        (parallel_new_pi env_dim width d pi))
      (AffineCore.compose_pinstrs_ext_at env_dim
        (List.map (parallel_old_pi env_dim width d) pis)
        (List.map (parallel_new_pi env_dim width d) pis)).
Proof.
  induction pis as [|head tail IH]; intros env_dim width d [|n] pi Hnth;
    simpl in *; try discriminate.
  - inversion Hnth; subst. left. reflexivity.
  - right. eapply IH. exact Hnth.
Qed.

Local Lemma parallel_point_ext_belongs :
  forall pis varctxt vars d tau pi,
    nth_error pis tau.(PolyLang.ip_nth) = Some pi ->
    PolyLang.belongs_to tau pi ->
    check_current_view_pinstrb pi = true ->
    (Datatypes.length pi.(PolyLang.pi_schedule) <= schedule_width_of_pis pis)%nat ->
    (d < schedule_width_of_pis pis)%nat ->
    PolyLang.belongs_to_ext
      (parallel_point_ext ((pis, varctxt), vars) d pi tau)
      (AffineCore.compose_pinstr_ext_at (Datatypes.length varctxt)
        (parallel_old_pi
          (Datatypes.length varctxt) (schedule_width_of_pis pis) d pi)
        (parallel_new_pi
          (Datatypes.length varctxt) (schedule_width_of_pis pis) d pi)).
Proof.
  intros pis varctxt vars d tau pi Hnth Hbel Hcurrent Hwidth Hd.
  pose proof (check_current_view_pinstrb_sound pi Hcurrent) as Hwitness.
  unfold PolyLang.belongs_to in Hbel.
  destruct Hbel as (Hdom & Htf & Hts & Hinstr & Hdepth).
  unfold PolyLang.belongs_to_ext, parallel_point_ext,
    AffineCore.compose_pinstr_ext_at.
  simpl.
  repeat split.
  - exact Hdom.
  - rewrite Htf.
    unfold PolyLang.current_transformation_of,
      PolyLang.current_transformation_at, parallel_old_pi.
    simpl. rewrite Hwitness. reflexivity.
  - change (
      firstn d (resize (schedule_width_of_pis pis)
        tau.(PolyLang.ip_time_stamp)) ++
      [nth d (resize (schedule_width_of_pis pis)
        tau.(PolyLang.ip_time_stamp)) 0%Z] =
      affine_product
        (schedule_coord_old_schedule
          (Datatypes.length varctxt) (schedule_width_of_pis pis) d pi)
        tau.(PolyLang.ip_index)).
    rewrite affine_product_schedule_coord_old_schedule by assumption.
    now rewrite Hts.
  - change (
      firstn d (resize (schedule_width_of_pis pis)
        tau.(PolyLang.ip_time_stamp)) =
      affine_product
        (schedule_coord_prefix_schedule
          (Datatypes.length varctxt) (schedule_width_of_pis pis) d pi)
        tau.(PolyLang.ip_index)).
    rewrite affine_product_schedule_coord_prefix_schedule by assumption.
    now rewrite Hts.
  - exact Hinstr.
  - exact Hdepth.
Qed.











Lemma lex_compare_singleton_lt :
  forall z1 z2,
    (z1 < z2)%Z ->
    lex_compare [z1] [z2] = Lt.
Proof.
  intros z1 z2 Hlt.
  simpl.
  destruct (z1 ?= z2) eqn:Hcmp; simpl.
  - apply Z.compare_eq_iff in Hcmp. lia.
  - reflexivity.
  - apply Z.compare_gt_iff in Hcmp. lia.
Qed.

(** * Executable certificate and soundness *)

(** The public [*_current*] names below are retained for compatibility.
    Their dimensions now denote canonical schedule coordinates, rather than
    coordinates in the current iteration point. *)

Definition check_pprog_parallel_currentb
  (pp : PolyLang.t) (plan : parallel_plan) : imp bool :=
  let d := plan.(target_dim) in
  if Nat.ltb d (schedule_width pp)
     && check_current_view_pprogb pp
  then AffineCore.validate (parallel_old_pprog pp d) (parallel_new_pprog pp d)
  else pure false.

Definition checked_parallelize_current
  (pp : PolyLang.t) (plan : parallel_plan) : imp (result parallel_cert) :=
  BIND ok <- check_pprog_parallel_currentb pp plan -;
  if ok
  then pure (Okk {| certified_dim := plan.(target_dim) |})
  else pure (Err "Parallel validation failed").

Lemma check_pprog_parallel_currentb_true_inv :
  forall pp plan,
    mayReturn (check_pprog_parallel_currentb pp plan) true ->
    (target_dim plan < schedule_width pp)%nat /\
    check_current_view_pprogb pp = true /\
    mayReturn
      (AffineCore.validate
         (parallel_old_pprog pp plan.(target_dim))
         (parallel_new_pprog pp plan.(target_dim)))
      true.
Proof.
  intros pp plan Hret.
  unfold check_pprog_parallel_currentb in Hret.
  destruct
    ((Nat.ltb (target_dim plan) (schedule_width pp)
        && check_current_view_pprogb pp)%bool) eqn:Hguard.
  - apply andb_true_iff in Hguard.
    destruct Hguard as [Hlt Hcur].
    split.
    + apply Nat.ltb_lt. exact Hlt.
    + split; [exact Hcur | exact Hret].
  - apply mayReturn_pure in Hret.
    discriminate.
Qed.

Local Lemma env_dim_of_pointwise :
  forall (varctxt : list Instr.ident)
         (tau : PolyLang.InstrPoint) (pi : PolyLang.PolyInstr),
    PolyLang.belongs_to tau pi ->
    Datatypes.length tau.(PolyLang.ip_index) =
      (Datatypes.length varctxt + pi.(PolyLang.pi_depth))%nat ->
    env_dim_of tau = Datatypes.length varctxt.
Proof.
  intros varctxt tau pi Hbel Hlen.
  unfold PolyLang.belongs_to in Hbel.
  destruct Hbel as (_ & _ & _ & _ & Hdepth).
  unfold env_dim_of. rewrite Hlen, Hdepth. lia.
Qed.

Local Lemma parallel_single_point_view :
  forall pis varctxt vars d tau pi,
    nth_error pis tau.(PolyLang.ip_nth) = Some pi ->
    PolyLang.belongs_to tau pi ->
    Datatypes.length tau.(PolyLang.ip_index) =
      (Datatypes.length varctxt + pi.(PolyLang.pi_depth))%nat ->
    check_current_view_pinstrb pi = true ->
    (Datatypes.length pi.(PolyLang.pi_schedule) <=
      schedule_width_of_pis pis)%nat ->
    (d < schedule_width_of_pis pis)%nat ->
    In
      (parallel_pinstr_ext ((pis, varctxt), vars) d pi)
      (parallel_pinstrs_ext ((pis, varctxt), vars) d) /\
    PolyLang.belongs_to_ext
      (parallel_point_ext ((pis, varctxt), vars) d pi tau)
      (parallel_pinstr_ext ((pis, varctxt), vars) d pi) /\
    Datatypes.length
      (parallel_point_ext ((pis, varctxt), vars) d pi tau).(PolyLang.ip_index_ext) =
      (Datatypes.length varctxt +
       (parallel_pinstr_ext
          ((pis, varctxt), vars) d pi).(PolyLang.pi_depth_ext))%nat /\
    PolyLang.eq_except_sched
      (PolyLang.old_of_ext
        (parallel_point_ext ((pis, varctxt), vars) d pi tau))
      tau.
Proof.
  intros pis varctxt vars d tau pi Hnth Hbel Hlen Hcurrent Hwidth Hd.
  split.
  - unfold parallel_pinstr_ext, parallel_pinstrs_ext.
    simpl. eapply parallel_ext_pi_in. exact Hnth.
  - split.
    + unfold parallel_pinstr_ext. simpl.
      eapply parallel_point_ext_belongs; eauto.
    + split.
      * unfold parallel_point_ext, parallel_pinstr_ext. simpl.
        exact Hlen.
      * eapply parallel_point_ext_eq_except_sched.
Qed.

Local Lemma parallel_direction_pointwise_permutable :
  forall pis varctxt vars d tau1 tau2 pi1 pi2,
    mayReturn
      (AffineCore.validate
        (parallel_old_pprog ((pis, varctxt), vars) d)
        (parallel_new_pprog ((pis, varctxt), vars) d))
      true ->
    nth_error pis tau1.(PolyLang.ip_nth) = Some pi1 ->
    nth_error pis tau2.(PolyLang.ip_nth) = Some pi2 ->
    PolyLang.belongs_to tau1 pi1 ->
    PolyLang.belongs_to tau2 pi2 ->
    Datatypes.length tau1.(PolyLang.ip_index) =
      (Datatypes.length varctxt + pi1.(PolyLang.pi_depth))%nat ->
    Datatypes.length tau2.(PolyLang.ip_index) =
      (Datatypes.length varctxt + pi2.(PolyLang.pi_depth))%nat ->
    check_current_view_pinstrb pi1 = true ->
    check_current_view_pinstrb pi2 = true ->
    (Datatypes.length pi1.(PolyLang.pi_schedule) <=
      schedule_width_of_pis pis)%nat ->
    (Datatypes.length pi2.(PolyLang.pi_schedule) <=
      schedule_width_of_pis pis)%nat ->
    (d < schedule_width_of_pis pis)%nat ->
    same_env_of tau1 tau2 ->
    same_prefix_before ((pis, varctxt), vars) d tau1 tau2 ->
    (nth d (padded_timestamp ((pis, varctxt), vars) tau1) 0%Z <
     nth d (padded_timestamp ((pis, varctxt), vars) tau2) 0%Z)%Z ->
    ILSema.Permutable tau1 tau2.
Proof.
  intros pis varctxt vars d tau1 tau2 pi1 pi2 Hval Hnth1 Hnth2
    Hbel1 Hbel2 Hlen1 Hlen2 Hcurrent1 Hcurrent2 Hwidth1 Hwidth2 Hd
    Hsame_env Hprefix Hlt.
  destruct
    (parallel_single_point_view
      pis varctxt vars d tau1 pi1
      Hnth1 Hbel1 Hlen1 Hcurrent1 Hwidth1 Hd)
    as (Hinext1 & Hbelext1 & Hidxext1 & Heq1).
  destruct
    (parallel_single_point_view
      pis varctxt vars d tau2 pi2
      Hnth2 Hbel2 Hlen2 Hcurrent2 Hwidth2 Hd)
    as (Hinext2 & Hbelext2 & Hidxext2 & Heq2).
  set (pi1_ext := parallel_pinstr_ext ((pis, varctxt), vars) d pi1) in *.
  set (pi2_ext := parallel_pinstr_ext ((pis, varctxt), vars) d pi2) in *.
  set (tau1_ext := parallel_point_ext ((pis, varctxt), vars) d pi1 tau1) in *.
  set (tau2_ext := parallel_point_ext ((pis, varctxt), vars) d pi2 tau2) in *.
  assert (Hsameidx :
    firstn (Datatypes.length varctxt) tau1_ext.(PolyLang.ip_index_ext) =
    firstn (Datatypes.length varctxt) tau2_ext.(PolyLang.ip_index_ext)).
  {
    subst tau1_ext tau2_ext. simpl.
    unfold same_env_of, env_prefix_of in Hsame_env.
    rewrite
      (env_dim_of_pointwise varctxt tau1 pi1 Hbel1 Hlen1),
      (env_dim_of_pointwise varctxt tau2 pi2 Hbel2 Hlen2)
      in Hsame_env.
    exact Hsame_env.
  }
  assert (Hnew_eq :
    PolyLang.ip_time_stamp2_ext tau1_ext =
    PolyLang.ip_time_stamp2_ext tau2_ext).
  {
    subst tau1_ext tau2_ext. simpl. exact Hprefix.
  }
  assert (Hold : PolyLang.instr_point_ext_old_sched_lt tau1_ext tau2_ext).
  {
    unfold PolyLang.instr_point_ext_old_sched_lt.
    subst tau1_ext tau2_ext. simpl.
    unfold same_prefix_before, padded_timestamp in Hprefix.
    rewrite Hprefix.
    rewrite lex_compare_app by reflexivity.
    rewrite lex_compare_reflexive.
    apply lex_compare_singleton_lt. exact Hlt.
  }
  assert (Hnew : PolyLang.instr_point_ext_new_sched_ge tau1_ext tau2_ext).
  {
    unfold PolyLang.instr_point_ext_new_sched_ge. left.
    rewrite Hnew_eq. apply lex_compare_reflexive.
  }
  assert (Hperm : PolyLang.Permutable_ext tau1_ext tau2_ext).
  {
    eapply AffineCore.validate_pointwise_implies_permutability
      with
        (pp1 := parallel_old_pprog ((pis, varctxt), vars) d)
        (pp2 := parallel_new_pprog ((pis, varctxt), vars) d)
        (env1 := varctxt) (env2 := varctxt)
        (vars1 := vars) (vars2 := vars)
        (pil1 := List.map
          (parallel_old_pi
            (Datatypes.length varctxt) (schedule_width_of_pis pis) d) pis)
        (pil2 := List.map
          (parallel_new_pi
            (Datatypes.length varctxt) (schedule_width_of_pis pis) d) pis)
        (pi1_ext := pi1_ext) (pi2_ext := pi2_ext); eauto.
  }
  eapply (permutable_eq_except_sched
    (PolyLang.old_of_ext tau1_ext) tau1
    (PolyLang.old_of_ext tau2_ext) tau2); eauto.
Qed.

Lemma check_pprog_parallel_currentb_pointwise_sound :
  forall pp plan,
    mayReturn (check_pprog_parallel_currentb pp plan) true ->
    parallel_safe_dim_pointwise pp plan.(target_dim).
Proof.
  intros [[pis varctxt] vars] [d] Hcheck.
  simpl in *.
  pose proof
    (check_pprog_parallel_currentb_true_inv
       ((pis, varctxt), vars) {| target_dim := d |} Hcheck)
    as (Hd & Hcurrent & Hval).
  unfold parallel_safe_dim_pointwise.
  intros tau1 tau2 pi1 pi2 Hnth1 Hnth2 Hbel1 Hbel2 Hlen1 Hlen2 Hslice.
  simpl in *.
  set (width := schedule_width_of_pis pis) in *.
  assert (Hinpi1 : In pi1 pis) by (eapply nth_error_In; eauto).
  assert (Hinpi2 : In pi2 pis) by (eapply nth_error_In; eauto).
  assert (Hwidth1 : (Datatypes.length pi1.(PolyLang.pi_schedule) <= width)%nat).
  { subst width. exact (schedule_width_ge_pinstr pis varctxt vars pi1 Hinpi1). }
  assert (Hwidth2 : (Datatypes.length pi2.(PolyLang.pi_schedule) <= width)%nat).
  { subst width. exact (schedule_width_ge_pinstr pis varctxt vars pi2 Hinpi2). }
  assert (Hcurrent1 : check_current_view_pinstrb pi1 = true).
  {
    unfold check_current_view_pprogb in Hcurrent.
    eapply forallb_forall in Hcurrent; eauto.
  }
  assert (Hcurrent2 : check_current_view_pinstrb pi2 = true).
  {
    unfold check_current_view_pprogb in Hcurrent.
    eapply forallb_forall in Hcurrent; eauto.
  }
  destruct Hslice as (Hsame_env & Hprefix & Hdiff).
  assert (Hneq_coord :
    nth d (padded_timestamp ((pis, varctxt), vars) tau1) 0%Z <>
    nth d (padded_timestamp ((pis, varctxt), vars) tau2) 0%Z).
  {
    intro Heq. apply Hdiff.
    rewrite nth_error_nth' with
      (d := 0%Z) (n := d)
      (l := padded_timestamp ((pis, varctxt), vars) tau1).
    2: { unfold padded_timestamp. rewrite resize_length. exact Hd. }
    rewrite nth_error_nth' with
      (d := 0%Z) (n := d)
      (l := padded_timestamp ((pis, varctxt), vars) tau2).
    2: { unfold padded_timestamp. rewrite resize_length. exact Hd. }
    now rewrite Heq.
  }
  destruct
    (Z_lt_ge_dec
      (nth d (padded_timestamp ((pis, varctxt), vars) tau1) 0%Z)
      (nth d (padded_timestamp ((pis, varctxt), vars) tau2) 0%Z))
    as [Hlt12 | Hge12].
  - subst width.
    eapply
      (parallel_direction_pointwise_permutable
        pis varctxt vars d tau1 tau2 pi1 pi2); eassumption.
  - assert (Hlt21 :
      (nth d (padded_timestamp ((pis, varctxt), vars) tau2) 0%Z <
       nth d (padded_timestamp ((pis, varctxt), vars) tau1) 0%Z)%Z) by lia.
    assert (Hsame_env_rev : same_env_of tau2 tau1).
    { unfold same_env_of in *. symmetry. exact Hsame_env. }
    assert (Hprefix_rev :
      same_prefix_before ((pis, varctxt), vars) d tau2 tau1).
    { unfold same_prefix_before in *. symmetry. exact Hprefix. }
    apply ILSema.Permutable_symm.
    subst width.
    eapply
      (parallel_direction_pointwise_permutable
        pis varctxt vars d tau2 tau1 pi2 pi1); eassumption.
Qed.

Lemma parallel_safe_dim_pointwise_implies_safe_dim :
  forall pp d,
    parallel_safe_dim_pointwise pp d ->
    parallel_safe_dim pp d.
Proof.
  intros pp d Hpointwise envv ipl tau1 tau2 Henvlen Hflat Hin1 Hin2 Hslice.
  destruct (flatten_instrs_member_inv _ _ _ _ Hflat Hin1)
    as [pi1 [Hnth1 [Hbel1 Hlen1]]].
  destruct (flatten_instrs_member_inv _ _ _ _ Hflat Hin2)
    as [pi2 [Hnth2 [Hbel2 Hlen2]]].
  eapply Hpointwise with (pi1 := pi1) (pi2 := pi2); eauto.
  - now rewrite <- Henvlen.
  - now rewrite <- Henvlen.
Qed.

Lemma parallel_cert_pointwise_sound_implies_sound :
  forall pp cert,
    parallel_cert_pointwise_sound pp cert ->
    parallel_cert_sound pp cert.
Proof.
  intros pp cert Hpointwise.
  eapply parallel_safe_dim_pointwise_implies_safe_dim.
  exact Hpointwise.
Qed.

Lemma check_pprog_parallel_currentb_sound :
  forall pp plan,
    mayReturn (check_pprog_parallel_currentb pp plan) true ->
    parallel_safe_dim pp plan.(target_dim).
Proof.
  intros pp plan Hcheck.
  eapply parallel_safe_dim_pointwise_implies_safe_dim.
  eapply check_pprog_parallel_currentb_pointwise_sound.
  exact Hcheck.
Qed.

Lemma checked_parallelize_current_sound :
  forall pp plan cert,
    mayReturn (checked_parallelize_current pp plan) (Okk cert) ->
    parallel_cert_sound pp cert.
Proof.
  intros pp plan cert Hchecked.
  unfold checked_parallelize_current in Hchecked.
  apply mayReturn_bind in Hchecked.
  destruct Hchecked as [ok [Hcheck Hret]].
  destruct ok;
    [apply mayReturn_pure in Hret
    | apply mayReturn_pure in Hret; discriminate].
  inversion Hret; subst; clear Hret.
  unfold parallel_cert_sound.
  simpl.
  eapply check_pprog_parallel_currentb_sound.
  exact Hcheck.
Qed.

Lemma checked_parallelize_current_pointwise_sound :
  forall pp plan cert,
    mayReturn (checked_parallelize_current pp plan) (Okk cert) ->
    parallel_cert_pointwise_sound pp cert.
Proof.
  intros pp plan cert Hchecked.
  unfold checked_parallelize_current in Hchecked.
  apply mayReturn_bind in Hchecked.
  destruct Hchecked as [ok [Hcheck Hret]].
  destruct ok;
    [apply mayReturn_pure in Hret
    | apply mayReturn_pure in Hret; discriminate].
  inversion Hret; subst; clear Hret.
  unfold parallel_cert_pointwise_sound.
  simpl.
  eapply check_pprog_parallel_currentb_pointwise_sound.
  exact Hcheck.
Qed.

Lemma checked_parallelize_current_implies_dim_in_range :
  forall pp plan cert,
    mayReturn (checked_parallelize_current pp plan) (Okk cert) ->
    (certified_dim cert < schedule_width pp)%nat.
Proof.
  intros pp plan cert Hchecked.
  unfold checked_parallelize_current in Hchecked.
  apply mayReturn_bind in Hchecked.
  destruct Hchecked as [ok [Hcheck Hret]].
  destruct ok;
    [apply mayReturn_pure in Hret
    | apply mayReturn_pure in Hret; discriminate].
  inversion Hret; subst; clear Hret.
  simpl.
  destruct (check_pprog_parallel_currentb_true_inv pp plan Hcheck)
    as (Hlt & _).
  exact Hlt.
Qed.

End ParallelValidator.

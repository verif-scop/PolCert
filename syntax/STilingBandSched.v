Require Import SPolIRs.
Require Import TilingBandDirectRuntime.
Require Import TilingWitness.
Require Import PolOpt.
Require Import String.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Local Open Scope string_scope.
Open Scope impure_scope.

Module CoreBandRuntime := TilingBandDirectRuntime SPolIRs.
Module CoreBandSched := CoreBandRuntime.Legacy.

Definition tiling_band_validation_route_acceptsb :=
  CoreBandRuntime.tiling_band_validation_route_acceptsb.

Definition check_pprog_pluto_permutable_tiling_bands_direct :=
  CoreBandSched.check_pprog_pluto_permutable_tiling_bands_direct.

Definition checked_tiling_sourceb_complete_direct_band_check :=
  CoreBandRuntime.checked_tiling_sourceb_complete_direct_band_check.

Definition checked_tiling_schedule_sourceb_first_runtime_validate_route :=
  CoreBandRuntime.checked_tiling_schedule_sourceb_first_runtime_validate_route.

Definition tiling_validation_route_label
    (route: CoreBandRuntime.tiling_band_validation_route) : string :=
  match route with
  | CoreBandRuntime.DirectBandAccepted => "permutable-band"
  | CoreBandRuntime.GeneralScheduleAccepted => "actual-schedule"
  | CoreBandRuntime.Rejected => "rejected"
  end.

Definition print_tiling_validation_route_label (_: string) : unit := tt.

Definition observe_tiling_validation_route
    (route: CoreBandRuntime.tiling_band_validation_route)
  : CoreBandRuntime.tiling_band_validation_route :=
  PolOpt.print
    (fun selected =>
       print_tiling_validation_route_label
         (tiling_validation_route_label selected))
    route.

Lemma observe_tiling_validation_route_eq :
  forall route, observe_tiling_validation_route route = route.
Proof.
  reflexivity.
Qed.

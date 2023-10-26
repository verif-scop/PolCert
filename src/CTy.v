Require Import TyTy.
Require Import ZArith.
Require Import Ctypes.
Require Import AST.
Require Import List.
Require Import Bool.
Require Import Base.
Require Import Maps.
Require Import LibTactics.
Require Import sflib.
Require Import Memory.
Import ListNotations.

Module CTy <: TY.

  (* Base type is used to annotate expressions *)
  Inductive basetype : Type :=
  | int32s
  .

  (* Definition basetype := basetype'. *)
  Definition dummy_basetype := int32s.

    (** Variable type is sugared. All variable's type should be wrapped as arrtype *)
    (** list Z for bounds; we use Z rather than nat for compatibility to CompCert *)
    (** when list Z is nil, the arr degrade to single cell variable *)
  Inductive arrtype : Type :=
  | arr_type_intro : basetype -> list Z -> arrtype
  .

  (* Definition arrtype := arrtype'. *)
  Definition dummy_arrtype := arr_type_intro dummy_basetype nil.


  Definition basetype_of_arrtype (ty: arrtype): basetype :=
    match ty with
    | arr_type_intro bty _ => bty
    end.

  Definition basetype_eqb (ty1 ty2: basetype): bool :=
    match ty1, ty2 with
    | int32s, int32s => true
    end.

  Definition arrtype_eqb (ty1 ty2: arrtype): bool :=
    match ty1, ty2 with
    | arr_type_intro bty1 bounds1, arr_type_intro bty2 bounds2 =>
      basetype_eqb bty1 bty2 && list_beq Z.t Z.eqb bounds1 bounds2
    end. 
  


  Lemma basetype_eqb_eq:
    forall (ty1 ty2: basetype),
      basetype_eqb ty1 ty2 = true <-> ty1 = ty2.
  Proof. intros. destruct ty1; destruct ty2; split; intro; simpls; trivial. Qed.

  Lemma basetype_eqb_refl:
    forall (ty: basetype),
      basetype_eqb ty ty = true.
  Proof. intros. unfold basetype_eqb. destruct ty. trivial. Qed.

  Lemma arrtype_eqb_eq:
    forall (ty1 ty2: arrtype),
      arrtype_eqb ty1 ty2 = true <-> ty1 = ty2.
  Proof.
    intros.
    split.
    - intros.
      destruct ty1, ty2.
      simpl in H.
      rewrite andb_true_iff in H.
      destruct H.
      apply basetype_eqb_eq in H.
      apply internal_list_dec_bl in H0. 2: eapply Z.eqb_eq.
      subst. reflexivity.
    - intros.
      subst.
      destruct ty2.
      simpl.
      apply andb_true_iff.
      split.
      + apply basetype_eqb_eq; trivial.
      + 
        eapply internal_list_dec_lb; trivial. 
        apply Z.eqb_eq.
  Qed.

  Definition t := arrtype.
  Definition eqb := arrtype_eqb.
  Definition eqb_eq := arrtype_eqb_eq.
  Definition dummy := dummy_arrtype.
  (** coversions from and to CompCert type *)

    
  Fixpoint base_of_compcert_arrtype (ty: Ctypes.type): option basetype :=
    match ty with
    | Tarray ty' _ _ => base_of_compcert_arrtype ty'
    | ty => if type_eqb ty type_int32s then Some CTy.int32s else None
    end.

  Fixpoint collect_compcert_arrtype_bounds (ty: Ctypes.type): option (list Z) :=
    match ty with
    | Tarray ty' bd _ => 
      match collect_compcert_arrtype_bounds ty' with
      | Some bounds => Some (bounds ++ [bd])
      | None => None
      end
    | ty => if type_eqb ty type_int32s then Some nil else None
    end.

  Definition of_compcert_arrtype (ty: Ctypes.type): option arrtype :=
    match ty with
    | Tarray ty' bd _ => 
      match base_of_compcert_arrtype ty', collect_compcert_arrtype_bounds ty with
      | Some ty, Some bounds =>
        Some (arr_type_intro ty bounds)
      | _, _ => None
      end
    | _ => None
    end. 

  Definition basetype_to_compcert_type (ty: basetype): Ctypes.type :=
    match ty with
    | int32s => type_int32s
    end.

  Definition basetype_size (ty: basetype): Z := 
    Ctypes.sizeof (PTree.empty Ctypes.composite) (basetype_to_compcert_type ty)  
  .

  Fixpoint arrtype_to_compcert_type_helper (basety: basetype) (bounds: list Z) : Ctypes.type :=
    match bounds with
    | nil => basetype_to_compcert_type basety
    | cons z zs => 
      Ctypes.Tarray (arrtype_to_compcert_type_helper basety zs) z (Ctypes.noattr)
    end
  .
  
  Definition arrtype_to_compcert_type (ty: arrtype): Ctypes.type :=
    match ty with
    | arr_type_intro ty bounds => arrtype_to_compcert_type_helper ty bounds
    end
  .

  Definition basetype_access_mode (ty: basetype): Ctypes.mode := 
    match ty with
    | int32s => Ctypes.By_value Mint32
    end
  .

  Lemma basety_size_eq_size_chunk:
    forall basety chunk,
      basetype_access_mode basety = By_value chunk ->
      basetype_size basety = size_chunk chunk.
  Proof. 
    intros. destruct basety eqn:Hbty; simpls. inv H.
    simpls. unfold CTy.basetype_size. simpls. trivial.
  Qed. 
  
End CTy.
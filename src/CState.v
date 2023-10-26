Require Import Bool.
Require Import List.
Require Import Csem.
Require Import Memory.
Require Import StateTy.
Require Import PolyBase.
Require Import Values.
Require Import Maps.
Require Import AST.
Require Import Globalenvs.
Require Import Ctypes.
Require Import ZArith.
Require Import LibTactics.
Require Import TyTy.
Require Import CTy.
Require Import Cop.
Require Import Linalg.
Require Import Lia.
Require Import sflib.

Module CState <: STATE.

    Module Ty := CTy.
    Definition state: Type := (genv * env * mem)%type.
    Definition mkState (ge: genv) (e: env) (m: mem) := (ge,e,m). 
    Definition t := state.

    Definition dummy_state:t := 
        mkState 
          {| genv_genv := (Genv.empty_genv Csyntax.fundef Ctypes.type []);
             genv_cenv := (PTree.empty composite) |}
          (Csem.empty_env) 
          (Mem.empty).

    Definition get_var_loc_type (st: t) (id: ident): option (block * Ctypes.type) :=
        let '(ge, e, m) := st in
        match e!id with
        | Some (b, ty) => Some (b, ty)
        | None => match Genv.find_var_info ge.(genv_genv) id, Genv.find_symbol ge.(genv_genv) id with 
                | Some def, Some b => Some (b, def.(gvar_info))
                | _, _ => None
                end
        end.

      Lemma get_var_loc_type_disregard_mem:
        forall ge e m m' id b ty,
          get_var_loc_type (ge, e, m) id = Some (b, ty) ->
          get_var_loc_type (ge, e, m') id = Some (b, ty).
      Proof. 
        intros. simpls.
        destruct (e!id); tryfalse; trivial. 
      Qed.
  
  
    (* State records values of *)
    (* 1. symbolic constants, like M/N, those invariants (not being written) inside loop nests *)
    (* 2. arrays, like alpha, beta, arr[][], they are written inside loop nests *)
    (* Note that state do not record values for "iterators". iterators are nameless at instruction level *)
    (* and should be allocated with fresh ident after codegen back to structural representation like Csyntax. *)
    (* Even though the state still records values for "ident" that was iterator. They are no longer iterator now. We could just regard them as symbolic constants. *)
    Definition mem_eq (m m': mem): Prop := 
        Mem.extends m m' /\ Mem.extends m' m.

    Lemma mem_eq_sym:
        forall m m', mem_eq m m' -> mem_eq m' m.
    Proof. intros. unfolds mem_eq. tauto. Qed.

    Lemma mem_eq_trans:
        forall m1 m2 m3, mem_eq m1 m2 -> mem_eq m2 m3 -> mem_eq m1 m3.
    Proof.
      intros. unfolds mem_eq. destruct H as (H1 & H2). destruct H0 as (H3 & H4). split.
      eapply Mem.extends_extends_compose; eauto.
      eapply Mem.extends_extends_compose; eauto.
    Qed.

    Lemma mem_eq_refl:
        forall m, mem_eq m m.
    Proof. intros. split. all: eapply Mem.extends_refl. Qed.

    Lemma mem_eq_prsv_valid_access:
      forall m m' chunk b ofs p,
        mem_eq m m' ->
          Mem.valid_access m chunk b ofs p ->
          Mem.valid_access m' chunk b ofs p.
    Proof. intros. destruct H. eapply Mem.valid_access_extends; eauto. Qed.


    Lemma mem_eq_prsv_next_block:
      forall m m',
        mem_eq m m' ->
        Mem.nextblock m = Mem.nextblock m'.
    Proof.
      intros. destruct H. inv H; trivial.
    Qed.

    Lemma mem_eq_prsv_perm:
      forall m m' b ofs k p,
        mem_eq m m' ->
        Mem.perm m b ofs k p ->
        Mem.perm m' b ofs k p.
    Proof. 
      intros. destruct H. 
      eapply Mem.perm_extends; eauto.
    Qed.

    Lemma mem_eq_prsv_contents:
      forall m m',
        mem_eq m m' ->
        forall b ofs, 
          Mem.perm m b ofs Cur Readable ->
          ZMap.get ofs ((Mem.mem_contents m)!!b) = ZMap.get ofs ((Mem.mem_contents m')!!b).
    Proof. 
      intros. rename H0 into Hread. destruct H.
      inv H. inv H0. clear - Hread mext_inj mext_inj0.
      unfolds inject_id.
      inv mext_inj. inv mext_inj0.
      assert (Mem.perm m' b ofs Cur Readable). {
        pose proof (mi_perm b b 0 ofs Cur Readable). 
        replace (ofs + 0) with ofs in H; try lia.
        eapply H; trivial.
      }
      eapply mi_memval in Hread; eauto.
      eapply mi_memval0 in H; eauto.
      replace (ofs + 0) with ofs in Hread; try lia.
      replace (ofs + 0) with ofs in H; try lia.
      inv Hread; inv H; tryfalse; eauto.
      {
        inv H2; inv H5; tryfalse; eauto.
        - inv H; inv H2; simpls.
          rewrite Integers.Ptrofs.add_zero; trivial.
        - rewrite <- H1 in H3. inv H3. trivial. 
      }
    Qed. 

    Lemma setN_inside_nth:
      forall vl ofs ofs' c,
        ofs' <= ofs < ofs' + Z.of_nat (length vl) ->
        ZMap.get ofs (Mem.setN vl ofs' c) = 
        nth (Z.to_nat (ofs - ofs')) vl (fst c).
    Proof.
      induction vl.
      - intros. simpls. lia.
      - intros. simpls.
      destruct (ofs - ofs') eqn:Hdelter; simpls; tryfalse; try lia.
      {
        assert (ofs = ofs'). lia. subst.
        rewrite Mem.setN_outside; try lia.
        eapply ZMap.gss.
      }
      {
        rewrite IHvl; simpls; try lia.
        remember (ofs - ofs') as delta.
        replace (ofs - (ofs' + 1)) with (delta - 1); try lia.
        assert (delta > 0). lia. 
        destruct (Z.to_nat (delta-1)) eqn:Hn; simpls; 
        destruct (Pos.to_nat p) eqn:Hp; simpls; try lia.
        - 
        assert (delta = 1). lia. subst. rewrite H1 in Hdelter.
        inv Hdelter. inv Hp. trivial.
        - 
        assert (n0 = S n). lia. subst; trivial.
      }  
    Qed.


    Lemma swap_store_cell_neq_prsv_mem_eq:
      forall m0 b1 ofs1 v1 m1' m1 b2 ofs2 v2 m2' m0' m1x' m1x m2x' chunk,
        Mem.store chunk m0 b1 ofs1 v1 = Some m1' ->
        Mem.store chunk m1 b2 ofs2 v2 = Some m2' ->
        Mem.store chunk m0' b2 ofs2 v2 = Some m1x' ->
        Mem.store chunk m1x b1 ofs1 v1 = Some m2x' ->
        mem_eq m0 m0' ->
        mem_eq m1 m1' ->
        mem_eq m1x m1x' ->
        (b1 <> b2 \/ ofs1 + (size_chunk chunk) <= ofs2 \/ ofs2 + (size_chunk chunk) <= ofs1 ) ->
        mem_eq m2' m2x'.
    Proof. 
      intros. split.
      - econs.
        + 
          assert (Mem.nextblock m2' = Mem.nextblock m0). {
            eapply Mem.nextblock_store in H0.
            eapply mem_eq_prsv_next_block in H4.
            eapply Mem.nextblock_store in H.
            eapply mem_eq_prsv_next_block in H3.
            lia.
          }
          assert (Mem.nextblock m2x' = Mem.nextblock m0'). {
            eapply Mem.nextblock_store in H2.
            eapply mem_eq_prsv_next_block in H5.
            eapply Mem.nextblock_store in H1.
            eapply mem_eq_prsv_next_block in H4.
            lia.
          }
          eapply mem_eq_prsv_next_block in H3. lia.
        + econs. 
          -- intros. unfold inject_id in H7. inv H7. 
             replace (ofs + 0) with ofs; try lia.
              eapply Mem.perm_store_1; eauto.
              eapply mem_eq_prsv_perm with (m:=m1x'). eapply mem_eq_sym; trivial.
              eapply Mem.perm_store_1; eauto.
              eapply mem_eq_prsv_perm with (m:=m0); eauto.
              eapply Mem.perm_store_2; eauto.
              eapply mem_eq_prsv_perm with (m:=m1); eauto.
              eapply Mem.perm_store_2; eauto.
          -- intros. unfold inject_id in H7. inv H7.
             destruct chunk0; simpls; exists 0; try lia.
          -- intros. unfolds inject_id. inv H7.
             replace (ofs + 0) with ofs; try lia.

             assert (forall b ofs, 
              Mem.perm m2' b ofs Cur Readable ->
              ZMap.get ofs (Mem.mem_contents m2')!!b = ZMap.get ofs (Mem.mem_contents m2x')!!b). {
              intros. rename ofs into ofs3. rename H8 into Hperm'.
              rename H7 into Hperm. 
              pose proof H as Hw1.
              pose proof H0 as Hw2.
              pose proof H1 as Hw3.
              pose proof H2 as Hw4.
              pose proof H3 as Heq0. pose proof H4 as Heq1. pose proof H5 as Heq1x.
              
              rename ofs0 into ofs.
              
              assert (b = b1 \/ b = b2 \/ (b <> b1 /\ b <> b2)). {
                clear. destruct b; destruct b1; destruct b2; try lia.
              }
              destruct H7 as [B | [B | B]].
              - subst.
                assert (b1 <> b2 \/ b1 = b2). {
                  clear. destruct b1; destruct b2; lia.
                }
                destruct H7.
                --  
                eapply Mem.store_mem_contents in H0. rewrite H0.
                rewrite PMap.gso; trivial.
                eapply mem_eq_prsv_contents with (ofs:=ofs) (b:=b1) in H4; trivial.
                rewrite H4.
                eapply Mem.store_mem_contents in H. rewrite H.
                rewrite PMap.gss.
                eapply Mem.store_mem_contents in H2. rewrite H2.
                rewrite PMap.gss.
                eapply mem_eq_prsv_contents with (ofs:=ofs) (b:=b1) in H5; trivial.
                eapply mem_eq_prsv_contents with (ofs:=ofs) (b:=b1) in H3; trivial.

                assert ((ofs < ofs1 \/ ofs >= ofs1 + Z.of_nat (length (encode_val chunk v1))) \/ (ofs1 <= ofs /\ ofs < ofs1 + Z.of_nat (length (encode_val chunk v1)))). {
                  rewrite encode_val_length.
                  rewrite <- size_chunk_conv.
                  clear. 
                  assert (size_chunk chunk > 0). {
                    destruct chunk; simpls; try lia.
                  }
                  destruct ofs; destruct ofs1; simpls; try solve [right; econs; lia]; try solve [left; left; lia]; try solve [left; right; lia]. 
                  all: destruct (size_chunk chunk); tryfalse; try lia.                   
                }
                destruct H8 as [OFS | OFS].
                {
                  pose proof OFS as OFS'.
                  eapply Mem.setN_outside with (c:=(Mem.mem_contents m0)!!b1) in OFS.
                  rewrite OFS.
                  eapply Mem.setN_outside with (c:=(Mem.mem_contents m1x)!!b1) in OFS'.
                  rewrite OFS'.
                  rewrite H5.
                  eapply Mem.store_mem_contents in H1.
                  rewrite H1. rewrite PMap.gso; trivial.
                }
                {
                  rewrite setN_inside_nth; trivial.
                  rewrite setN_inside_nth; trivial.
                  assert (Z.to_nat (ofs - ofs1) < length (encode_val chunk v1))%nat. {
                    clear - OFS; lia.
                  }
                  eapply nth_indep; trivial.
                }
                {
                  eapply Mem.perm_store_2; eauto.
                  eapply mem_eq_prsv_perm in Heq1; eauto.
                  eapply Mem.perm_store_2; eauto.
                }
                {
                  assert (Mem.perm m0 b1 ofs Cur Readable). {
                    eapply Mem.perm_store_2; eauto.
                    eapply mem_eq_prsv_perm in Heq1; eauto.
                    eapply Mem.perm_store_2; eauto.
                  }
                  eapply mem_eq_prsv_perm with (m':=m0') in H8; trivial.
                  eapply Mem.perm_store_1 in Hw3; eauto.
                  eapply mem_eq_prsv_perm; eauto. 
                  eapply mem_eq_sym; trivial.
                }
                {
                  eapply Mem.perm_store_2; eauto.
                }
                -- destruct H6; tryfalse. subst.
                eapply Mem.store_mem_contents in H0. rewrite H0.
                rewrite PMap.gss.
                eapply Mem.store_mem_contents in H2. rewrite H2.
                rewrite PMap.gss; trivial.

                assert ((ofs < ofs1 \/ ofs >= ofs1 + Z.of_nat (length (encode_val chunk v1))) \/ (ofs1 <= ofs /\ ofs < ofs1 + Z.of_nat (length (encode_val chunk v1)))). {
                  rewrite encode_val_length.
                  rewrite <- size_chunk_conv.
                  clear. 
                  assert (size_chunk chunk > 0). {
                    destruct chunk; simpls; try lia.
                  }
                  destruct ofs; destruct ofs1; simpls; try solve [right; econs; lia]; try solve [left; left; lia]; try solve [left; right; lia]. 
                  all: destruct (size_chunk chunk); tryfalse; try lia.                   
                }

                
                assert ((ofs < ofs2 \/ ofs >= ofs2 + Z.of_nat (length (encode_val chunk v2))) \/ (ofs2 <= ofs /\ ofs < ofs2 + Z.of_nat (length (encode_val chunk v2)))). {
                  rewrite encode_val_length.
                  rewrite <- size_chunk_conv.
                  clear. 
                  assert (size_chunk chunk > 0). {
                    destruct chunk; simpls; try lia.
                  }
                  destruct ofs; destruct ofs2; simpls; try solve [right; econs; lia]; try solve [left; left; lia]; try solve [left; right; lia]. 
                  all: destruct (size_chunk chunk); tryfalse; try lia.                   
                }


                destruct H7 as [OFS1 | OFS1].
                {
                  pose proof OFS1 as OFS1'.
                  eapply Mem.setN_outside with (c:=(Mem.mem_contents m1x)!!b2) in OFS1.
                  rewrite OFS1.
                  destruct H8 as [OFS2 | OFS2].
                  {
                    pose proof OFS2 as OFS2'.
                    eapply Mem.setN_outside with (c:=(Mem.mem_contents m1)!!b2) in OFS2.
                    rewrite OFS2.
                    eapply mem_eq_prsv_contents in H4.
                    rewrite H4.
                    eapply Mem.store_mem_contents in H.
                    rewrite H.
                    rewrite PMap.gss; trivial.
                    eapply Mem.setN_outside with (c:=(Mem.mem_contents m0)!!b2) in OFS1'. 
                    rewrite OFS1'.
                    eapply mem_eq_prsv_contents in H3.
                    rewrite H3.

                    eapply mem_eq_prsv_contents in H5.
                    rewrite H5.
                    eapply Mem.store_mem_contents in H1.
                    rewrite H1.

                    rewrite PMap.gss; trivial.

                    eapply Mem.setN_outside with (c:=(Mem.mem_contents m0')!!b2) in OFS2'. rewrite OFS2'. trivial.
                    {
                      assert (Mem.perm m0 b2 ofs Cur Readable). {
                        eapply Mem.perm_store_2; eauto.
                        eapply mem_eq_prsv_perm in Heq1; eauto.
                        eapply Mem.perm_store_2; eauto.
                      }
                      eapply mem_eq_prsv_perm with (m':=m0') in H7; trivial.
                      eapply Mem.perm_store_1 in Hw3; eauto.
                      eapply mem_eq_prsv_perm; eauto. 
                      eapply mem_eq_sym; trivial.
                    }
                    {
                      eapply Mem.perm_store_2; eauto.
                      eapply mem_eq_prsv_perm in Heq1; eauto.
                      eapply Mem.perm_store_2; eauto.
                    }                  
                    {
                      eapply Mem.perm_store_2; eauto.
                    }
                  }
                  { (* ofs inside write 2 range *)
                    rewrite setN_inside_nth; trivial.
                    assert (Z.to_nat (ofs - ofs2) < length (encode_val chunk v2))%nat. {
                      clear - OFS2. lia.
                    }
                    eapply mem_eq_prsv_contents in H5.
                    rewrite H5.
                    eapply Mem.store_mem_contents in H1.
                    rewrite H1.

                    rewrite PMap.gss; trivial.
                    rewrite setN_inside_nth; trivial.
                    eapply nth_indep; trivial.
                    {
                      assert (Mem.perm m0 b2 ofs Cur Readable). {
                        eapply Mem.perm_store_2; eauto.
                        eapply mem_eq_prsv_perm in Heq1; eauto.
                        eapply Mem.perm_store_2; eauto.
                      }
                      eapply mem_eq_prsv_perm with (m':=m0') in H8; trivial.
                      eapply Mem.perm_store_1 in Hw3; eauto.
                      eapply mem_eq_prsv_perm; eauto. 
                      eapply mem_eq_sym; trivial.
                    }
                  }
                }
                {
                  destruct H8 as [OFS2 | OFS2].
                  { (* ofs inside write 2 range *)
                    pose proof OFS1 as OFS1'.
                    eapply setN_inside_nth in OFS1; trivial.
                    rewrite OFS1.
                    assert (Z.to_nat (ofs - ofs1) < length (encode_val chunk v1))%nat. {
                      clear - OFS1'. lia.
                    }
                    eapply Mem.setN_outside with (c:=(Mem.mem_contents m1)!!b2) in OFS2.
                    rewrite OFS2.
                    eapply mem_eq_prsv_contents in H4.
                    rewrite H4.
                    eapply Mem.store_mem_contents in H.
                    rewrite H.
                    rewrite PMap.gss; trivial.
                    rewrite setN_inside_nth; trivial.
                    eapply nth_indep; trivial.
                    {
                      eapply Mem.perm_store_2; eauto.
                    }                  
                  }
                  {
                    clear - H6 OFS1 OFS2.
                    rewrite encode_val_length in OFS1, OFS2.
                    rewrite <- size_chunk_conv in OFS1, OFS2.
                    lia.
                  }
                }
              - subst.
                assert (b1 <> b2 \/ b1 = b2). {
                  clear. destruct b1; destruct b2; lia.
                }
                destruct H7.
                --  
                eapply Mem.store_mem_contents in H0. rewrite H0.
                rewrite PMap.gss; trivial.
                eapply Mem.store_mem_contents in H2. rewrite H2.
                rewrite PMap.gso; try lia.
                eapply mem_eq_prsv_contents with (ofs:=ofs) (b:=b2) in H5.
                rewrite H5.
                eapply Mem.store_mem_contents in H1.
                rewrite H1. rewrite PMap.gss; trivial.

                assert ((ofs < ofs2 \/ ofs >= ofs2 + Z.of_nat (length (encode_val chunk v2))) \/ (ofs2 <= ofs /\ ofs < ofs2 + Z.of_nat (length (encode_val chunk v2)))). {
                  rewrite encode_val_length.
                  rewrite <- size_chunk_conv.
                  clear. 
                  assert (size_chunk chunk > 0). {
                    destruct chunk; simpls; try lia.
                  }
                  destruct ofs; destruct ofs2; simpls; try solve [right; econs; lia]; try solve [left; left; lia]; try solve [left; right; lia]. 
                  all: destruct (size_chunk chunk); tryfalse; try lia.                   
                }
                destruct H8 as [OFS | OFS].
                {
                  pose proof OFS as OFS'.
                  eapply Mem.setN_outside with (c:=(Mem.mem_contents m1)!!b2) in OFS.
                  rewrite OFS.
                  eapply Mem.setN_outside with (c:=(Mem.mem_contents m0')!!b2) in OFS'.
                  rewrite OFS'.
                  
                eapply mem_eq_prsv_contents in H3.
                rewrite <- H3.
                eapply mem_eq_prsv_contents with (ofs:=ofs) (b:=b2) in H4.
                rewrite H4.
                
                eapply Mem.store_mem_contents in H. rewrite H.
                rewrite PMap.gso; try lia.
                trivial. 
                {
                  eapply Mem.perm_store_2; eauto.
                }
                {
                  eapply Mem.perm_store_2; eauto.
                  eapply mem_eq_prsv_perm in Heq1; eauto.
                  eapply Mem.perm_store_2; eauto.
                }
                }
                {
                  rewrite setN_inside_nth; trivial.
                  rewrite setN_inside_nth; trivial.
                  assert (Z.to_nat (ofs - ofs2) < length (encode_val chunk v2))%nat. {
                    clear - OFS; lia.
                  }
                  eapply nth_indep; trivial.
                }
                {
                assert (Mem.perm m0 b2 ofs Cur Readable). {
                  eapply Mem.perm_store_2; eauto.
                  eapply mem_eq_prsv_perm in Heq1; eauto.
                  eapply Mem.perm_store_2; eauto.
                }
                eapply mem_eq_prsv_perm with (m':=m0') in H8; trivial.
                eapply Mem.perm_store_1 in Hw3; eauto.
                eapply mem_eq_prsv_perm; eauto. 
                eapply mem_eq_sym; trivial.
              }
              -- destruct H6; tryfalse. subst.
                eapply Mem.store_mem_contents in H0. rewrite H0.
                rewrite PMap.gss.
                eapply Mem.store_mem_contents in H2. rewrite H2.
                rewrite PMap.gss; trivial.

                assert ((ofs < ofs1 \/ ofs >= ofs1 + Z.of_nat (length (encode_val chunk v1))) \/ (ofs1 <= ofs /\ ofs < ofs1 + Z.of_nat (length (encode_val chunk v1)))). {
                  rewrite encode_val_length.
                  rewrite <- size_chunk_conv.
                  clear. 
                  assert (size_chunk chunk > 0). {
                    destruct chunk; simpls; try lia.
                  }
                  destruct ofs; destruct ofs1; simpls; try solve [right; econs; lia]; try solve [left; left; lia]; try solve [left; right; lia]. 
                  all: destruct (size_chunk chunk); tryfalse; try lia.                   
                }
                assert ((ofs < ofs2 \/ ofs >= ofs2 + Z.of_nat (length (encode_val chunk v2))) \/ (ofs2 <= ofs /\ ofs < ofs2 + Z.of_nat (length (encode_val chunk v2)))). {
                  rewrite encode_val_length.
                  rewrite <- size_chunk_conv.
                  clear. 
                  assert (size_chunk chunk > 0). {
                    destruct chunk; simpls; try lia.
                  }
                  destruct ofs; destruct ofs2; simpls; try solve [right; econs; lia]; try solve [left; left; lia]; try solve [left; right; lia]. 
                  all: destruct (size_chunk chunk); tryfalse; try lia.                   
                }
                destruct H7 as [OFS1 | OFS1].
                {
                  pose proof OFS1 as OFS1'.
                  eapply Mem.setN_outside with (c:=(Mem.mem_contents m1x)!!b2) in OFS1.
                  rewrite OFS1.
                  destruct H8 as [OFS2 | OFS2].
                  {
                    pose proof OFS2 as OFS2'.
                    eapply Mem.setN_outside with (c:=(Mem.mem_contents m1)!!b2) in OFS2.
                    rewrite OFS2.
                    eapply mem_eq_prsv_contents in H4.
                    rewrite H4.
                    eapply Mem.store_mem_contents in H.
                    rewrite H.
                    rewrite PMap.gss; trivial.
                    eapply Mem.setN_outside with (c:=(Mem.mem_contents m0)!!b2) in OFS1'. 
                    rewrite OFS1'.
                    eapply mem_eq_prsv_contents in H3.
                    rewrite H3.

                    eapply mem_eq_prsv_contents in H5.
                    rewrite H5.
                    eapply Mem.store_mem_contents in H1.
                    rewrite H1.

                    rewrite PMap.gss; trivial.

                    eapply Mem.setN_outside with (c:=(Mem.mem_contents m0')!!b2) in OFS2'. rewrite OFS2'. trivial.
                    {
                      assert (Mem.perm m0 b2 ofs Cur Readable). {
                        eapply Mem.perm_store_2; eauto.
                        eapply mem_eq_prsv_perm in Heq1; eauto.
                        eapply Mem.perm_store_2; eauto.
                      }
                      eapply mem_eq_prsv_perm with (m':=m0') in H7; trivial.
                      eapply Mem.perm_store_1 in Hw3; eauto.
                      eapply mem_eq_prsv_perm; eauto. 
                      eapply mem_eq_sym; trivial.
                    }
                    {
                      eapply Mem.perm_store_2; eauto.
                      eapply mem_eq_prsv_perm in Heq1; eauto.
                      eapply Mem.perm_store_2; eauto.
                    }
                    
                    {
                      eapply Mem.perm_store_2; eauto.
                    }
                  }
                  { (* ofs inside write 2 range *)
                    rewrite setN_inside_nth; trivial.
                    assert (Z.to_nat (ofs - ofs2) < length (encode_val chunk v2))%nat. {
                      clear - OFS2. lia.
                    }
                    eapply mem_eq_prsv_contents in H5.
                    rewrite H5.
                    eapply Mem.store_mem_contents in H1.
                    rewrite H1.

                    rewrite PMap.gss; trivial.
                    rewrite setN_inside_nth; trivial.
                    eapply nth_indep; trivial.
                    {
                      assert (Mem.perm m0 b2 ofs Cur Readable). {
                        eapply Mem.perm_store_2; eauto.
                        eapply mem_eq_prsv_perm in Heq1; eauto.
                        eapply Mem.perm_store_2; eauto.
                      }
                      eapply mem_eq_prsv_perm with (m':=m0') in H8; trivial.
                      eapply Mem.perm_store_1 in Hw3; eauto.
                      eapply mem_eq_prsv_perm; eauto. 
                      eapply mem_eq_sym; trivial.
                    }
                  }
                }
                {
                  destruct H8 as [OFS2 | OFS2].
                  { (* ofs inside write 2 range *)
                    pose proof OFS1 as OFS1'.
                    eapply setN_inside_nth in OFS1; trivial.
                    rewrite OFS1.
                    assert (Z.to_nat (ofs - ofs1) < length (encode_val chunk v1))%nat. {
                      clear - OFS1'. lia.
                    }
                    eapply Mem.setN_outside with (c:=(Mem.mem_contents m1)!!b2) in OFS2.
                    rewrite OFS2.
                    eapply mem_eq_prsv_contents in H4.
                    rewrite H4.
                    eapply Mem.store_mem_contents in H.
                    rewrite H.
                    rewrite PMap.gss; trivial.
                    rewrite setN_inside_nth; trivial.
                    eapply nth_indep; trivial.                    
                    {
                      eapply Mem.perm_store_2; eauto.
                    }
                  }
                  {
                    clear - H6 OFS1 OFS2.
                    rewrite encode_val_length in OFS1, OFS2.
                    rewrite <- size_chunk_conv in OFS1, OFS2.
                    lia.
                  }
                }
              - destruct B as [B1 B2].
              eapply Mem.store_mem_contents in H0. rewrite H0.
              rewrite PMap.gso; trivial. 
              eapply mem_eq_prsv_contents with (ofs:=ofs) (b:=b) in H4.
              rewrite H4.
              eapply Mem.store_mem_contents in H. rewrite H.
              rewrite PMap.gso; trivial.
              eapply mem_eq_prsv_contents with (ofs:=ofs) (b:=b) in H3.
              rewrite H3.
              eapply Mem.store_mem_contents in H2. rewrite H2.
              rewrite PMap.gso; trivial.
              eapply mem_eq_prsv_contents with (ofs:=ofs) (b:=b) in H5.
              rewrite H5.
              eapply Mem.store_mem_contents in H1. rewrite H1.
              rewrite PMap.gso; trivial.
              {
                assert (Mem.perm m0 b ofs Cur Readable). {
                  eapply Mem.perm_store_2; eauto.
                  eapply mem_eq_prsv_perm in Heq1; eauto.
                  eapply Mem.perm_store_2; eauto.
                }
                eapply mem_eq_prsv_perm with (m':=m0') in H7; trivial.
                eapply Mem.perm_store_1 in Hw3; eauto.
                eapply mem_eq_prsv_perm; eauto. 
                eapply mem_eq_sym; trivial.
              }
              {
                eapply Mem.perm_store_2; eauto.
                eapply mem_eq_prsv_perm in Heq1; eauto.
                eapply Mem.perm_store_2; eauto.
              }
              {
                eapply Mem.perm_store_2; eauto.
              }             
            }
             rewrite H7. 
             destruct (ZMap.get ofs (Mem.mem_contents m2x')!!b3); econs; eauto.
             destruct v; econs; eauto.
             rewrite Integers.Ptrofs.add_zero. trivial. trivial.
        + intros.
          assert (Mem.perm m0 b ofs k p). {
            eapply mem_eq_prsv_perm with (m:=m0'). eapply mem_eq_sym; trivial.
            eapply Mem.perm_store_2; eauto.
            eapply mem_eq_prsv_perm in H5; eauto.
            eapply Mem.perm_store_2; eauto.
          }
          assert (Mem.perm m2' b ofs k p). {
            eapply Mem.perm_store_1; eauto.
            eapply mem_eq_prsv_perm with (m:=m1'). eapply mem_eq_sym; trivial.
            eapply Mem.perm_store_1; eauto.
          }
          left; trivial.
          - econs.
          + 
            assert (Mem.nextblock m2' = Mem.nextblock m0). {
              eapply Mem.nextblock_store in H0.
              eapply mem_eq_prsv_next_block in H4.
              eapply Mem.nextblock_store in H.
              eapply mem_eq_prsv_next_block in H3.
              lia.
            }
            assert (Mem.nextblock m2x' = Mem.nextblock m0'). {
              eapply Mem.nextblock_store in H2.
              eapply mem_eq_prsv_next_block in H5.
              eapply Mem.nextblock_store in H1.
              eapply mem_eq_prsv_next_block in H4.
              lia.
            }
            eapply mem_eq_prsv_next_block in H3. lia.
          + econs. 
            -- intros. unfold inject_id in H7. inv H7. 
               replace (ofs + 0) with ofs; try lia.
                eapply Mem.perm_store_1; eauto.
                eapply mem_eq_prsv_perm with (m:=m1'); eauto. 
                eapply mem_eq_sym; trivial.
                eapply Mem.perm_store_1; eauto.
                eapply mem_eq_prsv_perm with (m:=m0'); eauto.
                eapply mem_eq_sym; trivial.
                
                eapply Mem.perm_store_2; eauto.
                eapply mem_eq_prsv_perm with (m:=m1x). trivial. 
                eapply Mem.perm_store_2; eauto.
            -- intros. unfold inject_id in H7. inv H7.
               destruct chunk0; simpls; exists 0; try lia.
            -- intros. unfolds inject_id. inv H7.
               replace (ofs + 0) with ofs; try lia.

               assert (forall b ofs, 
               Mem.perm m2' b ofs Cur Readable ->
               ZMap.get ofs (Mem.mem_contents m2')!!b = ZMap.get ofs (Mem.mem_contents m2x')!!b). {
                intros. clear H8 ofs. 
                rename H7 into Hperm.
                rename ofs0 into ofs.
                pose proof H as Hw1.
                pose proof H0 as Hw2.
                pose proof H1 as Hw3.
                pose proof H2 as Hw4.
                pose proof H3 as Heq0. pose proof H4 as Heq1. pose proof H5 as Heq1x.
  
                assert (b = b1 \/ b = b2 \/ (b <> b1 /\ b <> b2)). {
                  clear. destruct b; destruct b1; destruct b2; try lia.
                }
                destruct H7 as [B | [B | B]].
                - subst.
                  assert (b1 <> b2 \/ b1 = b2). {
                    clear. destruct b1; destruct b2; lia.
                  }
                  destruct H7.
                  --  
                  eapply Mem.store_mem_contents in H0. rewrite H0.
                  rewrite PMap.gso; trivial.
                  eapply mem_eq_prsv_contents with (ofs:=ofs) (b:=b1) in H4.
                  rewrite H4.
                  eapply Mem.store_mem_contents in H. rewrite H.
                  rewrite PMap.gss.
                  eapply Mem.store_mem_contents in H2. rewrite H2.
                  rewrite PMap.gss.
                  eapply mem_eq_prsv_contents with (ofs:=ofs) (b:=b1) in H5.
                  eapply mem_eq_prsv_contents with (ofs:=ofs) (b:=b1) in H3.
  
                  assert ((ofs < ofs1 \/ ofs >= ofs1 + Z.of_nat (length (encode_val chunk v1))) \/ (ofs1 <= ofs /\ ofs < ofs1 + Z.of_nat (length (encode_val chunk v1)))). {
                    rewrite encode_val_length.
                    rewrite <- size_chunk_conv.
                    clear. 
                    assert (size_chunk chunk > 0). {
                      destruct chunk; simpls; try lia.
                    }
                    destruct ofs; destruct ofs1; simpls; try solve [right; econs; lia]; try solve [left; left; lia]; try solve [left; right; lia]. 
                    all: destruct (size_chunk chunk); tryfalse; try lia.                   
                  }
                  destruct H8 as [OFS | OFS].
                  {
                    pose proof OFS as OFS'.
                    eapply Mem.setN_outside with (c:=(Mem.mem_contents m0)!!b1) in OFS.
                    rewrite OFS.
                    eapply Mem.setN_outside with (c:=(Mem.mem_contents m1x)!!b1) in OFS'.
                    rewrite OFS'.
                    rewrite H5.
                    eapply Mem.store_mem_contents in H1.
                    rewrite H1. rewrite PMap.gso; trivial.
                  }
                  {
                    rewrite setN_inside_nth; trivial.
                    rewrite setN_inside_nth; trivial.
                    assert (Z.to_nat (ofs - ofs1) < length (encode_val chunk v1))%nat. {
                      clear - OFS; lia.
                    }
                    eapply nth_indep; trivial.
                  }
                  {
                    eapply Mem.perm_store_2; eauto.
                    eapply mem_eq_prsv_perm in Heq1; eauto.
                    eapply Mem.perm_store_2; eauto.
                  }
                  {
                    assert (Mem.perm m0 b1 ofs Cur Readable). {
                      eapply Mem.perm_store_2; eauto.
                      eapply mem_eq_prsv_perm in Heq1; eauto.
                      eapply Mem.perm_store_2; eauto.
                    }
                    eapply mem_eq_prsv_perm with (m':=m0') in H8; trivial.
                    eapply Mem.perm_store_1 in Hw3; eauto.
                    eapply mem_eq_prsv_perm; eauto. 
                    eapply mem_eq_sym; trivial.
                  }
                  {
                    eapply Mem.perm_store_2; eauto.
                  }
                  -- destruct H6; tryfalse. subst.
                  eapply Mem.store_mem_contents in H0. rewrite H0.
                  rewrite PMap.gss.
                  eapply Mem.store_mem_contents in H2. rewrite H2.
                  rewrite PMap.gss; trivial.
  
                  assert ((ofs < ofs1 \/ ofs >= ofs1 + Z.of_nat (length (encode_val chunk v1))) \/ (ofs1 <= ofs /\ ofs < ofs1 + Z.of_nat (length (encode_val chunk v1)))). {
                    rewrite encode_val_length.
                    rewrite <- size_chunk_conv.
                    clear. 
                    assert (size_chunk chunk > 0). {
                      destruct chunk; simpls; try lia.
                    }
                    destruct ofs; destruct ofs1; simpls; try solve [right; econs; lia]; try solve [left; left; lia]; try solve [left; right; lia]. 
                    all: destruct (size_chunk chunk); tryfalse; try lia.                   
                  }
  
                  
                  assert ((ofs < ofs2 \/ ofs >= ofs2 + Z.of_nat (length (encode_val chunk v2))) \/ (ofs2 <= ofs /\ ofs < ofs2 + Z.of_nat (length (encode_val chunk v2)))). {
                    rewrite encode_val_length.
                    rewrite <- size_chunk_conv.
                    clear. 
                    assert (size_chunk chunk > 0). {
                      destruct chunk; simpls; try lia.
                    }
                    destruct ofs; destruct ofs2; simpls; try solve [right; econs; lia]; try solve [left; left; lia]; try solve [left; right; lia]. 
                    all: destruct (size_chunk chunk); tryfalse; try lia.                   
                  }
  
  
                  destruct H7 as [OFS1 | OFS1].
                  {
                    pose proof OFS1 as OFS1'.
                    eapply Mem.setN_outside with (c:=(Mem.mem_contents m1x)!!b2) in OFS1.
                    rewrite OFS1.
                    destruct H8 as [OFS2 | OFS2].
                    {
                      pose proof OFS2 as OFS2'.
                      eapply Mem.setN_outside with (c:=(Mem.mem_contents m1)!!b2) in OFS2.
                      rewrite OFS2.
                      eapply mem_eq_prsv_contents in H4.
                      rewrite H4.
                      eapply Mem.store_mem_contents in H.
                      rewrite H.
                      rewrite PMap.gss; trivial.
                      eapply Mem.setN_outside with (c:=(Mem.mem_contents m0)!!b2) in OFS1'. 
                      rewrite OFS1'.
                      eapply mem_eq_prsv_contents in H3.
                      rewrite H3.
  
                      eapply mem_eq_prsv_contents in H5.
                      rewrite H5.
                      eapply Mem.store_mem_contents in H1.
                      rewrite H1.
  
                      rewrite PMap.gss; trivial.
  
                      eapply Mem.setN_outside with (c:=(Mem.mem_contents m0')!!b2) in OFS2'. rewrite OFS2'. trivial.
                      {
                        assert (Mem.perm m0 b2 ofs Cur Readable). {
                          eapply Mem.perm_store_2; eauto.
                          eapply mem_eq_prsv_perm in Heq1; eauto.
                          eapply Mem.perm_store_2; eauto.
                        }
                        eapply mem_eq_prsv_perm with (m':=m0') in H7; trivial.
                        eapply Mem.perm_store_1 in Hw3; eauto.
                        eapply mem_eq_prsv_perm; eauto. 
                        eapply mem_eq_sym; trivial.
                      }
                      {
                        eapply Mem.perm_store_2; eauto.
                        eapply mem_eq_prsv_perm in Heq1; eauto.
                        eapply Mem.perm_store_2; eauto.
                      }
                      {
                        eapply Mem.perm_store_2; eauto.
                      }
                    }
                    { (* ofs inside write 2 range *)
                      rewrite setN_inside_nth; trivial.
                      assert (Z.to_nat (ofs - ofs2) < length (encode_val chunk v2))%nat. {
                        clear - OFS2. lia.
                      }
                      eapply mem_eq_prsv_contents in H5.
                      rewrite H5.
                      eapply Mem.store_mem_contents in H1.
                      rewrite H1.
  
                      rewrite PMap.gss; trivial.
                      rewrite setN_inside_nth; trivial.
                      eapply nth_indep; trivial.
                      {
                        assert (Mem.perm m0 b2 ofs Cur Readable). {
                          eapply Mem.perm_store_2; eauto.
                          eapply mem_eq_prsv_perm in Heq1; eauto.
                          eapply Mem.perm_store_2; eauto.
                        }
                        eapply mem_eq_prsv_perm with (m':=m0') in H8; trivial.
                        eapply Mem.perm_store_1 in Hw3; eauto.
                        eapply mem_eq_prsv_perm; eauto. 
                        eapply mem_eq_sym; trivial.
                      }
                    }
                  }
                  {
                    destruct H8 as [OFS2 | OFS2].
                    { (* ofs inside write 2 range *)
                      pose proof OFS1 as OFS1'.
                      eapply setN_inside_nth in OFS1; trivial.
                      rewrite OFS1.
                      assert (Z.to_nat (ofs - ofs1) < length (encode_val chunk v1))%nat. {
                        clear - OFS1'. lia.
                      }
                      eapply Mem.setN_outside with (c:=(Mem.mem_contents m1)!!b2) in OFS2.
                      rewrite OFS2.
                      eapply mem_eq_prsv_contents in H4.
                      rewrite H4.
                      eapply Mem.store_mem_contents in H.
                      rewrite H.
                      rewrite PMap.gss; trivial.
                      rewrite setN_inside_nth; trivial.
                      eapply nth_indep; trivial.
                      {
                        eapply Mem.perm_store_2; eauto.
                      }
                    }
                    {
                      clear - H6 OFS1 OFS2.
                      rewrite encode_val_length in OFS1, OFS2.
                      rewrite <- size_chunk_conv in OFS1, OFS2.
                      lia.
                    }
                  }
                - subst.
                  assert (b1 <> b2 \/ b1 = b2). {
                    clear. destruct b1; destruct b2; lia.
                  }
                  destruct H7.
                  --  
                  eapply Mem.store_mem_contents in H0. rewrite H0.
                  rewrite PMap.gss; trivial.
                  eapply Mem.store_mem_contents in H2. rewrite H2.
                  rewrite PMap.gso; try lia.
                  eapply mem_eq_prsv_contents with (ofs:=ofs) (b:=b2) in H5.
                  rewrite H5.
                  eapply Mem.store_mem_contents in H1.
                  rewrite H1. rewrite PMap.gss; trivial.
  
                  assert ((ofs < ofs2 \/ ofs >= ofs2 + Z.of_nat (length (encode_val chunk v2))) \/ (ofs2 <= ofs /\ ofs < ofs2 + Z.of_nat (length (encode_val chunk v2)))). {
                    rewrite encode_val_length.
                    rewrite <- size_chunk_conv.
                    clear. 
                    assert (size_chunk chunk > 0). {
                      destruct chunk; simpls; try lia.
                    }
                    destruct ofs; destruct ofs2; simpls; try solve [right; econs; lia]; try solve [left; left; lia]; try solve [left; right; lia]. 
                    all: destruct (size_chunk chunk); tryfalse; try lia.                   
                  }
                  destruct H8 as [OFS | OFS].
                  {
                    pose proof OFS as OFS'.
                    eapply Mem.setN_outside with (c:=(Mem.mem_contents m1)!!b2) in OFS.
                    rewrite OFS.
                    eapply Mem.setN_outside with (c:=(Mem.mem_contents m0')!!b2) in OFS'.
                    rewrite OFS'.
                    
                  eapply mem_eq_prsv_contents in H3.
                  rewrite <- H3.
                  eapply mem_eq_prsv_contents with (ofs:=ofs) (b:=b2) in H4.
                  rewrite H4.
                  
                  eapply Mem.store_mem_contents in H. rewrite H.
                  rewrite PMap.gso; try lia.
                  trivial.
                  {
                    eapply Mem.perm_store_2; eauto.
                  }
                  {
                    eapply Mem.perm_store_2; eauto.
                    eapply mem_eq_prsv_perm in Heq1; eauto.
                    eapply Mem.perm_store_2; eauto.
                  }
                  }
                  {
                    rewrite setN_inside_nth; trivial.
                    rewrite setN_inside_nth; trivial.
                    assert (Z.to_nat (ofs - ofs2) < length (encode_val chunk v2))%nat. {
                      clear - OFS; lia.
                    }
                    eapply nth_indep; trivial.
                  }
                  {
                    assert (Mem.perm m0 b2 ofs Cur Readable). {
                      eapply Mem.perm_store_2; eauto.
                      eapply mem_eq_prsv_perm in Heq1; eauto.
                      eapply Mem.perm_store_2; eauto.
                    }
                    eapply mem_eq_prsv_perm with (m':=m0') in H8; trivial.
                    eapply Mem.perm_store_1 in Hw3; eauto.
                    eapply mem_eq_prsv_perm; eauto. 
                    eapply mem_eq_sym; trivial.
                  }
              -- destruct H6; tryfalse. subst.
                  eapply Mem.store_mem_contents in H0. rewrite H0.
                  rewrite PMap.gss.
                  eapply Mem.store_mem_contents in H2. rewrite H2.
                  rewrite PMap.gss; trivial.
  
                  assert ((ofs < ofs1 \/ ofs >= ofs1 + Z.of_nat (length (encode_val chunk v1))) \/ (ofs1 <= ofs /\ ofs < ofs1 + Z.of_nat (length (encode_val chunk v1)))). {
                    rewrite encode_val_length.
                    rewrite <- size_chunk_conv.
                    clear. 
                    assert (size_chunk chunk > 0). {
                      destruct chunk; simpls; try lia.
                    }
                    destruct ofs; destruct ofs1; simpls; try solve [right; econs; lia]; try solve [left; left; lia]; try solve [left; right; lia]. 
                    all: destruct (size_chunk chunk); tryfalse; try lia.                   
                  }
                  assert ((ofs < ofs2 \/ ofs >= ofs2 + Z.of_nat (length (encode_val chunk v2))) \/ (ofs2 <= ofs /\ ofs < ofs2 + Z.of_nat (length (encode_val chunk v2)))). {
                    rewrite encode_val_length.
                    rewrite <- size_chunk_conv.
                    clear. 
                    assert (size_chunk chunk > 0). {
                      destruct chunk; simpls; try lia.
                    }
                    destruct ofs; destruct ofs2; simpls; try solve [right; econs; lia]; try solve [left; left; lia]; try solve [left; right; lia]. 
                    all: destruct (size_chunk chunk); tryfalse; try lia.                   
                  }
                  destruct H7 as [OFS1 | OFS1].
                  {
                    pose proof OFS1 as OFS1'.
                    eapply Mem.setN_outside with (c:=(Mem.mem_contents m1x)!!b2) in OFS1.
                    rewrite OFS1.
                    destruct H8 as [OFS2 | OFS2].
                    {
                      pose proof OFS2 as OFS2'.
                      eapply Mem.setN_outside with (c:=(Mem.mem_contents m1)!!b2) in OFS2.
                      rewrite OFS2.
                      eapply mem_eq_prsv_contents in H4.
                      rewrite H4.
                      eapply Mem.store_mem_contents in H.
                      rewrite H.
                      rewrite PMap.gss; trivial.
                      eapply Mem.setN_outside with (c:=(Mem.mem_contents m0)!!b2) in OFS1'. 
                      rewrite OFS1'.
                      eapply mem_eq_prsv_contents in H3.
                      rewrite H3.
  
                      eapply mem_eq_prsv_contents in H5.
                      rewrite H5.
                      eapply Mem.store_mem_contents in H1.
                      rewrite H1.
  
                      rewrite PMap.gss; trivial.
  
                      eapply Mem.setN_outside with (c:=(Mem.mem_contents m0')!!b2) in OFS2'. rewrite OFS2'. trivial.
                      {
                        assert (Mem.perm m0 b2 ofs Cur Readable). {
                          eapply Mem.perm_store_2; eauto.
                          eapply mem_eq_prsv_perm in Heq1; eauto.
                          eapply Mem.perm_store_2; eauto.
                        }
                        eapply mem_eq_prsv_perm with (m':=m0') in H7; trivial.
                        eapply Mem.perm_store_1 in Hw3; eauto.
                        eapply mem_eq_prsv_perm; eauto. 
                        eapply mem_eq_sym; trivial.
                      }
                      {
                        eapply Mem.perm_store_2; eauto.
                        eapply mem_eq_prsv_perm in Heq1; eauto.
                        eapply Mem.perm_store_2; eauto.
                      }
                      {
                        eapply Mem.perm_store_2; eauto.
                      }
                    }
                    { (* ofs inside write 2 range *)
                      rewrite setN_inside_nth; trivial.
                      assert (Z.to_nat (ofs - ofs2) < length (encode_val chunk v2))%nat. {
                        clear - OFS2. lia.
                      }
                      eapply mem_eq_prsv_contents in H5.
                      rewrite H5.
                      eapply Mem.store_mem_contents in H1.
                      rewrite H1.
  
                      rewrite PMap.gss; trivial.
                      rewrite setN_inside_nth; trivial.
                      eapply nth_indep; trivial.
                      {
                        assert (Mem.perm m0 b2 ofs Cur Readable). {
                          eapply Mem.perm_store_2; eauto.
                          eapply mem_eq_prsv_perm in Heq1; eauto.
                          eapply Mem.perm_store_2; eauto.
                        }
                        eapply mem_eq_prsv_perm with (m':=m0') in H8; trivial.
                        eapply Mem.perm_store_1 in Hw3; eauto.
                        eapply mem_eq_prsv_perm; eauto. 
                        eapply mem_eq_sym; trivial.
                      }
                    }
                  }
                  {
                    destruct H8 as [OFS2 | OFS2].
                    { (* ofs inside write 2 range *)
                      pose proof OFS1 as OFS1'.
                      eapply setN_inside_nth in OFS1; trivial.
                      rewrite OFS1.
                      assert (Z.to_nat (ofs - ofs1) < length (encode_val chunk v1))%nat. {
                        clear - OFS1'. lia.
                      }
                      eapply Mem.setN_outside with (c:=(Mem.mem_contents m1)!!b2) in OFS2.
                      rewrite OFS2.
                      eapply mem_eq_prsv_contents in H4.
                      rewrite H4.
                      eapply Mem.store_mem_contents in H.
                      rewrite H.
                      rewrite PMap.gss; trivial.
                      rewrite setN_inside_nth; trivial.
                      eapply nth_indep; trivial.
                      {
                        eapply Mem.perm_store_2; eauto.
                      }
                    }
                    {
                      clear - H6 OFS1 OFS2.
                      rewrite encode_val_length in OFS1, OFS2.
                      rewrite <- size_chunk_conv in OFS1, OFS2.
                      lia.
                    }
                  }
                - destruct B as [B1 B2].
                eapply Mem.store_mem_contents in H0. rewrite H0.
                rewrite PMap.gso; trivial. 
                eapply mem_eq_prsv_contents with (ofs:=ofs) (b:=b) in H4.
                rewrite H4.
                eapply Mem.store_mem_contents in H. rewrite H.
                rewrite PMap.gso; trivial.
                eapply mem_eq_prsv_contents with (ofs:=ofs) (b:=b) in H3.
                rewrite H3.
                eapply Mem.store_mem_contents in H2. rewrite H2.
                rewrite PMap.gso; trivial.
                eapply mem_eq_prsv_contents with (ofs:=ofs) (b:=b) in H5.
                rewrite H5.
                eapply Mem.store_mem_contents in H1. rewrite H1.
                rewrite PMap.gso; trivial.
                {
                  assert (Mem.perm m0 b ofs Cur Readable). {
                    eapply Mem.perm_store_2; eauto.
                    eapply mem_eq_prsv_perm in Heq1; eauto.
                    eapply Mem.perm_store_2; eauto.
                  }
                  eapply mem_eq_prsv_perm with (m':=m0') in H7; trivial.
                  eapply Mem.perm_store_1 in Hw3; eauto.
                  eapply mem_eq_prsv_perm; eauto. 
                  eapply mem_eq_sym; trivial.
                }
                {
                  eapply Mem.perm_store_2; eauto.
                  eapply mem_eq_prsv_perm in Heq1; eauto.
                  eapply Mem.perm_store_2; eauto.
                }
                {
                  eapply Mem.perm_store_2; eauto.
                }
               }
               rewrite H7. 
               destruct (ZMap.get ofs (Mem.mem_contents m2x')!!b3); econs; eauto.
               destruct v; econs; eauto.
               rewrite Integers.Ptrofs.add_zero. trivial. 
               assert (Mem.perm m0' b3 ofs Cur Readable). {
                  eapply Mem.perm_store_2; eauto.
                  eapply mem_eq_prsv_perm in H5; eauto.
                  eapply Mem.perm_store_2; eauto.
                }
               assert (Mem.perm m0 b3 ofs Cur Readable). {
                  eapply mem_eq_prsv_perm; eauto.
                  eapply mem_eq_sym; trivial.
                }
                  eapply Mem.perm_store_1; eauto.
                  eapply mem_eq_prsv_perm with (m:=m1'). eapply mem_eq_sym; trivial.
                  eapply Mem.perm_store_1; eauto.
          + intros.
            assert (Mem.perm m0 b ofs k p). {
              eapply Mem.perm_store_2; eauto.
              eapply mem_eq_prsv_perm in H4; eauto.
              eapply Mem.perm_store_2; eauto.
            }
            assert (Mem.perm m2x' b ofs k p). {
              eapply Mem.perm_store_1; eauto.
              eapply mem_eq_prsv_perm with (m:=m1x'). eapply mem_eq_sym; trivial.
              eapply Mem.perm_store_1; eauto.
              eapply mem_eq_prsv_perm; eauto.
            }
            left; trivial.
    Qed.

    Definition eq (st st': t): Prop := 
        let '(ge, env, m) := st in
        let '(ge', env', m') := st' in
        ge = ge' /\ env = env' /\ mem_eq m m'.

    Lemma eq_sym:
        forall st st', eq st st' -> eq st' st.
    Proof. intros. unfolds eq. 
      destruct st as [[ge e] m]. destruct st' as [[ge' e'] m'].
      destruct H as (Hge & He & Hmf & Hmb).
      splits; subst; trivial. 
      unfold mem_eq; split; trivial.
    Qed.

    Lemma eq_refl:
        forall st, eq st st.
    Proof.
        intros. unfold eq. destruct st eqn:Hst; destruct p eqn:Hp; splits; trivial.
        unfold mem_eq. split.
        all: eapply Mem.extends_refl.
    Qed.

    Lemma eq_trans:
        forall st1 st2 st3, eq st1 st2 -> eq st2 st3 -> eq st1 st3.
    Proof. 
      intros. 
      destruct st1 as [[ge1 e1] m1]. 
      destruct st2 as [[ge2 e2] m2]. 
      destruct st3 as [[ge3 e3] m3].
      unfolds eq. 
      destruct H as (Hge1 & He1 & Hmf & Hmb).
      destruct H0 as (Hge2 & He2 & Hmf' & Hmb').
      splits; subst; eauto. unfold mem_eq. split.
      eapply Mem.extends_extends_compose; eauto.
      eapply Mem.extends_extends_compose; eauto.
    Qed.      

    Lemma advance_store_valid:
      forall chunk1 m1 b1 ofs1 v1 chunk2 m2 b2 ofs2 v2 m3 m2',
        Mem.store chunk1 m1 b1 ofs1 v1 = Some m2 ->
        mem_eq m2 m2' ->
        Mem.store chunk2 m2' b2 ofs2 v2 = Some m3 ->
        exists m2'',
          Mem.store chunk2 m1 b2 ofs2 v2 = Some m2''.
    Proof.
      intros.
      eapply Mem.store_valid_access_2 
        with (chunk':=chunk2) (b':=b2) (ofs':=ofs2) (p:=Writable) in H.
      eapply Mem.valid_access_store with (v:=v2) in H. destruct H. 
      exists x; trivial.
      eapply Mem.store_valid_access_3 in H1.
      destruct H0 as (_ & B).
      eapply Mem.valid_access_extends; eauto.
    Qed.

    Fixpoint calc_offset_helper (bounds subs: list Z) (sz: Z): option Z :=
        match bounds, subs with
        | [], [] => Some 0%Z
        | b::bounds', s::subs' => 
            if (b <=? s)%Z then None else
            match calc_offset_helper bounds' subs' (sz * b) with
            | None => None
            | Some ofs => Some (ofs + sz * s)%Z
            end
        | _, _ => None
        end
    .

    Definition calc_offset (ty: CTy.arrtype) (sub: list Z): option Z := 
      match ty with
      | CTy.arr_type_intro ty bounds =>
        if Nat.eqb (length bounds) (length sub) 
          && forallb (fun bd => (bd >? 0)%Z) bounds
          && forallb (fun s => (s >=? 0)%Z) sub
        then
          calc_offset_helper (List.rev bounds) (List.rev sub) (CTy.basetype_size ty)
        else None
      end
    .

    Example calc_offset_example:
        calc_offset (CTy.arr_type_intro (CTy.int32s) [10;10;10]%Z) [1;2;3]%Z = Some 492%Z.
        (* 3*4 + 2*(10*4) + (1*(10*10*4))*)
    Proof. simpl. reflexivity. Qed.

    
    Lemma calc_offset_helper_same_bounds_same_length:
      forall bounds sub1 sub2 sz ofs1 ofs2,
        calc_offset_helper bounds sub1 sz = Some ofs1 ->
        calc_offset_helper bounds sub2 sz = Some ofs2 ->
        length sub1 = length sub2.
    Proof. 
      induction bounds.
      - intros. simpls. destruct sub1; destruct sub2; tryfalse. trivial.
      - intros. simpls.
        destruct sub1 eqn:Hsub1; tryfalse. 
        destruct sub2 eqn:Hsub2; tryfalse.
        destruct (a <=? z); destruct (a <=? z0); tryfalse.
        destruct (calc_offset_helper bounds l (sz * a)) eqn:Hofs1; tryfalse.
        destruct (calc_offset_helper bounds l0 (sz * a)) eqn:Hofs2; tryfalse.
        simpls. f_equal. 
        eapply IHbounds; eauto.
    Qed. 


    Lemma calc_offset_helper_correct:
      forall bounds sub1 sub2 sz ofs1 ofs2,
        calc_offset_helper bounds sub1 sz = Some ofs1 ->
        calc_offset_helper bounds sub2 sz = Some ofs2 ->
        ~ sub1 =v= sub2 ->
        Forall (fun bd => (bd > 0)%Z) bounds ->
        Forall (fun s1 => (s1 >= 0)%Z) sub1 ->
        Forall (fun s2 => (s2 >= 0)%Z) sub2 ->
        sz > 0 ->
        ofs1 + sz <= ofs2 \/ ofs2 + sz <= ofs1.
    Proof.
      induction bounds.
      - intros. simpls.
        destruct sub1; destruct sub2; tryfalse.
        exfalso. eapply H1. eapply veq_refl.
      - intros. simpls.
        destruct sub1 eqn:Hsub1; destruct sub2 eqn:Hsub2; tryfalse.
        rename z into z1; rename l into l1.
        rename z0 into z2; rename l0 into l2. rename a into bd.
        destruct (bd <=? z1) eqn:Hbd1; tryfalse.
        destruct (bd <=? z2) eqn:Hbd2; tryfalse.
        destruct (calc_offset_helper bounds l1 (sz * bd)) eqn:Hofs1; tryfalse.
        destruct (calc_offset_helper bounds l2 (sz * bd)) eqn:Hofs2; tryfalse.
        inv H; inv H0.
        assert (z1 = z2 \/ z1 <> z2). { lia. }
        destruct H.
        + subst. 
          assert (~l1 =v= l2). {
            clear - H1. intro. apply H1.
            rewrite H. eapply veq_refl.
          }
          assert (bd > 0). {inv H2; trivial. }
          assert (z2 >= 0). {inv H3; trivial. }
          eapply IHbounds with (sz:=sz*bd) in H; eauto.
          destruct H.
          (** each bound should > 0; each subscript should >= 0. *)  
          -- left.
          assert (z2 = 0 \/ z2 > 0). { lia. }
          destruct H7. {
            subst. 
            cut (z + sz <= z0); try lia.
            clear - H5 H0 H.
            cut (z + sz <= z + sz * bd); try lia.
            eapply Zplus_le_compat_l.
            replace sz with (sz * 1%Z) at 1; try lia.
            eapply OrdersEx.Z_as_OT.mul_le_mono_nonneg_l; try lia.
          }
          eapply OrdersEx.Z_as_OT.leb_gt in Hbd1.
          clear - Hbd1 H H0 H5 H7.
          cut (z + sz * bd + sz <= z0 + sz * z2).
          {
            intro.
            cut (z + sz * z2 + sz <= z + sz * bd + sz).
            intro. lia.
            eapply Zplus_le_compat_r.
            eapply Zplus_le_compat_l.
            eapply Zmult_le_compat_l; try lia.
          }
          eapply OrdersEx.Z_as_DT.add_le_mono; try lia.
          replace sz with (sz * 1%Z) at 1; try lia.
          eapply OrdersEx.Z_as_OT.mul_le_mono_nonneg_l; try lia.
          -- right. 
            assert (z2 = 0 \/ z2 > 0). { lia. }
            destruct H7. {
              subst. 
              cut (z0 + sz <= z); try lia.
              clear - H5 H0 H.
              cut (z0 + sz <= z0 + sz * bd); try lia.
              eapply Zplus_le_compat_l.
              replace sz with (sz * 1%Z) at 1; try lia.
              eapply OrdersEx.Z_as_OT.mul_le_mono_nonneg_l; try lia.
            }
            eapply OrdersEx.Z_as_OT.leb_gt in Hbd1.
            clear - Hbd1 H H0 H5 H7.
            cut (z0 + sz * bd + sz <= z + sz * z2).
            {
              intro.
              cut (z0 + sz * z2 + sz <= z0 + sz * bd + sz).
              intro. lia.
              eapply Zplus_le_compat_r.
              eapply Zplus_le_compat_l.
              eapply Zmult_le_compat_l; try lia.
            }
            eapply OrdersEx.Z_as_DT.add_le_mono; try lia.
            replace sz with (sz * 1%Z) at 1; try lia.
            eapply OrdersEx.Z_as_OT.mul_le_mono_nonneg_l; try lia.
          -- inv H2; trivial.
          -- inv H3; trivial.   
          -- inv H4; trivial.
          -- lia.
        + assert (z1 < z2 \/ z2 < z1). {lia. }
        assert (l1 =v= l2 \/ ~l1 =v= l2). {tauto. }
        assert (bd > 0). {inv H2; trivial. }
        assert (z1 >= 0). {inv H3; trivial. }
        assert (z2 >= 0). {inv H4; trivial. }
        assert (z1 < bd). {lia. }
        assert (z2 < bd). {lia. }
        destruct H6.
        ++ (* if remained eq, then z = z0 *)
          assert (z = z0). {
            assert (l1 = l2). {
              clear - Hofs1 Hofs2 H6.
              assert (length l1 = length l2). {
                eapply calc_offset_helper_same_bounds_same_length; eauto.
              }
              eapply same_length_eq; trivial.
            }
            subst.
            rewrite Hofs1 in Hofs2. inv Hofs2; trivial.
          }
          subst. 
          destruct H0.
          -- left.
            replace (z0 + sz * z1 + sz) with (z0 + sz * (z1 + 1)); try lia.
            eapply Zplus_le_compat_l.
            eapply Zmult_le_compat_l; try lia.
          -- right.
            replace (z0 + sz * z2 + sz) with (z0 + sz * (z2 + 1)); try lia.
            eapply Zplus_le_compat_l.
            eapply Zmult_le_compat_l; try lia.
        ++ rename z into ofs1. rename z0 into ofs2.
          eapply IHbounds with (sz:=sz*bd) in H6; eauto; try lia.
          (* the outest dimension decide ofs order *)
          (* note that, z1 z2 are the innest dimension *)
          (* so it do not contribute to order *)
          destruct H6.
          -- left. clear H H0.
            replace (ofs1 + sz * z1 + sz) with (ofs1 + sz * (z1 + 1)); try lia.
            cut (ofs1 + sz* (z1 + 1) <= ofs1 + sz * bd); try lia.
            eapply Zplus_le_compat_l.
            eapply Zmult_le_compat_l; try lia.
          -- right. clear H H0.
            replace (ofs2 + sz * z2 + sz) with (ofs2 + sz * (z2 + 1)); try lia.
            cut (ofs2 + sz* (z2 + 1) <= ofs2 + sz * bd); try lia.
            eapply Zplus_le_compat_l.
            eapply Zmult_le_compat_l; try lia.
          -- inv H2; trivial.
          -- inv H3; trivial.
          -- inv H4; trivial.
    Qed.

    

    Lemma calc_offset_different_sub_implies_disjoint:
      forall aty chunk sub1 sub2 ofs1 ofs2,
        calc_offset aty sub1 = Some ofs1 ->
        calc_offset aty sub2 = Some ofs2 ->
        ~ veq sub1 sub2 ->
        CTy.basetype_access_mode (CTy.basetype_of_arrtype aty) = By_value chunk ->
        (ofs1 + size_chunk chunk <= ofs2)%Z \/ (ofs2 + size_chunk chunk <= ofs1)%Z.
    Proof.
      intros. 
      unfolds calc_offset.
      destruct aty eqn:Haty.
      destruct ( (length l =? length sub1)%nat && forallb (fun bd : Z => bd >? 0) l &&
      forallb (fun s : Z => s >=? 0) sub1)%nat eqn:Hlen1; tryfalse.
      destruct ( (length l =? length sub2)%nat && forallb (fun bd : Z => bd >? 0) l &&
      forallb (fun s : Z => s >=? 0) sub2)%nat eqn:Hlen2; tryfalse.
      do 2 rewrite andb_true_iff in Hlen1.
      do 2 rewrite andb_true_iff in Hlen2.
      destruct Hlen1 as ((Hlen1 & Hbd1) & Hsub1).
      destruct Hlen2 as ((Hlen2 & Hbd2) & Hsub2).
      eapply Nat.eqb_eq in Hlen1, Hlen2. rewrite Hlen1 in Hlen2.
      simpls. 
      eapply CTy.basety_size_eq_size_chunk in H2.
      rewrite H2 in H, H0.
      eapply calc_offset_helper_correct 
        with (bounds:=List.rev l) (sub1:=List.rev sub1) (sub2:=List.rev sub2); eauto.
      clear - H1 Hlen2. intro. apply H1.
      eapply veq_implies_rev_veq in H; eauto.
      do 2 rewrite List.rev_involutive in H. trivial.
      do 2 rewrite List.rev_length; trivial. 
      {
        eapply Forall_forall. intros.
        eapply forallb_forall with (x:=x) in Hbd1.
        lia. eapply in_rev; trivial.
      }
      {
        eapply Forall_forall. intros.
        eapply forallb_forall with (x:=x) in Hsub1.
        lia. eapply in_rev; trivial.
      }
      {
        eapply Forall_forall. intros.
        eapply forallb_forall with (x:=x) in Hsub2.
        lia. eapply in_rev; trivial.
      }
      {
        clear - H2. unfold CTy.basetype_size in H2.
        destruct b. simpls. lia.
      }
    Qed.

    Definition valid (id: ident) (ty: Ty.t) (st: t): Prop := 
      let '(ge, e, m) := st in
      forall b ty', 
        get_var_loc_type st id = Some (b, ty') /\
        Ty.of_compcert_arrtype ty' = Some ty /\
        Mem.range_perm m b 0 (sizeof ge ty') Cur Writable. 


    Inductive read_cell: MemCell -> Ty.basetype -> val -> t -> Prop :=
    | read_cell_intro: 
        forall cell v st id sub ge e m b ty ofs ty' basety chunk,
            cell = {| arr_id := id; arr_index := sub |} ->
            get_var_loc_type st id = Some (b, ty) ->
            st = (ge, e, m) ->
            CTy.of_compcert_arrtype ty = Some ty' ->
            CTy.basetype_of_arrtype ty' = basety -> 
            (* no semantics cast at this level *)
            calc_offset ty' sub = Some ofs ->
            CTy.basetype_access_mode basety = By_value chunk -> 
            Mem.load chunk m b ofs = Some v ->
            read_cell cell basety v st
    .

    Definition write_cell_dec (cell: MemCell) (basety: Ty.basetype) (v: val) (st: t): option t := 
        let '(ge, e, m) := st in
        let arr_id := cell.(arr_id) in
        let sub := cell.(arr_index) in
        let blk_ty := get_var_loc_type st arr_id
        in
        match blk_ty with
        | None => None
        | Some (b, ty) =>
            match CTy.of_compcert_arrtype ty with
            | Some ty' => 
                if CTy.basetype_eqb (CTy.basetype_of_arrtype ty') basety
                then 
                    match calc_offset ty' sub with
                    | None => None
                    | Some ofs => 
                        match CTy.basetype_access_mode basety with
                        | By_value chunk => 
                            match Mem.store chunk m b ofs v with
                            | None => None
                            | Some m' => Some (ge, e, m')
                            end
                        | _ => None
                        end
                    end
                else None
            | None => None
            end
        end
    .

    Inductive write_cell: MemCell -> Ty.basetype -> val -> t -> t -> Prop :=
    | write_cell_intro: 
        forall cell v st st' st0 st0' id sub ge e m m' b ty ofs ty' basety chunk,
            cell = {| arr_id := id; arr_index := sub |} ->
            st = (ge, e, m) ->
            get_var_loc_type st id = Some (b, ty) ->
            CTy.of_compcert_arrtype ty = Some ty' ->
            CTy.basetype_of_arrtype ty' = basety -> 
            (* no semantics cast at this level *)
            calc_offset ty' sub = Some ofs ->
            CTy.basetype_access_mode basety = By_value chunk -> 
            Mem.store chunk m b ofs v = Some m' ->
            st' = (ge, e, m') ->
            eq st st0 ->
            eq st' st0' ->
            write_cell cell basety v st0 st0'
    .

    Lemma write_cell_dec_correct:
        forall cell v st st' bty,
            write_cell_dec cell bty v st = Some st' -> write_cell cell bty v st st'.
    Proof.
      intros.
      unfold write_cell_dec in H.
      destruct st as [[ge e] m].
      destruct (get_var_loc_type (ge, e, m) (arr_id cell)) eqn:Heid; tryfalse.
      destruct p as (b, ty).
      destruct (CTy.of_compcert_arrtype ty) eqn:Hty; simpls; tryfalse.
      rename a into ty'.
      destruct (CTy.basetype_eqb (CTy.basetype_of_arrtype ty') bty) eqn:Hbty; simpls; tryfalse.
      destruct (calc_offset ty' (arr_index cell)) eqn:Hofs; simpls; tryfalse.
      destruct (CTy.basetype_access_mode bty) eqn:Hchunk; simpls; tryfalse.
      rename m0 into chunk.
      destruct (Mem.store chunk m b z v) eqn:Hm'; simpls; tryfalse.
      inv H.
      destruct cell eqn:Hcell; simpls.
      econs; eauto.
      eapply CTy.basetype_eqb_eq in Hbty; trivial.
      eapply eq_refl.
      eapply eq_refl.
    Qed.


        (* It would be easy to further weaken this condition retricting only on free vars of the fragment, no imposing non-aliasing on invisible programs. *)
    (* Of little significance, so we currently omit. *)
    Definition non_alias  (st: t): Prop :=
        forall id1 id2 b1 b2 (ty1 ty2: Ctypes.type),
          (* List.In id1 vars -> List.In id2 vars -> *)
          get_var_loc_type st id1 = Some (b1, ty1) ->
          get_var_loc_type st id2 = Some (b2, ty2) ->
          id1 <> id2 -> 
          b1 <> b2.
    

  Lemma write_cell_prsv_env:
  forall cell bty v st st' ge e m ge' e' m',
      write_cell cell bty v st st' ->
      st = (ge, e, m) ->
      st' = (ge', e', m') ->
      ge = ge' /\ e = e'.
  Proof.
    intros.
    inv H0. 
    inv H. inv H10. 
    inv H9. splits; trivial. destruct H0; destruct H1; subst; trivial.
  Qed.

    Lemma write_cell_prsv_nonalias:
      forall cell bty v st st',
        write_cell cell bty v st st' ->
        non_alias st ->
        non_alias st'.
    Proof. 
      intros. unfolds non_alias.
      intros.
      destruct st as [[ge e] m].
      destruct st' as [[ge' e'] m'].
      eapply write_cell_prsv_env in H; eauto.
      destruct H; subst.
      eapply H0; eauto.
    Qed.

    Lemma eq_prsv_nonalias:
      forall st st',
        eq st st' ->
        non_alias st ->
        non_alias st'.
    Proof. 
      intros. unfolds non_alias. unfolds eq.
      destruct st as [[ge e] m].
      destruct st' as [[ge' e'] m'].
      intros. 
      destruct H as (Hge & He & Hmf & Hmb). subst. 
      eapply H0; eauto.
    Qed.

    Lemma read_cell_stable_under_eq:
      forall rc ty v st1 st1',
        eq st1 st1' ->
        read_cell rc ty v st1 ->
        read_cell rc ty v st1'.
    Proof.
      intros. 
      destruct st1 as [[ge1 e1] m1].
      destruct st1' as [[ge1' e1'] m1'].
      unfolds eq. destruct H as (Hge & He & Hmf & Hmb). subst.
      inv H0.
      econs; eauto. inv H2.
      eapply Mem.load_extends with (m2:=m1') in Hmf; eauto.
      destruct Hmf as (v' & Hload & Hext).
      eapply Mem.load_extends with (m2:=m) in Hmb; eauto.
      destruct Hmb as (v'' & Hload' & Hext').
      rewrite Hload. f_equal.
      rewrite H7 in Hload'. inv Hload'.
      clear - Hext Hext'.
      inv Hext. inv Hext'; eauto.
      inv Hext'; trivial.
    Qed.

    Lemma write_cell_stable_under_eq:
      forall wc ty v st1 st1' st2 st2',
        eq st1 st1' ->
        eq st2 st2' ->
        write_cell wc ty v st1 st2 ->
        write_cell wc ty v st1' st2'.
    Proof. 
      intros.
      destruct st1 as [[ge1 e1] m1].
      destruct st1' as [[ge1' e1'] m1'].
      destruct st2 as [[ge2 e2] m2].
      destruct st2' as [[ge2' e2'] m2'].
      unfolds eq. 
      destruct H as (Hge1 & He1 & Hmf1 & Hmb1). subst.
      destruct H0 as (Hge2 & He2 & Hmf2 & Hmb2). subst.
      inv H1. 
      eapply write_cell_intro; eauto. 
      clear - Hmf1 Hmb1 H9 H10.
      unfolds eq.
      destruct H9 as (Hge & He & Hmf & Hmb). subst.
      destruct H10 as (Hge' & He' & Hmf' & Hmb'). subst.
      splits; trivial. 
      unfold mem_eq. split.
      eapply Mem.extends_extends_compose; eauto.
      eapply Mem.extends_extends_compose; eauto.
      unfolds eq.
      destruct H9 as (Hge & He & Hmf & Hmb). subst.
      destruct H10 as (Hge' & He' & Hmf' & Hmb'). subst.
      splits; trivial. unfold mem_eq; split. 
      eapply Mem.extends_extends_compose; eauto.
      eapply Mem.extends_extends_compose; eauto.
    Qed.

    (* currently, we only suppose single basetype int32s here, so no compatibility problem for access "size"*)
    Lemma write_after_write_cell_neq:
        forall cell1 cell2 v1 v2 st1 st2 st3 st2' bty bty',
            write_cell cell1 bty v1 st1 st2 -> 
            write_cell cell2 bty' v2 st2 st3 ->
            cell_neq cell1 cell2 ->
            write_cell cell2 bty' v2 st1 st2' ->
            non_alias st1 ->
            exists st3',
            write_cell cell1 bty v1 st2' st3' /\ eq st3 st3'.
    Proof.
      intros until bty'. intros Hw1 Hw2 Hneq Hw2' Halias.
      destruct st1 as [[ge1 e1] m1].
      destruct st2 as [[ge2 e2] m2].
      destruct st2' as [[ge2' e2'] m2'].
      destruct st3 as [[ge3 e3] m3].
      inv Hw1. inv Hw2. inv Hw2'.
      inv H.

      destruct H15 as (Hge1 & He1 & Hm1 ); subst.
      destruct H16 as (Hge2 & He2 & Hm2); subst.
      destruct H22 as (Hge2' & He2' & Hm2'); subst.
      destruct H23 as (Hge3 & He3 & Hm3); subst.
      destruct H8 as (Hge & He & Hm);
      destruct H9 as (Hge' & He' & Hm'); subst.

      rename ge3 into ge. rename e3 into e. 
      rename b1 into b2; rename ofs1 into ofs2. 
      rename b into b1; rename ofs into ofs1.
      rename m1 into m0'. rename m0 into m1''.
      rename m into m0. rename m' into m1.
      rename m2 into m1'.
      rename m'0 into m2. 
      rename m4 into m0''. rename m'1 into m1x. rename m2' into m1x'.
      rename m3 into m2'.
      rename id1 into id2. rename id into id1. 
      rename sub1 into sub2. rename sub into sub1.
      rename ty1 into ty2. 
      assert (b0 = b2 /\ ty0 = ty2). {
        clear - H3 H10. simpls.
        rewrite H3 in H10. inv H10; split; trivial.
      }
      destruct H; subst. 
      rewrite H7 in H14. inv H14. rename ty'1 into ty2'.
      clear H17 H3. 
      rewrite H11 in H18. inv H18.
      rewrite H12 in H19. inv H19. rename chunk1 into chunk2. rename chunk into chunk1.
      rename ty into ty1. rename ty' into ty1'.
      assert (chunk1 = chunk2). {
        clear - H5 H12.
        destruct ty1'; destruct ty2'; simpls.
        destruct b; destruct b0; simpls. rewrite H5 in H12. inv H12; trivial.
      }
      subst. rename chunk2 into chunk.
      rename H6 into Hw1. rename H13 into Hw2.
      rename H20 into Hw2'.
      (**
      write 1 then write 2:
      (<m0>, m0', m0'') --- b1,ofs1,v1 --> (<m1>, m1', m1'') --- b2,ofs2,v2 --> (<m2>, m2')

      write 2 then write 1:
      (m0, m0', <m0''>) --- b2,ofs2,v2 --> (<m1x>, m1x') --- b1,ofs1,v1 --> [<m2x>]
      
      The m2x is what we need.
      **)

      assert (exists m2x, 
        Mem.store chunk m1x' b1 ofs1 v1 = Some m2x /\ mem_eq m2x m2'). {
        (* first we try to prove there is m2x after storation in m1x', because of valid_access *)
        assert (Mem.valid_access m1x' chunk b1 ofs1 Writable). {
          eapply Mem.store_valid_access_3 in Hw2.
          eapply mem_eq_prsv_valid_access with (m':=m1) in Hw2.
          2: {
            clear - Hm' Hm1. eapply mem_eq_trans; eauto. eapply mem_eq_sym; trivial.
          }
          eapply Mem.store_valid_access_3 in Hw1.
          eapply mem_eq_prsv_valid_access with (m':=m0'') in Hw1.
          2: {
            clear - Hm Hm2'. eapply mem_eq_trans; eauto. eapply mem_eq_sym; trivial.
          } 
          eapply Mem.store_valid_access_1  in Hw2'; eauto.
          eapply mem_eq_prsv_valid_access; eauto.
        }
        eapply Mem.valid_access_store with (v:=v1) in H.
        destruct H as (m2x & Hw2x).
        exists m2x. split; trivial.
        (* then we prove the constructed m2x mem_eq to m2', as they just swap the last two disjoint writes. *)
        assert (mem_eq m2 m2x). {
          eapply swap_store_cell_neq_prsv_mem_eq
            with (chunk:=chunk) (m1:=m1'') (b2:=b2) (ofs2:=ofs2) (v2:=v2)
            (m1x':=m1x) (m0':=m0'') (m1x:=m1x') (m0:=m0) (m1':=m1)
            ; eauto.
          - eapply mem_eq_trans; eauto. eapply mem_eq_sym; trivial.
          - eapply mem_eq_trans; eauto. eapply mem_eq_sym; trivial.
          - eapply mem_eq_sym; trivial.
          - 
            unfold cell_neq in Hneq. simpl in Hneq. destruct Hneq.
            {
              left. eapply Halias; eauto. 
            }  
            {
              assert (id1 = id2 \/ id1 <> id2). {
                clear. destruct id1; destruct id2; simpls; try lia.
              }
              destruct H0. 2: {  
                eapply Halias in H0; eauto. 
              }
              right. subst. 
              assert (b1 = b2 /\ ty1 = ty2). {
                clear - H1 H10.
                simpls. rewrite H1 in H10. inv H10; split; trivial.
              } destruct H0; subst. rename b2 into b; rename ty2 into ty. 
              rewrite H2 in H7. inv H7. rename ty2' into ty'.
              rewrite H5 in H12. inv H12.
              
              eapply calc_offset_different_sub_implies_disjoint; eauto.
            }
        }
        eapply mem_eq_trans; eauto. eapply mem_eq_sym; trivial.
      }

      destruct H as (m2x & Hm2x & Hmeq).
      exists (ge, e, m2x). split.
      2: { splits; simpl; trivial. eapply mem_eq_sym; trivial. }
      eapply write_cell_intro with 
        (st:=(ge, e, m1x')) (st0':=(ge, e, m2x)) ; eauto.
      all: try eapply eq_refl.
    Qed.



    Lemma read_after_write_cell_neq:
      forall wc rc v1 v2 st st' bty bty',
          write_cell wc bty v1 st st' -> 
          cell_neq wc rc ->
          non_alias st ->
          read_cell rc bty' v2 st <->
          read_cell rc bty' v2 st'.
    Proof.
      intros. split; intro.
      - 
        destruct st as [[ge e] m].
        destruct st' as ((ge', e'), m').
        inv H.

        eapply read_cell_stable_under_eq with (st1':=(ge,e,m0)) in H2.
        2: { clear - H12. simpls. splits; trivial.  
          destruct H12 as (Hge & He & Hm). destruct Hm. split; trivial.
        }

        inversion_clear H2.
        inv H4.

        unfold cell_neq in H0. simpl in H0.
        unfolds eq. 
        destruct H12 as (Hge & He & Hm); subst.
        destruct H13 as (Hge' & He' & Hm'); subst. 
        
        eapply read_cell_stable_under_eq with (st1:=(ge', e', m'0)).
        { simpls. splits; trivial. }
        
        rename H10 into Hstore.
        eapply Mem.store_storebytes in Hstore.
        destruct H0.
        
        -- (* id neq *) 
          eapply read_cell_intro; eauto.
          rewrite <- H16.
          eapply Mem.load_storebytes_other
          with (b:=b) (ofs:=ofs) (bytes:=(encode_val chunk v1)); eauto. 
        -- (* subscript neq *)
          econs; eauto. rewrite <- H16.
          eapply Mem.load_storebytes_other
          with (b:=b) (ofs:=ofs) (bytes:=(encode_val chunk v1)); eauto; trivial.
          assert (id = id0 \/ id <> id0). {
            clear. destruct id; destruct id0; simpls; try lia.
          }
          destruct H0. 2: {  
            unfold non_alias in H1.
            eapply H1 with (id1:=id) (b1:=b) (id2:=id0) (b2:=b0) in H0; eauto. 
          }
          right. subst. rewrite H5 in H3. inv H3. 
          rewrite H6 in H7. inv H7. rename ty'0 into aty.
          rewrite H9 in H15. inv H15.
          rewrite encode_val_length.
          rewrite <- size_chunk_conv.
          eapply calc_offset_different_sub_implies_disjoint; eauto.
          intro. eapply H. 
          eapply veq_sym; trivial.
      - 
          destruct st as [[ge e] m].
          destruct st' as ((ge', e'), m').
          inv H.
  
          eapply read_cell_stable_under_eq with (st1':=(ge,e,m'0)) in H2.
          2: { 
            clear - H12 H13. simpls.
            destruct H13 as (Hge & He & Hm); subst.
            destruct H12 as (Hge' & He' & Hm'); subst. 
            splits; trivial.  
            destruct Hm. destruct Hm'. split.
            eapply Mem.extends_extends_compose; eauto. eapply Mem.extends_refl.
            eapply Mem.extends_extends_compose; eauto. eapply Mem.extends_refl.
          }
  
          inversion_clear H2.
          inv H4.
  
          unfold cell_neq in H0. simpl in H0.
          unfolds eq. 
          destruct H12 as (Hge & He & Hm); subst.
          destruct H13 as (Hge' & He' & Hm'); subst. 
          
          eapply read_cell_stable_under_eq with (st1:=(ge', e', m0)).
          { simpls. splits; trivial. }
          
          rename H10 into Hstore.
          eapply Mem.store_storebytes in Hstore.
          destruct H0.
          
          -- (* id neq *) 
            eapply read_cell_intro; eauto.
            rewrite <- H16.
            symmetry.
            eapply Mem.load_storebytes_other
            with (b:=b) (ofs:=ofs) (bytes:=(encode_val chunk v1)); eauto. 
          -- (* subscript neq *)
            econs; eauto. rewrite <- H16.
            symmetry.
            eapply Mem.load_storebytes_other
            with (b:=b) (ofs:=ofs) (bytes:=(encode_val chunk v1)); eauto; trivial.
            assert (id = id0 \/ id <> id0). {
              clear. destruct id; destruct id0; simpls; try lia.
            }
            destruct H0. 2: {  
              unfold non_alias in H1.
              eapply H1 with (id1:=id) (b1:=b) (id2:=id0) (b2:=b0) in H0; eauto. 
            }
            right. subst. 
            assert (b = b0 /\ ty = ty0). {
              clear - H3 H5.
              simpls. rewrite H5 in H3. inv H3; trivial. split; trivial.
            }
            destruct H0; subst.
            rewrite H6 in H7. inv H7. rename ty'0 into aty.
            rewrite H9 in H15. inv H15.
            rewrite encode_val_length.
            rewrite <- size_chunk_conv.
            eapply calc_offset_different_sub_implies_disjoint; eauto.
            intro. eapply H. 
            eapply veq_sym; trivial.
  Qed.
    
  Lemma sem_unary_operation_eq_invariant:
    forall ge e m ge' e' m' op v ty' v',
      eq (ge, e, m) (ge', e', m') ->
      sem_unary_operation op v (CTy.basetype_to_compcert_type ty') m = Some v' ->
      sem_unary_operation op v (CTy.basetype_to_compcert_type ty') m' = Some v'.
  Proof. 
    intros. unfolds eq. destruct H as (Hge & He & Hmf & Hmb). subst.
    destruct ty'; destruct op; destruct v; simpls; eauto.
  Qed.

  Lemma sem_binary_operation_eq_invariant:
    forall ge e m ge' e' m' op v1 ty1 v2 ty2 v',
      eq (ge, e, m) (ge', e', m') ->
      sem_binary_operation ge op v1 (CTy.basetype_to_compcert_type ty1) v2 (CTy.basetype_to_compcert_type ty2) m = Some v' ->
      sem_binary_operation ge' op v1 (CTy.basetype_to_compcert_type ty1) 
      v2 (CTy.basetype_to_compcert_type ty2) m' = Some v'.
  Proof. 
    intros. destruct H as (Hge & He & Hmf & Hmb). subst.
    destruct ty1; destruct ty2; destruct op; destruct v1; destruct v2; simpls; trivial.
  Qed.

  Lemma sem_unary_operation_write_cell_invariant:
    forall op v v' v0 wc ty ty' (m1 m2:mem) ge env m1 ge' env' m2,
      write_cell wc ty v0 (ge, env, m1) (ge', env', m2) ->
      sem_unary_operation op v (CTy.basetype_to_compcert_type ty') m1 = Some v' <->
      sem_unary_operation op v (CTy.basetype_to_compcert_type ty') m2 = Some v'.
  Proof.
    intros.
    split; intro.
    - 
      unfolds sem_unary_operation. destruct op; simpl in H0; try discriminate; eauto.
      unfolds CTy.basetype_to_compcert_type. destruct ty'; simpls.
      unfolds sem_notbool. unfolds bool_val; simpls. destruct v; simpls; try discriminate.
      trivial.
    - 
      unfolds sem_unary_operation. destruct op; simpl in H0; try discriminate; eauto.
      unfolds CTy.basetype_to_compcert_type. destruct ty'; simpls.
      unfolds sem_notbool. unfolds bool_val; simpls. destruct v; simpls; try discriminate.
      trivial.
  Qed.

  Lemma sem_binary_operation_write_cell_invariant:
    forall op v1 v2 v' v0 wc ty ty1 ty2 (m1 m2:mem) ge env m1 ge' env' m2,
      write_cell wc ty v0 (ge, env, m1) (ge', env', m2) ->
      sem_binary_operation ge op v1 (CTy.basetype_to_compcert_type ty1) 
      v2 (CTy.basetype_to_compcert_type ty2) m1 = Some v' <->
      sem_binary_operation ge op v1 (CTy.basetype_to_compcert_type ty1) 
      v2 (CTy.basetype_to_compcert_type ty2) m2 = Some v'.
  Proof.
    intros. split; intro.
    - unfolds CTy.basetype_to_compcert_type. destruct ty1; destruct ty2; simpls.
      unfolds sem_binary_operation. destruct op; simpls; trivial.
    - unfolds CTy.basetype_to_compcert_type. destruct ty1; destruct ty2; simpls.
      unfolds sem_binary_operation. destruct op; simpls; trivial.
  Qed.

End CState.

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Psatz.
Require Import Setoid Morphisms.
Require Import RelationPairs.
Require Import BinPos.

Require Import Misc.
Require Import Linalg.
Require Import LibTactics.
Import List.ListNotations.

Open Scope Z_scope.
Open Scope list_scope.
Open Scope vector_scope.

Lemma is_eq_iff_cmp_eq: 
    forall t1 t2,
        is_eq t1 t2 = true <-> lex_compare t1 t2 = Eq.
Proof.
    induction t1.
    {
        intros.
        split.
        {
            intro.
            simpls.
            destruct t2; simpls; trivial.
            destruct z; simpls; trivial; tryfalse.
            {
                eapply lex_compare_nil_is_null; trivial.
            }
        }
        {
            intro.
            simpls.
            destruct t2; simpls; trivial.
            destruct z; simpls; trivial; tryfalse.
            eapply is_null_lex_compare_nil; eauto.
        }
    }
    {
        intros.
        split.
        {
            intro.
            simpls. 
            destruct t2; simpls; trivial.
            {
                eapply andb_true_iff in H.
                destruct H.
                eapply lex_compare_nil_is_null in H0.
                rewrite H0.
                assert (a = 0). {try lia. }
                rewrite H1; simpls; trivial.
            }
            {
                eapply andb_true_iff in H.
                destruct H.
                eapply IHt1 in H0.
                (* eapply lex_compare_nil_is_null in H0. *)
                rewrite H0.
                assert (a = z). {try lia. }
                subst; trivial.
                rewrite Z.compare_refl; trivial.
            }
        }
        {
            intro.
            simpls. 
            destruct t2; simpls; trivial.
            {
                reflect.
                destruct a; simpls; trivial; tryfalse.
                split; trivial.
                eapply is_null_lex_compare_nil; eauto.
                destruct (lex_compare_nil t1); tryfalse.
                trivial.
            }
            {
                eapply andb_true_iff.
                rewrite (IHt1 t2).
                destruct (a?=z) eqn:G; try discriminate.
                split.
                {
                    eapply Z.compare_eq in G.
                    subst.
                    eapply Z.eqb_refl.
                }
                {
                    trivial.
                }
            }
        }
    }
Qed.


Lemma lex_compare_nil_trans: 
    forall l1 l2 cmp,
        CompOpp (lex_compare_nil l1) = cmp -> (** l1 < nil *)
        lex_compare_nil l2 = cmp ->           (** nil < l2 *)
        lex_compare l1 l2 = cmp.              (** l1 < l2 *)
Proof. 
    induction l1.
    {
        intros.
        destruct cmp.
        {
            destruct l2 eqn:Hl2; simpls; tryfalse; trivial.
        }
        {
            destruct l2 eqn:Hl2; simpls; tryfalse; trivial.
        }
        {
            destruct l2 eqn:Hl2; simpls; tryfalse; trivial.
        }
    }
    {
        intros.
        destruct cmp.
        {
            destruct l2 eqn:Hl2; simpls; tryfalse; trivial.
            destruct z eqn:Hz; simpls; tryfalse; trivial.
            destruct a eqn:Ha; simpls; tryfalse; trivial.
            eapply IHl1; eauto.
        }
        {
            destruct l2 eqn:Hl2; simpls; tryfalse; trivial.
            destruct z eqn:Hz; simpls; tryfalse; trivial.
            {
                destruct a eqn:Ha; simpls; tryfalse; trivial.
                eapply IHl1; eauto.    
            }
            {
                destruct a eqn:Ha; simpls; tryfalse; trivial.
            }
        }
        {
            destruct l2 eqn:Hl2; simpls; tryfalse; trivial.
            destruct z eqn:Hz; simpls; tryfalse; trivial.
            {
                destruct a eqn:Ha; simpls; tryfalse; trivial.
                eapply IHl1; eauto.    
            }
            {
                destruct a eqn:Ha; simpls; tryfalse; trivial.
            }
        }
    }
Qed.

Lemma lex_compare_trans: 
    forall b a c cmp, 
        lex_compare a b = cmp -> 
        lex_compare b c = cmp -> 
        lex_compare a c = cmp.
Proof. 
    induction b.
    {
        intros.
        destruct cmp.
        {
            eapply is_eq_iff_cmp_eq in H.
            rewrite <- H0.
            eapply lex_compare_left_eq; eauto.
        }
        {
            simpls.
            destruct a eqn:Ha; tryfalse. 
            simpls.
            destruct c eqn:Hc; tryfalse.
            {
                destruct z eqn:Hz; tryfalse; try lia.
                {
                    destruct z0 eqn:Hz0; tryfalse.
                    {
                        rewrite Z.compare_refl.
                        simpls.
                        eapply lex_compare_nil_trans; eauto.
                    }
                    {
                        simpls; trivial.
                    }                    
                }
                {
                    destruct z0 eqn:Hz0; tryfalse.
                    {
                        simpls; trivial.
                    }
                    {
                        simpls; trivial.
                    }     
                }
            }
        }
        {
            simpls.
            destruct a eqn:Ha; tryfalse. 
            simpls.
            destruct c eqn:Hc; tryfalse.
            {
                destruct z eqn:Hz; tryfalse; try lia.
                {
                    destruct z0 eqn:Hz0; tryfalse.
                    {
                        rewrite Z.compare_refl.
                        simpls.
                        eapply lex_compare_nil_trans; eauto.
                    }
                    {
                        simpls; trivial.
                    }                    
                }
                {
                    destruct z0 eqn:Hz0; tryfalse.
                    {
                        simpls; trivial.
                    }
                    {
                        simpls; trivial.
                    }     
                }
            }
        
        }   
    }
    {
        intros.
        rename a into tau.
        rename a0 into a.
        destruct cmp.
        {
            eapply is_eq_iff_cmp_eq in H.
            rewrite <- H0.
            eapply lex_compare_left_eq; eauto.
        }
        {
            simpls.
            destruct c eqn:Hc; tryfalse.
            {
                destruct tau eqn:Htau; tryfalse.
                {
                    destruct a eqn:Ha; simpls; tryfalse.
                    { 
                        rewrite H in H0.
                        unfold CompOpp in H0; tryfalse.
                    }
                    {
                        destruct z eqn:Hz; simpls; tryfalse; trivial.
                        eapply IHb with (c:=nil) in H; eauto.
                        {
                            rewrite lex_compare_nil_right in H; trivial.
                        }
                        {
                            rewrite <- lex_compare_nil_right in H0; trivial.
                        }
                    }
                }   
                {
                    destruct a eqn:Ha; simpls; tryfalse.
                    {
                        destruct z eqn:Hz; simpls; tryfalse; trivial.
                    }
                }
            }
            {
                destruct tau eqn:Htau; tryfalse.
                {
                    destruct a eqn:Ha; simpls; tryfalse.
                    {
                        destruct z eqn:Hz; simpls; tryfalse; trivial.
                        eapply IHb with (a:=nil) in H0; eauto.
                        {
                            rewrite lex_compare_nil_left in H0; trivial.
                        }
                        {
                            rewrite <- lex_compare_nil_left in H; trivial.
                        }
                    }
                    {   
                        destruct z eqn:Hz; simpls; tryfalse; trivial.
                        {
                            destruct z0 eqn:Hz0; simpls; tryfalse; trivial.
                            eapply IHb; eauto.
                        }
                        {
                            destruct z0 eqn:Hz0; simpls; tryfalse; trivial.
                        }
                        
                    }
                }   
                {
                    destruct a eqn:Ha; simpls; tryfalse.
                    {
                        destruct z eqn:Hz; simpls; tryfalse; trivial.
                    }
                    {
                        destruct z eqn:Hz; simpls; tryfalse; trivial.
                        destruct z0 eqn:Hz0; simpls; tryfalse; trivial.
                        destruct ((p1 ?= p)%positive) eqn:Hp1p; simpls; tryfalse; trivial.
                        {
                            destruct ((p ?= p0)%positive) eqn:Hpp0; simpls; tryfalse; trivial.
                            {
                                eapply Pos.compare_eq_iff in Hp1p.
                                eapply Pos.compare_eq_iff in Hpp0.
                                subst; simpls.
                                rewrite Pos.compare_refl.
                                eapply IHb; eauto.
                            }
                            {
                                eapply Pos.compare_eq_iff in Hp1p.
                                subst.
                                rewrite Hpp0; trivial.
                            }   
                        }
                        {
                            destruct ((p ?= p0)%positive) eqn:Hpp0; simpls; tryfalse; trivial.
                            {
                                eapply Pos.compare_eq_iff in Hpp0.
                                subst; simpls.
                                rewrite Hp1p; trivial.
                            }
                            {
                                eapply Pos.lt_trans with (m:=p)in Hp1p; eauto.
                                rewrite Hp1p; trivial.
                            }   
                        }
                    }
                }
                {
                    destruct a eqn:Ha; simpls; tryfalse.
                    {
                        unfold CompOpp.
                        destruct z eqn:Hz; simpls; tryfalse; trivial.
                        destruct z0 eqn:Hz0; simpls; tryfalse; trivial.
                        destruct z0 eqn:Hz0; simpls; tryfalse; trivial.
                        destruct z0 eqn:Hz0; simpls; tryfalse; trivial.

                        destruct ((p1 ?= p)%positive) eqn:Hp1p; simpls; tryfalse; trivial.
                        {
                            destruct ((p ?= p0)%positive) eqn:Hpp0; simpls; tryfalse; trivial.
                            {
                                eapply Pos.compare_eq_iff in Hp1p.
                                eapply Pos.compare_eq_iff in Hpp0.
                                subst; simpls.
                                rewrite Pos.compare_refl.
                                eapply IHb; eauto.
                            }
                            {
                                eapply Pos.compare_eq_iff in Hp1p.
                                subst.
                                rewrite Hpp0; trivial.
                            }   
                        }
                        {
                            destruct ((p ?= p0)%positive) eqn:Hpp0; tryfalse.
                            {
                                eapply Pos.compare_eq_iff in Hpp0.
                                subst; simpls.
                                rewrite Hp1p; trivial.
                            }
                            {   
                                simpls.
                                rewrite Pos.compare_gt_iff in Hp1p.
                                rewrite Pos.compare_gt_iff in Hpp0.
                                eapply Pos.lt_trans with (m:=p)in Hp1p; eauto.
                                rewrite <- Pos.compare_antisym.
                                rewrite Hp1p; trivial.
                            }   
                        }
                    }
                }
            }
        }
        { (** Gt *)
            simpls.
            destruct c eqn:Hc; tryfalse.
            {
                destruct tau eqn:Htau; tryfalse.
                {
                    destruct a eqn:Ha; simpls; tryfalse.
                    { 
                        rewrite H in H0.
                        unfold CompOpp in H0; tryfalse.
                    }
                    {
                        destruct z eqn:Hz; simpls; tryfalse; trivial.
                        eapply IHb with (c:=nil) in H; eauto.
                        {
                            rewrite lex_compare_nil_right in H; trivial.
                        }
                        {
                            rewrite <- lex_compare_nil_right in H0; trivial.
                        }
                    }
                }   
                {
                    destruct a eqn:Ha; simpls; tryfalse.
                    {
                        destruct z eqn:Hz; simpls; tryfalse; trivial.
                    }
                }
            }
            {
                destruct tau eqn:Htau; tryfalse.
                {
                    destruct a eqn:Ha; simpls; tryfalse.
                    {
                        destruct z eqn:Hz; simpls; tryfalse; trivial.
                        eapply IHb with (a:=nil) in H0; eauto.
                        {
                            rewrite lex_compare_nil_left in H0; trivial.
                        }
                        {
                            rewrite <- lex_compare_nil_left in H; trivial.
                        }
                    }
                    {   
                        destruct z eqn:Hz; simpls; tryfalse; trivial.
                        {
                            destruct z0 eqn:Hz0; simpls; tryfalse; trivial.
                            eapply IHb; eauto.
                        }
                        {
                            destruct z0 eqn:Hz0; simpls; tryfalse; trivial.
                        }
                        
                    }
                }   
                {
                    destruct a eqn:Ha; simpls; tryfalse.
                    {
                        unfold CompOpp.
                        destruct z eqn:Hz; simpls; tryfalse; trivial.
                        destruct z0 eqn:Hz0; simpls; tryfalse; trivial.
                        destruct z0 eqn:Hz0; simpls; tryfalse; trivial.
                        destruct ((p1 ?= p)%positive) eqn:Hp1p; simpls; tryfalse; trivial.
                        {
                            destruct ((p ?= p0)%positive) eqn:Hpp0; simpls; tryfalse; trivial.
                            {
                                eapply Pos.compare_eq_iff in Hp1p.
                                eapply Pos.compare_eq_iff in Hpp0.
                                subst; simpls.
                                rewrite Pos.compare_refl.
                                eapply IHb; eauto.
                            }
                            {
                                eapply Pos.compare_eq_iff in Hp1p.
                                subst.
                                rewrite Hpp0; trivial.
                            }   
                        }
                        {
                            destruct ((p ?= p0)%positive) eqn:Hpp0; tryfalse.
                            {
                                eapply Pos.compare_eq_iff in Hpp0.
                                subst; simpls.
                                rewrite Hp1p; trivial.
                            }
                            {   
                                simpls.
                                rewrite Pos.compare_gt_iff in Hp1p.
                                rewrite Pos.compare_gt_iff in Hpp0.
                                eapply Pos.lt_trans with (m:=p)in Hp1p; eauto.
                                rewrite Pos.compare_antisym.
                                rewrite Hp1p; trivial.
                            }   
                        }
                        destruct z0 eqn:Hz0; simpls; tryfalse; trivial.
                    }
                }
                {
                    destruct a eqn:Ha; simpls; tryfalse.
                    {
                        destruct z eqn:Hz; simpls; tryfalse; trivial.
                    }
                    {
                        destruct z eqn:Hz; simpls; tryfalse; trivial.
                        destruct z0 eqn:Hz0; simpls; tryfalse; trivial.
                        destruct ((p1 ?= p)%positive) eqn:Hp1p; simpls; tryfalse; trivial.
                        {
                            destruct ((p ?= p0)%positive) eqn:Hpp0; simpls; tryfalse; trivial.
                            {
                                eapply Pos.compare_eq_iff in Hp1p.
                                eapply Pos.compare_eq_iff in Hpp0.
                                subst; simpls.
                                rewrite Pos.compare_refl.
                                eapply IHb; eauto.
                            }
                            {
                                eapply Pos.compare_eq_iff in Hp1p.
                                subst.
                                rewrite Hpp0; trivial.
                            }   
                        }
                        {
                            destruct ((p ?= p0)%positive) eqn:Hpp0; simpls; tryfalse; trivial.
                            {
                                eapply Pos.compare_eq_iff in Hpp0.
                                subst; simpls.
                                rewrite Hp1p; trivial.
                            }
                            {
                                eapply Pos.lt_trans with (m:=p)in Hp1p; eauto.
                                rewrite Hp1p; trivial.
                            }   
                        }
                    }
                }
            }
        }
    }
Qed. 

Lemma lex_compare_total: 
    forall a b, 
        lex_compare a b = Lt \/ lex_compare b a = Lt \/ lex_compare a b = Eq.
Proof. 
    intros.
    remember (lex_compare a b) as res.
    symmetry in Heqres.
    destruct res eqn:G; try firstorder.
    right; left.
    rewrite lex_compare_antisym.
    rewrite Heqres. simpls; trivial.
Qed. 

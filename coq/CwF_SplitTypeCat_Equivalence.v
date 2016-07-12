
(**

 Ahrens, Lumsdaine, Voevodsky, 2015 - 2016

*)

Require Export UniMath.Foundations.Basics.Sets.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.more_on_pullbacks.
Require Export UniMath.CategoryTheory.UnicodeNotations.
Require Export UniMath.CategoryTheory.functor_categories.
Require Export UniMath.CategoryTheory.opp_precat.
Require Export UniMath.CategoryTheory.category_hset.
Require Export UniMath.CategoryTheory.yoneda.

Require Export Systems.Auxiliary.
Require Export Systems.UnicodeNotations.
Require Export Systems.Structures.
Require Import Systems.CwF_SplitTypeCat_Maps.
Require Import Systems.Bicats.Auxiliary.

Local Set Automatic Introduction.
(* only needed since imports globally unset it *)

Open Scope mor_scope.
Undelimit Scope transport.

Section Fix_Context.

Context {C : Precategory} (X : obj_ext_structure C).

Local Notation hsC := (homset_property C).

Local Notation "'Yo'" := (yoneda C hsC).
Local Notation "'Yo^-1'" :=  (invweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ ))).

Local Notation "Γ ◂ A" := (comp_ext _ Γ A) (at level 30).
Local Notation "'Ty'" := (fun X Γ => (TY X : functor _ _) Γ : hSet) (at level 10).
Local Notation "A [ f ]" := (# (TY X : functor _ _ ) f A) (at level 4).
Local Notation "'Tm'" := (fun Y Γ => (TM Y : functor _ _) Γ : hSet) (at level 10).

Local Notation Δ := comp_ext_compare.

Section compatible_structures.

Section canonical_TM.

(* TODO: there is a lot of redundancy between the lemmas of this section and [term_to_section] and companions. *)

Variable Z : qq_morphism_structure X.
Notation ZZ := (pr2 Z).
Variable Y : compatible_fam_structure Z.

Definition canonical_TM_to_given_data
  : Π Γ, (tm_from_qq Z Γ) ⇒ (Tm (pr1 Y) Γ)
:= (λ (Γ : C^op) (t : tm_from_qq_carrier Γ),
       (yoneda_weq C hsC Γ (TM (pr1 Y)))
         (# Yo (pr1 (pr2 t)) ;; Q (pr1 Y) (pr1 t))).

Lemma is_nat_trans_canonical_TM_to_given 
 : is_nat_trans (tm_from_qq Z) (TM (pr1 Y) : functor _ _ )
     canonical_TM_to_given_data.
Proof.
  intros Γ Γ' f.
  cbn; unfold yoneda_morphisms_data; unfold yoneda_objects_ob.
  apply funextsec. intro t. cbn.
  destruct t as [A [s e]].
  (* now use naturality of (yoneda_weq) on the right-hand side *)
  assert (XR := nat_trans_ax (natural_trans_yoneda_iso _ hsC (TM (pr1 Y))) _ _ f). 
  assert (XR1 := toforallpaths _ _ _ XR); cbn in XR1.
  set (XX := # Yo s ;; Q (pr1 Y) _ ). 
  assert (XR2 := XR1 XX).
  cbn in XR2; unfold yoneda_morphisms_data in XR2.
  etrans. Focus 2. apply XR2. clear XR2 XR1 XX XR.
  (* now use compatibility of [Q (Y)] with [qq] *)
  assert (XT :=  nat_trans_eq_pointwise (pr2 Y _ _ A f)).
  cbn in XT. unfold yoneda_morphisms_data, yoneda_objects_ob in XT.
  assert (XT1 := toforallpaths _ _ _ (XT Γ')).
  etrans. apply XT1.
  etrans. cbn. apply idpath.
  apply maponpaths.
  etrans. apply cancel_postcomposition, id_left.
  etrans. apply (PullbackArrow_PullbackPr2 (mk_Pullback _ _ _ _ _ _ _)).
  apply cancel_postcomposition, pathsinv0, id_left.
Time Qed.

Definition canonical_TM_to_given : (preShv C) ⟦tm_from_qq Z, TM (pr1 Y)⟧.
Proof.
  exists canonical_TM_to_given_data.
  apply is_nat_trans_canonical_TM_to_given.
Defined.

Definition given_TM_to_canonical
  : Π Γ, HSET ⟦ Tm (pr1 Y) Γ, tm_from_qq Z Γ⟧.
Proof.
  intro Γ. simpl.
  intro s'. set (S' := @yy _ hsC _ _ s').
  set (ps := (pp (pr1 Y) : nat_trans _ _ )  _ s').
  assert (XR : S' ;; pp (pr1 Y) = yy ( (pp (pr1 Y) : nat_trans _ _ ) _ s')).
  { 
    abstract (
    apply nat_trans_eq; [ apply has_homsets_HSET | ];
    intro Γ' ;
    apply funextsec;
    intro g; simpl; cbn;
    assert (XR := nat_trans_ax (pp (pr1 Y)) _ _ g);
    apply (toforallpaths _ _ _ XR)
     ) .
  } 
    exists ps.
    set (Pb := pr2 (pr1 Y) Γ ps). 
    set (T:= section_from_diagonal (pr1 Pb) (pr2 Pb) (S',,XR) ).
    mkpair.
    + apply Yo^-1.
      exact (pr1 T).
    + abstract
      (
      apply (invmaponpathsweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ )));
      etrans ; [ apply functor_comp |];
      etrans ; [ apply cancel_postcomposition ;
         apply( homotweqinvweq (weqpair _
           (yoneda_fully_faithful _ hsC Γ (comp_ext X Γ ps) ))) | ];
      simpl;
      match goal with |[ |- PullbackArrow ?HH _ _ _ _ ;; _ = _ ] => 
                       set (XR3:=HH) end;
      rewrite (PullbackArrow_PullbackPr1 XR3);
      apply pathsinv0; apply (functor_id Yo)
       ).
Time Defined.

Lemma given_to_canonical_to_given Γ
  : given_TM_to_canonical Γ ;; (canonical_TM_to_given : nat_trans _ _) Γ
  = identity _ .
Proof.
  apply funextsec; intro s.
  cbn; unfold yoneda_morphisms_data.
  rewrite id_left.
  unfold yoneda_map_1.
  match goal with |[|- _ ( ((_ (_ ?HH _ _ _ _ ) )) _  _ )  = _ ] => set (XR:= HH) end.
  assert (XR1 := PullbackArrow_PullbackPr2 XR).
  match goal with |[|- _ ( ((_ (_ ?HH ?E ?H ?K _ ) )) _  _ )  = _ ] => specialize (XR1 E H K)  end.
  match goal with |[|- _ ( ((_ (_ _ _ _ _ ?HH ) )) _  _ )  = _ ] => specialize (XR1 HH)  end.
  assert (XR2 := nat_trans_eq_pointwise XR1).
  simpl in XR2. 
  assert (XR3 := toforallpaths _ _ _ (XR2 Γ)).
  simpl in XR3.
  etrans. apply XR3.
  apply (toforallpaths _ _ _ (functor_id (TM (pr1 Y)) _ )).
Time Qed.

Lemma canonical_to_given_to_canonical Γ
  : (canonical_TM_to_given : nat_trans _ _ )  Γ ;; given_TM_to_canonical Γ = identity _ .
Proof.
  apply funextsec; intro t.
  destruct t as [A [s e]].
  use tm_from_qq_eq.
  - cbn; unfold yoneda_morphisms_data.  
    etrans. apply maponpaths, maponpaths, id_left.
    assert (XR := ! Q_pp (pr1 Y) A).
    assert (XR1 := nat_trans_eq_pointwise XR Γ).
    assert (XR2 := toforallpaths _ _ _ XR1 s).
    cbn in XR2; unfold yoneda_morphisms_data in XR2.
    etrans. apply XR2.
    etrans. apply (maponpaths (fun k => A[k]) e).
    apply (toforallpaths _ _ _ (functor_id (TY X) _ ) _).
  (* TODO: the second half could possibly be simplified by
  [Q_pp_Pb_unique]. *)
  - apply (invmaponpathsweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ ))).
    etrans. apply (functor_comp Yo).
    etrans. apply cancel_postcomposition.
            apply (homotweqinvweq
               (weqpair _ (yoneda_fully_faithful _  hsC _ _ ))).
    etrans. Focus 2. simpl. apply idpath.
    etrans. apply cancel_postcomposition. cbn. apply idpath.
    Time match goal with |[|- PullbackArrow ?HH _ _ _ ?PP ;; _ = _ ] =>
            set (XR:= HH); generalize PP end.
    intro ee.
    use (MorphismsIntoPullbackEqual (isPullback_Q_pp (pr1 Y) _ )).
    + etrans. apply (!assoc _ _ _ ).
      etrans. apply maponpaths. apply (!functor_comp _ _ _ _ _ _ ).
      etrans. apply maponpaths. apply maponpaths.
              apply comp_ext_compare_π.
      etrans. apply (PullbackArrow_PullbackPr1 XR).
      etrans. Focus 2. apply (functor_comp Yo).
      etrans. Focus 2. apply maponpaths. apply (!e).
      apply pathsinv0. apply (functor_id Yo).
    + etrans. apply (!assoc _ _ _ ).
      etrans. apply maponpaths.
              apply comp_ext_compare_Q.
      etrans. apply (PullbackArrow_PullbackPr2 XR).
      simpl.
      clear XR. clear ee.
      unfold yoneda_morphisms. unfold yoneda_morphisms_data.
      apply nat_trans_eq. apply (has_homsets_HSET).
      intro Γ'.
      apply funextsec.
      simpl. intro s'.
      cbn. simpl.
      rewrite id_left.
      assert (XR := nat_trans_ax (Q (pr1 Y) A) _ _ s').
      assert (XR1 := toforallpaths _ _ _ XR).
      apply pathsinv0. simpl in XR1. apply XR1.
Time Qed.

Lemma canonical_TM_to_given_pointwise_iso Γ
  : is_iso ((canonical_TM_to_given : nat_trans _ _) Γ).
Proof.
  apply (is_iso_qinv _ (given_TM_to_canonical Γ) ).
  split.
  - apply canonical_to_given_to_canonical.
  - apply given_to_canonical_to_given.
Defined.

Definition canonical_TM_to_given_iso
  : @iso (preShv C) (tm_from_qq Z) (TM (pr1 Y)).
Proof.
  exists canonical_TM_to_given.
  apply functor_iso_if_pointwise_iso.
  apply canonical_TM_to_given_pointwise_iso.
Defined.

End canonical_TM.

Lemma unique (Z : qq_morphism_data X)
             (ZZ : qq_morphism_axioms Z)
             (Y : compatible_fam_structure (Z,,ZZ))
  : compatible_fam_from_qq (Z,,ZZ) = Y.
Proof.
  set (i := isotoid _
                   (is_category_functor_category _ _ is_category_HSET)
                   (canonical_TM_to_given_iso (Z,,ZZ) Y)).
  apply subtypeEquality.
  { intro. do 4 (apply impred; intro).
    apply functor_category_has_homsets.
  }
  destruct Y as [Y YH]. simpl.
  apply subtypeEquality.
  { intro. apply isaprop_families_structure_axioms. }
  simpl.
  destruct Y as [Y YH']. simpl.
  use total2_paths.
  - simpl.
    apply i.
  - rewrite transportf_dirprod.
    destruct Y as [tm [p Q]].
    simpl.
    apply dirprodeq.
    + simpl.
      etrans. eapply pathsinv0.
      apply  (idtoiso_precompose (preShv C)).
      unfold i.
      rewrite idtoiso_inv.
      rewrite idtoiso_isotoid.
      simpl.
      apply nat_trans_eq. apply has_homsets_HSET.
      intro Γ. apply idpath.
    + cbn. simpl.

  assert (XR := 
          (idtoiso_transportf_family_of_morphisms (preShv C))).
  specialize (XR C (λ B, (TY X : functor _ _ ) B : hSet)).
  specialize (XR (λ Γ' B, (yoneda C hsC (Γ' ◂ B)))).
  etrans. apply XR.
  apply funextsec. intro Γ.
  apply funextsec. intro A.
  clear XR.
  unfold i. rewrite idtoiso_isotoid.
  simpl.
  apply nat_trans_eq. { apply has_homsets_HSET. }
  intro Γ'. simpl. cbn.
  apply funextsec.
  unfold yoneda_objects_ob.
  intro s.
  unfold yoneda_morphisms_data.
  rewrite id_left.

  cbn.
  
  simpl. clear i.
  specialize (YH Γ Γ' A (s ;; π _ )). simpl in YH.
  assert (XR := nat_trans_eq_pointwise YH Γ').
  assert (XR2 := toforallpaths _ _ _ XR).
  cbn in XR2.
  etrans. apply XR2.
  apply maponpaths.
  unfold yoneda_morphisms_data.
  match goal with |[|- PullbackArrow ?HH _ _ _ _ ;; _ = _ ] =>
            apply (PullbackArrow_PullbackPr2 HH) end.
Defined.





(* needs splitness? *)
Lemma iscontr_compatible_fam_structure (Z : qq_morphism_data X) (ZZ : qq_morphism_axioms Z)
: iscontr (compatible_fam_structure (Z,,ZZ)).
Proof.
  exists (compatible_fam_from_qq (Z,,ZZ)).
  intro t.
  apply pathsinv0. apply unique.
Defined.

Lemma compat_split_comp_eq (Y : families_structure _ X) :
  Π t : compatible_qq_morphism_structure Y,
  t = compatible_qq_from_fam Y.
Proof.
  intro t.
    apply subtypeEquality.
    { 
      intro.
(*      apply isofhleveldirprod. *)
      (*- apply isaprop_qq_morphism_axioms.*)
      - do 4 (apply impred; intro).
        apply functor_category_has_homsets. 
    }
    simpl.
    apply subtypeEquality.
    { 
      intro.
      apply @isaprop_qq_morphism_axioms, hsC.
    }
    apply subtypeEquality.
    {
      intro.
      do 4 (apply impred; intro).
      apply isofhleveltotal2. 
      - apply hsC.
      - intro. apply isaprop_isPullback.
    } 
    simpl.
    destruct t as [[t H1] H2]. simpl.
    destruct t as [q h]; simpl.
    apply funextsec. intro Γ.
    apply funextsec; intro Γ'.
    apply funextsec; intro f.
    apply funextsec; intro A.
    
    apply (invmaponpathsweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ ))).
    apply pathsinv0.
    etrans. apply Yo_qq_fam_Yo_of_qq.
    unfold Yo_of_qq.
    apply pathsinv0.
    apply PullbackArrowUnique.
    + etrans. apply maponpaths. cbn. apply idpath.
      rewrite <- functor_comp.
      etrans. eapply pathsinv0. apply (functor_comp Yo).
      apply maponpaths.
      apply pathsinv0. apply (pr1 (h _ _ _ _ )).
    + etrans. apply maponpaths. cbn. apply idpath.
      apply pathsinv0.
      apply H2.
Time Qed.
  

Lemma iscontr_compatible_split_comp_structure (Y : families_structure hsC X)
: iscontr (compatible_qq_morphism_structure Y).
Proof.
  exists (compatible_qq_from_fam Y).
  apply compat_split_comp_eq.
Qed.

End compatible_structures.

Section Equivalence.

Definition T1 : UU :=
  Σ Y : families_structure hsC X,
        compatible_qq_morphism_structure Y.

Definition T2 : UU :=
  Σ Z : qq_morphism_structure X,
        compatible_fam_structure Z.

Definition shuffle : T1 ≃ T2.
Proof.
  eapply weqcomp.
  unfold T1.
  unfold compatible_qq_morphism_structure.
  set (XR := @weqtotal2asstol).
  specialize (XR (families_structure hsC X)).
  specialize (XR (fun _ => qq_morphism_structure X)).
  simpl in XR.
  specialize (XR (fun YZ => iscompatible_fam_qq (pr1 YZ) (pr2 YZ))).
  apply XR.
  eapply weqcomp. Focus 2.
  unfold T2. unfold compatible_fam_structure.
  set (XR := @weqtotal2asstor).
  specialize (XR (qq_morphism_structure X)).
  specialize (XR (fun _ => families_structure hsC X)).
  simpl in XR.
  specialize (XR (fun YZ => iscompatible_fam_qq (pr2 YZ) (pr1 YZ))).
  apply XR.
  use weqbandf.
  - apply weqdirprodcomm.
  - intros. simpl.
    apply idweq.
Defined.

Definition forget_fam :
  T2 ≃ qq_morphism_structure X.
Proof.
  exists pr1.
  apply isweqpr1.
  intros [z zz].
  apply iscontr_compatible_fam_structure.
Defined.

Definition forget_comp :
  T1 ≃ families_structure hsC X.
Proof.
  exists pr1.
  apply isweqpr1.
  intro.
  apply iscontr_compatible_split_comp_structure.
Defined.

Definition weq_CwF_SplitTypeCat : families_structure hsC X ≃ qq_morphism_structure X.
Proof.
  eapply weqcomp.
    eapply invweq. apply forget_comp.
  eapply weqcomp.
    apply shuffle.
  apply forget_fam.
Defined.

End Equivalence.

End Fix_Context.



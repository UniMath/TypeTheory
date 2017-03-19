(**
  [TypeTheory.ALV1.CwF_SplitTypeCat_Equivalence]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

Require Import UniMath.Foundations.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Defs.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Maps.

Local Set Automatic Introduction.
(* only needed since imports globally unset it *)

Open Scope mor_scope.


Section Fix_Context.

Context {C : Precategory} (X : obj_ext_structure C).

Local Notation "Γ ◂ A" := (comp_ext _ Γ A) (at level 30).
Local Notation "'Ty'" := (fun X Γ => (TY X : functor _ _) Γ : hSet) (at level 10).
Local Notation "A [ f ]" := (# (TY X : functor _ _ ) f A) (at level 4).
Local Notation "'Tm'" := (fun Y Γ => (TM Y : functor _ _) Γ : hSet) (at level 10).

Local Notation Δ := comp_ext_compare.

Section compatible_structures.

Section canonical_TM.

Variable Z : qq_morphism_structure X.
Notation ZZ := (pr2 Z).
Variable Y : compatible_term_structure Z.

Definition canonical_TM_to_given_data
  {Γ} (Ase : tm_from_qq Z Γ : hSet) : (Tm Y Γ).
Proof.
  refine (# (TM _ : functor _ _) _ (te _ (pr1 Ase))). 
  exact (pr1 (pr2 Ase)).
Defined.

Lemma is_nat_trans_canonical_TM_to_given 
 : is_nat_trans (tm_from_qq Z) (TM Y : functor _ _ )
     (@canonical_TM_to_given_data).
Proof.
  intros Γ Γ' f.
  apply funextsec; intros [A [s e]].
  unfold canonical_TM_to_given_data; cbn.
  etrans. apply maponpaths, iscompatible_iscompatible', (pr2 Y).
  etrans. apply (toforallpaths _ _ _ (!functor_comp (TM Y) _ _ ) _).
  etrans. Focus 2. apply (toforallpaths _ _ _ (functor_comp (TM Y) _ _ ) _).
  apply maponpaths_2. 
  apply (@PullbackArrow_PullbackPr2 C _ _ _ _ _ (mk_Pullback _ _ _ _ _ _ _)).
Qed.

Definition canonical_TM_to_given : (preShv C) ⟦tm_from_qq Z, TM (pr1 Y)⟧.
Proof.
  exists @canonical_TM_to_given_data.
  apply is_nat_trans_canonical_TM_to_given.
Defined.

Definition given_TM_to_canonical
  : ∏ Γ, HSET ⟦ Tm (pr1 Y) Γ, tm_from_qq Z Γ⟧.
Proof.
  intros Γ t.
  exists ((pp (pr1 Y) : nat_trans _ _ )  _ t).
  apply term_to_section.
Defined.

Lemma given_to_canonical_to_given Γ
  : given_TM_to_canonical Γ ;; (canonical_TM_to_given : nat_trans _ _) Γ
  = identity _ .
Proof.
  apply funextsec; intro t.
  cbn. unfold canonical_TM_to_given_data, given_TM_to_canonical.
  apply term_to_section_recover.
Qed.

Lemma pp_canonical_TM_to_given
  : canonical_TM_to_given ;; pp Y
    = pp_from_qq Z.
Proof.
  apply nat_trans_eq. apply homset_property.
  intros Γ; simpl in Γ. apply funextsec; intros [A [s e]].
  cbn. unfold canonical_TM_to_given_data.
  etrans. apply (toforallpaths _ _ _ (nat_trans_ax (pp Y) _ _ s)). 
  etrans. cbn. apply maponpaths, pp_te.
  etrans. apply (toforallpaths _ _ _ (!functor_comp (TY X) _ _) _).
  etrans. apply maponpaths_2, e.
  apply (toforallpaths _ _ _ (functor_id (TY X) _ ) _).
Qed.

Lemma canonical_TM_to_given_paths_adjoint {Γ:C} Ase t
  : (canonical_TM_to_given : nat_trans _ _) Γ Ase = t
  -> Ase = given_TM_to_canonical Γ t.
Proof.
  destruct Ase as [A [s e]].
  intros H.
  (* This [assert] is to enable the [destruct eA] below. *)
  assert (eA : (pp Y : nat_trans _ _) _ t = A). {
    etrans. apply maponpaths, (!H).
    refine (toforallpaths _ _ _ 
      (nat_trans_eq_pointwise pp_canonical_TM_to_given _)
      _).
  }
  use total2_paths_f.
  exact (!eA).
  cbn. destruct eA; cbn. unfold idfun.
  apply subtypeEquality. { intros x; apply homset_property. }
  set (temp := proofirrelevance _ (isapropifcontr (term_to_section_aux t))).
  refine (maponpaths pr1 (temp (_,,_) (_,,_))).
  - cbn; split.
    + exact e.
    + exact H.
  - split.
    + apply (pr2 (pr2 (given_TM_to_canonical _ t))).
    + apply term_to_section_recover.
Qed.

Lemma canonical_to_given_to_canonical Γ
  : (canonical_TM_to_given : nat_trans _ _ )  Γ ;; given_TM_to_canonical Γ = identity _ .
Proof.
  apply funextsec; intro t.
  apply pathsinv0, canonical_TM_to_given_paths_adjoint, idpath.
Qed.

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
             (Y : compatible_term_structure (Z,,ZZ))
  : compatible_term_from_qq (Z,,ZZ) = Y.
Proof.
  set (i := isotoid _
                   (category_is_category _)
                   (canonical_TM_to_given_iso (Z,,ZZ) Y)).
  apply subtypeEquality.
  { intro. do 4 (apply impred; intro).
    apply homset_property. }
  destruct Y as [Y YH]. simpl.
  apply subtypeEquality.
  { intro. apply isaprop_term_fun_structure_axioms. }
  simpl.
  destruct Y as [Y YH']; simpl.
  use total2_paths_f.
  - apply i.
  - rewrite transportf_dirprod.
    destruct Y as [tm [p Q]]; simpl.
    apply dirprodeq; simpl.
    + etrans. eapply pathsinv0.
        apply  (idtoiso_precompose (preShv C)).
      unfold i.
      rewrite idtoiso_inv.
      rewrite idtoiso_isotoid.
      apply nat_trans_eq. 
      * apply has_homsets_HSET.
      * intro Γ. apply idpath.
    + assert (XR := 
          (idtoiso_transportf_family_of_morphisms (preShv C))).
      specialize (XR C (λ B, (TY X : functor _ _ ) B : hSet)).
      specialize (XR (λ Γ' B, (yoneda C (homset_property _) (Γ' ◂ B)))).
      etrans. apply XR.
      clear XR.
      apply funextsec; intro Γ.
      apply funextsec; intro A.
      unfold i. rewrite idtoiso_isotoid.
      apply nat_trans_eq. { apply has_homsets_HSET. }
      intro Γ'. simpl. cbn.
      apply funextsec;  intro s.
      unfold yoneda_morphisms_data.
      rewrite id_left.
      clear i.
      specialize (YH Γ Γ' A (s ;; π _ )). simpl in YH.
      assert (XR := nat_trans_eq_pointwise YH Γ').
      assert (XR2 := toforallpaths _ _ _ XR).
      cbn in XR2.
      etrans. apply XR2.
      clear XR2 XR YH.
      apply maponpaths.
      unfold yoneda_morphisms_data.
      match goal with |[|- PullbackArrow ?HH _ _ _ _ ;; _ = _ ] =>
            apply (PullbackArrow_PullbackPr2 HH) end.
Defined.



(* needs splitness? *)
Lemma iscontr_compatible_term_structure (Z : qq_morphism_data X) (ZZ : qq_morphism_axioms Z)
: iscontr (compatible_term_structure (Z,,ZZ)).
Proof.
  exists (compatible_term_from_qq (Z,,ZZ)).
  intro t.
  apply pathsinv0. apply unique.
Defined.

Lemma compat_split_comp_eq (Y : term_fun_structure _ X) :
  ∏ t : compatible_qq_morphism_structure Y,
  t = compatible_qq_from_term Y.
Proof.
  intro t.
    apply subtypeEquality.
    { intro.
      do 4 (apply impred; intro).
      apply homset_property. }
    simpl; apply subtypeEquality.
    { intro. apply @isaprop_qq_morphism_axioms. }
    apply subtypeEquality.
    { intro.
      do 4 (apply impred; intro).
      apply isofhleveltotal2. 
      - apply homset_property.
      - intro. apply isaprop_isPullback. } 
    simpl.
    destruct t as [[t H1] H2]. simpl.
    destruct t as [q h]; simpl.
    apply funextsec. intro Γ.
    apply funextsec; intro Γ'.
    apply funextsec; intro f.
    apply funextsec; intro A.    
    apply (invmaponpathsweq (weqpair _ (yoneda_fully_faithful _ (homset_property _) _ _ ))).
    apply pathsinv0.
    etrans. apply Yo_qq_term_Yo_of_qq.
    unfold Yo_of_qq.
    apply pathsinv0.
    apply PullbackArrowUnique.
    + etrans. apply maponpaths. cbn. apply idpath.
      rewrite <- functor_comp.
      etrans. eapply pathsinv0. refine (functor_comp Yo _ _).
      apply maponpaths.
      apply pathsinv0. apply (pr1 (h _ _ _ _ )).
    + etrans. apply maponpaths. cbn. apply idpath.
      apply pathsinv0.
      apply H2.
Time Qed.
  

Lemma iscontr_compatible_split_comp_structure (Y : term_fun_structure C X)
: iscontr (compatible_qq_morphism_structure Y).
Proof.
  exists (compatible_qq_from_term Y).
  apply compat_split_comp_eq.
Defined.

End compatible_structures.

Section Equivalence.

Definition T1 : UU :=
  ∑ Y : term_fun_structure C X,
        compatible_qq_morphism_structure Y.

Definition T2 : UU :=
  ∑ Z : qq_morphism_structure X,
        compatible_term_structure Z.

Definition shuffle : T1 ≃ T2.
Proof.
  eapply weqcomp.
  unfold T1.
  unfold compatible_qq_morphism_structure.
  set (XR := @weqtotal2asstol).
  specialize (XR (term_fun_structure C X)).
  specialize (XR (fun _ => qq_morphism_structure X)).
  simpl in XR.
  specialize (XR (fun YZ => iscompatible_term_qq (pr1 YZ) (pr2 YZ))).
  apply XR.
  eapply weqcomp. Focus 2.
  unfold T2. unfold compatible_term_structure.
  set (XR := @weqtotal2asstor).
  specialize (XR (qq_morphism_structure X)).
  specialize (XR (fun _ => term_fun_structure C X)).
  simpl in XR.
  specialize (XR (fun YZ => iscompatible_term_qq (pr2 YZ) (pr1 YZ))).
  apply XR.
  use weqbandf.
  - apply weqdirprodcomm.
  - intros. simpl.
    apply idweq.
Defined.

Definition forget_compat_term :
  T2 ≃ qq_morphism_structure X.
Proof.
  exists pr1.
  apply isweqpr1.
  intros [z zz].
  apply iscontr_compatible_term_structure.
Defined.

Definition forget_compat_qq :
  T1 ≃ term_fun_structure C X.
Proof.
  exists pr1.
  apply isweqpr1.
  intro.
  apply iscontr_compatible_split_comp_structure.
Defined.

Definition weq_CwF_SplitTypeCat : term_fun_structure C X ≃ qq_morphism_structure X.
Proof.
  eapply weqcomp.
    eapply invweq. apply forget_compat_qq.
  eapply weqcomp.
    apply shuffle.
  apply forget_compat_term.
Defined.

End Equivalence.

End Fix_Context.


 
(**
    TODO
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheory.
Require Import TypeTheory.Auxiliary.SetsAndPresheaves.

Require Import TypeTheory.CompCats.DiscreteComprehensionCat.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Local Definition D_ob {C : category} :=
  discrete_comprehension_cat_structure_with_default_mor_D_ob (C := C).

Local Definition F_ob {C : category} :=
  discrete_comprehension_cat_structure_with_default_mor_F_ob (C := C).

Local Definition D_lift_ob {C : category} :=
  discrete_comprehension_cat_structure_with_default_mor_D_lift_ob (C := C).

Local Definition D_ob_isaset {C : category} :=
  discrete_comprehension_cat_structure_with_default_mor_D_ob_isaset (C := C).

Local Definition D_id {C : category} :=
  discrete_comprehension_cat_structure_with_default_mor_D_id (C := C).

Local Definition D_comp {C : category} :=
  discrete_comprehension_cat_structure_with_default_mor_D_comp (C := C).

Local Definition F_mor {C : category} :=
  discrete_comprehension_cat_structure_with_default_mor_F_mor (C := C).

Section DiscCompCat_mor.

  Context (C : category).

  Definition DiscCompCatDef_TY
             (DC : discrete_comprehension_cat_structure_with_default_mor C)
    : preShv C.
  Proof.
    set (D_ob := pr1 DC).
    set (D_lift_ob := pr1 (pr2 (pr2 DC))).
    set (D_ob_isaset := pr1 (pr2 (pr2 (pr2 DC)))).
    set (D_id := pr1 (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 DC))))))).
    set (D_comp := pr2 (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 DC))))))).
    simpl in *.
    use tpair.
    - use tpair.
      + intros Γ. use tpair.
        * exact (D_ob Γ).
        * exact (D_ob_isaset Γ).
      + exact D_lift_ob.
    - use make_dirprod.
      + intros Γ. apply funextsec; intros A. apply D_id.
      + intros Γ Γ' Γ'' f g. apply funextsec; intros A.
        apply (D_comp _ _ _ _ _ _ _ _ (idpath _) (idpath _)).
  Defined.

  Definition DiscCompCatDef_mor_data
             (X Y : discrete_comprehension_cat_structure_with_default_mor C)
    : UU
    := ∑ (F_TY : ∏ {Γ : C}, D_ob X Γ → D_ob Y Γ),
       (* ϕ : *) ∏ (Γ : C) (A : D_ob X Γ),
            pr1 (F_ob X Γ A) --> pr1 (F_ob Y Γ (F_TY A)).

  Local Definition F_TY 
             {X Y : discrete_comprehension_cat_structure_with_default_mor C}
             (mor : DiscCompCatDef_mor_data X Y)
    := pr1 mor.

  Local Definition ϕ
             {X Y : discrete_comprehension_cat_structure_with_default_mor C}
             (mor : DiscCompCatDef_mor_data X Y)
    := pr2 mor.

  Definition DiscCompCatDef_mor_axiom_F_TY
             {X Y : discrete_comprehension_cat_structure_with_default_mor C}
             (mor : DiscCompCatDef_mor_data X Y)
    : UU
    := ∏ (Γ Γ' : C) (f : C ⟦ Γ', Γ ⟧) (A : D_ob X Γ),
       F_TY mor _ (D_lift_ob X _ _ f A) = D_lift_ob Y _ _ f (F_TY mor _ A).
                    
  Definition DiscCompCatDef_mor_axiom_ϕ_dpr
             {X Y : discrete_comprehension_cat_structure_with_default_mor C}
             (mor : DiscCompCatDef_mor_data X Y)
    : UU
    := ∏ (Γ : C) (A : D_ob X Γ),
       ϕ mor Γ A ;; pr2 (F_ob Y Γ (F_TY mor _ A)) = pr2 (F_ob X Γ A).

  Definition F_ob_compare
             {X : discrete_comprehension_cat_structure_with_default_mor C}
             {Γ : C} {A A' : D_ob X Γ} (e : A = A')
    : z_iso (pr1 (F_ob X Γ A)) (pr1 (F_ob X Γ A')).
  Proof.
    apply idtoiso, maponpaths, maponpaths, e.
  Defined.

  Lemma F_ob_compare_id {X : discrete_comprehension_cat_structure_with_default_mor C}
        {Γ : C} (A : D_ob X Γ)
    : F_ob_compare (idpath A) = identity_z_iso (pr1 (F_ob X Γ A)).
  Proof.
    apply idpath.
  Qed.

  Lemma F_ob_compare_id_general {X : discrete_comprehension_cat_structure_with_default_mor C}
        {Γ : C} {A : D_ob X Γ}
        (e : A = A)
    : F_ob_compare e = identity_z_iso (pr1 (F_ob X Γ A)).
  Proof.
    apply @pathscomp0 with (F_ob_compare (idpath _)). 
    apply maponpaths, D_ob_isaset.
    apply idpath.
  Qed.

  Lemma F_ob_compare_comp {X : discrete_comprehension_cat_structure_with_default_mor C}
        {Γ : C} {A A' A'' : D_ob X Γ} (e : A = A') (e' : A' = A'')
    : pr1 (F_ob_compare (e @ e')) = F_ob_compare e ;; F_ob_compare e'.
  Proof.
    etrans. 2: { apply idtoiso_concat_pr. } 
    unfold F_ob_compare. apply maponpaths, maponpaths.
    etrans. 2: apply maponpathscomp0. 
    apply maponpaths.
    apply maponpathscomp0.
  Qed.

  Lemma F_ob_compare_comp_general {X : discrete_comprehension_cat_structure_with_default_mor C}
        {Γ : C} {A A' A'' : D_ob X Γ}
        (e : A = A') (e' : A' = A'') (e'' : A = A'')
    : pr1 (F_ob_compare e'') = F_ob_compare e ;; F_ob_compare e'.
  Proof.
    refine (_ @ F_ob_compare_comp _ _).
    apply maponpaths, maponpaths, D_ob_isaset.
  Qed.

  Definition Δ
             {X Y : discrete_comprehension_cat_structure_with_default_mor C}
             (mor : DiscCompCatDef_mor_data X Y)
             (F_TY_ax : DiscCompCatDef_mor_axiom_F_TY mor)
    : ∏ (Γ Γ' : C) (f : C ⟦ Γ', Γ ⟧) (A : D_ob X Γ),
      C ⟦ pr1 (F_ob Y Γ' (F_TY mor Γ' (D_lift_ob X Γ Γ' f A))),
          pr1 (F_ob Y Γ' (D_lift_ob Y Γ Γ' f (F_TY mor Γ A))) ⟧.
  Proof.
    intros Γ A Γ' f.
    use F_ob_compare.
    apply F_TY_ax.
  Defined.
    
  Lemma Δ_ϕ
        {X Y : discrete_comprehension_cat_structure_with_default_mor C}
        (G : DiscCompCatDef_mor_data X Y)
        {Γ : C} {A A' : D_ob X Γ}
        (e : A = A')
    : F_ob_compare e ;; ϕ G Γ A' = ϕ G Γ A ;; F_ob_compare (maponpaths (F_TY G _) e).
  Proof.
    destruct e; simpl. etrans. apply id_left. apply pathsinv0, id_right.
  Defined.

  Definition DiscCompCatDef_mor_axiom_ϕ_qq
             {X Y : discrete_comprehension_cat_structure_with_default_mor C}
             (mor : DiscCompCatDef_mor_data X Y)
             (F_TY_ax : DiscCompCatDef_mor_axiom_F_TY mor)
    : UU
    := ∏ (Γ Γ' : C) (f : C ⟦ Γ', Γ ⟧) (A : D_ob X Γ),
       pr1 (F_mor X Γ' Γ (D_lift_ob X _ _ f A) A f (idpath _)) ;; ϕ mor Γ A =
       ϕ mor Γ' (D_lift_ob X _ _ f A) ;; Δ mor F_TY_ax Γ Γ' f A ;; pr1 (F_mor Y Γ' Γ (D_lift_ob Y _ _ f (F_TY mor _ A)) (F_TY mor _ A) f (idpath _))
  .

  Definition DiscCompCatDef_mor_axioms
             {X Y : discrete_comprehension_cat_structure_with_default_mor C}
             (mor : DiscCompCatDef_mor_data X Y)
    : UU
    := ∑ (F_TY_ax : DiscCompCatDef_mor_axiom_F_TY mor)
        (ϕ_dpr_ax : DiscCompCatDef_mor_axiom_ϕ_dpr mor),
      (* ϕ_qq_ax : *) DiscCompCatDef_mor_axiom_ϕ_qq mor F_TY_ax.

  Definition isaprop_DiscCompCatDef_mor_axiom_F_TY
             {X Y : discrete_comprehension_cat_structure_with_default_mor C}
             (mor : DiscCompCatDef_mor_data X Y)
    : isaprop (DiscCompCatDef_mor_axiom_F_TY mor).
  Proof.
    repeat (apply impred_isaprop; intros ?).
    apply D_ob_isaset.
  Qed.

  Definition isaprop_DiscCompCatDef_mor_axiom_ϕ_dpr
             {X Y : discrete_comprehension_cat_structure_with_default_mor C}
             (mor : DiscCompCatDef_mor_data X Y)
    : isaprop (DiscCompCatDef_mor_axiom_ϕ_dpr mor).
  Proof.
    repeat (apply impred_isaprop; intros ?).
    apply homset_property.
  Qed.
       
  Definition isaprop_DiscCompCatDef_mor_axiom_ϕ_qq
             {X Y : discrete_comprehension_cat_structure_with_default_mor C}
             (mor : DiscCompCatDef_mor_data X Y)
             (F_TY_ax : DiscCompCatDef_mor_axiom_F_TY mor)
    : isaprop (DiscCompCatDef_mor_axiom_ϕ_qq mor F_TY_ax).
  Proof.
    repeat (apply impred_isaprop; intros ?).
    apply homset_property.
  Qed.

  Definition isaprop_DiscCompCatDef_mor_axioms
             {X Y : discrete_comprehension_cat_structure_with_default_mor C}
             (mor : DiscCompCatDef_mor_data X Y)
    : isaprop (DiscCompCatDef_mor_axioms mor).
  Proof.
    apply Propositions.isaproptotal2.
    - intros ?. apply isapropdirprod.
      + apply isaprop_DiscCompCatDef_mor_axiom_ϕ_dpr.
      + apply isaprop_DiscCompCatDef_mor_axiom_ϕ_qq.
    - intros. apply isaprop_DiscCompCatDef_mor_axiom_F_TY. 
  Qed.

  Definition DiscCompCatDef_mor
             (X Y : discrete_comprehension_cat_structure_with_default_mor C)
    : UU
    := ∑ (mor : DiscCompCatDef_mor_data X Y), DiscCompCatDef_mor_axioms mor.

  Definition DiscCompCatDef_mor_to_mor_data
             {X Y : discrete_comprehension_cat_structure_with_default_mor C}
             (mor : DiscCompCatDef_mor X Y)
    : DiscCompCatDef_mor_data X Y
    := pr1 mor.

  Coercion DiscCompCatDef_mor_to_mor_data : DiscCompCatDef_mor >-> DiscCompCatDef_mor_data.

  Definition DiscCompCatDef_mor_eq
             {X Y : discrete_comprehension_cat_structure_with_default_mor C}
             (F G : DiscCompCatDef_mor X Y)
             (F_TY_eq : ∏ Γ (A : D_ob X Γ), F_TY F _ A = F_TY G _ A)
             (ϕ_eq : ∏ Γ (A : D_ob X Γ),
                     ϕ F _ A ;; F_ob_compare (F_TY_eq Γ A) = ϕ G _ A)
    : F = G.
  Proof.
    use total2_paths_f. 2: apply isaprop_DiscCompCatDef_mor_axioms.
    use total2_paths_f.
    - repeat (apply funextsec; intros ?). apply F_TY_eq.
    - etrans. use transportf_forall.
      apply funextsec; intros Γ.
      etrans. use transportf_forall.
      apply funextsec; intros A.
      refine (_ @ ϕ_eq Γ A).
      etrans. apply (functtransportf
                       (λ x, x Γ A)
                       (λ y, C ⟦ pr1 (F_ob X Γ A), pr1 (F_ob Y Γ y) ⟧)).
      etrans. apply (functtransportf
                       (λ x, F_ob Y Γ x)
                       (λ y, C ⟦ pr1 (F_ob X Γ A), pr1 y ⟧)).
      etrans. apply (functtransportf
                       (λ x, pr1 x)
                       (λ y, C ⟦ pr1 (F_ob X Γ A), y ⟧)).
      etrans. apply pathsinv0, idtoiso_postcompose.
      apply maponpaths.
      unfold F_ob_compare.
      apply maponpaths.
      apply maponpaths.
      apply maponpaths.
      apply maponpaths.
      apply D_ob_isaset.
  Defined.

  Definition DiscCompCatDef_precat_ob_mor
    : precategory_ob_mor
    := (_ ,, DiscCompCatDef_mor).
                                                              
             
  Definition DiscCompCatDef_mor_id_data
             (X : discrete_comprehension_cat_structure_with_default_mor C)
    : DiscCompCatDef_mor_data X X.
  Proof.
    use tpair.
    + intros Γ. apply idfun.
    + intros Γ A. apply identity.
  Defined.

  Definition DiscCompCatDef_mor_id_axioms
             (X : discrete_comprehension_cat_structure_with_default_mor C)
    : DiscCompCatDef_mor_axioms (DiscCompCatDef_mor_id_data X).
  Proof.
    use tpair. 2: use make_dirprod.
    + intros Γ Γ' f A. apply idpath.
    + intros Γ A. apply id_left.
    + intros Γ Γ' f A.
      etrans. apply id_right.
      apply pathsinv0.
      etrans. apply assoc'.
      etrans. apply id_left.
      apply id_left.
  Qed.

  Definition DiscCompCatDef_mor_id
             (X : discrete_comprehension_cat_structure_with_default_mor C)
    : DiscCompCatDef_mor X X
    := (_ ,, DiscCompCatDef_mor_id_axioms X).
  
  Definition DiscCompCatDef_mor_comp_data
             (X Y Z : discrete_comprehension_cat_structure_with_default_mor C)
             (F : DiscCompCatDef_mor_data X Y)
             (G : DiscCompCatDef_mor_data Y Z)
    : DiscCompCatDef_mor_data X Z.
  Proof.
    use tpair.
    + intros Γ A. apply (F_TY G _ (F_TY F _ A)).
    + intros Γ A. apply (ϕ F _ _ ;; ϕ G _ _).
  Defined.

  Definition DiscCompCatDef_mor_comp_axioms
             (X Y Z : discrete_comprehension_cat_structure_with_default_mor C)
             (F : DiscCompCatDef_mor X Y)
             (G : DiscCompCatDef_mor Y Z)
    : DiscCompCatDef_mor_axioms (DiscCompCatDef_mor_comp_data X Y Z F G).
  Proof.
    use tpair. 2: use make_dirprod.
    + intros Γ Γ' f A. cbn.
      etrans. apply maponpaths.
      apply (pr1 (pr2 F)).
      apply (pr1 (pr2 G)).
    + intros Γ A. cbn.
      etrans. apply assoc'.
      etrans. apply maponpaths.
      apply (pr1 (pr2 (pr2 G))).
      apply (pr1 (pr2 (pr2 F))).
    + intros Γ Γ' f A. cbn.
      etrans. apply assoc.
      etrans. apply maponpaths_2.
      apply (pr2 (pr2 (pr2 F))).
      etrans. apply assoc'.
      etrans. apply maponpaths.
      apply (pr2 (pr2 (pr2 G))).
      etrans. apply assoc.
      apply maponpaths_2.
      etrans. apply assoc'.
      etrans. 2: apply assoc.
      apply maponpaths.

      etrans. apply assoc.
      etrans. apply maponpaths_2, Δ_ϕ.
      etrans. apply assoc'.

      apply maponpaths.
      apply pathsinv0.
      apply F_ob_compare_comp_general.
  Qed.

  Definition DiscCompCatDef_mor_comp
             (X Y Z : discrete_comprehension_cat_structure_with_default_mor C)
             (F : DiscCompCatDef_mor X Y)
             (G : DiscCompCatDef_mor Y Z)
    : DiscCompCatDef_mor X Z
    := (_ ,, DiscCompCatDef_mor_comp_axioms X Y Z F G).

  Definition DiscCompCatDef_precat_id_comp
    : precategory_id_comp (DiscCompCatDef_precat_ob_mor)
    := (DiscCompCatDef_mor_id , DiscCompCatDef_mor_comp).

  Definition DiscCompCatDef_precat_data
    : precategory_data
    := (_ ,, DiscCompCatDef_precat_id_comp).

  Definition DiscCompCatDef_precat_id_left
             (X Y : DiscCompCatDef_precat_data)
             (F : DiscCompCatDef_precat_data ⟦ X, Y ⟧)
    : identity X ;; F = F.
  Proof.
    use DiscCompCatDef_mor_eq.
    - intros Γ A. apply idpath.
    - intros Γ A. etrans. apply id_right. apply id_left.
  Qed.

  Definition DiscCompCatDef_precat_id_right
             (X Y : DiscCompCatDef_precat_data)
             (F : DiscCompCatDef_precat_data ⟦ X, Y ⟧)
    : F ;; identity Y = F.
  Proof.
    use DiscCompCatDef_mor_eq.
    - intros Γ A. apply idpath.
    - intros Γ A. etrans. apply id_right. apply id_right.
  Qed.

  Definition DiscCompCatDef_precat_assoc
             (X Y Z W : DiscCompCatDef_precat_data)
             (F : DiscCompCatDef_precat_data ⟦ X, Y ⟧)
             (G : DiscCompCatDef_precat_data ⟦ Y, Z ⟧)
             (H : DiscCompCatDef_precat_data ⟦ Z, W ⟧)
    : F ;; (G ;; H) = (F ;; G) ;; H.
  Proof.
    use DiscCompCatDef_mor_eq.
    - intros Γ A. apply idpath.
    - intros Γ A. etrans. apply id_right. apply assoc.
  Qed.

  Definition DiscCompCatDef_precat_assoc'
             (X Y Z W : DiscCompCatDef_precat_data)
             (F : DiscCompCatDef_precat_data ⟦ X, Y ⟧)
             (G : DiscCompCatDef_precat_data ⟦ Y, Z ⟧)
             (H : DiscCompCatDef_precat_data ⟦ Z, W ⟧)
    : (F ;; G) ;; H = F ;; (G ;; H).
  Proof.
    use DiscCompCatDef_mor_eq.
    - intros Γ A. apply idpath.
    - intros Γ A. etrans. apply id_right. apply assoc'.
  Qed.

  Definition DiscCompCatDef_precat_axioms
    : is_precategory DiscCompCatDef_precat_data.
  Proof.
    use make_is_precategory.
    - apply DiscCompCatDef_precat_id_left.
    - apply DiscCompCatDef_precat_id_right.
    - apply DiscCompCatDef_precat_assoc.
    - apply DiscCompCatDef_precat_assoc'.
  Qed.

  Definition DiscCompCatDef_precat : precategory
    := (_ ,, DiscCompCatDef_precat_axioms).

  Definition DiscCompCatDef_precat_has_homsets
    : has_homsets DiscCompCatDef_precat.
  Proof.
    intros X Y.
    apply isaset_total2. 2: intros ?; apply isasetaprop, isaprop_DiscCompCatDef_mor_axioms.
    - apply isaset_total2.
      + repeat (apply impred_isaset; intros ?).
        apply D_ob_isaset.
      + intros ?.
        repeat (apply impred_isaset; intros ?).
        apply homset_property.
  Defined.

  Definition DiscCompCatDef_cat : category
    := (DiscCompCatDef_precat ,, DiscCompCatDef_precat_has_homsets).

End DiscCompCat_mor.

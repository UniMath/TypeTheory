(**
    TODO
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheory.
Require Import TypeTheory.CompCats.DiscreteComprehensionCat.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Local Definition D_ob {C : category} :=
  discrete_comprehension_cat_structure1_D_ob (C := C).

Local Definition F_ob {C : category} :=
  discrete_comprehension_cat_structure1_F_ob (C := C).

Local Definition D_lift_ob {C : category} :=
  discrete_comprehension_cat_structure1_D_lift_ob (C := C).

Local Definition D_ob_isaset {C : category} :=
  discrete_comprehension_cat_structure1_D_ob_isaset (C := C).

Local Definition D_id {C : category} :=
  discrete_comprehension_cat_structure1_D_id (C := C).

Local Definition D_comp {C : category} :=
  discrete_comprehension_cat_structure1_D_comp (C := C).

Local Definition D_mor_with_unique_lift {C : category} :=
  discrete_comprehension_cat_structure1_D_mor_with_unique_lift (C := C).

Local Definition D_mor {C : category}
      (DC : discrete_comprehension_cat_structure1 C)
  := pr1 (D_mor_with_unique_lift DC).

Local Definition D_lift_mor {C : category}
      (DC : discrete_comprehension_cat_structure1 C)
      {Γ Γ' : C}
      (f : C ⟦ Γ', Γ ⟧) (A : pr1 DC Γ)
  : D_mor DC Γ' Γ (D_lift_ob DC Γ Γ' f A) A f
  := pr1 (pr2 (pr2 (D_mor_with_unique_lift DC)) Γ Γ' f A).

Local Definition F_mor {C : category} :=
  discrete_comprehension_cat_structure1_F_mor (C := C).

Section DiscCompCat_mor.

  Context (C : category).

  Definition DiscCompCat_mor_data
             (X Y : discrete_comprehension_cat_structure1 C)
    : UU
    := ∑ (F_TY : ∏ {Γ : C}, D_ob X Γ → D_ob Y Γ),
       (* ϕ : *) ∏ (Γ : C) (A : D_ob X Γ),
            pr1 (F_ob X Γ A) --> pr1 (F_ob Y Γ (F_TY A)).

  Local Definition F_TY 
             {X Y : discrete_comprehension_cat_structure1 C}
             (mor : DiscCompCat_mor_data X Y)
    := pr1 mor.

  Local Definition ϕ
             {X Y : discrete_comprehension_cat_structure1 C}
             (mor : DiscCompCat_mor_data X Y)
    := pr2 mor.

  Definition DiscCompCat_mor_axiom_F_TY
             {X Y : discrete_comprehension_cat_structure1 C}
             (mor : DiscCompCat_mor_data X Y)
    : UU
    := ∏ (Γ Γ' : C) (f : C ⟦ Γ', Γ ⟧) (A : D_ob X Γ),
       F_TY mor _ (D_lift_ob X _ _ f A) = D_lift_ob Y _ _ f (F_TY mor _ A).
                    
  Definition DiscCompCat_mor_axiom_ϕ_dpr
             {X Y : discrete_comprehension_cat_structure1 C}
             (mor : DiscCompCat_mor_data X Y)
    : UU
    := ∏ (Γ : C) (A : D_ob X Γ),
       ϕ mor Γ A ;; pr2 (F_ob Y Γ (F_TY mor _ A)) = pr2 (F_ob X Γ A).

  Definition F_ob_compare
             {X : discrete_comprehension_cat_structure1 C}
             {Γ : C} {A A' : D_ob X Γ} (e : A = A')
    : z_iso (pr1 (F_ob X Γ A)) (pr1 (F_ob X Γ A')).
  Proof.
    apply idtoiso, maponpaths, maponpaths, e.
  Defined.

  Lemma F_ob_compare_id {X : discrete_comprehension_cat_structure1 C}
        {Γ : C} (A : D_ob X Γ)
    : F_ob_compare (idpath A) = identity_z_iso (pr1 (F_ob X Γ A)).
  Proof.
    apply idpath.
  Qed.

  Lemma F_ob_compare_id_general {X : discrete_comprehension_cat_structure1 C}
        {Γ : C} {A : D_ob X Γ}
        (e : A = A)
    : F_ob_compare e = identity_z_iso (pr1 (F_ob X Γ A)).
  Proof.
    apply @pathscomp0 with (F_ob_compare (idpath _)). 
    apply maponpaths, D_ob_isaset.
    apply idpath.
  Qed.

  Lemma F_ob_compare_comp {X : discrete_comprehension_cat_structure1 C}
        {Γ : C} {A A' A'' : D_ob X Γ} (e : A = A') (e' : A' = A'')
    : pr1 (F_ob_compare (e @ e')) = F_ob_compare e ;; F_ob_compare e'.
  Proof.
    etrans. 2: { apply idtoiso_concat_pr. }
    unfold F_ob_compare. apply maponpaths, maponpaths.
    etrans. 2: apply maponpathscomp0. 
    apply maponpaths.
    apply maponpathscomp0.
  Qed.

  Lemma F_ob_compare_comp_general {X : discrete_comprehension_cat_structure1 C}
        {Γ : C} {A A' A'' : D_ob X Γ}
        (e : A = A') (e' : A' = A'') (e'' : A = A'')
    : pr1 (F_ob_compare e'') = F_ob_compare e ;; F_ob_compare e'.
  Proof.
    refine (_ @ F_ob_compare_comp _ _).
    apply maponpaths, maponpaths, D_ob_isaset.
  Qed.

  Definition Δ
             {X Y : discrete_comprehension_cat_structure1 C}
             (mor : DiscCompCat_mor_data X Y)
             (F_TY_ax : DiscCompCat_mor_axiom_F_TY mor)
    : ∏ (Γ Γ' : C) (f : C ⟦ Γ', Γ ⟧) (A : D_ob X Γ),
      C ⟦ pr1 (F_ob Y Γ' (F_TY mor Γ' (D_lift_ob X Γ Γ' f A))),
          pr1 (F_ob Y Γ' (D_lift_ob Y Γ Γ' f (F_TY mor Γ A))) ⟧.
  Proof.
    intros Γ A Γ' f.
    use F_ob_compare.
    apply F_TY_ax.
  Defined.
    
  Lemma Δ_ϕ
        {X Y : discrete_comprehension_cat_structure1 C}
        (G : DiscCompCat_mor_data X Y)
        {Γ : C} {A A' : D_ob X Γ}
        (e : A = A')
    : F_ob_compare e ;; ϕ G Γ A' = ϕ G Γ A ;; F_ob_compare (maponpaths (F_TY G _) e).
  Proof.
    destruct e; simpl. etrans. apply id_left. apply pathsinv0, id_right.
  Qed.

  Definition F_TY_on_morphisms
             {X Y : discrete_comprehension_cat_structure1 C}
             (mor : DiscCompCat_mor_data X Y)
             (F_TY_ax : DiscCompCat_mor_axiom_F_TY mor)
             {Γ Γ' : C} {f : C ⟦ Γ, Γ' ⟧}
             {A : D_ob X Γ} {A' : D_ob X Γ'}
    : D_mor X Γ Γ' A A' f → D_mor Y Γ Γ' (F_TY mor _ A) (F_TY mor _ A') f.
  Proof.
    intros ff.
    apply (invweq (mor_with_unique_lift_mor_weq _ _ (D_ob_isaset Y) _)).
    etrans. apply pathsinv0, (F_TY_ax Γ' Γ f A').
    apply maponpaths.
    apply (mor_with_unique_lift_mor_weq _ _ (D_ob_isaset X) _ ff).
  Qed.

  Definition DiscCompCat_mor_axiom_ϕ_qq
             {X Y : discrete_comprehension_cat_structure1 C}
             (mor : DiscCompCat_mor_data X Y)
             (F_TY_ax : DiscCompCat_mor_axiom_F_TY mor)
    : UU
    := ∏ (Γ Γ' : C) (f : C ⟦ Γ', Γ ⟧)
         (A : D_ob X Γ) (A' : D_ob X Γ') (ff : D_mor X _ _ A' A f),
       pr1 (F_mor X Γ' Γ A' A f ff) ;; ϕ mor Γ A =
       ϕ mor Γ' A' ;; pr1 (F_mor Y Γ' Γ (F_TY mor _ A') (F_TY mor _ A) f
                                 (F_TY_on_morphisms mor F_TY_ax ff)).

  Definition DiscCompCat_mor_axioms
             {X Y : discrete_comprehension_cat_structure1 C}
             (mor : DiscCompCat_mor_data X Y)
    : UU
    := ∑ (F_TY_ax : DiscCompCat_mor_axiom_F_TY mor)
        (ϕ_dpr_ax : DiscCompCat_mor_axiom_ϕ_dpr mor),
      (* ϕ_qq_ax : *) DiscCompCat_mor_axiom_ϕ_qq mor F_TY_ax.

  Definition isaprop_DiscCompCat_mor_axiom_F_TY
             {X Y : discrete_comprehension_cat_structure1 C}
             (mor : DiscCompCat_mor_data X Y)
    : isaprop (DiscCompCat_mor_axiom_F_TY mor).
  Proof.
    repeat (apply impred_isaprop; intros ?).
    apply D_ob_isaset.
  Qed.

  Definition isaprop_DiscCompCat_mor_axiom_ϕ_dpr
             {X Y : discrete_comprehension_cat_structure1 C}
             (mor : DiscCompCat_mor_data X Y)
    : isaprop (DiscCompCat_mor_axiom_ϕ_dpr mor).
  Proof.
    repeat (apply impred_isaprop; intros ?).
    apply homset_property.
  Qed.
       
  Definition isaprop_DiscCompCat_mor_axiom_ϕ_qq
             {X Y : discrete_comprehension_cat_structure1 C}
             (mor : DiscCompCat_mor_data X Y)
             (F_TY_ax : DiscCompCat_mor_axiom_F_TY mor)
    : isaprop (DiscCompCat_mor_axiom_ϕ_qq mor F_TY_ax).
  Proof.
    repeat (apply impred_isaprop; intros ?).
    apply homset_property.
  Qed.

  Definition isaprop_DiscCompCat_mor_axioms
             {X Y : discrete_comprehension_cat_structure1 C}
             (mor : DiscCompCat_mor_data X Y)
    : isaprop (DiscCompCat_mor_axioms mor).
  Proof.
    apply Propositions.isaproptotal2.
    - intros ?. apply isapropdirprod.
      + apply isaprop_DiscCompCat_mor_axiom_ϕ_dpr.
      + apply isaprop_DiscCompCat_mor_axiom_ϕ_qq.
    - intros. apply isaprop_DiscCompCat_mor_axiom_F_TY. 
  Qed.

  Definition DiscCompCat_mor
             (X Y : discrete_comprehension_cat_structure1 C)
    : UU
    := ∑ (mor : DiscCompCat_mor_data X Y), DiscCompCat_mor_axioms mor.

  Definition DiscCompCat_mor_to_mor_data
             {X Y : discrete_comprehension_cat_structure1 C}
             (mor : DiscCompCat_mor X Y)
    : DiscCompCat_mor_data X Y
    := pr1 mor.

  Coercion DiscCompCat_mor_to_mor_data : DiscCompCat_mor >-> DiscCompCat_mor_data.

  Definition DiscCompCat_mor_eq
             {X Y : discrete_comprehension_cat_structure1 C}
             (F G : DiscCompCat_mor X Y)
             (F_TY_eq : ∏ Γ (A : D_ob X Γ), F_TY F _ A = F_TY G _ A)
             (ϕ_eq : ∏ Γ (A : D_ob X Γ),
                     ϕ F _ A ;; F_ob_compare (F_TY_eq Γ A) = ϕ G _ A)
    : F = G.
  Proof.
    use total2_paths_f. 2: apply isaprop_DiscCompCat_mor_axioms.
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

  Definition DiscCompCat_precat_ob_mor
    : precategory_ob_mor
    := (_ ,, DiscCompCat_mor).
                                                              
             
  Definition DiscCompCat_mor_id_data
             (X : discrete_comprehension_cat_structure1 C)
    : DiscCompCat_mor_data X X.
  Proof.
    use tpair.
    + intros Γ. apply idfun.
    + intros Γ A. apply identity.
  Defined.

  Definition DiscCompCat_mor_id_axioms
             (X : discrete_comprehension_cat_structure1 C)
    : DiscCompCat_mor_axioms (DiscCompCat_mor_id_data X).
  Proof.
    use tpair. 2: use make_dirprod.
    + intros Γ Γ' f A. apply idpath.
    + intros Γ A. apply id_left.
    + intros Γ Γ' f A A' ff.
      etrans. apply id_right. cbn.
      apply pathsinv0.
      etrans. apply id_left.
      apply maponpaths.
      apply maponpaths.
      apply isaprop_mor_with_unique_lift_mor.
      apply D_ob_isaset.
  Qed.

  Definition DiscCompCat_mor_id
             (X : discrete_comprehension_cat_structure1 C)
    : DiscCompCat_mor X X
    := (_ ,, DiscCompCat_mor_id_axioms X).
  
  Definition DiscCompCat_mor_comp_data
             (X Y Z : discrete_comprehension_cat_structure1 C)
             (F : DiscCompCat_mor_data X Y)
             (G : DiscCompCat_mor_data Y Z)
    : DiscCompCat_mor_data X Z.
  Proof.
    use tpair.
    + intros Γ A. apply (F_TY G _ (F_TY F _ A)).
    + intros Γ A. apply (ϕ F _ _ ;; ϕ G _ _).
  Defined.

  Definition DiscCompCat_mor_comp_axioms
             (X Y Z : discrete_comprehension_cat_structure1 C)
             (F : DiscCompCat_mor X Y)
             (G : DiscCompCat_mor Y Z)
    : DiscCompCat_mor_axioms (DiscCompCat_mor_comp_data X Y Z F G).
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
    + intros Γ Γ' f A A' ff. cbn.
      etrans. apply assoc.
      etrans. apply maponpaths_2.
      apply (pr2 (pr2 (pr2 F))).
      etrans. apply assoc'.
      etrans. apply maponpaths.
      apply (pr2 (pr2 (pr2 G))).
      etrans. 2: apply assoc.
      apply maponpaths.
      apply maponpaths.
      apply maponpaths.
      apply maponpaths.
      apply isaprop_mor_with_unique_lift_mor.
      apply D_ob_isaset.
  Qed.

  Definition DiscCompCat_mor_comp
             (X Y Z : discrete_comprehension_cat_structure1 C)
             (F : DiscCompCat_mor X Y)
             (G : DiscCompCat_mor Y Z)
    : DiscCompCat_mor X Z
    := (_ ,, DiscCompCat_mor_comp_axioms X Y Z F G).

  Definition DiscCompCat_precat_id_comp
    : precategory_id_comp (DiscCompCat_precat_ob_mor)
    := (DiscCompCat_mor_id , DiscCompCat_mor_comp).

  Definition DiscCompCat_precat_data
    : precategory_data
    := (_ ,, DiscCompCat_precat_id_comp).

  Definition DiscCompCat_precat_id_left
             (X Y : DiscCompCat_precat_data)
             (F : DiscCompCat_precat_data ⟦ X, Y ⟧)
    : identity X ;; F = F.
  Proof.
    use DiscCompCat_mor_eq.
    - intros Γ A. apply idpath.
    - intros Γ A. etrans. apply id_right. apply id_left.
  Qed.

  Definition DiscCompCat_precat_id_right
             (X Y : DiscCompCat_precat_data)
             (F : DiscCompCat_precat_data ⟦ X, Y ⟧)
    : F ;; identity Y = F.
  Proof.
    use DiscCompCat_mor_eq.
    - intros Γ A. apply idpath.
    - intros Γ A. etrans. apply id_right. apply id_right.
  Qed.

  Definition DiscCompCat_precat_assoc
             (X Y Z W : DiscCompCat_precat_data)
             (F : DiscCompCat_precat_data ⟦ X, Y ⟧)
             (G : DiscCompCat_precat_data ⟦ Y, Z ⟧)
             (H : DiscCompCat_precat_data ⟦ Z, W ⟧)
    : F ;; (G ;; H) = (F ;; G) ;; H.
  Proof.
    use DiscCompCat_mor_eq.
    - intros Γ A. apply idpath.
    - intros Γ A. etrans. apply id_right. apply assoc.
  Qed.

  Definition DiscCompCat_precat_assoc'
             (X Y Z W : DiscCompCat_precat_data)
             (F : DiscCompCat_precat_data ⟦ X, Y ⟧)
             (G : DiscCompCat_precat_data ⟦ Y, Z ⟧)
             (H : DiscCompCat_precat_data ⟦ Z, W ⟧)
    : (F ;; G) ;; H = F ;; (G ;; H).
  Proof.
    use DiscCompCat_mor_eq.
    - intros Γ A. apply idpath.
    - intros Γ A. etrans. apply id_right. apply assoc'.
  Qed.

  Definition DiscCompCat_precat_axioms
    : is_precategory DiscCompCat_precat_data.
  Proof.
    use make_is_precategory.
    - apply DiscCompCat_precat_id_left.
    - apply DiscCompCat_precat_id_right.
    - apply DiscCompCat_precat_assoc.
    - apply DiscCompCat_precat_assoc'.
  Qed.

  Definition DiscCompCat_precat : precategory
    := (_ ,, DiscCompCat_precat_axioms).

  Definition DiscCompCat_precat_has_homsets
    : has_homsets DiscCompCat_precat.
  Proof.
    intros X Y.
    apply isaset_total2. 2: intros ?; apply isasetaprop, isaprop_DiscCompCat_mor_axioms.
    - apply isaset_total2.
      + repeat (apply impred_isaset; intros ?).
        apply D_ob_isaset.
      + intros ?.
        repeat (apply impred_isaset; intros ?).
        apply homset_property.
  Defined.

  Definition DiscCompCat_cat : category
    := (DiscCompCat_precat ,, DiscCompCat_precat_has_homsets).

End DiscCompCat_mor.

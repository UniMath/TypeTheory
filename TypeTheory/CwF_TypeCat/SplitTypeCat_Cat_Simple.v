(**
    TODO
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheory.
Require Import TypeTheory.Auxiliary.SetsAndPresheaves.

Require Import TypeTheory.TypeCat.TypeCat.
Require Import TypeTheory.CwF_TypeCat.CwF_SplitTypeCat_Defs.
Require Import TypeTheory.CwF_TypeCat.TypeCat_Reassoc.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.

Section SplitTypeCat_Cat_Simple.

  Context (C : category).

  Definition TY'
    : split_typecat_structure C → preShv C.
  Proof.
    intros TC.
    use tpair.
    - use tpair.
      + intros Γ.
        exists (TC Γ).
        apply (pr1 (pr2 TC)).
      + intros Γ Γ' f A.
        apply (reind_typecat A f).
    - use make_dirprod.
      + intros Γ. simpl. 
        use funextsec; intros A.
        apply (pr1 (pr1 (pr2 (pr2 TC)))).
      + intros Γ Γ' Γ'' f g. simpl. 
        use funextsec; intros A.
        apply (pr1 (pr2 (pr2 (pr2 TC)))).
  Defined.

  Definition TY'_TY_eq
             (TC : split_typecat_structure C)
    : TY' TC = TY (weq_standalone_to_regrouped TC).
  Proof.
    use total2_paths_f.
    - apply idpath.
    - apply isaprop_is_functor. apply homset_property.
  Defined.

  Definition SplitTy_mor_data
             (X Y : split_typecat_structure C)
    : UU
    := ∑ (F_TY : ∏ (Γ : C), X Γ → Y Γ),
       (* ϕ : *) ∏ (Γ : C) (A : X Γ), Γ ◂ A --> Γ ◂ (F_TY _ A).

  Definition SplitTy_mor_axiom_F_TY
             {X Y : split_typecat_structure C}
             (mor : SplitTy_mor_data X Y)
    : UU
    := ∏ (Γ Γ' : C) (f : C ⟦ Γ', Γ ⟧) (A : X Γ),
       pr1 mor _ (reind_typecat A f) = reind_typecat (pr1 mor _ A) f.

  Definition SplitTy_mor_axiom_dpr
             {X Y : split_typecat_structure C}
             (mor : SplitTy_mor_data X Y)
    : UU
    := ∏ (Γ : C) (A : X Γ),
       pr2 mor Γ A ;; dpr_typecat _ = dpr_typecat _. (* ϕ ;; π (F_TY A) = π A *)

  Definition reind_ext_compare
             {X : split_typecat_structure C}
             {Γ : C} {A A' : TY' X $p Γ} (e : A = A')
    : z_iso (Γ ◂ A) (Γ ◂ A').
  Proof.
    apply idtoiso, maponpaths, e.
  Defined.

  Lemma reind_ext_compare_id {X : split_typecat_structure C}
        {Γ : C} (A : TY' X $p Γ)
    : reind_ext_compare (idpath A) = identity_z_iso (Γ ◂ A).
  Proof.
    apply idpath.
  Qed.

  Lemma reind_ext_compare_id_general {X : split_typecat_structure C}
        {Γ : C} {A : TY' X $p Γ}
        (e : A = A)
    : reind_ext_compare e = identity_z_iso (Γ ◂ A).
  Proof.
    apply @pathscomp0 with (reind_ext_compare (idpath _)). 
    apply maponpaths, setproperty.
    apply idpath.
  Qed.

  Lemma reind_ext_compare_comp {X : split_typecat_structure C}
        {Γ : C} {A A' A'' : TY' X $p Γ} (e : A = A') (e' : A' = A'')
    : pr1 (reind_ext_compare (e @ e')) = reind_ext_compare e ;; reind_ext_compare e'.
  Proof.
    etrans. 2: { apply idtoiso_concat_pr. } 
    unfold reind_ext_compare. apply maponpaths, maponpaths.
    apply maponpathscomp0. 
  Qed.

  Lemma reind_ext_compare_comp_general {X : split_typecat_structure C}
        {Γ : C} {A A' A'' : TY' X $p Γ}
        (e : A = A') (e' : A' = A'') (e'' : A = A'')
    : pr1 (reind_ext_compare e'') = reind_ext_compare e ;; reind_ext_compare e'.
  Proof.
    refine (_ @ reind_ext_compare_comp _ _).
    apply maponpaths, maponpaths, setproperty.
  Qed.

  Definition F_TY_reind_ext_eq
             (X Y : split_typecat_structure C)
             (mor : SplitTy_mor_data X Y)
             (F_TY_ax : SplitTy_mor_axiom_F_TY mor)
    : ∏ (Γ : C) (A : X Γ) (Γ' : C) (f : Γ' --> Γ),
      pr1 mor _ (A {{f}})
      = (pr1 mor _ A) {{f}}.
  Proof.
    intros Γ Γ' f A.
    apply F_TY_ax.
  Defined.

  Definition F_TY_reind_ext_compare
             (X Y : split_typecat_structure C)
             (mor : SplitTy_mor_data X Y)
             (F_TY_ax : SplitTy_mor_axiom_F_TY mor)
    : ∏ (Γ : C) (A : X Γ) (Γ' : C) (f : Γ' --> Γ),
      z_iso (Γ' ◂ pr1 mor _ (A {{f}}))
          (Γ' ◂ (pr1 mor _ A) {{f}}).
  Proof.
    intros Γ Γ' f A.
    use reind_ext_compare.
    apply F_TY_reind_ext_eq.
    apply F_TY_ax.
  Defined.

  Local Definition Δ := F_TY_reind_ext_compare.

  Lemma Δ_φ {X Y : split_typecat_structure C} (mor : SplitTy_mor_data X Y)
        {Γ : C} {A A' : TY' X $p Γ} (e : A = A')
    : reind_ext_compare e ;; pr2 mor Γ A'
      = pr2 mor _ A ;; reind_ext_compare (maponpaths (pr1 mor _) e).
  Proof.
    destruct e; simpl. etrans. apply id_left. apply pathsinv0, id_right.
  Qed. 

  Definition SplitTy_mor_axiom_q
             {X Y : split_typecat_structure C}
             (mor : SplitTy_mor_data X Y)
             (F_TY_ax : SplitTy_mor_axiom_F_TY mor)
    : UU
    := ∏ (Γ Γ' : C) (f : Γ' --> Γ) (A : X Γ),
       q_typecat A f ;; pr2 mor Γ A
       = pr2 mor Γ' (A {{f}}) ;; Δ _ _ _ F_TY_ax Γ A Γ' f ;; q_typecat _ f.

  Definition SplitTy_mor_axioms
             {X Y : split_typecat_structure C}
             (mor : SplitTy_mor_data X Y)
    : UU
    := ∑ (F_TY_ax : SplitTy_mor_axiom_F_TY mor)
         (dpr_ax : SplitTy_mor_axiom_dpr mor),
       SplitTy_mor_axiom_q mor F_TY_ax.

  Definition isaprop_SplitTy_mor_axioms
             {X Y : split_typecat_structure C}
             (mor : SplitTy_mor_data X Y)
    : isaprop (SplitTy_mor_axioms mor).
  Proof.
    apply Propositions.isaproptotal2.
    - intros ?. apply isapropdirprod.
      + repeat (apply impred_isaprop; intros ?). apply homset_property.
      + repeat (apply impred_isaprop; intros ?). apply homset_property.
    - intros.
      repeat (apply funextsec; intros ?).
      apply (pr1 (pr2 Y)).
  Defined.

  Definition SplitTy_mor
             (X Y : split_typecat_structure C)
    : UU
    := ∑ (mor_data : SplitTy_mor_data X Y),
       SplitTy_mor_axioms mor_data.

  Lemma SplitTy_mor_eq {X Y} (mor1 mor2 : SplitTy_mor X Y)
        (e_TY : ∏ Γ (A : TY' X $p Γ),
                pr1 (pr1 mor1) _ A =
                pr1 (pr1 mor2) _ A)
        (e_ϕ : ∏ Γ (A : TY' X $p Γ),
                  pr2 (pr1 mor1) _ A ;; reind_ext_compare (e_TY _ _)
                  = pr2 (pr1 mor2) _ A)
    : mor1 = mor2.
  Proof.
    use total2_paths_f. 2: apply isaprop_SplitTy_mor_axioms.
    use total2_paths_f.
    + repeat (apply funextsec; intros ?).
      apply e_TY.
    + etrans. use transportf_forall.
      apply funextsec; intros Γ.
      etrans. use transportf_forall.
      apply funextsec; intros A.
      refine (_ @ e_ϕ Γ A).
      etrans. apply (functtransportf
                       (λ x, x Γ A)
                       (λ y, C ⟦ Γ ◂ A, Γ ◂ y ⟧)).
      etrans. apply (functtransportf
                       (λ x, Γ ◂ x)
                       (λ y, C ⟦ Γ ◂ A, y ⟧)).
      etrans. apply pathsinv0, idtoiso_postcompose.
      apply maponpaths.
      unfold reind_ext_compare, ext_typecat.
      apply maponpaths.
      apply maponpaths.
      apply maponpaths.
      apply (pr1 (pr2 Y)).
  Qed.

  Definition SplitTy_mor_id
             (X : split_typecat_structure C)
    : SplitTy_mor X X.
  Proof.
    use tpair.
    - use tpair.
      + intros Γ. exact (idfun _).
      + intros Γ A. apply identity.
    - use tpair. 2: use make_dirprod.
      + intros Γ Γ' f A. apply idpath.
      + intros Γ A. apply id_left.
      + intros Γ Γ' f A. simpl.
        etrans. apply id_right.
        etrans. 2: apply assoc.
        etrans. 2: apply pathsinv0, id_left.
        apply pathsinv0.
        apply id_left.
  Defined.

  Definition SplitTy_mor_comp
             {X Y Z : split_typecat_structure C}
             (ff : SplitTy_mor X Y)
             (gg : SplitTy_mor Y Z)
    : SplitTy_mor X Z.
  Proof.
    use tpair.
    - use tpair.
      + intros Γ A. exact (pr1 (pr1 gg) _ (pr1 (pr1 ff) _ A)).
      + intros Γ A. exact (pr2 (pr1 ff) _ _ ;; pr2 (pr1 gg) _ _).
    - use tpair. 2: use make_dirprod.
      + intros Γ Γ' f A. simpl.
        etrans. apply maponpaths.
        apply (pr1 (pr2 ff)).
        apply (pr1 (pr2 gg)).
      + intros Γ A. simpl.
        etrans. apply assoc'.
        etrans. apply maponpaths.
        apply (pr1 (pr2 (pr2 gg))).
        apply (pr1 (pr2 (pr2 ff))).
      + intros Γ Γ' f A. simpl.
        set (ff_q := pr2 (pr2 (pr2 ff)) Γ Γ' f A).
        set (gg_q := pr2 (pr2 (pr2 gg))).
        etrans. apply assoc.
        etrans. apply maponpaths_2, ff_q.

        etrans. apply assoc'.
        etrans. apply assoc'.
        etrans. 2: apply assoc.
        etrans. 2: apply assoc.
        apply maponpaths.

        etrans. apply maponpaths, gg_q.

        etrans. apply assoc.
        etrans. apply maponpaths_2, assoc.
        etrans. apply maponpaths_2, maponpaths_2.
        apply Δ_φ.

        etrans. apply assoc'.
        etrans. apply assoc'.
        apply maponpaths.

        etrans. apply assoc.
        apply maponpaths_2.
        apply pathsinv0, reind_ext_compare_comp_general.
  Defined.

  Definition SplitTy_ob_mor
    : precategory_ob_mor
    := (split_typecat_structure C ,, SplitTy_mor).

  Definition SplitTy_id_comp
    : precategory_id_comp SplitTy_ob_mor.
  Proof.
    use make_dirprod.
    - apply SplitTy_mor_id.
    - intros X Y Z. apply SplitTy_mor_comp.
  Defined.

  Definition SplitTy_precat_data
    : precategory_data
    := (SplitTy_ob_mor ,, SplitTy_id_comp).

  Definition SplitTy_precat_axioms
    : is_precategory SplitTy_precat_data.
  Proof.
    repeat use make_dirprod.
    - intros X Y f. use SplitTy_mor_eq.
      + intros Γ A. apply idpath.
      + intros Γ A. cbn. etrans. apply maponpaths_2, id_left. apply id_right.
    - intros X Y f. use SplitTy_mor_eq.
      + intros Γ A. apply idpath.
      + intros Γ A. cbn. etrans. apply maponpaths_2, id_right. apply id_right.
    - intros X Y Z W f g h. use SplitTy_mor_eq.
      + intros Γ A. apply idpath.
      + intros Γ A. cbn. etrans. apply maponpaths_2, assoc. apply id_right.
    - intros X Y Z W f g h. use SplitTy_mor_eq.
      + intros Γ A. apply idpath.
      + intros Γ A. cbn. etrans. apply maponpaths_2, assoc'. apply id_right.
  Defined.

  Definition SplitTy_precat : precategory
    := (_ ,, SplitTy_precat_axioms).

  Definition SplitTy_precat_homsets : has_homsets SplitTy_precat.
  Proof.
    unfold has_homsets.
    intros X Y.
    apply isaset_total2. 2: intros ?; apply isasetaprop, isaprop_SplitTy_mor_axioms.
    - apply isaset_total2.
      + repeat (apply impred_isaset; intros ?).
        apply (pr1 (pr2 Y)).
      + intros ?.
        repeat (apply impred_isaset; intros ?).
        apply homset_property.
  Defined.

  Definition SplitTy_cat : category
    := (SplitTy_precat ,, SplitTy_precat_homsets).
  
End SplitTypeCat_Cat_Simple.

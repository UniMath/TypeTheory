(**
    TODO
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheory.

Require Import TypeTheory.CwF_TypeCat.CwF_SplitTypeCat_Defs.
Require Import TypeTheory.TypeCat.TypeCat.
Require Import TypeTheory.CwF_TypeCat.TypeCat_Reassoc.
Require Import TypeTheory.CwF_TypeCat.SplitTypeCat_Cat_Simple.
Require Import TypeTheory.CompCats.DiscCompCatDef_Cat.
Require Import TypeTheory.CompCats.DiscreteComprehensionCat.
Require Import TypeTheory.TypeCat_CompCat.SplitTypeCat_ComprehensionCat.

Section SplitTypeCat_DiscCompCatDef_catiso.

  Context (C : category).

  Definition SplitTy_DiscComp_weq
    : SplitTy_cat C ≃ DiscCompCatDef_cat C
    := split_typecat_structure_discrete_comprehension_cat_structure_default_mor_weq.

  Definition SplitTy_DiscComp_mor_data_weq
             {X Y : SplitTy_cat C}
    : SplitTy_mor_data C X Y ≃
        DiscCompCatDef_mor_data C (SplitTy_DiscComp_weq X) (SplitTy_DiscComp_weq Y).
  Proof.
    apply idweq.
  Defined.
    
  Definition Δ_weq
             {X Y : SplitTy_cat C}
             {F : SplitTy_mor_data C X Y}
             {F_TY_ax : SplitTy_mor_axiom_F_TY C F}
             {Γ Γ' : C} {f : C ⟦ Γ', Γ ⟧} {A : pr1 X Γ}
    : pr1 (SplitTypeCat_Cat_Simple.Δ C X Y F F_TY_ax Γ A Γ' f)
      = Δ C (SplitTy_DiscComp_mor_data_weq F)
    (λ (Γ0 Γ'0 : C) (f0 : C ⟦ Γ'0, Γ0 ⟧) (A0 : pr1 X Γ0),
     F_TY_reind_ext_eq C X Y F F_TY_ax Γ0 A0 Γ'0 f0) Γ Γ' f A.
  Proof.
    unfold SplitTypeCat_Cat_Simple.Δ, Δ.
    unfold F_TY_reind_ext_compare, F_TY_reind_ext_eq, reind_ext_compare, F_ob_compare.
    apply maponpaths.
    apply maponpaths.
    apply pathsinv0.
    apply (maponpathscomp
             (DiscCompCatDef_Cat.F_ob (SplitTy_DiscComp_weq Y) Γ')
             pr1).
  Defined.

  Definition SplitTy_DiscComp_mor_weq
             (X Y : SplitTy_cat C)
    : SplitTy_cat C ⟦ X , Y ⟧ ≃
                  DiscCompCatDef_cat C ⟦ SplitTy_DiscComp_weq X , SplitTy_DiscComp_weq Y ⟧.
  Proof.
    apply (PartA.weqtotal2 (idweq _)); intros F.
    apply (PartA.weqtotal2 (idweq _)); intros F_TY_ax.
    apply (PartA.weqdirprodf (idweq _)).
    apply weqonsecfibers; intros Γ.
    apply weqonsecfibers; intros Γ'.
    apply weqonsecfibers; intros f.
    apply weqonsecfibers; intros A.
    apply MoreEquivalences.weq_pathscomp0r.
    apply maponpaths_2.
    apply maponpaths.
    exact Δ_weq.
  Defined.

  Definition SplitTy_DiscComp_functor_data
    : functor_data (SplitTy_cat C) (DiscCompCatDef_cat C).
  Proof.
    use tpair.
    - exact SplitTy_DiscComp_weq.
    - exact SplitTy_DiscComp_mor_weq.
  Defined.

  Definition SplitTy_DiscComp_functor_axioms
    : is_functor SplitTy_DiscComp_functor_data.
  Proof.
    use make_dirprod.
    - intros X.
      use DiscCompCatDef_mor_eq.
      + intros Γ A. apply idpath.
      + intros Γ A. apply id_right.
    - intros X Y Z f g.
      use DiscCompCatDef_mor_eq.
      + intros Γ A. apply idpath.
      + intros Γ A. apply id_right.
  Defined.

  Definition SplitTy_DiscComp_functor
    : functor (SplitTy_cat C) (DiscCompCatDef_cat C)
    := (_ ,, SplitTy_DiscComp_functor_axioms).

  Definition SplitTy_DiscComp_functor_is_catiso
    : is_catiso SplitTy_DiscComp_functor.
  Proof.
    unfold is_catiso.
    use make_dirprod.
    - intros X Y. apply (pr2 (SplitTy_DiscComp_mor_weq X Y)).
    - apply (pr2 SplitTy_DiscComp_weq).
  Defined.
  
End SplitTypeCat_DiscCompCatDef_catiso.

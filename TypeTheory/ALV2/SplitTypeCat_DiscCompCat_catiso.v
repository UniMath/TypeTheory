(**
    TODO
*)

Require Import UniMath.Foundations.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.

Require Import TypeTheory.Auxiliary.Auxiliary.

Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Defs.
Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.ALV1.TypeCat_Reassoc.
Require Import TypeTheory.ALV2.SplitTypeCat_Cat_Simple.
Require Import TypeTheory.ALV2.DiscCompCat_Cat.
Require Import TypeTheory.ALV2.DiscreteComprehensionCat.
Require Import TypeTheory.ALV2.SplitTypeCat_ComprehensionCat.

Section SplitTypeCat_DiscCompCat_catiso.

  Context (C : category).

  Definition SplitTy_DiscComp_weq
    : SplitTy_cat C ≃ DiscCompCat_cat C
    := split_typecat_structure_discrete_comprehension_cat_structure_weq.

  Definition SplitTy_DiscComp_Ty_eq
             (X : SplitTy_cat C)
    : TY' _ (X : split_typecat_structure C)
      = preshv_from_disc_comp_cat_structure _
          (SplitTy_DiscComp_weq X : discrete_comprehension_cat_structure C).
  Proof.
    use total2_paths_f.
    - apply idpath.
    - apply isaprop_is_functor. apply homset_property.
  Defined.

  Definition SplitTy_DiscComp_functor_data
    : functor_data (SplitTy_cat C) (DiscCompCat_cat C).
  Proof.
    use tpair.
    - apply SplitTy_DiscComp_weq.
    - intros X Y. apply idweq.
  Defined.

  Definition SplitTy_DiscComp_functor_axioms
    : is_functor SplitTy_DiscComp_functor_data.
  Proof.
    use make_dirprod.
    - intros X. apply idpath.
    - intros X Y Z f g. apply idpath.
  Defined.

  Definition SplitTy_DiscComp_functor
    : functor (SplitTy_cat C) (DiscCompCat_cat C)
    := (_ ,, SplitTy_DiscComp_functor_axioms).

  Definition SplitTy_DiscComp_functor_is_catiso
    : is_catiso SplitTy_DiscComp_functor.
  Proof.
    unfold is_catiso.
    use make_dirprod.
    - intros X Y. apply (pr2 (idweq _)).
    - apply (pr2 SplitTy_DiscComp_weq).
  Defined.
  
End SplitTypeCat_DiscCompCat_catiso.

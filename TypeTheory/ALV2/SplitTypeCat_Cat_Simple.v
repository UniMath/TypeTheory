(**
    TODO
*)

Require Import UniMath.Foundations.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Defs.
Require Import TypeTheory.ALV1.TypeCat.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.

Section SplitTypeCat_Cat_Simple.

  Context (C : category).

  Definition SplitTy_ob_mor
    : precategory_ob_mor.
  Proof.
    use tpair.
    - apply (split_typecat'_structure C).
    - intros X Y. exact (TY X --> TY Y).
  Defined.

  Print precategory_data .

  Definition SplitTy_id_comp
    : precategory_id_comp SplitTy_ob_mor.
  Proof.
    use make_dirprod.
    - intros X. apply identity.
    - intros X Y Z. apply compose.
  Defined.

  Definition SplitTy_precat_data
    : precategory_data
    := (SplitTy_ob_mor ,, SplitTy_id_comp).

  Definition SplitTy_precat_axioms
    : is_precategory SplitTy_precat_data.
  Proof.
    repeat use make_dirprod.
    - intros; apply id_left.
    - intros; apply id_right.
    - intros; apply assoc.
    - intros; apply assoc'.
  Defined.

  Definition SplitTy_precat : precategory
    := (_ ,, SplitTy_precat_axioms).

  Definition SplitTy_precat_homsets : has_homsets SplitTy_precat.
  Proof.
    unfold has_homsets.
    intros. apply homset_property.
  Defined.

  Definition SplitTy_cat : category
    := (SplitTy_precat ,, SplitTy_precat_homsets).
  
End SplitTypeCat_Cat_Simple.

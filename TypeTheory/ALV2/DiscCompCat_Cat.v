(**
    TODO
*)

Require Import UniMath.Foundations.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Defs.
Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.ALV2.DiscreteComprehensionCat.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Section DiscCompCat_Cat_Simple.

  Context (C : category).

  Definition preshv_from_disc_comp_cat_structure
             (DCC : discrete_comprehension_cat_structure C)
    : preShv C.
  Proof.
    apply preshv_from_disc_fib_ob.
    exists (pr1 DCC).
    exact (pr1 (pr2 DCC)).
  Defined.

  Local Definition TY := preshv_from_disc_comp_cat_structure.

  Definition DiscCompCat_ob_mor
    : precategory_ob_mor.
  Proof.
    use tpair.
    - apply (discrete_comprehension_cat_structure C).
    - intros X Y. exact (TY X --> TY Y).
  Defined.

  Definition DiscCompCat_id_comp
    : precategory_id_comp DiscCompCat_ob_mor.
  Proof.
    use make_dirprod.
    - intros X. apply identity.
    - intros X Y Z. apply compose.
  Defined.

  Definition DiscCompCat_precat_data
    : precategory_data
    := (DiscCompCat_ob_mor ,, DiscCompCat_id_comp).

  Definition DiscCompCat_precat_axioms
    : is_precategory DiscCompCat_precat_data.
  Proof.
    repeat use make_dirprod.
    - intros; apply id_left.
    - intros; apply id_right.
    - intros; apply assoc.
    - intros; apply assoc'.
  Defined.

  Definition DiscCompCat_precat : precategory
    := (_ ,, DiscCompCat_precat_axioms).

  Definition DiscCompCat_precat_homsets : has_homsets DiscCompCat_precat.
  Proof.
    unfold has_homsets.
    intros. apply homset_property.
  Defined.

  Definition DiscCompCat_cat : category
    := (DiscCompCat_precat ,, DiscCompCat_precat_homsets).
  
End DiscCompCat_Cat_Simple.

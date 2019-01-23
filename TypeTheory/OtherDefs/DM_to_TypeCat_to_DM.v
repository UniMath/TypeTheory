(** 
 
 Ahrens, Lumsdaine, Voevodsky, 2015

 Contents:

  - Definition of a Category with Display maps from a Comprehension Category
      (assumption of saturatedness needed for pullbacks forming hprop)
*)

Require Import UniMath.Foundations.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.total2_paths.

Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.OtherDefs.DM.
Require Import TypeTheory.OtherDefs.DM_to_TypeCat.
Require Import TypeTheory.OtherDefs.TypeCat_to_DM.

(** * Construction of Comprehension precategory from Display map precategory *)

Section TypeCat_to_DM.

Variable CC : precategory.
Variable H : is_univalent CC.  
Variable C : DM_structure CC.

Lemma DM_to_TypeCat_to_DM : DM_structure_of_TypeCat _ H (type_cat_struct_from_DM _ (pr2 H)  C) = C.
Proof.
  apply DM_equal.
  - assumption.
  - intros. unfold DM_structure_of_TypeCat in X.
    simpl in *.
    unfold DM_type in X. simpl in *.
    unfold dm_sub_struct_of_TypeCat in X; simpl in X.
    unfold type_cat_struct_from_DM in X. simpl in *.
    set (X' := hProppair (DM_type C f) (pr2 (pr2 C) _ _ _ )).
    apply (X X'). unfold X'; clear X' X.
    intro T. simpl in *.
    unfold iso_to_dpr in T. simpl.
    destruct T as [t p].
    destruct t.
    simpl in *.
Abort.
    
End TypeCat_to_DM.

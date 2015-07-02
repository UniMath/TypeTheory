
(** 
  
 Ahrens, Lumsdaine, Voevodsky, 2015

Contents:

  - Construction of a Comprehension precategory from a precategory with Families
  - Proof that the constructed TypeCat is split

*)


Require Import UniMath.RezkCompletion.total2_paths.

Require Import Systems.Auxiliary.
Require Import Systems.UnicodeNotations.
Require Import Systems.TypeCat.
Require Import Systems.CwF.
Require Import Systems.TypeCat.
Require Import Systems.DM.
Require Import Systems.CwF_to_TypeCat.
Require Import Systems.CwF_to_DM.
Require Import Systems.TypeCat_to_DM.

Require Import UniMath.RezkCompletion.limits.pullbacks.

Section compare_maps.

  Context (CC : precategory) (C : cwf_struct CC) (H : is_category CC).

  Lemma maps_equal : DM_structure_of_TypeCat _ H (comp_cat_of_precwf _ C (pr2 H)) = DM_structure_of_CwF _ C H.
  Proof.
    apply DM_equal.
    - exact H.
    - simpl. intros.
      unfold DM_type in *.
      unfold dm_sub_struct_of_TypeCat in *.
      unfold dm_sub_struct_of_CwF.
      apply X.
    - intros. apply X.
  Defined.
      
End compare_maps.


(** 
  
 Ahrens, Lumsdaine, Voevodsky, 2015

Contents:

  - Commutativity of the constructions between CwFs, type-(pre)cats, and DM-cats

*)


Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.limits.pullbacks.

Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.OtherDefs.CwF_Pitts.
Require Import TypeTheory.OtherDefs.DM.
Require Import TypeTheory.OtherDefs.CwF_Pitts_to_TypeCat.
Require Import TypeTheory.OtherDefs.CwF_Pitts_to_DM.
Require Import TypeTheory.OtherDefs.TypeCat_to_DM.


Section compare_maps.

  Context (CC : precategory) (C : cwf_struct CC) (H : is_univalent CC).

  Lemma maps_equal : DM_structure_of_TypeCat _ H (type_cat_of_precwf _ C (pr2 H)) = DM_structure_of_CwF _ C H.
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



(*
Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.CategoryTheory.UnicodeNotations.

*)

Require Import UniMath.CategoryTheory.equivalences.

Require Import Systems.Auxiliary.
Require Import Systems.UnicodeNotations.
Require Import Systems.Displayed_Cats.Auxiliary.
Require Import Systems.Displayed_Cats.Core.

Require Import Systems.Displayed_Cats.Constructions.
Require Import Systems.Displayed_Cats.Equivalences.
Require Import Systems.Structures.
Require Import Systems.CwF_SplitTypeCat_Maps.

Require Import Systems.Structures_Cats.
Require Import Systems.Structures_Univalent_Cats.
Require Import Systems.Structures_Equiv_Cats.

Section Structures_Equiv_Cats.

Context (C : Precategory) (X : obj_ext_Precat C).
(* TODO: remove [has_homsets] arguments from [adj_equiv_of_cats_is_weq_of_objects]. *)

Definition fam_struc_to_qq_struc_equiv_types
  : (fibre_precategory (families_disp_precat C) X)
   ≃ (fibre_precategory (qq_structure_disp_precat C) X).
Proof.
  eapply weq_on_objects_from_adj_equiv_of_cats.
  - apply is_category_fibre.
    apply is_category_families_structure.
  - apply fam_struc_to_qq_struc_is_equiv.
  Unshelve.
  apply is_category_fibre, is_category_qq_morphism.
Defined.

Print Assumptions fam_struc_to_qq_struc_equiv_types.

End Structures_Equiv_Cats.


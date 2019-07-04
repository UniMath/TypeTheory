
(** * Displayed Category from a category with display maps

Definition of the displayed category of display maps over a category [C]

Given a category with display maps [C], we define a displayed 
category over [C]. Objects over [c:C] are display maps into [c].

*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.limits.pullbacks.

Require Import TypeTheory.Auxiliary.Auxiliary.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.ComprehensionC.
Require Import TypeTheory.Displayed_Cats.DisplayedCatFromCwDM.
Require Import TypeTheory.OtherDefs.DM.

Local Set Automatic Introduction.

Section Comp_Cat_of_DM_Structure.

Context {C : category}.

(* TODO: change name [dm_sub_pb] to something more comprehensible, e.g. [dm_struct]. *)
Variable (H : dm_sub_pb C).

Definition comprehension_of_dm_structure_data
  : disp_functor_data (functor_identity C) (DM_disp H) (disp_codomain C).
Proof.
  use tpair.
  + intros x d. cbn in *.
    exact (pr1 d).
  + cbn. intros x y xx yy f ff. 
    exact ff.
Defined.

Definition comprehension_of_dm_structure_axioms
  : disp_functor_axioms comprehension_of_dm_structure_data.
Proof.
  cbn; repeat split; cbn.
  + intros.
    apply subtypePath.
    { intro. apply homset_property. }
    apply idpath.
  + intros.
    apply subtypePath.
    { intro. apply homset_property. }
    apply idpath.
Qed.

Definition comprehension_of_dm_structure
  : disp_functor _ _ _ := _ ,, comprehension_of_dm_structure_axioms.

Lemma is_cartesian_comprehension_of_dm_structure
  : is_cartesian_disp_functor comprehension_of_dm_structure.
Proof.
  use cartesian_functor_from_cleaving.
  - apply is_fibration_DM_disp.
  - intros c c' f d. 
    apply isPullback_cartesian_in_cod_disp.
    apply isPullback_of_dm_sub_pb, homset_property.
Qed.

Definition total_comprehension_of_dm_structure
  : functor _ _ := total_functor comprehension_of_dm_structure.


(** This commutativity is an instance of a general lemma about comprehension categories
    once we have produced [comp_cat_of_dm] below
*)
Lemma comprehension_of_dm_structure_triangle_commutes 
: functor_composite total_comprehension_of_dm_structure (pr1_category _)
  = pr1_category _ . 
Proof. 
  apply functor_eq. 
  - apply homset_property.
  - apply idpath.
Qed.

Definition comp_cat_of_dm :  comprehension_cat_structure C.
Proof.
  use tpair.
  - apply DM_disp. apply H.
  - use tpair. 
    + apply is_fibration_DM_disp.
    + use tpair. 
      * apply comprehension_of_dm_structure.
      * apply is_cartesian_comprehension_of_dm_structure.
Defined.

End Comp_Cat_of_DM_Structure.




(**
  [TypeTheory.ALV2.Comprehension_Cats]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**
TODO
*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.TypeCat.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.ComprehensionC.

Set Automatic Introduction.

Locate "exists!".

Section TypeCat_to_ComprehensionCat.

  Context (C : category).

  Context (TC : typecat_structure C).

  Definition typecat_disp_ob_mor : disp_cat_ob_mor C.
  Proof.
    use tpair.
    - apply TC.
    - intros Γ' Γ A' A f.
      exact (∑ ff : Γ' ◂ A' --> Γ ◂ A,
                    ff ;; dpr_typecat A = dpr_typecat A' ;; f).
  Defined.
  
  Definition typecat_disp_id_comp : disp_cat_id_comp _ typecat_disp_ob_mor.
    split.
    + intros Γ A; cbn in *.
      use tpair.
      * apply identity.
      * etrans. apply id_left. apply pathsinv0, id_right.
    + intros ? ? ? ? ? ? ? ? ff gg; cbn in *.
      use tpair.
      * apply (pr1 ff ;; pr1 gg).
      * simpl.
        etrans. apply assoc'.
        etrans. apply maponpaths, (pr2 gg).
        etrans. apply assoc.
        etrans. apply maponpaths_2, (pr2 ff).
        apply assoc'.
  Defined.

  Definition typecat_disp_data : disp_cat_data C
    := (typecat_disp_ob_mor,, typecat_disp_id_comp).
  
  Definition typecat_disp_axioms : disp_cat_axioms _ typecat_disp_data.
  Proof.
    repeat apply tpair; intros; try apply homset_property.
    - (* id_left_disp *) 
      apply subtypePath.
      { intro. apply homset_property. }
      etrans. apply id_left.
      apply pathsinv0.
      etrans. refine (pr1_transportf (C⟦_,_⟧) _ _ _ _ _ _ ).
      use transportf_const.
    - (* id_right_disp *) 
      apply subtypePath.
      { intro. apply homset_property. }
      etrans. apply id_right.
      apply pathsinv0.
      etrans. refine (pr1_transportf (C⟦_,_⟧) _ _ _ _ _ _ ).
      use transportf_const.
    - (* assoc_disp *) 
      apply subtypePath.
      { intro. apply homset_property. }
      etrans. apply assoc.
      apply pathsinv0.
      etrans. unfold mor_disp.
      refine (pr1_transportf (C⟦_,_⟧) _ _ _ _ _ _ ).
      use transportf_const.
    - (* homsets_disp *)
      apply (isofhleveltotal2 2).
      + apply homset_property.
      + intro. apply isasetaprop. apply homset_property.
  Defined.

  Definition typecat_disp : disp_cat C
    := (typecat_disp_data ,, typecat_disp_axioms).

End TypeCat_to_ComprehensionCat.

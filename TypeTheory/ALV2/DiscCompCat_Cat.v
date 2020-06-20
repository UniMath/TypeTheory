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

Section Auxiliary.

  Definition disp_functor_composite_assoc 
             {C : category}
             (X Y Z W : disp_cat C)
             (F : disp_functor (functor_identity C) X Y)
             (G : disp_functor (functor_identity C) Y Z)
             (H : disp_functor (functor_identity C) Z W)
    : disp_nat_trans (nat_trans_id (functor_identity _))
        (disp_functor_composite (disp_functor_composite F G) H)
        (disp_functor_composite F (disp_functor_composite G H)).
  Proof.
    apply disp_nat_trans_id.
  Defined.

  Definition disp_nat_trans_right
             {C : category}
             {X Y Z : disp_cat C}
             (F : disp_functor (functor_identity C) X Y)
             {G : disp_functor (functor_identity C) Y Z}
             {H : disp_functor (functor_identity C) Y Z}
             (α : disp_nat_trans (nat_trans_id _) G H)
    : disp_nat_trans (nat_trans_id _)
        (disp_functor_composite F G)
        (disp_functor_composite F H).
  Proof.
    use tpair.
    - intros Γ A. apply α.
    - intros Γ Γ' f A A' ff. cbn.
      apply (pr2 α Γ Γ' f (F _ A) (F _ A') (disp_functor_on_morphisms F ff)).
  Defined.

  Lemma nat_trans_id_id
        {C : category}
    : (nat_trans_comp _ _ _
                      (nat_trans_id (functor_identity C))
                      (nat_trans_id (functor_identity C)))
      = nat_trans_id (functor_identity C).
  Proof.
    use total2_paths_f.
    - repeat (apply funextsec; intros ?). cbn.
      apply id_left.
    - repeat (apply funextsec; intros ?). apply homset_property.
  Defined.

  Definition disp_nat_trans_comp_over_id
             {C : category}
             {D D' : disp_cat C}
             {R'' : disp_functor_data (functor_identity _) D' D}
             {R' : disp_functor_data (functor_identity _) D' D}
             {R : disp_functor_data (functor_identity _) D' D}
             (b' : disp_nat_trans (nat_trans_id _) R'' R')
             (b : disp_nat_trans (nat_trans_id _) R' R)
    : disp_nat_trans (nat_trans_id _) R'' R.
  Proof.
    apply (transportf (λ (a : nat_trans _ _), disp_nat_trans a R'' R)
                      nat_trans_id_id
                      (disp_nat_trans_comp b' b)
          ).
  Defined.

End Auxiliary.

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

  Search disp_nat_trans.
  Search nat_trans.
  
  Definition DiscCompCat_mor
             (X Y : discrete_comprehension_cat_structure C)
    : UU
    := ∑ (F_TY : disp_functor (functor_identity _) (pr1 X) (pr1 Y)),
       disp_nat_trans (nat_trans_id (functor_identity C)) (pr1 (pr2 (pr2 X)))
                      (disp_functor_composite F_TY (pr1 (pr2 (pr2 Y)))).

  Definition DiscCompCat_ob_mor
    : precategory_ob_mor
    := (discrete_comprehension_cat_structure C ,, DiscCompCat_mor).

  Definition DiscCompCat_id_comp
    : precategory_id_comp DiscCompCat_ob_mor.
  Proof.
    use make_dirprod.
    - intros X.
      exists (disp_functor_identity _).
      apply disp_nat_trans_id.
    - intros X Y Z F G.
      exists (disp_functor_composite (pr1 F) (pr1 G)).
      apply (disp_nat_trans_comp_over_id (pr2 F) (disp_nat_trans_right (pr1 F) (pr2 G))).
  Defined.

  Definition DiscCompCat_precat_data
    : precategory_data
    := (DiscCompCat_ob_mor ,, DiscCompCat_id_comp).

  Definition DiscCompCat_precat_axioms
    : is_precategory DiscCompCat_precat_data.
  Proof.
    repeat use make_dirprod.
    - intros. use total2_paths_f.
      + use total2_paths_f.
        * apply idpath.
        * apply isaprop_disp_functor_axioms.
      + use total2_paths_f.
        * repeat (apply funextsec; intros ?).
          etrans. apply (pr1_transportf
                           _ _
                           (λ x xx, _)
                         ).
          cbn. left.
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

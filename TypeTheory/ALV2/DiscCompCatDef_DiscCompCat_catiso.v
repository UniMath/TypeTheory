(**
    TODO
*)

Require Import UniMath.Foundations.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.

Require Import TypeTheory.Auxiliary.Auxiliary.

Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Defs.
Require Import TypeTheory.ALV2.DiscCompCat_Cat.
Require Import TypeTheory.ALV2.DiscCompCatDef_Cat.
Require Import TypeTheory.ALV2.DiscreteComprehensionCat.

Section SplitTypeCat_DiscCompCat_catiso.

  Context (C : category).

  Definition DiscCompCat_DiscCompCatDef_weq
    : DiscCompCat_cat C ≃ DiscCompCatDef_cat C
    := discrete_comprehension_cat_structure_with_default_mor_weq1.

  Definition DiscCompCat_DiscCompCatDef_mor_weq
             (X Y : DiscCompCat_cat C)
    : DiscCompCat_cat C ⟦ X, Y ⟧
        ≃ DiscCompCatDef_cat C ⟦ DiscCompCat_DiscCompCatDef_weq X
                               , DiscCompCat_DiscCompCatDef_weq Y ⟧.
  Proof.
    apply (PartA.weqtotal2 (idweq _)); intros F_TY.
    apply (PartA.weqtotal2 (idweq _)); intros F_TY_ax.
    apply (PartA.weqtotal2 (idweq _)); intros ϕ_dpr_ax.
    apply weqonsecfibers; intros Γ.
    apply weqonsecfibers; intros Γ'.
    apply weqonsecfibers; intros f.
    apply weqonsecfibers; intros A.
    use weq_iso.
    - intros p.
      etrans.
      apply (p (DiscCompCatDef_Cat.D_lift_ob (DiscCompCat_DiscCompCatDef_weq X) _ _ f A)
               (invweq (mor_with_unique_lift_mor_weq _ _ _ (pr1 (pr2 (pr2 (pr2 (pr2 X)))))) (idpath _))
            ).
      set (uf := pr2 (pr2 (pr2 mor) Γ Γ' f A)).
      set (p := uf (A' ,, ff) : (A' ,, ff) = _).
    - intros p A' ff.
      etrans.
      set (mor := pr1 (pr2 (pr2 (pr2 (pr2 (DiscCompCat_DiscCompCatDef_weq X)))))).
      set (uf := pr2 (pr2 (pr2 mor) Γ Γ' f A)).
      set (p := uf (A' ,, ff) : (A' ,, ff) = _).
      apply p.
  Defined.

  Definition DiscCompCat_DiscCompCatDef_functor_data
    : functor_data (DiscCompCatDef_cat C) (DiscCompCat_cat C).
  Proof.
    use tpair.
    - apply DiscCompCat_DiscCompCatDef_weq.
    - intros X Y. apply idweq.
  Defined.

  Definition DiscCompCat_DiscCompCatDef_functor_axioms
    : is_functor DiscCompCat_DiscCompCatDef_functor_data.
  Proof.
    use make_dirprod.
    - intros X. apply idpath.
    - intros X Y Z f g. apply idpath.
  Defined.

  Definition DiscCompCat_DiscCompCatDef_functor
    : functor (DiscCompCatDef_cat C) (DiscCompCat_cat C)
    := (_ ,, DiscCompCat_DiscCompCatDef_functor_axioms).

  Definition DiscCompCat_DiscCompCatDef_functor_is_catiso
    : is_catiso DiscCompCat_DiscCompCatDef_functor.
  Proof.
    unfold is_catiso.
    use make_dirprod.
    - intros X Y. apply (pr2 (idweq _)).
    - apply (pr2 DiscCompCat_DiscCompCatDef_weq).
  Defined.
  
End SplitTypeCat_DiscCompCat_catiso.

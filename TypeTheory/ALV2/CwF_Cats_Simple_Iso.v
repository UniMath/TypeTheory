(**
  [TypeTheory.ALV2.CwF_Cats_Simple_Iso]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**
This module establishes an isomorphism of categories of
CwF structures with slightly different definition of morphisms.
Specifically, [CwF_Cats_Simple.weq_cwf_structure_mor_with_ϕ] is
at the core of this isomorpshim.

Main definitions here are

- [cwf_to_cwfS_functor] and [cwf_to_cwfS_is_catiso] — isomorphism of "regular" and "simple" categories of CwF structure.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.CwF_def.
Require Import TypeTheory.ALV2.CwF_Cats.
Require TypeTheory.ALV2.CwF_Cats_Simple.
Require Import UniMath.CategoryTheory.catiso.


Section CwF_Cats_Simple_Iso.

  Context (C : category).

  Section mor.
    
    Context (X Y : cwf_structure C).

    Definition cwf_to_cwfS_structure_mor_with_ϕ
      : cwf_structure_mor X Y → CwF_Cats_Simple.cwf_structure_mor_with_ϕ X Y.
    Proof.
      intros mor.
      set (F_TM := pr11 mor).
      set (F_TY := pr121 mor).
      set (ϕ := pr221 mor).
      set (ax1 := pr12 mor).
      set (ax2 := pr122 mor).
      set (ax3 := pr222 mor).
      exact (((F_TM ,, F_TY) ,, ax2) ,, (ϕ ,, ax1 ,, ax3)).
    Defined.

    Definition cwfS_to_cwf_structure_mor_with_ϕ
      : CwF_Cats_Simple.cwf_structure_mor_with_ϕ X Y → cwf_structure_mor X Y.
    Proof.
      intros morS_with_ϕ.
      set (F_TM := pr111 morS_with_ϕ).
      set (F_TY := pr211 morS_with_ϕ).
      set (ax2 := pr21 morS_with_ϕ).
      set (ϕ := pr12 morS_with_ϕ).
      set (ax1 := pr122 morS_with_ϕ).
      set (ax3 := pr222 morS_with_ϕ).
      exact ((F_TM ,, F_TY ,, ϕ) ,, (ax1 ,, ax2 ,, ax3)).
    Defined.

    Definition isweq_cwf_to_cwfS_structure_mor_with_ϕ
      : isweq cwf_to_cwfS_structure_mor_with_ϕ.
    Proof.
      apply (isweq_iso cwf_to_cwfS_structure_mor_with_ϕ
                       cwfS_to_cwf_structure_mor_with_ϕ).
      - intros mor.
        use cwf_structure_mor_eq.
        + intros Γ A. apply idpath.
        + intros Γ A. apply idpath.
        + intros Γ A. apply id_right.
      - intros morS_with_ϕ.
        use CwF_Cats_Simple.cwf_structure_mor_with_ϕ_eq.
        + apply idpath.
        + apply idpath.
    Defined.

    Definition weq_cwf_cwfS_structure_mor_with_ϕ
      : cwf_structure_mor X Y ≃ CwF_Cats_Simple.cwf_structure_mor_with_ϕ X Y
      := (_ ,, isweq_cwf_to_cwfS_structure_mor_with_ϕ).

    Definition weq_cwf_cwfS_structure_mor
      : cwf_structure_mor X Y ≃ CwF_Cats_Simple.cwf_structure_mor X Y.
    Proof.
      eapply weqcomp.
      apply weq_cwf_cwfS_structure_mor_with_ϕ.
      apply CwF_Cats_Simple.weq_cwf_structure_mor_with_ϕ.
    Defined.

  End mor.

  (* CwF to CwF (simple) functor *)

  Definition cwf_to_cwfS_functor_data
    : functor_data (@cwf_structure_cat C)
                   (@CwF_Cats_Simple.cwf_structure_cat C).
  Proof.
    use make_functor_data.
    - apply idweq.
    - apply weq_cwf_cwfS_structure_mor.
  Defined.

  Definition cwf_to_cwfS_functor_idax
    : functor_idax cwf_to_cwfS_functor_data.
  Proof.
    intros c. 
    use total2_paths_f.
    + apply idpath.
    + apply homset_property.
  Defined.

  Definition cwf_to_cwfS_functor_compax
    : functor_compax cwf_to_cwfS_functor_data.
  Proof.
    intros a b c.
    intros f g.

    use total2_paths_f.
    + apply idpath.
    + apply homset_property.
  Defined.

  Definition cwf_to_cwfS_is_functor
    : is_functor cwf_to_cwfS_functor_data
    := (cwf_to_cwfS_functor_idax ,, cwf_to_cwfS_functor_compax).
  
  Definition cwf_to_cwfS_functor
    : functor (@cwf_structure_precategory_data C)
              (@CwF_Cats_Simple.cwf_structure_precategory_data C).
  Proof.
    use (make_functor cwf_to_cwfS_functor_data).
    apply cwf_to_cwfS_is_functor.
  Defined.

  Definition cwf_to_cwfS_is_catiso : is_catiso cwf_to_cwfS_functor.
  Proof.
    use tpair.
    - unfold fully_faithful.
      intros X Y.
      apply (pr2 (weq_cwf_cwfS_structure_mor _ _)).
    - apply (pr2 (idweq _)).
  Defined.

End CwF_Cats_Simple_Iso.

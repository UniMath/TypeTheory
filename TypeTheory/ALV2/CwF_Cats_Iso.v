(**
  [TypeTheory.ALV1.CwF_Cats]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**
This module defines an isomorphism of categories for slightly
different definitions of CwF structures.
Since the difference is merely how components of objects and morphisms
are "packed" the proof boils down to a simple repackaging.

See [weq_cwf'_cwf_structure] for the "repackaging" of objects
and [weq_cwf'_to_cwf_structure_mor] for morphisms.

Main definitions are

- [cwf'_to_cwf_functor], [cwf'_to_cwf_is_catiso] — isomorphism of categories of [cwf_structure] and [cwf'_structure] (composed of [obj_ext_structure] and [term_fun_structure])
*)


Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.CwF_def.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Defs.
(* Require Import TypeTheory.ALV1.CwF_Defs_Equiv. *)

Require Import TypeTheory.ALV2.CwF_Cats.
Require Import TypeTheory.ALV2.CwF_SplitTypeCat_Cats.
Require Import UniMath.CategoryTheory.catiso.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Equivalences.


Section CwF_Cat_Equiv.

  Context (C : category).

  Definition cwf_to_cwf'_structure : cwf_structure C → cwf'_structure C.
  Proof.
    intros [[[Ty Tm] p] ΓAπ_te_axiom_isPullback].
    set (ΓAπ      := λ Γ A, pr1 (ΓAπ_te_axiom_isPullback Γ A)).
    set (te       := λ Γ A, pr1 (pr1 (pr2 (ΓAπ_te_axiom_isPullback Γ A)))).
    set (te_axiom := λ Γ A, pr2 (pr1 (pr2 (ΓAπ_te_axiom_isPullback Γ A)))).
    set (pullback := λ Γ A, pr2 (pr2 (ΓAπ_te_axiom_isPullback Γ A))).
    set (axioms   := λ Γ A, (te_axiom Γ A, pullback Γ A)).
    exact ((Ty ,, ΓAπ) ,, ((Tm ,, p ,, te) ,, axioms)).
  Defined.
  
  Definition cwf'_to_cwf_structure : cwf'_structure C → cwf_structure C.
  Proof.
    intros [[Ty ΓAπ] [[Tm [p te]] axioms]].
    set (te_axiom := λ Γ A, pr1 (axioms Γ A)).
    set (pullback := λ Γ A, pr2 (axioms Γ A)).
  
    set (pp := ((Ty ,, Tm) ,, p) : mor_total (preShv C)).
    set (r := (λ Γ A,
               (ΓAπ Γ A ,, (te Γ A ,, te_axiom Γ A) ,, pullback Γ A))
              : cwf_representation pp).
    exact (pp ,, r).
  Defined.
  
  Definition isweq_cwf'_to_cwf_structure : isweq cwf'_to_cwf_structure.
  Proof.
    apply (isweq_iso cwf'_to_cwf_structure cwf_to_cwf'_structure).
    - intros x. apply idpath.
    - intros x. apply idpath.
  Defined.
  
  Definition weq_cwf'_cwf_structure
    : cwf'_structure C ≃ cwf_structure C.
  Proof.
    use tpair.
    - apply cwf'_to_cwf_structure.
    - apply isweq_cwf'_to_cwf_structure.
  Defined.

  (* Morphisms of CwF' structures *)
  Definition cwf'_structure_mor (X Y : cwf'_structure C) : UU
    := ∑ (ext : obj_ext_mor (pr1 X) (pr1 Y)),
       term_fun_mor X Y ext.

  Section mor.
    
    Context (X' Y' : cwf'_structure C).

    Local Definition X := cwf'_to_cwf_structure X'.
    Local Definition Y := cwf'_to_cwf_structure Y'.

    Definition cwf'_to_cwf_structure_mor
      : cwf'_structure_mor X' Y' → cwf_structure_mor X Y.
    Proof.
      intros [[F_TY p_ax1] [F_TM [ax2 ax3]]].
      set (p   := λ Γ A, pr1 (p_ax1 Γ A)).
      set (ax1 := λ Γ A, pr2 (p_ax1 Γ A)).
      exact ((F_TM ,, F_TY ,, p) ,, (ax1 ,, ax2 ,, ax3)).
    Defined.

    Definition cwf_to_cwf'_structure_mor
      : cwf_structure_mor X Y → cwf'_structure_mor X' Y'.
    Proof.
      intros [[F_TM [F_TY p]] [ax1 [ax2 ax3]]].
      set (ext := (F_TY ,, λ Γ A, (p Γ A ,, ax1 Γ A))
                  : obj_ext_mor (pr1 X') (pr1 Y')).
      set (tfm := (F_TM ,, ax2 ,, ax3) : term_fun_mor X' Y' ext).
      exact (ext ,, tfm).
    Defined.

    Definition isweq_cwf'_to_cwf_structure_mor : isweq cwf'_to_cwf_structure_mor.
    Proof.
      apply (isweq_iso cwf'_to_cwf_structure_mor
                       cwf_to_cwf'_structure_mor).
      - intros x. apply idpath.
      - intros x. apply idpath.
    Defined.

    Definition weq_cwf'_to_cwf_structure_mor
        : cwf'_structure_mor X' Y' ≃ cwf_structure_mor X Y.
    Proof.
      use tpair.
      - apply cwf'_to_cwf_structure_mor.
      - apply isweq_cwf'_to_cwf_structure_mor.
    Defined.

  End mor.

  (* CwF' to CwF functor *)

  Definition cwf'_to_cwf_functor_data
    : functor_data (term_fun_structure_precat C) (@cwf_structure_cat C).
  Proof.
    use make_functor_data.
    - apply cwf'_to_cwf_structure.
    - apply cwf'_to_cwf_structure_mor.
  Defined.

  Definition cwf'_to_cwf_functor_idax
    : functor_idax cwf'_to_cwf_functor_data.
  Proof.
    intros c. 
    use total2_paths_f.
    + apply idpath.
    + use total2_paths_f.
      * apply idpath.
      * use total2_paths_f.
        -- apply idpath.                 
        -- apply impred_isaprop. intros Γ.
           apply impred_isaprop. intros A.
           apply setproperty.
  Defined.

  Definition cwf'_to_cwf_functor_compax
    : functor_compax cwf'_to_cwf_functor_data.
  Proof.
    intros a b c.
    intros f g.

    use total2_paths_f.
    + apply idpath.
    + apply dirprod_paths.
      - apply impred_isaprop. intros Γ.
        apply impred_isaprop. intros A.
        apply homset_property.
      - apply dirprod_paths.
        * apply homset_property.
        * apply impred_isaprop. intros Γ.
          apply impred_isaprop. intros A.
          apply setproperty.
  Defined.

  Definition cwf'_to_cwf_is_functor
    : is_functor cwf'_to_cwf_functor_data
    := (cwf'_to_cwf_functor_idax ,, cwf'_to_cwf_functor_compax).
  
  Definition cwf'_to_cwf_functor
    : functor (term_fun_structure_precat C)
              (@cwf_structure_precategory_data C).
  Proof.
    use (make_functor cwf'_to_cwf_functor_data).
    apply cwf'_to_cwf_is_functor.
  Defined.

  Definition cwf'_to_cwf_is_catiso : is_catiso cwf'_to_cwf_functor.
  Proof.
    use tpair.
    - unfold fully_faithful.
      intros X Y.
      apply isweq_cwf'_to_cwf_structure_mor.
    - apply isweq_cwf'_to_cwf_structure.
  Defined.

End CwF_Cat_Equiv.

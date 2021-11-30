(**
  [TypeTheory.ALV2.CwF_Cats_Simple]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**
This module defines a category of CwF structures.
Objects come from [cwf_structure].

Morphisms are defined simply as a pair of natural transformations
for Tm and Ty components of CwF structure.

The main difference from definition in TypeTheory.ALV2.CwF_Cats
is that here we do not have a ϕ component (and corresponding axioms)
as it is completely derived from CwF pullback and the simple morphism.

Main definitions are

- [cwf_structure_cat] - category of CwF structures (for a fixed category C).
- [iscontr_cwf_structure_mor_ϕ] — a proof that there is a unique ϕ for every morphism;
- [weq_cwf_structure_mor_with_ϕ] — an equivalence of [cwf_structure_mor] and [cwf_structure_mor_with_ϕ];
*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.CategoryTheory.yoneda.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.CwF_def.


Section CwF_structure_cat.
  Context {C : category}.

  (* Extract the terms presheaf from a CwF structure. *)
  Definition TM (X : cwf_structure C) : [C^op, SET]
    := Tm (pr1 X).

  (* Extract the types presheaf from a CwF structure. *)
  Definition TY (X : cwf_structure C) : [C^op, SET]
    := Ty (pr1 X).

  (* Extract the extended context Γ.A
     given Γ and A in a given CwF structure. *)
  Definition cwf_extended_context
             (X : cwf_structure C)
             (Γ : C)
             (A : (TY X : functor _ _) Γ : hSet)
    : C
    := pr1 (pr1 (pr2 X _ A)).

  Local Notation "Γ ◂ A" := (cwf_extended_context _ Γ A) (at level 40).

  (* Extract the weakening projection π A : Γ ◂ A --> Γ *)
  Definition cwf_projection
             (X : cwf_structure C)
             (Γ : C)
             (A : (TY X : functor _ _) Γ : hSet)
    : Γ ◂ A --> Γ
    := pr2 (pr1 (pr2 X _ A)).

  Local Notation "'π' A" := (cwf_projection _ _ A) (at level 40).

  (* Extract the term in the extended context Γ.A *)
  Definition cwf_extended_context_term
             (X : cwf_structure C)
             (Γ : C)
             (A : (TY X : functor _ _) Γ : hSet)
    : (TM X : functor _ _) (Γ ◂ A) : hSet
    := pr1 (pr1 (pr2 (pr2 X _ A))).

  Local Notation "'te' A" := (cwf_extended_context_term _ _ A) (at level 40).

  (* CwF morphism data:
     - a natural transformation of terms presheaves;
     - a natural transformation of types presheaves;
  *)
  Definition cwf_structure_mor_data (X X' : cwf_structure C) : UU
    := (TM X --> TM X') × (TY X --> TY X').

  (* TM part of CwF morphism:
     a natural transformation of terms presheaves. *)
  Definition cwf_structure_mor_TM
             {X X' : cwf_structure C}
             (f : cwf_structure_mor_data X X')
    : TM X --> TM X'
    := pr1 f.

  (* TY part of CwF morphism:
     a natural transformation of types presheaves. *)
  Definition cwf_structure_mor_TY
             {X X' : cwf_structure C}
             (f : cwf_structure_mor_data X X')
    : TY X --> TY X'
    := pr2 f.

  (* coherence for "typing" natural transformation *)
  Definition cwf_structure_mor_typing_axiom
             (X X' : cwf_structure C)
             (mor : cwf_structure_mor_data X X')
    : UU
    := pr1 mor ;; pr1 X' = pr1 X ;; pr2 mor.

  Definition is_cwf_structure_mor
             (X X' : cwf_structure C)
             (mor : cwf_structure_mor_data X X')
    : UU
    := cwf_structure_mor_typing_axiom X X' mor.

  Lemma isaprop_is_cwf_structure_mor
        (X X' : cwf_structure C)
        (mor : cwf_structure_mor_data X X')
    : isaprop (is_cwf_structure_mor X X' mor).
  Proof.
    apply homset_property.
  Defined.
                                         
  (* CwF morphism:
     - a natural transformation of terms presheaves;
     - a natural transformation of types presheaves;
     - coherence conditions.
  *)
  Definition cwf_structure_mor (X X' : cwf_structure C) : UU
    := ∑ (mor : cwf_structure_mor_data X X'),
       is_cwf_structure_mor X X' mor.

  Coercion cwf_structure_mor_to_data
           (X X' : cwf_structure C)
           (mor : cwf_structure_mor X X')
    : cwf_structure_mor_data X X'
    := pr1 mor.
  
  (* Prove that two morphisms of CwF structures are equal
     given their constituent parts are equal pairwise. *)
  Definition cwf_structure_mor_eq (X X' : cwf_structure C)
             (f g : cwf_structure_mor X X')
             (* equality of TM components *)
             (e_TM : cwf_structure_mor_TM f = cwf_structure_mor_TM g)
             (* equality of TY components *)
             (e_TY : cwf_structure_mor_TY f = cwf_structure_mor_TY g)
    : f = g.
  Proof.
    use total2_paths_f.
    - use dirprod_paths.
      + apply e_TM.
      + apply e_TY.
    - apply isaprop_is_cwf_structure_mor.
  Defined.

  (* # Yo ϕ part of CwF morphism:
     a morphism in C moving context from one CwF to another. *)
  Definition cwf_structure_mor_Yo_ϕ
             {X X' : cwf_structure C}
             (f : cwf_structure_mor X X')
             (Γ : C^op) (A : (TY X : functor _ _) Γ : hSet)
    : Yo (Γ ◂ A) --> Yo (Γ ◂ ((cwf_structure_mor_TY f : nat_trans _ _) _ A)).
  Proof.
    set (A' := (cwf_structure_mor_TY f : nat_trans _ _) _ A).
    set (X'_isPullback := pr2 (pr2 (pr2 X' Γ A')) : isPullback _).
    set (X_commutes := pr2 (pr1 (pr2 (pr2 X Γ A))) : _ = _).
    apply (X'_isPullback
             _ (# Yo (π A)) (yy (te A) ;; cwf_structure_mor_TM f)).
    etrans. apply maponpaths, pathsinv0, yy_comp_nat_trans.
    etrans. apply assoc.
    etrans. apply maponpaths_2, pathsinv0, yy_natural.
    etrans. apply maponpaths_2, maponpaths, pathsinv0, X_commutes.
    etrans. apply maponpaths_2, pathsinv0, yy_comp_nat_trans.
    etrans. apply assoc'.
    etrans. apply maponpaths, pathsinv0, (pr2 f).
    apply assoc.
  Defined.

  Definition cwf_structure_mor_ϕ_data
             {X X' : cwf_structure C}
             (f : cwf_structure_mor X X')
    : UU
    := ∏ (Γ : C^op) (A : (TY X : functor _ _) Γ : hSet),
       (Γ ◂ A --> Γ ◂ ((cwf_structure_mor_TY f : nat_trans _ _) _ A)).

  Definition has_cwf_structure_mor_weakening_axiom
             {X X' : cwf_structure C}
             (mor : cwf_structure_mor X X')
             (ϕ : cwf_structure_mor_ϕ_data mor)
    : UU
    := ∏ (Γ : C) (A : (TY X : functor _ _) Γ : hSet),
       ϕ Γ A ;; π ((cwf_structure_mor_TY mor : nat_trans _ _) _ A)
       = π A.

  Definition has_cwf_structure_mor_term_axiom
             {X X' : cwf_structure C}
             (mor : cwf_structure_mor X X')
             (ϕ : cwf_structure_mor_ϕ_data mor)
    : UU
    := ∏ (Γ : C) (A : (TY X : functor _ _) Γ : hSet),
       ((cwf_structure_mor_TM mor : nat_trans _ _) _ (te A))
       = # (TM X' : functor _ _) (ϕ Γ A) (te _). 

  Definition cwf_structure_mor_ϕ 
             {X X' : cwf_structure C}
             (mor : cwf_structure_mor X X')
    : UU
    := ∑ (ϕ : cwf_structure_mor_ϕ_data mor),
       has_cwf_structure_mor_weakening_axiom mor ϕ
         × has_cwf_structure_mor_term_axiom mor ϕ.

  Definition cwf_structure_mor_ϕ_data_of
             {X X' : cwf_structure C}
             (f : cwf_structure_mor X X')
    : cwf_structure_mor_ϕ_data f.
  Proof.
    intros Γ A.
    apply (yoneda_fully_faithful _ ).
    apply cwf_structure_mor_Yo_ϕ.
  Defined.

  Definition cwf_structure_mor_weakening_axiom_of
             {X X' : cwf_structure C}
             (mor : cwf_structure_mor X X')
    : has_cwf_structure_mor_weakening_axiom
        mor (cwf_structure_mor_ϕ_data_of mor).
  Proof.
    intros Γ A.
    apply (invmaponpathsweq (# Yo ,, yoneda_fully_faithful _ _ _)).
    etrans. apply functor_comp.
    etrans. apply maponpaths_2.
    apply (homotweqinvweq (# Yo ,, yoneda_fully_faithful _ _ _ )).
    simpl.
    set (A' := (cwf_structure_mor_TY mor : nat_trans _ _) _ A).
    set (X'_isPullback := pr2 (pr2 (pr2 X' Γ A'))).
    set (X'_Pullback := make_Pullback _ X'_isPullback).
    set (P := PullbackArrow_PullbackPr1
                X'_Pullback _
                (# Yo (π A))
                (yy (te A) ;; cwf_structure_mor_TM mor)).
    apply P.
  Defined.

  Definition cwf_structure_mor_term_axiom_of
             {X X' : cwf_structure C}
             (mor : cwf_structure_mor X X')
    : has_cwf_structure_mor_term_axiom
        mor (cwf_structure_mor_ϕ_data_of mor).
  Proof.
    intros Γ A.
    apply (invmaponpathsweq (@yy _ _ _)).
    etrans. apply pathsinv0, yy_comp_nat_trans.
    apply pathsinv0.
    etrans. apply yy_natural.
    etrans. apply maponpaths_2.
    apply (homotweqinvweq (# Yo ,, yoneda_fully_faithful _ _ _ )).
    set (A' := (cwf_structure_mor_TY mor : nat_trans _ _) _ A).
    set (X'_isPullback := pr2 (pr2 (pr2 X' Γ A'))).
    set (X'_Pullback := make_Pullback _ X'_isPullback).
    set (P := PullbackArrow_PullbackPr2
                X'_Pullback _
                (# Yo (π A))
                (yy (te A) ;; cwf_structure_mor_TM mor)).
    apply P.
  Defined.

  Definition cwf_structure_mor_ϕ_of
             {X X' : cwf_structure C}
             (f : cwf_structure_mor X X')
    : cwf_structure_mor_ϕ f
    := (cwf_structure_mor_ϕ_data_of f,,
        cwf_structure_mor_weakening_axiom_of f,,
        cwf_structure_mor_term_axiom_of f).

  Definition iscontr_cwf_structure_mor_ϕ
             {X X' : cwf_structure C}
             (mor : cwf_structure_mor X X')
    : iscontr (cwf_structure_mor_ϕ mor).
  Proof.
    exists (cwf_structure_mor_ϕ_of mor).
    intros ϕ.
    use total2_paths_f.
    - apply funextsec. intros Γ.
      apply funextsec. intros A.
      apply (invmaponpathsweq (# Yo ,, yoneda_fully_faithful _ _ _)).
      set (A' := (cwf_structure_mor_TY mor : nat_trans _ _) _ A).
      set (X'_isPullback := pr2 (pr2 (pr2 X' Γ A'))).
      set (P := PullbackArrowUnique
                  _
                  X'_isPullback
                  _
                  (# Yo (π A))
                  (yy (te A) ;; cwf_structure_mor_TM mor)
          ).

      assert ( # Yo (π A) ;; yy A' =
               yy (te A) ;; cwf_structure_mor_TM mor ;; pr1 X')
        as Hcomm.
      {
        etrans. apply maponpaths, pathsinv0, yy_comp_nat_trans.
        etrans. apply assoc.
        set (te_commutes := pr2 (pr1 (pr2 (pr2 X Γ A))) : _ = _).
        set (X'_commutes := cwf_square_comm te_commutes).
        etrans. apply maponpaths_2, X'_commutes.
        etrans. apply assoc'.
        etrans. apply maponpaths, pathsinv0, (pr2 mor).
        apply assoc.
      }
      
      etrans. apply (P Hcomm).
      + etrans. apply pathsinv0, functor_comp.
        apply maponpaths.
        apply (pr1 (pr2 ϕ)).
      + etrans. apply pathsinv0, yy_natural.
        etrans. apply maponpaths, pathsinv0, (pr2 (pr2 ϕ)).
        apply pathsinv0, yy_comp_nat_trans.
      + apply pathsinv0, P.
        * etrans. apply pathsinv0, functor_comp.
          apply maponpaths.
          apply (cwf_structure_mor_weakening_axiom_of mor).
        * etrans. apply pathsinv0, yy_natural.
          etrans. apply maponpaths, pathsinv0, (cwf_structure_mor_term_axiom_of mor).
          apply pathsinv0, yy_comp_nat_trans.

    - apply dirprod_paths.
      + apply funextsec. intros Γ.
        apply funextsec. intros A.
        apply homset_property.
      + apply funextsec. intros Γ.
        apply funextsec. intros A.
        apply setproperty.
  Defined.

  Definition cwf_structure_mor_with_ϕ (X X' : cwf_structure C)
    : UU
    := ∑ (mor : cwf_structure_mor X X'), cwf_structure_mor_ϕ mor.

  Coercion cwf_structure_mor_with_ϕ_to_mor
           (X X' : cwf_structure C)
           (mor : cwf_structure_mor_with_ϕ X X')
    : cwf_structure_mor X X'
    := pr1 mor.

  Definition weq_cwf_structure_mor_with_ϕ
             {X X' : cwf_structure C}
    : cwf_structure_mor_with_ϕ X X' ≃ cwf_structure_mor X X'.
  Proof.
    apply weqpr1.
    intros mor.
    apply iscontr_cwf_structure_mor_ϕ.
  Defined.

  Definition cwf_structure_mor_with_ϕ_eq
             {X X' : cwf_structure C}
             (f g : cwf_structure_mor_with_ϕ X X')
             (e_TM : cwf_structure_mor_TM f = cwf_structure_mor_TM g)
             (e_TY : cwf_structure_mor_TY f = cwf_structure_mor_TY g)
    : f = g.
  Proof.
    use total2_paths_f.
    - use cwf_structure_mor_eq.
      + apply e_TM.
      + apply e_TY.
    - apply proofirrelevancecontr.
      apply iscontr_cwf_structure_mor_ϕ.
  Defined.

  Definition make_cwf_structure_mor
             {X X' : cwf_structure C}
             (mor : cwf_structure_mor_data X X')
             (e_typing : cwf_structure_mor_typing_axiom X X' mor)
    : cwf_structure_mor X X'
    := (mor ,, e_typing).

  (* Definitions of objects and morphisms for
     the category of CwF structures. *)
  Definition cwf_structure_precategory_ob_mor : precategory_ob_mor
    := make_precategory_ob_mor
         (cwf_structure C) cwf_structure_mor.

  (* Precategory data for CwF structures:
     - definitions of objects & morphisms;
     - definition of identity morphisms;
     - definition of morphism composition.

     All definitions are straighforward and based on
     composition of corresponding natural transformations and morphisms.
   *)
  Definition cwf_structure_precategory_data : precategory_data.
  Proof.
    apply (make_precategory_data cwf_structure_precategory_ob_mor).

    + (* Identity morphisms *)
      intros X.
      use make_cwf_structure_mor.
      - exists (identity _).
        apply identity.
      - unfold cwf_structure_mor_typing_axiom. simpl.
        etrans. apply (id_left (pr1 X)).
        apply pathsinv0, (id_right (pr1 X)).

    + (* Composition of morphisms *)
      intros X Y Z.
      intros [[F_TM F_TY] ax] [[F_TM' F_TY'] ax'].
      use make_cwf_structure_mor.
      - exists (F_TM ;; F_TM').
        apply (F_TY ;; F_TY').
      - unfold cwf_structure_mor_typing_axiom. simpl.
        etrans. apply (assoc' F_TM).
        etrans. apply maponpaths, ax'.
        etrans. apply (assoc F_TM).
        etrans. apply maponpaths_2, ax.
        apply (assoc' (pr1 X)).
  Defined.

  (* Axioms for CwF structure morphisms:
     - identity · f = f
     - f · identity = f
     - f · (g · h) = (f · g) · h
   *)
  Definition cwf_structure_precategory_axioms
    : is_precategory cwf_structure_precategory_data.
  Proof.
    use make_is_precategory_one_assoc.
    - (* Left identity: identity · f = f *)
      intros a b f.
      use cwf_structure_mor_eq.
      + apply id_left.
      + apply id_left.
    - (* Right identity: f · identity = f *)
      intros a b f.
      use cwf_structure_mor_eq.
      + apply id_right.
      + apply id_right.
    - (* Associativity: f · (g · h) = (f · g) · h *)
      intros a b c d.
      intros f g h.
      use cwf_structure_mor_eq.
      + apply assoc.
      + apply assoc.
  Defined.

  (* Precategory of CwF-structures *)
  Definition cwf_structure_precat : precategory
    := (_,, cwf_structure_precategory_axioms).

  Lemma isaset_cwf_structure_mor
           (X X' : cwf_structure C)
     : isaset (cwf_structure_mor X X').
  Proof.
    apply isaset_total2.
    - apply isaset_dirprod.
      + apply homset_property.
      + apply homset_property.
    - intros mor.
      apply isasetaprop.
      apply isaprop_is_cwf_structure_mor.
  Defined.

  Definition cwf_structure_has_homsets
    : has_homsets cwf_structure_precategory_data.
  Proof.
    intros X X'.
    apply isaset_cwf_structure_mor.
  Defined.

  (* Category of CwF-structures *)
  Definition cwf_structure_cat : category
    := (cwf_structure_precat ,, cwf_structure_has_homsets).

End CwF_structure_cat.

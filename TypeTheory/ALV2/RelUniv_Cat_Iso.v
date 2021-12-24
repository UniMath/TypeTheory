(**
  [TypeTheory.ALV2.RelUniv_Cat_Iso]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**
This module establishes an an isomorphism of
categories of "simple" and "full" categories of relative J-universe structures.
The isomorphism follows from the fact that ϕ component is completely determined
by the remaining parts of a morphisms when J is fully faithful.

Main definitions:

- [reluniv_functor] and [reluniv_cat_iso].

*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheory.
Require Import TypeTheory.ALV1.RelativeUniverses.
Require Import TypeTheory.ALV2.RelUniv_Cat_Simple.
Require Import TypeTheory.ALV2.RelUniv_Cat.
Require Import UniMath.CategoryTheory.catiso.

Section Cat_Iso.

  Context {C D : category}.
  Context (J : functor C D).
  Context (ff_J : fully_faithful J).

  Definition reluniv_mor_to_reluniv_mor_with_ϕ
             (u1 u2 : relative_universe J)
    : relative_universe_mor _ u1 u2 → reluniv_mor_with_ϕ _ u1 u2.
  Proof.
    intros mor.
    exact (mor ,, reluniv_mor_ϕ_of _ ff_J mor).
  Defined.

  Definition reluniv_mor_with_ϕ_to_reluniv_mor
             (u1 u2 : relative_universe J)
    : reluniv_mor_with_ϕ _ u1 u2 → relative_universe_mor _ u1 u2
    := pr1.

  Definition isweq_reluniv_mor_to_reluniv_mor_with_ϕ
             (u1 u2 : relative_universe J)
    : isweq (reluniv_mor_to_reluniv_mor_with_ϕ u1 u2).
  Proof.
    apply (isweq_iso _ (reluniv_mor_with_ϕ_to_reluniv_mor _ _)).
    - intros mor. apply idpath.
    - intros mor.
      apply reluniv_mor_with_ϕ_eq_faithful.
      + apply idpath.
      + apply idpath.
      + apply fully_faithful_implies_full_and_faithful, ff_J.
  Defined.

  Definition weq_reluniv_mor
             (u1 u2 : relative_universe J)
    : relative_universe_mor _ u1 u2 ≃ reluniv_mor_with_ϕ _ u1 u2
    := (_ ,, isweq_reluniv_mor_to_reluniv_mor_with_ϕ u1 u2).

  Definition reluniv_functor_data
    : functor_data (@reluniv_cat C _ J)
                   (@reluniv_with_ϕ_cat C _ J).
  Proof.
    use make_functor_data.
    - apply idweq.
    - intros u1 u2. apply weq_reluniv_mor.
  Defined.

  Definition reluniv_functor_idax
    : functor_idax reluniv_functor_data.
  Proof.
    intros c. 
    use reluniv_mor_with_ϕ_eq_faithful.
    - apply idpath.
    - apply idpath.
    - apply fully_faithful_implies_full_and_faithful, ff_J.
  Defined.

  Definition reluniv_functor_compax
    : functor_compax reluniv_functor_data.
  Proof.
    intros a b c.
    intros f g.

    use reluniv_mor_with_ϕ_eq_faithful.
    - apply idpath.
    - apply idpath.
    - apply fully_faithful_implies_full_and_faithful, ff_J.
  Defined.

  Definition reluniv_is_functor
    : is_functor reluniv_functor_data
    := (reluniv_functor_idax ,, reluniv_functor_compax).
  
  Definition reluniv_functor
    : functor (reluniv_cat J)
              (reluniv_with_ϕ_cat J).
  Proof.
    use (make_functor reluniv_functor_data).
    apply reluniv_is_functor.
  Defined.

  Definition reluniv_is_catiso : is_catiso reluniv_functor.
  Proof.
    use tpair.
    - unfold fully_faithful.
      intros u1 u2.
      apply weq_reluniv_mor.
    - apply (pr2 (idweq _)).
  Defined.

End Cat_Iso.

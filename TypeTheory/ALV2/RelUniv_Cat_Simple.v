(**
  [TypeTheory.ALV2.RelUniv_Cat]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(** 
This module defines two categories of relative J-universe structures:
- [reluniv_cat] — with "simple" (or naive) morphisms (simple commutative squares);
- [reluniv_with_ϕ_cat] — with "full" morphisms (with explicit ϕ component and corresponding axioms).

ϕ component is completely determined by the remaining parts of a morphisms when J is fully faithful.
This result is reflected in [reluniv_mor_ϕ_of] and futher developed into an isomorphism of
categories in [TypeTheory.ALV2.RelUniv_Cat_Iso].

An isomorphism between a (simple) category of CwF structures and
(simple) category of relative universe structures over the Yoneda embedding functor
is also demonstrated in [TypeTheory.ALV2.RelUniv_Cat_Yo_CwF_Iso].

Other important definitions:
- [iscontr_reluniv_mor_ϕ] — proof that ϕ component is contractible when J is fully faithful;
- [isaprop_reluniv_mor_ϕ] — proof that ϕ component is proposition when J is faithful.

TODO: document/update Comm_Squares and Functor_Squares sections.

*)

Require Import UniMath.Foundations.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.limits.pullbacks.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.RelativeUniverses.

Local Set Automatic Introduction.
(* only needed since imports globally unset it *)

Section RelUniv.

  Context {C D : category}.
  Context (J : functor C D).

Section RelUniv_Cat_Simple.

  Context (pb_structure : functor C D → ∏ a b : D, D ⟦ b, a ⟧ → Type).
  Let gen_reluniv J := ∑ X : mor_total D, pb_structure J _ _ X.

  Local Definition Ũ (u : gen_reluniv J) := source (pr1 u).
  Local Definition U (u : gen_reluniv J) := target (pr1 u).

  Definition gen_reluniv_mor_data
             (u1 u2 : gen_reluniv J)
    : UU
    := (Ũ u1 --> Ũ u2) × (U u1 --> U u2).

  Local Definition F_Ũ
        {u1 u2 : gen_reluniv J}
        (mor : gen_reluniv_mor_data u1 u2)
    : Ũ u1 --> Ũ u2
    := pr1 mor.
  Local Definition F_U
        {u1 u2 : gen_reluniv J}
        (mor : gen_reluniv_mor_data u1 u2)
    : U u1 --> U u2
    := pr2 mor.

  Definition is_gen_reluniv_mor
             {u1 u2 : gen_reluniv J}
             (mor : gen_reluniv_mor_data u1 u2)
    : UU
    := F_Ũ mor ;; pr1 u2 = pr1 u1 ;; F_U mor.

  Definition isaprop_is_gen_reluniv_mor
             {u1 u2 : gen_reluniv J}
             (mor : gen_reluniv_mor_data u1 u2)
    : isaprop (is_gen_reluniv_mor mor).
  Proof.
    apply homset_property.
  Defined.

  Definition gen_reluniv_mor
             (u1 u2 : gen_reluniv J)
    : UU
    := ∑ (mor : gen_reluniv_mor_data u1 u2),
       is_gen_reluniv_mor mor.

  Coercion gen_reluniv_mor_to_data
           (u1 u2 : gen_reluniv J)
           (mor : gen_reluniv_mor u1 u2)
    : gen_reluniv_mor_data u1 u2
    := pr1 mor.

  Definition gen_reluniv_mor_eq
             (u1 u2 : gen_reluniv J)
             (g h : gen_reluniv_mor u1 u2)
             (e_Ũ : F_Ũ g = F_Ũ h)
             (e_U : F_U g = F_U h)
    : g = h.
  Proof.
    use total2_paths_f.
    - use dirprod_paths.
      + apply e_Ũ.
      + apply e_U.
    - apply isaprop_is_gen_reluniv_mor.
  Defined.

  Definition gen_reluniv_mor_id
             (u : gen_reluniv J)
    : gen_reluniv_mor u u.
  Proof.
    use tpair.
    - exists (identity _).
      apply identity.
    - unfold is_gen_reluniv_mor. simpl.
      etrans. apply id_left.
      apply pathsinv0, id_right.
  Defined.

  Definition gen_reluniv_mor_comp
             (a b c : gen_reluniv J)
             (g : gen_reluniv_mor a b)
             (h : gen_reluniv_mor b c)
    : gen_reluniv_mor a c.
  Proof.
    use tpair.
    - exists (F_Ũ g ;; F_Ũ h).
      exact (F_U g ;; F_U h).
    - unfold is_gen_reluniv_mor. simpl.
      etrans. apply assoc'.
      etrans. apply maponpaths, (pr2 h).
      etrans. apply assoc.
      etrans. apply maponpaths_2, (pr2 g).
      apply assoc'.
  Defined.

  Definition gen_reluniv_precat_ob_mor : precategory_ob_mor
    := (gen_reluniv J ,, gen_reluniv_mor).

  Definition gen_reluniv_precat_id_comp
    : precategory_id_comp gen_reluniv_precat_ob_mor
    := (gen_reluniv_mor_id ,, gen_reluniv_mor_comp).

  Definition gen_reluniv_precat_data : precategory_data
    := (gen_reluniv_precat_ob_mor ,, gen_reluniv_precat_id_comp).

  Definition gen_reluniv_is_precategory : is_precategory gen_reluniv_precat_data.
  Proof.
    use make_is_precategory_one_assoc.
    - intros a b g.
      use gen_reluniv_mor_eq.
      * apply id_left.
      * apply id_left.
    - intros a b g.
      use gen_reluniv_mor_eq.
      * apply id_right.
      * apply id_right.
    - intros a b c d g h k.
      use gen_reluniv_mor_eq.
      * apply assoc.
      * apply assoc.
  Defined.

  Definition gen_reluniv_precat : precategory
    := ( gen_reluniv_precat_data ,, gen_reluniv_is_precategory ).

  Definition isaset_gen_reluniv_mor
             (u1 u2 : gen_reluniv J)
    : isaset (gen_reluniv_mor u1 u2).
  Proof.
    apply isaset_total2.
    - apply isaset_dirprod.
      + apply homset_property.
      + apply homset_property.
    - intros mor.
      apply isasetaprop.
      apply isaprop_is_gen_reluniv_mor.
  Defined.

  Definition gen_reluniv_has_homsets : has_homsets gen_reluniv_precat.
  Proof.
    unfold has_homsets.
    intros a b.
    apply isaset_gen_reluniv_mor.
  Defined.

  Definition gen_reluniv_cat : category
    := ( gen_reluniv_precat ,, gen_reluniv_has_homsets ).

End RelUniv_Cat_Simple.

    Definition reluniv_cat : category
      := gen_reluniv_cat rel_universe_structure.

    Definition weak_reluniv_cat : category
      := gen_reluniv_cat is_universe_relative_to.

End RelUniv.
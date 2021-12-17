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

*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.RelativeUniverses.

Require Import UniMath.CategoryTheory.catiso.


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

  Definition F_Ũ
        {u1 u2 : gen_reluniv J}
        (mor : gen_reluniv_mor_data u1 u2)
    : Ũ u1 --> Ũ u2
    := pr1 mor.
  Definition F_U
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

Section WeakRelUniv_is_univalent.

    Definition is_weak_reluniv_ob
      : arrow_category D → hProp.
    Proof.
      intros abf.
      set (a := pr1 (pr1 abf)).
      set (b := dirprod_pr2 (pr1 abf)).
      set (f := pr2 abf).
      use tpair.
      - apply (is_universe_relative_to J f).
      - apply impred. intros x.
        apply impred. intros y.
        apply isapropishinh.
    Defined.

    Definition weak_reluniv_subcat : category
      := subcategory _ (full_sub_precategory is_weak_reluniv_ob).

    Definition weak_reluniv_cat_subcat_weq_ob
      : ob weak_reluniv_cat ≃ ob weak_reluniv_subcat.
    Proof.
      use weq_iso.
      - intros u.
        set (b := pr1 (pr1 (pr1 u))).
        set (a := dirprod_pr2 (pr1 (pr1 u))).
        set (f := pr2 (pr1 u)).
        set (comm := pr2 u).
        apply (((a,b),,f),,comm).
      - intros ff.
        set (a := pr1 (pr1 (pr1 ff))).
        set (b := dirprod_pr2 (pr1 (pr1 ff))).
        set (f := pr2 (pr1 ff)).
        set (comm := pr2 ff).
        apply (((b,a),,f),,comm).
      - intros u. apply idpath.
      - intros u. apply idpath.
    Defined.

    Definition weak_reluniv_cat_subcat_weq_mor
               (u1 u2 : weak_reluniv_cat)
      : weak_reluniv_cat ⟦ u1, u2 ⟧
          ≃ weak_reluniv_subcat
            ⟦ weak_reluniv_cat_subcat_weq_ob u1,
              weak_reluniv_cat_subcat_weq_ob u2 ⟧.
    Proof.
      use weq_iso.
      - intros mor.
        set (b_to_d := pr1 (pr1 mor)).
        set (a_to_c := dirprod_pr2 (pr1 mor)).
        set (comm_square := pr2 mor).
        use (tpair _ _ tt).
        use tpair.
        + apply (make_dirprod b_to_d a_to_c).
        + apply pathsinv0, comm_square.
      - intros mor.
        set (b_to_d := pr1 (pr1 (pr1 mor))).
        set (a_to_c := dirprod_pr2 (pr1 (pr1 mor))).
        set (comm_square := pr2 (pr1 mor)).
        use tpair.
        + use make_dirprod.
            * apply b_to_d.
            * apply a_to_c.
        + apply pathsinv0, comm_square.
      - intros mor.
        use gen_reluniv_mor_eq.
        + apply idpath.
        + apply idpath.
      - intros mor.
        use total2_paths_f.
        + use arrow_category_mor_eq.
          * apply idpath.
          * apply idpath.
        + apply isapropunit.
    Defined.

    Definition weak_reluniv_cat_to_full_subcat
      : catiso weak_reluniv_cat weak_reluniv_subcat.
    Proof.
      use tpair.
      - use make_functor.
        + use make_functor_data.
          * apply weak_reluniv_cat_subcat_weq_ob.
          * apply weak_reluniv_cat_subcat_weq_mor.
        + use tpair.
          * intros u.
            use dirprod_paths.
            -- use arrow_category_mor_eq.
               ++ apply idpath.
               ++ apply idpath.
            -- apply isapropunit.
          * intros a b c f g.
            use dirprod_paths.
            -- use arrow_category_mor_eq.
               ++ apply idpath.
               ++ apply idpath.
            -- apply isapropunit.
      - use make_dirprod.
        + intros a b.
          apply (pr2 (weak_reluniv_cat_subcat_weq_mor a b)).
        + apply weak_reluniv_cat_subcat_weq_ob.
    Defined.

    Definition weak_reluniv_cat_is_univalent
               (D_univ : is_univalent D)
      : is_univalent weak_reluniv_cat.
    Proof.
      use (catiso_univalent _ _ weak_reluniv_cat_to_full_subcat).
      apply (is_univalent_full_subcat
               (arrow_category D)
               is_weak_reluniv_ob
               (arrow_category_is_univalent D_univ)
            ).
    Defined.

End WeakRelUniv_is_univalent.

End RelUniv.

Section RelUniv_Functor.

  Context {C D : category}.
  Context (J : functor C D).

  Definition weak_from_reluniv_mor
             (u1 u2 : relative_universe J)
    : gen_reluniv_mor J rel_universe_structure u1 u2
      → gen_reluniv_mor J is_universe_relative_to
                        (weak_from_relative_universe _ u1)
                        (weak_from_relative_universe _ u2).
  Proof.
    intros mor.
    set (f := pr1 (pr1 mor)).
    set (g := pr2 (pr1 mor)).
    set (is_mor := pr2 mor).
    apply ((f ,, g) ,, is_mor).
  Defined.

  Definition reluniv_from_weak_mor
             (u1 u2 : relative_universe J)
    : gen_reluniv_mor J is_universe_relative_to
                      (weak_from_relative_universe _ u1)
                      (weak_from_relative_universe _ u2)
      → gen_reluniv_mor J rel_universe_structure u1 u2.
  Proof.
    intros mor.
    set (f := pr1 (pr1 mor)).
    set (g := pr2 (pr1 mor)).
    set (is_mor := pr2 mor).
    apply ((f ,, g) ,, is_mor).
  Defined.

  Definition isweq_weak_from_reluniv_mor
             (u1 u2 : relative_universe J)
    : isweq (weak_from_reluniv_mor u1 u2).
  Proof.
    use isweq_iso.
    - apply reluniv_from_weak_mor.
    - intros x. apply idpath.
    - intros x. apply idpath.
  Defined.

  Definition weak_from_reluniv_functor_data
    : functor_data (reluniv_cat J) (weak_reluniv_cat J).
  Proof.
    use make_functor_data.
    - apply weak_from_relative_universe.
    - apply weak_from_reluniv_mor.
  Defined.

  Definition weak_from_reluniv_functor_idax
    : functor_idax weak_from_reluniv_functor_data.
  Proof.
    intros u.
    apply idpath.
  Defined.

  Definition weak_from_reluniv_functor_compax
    : functor_compax weak_from_reluniv_functor_data.
  Proof.
    intros a b c f g.
    apply idpath.
  Defined.

  Definition weak_from_reluniv_is_functor
    : is_functor weak_from_reluniv_functor_data
    := (weak_from_reluniv_functor_idax ,, weak_from_reluniv_functor_compax).
  
  Definition weak_from_reluniv_functor
    : functor (reluniv_cat J) (weak_reluniv_cat J)
    := make_functor weak_from_reluniv_functor_data
                    weak_from_reluniv_is_functor.

  Definition weak_from_reluniv_functor_is_faithful
    : faithful weak_from_reluniv_functor.
  Proof.
    intros u1 u2.
    apply isinclweq.
    apply isweq_weak_from_reluniv_mor.
  Defined.

  Definition weak_from_reluniv_functor_is_full
    : full weak_from_reluniv_functor.
  Proof.
    intros u1 u2.
    apply issurjectiveweq.
    apply isweq_weak_from_reluniv_mor.
  Defined.

  Definition weak_from_reluniv_functor_ff
    : fully_faithful weak_from_reluniv_functor.
  Proof.
    apply full_and_faithful_implies_fully_faithful.
    use make_dirprod.
    - apply weak_from_reluniv_functor_is_full.
    - apply weak_from_reluniv_functor_is_faithful.
  Defined.

  Definition weak_from_reluniv_functor_is_catiso
             (Ccat : is_univalent C) (J_ff : fully_faithful J)
    : is_catiso weak_from_reluniv_functor.
  Proof.
    use make_dirprod.
    - apply weak_from_reluniv_functor_ff.
    - apply (weqproperty (weq_relative_universe_weak_relative_universe _ Ccat J_ff)).
  Defined.

  Definition weak_from_reluniv_functor_catiso
             (Ccat : is_univalent C) (J_ff : fully_faithful J)
    : catiso (reluniv_cat J) (weak_reluniv_cat J)
    := (weak_from_reluniv_functor
          ,, weak_from_reluniv_functor_is_catiso Ccat J_ff).
  
  Definition reluniv_cat_is_univalent
             (Ccat : is_univalent C) (J_ff : fully_faithful J)
             (Dcat : is_univalent D)
    : is_univalent (reluniv_cat J).
  Proof.
    use (catiso_univalent
           _ _ (weak_from_reluniv_functor_catiso Ccat J_ff)).
    apply weak_reluniv_cat_is_univalent.
    apply Dcat.
  Defined.

  Definition weak_reluniv_isaset
             (obD_isaset : isaset (ob D))
    : isaset (weak_reluniv_cat J).
  Proof.
    use isaset_total2.
    - use isaset_total2.
      + use isaset_dirprod.
        * apply obD_isaset.
        * apply obD_isaset.
      + intros d. apply homset_property.
    - intros mor.
      apply isasetaprop.
      apply impred. intros c.
      apply impred. intros d.
      apply isapropishinh.
  Qed.

  (* Lemma 3.8.2 from the HoTT book *)
  Definition ishinh_impred
             {X : hSet} {P : X → UU}
             (AC : AxiomOfChoice.AxiomOfChoice)
    : (∏ (x : X), ∥ P x ∥) → ∥ ∏ (x : X), P x ∥.
  Proof.
    apply (AC X P).
  Defined.

  (* A version of ishinh_impred for 2 arguments and types *)
  Definition ishinh_impred2_UU
             {X : UU} {Y : X → UU} {P : ∏ (x : X), Y x → UU}
             (X_isaset : isaset X)
             (Y_isaset : ∏ (x : X), isaset (Y x))
             (AC : AxiomOfChoice.AxiomOfChoice)
    : (∏ (x : X) (y : Y x), ∥ P x y ∥) → ∥ ∏ (x : X) (y : Y x), P x y ∥.
  Proof.
    intros f.
    set (X' := make_hSet _ X_isaset).
    set (Y' := λ (x : X), make_hSet _ (Y_isaset x)).
    apply (AC _ _ (λ (x : X'), AC _ _ (λ (y : Y' x), f x y))).
  Defined.

  Definition to_ishinh_rel_universe_structure
             (AC : AxiomOfChoice.AxiomOfChoice)
             (obC_isaset : isaset C)
             {u1 u2 : D}
             {mor : D ⟦ u1, u2 ⟧}
    : is_universe_relative_to J mor → ∥ rel_universe_structure J mor ∥.
  Proof.
    use ishinh_impred2_UU.
    - apply obC_isaset.
    - intros c.
      apply homset_property.
    - apply AC.
  Defined.

  Definition weak_from_reluniv_functor_issurjective
             (AC : AxiomOfChoice.AxiomOfChoice)
             (obC_isaset : isaset C)
    : issurjective weak_from_reluniv_functor.
  Proof.
    intros u.
    use (@hinhfun (rel_universe_structure J (pr1 u))).
    - intros rs.
      use tpair.
      + use tpair.
        * apply (pr1 u).
        * apply rs.
      + use total2_paths_f.
        * apply idpath.
        * apply funextsec. intros X.
          apply funextsec. intros Y.
          apply isapropishinh.
    - apply (to_ishinh_rel_universe_structure AC obC_isaset (pr2 u)).
  Defined.

End RelUniv_Functor.

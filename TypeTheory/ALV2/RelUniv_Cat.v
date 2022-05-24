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

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.limits.pullbacks.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheory.
Require Import TypeTheory.Auxiliary.TypeOfMorphisms.

Require Import TypeTheory.RelUniv.RelativeUniverses.
Require Import TypeTheory.ALV2.RelUniv_Cat_Simple.


Section RelUniv.

  Context {C D : category}.
  Context (J : functor C D).

Section RelUniv_ϕ_Cat.

  Local Definition Ũ (u : relative_universe J) := source (pr1 u).
  Local Definition U (u : relative_universe J) := target (pr1 u).

  Definition relative_universe_mor_data := gen_reluniv_mor_data J rel_universe_structure.
  Definition relative_universe_mor := gen_reluniv_mor J rel_universe_structure.

  Coercion reluniv_mor_to_data
           (u1 u2 : relative_universe J)
           (mor : relative_universe_mor u1 u2)
    : relative_universe_mor_data u1 u2
    := pr1 mor.

  Local Definition F_Ũ
        {u1 u2 : relative_universe J}
        (mor : relative_universe_mor_data u1 u2)
    : Ũ u1 --> Ũ u2
    := pr1 mor.
  Local Definition F_U
        {u1 u2 : relative_universe J}
        (mor : relative_universe_mor_data u1 u2)
    : U u1 --> U u2
    := pr2 mor.

  Local Definition Xf (u : relative_universe J)
        (X : C) (f : J X --> U u) : C
    := pr1 (pr1 (pr2 u X f)).
  Local Definition π (u : relative_universe J)
        (X : C) (f : J X --> U u) : C ⟦ Xf u X f, X ⟧
    := pr1 (pr2 (pr1 (pr2 u X f))).
  Local Definition Q (u : relative_universe J)
        (X : C) (f : J X --> U u) : D ⟦ J (Xf u X f), Ũ u ⟧
    := pr2 (pr2 (pr1 (pr2 u X f))).
  Local Definition u_commutes (u : relative_universe J)
        (X : C) (f : J X --> U u)
    : # J (fp (pr1 (pr2 u X f)));; f = fq (pr1 (pr2 u X f));; pr1 u
    := pr1 (pr2 (pr2 u X f)).
  Local Definition u_isPullback (u : relative_universe J)
        (X : C) (f : J X --> U u)
    : isPullback (*f (pr1 u) (# J (fp (pr1 (pr2 u X f))))
                 (fq (pr1 (pr2 u X f)))*) (pr1 (pr2 (pr2 u X f)))
    := pr2 (pr2 (pr2 u X f)).

  Definition reluniv_mor_ϕ_data
             {u1 u2 : relative_universe J}
             (mor : relative_universe_mor u1 u2)
             (X : C) (f : J X --> U u1)
    : UU
    := Xf u1 X f --> Xf u2 X (f ;; F_U mor).
  
  Definition has_reluniv_mor_axiom_ϕ_π
             {u1 u2 : relative_universe J}
             (mor : relative_universe_mor u1 u2)
             (X : C) (f : J X --> U u1)
             (ϕ : reluniv_mor_ϕ_data mor X f)
    : UU
    := ϕ ;; π u2 X (F_U mor ∘ f) = π u1 X f.
  
  Definition has_reluniv_mor_axiom_ϕ_Q
             {u1 u2 : relative_universe J}
             (mor : relative_universe_mor u1 u2)
             (X : C) (f : J X --> U u1)
             (ϕ : reluniv_mor_ϕ_data mor X f)
    : UU
    := # J ϕ ;; Q u2 X (F_U mor ∘ f) = Q u1 X f ;; F_Ũ mor.

  Definition reluniv_mor_ϕ
             {u1 u2 : relative_universe J}
             (mor : relative_universe_mor u1 u2)
             (X : C) (f : J X --> U u1)
    : UU
    := ∑ (ϕ : reluniv_mor_ϕ_data mor X f),
       has_reluniv_mor_axiom_ϕ_π mor X f ϕ ×
         has_reluniv_mor_axiom_ϕ_Q mor X f ϕ.

  Definition reluniv_mor_J_ϕ_data_of
             {u1 u2 : relative_universe J}
             (mor : relative_universe_mor u1 u2)
    : ∏ (X : C) (f : J X --> U u1),
      J (Xf u1 X f) --> J (Xf u2 X (f ;; F_U mor)).
  Proof.
    intros X f.
    apply (u_isPullback u2 X (f ;; F_U mor)
                        _ (# J (π u1 X f)) (Q u1 X f ;; F_Ũ mor)).
    etrans. apply assoc.
    etrans. apply maponpaths_2, (u_commutes u1 X f).
    etrans. apply assoc'.
    apply pathsinv0.
    etrans. apply assoc'.
    apply maponpaths.
    apply (pr2 mor).
  Defined.

  Definition reluniv_mor_ϕ_data_of
             (ff_J : fully_faithful J)
             {u1 u2 : relative_universe J}
             (mor : relative_universe_mor u1 u2)
    : ∏ (X : C) (f : J X --> U u1),
      reluniv_mor_ϕ_data mor X f.
  Proof.
    intros X f.
    apply ff_J.
    apply reluniv_mor_J_ϕ_data_of.
  Defined.

  Definition reluniv_mor_axiom_ϕ_π
             (ff_J : fully_faithful J)
             {u1 u2 : relative_universe J}
             (mor : relative_universe_mor u1 u2)
    : ∏ (X : C) (f : J X --> U u1),
      has_reluniv_mor_axiom_ϕ_π mor X f
        (reluniv_mor_ϕ_data_of ff_J mor X f).
  Proof.
    intros X f.
    apply (invmaponpathsweq (# J ,, ff_J _ _)).
    etrans. apply functor_comp.
    etrans. apply maponpaths_2, (homotweqinvweq (# J ,, ff_J _ _) _).
    simpl.
    set (u2_Pullback
         := make_Pullback
             _
              (u_isPullback u2 X (f ;; F_U mor))).
    apply (PullbackArrow_PullbackPr1 u2_Pullback).
  Defined.

  Definition reluniv_mor_axiom_ϕ_Q
             (ff_J : fully_faithful J)
             {u1 u2 : relative_universe J}
             (mor : relative_universe_mor u1 u2)
    : ∏ (X : C) (f : J X --> U u1),
      has_reluniv_mor_axiom_ϕ_Q mor X f
        (reluniv_mor_ϕ_data_of ff_J mor X f).
  Proof.
    intros X f.
    set (u2_Pullback
         := make_Pullback
            _
              (u_isPullback u2 X (f ;; F_U mor))).
    etrans. apply maponpaths_2, (homotweqinvweq (# J ,, ff_J _ _) _).
    apply (PullbackArrow_PullbackPr2 u2_Pullback).
  Defined.

  Definition reluniv_mor_ϕ_of
             (ff_J : fully_faithful J)
             {u1 u2 : relative_universe J}
             (mor : relative_universe_mor u1 u2)
    : ∏ (X : C) (f : J X --> U u1),
      reluniv_mor_ϕ mor X f.
  Proof.
    intros X f.
    exists (reluniv_mor_ϕ_data_of ff_J mor X f).
    use make_dirprod.
    - apply reluniv_mor_axiom_ϕ_π.
    - apply reluniv_mor_axiom_ϕ_Q.
  Defined.

  Definition isaprop_reluniv_mor_ϕ
             (f_J : faithful J)
             {u1 u2 : relative_universe J}
             (mor : relative_universe_mor u1 u2)
             (X : C) (f : J X --> U u1)
    : isaprop (reluniv_mor_ϕ mor X f).
  Proof.
    apply invproofirrelevance.
    intros ϕ ϕ'.
    use total2_paths_f.
    + apply (invmaponpathsincl (# J) (f_J _ _)).
      set (P := PullbackArrowUnique
               _
               (u_isPullback u2 X (f ;; F_U mor))
               _ (# J (π u1 X f)) (Q u1 X f ;; F_Ũ mor)
            ).
      assert (# J (π u1 X f) ;; (f ;; F_U mor) =
              Q u1 X f ;; F_Ũ mor ;; pr1 u2) as Hcomm.
      {
        etrans. apply assoc.
        etrans. apply maponpaths_2, (u_commutes u1 X f).
        etrans. apply assoc'.
        etrans. apply maponpaths, pathsinv0, (pr2 mor).
        apply assoc.
      }
      etrans. apply (P Hcomm).
      * etrans. apply pathsinv0, functor_comp.
        apply maponpaths, (pr1 (pr2 ϕ)).
      * apply (pr2 (pr2 ϕ)).
      * apply pathsinv0, P.
        -- etrans. apply pathsinv0, functor_comp.
          apply maponpaths, (pr1 (pr2 ϕ')).
        -- apply (pr2 (pr2 ϕ')).
    + apply dirprod_paths.
      * apply homset_property.
      * apply homset_property.
  Defined.

  Definition iscontr_reluniv_mor_ϕ
             (ff_J : fully_faithful J)
             {u1 u2 : relative_universe J}
             (mor : relative_universe_mor u1 u2)
             (X : C) (f : J X --> U u1)
    : iscontr (reluniv_mor_ϕ mor X f).
  Proof.
    apply iscontraprop1.
    apply isaprop_reluniv_mor_ϕ.
    - apply fully_faithful_implies_full_and_faithful, ff_J.
    - apply reluniv_mor_ϕ_of, ff_J.
  Defined.

  Definition reluniv_mor_with_ϕ
             (u1 u2 : relative_universe J)
    : UU
    := ∑ (mor : relative_universe_mor u1 u2),
       ∏ (X : C) (f : J X --> U u1), reluniv_mor_ϕ mor X f.

  Lemma reluniv_ϕ_π_eq_π
        {C' : category}
        {X : C'} {F : Type} {P : F → C'}
        (f g : F)
        (π : ∏ (k : F), P k --> X)
        (ϕ : ∏ (k : F) (fk : f = k), P f --> P k)
        (ϕ_f : ϕ f (idpath f) = identity _)
    : ∏ (fg : f = g), ϕ g fg ;; π g = π f.
  Proof.
    intros gf.
    use (paths_rect _ _ (λ k fk, ϕ k fk ;; π k = π f) _ _ gf). simpl.
    etrans. apply maponpaths_2, ϕ_f.
    apply id_left.
  Defined.

  Definition reluniv_mor_with_ϕ_id
             (u : relative_universe J)
    : reluniv_mor_with_ϕ u u.
  Proof.
    use tpair.
    - apply gen_reluniv_mor_id.
    - intros X f.
      use tpair.
      + apply idtoiso.
        apply maponpaths, pathsinv0, id_right.
      + use make_dirprod.
        * apply (reluniv_ϕ_π_eq_π _ _ _ (λ _ fk, pr1 (idtoiso (maponpaths (Xf u X) fk)))).
          apply idpath.
        * unfold has_reluniv_mor_axiom_ϕ_Q.
          apply pathsinv0. etrans. apply id_right. apply pathsinv0.
          apply (reluniv_ϕ_π_eq_π _ _ _ (λ _ fk, # J (pr1 (idtoiso (maponpaths (Xf u X) fk))))).
          apply functor_id.
  Defined.

  Definition reluniv_mor_with_ϕ_comp
             (a b c : relative_universe J)
             (g : reluniv_mor_with_ϕ a b)
             (h : reluniv_mor_with_ϕ b c)
    : reluniv_mor_with_ϕ a c.
  Proof.
    use tpair.
    - apply (gen_reluniv_mor_comp _ _ _ _ _ (pr1 g) (pr1 h)).
    - intros X f.
      use tpair.
      + unfold reluniv_mor_ϕ_data.
        set (ϕ1 := pr1 (pr2 g X f)).
        set (ϕ2 := pr1 (pr2 h X (f ;; F_U (pr1 g)))).
        eapply compose. apply (ϕ1 ;; ϕ2).
        apply idtoiso.
        apply maponpaths, assoc'.
      + use make_dirprod.
        * set (ϕ_π1 := pr1 (pr2 (pr2 g X f))).
          set (ϕ_π2 := pr1 (pr2 (pr2 h X (f ;; F_U (pr1 g))))).
          etrans. apply assoc'.
          etrans. apply maponpaths.
          apply (reluniv_ϕ_π_eq_π _ _ _ (λ _ fk, pr1 (idtoiso (maponpaths (Xf _ X) fk)))).
          apply idpath.
          etrans. apply assoc'.
          etrans. apply maponpaths, ϕ_π2.
          apply ϕ_π1.
        * set (ϕ_Q1 := pr2 (pr2 (pr2 g X f))).
          set (ϕ_Q2 := pr2 (pr2 (pr2 h X (f ;; F_U (pr1 g))))).
          unfold has_reluniv_mor_axiom_ϕ_Q in *.
          etrans. apply maponpaths_2, functor_comp.
          etrans. apply maponpaths_2, maponpaths_2, functor_comp.
          etrans. apply assoc'.
          etrans. apply maponpaths.
          apply (reluniv_ϕ_π_eq_π _ _ _ (λ _ fk, # J (pr1 (idtoiso (maponpaths (Xf _ X) fk))))).
          apply functor_id.
          etrans. apply assoc'.
          etrans. apply maponpaths, ϕ_Q2.
          etrans. apply assoc.
          etrans. apply maponpaths_2, ϕ_Q1.
          apply assoc'.
  Defined.

  Definition reluniv_mor_with_ϕ_eq_faithful
             (u1 u2 : relative_universe J)
             (g h : reluniv_mor_with_ϕ u1 u2)
             (e_Ũ : F_Ũ (pr1 g) = F_Ũ (pr1 h))
             (e_U : F_U (pr1 g) = F_U (pr1 h))
             (f_J : faithful J)
    : g = h.
  Proof.
    use total2_paths_f.
    - use gen_reluniv_mor_eq.
      + apply e_Ũ.
      + apply e_U.
    - apply impred_isaprop. intros X.
      apply impred_isaprop. intros f.
      apply isaprop_reluniv_mor_ϕ.
      apply f_J.
  Defined.

  Definition reluniv_with_ϕ_Xf_compat
             {u1 u2 : relative_universe J}
             {g h : relative_universe_mor u1 u2}
             (e_U : F_U g = F_U h)
    : ∏ (X : C) (f : J X --> U u1),
      Xf u2 X (f ;; F_U g) --> Xf u2 X (f ;; F_U h).
  Proof.
    intros X f.
    apply idtoiso, maponpaths, maponpaths.
    apply e_U.
  Defined.

  Definition reluniv_mor_with_ϕ_eq
             (u1 u2 : relative_universe J)
             (g h : reluniv_mor_with_ϕ u1 u2)
             (e_Ũ : F_Ũ (pr1 g) = F_Ũ (pr1 h))
             (e_U : F_U (pr1 g) = F_U (pr1 h))
             (e_ϕ : ∏ (X : C) (f : J X --> U u1),
                    pr1 (pr2 g X f) ;; reluniv_with_ϕ_Xf_compat e_U X f
                    = pr1 (pr2 h X f))
    : g = h.
  Proof.
    use total2_paths_f.
    - use gen_reluniv_mor_eq.
      + apply e_Ũ.
      + apply e_U.
    - etrans. use transportf_forall. apply funextsec. intros X.
      etrans. use transportf_forall. apply funextsec. intros f.
      use total2_paths_f.
      + etrans.
        
        set (A := relative_universe_mor u1 u2).
        set (B := λ (a : A), reluniv_mor_ϕ_data a X f).
        set (P := λ (a : A) (b : B a),
                  has_reluniv_mor_axiom_ϕ_π a X f b
                    × has_reluniv_mor_axiom_ϕ_Q a X f b).
        apply (pr1_transportf _ _ P).

        etrans. unfold reluniv_mor_ϕ_data.
        apply (@functtransportf
                 _ _
                 (λ (m : relative_universe_mor u1 u2), Xf u2 X (f ;; F_U m))
                 (λ (c : C), C ⟦ Xf u1 X f, c ⟧)
              ).

        etrans. apply pathsinv0, idtoiso_postcompose.
        
        apply pathsinv0.
        etrans. apply pathsinv0, e_ϕ.
        apply maponpaths.

        unfold reluniv_with_ϕ_Xf_compat.
        apply pathsinv0.
        etrans. apply maponpaths, maponpaths.
        apply pathsinv0.
        apply (@maponpathscomp
               _ _ _ _ _
               (λ (m : relative_universe_mor u1 u2), f ;; F_U m)
               (Xf u2 X)
            ).
        apply maponpaths, maponpaths, maponpaths.
        etrans. apply pathsinv0.
        apply (@maponpathscomp
                 _ _ _ _ _
                 (λ (m : relative_universe_mor u1 u2), F_U m)
              (compose f)).
        apply maponpaths.
        apply homset_property.
      + apply dirprod_paths.
        * apply homset_property.
        * apply homset_property.
  Defined.

  Definition reluniv_with_ϕ_ob_mor : precategory_ob_mor
    := make_precategory_ob_mor
         (relative_universe J) reluniv_mor_with_ϕ.

  Definition reluniv_with_ϕ_precategory_data : precategory_data.
  Proof.
    apply (make_precategory_data reluniv_with_ϕ_ob_mor).
    - apply reluniv_mor_with_ϕ_id.
    - apply reluniv_mor_with_ϕ_comp.
  Defined.

  Definition reluniv_ϕ_idtoiso_pre_post
             (u1 u2 : relative_universe J)
             (mor : relative_universe_mor u1 u2)
             (ϕ : ∏ (X : C) (f : J X --> U u1), reluniv_mor_ϕ mor X f)
             (X : C)
             (f g : J X --> U u1)
             (e_fg : f = g)
             (e_fg' : f ;; F_U mor = g ;; F_U mor)
    : idtoiso (! maponpaths (Xf u1 X) e_fg)
              ;; pr1 (ϕ X f)
              ;; idtoiso (maponpaths (Xf u2 X) e_fg')
      = pr1 (ϕ X g).
  Proof.
    assert (e_e : e_fg' = maponpaths (postcompose (F_U mor)) e_fg). { apply homset_property. }
    rewrite e_e. (* FIXME: is this ok? *)
    use (paths_rect
           _ _
           (λ k e_fk,
            idtoiso (! maponpaths (Xf u1 X) e_fk)
              ;; pr1 (ϕ X f)
              ;; idtoiso (maponpaths (Xf u2 X) (maponpaths (postcompose (F_U mor)) e_fk))
            = pr1 (ϕ X k)) _ _ e_fg).
    simpl.
    etrans. apply id_right.
    apply id_left.
  Defined.

  Definition reluniv_with_ϕ_precategory_axioms
    : is_precategory reluniv_with_ϕ_precategory_data.
  Proof.
    use make_is_precategory_one_assoc.
    - intros u1 u2 mor.
      use reluniv_mor_with_ϕ_eq.
      + apply id_left.
      + apply id_left.
      + intros X f. cbn.
        unfold reluniv_with_ϕ_Xf_compat.
        etrans. apply assoc'.
        etrans. apply maponpaths, pathsinv0, idtoiso_concat_pr.
        etrans. apply maponpaths_2, maponpaths_2.
        apply maponpaths, maponpaths, maponpathsinv0.
        etrans. apply maponpaths, maponpaths, maponpaths.
        apply pathsinv0, maponpathscomp0.
        apply reluniv_ϕ_idtoiso_pre_post.
    - intros u1 u2 mor.
      use reluniv_mor_with_ϕ_eq.
      + apply id_right.
      + apply id_right.
      + intros X f. cbn.
        etrans. apply assoc'.
        etrans. apply maponpaths, pathsinv0, idtoiso_concat_pr.
        etrans. apply assoc'.
        etrans. apply maponpaths, pathsinv0, idtoiso_concat_pr.
        
        etrans. 2: apply id_right.
        apply maponpaths.
        apply idtoiso_eq_idpath.

        etrans. apply pathsinv0, maponpaths, maponpathscomp0.
        etrans. apply pathsinv0, maponpathscomp0.
        apply pathsinv0.
        etrans. apply pathsinv0. apply PartA.maponpaths_idpath.
        apply maponpaths.
        apply homset_property.
    - intros a b c d g h k.
      use reluniv_mor_with_ϕ_eq.
      + apply assoc.
      + apply assoc.
      + intros X f. cbn.

        (* Oversimplified version of the equation:

           g f ; ( h (f;g) ; k ((f;g);h) ; idtoiso ) ; idtoiso ; compat
           =
           g f ; h (f;g) ; idtoiso ; k (f;(g;h)) ; idtoiso
        *)

        (* Step 1: get rid of (g h) *)
        etrans. apply assoc'.
        etrans. apply assoc'.
        apply pathsinv0.
        etrans. apply assoc'.
        etrans. apply assoc'.
        etrans. apply assoc'.
        apply maponpaths.

        (* Oversimplified version of the equation:

           h (f;g) ; k (f;g;h) ; idtoiso ; idtoiso ; compat
           =
           h (f;g) ; idtoiso ; (k (f;(g;h)) ; idtoiso)
        *)

        (* Step 2: get rid of h (f;g) *)
        apply pathsinv0.
        etrans. apply assoc'.
        etrans. apply assoc'.
        apply maponpaths.

        (* Oversimplified version of the equation:

           k (f;g;h) ; idtoiso ; idtoiso ; compat
           =
           idtoiso ; (k (f;(g;h)) ; idtoiso)
        *)

        (* Step 3: change k (f;(g;h)) to k (f;g;h) *)
        apply pathsinv0.
        etrans. apply maponpaths, maponpaths_2, pathsinv0.
        apply (reluniv_ϕ_idtoiso_pre_post
                 _ _ _ _ X _ _
                 (assoc' _ _ _)
                 (maponpaths (λ k, k ;; _) (assoc' _ _ _))).

        (* Oversimplified version of the equation:

           idtoiso ; (idtoiso ; k (f;g;h) ; idtoiso ; idtoiso)
           =
           k (f;g;h) ; idtoiso ; idtoiso ; compat
        *)
        
        (* Step 4: get rid of idtoiso on the left of k *)
        etrans. apply maponpaths, assoc'.
        etrans. apply maponpaths, assoc'.
        etrans. apply assoc.
        etrans. apply maponpaths_2, pathsinv0, idtoiso_concat_pr.
        etrans. apply maponpaths_2, idtoiso_eq_idpath.
        apply pathsinv0r.
        etrans. apply id_left.
        
        (* Oversimplified version of the equation:

           k (f;g;h) ; (idtoiso ; idtoiso)
           =
           k (f;g;h) ; idtoiso ; idtoiso ; compat
        *)
        
        (* Step 5: get rid of k *)
        apply maponpaths.
        
        (* Oversimplified version of the equation:

           idtoiso ; idtoiso
           =
           idtoiso ; idtoiso ; compat
        *)
        
        (* Step 6: reduce equality of idtoiso to equality of paths *)
        etrans. apply pathsinv0, idtoiso_concat_pr.
        etrans. 2: { apply maponpaths, idtoiso_concat_pr. }
        etrans. 2: { apply idtoiso_concat_pr. }
        apply maponpaths, maponpaths, pathsinv0.

        (* Step 7: factor out Xf d X *)
        etrans. apply pathsinv0, maponpaths, maponpathscomp0.
        etrans. apply pathsinv0, maponpathscomp0.
        apply pathsinv0.
        etrans. apply pathsinv0, maponpathscomp0.
        apply maponpaths.

        (* Step 8: complete the proof *)
        apply homset_property.
  Defined.

  Definition reluniv_with_ϕ_precat : precategory
    := ( reluniv_with_ϕ_precategory_data ,, reluniv_with_ϕ_precategory_axioms ).

  Definition isaset_reluniv_mor_with_ϕ
             (u1 u2 : relative_universe J)
    : isaset (reluniv_mor_with_ϕ u1 u2).
  Proof.
    apply isaset_total2.
    - apply isaset_gen_reluniv_mor.
    - intros mor.
      apply impred_isaset. intros X.
      apply impred_isaset. intros f.
      apply isaset_total2.
      + apply homset_property.
      + intros ϕ.
        apply isasetaprop.
        apply isapropdirprod.
        * apply homset_property.
        * apply homset_property.
  Defined.

  Definition reluniv_with_ϕ_has_homsets : has_homsets reluniv_with_ϕ_precat.
  Proof.
    unfold has_homsets.
    intros a b.
    apply isaset_reluniv_mor_with_ϕ.
  Defined.

  Definition reluniv_with_ϕ_cat : category
    := ( reluniv_with_ϕ_precat ,, reluniv_with_ϕ_has_homsets ).

End RelUniv_ϕ_Cat.

End RelUniv.

(** * Functors of relative universe categories *)

(** ** Lax commutative squares *)

Section Comm_Squares.
(* TODO: perhaps it would be better to unify this with the displayed arrow category. *)

Context {C : precategory}.
  
Definition comm_square
      {c c' : C} (f : c --> c')
      {d d' : C} (g : d --> d')
  := ∑ (hk : c --> d × c' --> d'), (pr1 hk ;; g = f ;; pr2 hk). 

Definition dom_comm_square
      {c c' : C} {f : c --> c'}
      {d d' : C} {g : d --> d'}
    : comm_square f g -> c --> d
  := (@funcomp _ _ (fun _ => _) pr1 pr1).

Definition cod_comm_square
      {c c' : C} {f : c --> c'}
      {d d' : C} {g : d --> d'}
    : comm_square f g -> c' --> d'
  := (@funcomp _ _ _ pr1 (@pr2 _ (fun _ => _))).

Definition commutes_comm_square
      {c c' : C} {f : c --> c'}
      {d d' : C} {g : d --> d'}
    (hk : comm_square f g)
  : dom_comm_square hk ;; g = f ;; cod_comm_square hk
:= pr2 hk.

End Comm_Squares.

Section Functor_Squares.

(* Start by defining “pre-functor-squares”, with no commutativity,
  so that we can have a single pair of access functions [dom_functor], 
  [cod_functor] which can (via coercions) be used for lax-, colax-, and
  pseudo-commutative squares alike. *)

Definition pre_functor_square 
    {C D : precategory} (J : C ⟶ D)
    {C' D' : precategory} (J' : C' ⟶ D')
  : UU
:= (functor C C' × functor D D').

Definition dom_functor 
    {C D : precategory} {J : C ⟶ D}
    {C' D' : precategory} {J' : C' ⟶ D'}
  : pre_functor_square J J' -> C ⟶ C'
:= pr1.

Definition cod_functor 
    {C D : precategory} {J : C ⟶ D}
    {C' D' : precategory} {J' : C' ⟶ D'}
  : pre_functor_square J J' -> D ⟶ D'
:= pr2.

Definition lax_functor_square
    {C D : precategory} (J : functor C D)
    {C' D' : precategory} (J' : functor C' D')
  : UU
:= ∑ (FG : pre_functor_square J J'),
     nat_trans ((dom_functor FG) ∙ J')
               (J ∙ (cod_functor FG)).

Coercion pre_functor_square_of_lax_functor_square
    {C D : precategory} {J : functor C D}
    {C' D' : precategory} {J' : functor C' D'}
  : lax_functor_square J J' -> pre_functor_square J J'
:= pr1.

Definition make_lax_functor_square
    {C D : precategory} {J : C ⟶ D}
    {C' D' : precategory} {J' : C' ⟶ D'}
    (F : C ⟶ C') (G : D ⟶ D') (α : nat_trans (F ∙ J') (J ∙ G))
  : lax_functor_square J J'
:= ((F,G) ,, α).

Definition commutes_lax_functor_square
    {C D : precategory} {J : C ⟶ D}
    {C' D' : precategory} {J' : C' ⟶ D'}
    (FG : lax_functor_square J J')
  : nat_trans _ _
:= pr2 FG.

End Functor_Squares.

Section Relative_Universe_Functor.

Context {C D : category} {J : functor C D} (U : relative_universe J)
        {C' D' : category} {J' : functor C' D'} (U' : relative_universe J')
        (FGα : lax_functor_square J J').

Definition relative_universe_functor : UU.
Proof.
  set (F := dom_functor FGα).
  set (G := cod_functor FGα).
  set (α := commutes_lax_functor_square FGα).
  simple refine ((∑ (t : _) (ϕ : _), _ × _) × _).
  - (* t : comparison square between the universes *)
    exact (comm_square (# G (mor U)) (mor U')).
  - (* ϕ : comparison maps between “context extensions” *)
    refine (forall (X:C) (f : J X --> base U), F _ --> _).
    + exact (fpb_ob (U X f)).
    + refine (fpb_ob (U' (F X) _)).
      refine (_ ;; cod_comm_square t).
      refine (_ ;; # G f).
      exact (α _).
  - refine (forall (X:C) (f : J X --> base U), _ × _).
    + (* ϕ is over the base *)
      exact (ϕ X f ;; fp _ = # F (fp _)).
    + (* ϕ commutes with the canonical pullback morphism *)
      exact (#J' (ϕ X f) ;; (fq _)
             = α (fpb_ob (U X f)) ;; #G (fq _) ;; dom_comm_square t).
  - (* ϕ is natural *)
    (* TODO: give this, once we have added the missing functoriality condition in the definition of relative universes. *)
    exact unit.
  - (* G preserves the canonical pullbacks *)
    refine (forall (X:C) (f : J X --> base U),
                isPullback (functor_on_square _ _ G _)).
    exact (pr1 (pr2 (U X f))). (* TODO: access functions for [commutes_and_is_pullback] and [fpullback] ! *)
Defined.

End Relative_Universe_Functor.


Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.All.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheory.

(** * The total type of morphisms of a precategory *)

Section Mor_Total.

Definition mor_total (C : precategory) : UU
  := ∑ (ab : C × C), C⟦pr2 ab, pr1 ab⟧.

Definition morphism_as_total {C : precategory} {a b : C} (f : a --> b)
  : mor_total C.
Proof.
  exists (b,,a).
  exact f.
Defined.

Definition source {C} (X : mor_total C) : C := pr2 (pr1 X).
Definition target {C} (X : mor_total C) : C := pr1 (pr1 X).
Definition morphism_from_total {C} (X : mor_total C)
  : C ⟦source X, target X⟧
  := pr2 X.
Coercion morphism_from_total : mor_total >-> precategory_morphisms.

Definition functor_on_mor_total {C D : precategory} (F : functor C D) 
           (p : mor_total C) : mor_total D.
Proof.
  exists (F (pr1 (pr1 p)) ,, F (pr2 (pr1 p)) ).
  exact (#F p).
Defined.

Definition isweq_left_adj_equivalence_on_mor_total
    {C D : category} (F : functor C D)
    (isC : is_univalent C) (isD : is_univalent D)
    (H : adj_equivalence_of_cats F) 
  : isweq (functor_on_mor_total F).
Proof.
  use (gradth _ _ _ _ ).
  - apply (functor_on_mor_total (adj_equivalence_inv H)).
  - intro p.
    use total2_paths_f.
    + cbn. destruct p as [[a b] f].
      apply pathsdirprod; cbn. 
      * apply (isotoid _ isC). 
        apply z_iso_inv_from_z_iso, (unit_pointwise_z_iso_from_adj_equivalence H).
      * apply (isotoid _ isC).
        apply z_iso_inv_from_z_iso, (unit_pointwise_z_iso_from_adj_equivalence H).
    + cbn. destruct p as [[a b] f]. cbn in *.
      etrans. apply (transportf_pair (λ x : C × C, C ⟦ pr2 x, pr1 x ⟧)).
      cbn.
      rewrite transportf_isotoid.
      rewrite transportf_isotoid'.
      cbn. (*unfold precomp_with. rewrite id_right.*)
      rewrite assoc.
      assert (XR := nat_trans_ax (unit_from_are_adjoints (pr2 (pr1 H)))).
      cbn in XR. rewrite <- XR.
      rewrite <- assoc. 
      etrans. apply maponpaths.
      apply (z_iso_inv_after_z_iso (unit_pointwise_z_iso_from_adj_equivalence H a)).
      apply id_right.
    - intro p.
    use total2_paths_f.
    + cbn. destruct p as [[a b] f].
      apply pathsdirprod; cbn. 
      * apply (isotoid _ isD). 
        apply (counit_pointwise_z_iso_from_adj_equivalence H).
      * apply (isotoid _ isD).
        apply (counit_pointwise_z_iso_from_adj_equivalence H).
    + cbn. destruct p as [[a b] f]. cbn in *.
      etrans. apply (transportf_pair (λ x : D × D, D ⟦ pr2 x, pr1 x ⟧)).
      cbn.
      rewrite transportf_isotoid.
      rewrite transportf_isotoid'.
      cbn.
      assert (XR := nat_trans_ax (counit_from_are_adjoints (pr2 (pr1 H)))).
      cbn in XR. rewrite XR. clear XR.
      rewrite assoc. 
      etrans. apply maponpaths_2.
      apply (z_iso_after_z_iso_inv (counit_pointwise_z_iso_from_adj_equivalence H _)).
      apply id_left.
Defined.

Definition isweq_equivalence_on_mor_total {C D : category}
           (isC : is_univalent C) (isD : is_univalent D)
           (F : functor C D) (G : functor D C)
           (eta : z_iso (C:= [_ , _ ]) (functor_identity C) (F ∙ G))
           (eps : z_iso (C:= [_ , _ ]) (G ∙ F) (functor_identity D))
: isweq (functor_on_mor_total F).
Proof.
  use (gradth _ _ _ _ ).
  - apply (functor_on_mor_total G).
  - intro p.
    use total2_paths_f.
    + cbn. destruct p as [[a b] f].
      apply pathsdirprod; cbn. 
      * apply (isotoid _ isC). 
        apply z_iso_inv_from_z_iso. apply (z_iso_ob eta).
      * apply (isotoid _ isC).
        apply z_iso_inv_from_z_iso. apply (z_iso_ob eta).
    + cbn. destruct p as [[a b] f]. cbn in *.
      etrans. apply (transportf_pair (λ x : C × C, C ⟦ pr2 x, pr1 x ⟧)).
      cbn.
      rewrite transportf_isotoid.
      rewrite transportf_isotoid'.
(*      cbn. unfold precomp_with. rewrite id_right. *)
      rewrite assoc. assert (XR := nat_trans_ax (pr1 eta)).
      cbn in XR. rewrite <- XR.
      rewrite <- assoc.
      etrans. apply maponpaths.
      apply (nat_trans_inv_pointwise_inv_after_z_iso _ _ C _ _ (pr1 eta)).
      apply id_right.
  - intro p.
    use total2_paths_f.
    + cbn. destruct p as [[a b] f].
      apply pathsdirprod; cbn. 
      * apply (isotoid _ isD). 
        apply (z_iso_ob eps).
      * apply (isotoid _ isD).
        apply (z_iso_ob eps).
    + cbn. destruct p as [[a b] f]. cbn in *.
      etrans. apply (transportf_pair (λ x : D × D, D ⟦ pr2 x, pr1 x ⟧)).
      cbn.
      rewrite transportf_isotoid.
      rewrite transportf_isotoid'.
      cbn. unfold precomp_with. 
      assert (XR := nat_trans_ax (pr1 eps)).
      cbn in XR. rewrite XR. clear XR.
      rewrite assoc. 
      etrans. apply maponpaths_2.
      apply (nat_trans_inv_pointwise_inv_before_z_iso _ _ D  _ _ (pr1 eps)).
      apply id_left.
Defined.

End Mor_Total.


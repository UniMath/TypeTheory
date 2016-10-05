
(**

 Ahrens, Lumsdaine, Voevodsky, 2015 - 2016

*)

Require Import UniMath.Foundations.Basics.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.
Require Import TypeTheory.ALV1.RelUnivStructure.

Set Automatic Introduction.

Local Notation "[ C , D ]" := (functorPrecategory C D).

Section fix_category.

Variable C : Precategory.

Let RC := Rezk_completion C (homset_property _).
Let hsRCop : has_homsets RC^op := has_homsets_opp (homset_property _).

Local Notation "'YoR'" := (Yo : functor RC (preShv _)).

Hypothesis X : @relative_universe_structure C _ Yo.

Let YoR_ff : fully_faithful YoR := yoneda_fully_faithful _ (homset_property _).

(* TODO: [pr2 RC], really?  Doens’t [category] have an access function for the [is_category] part? *)
Definition R1 := rel_univ_struct_functor Yo X YoR YoR_ff (pr2 RC).

(* TODO: should preShv be defined as a [category]?  Fine provided there is a coercion [category] >-> [Precategory]. *)
Lemma is_category_preShv D : is_category (preShv D).
Proof.
    apply (is_category_functor_category _ _ is_category_HSET).
Defined.

Definition R2 :=  R1 (is_category_preShv RC) (Rezk_eta _ _ ).

Definition ext : functor (preShv C) (preShv RC).
Proof.
  set (T:= Rezk_op_adj_equiv C (homset_property _) HSET is_category_HSET).
  apply (equivalences.right_adjoint (pr1 T)).
Defined.

Let R3 := R2 ext.
  

Definition fi : iso (C:=[C, preShv RC])
          (functor_composite Yo ext)
          (functor_composite (Rezk_eta C (homset_property _)) YoR).
Proof.
  set (T:= @iso_from_fully_faithful_reflection _ _ 
             (pre_composition_functor C^op _ HSET hsRCop has_homsets_HSET 
                                           (functor_opp (Rezk_eta C (homset_property _))))
      ).
  set (XTT:= pre_comp_rezk_eta_opp_is_fully_faithful C (homset_property _) HSET is_category_HSET).
  specialize (T XTT).
  set (XR := iso_from_iso_with_postcomp).
  apply (XR _ _ _ (functor_category_has_homsets _ _ _ )
                  (functor_category_has_homsets _ _ _ )  _ _ _ XTT).
  eapply iso_comp.
     apply functor_assoc_iso.
  eapply iso_comp.
     eapply functor_precomp_iso.
     apply counit_iso_from_adj_equivalence_of_precats.
  eapply iso_comp.
    apply functor_comp_id_iso.

  exists (yoneda_functor_precomp_nat_trans _ _ _ _ _ ).
  apply functor_iso_if_pointwise_iso.
    intro c. apply is_iso_yoneda_functor_precomp.
    apply Rezk_eta_fully_faithful.
Defined.

Let R4 := R3 fi (pr2 fi).
Let R5 := R4 (Rezk_eta_essentially_surjective _ _ ).
Let R6 := R5 (right_adj_equiv_is_ff _ _ _ _ ).

Lemma preserves_pullbacks_ext
  : maps_pb_squares_to_pb_squares (preShv C) (preShv RC) ext.
Proof.
  intros ? ? ? ? ? ? ? ? ? ?.
  apply isPullback_image_square.
  apply functor_category_has_homsets.
  apply right_adj_equiv_is_ff.
  apply right_adj_equiv_is_ess_sur.
  assumption.
Defined.

Definition Rezk_on_RelUnivYoneda := R6 preserves_pullbacks_ext.
Print Assumptions Rezk_on_RelUnivYoneda.

End fix_category.


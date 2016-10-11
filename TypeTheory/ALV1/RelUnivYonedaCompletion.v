(**
  [TypeTheory.ALV1.RelUnivYonedaCompletion]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(** This file provides the result: given a universe in [preShv C] relative to the Yoneda embedding [ Yo : C -> preShv C ], this transfers to a similar relative universe in [ preShv (RC C) ]. i.e. on the Rezk-completion of [C]. *)
Require Import UniMath.Foundations.Basics.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.
Require Import TypeTheory.ALV1.RelativeUniverses.

Set Automatic Introduction.

(** * Instantiating the data and hypotheses of transfer of relative universes to Yoneda *)

Local Notation "[ C , D ]" := (functorPrecategory C D).

Section fix_category.

Variable C : Precategory.

Let RC := Rezk_completion C (homset_property _).
Let hsRCop : has_homsets RC^op := has_homsets_opp (homset_property _).

Local Notation "'YoR'" := (Yo : functor RC (preShv _)).

Hypothesis X : @relative_universe C _ Yo.

Let YoR_ff : fully_faithful YoR := yoneda_fully_faithful _ (homset_property _).

(** ** The right vertical functor *)

Definition ext : functor (preShv C) (preShv RC).
Proof.
  set (T:= Rezk_op_adj_equiv C (homset_property _) HSET is_category_HSET).
  apply (equivalences.right_adjoint (pr1 T)).
Defined.
  
(** ** The natural isomorphism *)

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

(** ** Right vertical functor preserves pullbacks *)

(* TODO: should be an instance of “right adjoints preserve pullbacks”. *)
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

(** ** The instantiation *)

Definition Rezk_on_RelUnivYoneda : relative_universe
  ((yoneda RC (homset_property RC) : functor RC (preShv RC))
   :
   functor RC (preShv RC)).
Proof.
  cbn.
  use (transfer_of_rel_univ_with_ess_surj
         Yo 
         X 
         YoR 
         (Rezk_eta _ _ )
         ext
         fi
         (pr2 fi)
         preserves_pullbacks_ext
         (Rezk_eta_essentially_surjective _ _ )
         RC
         YoR_ff
         (right_adj_equiv_is_full _ _)
       ).
Defined.

End fix_category.

Print Assumptions Rezk_on_RelUnivYoneda.

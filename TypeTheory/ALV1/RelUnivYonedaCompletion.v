(**
  [TypeTheory.ALV1.RelUnivYonedaCompletion]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(** This file provides the result: given a universe in [preShv C] relative to the Yoneda embedding [ Yo : C -> preShv C ], this transfers to a similar relative universe in [ preShv (RC C) ]. i.e. on the Rezk-completion of [C]. *)
Require Import UniMath.Foundations.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.
Require Import TypeTheory.ALV1.RelativeUniverses.


Set Automatic Introduction.

(** * Instantiating the data and hypotheses of transfer of relative universes to Yoneda *)

Local Notation "[ C , D ]" := (functor_Precategory C D).

Section fix_category.

Variable C : Precategory.

Let RC : category := Rezk_completion C (homset_property _).
Let hsRCop : has_homsets RC^op := has_homsets_opp (homset_property _).

Local Notation "'YoR'" := (Yo : functor RC (preShv _)).

Definition precomp_with_Rezk_eta_op : preShv RC ⟶ preShv C.
Proof.
  apply (pre_composition_functor C^op
           (Rezk_completion C (homset_property C))^op HSET
           (has_homsets_opp
              (pr2 (pr2 (Rezk_completion C (homset_property C)))))
           (pr2 is_category_HSET)
           (functor_opp (Rezk_eta C (homset_property C)))).
Defined.

Let YoR_ff : fully_faithful YoR := yoneda_fully_faithful _ (homset_property _).

Definition adj_equiv_C : adj_equivalence_of_precats precomp_with_Rezk_eta_op.
Proof.
  apply Rezk_op_adj_equiv.
Defined.

(** ** The right vertical functor *)

Definition ext : functor (preShv C) (preShv RC).
Proof.
  apply (right_adjoint adj_equiv_C).
Defined.

Definition has_homsets_preShv X : has_homsets (preShv X).
Proof.
  apply functor_category_has_homsets.
Defined.


Definition epsinv : iso (C:=[ _ , _ , (has_homsets_preShv _ )]) 
                     (functor_identity (preShv C)) (ext ∙ precomp_with_Rezk_eta_op).
Proof.
  set (XR':= (counit_iso_from_adj_equivalence_of_precats (has_homsets_preShv _ ) adj_equiv_C)).
  apply iso_inv_from_iso.
  apply XR'.
Defined.

Definition etainv : iso (C:=[ _ , _ , (has_homsets_preShv _ )]) 
                        (precomp_with_Rezk_eta_op ∙ ext) (functor_identity (preShv RC)).
Proof.
  set (XR := (unit_iso_from_adj_equivalence_of_precats (has_homsets_preShv _ ) adj_equiv_C)).
  apply iso_inv_from_iso.
  apply XR.
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

Definition Rezk_on_RelUnivYoneda (X : @relative_universe C _ Yo)
  : relative_universe
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

Search (full _ ).

Definition Rezk_eta_full : full (Rezk_eta C (homset_property C)).
Proof.
  apply full_from_ff.
  apply Rezk_eta_fully_faithful.
Defined.

Lemma is_category_preShv X : is_category (preShv X).
Proof.
  apply is_category_functor_category.
Defined.

Definition Rezk_on_RepMaps : 
  mere_relative_universe (yoneda C (homset_property C)) ≃ mere_relative_universe YoR.
Proof.
  set (XR := @weq_mere_universe_transfer 
               C 
               (preShv C)
               (yoneda C (homset_property C))
               RC
               (preShv RC)
               YoR 
               (Rezk_eta _ _ )
               ext
               fi
               (pr2 fi)
               preserves_pullbacks_ext
               (Rezk_eta_essentially_surjective _ _ ) 
               (right_adj_equiv_is_full _ _)
               Rezk_eta_full
               (is_category_preShv _ )
               (is_category_preShv _ )
               precomp_with_Rezk_eta_op
      ).
  use XR.
  - apply epsinv.
  - apply etainv.
  - apply right_adj_equiv_is_ff.
Defined.

End fix_category.

(* Print Assumptions Rezk_on_RelUnivYoneda. *)

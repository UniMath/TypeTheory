(**
  [TypeTheory.ALV1.Transport_Along_Equivs]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(** This file provides two results:

  Given a universe in [preShv C] relative to the Yoneda embedding [ Yo : C ⟶ preShv C ], 
  and a fully faithful and essentially surjective functor [F : C ⟶ D],
  and [D] is a univalent category, then
  we obtain a universe relative to [Yo : D ⟶ preShv D]

  Furthermore, given a weak equivalence [F : C ⟶ D] as above,
  then we obtain an equivalence of 
  weak universes on [Yo C] and on [Yo D].

  Put differently, weak relative universes (and hence representable maps of presheaves)
  are invariant under weak equivalences, whereas cwf structures
  are not - even though they can be transported along weak equivalences
  in the direction of the underlying functor if the target category is univalent.

  The results of this file could (should, actually) be instantiated 
  in order to obtain the result of ALV1.RelUnivYonedaCompletion.

*)


Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.precomp_ess_surj.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.RelativeUniverses.


(** * Transfer of relative universes to Yoneda along weak equivalence *)

Local Notation "[ C , D ]" := (functor_category C D).

Section fix_category.

(** 
Goal: Transfer a (weak) relative universe from the top to the bottom functor

<<<
  C ------------> preShv C
  |               |  /\
  | F             |  | precomp with F^op
  v               V  |
  D ------------> preShv D

>>>

The right vertical down arrow is obtained as the inverse of the equivalence
given by precomposition with [F^op].
Indeed, since [F], and hence [F^op] is ff and ess surj, so is
precomposition with [F^op].

*)


Context {C D : category}
        (F : functor C D)
        (F_ff : fully_faithful F)
        (F_es : essentially_surjective F).

(** ** The square of functors, and a natural isomorphism *)

Definition Fop_precomp : preShv D ⟶ preShv C.
Proof.
  use (pre_composition_functor C^op D^op HSET _ _ (functor_opp F) ).
  apply has_homsets_opp. apply homset_property.
Defined.

Definition ff_Fop_precomp : fully_faithful Fop_precomp.
Proof.
  apply pre_composition_with_ess_surj_and_fully_faithful_is_fully_faithful.
  + apply opp_functor_essentially_surjective. apply F_es.
  + apply opp_functor_fully_faithful. apply F_ff.
Defined.

Definition es_Fop_precomp : essentially_surjective Fop_precomp.
Proof.
  apply pre_composition_essentially_surjective.
  + apply opp_functor_essentially_surjective. apply F_es.
  + apply opp_functor_fully_faithful. apply F_ff.
Defined.


Definition equiv_Fcomp : adj_equivalence_of_precats Fop_precomp.
Proof.
  apply rad_equivalence_of_precats.
  - apply is_univalent_functor_category.
  - apply ff_Fop_precomp.
  - apply es_Fop_precomp.
Defined.

(** *** The right vertical functor *)

Definition ext : functor (preShv C) (preShv D).
Proof.
  apply (right_adjoint equiv_Fcomp).
Defined.


(** *** The right vertical functor *)

Definition has_homsets_preShv X : has_homsets (preShv X).
Proof.
  apply functor_category_has_homsets.
Defined.


Definition epsinv : iso (C:=[_ , _ , has_homsets_preShv _ ])
                        (functor_identity (preShv C)) (ext ∙ Fop_precomp).
Proof.
  set (XR':= (counit_iso_from_adj_equivalence_of_precats equiv_Fcomp)).
  apply iso_inv_from_iso.
  apply XR'.
Defined.


Definition etainv : iso (C:=[ _ , _ , (has_homsets_preShv _ )]) 
                        (Fop_precomp ∙ ext) (functor_identity (preShv D)).
Proof.
  set (XR := (unit_iso_from_adj_equivalence_of_precats equiv_Fcomp)).
  apply iso_inv_from_iso.
  apply XR.
Defined.

(** *** The natural isomorphism *)

Definition fi : iso (C:=[C, preShv D])
          (functor_composite Yo ext)
          (functor_composite F Yo).
Proof.
  set (T:= @iso_from_fully_faithful_reflection _ _ 
             (pre_composition_functor C^op _ HSET (has_homsets_opp (homset_property _) ) has_homsets_HSET 
                                           (functor_opp (F)))
      ).

  set (XTT := ff_Fop_precomp).
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
    apply F_ff.
Defined.


(** ** Proof of the properties of the functors involved *)

(** *** Right vertical functor preserves pullbacks *)

(* TODO: should be an instance of “right adjoints preserve pullbacks”. *)
Lemma preserves_pullbacks_ext
  : maps_pb_squares_to_pb_squares (preShv C) (preShv D) ext.
Proof.
  intros ? ? ? ? ? ? ? ? ? ?.
  apply isPullback_image_square.
  apply functor_category_has_homsets.
  apply right_adj_equiv_is_ff.
  apply right_adj_equiv_is_ess_sur.
  assumption.
Defined.

(** * Transfer of a relative universe *)

Definition Transfer_of_RelUnivYoneda (Dcat : is_univalent D) (X : @relative_universe C _ Yo)
  : relative_universe
      ((yoneda D (homset_property D) : functor D (preShv D))
       :
         functor D (preShv D)).
Proof.
  cbn.
  use (transfer_of_rel_univ_with_ess_surj
         Yo 
         X 
         Yo
         F
         ext
         fi
         (pr2 fi)
         preserves_pullbacks_ext
         F_es
         Dcat
         (yoneda_fully_faithful _ _ )
         (right_adj_equiv_is_full _ _)
       ).
Defined.



Lemma is_univalent_preShv X : is_univalent (preShv X).
Proof.
  apply is_univalent_functor_category.
Defined.

(** * Transfer of a relative weak universe *)

Definition Transfer_of_WeakRelUnivYoneda : 
  weak_relative_universe (yoneda C (homset_property C)) ≃ 
                         weak_relative_universe (yoneda D (homset_property D)).
Proof.
  set (XR := @weq_weak_relative_universe_transfer 
               C 
               (preShv C)
               (yoneda C (homset_property C))
               D
               (preShv D)
               Yo 
               F
               ext
               fi
               (pr2 fi)
               preserves_pullbacks_ext
               F_es
               (right_adj_equiv_is_full _ _)
               (full_from_ff _ F_ff)
               (is_univalent_preShv _ )
               (is_univalent_preShv _ )
               Fop_precomp
      ).
  use XR.
  - apply epsinv.
  - apply etainv.
  - apply right_adj_equiv_is_ff.
Defined.

End fix_category.

(* *)



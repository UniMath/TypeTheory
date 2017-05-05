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
Require Import TypeTheory.ALV1.Transport_along_Equivs.

Set Automatic Introduction.

(** * Instantiating the hypotheses of transfer of relative universes to Yoneda *)

Local Notation "[ C , D ]" := (functor_Precategory C D).

Section fix_category.

Variable C : Precategory.
Let RC : univalent_category := Rezk_completion C (homset_property _).

Definition Rezk_on_RelUnivYoneda (X : @relative_universe C _ Yo)
  : relative_universe
      ((yoneda RC (homset_property RC) : functor RC (preShv RC))
       :
         functor RC (preShv RC)).
Proof.
  use (Transfer_of_RelUnivYoneda (Rezk_eta C _) ).
  - apply Rezk_eta_fully_faithful.
  - apply Rezk_eta_essentially_surjective.
  - apply univalent_category_is_univalent.
  - apply X.
Defined.

Definition Rezk_eta_full : full (Rezk_eta C (homset_property C)).
Proof.
  apply full_from_ff.
  apply Rezk_eta_fully_faithful.
Defined.

Lemma is_univalent_preShv X : is_univalent (preShv X).
Proof.
  apply is_univalent_functor_category.
Defined.

Definition Rezk_on_WeakRelUnivYo : 
  weak_relative_universe (yoneda C (homset_property C)) 
                         ≃ weak_relative_universe (yoneda RC (homset_property _ ) ).
Proof.
  use (Transfer_of_WeakRelUnivYoneda (Rezk_eta C _ )).
  - apply Rezk_eta_fully_faithful.
  - apply Rezk_eta_essentially_surjective.
Defined.


End fix_category.

(* *) 

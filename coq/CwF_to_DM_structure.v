
Require Import UniMath.Foundations.hlevel2.hSet.
Require Import UniMath.RezkCompletion.total2_paths.

Require Import Systems.Auxiliary.
Require Import Systems.UnicodeNotations.
Require Import Systems.CompCat_structure.
Require Import Systems.cwf_structure.
Require Import Systems.DM_structure.

(* Locally override the notation [ γ ♯ a ], at a higher level,
  to get more informative bracketing when pairing meets composition. *) 
Local Notation "γ # a" := (pairing γ a) (at level 75).


(** * Comprehension pre-precats from pre-cats with families

Every pre-CwF gives rise to a DM precategory.
*)

Section DM_of_CwF.

(* TODO: move the [has_homsets] assumption to the definition of a [pre_cwf]? 
   TODO: discuss namine of [has_homsets]: wouldn’t e.g. [homs_are_sets] be clearer? *)
Context (CC : precategory) (C : cwf_struct CC) (homs_sets : has_homsets CC).

(** Being isomorphic to a dependent projection *)
Definition iso_to_dpr {Γ Γ'} (γ : Γ ⇒ Γ') : UU
  := Σ Δ (A : C⟨Δ⟩) (f : iso (Δ∙A) Γ)(g : iso Δ Γ'),
        f ;; γ = π _ ;; g.

Definition dm_sub_struct_of_CwF : dm_sub_struct CC.
Proof.
  unfold dm_sub_struct.
  intros Γ Γ' γ.
  exact (ishinh (iso_to_dpr γ)).
Defined.

Lemma dm_sub_closed_under_iso_of_CwF : dm_sub_closed_under_iso dm_sub_struct_of_CwF.
Proof.
  unfold dm_sub_closed_under_iso.
  intros Γ Γ' γ Δ Δ' δ f g H.
  unfold dm_sub_struct_of_CwF in γ.
  destruct γ as [γ A]. simpl in H. unfold DM_type in A.
  apply A.
  intro A'.
  apply hinhpr.
  destruct A' as [E [ET [h [k Hhk]]]].
  unfold iso_to_dpr.
  exists E.
  exists ET.
  exists (iso_comp h f).
  exists (iso_comp k g).
  simpl.
  rewrite assoc. rewrite <- Hhk.
  repeat rewrite <- assoc. apply maponpaths.
  apply pathsinv0. assumption.
Qed.

Definition pb_of_DM_of_CwF : pb_of_DM_struct dm_sub_struct_of_CwF.
Proof.
  unfold pb_of_DM_struct.
  intros Γ Γ' γ Δ f.
  destruct γ as [γ A]. simpl.
  (* now we need that Pullbacks are propositions, that is, we need [C] saturated *)
  admit.
Admitted.

  
End DM_of_CwF.


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
  := Σ (A : C⟨Γ'⟩) (f : iso (Γ'∙A) Γ),
        π _ = f ;; γ .

Definition dm_sub_struct_of_CwF : dm_sub_struct CC.
Proof.
  unfold dm_sub_struct.
  intros Γ Γ' γ.
  exact (ishinh (iso_to_dpr γ)).
Defined.

Lemma dm_sub_closed_under_iso_of_CwF : dm_sub_closed_under_iso dm_sub_struct_of_CwF.
Proof.
  unfold dm_sub_closed_under_iso.
  intros Δ Γ γ Δ' δ h H.
  unfold dm_sub_struct_of_CwF in γ.
  destruct γ as [γ A]. simpl in *. unfold DM_type in A.
  apply A.
  intro A'.
  apply hinhpr.
  clear A.
  destruct A' as [A [f TH]].
  unfold iso_to_dpr.
  exists A.
  set (T:= iso_comp f h).
  exists T.
  unfold T. simpl.
  rewrite TH; clear TH.
  rewrite <- assoc. apply maponpaths.
  sym. assumption.
Qed.

(*
Definition q_precwf {Γ} (A : C ⟨ Γ ⟩ ) {Γ'} (f : Γ' ⇒ Γ)
  : (comp_obj  Γ' (A[f])) ⇒ (Γ ∙ A).
Proof.
  set (T:= @pairing _ C).
  apply T with (γ := π _ ;; f).
  refine (transportb (term C (Γ' ∙ (A [f])) ) (reindx_type_comp C _ _ A) _).
  apply gen_elem.
Defined.
*)

Definition pb_of_DM_of_CwF : pb_of_DM_struct dm_sub_struct_of_CwF.
Proof.
  unfold pb_of_DM_struct.
  intros Δ Γ γ Γ' f.
  destruct γ as [γ B]. simpl.
  match goal with | [ |- ?T ] => assert (X : isaprop T) end.
  { admit. (* now we need that Pullbacks are propositions, that is, we need [C] saturated *) }
  unfold DM_type in B. simpl in *.
  unfold dm_sub_struct_of_CwF in B.
  set (T:= hProppair _ X).
  set (T':= B T).
  apply T'.
  unfold T; simpl;
  clear X T T'.
  intro T.
  unfold iso_to_dpr in T.
  destruct T as [A [h e]].
  clear B.
  exists (Γ' ∙ (A[f])).
  exists (π _ ).
  exists (q_precwf _ _ ;; h).
  set (T:= postcomp_pb_with_iso CC homs_sets). eapply T.
  apply is_pullback_reindx_cwf. assumption.
  sym. assumption.
Admitted.

Definition dm_sub_pb_of_CwF : dm_sub_pb CC.
Proof.
  exists dm_sub_struct_of_CwF.
  exact pb_of_DM_of_CwF.
Defined.

Definition dm_closed_under_pb_of_CwF :  dm_closed_under_pb dm_sub_pb_of_CwF.
Proof.
  unfold dm_closed_under_pb.
  intros Γ Γ' γ Δ f.
  unfold DM_type. simpl. unfold dm_sub_struct_of_CwF.
  match goal with | [ |- ?T ] => assert (X : isaprop T) end.
  { apply pr2. }
  set (T:= hProppair _ X).
  destruct γ as [γ H]. simpl in *.
  set (T':= H T).
  apply T'.
  unfold T; simpl;
  clear X T T'.
  intro H'.
  apply hinhpr.
  unfold iso_to_dpr.
  destruct H' as [A [h HT]].
  unfold pb_mor_of_DM. simpl.
  admit.
Admitted.
  
End DM_of_CwF.

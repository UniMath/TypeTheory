
(** 

 Ahrens, Lumsdaine, Voevodsky, 2015

 Contents:

  - Definition of a Display map category from Category with Families
    (requires Pullbacks to be hProps, e.g., as in a saturated precategory

*)


Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.OtherDefs.CwF_Pitts.
Require Import TypeTheory.OtherDefs.DM.

(* Locally override the notation [ γ ♯ a ], at a higher level,
  to get more informative bracketing when pairing meets composition. *) 
Local Notation "γ ## a" := (pairing γ a) (at level 75).

(** * Category with DM from Category with families

*)

Section DM_of_CwF.

(** assumption of [CC] being saturated is essential: we need pullbacks to be propositions *)
Context (CC : precategory) (C : cwf_struct CC) (H : is_univalent CC).

(** Being isomorphic to a dependent projection *)
Definition iso_to_dpr {Γ Γ'} (γ : Γ --> Γ') : UU
  := ∑ (A : C⟨Γ'⟩) (f : iso (Γ'∙A) Γ),
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
  intros Δ Γ γ Δ' δ h HT.
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


Definition pb_of_DM_of_CwF : pb_of_DM_struct dm_sub_struct_of_CwF.
Proof.
  unfold pb_of_DM_struct.
  intros Δ Γ γ Γ' f.
  destruct γ as [γ B]. simpl.
  match goal with | [ |- ?T ] => assert (X : isaprop T) end.
  { apply isofhleveltotal2.
    - apply isaprop_Pullback. assumption.
    - intros. apply isapropishinh.
  }
  unfold DM_type in B. simpl in *.
  unfold dm_sub_struct_of_CwF in B.
  set (T:= make_hProp _ X).
  set (T':= B T).
  apply T'.
  unfold T; simpl;
  clear X T T'.
  intro T.
  unfold iso_to_dpr in T.
  destruct T as [A [h e]].
  clear B.
  unshelve refine (tpair _ _ _ ).
  - unshelve refine (make_Pullback _ _ _ _ _ _ _ ).
    + apply (Γ' ∙ (A{{f}})).
    + apply (q_precwf _ _ ;; h).
    + apply (π _ ). 
    + simpl. unfold dm_sub_struct_of_CwF.
      simpl.
      set (T:= postcomp_pb_with_iso CC (pr2 H)).
      set (T':= T _ _ _ _  (q_precwf A f) _ _ f _ (is_pullback_reindx_cwf (pr2 H) _ _ _ _ )).
      refine (pr1 (T' _ _ _ _ )).
      sym. assumption.
    + 
      set (T:= postcomp_pb_with_iso CC (pr2 H)).
      set (T':= T _ _ _ _  (q_precwf A f) _ _ f _ (is_pullback_reindx_cwf (pr2 H) _ _ _ _ )).
      eapply (pr2 (T' _ _ _ _ )).
  - simpl.
    apply hinhpr.
    unfold iso_to_dpr.
    exists (A{{f}}).
    exists (identity_iso _ ).
    sym. apply id_left.
Defined.


Definition dm_sub_pb_of_CwF : dm_sub_pb CC.
Proof.
  exists dm_sub_struct_of_CwF.
  exact pb_of_DM_of_CwF.
Defined.

Definition  DM_structure_of_CwF :  DM_structure CC.
Proof.
  exists dm_sub_pb_of_CwF.
  exists dm_sub_closed_under_iso_of_CwF.
  intros. apply isapropishinh.
Defined.


End DM_of_CwF.

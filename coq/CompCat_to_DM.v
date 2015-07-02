(** 
 
 Ahrens, Lumsdaine, Voevodsky, 2015

 Contents:

  - Definition of a Category with Display maps from a Comprehension Category
      (assumption of saturatedness needed for pullbacks forming hprop)
*)


Require Import UniMath.RezkCompletion.total2_paths.

Require Import Systems.Auxiliary.
Require Import Systems.UnicodeNotations.
Require Import Systems.CompCat.
Require Import Systems.DM.


(** * Construction of Comprehension precategory from Display map precategory *)

Section CompCat_to_DM.

Variable CC : precategory.
Variable H : is_category CC.  
Variable C : comp_cat_struct CC.

Definition iso_to_dpr {Γ Γ'} (γ : Γ ⇒ Γ') : UU
  := Σ (A : C Γ') (f : iso (Γ'◂ A) Γ),
        dpr_comp_cat _ = f ;; γ .

Definition dm_sub_struct_of_CompCat : dm_sub_struct CC.
Proof.
  unfold dm_sub_struct.
  intros Γ Γ' γ.
  exact (ishinh (iso_to_dpr γ)).
Defined.

Lemma dm_sub_closed_under_iso_of_CompCat : dm_sub_closed_under_iso dm_sub_struct_of_CompCat.
Proof.
  unfold dm_sub_closed_under_iso.
  intros Δ Γ γ Δ' δ h HT.
  unfold dm_sub_struct_of_CompCat in γ.
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

Definition pb_of_DM_of_CompCat : pb_of_DM_struct dm_sub_struct_of_CompCat.
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
  unfold dm_sub_struct_of_CompCat in B.
  set (T:= hProppair _ X).
  set (T':= B T).
  apply T'.
  unfold T; simpl;
  clear X T T'.
  intro T.
  unfold iso_to_dpr in T.
  destruct T as [A [h e]].
  clear B.
  refine (tpair _ _ _ ).
  - refine (tpair _ _ _).
    + exists (Γ' ◂ (A[f])).
      exists (q_comp_cat _ _ ;; h).
      exact (dpr_comp_cat _ ).
    + simpl. unfold dm_sub_struct_of_CompCat.
      simpl.
      set (T:= postcomp_pb_with_iso CC (pr2 H)).
      eapply T.
      apply  reind_pb_comp_cat. 
      sym. assumption.
  - simpl.
    apply hinhpr.
    unfold iso_to_dpr.
    exists (A[f]).
    exists (identity_iso _ ).
    sym. apply id_left.
Defined.

Definition dm_sub_pb_of_CompCat : dm_sub_pb CC.
Proof.
  exists dm_sub_struct_of_CompCat.
  exact pb_of_DM_of_CompCat.
Defined.

Definition DM_structure_of_CompCat : DM_structure CC.
Proof.
  exists dm_sub_pb_of_CompCat.
  exists dm_sub_closed_under_iso_of_CompCat.
  intros. apply isapropishinh.
Defined.
    
End CompCat_to_DM.
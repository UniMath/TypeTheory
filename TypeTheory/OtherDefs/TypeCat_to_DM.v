(** 
 
 Ahrens, Lumsdaine, Voevodsky, 2015

 Contents:

  - Definition of a Category with Display maps from a Comprehension Category
      (assumption of saturatedness needed for pullbacks forming hprop)
*)

Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.
Require Import TypeTheory.Auxiliary.Auxiliary.

Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.OtherDefs.DM.

(** * Construction of Comprehension precategory from Display map precategory *)

Section TypeCat_to_DM.

Variable CC : precategory.
Variable H : is_univalent CC.  
Variable C : typecat_structure CC.

Definition iso_to_dpr {Γ Γ'} (γ : Γ --> Γ') : UU
  := ∑ (A : C Γ') (f : iso (Γ'◂ A) Γ),
        dpr_typecat _ = f ;; γ .

Definition dm_sub_struct_of_TypeCat : dm_sub_struct CC.
Proof.
  unfold dm_sub_struct.
  intros Γ Γ' γ.
  exact (ishinh (iso_to_dpr γ)).
Defined.

Lemma dm_sub_closed_under_iso_of_TypeCat : dm_sub_closed_under_iso dm_sub_struct_of_TypeCat.
Proof.
  unfold dm_sub_closed_under_iso.
  intros Δ Γ γ Δ' δ h HT.
  unfold dm_sub_struct_of_TypeCat in γ.
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

Definition pb_of_DM_of_TypeCat : pb_of_DM_struct dm_sub_struct_of_TypeCat.
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
  unfold dm_sub_struct_of_TypeCat in B.
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
    + apply (Γ' ◂ (A{{f}})).
    + apply (q_typecat _ _ ;; h).
    + apply (dpr_typecat _ ).
    + simpl. unfold dm_sub_struct_of_TypeCat.
      simpl.
      set (T:= postcomp_pb_with_iso CC (pr2 H)).
      refine (pr1 (T _ _ _ _  (q_typecat A f) _ _ f _ _ _ _ _ _ )).
      apply is_symmetric_isPullback. exact (pr2 H).
      apply reind_pb_typecat.
      sym. assumption.
    + 
      set (T:= postcomp_pb_with_iso CC (pr2 H)).
      eapply (pr2 (T _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
 - simpl.
    apply hinhpr.
    unfold iso_to_dpr.
    exists (A{{f}}).
    exists (identity_iso _ ).
    sym. apply id_left.
Defined.

Definition dm_sub_pb_of_TypeCat : dm_sub_pb CC.
Proof.
  exists dm_sub_struct_of_TypeCat.
  exact pb_of_DM_of_TypeCat.
Defined.

Definition DM_structure_of_TypeCat : DM_structure CC.
Proof.
  exists dm_sub_pb_of_TypeCat.
  exists dm_sub_closed_under_iso_of_TypeCat.
  intros. apply isapropishinh.
Defined.
    
End TypeCat_to_DM.

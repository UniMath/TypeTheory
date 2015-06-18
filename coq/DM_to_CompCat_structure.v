
Require Import UniMath.RezkCompletion.total2_paths.

Require Import Systems.Auxiliary.
Require Import Systems.UnicodeNotations.
Require Import Systems.CompCat_structure.
Require Import Systems.DM_structure.


Section DM_to_CompCat.

Variable CC : precategory.
Variable C : DM_structure CC.

Definition comp_cat_struct1_from_DM : comp_cat_struct1 CC.
Proof.
  unfold comp_cat_struct1.
  exists (fun X => Σ Y, DM C Y X).
  refine (tpair _ _ _ ).
  - intros Γ H. exact (pr1 H).
  - intros Γ Γ'γ Δ f.
    exists (pr2 Γ'γ ⋆ f).
    apply pb_DM_of_DM.
Defined.

Definition comp_cat_struct2_from_DM : comp_cat_struct2 comp_cat_struct1_from_DM.
Proof.
  unfold comp_cat_struct2.
  refine (tpair _ _ _ ).
  - intros Γ A; simpl.
    unfold ext_comp_cat. simpl.
    apply (pr2 A).
  - simpl.
    refine (tpair _ _ _ ).
    + intros Γ A Δ f.
      unfold ext_comp_cat; simpl.
      apply pb_arrow_of_arrow.
    + {
        refine (tpair _ _ _ ).
        - intros Γ A Γ' f.
          apply sqr_comm_of_DM.
        - intros. apply isPullback_of_DM. }
Defined.

Definition comp_cat_struct_from_DM : comp_cat_struct CC.
Proof.
  exists comp_cat_struct1_from_DM.
  exact comp_cat_struct2_from_DM.
Defined.

(* this seems to require (at least!) that the objects of the underlying category form a set *)
(*
Lemma is_split_comp_cat_from_DM : is_split_comp_cat comp_cat_struct_from_DM.
Proof.
  repeat split.
  - admit. (* this is probably false when objects don't form a set *)
  - simpl.
    refine (tpair _ _ _ ).
    + unfold reind_comp_cat; simpl.
*)
    
End DM_to_CompCat.
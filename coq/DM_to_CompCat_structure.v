(** 
 
 Ahrens, Lumsdaine, Voevodsky, 2015

 Contents:

  - Definition of a Comprehension precategory from a precategory with Display maps
  
*)


Require Import UniMath.RezkCompletion.total2_paths.

Require Import Systems.Auxiliary.
Require Import Systems.UnicodeNotations.
Require Import Systems.CompCat_structure.
Require Import Systems.DM_structure.


(** * Construction of Comprehension precategory from Display map precategory *)

Section DM_to_CompCat.

Variable CC : precategory.
Variable C : DM_structure CC.



Definition comp_cat_struct1_from_DM : comp_cat_struct1 CC.
Proof.
  unfold comp_cat_struct1.
  exists (DM_over C).
(*  exists (fun X => Σ (Yf : Σ Y, X ⇒ Y), DM_type C (pr2 Yf)). *)
  refine (tpair _ _ _ ).
  - intros Γ H. exact (ob_from_DM_over H).
  - intros Γ Δ'γH Γ' f.
    simpl in *.
    refine (tpair _ _ _ ).
    + exists ( (DM_from_DM_over Δ'γH) ⋆ f).
      apply pb_mor_of_DM.
    + simpl.
      refine (pr2 (pb_DM_of_DM _ _ )).
Defined.

Definition comp_cat_struct2_from_DM : comp_cat_struct2 comp_cat_struct1_from_DM.
Proof.
  unfold comp_cat_struct2.
  refine (tpair _ _ _ ).
  - intros Γ A; simpl.
    unfold ext_comp_cat. simpl.
    unfold comp_cat_struct1_from_DM in A. simpl in *.
    apply (pr2 (pr1 A)).
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

Lemma is_type_saturated_comp_cat_from_DM : is_type_saturated_comp_cat comp_cat_struct_from_DM.
Proof.
  unfold is_type_saturated_comp_cat.
  intro Γ. unfold comp_cat_struct_from_DM.
  simpl.
  unfold ext_comp_cat. simpl.
  unfold dpr_comp_cat. simpl.
  assert (
      (λ A : DM_over C Γ,
      tpair (λ X : CC, X ⇒ Γ) (ob_from_DM_over A) (pr2 (pr1 A)))
      = pr1).
  { apply funextfunax.
    intro x.
    destruct x. simpl.
    destruct t.
    apply idpath.
  }
  rewrite X.
  apply isinclpr1.
  intros. apply (pr2 (pr2 C)).
Qed.  
  
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
(** 
 
 Ahrens, Lumsdaine, Voevodsky, 2015

 Contents:

  - Definition of a Comprehension precategory from a precategory with Display maps
  
*)


Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.limits.pullbacks.

Require Import TypeTheory.Auxiliary.UnicodeNotations.
Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.OtherDefs.DM.
Require Import TypeTheory.Auxiliary.Auxiliary.

(** * Construction of Comprehension precategory from Display map precategory *)

Section DM_to_TypeCat.

Variable CC : precategory.
Variable hs : has_homsets CC. 
Variable C : DM_structure CC.



Definition type_cat_structure1_from_DM : typecat_structure1 CC.
Proof.
  unfold typecat_structure1.
  exists (DM_over C).
(*  exists (fun X => ∑ (Yf : ∑ Y, X --> Y), DM_type C (pr2 Yf)). *)
  refine (tpair _ _ _ ).
  - intros Γ H. exact (ob_from_DM_over H).
  - intros Γ Δ'γH Γ' f.
    simpl in *.
    unshelve refine (tpair _ _ _ ).
    + exists ( (DM_from_DM_over Δ'γH) ⋆ f).
      apply pb_mor_of_DM.
    + simpl.
      refine (pr2 (pb_DM_of_DM _ _ )).
Defined.

Definition type_cat_structure2_from_DM : typecat_structure2 type_cat_structure1_from_DM.
Proof.
  unfold typecat_structure2.
  unshelve refine (tpair _ _ _ ).
  - intros Γ A; simpl.
    unfold ext_typecat. simpl.
    unfold type_cat_structure1_from_DM in A. simpl in *.
    apply (pr2 (pr1 A)).
  - simpl.
    unshelve refine (tpair _ _ _ ).
    + intros Γ A Δ f.
      unfold ext_typecat; simpl.
      apply pb_arrow_of_arrow.
    + {
        unshelve refine (tpair _ _ _ ).
        - intros Γ A Γ' f.
          unshelve refine (sqr_comm_of_DM (( DM_from_DM_over A)) _ ).
        - intros.
          apply is_symmetric_isPullback. { apply hs. }
          refine (@isPullback_of_DM  _ _ _ _ _ _ _ _ ).
          apply hs. }
Defined.

Definition type_cat_struct_from_DM : typecat_structure CC.
Proof.
  exists type_cat_structure1_from_DM.
  exact type_cat_structure2_from_DM.
Defined.

Lemma is_type_saturated_type_cat_from_DM : is_type_saturated_typecat type_cat_struct_from_DM.
Proof.
  unfold is_type_saturated_typecat.
  intro Γ. unfold type_cat_struct_from_DM.
  simpl.
  unfold ext_typecat. simpl.
  unfold dpr_typecat. simpl.
  assert (
      (λ A : DM_over C Γ,
      tpair (λ X : CC, X --> Γ) (ob_from_DM_over A) (pr2 (pr1 A)))
      = pr1).
  { apply funextfun.
    intro x.
    destruct x as [t p]. simpl.
    destruct t; apply idpath.
  }
  rewrite X.
  apply isinclpr1.
  intros. apply (pr2 (pr2 C)).
Qed.  
  
(* this seems to require (at least!) that the objects of the underlying category form a set *)
(*
Lemma is_split_type_cat_from_DM : is_split_type_cat type_cat_struct_from_DM.
Proof.
  repeat split.
  - admit. (* this is probably false when objects don't form a set *)
  - simpl.
    refine (tpair _ _ _ ).
    + unfold reind_type_cat; simpl.
*)
    
End DM_to_TypeCat.

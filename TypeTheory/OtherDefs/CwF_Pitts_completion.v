
(** * From CwFs to univalent CwFs *)
(**
  Contents:

    - goal (not yet complete): transfer of CwF structure along the Rezk-completion construction
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.yoneda.
Require Import UniMath.CategoryTheory.rezk_completion.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.
Require Import TypeTheory.OtherDefs.CwF_Pitts.
Require Import TypeTheory.Categories.category_of_elements.

Local Arguments iso: clear implicits.

(** How to get a functor from RC(C) to D when having one from C to D **)

Definition Rezk_functor (C : category) (D : univalent_category) 
    (F : functor C D) 
  :  functor (Rezk_completion C) D.
Proof.
  set (H:=Rezk_eta_Universal_Property C D  (pr2 D)).
  apply (invmap (make_weq _  H)).
  apply F.
Defined.

(** * Saturating a CwF *)

Section CwF_completion.

Context (CC : category) (C : cwf_struct CC).

(** ** The "type" part of a CwF **)

(** The "type" part is a functor into the opposite of HSET.
    We thus obtain a "type" functor on RC(C) by univ property
**)

Definition type_hSet (Γ : CC) : hSet := make_hSet (C⟨Γ⟩) (cwf_types_isaset _ _ ). 

Definition type_functor_data : functor_data CC (opp_precat HSET).
Proof.
  exists type_hSet.
  intros Γ Γ' γ A. exact (rtype A γ).
Defined.
  
Definition type_is_functor : is_functor type_functor_data.
Proof.
  split; intros; simpl.
  - intros Γ. apply funextfun; intro A. apply reindx_type_id. 
    apply reindx_laws_from_cwf_struct.
  - intros Γ Γ' Γ'' f g. apply funextfun; intro A.
    apply reindx_type_comp.
    apply reindx_laws_from_cwf_struct.
Qed.

Definition type_functor : functor _ _ := tpair _ _ type_is_functor.

Definition RC_type_functor : functor (Rezk_completion CC) (opp_precat HSET).
Proof.  
  apply (Rezk_functor CC (op_unicat HSET_univalent_category)).
  apply type_functor.
Defined.
  
(** ** The "term" part of a CwF **)
(** The "term" part is a functor from the category of elements of "type"
    into (the opposite of) sets.
**)



End CwF_completion.



(** * From preCwFs to CwFs *)
(**
  Contents:

    - not much yet
*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.yoneda.
Require Import UniMath.CategoryTheory.rezk_completion.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.
Require Import TypeTheory.OtherDefs.CwF_Pitts.
Require Import TypeTheory.Categories.category_of_elements.

Set Automatic Introduction.

Arguments iso: clear implicits.

(** How to get a functor from RC(C) to D when having one from C to D **)

Definition Rezk_functor (C : precategory) (hs : has_homsets C) (D : univalent_category) 
    (F : functor C D) 
  :  functor (Rezk_completion C hs) D.
Proof.
  set (H:=Rezk_eta_Universal_Property C hs D  (pr2 D)).
  apply (invmap (weqpair _  H)).
  apply F.
Defined.

(** The opposite precategory of a saturated category is saturated. **)

Definition opp_iso_inv {C : precategory} {a b : C} : iso (opp_precat C) a b → iso C b a.
Proof.
  intro f.
  set (H:= is_z_iso_from_is_iso f (pr2 f)).
  exists (pr1 f).
  apply is_iso_from_is_z_iso.
  exists (pr1 H).
  split.
  - apply (pr2 (pr2 H)).
  - apply (pr1 (pr2 H)).
Defined.

Lemma opp_iso_opp_iso_inv (C : precategory) (a b : C) (f : iso (opp_precat C) a b) : 
   opp_iso (opp_iso_inv f) = f.
Proof.
  apply eq_iso.
  apply idpath.
Qed.

Lemma opp_iso_inv_opp_iso (C : precategory) (a b : C) (f : iso C a b) : 
   opp_iso_inv (opp_iso f) = f.
Proof.
  apply eq_iso.
  apply idpath.
Qed.

Definition weq_opp_iso (C : precategory) (a b : C) : 
  iso C a b ≃ iso (opp_precat C) b a.
Proof.
  exists (opp_iso).
  apply (gradth (@opp_iso _ _ _  ) (@opp_iso_inv _ _ _ )).
  - apply opp_iso_inv_opp_iso.
  - apply opp_iso_opp_iso_inv.
Defined.

Definition isotoid_opp (C : precategory) (H : is_univalent C) (a b : opp_precat C) : 
   weq (a = b) (iso (opp_precat C) a b).
Proof.
  eapply weqcomp.
  - apply weqpathsinv0.
  - eapply weqcomp.
    + apply (weqpair (@idtoiso C b a) (pr1 H b a)).
    + apply weq_opp_iso.
Defined.


Definition is_univalent_opp (C : precategory) (H : is_univalent C) : is_univalent (opp_precat C).
Proof.
  split; intros; simpl in *.
  - set (H1:=@isweqhomot).
    set (H2 := H1 _ _ (isotoid_opp C H a b)).
    apply H2.
    intro t; induction t.
    apply eq_iso; apply idpath.
    apply (pr2 (isotoid_opp C H a b)).
  - intros a b. apply (pr2 H).
Qed.
 
Definition opp_univalent_cat (C : univalent_category) : univalent_category.
Proof.
  exists (opp_precat C).
  apply is_univalent_opp.
  apply (pr2 C).
Defined.


(** * Saturating a CwF *)

Section CwF_completion.

Context (CC : precategory) (C : cwf_struct CC).

(** ** The "type" part of a CwF **)

(** The "type" part is a functor into the opposite of HSET.
    We thus obtain a "type" functor on RC(C) by univ property
**)

Definition type_hSet (Γ : CC) : hSet := hSetpair (C⟨Γ⟩) (cwf_types_isaset _ _ ). 

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

Definition RC_type_functor : functor (Rezk_completion CC (has_homsets_cwf C)) (opp_precat HSET).
Proof.  
  apply (Rezk_functor CC _ (opp_univalent_cat HSET_univalent_category)).
  apply type_functor.
Defined.
  
(** ** The "term" part of a CwF **)
(** The "term" part is a functor from the category of elements of "type"
    into (the opposite of) sets.
**)



End CwF_completion.


(**

 Ahrens, Lumsdaine, Voevodsky, 2015 - 2016

*)

Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.CategoryTheory.UnicodeNotations.

Require Import Systems.Auxiliary.
Require Import Systems.UnicodeNotations.
Require Import Systems.Bicats.Auxiliary.
Require Import Systems.Bicats.Displayed_Precats.
Require Import Systems.Structures.
Require Import Systems.Structures_Cats.
Require Import Systems.Structures_Equiv_Cats.

Local Set Automatic Introduction.
(* only needed since imports globally unset it *)

Section Fix_Context.

Context {C : Precategory}.

Local Notation hsC := (homset_property C).

Local Notation "'Yo'" := (yoneda C hsC).
Local Notation "'Yo^-1'" :=  (invweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ ))).

Local Notation "Γ ◂ A" := (comp_ext _ Γ A) (at level 30).
Local Notation "'Ty'" := (fun X Γ => (TY X : functor _ _) Γ : hSet) (at level 10).

Local Notation Δ := comp_ext_compare.
Local Notation φ := obj_ext_mor_φ.

Theorem is_category_obj_ext
  : is_category (obj_ext_Precat C).
Proof.
  split. Focus 2. apply homset_property.
  intros a b. simpl in *. unfold obj_ext_structure in a, b.
  admit.
  (* Probably the hardest *)
Admitted.

Theorem is_category_families_structure
  : is_category_disp (families_disp_precat C).
Proof.
  apply is_category_disp_from_fibers.
  admit.
  (* Probably also not easy; [isaprop_families_mor] should be helpful. *)
Admitted.


Lemma isaset_qq_morphism_structure (x : obj_ext_structure C) 
  : isaset (qq_morphism_structure x).
Proof.
  apply (isofhleveltotal2 2).
  - apply (isofhleveltotal2 2).
    + do 4 (apply impred; intro).
      apply Precategories.homset_property.
    + intros. do 4 (apply impred; intro).
      apply (isofhleveltotal2 2).
      * apply hlevelntosn.
        apply Precategories.homset_property.
      * intro. apply hlevelntosn.
        apply pullbacks.isaprop_isPullback.
  - intro d. unfold qq_morphism_axioms.
    apply isofhleveldirprod.
    + do 2 (apply impred; intro).
      apply hlevelntosn.
      apply Precategories.homset_property.
    + do 6 (apply impred; intro).
      apply hlevelntosn.
      apply Precategories.homset_property.
Qed. 

Lemma isaprop_iso_disp_qq_morphism_structure 
  (x : obj_ext_Precat C)
  (d d' : (qq_structure_disp_precat C) x)
  : isaprop (iso_disp (identity_iso x) d d').
Proof.
  apply (isofhleveltotal2 1).
  - do 4 (apply impred; intro).
    apply Precategories.homset_property.
  - intro. apply isaprop_is_iso_disp.
Qed.

Lemma qq_structure_eq 
  (x : obj_ext_Precat C)
  (d d' : qq_morphism_structure x)
  (H : ∀ (Γ Γ' : C) (f : Γ' ⇒ Γ) (A : (TY x : functor _ _ ) Γ : hSet), 
           qq d f A = qq d' f A)
  : d = d'.
Proof.
  apply subtypeEquality.
  { intro. apply (@isaprop_qq_morphism_axioms _  (Precategories.homset_property _ )). }
  apply subtypeEquality.
  { intro. do 4 (apply impred; intro). 
           apply isofhleveltotal2.
     + apply Precategories.homset_property.
     + intro. apply pullbacks.isaprop_isPullback.
  } 
  do 4 (apply funextsec; intro).
  apply H.
Defined.

Definition qq_structure_iso_disp_to_id
  (x : obj_ext_Precat C)
  (d d' : (qq_structure_disp_precat C) x)
  : iso_disp (identity_iso x) d d' → d = d'.
Proof.
  intro H. 
  apply qq_structure_eq.
  intros Γ Γ' f A.
  assert (XR := pr1 H); clear H.
  specialize (XR _ _ f A).
  rewrite id_right in XR.
  rewrite id_left in XR.
  etrans. apply XR.
  match goal with [|- Δ ?ee ;; _ = _ ] => set (e := ee) end.  
  simpl in e; unfold identity in e; simpl in e.
  assert (X : e = idpath _ ).
  { apply setproperty. }
  rewrite X. apply id_left.
Defined.  
  
Theorem is_category_qq_morphism
  : is_category_disp (qq_structure_disp_precat C).
Proof.
  apply is_category_disp_from_fibers.
  intros x d d'. 
  use isweqimplimpl. 
  - apply qq_structure_iso_disp_to_id.
  - apply isaset_qq_morphism_structure.
  - apply isaprop_iso_disp_qq_morphism_structure.
Defined.


Lemma isaprop_iso_disp_strucs_compat_disp_precat
  (x : total_precat (families_disp_precat C × qq_structure_disp_precat C))
  (d d' : strucs_compat_disp_precat x)
  : isaprop (iso_disp (identity_iso x) d d').
Proof.
  unfold iso_disp.
  apply isofhleveltotal2.
  - apply hlevelntosn.
    apply iscontrunit.
  - intro.
    apply isaprop_is_iso_disp.
Qed.


Definition  strucs_compat_iso_disp_to_id
  (x : total_precat (families_disp_precat C × qq_structure_disp_precat C))
  (d d' : strucs_compat_disp_precat x)
  : iso_disp (identity_iso x) d d' → d = d'.
Proof.
  intro H.
  do 4 (apply funextsec; intro).
  apply functor_category_has_homsets.
Defined.

Theorem is_category_strucs_compat
  : is_category_disp (@strucs_compat_disp_precat C).
Proof.
  apply is_category_disp_from_fibers.
  intros x d d'.
  use isweqimplimpl.
  - apply strucs_compat_iso_disp_to_id.
  - apply hlevelntosn.
    apply CwF_SplitTypeCat_Maps.isaprop_iscompatible_fam_qq.
  - apply isaprop_iso_disp_strucs_compat_disp_precat.
Defined.

End Fix_Context.
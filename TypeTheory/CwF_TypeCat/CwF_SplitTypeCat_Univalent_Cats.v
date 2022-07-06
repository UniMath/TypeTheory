(**
  [TypeTheory.CwF_TypeCat.CwF_SplitTypeCat_Univalent_Cats]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.slicecat.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheory.
Require Import TypeTheory.Auxiliary.SetsAndPresheaves.

Require Import TypeTheory.CwF_TypeCat.CwF_SplitTypeCat_Defs.
Require Import TypeTheory.CwF_TypeCat.CwF_SplitTypeCat_Cats.
Require Import TypeTheory.CwF_TypeCat.CwF_SplitTypeCat_Equiv_Cats.


Section Auxiliary.

Lemma transportf_term_fun_mor_TM {C : category}
  {X X' : obj_ext_cat C} {F F' : X --> X'} (e : F = F')
  {Y : term_fun_disp_cat C X} {Y'} (FY : Y -->[F] Y')
  : term_fun_mor_TM (transportf _ e FY) = term_fun_mor_TM FY.
Proof.
  destruct e; apply idpath.
Qed.

End Auxiliary.

Section Fix_Context.

Context {C : category}.

Local Notation "Γ ◂ A" := (comp_ext _ Γ A) (at level 30).
Local Notation "'Ty'" := (fun X Γ => TY X #p Γ) (at level 10).

Local Notation Δ := comp_ext_compare.
Local Notation φ := obj_ext_mor_φ.


Section Is_Univalent_Obj_Ext_Disp.

  Context {C_univalent : is_univalent C}.

  (* OUTLINE:
  for ext_disp Cxt_dispct-extension structures X, X',
  X = X'
  <~> forall Γ A, (X Γ A = X' Γ A)    (by funext)
  <~> forall Γ Α, (iso (slice ___))   (by [id_weq_iso_slicecat])
  <~> iso (obj_ext) X X'              (by hand, in [slice_isos_to_obj_ext_iso])
  *)

  Lemma slice_maps_to_obj_ext_map {TY : PreShv C} {X X' : obj_ext_disp TY}
    : (∏ Γ A, slice_cat C Γ ⟦ X Γ A , X' Γ A ⟧)
    -> X -->[identity_z_iso TY] X'.
  Proof.
    intros I Γ A.
    exists (pr1 (I Γ A)).  
    apply pathsinv0, (pr2 (I Γ A)).  
  Defined.

  Lemma is_iso_slice_isos_to_obj_ext_map {TY : PreShv C} {X X' : obj_ext_disp TY}
    (I : ∏ Γ A, @z_iso (slice_cat C Γ) (X Γ A) (X' Γ A))
    : is_z_iso_disp (identity_z_iso _) (slice_maps_to_obj_ext_map (fun Γ A => I Γ A)).
  Proof.
    exists (slice_maps_to_obj_ext_map (fun Γ A => inv_from_z_iso (I Γ A))).
    split.
    - use obj_ext_mor_disp_transportb_eq_gen.
      + cbn; intros; apply idpath.
      + cbn; intros.
        etrans. { apply id_right. } 
        exact (maponpaths pr1 (z_iso_after_z_iso_inv (I Γ A))).
    - use obj_ext_mor_disp_transportb_eq_gen.
      + cbn; intros; apply idpath.
      + cbn; intros.
        etrans. { apply id_right. } 
        exact (maponpaths pr1 (z_iso_inv_after_z_iso (I Γ A))).
  Qed.

  Lemma slice_isos_to_obj_ext_iso {TY : PreShv C} (X X' : obj_ext_disp TY)
    : (∏ Γ A, @z_iso (slice_cat C Γ) (X Γ A) (X' Γ A))
    -> z_iso_disp (identity_z_iso TY) X X'.
  Proof.
    intros I.
    exists (slice_maps_to_obj_ext_map I).
    apply is_iso_slice_isos_to_obj_ext_map.
  Defined.

  Lemma obj_ext_map_to_slice_maps {TY : PreShv C} {X X' : obj_ext_disp TY}
    : X -->[identity_z_iso TY] X'
      -> (∏ Γ A, slice_cat C Γ ⟦ X Γ A , X' Γ A ⟧).
  Proof.
    intros I Γ A.
    exists (pr1 (I Γ A)).  
    apply pathsinv0, (pr2 (I Γ A)).
  Defined.

  Lemma is_iso_obj_ext_iso_to_slice_maps {TY : PreShv C} {X X' : obj_ext_disp TY}
    (I : z_iso_disp (identity_z_iso TY) X X')
    : forall Γ A, is_z_isomorphism (obj_ext_map_to_slice_maps I Γ A).
  Proof.
    intros Γ A.
    exists (obj_ext_map_to_slice_maps (inv_mor_disp_from_z_iso I) Γ A).
    split; apply subtypePath; cbn.
    1, 3: intro f; apply homset_property.
    - set (I_V := inv_mor_after_z_iso_disp I).
      apply (maponpaths (fun f => obj_ext_mor_disp_φ f A)) in I_V.
      etrans. { apply I_V. }
      etrans. { use obj_ext_mor_disp_transportb. }
      etrans. { apply id_left. }
      apply comp_ext_compare_id_general. 
    - set (V_I := z_iso_disp_after_inv_mor I).
      apply (maponpaths (fun f => obj_ext_mor_disp_φ f A)) in V_I.
      etrans. { apply V_I. }
      etrans. { use obj_ext_mor_disp_transportb. }
      etrans. { apply id_left. }
      apply comp_ext_compare_id_general. 
  Qed.

  Lemma isweq_slice_isos_obj_ext_iso {TY : PreShv C} (X X' : obj_ext_disp TY)
    : isweq (slice_isos_to_obj_ext_iso X X').
  Proof.
    use gradth.
    - intros I Γ A; use tpair.
      apply (obj_ext_map_to_slice_maps I). 
      apply is_iso_obj_ext_iso_to_slice_maps.
    - intros I.
      apply funextsec; intros Γ.
      apply funextsec; intros A.
      apply z_iso_eq.
      apply subtypePath. { intros ?; apply homset_property. }
      apply idpath.
    - intros I.
      apply eq_z_iso_disp.
      apply obj_ext_mor_disp_eq.
      intros ? ?. apply idpath.
  Qed.

  Lemma weq_slice_isos_obj_ext_iso {TY : PreShv C} (X X' : obj_ext_disp TY)
    : (∏ Γ A, @z_iso (slice_cat C Γ) (X Γ A) (X' Γ A))
    ≃ z_iso_disp (identity_z_iso TY) X X'.
  Proof.
    exists (slice_isos_to_obj_ext_iso _ _).
    apply isweq_slice_isos_obj_ext_iso.
  Defined.

  Lemma is_univalent_mor_weq {TY : PreShv C} (X X' : obj_ext_disp TY)
    : X = X' ≃ z_iso_disp (identity_z_iso TY) X X'.
  Proof.
    apply (@weqcomp _ (forall Γ A, X Γ A = X' Γ A)).
    { refine (weqcomp _ _). { apply weqtoforallpaths. } 
      apply weqonsecfibers; intros Γ. 
      apply weqtoforallpaths.
    }
    eapply weqcomp.
    { apply weqonsecfibers; intros Γ.
      apply weqonsecfibers; intros A.
      use id_weq_z_iso_slicecat; auto.
    }
    apply weq_slice_isos_obj_ext_iso.
  Defined.
  
  Lemma is_univalent_obj_ext_fibers : is_univalent_in_fibers (@obj_ext_disp C).
  Proof.
    unfold is_univalent_in_fibers.
    intros TY X X'.
    use weqhomot. { apply is_univalent_mor_weq. }
    intros e; destruct e.
    apply eq_z_iso_disp.
    apply obj_ext_mor_disp_eq.
    intros; apply idpath.
  Qed.

  Theorem is_univalent_obj_ext_disp : is_univalent_disp (@obj_ext_disp C).
  Proof.
    apply is_univalent_disp_from_fibers,
          is_univalent_obj_ext_fibers.
  Defined.
  
  Theorem is_univalent_obj_ext : is_univalent (obj_ext_cat C).
  Proof.
    apply is_univalent_total_category.
    - apply is_univalent_functor_category, univalent_category_is_univalent.
    - apply is_univalent_obj_ext_disp.
  Defined.

End Is_Univalent_Obj_Ext_Disp.

Section Is_Univalent_Families_Strucs.

Definition iso_disp_to_TM_eq
  (X : obj_ext_cat C)
  (Y Y' : (term_fun_disp_cat C) X)
  : z_iso_disp (identity_z_iso X) Y Y'
  -> TM (Y : term_fun_structure _ X) = TM (Y' : term_fun_structure _ X).
Proof.
  intro i.
  use isotoid.
  - apply univalent_category_is_univalent.
  - exists (term_fun_mor_TM (i : _ -->[_] _)).
    exists (term_fun_mor_TM (inv_mor_disp_from_z_iso i)).
    split.
    + etrans. exact (maponpaths term_fun_mor_TM (inv_mor_after_z_iso_disp i)).
      apply transportf_term_fun_mor_TM.
    + etrans. exact (maponpaths term_fun_mor_TM (z_iso_disp_after_inv_mor i)).
      apply transportf_term_fun_mor_TM.
Defined.

Lemma prewhisker_iso_disp_to_TM_eq 
  {X} {Y Y' : term_fun_disp_cat C X}
  (FG : z_iso_disp (identity_z_iso X) Y Y')
  {P : preShv C} (α : TM (Y : term_fun_structure _ X) --> P)
: transportf (λ P' : preShv C, P' --> P) (iso_disp_to_TM_eq _ _ _ FG) α
  = term_fun_mor_TM (pr1 (pr2 FG)) ;; α.
Proof.
  etrans. apply transportf_isotoid.
  apply maponpaths_2.
  apply inv_from_z_iso_from_is_z_iso.
Qed.

Lemma postwhisker_iso_disp_to_TM_eq 
  {X} {Y Y' : term_fun_disp_cat C X}
  (FG : z_iso_disp (identity_z_iso X) Y Y')
  {P : preShv C} (α : P --> TM (Y : term_fun_structure _ X))
: transportf (λ P' : preShv C, P --> P') (iso_disp_to_TM_eq _ _ _ FG) α
  = α ;; term_fun_mor_TM (pr1 FG).
Proof.
  apply postwhisker_isotoid.
Qed.

Lemma idtoiso_iso_disp_to_TM_eq 
  {X} {Y Y' : term_fun_disp_cat C X}
  (FG : z_iso_disp (identity_z_iso X) Y Y')
: (idtoiso (iso_disp_to_TM_eq _ _ _ FG) : _ --> _)
  = term_fun_mor_TM (FG : _ -->[_] _).
Proof.
  exact (maponpaths pr1 (idtoiso_isotoid _ _ _ _ _)).
Qed.

Definition iso_to_id__term_fun_disp_cat
  {X : obj_ext_cat C}
  (Y Y' : term_fun_disp_cat C X)
  : z_iso_disp (identity_z_iso _) Y Y' -> Y = Y'.
Proof.
  intros i.
  apply subtypePath. { intro. apply isaprop_term_fun_structure_axioms. }
  apply total2_paths_f with (iso_disp_to_TM_eq _ _ _ i).
  rewrite transportf_dirprod.
  apply dirprodeq.
  - etrans. apply prewhisker_iso_disp_to_TM_eq.
    etrans. apply term_fun_mor_pp.
    exact (id_right (pp _)).
  - etrans. refine (transportf_forall _ _ _).
    apply funextsec; intros Γ.
    etrans. refine (transportf_forall _ _ _).
    apply funextsec; intros A.
    etrans. apply transportf_pshf.
    etrans.
      refine (toforallpaths _ (te _ _)).
      refine (toforallpaths _ _).
      apply maponpaths, idtoiso_iso_disp_to_TM_eq.
    etrans. apply term_fun_mor_te.
    exact (toforallpaths (functor_id (TM _) _) _).
Qed.

Theorem is_univalent_term_fun_structure
  : is_univalent_disp (term_fun_disp_cat C).
Proof.
  apply is_univalent_disp_from_fibers.
  intros X.
  apply eq_equiv_from_retraction with iso_to_id__term_fun_disp_cat.
  - intros. apply eq_z_iso_disp, isaprop_term_fun_mor.
Qed.

End Is_Univalent_Families_Strucs.

Section Is_Univalent_qq_Strucs.

Lemma isaset_qq_morphism_structure (x : obj_ext_structure C) 
  : isaset (qq_morphism_structure x).
Proof.
  apply (isofhleveltotal2 2).
  - apply (isofhleveltotal2 2).
    + do 4 (apply impred; intro).
      apply homset_property.
    + intros. do 4 (apply impred; intro).
      apply (isofhleveltotal2 2).
      * apply hlevelntosn.
        apply homset_property.
      * intro. apply hlevelntosn.
        apply pullbacks.isaprop_isPullback.
  - intro d. unfold qq_morphism_axioms.
    apply isofhleveldirprod.
    + do 2 (apply impred; intro).
      apply hlevelntosn.
      apply homset_property.
    + do 6 (apply impred; intro).
      apply hlevelntosn.
      apply homset_property.
Qed.

Lemma isaprop_iso_disp_qq_morphism_structure 
  (x : obj_ext_cat C)
  (d d' : (qq_structure_disp_cat C) x)
  : isaprop (z_iso_disp (identity_z_iso x) d d').
Proof.
  apply (isofhleveltotal2 1).
  - do 4 (apply impred; intro).
    apply homset_property.
  - intro. apply isaprop_is_z_iso_disp.
Qed.

Lemma qq_structure_eq 
  (x : obj_ext_cat C)
  (d d' : qq_morphism_structure x)
  (H : ∏ (Γ Γ' : C) (f : Γ' --> Γ) (A : TY x $p Γ), 
           qq d f A = qq d' f A)
  : d = d'.
Proof.
  apply subtypePath.
  { intro. apply isaprop_qq_morphism_axioms. }
  apply subtypePath.
  { intro. do 4 (apply impred; intro). 
           apply isofhleveltotal2.
     + apply homset_property.
     + intro. apply pullbacks.isaprop_isPullback.
  } 
  do 4 (apply funextsec; intro).
  apply H.
Defined.

Definition qq_structure_iso_disp_to_id
  (x : obj_ext_cat C)
  (d d' : (qq_structure_disp_cat C) x)
  : z_iso_disp (identity_z_iso x) d d' → d = d'.
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
  
Theorem is_univalent_qq_morphism
  : is_univalent_disp (qq_structure_disp_cat C).
Proof.
  apply is_univalent_disp_from_fibers.
  intros x d d'. 
  use isweqimplimpl. 
  - apply qq_structure_iso_disp_to_id.
  - apply isaset_qq_morphism_structure.
  - apply isaprop_iso_disp_qq_morphism_structure.
Defined.

End Is_Univalent_qq_Strucs.

Section Is_Univalent_Compat_Strucs.

Lemma isaprop_iso_disp_strucs_compat_disp_cat
  (x : total_category (term_fun_disp_cat C × qq_structure_disp_cat C))
  (d d' : strucs_compat_disp_cat x)
  : isaprop (z_iso_disp (identity_z_iso x) d d').
Proof.
  unfold z_iso_disp.
  apply isofhleveltotal2.
  - apply hlevelntosn.
    apply iscontrunit.
  - intro.
    apply isaprop_is_z_iso_disp.
Qed.


Definition  strucs_compat_iso_disp_to_id
  (x : total_category (term_fun_disp_cat C × qq_structure_disp_cat C))
  (d d' : strucs_compat_disp_cat x)
  : z_iso_disp (identity_z_iso x) d d' → d = d'.
Proof.
  intro H.
  do 4 (apply funextsec; intro).
  apply setproperty.
Defined.

Theorem is_univalent_strucs_compat
  : is_univalent_disp (@strucs_compat_disp_cat C).
Proof.
  apply is_univalent_disp_from_fibers.
  intros x d d'.
  use isweqimplimpl.
  - apply strucs_compat_iso_disp_to_id.
  - apply hlevelntosn.
    apply CwF_SplitTypeCat_Maps.isaprop_iscompatible_term_qq.
  - apply isaprop_iso_disp_strucs_compat_disp_cat.
Defined.

End Is_Univalent_Compat_Strucs.

Section Is_Univalent_Total_Cats.

  Context (C_univ : is_univalent C).

  Theorem is_univalent_cwf'_structure_precat
    : is_univalent (cwf'_structure_precat C).
  Proof.
    apply is_univalent_total_category.
    - apply @is_univalent_obj_ext; auto.
    - apply is_univalent_term_fun_structure.
  Defined.
  
  Theorem is_univalent_sty'_structure_precat
    : is_univalent (sty'_structure_precat C).
  Proof.
    apply is_univalent_total_category.
    - apply @is_univalent_obj_ext; auto.
    - apply is_univalent_qq_morphism.
  Defined.

End Is_Univalent_Total_Cats.

End Fix_Context.

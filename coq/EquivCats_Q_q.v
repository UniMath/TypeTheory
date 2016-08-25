(**

 Ahrens, Lumsdaine, Voevodsky, 2015 - 2016

Main definitions:

- [obj_ext_precat]
- [families_disp_precat], [families_structure_precat]
- [qq_structure_disp_precat], [qq_structure_precat]
*)

Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.more_on_pullbacks.

Require Import Systems.UnicodeNotations.
Require Import Systems.Auxiliary.
Require Import Systems.Structures.
Require UniMath.Ktheory.Precategories.
Require Import UniMath.Ktheory.StandardCategories.


Local Set Automatic Introduction.
(* only needed since imports globally unset it *)


(** Some local notations, *)

Local Notation "Γ ◂ A" := (comp_ext _ Γ A) (at level 30).
Local Notation "'Ty'" := (fun X Γ => (TY X : functor _ _) Γ : hSet) (at level 10).
Local Notation "'Tm'" := (fun Y Γ => (TM Y : functor _ _) Γ : hSet) (at level 10).
Local Notation Δ := comp_ext_compare.

Section fix_cat_obj_ext.

Variable C : precategory.
Variable hsC : has_homsets C.
Variable X : obj_ext_structure C.


(** * Precategory of families-structures *)
Section Families_Structure_Precat.

Local Notation "'Yo'" := (yoneda _ hsC).

Definition families_mor 
    (Y Y' : families_structure hsC X) 
  : UU
:= Σ FF_TM : TM Y --> TM Y',
       FF_TM ;; pp Y' = pp Y 
     × 
       Π {Γ:C} {A : Ty X Γ}, Q Y A ;; FF_TM =  Q Y' _.

Definition families_mor_TM {Y} {Y'} (FF : families_mor Y Y')
  : _ --> _
:= pr1 FF.

Definition families_mor_pp {Y} {Y'} (FF : families_mor Y Y')
  : families_mor_TM FF ;; pp Y' = pp Y 
:= pr1 (pr2 FF).

Definition families_mor_Q {Y} {Y'} (FF : families_mor Y Y')
    {Γ} A
  : _ = _
:= pr2 (pr2 FF) Γ A.

(* TODO: inline in [isaprop_families_mor]? *)
Lemma families_mor_eq {Y} {Y'} (FF FF' : families_mor Y Y')
    (e_TM : Π Γ (t : Tm Y Γ),
      (families_mor_TM FF : nat_trans _ _) _ t
      = (families_mor_TM FF' : nat_trans _ _) _ t)
  : FF = FF'.
Proof.
  apply subtypeEquality.
  - intros x; apply isapropdirprod.
    + apply functor_category_has_homsets.
    + repeat (apply impred_isaprop; intro). apply functor_category_has_homsets.
  - apply nat_trans_eq. apply has_homsets_HSET. 
    intros Γ. apply funextsec. unfold homot. apply e_TM.
Qed.


(* This is not full naturality of [term_to_section]; it is just what is required for [isaprop_families_mor] below. *)
Lemma term_to_section_naturality {Y} {Y'}
  {FY : families_mor Y Y'}
  {Γ : C} (t : Tm Y Γ) (A := (pp Y : nat_trans _ _) _ t)
  : pr1 (term_to_section ((families_mor_TM FY : nat_trans _ _) _ t))
  = pr1 (term_to_section t) 
   ;; Δ (!toforallpaths _ _ _ (nat_trans_eq_pointwise (families_mor_pp FY) Γ) t).
Proof.
  set (t' := (families_mor_TM FY : nat_trans _ _) _ t).
  set (A' := (pp Y' : nat_trans _ _) _ t').
  set (Pb := isPullback_preShv_to_pointwise hsC (isPullback_Q_pp Y' A') Γ);
    simpl in Pb.
  apply (pullback_HSET_elements_unique Pb); clear Pb.
  - unfold yoneda_morphisms_data; cbn.
    etrans. refine (pr2 (term_to_section t')). apply pathsinv0.
    etrans. Focus 2. refine (pr2 (term_to_section t)).
    etrans. apply @pathsinv0, assoc.
(*
    etrans. apply @pathsinv0, assoc.
*)
    apply maponpaths.
    apply comp_ext_compare_π.
(*
    etrans. Focus 2. apply @obj_ext_mor_ax.
    apply maponpaths. 
    apply comp_ext_compare_π.
*)
  - etrans. apply term_to_section_recover. apply pathsinv0.
    etrans. apply Q_comp_ext_compare.
    etrans. apply @pathsinv0.
      set (H1 := nat_trans_eq_pointwise (families_mor_Q FY A) Γ).
      exact (toforallpaths _ _ _ H1 _).
    cbn. apply maponpaths. apply term_to_section_recover.
Qed.

Lemma families_mor_recover_term  {Y} {Y'}
  {FY : families_mor Y Y'}
  {Γ : C} (t : Tm Y Γ)
  : (families_mor_TM FY : nat_trans _ _) Γ t
  = (Q Y' _ : nat_trans _ _) Γ (pr1 (term_to_section t) ).
Proof.
  etrans. apply @pathsinv0, term_to_section_recover.
  etrans. apply maponpaths, term_to_section_naturality.
  apply Q_comp_ext_compare.
Qed.

(* TODO: once all obligations proved, replace [families_mor_eq] with this in subsequent proofs. *)
Lemma isaprop_families_mor {Y} {Y'}
  : isaprop (families_mor Y Y').
Proof.
  apply invproofirrelevance; intros FF FF'. apply families_mor_eq.
  intros Γ t.
  etrans. apply families_mor_recover_term.
  apply @pathsinv0. apply families_mor_recover_term.
Qed.

(*
Lemma families_mor_transportf {X X'} {Y Y'}
    {F F' : X --> X'} (eF : F = F') (FF : families_mor Y Y' F)
    {Γ:C} (t : Tm Y Γ)
  : (families_mor_TM (transportf _ eF FF) : nat_trans _ _) Γ t
    = (families_mor_TM FF : nat_trans _ _) Γ t.
Proof.
  destruct eF. apply idpath.
Qed.
 *)

Definition families_ob_mor : precategory_ob_mor. (* disp_precat_ob_mor (obj_ext_Precat C). *)
Proof.
  exists (families_structure hsC X).
  exact @families_mor.
Defined.

Definition families_id_comp : disp_precat_id_comp _ families_ob_mor.
Proof.
  apply tpair.
  - intros X Y. simpl; unfold families_mor.
    exists (identity _). apply tpair.
    + etrans. apply id_left. apply pathsinv0, id_right.
    + intros Γ A. etrans. apply id_right.
      apply pathsinv0. refine (_ @ id_left _).
      refine (maponpaths (fun k => k ;; _) _).
      apply functor_id.
  - intros X0 X1 X2 F G Y0 Y1 Y2 FF GG.
    exists (families_mor_TM FF ;; families_mor_TM GG). apply tpair.
    + etrans. apply @pathsinv0. apply assoc.
      etrans. apply maponpaths, families_mor_pp.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition, families_mor_pp.
      apply pathsinv0. apply assoc.
    + intros Γ A.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition, families_mor_Q.
      etrans. apply @pathsinv0, assoc.
      etrans. apply maponpaths, families_mor_Q.
      etrans. apply assoc.
      apply cancel_postcomposition.
      apply pathsinv0, functor_comp.
Defined.

Definition families_data : disp_precat_data (obj_ext_Precat C)
  := (_ ,, families_id_comp).

Definition families_axioms : disp_precat_axioms _ families_data.
Proof.
  repeat apply tpair.
  - intros. apply families_mor_eq. intros.
    etrans. Focus 2. apply @pathsinv0, families_mor_transportf.
    apply idpath.
  - intros. apply families_mor_eq. intros.
    etrans. Focus 2. apply @pathsinv0, families_mor_transportf.
    apply idpath.
  - intros. apply families_mor_eq. intros.
    etrans. Focus 2. apply @pathsinv0, families_mor_transportf.
    apply idpath.
  - intros. apply isaset_total2.
    apply functor_category_has_homsets.
    intros. apply isasetaprop, isapropdirprod.
    apply functor_category_has_homsets.
    repeat (apply impred_isaprop; intro). apply functor_category_has_homsets.
Qed.

Definition families_disp_precat : disp_precat (obj_ext_Precat C)
  := (_ ,, families_axioms).

Definition families_structure_precat : precategory
  := total_precat families_disp_precat.

End Families_Structure_Precat.

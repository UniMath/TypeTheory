(**

 Ahrens, Lumsdaine, Voevodsky, 2015 - 2016

Main definitions:

- [families_precategory]
- [qq_structure_precategory]
- category of compatible pairs
- projection functors from compatible pairs to structures
- proof that those projection functors are split and ff

*)

Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.more_on_pullbacks.
Require Import UniMath.CategoryTheory.equivalences.
Require Import Systems.UnicodeNotations.
Require Import Systems.Auxiliary.
Require Import Systems.Structures.
Require UniMath.Ktheory.Precategories.
Require Import UniMath.Ktheory.StandardCategories.
Require Import Systems.CwF_SplitTypeCat_Maps.
Require Import Systems.CwF_SplitTypeCat_Equivalence.

Local Set Automatic Introduction.
(* only needed since imports globally unset it *)

Notation Precategory := Precategories.Precategory.
Coercion Precategories.Precategory_to_precategory
  : Precategories.Precategory >-> precategory.
Notation homset_property := Precategories.homset_property.
Notation functorPrecategory := Precategories.functorPrecategory.

(** Some local notations, *)

Local Notation "Γ ◂ A" := (comp_ext _ Γ A) (at level 30).
Local Notation "'Ty'" := (fun X Γ => (TY X : functor _ _) Γ : hSet) (at level 10).
Local Notation "'Tm'" := (fun Y Γ => (TM Y : functor _ _) Γ : hSet) (at level 10).
Local Notation Δ := comp_ext_compare.

Section fix_cat_obj_ext.

Variable C : Precategories.Precategory.
Definition hsC : has_homsets C := homset_property C.
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
    apply maponpaths.
    apply comp_ext_compare_π.
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


Definition families_ob_mor : precategory_ob_mor. 
Proof.
  exists (families_structure hsC X).
  exact @families_mor.
Defined.

Definition families_id_comp : precategory_id_comp families_ob_mor.
Proof.
  apply tpair.
  - intros Y. simpl; unfold families_mor.
    exists (identity _). apply tpair.
    + apply id_left. 
    + intros Γ A. apply id_right.
  - intros Y0 Y1 Y2 FF GG.
    exists (families_mor_TM FF ;; families_mor_TM GG). apply tpair.
    + etrans. apply @pathsinv0. apply assoc.
      etrans. apply maponpaths, families_mor_pp.
      apply families_mor_pp.
    + intros Γ A.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition, families_mor_Q.
      apply families_mor_Q.
Defined.

Definition families_data : precategory_data 
  := (_ ,, families_id_comp).

Definition families_axioms : is_precategory families_data.
Proof.
  repeat apply tpair.
  - intros. apply families_mor_eq. intros.
    apply idpath.
  - intros. apply families_mor_eq. intros.
    apply idpath.
  - intros. apply families_mor_eq. intros.
    apply idpath.
Qed.


Definition families_precategory : precategory 
  := (_ ,, families_axioms).


Lemma has_homsets_families_precat 
  : has_homsets families_precategory.
Proof.
  intros a b. apply isaset_total2.
  apply functor_category_has_homsets.
  intros. apply isasetaprop, isapropdirprod.
  apply functor_category_has_homsets.
  repeat (apply impred_isaprop; intro). apply functor_category_has_homsets.
Qed.

End Families_Structure_Precat.

(** * Precategory of cartesian _q_-morphism-structures *)
Section qq_Structure_Precat.

Definition qq_structure_ob_mor : precategory_ob_mor.
Proof.
  exists (qq_morphism_structure X).
  intros Z Z'.
  refine (Π Γ' Γ (f : C ⟦ Γ' , Γ ⟧) (A : Ty X Γ), _).
  refine (qq Z f A  = _).
  refine (qq Z' f _ ).
Defined.

Lemma isaprop_qq_structure_mor
  (Z Z' : qq_structure_ob_mor)
  : isaprop (Z --> Z').
Proof.
  repeat (apply impred_isaprop; intro). apply hsC. 
Qed.

Definition qq_structure_id_comp : precategory_id_comp qq_structure_ob_mor.
Proof.
  apply tpair.
  - intros Z;
    intros Γ Γ' f A. apply idpath.
  - intros Z0 Z1 Z2;
    intros FF GG Γ Γ' f A.
    etrans. apply FF. apply GG.
Qed.

Definition qq_structure_data : precategory_data 
  := (_ ,, qq_structure_id_comp).

Definition qq_structure_axioms : is_precategory qq_structure_data.
Proof.
  repeat apply tpair; intros;
    try apply isasetaprop; apply isaprop_qq_structure_mor.
Qed.

Definition qq_structure_precategory : precategory
  := (_ ,, qq_structure_axioms).

End qq_Structure_Precat.

Arguments qq_structure_precategory : clear implicits.

Section Compatible_Disp_Cat.

(* TODO: rename [strucs_compat_FOO] to [strucs_iscompat_FOO] throughout, to disambiguate these from the sigma’d displayed-precat [compat_structures]. *)

Definition strucs_compat_ob_mor
  : precategory_ob_mor.
Proof.
  use tpair.
  - exact (Σ YZ : (families_precategory × qq_structure_precategory), 
                  iscompatible_fam_qq (pr1 YZ) (pr2 YZ)).
  - intros YZ YZ'.
    exact ((pr1 (pr1 YZ)) --> (pr1 (pr1 YZ')) × (pr2 (pr1 YZ)) --> pr2 (pr1 YZ')).
Defined.

Definition strucs_compat_id_comp
  : precategory_id_comp strucs_compat_ob_mor.
Proof.
  split. 
  - intro; split; apply identity.
  - intros a b c f g. split. 
    eapply @compose. apply (pr1 f). apply (pr1 g). 
    eapply @compose. apply (pr2 f). apply (pr2 g). 
Defined.

Definition strucs_compat_data : precategory_data 
  := ( _ ,, strucs_compat_id_comp).

Definition strucs_compat_axioms : is_precategory strucs_compat_data.
Proof.
  repeat apply tpair; intros.
  - apply dirprodeq;    apply id_left.
  - apply dirprodeq; apply id_right.
  - apply dirprodeq; apply assoc.
Qed.

Definition compat_structures_precategory
  : precategory 
:= ( _ ,, strucs_compat_axioms).

(* should this be the name of the compatible pairs category? *)
(*
Definition compat_structures_disp_precat
  := sigma_disp_precat strucs_compat_disp_precat.
*)


Definition compat_structures_pr1_functor
  : functor compat_structures_precategory families_precategory.
Proof.
  mkpair.
  - mkpair.
    + exact (fun YZp => pr1 (pr1 YZp)).
    + intros a b f. apply (pr1 f).
  - mkpair.
    + intro c. apply idpath.
    + intros a b c f g. apply idpath.
Defined.

Definition compat_structures_pr2_functor
  : functor compat_structures_precategory qq_structure_precategory.
Proof.
  mkpair.
  - mkpair.
    + exact (fun YZp => pr2 (pr1 YZp)).
    + intros a b f. apply (pr2 f).
  - mkpair.
    + intro c. apply idpath.
    + intros a b c f g. apply idpath.
Defined.


End Compatible_Disp_Cat.

Section Unique_QQ_From_Fam.

Lemma qq_from_fam_ob (Y : families_precategory)
  : Σ (Z : qq_structure_precategory), iscompatible_fam_qq Y Z.
Proof.
  exists (qq_from_fam Y).
  apply iscompatible_qq_from_fam.
Defined.

Lemma qq_from_fam_mor 
  {Y : families_precategory} {Y'} (FY : Y --> Y')
  {Z : qq_structure_precategory} {Z'}
  (W : iscompatible_fam_qq Y Z)
  (W' : iscompatible_fam_qq Y' Z')
  : Z --> Z'. 
Proof.
  intros Γ' Γ f A.
  cbn in W, W', FY. unfold iscompatible_fam_qq in *. 
  unfold families_mor in FY.
  apply (Q_pp_Pb_unique Y'); simpl; unfold yoneda_morphisms_data.
  -     (* TODO: name of [obj_ext_mor_ax] unmemorable.  Rename more like [qq_π]? *)
    etrans. apply @pathsinv0, qq_π.
      (* TODO: name of [qq_π] misleading, suggests opposite direction. *)
    apply pathsinv0.
    etrans. apply @pathsinv0, qq_π.
    apply idpath.
  (* Maybe worth abstracting the following pointwise application of [W],
   [families_mor_Q], etc. as lemmas? *)
  - etrans.
      exact (!toforallpaths _ _ _
        (nat_trans_eq_pointwise (families_mor_Q FY _) _) _).
    etrans. apply maponpaths, @pathsinv0, id_left.
    etrans. cbn. apply maponpaths.
      exact (!toforallpaths _ _ _
        (nat_trans_eq_pointwise (W _ _ _ _) _) _).
    apply pathsinv0.
    assert (XR := nat_trans_eq_pointwise (W' _ _ A f)).
    specialize (XR (Γ' ◂ # (TY X : functor _ _ ) f A)). cbn in XR.
    assert (XR' := toforallpaths _ _ _ XR). unfold homot in XR'. 
      unfold yoneda_morphisms_data in XR'.
    specialize (XR' (identity _ )).
    etrans. apply maponpaths. eapply pathsinv0. apply id_left.
    etrans. apply (!XR').
    clear XR' XR.
    etrans. apply maponpaths, @pathsinv0, id_left.
    rewrite id_left.
    exact (!toforallpaths _ _ _
      (nat_trans_eq_pointwise (families_mor_Q FY _) _) _).
Time Qed.


Lemma qq_from_fam_mor_unique 
  {Y : families_precategory} {Y'} (FY : Y --> Y')
  {Z : qq_structure_precategory} {Z'}
  (W : iscompatible_fam_qq Y Z)
  (W' : iscompatible_fam_qq Y' Z')
  : isaprop (Z --> Z').
Proof.
  simpl. repeat (apply impred_isaprop; intro). apply hsC.
Qed.

End Unique_QQ_From_Fam.

Section Unique_Fam_From_QQ.

Lemma fam_from_qq_ob (Z : qq_structure_precategory)
  : Σ (Y : families_precategory), iscompatible_fam_qq Y Z.
Proof.
  exists (fam_from_qq Z).
  apply iscompatible_fam_from_qq.
Defined.

(** The next main goal is the following statement.  However, the construction of the morphism of families structures is rather large; so we break out the first component (the map of term presheaves) into several independent lemmas, before returning to this in [fam_from_qq_mor] below. *)
Lemma fam_from_qq_mor
  {Z : qq_structure_precategory} {Z'} (FZ : Z --> Z')
  {Y : families_precategory} {Y'}
  (W : iscompatible_fam_qq Y Z)
  (W' : iscompatible_fam_qq Y' Z')
  : (Y --> Y').
Abort.

Lemma fam_from_qq_mor_TM_data 
  {Z : qq_structure_precategory} {Z'} (FZ : Z --> Z')
  {Y : families_precategory} {Y'}
  (W : iscompatible_fam_qq Y Z)
  (W' : iscompatible_fam_qq Y' Z')
  : Π Γ,
    ((TM (Y : families_structure _ _) : functor _ _) Γ : hSet)
    -> ((TM (Y' : families_structure _ _) : functor _ _) Γ : hSet).
Proof.
  intros Γ t; simpl in Γ.
  exact ((Q _ _ : nat_trans _ _) _ (pr1 (term_to_section t) )).
Defined.

Lemma fam_from_qq_mor_TM_naturality 
  {Z : qq_structure_precategory} {Z'} (FZ : Z --> Z')
  {Y : families_precategory} {Y'}
  (W : iscompatible_fam_qq Y Z)
  (W' : iscompatible_fam_qq Y' Z')
  : is_nat_trans (TM _ : functor _ _) _ (fam_from_qq_mor_TM_data FZ W W').
Proof.
  simpl in Y, Y'.
  intros Γ' Γ f; apply funextsec; intros t.
  (* Part 1: naturality of the section-to-term map back to [Tm Y']. *)
  etrans. Focus 2. exact (toforallpaths _ _ _ (nat_trans_ax (Q Y' _) _ _ _) _).
  cbn. simpl in W, W'; unfold iscompatible_fam_qq in W, W'.
  (* We want to apply [W'] on the lhs, so we need to munge the type argument
  of [Q] to a form with the [f] action outermost.  Naturality will show that
  the type is equal to such a form; [Q_comp_ext_compare] pushes that type
  equality through [Q]. *)
  unfold fam_from_qq_mor_TM_data.
  etrans. 
    apply @pathsinv0.
    simple refine (Q_comp_ext_compare _ _); simpl.
    Focus 2. 
      exact (toforallpaths _ _ _ (nat_trans_ax (pp Y) _ _ _) _).
  etrans.
    exact (toforallpaths _ _ _ (nat_trans_eq_pointwise (W' _ _ _ _) _) _).
  apply (maponpaths ((Q _ _ : nat_trans _ _ ) Γ)).
  simpl. unfold yoneda_morphisms_data.
  (* Part 2: naturality of the transfer along [F]. *)

  etrans. apply @pathsinv0, assoc.
  etrans. apply maponpaths. apply maponpaths. eapply pathsinv0. apply FZ.
  etrans. apply assoc.
  (* Part 3: naturality in [Γ] of the term-to-section construction from [Tm Y]. *)
  apply (Q_pp_Pb_unique Y).
  + unfold yoneda_morphisms_data. 
    apply @pathscomp0 with f.
    * etrans. apply @pathsinv0, assoc.
      etrans. apply maponpaths, @pathsinv0, qq_π.
      etrans. apply assoc.
      etrans. Focus 2. apply id_left.
      apply cancel_postcomposition.
      etrans. apply @pathsinv0, assoc.
      etrans. apply maponpaths, comp_ext_compare_π.
      exact (pr2 (term_to_section _)).
    * etrans. apply @pathsinv0, id_right.
      etrans. Focus 2. apply assoc.
      apply maponpaths, pathsinv0.
      exact (pr2 (term_to_section _)).
  + etrans. Focus 2.
      exact (toforallpaths _ _ _ (!nat_trans_ax (Q _ _) _ _ _) _).
    etrans. Focus 2. cbn.
      apply maponpaths, @pathsinv0, term_to_section_recover.
    etrans.
      exact (!toforallpaths _ _ _ (nat_trans_eq_pointwise (W _ _ _ _) _) _).
    etrans. apply Q_comp_ext_compare.
    apply term_to_section_recover.
Time Qed.

Definition fam_from_qq_mor_TM 
    {Z : qq_structure_precategory} {Z'} (FZ : Z --> Z')
    {Y : families_precategory} {Y'}
    (W : iscompatible_fam_qq Y Z)
    (W' : iscompatible_fam_qq Y' Z')
  : TM (Y : families_structure _ _) --> TM (Y' : families_structure _ _)
:= (fam_from_qq_mor_TM_data _ _ _,, fam_from_qq_mor_TM_naturality FZ W W').

Lemma fam_from_qq_mor
  {Z : qq_structure_precategory} {Z'} (FZ : Z --> Z')
  {Y : families_precategory} {Y'}
  (W : iscompatible_fam_qq Y Z)
  (W' : iscompatible_fam_qq Y' Z')
  : (Y --> Y').
Proof.
  simpl in W, W'; unfold iscompatible_fam_qq in W, W'. (* Readability *)
  simpl in Y, Y'.  (* To avoid needing casts [Y : families_structure _]. *)
  simpl; unfold families_mor.
  exists (fam_from_qq_mor_TM FZ W W').
  apply dirprodpair; try intros Γ A; apply nat_trans_eq; cbn.
  - apply has_homsets_HSET.
  - simpl. intros Γ; apply funextsec; intros t.
    etrans. refine (!toforallpaths _ _ _ (nat_trans_eq_pointwise (Q_pp _ _) _) _).
    simpl. unfold yoneda_morphisms_data; cbn.
    etrans.
      refine (toforallpaths _ _ _ _ ((pp Y : nat_trans _ _) Γ t)).
      apply maponpaths.
      exact (pr2 (term_to_section _)).
    exact (toforallpaths _ _ _ (functor_id (TY _) _) _).
  - apply has_homsets_HSET.
  - intros Γ'. unfold yoneda_morphisms_data, yoneda_objects_ob; cbn.
    apply funextsec; intros f.

    unfold fam_from_qq_mor_TM_data.

    assert (XR:= @Q_pp _ _ _ Y _ A).
    assert (XR' := nat_trans_eq_pointwise XR Γ').
    assert (XR'':= toforallpaths _ _ _ XR'). unfold homot in XR''.
    specialize (XR'' f).
    etrans.
      (* TODO: consider changing direction of [Q_comp_ext_compare]?*)
      apply @pathsinv0.         
         simple refine (Q_comp_ext_compare _ _); simpl.
         exact (# (TY _ : functor _ _ ) (f ;; π _ ) A).      
      refine (!toforallpaths _ _ _ (nat_trans_eq_pointwise (Q_pp _ _) _) _).
    cbn.
    Arguments Δ [_ _ _ _ _ _]. idtac.
    etrans. exact (toforallpaths _ _ _ (nat_trans_eq_pointwise (W' _ _ _ _) _) _).
    simpl; unfold yoneda_morphisms_data; cbn.  apply maponpaths.
    etrans. apply @pathsinv0, assoc.
    etrans. apply maponpaths.
      apply @pathsinv0.  apply maponpaths. apply FZ.
    assert (XRT := @map_from_term_recover _ _ _ _ W).
    rewrite assoc.
    apply XRT.
Time Qed.

Lemma fam_from_qq_mor_unique 
  {Z : qq_structure_precategory} {Z'} (FZ : Z --> Z')
  {Y : families_precategory} {Y'}
  (W : iscompatible_fam_qq Y Z)
  (W' : iscompatible_fam_qq Y' Z')
  : isaprop ( Y --> Y').
Proof.
  simpl. apply isaprop_families_mor.
Defined.

End Unique_Fam_From_QQ.


(*
TODO: scrap this section, and recover it from the displayed version. *) 
Section Strucs_Equiv_Precats.

Lemma compat_structures_pr1_split_ess_surj
  : split_ess_surj (compat_structures_pr1_functor).
Proof.
  intro Y.
  exists (((Y,, qq_from_fam Y)),,iscompatible_qq_from_fam Y).
  apply identity_iso.
Defined.

Lemma compat_structures_pr1_fully_faithful
  : fully_faithful (compat_structures_pr1_functor).
Proof.
  intros YZW YZW'.
  destruct YZW as [  [Y Z]  W].
  destruct YZW' as [ [Y' Z']  W'].
  unfold compat_structures_pr1_functor; simpl.
  use gradth.
  - intro f. exists f. use (qq_from_fam_mor f W W').
  - intros. cbn. destruct x as [f q]. cbn.
    apply maponpaths. 
    apply proofirrelevance.
    use (qq_from_fam_mor_unique f); assumption. 
  - intros y. cbn. apply idpath.
Qed.

Lemma compat_structures_pr2_split_ess_surj
  : split_ess_surj (compat_structures_pr2_functor).
Proof.
  intros Z.
  exists (((fam_from_qq Z,, Z)),,iscompatible_fam_from_qq Z).
  apply identity_iso.
Defined.

Lemma compat_structures_pr2_fully_faithful
  : fully_faithful (compat_structures_pr2_functor).
Proof.
  intros YZW YZW';
  destruct YZW as [  [Y Z]  W];
  destruct YZW' as [  [Y' Z']  W'].
  unfold compat_structures_pr2_functor; simpl.
  use gradth.
  - intro x.
    exists (fam_from_qq_mor x W W').
    exact x.
  - intro r. cbn.
    destruct r as [r1 r2]. apply maponpaths_2.
    apply proofirrelevance.
    use (fam_from_qq_mor_unique r2); assumption.
  - intros. apply idpath.
Qed.

End Strucs_Equiv_Precats.

Section Is_Category_Families_Strucs.

(*
(* TODO: inline *) 
Lemma isaprop_whatever
  (x : obj_ext_Precat C)
  (d d' : (families_disp_precat C) x)
  : isaprop (iso_disp (identity_iso x) d d').
Proof.
  apply isofhleveltotal2.
  - apply isaprop_families_mor.
  - intro. apply isaprop_is_iso_disp.
Qed.
*)

Definition iso_to_TM_eq
  (Y Y' : families_precategory)
  : iso Y Y' 
  -> TM (Y : families_structure _ X) = TM (Y' : families_structure _ X).
Proof.
  intro i.
  use isotoid.
  - apply (is_category_functor_category _ _ is_category_HSET).
  - exists (families_mor_TM (i : _ --> _)).
    apply is_iso_from_is_z_iso.
    exists (families_mor_TM (inv_from_iso i)).
    split.
    + exact (maponpaths families_mor_TM (iso_inv_after_iso i)).
    + exact (maponpaths families_mor_TM (iso_after_iso_inv i)).
Defined.

Lemma prewhisker_iso_to_TM_eq 
  {Y Y' : families_precategory}
  (FG : iso Y Y')
  {P : preShv C} (α : TM (Y : families_structure _ X) --> P)
: transportf (λ P' : preShv C, P' --> P) (iso_to_TM_eq  _ _ FG) α
  = families_mor_TM (*pr1 (pr2 FG)*) (inv_from_iso FG) ;; α.
Proof.
  etrans. apply transportf_isotoid.
  apply maponpaths_2.
  apply inv_from_iso_from_is_z_iso.
Qed.

Lemma postwhisker_iso_to_TM_eq 
  {Y Y' : families_precategory}
  (FG : iso Y Y')
  {P : preShv C} (α : P --> TM (Y : families_structure _ X))
: transportf (λ P' : preShv C, P --> P') (iso_to_TM_eq _ _ FG) α
  = α ;; families_mor_TM (pr1 FG).
Proof.
  apply postwhisker_isotoid.
Qed.

Definition iso_to_id_families_precategory
  (Y Y' : families_precategory)
  : iso Y Y' -> Y = Y'.
Proof.
  intros i.
  apply subtypeEquality. { intro. apply isaprop_families_structure_axioms. }
  apply total2_paths with (iso_to_TM_eq _ _ i).
  etrans. refine (transportf_dirprod _ _ _ _ _ _).
  apply dirprodeq; simpl.
  - etrans. apply prewhisker_iso_to_TM_eq.
    apply families_mor_pp. 
  - etrans. refine (transportf_forall _ _ _).
    apply funextsec; intros Γ.
    etrans. refine (transportf_forall _ _ _).
    apply funextsec; intros A.
    etrans. refine (postwhisker_iso_to_TM_eq i (Q _ _)).
    apply families_mor_Q.
Qed.

Lemma has_homsets_families_precategory
  : has_homsets families_precategory.
Proof.
  intros a b.
  apply isaset_total2.
  apply functor_category_has_homsets.
  intros. apply isasetaprop, isapropdirprod.
  apply functor_category_has_homsets.
  repeat (apply impred_isaprop; intro). apply functor_category_has_homsets.
Qed.

Theorem is_category_families_structure
  : is_category families_precategory.
Proof.
  split.
  - apply eq_equiv_from_retraction with iso_to_id_families_precategory.
    intros. apply eq_iso. apply isaprop_families_mor.
  - apply has_homsets_families_precategory. 
Qed.

End Is_Category_Families_Strucs.

Section Is_Category_qq_Strucs.

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

Lemma isaprop_iso_qq_morphism_structure 
  (d d' : qq_structure_precategory)
  : isaprop (iso d d').
Proof.
  apply (isofhleveltotal2 1).
  - do 4 (apply impred; intro).
    apply homset_property.
  - intro. apply isaprop_is_iso.
Qed.

Lemma qq_structure_eq 
  (x : obj_ext_structure C)
  (d d' : qq_morphism_structure x)
  (H : Π (Γ Γ' : C) (f : Γ' --> Γ) (A : (TY x : functor _ _ ) Γ : hSet), 
           qq d f A = qq d' f A)
  : d = d'.
Proof.
  apply subtypeEquality.
  { intro. apply (@isaprop_qq_morphism_axioms _ (homset_property _ )). }
  apply subtypeEquality.
  { intro. do 4 (apply impred; intro). 
           apply isofhleveltotal2.
     + apply homset_property.
     + intro. apply pullbacks.isaprop_isPullback.
  } 
  do 4 (apply funextsec; intro).
  apply H.
Defined.

Definition qq_structure_iso_to_id
(*  (x : obj_ext_structure C) *)
  (d d' : qq_structure_precategory)
  : iso d d' → d = d'.
Proof.
  intro H. 
  apply qq_structure_eq.
  intros Γ Γ' f A.
  apply (pr1 H).
Defined.  
  
Lemma has_homsets_qq_structure_precategory
  : has_homsets qq_structure_precategory.
Proof.
  intros a b. apply isasetaprop. apply isaprop_qq_structure_mor.
Qed.

Theorem is_category_qq_morphism
  : is_category qq_structure_precategory.
Proof.
  split.
  - intros d d'. 
    use isweqimplimpl. 
    + apply qq_structure_iso_to_id.
    + apply isaset_qq_morphism_structure.
    + apply isaprop_iso_qq_morphism_structure.
  - apply has_homsets_qq_structure_precategory.
Qed.

End Is_Category_qq_Strucs.

Lemma has_homsets_compat_structures_precategory  
  : has_homsets compat_structures_precategory.
Proof.
  intros a b.  
  apply isasetdirprod. 
  - apply has_homsets_families_precategory.
  - apply has_homsets_qq_structure_precategory. 
Qed.

Definition pr1_equiv : adj_equivalence_of_precats compat_structures_pr1_functor.
Proof.
  use adj_equivalence_of_precats_ff_split.
  - apply compat_structures_pr1_fully_faithful.
  - apply compat_structures_pr1_split_ess_surj.
Defined.

Definition pr2_equiv : adj_equivalence_of_precats compat_structures_pr2_functor.
Proof.
  use adj_equivalence_of_precats_ff_split.
  - apply compat_structures_pr2_fully_faithful.
  - apply compat_structures_pr2_split_ess_surj.
Defined.

Definition pr1_equiv_inv : adj_equivalence_of_precats (right_adjoint pr1_equiv).
Proof.
  use adj_equivalence_of_precats_inv.
  - apply has_homsets_compat_structures_precategory.
  - apply has_homsets_families_precategory.
Defined.

Definition equiv_of_structures : adj_equivalence_of_precats _ 
  := @comp_adj_equivalence_of_precats _ _ _ 
       has_homsets_families_precategory
       has_homsets_compat_structures_precategory
       has_homsets_qq_structure_precategory
       _ _ pr1_equiv_inv pr2_equiv.

Definition equiv_of_types_of_structures 
  : families_precategory ≃ qq_structure_precategory.
Proof.
  use (weq_on_objects_from_adj_equiv_of_cats _ _
           is_category_families_structure
           is_category_qq_morphism
           _
           equiv_of_structures).
Defined.

Lemma foo : equiv_of_types_of_structures ~ weq_CwF_SplitTypeCat X.
Proof.
  intro Y.
  apply idpath.
Defined.

Print Assumptions foo.

End fix_cat_obj_ext.


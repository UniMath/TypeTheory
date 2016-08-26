(**

 Ahrens, Lumsdaine, Voevodsky, 2015 - 2016

Main definitions:

- [families_precategory]
- [qq_structure_precategory]
*)

Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.more_on_pullbacks.

Require Import Systems.UnicodeNotations.
Require Import Systems.Auxiliary.
Require Import Systems.Structures.
Require UniMath.Ktheory.Precategories.
Require Import UniMath.Ktheory.StandardCategories.
Require Import Systems.CwF_SplitTypeCat_Maps.

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
  - intros Z; cbn.
    intros Γ Γ' f A. apply idpath.
(*
    etrans. apply id_right.
    apply pathsinv0.
    etrans. apply @pathsinv0, assoc. 
    etrans. apply id_left.
    etrans.
      apply cancel_postcomposition.
      apply comp_ext_compare_id_general.
    apply id_left.
*)
  - intros Z0 Z1 Z2.
    intros FF GG Γ Γ' f A. cbn.
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
  - 
    intros YZ YZ'.
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
  : ( Z --> Z'). (* , W -->[(F,,(FY,,FZ))] W'. *)
Proof.
(*
  refine (_,, tt).
*)
  intros Γ' Γ f A.
  cbn in W, W', FY. unfold iscompatible_fam_qq in *. 
  unfold families_mor in FY.
  apply (Q_pp_Pb_unique Y'); simpl; unfold yoneda_morphisms_data.
  - 
    (* etrans. apply @pathsinv0, assoc. *)
(*
    etrans. apply maponpaths, obj_ext_mor_ax.
*)
      (* TODO: name of [obj_ext_mor_ax] unmemorable.  Rename more like [qq_π]? *)
    etrans. apply @pathsinv0, qq_π.
      (* TODO: name of [qq_π] misleading, suggests opposite direction. *)
    apply pathsinv0.
(*
    etrans. apply @pathsinv0, assoc.
*)
    etrans. apply (* maponpaths, *) @pathsinv0, qq_π.
    apply idpath.
(*
    etrans. apply assoc. apply cancel_postcomposition.
    etrans. apply @pathsinv0, assoc.
    etrans. apply maponpaths. apply comp_ext_compare_π.
    apply obj_ext_mor_ax.
*)
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
Abort.   

(*
    etrans. 
      exact (!toforallpaths _ _ _ 
        (nat_trans_eq_pointwise (W' _ _ _ _) _) _ ).
    etrans. apply Q_comp_ext_compare.
    etrans. apply maponpaths, @pathsinv0, id_left.
    exact (!toforallpaths _ _ _
      (nat_trans_eq_pointwise (families_mor_Q FY _) _) _).
Time Qed.
*)

Lemma qq_from_fam_mor_unique 
  {Y : families_precategory} {Y'} (FY : Y --> Y')
  {Z : qq_structure_precategory} {Z'}
  (W : iscompatible_fam_qq Y Z)
  (W' : iscompatible_fam_qq Y Z')
  : isaprop (Z --> Z').
Proof.
  - simpl. repeat (apply impred_isaprop; intro). apply hsC.
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
(*
  etrans. 
    apply @pathsinv0.
    simple refine (Q_comp_ext_compare _ _); simpl.
    Focus 2. etrans. (*apply maponpaths.*)
      exact (toforallpaths _ _ _ (nat_trans_ax (pp Y) _ _ _) _).
    exact (toforallpaths _ _ _ (nat_trans_ax (obj_ext_mor_TY F) _ _ _) _).
  etrans.
    exact (toforallpaths _ _ _ (nat_trans_eq_pointwise (W' _ _ _ _) _) _).
  apply (maponpaths ((Q _ _ : nat_trans _ _ ) Γ)).
  simpl. unfold yoneda_morphisms_data.
  (* Part 2: naturality of the transfer along [F]. *)
  etrans. apply @pathsinv0, assoc.
  etrans. apply @pathsinv0, assoc.
  etrans. apply maponpaths.
    etrans. apply assoc. 
    etrans. apply cancel_postcomposition. Focus 2.
      apply @pathsinv0. 
      etrans. Focus 2. apply assoc. 
      apply maponpaths, FZ.
    etrans. Focus 2. apply @pathsinv0, assoc.
    etrans. Focus 2. apply cancel_postcomposition.
      apply @pathsinv0, Δ_φ.
    etrans. Focus 2. apply assoc.
    apply maponpaths, comp_ext_compare_comp.
  etrans. apply assoc.
  etrans. apply assoc.
  etrans. Focus 2. apply @pathsinv0, assoc.
  apply cancel_postcomposition.
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
*)
Admitted.

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
(*
    etrans. refine (toforallpaths _ _ _(!nat_trans_ax (obj_ext_mor_TY _) _ _ _) _).
*)
(*
    cbn; apply maponpaths.
*)
    etrans.
      refine (toforallpaths _ _ _ _ ((pp Y : nat_trans _ _) Γ t)).
      apply maponpaths.
(*
      etrans. apply @pathsinv0, assoc.
      etrans. apply maponpaths, obj_ext_mor_ax.
*)
      exact (pr2 (term_to_section _)).
    exact (toforallpaths _ _ _ (functor_id (TY _) _) _).
  - apply has_homsets_HSET.
  - intros Γ'. unfold yoneda_morphisms_data, yoneda_objects_ob; cbn.
    apply funextsec; intros f.

(*  checks until here   *)

(*
    etrans.
      (* TODO: consider changing direction of [Q_comp_ext_compare]?*)
      apply @pathsinv0. simple refine (Q_comp_ext_compare _ _); simpl.
        exact ((obj_ext_mor_TY F : nat_trans _ _) _ 
                 (# (TY _ : functor _ _) (f ;; π _) A)). 
      apply maponpaths.
      refine (!toforallpaths _ _ _ (nat_trans_eq_pointwise (Q_pp _ _) _) _).
    cbn.
    Arguments Δ [_ _ _ _ _ _]. idtac.
    etrans. apply maponpaths.
      etrans. apply @pathsinv0, assoc.
      etrans. apply maponpaths, @pathsinv0, Δ_φ.
      apply assoc.
    etrans. 
      apply @pathsinv0. simple refine (Q_comp_ext_compare _ _); simpl.
        exact (# (TY _ : functor _ _) (f ;; π _)
                 ((obj_ext_mor_TY F : nat_trans _ _) _ A)).
      exact (toforallpaths _ _ _ (nat_trans_ax (obj_ext_mor_TY F) _ _ _) _).
    cbn.
    etrans. exact (toforallpaths _ _ _ (nat_trans_eq_pointwise (W' _ _ _ _) _) _).
    simpl; unfold yoneda_morphisms_data; cbn.  apply maponpaths.
    etrans. apply @pathsinv0, assoc.
    etrans. apply @pathsinv0, assoc.
    etrans. apply maponpaths.
      etrans. apply assoc.
      apply @pathsinv0, FZ.
    etrans. apply assoc.
    apply cancel_postcomposition.
  apply (map_from_term_recover W).
Time Qed.
*)
Admitted.

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

(* TODO: could strengthen to “explicitly essentially surjective” *)
Lemma compat_structures_pr1_ess_surj
  : essentially_surjective (compat_structures_pr1_functor).
Proof.
  unfold essentially_surjective.
(*
  intros XY; destruct XY as [X Y]; apply hinhpr.
*)
  intro Y.
  apply hinhpr.
  exists (((Y,, qq_from_fam Y)),,iscompatible_qq_from_fam Y).
  apply identity_iso.
Qed.

Lemma compat_structures_pr1_fully_faithful
  : fully_faithful (compat_structures_pr1_functor).
Proof.
  intros YZW YZW'.
  destruct YZW as [  [Y Z]  W].
  destruct YZW' as [ [Y' Z']  W'].
  unfold compat_structures_pr1_functor; simpl.
Abort.
(*
  assert (structural_lemma :
    Π A (B C : A -> UU) (D : Π a, B a -> C a -> UU)
      (H : Π a b, iscontr (Σ c, D a b c)),
    isweq (fun abcd : Σ (abc : Σ a, (B a × C a)),
                        D (pr1 abc) (pr1 (pr2 abc)) (pr2 (pr2 abc))
            => (pr1 (pr1 abcd),, pr1 (pr2 (pr1 abcd))))).
    clear C X Y Z W  Y' Z' W'.
  { intros A B C D H.
    use gradth.
    + intros ab.
      set (cd := iscontrpr1 (H (pr1 ab) (pr2 ab))). 
        exact ((pr1 ab,, (pr2 ab,, pr1 cd)),, pr2 cd).
    + intros abcd; destruct abcd as [ [a [b c] ] d]; simpl.
      refine (@maponpaths _ _ 
        (fun cd : Σ c' : C a, (D a b c') => (a,, b,, (pr1 cd)),, (pr2 cd))
        _ (_,, _) _).
      apply proofirrelevancecontr, H.
    + intros ab; destruct ab as [a b]. apply idpath. }
  simple refine (structural_lemma _ _ _ _ _).
  - intros FX FY FZ.
      exists (W -->[FX,,(FY,,FZ)] W').
  - intros FX FY. apply iscontraprop1.
    exact (qq_from_fam_mor_unique FY W W').
    exact (qq_from_fam_mor FY W W').
Qed.
*)
(* TODO: could strengthen to “explicitly essentially surjective” *)
Lemma compat_structures_pr2_ess_surj
  : essentially_surjective (compat_structures_pr2_functor).
Proof.
  unfold essentially_surjective.
  intros Z; apply hinhpr.
  exists (((fam_from_qq Z,, Z)),,iscompatible_fam_from_qq Z).
  apply identity_iso.
Qed.

Lemma compat_structures_pr2_fully_faithful
  : fully_faithful (compat_structures_pr2_functor).
Proof.
  intros YZW YZW';
  destruct YZW as [  [Y Z]  W];
  destruct YZW' as [  [Y' Z']  W'].
  unfold compat_structures_pr2_functor; simpl.
Abort.
(*
  assert (structural_lemma :
    Π A (B C : A -> UU) (D : Π a, B a -> C a -> UU)
      (H : Π a c, iscontr (Σ b, D a b c)),
    isweq (fun abcd : Σ (abc : Σ a, (B a × C a)),
                        D (pr1 abc) (pr1 (pr2 abc)) (pr2 (pr2 abc))
            => (pr1 (pr1 abcd),, pr2 (pr2 (pr1 abcd))))).
    clear C X Y Z W  Y' Z' W'.
  { intros A B C D H.
    use gradth.
    + intros ac.
      set (bd := iscontrpr1 (H (pr1 ac) (pr2 ac))). 
        exact ((pr1 ac,, (pr1 bd,, pr2 ac)),, pr2 bd).
    + intros abcd; destruct abcd as [ [a [b c] ] d]; simpl.
      refine (@maponpaths _ _ 
        (fun bd : Σ b' : B a, (D a b' c) => (a,, (pr1 bd),, c),, (pr2 bd))
        _ (_,, _) _).
      apply proofirrelevancecontr, H.
    + intros ac; destruct ac as [a c]. apply idpath. }
  simple refine (structural_lemma _ _ _ _ _).
  - intros FX FY FZ.
      exists (W -->[FX,,(FY,,FZ)] W').
  - intros FX FY. apply iscontraprop1.
    exact (fam_from_qq_mor_unique FY W W').
    exact (fam_from_qq_mor FY W W').
Qed.
*)
End Strucs_Equiv_Precats.

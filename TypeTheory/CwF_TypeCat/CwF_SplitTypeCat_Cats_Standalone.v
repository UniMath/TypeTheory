(**
  [TypeTheory.CwF_TypeCat.CwF_SplitTypeCat_Cats_Standalone]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**

This file defines the categories of term-structures and _q_-morphism structures over a fixed object-extension structure, and proves that they are univalent and equivalent.

For the more interesting case where the object-extension structure is also allowed to vary, see [CwF_Split_TypeCat_Cats], where this more general category is constructed, using the formalism of displayed categories, and [CwF_SplitTypeCat_Equiv_Cats], giving the equivalence in the displayed setting.

In general, this file should be deprecated, and the displayed version should be used for all further development.  This standalone version is included just to give the equivalence in a form independent of the development of displayed categories.


Main definitions:

- [term_fun_precategory]
- [qq_structure_precategory]
- category of compatible pairs
- projection functors from compatible pairs to structures
- proof that those projection functors are split and ff

*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheory.
Require Import TypeTheory.Auxiliary.SetsAndPresheaves.

Require Import TypeTheory.CwF_TypeCat.CwF_SplitTypeCat_Defs.
Require Import TypeTheory.CwF_TypeCat.CwF_SplitTypeCat_Maps.
Require Import TypeTheory.CwF_TypeCat.CwF_SplitTypeCat_Equivalence.


(** Some local notations, *)

Local Notation "Γ ◂ A" := (comp_ext _ Γ A) (at level 30).
Local Notation "'Ty'" := (fun X Γ => TY X $p Γ) (at level 10).
Local Notation "'Tm'" := (fun Y Γ => TM Y $p Γ) (at level 10).

Local Notation Δ := comp_ext_compare.

Section fix_cat_obj_ext.

Variable C : category.
Variable X : obj_ext_structure C.


(** * category of term-structures *)
Section Term_Fun_Structure_Precat.

Definition term_fun_mor 
    (Y Y' : term_fun_structure C X) 
  : UU
:= ∑ FF_TM : TM Y --> TM Y',
       FF_TM ;; pp Y' = pp Y 
     × 
       ∏ {Γ:C} {A : Ty X Γ},
           FF_TM $nt (te Y A) = te Y' _.


Definition term_fun_mor_TM {Y Y'} (FF : term_fun_mor Y Y')
  : _ --> _
:= pr1 FF.

Definition term_fun_mor_pp {Y Y'} (FF : term_fun_mor Y Y')
  : term_fun_mor_TM FF ;; pp Y' = pp Y 
:= pr1 (pr2 FF).

Definition term_fun_mor_te {Y Y'} (FF : term_fun_mor Y Y')
    {Γ:C} (A : Ty X Γ)
  : term_fun_mor_TM FF $nt (te Y A) = (te Y' _)
:= pr2 (pr2 FF) Γ A.

Definition term_fun_mor_Q {Y Y'} (FF : term_fun_mor Y Y')
    {Γ:C} (A : Ty X Γ)
  : Q Y A ;; term_fun_mor_TM FF = Q Y' _.
Proof.
  apply nat_trans_eq. apply homset_property.
  intros Γ'; simpl in Γ'.
  unfold yoneda_objects_ob. apply funextsec; intros f.
  etrans. apply nat_trans_ax_pshf.
  cbn. apply maponpaths, term_fun_mor_te.
Qed.

(* Defined only locally, since once [isaprop_term_fun_mor_eq] is defined, that should always be used in place of this. *)
Local Lemma term_fun_mor_eq {Y} {Y'} (FF FF' : term_fun_mor Y Y')
    (e_TM : ∏ Γ (t : Tm Y Γ),
      term_fun_mor_TM FF $nt t
      = term_fun_mor_TM FF' $nt t)
  : FF = FF'.
Proof.
  apply subtypePath.
  - intros x; apply isapropdirprod.
    + apply homset_property.
    + repeat (apply impred_isaprop; intro). apply setproperty.
  - apply nat_trans_eq. apply has_homsets_HSET. 
    intros Γ. apply funextsec. unfold homot. apply e_TM.
Qed.


(* This is not full naturality of [term_to_section]; it is just what is required for [isaprop_term_fun_mor] below. *)
Lemma term_to_section_naturality {Y} {Y'}
  {FY : term_fun_mor Y Y'}
  {Γ : C} (t : Tm Y Γ) (A := pp Y $nt t)
  : pr1 (term_to_section (term_fun_mor_TM FY $nt t))
  = pr1 (term_to_section t) 
   ;; Δ (!nat_trans_eq_pointwise_pshf (term_fun_mor_pp FY) _).
Proof.
  set (t' := term_fun_mor_TM FY $nt t).
  set (A' := pp Y' $nt t').
  set (Pb := isPullback_preShv_to_pointwise (isPullback_Q_pp Y' A') Γ);
    simpl in Pb.
  apply (pullback_HSET_elements_unique Pb); clear Pb.
  - unfold yoneda_morphisms_data; cbn.
    etrans. use (pr2 (term_to_section t')). apply pathsinv0.
    etrans. 2: { refine (pr2 (term_to_section t)). }
    etrans. apply @pathsinv0, assoc.
    apply maponpaths.
    apply comp_ext_compare_π.
  - etrans. apply term_to_section_recover. 
    apply pathsinv0.
    etrans. apply Q_comp_ext_compare.
    etrans.
      eapply pathsinv0, nat_trans_eq_pointwise_pshf, term_fun_mor_Q.
    cbn. apply maponpaths, term_to_section_recover.
Qed.

Lemma term_fun_mor_recover_term  {Y} {Y'}
  {FY : term_fun_mor Y Y'}
  {Γ : C} (t : Tm Y Γ)
  : term_fun_mor_TM FY $nt t
  = Q Y' _ $nt (pr1 (term_to_section t) ).
Proof.
  etrans. apply @pathsinv0, term_to_section_recover.
  etrans. apply maponpaths, term_to_section_naturality.
  apply Q_comp_ext_compare.
Qed.

Lemma isaprop_term_fun_mor {Y} {Y'}
  : isaprop (term_fun_mor Y Y').
Proof.
  apply invproofirrelevance; intros FF FF'. apply term_fun_mor_eq.
  intros Γ t.
  etrans. apply term_fun_mor_recover_term.
  apply @pathsinv0. apply term_fun_mor_recover_term.
Qed.


Definition term_fun_ob_mor : precategory_ob_mor. 
Proof.
  exists (term_fun_structure C X).
  exact @term_fun_mor.
Defined.

Definition term_fun_id_comp : precategory_id_comp term_fun_ob_mor.
Proof.
  apply tpair.
  - intros Y. simpl; unfold term_fun_mor.
    exists (identity _). apply tpair.
    + apply id_left. 
    + intros Γ A. apply idpath.
  - intros Y0 Y1 Y2 FF GG.
    exists (term_fun_mor_TM FF ;; term_fun_mor_TM GG). apply tpair.
    + etrans. apply @pathsinv0. apply assoc.
      etrans. apply maponpaths, term_fun_mor_pp.
      apply term_fun_mor_pp.
    + intros Γ A.
      etrans. cbn. apply maponpaths, term_fun_mor_te.
      apply term_fun_mor_te.
Defined.

Definition term_fun_data : precategory_data 
  := (_ ,, term_fun_id_comp).

Definition term_fun_axioms : is_precategory term_fun_data.
Proof.
  use make_is_precategory_one_assoc; intros; apply isaprop_term_fun_mor.
Qed.

Definition term_fun_precategory : precategory 
  := (_ ,, term_fun_axioms).

Lemma has_homsets_term_fun_precat 
  : has_homsets term_fun_precategory.
Proof.
  intros a b. apply isaset_total2.
  apply homset_property.
  intros. apply isasetaprop, isapropdirprod.
  apply homset_property.
  repeat (apply impred_isaprop; intro). apply setproperty.
Qed.

End Term_Fun_Structure_Precat.

(** * category of _q_-morphism-structures *)

Section qq_Structure_Precat.

Definition qq_structure_ob_mor : precategory_ob_mor.
Proof.
  exists (qq_morphism_structure X).
  intros Z Z'.
  use (∏ Γ' Γ (f : C ⟦ Γ' , Γ ⟧) (A : Ty X Γ), _).
  use (qq Z f A  = _).
  use (qq Z' f).
Defined.

Lemma isaprop_qq_structure_mor
  (Z Z' : qq_structure_ob_mor)
  : isaprop (Z --> Z').
Proof.
  repeat (apply impred_isaprop; intro). apply homset_property. 
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
  - exact (∑ YZ : (term_fun_precategory × qq_structure_precategory), 
                  iscompatible_term_qq (pr1 YZ) (pr2 YZ)).
  - intros YZ YZ'.
    exact ((pr1 (pr1 YZ)) --> (pr1 (pr1 YZ'))
           × (pr2 (pr1 YZ)) --> pr2 (pr1 YZ')).
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
  use make_is_precategory_one_assoc; intros.
  - apply dirprodeq; apply id_left.
  - apply dirprodeq; apply id_right.
  - apply dirprodeq; apply assoc.
Qed.

Definition compat_structures_precategory
  : precategory 
:= ( _ ,, strucs_compat_axioms).

(* should this be the name of the compatible pairs category? *)
(*
Definition compat_structures_disp_cat
  := sigma_disp_cat strucs_compat_disp_cat.
*)


Definition compat_structures_pr1_functor
  : functor compat_structures_precategory term_fun_precategory.
Proof.
  use tpair.
  - use tpair.
    + exact (fun YZp => pr1 (pr1 YZp)).
    + intros a b f. apply (pr1 f).
  - use tpair.
    + intro c. apply idpath.
    + intros a b c f g. apply idpath.
Defined.

Definition compat_structures_pr2_functor
  : functor compat_structures_precategory qq_structure_precategory.
Proof.
  use tpair.
  - use tpair.
    + exact (fun YZp => pr2 (pr1 YZp)).
    + intros a b f. apply (pr2 f).
  - use tpair.
    + intro c. apply idpath.
    + intros a b c f g. apply idpath.
Defined.


End Compatible_Disp_Cat.

Section Unique_QQ_From_Term.

Lemma qq_from_term_ob (Y : term_fun_precategory)
  : ∑ (Z : qq_structure_precategory), iscompatible_term_qq Y Z.
Proof.
  exists (qq_from_term Y).
  apply iscompatible_qq_from_term.
Defined.

Lemma qq_from_term_mor 
  {Y : term_fun_precategory} {Y'} (FY : Y --> Y')
  {Z : qq_structure_precategory} {Z'}
  (W : iscompatible_term_qq Y Z)
  (W' : iscompatible_term_qq Y' Z')
  : Z --> Z'. 
Proof.
  intros Γ' Γ f A.
  cbn in W, W', FY. unfold iscompatible_term_qq in *. 
  unfold term_fun_mor in FY.
  apply (Q_pp_Pb_unique Y'); simpl; unfold yoneda_morphisms_data.
  - etrans. apply qq_π.
    apply pathsinv0, qq_π.
  - etrans. cbn. apply maponpaths, @pathsinv0, (term_fun_mor_te FY).
    etrans. apply pathsinv0, nat_trans_ax_pshf.
    etrans. cbn. apply maponpaths, @pathsinv0, W.
    etrans. apply term_fun_mor_te.
    apply W'.
Qed.


Lemma qq_from_term_mor_unique 
  {Y : term_fun_precategory} {Y'} (FY : Y --> Y')
  {Z : qq_structure_precategory} {Z'}
  (W : iscompatible_term_qq Y Z)
  (W' : iscompatible_term_qq Y' Z')
  : isaprop (Z --> Z').
Proof.
  simpl. repeat (apply impred_isaprop; intro). apply homset_property.
Qed.

End Unique_QQ_From_Term.

Section Unique_Term_From_QQ.

Lemma term_from_qq_ob (Z : qq_structure_precategory)
  : ∑ (Y : term_fun_precategory), iscompatible_term_qq Y Z.
Proof.
  exists (term_from_qq Z).
  apply iscompatible_term_from_qq.
Defined.

(** The next main goal is the following statement.  However, the construction of the morphism of term structures is rather large; so we break out the first component (the map of term presheaves) into several independent lemmas, before returning to this in [term_from_qq_mor] below. *)
Lemma term_from_qq_mor
  {Z Z' : qq_structure_precategory} (FZ : Z --> Z')
  {Y : term_fun_precategory} {Y'}
  (W : iscompatible_term_qq Y Z)
  (W' : iscompatible_term_qq Y' Z')
  : (Y --> Y').
Abort.

(* TODO: rename and upstream this section! *)
Section Rename_me.
(* TODO: naming conventions in this section clash rather with those of [CwF_TypeCat.CwF_SplitTypeCat_Equivalence]. Consider! *)
Lemma tm_from_qq_mor_data {Z Z' : qq_structure_precategory} (FZ : Z --> Z')
  : nat_trans_data (tm_from_qq Z) (tm_from_qq Z').
Proof.
  intros Γ Ase; exact Ase. (* ! *)
Defined.

Lemma tm_from_qq_mor_naturality
    {Z Z' : qq_structure_precategory} (FZ : Z --> Z')
  : is_nat_trans (tm_from_qq Z) (tm_from_qq Z') (tm_from_qq_mor_data FZ).
Proof.
  intros Γ Γ' f; cbn in Γ, Γ', f.
  apply funextsec; intros [A [s e]].
  use tm_from_qq_eq.
  - apply idpath.
  - etrans. apply id_right.
    cbn. apply PullbackArrowUnique.
    + set (XX := (make_Pullback _ (qq_π_Pb (pr1 Z) f A))).
      apply (PullbackArrow_PullbackPr1 XX).
    + cbn; cbn in FZ. etrans. apply maponpaths, @pathsinv0, FZ.
      apply (PullbackArrow_PullbackPr2 (make_Pullback _ _)). 
Qed.

Lemma tm_from_qq_mor_TM {Z Z' : qq_structure_precategory} (FZ : Z --> Z')
  : nat_trans (tm_from_qq Z) (tm_from_qq Z').
Proof.
  exists (tm_from_qq_mor_data FZ).
  apply tm_from_qq_mor_naturality.
Defined.

Lemma tm_from_qq_mor_pp {Z Z' : qq_structure_precategory} (FZ : Z --> Z')
  : (tm_from_qq_mor_TM FZ : preShv C ⟦ _ , _ ⟧) ;; pp_from_qq Z'
  = pp_from_qq Z.
Proof.
  apply nat_trans_eq. apply homset_property.
  intros Γ. apply idpath.
Qed.

Lemma tm_from_qq_mor_te {Z Z' : qq_structure_precategory} (FZ : Z --> Z')
    {Γ} (A : Ty X Γ)
  : tm_from_qq_mor_TM FZ _ (te_from_qq Z A) = (te_from_qq Z' A).
Proof.
  cbn.
  use tm_from_qq_eq.
  - apply idpath.
  - etrans. apply id_right. 
    cbn. apply PullbackArrowUnique.
    + cbn. apply (PullbackArrow_PullbackPr1 (make_Pullback _ _)).
    + cbn. cbn in FZ. 
      etrans. apply maponpaths, @pathsinv0, FZ.
      apply (PullbackArrow_PullbackPr2 (make_Pullback _ _)). 
Qed.

End Rename_me.

Definition term_from_qq_mor_TM 
    {Z : qq_structure_precategory} {Z'} (FZ : Z --> Z')
    {Y : term_fun_precategory} {Y'}
    (W : iscompatible_term_qq Y Z)
    (W' : iscompatible_term_qq Y' Z')
  : TM (Y : term_fun_structure _ _) --> TM (Y' : term_fun_structure _ _).
Proof.
  use ( _ ;; (tm_from_qq_mor_TM FZ : preShv C ⟦ _ , _ ⟧) ;; _).
  - exact (given_TM_to_canonical _ _ (Y,,W)).
  - exact (canonical_TM_to_given _ _ (Y',,W')).
Defined.

Lemma term_from_qq_mor
  {Z : qq_structure_precategory} {Z'} (FZ : Z --> Z')
  {Y : term_fun_precategory} {Y'}
  (W : iscompatible_term_qq Y Z)
  (W' : iscompatible_term_qq Y' Z')
  : (Y --> Y').
Proof.
  simpl in W, W'; unfold iscompatible_term_qq in W, W'. (* Readability *)
  simpl in Y, Y'.  (* To avoid needing casts [Y : term_fun_structure _]. *)
  simpl; unfold term_fun_mor.
  exists (term_from_qq_mor_TM FZ W W').
  apply make_dirprod; try intros Γ A.
  - etrans. apply @pathsinv0, assoc.
    etrans. apply maponpaths, (pp_canonical_TM_to_given _ _ (_,,_)).
    etrans. apply @pathsinv0, assoc.
    etrans. apply maponpaths, tm_from_qq_mor_pp.
    apply (pp_given_TM_to_canonical _ _ (_,,_)).
  - unfold term_from_qq_mor_TM.
    cbn.
    etrans. apply maponpaths, (given_TM_to_canonical_te _ _ (_,,W)).
    etrans. apply maponpaths, (tm_from_qq_mor_te FZ).
    apply (canonical_TM_to_given_te _ _ (_,,_)).
Qed.

Lemma term_from_qq_mor_unique 
  {Z : qq_structure_precategory} {Z'} (FZ : Z --> Z')
  {Y : term_fun_precategory} {Y'}
  (W : iscompatible_term_qq Y Z)
  (W' : iscompatible_term_qq Y' Z')
  : isaprop ( Y --> Y').
Proof.
  simpl. apply isaprop_term_fun_mor.
Defined.

End Unique_Term_From_QQ.


Section Strucs_Equiv_Precats.

Lemma compat_structures_pr1_split_ess_surj
  : split_ess_surj (compat_structures_pr1_functor).
Proof.
  intro Y.
  exists (((Y,, qq_from_term Y)),,iscompatible_qq_from_term Y).
  apply identity_z_iso.
Defined.

Lemma compat_structures_pr1_fully_faithful
  : fully_faithful (compat_structures_pr1_functor).
Proof.
  intros YZW YZW'.
  destruct YZW as [  [Y Z]  W].
  destruct YZW' as [ [Y' Z']  W'].
  unfold compat_structures_pr1_functor; simpl.
  use gradth.
  - intro f. exists f. use (qq_from_term_mor f W W').
  - intros. cbn. destruct x as [f q]. cbn.
    apply maponpaths.
    apply proofirrelevance.
    use (qq_from_term_mor_unique f); assumption. 
  - intros y. cbn. apply idpath.
Qed.

Lemma compat_structures_pr2_split_ess_surj
  : split_ess_surj (compat_structures_pr2_functor).
Proof.
  intros Z.
  exists (((term_from_qq Z,, Z)),,iscompatible_term_from_qq Z).
  apply identity_z_iso.
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
    exists (term_from_qq_mor x W W').
    exact x.
  - intro r. cbn.
    destruct r as [r1 r2]. apply maponpaths_2.
    apply proofirrelevance.
    use (term_from_qq_mor_unique r2); assumption.
  - intros. apply idpath.
Qed.

End Strucs_Equiv_Precats.

Section Is_Univalent_Families_Strucs.


Definition iso_to_TM_eq
  (Y Y' : term_fun_precategory)
  : z_iso Y Y' 
  -> TM (Y : term_fun_structure _ X) = TM (Y' : term_fun_structure _ X).
Proof.
  intro i.
  use isotoid.
  - apply univalent_category_is_univalent.
  - exists (term_fun_mor_TM (i : _ --> _)).
    exists (term_fun_mor_TM (inv_from_z_iso i)).
    split.
    + exact (maponpaths term_fun_mor_TM (z_iso_inv_after_z_iso i)).
    + exact (maponpaths term_fun_mor_TM (z_iso_after_z_iso_inv i)).
Defined.

Lemma prewhisker_iso_to_TM_eq 
  {Y Y' : term_fun_precategory}
  (FG : z_iso Y Y')
  {P : preShv C} (α : TM (Y : term_fun_structure _ X) --> P)
: transportf (λ P' : preShv C, P' --> P) (iso_to_TM_eq  _ _ FG) α
  = term_fun_mor_TM (inv_from_z_iso FG) ;; α.
Proof.
  etrans. apply transportf_isotoid.
  apply maponpaths_2.
  apply inv_from_z_iso_from_is_z_iso.
Qed.

Lemma postwhisker_iso_to_TM_eq 
  {Y Y' : term_fun_precategory}
  (FG : z_iso Y Y')
  {P : preShv C} (α : P --> TM (Y : term_fun_structure _ X))
: transportf (λ P' : preShv C, P --> P') (iso_to_TM_eq _ _ FG) α
  = α ;; term_fun_mor_TM (pr1 FG).
Proof.
  use postwhisker_isotoid.
Qed.

Lemma idtoiso_iso_to_TM_eq 
  {Y Y' : term_fun_precategory}
  (FG : z_iso Y Y')
: (idtoiso (iso_to_TM_eq _ _ FG) : _ --> _)
  = term_fun_mor_TM (FG : _ --> _).
Proof.
  use (maponpaths pr1 (idtoiso_isotoid _ _ _ _ _)).
Qed.

Definition iso_to_id_term_fun_precategory
  (Y Y' : term_fun_precategory)
  : z_iso Y Y' -> Y = Y'.
Proof.
  intros i.
  apply subtypePath. { intro. apply isaprop_term_fun_structure_axioms. }
  apply total2_paths_f with (iso_to_TM_eq _ _ i).
  rewrite transportf_dirprod.
  apply dirprodeq.
  - etrans. apply prewhisker_iso_to_TM_eq.
    apply term_fun_mor_pp. 
  - etrans. use transportf_forall.
    apply funextsec; intros Γ.
    etrans. use transportf_forall.
    apply funextsec; intros A.
    etrans. apply transportf_pshf.
    etrans.
      refine (toforallpaths _ (te _ _)).
      refine (toforallpaths _ _).
      apply maponpaths, idtoiso_iso_to_TM_eq.
    apply term_fun_mor_te.
Qed.

Lemma has_homsets_term_fun_precategory
  : has_homsets term_fun_precategory.
Proof.
  intros a b.
  apply isaset_total2.
  apply homset_property.
  intros. apply isasetaprop, isapropdirprod.
  apply homset_property.
  repeat (apply impred_isaprop; intro). apply setproperty.
Qed.

Definition term_fun_category : category
  := make_category _ has_homsets_term_fun_precategory.

Theorem is_univalent_term_fun_structure
  : is_univalent term_fun_category.
Proof.
  use eq_equiv_from_retraction.
  - apply iso_to_id_term_fun_precategory.
  - intros. apply z_iso_eq. apply isaprop_term_fun_mor.
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

Lemma has_homsets_qq_structure_precategory
  : has_homsets qq_structure_precategory.
Proof.
  intros a b. apply isasetaprop. apply isaprop_qq_structure_mor.
Qed.

Definition qq_structure_category : category
  := make_category _ has_homsets_qq_structure_precategory.


Lemma isaprop_iso_qq_morphism_structure 
  (d d' : qq_structure_category)
  : isaprop (z_iso d d').
Proof.
  apply (isofhleveltotal2 1).
  - do 4 (apply impred; intro).
    apply homset_property.
  - intro. apply isaprop_is_z_isomorphism.
Qed.

Lemma qq_structure_eq 
  (x : obj_ext_structure C)
  (d d' : qq_morphism_structure x)
  (H : ∏ (Γ Γ' : C) (f : Γ' --> Γ) (A : Ty x Γ), 
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

Definition qq_structure_iso_to_id
  (d d' : qq_structure_precategory)
  : z_iso d d' → d = d'.
Proof.
  intro H. 
  apply qq_structure_eq.
  intros Γ Γ' f A.
  use (pr1 H).
Defined.  

Theorem is_univalent_qq_morphism
  : is_univalent qq_structure_category.
Proof.
  intros d d'. 
  use isweqimplimpl. 
  + apply qq_structure_iso_to_id.
  + apply isaset_qq_morphism_structure.
  + apply isaprop_iso_qq_morphism_structure.
Qed.

End Is_Univalent_qq_Strucs.

Lemma has_homsets_compat_structures_precategory  
  : has_homsets compat_structures_precategory.
Proof.
  intros a b.  
  apply isasetdirprod. 
  - apply has_homsets_term_fun_precategory.
  - apply has_homsets_qq_structure_precategory. 
Qed.

Definition compat_structures_category : category
  := make_category _ has_homsets_compat_structures_precategory.

Definition pr1_equiv : @adj_equivalence_of_cats
                         compat_structures_category
                         term_fun_category
                         compat_structures_pr1_functor.
Proof.
  use adj_equivalence_of_cats_ff_split.
  - apply compat_structures_pr1_fully_faithful.
  - apply compat_structures_pr1_split_ess_surj.
Defined.

Definition pr2_equiv : @adj_equivalence_of_cats
                         compat_structures_category
                         qq_structure_category
                         compat_structures_pr2_functor.
Proof.
  use adj_equivalence_of_cats_ff_split.
  - apply compat_structures_pr2_fully_faithful.
  - apply compat_structures_pr2_split_ess_surj.
Defined.

Definition pr1_equiv_inv : adj_equivalence_of_cats (right_adjoint pr1_equiv).
Proof.
  use adj_equivalence_of_cats_inv.
Defined.

Definition equiv_of_structures : adj_equivalence_of_cats _ 
  := @comp_adj_equivalence_of_cats _ _ _ _ _ 
                                      pr1_equiv_inv pr2_equiv.

Definition equiv_of_types_of_structures 
  : term_fun_precategory ≃ qq_structure_precategory.
Proof.
  use (weq_on_objects_from_adj_equiv_of_cats _ _
           is_univalent_term_fun_structure
           is_univalent_qq_morphism
           _
           equiv_of_structures).
Defined.


Lemma equiv_of_types_equal_direct_constr 
  : equiv_of_types_of_structures ~ weq_term_qq X.
Proof.
  intro Y.
  apply idpath.
Defined.

(* Print Assumptions equiv_of_types_equal_direct_constr. *)

End fix_cat_obj_ext.


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

Require Import Systems.Bicats.Auxiliary.
Require Import Systems.Bicats.Displayed_Precats.

Local Set Automatic Introduction.
(* only needed since imports globally unset it *)


(** Some local notations, *)

Local Notation "Γ ◂ A" := (comp_ext _ Γ A) (at level 30).
Local Notation "'Ty'" := (fun X Γ => (TY X : functor _ _) Γ : hSet) (at level 10).
Local Notation "'Tm'" := (fun Y Γ => (TM Y : functor _ _) Γ : hSet) (at level 10).

(* TODO: as ever, upstream to [Systems.Auxiliary], and look for in library. *)
Section Auxiliary.

End Auxiliary.

Local Notation Δ := comp_ext_compare.
 
(** * Precategory of object-extension structures *)
Section Obj_Ext_Precat.

Context {C : Precategory}.
Local Notation hsC := (homset_property C).

Definition obj_ext_mor (X X' : obj_ext_structure C)
  := Σ F_TY : TY X ⇒ TY X',
       ∀ {Γ:C} {A : Ty X Γ},
         Σ φ : (Γ ◂ A ⇒ Γ ◂ ((F_TY : nat_trans _ _) _ A)),
           φ ;; π _ = π A.

Definition obj_ext_mor_TY {X X'} (F : obj_ext_mor X X') : _ ⇒ _
  := pr1 F.

(* TODO: is this actually useful?  Maybe remove. *)
Notation "F [ A ]" := ((obj_ext_mor_TY F : nat_trans _ _) _ A) (at level 4) : TY_scope.
Delimit Scope TY_scope with TY.
Bind Scope TY_scope with TY.
Open Scope TY_scope.

Definition obj_ext_mor_φ {X X'} (F : obj_ext_mor X X')
    {Γ:C} (A : Ty X Γ)
  : Γ ◂ A ⇒ Γ ◂ F[ A ]
:= pr1 (pr2 F _ _).

Local Notation φ := obj_ext_mor_φ.

Definition obj_ext_mor_ax {X X'} (F : obj_ext_mor X X')
    {Γ:C} (A : Ty X Γ)
  : φ F A ;; π _ = π A
:= pr2 (pr2 F _ _).

(* TODO: try to speed up? *)
Lemma obj_ext_mor_eq {X X'} (F F' : obj_ext_mor X X')
  (e_TY : ∀ Γ (A : Ty X Γ), F [ A ] = F' [ A ])
  (e_comp : ∀ Γ (A : Ty X Γ),
    φ F A ;; @Δ _ _ _ _ _ (e_TY _ _)
    = φ F' A)
  : F = F'.
Proof.
  use total2_paths.
    apply nat_trans_eq. apply has_homsets_HSET.
    intros Γ; apply funextsec; intros A.
    apply e_TY.
  apply funextsec; intros Γ; apply funextsec; intros A.
  use total2_paths. Focus 2. apply hsC.
  refine (_ @ e_comp Γ A).
  etrans.
    apply maponpaths.
    refine (toforallpaths _ _ _ _ _).
    etrans. refine (toforallpaths _ _ _ _ _).
      refine (transportf_forall _ _ _). simpl.
    refine (transportf_forall _ _ _). simpl.
  etrans. refine (pr1_transportf (nat_trans _ _) _ _ _ _ _ _).
  simpl.
  etrans. refine (@functtransportf (nat_trans _ _) _ _ _ _ _ _ _).
  etrans. apply @pathsinv0, idtoiso_postcompose.
  apply maponpaths.
  etrans. apply maponpaths, maponpaths. apply @pathsinv0.
    refine (@maponpathscomp (nat_trans _ _) _ _ _ _ _ _ _).
  apply (maponpaths Δ), setproperty.
Qed.

(* The type of the [e_comp] argument of [obj_ext_mor_eq] depends on the [e_TY] argument.  However, the type of [e_TY] is an hset; so we generally don’t need to know what it is, so we can give this in a form where the [e_comp] just assumes _some_ [e_TY] is available, thereby making these two arguments independent.

TODO: see if using this instead of [obj_ext_mor_eq] speeds up any proofs. *)
Lemma obj_ext_mor_eq' {X X'} (F F' : obj_ext_mor X X')
  (e_TY : ∀ Γ (A : Ty X Γ), F [ A ] = F' [ A ])
  (e_comp_gen : ∀ (e_TY : ∀ Γ (A : Ty X Γ), F [ A ] = F' [ A ]),
    ∀ Γ (A : Ty X Γ),
    φ F A ;; @Δ _ _ _ _ _ (e_TY _ _)
    = φ F' A)
  : F = F'.
Proof.
  exact (obj_ext_mor_eq F F' e_TY (e_comp_gen e_TY)).
Qed.

Definition obj_ext_ob_mor : precategory_ob_mor.
Proof.
  exists (obj_ext_structure C).
  apply obj_ext_mor.
Defined.

Definition obj_ext_id_comp : precategory_id_comp (obj_ext_ob_mor).
Proof.
  apply tpair.
  - intro X. exists (identity _).
    intros Γ A; cbn. exists (identity _).
    apply id_left.
  - intros X X' X'' F G.
    exists ( obj_ext_mor_TY F ;; obj_ext_mor_TY G ).
    intros Γ A.
    exists ( φ F A ;; φ G _ ); cbn.
    etrans. apply @pathsinv0, assoc. 
    etrans. apply maponpaths, obj_ext_mor_ax.
    apply obj_ext_mor_ax.
Defined.

Definition obj_ext_precat_data : precategory_data
  := (_ ,, obj_ext_id_comp).

Definition obj_ext_precat_axioms : is_precategory obj_ext_precat_data.
Proof.
  repeat apply tpair.
  - intros X X' F. use obj_ext_mor_eq.
      intros Γ A; apply idpath.
    intros Γ A; cbn.
    etrans. apply id_right. apply id_left.
  - intros X X' F. use obj_ext_mor_eq.
      intros Γ A; apply idpath.
    intros Γ A; cbn.
    etrans. apply id_right. apply id_right.
  - intros X0 X1 X2 X3 F G H. use obj_ext_mor_eq.
      intros Γ A; apply idpath.
    intros Γ A; cbn.
    etrans. apply id_right.
    apply assoc.
Qed.

Definition obj_ext_precat : precategory
  := (_ ,, obj_ext_precat_axioms).

Definition obj_ext_has_homsets : has_homsets obj_ext_precat_data.
Proof.
  intros X X'. apply isaset_total2.
  - apply functor_category_has_homsets.
  - intros α. apply impred_isaset; intros Γ; apply impred_isaset; intros A.
    apply isaset_total2. apply hsC.
    intros φ. apply isasetaprop. apply hsC.
Qed.

Definition obj_ext_Precat : Precategory
  := (obj_ext_precat ,, obj_ext_has_homsets).

(** ** Utility lemmas *)
Lemma Δ_φ {X X' : obj_ext_Precat} (F : X ⇒ X')
    {Γ : C} {A A' : Ty X Γ} (e : A = A')
  : Δ e ;; φ F A' = φ F A ;; Δ (maponpaths ((obj_ext_mor_TY F : nat_trans _ _) _) e).
Proof.
  destruct e; simpl. etrans. apply id_left. apply pathsinv0, id_right.
Qed.

End Obj_Ext_Precat.

(* TODO: possibly clear more implicits, in e.g. [object_ext_precat_data], etc. *)
Arguments obj_ext_Precat _ : clear implicits.

Local Notation φ := obj_ext_mor_φ.


(** * Precategory of families-structures *)
Section Families_Structure_Precat.

Context {C : Precategory}.
Local Notation hsC := (homset_property C).

Local Notation "'Yo'" := (yoneda _ hsC).

Definition families_mor {X X' : obj_ext_Precat C}
    (Y : families_structure hsC X) (Y' : families_structure hsC X') (F : X ⇒ X')
  : Type
:= Σ FF_TM : TM Y ⇒ TM Y',
       FF_TM ;; pp Y' = pp Y ;; obj_ext_mor_TY F
     × 
       ∀ {Γ:C} {A : Ty X Γ}, Q Y A ;; FF_TM = #Yo (φ F A) ;; Q Y' _.

Definition families_mor_TM {X X'} {Y} {Y'} {F : X ⇒ X'} (FF : families_mor Y Y' F)
  : _ ⇒ _
:= pr1 FF.

Definition families_mor_pp {X X'} {Y} {Y'} {F : X ⇒ X'} (FF : families_mor Y Y' F)
  : families_mor_TM FF ;; pp Y' = pp Y ;; obj_ext_mor_TY F
:= pr1 (pr2 FF).

Definition families_mor_Q {X X'} {Y} {Y'} {F : X ⇒ X'} (FF : families_mor Y Y' F)
    {Γ} A
  : _ = _
:= pr2 (pr2 FF) Γ A.

(* TODO: inline in [isaprop_families_mor]? *)
Lemma families_mor_eq {X X'} {Y} {Y'} {F : X ⇒ X'} (FF FF' : families_mor Y Y' F)
    (e_TM : ∀ Γ (t : Tm Y Γ),
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
Lemma term_to_section_naturality {X X'} {Y} {Y'}
  {F : X ⇒ X'} {FY : families_mor Y Y' F}
  {Γ : C} (t : Tm Y Γ) (A := (pp Y : nat_trans _ _) _ t)
  : pr1 (term_to_section ((families_mor_TM FY : nat_trans _ _) _ t))
  = pr1 (term_to_section t) ;; φ F _
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
    etrans. apply @pathsinv0, assoc.
    apply maponpaths.
    etrans. Focus 2. apply @obj_ext_mor_ax.
    apply maponpaths. 
    apply comp_ext_compare_π.
  - etrans. apply term_to_section_recover. apply pathsinv0.
    etrans. apply Q_comp_ext_compare.
    etrans. apply @pathsinv0.
      set (H1 := nat_trans_eq_pointwise (families_mor_Q FY A) Γ).
      exact (toforallpaths _ _ _ H1 _).
    cbn. apply maponpaths. apply term_to_section_recover.
Qed.

Lemma families_mor_recover_term {X X'} {Y} {Y'}
  {F : X ⇒ X'} {FY : families_mor Y Y' F}
  {Γ : C} (t : Tm Y Γ)
  : (families_mor_TM FY : nat_trans _ _) Γ t
  = (Q Y' _ : nat_trans _ _) Γ (pr1 (term_to_section t) ;; φ F _).
Proof.
  etrans. apply @pathsinv0, term_to_section_recover.
  etrans. apply maponpaths, term_to_section_naturality.
  apply Q_comp_ext_compare.
Qed.

(* TODO: once all obligations proved, replace [families_mor_eq] with this in subsequent proofs. *)
Lemma isaprop_families_mor {X X'} {Y} {Y'} {F : X ⇒ X'}
  : isaprop (families_mor Y Y' F).
Proof.
  apply invproofirrelevance; intros FF FF'. apply families_mor_eq.
  intros Γ t.
  etrans. apply families_mor_recover_term.
  apply @pathsinv0. apply families_mor_recover_term.
Qed.

Lemma families_mor_transportf {X X'} {Y Y'}
    {F F' : X ⇒ X'} (eF : F = F') (FF : families_mor Y Y' F)
    {Γ:C} (t : Tm Y Γ)
  : (families_mor_TM (transportf _ eF FF) : nat_trans _ _) Γ t
    = (families_mor_TM FF : nat_trans _ _) Γ t.
Proof.
  destruct eF. apply idpath.
Qed.
 
Definition families_ob_mor : disp_precat_ob_mor (obj_ext_Precat C).
Proof.
  exists (fun X => families_structure hsC X).
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

Arguments families_disp_precat _ : clear implicits.
Arguments families_structure_precat _ : clear implicits.

(** * Precategory of cartesian _q_-morphism-structures *)
Section qq_Structure_Precat.

Context {C : Precategory}.
Local Notation hsC := (homset_property C).

Definition qq_structure_ob_mor : disp_precat_ob_mor (obj_ext_Precat C).
Proof.
  exists (fun X => qq_morphism_structure X).
  intros X X' Z Z' F.
  refine (∀ Γ' Γ (f : C ⟦ Γ' , Γ ⟧) (A : Ty X Γ), _).
  refine (qq Z f A ;; φ F A = _).
  refine (φ F _ ;; Δ _ ;; qq Z' f _).
  revert A; apply toforallpaths.
  refine (nat_trans_ax (obj_ext_mor_TY F) _ _ _).
Defined.

Lemma isaprop_qq_structure_mor
  {X X'} F (Z : qq_structure_ob_mor X) (Z' : qq_structure_ob_mor X')
  : isaprop (Z ⇒[F] Z').
Proof.
  repeat (apply impred_isaprop; intro). apply homset_property.
Qed.

Definition qq_structure_id_comp : disp_precat_id_comp _ qq_structure_ob_mor.
Proof.
  apply tpair.
  - intros X Z; cbn.
    intros Γ Γ' f A.
    etrans. apply id_right.
    apply pathsinv0.
    etrans. apply @pathsinv0, assoc. 
    etrans. apply id_left.
    etrans.
      apply cancel_postcomposition.
      apply comp_ext_compare_id_general.
    apply id_left.
  - intros X0 X1 X2 F G Z0 Z1 Z2.
    intros FF GG Γ Γ' f A. cbn.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition, FF.
    etrans. apply @pathsinv0, assoc.
    etrans. apply maponpaths, GG.
    etrans. apply @pathsinv0, assoc.
    etrans. Focus 2. etrans; apply assoc.
    apply maponpaths.
    etrans. apply assoc.
    etrans. Focus 2. apply @pathsinv0, assoc.
    apply cancel_postcomposition.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition, Δ_φ.
    etrans. apply @pathsinv0, assoc.
    apply maponpaths.
    apply pathsinv0, comp_ext_compare_comp_general.
Qed.

Definition qq_structure_data : disp_precat_data (obj_ext_Precat C)
  := (_ ,, qq_structure_id_comp).

Definition qq_structure_axioms : disp_precat_axioms _ qq_structure_data.
Proof.
  repeat apply tpair; intros;
    try apply isasetaprop; apply isaprop_qq_structure_mor.
Qed.

Definition qq_structure_disp_precat : disp_precat (obj_ext_Precat C)
  := (_ ,, qq_structure_axioms).

Definition qq_structure_precat : precategory
  := total_precat (qq_structure_disp_precat).

End qq_Structure_Precat.

Arguments qq_structure_disp_precat _ : clear implicits.
Arguments qq_structure_precat _ : clear implicits.


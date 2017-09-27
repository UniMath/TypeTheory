(**
  [TypeTheory.ALV2.CwF_SplitTypeCat_Cats]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(** 
Main definitions:

- [obj_ext_precat]
- [term_fun_disp_cat], [term_fun_structure_precat]
- [qq_structure_disp_cat], [qq_structure_precat]
*)

Require Import UniMath.Foundations.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.UnicodeNotations.
Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Defs.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.

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
 
(** * category of object-extension structures *)
Section Obj_Ext_Precat.

Context {C : category}.

Definition obj_ext_mor (X X' : obj_ext_structure C)
  := ∑ F_TY : TY X --> TY X',
       ∏ {Γ:C} {A : Ty X Γ},
         ∑ φ : (Γ ◂ A --> Γ ◂ ((F_TY : nat_trans _ _) _ A)),
           φ ;; π _ = π A.

Definition obj_ext_mor_TY {X X'} (F : obj_ext_mor X X') : _ --> _
  := pr1 F.

(* TODO: is this actually useful?  Maybe remove. *)
Notation "F [ A ]" := ((obj_ext_mor_TY F : nat_trans _ _) _ A) (at level 4) : TY_scope.
Delimit Scope TY_scope with TY.
Bind Scope TY_scope with TY.
Open Scope TY_scope.

Definition obj_ext_mor_φ {X X'} (F : obj_ext_mor X X')
    {Γ:C} (A : Ty X Γ)
  : Γ ◂ A --> Γ ◂ F[ A ]
:= pr1 (pr2 F _ _).

Local Notation φ := obj_ext_mor_φ.

Definition obj_ext_mor_ax {X X'} (F : obj_ext_mor X X')
    {Γ:C} (A : Ty X Γ)
  : φ F A ;; π _ = π A
:= pr2 (pr2 F _ _).

(* TODO: try to speed up? *)
Lemma obj_ext_mor_eq {X X'} (F F' : obj_ext_mor X X')
  (e_TY : ∏ Γ (A : Ty X Γ), F [ A ] = F' [ A ])
  (e_comp : ∏ Γ (A : Ty X Γ),
    φ F A ;; @Δ _ _ _ _ _ (e_TY _ _)
    = φ F' A)
  : F = F'.
Proof.
  use total2_paths_f.
    apply nat_trans_eq. apply has_homsets_HSET.
    intros Γ; apply funextsec; intros A.
    apply e_TY.
  apply funextsec; intros Γ; apply funextsec; intros A.
  use total2_paths_f. Focus 2. apply homset_property.
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
  (e_TY : ∏ Γ (A : Ty X Γ), F [ A ] = F' [ A ])
  (e_comp_gen : ∏ (e_TY : ∏ Γ (A : Ty X Γ), F [ A ] = F' [ A ]),
    ∏ Γ (A : Ty X Γ),
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
  - apply homset_property.
  - intros α. apply impred_isaset; intros Γ; apply impred_isaset; intros A.
    apply isaset_total2. apply homset_property.
    intros φ. apply isasetaprop. apply homset_property.
Qed.

Definition obj_ext_Precat : category
  := (obj_ext_precat ,, obj_ext_has_homsets).

(** ** Utility lemmas *)
Lemma Δ_φ {X X' : obj_ext_Precat} (F : X --> X')
    {Γ : C} {A A' : Ty X Γ} (e : A = A')
  : Δ e ;; φ F A' = φ F A ;; Δ (maponpaths ((obj_ext_mor_TY F : nat_trans _ _) _) e).
Proof.
  destruct e; simpl. etrans. apply id_left. apply pathsinv0, id_right.
Qed.

End Obj_Ext_Precat.

(* TODO: possibly clear more implicits, in e.g. [object_ext_precat_data], etc. *)
Arguments obj_ext_Precat _ : clear implicits.

Local Notation φ := obj_ext_mor_φ.


(** * category of term structures *)
Section Term_Fun_Structure_Precat.

Context {C : category}.

Definition term_fun_mor {X X' : obj_ext_Precat C}
    (Y : term_fun_structure C X) (Y' : term_fun_structure C X') (F : X --> X')
  : UU
:= ∑ FF_TM : TM Y --> TM Y',
       FF_TM ;; pp Y' = pp Y ;; obj_ext_mor_TY F
     × 
       ∏ {Γ:C} {A : Ty X Γ},
         (FF_TM : nat_trans _ _) _ (te Y A)
         = # (TM Y' : functor _ _) (φ F A) (te Y' _).

Definition term_fun_mor_TM {X X'} {Y} {Y'} {F : X --> X'} (FF : term_fun_mor Y Y' F)
  : _ --> _
:= pr1 FF.
(* TODO: try making this a coercion to [nat_trans]?  (Requires type annotation in this definition so may cause problems elsewhere.) *)

Definition term_fun_mor_pp {X X'} {Y} {Y'} {F : X --> X'} (FF : term_fun_mor Y Y' F)
  : term_fun_mor_TM FF ;; pp Y' = pp Y ;; obj_ext_mor_TY F
:= pr1 (pr2 FF).

Definition term_fun_mor_te {X X'} {Y} {Y'} {F : X --> X'} (FF : term_fun_mor Y Y' F)
    {Γ:C} (A : Ty X Γ)
  : (term_fun_mor_TM FF : nat_trans _ _) _ (te Y A)
  = # (TM Y' : functor _ _) (φ F A) (te Y' _)
:= pr2 (pr2 FF) Γ A.

Definition term_fun_mor_Q {X X'} {Y} {Y'} {F : X --> X'} (FF : term_fun_mor Y Y' F)
    {Γ:C} (A : Ty X Γ)
  : Q Y A ;; term_fun_mor_TM FF = #Yo (φ F A) ;; Q Y' _.
Proof.
  apply nat_trans_eq. apply homset_property.
  intros Γ'; simpl in Γ'.
(* Insert [cbn] to see what’s actually happening; removed for compile speed. *)
  unfold yoneda_objects_ob. apply funextsec; intros f.
  etrans. 
    refine (toforallpaths _ _ _ (nat_trans_ax (term_fun_mor_TM FF) _ _ _) _).
  etrans. cbn. apply maponpaths, term_fun_mor_te.
  refine (toforallpaths _ _ _ (!functor_comp (TM Y') _ _ ) _).
Qed.

(* TODO: inline in [isaprop_term_fun_mor]? *)
Lemma term_fun_mor_eq {X X'} {Y} {Y'} {F : X --> X'} (FF FF' : term_fun_mor Y Y' F)
    (e_TM : ∏ Γ (t : Tm Y Γ),
      (term_fun_mor_TM FF : nat_trans _ _) _ t
      = (term_fun_mor_TM FF' : nat_trans _ _) _ t)
  : FF = FF'.
Proof.
  apply subtypeEquality.
  - intros x; apply isapropdirprod.
    + apply homset_property.
    + repeat (apply impred_isaprop; intro). apply setproperty.
  - apply nat_trans_eq. apply has_homsets_HSET. 
    intros Γ. apply funextsec. unfold homot. apply e_TM.
Qed.


(* This is not full naturality of [term_to_section]; it is just what is required for [isaprop_term_fun_mor] below. *)
Lemma term_to_section_naturality {X X'} {Y} {Y'}
  {F : X --> X'} {FY : term_fun_mor Y Y' F}
  {Γ : C} (t : Tm Y Γ) (A := (pp Y : nat_trans _ _) _ t)
  : pr1 (term_to_section ((term_fun_mor_TM FY : nat_trans _ _) _ t))
  = pr1 (term_to_section t) ;; φ F _
   ;; Δ (!toforallpaths _ _ _ (nat_trans_eq_pointwise (term_fun_mor_pp FY) Γ) t).
Proof.
  set (t' := (term_fun_mor_TM FY : nat_trans _ _) _ t).
  set (A' := (pp Y' : nat_trans _ _) _ t').
  set (Pb := isPullback_preShv_to_pointwise (homset_property _) (isPullback_Q_pp Y' A') Γ);
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
      set (H1 := nat_trans_eq_pointwise (term_fun_mor_Q FY A) Γ).
      exact (toforallpaths _ _ _ H1 _).
    cbn. apply maponpaths. apply term_to_section_recover.
Qed.

Lemma term_fun_mor_recover_term {X X'} {Y} {Y'}
  {F : X --> X'} {FY : term_fun_mor Y Y' F}
  {Γ : C} (t : Tm Y Γ)
  : (term_fun_mor_TM FY : nat_trans _ _) Γ t
  = (Q Y' _ : nat_trans _ _) Γ (pr1 (term_to_section t) ;; φ F _).
Proof.
  etrans. apply @pathsinv0, term_to_section_recover.
  etrans. apply maponpaths, term_to_section_naturality.
  apply Q_comp_ext_compare.
Qed.

(* TODO: once all obligations proved, replace [term_fun_mor_eq] with this in subsequent proofs. *)
Lemma isaprop_term_fun_mor {X X'} {Y} {Y'} {F : X --> X'}
  : isaprop (term_fun_mor Y Y' F).
Proof.
  apply invproofirrelevance; intros FF FF'. apply term_fun_mor_eq.
  intros Γ t.
  etrans. apply term_fun_mor_recover_term.
  apply @pathsinv0. apply term_fun_mor_recover_term.
Qed.

Lemma term_fun_mor_transportf {X X'} {Y Y'}
    {F F' : X --> X'} (eF : F = F') (FF : term_fun_mor Y Y' F)
    {Γ:C} (t : Tm Y Γ)
  : (term_fun_mor_TM (transportf _ eF FF) : nat_trans _ _) Γ t
    = (term_fun_mor_TM FF : nat_trans _ _) Γ t.
Proof.
  destruct eF. apply idpath.
Qed.
 
Definition term_fun_ob_mor : disp_cat_ob_mor (obj_ext_Precat C).
Proof.
  exists (fun X => term_fun_structure C X).
  exact @term_fun_mor.
Defined.

Definition term_fun_id_comp : disp_cat_id_comp _ term_fun_ob_mor.
Proof.
  apply tpair.
  - intros X Y. simpl; unfold term_fun_mor.
    exists (identity _). apply tpair.
    + etrans. apply id_left. apply pathsinv0, id_right.
    + intros Γ A; cbn.
      refine (toforallpaths _ _ _ (!functor_id (TM _) _) _).
  - intros X0 X1 X2 F G Y0 Y1 Y2 FF GG.
    exists (term_fun_mor_TM FF ;; term_fun_mor_TM GG). apply tpair.
    + etrans. apply @pathsinv0. apply assoc.
      etrans. apply maponpaths, term_fun_mor_pp.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition, term_fun_mor_pp.
      apply pathsinv0. apply assoc.
    + intros Γ A.
      etrans. cbn. apply maponpaths, term_fun_mor_te.
      etrans. refine (toforallpaths _ _ _
                        (nat_trans_ax (term_fun_mor_TM _) _ _ _) _).
      etrans. cbn. apply maponpaths, term_fun_mor_te.
      refine (toforallpaths _ _ _ (!functor_comp (TM _) _ _) _).
Defined.

Definition term_fun_data : disp_cat_data (obj_ext_Precat C)
  := (_ ,, term_fun_id_comp).

Definition term_fun_axioms : disp_cat_axioms _ term_fun_data.
Proof.
  repeat apply tpair.
  - intros. apply term_fun_mor_eq. intros.
    etrans. Focus 2. apply @pathsinv0, term_fun_mor_transportf.
    apply idpath.
  - intros. apply term_fun_mor_eq. intros.
    etrans. Focus 2. apply @pathsinv0, term_fun_mor_transportf.
    apply idpath.
  - intros. apply term_fun_mor_eq. intros.
    etrans. Focus 2. apply @pathsinv0, term_fun_mor_transportf.
    apply idpath.
  - intros. apply isaset_total2.
    apply homset_property.
    intros. apply isasetaprop, isapropdirprod.
    apply homset_property.
    repeat (apply impred_isaprop; intro). apply setproperty.
Qed.

Definition term_fun_disp_cat : disp_cat (obj_ext_Precat C)
  := (_ ,, term_fun_axioms).

Definition term_fun_structure_precat : precategory
  := total_category term_fun_disp_cat.

End Term_Fun_Structure_Precat.

Arguments term_fun_disp_cat _ : clear implicits.
Arguments term_fun_structure_precat _ : clear implicits.

(** * category of _q_-morphism-structures *)
Section qq_Structure_Precat.

Context {C : category}.

Definition qq_structure_ob_mor : disp_cat_ob_mor (obj_ext_Precat C).
Proof.
  exists (fun X => qq_morphism_structure X).
  intros X X' Z Z' F.
  refine (∏ Γ' Γ (f : C ⟦ Γ' , Γ ⟧) (A : Ty X Γ), _).
  refine (qq Z f A ;; φ F A = _).
  refine (φ F _ ;; Δ _ ;; qq Z' f _).
  revert A; apply toforallpaths.
  refine (nat_trans_ax (obj_ext_mor_TY F) _ _ _).
Defined.

Lemma isaprop_qq_structure_mor
  {X X'} F (Z : qq_structure_ob_mor X) (Z' : qq_structure_ob_mor X')
  : isaprop (Z -->[F] Z').
Proof.
  repeat (apply impred_isaprop; intro). apply homset_property.
Qed.

Definition qq_structure_id_comp : disp_cat_id_comp _ qq_structure_ob_mor.
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

Definition qq_structure_data : disp_cat_data (obj_ext_Precat C)
  := (_ ,, qq_structure_id_comp).

Definition qq_structure_axioms : disp_cat_axioms _ qq_structure_data.
Proof.
  repeat apply tpair; intros;
    try apply isasetaprop; apply isaprop_qq_structure_mor.
Qed.

Definition qq_structure_disp_cat : disp_cat (obj_ext_Precat C)
  := (_ ,, qq_structure_axioms).

Definition qq_structure_precat : precategory
  := total_category (qq_structure_disp_cat).

End qq_Structure_Precat.

Arguments qq_structure_disp_cat _ : clear implicits.
Arguments qq_structure_precat _ : clear implicits.


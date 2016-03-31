(**

 Ahrens, Lumsdaine, Voevodsky, 2015 - 2016

Main definitions:

- [obj_ext_precat]
- [families_disp_precat]
- [qq_disp_precat]
*)

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

Lemma transportf_forall {A B} (C : A -> B -> Type)
  {x0 x1 : A} (e : x0 = x1) (f : forall y:B, C x0 y)
  : transportf (fun x => forall y, C x y) e f
  = fun y => transportf (fun x => C x y) e (f y).
Proof.
  destruct e; apply idpath.
Defined.

Lemma maponpaths_apply {A B} {f0 f1 : A -> B} (e : f0 = f1) (x : A)
  : maponpaths (fun f => f x) e
  = toforallpaths _ _ _ e x.
Proof.
  destruct e; apply idpath.
Defined.

(* TODO: upstream following group (and its [Δ] notation) to [Systems.Structures]. *)
Definition comp_ext_compare {C:precategory} {X : obj_ext_structure C}
    {Γ : C} {A A' : Ty X Γ} (e : A = A')
  : Γ ◂ A ⇒ Γ ◂ A'
:= idtoiso (maponpaths (comp_ext X Γ) e).

Lemma comp_ext_compare_id {C:precategory} {X : obj_ext_structure C}
    {Γ : C} (A : Ty X Γ)
  : comp_ext_compare (idpath A) = identity (Γ ◂ A).
Proof.
  apply idpath.
Qed.

Lemma comp_ext_compare_id_general {C:precategory} {X : obj_ext_structure C}
    {Γ : C} {A : Ty X Γ} (e : A = A)
  : comp_ext_compare e = identity (Γ ◂ A).
Proof.
  apply @pathscomp0 with (comp_ext_compare (idpath _)).
  apply maponpaths, setproperty.
  apply idpath.
Qed.

Lemma comp_ext_compare_comp {C:precategory} {X : obj_ext_structure C}
    {Γ : C} {A A' A'' : Ty X Γ} (e : A = A') (e' : A' = A'')
  : comp_ext_compare (e @ e') = comp_ext_compare e ;; comp_ext_compare e'.
Proof.
  apply pathsinv0.
  etrans. apply idtoiso_concat_pr. 
  unfold comp_ext_compare. apply maponpaths, maponpaths.
  apply pathsinv0, maponpathscomp0. 
Qed.

Lemma comp_ext_compare_comp_general {C:precategory} {X : obj_ext_structure C}
    {Γ : C} {A A' A'' : Ty X Γ} (e : A = A') (e' : A' = A'') (e'' : A = A'')
  : comp_ext_compare e'' = comp_ext_compare e ;; comp_ext_compare e'.
Proof.
  refine (_ @ comp_ext_compare_comp _ _).
  apply maponpaths, setproperty.
Qed.

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
  : _ = _
:= pr1 (pr2 FF).

Definition families_mor_Q {X X'} {Y} {Y'} {F : X ⇒ X'} (FF : families_mor Y Y' F)
    {Γ} A
  : _ = _
:= pr2 (pr2 FF) Γ A.

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
    intros Γ. apply funextsec. apply e_TM.
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

End Families_Structure_Precat.

Arguments families_disp_precat _ : clear implicits.

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

End qq_Structure_Precat.

Arguments qq_structure_disp_precat _ : clear implicits.


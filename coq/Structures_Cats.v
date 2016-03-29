(**

 Ahrens, Lumsdaine, Voevodsky, 2015 - 2016

*)

Require Import Systems.UnicodeNotations.
Require Import Systems.Auxiliary.
Require Import Systems.Structures.

Require Import Systems.Bicats.Auxiliary.
Require Import Systems.Bicats.Displayed_Precats.

Local Set Automatic Introduction.
(* only needed since imports globally unset it *)

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
  
End Auxiliary.


(** Start by redefining some local notations, and then fixing the base category. *)

Notation "Γ ◂ A" := (comp_ext _ Γ A) (at level 30).

Section Fix_Base_Category.

Context {C : precategory} {hsC : has_homsets C}.


(** * Object-extension structures *)

Definition obj_ext_mor (X X' : obj_ext_structure C)
  := Σ F_TY : TY X ⇒ TY X',
       ∀ {Γ:C} {A : (TY X : functor _ _) Γ : hSet},
         Σ φ : (Γ ◂ A ⇒ Γ ◂ ((F_TY : nat_trans _ _) _ A)),
           φ ;; π _ = π A.

Definition obj_ext_mor_TY {X X'} (F : obj_ext_mor X X') : _ ⇒ _
  := pr1 F.

Notation "F [ A ]" := ((obj_ext_mor_TY F : nat_trans _ _) _ A) (at level 4) : TY_scope.
Delimit Scope TY_scope with TY.
Bind Scope TY_scope with TY.
Open Scope TY_scope.

Definition obj_ext_mor_ext {X X'} (F : obj_ext_mor X X')
    {Γ:C} (A : (TY X : functor _ _) Γ : hSet)
  : Γ ◂ A ⇒ Γ ◂ F[ A ]
:= pr1 (pr2 F _ _).

Definition obj_ext_mor_ax {X X'} (F : obj_ext_mor X X')
    {Γ:C} (A : (TY X : functor _ _) Γ : hSet)
  : obj_ext_mor_ext F A ;; π _ = π A
:= pr2 (pr2 F _ _).

(* TODO: try to speed up? *)
Lemma obj_ext_mor_eq {X X'} (F F' : obj_ext_mor X X')
  (e_TY : ∀ Γ (A : (TY X : functor _ _) Γ : hSet), 
              F [ A ] = F' [ A ])
  (e_comp : ∀ Γ (A : (TY X : functor _ _) Γ : hSet),
    obj_ext_mor_ext F A ;; idtoiso (maponpaths (comp_ext X' _) (e_TY _ _))
    = obj_ext_mor_ext F' A)
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
  apply maponpaths, maponpaths, maponpaths.
  etrans. apply @pathsinv0.
    refine (@maponpathscomp (nat_trans _ _) _ _ _ _ _ _ _).
  apply maponpaths.
  apply setproperty.
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
    exists ( obj_ext_mor_ext F A ;; obj_ext_mor_ext G _ ); cbn.
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

End Fix_Base_Category.

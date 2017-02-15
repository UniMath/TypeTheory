(**
  [TypeTheory.ALV2.CwF_SplitTypeCat_Univalent_Cats]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

Require Import UniMath.Foundations.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.
Require Import TypeTheory.Displayed_Cats.Auxiliary.
Require Import TypeTheory.Displayed_Cats.Core.
Require Import TypeTheory.Displayed_Cats.Constructions.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Defs.
Require Import TypeTheory.ALV2.CwF_SplitTypeCat_Cats.
Require Import TypeTheory.ALV2.CwF_SplitTypeCat_Equiv_Cats.

Local Set Automatic Introduction.
(* only needed since imports globally unset it *)


Section Auxiliary.

Lemma transportf_term_fun_mor_TM {C : Precategory}
  {X X' : obj_ext_Precat C} {F F' : X --> X'} (e : F = F')
  {Y : term_fun_disp_precat C X} {Y'} (FY : Y -->[F] Y')
  : term_fun_mor_TM (transportf _ e FY) = term_fun_mor_TM FY.
Proof.
  destruct e; apply idpath.
Qed.

End Auxiliary.

Section Fix_Context.

Context {C : Precategory}.

Local Notation "Γ ◂ A" := (comp_ext _ Γ A) (at level 30).
Local Notation "'Ty'" := (fun X Γ => (TY X : functor _ _) Γ : hSet) (at level 10).

Local Notation Δ := comp_ext_compare.
Local Notation φ := obj_ext_mor_φ.


Section Is_Category_Obj_Ext_1.

Definition obj_ext_iso_alt (X X' : obj_ext_Precat C) : UU :=
  ∑ F_TY : iso (TY X) (TY X'),
        ∏ {Γ:C} {A' : Ty X' Γ},
         ∑ φ : iso (Γ ◂ ((inv_from_iso F_TY) : nat_trans _ _ ) _ A') (Γ ◂  A'),
           φ ;; π _ = π _ .

(* TODO: anstract this as a general function on any [category] (if there isn’t one already provided). *) 
Definition is_saturated_preShv (F G : preShv C) : F = G ≃ iso F G.
Proof.
  apply (weqpair idtoiso (pr1 (category_is_category _) _ _ )).
Defined.

Definition weq_eq_obj_ext_iso_alt (X X' : obj_ext_Precat C) :
  (X = X') ≃ obj_ext_iso_alt X X'.
Proof.
  eapply weqcomp. apply total2_paths_equiv.
  
  set (H := is_saturated_preShv (TY X) (TY X')).
  use (weqbandf H).
  intro F. simpl.
(*  rewrite transportf_forall. (* do better *) *)
  eapply weqcomp. apply weqtoforallpaths.
  apply weqonsecfibers.
  intro Γ.
  eapply weqcomp. apply weqtoforallpaths. simpl.
  apply weqonsecfibers.
  intro A'.
  eapply weqcomp. apply total2_paths_equiv.
  simpl.
(*  rewrite transportf_forall. *)
  use weqbandf. simpl.
  - 
    set (RX := @transportf_forall).
    specialize (RX (preShv C) C).
    specialize (RX (fun F Γ' => ((F:functor _ _ ) Γ' : hSet) → ∑ ΓA : C, ΓA --> Γ')).
    simpl in RX.
    specialize (RX _ _ F).
    rewrite RX.
    simpl.
    clear RX.
    rewrite transportf_forall_var.

    simpl. cbn.
 
  admit.
Abort.

End Is_Category_Obj_Ext_1.

(* TODO: above here and below here are two mostly separate approaches to [is_category_obj_ext].  Once one is complete, most of the other can probably be pruned *)

Section Is_Category_Obj_Ext_2.

(* TODO: move*)
Definition obj_ext_to_preShv_functor_data
  : functor_data (obj_ext_Precat C) (preShv C).
Proof.
  use tpair.
  apply pr1.
  simpl; intros X X'; apply pr1.
Defined.

(* TODO: move *)
Definition obj_ext_to_preShv_functor_axioms
  : is_functor obj_ext_to_preShv_functor_data.
Proof.
  split; intro; intros; apply idpath.
Qed.

(* TODO: move; rename to [obj_ext_TY_functor]? *)
Definition obj_ext_to_preShv_functor
  : functor (obj_ext_Precat C) (preShv C)
:= (_ ,, obj_ext_to_preShv_functor_axioms).



Definition transportf_obj_ext
  {T T' : preShv C} (e : T = T')
  (extn : ∏ Γ : C, ((T : functor _ _) Γ : hSet) → ∑ ΓA : C, ΓA --> Γ) 
: transportf _ e extn
  = fun Γ A => extn Γ ((inv_from_iso (idtoiso e) : nat_trans _ _) Γ A).
Proof.
  destruct e; cbn. apply idpath.
Defined.

Lemma obj_ext_mor_TY_eq {X X' : obj_ext_Precat C}
  {F F' : X --> X'} (E : F = F')
  {Γ} (A : Ty X Γ)
: (obj_ext_mor_TY F : nat_trans _ _) _ A
  = (obj_ext_mor_TY F' : nat_trans _ _) _ A.
Proof.
  destruct E; apply idpath.
Qed.

Lemma obj_ext_mor_φ_eq {X X' : obj_ext_Precat C}
  {F F' : X --> X'} (E : F = F')
  {Γ} (A : Ty X Γ)
: φ F A ;; Δ (obj_ext_mor_TY_eq E A)
  = φ F' A.
Proof.
  destruct E.
  etrans. apply maponpaths, comp_ext_compare_id_general.
  apply id_right.
Qed.

Definition iso_to_obj_ext_eq (H : is_category C)
  {X X' : obj_ext_Precat C}
: (iso X X') -> (X = X').
Proof.
  intros F.
  apply (total2_paths_f (isotoid _
    (category_is_category _)
    (functor_on_iso obj_ext_to_preShv_functor F))).
  etrans. apply transportf_obj_ext.
  apply funextsec; intro Γ; apply funextsec; intro A.
  rewrite idtoiso_isotoid.
  etrans.
  { apply maponpaths.
    refine (toforallpaths _ _ _ _ A).
    refine (toforallpaths _ _ _ _ Γ).
    eapply pathsinv0, maponpaths.
    refine (maponpaths pr1 (functor_on_iso_inv _ _ obj_ext_to_preShv_functor _ _ _)).
  }
  set (F' := inv_from_iso F).
  set (FF' := iso_after_iso_inv F).
  set (F'F := iso_inv_after_iso F).
  simpl.
  (* Now we break out a proof-irrelevant subproof needed later.  By breaking it out _before_ [use total2_paths_f], we ensure that this large subterm only occurs once in the proof term; this saves c.30s at the [Defined.] 

  For reading: skip this subproof block for now, then imagine it inlined at [exact H'] below. *)
  assert (H' : is_inverse_in_precat
     (φ _ ((obj_ext_mor_TY (inv_from_iso F) : nat_trans _ _) Γ A)
       ;; Δ (obj_ext_mor_TY_eq FF' A))
     (φ (inv_from_iso F) A)).
  { split.
    * etrans. eapply pathsinv0, assoc.
      etrans. apply maponpaths, Δ_φ.
      etrans. apply assoc.
      etrans. Focus 2. apply (obj_ext_mor_φ_eq F'F).
      cbn. apply maponpaths.
      apply maponpaths, setproperty.
    * etrans. apply assoc.
      apply (obj_ext_mor_φ_eq FF').
  }
  use total2_paths_f.
  use isotoid. assumption.
  exists (φ (F : _ --> _) _ ;; Δ (obj_ext_mor_TY_eq FF' _)).
  + simpl. apply is_iso_from_is_z_iso.
    exists (φ _ _). exact H'.
  + etrans. apply transportf_isotoid.
    etrans. apply maponpaths_2. 
      apply inv_from_iso_from_is_z_iso.
    apply obj_ext_mor_ax.
Defined.

(* TODO: inline *)
Lemma foo {X X' : obj_ext_Precat C} (e : X = X')
  {Γ} (A : Ty X Γ)
: comp_ext X Γ A
  --> comp_ext X' Γ ((obj_ext_mor_TY (idtoiso e : X --> X') : nat_trans _ _) _ A).
Proof.
  Unset Printing Notations.
  revert Γ A.
  set (e' := (fiber_paths e)). simpl in e'.
  assert (H : (fun Γ (A : Ty X' Γ)
                => pr2 X Γ (transportb (fun (T : functor C^op hset_precategory) => T Γ : hSet) (base_paths X X' e) A))
              = pr2 X').
  { etrans. Focus 2. apply e'.
    apply pathsinv0.
    etrans. refine (transportf_forall _ _ _). simpl.
    apply funextsec; intros Γ.
    apply (transportf_forall_var _
     (fun (T : functor C^op hset_precategory) => T Γ : hSet)).
  }
  intros Γ A; simpl in A. 
  refine (_ ;; _).
    Focus 2. eapply idtoiso.
    refine (maponpaths pr1 (toforallpaths _ _ _
              (toforallpaths _ _ _ H Γ) _)).
  apply Δ. destruct e; apply idpath.
  Set Printing Notations.
Defined.

Lemma funextsec_idpath (T : UU) (P : T -> UU) (f : forall t, P t)
  : funextsec P f f (fun t => idpath _) = idpath _.
Proof.
  apply invmap_eq. apply idpath.
Defined.

(* TODO: name *)
Lemma foo2 {X X' : obj_ext_Precat C} (e : X = X')
  {Γ} (A : Ty X Γ)
: φ (idtoiso e : _ --> _) A = foo e A.
Proof.
  (* should be trivial once [foo] is defined correctly: *)
  destruct e. cbn. apply pathsinv0.
  unfold foo. cbn. 
  etrans. apply id_left. 
  rewrite funextsec_idpath; apply idpath.
Qed.

Theorem is_category_obj_ext (H : is_category C)
  : is_category (obj_ext_Precat C).
Proof.
  split. Focus 2. apply homset_property.
  apply (eq_equiv_from_retraction _ (@iso_to_obj_ext_eq H)). 
  intros X X' F.
  apply eq_iso.
  apply obj_ext_mor_eq'.
  - intros Γ; apply toforallpaths; revert Γ; apply toforallpaths.
    apply maponpaths.
    refine (@maponpaths _ _ pr1
      (functor_on_iso (obj_ext_to_preShv_functor) _)
      (functor_on_iso _ _) _).
    etrans. apply @pathsinv0, maponpaths_idtoiso.
    etrans. apply maponpaths, base_total2_paths.
    apply (idtoiso_isotoid _ _ _ _ _).
  - intros e_TY Γ A.
    etrans. apply maponpaths_2. apply foo2. unfold foo.
    etrans. apply maponpaths_2. apply maponpaths.
    eapply (maponpaths pr1).
    (* lemma foo2 above: [φ] of an [idtoiso] is… what? *) 
Abort.

End Is_Category_Obj_Ext_2.

Section Is_Category_Families_Strucs.

(* TODO: inline *) 
Lemma isaprop_whatever
  (x : obj_ext_Precat C)
  (d d' : (term_fun_disp_precat C) x)
  : isaprop (iso_disp (identity_iso x) d d').
Proof.
  apply isofhleveltotal2.
  - apply isaprop_term_fun_mor.
  - intro. apply isaprop_is_iso_disp.
Qed.

Definition iso_disp_to_TM_eq
  (X : obj_ext_Precat C)
  (Y Y' : (term_fun_disp_precat C) X)
  : iso_disp (identity_iso X) Y Y'
  -> TM (Y : term_fun_structure _ X) = TM (Y' : term_fun_structure _ X).
Proof.
  intro i.
  use isotoid.
  - apply category_is_category.
  - exists (term_fun_mor_TM (i : _ -->[_] _)).
    apply is_iso_from_is_z_iso.
    exists (term_fun_mor_TM (inv_mor_disp_from_iso i)).
    split.
    + etrans. exact (maponpaths term_fun_mor_TM (inv_mor_after_iso_disp i)).
      apply transportf_term_fun_mor_TM.
    + etrans. exact (maponpaths term_fun_mor_TM (iso_disp_after_inv_mor i)).
      apply transportf_term_fun_mor_TM.
Defined.

Lemma prewhisker_iso_disp_to_TM_eq 
  {X} {Y Y' : term_fun_disp_precat C X}
  (FG : iso_disp (identity_iso X) Y Y')
  {P : preShv C} (α : TM (Y : term_fun_structure _ X) --> P)
: transportf (λ P' : preShv C, P' --> P) (iso_disp_to_TM_eq _ _ _ FG) α
  = term_fun_mor_TM (pr1 (pr2 FG)) ;; α.
Proof.
  etrans. apply transportf_isotoid.
  apply maponpaths_2.
  apply inv_from_iso_from_is_z_iso.
Qed.

Lemma postwhisker_iso_disp_to_TM_eq 
  {X} {Y Y' : term_fun_disp_precat C X}
  (FG : iso_disp (identity_iso X) Y Y')
  {P : preShv C} (α : P --> TM (Y : term_fun_structure _ X))
: transportf (λ P' : preShv C, P --> P') (iso_disp_to_TM_eq _ _ _ FG) α
  = α ;; term_fun_mor_TM (pr1 FG).
Proof.
  apply postwhisker_isotoid.
Qed.

Definition iso_to_id__term_fun_disp_precat
  {X : obj_ext_Precat C}
  (Y Y' : term_fun_disp_precat C X)
  : iso_disp (identity_iso _) Y Y' -> Y = Y'.
Proof.
  intros i.
  apply subtypeEquality. { intro. apply isaprop_term_fun_structure_axioms. }
  apply total2_paths_f with (iso_disp_to_TM_eq _ _ _ i).
  etrans. refine (transportf_dirprod _ _ _ _ _ _).
  apply dirprodeq; simpl.
  - etrans. apply prewhisker_iso_disp_to_TM_eq.
    etrans. apply term_fun_mor_pp.
    exact (id_right (pp _)).
  - etrans. refine (transportf_forall _ _ _).
    apply funextsec; intros Γ.
    etrans. refine (transportf_forall _ _ _).
    apply funextsec; intros A.
    etrans. refine (postwhisker_iso_disp_to_TM_eq i (Q _ _)).
    etrans. apply term_fun_mor_Q.
    etrans. Focus 2. exact (id_left (Q _ A)).
    apply maponpaths_2. apply functor_id.
Qed.

Theorem is_category_term_fun_structure
  : is_category_disp (term_fun_disp_precat C).
Proof.
  apply is_category_disp_from_fibers.
  intros X.
  apply eq_equiv_from_retraction with iso_to_id__term_fun_disp_precat.
  - intros. apply eq_iso_disp, isaprop_term_fun_mor.
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

Lemma isaprop_iso_disp_qq_morphism_structure 
  (x : obj_ext_Precat C)
  (d d' : (qq_structure_disp_precat C) x)
  : isaprop (iso_disp (identity_iso x) d d').
Proof.
  apply (isofhleveltotal2 1).
  - do 4 (apply impred; intro).
    apply homset_property.
  - intro. apply isaprop_is_iso_disp.
Qed.

Lemma qq_structure_eq 
  (x : obj_ext_Precat C)
  (d d' : qq_morphism_structure x)
  (H : ∏ (Γ Γ' : C) (f : Γ' --> Γ) (A : (TY x : functor _ _ ) Γ : hSet), 
           qq d f A = qq d' f A)
  : d = d'.
Proof.
  apply subtypeEquality.
  { intro. apply isaprop_qq_morphism_axioms. }
  apply subtypeEquality.
  { intro. do 4 (apply impred; intro). 
           apply isofhleveltotal2.
     + apply homset_property.
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

End Is_Category_qq_Strucs.

Section Is_Category_Compat_Strucs.

Lemma isaprop_iso_disp_strucs_compat_disp_precat
  (x : total_precat (term_fun_disp_precat C × qq_structure_disp_precat C))
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
  (x : total_precat (term_fun_disp_precat C × qq_structure_disp_precat C))
  (d d' : strucs_compat_disp_precat x)
  : iso_disp (identity_iso x) d d' → d = d'.
Proof.
  intro H.
  do 4 (apply funextsec; intro).
  apply homset_property.
Defined.

Theorem is_category_strucs_compat
  : is_category_disp (@strucs_compat_disp_precat C).
Proof.
  apply is_category_disp_from_fibers.
  intros x d d'.
  use isweqimplimpl.
  - apply strucs_compat_iso_disp_to_id.
  - apply hlevelntosn.
    apply CwF_SplitTypeCat_Maps.isaprop_iscompatible_term_qq.
  - apply isaprop_iso_disp_strucs_compat_disp_precat.
Defined.

End Is_Category_Compat_Strucs.

End Fix_Context.
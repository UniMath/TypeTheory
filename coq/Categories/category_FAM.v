
(** * The category FAM(C) *)
(**
  Contents:

    - Definition of the precategory FAM(C) for a precategory C
    - TODO: FAM(C) saturated if C is
*)

Require Export UniMath.Foundations.Sets.

Require Import UniMath.Foundations.FunctionalExtensionality.

Require Export UniMath.CategoryTheory.precategories.
Require Export UniMath.CategoryTheory.functor_categories.
Require Export UniMath.CategoryTheory.category_hset.
Require Export UniMath.CategoryTheory.yoneda.
Require Export UniMath.CategoryTheory.rezk_completion.

Require Export Systems.Auxiliary.
Require Export Systems.UnicodeNotations.

Section Auxiliary.

Lemma transportf_eqweqmap (A B : UU) (p : A = B) C (A' : A → C) (b : B) :
  transportf (λ X, X → C) p A' b = A' (eqweqmap (!p) b).
Proof.
  induction p.
  apply idpath.
Defined.

Lemma eqweqmap_not (A B : UU) (p : A = B) (b : B) : 
  eqweqmap (!p) b = invweq (eqweqmap p ) b.
Proof.
  induction p.
  apply idpath.
Defined.

Lemma transportf_weqtopaths (A B : UU) (f : A ≃ B) C (A' : A → C) (b : B):
 transportf (λ x : UU, x → C) (weqtopaths f) A' b = A' (invmap f b).
Proof.
  rewrite transportf_eqweqmap.
  rewrite  eqweqmap_not.
  rewrite weqpathsweq.
  apply idpath.
Defined.  

Lemma transportf_toforallpaths {A B : UU} {f g : A → B} (H : f = g) 
   (P : A → B → UU) (x : ∀ a, P a (f a)) (a : A) : 
  transportf (λ b : B, P a b) (toforallpaths _ _ _ H a) (x a)
  = transportf (λ x0 : A → B, ∀ a0 : A, _ ) H x a.
Proof.
  intros.
  induction H.
  apply idpath.
Defined.

Lemma funextsec_idpath (A : UU) (B : A → UU) (f : ∀ a : A, B a)
  (H : ∀ x, f x = f x) (H' : ∀ x, H x = idpath _ ) 
  : funextsec _ _ _ H = idpath f.
Proof.
  eapply pathscomp0.
    eapply maponpaths. apply funextsec. apply H'.
  refine (homotinvweqweq _ (idpath f)).
Defined.

Lemma isweqpathscomp0l {X : UU} {x x' : X} (x'' : X) (e : x = x')
  : isweq (λ e' : x' = x'', e @ e').
Proof.
  destruct e. simpl. apply idisweq.
Qed.

Definition weqpathscomp0l {X : UU} {x x' : X} (x'' : X) (e : x = x')
  := weqpair _ (isweqpathscomp0l x'' e).

End Auxiliary.


Section FAM.

Variable C : precategory.

Definition obj_UU : UU := Σ A : UU, A → C.

Definition obj : UU := Σ A : obj_UU, isaset (pr1 A).

Definition obj_UU_from_obj (X : obj) : obj_UU := pr1 X.
Coercion obj_UU_from_obj : obj >-> obj_UU.

Definition index_type (A : obj) : UU := pr1 (pr1 A).
Definition index_func (A : obj) : index_type A → C := pr2 (pr1 A).

Notation "A ₁" := (index_type A)(at level 3).
Notation "A ₂" := (index_func A)(at level 3).


(*
Notation "A ₁" := (pr1 (pr1 A))(at level 3).
Notation "A ₂" := (pr2 (pr1 A))(at level 3).
 *)

Definition mor (A B : obj_UU) : UU := Σ f : pr1 A → pr1 B,
      ∀ a : pr1 A, pr2 A a ⇒ pr2 B (f a).

Definition FAM_obj_eq_type (A B : obj_UU) : UU 
  := 
  Σ f : pr1 A ≃ pr1 B, ∀ a : pr1 A, pr2 A a = pr2 B (f a).

Definition FAM_obj_eq_inv {A B : obj_UU} : A = B → FAM_obj_eq_type A B.
Proof.
  induction 1.
  exists (idweq _ ).
  exact (λ a, idpath _ ).
Defined.

Definition FAM_obj_UU_eq_inv {A B : obj} : A = B → FAM_obj_eq_type A B.
Proof.
  induction 1.
  exists (idweq _ ).
  exact (λ a, idpath _ ).
Defined.

Definition FAM_obj_UU_eq_sigma {A B : obj_UU} (f : pr1 A ≃ pr1 B) 
   (H : ∀ a : pr1 A, pr2 A a = pr2 B (f a)) : A = B.
Proof.
  apply (total2_paths (weqtopaths f)).
  apply funextsec; intro b.
  rewrite transportf_weqtopaths.
  rewrite H.
  apply maponpaths.
  apply homotweqinvweq.
Defined.

Definition FAM_obj_UU_weq (A B : obj_UU) : (A = B) ≃ FAM_obj_eq_type A B.
Proof.
  eapply weqcomp.
  - apply total2_paths_equiv.
  - apply (weqbandf (weqpair _ (univalenceaxiom _  _ ))).
    simpl.
    intro p.
    destruct A as [A x].
    destruct B as [B y].
    simpl in *.
    induction p.
    apply (weqtoforallpaths _ _ _ ).
Defined.

Definition FAM_obj_weq_1 (A B : obj) : (A = B) ≃ FAM_obj_eq_type A B.
Proof.   
  eapply weqcomp.
  - apply subtypeInjectivity.
    intros ? ; apply isapropisaset.
  - apply FAM_obj_UU_weq.
Defined.

Definition FAM_mor_eq_type {A B : obj} (f g : mor A B) : UU 
  := 
  Σ H : ∀ a : A ₁, pr1 f a = pr1 g a,
  (∀ a : A ₁, transportf (λ b, A ₂ a ⇒ B ₂ b) (H a) (pr2 f a) = pr2 g a).

Definition FAM_mor_equiv {A B : obj} (f g : mor A B) : 
   f = g ≃ FAM_mor_eq_type f g.
Proof.
  eapply weqcomp.
  - apply total2_paths_equiv.
  - refine ( @weqbandf _ _ (weqtoforallpaths _ _ _ ) _ _ _ ).
    simpl.
    intro H.
    destruct f as [f x].
    destruct g as [g y].
    simpl in *.
    eapply weqcomp. Focus 2. apply weqtoforallpaths.
    apply weqpathscomp0l.
    apply funextsec; intro t.
    apply (transportf_toforallpaths _ (λ a b, (A ₂) a ⇒ (B ₂) b)).
Defined.
  
Definition FAM_ob_mor : precategory_ob_mor.
Proof.
  exists obj.  
  exact (λ A B, Σ f : A ₁ → B ₁,
        ∀ a : A ₁, A ₂ a ⇒ B ₂ (f a)).
Defined.

Definition FAM_precategory_data : precategory_data.
Proof.
  exists FAM_ob_mor.
  split; intros.
  - exists (λ a, a). exact (λ a, identity _ ).
  - exists (λ a, pr1 X0 (pr1 X a)).
    exact (λ a, pr2 X _ ;; pr2 X0 _). 
Defined.

Lemma is_precategory_FAM : is_precategory FAM_precategory_data.
Proof.
  repeat split; intros; simpl.
  - apply (invmap (FAM_mor_equiv _ _ )). 
    exists (fun _ => idpath _ ).
    intros; apply id_left.
  - apply (invmap (FAM_mor_equiv _ _ )).
    exists (fun _ => idpath _ ).
    intros; apply id_right.
  - apply (invmap (FAM_mor_equiv _ _ )).
    exists (fun _ => idpath _ ). 
    intros; apply assoc.
Qed.

Definition FAM : precategory := tpair _ _ is_precategory_FAM.

Lemma has_homsets_FAM : has_homsets C → has_homsets FAM.
Proof.
  intro H.
  intros A B f g.
  apply (isofhlevelweqb 1 (FAM_mor_equiv f g)).
  apply isofhleveltotal2.
  - apply impred; intros ?.
    apply (pr2 B).
  - intros.
    apply impred; intros ? .
    apply H.
Qed.

(** ** [FAM(C)] is saturated if C is *)
(** we construct an equivalence between equalities between (A,f) and (B,g) and isos between them,
   by composing many "small" equivalences
   
    the first equivalence is [FAM_obj_weq_1] from above 
*)


Definition FAM_obj_eq_type_2 (A B : obj_UU) : UU 
  := 
  Σ f : pr1 A ≃ pr1 B, ∀ a : pr1 A, iso (pr2 A a) (pr2 B (f a)).

Lemma FAM_obj_weq_2 (A B : obj) (H : is_category C) :
  FAM_obj_eq_type A B ≃ FAM_obj_eq_type_2 A B.
Proof.
  unfold FAM_obj_eq_type, FAM_obj_eq_type_2.
  apply weqfibtototal.
  intro f.
  apply weqonsecfibers.
  intro x.
  assert (T:=pr1 H).
  exists (@idtoiso _ _ _ ).
  apply (pr1 H).
Defined.  

Lemma FAM_obj_weq_3 (A B : obj) : 
  FAM_obj_eq_type_2 A B ≃
          Σ f : pr1 (pr1 A) → pr1 (pr1 B), 
             Σ i : ∀ a : pr1 (pr1 A), pr2 (pr1 A) a ⇒ pr2 (pr1 B) (f a), isweq f × ∀ a, is_iso (i a).
Proof.
  unfold FAM_obj_eq_type_2.
  simpl.
  apply (weqcomp (weqtotal2asstor _ _ )).
  apply weqfibtototal.
  intro f. simpl.
  
  eapply weqcomp.
  - apply weqdirprodcomm.
  - apply invweq.
    eapply weqcomp.
    apply weqfibtototal.
    intro i.
    apply weqdirprodcomm.
    
    eapply weqcomp. 
      refine (weqtotal2asstol _ _ ).
        intro H. eapply (isweq f).
    
    eapply weqcomp.
       apply weqdirprodcomm.
    apply invweq.   
    eapply weqcomp.
       apply weqdirprodcomm.
     apply weqfibtototal.
     intro T.

     (* Search ( (∀ _ , _ ) ≃ (Σ _ , _ )). *)
     apply weqforalltototal.
Defined.
  

(** Characterisation of isos in [FAM] as pairs of a bijection and a family of isos **)

Definition isopair {C : precategory} {a b : C} (f : a ⇒ b) (H : is_iso f) : iso a b 
  := tpair _ f H.

Section isos.

Definition isweq_from_is_iso {A B : FAM} (f : A ⇒ B) : is_iso f → isweq (pr1 f). 
Proof.
  intro H.
  apply (gradth _ (pr1 (inv_from_iso (isopair f H)))).
  - intro x. 
    apply (toforallpaths _ _ _ (maponpaths pr1 (iso_inv_after_iso (isopair f H)))).
  - intro x.
    apply (toforallpaths _ _ _ (maponpaths pr1 (iso_after_iso_inv (isopair f H)))).
Defined.

Definition FAM_is_iso {A B : FAM} (f : A ⇒ B) : UU := 
   isweq (pr1 f) × (∀ x, is_iso (pr2 f x)).

Definition inv_from_FAM_is_iso {A B : FAM} {f : A ⇒ B} (H : FAM_is_iso f) : B ⇒ A.
Proof.
  set (finv := invmap (weqpair _ (pr1 H))).
  exists finv.
  intro b.
  set (H' := pr2 H (finv b)). simpl in H'.
  set (x  := isopair _ H': iso (A ₂ (finv b)) (B ₂ (pr1 f (finv b)))).
  set (xinv := inv_from_iso x).
  set (xinvtr := transportf (λ b', B ₂ b' ⇒ A ₂ (finv b))
         (homotweqinvweq _ _ ) xinv : B ₂ b ⇒ A ₂ (finv b)).
  exact xinvtr.
Defined.


Lemma transportf_comp (C' : precategory) (X : UU) (P : X → C') (a b : C') (x x' : X)
   (p : x = x')
   (f : a ⇒ b) (g : b ⇒ P x) : 
   transportf (λ c, a ⇒ P c) p (f ;; g) = 
    f ;; transportf (λ c, b ⇒ P c) p g.
Proof.
  induction p.
  apply idpath.
Qed.
    

Lemma is_iso_from_FAM_is_iso (A B : FAM) (f : A ⇒ B) : FAM_is_iso f → is_iso f.
Proof.
  intros H.
  apply is_iso_from_is_z_iso.
  exists (inv_from_FAM_is_iso H).
  destruct f as [f1 f2], H as [H1 H2]. simpl in *.
  split.
  - apply (invmap (FAM_mor_equiv _ _ )).
    exists (λ a, homotinvweqweq _ _ ).
    intro a. simpl.
    
    set (p := homotinvweqweq (weqpair f1 H1) a).
    set (p' := homotweqinvweq (weqpair f1 H1) (f1 a)).
    assert (tri : maponpaths f1 p = p'). apply (homotweqinvweqweq (weqpair _ _)).
    clearbody p'. destruct tri. simpl in *.

    assert (transp_lem : forall (a1 a2 : A ₁) (q : a2 = a1),
      transportf (λ b : A ₁, A ₂ a1 ⇒ A ₂ b) q
      (f2 a1 ;;
        transportf
          (λ b' : B ₁, B ₂ b' ⇒ A ₂ a2)
          (maponpaths f1 q)
          (inv_from_iso (isopair (f2 a2) (H2 a2))))
      = identity (A ₂ a1)).
      intros. destruct q; simpl. cbn. unfold idfun; simpl.
      apply (iso_inv_after_iso (isopair _ _)).
    apply transp_lem.

  - apply (invmap (FAM_mor_equiv _ _ )).
    exists (λ a, homotweqinvweq (weqpair _ _) _).
    intro b. simpl.
    set (p := (homotweqinvweq (weqpair f1 H1) b)).
    change (transportf (λ b0 : B ₁, B ₂ b ⇒ B ₂ b0)
                         (homotweqinvweq (weqpair f1 H1) b))
    with (transportf (λ b0 : B ₁, B ₂ b ⇒ B ₂ b0) p).
    set (a := (invmap (weqpair f1 H1) b)) in *. clearbody p. clearbody a.
    destruct p. cbn. unfold idfun; simpl. apply iso_after_iso_inv.
Qed.


Lemma FAM_is_iso_from_is_iso (A B : FAM) (f : A ⇒ B) : is_iso f → FAM_is_iso f.
Proof.
  intro f_iso.
  split.
  - apply isweq_from_is_iso. assumption.
  - set (g := iso_inv_from_iso (isopair f f_iso) : B ⇒ A).
    set (fg' := iso_inv_after_iso _ : f ;; g = identity A).
    set (gf' := iso_after_iso_inv _ : g ;; f = identity B).
    set (fg:= FAM_mor_equiv _ _ fg'). clearbody fg; clear fg'.
    set (gf:= FAM_mor_equiv _ _ gf'). clearbody gf; clear gf'.
    clearbody g; clear f_iso.
    
    destruct f as [f1 f2], g as [g1 g2],
             fg as [fg1 fg2], gf as [gf1 gf2]; simpl in *.
    intro a. 
    apply is_iso_from_is_z_iso.
    set (inv := transportf (λ a', B ₂ _  ⇒ A ₂ a') (fg1 a) (g2 (f1 a))).
    exists inv. subst inv.
    split.
    
    + eapply pathscomp0. Focus 2. apply fg2. symmetry.
      eapply pathscomp0. apply (functtransportf (A ₂)).
      eapply pathscomp0. symmetry; apply idtoiso_postcompose.
      eapply pathscomp0. symmetry; apply assoc.
      apply maponpaths. eapply pathscomp0. apply idtoiso_postcompose.
      symmetry. apply functtransportf.
      
    + eapply pathscomp0. Focus 2. apply gf2.
      eapply pathscomp0. cancel_postcomposition.
        eapply pathscomp0. apply (functtransportf (A ₂)).
        symmetry; apply idtoiso_postcompose.
      symmetry. eapply pathscomp0. apply (functtransportf (B ₂)).
      eapply pathscomp0. symmetry; apply idtoiso_postcompose.
      eapply pathscomp0. symmetry; apply assoc.
      eapply pathscomp0. Focus 2. apply assoc.
      apply maponpaths.

      assert (f2_natl : forall a1 a2 (p : a2 = a1),
                          f2 a2 ;; idtoiso (maponpaths (fun a => B ₂ (f1 a)) p)
                          = idtoiso (maponpaths (A ₂) p) ;; f2 a1).
        destruct p. eapply pathscomp0. apply id_right. sym. apply id_left.
      eapply pathscomp0. Focus 2. apply f2_natl.
      apply maponpaths , maponpaths, maponpaths.
      eapply pathscomp0. Focus 2. apply maponpathscomp.
      apply maponpaths. apply (pr2 B).
Qed.

Lemma isaprop_FAM_is_iso {A B : FAM} (f : A ⇒ B) : has_homsets C -> isaprop (FAM_is_iso f).
Proof.
  intros HC.
  apply isofhleveltotal2.
  - apply isapropisweq.
  - intros _. apply impred. intros. apply isaprop_is_iso.
Qed.

  
Lemma FAM_is_iso_weq {A B : FAM} (f : A ⇒ B)
  : has_homsets C -> is_iso f ≃ FAM_is_iso f.
Proof.
  intros HC. apply weqimplimpl.
  - apply FAM_is_iso_from_is_iso.
  - apply is_iso_from_FAM_is_iso.
  - apply isaprop_is_iso.
  - apply isaprop_FAM_is_iso. assumption.
Defined.

End isos.

Lemma FAM_obj_weq_4 (A B : ob FAM) : 
  (Σ f1 : pr1 (pr1 A) → pr1 (pr1 B), 
   Σ f2 : ∀ a : pr1 (pr1 A), pr2 (pr1 A) a ⇒ pr2 (pr1 B) (f1 a),
     isweq f1 × ∀ a, is_iso (f2 a))
  ≃ Σ (f : A ⇒ B), FAM_is_iso f.
Proof.
  refine (weqgradth _ _ _ _).
  - intros [f1 [f2 [wf1 wf2]]]. exists (tpair _ f1 f2). exists wf1. exact wf2.
  - intros [[f1 f2] [wf1 wf2]]. exists f1. exists f2. exists wf1. exact wf2.
  - intros [f1 [f2 [wf1 wf2]]]. simpl. apply idpath.
  - intros [[f1 f2] [wf1 wf2]]. simpl. apply idpath.
Defined.

Lemma FAM_obj_weq_5 (A B : ob FAM) (H : has_homsets C) 
  : (Σ (f : A ⇒ B), FAM_is_iso f)
  ≃ Σ (f : A ⇒ B), is_iso f.
Proof.
  refine (weqbandf _ _ _ _).
  - apply idweq.
  - simpl. intros. apply invweq. apply FAM_is_iso_weq. assumption.
Defined.

Definition FAM_obj_weq (A B : ob FAM) (H : is_category C)
: (A = B) ≃ Σ (f : A ⇒ B), is_iso f.
Proof.
  apply (weqcomp (FAM_obj_weq_1 A B)).
  apply (weqcomp (FAM_obj_weq_2 A B H)).
  apply (weqcomp (FAM_obj_weq_3 A B)).
  apply (weqcomp (FAM_obj_weq_4 A B)).
  exact (FAM_obj_weq_5 A B (pr2 H)).
Defined.

(* We still need to know that the underlying map of this equivalence agrees with [ idtoiso ]. *)

Definition FAM_id1 (A : ob FAM) : FAM_obj_eq_type (pr1 A) (pr1 A).
Proof.
  exists (idweq _). intros; apply idpath.
Defined.
  
Lemma FAM_obj_weq_1_id (A : ob FAM)
  : (FAM_obj_weq_1 A A (idpath A)) = FAM_id1 A.
Proof.
  apply (@total2_paths _ _
                       (FAM_obj_weq_1 A A (idpath A))
                       (FAM_id1 A)
                       (idpath _)).
  apply funextsec; intros t.
  destruct A as [[A1 A2] A3]; cbn. apply idpath.
Qed.

Definition FAM_id2 (A : ob FAM) : FAM_obj_eq_type_2 (pr1 A) (pr1 A).
Proof.
  exists (idweq _). intros; apply identity_iso.
Defined.

Lemma FAM_obj_weq_2_id (A : ob FAM) (H : is_category C)
  : (FAM_obj_weq_2 A A H (FAM_id1 A)) = FAM_id2 A.
Proof.
  apply (total2_paths (idpath _)).
  cbn. apply idpath.
Qed.

Definition FAM_id3 (A : ob FAM)
  : Σ (f : A ₁ → A ₁) (i : ∀ a : A ₁, A ₂ a ⇒ A ₂ (f a)),
          isweq f × (∀ a : A ₁, is_iso (i a)).
Proof.
  exists (idfun _). exists (fun a => identity _).
  split. apply idisweq. intros; apply identity_is_iso.
Defined.

Lemma FAM_obj_weq_3_id (A : ob FAM)
  : (FAM_obj_weq_3 A A (FAM_id2 A)) = FAM_id3 A.
Proof.
  apply (total2_paths (idpath _)).
  refine (total2_paths _ _).
  - apply funextsec; intros a.
    destruct A as [[A1 A2] A3].
    eapply pathscomp0. Focus 2. exact (idpath (identity _)).
    exact (idpath _).
  - apply proofirrelevance.
    apply isofhleveltotal2.
    + apply isapropisweq.
    + intros _. apply impred; intros. apply isaprop_is_iso.
Qed.

Definition FAM_id4 (A : ob FAM)
  : (Σ f : A ⇒ A, FAM_is_iso f).
Proof.
  exists (identity _).
  split; simpl. apply idisweq. intros; apply identity_is_iso.
Defined.

Lemma FAM_obj_weq_4_id (A : ob FAM)
  : (FAM_obj_weq_4 A A (FAM_id3 A)) = FAM_id4 A.
Proof.
  apply idpath.
Qed.

Lemma FAM_obj_weq_5_id (A : ob FAM) (H : has_homsets C)
  : pr1 (FAM_obj_weq_5 A A H (FAM_id4 A)) = identity A.
Proof.
  apply idpath.
Qed.

Lemma FAM_obj_weq_idpath (A : ob FAM) (H : is_category C)
  : (FAM_obj_weq A A H (idpath A)) = identity_iso A.
Proof.
  unfold FAM_obj_weq.
  eapply pathscomp0. eapply (maponpaths (FAM_obj_weq_5 A A (pr2 H))).
  eapply pathscomp0. eapply (maponpaths (FAM_obj_weq_4 A A)).
  eapply pathscomp0. eapply (maponpaths (FAM_obj_weq_3 A A)).
  eapply pathscomp0. eapply (maponpaths (FAM_obj_weq_2 A A H)).
  apply FAM_obj_weq_1_id.
  apply FAM_obj_weq_2_id.
  apply FAM_obj_weq_3_id.
  apply FAM_obj_weq_4_id.
  apply eq_iso, FAM_obj_weq_5_id.
Qed.
(* TODO: can we improve efficiency here? *)

Theorem FAM_is_category : is_category C -> is_category FAM.
Proof.
  intros H. split.
  - intros A B.
    apply (isweqhomot' (FAM_obj_weq A B H)).
    exact (pr2 (FAM_obj_weq A B H)).
    intros p; destruct p. apply FAM_obj_weq_idpath.
  - apply has_homsets_FAM. exact (pr2 H).
Qed.

End FAM.
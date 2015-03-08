
(** * The category FAM(C) *)
(**
  Contents:

    - Definition of the precategory FAM(C) for a precategory C
    - TODO: FAM(C) saturated if C is
*)

Require Export Systems.Auxiliary.
Require Export Systems.UnicodeNotations.
Require Export UniMath.Foundations.hlevel2.hSet.

Require Import UniMath.Foundations.Proof_of_Extensionality.funextfun.

Require Export RezkCompletion.precategories.
Require Export RezkCompletion.functors_transformations.
Require Export RezkCompletion.category_hset.
Require Export RezkCompletion.yoneda.
Require Export RezkCompletion.rezk_completion.

Require Export Systems.Auxiliary.

Search (transportf _ _ _ = _ ).

Lemma transportf_idpath (A : UU) (B : A → UU) (a : A) (x : B a) :
   transportf _ (idpath a) x = x.
Proof.
  apply idpath.
Defined.

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

Lemma transportf_toforallpaths (A B : UU) (f g : A → B) (P : B → UU)
   (x : ∀ a, P (f a)) (H : f = g) (a : A): 
  transportf (λ x0 : A → B, ∀ a0 : A, _ )
     H x a =
   transportf (λ b : B, P b) (toforallpaths _ _ _ H a) (x a).
Proof.
  intros.
  induction H.
  apply idpath.
Defined.

Lemma transportf_funext (A B : UU) (f g : A → B) (H : ∀ x, f x = g x) (a : A) (P : B → UU)
   (x : ∀ a, P (f a)) (x' : ∀ a, P (g a))  : 
  transportf (λ x0 : A → B, ∀ a0 : A, _ )
     (funextsec _ f g H) x a =
   transportf (λ b : B, P b ) (H a) (x a).
Proof.
  intros.
  rewrite transportf_toforallpaths.
  rewrite toforallpaths_funextsec.
  apply idpath.
Defined.

Lemma transportf_toforallpaths2 (A B : UU) (f g : A → B) (P : A → B → UU)
   (x : ∀ a, P a (f a)) (H : f = g) (a : A): 
  transportf (λ x0 : A → B, ∀ a0 : A, _ )
     H x a =
   transportf (λ b : B, P a b) (toforallpaths _ _ _ H a) (x a).
Proof.
  intros.
  induction H.
  apply idpath.
Defined.

Lemma transportf_funext2 (A B : UU) (f g : A → B) (H : ∀ x, f x = g x) (a : A) (P : A → B → UU)
   (x : ∀ a, P a (f a))   : 
  transportf (λ x0 : A → B, ∀ a0 : A, _ )
     (funextsec _ f g H) x a =
   transportf (λ b : B, P a b ) (H a) (x a).
Proof.
  intros.
  rewrite transportf_toforallpaths2.
  rewrite toforallpaths_funextsec.
  apply idpath.
Defined.

Definition path_assoc {X} {a b c d:X}
        (f : a = b) (g : b = c) (h : c = d)
      : f @ (g @ h) = (f @ g) @ h.
Proof.
  intros; destruct f; 
  apply  idpath.
Defined.



Lemma funextsec_idpath (A : UU) (B : A → UU) (f : ∀ a : A, B a)
  (H : ∀ x, f x = f x) (H' : ∀ x, H x = idpath _ ) 
  : funextsec _ _ _ H = idpath f.
Proof.
  set (H1:= invmaponpathsweq (weqtoforallpaths B f f)).
  apply H1.
  simpl.
  rewrite toforallpaths_funextsec.
  apply funextsec.
  intro a. simpl.
  apply H'.
Defined.

Lemma homot_toforallpaths_weq (A B : UU) (f g f' : A → B) (H : ∀ x, f x = f' x) :
   f = g ≃ ∀ x, f' x = g x.
Proof.
  exists (λ H', λ x, ! H x @ toforallpaths _ _ _ H' x).
  apply (gradth _ (λ H' : ∀ x, f' x = g x, (funextsec _ _ _ (λ x, H x @ H' x)))).
  - intro H'. induction H'.
    simpl. apply funextsec_idpath.
    intro a; rewrite path_assoc.
    rewrite pathscomp0rid.
    apply pathsinv0r.
  - intros.
    apply funextsec; intro a. simpl.
    rewrite toforallpaths_funextsec.
    rewrite path_assoc.
    rewrite pathsinv0l.
    apply idpath.
Defined.


Lemma homot_toforallpaths_dep_weq (A : UU) (B : A → UU) (f g f' : ∀ a, B a) (H : ∀ x, f x = f' x) :
   f = g ≃ ∀ x, f' x = g x.
Proof.
  exists (λ H', λ x, ! H x @ toforallpaths _ _ _ H' x).
  apply (gradth _ (λ H' : ∀ x, f' x = g x, (funextsec _ _ _ (λ x, H x @ H' x)))).
  - intro H'. induction H'.
    simpl. apply funextsec_idpath.
    intro a. rewrite path_assoc. 
    rewrite pathscomp0rid.
    apply pathsinv0r.
  - intros.
    apply funextsec; intro a. simpl.
    rewrite toforallpaths_funextsec.
    rewrite path_assoc.
    rewrite pathsinv0l.
    apply idpath.
Defined.


Section FAM.

Variable C : precategory.

Definition obj_UU : UU := Σ A : UU, A → C.

Definition obj : UU := Σ A : obj_UU, isaset (pr1 A).

Definition obj_UU_from_obj (X : obj) : obj_UU := pr1 X.
Coercion obj_UU_from_obj : obj >-> obj_UU.

Notation "A ₁" := (pr1 (pr1 A))(at level 3).
Notation "A ₂" := (pr2 (pr1 A))(at level 3).

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

Definition FAM_obj_weq (A B : obj) : (A = B) ≃ FAM_obj_eq_type A B.
Proof.   
  eapply weqcomp.
  - apply total2_paths_isaprop_equiv.
    intros ? ; apply isapropisaset.
  - apply FAM_obj_UU_weq.
Defined.

Definition FAM_mor_eq_type {A B : obj} (f g : mor A B) : UU 
  := 
  Σ H : ∀ a : A ₁, pr1 f a = pr1 g a,
  (∀ a : A ₁, transportf (λ b, A ₂ a ⇒ B ₂ b) (H a) (pr2 f a) = pr2 g a).

(* not needed, is integrated in FAM_mor_equiv
Lemma FAM_mor_eq {A B : obj} {f g : mor A B} 
  (H : ∀ a : A ₁, pr1 f a = pr1 g a) :  
  (∀ a : A ₁, transportf (λ b, A ₂ a ⇒ B ₂ b) (H a) (pr2 f a) = pr2 g a) → f = g.
Proof.
  intro t.
  apply (total2_paths (funextsec  _ _ _ H)).
  apply funextsec. intro a.
  destruct f as [f x].
  destruct g as [g x'].
  simpl in *.
  rewrite <- t; clear t.
  simpl in *.
  set (H1:= transportf_funext2 (A ₁) (B ₁) f g H a).
  set (H2 := H1 (fun a b => A ₂ a ⇒ B ₂ b) ). simpl in *.
  apply H2.
Defined.  
*)

(* not needed, is integrated in FAM_mor_equiv
Definition FAM_mor_eq_sigma {A B : obj} {f g : mor A B} : 
   (Σ H : ∀ a : A ₁, pr1 f a = pr1 g a,
     ∀ a : A ₁, transportf (λ b, A ₂ a ⇒ B ₂ b) (H a) (pr2 f a) = pr2 g a)
   → f = g 
  := λ Hx, FAM_mor_eq (pr1 Hx) (pr2 Hx).
*)

(* not needed, is integrated in FAM_mor_equiv
Lemma FAM_mor_eq_inv {A B : obj} {f g : mor A B} : f = g → 
   Σ H : ∀ a : A ₁, pr1 f a = pr1 g a,
     ∀ a : A ₁, transportf (λ b, A ₂ a ⇒ B ₂ b) (H a) (pr2 f a) = pr2 g a.
Proof.
  induction 1.
  exists (λ _ , idpath _ ).
  intro a.
  apply idpath.
Defined.
*)

(*  Lemmas towards a proof of what is already done in Foundations as weqbandf

Definition Sigma_retype {A A' : UU} (B : A' → UU) (f : A → A') : A → UU 
  := λ a, B (f a).
 
Definition Sigma_retype_map {A A' : UU} (B : A' → UU) (f : A ≃ A') : 
  (Σ a' : A', B a') → Σ a : A, Sigma_retype B f a.
Proof.
  intro ap.
  exists (invmap f (pr1 ap)).
  unfold Sigma_retype.
  exact (transportf (λ a, B a) (! homotweqinvweq _ _ ) (pr2 ap)).
Defined.
  
Definition Sigma_retype_inv {A A' : UU} (B : A' → UU) (f : A ≃ A') : 
  (Σ a : A, Sigma_retype B f a) → (Σ a' : A', B a').
Proof.
  intro ap.
  unfold Sigma_retype in ap.
  exists (f (pr1 ap)).
  exact (pr2 ap).
Defined.

Definition Sigma_retype_weq {A A' : UU} (hs : isaset A') (B : A' → UU) (f : A ≃ A') : 
  (Σ a' : A', B a') ≃ Σ a : A, Sigma_retype B f a.
Proof.
  exists (Sigma_retype_map _ _ ).
  apply (gradth _ (Sigma_retype_inv _ _ )).
  - intro x. simpl in *.
    refine (total2_paths _ _ ).
    exact (homotweqinvweq f (pr1 x)).
    simpl. rewrite  transportf_pathscomp0.
    Search (! _ @ _ = _ ).
    rewrite (pathsinv0l).
    apply idpath.
  - intro x; simpl in *.
    refine (total2_paths _ _ ).
    exact (homotinvweqweq _ _ ).
    simpl. unfold Sigma_retype in *. simpl in *. 
    destruct x as [a p]. simpl in *.
    rewrite  functtransportf.
    rewrite transportf_pathscomp0.
    Search (  maponpaths _ _ @ _ ).
    simpl.
    assert (H : (! homotweqinvweq f (f a) @ maponpaths f (homotinvweqweq f a)) = idpath _ ).
      { apply proofirrelevance. apply hs. }
    rewrite H.
    apply idpath.
Defined.

Definition Sigma_pointwise_map {A : UU} (B B' : A → UU) (x : ∀ a, B a ≃ B' a) : 
   (Σ a, B a) → Σ a, B' a.
Proof.
  intro ap.  
  exact (tpair _ (pr1 ap) (x _ (pr2 ap))).
Defined.

Definition Sigma_pointwise_inv {A : UU} (B B' : A → UU) (x : ∀ a, B a ≃ B' a) : 
   (Σ a, B' a) → Σ a, B a.
Proof.
  intro ap.  
  exact (tpair _ (pr1 ap) (invmap (x _) (pr2 ap))).
Defined.

Definition Sigma_pointwise_weq {A : UU} (B B' : A → UU) (x : ∀ a, B a ≃ B' a) : 
   (Σ a, B a) ≃ Σ a, B' a.
Proof.
  exists (Sigma_pointwise_map _ _ x).  
  apply (gradth _ (Sigma_pointwise_inv _ _ x )).
  - intros [a p]; simpl.
    unfold Sigma_pointwise_inv. unfold Sigma_pointwise_map.
    simpl.
    apply maponpaths.
    apply homotinvweqweq.
  - intros [a p].
    unfold Sigma_pointwise_inv, Sigma_pointwise_map; simpl.
    apply maponpaths.
    apply homotweqinvweq.
Defined.


Lemma weq_Sigmas {A A' : UU} {B : A → UU} {B' : A' → UU} (hs : isaset A') (f : A ≃ A') 
   (P : ∀ a : A, B a ≃ B' (f a)) : (Σ a, B a) ≃ Σ a', B' a'.
Proof.
  eapply weqcomp.
    Focus 2.
      set (x := @Sigma_retype_weq A A' hs B' f).
      apply (invweq x).
   apply Sigma_pointwise_weq.
   apply P.
Defined.
*)

Definition FAM_mor_equiv {A B : obj} (f g : mor A B) : 
   f = g ≃ FAM_mor_eq_type f g.
Proof.
  eapply weqcomp.
  - apply total2_paths_equiv.
  - refine ( @weqbandf _ _ (weqtoforallpaths _ _ _ ) _ _ _ ).
   + simpl.
     intro H.
     set (H':=homot_toforallpaths_dep_weq).
     destruct f as [f x].
     destruct g as [g y].
     simpl in *.
     refine (homot_toforallpaths_dep_weq _ _ _ _ _ _ ).
     intro a. 
     destruct A as [[A F] Ahs].
     destruct B as [[B G] Bhs].
     simpl in *.
     set (H2 := transportf_toforallpaths2).
     set (H3 := H2 _ _  f g ). 
     set (H4:=  H3 (λ a b, F a ⇒ G b)). apply H4.
Defined.
  
Definition FAM_ob_mor : precategory_ob_mor.
Proof.
  exists obj.  
  exact  (λ A B, Σ f : A ₁ → B ₁,
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


(*Definition FAM_iso (A B : FAM) : UU := Σ f : A ⇒ B,
    isweq (pr1 f) × (∀ x, is_iso (pr2 f x)).
*)
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
  intro H.
  apply is_iso_from_is_z_iso.
  exists (inv_from_FAM_is_iso H).
  split.
  - apply (invmap (FAM_mor_equiv _ _ )).
    exists (λ a, homotinvweqweq _ _ ).
    intro a.
    simpl.
    set (H':= pr2 H a). 
    set (H2 := is_z_iso_from_is_iso _ H').
    
    set (ff := weqpair (pr1 f) (pr1 H)).
    set (aa := isopair (pr2 f a) (pr2 H a)).
    set (Hinv1:= pr1 (pr2 H2)).
    rewrite <- Hinv1.
    destruct f as [f x]; simpl in *.
    destruct H2 as [xa_inv [Ha Hb]]; simpl in *.
    rewrite transportf_comp.
    apply maponpaths.
    Check (homotweqinvweq ff (f a)). (* ff (invmap ff (f a)) = f a *)
    Check (homotinvweqweq ff a). (* invmap ff (ff a) = a *)
    admit.
  - apply (invmap (FAM_mor_equiv _ _ )).
    exists (λ a, homotweqinvweq _ _ ).
    intro b.
    admit.
Qed.

Lemma FAM_is_iso_from_is_iso (A B : FAM) (f : A ⇒ B) : is_iso f → FAM_is_iso f.
Proof.
  intro H.
  split.
  - apply isweq_from_is_iso. assumption.
  - intro a.
    set (ff:=isopair f H).
    set (finv := iso_inv_from_iso ff).
    set (HH := iso_inv_after_iso ff).
    set (HHH := iso_after_iso_inv ff).
    set (HH':= FAM_mor_equiv _ _ HH). clearbody HH'.
    set (HHH':= FAM_mor_equiv _ _ HHH). clearbody HHH'.
    set (HH'':= pr1 HH'). simpl in *.
    apply is_iso_from_is_z_iso.
    set (H2:= finv ₂ (pr1 f a)). simpl in *.
    set (inv:= transportf (λ a', B ₂ _  ⇒ A ₂ a') (HH'' a) H2). simpl in *.
    exists inv.
    split.
    + unfold inv. simpl in *.
      set (H1:= pr2 HH' a). simpl in *. unfold HH''. simpl in *.
      unfold H2. 
      rewrite <- H1.
      apply pathsinv0.
      apply transportf_comp.
    + unfold inv. simpl in *.
      set (H1:= pr2 HHH' (pr1 f a)). simpl in *.
      unfold HH''. unfold H2. simpl in *.
      rewrite <- H1.
      set (H4:=homotinvweqweq (weqpair _ (isweq_from_is_iso f H)) a). simpl in *.
      clearbody H4.
      clear H4.
      rewrite  transportf_comp. 
      clear H1. clear HH. clear HHH. 

      Check (pr1 HHH'(pr1 f a)). (* (inv_from_iso f ;; f) (f ₁ a) = identity B (f ₁ a) *)
      Check (pr1 HH' a) (* (f ;; inv_from_iso f) a = identity A a *) .
      idtac.
      admit.
Qed.

End isos.

End FAM.
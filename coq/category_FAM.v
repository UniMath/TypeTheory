
(** * The category FAM(C) *)
(**
  Contents:

    - Definition of the precategory FAM(C) for a precategory C
    - TODO: FAM(C) saturated if C is
*)

Require Export Systems.Auxiliary.
Require Export Systems.UnicodeNotations.
Require Export UniMath.Foundations.hlevel2.hSet.

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

Definition obj : UU := Σ A : hSet, A → C.
Definition mor (A B : obj) : UU := Σ f : pr1 A → pr1 B,
      ∀ a : (pr1 A), (pr2 A) a ⇒ (pr2 B) (f a).

Definition FAM_mor_eq_type {A B : obj} (f g : mor A B) : UU 
  := 
  Σ H : ∀ a : pr1 A, pr1 f a = pr1 g a,
  (∀ a : pr1 A, transportf (λ b, pr2 A a ⇒ pr2 B b) (H a) (pr2 f a) = pr2 g a).

Lemma FAM_mor_eq {A B : obj} {f g : mor A B} 
  (H : ∀ a : pr1 A, pr1 f a = pr1 g a) :  
  (∀ a : pr1 A, transportf (λ b, pr2 A a ⇒ pr2 B b) (H a) (pr2 f a) = pr2 g a) → f = g.
Proof.
  intro t.
  apply (total2_paths (funextsec  _ _ _ H)).
  apply funextsec. intro a.
  destruct f as [f x].
  destruct g as [g x'].
  simpl in *.
  rewrite <- t; clear t.
  simpl in *.
  set (H1:= transportf_funext2 (pr1 A) (pr1 B) f g H a).
  set (H2 := H1 (fun a b =>  pr2 A a ⇒ pr2 B b) ). simpl in *.
  apply H2.
Defined.  

Definition FAM_mor_eq_sigma {A B : obj} {f g : mor A B} : 
   (Σ H : ∀ a : pr1 A, pr1 f a = pr1 g a,
     ∀ a : pr1 A, transportf (λ b, pr2 A a ⇒ pr2 B b) (H a) (pr2 f a) = pr2 g a)
   → f = g 
  := λ Hx, FAM_mor_eq (pr1 Hx) (pr2 Hx).

Lemma FAM_mor_eq_inv {A B : obj} {f g : mor A B} : f = g → 
   Σ H : ∀ a : pr1 A, pr1 f a = pr1 g a,
     ∀ a : pr1 A, transportf (λ b, pr2 A a ⇒ pr2 B b) (H a) (pr2 f a) = pr2 g a.
Proof.
  induction 1.
  exists (λ _ , idpath _ ).
  intro a.
  apply idpath.
Defined.

(*
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
  - 
  Print funextsec.
  refine ( @weqbandf _ _ (weqtoforallpaths _ _ _ ) _ _ _ ).
   + simpl.
     intro H.
     set (H':=homot_toforallpaths_dep_weq).
     destruct f as [f x].
     destruct g as [g y].
     simpl in *.
     refine (homot_toforallpaths_dep_weq _ _ _ _ _ _ ).
     intro a. 
     destruct A as [A F].
     destruct B as [B G].
     simpl in *.
     set (H2 := transportf_toforallpaths2).
     set (H3 := H2 A B f g ). 
     set (H4:=  H3 (λ a b, F a ⇒ G b)). apply H4.
Defined.
  
  
Definition FAM_ob_mor : precategory_ob_mor.
Proof.
  exists (Σ A : hSet, A → C).  
  exact  (λ A B, Σ f : pr1 A → pr1 B,
      ∀ a : (pr1 A), (pr2 A) a ⇒ (pr2 B) (f a)).
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
  - refine (@FAM_mor_eq _ _ _ _ _ _ ).
    + exact (fun _ => idpath _ ).
    + intros. simpl . 
      rewrite transportf_idpath.
      apply id_left.
  - refine (@FAM_mor_eq _ _ _ _ _ _ ).
    + exact (fun _ => idpath _ ).
    + intros; rewrite transportf_idpath.
      apply id_right.
  - refine (@FAM_mor_eq _ _ _ _ _ _ ).
    + exact (fun _ => idpath _ ). 
    + intros; rewrite transportf_idpath.
      apply assoc.
Qed.

Definition FAM : precategory := tpair _ _ is_precategory_FAM.

(** Characterisation of isos in [FAM] as pairs of a bijection and a family of isos **)

Section isos.

Definition isweq_from_iso {A B : FAM} (f : iso A B) : isweq (pr1 (pr1 f)). 
Proof.
  apply (gradth _ (pr1 (inv_from_iso f))).
  - intro x. 
    apply (toforallpaths _ _ _ (maponpaths pr1 (iso_inv_after_iso f))).
  - intro x.
    apply (toforallpaths _ _ _ (maponpaths pr1 (iso_after_iso_inv f))).
Defined.


Definition FAM_iso (A B : FAM) : UU := Σ f : A ⇒ B,
    isweq (pr1 f) × (∀ x, is_iso (pr2 f x)).

Lemma weq_iso_FAM_iso (A B : FAM) : iso A B → FAM_iso A B.
Proof.
  intro f.
  exists (pr1 f).
  split. 
  - apply isweq_from_iso.
  - intro a.
    set (H := iso_inv_from_iso f).
    set (HH := iso_inv_after_iso f).
    set (HHH := iso_after_iso_inv f).
    set (HH':= FAM_mor_equiv _ _ HH). clearbody HH'.
    set (HHH':= FAM_mor_equiv _ _ HHH). clearbody HHH'.
    set (HH'':= pr1 HH'). simpl in *.
    apply is_iso_from_is_z_iso.
    set (H2:= pr2 (pr1 H)). simpl in *.
    set (inv:= transportf (λ a', pr2 B _  ⇒ pr2 A a') (HH'' a) (H2 (pr1 (pr1 f) a))).
    simpl in *.
    exists inv.
    split.
    + unfold inv. simpl in *.
      set (H1:= pr2 HH' a). simpl in *. unfold HH''. simpl in *.
      unfold H2. Check (pr1 HH' a). 
      admit.
    + unfold inv. simpl in *.
      set (H1:= pr2 HHH' (pr1 (pr1 f) a)). simpl in *.
      unfold HH''. unfold H2. simpl in *.
      rewrite <- H1.
      set (H4:=homotinvweqweq (weqpair _ (isweq_from_iso f)) a). simpl in *.
      clearbody H4.
      assert (H3 : pr1 (inv_from_iso f) (pr1 (pr1 f) a) = a).
      {  set (H5:= homotinvweqweq (weqpair _ (isweq_from_iso f))). 
          apply H5. } 
      assert (H4 : pr2 f (pr1 (inv_from_iso f) (pr1 (pr1 f) a)) = 
                   pr2 f a).
      rewrite H3 in H1.
      pattern 
      simpl in *.
      rewrite H3.
     in H4; simpl in H4.
      rewrite H4.
      Check (pr1 HH' a).
      admit.
Defined.

      rewrite <- H1.
      simpl in *.
      destruct f as [f isisof].
      simpl in *.
      Search (transportf _ _ ( _ ;; _ )).
      unfold HH'.
      unfold HHH' in H1.
    Focus 2.
    set (inv:= H2 (pr1 (pr1 f) x)).
    assert (H': pr1 (inv_from_iso f) (pr1 (pr1 f) x) = x).
    { rewrite <- H8. apply idpath. }
    rewrite H' in inv. clear H'. clear H8. clear H6.
    exists inv.
    set (H':=is_z_iso_from_is_iso f (pr2 f)).
    set (H1:=pr1 (pr2 H')).
    set (H3 := FAM_mor_equiv _ _ H1).
    unfold FAM_mor_eq_type in H3. clearbody H3. simpl in *.
    split.
    + set (H3':= pr2 H3 x).
      rewrite <- H3'. clear H3'.  unfold compose. simpl in *.
      simpl. unfold inv.
      clear H3' H3.
    
    
    simpl in *.

    rewrite H8 in inv. set (H6 := weqpair _ (isweq_from_iso f)).
    
    unfold H6 in H7. simpl in *.
    rewrite (H7) in inv.
    set (H3 := pr1 (pr1 f)). simpl in *.
    set (H4 := H3 x).
    set (H5:= pr1
    exists (pr1 H ((pr1 (pr1 f)) x)).
    
    destruct f as [f is_iso_f].
    simpl in *.
    set (H2:= pr2 H). simpl in *.
    Print mor.
    set (H3 := pr1 (pr1 f)). simpl in *.
    set (H4 := H3 x).
    set (H5:= pr1
    exists (pr1 H ((pr1 (pr1 f)) x)).
    apply bla.
  admit.
Defined.


Definition fam_of_isos_from_iso (f : iso A B) 
  : ∀ a : pr1 A, iso (pr2 A a) (pr2 B (pr1 (pr1 f) a)) .
Proof.  
  intro a.
  exists (pr2 (pr1 f) a).
  set (H:= pr2 (inv_from_iso f) (pr1 (pr1 f) a)).
  simpl in *.
  set (H1:=toforallpaths _ _ _ (maponpaths pr1 (iso_inv_after_iso f))).
  simpl in H1.
  rewrite (H1) in H. clear H1.
  apply is_iso_from_is_z_iso.
  exists H.
  split.
  - set (H1:= (iso_inv_after_iso f)).
    set (H2:= pr2 H1).
    simpl in *.

End FAM.
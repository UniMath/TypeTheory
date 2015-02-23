
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

Search (transportf _ _ _ = _ ).

Lemma transportf_idpath (A : UU) (B : A → UU) (a : A) (x : B a) :
   transportf _ (idpath a) x = x.
Proof.
  apply idpath.
Defined.

Lemma function_eq {A B : UU} {f g : A → B} (H : f = g) (a : A) : f a = g a.
Proof.
  induction H.
  apply idpath.
Defined.
Print toforallpaths.
Lemma transportf_toforallpaths (A B : UU) (f g : A → B) (P : B → UU)
   (x : ∀ a, P (f a)) (*x' : ∀ a, P (g a)*) (H : f = g) (a : A): 
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
   (x : ∀ a, P a (f a)) (*x' : ∀ a, P (g a)*) (H : f = g) (a : A): 
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


Section FAM.

Variable C : precategory.

Definition obj : UU := Σ A : hSet, A → C.
Definition mor (A B : obj) : UU := Σ f : pr1 A → pr1 B,
      ∀ a : (pr1 A), (pr2 A) a ⇒ (pr2 B) (f a).

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

End FAM.
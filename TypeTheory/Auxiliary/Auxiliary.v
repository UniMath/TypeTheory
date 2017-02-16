(**
  [TypeTheory.Auxiliary.Auxiliary]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(** 

Auxiliary background lemmas for the Ahrens/Lumsdaine/Voevodsky “Systems” project.  
Possibly some should be upstreamed to “UniMath” eventually.

*)


Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.pullbacks.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.
Require Import UniMath.CategoryTheory.category_hset_structures.

(*

Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.pullbacks.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.category_hset_structures.
Require Import UniMath.CategoryTheory.yoneda.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.equivalences.
*)
Require Import TypeTheory.Auxiliary.UnicodeNotations.

Set Automatic Introduction.

Undelimit Scope transport.

Notation "( x , y , .. , z )" := (dirprodpair .. (dirprodpair x y) .. z) : core_scope.
(** Replaces builtin notation for [pair], since we use [dirprod, dirprodpair] instead of [prod, pair]. *)


(** Redeclare this notation, along with a new scope. *)
Notation "ff ;; gg" := (compose ff gg)
  (at level 50, left associativity, format "ff  ;;  gg")
  : mor_scope.
Delimit Scope mor_scope with mor.
Bind Scope mor_scope with precategory_morphisms.
Open Scope mor_scope.


(** * Some tactics *)

Tactic Notation "etrans" := eapply pathscomp0.
Tactic Notation "rew_trans_@" := repeat (etrans ; [ apply transport_f_f |]).
Tactic Notation "sym" := apply pathsinv0.
Tactic Notation "assoc" := apply @pathsinv0, path_assoc.
Tactic Notation "cancel_postcomposition" := apply cancel_postcomposition.

(** * Some argument settings *)

Arguments functor_on_inv_from_iso {_ _} _  {_ _} f.

(** * Path-algebra: general lemmas about transport, equivalences, etc. *)

Lemma weqhomot {A B : UU} (f : A -> B) (w : A ≃ B) (H : w ~ f) : isweq f.
Proof.
  apply isweqhomot with w. apply H. apply weqproperty.
Defined.

(** A useful lemma for binary functions, generalising e.g. [cancel_postcomposition]: *)
(*TODO: look carefully for this in the library *)
Definition maponpaths_2 {X Y Z : UU} (f : X -> Y -> Z) {x x'} (e : x = x') y
  : f x y = f x' y
:= maponpaths (fun x => f x y) e.

Lemma pr1_transportf (A : UU) (B : A -> UU) (P : ∏ a, B a -> UU)
   (a a' : A) (e : a = a') (xs : ∑ b : B a, P _ b):
   pr1 (transportf (fun x => ∑ b : B x, P _ b) e xs) = 
     transportf (fun x => B x) e (pr1 xs).
Proof.
  destruct e; apply idpath.
Defined.

Lemma transportf_const (A B : UU) (a a' : A) (e : a = a') (b : B) :
   transportf (fun _ => B) e b = b.
Proof.
  induction e.
  apply idpath.
Defined.

Lemma transportf_forall {A B} (C : A -> B -> UU)
  {x0 x1 : A} (e : x0 = x1) (f : forall y:B, C x0 y)
  : transportf (fun x => forall y, C x y) e f
  = fun y => transportf (fun x => C x y) e (f y).
Proof.
  destruct e; apply idpath.
Defined.

Definition transportf_forall_var :
  ∏ (A : UU) (B : A -> UU) (C : UU)
    (a1 a2 : A) (e : a1 = a2)
    (f : B a1 -> C),
  transportf (λ x : A, ∏ y : B x, C) e f =
  (λ y : B a2 , f (transportb B e y)).
Proof.
  intros A B D a1 a2 e f.
  induction e.
  apply idpath.
Defined.

Definition transportf_forall_var2 :
  ∏ (A : UU) (B C : A -> UU) 
    (a1 a2 : A) (e : a1 = a2)
    (f : B a1 -> C a1),
  transportf (λ x : A, ∏ y : B x, C x) e f =  
  (λ y : B a2 , transportf _ e (f (transportb B e y))).
Proof.
  intros A B D a1 a2 e f.
  induction e.
  apply idpath.
Defined.

Lemma maponpaths_apply {A B} {f0 f1 : A -> B} (e : f0 = f1) (x : A)
  : maponpaths (fun f => f x) e
  = toforallpaths _ _ _ e x.
Proof.
  destruct e; apply idpath.
Defined.

Lemma maponpaths_eq_idpath
  : ∏ (T1 T2 : UU) (f : T1 -> T2) (t1 : T1) (e : t1 = t1)
      (H : e = idpath _ ), maponpaths f e = idpath _ .
Proof.
  intros.
  exact (maponpaths (maponpaths f) H).
Defined.

Lemma transportf_comp_lemma (X : UU) (B : X -> UU) {A A' A'': X} (e : A = A'') (e' : A' = A'')
  (x : B A) (x' : B A')
  : transportf _ (e @ !e') x = x'
  -> transportf _ e x = transportf _ e' x'.
Proof.
  intro H.
  eapply pathscomp0. Focus 2.
    apply maponpaths. exact H.
  eapply pathscomp0. Focus 2.
    symmetry. apply transport_f_f.
  apply (maponpaths (fun p => transportf _ p x)).
  apply pathsinv0.
  eapply pathscomp0.
  - apply @pathsinv0, path_assoc. 
  - eapply pathscomp0. 
    apply maponpaths.
    apply pathsinv0l.
    apply pathscomp0rid.
Defined.

Lemma transportf_comp_lemma_hset (X : UU) (B : X -> UU) (A : X) (e : A = A)
  {x x' : B A} (hs : isaset X)
  : x = x'
  -> transportf _ e x = x'.
Proof.
  intros ex.
  apply @pathscomp0 with (transportf _ (idpath _) x).
  - apply (maponpaths (fun p => transportf _ p x)).
    apply hs.
  - exact ex.
Qed.

(* TODO: redundant: replace with general-purpose [maponpaths_2]. *)
Lemma transportf_ext (X : UU) (B : X -> UU) (A A' : X) (e e' : A = A') p :
  e = e' -> transportf _ e p = transportf B e' p.
Proof.
  intro H; induction H; apply idpath.
Defined.

(** ** Lemmas on equivalences *)

Lemma invmap_eq {A B : UU} (f : A ≃ B) (b : B) (a : A)
  : b = f a → invmap f b = a.
Proof.
  intro H.
  apply (invmaponpathsweq f).
  etrans. apply homotweqinvweq. apply H.
Defined.

Definition isweqpathscomp0l {X : UU} {x x' : X} (x'' : X) (e: x = x') :
   isweq (fun (e' : x' = x'') => e @ e').
Proof.
  intros.
  apply (gradth _ (fun e'' => !e @ e'')).
  - intro p. rewrite path_assoc. rewrite pathsinv0l.
    apply idpath.
  - intro p. rewrite path_assoc. rewrite pathsinv0r.
    apply idpath.
Defined.

(*
Definition rewrite_in_equivalence (A X : UU) (a a' b : A) :
  a = a' → (a' = b) ≃ X → (a = b) ≃ X.
Proof.
  intros.
  set  (H:= weqpair _ (isweqpathscomp0l b (!X0))).
  eapply weqcomp. apply H.
  apply X1.
Defined.
*)

(** ** Other general lemmas *)

(* A slightly surprising but very useful lemma for characterising identity types.

Concisely: to show that a family of functions [w : forall a b, a = b -> P a b] are equivalences, it’s enough to show they have a retraction; the retraction is then automatically a quasi-inverse, because of the fact that the coconut is contractible.
 
Often one can save a bit of work with this (since the other direction of inverseness may not be so obvious in individual cases).

TODO: move; consider naming; see if this can be used to simplify other proofs of [is_category] and similar? *)
Lemma eq_equiv_from_retraction {A} {P : A -> A -> UU} 
    (w : forall a b, a = b -> P a b)
    (v : forall a b, P a b -> a = b)
  : (forall a b (p : P a b), w _ _ (v _ _ p) = p)
  -> forall a b, isweq (w a b).
Proof.
  intros wv a.
  apply isweqtotaltofib. (* first of the two key steps *)
  use gradth.
  - intros bp. exists (pr1 bp). apply v, (pr2 bp).
  - intros be; apply connectedcoconusfromt. (* the second key step *)
  - intros bp. use total2_paths_f. apply idpath. apply wv.
Qed.


(** * Algebra in (pre)categories *)

Lemma is_iso_comp_is_iso {C : precategory} {a b c : ob C}
  (f : C⟦a, b⟧) (g : C⟦b, c⟧) 
  : is_iso f -> is_iso g -> is_iso (f ;; g).
Proof.
  intros Hf Hg.
  apply (is_iso_comp_of_isos (isopair f Hf) (isopair g Hg)).
Defined.

Lemma functor_is_iso_is_iso {C C' : precategory} (F : functor C C')
    {a b : ob C} (f : C ⟦a,b⟧) (fH : is_iso f) : is_isomorphism (#F f).
Proof.
  apply (functor_on_iso_is_iso _ _ F _ _ (isopair f fH)).
Defined.


(* TODO: check more thoroughly if this is provided in the library; if so, use the library version, otherwise move this upstream.  Cf. also https://github.com/UniMath/UniMath/issues/279 *)
Lemma inv_from_iso_from_is_z_iso {D: precategory} {a b : D}
  (f: a --> b) (g : b --> a) (H : is_inverse_in_precat f g)
: inv_from_iso (f ,, (is_iso_from_is_z_iso _ (g ,, H))) 
  = g.
Proof.
  cbn. apply id_right.
Qed.

(** The total type of morphisms of a precategory *)
Definition mor_total (C : precategory) : UU
  := ∑ (ab : C × C), C⟦pr2 ab, pr1 ab⟧.

Definition morphism_as_total {C : precategory} {a b : C} (f : a --> b)
  := ((_,,_),,f) : mor_total C.

Definition source {C} (X : mor_total C) : C := pr2 (pr1 X).
Definition target {C} (X : mor_total C) : C := pr1 (pr1 X).
Definition morphism_from_total {C} (X : mor_total C)
  : C ⟦source X, target X⟧
  := pr2 X.
Coercion morphism_from_total : mor_total >-> precategory_morphisms.


(** ** Equivalences of categories *)
(** Specifically: the composition of (adjoint) equivalences of precats. *)

Coercion left_adj_from_adj_equiv (X Y : precategory) (K : functor X Y)
         (HK : adj_equivalence_of_precats K)
  : is_left_adjoint K
:= pr1 HK.

Section about_equivalences.

Variables D1 D2 : precategory.
Variable F : functor D1 D2.
Variable GG : adj_equivalence_of_precats F.

Let G : functor D2 D1 := right_adjoint GG.
Let η := unit_from_left_adjoint GG.
Let ε := counit_from_left_adjoint GG.
Let ηinv a := iso_inv_from_iso (unit_pointwise_iso_from_adj_equivalence GG a).
Let εinv a := iso_inv_from_iso (counit_pointwise_iso_from_adj_equivalence GG a).


Lemma right_adj_equiv_is_ff : fully_faithful G.
Proof.
  intros c d.
  set (inv := (fun f : D1 ⟦G c, G d⟧ => εinv _ ;; #F f ;; ε _ )).
  simpl in inv.
  apply (gradth _ inv ).
  - intro f. simpl in f. unfold inv.
    assert (XR := nat_trans_ax ε). simpl in XR.
    rewrite <- assoc.
    etrans. apply maponpaths. apply XR.
    rewrite assoc.
    etrans. apply cancel_postcomposition. apply iso_after_iso_inv.
    apply id_left.
  - intro g.
    unfold inv. repeat rewrite functor_comp.
    match goal with |[|- ?f1 ;; ?f2 ;; ?f3 = _ ] =>
       pathvia ((f1 ;; ηinv _ ) ;; (η _ ;; f2) ;; f3) end.
    + repeat rewrite <- assoc. apply maponpaths.
      repeat rewrite assoc.
      etrans. Focus 2. do 2 apply cancel_postcomposition. eapply pathsinv0, iso_after_iso_inv.
      rewrite id_left. apply idpath.
    + assert (XR := nat_trans_ax η). simpl in XR. rewrite <- XR. clear XR.
      repeat rewrite <- assoc.
      etrans. do 3 apply maponpaths. apply  triangle_id_right_ad. rewrite id_right.
      rewrite assoc.
      etrans. Focus 2. apply id_left.
      apply cancel_postcomposition.
      etrans. apply cancel_postcomposition. apply functor_on_inv_from_iso.
      assert (XR := triangle_id_right_ad (pr2 (pr1 GG))).
      simpl in XR.
      unfold ηinv. simpl.
      match goal with |[|- inv_from_iso ?e ;; inv_from_iso ?f = _ ] =>
                       assert (XRR := maponpaths pr1 (iso_inv_of_iso_comp _ _ _ _ f e)) end. 
      simpl in XRR.
      etrans. apply (! XRR). clear XRR.
      apply pathsinv0, inv_iso_unique'.
      simpl. cbn. unfold precomp_with.
      rewrite id_right. apply XR.
Defined.
  
Lemma right_adj_equiv_is_ess_sur : essentially_surjective G.
Proof.
  intro d.
  apply hinhpr.
  exists (F d).
  exact (ηinv d).
Defined.

End about_equivalences.


Section eqv_comp.

Context {A B C : precategory}
        {hsA : has_homsets A}
        {hsB : has_homsets B}
        {hsC : has_homsets C}
        {F : functor A B}
        {F' : functor B C}.

Section adj_comp.

Hypothesis adF : is_left_adjoint F.
Hypothesis adF' : is_left_adjoint F'.

Let η : functor_precategory _ _ hsA ⟦ _ , _ ⟧ := unit_from_left_adjoint adF.
Let η' : functor_precategory _ _  hsB ⟦ _ , _ ⟧ := unit_from_left_adjoint adF'.
Let ε : functor_precategory _ _ hsB ⟦ _ , _ ⟧ := counit_from_left_adjoint adF.
Let ε' : functor_precategory _ _ hsC ⟦ _ , _ ⟧ := counit_from_left_adjoint adF'.
Let G := right_adjoint adF.
Let G' := right_adjoint adF'.

Definition unit_comp : (functor_precategory A A hsA) 
   ⟦ functor_identity A,
     functor_composite (functor_composite F F') (functor_composite G' G) ⟧
:=
    let Fη' := # (pre_composition_functor _ _ _ hsB hsB F) η' in
    let Fη'G := # (post_composition_functor _ _ _ _ hsA G) Fη' in
  (η ;; Fη'G).


Definition counit_comp : (functor_precategory C C hsC) 
    ⟦functor_composite (functor_composite G' G) (functor_composite F F'), 
     functor_identity C⟧
:= 
    let G'ε := # (pre_composition_functor _ _ _ hsB hsB G') ε in
    let G'εF' := # (post_composition_functor _ _ _ _ hsC F') G'ε in 
  (G'εF' ;; ε').

Lemma form_adjunction_comp
  : form_adjunction
      (functor_composite F F') (functor_composite G' G)
      unit_comp counit_comp.
Proof.
  mkpair; cbn in *; simpl in *.
  (* The proof of each triangle identity roughly goes as follows:
     - overall, we have a composite of four arrows;
     - apply naturality to pull the middle two past each other;
     - use the triangle identity from one adjunction to collapse the first pair, and from the other adjunction to collapse the second pair.

    Everything else consists of associativity, functoriality, etc. in order to get to these key steps.

    Written more algebraically, and suppressing associavity, the proof of the first identity is:

      F' F ( η ;; (G η' F) ) ) ;; (F' ε G' F' F) ;; (ε' F' F)
    =   (functoriality)
      F' ( F (η ;; (G η' F) ) ;; (ε G' F' F) ) ;; (ε' F' F)
    =   (functoriality)
      F' ( F η ;; F G η' F ;; ε G' F' F ) ;; (ε' F' F)
    =   (naturality)
      F' ( F η ;; ε F ;; η' F ) ;; (ε' F' F)
    =   (triangle identity for first adjunction)
      F' ( 1 F ;; η' F ) ;; (ε' F' F)
    =   (id_left, distributing over postcomposition)
      (F' η' ;; ε' F') F
    =   (triangle identity of second adjunction)
      1 F' F

    The second is completely dual: the same steps in the same order, only with pre- and post-composition switched.
*)
  - intro a.
    assert (T1 := triangle_id_left_ad  (pr2 adF) a).
    assert (T1' := triangle_id_left_ad (pr2 adF') (F a)).
    (* Burrow in to get to the naturality. *)
    etrans.
    + etrans. apply assoc.
      apply maponpaths_2.
      etrans. apply @pathsinv0, functor_comp.
      apply maponpaths.
      etrans. apply maponpaths_2, functor_comp.
      etrans. apply @pathsinv0, assoc.
      apply maponpaths, (nat_trans_ax ε).
    (* Now apply T1 from each of the original adjunctions. *)
    + cbn. etrans.
      * apply maponpaths_2, maponpaths.
        etrans. apply assoc.
        etrans. apply maponpaths_2, T1.
        apply id_left.
      * apply T1'.
  - intro c.
    assert (T2 := triangle_id_right_ad (pr2 adF) (G' c)).
    assert (T2' := triangle_id_right_ad (pr2 adF') c).
    (* Burrow in to get to the naturality. *)
    etrans.
    + etrans. apply @pathsinv0, assoc.
      apply maponpaths.
      etrans. apply @pathsinv0, functor_comp.
      apply maponpaths.
      etrans. apply maponpaths, functor_comp.
      etrans. apply assoc.
      apply maponpaths_2, @pathsinv0, (nat_trans_ax η').
    (* Now apply T2 from each of the original adjunctions. *)
    + cbn. etrans.
      * apply maponpaths, maponpaths.
        etrans. apply @pathsinv0, assoc.
        etrans. apply maponpaths, T2'.
        apply id_right.
      * apply T2.
Qed.

Definition comp_adjunction : is_left_adjoint (functor_composite F F').
Proof.
  exists (functor_composite G' G).
  exists (unit_comp ,, counit_comp).
  apply form_adjunction_comp.
Defined.

End adj_comp.

Hypothesis HF : adj_equivalence_of_precats F.
Hypothesis HF' : adj_equivalence_of_precats F'.



Definition comp_adj_equivalence_of_precats 
  : adj_equivalence_of_precats (functor_composite F F').
Proof.
  exists (comp_adjunction HF HF').
  mkpair.
  - intro. apply is_iso_comp_is_iso.
    + apply (pr1 (pr2 HF)).
    + simpl. apply functor_is_iso_is_iso, (pr1 (pr2 HF')).
  - intro. apply is_iso_comp_is_iso.
    + apply functor_is_iso_is_iso, (pr2 (pr2 HF)).
    + apply (pr2 (pr2 HF')).
Defined.

End eqv_comp.

Section eqv_inv.

Context {A B : precategory}
        {hsA : has_homsets A}
        {hsB : has_homsets B}
        {F : functor A B}.

Hypothesis adEquivF : adj_equivalence_of_precats F.

Let η : functor_precategory _ _ hsA ⟦ _ , _ ⟧ := unit_from_left_adjoint adEquivF.
Let ε : functor_precategory _ _ hsB ⟦ _ , _ ⟧ := counit_from_left_adjoint adEquivF.
Let G := right_adjoint adEquivF.

Let ηiso := unit_iso_from_adj_equivalence_of_precats hsA adEquivF.
Let εiso := counit_iso_from_adj_equivalence_of_precats hsB adEquivF.


Lemma form_adjunction_inv : 
 form_adjunction G F (inv_from_iso εiso) (inv_from_iso ηiso).
Proof.
  split.
  - intro b.
    apply (pre_comp_with_iso_is_inj _ _ _ _ (#G ((pr1 εiso : nat_trans _ _ )  b))).
    + apply (functor_is_iso_is_iso G). 
      apply is_functor_iso_pointwise_if_iso. apply pr2.
    + etrans. apply assoc.
      etrans. apply maponpaths_2. eapply pathsinv0. apply functor_comp.
      etrans. apply maponpaths_2. apply maponpaths.
              apply (nat_trans_eq_pointwise (iso_inv_after_iso εiso)).
      etrans. apply maponpaths_2. apply functor_id.
      etrans. apply id_left.
      apply (pre_comp_with_iso_is_inj _ _ _ _ (((pr1 ηiso : nat_trans _ _ ) (G b)))).
      * apply is_functor_iso_pointwise_if_iso. apply pr2.
      * etrans. apply (nat_trans_eq_pointwise (iso_inv_after_iso ηiso)).
        apply pathsinv0. 
        etrans. apply assoc.
        etrans. apply id_right.
        assert (XR := triangle_id_right_ad (pr2 (pr1 adEquivF))).
        apply XR.
  - intro a.
    apply (pre_comp_with_iso_is_inj _ _ _ _ (((pr1 εiso : nat_trans _ _ ) _))).
    * apply is_functor_iso_pointwise_if_iso. apply pr2.
    * etrans. apply assoc.
      etrans. apply maponpaths_2.
        apply (nat_trans_eq_pointwise (iso_inv_after_iso εiso)).
      etrans. apply id_left.
      apply (pre_comp_with_iso_is_inj _ _ _ _ (#F ((pr1 ηiso : nat_trans _ _ ) a))).
      { apply (functor_is_iso_is_iso F). 
        apply is_functor_iso_pointwise_if_iso. apply pr2.
      }
      etrans. eapply pathsinv0. apply functor_comp.
      etrans. apply maponpaths. apply (nat_trans_eq_pointwise (iso_inv_after_iso ηiso )).
      etrans. apply functor_id.
      apply pathsinv0.
      rewrite id_right.
      apply triangle_id_left_ad.
Qed.    


Definition is_left_adjoint_inv : is_left_adjoint G.
Proof.
  mkpair.
  - apply F.
  - mkpair.
    exists (pr1 (iso_inv_from_iso εiso)).
    exact (pr1 (iso_inv_from_iso ηiso)).
    apply form_adjunction_inv.
Defined.

Definition adj_equivalence_of_precats_inv 
  : adj_equivalence_of_precats G.
Proof.
  exists is_left_adjoint_inv.
  split.
  - intro b.
    apply (is_functor_iso_pointwise_if_iso _ _ hsB _ _  
                        (iso_inv_from_iso εiso) (pr2 (iso_inv_from_iso εiso))). 
  - intro a.
    apply (is_functor_iso_pointwise_if_iso _ _ hsA _ _  
                        (iso_inv_from_iso ηiso) (pr2 (iso_inv_from_iso ηiso))). 
Defined.
  
End eqv_inv.

Section eqv_from_ess_split_and_ff.

Definition split_ess_surj {A B : precategory}
  (F : functor A B) 
  := ∏ b : B, ∑ a : A, iso (F a) b.

Context {A B : precategory}
        {hsA : has_homsets A}
        {hsB : has_homsets B}
        {F : functor A B}
        (Fff : fully_faithful F)
        (Fses : split_ess_surj F).

Let Fweq {a b} f := (weq_from_fully_faithful Fff a b f).
Let Finv {a b} g := (invweq (weq_from_fully_faithful Fff a b) g).

Definition G_ff_split_data : functor_data B A.
Proof.
  mkpair.
  - intro b. exact (pr1 (Fses b)).
  - intros b b' f'; cbn.
    apply Finv.
    exact (pr2 (Fses b) ;; f' ;; inv_from_iso (pr2 (Fses b'))).
Defined.

Definition G_ff_split_ax : is_functor G_ff_split_data.
Proof.
  split.
  - intro b. cbn. rewrite id_right. simpl.
    apply invmap_eq. cbn.
    etrans. apply iso_inv_after_iso.
    apply pathsinv0, functor_id.
  - intros b b1 b2 f g.
    apply invmap_eq; cbn.
    rewrite functor_comp.
    apply pathsinv0.
    etrans. apply maponpaths.
       apply (homotweqinvweq (weqpair _ (Fff _ _ ))).
    etrans. apply maponpaths_2.
       apply (homotweqinvweq (weqpair _ (Fff _ _ ))).
    repeat rewrite <- assoc. apply maponpaths. apply maponpaths.
    repeat rewrite assoc. apply maponpaths_2.
    etrans. apply maponpaths_2.  apply iso_after_iso_inv.
    apply id_left.
Qed.

Definition G_ff_split : functor _ _ := ( _ ,, G_ff_split_ax).


Definition is_nat_trans_ε_ff_split : 
 is_nat_trans (functor_composite_data G_ff_split_data F)
    (functor_identity_data B) (λ b : B, pr2 (Fses b)).
Proof.
  intros b b' g;
  etrans; [ apply maponpaths_2 ; use homotweqinvweq |];
  repeat rewrite <- assoc; 
  apply maponpaths;
  rewrite iso_after_iso_inv;
  apply id_right.
Qed.

Definition ε_ff_split
  : nat_trans (functor_composite G_ff_split F) (functor_identity B).
Proof.
  mkpair.
  - intro b.
    exact (pr2 (Fses b)).
  - apply is_nat_trans_ε_ff_split.
Defined.

Lemma is_nat_trans_η_ff_split : 
 is_nat_trans (functor_identity_data A)
    (functor_composite_data F G_ff_split_data)
    (λ a : A, Finv (inv_from_iso (pr2 (Fses (F ((functor_identity A) a)))))).
Proof.
  intros a a' f;
  apply (invmaponpathsweq (weqpair _ (Fff _ _ )));
  cbn;
  rewrite functor_comp;
  rewrite functor_comp;
  etrans; [ apply maponpaths; use homotweqinvweq |];
  apply pathsinv0;
  etrans; [ apply maponpaths; use homotweqinvweq |];
  etrans; [ apply maponpaths_2; use homotweqinvweq |];
  repeat rewrite assoc;
  rewrite iso_after_iso_inv;
  rewrite id_left ;
  apply idpath.
Qed.


Definition η_ff_split : nat_trans (functor_identity A) (functor_composite F G_ff_split).
Proof.
  mkpair.
  -  intro a.
     apply Finv.
     apply (inv_from_iso (pr2 (Fses _ ))).
  - apply is_nat_trans_η_ff_split. 
Defined.
    
Lemma form_adjunction_ff_split 
  : form_adjunction F G_ff_split η_ff_split ε_ff_split.
  simpl. split.
  * intro a.
    cbn. 
    etrans. apply maponpaths_2. use homotweqinvweq. 
    apply iso_after_iso_inv.
  * intro b.
    cbn. 
    apply (invmaponpathsweq (weqpair _ (Fff _ _ ))).
    cbn.
    rewrite functor_comp.
    rewrite functor_id.
    etrans. apply maponpaths. use homotweqinvweq.
    etrans. apply maponpaths_2. use homotweqinvweq.
    repeat rewrite assoc.
    rewrite iso_after_iso_inv.
    rewrite id_left.
    apply iso_inv_after_iso.
Qed.

Definition adj_equivalence_of_precats_ff_split : adj_equivalence_of_precats F.
Proof.
  mkpair.
  - exists G_ff_split.
    mkpair.
    + exists η_ff_split. 
      exact ε_ff_split. 
    + apply form_adjunction_ff_split. 
  - split; cbn.
    + intro a. 
      use (fully_faithful_reflects_iso_proof _ _ _ Fff _ _ (isopair _ _ )).
      apply is_iso_inv_from_iso. 
    + intro b. apply pr2.
Defined.

End eqv_from_ess_split_and_ff.

(** ** Properties of functors *)

Definition split_full {C D : precategory} (F : functor C D) : UU
  := ∏ c c' (f : F c --> F c'), hfiber (#F) f.

Lemma full_from_split_full {C D : precategory} (F : functor C D)
  : split_full F -> full F.
Proof.
  intros H c c' f.
  apply hinhpr, H.
Qed.

Lemma split_full_from_ff {C D : precategory} (F : functor C D)
  : fully_faithful F -> split_full F.
Proof.
  intros H c c' f.
  exists (fully_faithful_inv_hom H c c' f).
  apply (homotweqinvweq (weq_from_fully_faithful _ _ _)).
Qed.

Lemma full_from_ff
  {D D' : precategory} (F : functor D D')
  : fully_faithful F -> full F.
Proof.
  intros. apply full_from_split_full, split_full_from_ff; assumption.
Qed.

Lemma right_adj_equiv_is_full {D1 D2 : precategory}
  (F : functor D1 D2) (GG : adj_equivalence_of_precats F)
  : full (right_adjoint GG).
Proof.
  apply full_from_ff, right_adj_equiv_is_ff.
Qed.

(** ** Misc lemmas/definitions on (pre)categories *)

(* Access function for [is_category] of categories.
  TODO: check naming is consistent with other similar access functions. *)
Definition category_is_category (C : category) : is_category C
  := pr2 C.
Coercion category_is_category : category >-> is_category.

(* TODO: raise issue in [CategoryTheory.precategories]: delete [category_has_homsets], since now redundant with [homset_property], since [category] coerces to [Precategory]. *)

(* TODO: raise issue: should the [HSET] provided be this by default, and current [HSET] be renamed to [HSET_precategory]? *)
Definition HSET_category : category.
Proof.
  exists HSET; split.
  - apply is_category_HSET.
  - apply has_homsets_HSET.
Defined.

Definition functor_category (C : precategory) (D : category)
  : category.
Proof.
  exists (functor_precategory C D (homset_property D)); split.
  - apply is_category_functor_category.
  - apply functor_category_has_homsets.
Defined.

Definition preShv C := functor_category C^op HSET_category.

Notation "'Yo'" := (yoneda _ (homset_property _) : functor _ (preShv _)).
Notation "'Yo^-1'" := (invweq (weqpair _ (yoneda_fully_faithful _ (homset_property _) _ _ ))).

(* TODO: perhaps rename e.g. [yoneda_eq]? *)
Definition yy {C : precategory} {hsC : has_homsets C}
  {F : preShv C} {c : C} : ((F : functor _ _) c : hSet) ≃ _ ⟦ yoneda _ hsC c, F⟧.
Proof.
  apply invweq.
  apply yoneda_weq.
Defined.

Arguments yy {_ _ _ _}.

Lemma yy_natural {C : precategory} {hsC : has_homsets C}
  (F : preShv C) (c : C) (A : (F:functor _ _) c : hSet) 
                  c' (f : C⟦c', c⟧) :
        yy (# (F : functor _ _) f A) = # (yoneda _ hsC) f ;; yy A.
Proof.
  assert (XTT := is_natural_yoneda_iso_inv _ hsC F _ _ f).
  apply (toforallpaths _ _ _ XTT).
Qed.

Lemma yy_comp_nat_trans {C : precategory} {hsC : has_homsets C}
      (F F' : preShv C) (p : _ ⟦F, F'⟧)
      A (v : (F : functor _ _ ) A : hSet)
  : yy (hsC:=hsC) v ;; p = yy ((p : nat_trans _ _ )  _ v).
Proof.
  apply nat_trans_eq.
  - apply has_homsets_HSET.
  - intro c. simpl. 
    apply funextsec. intro f. cbn.
    assert (XR := toforallpaths _ _ _ (nat_trans_ax p _ _ f) v ).
    cbn in XR.
    apply XR.
Qed.

Lemma transportf_yy {C : precategory} {hsC : has_homsets C}
      (F : preShv C) (c c' : C) (A : (F : functor _ _ ) c : hSet)
      (e : c = c'):
  yy (transportf (fun d => (F : functor _ _ ) d : hSet) e A) = 
  transportf (fun d => preShv C ⟦ yoneda _ hsC d, F⟧) e (yy A).
Proof.
  induction e.
  apply idpath.
Defined.

Lemma forall_isotid (A : precategory) (a_is : is_category A) 
      (a a' : A) (P : iso a a' -> UU) :
  (∏ e, P (idtoiso e)) → ∏ i, P i.
Proof.
  intros H i.
  rewrite <- (idtoiso_isotoid _ a_is).
  apply H.
Defined.

Lemma transportf_isotoid_functor 
  (A X : precategory) (H : is_category A)
  (K : functor A X)
   (a a' : A) (p : iso a a') (b : X) (f : K a --> b) :
 transportf (fun a0 => K a0 --> b) (isotoid _ H p) f = #K (inv_from_iso p) ;; f.
Proof.
  rewrite functor_on_inv_from_iso. simpl. cbn.
  unfold precomp_with. rewrite id_right.
  generalize p.
  apply forall_isotid.
  - apply H.
  - intro e. induction e.
    cbn.
    rewrite functor_id.
    rewrite id_left.
    rewrite isotoid_identity_iso.
    apply idpath.
Defined.


Lemma idtoiso_transportf_family_of_morphisms (D : precategory)
      (A : UU) (B : A -> UU)
      (F : ∏ a, B a -> D)
      (d d' : D) (deq : d = d')
      (R : ∏ a (b : B a), D⟦ F a b, d⟧)
     
: transportf (λ x, ∏ a b, D⟦ F a b, x⟧) deq R 
  =
  λ a b, R a b ;; idtoiso deq.
Proof.
  destruct deq.
  apply funextsec.
  intro. apply funextsec. intro.
  apply pathsinv0.
  apply id_right.
Qed.


Lemma idtoiso_concat_pr (C : precategory) (a a' a'' : ob C)
  (p : a = a') (q : a' = a'') :
  idtoiso p ;; idtoiso q = idtoiso (p @ q).
Proof.
  apply pathsinv0.
  apply (base_paths _ _ (idtoiso_concat _ _ _ _ _ _ )).
Defined.

Lemma idtoiso_eq_idpath (C : precategory) (a : C) (e : a = a)
    (H : e = idpath _ )
  : identity a = idtoiso e.
Proof.
  rewrite H.
  apply idpath.
Qed.


Arguments cancel_postcomposition [C a b c] f f' g _ .

Lemma idtoiso_postcompose_idtoiso_pre {C : precategory} {a b c : C} 
      (g : a --> b) (f : a --> c)
      (p : b = c) 
  : g = f ;; idtoiso (!p) -> g ;; idtoiso p = f.
Proof.
  induction p. simpl.
  rewrite id_right.
  induction 1.
  apply id_right.
Qed.

(* Left-handed counterpart to [transportf_isotoid], which could be called [prewhisker_isotoid] analogously — neither of these is a fully general transport lemma, they’re about specific cases.

  TODO: look for dupes in library; move; consider naming conventions; rename D to C. *)
Lemma postwhisker_isotoid {D : precategory} (H : is_category D)
    {a b b' : D} (f : a --> b) (p : iso b b')
  : transportf (fun b0 => a --> b0) (isotoid _ H p) f
  = f ;; p.
Proof.
  rewrite <- idtoiso_postcompose.
  apply maponpaths, maponpaths, idtoiso_isotoid.
Qed.

Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).

Lemma inv_from_iso_iso_from_fully_faithful_reflection {C D : precategory}
      (F : functor C D) (HF : fully_faithful F) (a b : C) (i : iso (F a) (F b))
      : inv_from_iso
       (iso_from_fully_faithful_reflection HF i) = 
 iso_from_fully_faithful_reflection HF (iso_inv_from_iso i).
Proof.
  cbn.
  unfold precomp_with.
  apply id_right.
Defined.

Definition nat_iso_from_pointwise_iso (D E : precategory)
  (hsE : has_homsets E)
  (F G : [D, E, hsE])
  (a : ∏ d, iso ((F : functor _ _) d) ((G : functor _ _) d))
  (H : is_nat_trans _ _ a)
  : iso F G.
Proof.
  use functor_iso_from_pointwise_iso .
  mkpair.
  - intro d. apply a.
  - apply H.
  - intro d. apply (pr2 (a d)).
Defined.

Lemma iso_from_iso_with_postcomp (D E E' : precategory) hsE hsE'
  (F G : functor D E) (H : functor E E')
  (Hff : fully_faithful H) : 
  iso (C:=[D, E', hsE']) (functor_composite F H) (functor_composite G H)
  ->
  iso (C:=[D, E, hsE]) F G.
Proof.
  intro a.
  use nat_iso_from_pointwise_iso.
  - intro d. simpl.
    apply (iso_from_fully_faithful_reflection Hff).
    apply (functor_iso_pointwise_if_iso _ _ _ _ _ a (pr2 a)).
  - abstract (
    simpl; intros d d' f;
    assert (XR := nat_trans_ax (pr1 a : nat_trans _ _ ));
    simpl in XR;
    apply (invmaponpathsweq (weq_from_fully_faithful Hff _ _ ));
    simpl; rewrite functor_comp; rewrite functor_comp;
    assert (XTT:=homotweqinvweq (weq_from_fully_faithful Hff (F d') (G d')  ));
    simpl in *;
    etrans; [apply maponpaths; apply XTT |];
    clear XTT;
    assert (XTT:=homotweqinvweq (weq_from_fully_faithful Hff (F d) (G d)  ));
    simpl in *;
    etrans; [| apply cancel_postcomposition; apply (!XTT _ )];
    apply XR
    ).
Defined.


Definition functor_assoc_iso (D1 D2 D3 D4 : precategory) hsD4
     (F : functor D1 D2) (G : functor D2 D3) (H : functor D3 D4) :
    iso (C:=[D1,D4,hsD4])
         (functor_composite (functor_composite F G) H)
         (functor_composite F (functor_composite G H)).
Proof.
  use nat_iso_from_pointwise_iso.
  - intro d. apply identity_iso.
  - abstract (
        intros x x' f;
        rewrite id_left;
        rewrite id_right;
        apply idpath
     ).
Defined.

Definition functor_comp_id_iso (D1 D2 : precategory) hsD2
     (F : functor D1 D2) :
  iso (C:=[D1,D2,hsD2]) (functor_composite F (functor_identity _ )) F.
Proof.
  use nat_iso_from_pointwise_iso.
  - intro. apply identity_iso.
  - abstract (
       intros x x' f;
       rewrite id_left;
       rewrite id_right;
       apply idpath
    ).
Defined.

Definition functor_precomp_iso (D1 D2 D3 : precategory)  hsD3
    (F : functor D1 D2) (G H : functor D2 D3) :
    iso (C:=[D2,D3,hsD3]) G H ->
    iso (C:=[D1,D3,hsD3]) (functor_composite F G)
                          (functor_composite F H).
Proof.
  intro a.
  use nat_iso_from_pointwise_iso.
  - intro d. apply (functor_iso_pointwise_if_iso _ _ _ _ _ a (pr2 a)).
  - abstract (intros x x' f; apply (nat_trans_ax (pr1 a))).
Defined.


Definition adj_from_equiv (D1 D2 : precategory) (F : functor D1 D2):
    adj_equivalence_of_precats F → is_left_adjoint F := fun x => pr1 x.
Coercion adj_from_equiv : adj_equivalence_of_precats >-> is_left_adjoint.


(** ** Lemmas on pullbacks *)

Section Square_Transfers.

Definition commutes_and_is_pullback {C : precategory} {a b c d : C}
    (f : b --> a) (g : c --> a) (p1 : d --> b) (p2 : d --> c)
  : UU
:= ∑ (H : p1 ;; f = p2 ;; g), isPullback _ _ _ _ H.

(* Note: should have a dual version where [i_a], instead of [i_d], is assumed iso (and using [post_comp_with_iso_is_inj] in the proof). *)
Lemma commuting_square_transfer_iso {C : precategory}
      {a b c d : C}
      {f : b --> a} {g : c --> a} {p1 : d --> b} {p2 : d --> c}
      {a' b' c' d' : C}
      {f' : b' --> a'} {g' : c' --> a'} {p1' : d' --> b'} {p2' : d' --> c'}
      {i_a : a --> a'} {i_b : b --> b'} {i_c : c --> c'} {i_d : iso d d'}
      (i_f : f ;; i_a = i_b ;; f') (i_g : g ;; i_a = i_c ;; g')
      (i_p1 : p1 ;; i_b = i_d ;; p1') (i_p2 : p2 ;; i_c = i_d ;; p2')
   : p1 ;; f = p2;; g
   -> p1' ;; f' = p2' ;; g'.
Proof.
  intro H.
  refine (pre_comp_with_iso_is_inj _ _ _ _ i_d _ _ _ _).
  exact (pr2 i_d).  (* TODO: access function [is_iso_from_iso]? *)
  rewrite 2 assoc.
  rewrite <- i_p1, <- i_p2.
  rewrite <- 2 assoc.
  rewrite <- i_f, <- i_g.
  rewrite 2 assoc.
  apply maponpaths_2, H.
Qed.

(* Generalisation of [isPulback_iso_of_morphisms].  TODO: prove, move. *)
Lemma isPullback_transfer_iso {C : Precategory}
      {a b c d : C}
      {f : b --> a} {g : c --> a} {p1 : d --> b} {p2 : d --> c}
      (H : p1 ;; f = p2;; g)
      {a' b' c' d' : C}
      {f' : b' --> a'} {g' : c' --> a'} {p1' : d' --> b'} {p2' : d' --> c'}
      (H' : p1' ;; f' = p2' ;; g')
      {i_a : iso a a'} {i_b : iso b b'} {i_c : iso c c'} {i_d : iso d d'}
      (i_f : f ;; i_a = i_b ;; f') (i_g : g ;; i_a = i_c ;; g')
      (i_p1 : p1 ;; i_b = i_d ;; p1') (i_p2 : p2 ;; i_c = i_d ;; p2')
   : isPullback _ _ _ _ H
   -> isPullback _ _ _ _ H'.
Proof.
  intros Hpb.
  apply (mk_isPullback _ ).    
  intros X h k H''.
  simple refine (tpair _ _ _ ).
  - simple refine (tpair _ _ _ ).
    { refine ( _ ;; i_d ).
      simple refine (PullbackArrow (mk_Pullback _ _ _ _ _ _ Hpb) _ _ _ _).
      + exact (h ;; iso_inv_from_iso i_b).
      + exact (k ;; iso_inv_from_iso i_c).
      + abstract (
          apply (post_comp_with_iso_is_inj _ _ _ i_a (pr2 _));
            (* TODO: access function for isos! *)
          repeat rewrite <- assoc;
          rewrite i_f, i_g;
          eapply @pathscomp0;
          [ apply maponpaths; rewrite assoc;
            apply maponpaths_2, iso_after_iso_inv
          | eapply @pathsinv0, @pathscomp0;
          [ apply maponpaths; rewrite assoc;
            apply maponpaths_2, iso_after_iso_inv
          | rewrite 2 id_left; apply @pathsinv0, H''
          ]]
        ).
    }
    cbn; split;
    abstract (
      rewrite <- assoc;
      eapply @pathscomp0;
      [ apply maponpaths, @pathsinv0;
        try apply i_p2; try apply i_p1
      | rewrite assoc;
      eapply @pathscomp0;
      [ apply maponpaths_2;
        try apply (PullbackArrow_PullbackPr2 (mk_Pullback _ _ _ _ _ _ _));
        try apply (PullbackArrow_PullbackPr1 (mk_Pullback _ _ _ _ _ _ _))
      | rewrite <- assoc, iso_after_iso_inv; apply id_right]] ).
  - intros hk'.
    apply subtypeEquality.
      intro; apply isapropdirprod; apply homset_property.
    cbn.
    apply (post_comp_with_iso_is_inj _ _ _ (iso_inv_from_iso i_d) (pr2 _)).
    eapply @pathscomp0. Focus 2.
      rewrite <- assoc. cbn. rewrite iso_inv_after_iso. eapply pathsinv0, id_right.
    apply PullbackArrowUnique; cbn.
    + apply (post_comp_with_iso_is_inj _ _ _ i_b (pr2 _)).
      repeat rewrite <- assoc.
      rewrite i_p1, iso_after_iso_inv, id_right.
      eapply @pathscomp0.
        apply maponpaths. rewrite assoc, iso_after_iso_inv. apply id_left.
      apply (pr1 (pr2 hk')).
    + apply (post_comp_with_iso_is_inj _ _ _ i_c (pr2 _)).
      repeat rewrite <- assoc.
      rewrite i_p2, iso_after_iso_inv, id_right.
      eapply @pathscomp0.
        apply maponpaths. rewrite assoc, iso_after_iso_inv. apply id_left.
      apply (pr2 (pr2 hk')).
  Qed.

(* Generalisation of [isPulback_iso_of_morphisms].  TODO: prove, move. *)
Lemma commutes_and_is_pullback_transfer_iso {C : Precategory}
      {a b c d : C}
      {f : b --> a} {g : c --> a} {p1 : d --> b} {p2 : d --> c}
      {a' b' c' d' : C}
      {f' : b' --> a'} {g' : c' --> a'} {p1' : d' --> b'} {p2' : d' --> c'}
      {i_a : iso a a'} {i_b : iso b b'} {i_c : iso c c'} {i_d : iso d d'}
      (i_f : f ;; i_a = i_b ;; f') (i_g : g ;; i_a = i_c ;; g')
      (i_p1 : p1 ;; i_b = i_d ;; p1') (i_p2 : p2 ;; i_c = i_d ;; p2')
      (H : p1 ;; f = p2 ;; g) (P : isPullback _ _ _ _ H)
   : commutes_and_is_pullback f' g' p1' p2'.
Proof.
  exists (commuting_square_transfer_iso i_f i_g i_p1 i_p2 H).
  exact (isPullback_transfer_iso _ _ i_f i_g i_p1 i_p2 P).
Qed.

End Square_Transfers.

Section on_pullbacks.

  Variable C : precategory.
  Variable hs : has_homsets C.
  Variables a b c d : C.
  Variables (f : a --> b) (g : a --> c) (k : b --> d) (h : c --> d).

(**
<<
      f
   a----b
 g |    | k
   |    |
   c----d
     h 
>>
*)

  Variable sqr_comm : f ;; k = g ;; h.
  Variable Pb : isPullback k h f g sqr_comm.


  Lemma square_morphism_equal k' (e : k' = k) : f ;; k' = g ;; h.
  Proof.
    rewrite e. assumption.
  Defined.

  Lemma isPb_morphism_equal k' (e : k' = k) : 
        isPullback k' h f g (square_morphism_equal _ e).
  Proof.
    match goal with |[|- isPullback _ _ _ _ ?HH] => generalize HH end.
    rewrite e.
    intro.
    apply Pb.
  Defined.


  Local Definition Pbb : Pullback k h.
  Proof.
    unshelve refine (mk_Pullback _ _ _ _ _ _ _ ).
      - apply a.
      - apply f.
      - apply g.
      - apply sqr_comm.
      - apply Pb.
  Defined.
  
  Definition map_into_Pb {e : C} (x : e --> b) (y : e --> c)
  :  x ;; k = y ;; h → e --> a.
  Proof.
    intro H.
    unshelve refine (PullbackArrow Pbb _ _ _ _ ).
    - apply x.
    - apply y.
    - apply H.
  Defined.
      
  Definition Pb_map_commutes_1 {e : C} (x : e --> b) (y : e --> c) H
  : map_into_Pb x y H ;; f = x.
  Proof.
    assert (P:=PullbackArrow_PullbackPr1 Pbb).
    apply P.
  Qed.

  Definition Pb_map_commutes_2 {e : C} (x : e --> b) (y : e --> c) H
  : map_into_Pb x y H ;; g = y.
  Proof.
    assert (P:=PullbackArrow_PullbackPr2 Pbb).
    apply P.
  Qed.

  Lemma map_into_Pb_unique (e : C) (x y : e --> a)
  : x ;; f = y ;; f → x ;; g = y ;; g → x = y.
  Proof.
    intros H H'.
    set (T:=@map_into_Pb _ (x ;; f)(y ;; g)).
    assert  (TH : x ;; f ;; k = y ;; g ;; h).
    { rewrite H. repeat rewrite <- assoc. rewrite sqr_comm. apply idpath. }
    pathvia (T TH).
    apply PullbackArrowUnique. apply idpath. assumption.
    apply pathsinv0. apply PullbackArrowUnique. apply pathsinv0; assumption.
    apply idpath.
  Qed.

  Lemma postcomp_pb_with_iso (y : C) (r : y --> d) (i : iso b y) (Hi : i ;; r = k) :
    ∑ H : f ;; i ;; r = g ;; h, isPullback _ _ _ _ H.
  Proof.
    simple refine (@commutes_and_is_pullback_transfer_iso (C,,hs)
              _ _ _ _  _ _ _ _
              _ _ _ _  _ _ _ _
              _ _ _ _  _ _ _ _
              _ Pb);
    try apply identity_iso;
    try rewrite id_left;
    try rewrite id_right;
    try apply idpath.
    apply pathsinv0, Hi.
  Qed. 
 
End on_pullbacks.

Arguments map_into_Pb {_ _ _ _ _ _ _ _ _ } _ _ {_} _ _ _ .
Arguments map_into_Pb_unique {_ _ _ _ _ _ _ _ _} _ _ {_} _ _ _ _   .

Section Pullbacks_hSet.

(* TODO: does this already exist?

  If we had the standard pullback of hsets defined, this could be maybe better stated as the fact that P is a pullback if the map from P to the standard pullback is an iso. *)
Lemma isPullback_HSET {P A B C : HSET}
  (p1 : P --> A) (p2 : P --> B) (f : A --> C) (g : B --> C) (ep : p1 ;; f = p2 ;; g) 
  : (∏ a b (e : f a = g b), ∃! ab, p1 ab = a × p2 ab = b)
  -> isPullback _ _ _ _ ep.
Proof.
  intros H X h k ehk.
  set (H_existence := fun a b e => pr1 (H a b e)).
  set (H_uniqueness := fun a b e x x' => base_paths _ _ (proofirrelevancecontr (H a b e) x x')).
  apply iscontraprop1.
  - apply invproofirrelevance.
    intros hk hk'.
    apply subtypeEquality. { intro. apply isapropdirprod; apply setproperty. }
    destruct hk as [hk [eh ek]], hk' as [hk' [eh' ek']]; simpl.
    apply funextsec; intro x.
    refine (H_uniqueness (h x) (k x) _ (_,,_) (_,,_)).
    apply (toforallpaths _ _ _ ehk).
    split. apply (toforallpaths _ _ _ eh). apply (toforallpaths _ _ _ ek).
    split. apply (toforallpaths _ _ _ eh'). apply (toforallpaths _ _ _ ek').
  - mkpair. 
    + intros x. refine (pr1 (H_existence (h x) (k x) _)). apply (toforallpaths _ _ _ ehk).
    + simpl.
      split; apply funextsec; intro x.
      apply (pr1 (pr2 (H_existence _ _ _))). apply (pr2 (pr2 (H_existence _ _ _))).
Qed.


(* TODO: unify with [isPullback_HSET]? *)
Lemma pullback_HSET_univprop_elements {P A B C : HSET}
    {p1 : HSET ⟦ P, A ⟧} {p2 : HSET ⟦ P, B ⟧}
    {f : HSET ⟦ A, C ⟧} {g : HSET ⟦ B, C ⟧}
    (ep : p1 ;; f = p2 ;; g)
    (pb : isPullback f g p1 p2 ep)
  : (∏ a b (e : f a = g b), ∃! ab, p1 ab = a × p2 ab = b).
Proof.
  intros a b e.
  set (Pb := (mk_Pullback _ _ _ _ _ _ pb)).
  apply iscontraprop1.
  - apply invproofirrelevance; intros [ab [ea eb]] [ab' [ea' eb']].
    apply subtypeEquality; simpl.
      intros x; apply isapropdirprod; apply setproperty.
    refine (@toforallpaths unitset _ (fun _ => ab) (fun _ => ab') _ tt).
    refine (MorphismsIntoPullbackEqual pb _ _ _ _ );
    apply funextsec; intros []; cbn;
    (eapply @pathscomp0; [ eassumption | apply pathsinv0; eassumption]).
  - simple refine (_,,_).
    refine (_ tt).
    refine (PullbackArrow Pb (unitset : HSET)
      (fun _ => a) (fun _ => b) _).
    apply funextsec; intro; exact e.
    simpl; split.
    + generalize tt; apply toforallpaths.
      apply (PullbackArrow_PullbackPr1 Pb unitset).
    + generalize tt; apply toforallpaths.
      apply (PullbackArrow_PullbackPr2 Pb unitset).
Defined.

Lemma pullback_HSET_elements_unique {P A B C : HSET}
    {p1 : HSET ⟦ P, A ⟧} {p2 : HSET ⟦ P, B ⟧}
    {f : HSET ⟦ A, C ⟧} {g : HSET ⟦ B, C ⟧}
    {ep : p1 ;; f = p2 ;; g}
    (pb : isPullback f g p1 p2 ep)
    (ab ab' : P : hSet)
    (e1 : p1 ab = p1 ab') (e2 : p2 ab = p2 ab')
  : ab = ab'.
Proof.
  set (temp := proofirrelevancecontr 
    (pullback_HSET_univprop_elements _ pb (p1 ab') (p2 ab')
        (toforallpaths _ _ _ ep ab'))).
  refine (maponpaths pr1 (temp (ab,, _) (ab',, _))).
  - split; assumption.
  - split; apply idpath.
Qed.


(* TODO: upstream this and the following lemma, and unify them with the converse implication about pullbacks. *)
Lemma square_commutes_preShv_to_pointwise {C : precategory} (hsC : has_homsets C)
    {X Y Z W : preShv C}
    {f : Y --> X} {g : Z --> X} {p1 : W --> Y} {p2 : W --> Z}
    (e : p1 ;; f = p2 ;; g)
    (c : C)
  : ((p1 : nat_trans _ _) c) ;; ((f : nat_trans _ _) c)
  = ((p2 : nat_trans _ _) c) ;; ((g : nat_trans _ _) c).
Proof.
  apply (nat_trans_eq_pointwise e).
Qed.

(* TODO: unify with the converse implication. *)
Lemma isPullback_preShv_to_pointwise {C : precategory} (hsC : has_homsets C)
    {X Y Z W : preShv C}
    {f : Y --> X} {g : Z --> X} {p1 : W --> Y} {p2 : W --> Z}
    {e : p1 ;; f = p2 ;; g} (pb : isPullback _ _ _ _ e)
    (c : C)
  : isPullback ((f : nat_trans _ _) c) ((g : nat_trans _ _) c)
      ((p1 : nat_trans _ _) c) ((p2 : nat_trans _ _) c)
      (square_commutes_preShv_to_pointwise hsC e c).
Proof.
  set (XR := @isLimFunctor_is_pointwise_Lim C^op HSET has_homsets_HSET
            pushout_graph).
  set (XT1 := pullback_diagram _ f g).
  specialize (XR XT1).
  transparent assert
       (XH : (∏ a : C^op,
        LimCone
          (@colimits.diagram_pointwise C^op HSET has_homsets_HSET
             pushout_graph XT1 a))).
    { intro. apply LimConeHSET.  }
    specialize (XR XH).
    specialize (XR W). 
    set (XT := PullbCone _ _ _ _ p1 p2 e).
    specialize (XR XT).
    transparent assert (XTT : (isLimCone XT1 W XT)).
    { apply @equiv_isPullback_1.
      apply functor_category_has_homsets.
      assumption.
    }
    specialize (XR XTT c).    
    intros S h k H.
    specialize (XR S).
    simpl in XR.
    transparent assert (
        HC :  (cone
              (@colimits.diagram_pointwise C^op HSET has_homsets_HSET
                                               pushout_graph (pullback_diagram (preShv C) f g) c) S)).
    { use mk_cone.
      apply three_rec_dep; cbn.
      - apply h.
      - simpl. apply (h ;; (pr1 f c)).
      - apply k.
      - use three_rec_dep; use three_rec_dep.
        + exact (Empty_set_rect _ ).
        + intro. apply idpath.
        + exact (Empty_set_rect _ ).
        + exact (Empty_set_rect _ ).
        + exact (Empty_set_rect _ ).
        + exact (Empty_set_rect _ ).
        + exact (Empty_set_rect _ ).
        + intro; apply (!H).
        + exact (Empty_set_rect _ ).
    }
    specialize (XR HC).
    mkpair.
  - exists (pr1 (iscontrpr1 XR)).
    split.
    + apply (pr2 (pr1 XR) One).
    + apply (pr2 (pr1 XR) Three).
  - intro t.
    apply subtypeEquality.
    + intro. apply isapropdirprod; apply has_homsets_HSET.
    + simpl.
      apply path_to_ctr.
      destruct t as [t [H1 H2]].
      use three_rec_dep.
      * apply H1.
      * destruct H1.
        apply idpath.
      * apply H2.
Qed.


End Pullbacks_hSet.

(**
will be an instance of a general lemma to be proved
   in UniMath
*)
Definition isaprop_Pullback (C : precategory) (H : is_category C)
           (a b c : C) (f : b --> a) (g : c --> a)
: isaprop (Pullback f g).
Proof.
  unfold Pullback.
  apply invproofirrelevance.
  unfold Pullback.
  intros Pb Pb'.
  apply subtypeEquality.
  - intro; apply isofhleveltotal2.
    + destruct H as [H1 H2]. apply H2.
    + intros; apply isaprop_isPullback.
  - apply (total2_paths_f (isotoid _ H (iso_from_Pullback_to_Pullback Pb Pb' ))). 
    rewrite transportf_dirprod, transportf_isotoid.
    rewrite inv_from_iso_iso_from_Pullback.
    rewrite transportf_isotoid.
    rewrite inv_from_iso_iso_from_Pullback.
    destruct Pb as [Cone bla];
    destruct Pb' as [Cone' bla'];
    simpl in *.
    destruct Cone as [p [h k]];
    destruct Cone' as [p' [h' k']];
    simpl in *. 
    unfold from_Pullback_to_Pullback;
    rewrite PullbackArrow_PullbackPr2, PullbackArrow_PullbackPr1.
    apply idpath.
Qed.



Section Pullback_Unique_Up_To_Iso.

(*   a'   b'
      f  /h
   a----b  b'
   |    |
 g |    | k
   |    |
   c----d
     j 

   and pb square a' b' c d, and h iso
    
   task: construct iso from a to a'

 *)
  
  Variable CC : precategory.
  Variables A B C D A' B' : CC.
  Variables (f : A --> B) (g : A --> C) (k : B --> D) (j : C --> D) (H : f ;; k = g ;; j)
            (pb : isPullback _ _ _ _ H).
  Variables (f' : A' --> B') (g' : A' --> C) (r : B' --> D) (h : iso B B').
  Variable (H' : f' ;; r = g' ;; j).
  Variable (pb' : isPullback _ _ _ _ H').
  Variable (T : h ;; r = k).

  Definition map_to_2nd_pb : A --> A'.
  Proof.
    unshelve refine (map_into_Pb H' pb' _ _ _  ).
    - exact (f ;; h).
    - exact g.
    - eapply pathscomp0. Focus 2. apply H.
      eapply pathscomp0. apply (!assoc _ _ _ ).
      apply maponpaths. apply T.
  Defined.

  Definition map_to_1st_pb : A' --> A.
  Proof.
    unshelve refine (map_into_Pb H pb _ _ _ ).
    - exact (f';; inv_from_iso h).
    - exact g'.
    - eapply pathscomp0; [| apply H'].
      eapply pathscomp0; [ apply (!assoc _ _ _ ) |].
      apply maponpaths. apply iso_inv_on_right.
      apply (!T).
  Defined.

  Lemma inv1 : map_to_2nd_pb ;; map_to_1st_pb = identity _ .
  Proof.
    apply (map_into_Pb_unique  H pb).
    - rewrite id_left.
      rewrite <- assoc.
      unfold map_to_1st_pb.
      rewrite Pb_map_commutes_1.
      rewrite assoc.
      apply pathsinv0.
      apply iso_inv_on_left.
      unfold map_to_2nd_pb.
      match goal with |[ |- map_into_Pb ?H1 ?pb1 ?x1 ?y1 ?R1 ;; _ = _ ] => assert
           (T1:=@Pb_map_commutes_1 _ _ _ _ _ _ _ _ _ H' pb' _ x1 y1 R1) end.
      apply T1.
    - rewrite id_left.
      rewrite <- assoc.
      unfold map_to_1st_pb.
      rewrite Pb_map_commutes_2.
      unfold map_to_2nd_pb.
      apply Pb_map_commutes_2.
  Qed.

  Lemma inv2 : map_to_1st_pb ;; map_to_2nd_pb = identity _ .
  Proof.
    apply (map_into_Pb_unique  H' pb').
    - rewrite id_left.
      rewrite <- assoc.
      unfold map_to_2nd_pb.
      rewrite Pb_map_commutes_1.
      rewrite assoc.
      unfold map_to_1st_pb.
      rewrite Pb_map_commutes_1.
      rewrite <- assoc.
      rewrite iso_after_iso_inv.
      apply id_right.
    - rewrite id_left.
      rewrite <- assoc.
      unfold map_to_2nd_pb.
      rewrite Pb_map_commutes_2.
      unfold map_to_1st_pb.
      apply Pb_map_commutes_2.
  Qed.

  Definition iso_to_second_pb : iso A A'.
  Proof.
    exists map_to_2nd_pb.
    simple refine (is_iso_qinv _ map_to_1st_pb _ ).
    split.
    - apply inv1.
    - apply inv2.
  Defined.

End Pullback_Unique_Up_To_Iso.

Arguments map_into_Pb {_ _ _ _ _} _ _ _ _ _ _ {_} _ _ _ .
Arguments Pb_map_commutes_1 {_ _ _ _ _} _ _ _ _ _ _ {_} _ _ _ .
Arguments Pb_map_commutes_2 {_ _ _ _ _} _ _ _ _ _ _ {_} _ _ _ .


(** * Unorganised lemmas *)

(* Lemmas that probably belong in one of the sections above, but haven’t been sorted into them yet.  Mainly a temporary holding pen for lemmas being upstreamed from other files. TODO: empty this bin frequently (but keep it here for re-use). *) 
Section Unorganised.

End Unorganised.
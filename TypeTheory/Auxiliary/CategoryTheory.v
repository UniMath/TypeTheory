

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.All.
(* a few libraries need to be reloaded after “All”,
   to claim precedence on overloaded names *)
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.pullbacks.
Require Import UniMath.CategoryTheory.limits.pullbacks.

Require Import TypeTheory.Auxiliary.Auxiliary.


(** * General notations and scopes *)

(** We redeclare this notation, along with a new scope . *)
Notation "ff ;; gg" := (compose ff gg)
  (at level 50, left associativity, format "ff  ;;  gg")
  : mor_scope.
Delimit Scope mor_scope with mor.
Bind Scope mor_scope with precategory_morphisms.
Open Scope mor_scope.

Declare Scope precat.
Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op") : precat.
Delimit Scope precat with precat.

Open Scope cat.
Open Scope cat_deprecated.

(** * Isomorphism lemmas *)

Arguments functor_on_inv_from_iso {_ _} _  {_ _} f.

Lemma is_iso_comp_is_iso {C : precategory} {a b c : ob C}
  (f : C⟦a, b⟧) (g : C⟦b, c⟧) 
  : is_iso f -> is_iso g -> is_iso (f ;; g).
Proof.
  intros Hf Hg.
  apply (is_iso_comp_of_isos (make_iso f Hf) (make_iso g Hg)).
Defined.

(* TODO: check more thoroughly if this is provided in the library; if so, use the library version, otherwise move this upstream.  Cf. also https://github.com/UniMath/UniMath/issues/279 *)
Lemma inv_from_iso_from_is_z_iso {D: precategory} {a b : D}
  (f: a --> b) (g : b --> a) (H : is_inverse_in_precat f g)
: inv_from_iso (f ,, (is_iso_from_is_z_iso _ (g ,, H))) 
  = g.
Proof.
  cbn. apply id_right.
Qed.

(** * Idtoiso and isotoid *)

Lemma idtoiso_identity_iso {C : precategory} (a : C)
  : idtoiso (idpath a) = identity_iso a.
Proof.
  apply idpath.
Defined.

Lemma idtoiso_identity {C : precategory} (a : C)
  : (idtoiso (idpath a) : _ --> _) = identity a.
Proof.
  apply idpath.
Defined.

Lemma forall_isotid (A : category) (a_is : is_univalent A) 
      (a a' : A) (P : iso a a' -> UU) :
  (∏ e, P (idtoiso e)) → ∏ i, P i.
Proof.
  intros H i.
  rewrite <- (idtoiso_isotoid _ a_is).
  apply H.
Defined.

Lemma transportf_isotoid_functor 
  (A X : category) (H : is_univalent A)
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
  (idtoiso (p @ q) : _ --> _) = idtoiso p ;; idtoiso q.
Proof.
  apply (base_paths _ _ (idtoiso_concat _ _ _ _ _ _ )).
Defined.

Lemma idtoiso_eq_idpath (C : precategory) (a : C) (e : a = a)
    (H : e = idpath _ )
  : (idtoiso e : _ --> _) = identity_iso _.
Proof.
  apply maponpaths, (maponpaths idtoiso H).
Qed.

Lemma idtoiso_precompose'
  : ∏ (C : precategory) (a a' b : C) (p : a' = a) (f : C ⟦ a, b ⟧),
    transportb (λ a0 : C, C ⟦ a0, b ⟧) p f = (idtoiso p;; f)%mor.
Proof.
  intros; induction p. apply pathsinv0, id_left.
Defined.

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
Lemma postwhisker_isotoid {D : category} (H : is_univalent D)
    {a b b' : D} (f : a --> b) (p : iso b b')
  : transportf (fun b0 => a --> b0) (isotoid _ H p) f
  = f ;; p.
Proof.
  rewrite <- idtoiso_postcompose.
  apply maponpaths, maponpaths, idtoiso_isotoid.
Qed.

(** * Constant functors *)

Definition constant_functor_functor_data {C1 C2 : category}
  : functor_data C2 [C1,C2].
Proof.
  use tpair.
  - apply constant_functor.
  - simpl. apply constant_nat_trans.
Defined.

Definition constant_functor_functor_is_functor (C1 C2 : category)
  : is_functor (@constant_functor_functor_data C1 C2).
Proof.
  split.
  - intro. apply nat_trans_eq. { apply homset_property. }
    intro; apply idpath.
  - intros ? ? ? ? ?. apply nat_trans_eq. { apply homset_property. }
    intro; apply idpath.
Qed.

Definition constant_functor_functor {C1 C2 : category}
  : [C2,[C1,C2]]
:= make_functor _ (constant_functor_functor_is_functor C1 C2).

Lemma constant_nat_trans_is_iso
    {C1 C2 : category} {x y : C2} (f : x --> y )
  : is_iso f -> @is_iso [C1,C2] _ _ (constant_nat_trans C1 f).
Proof.
  intro f_iso. use functor_iso_if_pointwise_iso.
  intro; apply f_iso.
Defined.

Lemma constant_nat_iso
    {C1 C2 : category} {x y : C2} (f : iso x y )
  : @iso [C1,C2] (constant_functor C1 _ x) (constant_functor C1 _ y).
Proof.
  exists (constant_nat_trans _ f).
  apply constant_nat_trans_is_iso, iso_is_iso.
Defined.

Definition nat_trans_from_nat_iso
    {C D : category} {F G : functor C D} (α : nat_iso F G)
  : nat_trans F G
:= pr1 α.
Coercion nat_trans_from_nat_iso : nat_iso >-> nat_trans.

(** * Properties of functors *)

Definition split_ess_surj {A B : precategory}
  (F : functor A B) 
  := ∏ b : B, ∑ a : A, iso (F a) b.

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

Lemma right_adj_equiv_is_full {D1 D2 : category}
  (F : functor D1 D2) (GG : adj_equivalence_of_cats F)
  : full (right_adjoint GG).
Proof.
  apply full_from_ff, right_adj_equiv_is_ff.
Qed.


Definition ff_on_isos {C D : precategory} (F : functor C D) : UU
  := ∏ c c', isweq (@functor_on_iso _ _ F c c').

Lemma fully_faithful_impl_ff_on_isos {C D : precategory} (F : functor C D) 
      : fully_faithful F -> ff_on_isos F.
Proof.
  intros Fff c c'.
  use gradth.
  - intro XR. exists (invmap (make_weq _ (Fff _ _ )) XR). cbn.
    apply (ff_reflects_is_iso _ _ _ Fff).
    assert (XT := homotweqinvweq (make_weq _ (Fff c c' ))).
    cbn in *.
    apply (transportb (λ i : _ --> _, is_iso i) (XT (pr1 XR) )).
    apply XR.
  - cbn. intro i. apply eq_iso. cbn.
    apply (homotinvweqweq (make_weq _ (Fff _ _ ))).
  - cbn. intro i. apply eq_iso. cbn.
    apply (homotweqinvweq (make_weq _ (Fff _ _ ))).
Defined.

Definition reflects_pullbacks {C D : category} (F : functor C D) : UU
  := ∏ {a b c d : C}{f : C ⟦b, a⟧} {g : C ⟦c, a⟧} {h : C⟦d, b⟧} {k : C⟦d,c⟧}
       (H : h · f = k · g),
     isPullback (functor_on_square _ _ F H) -> isPullback H.

Lemma ff_reflects_pullbacks {C D : category} {F : functor C D}
      (F_ff : fully_faithful F) : reflects_pullbacks F.
Proof.
  do 10 intro.
  use (isPullback_preimage_square _ _ _ _ _ _ X).
  - apply homset_property.
  - apply F_ff.
Defined.

(** * Equivalences *)

Section Adjoint_Equivalences.

(* TODO: remove this once renamed to this upstream (from erroneous “…precats…”) *)
Coercion adj_equiv_of_cats_from_adj {A B : category} (E : adj_equiv A B)
  : adj_equivalence_of_cats E := pr2 E.

Definition adj_equiv_from_adjunction
    {C D : category}
    (FG : adjunction C D)
    (unit_iso : forall c:C, is_iso (adjunit FG c))
    (counit_iso : forall d:D, is_iso (adjcounit FG d))
  : adj_equiv C D.
Proof.
  exists (left_functor FG).
  use tpair.
  - exists (right_functor FG).
    use tpair.
    + split.
      * exact (adjunit FG).
      * exact (adjcounit FG).
    + exact (pr2 FG).
  - split; cbn.
    + apply unit_iso.
    + apply counit_iso.
Defined.

Definition compose_adj_equiv
    {C D E : category}
    (F : adj_equiv C D)
    (G : adj_equiv D E)
  : adj_equiv C E.
Proof.
  exists (functor_composite F G).
  apply comp_adj_equivalence_of_cats;
    apply adj_equiv_of_cats_from_adj.
Defined.

Definition inv_adj_equiv
    {C D : category}
    (F : adj_equiv C D)
  : adj_equiv D C.
Proof.
  exists (adj_equivalence_inv F).
  apply adj_equivalence_of_cats_inv.
Defined.

End Adjoint_Equivalences.

Section eqv_from_ess_split_and_ff.

Context {A B : category}
        {F : functor A B}
        (Fff : fully_faithful F)
        (Fses : split_ess_surj F).

Let Fweq {a b} f := (weq_from_fully_faithful Fff a b f).
Let Finv {a b} g := (invweq (weq_from_fully_faithful Fff a b) g).

Definition G_ff_split_data : functor_data B A.
Proof.
  use tpair.
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
       apply (homotweqinvweq (make_weq _ (Fff _ _ ))).
    etrans. apply maponpaths_2.
       apply (homotweqinvweq (make_weq _ (Fff _ _ ))).
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
  use tpair.
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
  apply (invmaponpathsweq (make_weq _ (Fff _ _ )));
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


Definition η_ff_split
  : nat_trans (functor_identity A) (functor_composite F G_ff_split).
Proof.
  use tpair.
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
    apply (invmaponpathsweq (make_weq _ (Fff _ _ ))).
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

Definition adj_equivalence_of_cats_ff_split : adj_equivalence_of_cats F.
Proof.
  use tpair.
  - exists G_ff_split.
    use tpair.
    + exists η_ff_split. 
      exact ε_ff_split. 
    + apply form_adjunction_ff_split. 
  - split; cbn.
    + intro a. 
      use (fully_faithful_reflects_iso_proof _ _ _ Fff _ _ (make_iso _ _ )).
      apply is_iso_inv_from_iso. 
    + intro b. apply pr2.
Defined.

End eqv_from_ess_split_and_ff.

(** * Cat-isomorphisms *)

Section CatIso.

Definition catiso_is_path_cat (C D : category)
  : (C = D) ≃ catiso C D.
Proof.
  eapply weqcomp.
  - eapply PartA.path_sigma_hprop.
    apply isaprop_has_homsets.
  - apply catiso_is_path_precat.
    apply D.
Defined.

Definition catiso_univalent (C : category) (D : category)
  : catiso D C → is_univalent C → is_univalent D.
Proof.
  intros i C_univ.
  set (D_eq_C := invweq (catiso_is_path_cat _ _ ) i).
  use (transportb _ D_eq_C).
  apply C_univ.
Defined.

End CatIso.

(** * Univalent categories *)

Coercion univalent_category_is_univalent : univalent_category >-> is_univalent.

Definition functor_univalent_category (C : precategory) (D : univalent_category)
  : univalent_category.
Proof.
  exists (functor_category C D).
  apply is_univalent_functor_category.
  apply D.
Defined.

(** * Functors and isomorphisms *)

Lemma functor_is_iso_is_iso {C C' : precategory} (F : functor C C')
    {a b : ob C} (f : C ⟦a,b⟧) (fH : is_iso f) : is_iso (#F f).
Proof.
  apply (functor_on_iso_is_iso _ _ F _ _ (make_iso f fH)).
Defined.

Definition iso_ob {C : precategory} {D : category}
          {F G : functor C D} (a : iso (C:= [C, D]) F G)
  : ∏ c, iso (F c) (G c).
Proof.
  intro c.
  use make_iso.
  - cbn. apply ((pr1 a : nat_trans _ _ ) c).
  - apply is_functor_iso_pointwise_if_iso. apply (pr2 a).
Defined.

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

Definition nat_iso_from_pointwise_iso (D : precategory) (E : category)
  (F G : [D, E])
  (a : ∏ d, iso ((F : functor _ _) d) ((G : functor _ _) d))
  (H : is_nat_trans _ _ a)
  : iso F G.
Proof.
  use functor_iso_from_pointwise_iso .
  use tpair.
  - intro d. apply a.
  - apply H.
  - intro d. apply (pr2 (a d)).
Defined.

Lemma iso_from_iso_with_postcomp (D E E' : category)
  (F G : functor D E) (H : functor E E')
  (Hff : fully_faithful H) : 
  iso (C:=[D, E']) (functor_composite F H) (functor_composite G H)
  ->
  iso (C:=[D, E]) F G.
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
    etrans; [| apply maponpaths_2; apply (!XTT _ )];
    apply XR
    ).
Defined.

Definition functor_assoc_iso (D1 D2 D3 : precategory) (D4 : category)
     (F : functor D1 D2) (G : functor D2 D3) (H : functor D3 D4) :
    iso (C:=[D1,D4])
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

Definition functor_comp_id_iso (D1 : precategory) (D2 : category)
     (F : functor D1 D2) :
  iso (C:=[D1,D2]) (functor_composite F (functor_identity _ )) F.
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

Definition functor_precomp_iso (D1 D2 : precategory) (D3 : category)
    (F : functor D1 D2) (G H : functor D2 D3) :
    iso (C:=[D2,D3]) G H ->
    iso (C:=[D1,D3]) (functor_composite F G)
                          (functor_composite F H).
Proof.
  intro a.
  use nat_iso_from_pointwise_iso.
  - intro d. apply (functor_iso_pointwise_if_iso _ _ _ _ _ a (pr2 a)).
  - abstract (intros x x' f; apply (nat_trans_ax (pr1 a))).
Defined.

(** * Basic pullback utility functions *)

Section Pullback_Basics.

Definition map_into_Pb
    {C : precategory} {a b c d : C}
    {f : a --> b} {g : a --> c} {k : b --> d} {h : c --> d}
    {sqr_comm : f ;; k = g ;; h}
    (Pb : isPullback sqr_comm)
    {e : C} (x : e --> b) (y : e --> c) (H : x ;; k = y ;; h)
  :  e --> a.
Proof.
  eapply (PullbackArrow (make_Pullback _ Pb)).
  apply H.
Defined.

Definition Pb_map_commutes_1
    {C : precategory} {a b c d : C}
    {f : a --> b} {g : a --> c} {k : b --> d} {h : c --> d}
    {sqr_comm : f ;; k = g ;; h}
    (Pb : isPullback sqr_comm)
    {e : C} (x : e --> b) (y : e --> c) H
  : map_into_Pb Pb x y H ;; f = x.
Proof.
  apply (PullbackArrow_PullbackPr1 (make_Pullback _ _)).
Qed.

Definition Pb_map_commutes_2
    {C : precategory} {a b c d : C}
    {f : a --> b} {g : a --> c} {k : b --> d} {h : c --> d}
    {sqr_comm : f ;; k = g ;; h}
    (Pb : isPullback sqr_comm)
    {e : C} (x : e --> b) (y : e --> c) H
  : map_into_Pb Pb x y H ;; g = y.
Proof.
  apply (PullbackArrow_PullbackPr2 (make_Pullback _ _)).
Qed.

Lemma map_into_Pb_unique
    {C : precategory} {a b c d : C}
    {f : a --> b} {g : a --> c} {k : b --> d} {h : c --> d}
    {sqr_comm : f ;; k = g ;; h}
    (Pb : isPullback sqr_comm)
    {e : C} {x y : e --> a}
    (e_f : x ;; f = y ;; f) (e_g : x ;; g = y ;; g)
  : x = y.
Proof.
  etrans.
  { use (PullbackArrowUnique _ Pb); try eassumption.
    repeat rewrite <- assoc. apply maponpaths; assumption. }
  apply pathsinv0, (PullbackArrowUnique _ Pb); apply idpath.
Qed.

(* In fact this is trivial, since the equality doesn’t appear in the type of the pullback. However, it’s convenient for proof scripts. *)
Lemma isPullback_indepdent_of_path
    {C : precategory} {a b c d : C}
    {f : a --> b} {g : a --> c} {k : b --> d} {h : c --> d}
    {sqr_comm : f ;; k = g ;; h}
    (Pb : isPullback sqr_comm)
    (sqr_comm' :  f ;; k = g ;; h)
  : isPullback (sqr_comm').
Proof.
  exact Pb.
Defined.

(* Duplicate of [is_symmetric_isPullback] from UniMath, but without the un-needed [has_homsets]/[category] assumption *)
Lemma is_symmetric_isPullback
    {C : precategory}
    {a b c d : C} {f : b --> a} {g : c --> a}
    {p1 : d --> b} {p2 : d --> c} {H : p1 · f = p2 · g}
    (pb : isPullback H)
  : isPullback (! H).
Proof.
  use make_isPullback.
  intros e h k H'.
  use (iscontrweqf _ (pb e k h (! H'))).
  use (weqtotal2 (idweq _)).
  intros ?. apply weqdirprodcomm.
Defined.

(* Variant of [is_symmetric_isPullback], more convenient for applying when reasoning bottom-up. *)
Lemma is_symmetric'_isPullback
    {C : precategory}
    {a b c d : C} {f : b --> a} {g : c --> a}
    {p1 : d --> b} {p2 : d --> c} {H : p1 · f = p2 · g}
    (pb : isPullback (! H))
  : isPullback H.
Proof.
  eapply transportf. 2: { eapply is_symmetric_isPullback, pb. }
  apply pathsinv0inv0.
Defined.

End Pullback_Basics.

(** * Pullback transfer lemmas *)

Section Pullback_transfers.
(* Various results, generally showing that perturbing a pullback squares by equalities and/or isos is still a pullback. *)

Lemma square_morphism_equal
    {C : precategory} {a b c d : C}
    {f : a --> b} {g : a --> c} {k : b --> d} {h : c --> d}
    (sqr_comm : f ;; k = g ;; h)
    {k'} (e : k' = k)
  : f ;; k' = g ;; h.
Proof.
  rewrite e. assumption.
Defined.

Lemma isPb_morphism_equal
    {C : precategory} {a b c d : C}
    {f : a --> b} {g : a --> c} {k : b --> d} {h : c --> d}
    (sqr_comm : f ;; k = g ;; h)
    (Pb : isPullback sqr_comm)
    {k'} (e : k' = k)
  : isPullback (square_morphism_equal sqr_comm e).
Proof.
  match goal with |[|- isPullback ?HH] => generalize HH end.
  rewrite e.
  intro.
  apply Pb.
Defined.

Definition commutes_and_is_pullback {C : category} {a b c d : C}
    (f : b --> a) (g : c --> a) (p1 : d --> b) (p2 : d --> c)
  : UU
:= ∑ (H : p1 ;; f = p2 ;; g), isPullback H.

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
  refine (pre_comp_with_iso_is_inj _ _ _ i_d _ _ _ _).
  exact (pr2 i_d).  (* TODO: access function [is_iso_from_iso]? *)
  rewrite 2 assoc.
  rewrite <- i_p1, <- i_p2.
  rewrite <- 2 assoc.
  rewrite <- i_f, <- i_g.
  rewrite 2 assoc.
  apply maponpaths_2, H.
Qed.

(* Generalisation of [isPulback_iso_of_morphisms].
TODO: This probably should work in an arbitrary precategory, i.e. not requiring the hom-sets assumption.  Try upgrading proof to show that? *)
Lemma isPullback_transfer_iso {C : category}
      {a b c d : C}
      {f : b --> a} {g : c --> a} {p1 : d --> b} {p2 : d --> c}
      (H : p1 ;; f = p2;; g)
      {a' b' c' d' : C}
      {f' : b' --> a'} {g' : c' --> a'} {p1' : d' --> b'} {p2' : d' --> c'}
      (H' : p1' ;; f' = p2' ;; g')
      {i_a : iso a a'} {i_b : iso b b'} {i_c : iso c c'} {i_d : iso d d'}
      (i_f : f ;; i_a = i_b ;; f') (i_g : g ;; i_a = i_c ;; g')
      (i_p1 : p1 ;; i_b = i_d ;; p1') (i_p2 : p2 ;; i_c = i_d ;; p2')
   : isPullback H
   -> isPullback H'.
Proof.
  intros Hpb.
  apply (make_isPullback _ ).    
  intros X h k H''.
  simple refine (tpair _ _ _ ).
  - simple refine (tpair _ _ _ ).
    { refine ( _ ;; i_d ).
      simple refine (PullbackArrow (make_Pullback _ Hpb) _ _ _ _).
      + exact (h ;; iso_inv_from_iso i_b).
      + exact (k ;; iso_inv_from_iso i_c).
      + abstract (
          apply (post_comp_with_iso_is_inj _ _ i_a (pr2 _));
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
        try apply (PullbackArrow_PullbackPr2 (make_Pullback _ _));
        try apply (PullbackArrow_PullbackPr1 (make_Pullback _ _))
      | rewrite <- assoc, iso_after_iso_inv; apply id_right]] ).
  - intros hk'.
    apply subtypePath.
      intro; apply isapropdirprod; apply homset_property.
    cbn.
    apply (post_comp_with_iso_is_inj _ _ (iso_inv_from_iso i_d) (pr2 _)).
    eapply @pathscomp0.
    2: { rewrite <- assoc. cbn. rewrite iso_inv_after_iso.
         eapply pathsinv0, id_right. }
    apply PullbackArrowUnique; cbn.
    + apply (post_comp_with_iso_is_inj _ _ i_b (pr2 _)).
      repeat rewrite <- assoc.
      rewrite i_p1, iso_after_iso_inv, id_right.
      eapply @pathscomp0.
        apply maponpaths. rewrite assoc, iso_after_iso_inv. apply id_left.
      apply (pr1 (pr2 hk')).
    + apply (post_comp_with_iso_is_inj _ _ i_c (pr2 _)).
      repeat rewrite <- assoc.
      rewrite i_p2, iso_after_iso_inv, id_right.
      eapply @pathscomp0.
        apply maponpaths. rewrite assoc, iso_after_iso_inv. apply id_left.
      apply (pr2 (pr2 hk')).
  Qed.

(* Generalisation of [isPulback_iso_of_morphisms]. *)
Lemma commutes_and_is_pullback_transfer_iso {C : category}
      {a b c d : C}
      {f : b --> a} {g : c --> a} {p1 : d --> b} {p2 : d --> c}
      {a' b' c' d' : C}
      {f' : b' --> a'} {g' : c' --> a'} {p1' : d' --> b'} {p2' : d' --> c'}
      {i_a : iso a a'} {i_b : iso b b'} {i_c : iso c c'} {i_d : iso d d'}
      (i_f : f ;; i_a = i_b ;; f') (i_g : g ;; i_a = i_c ;; g')
      (i_p1 : p1 ;; i_b = i_d ;; p1') (i_p2 : p2 ;; i_c = i_d ;; p2')
      (H : p1 ;; f = p2 ;; g) (P : isPullback H)
   : commutes_and_is_pullback f' g' p1' p2'.
Proof.
  exists (commuting_square_transfer_iso i_f i_g i_p1 i_p2 H).
  exact (isPullback_transfer_iso _ _ i_f i_g i_p1 i_p2 P).
Qed.

Lemma postcomp_commutes_and_is_pb_with_iso
    {C : category} {a b c d : C}
    {f : a --> b} {g : a --> c} {k : b --> d} {h : c --> d}
    (sqr_comm : f ;; k = g ;; h)
    (Pb : isPullback sqr_comm)
    {y : C} (r : y --> d) (i : iso b y) (Hi : i ;; r = k)
  : ∑ H : f ;; i ;; r = g ;; h, isPullback H.
Proof.
  simple refine (commutes_and_is_pullback_transfer_iso _ _ _ _ _ Pb);
    try apply identity_iso;
    try rewrite id_left;
    try rewrite id_right;
    try apply idpath.
  apply pathsinv0, Hi.
Qed.

Definition postcomp_pb_with_iso
    {C : category} {a b c d : C}
    {f : a --> b} {g : a --> c} {k : b --> d} {h : c --> d}
    (sqr_comm : f ;; k = g ;; h)
    (Pb : isPullback sqr_comm)
    {y : C} (r : y --> d) (i : iso b y) (Hi : i ;; r = k)
  : isPullback _
:= pr2 (postcomp_commutes_and_is_pb_with_iso _ Pb _ i Hi).

End Pullback_transfers.

(** * Uniqueness of pullbacks *)

Definition isaprop_Pullback (C : category) (H : is_univalent C)
           (a b c : C) (f : b --> a) (g : c --> a)
: isaprop (Pullback f g).
Proof.
  unfold Pullback.
  apply invproofirrelevance.
  unfold Pullback.
  intros Pb Pb'.
  apply subtypePath.
  - intro; apply isofhleveltotal2.
    + apply homset_property.
    + intros; apply isaprop_isPullback.
  - apply (total2_paths_f (isotoid _ H (iso_from_Pullback_to_Pullback _ _))).
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

(* TODO: check for results of the following section upstream *)
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
  
  Variable CC : category.
  Variables A B C D A' B' : CC.
  Variables (f : A --> B) (g : A --> C) (k : B --> D) (j : C --> D)
            (H : f ;; k = g ;; j) (pb : isPullback H).
  Variables (f' : A' --> B') (g' : A' --> C) (r : B' --> D) (h : iso B B').
  Variable (H' : f' ;; r = g' ;; j).
  Variable (pb' : isPullback H').
  Variable (T : h ;; r = k).

  Definition map_to_2nd_pb : A --> A'.
  Proof.
    use (map_into_Pb pb').
    - exact (f ;; h).
    - exact g.
    - eapply pathscomp0. 2: { apply H. }
      eapply pathscomp0. apply (!assoc _ _ _ ).
      apply maponpaths. apply T.
  Defined.

  Definition map_to_1st_pb : A' --> A.
  Proof.
    use (map_into_Pb pb).
    - exact (f';; inv_from_iso h).
    - exact g'.
    - eapply pathscomp0; [| apply H'].
      eapply pathscomp0; [ apply (!assoc _ _ _ ) |].
      apply maponpaths. apply iso_inv_on_right.
      apply (!T).
  Defined.

  Lemma inv1 : map_to_2nd_pb ;; map_to_1st_pb = identity _ .
  Proof.
    apply (map_into_Pb_unique pb).
    - rewrite id_left.
      rewrite <- assoc.
      unfold map_to_1st_pb.
      rewrite Pb_map_commutes_1.
      rewrite assoc.
      apply pathsinv0.
      apply iso_inv_on_left.
      unfold map_to_2nd_pb.
      use Pb_map_commutes_1.
    - rewrite id_left.
      rewrite <- assoc.
      unfold map_to_1st_pb.
      rewrite Pb_map_commutes_2.
      unfold map_to_2nd_pb.
      apply Pb_map_commutes_2.
  Qed.

  Lemma inv2 : map_to_1st_pb ;; map_to_2nd_pb = identity _ .
  Proof.
    apply (map_into_Pb_unique pb').
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

(** * Limits and colimits *)

(* NOTE: just initial and terminal objects for now; but if any other material on general limits/colimits is added, it should be grouped here. *)
Section Limits.

  Lemma isaprop_isTerminal {C : category} (x : C) : isaprop (isTerminal C x).
  Proof.
    repeat (apply impred; intro).
    apply isapropiscontr.
  Qed.

  Lemma isaprop_isInitial {C : category} (x : C) : isaprop (isInitial C x).
  Proof.
    repeat (apply impred; intro).
    apply isapropiscontr.
  Qed.

End Limits.

(** * Sections of maps *)

(* TODO: currently, sections are independently developed in many places in [TypeTheory].  Try to unify the treatments of them here?  Also unify with ad hoc material on sections in [UniMath.CategoryTheory.limits.pullbacks]: [pb_of_section], [section_from_diagonal], etc.*)
Section Sections.

  Definition section {C : precategory} {X Y : C} (f : X --> Y)
    := ∑ (s : Y --> X), s ;; f = identity _.

  Coercion section_pr1 {C : precategory} {X Y : C} (f : X --> Y)
    : section f -> (Y --> X)
  := pr1.

  Definition section_property {C : precategory}
      {X Y : C} {f : X --> Y} (s : section f)
    : s ;; f = identity _
  := pr2 s.

  Definition paths_section {C : category} {X Y : C} {f : X --> Y}
      {s s' : section f}
    : ((s : Y --> X) = s') -> s = s'.
  Proof.
    apply subtypePath.
    intro; apply homset_property.
  Qed.

  Definition isaset_section {C : category} {X Y : C} {f : X --> Y}
    : isaset (section f).
  Proof.
    apply isaset_total2.
    - apply homset_property.
    - intros; apply isasetaprop, homset_property.
  Qed.

End Sections.

(** * The total type of morphisms of a precategory *)

Section Mor_Total.

Definition mor_total (C : precategory) : UU
  := ∑ (ab : C × C), C⟦pr2 ab, pr1 ab⟧.

Definition morphism_as_total {C : precategory} {a b : C} (f : a --> b)
  : mor_total C.
Proof.
  exists (b,,a).
  exact f.
Defined.

Definition source {C} (X : mor_total C) : C := pr2 (pr1 X).
Definition target {C} (X : mor_total C) : C := pr1 (pr1 X).
Definition morphism_from_total {C} (X : mor_total C)
  : C ⟦source X, target X⟧
  := pr2 X.
Coercion morphism_from_total : mor_total >-> precategory_morphisms.

Definition functor_on_mor_total {C D : precategory} (F : functor C D) 
           (p : mor_total C) : mor_total D.
Proof.
  exists (F (pr1 (pr1 p)) ,, F (pr2 (pr1 p)) ).
  exact (#F p).
Defined.

Definition isweq_left_adj_equivalence_on_mor_total
    {C D : category} (F : functor C D)
    (isC : is_univalent C) (isD : is_univalent D)
    (H : adj_equivalence_of_cats F) 
  : isweq (functor_on_mor_total F).
Proof.
  use (gradth _ _ _ _ ).
  - apply (functor_on_mor_total (adj_equivalence_inv H)).
  - intro p.
    use total2_paths_f.
    + cbn. destruct p as [[a b] f].
      apply pathsdirprod; cbn. 
      * apply (isotoid _ isC). 
        apply iso_inv_from_iso, (unit_pointwise_iso_from_adj_equivalence H).
      * apply (isotoid _ isC).
        apply iso_inv_from_iso, (unit_pointwise_iso_from_adj_equivalence H).
    + cbn. destruct p as [[a b] f]. cbn in *.
      etrans. apply (transportf_pair (λ x : C × C, C ⟦ pr2 x, pr1 x ⟧)).
      cbn.
      rewrite transportf_isotoid.
      rewrite transportf_isotoid'.
      cbn. unfold precomp_with. rewrite id_right.
      rewrite assoc.
      assert (XR := nat_trans_ax (unit_from_are_adjoints (pr2 (pr1 H)))).
      cbn in XR. rewrite <- XR.
      rewrite <- assoc. 
      etrans. apply maponpaths.
      apply (iso_inv_after_iso (unit_pointwise_iso_from_adj_equivalence H a)).
      apply id_right.
    - intro p.
    use total2_paths_f.
    + cbn. destruct p as [[a b] f].
      apply pathsdirprod; cbn. 
      * apply (isotoid _ isD). 
        apply (counit_pointwise_iso_from_adj_equivalence H).
      * apply (isotoid _ isD).
        apply (counit_pointwise_iso_from_adj_equivalence H).
    + cbn. destruct p as [[a b] f]. cbn in *.
      etrans. apply (transportf_pair (λ x : D × D, D ⟦ pr2 x, pr1 x ⟧)).
      cbn.
      rewrite transportf_isotoid.
      rewrite transportf_isotoid'.
      cbn. unfold precomp_with. 
      assert (XR := nat_trans_ax (counit_from_are_adjoints (pr2 (pr1 H)))).
      cbn in XR. rewrite XR. clear XR.
      rewrite assoc. 
      etrans. apply maponpaths_2.
      apply (iso_after_iso_inv (counit_pointwise_iso_from_adj_equivalence H _)).
      apply id_left.
Defined.

Definition isweq_equivalence_on_mor_total {C D : category}
           (isC : is_univalent C) (isD : is_univalent D)
           (F : functor C D) (G : functor D C)
           (eta : iso (C:= [_ , _ ]) (functor_identity C) (F ∙ G))
           (eps : iso (C:= [_ , _ ]) (G ∙ F) (functor_identity D))
: isweq (functor_on_mor_total F).
Proof.
  use (gradth _ _ _ _ ).
  - apply (functor_on_mor_total G).
  - intro p.
    use total2_paths_f.
    + cbn. destruct p as [[a b] f].
      apply pathsdirprod; cbn. 
      * apply (isotoid _ isC). 
        apply iso_inv_from_iso. apply (iso_ob eta).
      * apply (isotoid _ isC).
        apply iso_inv_from_iso. apply (iso_ob eta).
    + cbn. destruct p as [[a b] f]. cbn in *.
      etrans. apply (transportf_pair (λ x : C × C, C ⟦ pr2 x, pr1 x ⟧)).
      cbn.
      rewrite transportf_isotoid.
      rewrite transportf_isotoid'.
      cbn. unfold precomp_with. rewrite id_right.
      rewrite assoc. assert (XR := nat_trans_ax (pr1 eta)).
      cbn in XR. rewrite <- XR.
      rewrite <- assoc.
      rewrite id_right.
      etrans. apply maponpaths.
      apply (nat_trans_inv_pointwise_inv_after _ _ C _ _ (pr1 eta)).
      apply id_right.
  - intro p.
    use total2_paths_f.
    + cbn. destruct p as [[a b] f].
      apply pathsdirprod; cbn. 
      * apply (isotoid _ isD). 
        apply (iso_ob eps).
      * apply (isotoid _ isD).
        apply (iso_ob eps).
    + cbn. destruct p as [[a b] f]. cbn in *.
      etrans. apply (transportf_pair (λ x : D × D, D ⟦ pr2 x, pr1 x ⟧)).
      cbn.
      rewrite transportf_isotoid.
      rewrite transportf_isotoid'.
      cbn. unfold precomp_with. 
      assert (XR := nat_trans_ax (pr1 eps)).
      cbn in XR. rewrite XR. clear XR.
      rewrite assoc. 
      rewrite id_right.
      etrans. apply maponpaths_2.
      apply (nat_trans_inv_pointwise_inv_before _ _ D  _ _ (pr1 eps)).
      apply id_left.
Defined.

End Mor_Total.

(** * Comprehension categories *)

Definition comprehension_cat
  := ∑ (C : category), (comprehension_cat_structure C).

Coercion category_of_comprehension_cat (C : comprehension_cat) := pr1 C.
Coercion structure_of_comprehension_cat (C : comprehension_cat) := pr2 C.


(** * Unorganised lemmas *)

(* Lemmas that probably belong in one of the sections above, but haven’t been sorted into them yet.  Mainly a temporary holding pen for lemmas being upstreamed from other files. TODO: empty this bin frequently (but keep it here for re-use). *) 
Section Unorganised.

End Unorganised.

(** * Notes *)

(* TODO: Notes towards some possible improvements in UniMath’s treatment of adjunctions, equivalences (and a few other unrelated things in the library):

  One really confusing point is having
  [adj_equivalence_of_cats] for the property of (or structure on) a functor,
  while
  [equivalence_of_cats] is the sigma-type of this over functors.

  Suggestion:
  - [equivalence] changes to [equiv] throughout (this seems unambiguous?)

  - [adj_equivalence_of_cats]
    changes to either
    [is_adj_equiv] or [adj_equiv_structure]
    (possible also [_of_cats], but this seems reasonably implicit since it’s on a functor) 
  - [equivalence_of_cats]
    changes to [adj_equiv_of_cats]
  - lemmas about them are renamed as consistently as possible, following these.

  - consolidate with the material from [DisplayedCats.Equivalences_bis], including its adj_equiv.

  - projection from an equivalence to its functor is made a coercion?
  - in particular, the confusion about variance for adjoints should be resolved if possible!
  - coercions should respect the fact that equivalences have a primary direction, as do individual adjoints, but “adjunctions” don’t.

  - equivalences should have clear access functions to all components

  Displayed:
  - rename [disp_adjunction_id] -> [disp_adjunction_over_id]

  - add access function for triangle identities of adjunction?
    e.g. coercion [adjunction_property : adjunction -> forms_adjunction]
    and access functions [triangle_1], [triangle_2] from there?

  Unrelated:

  - improve stuff on nat isos?  Move from current location to a more core one, and give good access functions, e.g. use it in lemmase like [functor_iso_from_pointwise_iso]?

  - Rename “transportb_transpose_right”.

*)

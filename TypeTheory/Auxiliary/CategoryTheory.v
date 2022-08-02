Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.All.
(* a few libraries need to be reloaded after “All”,
   to claim precedence on overloaded names *)
Require Import UniMath.CategoryTheory.limits.graphs.limits.
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

(* TODO: check more thoroughly if this is provided in the library; if so, use the library version, otherwise move this upstream.  Cf. also https://github.com/UniMath/UniMath/issues/279 *)
Lemma inv_from_z_iso_from_is_z_iso {D: precategory} {a b : D}
  (f: a --> b) (g : b --> a) (H : is_inverse_in_precat f g)
: inv_from_z_iso (f ,,  (g ,, H)) 
  = g.
Proof.
  apply idpath.
Qed.

(** * Idtoiso and isotoid *)

Lemma idtoiso_identity_z_iso {C : precategory} (a : C)
  : idtoiso (idpath a) = identity_z_iso a.
Proof.
  apply idpath.
Defined.

Lemma idtoiso_identity {C : precategory} (a : C)
  : (idtoiso (idpath a) : _ --> _) = identity a.
Proof.
  apply idpath.
Defined.

Lemma forall_isotid (A : category) (a_is : is_univalent A) 
      (a a' : A) (P : z_iso a a' -> UU) :
  (∏ e, P (idtoiso e)) → ∏ i, P i.
Proof.
  intros H i.
  rewrite <- (idtoiso_isotoid _ a_is).
  apply H.
Defined.

Lemma transportf_isotoid_functor 
  (A X : category) (H : is_univalent A)
  (K : functor A X)
   (a a' : A) (p : z_iso a a') (b : X) (f : K a --> b) :
 transportf (fun a0 => K a0 --> b) (isotoid _ H p) f = #K (inv_from_z_iso p) ;; f.
Proof.
  rewrite functor_on_inv_from_z_iso. simpl. cbn.
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
  cbn.
  induction q.
  rewrite idtoiso_identity_z_iso.
  rewrite id_right.
  induction p.
  apply idpath.
Defined.

Lemma idtoiso_eq_idpath (C : precategory) (a : C) (e : a = a)
    (H : e = idpath _ )
  : (idtoiso e : _ --> _) = identity_z_iso _.
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
    {a b b' : D} (f : a --> b) (p : z_iso b b')
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

Lemma constant_nat_trans_is_z_iso
    {C1 C2 : category} {x y : C2} (f : x --> y )
  : is_z_isomorphism f -> @is_z_isomorphism [C1,C2] _ _ (constant_nat_trans C1 f).
Proof.
  intro f_iso. use nat_trafo_z_iso_if_pointwise_z_iso.
  intro; apply f_iso.
Defined.

Lemma constant_nat_z_iso
    {C1 C2 : category} {x y : C2} (f : z_iso x y )
  : @z_iso [C1,C2] (constant_functor C1 _ x) (constant_functor C1 _ y).
Proof.
  exists (constant_nat_trans _ f).
  apply constant_nat_trans_is_z_iso, z_iso_is_z_isomorphism.
Defined.

Definition nat_trans_from_nat_z_iso
    {C D : category} {F G : functor C D} (α : nat_z_iso F G)
  : nat_trans F G
:= pr1 α.
Coercion nat_trans_from_nat_z_iso : nat_z_iso >-> nat_trans.

(** * Properties of functors *)

Definition split_ess_surj {A B : precategory}
  (F : functor A B) 
  := ∏ b : B, ∑ a : A, z_iso (F a) b.

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


Definition ff_on_z_isos {C D : precategory} (F : functor C D) : UU
  := ∏ c c', isweq (@functor_on_z_iso _ _ F c c').

Lemma fully_faithful_impl_ff_on_isos {C D : category} (F : functor C D) 
      : fully_faithful F -> ff_on_z_isos F.
Proof.
  intros Fff c c'.
  use gradth.
  - intro XR. exists (invmap (make_weq _ (Fff _ _ )) XR). cbn.
    apply (ff_reflects_is_iso _ _ _ Fff).
    assert (XT := homotweqinvweq (make_weq _ (Fff c c' ))).
    cbn in *.
    apply (transportb (λ i : _ --> _, is_z_isomorphism i) (XT (pr1 XR) )).
    apply XR.
  - cbn. intro i. apply z_iso_eq. cbn.
    apply (homotinvweqweq (make_weq _ (Fff _ _ ))).
  - cbn. intro i. apply z_iso_eq. cbn.
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

Definition adj_equiv_from_adjunction
    {C D : category}
    (FG : adjunction C D)
    (unit_iso : forall c:C, is_z_isomorphism (adjunit FG c))
    (counit_iso : forall d:D, is_z_isomorphism (adjcounit FG d))
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
    exact (pr2 (Fses b) ;; f' ;; inv_from_z_iso (pr2 (Fses b'))).
Defined.

Definition G_ff_split_ax : is_functor G_ff_split_data.
Proof.
  split.
  - intro b. cbn. rewrite id_right. simpl.
    apply invmap_eq. cbn.
    etrans. apply z_iso_inv_after_z_iso.
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
    etrans. apply maponpaths_2.  apply z_iso_after_z_iso_inv.
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
  rewrite z_iso_after_z_iso_inv;
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
    (λ a : A, Finv (inv_from_z_iso (pr2 (Fses (F ((functor_identity A) a)))))).
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
  rewrite z_iso_after_z_iso_inv;
  rewrite id_left ;
  apply idpath.
Qed.


Definition η_ff_split
  : nat_trans (functor_identity A) (functor_composite F G_ff_split).
Proof.
  use tpair.
  -  intro a.
     apply Finv.
     apply (inv_from_z_iso (pr2 (Fses _ ))).
  - apply is_nat_trans_η_ff_split. 
Defined.
    
Lemma form_adjunction_ff_split 
  : form_adjunction F G_ff_split η_ff_split ε_ff_split.
  simpl. split.
  * intro a.
    cbn. 
    etrans. apply maponpaths_2. use homotweqinvweq. 
    apply z_iso_after_z_iso_inv.
  * intro b.
    cbn. 
    apply (invmaponpathsweq (make_weq _ (Fff _ _ ))).
    cbn.
    rewrite functor_comp.
    rewrite functor_id.
    etrans. apply maponpaths. use homotweqinvweq.
    etrans. apply maponpaths_2. use homotweqinvweq.
    repeat rewrite assoc.
    rewrite z_iso_after_z_iso_inv.
    rewrite id_left.
    apply z_iso_inv_after_z_iso.
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
      use (fully_faithful_reflects_iso_proof _ _ _ Fff _ _ (make_z_iso' _ _ )).
      apply is_z_iso_inv_from_z_iso. 
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
Definition z_iso_ob {C : precategory} {D : category}
          {F G : functor C D} (a : z_iso (C:= [C, D]) F G)
  : ∏ c, z_iso (F c) (G c).
Proof.
  intro c.
  use make_z_iso'.
  - cbn. apply ((pr1 a : nat_trans _ _ ) c).
  - apply nat_trafo_pointwise_z_iso_if_z_iso. apply (pr2 a).
Defined.

Lemma inv_from_z_iso_z_iso_from_fully_faithful_reflection {C D : precategory}
      (F : functor C D) (HF : fully_faithful F) (a b : C) (i : z_iso (F a) (F b))
      : inv_from_z_iso
       (iso_from_fully_faithful_reflection HF i) = 
 iso_from_fully_faithful_reflection HF (z_iso_inv_from_z_iso i).
Proof.
  apply idpath.
Defined.

Definition nat_z_iso_from_pointwise_z_iso (D : precategory) (E : category)
  (F G : [D, E])
  (a : ∏ d, z_iso ((F : functor _ _) d) ((G : functor _ _) d))
  (H : is_nat_trans _ _ a)
  : z_iso F G.
Proof.
  use z_iso_from_nat_z_iso.
  use tpair.
  - use tpair.
    + intro d. apply a.
    +  apply H.
  - intro d. apply (pr2 (a d)).
Defined.

Lemma z_iso_from_z_iso_with_postcomp (D E E' : category)
  (F G : functor D E) (H : functor E E')
  (Hff : fully_faithful H) : 
  z_iso (C:=[D, E']) (functor_composite F H) (functor_composite G H)
  ->
  z_iso (C:=[D, E]) F G.
Proof.
  intro a.
  use nat_z_iso_from_pointwise_z_iso.
  - intro d. simpl.
    apply (iso_from_fully_faithful_reflection Hff).
    apply (functor_z_iso_pointwise_if_z_iso _ _ _ _ _ a (pr2 a)).
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

Definition functor_assoc_z_iso (D1 D2 D3 : precategory) (D4 : category)
     (F : functor D1 D2) (G : functor D2 D3) (H : functor D3 D4) :
    z_iso (C:=[D1,D4])
         (functor_composite (functor_composite F G) H)
         (functor_composite F (functor_composite G H)).
Proof.
  use nat_z_iso_from_pointwise_z_iso.
  - intro d. apply identity_z_iso.
  - abstract (
        intros x x' f;
        rewrite id_left;
        rewrite id_right;
        apply idpath
     ).
Defined.

Definition functor_comp_id_z_iso (D1 : precategory) (D2 : category)
     (F : functor D1 D2) :
  z_iso (C:=[D1,D2]) (functor_composite F (functor_identity _ )) F.
Proof.
  use nat_z_iso_from_pointwise_z_iso.
  - intro. apply identity_z_iso.
  - abstract (
       intros x x' f;
       rewrite id_left;
       rewrite id_right;
       apply idpath
    ).
Defined.

Definition functor_precomp_z_iso (D1 D2 : precategory) (D3 : category)
    (F : functor D1 D2) (G H : functor D2 D3) :
    z_iso (C:=[D2,D3]) G H ->
    z_iso (C:=[D1,D3]) (functor_composite F G)
                          (functor_composite F H).
Proof.
  intro a.
  use nat_z_iso_from_pointwise_z_iso.
  - intro d. apply (functor_z_iso_pointwise_if_z_iso _ _ _ _ _ a (pr2 a)).
  - abstract (intros x x' f; apply (nat_trans_ax (pr1 a))).
Defined.

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

  Definition isaset_section {C : category} {X Y : C} (f : X --> Y)
    : isaset (section f).
  Proof.
    apply isaset_total2.
    - apply homset_property.
    - intros; apply isasetaprop, homset_property.
  Qed.

  Definition section_hSet {C : category} {X Y : C} (f : X --> Y)
    := make_hSet (section f) (isaset_section f).

End Sections.

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

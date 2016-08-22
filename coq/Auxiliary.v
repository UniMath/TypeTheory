
(** 

 Ahrens, Lumsdaine, Voevodsky 2015

Auxiliary background lemmas for the Ahrens/Lumsdaine/Voevodsky “Systems” project.  
Possibly some should be upstreamed to “UniMath” eventually.

*)


Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.Foundations.Combinatorics.StandardFiniteSets.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.limits.graphs.pullbacks.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.category_hset_structures.
Require Import UniMath.CategoryTheory.yoneda.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.equivalences.

Require Import Systems.UnicodeNotations.

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

Lemma pr1_transportf (A : UU) (B : A -> UU) (P : Π a, B a -> UU)
   (a a' : A) (e : a = a') (xs : Σ b : B a, P _ b):
   pr1 (transportf (fun x => Σ b : B x, P _ b) e xs) = 
     transportf (fun x => B x) e (pr1 xs).
Proof.
  destruct e; apply idpath.
Defined.

Lemma transportf_const (A B : UU) (a a' : A) (e : a = a') (b : B) :
   transportf (fun _ => B) e b = b.
Proof.
  induction e.
  apply idpath.
Qed.

Lemma transportf_forall {A B} (C : A -> B -> UU)
  {x0 x1 : A} (e : x0 = x1) (f : forall y:B, C x0 y)
  : transportf (fun x => forall y, C x y) e f
  = fun y => transportf (fun x => C x y) e (f y).
Proof.
  destruct e; apply idpath.
Defined.

Definition transportf_forall_var :
  Π (A : UU) (B : A -> UU) (C : UU)
    (a1 a2 : A) (e : a1 = a2)
(f : B a1 -> C),
transportf (λ x : A, Π y : B x, C) e f =
(λ y : B a2 ,  f (transportb B e y)).
Proof.
  intros A B D a1 a2 e f.
  induction e.
  apply idpath.
Defined.

Definition transportf_forall_var2 :
  Π (A : UU) (B C : A -> UU) 
    (a1 a2 : A) (e : a1 = a2)
    (f : B a1 -> C a1),
transportf (λ x : A, Π y : B x, C x) e f =  
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
  : Π (T1 T2 : UU) (f : T1 -> T2) (t1 : T1) (e : t1 = t1)
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
    apply (maponpaths (fun p => transportf _ p x)).
    apply hs.
  exact ex.
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

Definition rewrite_in_equivalence (A X : UU) (a a' b : A) :
  a = a' → (a' = b) ≃ X → (a = b) ≃ X.
Proof.
  intros.
  set  (H:= weqpair _ (isweqpathscomp0l b (!X0))).
  eapply weqcomp. apply H.
  apply X1.
Defined.

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
  - intros bp. use total2_paths. apply idpath. apply wv.
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

(** ** Equivalences of categories *)
(** Specifically: the composition of (adjoint) equivalences of precats. *)

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
    assert (T1 := triangle_id_left_ad _ _ _ adF a).
    assert (T1' := triangle_id_left_ad _ _ _ adF' (F a)).
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
    assert (T2 := triangle_id_right_ad _ _ _ adF (G' c)).
    assert (T2' := triangle_id_right_ad _ _ _ adF' c).
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

Coercion left_adj_from_adj_equiv (X Y : precategory) (K : functor X Y)
         (HK : adj_equivalence_of_precats K)
  : is_left_adjoint K
:= pr1 HK.

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

(** ** Misc lemmas/definitions on (pre)categories *)

Definition preShv C := functor_precategory C^op HSET has_homsets_HSET.

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

Lemma idtoiso_transportf_family_of_morphisms (D : precategory)
      (A : UU) (B : A -> UU)
      (F : Π a, B a -> D)
      (d d' : D) (deq : d = d')
      (R : Π a (b : B a), D⟦ F a b, d⟧)
     
: transportf (λ x, Π a b, D⟦ F a b, x⟧)
             deq R =
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

(* Seems to be an exact duplicate of a library lemma.  TODO: remove; or, if it’s not a duplicate, document the difference!

Really it’s just the *arguments* that we want to change (and for [cancel_precomposition] too. *)
Lemma cancel_postcomposition {C : precategory} {a b c : C} (f f' : a --> b) (g : b --> c)
: f = f' -> f ;; g = f' ;; g.
Proof.
  intro H. apply (maponpaths (fun f => f ;; g) H).
Defined.

Lemma idtoiso_postcompose_idtoiso_pre {C : precategory} {a b c : C} (g : a --> b) (f : a --> c)
              (p : b = c) :
  g = f ;; idtoiso (!p) -> g ;; idtoiso p = f.
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


(** ** Lemmas on pullbacks *)

Section on_pullbacks.

  Variable C : precategory.
  Variable hs : has_homsets C.
  Variables a b c d : C.
  Variables (f : a --> b) (g : a --> c) (k : b --> d) (h : c --> d).

(*
      f
   a----b
 g |    | k
   |    |
   c----d
     h 
    
 *)

  Variable sqr_comm : f ;; k = g ;; h.
  Variable Pb : limits.pullbacks.isPullback k h f g sqr_comm.


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
    Σ H : f ;; i ;; r = g ;; h, isPullback _ _ _ _ H.
  Proof.
    unshelve refine (tpair _ _ _ ).
    { eapply pathscomp0 ; [|apply sqr_comm].
      eapply pathscomp0. eapply pathsinv0; apply assoc.
      apply maponpaths. apply Hi.
    }
    apply (mk_isPullback _ ).    
    intros e s t HH.
    unshelve refine (tpair _ _ _ ).
    - unshelve refine (tpair _ _ _ ).
      set (T:= @map_into_Pb e).
      set (T':= T (s ;; inv_from_iso i) t).
      apply T'. { rewrite <- HH. rewrite <- assoc. apply maponpaths.
                  apply iso_inv_on_right. apply pathsinv0; assumption. }
                simpl.
      split.
      + assert (T1:= @Pb_map_commutes_1).
        eapply pathscomp0. apply assoc.
        rewrite T1.
        rewrite <- assoc.
        rewrite iso_after_iso_inv.
        apply id_right.
      + apply Pb_map_commutes_2.
    - intro t0.
      apply subtypeEquality.
      + intro. apply isapropdirprod; apply hs.
      + simpl.
        destruct t0 as [w [Ht1 Ht2]]; simpl in *.
        apply PullbackArrowUnique.
        * apply iso_inv_on_left.
          rewrite <- Ht1. apply assoc.
        * assumption.
Defined.    
 
End on_pullbacks.

Arguments map_into_Pb {_ _ _ _ _ _ _ _ _ } _ _ {_} _ _ _ .
Arguments map_into_Pb_unique {_ _ _ _ _ _ _ _ _} _ _ {_} _ _ _ _   .

Section Pullbacks_hSet.

(* TODO: does this already exist?

  If we had the standard pullback of hsets defined, this could be maybe better stated as the fact that P is a pullback if the map from P to the standard pullback is an iso. *)
Lemma isPullback_HSET {P A B C : HSET}
  (p1 : P --> A) (p2 : P --> B) (f : A --> C) (g : B --> C) (ep : p1 ;; f = p2 ;; g) 
  : (Π a b (e : f a = g b), ∃! ab, p1 ab = a × p2 ab = b)
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
  : (Π a b (e : f a = g b), ∃! ab, p1 ab = a × p2 ab = b).
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

  set (XR := isLimFunctor_is_pointwise_Lim C^op HSET has_homsets_HSET
            graphs.pullbacks.pushout_graph).
  set (XT1 := graphs.pullbacks.pullback_diagram _ f g).
  specialize (XR XT1).
  transparent assert
       (XH : (Π a : C^op,
        LimCone
          (colimits.diagram_pointwise C^op HSET has_homsets_HSET
             pullbacks.pushout_graph XT1 a))).

    { intro. apply LimConeHSET.  }
    specialize (XR XH).
    specialize (XR W). 

    set (XT := graphs.pullbacks.PullbCone _ _ _ _ p1 p2 e).
    specialize (XR XT).
    transparent assert (XTT : (isLimCone XT1 W XT)).
    { apply @graphs.pullbacks.equiv_isPullback_1.
      apply functor_category_has_homsets.
      assumption.
    }
    specialize (XR XTT c).

    
    intros S h k H.
    specialize (XR S).
    simpl in XR.
    transparent assert (
        HC :  (cone
              (colimits.diagram_pointwise C^op HSET has_homsets_HSET
                                               pushout_graph (pullback_diagram (preShv C) f g) c) S)).
    { use mk_cone.
      apply three_rec_dep; cbn.
(*      intro v.
      destruct v.*)
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
  - apply (total2_paths  (isotoid _ H (iso_from_Pullback_to_Pullback Pb Pb' ))). 
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
      eapply pathscomp0. apply (!assoc _ _ _ _ _ _ _ _ ).
      apply maponpaths. apply T.
  Defined.

  Definition map_to_1st_pb : A' --> A.
  Proof.
    unshelve refine (map_into_Pb H pb _ _ _ ).
    - exact (f';; inv_from_iso h).
    - exact g'.
    - eapply pathscomp0; [| apply H'].
      eapply pathscomp0; [ apply (!assoc _ _ _ _ _ _ _ _) |].
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
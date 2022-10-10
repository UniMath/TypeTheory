
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.All.
(* a few libraries need to be reloaded after “All”,
   to claim precedence on overloaded names *)
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.pullbacks.
Require Import UniMath.CategoryTheory.limits.pullbacks.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheory.

(** * Presheaf generalities *)

Arguments nat_trans_ax {C C'} {F F'} a {x x'} f.
Arguments nat_trans_comp {_ _ _ _ _} _ _.

Definition preShv C := functor_univalent_category C^op HSET_univalent_category.
(* Note: just like notation "PreShv" upstream, but univalent. TODO: unify these? *)

(* Notations for working with presheaves and natural transformations given as objects of [preShv C], since applying them directly requires type-casts before the coercions to [Funclass] trigger. *) 
Notation "#p F" := (functor_on_morphisms (F : functor _ _)) (at level 3)
  : cat.
Notation "P $p c" 
  := (((P : preShv _) : functor _ _) c : hSet)
  (at level 65) : cat.
Notation "α $nt x" 
  := (((α : preShv _ ⟦_ , _ ⟧) : nat_trans _ _) _ x)
  (at level 65) : cat.
(* The combinations of type-casts here are chosen as they’re what seems to work for as many given types as possible *)
(* TODO: consider these notations. Some such notations for applying presheaves is certainly good, but the choice of these symbols, levels, scopes, etc are fairly unconsidered/arbitrary for now. *)

Lemma functor_comp_pshf {C : category}
      { P : preShv C } {c : C} (x : P $p c)
      {c' : C} (f : c' --> c) {c'' : C} (f' : c'' --> c')
   : #p P (f' ;; f) x = #p P f' (#p P f x).
Proof.
  revert x. apply toforallpaths, (functor_comp P).
Defined.

Lemma functor_id_pshf {C : category}
      { P : preShv C } {c : C} (x : P $p c)
   : #p P (identity c) x = x.
Proof.
  revert x. apply toforallpaths, (functor_id P).
Defined.

Lemma nat_trans_ax_pshf {C : category}
      { P Q : preShv C } (α : P --> Q)
      {c : C} (x : P $p c) {c' : C} (f : c' --> c)
   : α $nt (#p P f x) = #p Q f (α $nt x).
Proof.
  revert x. apply toforallpaths, (nat_trans_ax α).
Defined.

Lemma nat_trans_eq_pointwise_pshf {C : category}
      {P Q : preShv C } {α β : P --> Q} (e : α = β)
      {c : C} (x : P $p c)
   : α $nt x = β $nt x.
Proof.
  revert x. apply toforallpaths, (nat_trans_eq_pointwise e).
Defined.

Lemma transportf_pshf {C : category}
    {P P' : preShv C} (e : P = P')
    {c : C} (x : P $p c)
  : transportf (fun Q => Q $p c) e x
  = (idtoiso e : _ --> _) $nt x.
Proof.
  destruct e; apply idpath.
Qed.

Lemma transportf_pshf' {C : category} (P : preShv C)
  {c c' : C} (e : c = c') (x : P $p c)
  : transportf (fun c => P $p c) e x
    = #p P (idtoiso (!e)) x.
Proof.
  destruct e. cbn.
  apply pathsinv0. apply functor_id_pshf.
Qed.

Lemma transportf_isotoid_pshf {C : category}
    {P P' : preShv C} (i : z_iso P P')
    {c : C} (x : P $p c)
  : transportf (fun Q => Q $p c)
      (isotoid _ (univalent_category_is_univalent (preShv C)) i) x
  = (i : _ --> _) $nt x.
Proof.
  etrans. apply transportf_pshf.
  refine (toforallpaths _ x).
  refine (toforallpaths _ c).
  apply maponpaths, maponpaths, idtoiso_isotoid.
Qed.

(** * Yoneda embedding *)

Notation "'Yo'" := (yoneda _ : functor _ (preShv _)).
Notation "'Yo^-1'" := (invweq (make_weq _ (yoneda_fully_faithful _ _ _ ))).

(* TODO: perhaps rename e.g. [yoneda_eq]? *)
Definition yy {C : category}
    {F : preShv C} {c : C}
  : F $p c ≃ _ ⟦ yoneda _ c, F⟧.
Proof.
  apply invweq.
  apply yoneda_weq.
Defined.

Lemma yy_natural {C : category} 
    (F : preShv C) (c : C) (A : F $p c) 
    c' (f : C⟦c', c⟧)
  : yy (#p F f A) = # (yoneda _ ) f ;; yy A.
Proof.
  apply (toforallpaths (is_natural_yoneda_iso_inv _ F _ _ f)).
Qed.

Lemma yy_comp_nat_trans {C : category}
      (F F' : preShv C) (p : _ ⟦F, F'⟧)
      A (v : F $p A)
  : yy v ;; p = yy (p $nt v).
Proof.
  apply nat_trans_eq.
  - apply homset_property.
  - intro c. simpl. 
    apply funextsec. intro f. cbn.
    apply nat_trans_ax_pshf.
Qed.

Lemma yoneda_postcompose {C : category} (P : preShv C)
  {y z : C} (α : P --> Yo y) (f : y --> z)
  {x:C} (p : P $p x)
  : (α $nt p) ;; f
    = (α ;; yoneda_morphisms _ _ _ f) $nt p.
Proof.
  apply idpath.
Defined.

Lemma transportf_yy {C : category}
      (F : preShv C) (c c' : C) (A : F $p c)
      (e : c = c')
  : yy (transportf (fun d => F $p d) e A) 
    = transportf (fun d => preShv C ⟦ yoneda _ d, F⟧) e (yy A).
Proof.
  induction e.
  apply idpath.
Defined.

(** * Pullbacks of sets and presheaves *)

Section Pullbacks_hSet.

(* TODO: does this already exist?

  If we had the standard pullback of hsets defined, this could be maybe better stated as the fact that P is a pullback if the map from P to the standard pullback is an iso. *)
Lemma isPullback_HSET {P A B C : HSET}
    (p1 : P --> A) (p2 : P --> B) (f : A --> C) (g : B --> C)
    (ep : p1 ;; f = p2 ;; g)
  : (∏ a b (e : f a = g b), ∃! ab, p1 ab = a × p2 ab = b)
  -> isPullback ep.
Proof.
  intros H X h k ehk.
  set (H_existence := fun a b e => pr1 (H a b e)).
  set (H_uniqueness
    := fun a b e x x' => base_paths _ _ (proofirrelevancecontr (H a b e) x x')).
  apply iscontraprop1.
  - apply invproofirrelevance.
    intros hk hk'.
    apply subtypePath. { intro. apply isapropdirprod; apply homset_property. }
    destruct hk as [hk [eh ek]], hk' as [hk' [eh' ek']]; simpl.
    apply funextsec; intro x.
    refine (H_uniqueness (h x) (k x) _ (_,,_) (_,,_));
      try split;
    revert x; apply toforallpaths; assumption.
  - use tpair. 
    + intros x. refine (pr1 (H_existence (h x) (k x) _)).
      apply (toforallpaths ehk).
    + simpl.
      split; apply funextsec; intro x.
      * apply (pr1 (pr2 (H_existence _ _ _))). 
      * apply (pr2 (pr2 (H_existence _ _ _))).
Qed.

(* TODO: unify with [isPullback_HSET]? *)
Lemma pullback_HSET_univprop_elements {P A B C : HSET}
    {p1 : HSET ⟦ P, A ⟧} {p2 : HSET ⟦ P, B ⟧}
    {f : HSET ⟦ A, C ⟧} {g : HSET ⟦ B, C ⟧}
    (ep : p1 ;; f = p2 ;; g)
    (pb : isPullback (*f g p1 p2*) ep)
  : (∏ a b (e : f a = g b), ∃! ab, p1 ab = a × p2 ab = b).
Proof.
  intros a b e.
  set (Pb := (make_Pullback _ pb)).
  apply iscontraprop1.
  - apply invproofirrelevance; intros [ab [ea eb]] [ab' [ea' eb']].
    apply subtypePath; simpl.
      intros x; apply isapropdirprod; apply setproperty.
    refine (@toforallpaths unitset _ _ _ _ tt).
    refine (MorphismsIntoPullbackEqual pb _ _ _ _ _ );
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
    (pb : isPullback (*f g p1 p2*) ep)
    (ab ab' : P : hSet)
    (e1 : p1 ab = p1 ab') (e2 : p2 ab = p2 ab')
  : ab = ab'.
Proof.
  set (temp := proofirrelevancecontr 
    (pullback_HSET_univprop_elements _ pb (p1 ab') (p2 ab')
        (toforallpaths ep ab'))).
  refine (maponpaths pr1 (temp (ab,, _) (ab',, _))).
  - split; assumption.
  - split; apply idpath.
Qed.


(* TODO: upstream this and the following lemma, and unify them with the converse implication about pullbacks. *)
Lemma square_commutes_preShv_to_pointwise {C : category}
    {X Y Z W : preShv C}
    {f : Y --> X} {g : Z --> X} {p1 : W --> Y} {p2 : W --> Z}
    (e : p1 ;; f = p2 ;; g)
    (c : C)
  : ((p1 : nat_trans _ _) c) ;; ((f : nat_trans _ _) c)
  = ((p2 : nat_trans _ _) c) ;; ((g : nat_trans _ _) c).
Proof.
  apply (nat_trans_eq_pointwise e).
Qed.

(* TODO: unify with the converse implication;
  perhaps also generalise to all functor categories?  *)
Lemma isPullback_preShv_to_pointwise {C : category}
    {X Y Z W : preShv C}
    {f : Y --> X} {g : Z --> X} {p1 : W --> Y} {p2 : W --> Z}
    {e : p1 ;; f = p2 ;; g} (pb : isPullback e)
    (c : C)
  : isPullback (square_commutes_preShv_to_pointwise e c).
Proof.
  set (XR := @isLimFunctor_is_pointwise_Lim C^op HSET
            pullback_graph).
  set (XT1 := pullback_diagram _ f g).
  specialize (XR XT1).
  transparent assert
       (XH : (∏ a : C^op,
        LimCone
          (@colimits.diagram_pointwise C^op HSET 
             pullback_graph XT1 a))).
    { intro. apply LimConeHSET.  }
    specialize (XR XH).
    specialize (XR W). 
    set (XT := PullbCone _ _ _ _ p1 p2 e).
    specialize (XR XT).
    transparent assert (XTT : (isLimCone XT1 W XT)).
    { apply @equiv_isPullback_1.
      exact pb.
    }
    specialize (XR XTT c).    
    intros S h k H.
    specialize (XR S).
    simpl in XR.
    transparent assert (HC
      :  (cone (@colimits.diagram_pointwise C^op HSET 
                    pullback_graph (pullback_diagram (preShv C) f g) c) S)).
    { use make_cone.
      apply three_rec_dep; cbn.
      - apply h.
      - simpl. apply (h ;; (pr1 f c)).
      - apply k.
      - use three_rec_dep; use three_rec_dep.
        + exact (empty_rect _ ).
        + intro. apply idpath.
        + exact (empty_rect _ ).
        + exact (empty_rect _ ).
        + exact (empty_rect _ ).
        + exact (empty_rect _ ).
        + exact (empty_rect _ ).
        + intro; apply (!H).
        + exact (empty_rect _ ).
    }
    specialize (XR HC).
    use tpair.
  - exists (pr1 (iscontrpr1 XR)).
    split.
    + apply (pr2 (pr1 XR) One).
    + apply (pr2 (pr1 XR) Three).
  - intro t.
    apply subtypePath.
    + intro. apply isapropdirprod; apply homset_property.
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


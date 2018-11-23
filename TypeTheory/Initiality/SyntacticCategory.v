(** This file defines the syntactic category of our toy type theory, and the logical structure on it.

As a matter of organisation: all concrete lemmas involving derivations should live upstream in [TypingLemmas]; this file should simply package them up into the appropriate categorical structure. *)

Require Import UniMath.All.

Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.Initiality.SplitTypeCat_Maps.
Require Import TypeTheory.Initiality.SplitTypeCat_Structure.
Require Import TypeTheory.Initiality.Syntax.
Require Import TypeTheory.Initiality.SyntaxLemmas.
Require Import TypeTheory.Initiality.Typing.
Require Import TypeTheory.Initiality.TypingLemmas.

Local Open Scope judgement.

Section Auxiliary.
 (* we’ll need some material here about quotients:
  particularly, [lemmas.setquotprpathsandR] from [PAdics], I guess? *)

  (* Upstream issues to possibly raise about [setquot]:
  - should [pr1] of [eqrel] coerce to [hrel], not directly to [Funclass]?
  - should [QuotientSet.setquotfun2] replace [setquotfun2]? *)

  (** Variant of [setquotuniv] with the [isaset] hypothesis separated out,
  for easier interactive use with [use], analogous to [setquotunivprop']. *)
  Definition setquotuniv' {X : UU} {R : hrel X} {Y : UU}
      (isaset_Y : isaset Y) (f : X -> Y) (f_respects_R : iscomprelfun R f)
    : setquot R -> Y.
  Proof.
    use (setquotuniv _ (_,,_)); assumption.
  Defined.

  (** TODO: is [setquot_rect], the general dependent universal property of [setquot], really not provided in the library somewhere?

  Here we put it together from [setquotuniv] (the non-dependent version) and [setquotunivprop] (the version for hprop-valued predicates). Unfortunately, that means it doesn’t compute, since [setquotunivprop] doesn’t.  With a bit more thought, could we give a version that computes nicely like [setquotuniv]? *)
  Definition setquot_rect_aux {X:UU} {R:eqrel X}
      (P : setquot R -> UU) (isaset_P : forall xx, isaset (P xx))
      (d : forall x:X, P (setquotpr R x))
      (d_respects_R : forall (x y:X) (r : R x y),
          transportf _ (iscompsetquotpr _ _ _ r) (d x) = d y)
    : ∑ (f : forall xx, P xx), forall x, f (setquotpr R x) = d x.
  Proof.
    transparent assert (f_nondep : (setquot R -> ∑ xx, P xx)).
    { use setquotuniv'.
      - apply isaset_total2; try assumption. apply isasetsetquot.
      - intros x. exact (_,, d x).
      - intros x y r. refine (total2_paths_f _ _). apply (d_respects_R _ _ r).
    }
    transparent assert (f_commutes : (forall xx, pr1 (f_nondep xx) = xx)).
    { use setquotunivprop'.
      - intros; apply isasetsetquot.
      - intros x. apply idpath.
    }
    exists (fun xx => transportf _ (f_commutes xx) (pr2 (f_nondep xx))).
    intros x. eapply pathscomp0. 2: { apply idpath_transportf. }
    apply maponpaths_2. apply isasetsetquot.
  Qed.

  Definition setquot_rect {X:UU} {R:eqrel X}
      (P : setquot R -> UU) (isaset_P : forall xx, isaset (P xx))
      (d : forall x:X, P (setquotpr R x))
      (d_respects_R : forall (x y:X) (r : R x y),
          transportf _ (iscompsetquotpr _ _ _ r) (d x) = d y)
    : forall xx, P xx
  := pr1 (setquot_rect_aux P isaset_P d d_respects_R).

  Definition setquot_comp {X:UU} {R:eqrel X}
      (P : setquot R -> UU) (isaset_P : forall xx, isaset (P xx))
      (d : forall x:X, P (setquotpr R x))
      (d_respects_R : forall (x y:X) (r : R x y),
          transportf _ (iscompsetquotpr _ _ _ r) (d x) = d y)
    : forall x, (setquot_rect P isaset_P d d_respects_R) (setquotpr R x) = d x
  := pr2 (setquot_rect_aux P isaset_P d d_respects_R).

End Auxiliary.

(** The construction of the syntactic type-category is rather trickier than one might hope, because of the need to quotient by some form of context equality — which, as ever when quotienting objects of a category, is quite fiddly.

For just the _category_ this is unnecessary, but for the _type-category_, it is unavoidable: types must be modulo equality, in order to form a presheaf, but then so must contexts, in order for context extension to be well-defined. 

At the same time, to get a _contextual_ type-category, one must stratify the objects: the flat contexts up to flat context equality form a type-category, but it will not in general contextual. *)

Section Stratified_Contexts.

(** The conventional version of contexts, as opposed to the “flat” notion we take as primitive. *)
  Fixpoint stratified_context_of_length (n:nat) : UU
  := match n with
    | O => unit
    | S n => (stratified_context_of_length n) × (ty_expr n)
  end.
  Arguments stratified_context_of_length : simpl nomatch.

  Definition empty_stratified_context
    := tt : stratified_context_of_length 0.
  Opaque empty_stratified_context.

  (** NOTE: [context_last] and [context_rest] are only defined for stratified
  contexts, so we don’t need to explicitly include it in their names. *)
  Definition context_last {n} (Γ : stratified_context_of_length (S n))
    : ty_expr n
  := pr2 Γ.

  Definition context_rest {n} (Γ : stratified_context_of_length (S n))
    : stratified_context_of_length n
  := pr1 Γ.
  
  Definition extend_stratified_context {n}
      (Γ : stratified_context_of_length n) (A : ty_expr n)
    : stratified_context_of_length (S n)
  := (Γ,,A).

  Fixpoint context_of_stratified_context
      {n} (Γ : stratified_context_of_length n) {struct n}
    : context_of_length n.
  Proof.
    destruct n as [ | n].
    - exact [::]%context.
    - exact (context_extend
               (context_of_stratified_context _ (context_rest Γ))
               (context_last Γ)).
  Defined.
  Global Arguments context_of_stratified_context : simpl nomatch.

  Coercion context_of_stratified_context
    : stratified_context_of_length >-> context_of_length.

End Stratified_Contexts.

Delimit Scope stratified_context_scope with strat_cxt.
Bind Scope stratified_context_scope with stratified_context_of_length.
Notation "[: :]"
  := (empty_stratified_context) (format "[: :]") : stratified_context_scope.
Notation "Γ ;; A" := (extend_stratified_context Γ A)
               (at level 50, left associativity) : stratified_context_scope. 
Notation "[: A ; .. ; Z :] " := (..([: :] ;; A) .. ;; Z)%strat_cxt
                                                 : stratified_context_scope.

Section Stratified_Context_Equality.

  Fixpoint derivation_cxteq
      {n} (Γ Δ : stratified_context_of_length n) {struct n}
    : UU.
  Proof.
    destruct n as [ | n].
    - exact unit.
    - exact (derivation_cxteq _ (context_rest Γ) (context_rest Δ)
             × [! context_rest Γ |- context_last Γ === context_last Δ !]).
  Defined.
  Arguments derivation_cxteq : simpl nomatch.

  Notation "[! |- Δ === Γ !]" := (derivation_cxteq Δ Γ)
                    (format "[!  |-  Δ  ===  Γ  !]") : judgement_scope.

  Fixpoint derive_flat_cxteq_from_cxteq
      {n} {Γ Δ : stratified_context_of_length n} {struct n}
    : [! |- Γ === Δ !] -> [! |f- Γ === Δ !].
  Proof.
    destruct n as [ | n].
    - intro; split; intros [].
    - destruct Γ as [Γ A], Δ as [Δ B]. 
      cbn; intros [? ?].
  (* TODO: how to stop [@context_of_stratified_context] unfolding here? *)
      apply derive_extend_flat_cxteq; fold @context_of_stratified_context;
        auto.
  (* TODO: need either eliminate flat-context assumption in [derive_extend_flat_cxteq],
     or else add assumption of (stratified) well-formedness of [Γ], [Δ] here:
      [ (d_Γ : [! |f- Γ !]) (d_Δ : [! |f- Δ !]) ] *)
  Admitted.

  Coercion derive_flat_cxteq_from_cxteq
    : derivation_cxteq >-> derivation_flat_cxteq.

  (* TODO: 
     - retool category definitions below to use stratified instead of flat
       context+equalities
   *)

End Stratified_Context_Equality.

Notation "[! |- Δ === Γ !]" := (derivation_cxteq Δ Γ)
                          (format "[!  |-  Δ  ===  Γ  !]") : judgement_scope.


Section Contexts_Modulo_Equality.

  (* TODO: replace [ |f- ] with [ |- ] here, once [ |- Γ ] defined above. *)
  Definition wellformed_context_of_length (n : nat) : UU
  := ∑ (Γ : context_of_length n), [! |f- Γ !].

  Coercion context_of_wellformed_context {n} (Γ : wellformed_context_of_length n)
    : context_of_length n
  := pr1 Γ.

  Definition derivation_wellformed_context
             {n} (Γ : wellformed_context_of_length n)
    : [! |f- Γ !]
  := pr2 Γ.
  Coercion derivation_wellformed_context
    : wellformed_context_of_length >-> derivation_flat_context.

  Definition derivable_cxteq_hrel {n} : hrel (wellformed_context_of_length n)
  := fun Γ Δ => ∥ derivation_flat_cxteq Γ Δ ∥.

  Lemma derivable_cxteq_is_eqrel n : iseqrel (@derivable_cxteq_hrel n).
  Proof.
    repeat split.
    - intros Γ Δ Θ; apply hinhfun2.
      exact (derive_flat_cxteq_trans Γ Δ Θ).
    - intros Γ; apply hinhpr.
      exact (derive_flat_cxteq_refl Γ).
    - intros Γ Δ; apply hinhfun.
      exact (derive_flat_cxteq_sym Γ Δ).
  Qed.

  Definition derivable_cxteq {n} : eqrel (wellformed_context_of_length n)
  := (_,,derivable_cxteq_is_eqrel n).

  Definition context_of_length_mod_eq n := setquot (@derivable_cxteq n).

  Definition context_mod_eq
  := ∑ (n:nat), context_of_length_mod_eq n.

  Local Definition length : context_mod_eq -> nat := pr1.

  Definition context_class {n} (Γ : wellformed_context_of_length n)
    : context_mod_eq
  := (n,, setquotpr _ Γ).
  Coercion context_class : wellformed_context_of_length >-> context_mod_eq.

  Definition context_representative (ΓΓ : context_mod_eq) : UU
  := ∑ (Γ : wellformed_context_of_length (length ΓΓ)), setquotpr _ Γ = (pr2 ΓΓ).
  Coercion context_representative : context_mod_eq >-> UU.

  Definition context_representative_as_context
      {ΓΓ} (Γ : context_representative ΓΓ)
    : wellformed_context_of_length (length ΓΓ)
  := pr1 Γ.
  Coercion context_representative_as_context
    : context_representative >-> wellformed_context_of_length.

  Lemma cxteq_context_representatives {ΓΓ : context_mod_eq} (Γ Γ' : ΓΓ)
    : ∥ derivation_flat_cxteq Γ Γ' ∥.
  Proof.
    refine (lemmas.setquotprpathsandR (derivable_cxteq) Γ Γ' _).
    exact (pr2 Γ @ ! pr2 Γ').
  Defined.

  Lemma take_context_representative
      (ΓΓ : context_mod_eq) {X:UU} (h_X : isaprop X)
      (f : context_representative ΓΓ -> X)
    : X.
  Proof.
    refine (factor_through_squash _ f _). { assumption. }
    destruct ΓΓ as [n ΓΓ]. generalize ΓΓ.
    apply setquotunivprop'.
    { intros; apply isapropishinh. }
    intros Γ; apply hinhpr. exists Γ; auto.
  Defined.

End Contexts_Modulo_Equality.

Section Context_Maps.
(** Definition of context maps, and basic auxiliary functions on them. *)

  (** Note: the truncation of the derivation part is mathematically redundant,
  since we will later quotient anyway.  However, it lets us get better
  computational behaviour on the map part, in compositions etc. *)
  Local Definition map (ΓΓ ΔΔ : context_mod_eq) : UU
    := ∑ (f : raw_context_map (length ΓΓ) (length ΔΔ)),
       ∀ (Γ : ΓΓ) (Δ : ΔΔ), ∥ [! |- f ::: Γ ---> Δ !] ∥.

  Definition raw_of_context_map {ΓΓ ΔΔ} (f : map ΓΓ ΔΔ) : raw_context_map _ _
  := pr1 f.
  Coercion raw_of_context_map : map >-> raw_context_map.

  Local Definition map_derivable {ΓΓ ΔΔ} (f : map ΓΓ ΔΔ)
    : ∀ (Γ : ΓΓ) (Δ : ΔΔ), ∥ [! |- f ::: Γ ---> Δ !] ∥
  := pr2 f.

  Local Definition mapeq_hrel {ΓΓ ΔΔ} (f g : map ΓΓ ΔΔ)
  := ∀ (Γ : ΓΓ) (Δ : ΔΔ), ∥ [! |- f === g ::: Γ ---> Δ !] ∥.

  Local Definition mapeq_is_eqrel (ΓΓ ΔΔ : context_mod_eq)
    : iseqrel (@mapeq_hrel ΓΓ ΔΔ).
  Admitted.

  Local Definition mapeq_eqrel ΓΓ ΔΔ : eqrel (map ΓΓ ΔΔ)
  := (_,,mapeq_is_eqrel ΓΓ ΔΔ).

  Local Definition map_mod_eq (ΓΓ ΔΔ : context_mod_eq) : UU
  := setquot (mapeq_eqrel ΓΓ ΔΔ).

  Local Definition map_representative {ΓΓ ΔΔ} (ff : map_mod_eq ΓΓ ΔΔ) : UU
  := ∑ (f : map ΓΓ ΔΔ), setquotpr _ f = ff.
  Coercion map_representative : map_mod_eq >-> UU.

  Local Definition map_representative_as_map
      {ΓΓ ΔΔ} {ff : map_mod_eq ΓΓ ΔΔ} (f : map_representative ff)
    : map ΓΓ ΔΔ
  := pr1 f.
  Coercion map_representative_as_map : map_representative >-> map.

  (* TODO: consider naming of this and other analogous lemmas *)

  (** Generally useful lemma: while the definition of map well-typedness is 
  with respect to _all_ contexts representing of its source/target, it’s enough
  to show it with respect to _some_ such representatives. *)
  Lemma map_for_some_rep
      {ΓΓ ΔΔ} (f : raw_context_map (length ΓΓ) (length ΔΔ))
    : ∥ ∑ (Γ:ΓΓ) (Δ:ΔΔ), [! |- f ::: Γ ---> Δ !] ∥
    -> ∀ (Γ:ΓΓ) (Δ:ΔΔ), ∥ [! |- f ::: Γ ---> Δ !] ∥.
  Proof.
    intros H Γ Δ.
    apply (squash_to_prop H). { apply isapropishinh. }
    intros [Γ' [Δ' d_f]].
    apply (squash_to_prop (cxteq_context_representatives Γ Γ')).
    { apply isapropishinh. }
    intros e_Γ.
    apply (squash_to_prop (cxteq_context_representatives Δ Δ')).
    { apply isapropishinh. }
    intros e_Δ.
    apply hinhpr.
    admit. (* TODO: show in [TypingLemmas] that context maps respect flat equality in source + target *)
  Admitted.

  Lemma mapeq_for_some_rep
      {ΓΓ ΔΔ} (f g : raw_context_map (length ΓΓ) (length ΔΔ))
    : ∥ ∑ (Γ:ΓΓ) (Δ:ΔΔ), [! |- f === g ::: Γ ---> Δ !] ∥
    -> ∀ (Γ:ΓΓ) (Δ:ΔΔ), ∥ [! |- f === g ::: Γ ---> Δ !] ∥.
  Proof.
    intros H Γ Δ.
    apply (squash_to_prop H). { apply isapropishinh. }
    intros [Γ' [Δ' d_f]].
    apply (squash_to_prop (cxteq_context_representatives Γ Γ')).
    { apply isapropishinh. }
    intros e_Γ.
    apply (squash_to_prop (cxteq_context_representatives Δ Δ')).
    { apply isapropishinh. }
    intros e_Δ.
    apply hinhpr.
    admit. (* TODO: show in [TypingLemmas] that context map equality respects flat equality in source + target *)
  Admitted.

End Context_Maps.

Section Context_Map_Operations.

  Local Definition idmap ΓΓ : map_mod_eq ΓΓ ΓΓ.
  Proof.
    refine (setquotpr _ _).
    exists (idmap_raw_context _).
    apply map_for_some_rep.
    apply (take_context_representative ΓΓ). { apply isapropishinh. }
    intros Γ. apply hinhpr. exists Γ; exists Γ.
    use derive_idmap; apply derivation_wellformed_context.
  Defined.

  Local Definition compose
      {ΓΓ ΔΔ ΘΘ} (ff : map_mod_eq ΓΓ ΔΔ) (gg : map_mod_eq ΔΔ ΘΘ)
    : map_mod_eq ΓΓ ΘΘ.
  Proof.
    revert ff gg. use QuotientSet.setquotfun2; [ | split].
    - (* construction of the composite *)
      intros f g. exists (comp_raw_context f g); intros Γ Θ.
      (* TODO: perhaps try to condense and [abstract] the following. *)
      apply (take_context_representative ΔΔ). { apply isapropishinh. }
      intros Δ.
      apply (squash_to_prop (map_derivable f Γ Δ)). { apply isapropishinh. }
      intros d_f.
      apply (squash_to_prop (map_derivable g Δ Θ)). { apply isapropishinh. }
      intros d_g.
      apply hinhpr. refine (derive_comp d_f _);
        auto using derivation_wellformed_context.
    - (* respecting equality in [f] *)
      intros f f' g e_f Γ Θ. cbn.
      apply (take_context_representative ΔΔ). { apply isapropishinh. } intros Δ.
      specialize (e_f Γ Δ); revert e_f.
      apply factor_through_squash. { apply isapropishinh. } intros e_f.
      apply (squash_to_prop (map_derivable f Γ Δ)). { apply isapropishinh. }
      intros d_f.
      apply (squash_to_prop (map_derivable f' Γ Δ)). { apply isapropishinh. }
      intros d_f'.
      apply (squash_to_prop (map_derivable g Δ Θ)). { apply isapropishinh. }
      intros d_g.
      apply hinhpr; simple refine (comp_raw_context_cong_l _ _ _ e_f _);
        auto using derivation_wellformed_context.
    - (* respecting equality in [g] *)
      cbn; intros f g g' e_g Γ Θ.
      apply (take_context_representative ΔΔ). { apply isapropishinh. }
      intros Δ.
      specialize (e_g Δ Θ); revert e_g.
      apply factor_through_squash. { apply isapropishinh. } intros e_g.
      apply (squash_to_prop (map_derivable f Γ Δ)). { apply isapropishinh. }
      intros d_f.
      apply hinhpr; simple refine (comp_raw_context_cong_r _ _ e_g);
        auto using derivation_wellformed_context.
  Defined.
  
  (* TODO: “empty” and “extension” context maps. *)

End Context_Map_Operations.

Section Category.

  (* TODO: lemmas on associativity etc.  Should be immediate from the
  similar lemmas on raw ones in [SyntaxLemmas]. *)

  Lemma idmap_left {ΓΓ ΔΔ : context_mod_eq} (f : map_mod_eq ΓΓ ΔΔ)
    : compose (idmap _) f = f.
  Proof.
    revert f. refine (setquotunivprop' _ _ _). { intro; apply isasetsetquot. }
    intros f. cbn.
    apply maponpaths. apply subtypeEquality_prop.
    apply id_left_raw_context.
  Qed.

  Lemma idmap_right {ΓΓ ΔΔ : context_mod_eq} (f : map_mod_eq ΓΓ ΔΔ)
    : compose f (idmap _) = f.
  Proof.
    revert f. refine (setquotunivprop' _ _ _). { intro; apply isasetsetquot. }
    intros f. cbn.
    apply maponpaths. apply subtypeEquality_prop.
    apply id_right_raw_context.
  Qed.

  Lemma compose_assoc {ΓΓ0 ΓΓ1 ΓΓ2 ΓΓ3 : context_mod_eq} (f : map_mod_eq ΓΓ0 ΓΓ1)
    (g : map_mod_eq ΓΓ1 ΓΓ2) (h : map_mod_eq ΓΓ2 ΓΓ3)
    : compose f (compose g h) = compose (compose f g) h.
  Proof.
    revert f. apply setquotunivprop'. { intro; apply isasetsetquot. } intros f.
    revert g. apply setquotunivprop'. { intro; apply isasetsetquot. } intros g.
    revert h. apply setquotunivprop'. { intro; apply isasetsetquot. } intros h.
    cbn.
    apply maponpaths. apply subtypeEquality_prop.
    cbn. apply pathsinv0, assoc_raw_context.
  Qed.
  
  (* TODO: issue to raise in UniMath: [mk_category] is constructor for a _univalent_ category! *)
  Definition syntactic_category : category.
  Proof.
    use tpair.
    - use mk_precategory_one_assoc.
     + use ((context_mod_eq,,map_mod_eq),,_).
       exists idmap.
       intros Γ Δ Θ.
       apply compose.
     + repeat split.
       * intros ΓΓ ΔΔ f.
         exact (idmap_left f).
       * intros ΓΓ ΔΔ f.
         exact (idmap_right f).
       * intros ΓΓ0 ΓΓ1 ΓΓ2 ΓΓ3 f g h.
         apply (compose_assoc f g h).
    - intros ? ?; apply isasetsetquot.
  Defined.

End Category.

Section Split_Typecat.

  Definition syntactic_typecat : split_typecat.
  Admitted.

End Split_Typecat.

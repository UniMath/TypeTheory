(** This file defines the syntactic category of our toy type theory, and the logical structure on it.

As a matter of organisation: all concrete lemmas involving derivations should live upstream in [TypingLemmas]; this file should simply package them up into the appropriate categorical structure. *)

Require Import UniMath.All.

Require Import TypeTheory.Auxiliary.Auxiliary.
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

  (** [setquot_rect]: the general dependent universal property of [setquot].
  To give a function into a dependent family of sets over the quotient, it suffices to construct the function on the domain of the quotient, and show your construction respects equivalence.

  Unfortunately, this currently doesn’t compute; the intended “computation” is given as a lemma, [setquot_comp.] *)
  (* TODO: with a bit more thought, could one give a version that computes nicely, like [setquotuniv]? *)
  (* TODO: possible alternative name [setquotuniv_dep] *)
  Definition setquot_rect {X:UU} {R:eqrel X}
      (P : setquot R -> UU) (isaset_P : forall xx, isaset (P xx))
      (d : forall x:X, P (setquotpr R x))
      (d_respects_R : forall (x y:X) (r : R x y),
          transportf _ (iscompsetquotpr _ _ _ r) (d x) = d y)
    : forall xx, P xx.
  Proof.
    intros xx.
    transparent assert (f : (xx -> P xx)).
    { intros x. refine (transportf _ _ (d (pr1 x))). apply setquotl0. }
    apply (pr1image f).
    apply (squash_to_prop (eqax0 (pr2 xx))).
    2: { apply prtoimage. }
    apply invproofirrelevance. intros [y Hy] [y' Hy'].
    apply subtypeEquality. { intro; apply isapropishinh. } simpl.
    apply (squash_to_prop Hy). { apply isaset_P. }
    clear Hy; intros [x e_xy].
    apply (squash_to_prop Hy'). { apply isaset_P. }
    clear Hy'; intros [x' e_xy'].
    destruct e_xy, e_xy'. subst f; simpl.
    assert (R_xx' : R (pr1 x) (pr1 x')).
    { apply (eqax2 (pr2 xx)); [apply x | apply x']. }
    rewrite <- (d_respects_R _ _ R_xx').
    eapply pathscomp0. 2: { apply pathsinv0, transport_f_f. }
    (* TODO: raise issue in [UniMath], several redundant identical lemmas: [app], [transportf_paths], [transportf_ext].
     One of these is certainly enough (and in any case, all are instances of [maponpaths_2]). *)
    apply maponpaths_2, isasetsetquot.
  Defined.

  Definition setquot_comp {X:UU} {R:eqrel X}
      (P : setquot R -> UU) (isaset_P : forall xx, isaset (P xx))
      (d : forall x:X, P (setquotpr R x))
      (d_respects_R : forall (x y:X) (r : R x y),
          transportf _ (iscompsetquotpr _ _ _ r) (d x) = d y)
    : forall x, (setquot_rect P isaset_P d d_respects_R) (setquotpr R x) = d x.
  Proof.
    intros x. unfold setquot_rect; simpl.
    eapply pathscomp0. 2: { apply idpath_transportf. }
    apply maponpaths_2, isasetsetquot.
  Defined.

  Opaque setquot_rect setquot_comp.

  Definition representative {X:UU} {R:eqrel X} (x:setquot R) : UU
  := hfiber (setquotpr R) x.

  (** Make [simpl] unfold [ (f ∘ g) x ] but not [ f ∘ g ]: *)
  Arguments funcomp {_ _ _} _ _ _/.
  (* TODO: see if upstreaming this helps other places where [unfold funcomp] is given explicitly *)

  Definition take_representative_with_isaset
      {X:UU} {R:eqrel X} (xx:setquot R)
      {Y:UU} (H_Y : isaset Y)
      (f : representative xx -> Y) (H_f : forall xx xx', f xx = f xx')
    : Y.
  Proof.
    simple refine (setquot_rect (fun xx' => (xx' = xx -> Y)) _ _ _ xx (idpath _)).
    - intros xx'. repeat (apply impred_isaset; intros); assumption.
    - intros x e. exact (f (x,, e)).
    - intros x y r.
      eapply pathscomp0. { use transportf_fun. }
      apply funextfun; intros e. simpl.
      apply H_f.
  Defined.

  Lemma take_representative_comp
      {X:UU} {R:eqrel X} (x:X)
      {Y:UU} (H_Y : isaset Y)
      (f : representative (setquotpr R x) -> Y) (H_f : forall xx xx', f xx = f xx')
    : take_representative_with_isaset (setquotpr R x) H_Y f H_f = f (x,,idpath _).
  Proof.
    unfold take_representative_with_isaset.
    eapply pathscomp0. { refine (toforallpaths _ _ _ _ _).  use setquot_comp. }
    apply idpath.
  Qed.

  Definition take_representative_with_hSet
      {X:UU} {R:eqrel X} (xx:setquot R)
      (Y:hSet)
      (f : representative xx -> Y) (H_f : forall xx xx', f xx = f xx')
    : Y.
  Proof.
    use take_representative_with_isaset; auto; apply setproperty.
  Defined.

  (* TODO: perhaps add [take_representative_with_isaprop], […with_hProp] also *)
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
      [ (d_Γ : [! |- Γ !]) (d_Δ : [! |- Δ !]) ] *)
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
  Identity Coercion id_context_of_length_mod_eq 
    : context_of_length_mod_eq >-> setquot.

  Definition context_mod_eq
  := ∑ (n:nat), context_of_length_mod_eq n.

  Definition mk_context_mod_eq {n} (ΓΓ : context_of_length_mod_eq n)
    : context_mod_eq
  := (n,,ΓΓ).
  Coercion mk_context_mod_eq : context_of_length_mod_eq >-> context_mod_eq.

  Local Definition length : context_mod_eq -> nat := pr1.
  Coercion length : context_mod_eq >-> nat.
  Add Printing Coercion length.

  Definition pr2_context_mod_eq (ΓΓ : context_mod_eq)
    : context_of_length_mod_eq ΓΓ
  := pr2 ΓΓ.
  Coercion pr2_context_mod_eq : context_mod_eq >-> context_of_length_mod_eq.

  Definition context_class {n} (Γ : wellformed_context_of_length n)
    : context_mod_eq
  := (n,, setquotpr _ Γ).
  Coercion context_class : wellformed_context_of_length >-> context_mod_eq.

  Definition context_representative (ΓΓ : context_mod_eq) : UU
  := ∑ (Γ : wellformed_context_of_length (length ΓΓ)), setquotpr _ Γ = (pr2 ΓΓ).

  Definition context_representative_as_context
      {ΓΓ} (Γ : context_representative ΓΓ)
    : wellformed_context_of_length (length ΓΓ)
  := pr1 Γ.
  Coercion context_representative_as_context
    : context_representative >-> wellformed_context_of_length.

  Definition context_as_context_representative
      {n} (Γ : wellformed_context_of_length n)
    : context_representative Γ
  := (_,,idpath _).
  Coercion context_as_context_representative
    : wellformed_context_of_length >-> context_representative.

  Lemma cxteq_context_representatives
      {ΓΓ : context_mod_eq} (Γ Γ' : context_representative ΓΓ)
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

  (* TODO: will probably have to refactor the following to depend directly on [context_of_length_mod_eq], as with [type_over] etc below. *)

  (** Note: the truncation of the derivation part is mathematically redundant,
  since we will later quotient anyway.  However, it lets us get better
  computational behaviour on the map part, in compositions etc. *)
  (* NOTE: does it really? *)
  Local Definition map (ΓΓ ΔΔ : context_mod_eq) : UU
    := ∑ (f : raw_context_map ΓΓ ΔΔ),
       ∀ (Γ : context_representative ΓΓ) (Δ : context_representative ΔΔ),
         ∥ [! |- f ::: Γ ---> Δ !] ∥.

  Definition raw_of_context_map {ΓΓ ΔΔ} (f : map ΓΓ ΔΔ) : raw_context_map _ _
  := pr1 f.
  Coercion raw_of_context_map : map >-> raw_context_map.

  Local Definition map_derivable {ΓΓ ΔΔ} (f : map ΓΓ ΔΔ)
    : ∀ (Γ : context_representative ΓΓ) (Δ : context_representative ΔΔ),
      ∥ [! |- f ::: Γ ---> Δ !] ∥
  := pr2 f.

  Local Definition mapeq_hrel {ΓΓ ΔΔ} (f g : map ΓΓ ΔΔ)
  := ∀ (Γ : context_representative ΓΓ) (Δ : context_representative ΔΔ),
      ∥ [! |- f === g ::: Γ ---> Δ !] ∥.

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
      {ΓΓ ΔΔ : context_mod_eq} (f : raw_context_map ΓΓ ΔΔ)
    : (∃ (Γ:context_representative ΓΓ) (Δ:context_representative ΔΔ),
          [! |- f ::: Γ ---> Δ !])
    -> ∀ (Γ:context_representative ΓΓ) (Δ:context_representative ΔΔ),
        ∥ [! |- f ::: Γ ---> Δ !] ∥.
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
      {ΓΓ ΔΔ : context_mod_eq} (f g : raw_context_map ΓΓ ΔΔ)
    : (∃ (Γ:context_representative ΓΓ) (Δ:context_representative ΔΔ),
        [! |- f === g ::: Γ ---> Δ !])
    -> ∀ (Γ:context_representative ΓΓ) (Δ:context_representative ΔΔ),
        ∥ [! |- f === g ::: Γ ---> Δ !] ∥.
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

Section Syntactic_Types.

  (** NOTE: it is slightly subtle, but crucial, that the following definitions 
  depend directly on [context_of_length_mod_eq] not on [context_mod_eq]: it is 
  [context_of_length_mod_eq] that is directly a [setquot], and so we need this
  dependence in order to apply the dependent universal property of [setquot],
  i.e. for constructing functions whose first argument is a context and whose
  later arguments depend on the context, e.g. context extension or any of the
  logical structure on the syntactic category. *)

  Definition is_type_over {n} (ΓΓ : context_of_length_mod_eq n)
     (A : ty_expr n) : UU
  := ∀ Γ : context_representative (n,,ΓΓ), ∥ [! Γ |- A !] ∥.

  Definition id_is_type_over {n}
    {ΓΓ : context_of_length_mod_eq n} {A : ty_expr n} (d_A : is_type_over ΓΓ A)
  := d_A : ∏ Γ, _.
  Coercion id_is_type_over : is_type_over >-> Funclass.

  Local Definition type_over {n} (ΓΓ : context_of_length_mod_eq n)
  := ∑ A, is_type_over ΓΓ A.

  Coercion type_of_type_over {n} {ΓΓ : _ n} : type_over ΓΓ -> ty_expr ΓΓ := pr1.

  Definition type_over_is_type {n} {ΓΓ : _ n} (A : type_over ΓΓ)
  := pr2 A : is_type_over ΓΓ A.
  Coercion type_over_is_type : type_over >-> is_type_over.

  Definition typeeq_hrel {n} {ΓΓ : _ n} : hrel (type_over ΓΓ)
  := fun A B => ∀ Γ : context_representative ΓΓ, ∥ [! Γ |- A === B !] ∥.

  Proposition typeeq_is_eqrel {n} (ΓΓ : _ n) : iseqrel (@typeeq_hrel n ΓΓ).
  Proof.
    repeat split.
    - intros A B C e_AB e_BC Γ.
      apply (squash_to_prop (A Γ)). { apply isapropishinh. } intros d_A.
      apply (squash_to_prop (B Γ)). { apply isapropishinh. } intros d_B.
      apply (squash_to_prop (C Γ)). { apply isapropishinh. } intros d_C.
      apply (squash_to_prop (e_AB Γ)). { apply isapropishinh. } 
      clear e_AB; intros e_AB.
      apply (squash_to_prop (e_BC Γ)). { apply isapropishinh. } 
      clear e_BC; intros e_BC.
      now apply hinhpr, (derive_tyeq_trans Γ _ B).
    - intros A Γ.
      apply (squash_to_prop (A Γ)). { apply isapropishinh. } intros d_A.
      now apply hinhpr, derive_tyeq_refl.
    - intros A B e_AB Γ.
      apply (squash_to_prop (e_AB Γ)). { apply isapropishinh. } 
      clear e_AB; intros e_AB.
      now apply hinhpr, derive_tyeq_sym.
  Defined.

  Definition typeeq_eqrel {n} {ΓΓ : _ n} : eqrel (type_over ΓΓ)
  := (_,, typeeq_is_eqrel ΓΓ).

  Local Definition type_mod_eq {n} (ΓΓ : context_of_length_mod_eq n) : UU
  := setquot (@typeeq_eqrel _ ΓΓ).

  Local Definition type_representative {n} {ΓΓ : _ n} (AA : type_mod_eq ΓΓ) : UU
  := ∑ (A : type_over ΓΓ), setquotpr _ A = AA.
  Coercion type_representative : type_mod_eq >-> UU.

  Local Definition type_representative_as_type
      {n} {ΓΓ : _ n} {AA : type_mod_eq ΓΓ} (A : type_representative AA)
  := pr1 A : type_over ΓΓ.
  Coercion type_representative_as_type : type_representative >-> type_over.

  (* TODO: generalise to general “representatives” *)
  Lemma typeeq_type_representatives
      {n} {ΓΓ : _ n} {AA : type_mod_eq ΓΓ} (A A' : type_representative AA)
    : typeeq_eqrel A A'.
  Proof.
    refine (lemmas.setquotprpathsandR typeeq_eqrel A A' _).
    exact (pr2 A @ ! pr2 A').
  Defined.

  Lemma type_for_some_rep
      {ΓΓ : context_mod_eq} (A : ty_expr ΓΓ)
    : (∃ (Γ:context_representative ΓΓ), [! Γ |- A !])
    -> is_type_over ΓΓ A.
  Proof.
    intros H Γ.
    apply (squash_to_prop H). { apply isapropishinh. }
    intros [Γ' d_A].
    apply (squash_to_prop (cxteq_context_representatives Γ Γ')).
    { apply isapropishinh. } intros e_Γ.
    apply hinhpr.
    apply (derive_ty_conv_cxteq Γ' Γ); auto.
    exact (derive_flat_cxteq_sym Γ Γ' e_Γ).
  Qed.

  Lemma typeeq_for_some_rep
      {ΓΓ : context_mod_eq} (A B : type_over ΓΓ)
    : (∃ (Γ:context_representative ΓΓ), [! Γ |- A === B !])
    -> typeeq_hrel A B.
  Proof.
    intros H Γ.
    apply (squash_to_prop H). { apply isapropishinh. }
    intros [Γ' d_AB].
    apply (squash_to_prop (cxteq_context_representatives Γ Γ')).
    { apply isapropishinh. } intros e_Γ.
    apply hinhpr.
    apply (derive_tyeq_conv_cxteq Γ' Γ); auto.
    exact (derive_flat_cxteq_sym Γ Γ' e_Γ).
  Qed.

End Syntactic_Types.

Section Split_Typecat.

  Definition syntactic_typecat_structure : typecat_structure syntactic_category.
  Proof.
    repeat use tpair.
    - (* define the types *)
      intros ΓΓ; cbn in ΓΓ. exact (type_mod_eq ΓΓ).
    - (* context extension *)
      (* TODO: abstract this out *)
      intros ΓΓ AA; cbn in ΓΓ, AA.
      exists (S (length ΓΓ)).
      use (take_representative_with_isaset ΓΓ); try apply isasetsetquot;
        change (representative ΓΓ) with (context_representative ΓΓ).
      + intros Γ.
        use (take_representative_with_isaset AA); try apply isasetsetquot;
          change (representative AA) with (type_representative AA).
    (* TODO: make specialisations of [take_representative] to avoid these [change]s? *)
        * intros A.
          apply setquotpr; exists (Γ;;A)%context.
          admit. (* TODO: should be [exact (A Γ)], but need to either truncate the cxt derivation in defs of objects, or un-truncate the type derivation in def of types. *)
        * intros A A'. simpl.
          apply iscompsetquotpr. cbn.
          apply (squash_to_prop (typeeq_type_representatives A A' Γ)).
          { apply isapropishinh. }
          intros e_AA'. apply hinhpr, derive_extend_flat_cxteq; try apply (pr1 Γ).
          -- exact (derive_flat_cxteq_refl (pr1 Γ)).
          -- exact e_AA'.
      + intros Γ Γ'. simpl.
        revert AA.
        use setquotunivprop'. { intros; apply isasetsetquot. } intros A.
        eapply pathscomp0. { apply take_representative_comp. }
        eapply pathscomp0. 2: { apply pathsinv0, take_representative_comp. }
        apply iscompsetquotpr. cbn.
        apply (squash_to_prop (A Γ)). { apply isapropishinh. } intros d_A.
        apply (squash_to_prop (cxteq_context_representatives Γ Γ')).
        { apply isapropishinh. } intros e_ΓΓ'.
        apply hinhpr, derive_extend_flat_cxteq; auto using derive_tyeq_refl.
        * apply (pr1 Γ).
        * apply (pr1 Γ').
    - (* dependent projection *)
      admit.
  Admitted.

  Lemma is_split_syntactic_typecat_structure
    : is_split_typecat syntactic_typecat_structure.
  Proof.
  Admitted.

  Definition syntactic_typecat : split_typecat
  := ((syntactic_category,, syntactic_typecat_structure),,
                                          is_split_syntactic_typecat_structure).

End Split_Typecat.

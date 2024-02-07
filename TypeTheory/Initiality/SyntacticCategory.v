(** This file defines the syntactic category of our toy type theory, and the logical structure on it.

As a matter of organisation: all concrete lemmas involving derivations should live upstream in [TypingLemmas]; this file should simply package them up into the appropriate categorical structure. *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Graphs.Terminal.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheory.
Require Import TypeTheory.Auxiliary.Partial.
Require Import TypeTheory.Auxiliary.SetQuotients.
Require Import TypeTheory.TypeCat.TypeCat.
Require Import TypeTheory.TypeCat.General.
Require Import TypeTheory.TypeCat.Contextual.
Require Import TypeTheory.Initiality.Syntax.
Require Import TypeTheory.Initiality.SyntaxLemmas.
Require Import TypeTheory.Initiality.Typing.
Require Import TypeTheory.Initiality.TypingLemmas.

Local Open Scope judgement.

Section Auxiliary.

(** Useful for getting computation on partially complete definitions (like how the [admit] tactic used to behave).
  BUT: keep commented out when not needed, so as not to have inconsistency lying around. *)
(*
  Lemma temp_admit {X} : X. Admitted.
*)

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
  contexts, so we don’t explicitly include “stratified” in their names. *)
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
  Global Arguments context_of_stratified_context : simpl never.
  (* TODO: this seems to often unfold too much.  Why??
   A workaround for now: manual folding, [fold @context_of_stratified_context]. *)

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

Local Open Scope stratified_context_scope.

Section Stratified_Wellformed_Contexts.

  Fixpoint derivation_strat_cxt
      {n} (Γ : stratified_context_of_length n) {struct n}
    : UU.
  Proof.
    destruct n as [ | n].
    - exact unit.
    - exact (derivation_strat_cxt _ (context_rest Γ)
             × [! context_rest Γ |- context_last Γ !]).
  Defined.
  Arguments derivation_strat_cxt : simpl nomatch.

  Notation "[! |- Γ !]" := (derivation_strat_cxt Γ)
                    (format "[!  |-  Γ  !]") : judgement_scope.

  Definition derive_empty_stratified_context : [! |- [::] !] := tt.

  Definition derive_extend_stratified_context
      {n} {Γ : stratified_context_of_length n} {A : ty_expr Γ}
      (d_Γ : [! |- Γ !]) (d_A : [! Γ |- A !])
    : [! |- Γ;;A !]
  := (d_Γ,,d_A).

  Fixpoint derive_flat_cxt_from_strat
      {n} {Γ : stratified_context_of_length n} {struct n}
    : [! |- Γ !] -> [! |f- Γ !].
  Proof.
    destruct n as [ | n].
    - intro; intros [].
    - destruct Γ as [Γ A]. intros [d_Γ d_A].
      exact (derive_flat_extend_context
               (derive_flat_cxt_from_strat _ _ d_Γ) d_A).
  Defined.

  Coercion derive_flat_cxt_from_strat
    : derivation_strat_cxt >-> derivation_flat_context.
  (* TODO: rename a bit to be more consistent with [_cxt] vs [_context]. *)

End Stratified_Wellformed_Contexts.

Notation "[! |- Γ !]" := (derivation_strat_cxt Γ)
                    (format "[!  |-  Γ  !]") : judgement_scope.

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
      {n} {Γ Δ : stratified_context_of_length n}
      (d_Γ : [! |- Γ !]) (d_Δ : [! |- Δ !]) {struct n}
    : [! |- Γ === Δ !] -> [! |f- Γ === Δ !].
  Proof.
    destruct n as [ | n].
    - intro; split; intros [].
    - destruct Γ as [Γ A], Δ as [Δ B], d_Γ as [? ?], d_Δ as [? ?].
      cbn; intros [? ?].
  (* TODO: how to stop [@context_of_stratified_context] unfolding here? *)
      apply derive_extend_flat_cxteq; fold @context_of_stratified_context;
        auto using derive_flat_cxt_from_strat.
  Defined.

  Coercion derive_flat_cxteq_from_cxteq
    : derivation_cxteq >-> derivation_flat_cxteq.

End Stratified_Context_Equality.

Notation "[! |- Δ === Γ !]" := (derivation_cxteq Δ Γ)
                          (format "[!  |-  Δ  ===  Γ  !]") : judgement_scope.


Section Contexts_Modulo_Equality.

  Definition wellformed_context_of_length (n : nat) : UU
  := ∑ (Γ : stratified_context_of_length n), ∥ [! |- Γ !] ∥.

  Coercion context_of_wellformed_context {n} (Γ : wellformed_context_of_length n)
    : stratified_context_of_length n
  := pr1 Γ.

  Definition context_derivable
      {n} (Γ : wellformed_context_of_length n)
  := pr2 Γ  : ∥ [! |- Γ !] ∥.
  Coercion context_derivable
    : wellformed_context_of_length >-> hProptoType.

  Definition context_derivable'
      {n} (Γ : wellformed_context_of_length n)
  := pr2 Γ  : hProptoType (∥ [! |- Γ !] ∥).
  Coercion context_derivable'
    : wellformed_context_of_length >-> hProptoType.
  (* NOTE: this is needed since [ ∥ _ ∥ ] sometimes desugars to [ pr1hSet … ] and sometimes to [ hProptoType … ]. *)

  Definition empty_wellformed_context_of_length : wellformed_context_of_length 0.
  Proof.
    exists tt.
    apply hinhpr.
    exact tt.
  Defined.

  Definition derivable_cxteq_hrel {n} : hrel (wellformed_context_of_length n)
  := fun Γ Δ => ∥ derivation_flat_cxteq Γ Δ ∥.

  Lemma derivable_cxteq_is_eqrel n : iseqrel (@derivable_cxteq_hrel n).
  Proof.
    repeat split.
    - intros Γ Δ Θ.
      refine (hinhfun5 _ Γ Δ Θ); intros.
      eauto using derive_flat_cxteq_trans, derive_flat_cxt_from_strat.
    - intros Γ. refine (hinhfun _ Γ).
      exact derive_flat_cxteq_refl.
    - intros Γ Δ.
      refine (hinhfun3 _ Γ Δ); intros.
      eauto using derive_flat_cxteq_sym, derive_flat_cxt_from_strat.
  Qed.

  Definition derivable_cxteq {n} : eqrel (wellformed_context_of_length n)
  := (_,,derivable_cxteq_is_eqrel n).

  Definition context_of_length_mod_eq n := setquot (@derivable_cxteq n).
  Identity Coercion id_context_of_length_mod_eq
    : context_of_length_mod_eq >-> setquot.

  Definition context_mod_eq
  := ∑ (n:nat), context_of_length_mod_eq n.

  Definition make_context_mod_eq {n} (ΓΓ : context_of_length_mod_eq n)
    : context_mod_eq
  := (n,,ΓΓ).
  Coercion make_context_mod_eq : context_of_length_mod_eq >-> context_mod_eq.

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
    refine (invmap (weqpathsinsetquot (derivable_cxteq) Γ Γ') _).
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
    intros Γ; apply hinhpr. exists Γ; apply idpath.
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

  Local Definition mapeq (ΓΓ ΔΔ : context_mod_eq) (f g : raw_context_map ΓΓ ΔΔ)
  := ∀ (Γ : context_representative ΓΓ) (Δ : context_representative ΔΔ),
      ∥ [! |- f === g ::: Γ ---> Δ !] ∥.

  Local Definition mapeq_hrel {ΓΓ ΔΔ} (f g : map ΓΓ ΔΔ)
  := mapeq ΓΓ ΔΔ f g.

  Local Definition mapeq_is_eqrel (ΓΓ ΔΔ : context_mod_eq)
    : iseqrel (@mapeq_hrel ΓΓ ΔΔ).
  Proof.
    repeat split.
    - intros f g h e1 e2 Γ Δ.
      unsquash from Γ Δ (map_derivable f Γ Δ) (map_derivable g Γ Δ)
                    (map_derivable h Γ Δ) (e1 Γ Δ) (e2 Γ Δ)
        as d_Γ d_Δ d_f d_g d_h d_fg d_gh; apply hinhpr.
      refine (derive_mapeq_trans _ _ _ d_g _ _ _);
        auto using derive_flat_cxt_from_strat.
    - intros f Γ Δ.
      unsquash from (map_derivable f Γ Δ) as H; apply hinhpr.
      apply derive_mapeq_refl; auto.
    - intros f g e Γ Δ.
      unsquash from Γ Δ (map_derivable f Γ Δ) (map_derivable g Γ Δ) (e Γ Δ)
        as ? ? ? ? ?. apply hinhpr; intro i.
      apply derive_mapeq_sym; auto using derive_flat_cxt_from_strat.
  Qed.

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
        ∥ [! |- f ::: Γ ---> Δ !] ∥)
    -> ∀ (Γ:context_representative ΓΓ) (Δ:context_representative ΔΔ),
        ∥ [! |- f ::: Γ ---> Δ !] ∥.
  Proof.
    intros H Γ Δ.
    unsquash H as [Γ' [Δ' d_f]]; unsquash d_f.
    unsquash from Γ Γ' Δ Δ' (cxteq_context_representatives Γ Γ')
                    (cxteq_context_representatives Δ Δ')
      as ? d_Γ' ? d_Δ' ? ?. apply hinhpr.
    apply (derive_map_conv_cxteq_dom d_Γ');
      auto using derive_flat_cxt_from_strat, derive_flat_cxteq_sym.
    use (derive_map_conv_cxteq_cod _ d_Δ');
      auto using derive_flat_cxt_from_strat, derive_flat_cxteq_sym.
  Qed.

  Lemma raw_mapeq_for_some_rep
      {ΓΓ ΔΔ : context_mod_eq} (f g : raw_context_map ΓΓ ΔΔ)

    : (∃ (Γ:context_representative ΓΓ) (Δ:context_representative ΔΔ),
        ∥ [! |- f ::: Γ ---> Δ !]
          × [! |- g ::: Γ ---> Δ !]
          × [! |- f === g ::: Γ ---> Δ !] ∥)
    -> ∀ (Γ:context_representative ΓΓ) (Δ:context_representative ΔΔ),
        ∥ [! |- f === g ::: Γ ---> Δ !] ∥.
  Proof.
    intros H Γ Δ.
    unsquash H as [Γ' [Δ' d_fg]].
    unsquash from Γ Γ' Δ Δ' d_fg
             (cxteq_context_representatives Γ Γ')
             (cxteq_context_representatives Δ Δ')
      as ? d_Γ' ? d_Δ' [? [? ?]] ? ?. apply hinhpr.
    apply (derive_mapeq_conv_cxteq_dom d_Γ');
      auto using derive_flat_cxt_from_strat, derive_flat_cxteq_sym,
         (derive_map_conv_cxteq_cod d_Γ' d_Δ').
    use (derive_mapeq_conv_cxteq_cod _ d_Δ');
      auto using derive_flat_cxt_from_strat, derive_flat_cxteq_sym.
  Qed.

  Lemma mapeq_for_some_rep
      {ΓΓ ΔΔ : context_mod_eq} (f g : map ΓΓ ΔΔ)
    : (∃ (Γ:context_representative ΓΓ) (Δ:context_representative ΔΔ),
        ∥ [! |- f === g ::: Γ ---> Δ !] ∥)
    -> ∀ (Γ:context_representative ΓΓ) (Δ:context_representative ΔΔ),
        ∥ [! |- f === g ::: Γ ---> Δ !] ∥.
  Proof.
    intros H. apply raw_mapeq_for_some_rep.
    unsquash H as [Γ [Δ H]]; unsquash H.
    apply hinhpr; exists Γ, Δ.
    unsquash from (map_derivable f Γ Δ) (map_derivable g Γ Δ) as ? ?.
    apply hinhpr. intros; repeat split; auto.
  Qed.

  Lemma mapeq_from_path
      {ΓΓ ΔΔ : context_mod_eq} (f g : map ΓΓ ΔΔ)
    : (forall i, f i = g i)
    -> mapeq ΓΓ ΔΔ f g.
  Proof.
    intros e_fg Γ Δ.
    unsquash from (map_derivable f Γ Δ) as d_f; apply hinhpr.
    intros i; rewrite <- (e_fg i).
    apply derive_tmeq_refl, d_f.
  Qed.

End Context_Maps.

Section Context_Map_Operations.

  Local Definition idmap ΓΓ : map_mod_eq ΓΓ ΓΓ.
  Proof.
    refine (setquotpr _ _).
    exists (idmap_raw_context _).
    abstract (
      apply map_for_some_rep;
      apply (take_context_representative ΓΓ);
      [ apply isapropishinh
      | intros Γ; apply hinhpr; exists Γ; exists Γ;
        refine (hinhfun _ Γ); intros;
        use derive_idmap; apply derive_flat_cxt_from_strat; assumption]).
  Defined.

  Local Definition compose
      {ΓΓ ΔΔ ΘΘ} (ff : map_mod_eq ΓΓ ΔΔ) (gg : map_mod_eq ΔΔ ΘΘ)
    : map_mod_eq ΓΓ ΘΘ.
  Proof.
    revert ff gg. use setquotfun2'; [ | split].
    - (* construction of the composite *)
      intros f g. exists (comp_raw_context f g).
      abstract (intros Γ Θ;
        apply (take_context_representative ΔΔ);
        [ apply isapropishinh |
          intros Δ;
          unsquash from Δ (map_derivable f Γ Δ) (map_derivable g Δ Θ)
            as d_Δ d_f d_g; apply hinhpr;
          eauto using (derive_comp d_f) ]).
    - (* respecting equality in [f] *)
      abstract ( intros f f' g e_f Γ Θ; cbn;
        apply (take_context_representative ΔΔ);
        [ apply isapropishinh |
          intros Δ;
          unsquash from Γ (e_f Γ Δ) (map_derivable f Γ Δ)
                       (map_derivable f' Γ Δ) (map_derivable g Δ Θ)
            as ? e ? ? ?; apply hinhpr;
          refine (comp_raw_context_cong_l _ _ _ e _);
          auto using derive_flat_cxt_from_strat ]).
    - (* respecting equality in [g] *)
      abstract ( cbn; intros f g g' e_g Γ Θ;
        apply (take_context_representative ΔΔ);
        [ apply isapropishinh |
          intros Δ;
          unsquash from Γ (e_g Δ Θ) (map_derivable f Γ Δ) as ? e ?;
          apply hinhpr; refine (comp_raw_context_cong_r _ _ e);
          auto using derive_flat_cxt_from_strat ]).
  Defined.

  (* TODO: “empty” and “extension” context maps. *)

End Context_Map_Operations.

Section Category.

  (* TODO: lemmas on associativity etc.  Should be immediate from the
  similar lemmas on raw ones in [SyntaxLemmas]. *)

  Lemma idmap_left {ΓΓ ΔΔ : context_mod_eq} (f : map_mod_eq ΓΓ ΔΔ)
    : compose (idmap _) f = f.
  Proof.
    revert f. apply setquotunivprop'. { intro; apply isasetsetquot. }
    intros f. cbn.
    apply maponpaths. apply subtypePath_prop.
    apply id_left_raw_context.
  Qed.

  Lemma idmap_right {ΓΓ ΔΔ : context_mod_eq} (f : map_mod_eq ΓΓ ΔΔ)
    : compose f (idmap _) = f.
  Proof.
    revert f. apply setquotunivprop'. { intro; apply isasetsetquot. }
    intros f. cbn.
    apply maponpaths. apply subtypePath_prop.
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
    apply maponpaths. apply subtypePath_prop.
    cbn. apply pathsinv0, assoc_raw_context.
  Qed.

  (* TODO: issue to raise in UniMath: [make_category] is constructor for a _univalent_ category! *)
  Definition syntactic_category : category.
  Proof.
    use tpair.
    - use make_precategory_one_assoc.
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

  Definition type_derivable {n} {ΓΓ : _ n} (A : type_over ΓΓ)
  := pr2 A : is_type_over ΓΓ A.
  Coercion type_derivable : type_over >-> is_type_over.

  Definition typeeq_hrel {n} {ΓΓ : _ n} : hrel (type_over ΓΓ)
  := fun A B => ∀ Γ : context_representative ΓΓ, ∥ [! Γ |- A === B !] ∥.

  Proposition typeeq_is_eqrel {n} (ΓΓ : _ n) : iseqrel (@typeeq_hrel n ΓΓ).
  Proof.
    repeat split.
    - intros A B C e_AB e_BC Γ.
      apply (squash_to_hProp (A Γ)). intros d_A.
      apply (squash_to_hProp (B Γ)). intros d_B.
      apply (squash_to_hProp (C Γ)). intros d_C.
      apply (squash_to_hProp (e_AB Γ)). clear e_AB; intros e_AB.
      apply (squash_to_hProp (e_BC Γ)). clear e_BC; intros e_BC.
      now apply hinhpr, (derive_tyeq_trans Γ _ B).
    - intros A Γ.
      apply (squash_to_hProp (A Γ)). intros d_A.
      now apply hinhpr, derive_tyeq_refl.
    - intros A B e_AB Γ.
      apply (squash_to_hProp (e_AB Γ)). clear e_AB; intros e_AB.
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

  (* TODO: perhaps generalise to “representatives” of arbitrary eqrel, and upstream? *)

  Lemma typeeq_type_representatives
      {n} {ΓΓ : _ n} {AA : type_mod_eq ΓΓ} (A A' : type_representative AA)
    : typeeq_eqrel A A'.
  Proof.
    refine (invmap (weqpathsinsetquot typeeq_eqrel A A') _).
    exact (pr2 A @ ! pr2 A').
  Defined.

  Lemma type_for_some_rep
      {ΓΓ : context_mod_eq} (A : ty_expr ΓΓ)
    : (∃ (Γ:context_representative ΓΓ), [! Γ |- A !])
    -> is_type_over ΓΓ A.
  Proof.
    intros H Γ.
    unsquash H as [Γ' d_A].
    unsquash from Γ Γ' (cxteq_context_representatives Γ Γ') as d_Γ d_Γ' e_Γ.
    apply hinhpr, (derive_ty_conv_cxteq Γ');
      eauto using derive_flat_cxteq_sym, derive_flat_cxt_from_strat.
  Qed.

  Lemma typeeq_for_some_rep
      {ΓΓ : context_mod_eq} (A B : type_over ΓΓ)
    : (∃ (Γ:context_representative ΓΓ), [! Γ |- A === B !])
    -> typeeq_hrel A B.
  Proof.
    intros H Γ.
    unsquash H as [Γ' d_AB].
    unsquash from Γ Γ' (cxteq_context_representatives Γ Γ') as d_Γ d_Γ' e_Γ.
    apply hinhpr, (derive_tyeq_conv_cxteq Γ');
      eauto using derive_flat_cxt_from_strat, derive_flat_cxteq_sym.
  Qed.

End Syntactic_Types.

Section Split_Typecat.

  Local Definition ext (ΓΓ : context_mod_eq) (AA : type_mod_eq ΓΓ)
    : context_mod_eq.
  Proof.
    exists (S (length ΓΓ)).
    (* TODO: can we do this with a non-dependent elimination principle
       (ideally, a non-dependent version of [take_representative_with_isaset])
       to get the syntax part computing?? *)
    use (take_representative_with_isaset ΓΓ); try apply isasetsetquot;
      change (representative ΓΓ) with (context_representative ΓΓ).
    - intros Γ.
      use (setquotfun _ _ _ _ AA).
      + intros A. exists (Γ ;; A)%strat_cxt.
        abstract (
          refine (hinhfun2 _ Γ (A Γ)); intros d_Γ d_ΓA;
          exact (derive_extend_stratified_context d_Γ d_ΓA)).
      + intros A A' e_A.
        abstract (
          refine (hinhfun2 _ Γ (e_A Γ)); clear e_A; intros d_Γ e_A;
          apply derive_extend_flat_cxteq;
          auto using derive_flat_cxt_from_strat, d_Γ;
          exact (derive_flat_cxteq_refl d_Γ)).
    - intros Γ Γ'; simpl; revert AA.
      abstract (
        use setquotunivprop'; [ intros; apply isasetsetquot |
        intros A;
        apply iscompsetquotpr;
        unsquash from Γ Γ' (A Γ) (cxteq_context_representatives Γ Γ')
          as ? ? ? ?;
        apply hinhpr, derive_extend_flat_cxteq;
        auto using derive_flat_cxt_from_strat, derive_tyeq_refl ]).
  Defined.

  Local Definition ext_representative
      {ΓΓ : context_mod_eq} (Γ : context_representative ΓΓ)
      (A : type_over ΓΓ)
    : context_representative (ext ΓΓ (setquotpr _ A)).
  Proof.
    use tpair.
    - exists (Γ ;; A)%strat_cxt. shelve.
    - apply pathsinv0. use take_representative_comp.
  Defined.

  Local Definition reind
      {ΓΓ : context_mod_eq} (AA : type_mod_eq ΓΓ)
      {ΓΓ' : context_mod_eq} (ff : map_mod_eq ΓΓ' ΓΓ)
    : type_mod_eq ΓΓ'.
  Proof.
    simple refine (setquotfun2' _ _ ff AA); try split.
    - (* give the reindexed type *)
      intros f A.
      exists (subst_ty f A).
      intros Γ'.
      apply (take_context_representative ΓΓ). { apply propproperty. } intros Γ.
      refine (hinhfun2 _ (map_derivable f Γ' Γ) (type_derivable A Γ)).
      intros d_f d_A.
      (* TODO: make [derive_subst_ty] etc. as specialisations of [subst_derivation], and replace [subst_derivation [! _ |- _ !] ] with them throughout? *)
      exact (subst_derivation _ d_A d_f).
    - (* respects equality in the map *)
      clear AA ff. intros f f' A e_f Γ'. cbn.
      apply (take_context_representative ΓΓ). { apply propproperty. } intros Γ.
      refine (hinhfun5 _ (type_derivable A Γ) Γ'
                       (map_derivable f Γ' Γ) (map_derivable f' Γ' Γ)
                       (e_f Γ' Γ)).
      intros d_Γ_A d_Γ' d_f d_f' d_e_f.
      use (substeq_derivation _ d_Γ_A); auto using derive_flat_cxt_from_strat.
    - (* respects equality in the type *)
      clear AA ff. intros f A A' e_A Γ'. cbn.
      apply (take_context_representative ΓΓ). { apply propproperty. } intros Γ.
      refine (hinhfun2 _ (map_derivable f Γ' Γ) (e_A Γ)).
      intros d_f d_e_A.
      exact (subst_derivation _ d_e_A d_f).
  Defined.

  Definition syntactic_typecat_structure1 : typecat_structure1 syntactic_category.
  Proof.
    repeat use tpair.
    - (* define the types *)
      intros ΓΓ; cbn in ΓΓ. exact (type_mod_eq ΓΓ).
    - (* context extension *)
      exact ext.
    - (* reindexing *)
      exact @reind.
  Defined.

  Local Definition dpr (ΓΓ : context_mod_eq) (AA : type_mod_eq ΓΓ)
    : map_mod_eq (ext ΓΓ AA) ΓΓ.
  Proof.
    use setquotpr.
    exists (dB_next_context_map _).
    apply map_for_some_rep.
    apply (take_context_representative ΓΓ). { apply propproperty. } intros Γ.
    revert AA. use setquotunivprop'. { intros; apply isapropishinh. } intros A.
    cbn. apply hinhpr.
    exists (ext_representative Γ _); cbn.
    exists Γ.
    unsquash from Γ (A Γ) as d_Γ d_A; apply hinhpr;
    exact (derive_dB_next_context_map d_Γ d_A).
  Defined.

  Local Definition qmor_raw
      {ΓΓ : context_mod_eq} (AA : type_mod_eq ΓΓ)
      {ΓΓ' : context_mod_eq} (f : raw_context_map ΓΓ' ΓΓ)
    : raw_context_map (S ΓΓ') (S ΓΓ).
  Proof.
    exact (weaken_raw_context_map f).
  Defined.

  Local Definition qmor_derivable
      {ΓΓ : context_mod_eq} (AA : type_mod_eq ΓΓ)
      {ΓΓ' : context_mod_eq} (f : map ΓΓ' ΓΓ)
    : ∀ (Γ : context_representative (ext ΓΓ' (reind AA (setquotpr _ f))))
        (Δ : context_representative (ext ΓΓ AA)),
       ∥ [! |- qmor_raw AA f ::: Γ ---> Δ !] ∥.
  Proof.
    apply (take_context_representative ΓΓ). { apply propproperty. } intros Γ.
    apply (take_context_representative ΓΓ'). { apply propproperty. } intros Γ'.
    revert AA. use setquotunivprop'. { intros; apply propproperty. } intros A.
    apply map_for_some_rep, hinhpr.
    exists (ext_representative Γ' _); cbn.
    exists (ext_representative Γ _); cbn.
    unsquash from Γ Γ' (A Γ) (map_derivable f Γ' Γ) as d_Γ d_Γ' d_A d_f;
      apply hinhpr.
    refine (derive_weaken_raw_context_map _ _ _ d_f);
      auto using derive_flat_cxt_from_strat.
  Qed.

  Local Definition qmor_eq
      {ΓΓ : context_mod_eq} (AA : type_mod_eq ΓΓ)
      {ΓΓ' : context_mod_eq}
      {f g : map ΓΓ' ΓΓ} (e_fg : mapeq ΓΓ' ΓΓ f g)
    : mapeq (ext ΓΓ' (reind AA (setquotpr _ g))) (ext ΓΓ AA)
            (qmor_raw AA f) (qmor_raw AA g).
  Proof.
    refine (raw_mapeq_for_some_rep _ _ _).
    apply (take_context_representative ΓΓ). { apply propproperty. } intros Γ.
    apply (take_context_representative ΓΓ'). { apply propproperty. } intros Γ'.
    revert AA. use setquotunivprop'. { intros; apply propproperty. } intros A.
    unsquash from Γ Γ' (A Γ)
             (map_derivable f Γ' Γ) (map_derivable g Γ' Γ) (e_fg Γ' Γ)
      as d_Γ d_Γ' d_A d_f d_g d_fg; apply hinhpr.
    exists (ext_representative Γ' _); simpl.
    exists (ext_representative Γ _); simpl.
    apply hinhpr; repeat split.
    + (* TODO: this should probably be abstracted to [TypingLemmas];
           but it seems such an unnatural lemma! *)
      refine (@derive_map_conv_cxteq_dom (S _)
                         (Γ';;subst_ty f A) (Γ';;subst_ty g A) _ _ _ _ _ _ _);
        try apply derive_flat_extend_context;
        try apply (subst_derivation [! Γ |- A !]);
        try apply derive_extend_flat_cxteq, (substeq_derivation [! Γ |- A !]);
        try refine (derive_flat_extend_context _ d_A);
        try refine (derive_weaken_raw_context_map _ _ _ d_f);
        auto using derive_flat_cxt_from_strat, (@derive_flat_cxteq_refl Γ').
    + refine (derive_weaken_raw_context_map _ _ _ d_g);
        auto using derive_flat_cxt_from_strat.
    + refine (derive_weaken_raw_context_mapeq _ _ _ _ _ d_fg);
        auto using derive_flat_cxt_from_strat.
  Qed.

  Local Definition qmor
      {ΓΓ : context_mod_eq} (AA : type_mod_eq ΓΓ)
      {ΓΓ' : context_mod_eq} (ff : map_mod_eq ΓΓ' ΓΓ)
    : map_mod_eq (ext ΓΓ' (reind AA ff)) (ext ΓΓ AA).
  Proof.
    revert ff.
    simple refine (@setquot_to_dependent_subquotient _ _
              (raw_context_map (S _) _) _ _ _ _ _).
    - intros f. exact (qmor_raw AA f).
    - intros f. apply qmor_derivable.
    - intros f g e_fg. exact (qmor_eq AA e_fg).
  Defined.

  Local Definition dpr_q
      {ΓΓ : context_mod_eq} (AA : type_mod_eq ΓΓ)
      {ΓΓ' : context_mod_eq} (ff : map_mod_eq ΓΓ' ΓΓ)
    : compose (qmor AA ff) (dpr _ AA) = compose (dpr _ (reind AA ff)) ff.
  Proof.
    revert ff; use setquotunivprop'. { intros; apply isasetsetquot. } intros f.
    simpl.
    apply iscompsetquotpr.
    use mapeq_from_path.
    intros i; simpl.
    apply rename_as_subst_tm.
  Qed.

  Local Definition reind_pb_raw
      {ΓΓ ΓΓ' ΔΔ: context_mod_eq}
      (g : raw_context_map ΔΔ ΓΓ') (h : raw_context_map ΔΔ (S ΓΓ))
    : raw_context_map ΔΔ (S ΓΓ').
  Proof.
    exact (extend_raw_context_map g (h dB_top)).
  Defined.

  Arguments reind_pb_raw {_ _ _} _ _ _/.

  Local Definition reind_pb_derivable
      {ΓΓ : context_mod_eq} (AA : type_mod_eq ΓΓ)
      {ΓΓ' : context_mod_eq} (f : map ΓΓ' ΓΓ)
      {ΔΔ: context_mod_eq}
      (g : map ΔΔ ΓΓ') (h : map ΔΔ (ext ΓΓ AA))
      (H_e : mapeq ΔΔ ΓΓ (comp_raw_context g f)
                     (comp_raw_context h (dB_next_context_map _)))
    : ∀ (Δ : context_representative ΔΔ)
        (Γ'A : context_representative (ext ΓΓ' (reind AA (setquotpr _ f)))),
       ∥ [! |- reind_pb_raw g h ::: Δ ---> Γ'A !] ∥.
  Proof.
    apply (take_context_representative ΓΓ). { apply propproperty. } intros Γ.
    apply (take_context_representative ΓΓ'). { apply propproperty. } intros Γ'.
    apply (take_context_representative ΔΔ). { apply propproperty. } intros Δ.
    revert AA h H_e. use setquotunivprop'.
    { intros; repeat (apply impred_isaprop; intros); apply propproperty. }
    intros A h H_e.
    apply map_for_some_rep, hinhpr.
    exists Δ; simpl.
    exists (ext_representative Γ' _); simpl.
    refine (hinhpr _ ⊛ Γ ⊛ Γ' ⊛ Δ ⊛ (A Γ)
                     ⊛ (map_derivable f Γ' Γ) ⊛ (map_derivable g Δ Γ')
                     ⊛ (map_derivable h Δ (ext_representative Γ A))
                     ⊛ (H_e Δ Γ)).
    clear H_e; intros d_Γ d_Γ' d_Δ d_A d_f d_g d_h H_eq.
    (* TODO: abstract the following and upstream to [TypingLemmas] *)
    refine (derive_extend_context_map d_g _); simpl.
    assert (d_dpr_h
         : [! |- comp_raw_context h (dB_next_context_map Γ) ::: Δ ---> Γ !]).
    { refine (derive_comp d_h _).
      use derive_dB_next_context_map; auto using derive_flat_cxt_from_strat. }
    assert (d_g_f : [! |- comp_raw_context g f ::: Δ ---> Γ !]).
    { exact (derive_comp d_g d_f). }
    refine (derive_tm_conv _ _ _ _ _ _ _ (d_h dB_top)); simpl;
      change ((Γ;; A) dB_top) with (rename_ty dB_next A).
    - rewrite subst_rename_ty.
      refine (subst_derivation [! _ |- _ !] d_A d_dpr_h).
    - rewrite subst_subst_ty.
      refine (subst_derivation [! _ |- _ !] d_A d_g_f).
    - rewrite subst_rename_ty, subst_subst_ty.
      apply derive_tyeq_sym.
      refine (substeq_derivation [! Γ |- A !] _ _ _ _ _);
          auto using derive_flat_cxt_from_strat.
  Qed.

  (* TODO: [reind_pb_eq], analogous to [qmor_eq] *)

  Local Definition reind_pb
      {ΓΓ : context_mod_eq} (AA : type_mod_eq ΓΓ)
      {ΓΓ' : context_mod_eq} (ff : map_mod_eq ΓΓ' ΓΓ)
    : @isPullback syntactic_category _ _ _ _
           ff (dpr ΓΓ AA) (dpr ΓΓ' (reind AA ff)) (qmor AA ff)
           (! dpr_q AA ff).
  Proof.
    use make_isPullback; simpl.
    intros ΓΓ'' gg hh Heq.
    use unique_exists; simpl.
    3: { intros. apply isapropdirprod; apply isasetsetquot. }
    - admit.
    - split. (* hopefully straightforward with [mapeq_from_path]. *)
      + admit.
      + admit.
    - intros hh' [Hgg Hhh].
      admit.
  Admitted. (* [SyntacticCategory.reind_pb]: hopefully fairly local *)

  Definition syntactic_typecat_structure : typecat_structure syntactic_category.
  Proof.
    exists syntactic_typecat_structure1.
    repeat use tpair.
    - exact dpr.  (* dependent projection *)
    - exact @qmor. (* “q-morphisms” *)
    - exact @dpr_q. (* commutativity of q-morphisms*)
    - exact @reind_pb. (* pullback condition *)
  Defined.

  Lemma is_split_syntactic_typecat_structure
    : is_split_typecat syntactic_typecat_structure.
  Proof.
    repeat split.
    - intros Γ.
      apply isasetsetquot.
    - use tpair.
      + intros ΓΓ AA.
        revert AA; use setquotunivprop'; [intros; apply isasetsetquot|]; intros A.
        apply iscompsetquotpr; simpl; intros Γ.
        use (hinhfun _ (type_derivable A Γ)); intro d_A.
        rewrite subst_idmap_ty.
        now apply derive_tyeq_refl.
      + intros ΓΓ AA.
        unfold q_typecat; simpl; unfold qmor, identity, idmap; simpl.
        rewrite setquot_to_dependent_subquotient_comp.
        simpl.
        (* Should use [derive_idmap_gen]. *)
        (* TODO: state this in terms of syntactic category *)
        admit. (* How to approach this? *)
    - use tpair.
      + simpl.
        intros ΓΓ AA ΓΓ' ff ΓΓ'' gg.
        revert AA; use setquotunivprop'; [intros; apply isasetsetquot|]; intros A.
        revert ff; use setquotunivprop'; [intros; apply isasetsetquot|]; intros f.
        revert gg; use setquotunivprop'; [intros; apply isasetsetquot|]; intros g.
        apply (take_context_representative ΓΓ); [apply isasetsetquot|]; intros Γ.
        apply (take_context_representative ΓΓ'); [apply isasetsetquot|]; intros Γ'.
        apply iscompsetquotpr; cbn; intros Γ''.
        unsquash from (type_derivable A Γ) (map_derivable f Γ' Γ)
                      (map_derivable g Γ'' Γ')
          as hA hf hg; apply hinhpr.
        rewrite <- subst_subst_ty.
        apply derive_tyeq_refl.
        use (subst_derivation [! Γ' |- _ !] _ hg).
        exact (subst_derivation [! Γ |- _ !] hA hf).
      + simpl.
        admit. (* This should be provable once we know how to do the above admit *)
  Admitted. (* [is_split_syntactic_typecat_structure]: seems a bit harder than one might expect. *)

  Definition syntactic_typecat : split_typecat
  := ((syntactic_category,, syntactic_typecat_structure),,
       is_split_syntactic_typecat_structure).

End Split_Typecat.

Section Contextuality.

  (* TODO: Should some of these lemmas be upstreamed? *)

  Local Definition empty_context : syntactic_typecat.
  Proof.
    exists 0.
    apply setquotpr.
    exact empty_wellformed_context_of_length.
  Defined.

  Definition raw_context_map_0 (n : ℕ) : raw_context_map n 0.
  Proof.
    intros x; induction x.
  Defined.

  (* TODO: opacify parts of this *)
  Lemma isTerminal_empty_context : isTerminal syntactic_typecat empty_context.
  Proof.
    use make_isTerminal.
    intros x.
    use tpair.
    - apply setquotpr.
      use tpair.
      + apply raw_context_map_0.
      + simpl.
        intros xx xxx.
        apply hinhpr.
        intros e; induction e.
    - cbn; intros f.
      use (setquot_rect_isaprop (fun X => X = _)); clear f.
      + intros g.
        use (isasetsetquot (mapeq_eqrel x empty_context)).
      + cbn; intros g.
        apply (iscompsetquotpr (mapeq_eqrel x empty_context)).
        intros ? ?; apply hinhpr.
        intros e; induction e.
  Defined.

  (* This is maybe not needed *)
  Lemma wellformed_context_of_length_rest (n : ℕ) :
    wellformed_context_of_length (S n) → wellformed_context_of_length n.
  Proof.
    intros G.
    exists (pr11 G).
    apply (hinhfun pr1 (pr2 G)).
  Defined.

  Lemma syntactic_typecat_is_contextual : is_contextual syntactic_typecat.
  Proof.
    exists empty_context, isTerminal_empty_context.
    intros [n G].
    revert G.
    use setquot_rect_isaprop; intros [G HG].
    - apply isapropiscontr.
    - use unique_exists.
      + induction n.
        apply (0,,tt).
        exists (S (pr1 (IHn (context_rest G) (hinhfun pr1 HG)))).
        use extension_extend.
        apply (pr2 (IHn (context_rest G) (hinhfun pr1 HG))).
        apply setquotpr.
        admit.
      + admit.
      + simpl in *.
        admit.
      + admit.
  Admitted. (* [syntactic_typecat_is_contextual].  Self-contained, proof-irrelevant. *)

  Definition syntactic_contextual_cat : contextual_cat
    := (syntactic_typecat,, syntactic_typecat_is_contextual).

End Contextuality.

(** Miscellaneous lemmas and constructions, e.g. the correspondence between terms in the syntactic sense and terms of the syntactic typecat in the type-category sense *)
Section Misc.

  Definition raw_context_as_partial_object {n}
      (Γ : stratified_context_of_length n)
    : partial (syntactic_category).
  Proof.
    exists ( ∥ [! |- Γ !] ∥ ).
    exists n; apply setquotpr; exists Γ; assumption.
  Defined.

  Definition ty_expr_as_type
      {n} (Γ : wellformed_context_of_length n)
      {A : ty_expr n} (d_A : ∥ [! Γ |- A !] ∥)
    : type_mod_eq Γ.
  Proof.
    apply setquotpr; exists A.
    apply type_for_some_rep.
    refine (hinhfun _ d_A); clear d_A; intros d_A.
    exact (context_as_context_representative Γ,, d_A).
  Defined.

  Definition ty_expr_as_partial_type
      {n} (Γ : wellformed_context_of_length n) (A : ty_expr n)
    : partial (type_mod_eq Γ).
  Proof.
    exists (∥ [! Γ |- A !] ∥).
    apply ty_expr_as_type.
  Defined.

  Definition tm_expr_as_term
      {n} (Γ : wellformed_context_of_length n)
      {A : ty_expr n} (isd_A : ∥ [! Γ |- A !] ∥)
      {a : tm_expr n} (isd_a : ∥ [! Γ |- a ::: A !] ∥)
    : @tm syntactic_typecat _ (ty_expr_as_type Γ isd_A).
  Proof.
    use tpair.
    - (* morphism part *)
      apply setquotpr.
      exists (tm_as_raw_context_map a).
      abstract (
          apply map_for_some_rep, hinhpr;
          refine (context_as_context_representative _,,_);
          use tpair;
          [ apply ext_representative, context_as_context_representative
          | refine (hinhfun2 _ (context_derivable Γ) (isd_a)); intros d_Γ d_a; cbn;
            refine (derive_tm_as_raw_context_map _ _);
        auto using derive_flat_cxt_from_strat]).
    - (* section property *)
      apply iscompsetquotpr; cbn.
      (* TODO: adapt [mapeq_for_some_rep] to incorporate [iscompsetquotpr]? *)
      refine (raw_mapeq_for_some_rep _ _ _); apply hinhpr.
      refine (context_as_context_representative _,,_).
      refine (context_as_context_representative _,,_).
      refine (hinhfun3 _ (context_derivable Γ) isd_A isd_a); intros d_Γ d_A d_a.
      repeat split.
      + use (@derive_comp _ (Γ;;A)%context).
        * refine (derive_tm_as_raw_context_map _ _);
            auto using derive_flat_cxt_from_strat.
        * use derive_dB_next_context_map; auto using derive_flat_cxt_from_strat.
      + use derive_idmap; auto using derive_flat_cxt_from_strat.
      + apply derive_mapeq_refl.
        use (@derive_comp _ (Γ;;A)%context).
        * refine (derive_tm_as_raw_context_map _ _);
            auto using derive_flat_cxt_from_strat.
        * use derive_dB_next_context_map; auto using derive_flat_cxt_from_strat.
  Defined.

  Definition tm_expr_as_partial_term
      {n} (Γ : wellformed_context_of_length n)
      {A : ty_expr n} (isd_A : ∥ [! Γ |- A !] ∥)
      (a : tm_expr n)
    : partial (@tm syntactic_typecat _ (ty_expr_as_type Γ isd_A)).
  Proof.
    exists (∥ [! Γ |- a ::: A !] ∥).
    apply tm_expr_as_term.
  Defined.

  Lemma tm_transportf_tm_expr_as_term_gen
      {n} (Γ : wellformed_context_of_length n)
      {A : ty_expr n} (isd_A : ∥ [! Γ |- A !] ∥)
      {A' : ty_expr n} (isd_A' : ∥ [! Γ |- A' !] ∥)
      (e_A : ty_expr_as_type Γ isd_A = ty_expr_as_type Γ isd_A')
      {a : tm_expr n} (isd_a : ∥ [! Γ |- a ::: A !] ∥)
      (isd_a' : ∥ [! Γ |- a ::: A' !] ∥)
    : @tm_transportf syntactic_typecat _ (ty_expr_as_type Γ isd_A) _
        e_A (tm_expr_as_term Γ isd_A isd_a)
      = tm_expr_as_term Γ isd_A' isd_a'.
  Proof.
  Admitted. (* [tm_transportf_tm_expr_as_term_gen]: hopefully not too hard *)

End Misc.

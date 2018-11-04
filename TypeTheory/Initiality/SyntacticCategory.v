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

For just the _category_ this is unnecessary, but for the _type-category_, it is unavoidable: types must be modulo equality, in order to form a presheaf, but then so must contexts, in order for context extension to be well-defined. *)

Section Context_Equality.
(* Probably this (or some of it) should be upstreamed to with the other “auxiliary judgements” in [TypingLemmas]. *)

  Definition wellformed_context_of_length (n : nat) : UU
  := ∑ (Γ : context_of_length n), [! |- Γ !].

  Coercion context_of_wellformed_context {n} (Γ : wellformed_context_of_length n)
    : context_of_length n
  := pr1 Γ.

  Definition derivation_wellformed_context
             {n} (Γ : wellformed_context_of_length n)
    : [! |- Γ !]
  := pr2 Γ.

  (** We only compare contexts of the same length for equality.

  Two contexts are equal if they _both_ believe all their types are equal.

  Note 1: one direction wouldn’t suffice, for general type theories.  E.g.
  in ETT with the reflection rule, define a predicate [P] over [nat] with
  [ P 0 ] false, and [ P 1 ] true.  Then [ P 0 ] proves that [ 0 === 1 : nat ]
  and hence that [ P 0 === P 1 ], but [ P 1 ] doesn’t prove this, so for the
  contexts [ x0 : P 0 ] and [ x0 : P 1 ], one direction of the below conditions
  will hold, but not both.

  Note 2: this is a _flat_ form of context equality, not stratified, analogous to [ [! |f- Γ !] ] not [ [! |f- Γ !] ].  As such, we don’t expect it to give a contextual category: a context may (up to equality) be built up from types in several different ways.  For initiality, we will at some point have to remedy this: either by taking the contextual core of what this gives, or some other way. *)
  Definition derivation_cxteq {n} (Γ Δ : context_of_length n) : UU
  :=   (forall i, [! Γ |- Γ i === Δ i !])
     × (forall i, [! Δ |- Δ i === Γ i !]).

  Notation "[! |- Δ === Γ !]" := (derivation_cxteq Δ Γ)
                    (format "[!  |-  Δ  ===  Γ  !]") : judgement_scope.

  (** While the definition of this relation works for arbitrary raw contexts,
  the proof that it is an equivalence relation requires restriction to well-
  formed contexts. *)
  Definition derivable_cxteq_hrel {n} : hrel (wellformed_context_of_length n)
  := fun Γ Δ => ∥ derivation_cxteq Γ Δ ∥.

  Definition derivable_cxteq_is_eqrel n : iseqrel (@derivable_cxteq_hrel n).
  Admitted.

  Definition derivable_cxteq {n} : eqrel (wellformed_context_of_length n)
  := (_,,derivable_cxteq_is_eqrel n).

End Context_Equality.

Section Contexts_Modulo_Equality.

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

  (** Note: the truncation of the derivation part is mathematically redundant,
  since we will later quotient anyway.  However, it lets us get better
  computational behaviour on the map part, in compositions etc. *)
  Local Definition map (ΓΓ ΔΔ : context_mod_eq) : UU
    := ∑ (f : raw_context_map (length ΓΓ) (length ΔΔ)),
       ∥ forall (Γ : ΓΓ) (Δ : ΔΔ), [! |- f ::: Γ ---> Δ !] ∥.

  (* TODO: lemma that here (and in later similar definitions) it’s sufficient to show typing for _some_ representative, to get it for all representatives. *)

  Definition raw_of_context_map {ΓΓ ΔΔ} (f : map ΓΓ ΔΔ) : raw_context_map _ _
  := pr1 f.
  Coercion raw_of_context_map : map >-> raw_context_map.

  Local Definition map_derivable {ΓΓ ΔΔ} (f : map ΓΓ ΔΔ)
    : ∥ forall (Γ : ΓΓ) (Δ : ΔΔ), [! |- f ::: Γ ---> Δ !] ∥
  := pr2 f.
  
  Local Definition mapeq_hrel {ΓΓ ΔΔ} (f g : map ΓΓ ΔΔ)
  := ∥ forall (Γ : ΓΓ) (Δ : ΔΔ), [! |- f === g ::: Γ ---> Δ !] ∥.

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

  Local Definition compose
      {ΓΓ ΔΔ ΘΘ} (ff : map_mod_eq ΓΓ ΔΔ) (gg : map_mod_eq ΔΔ ΘΘ)
    : map_mod_eq ΓΓ ΘΘ.
  Proof.
    revert ff gg. use QuotientSet.setquotfun2; [ | split].
    - (* construction of the composite *)
      intros f g. exists (comp_raw_context f g).
      (* TODO: perhaps try to condense and [abstract] the following. *)
      apply (squash_to_prop (map_derivable f)). { apply isapropishinh. }
      intros d_f.
      apply (squash_to_prop (map_derivable g)). { apply isapropishinh. }
      intros d_g.
      apply (take_context_representative ΔΔ). { apply isapropishinh. }
      intros Δ.
      apply hinhpr; intros Γ Θ.
      refine (@derivation_comp_raw_context Γ Δ Θ _ (raw_of_context_map f) _ _ _);
        auto using derivation_wellformed_context.
    - (* respecting equality in [f] *)
      intros f f' g. cbn.
      apply factor_through_squash. { apply isapropishinh. } intros e_f.
      apply (squash_to_prop (map_derivable f)). { apply isapropishinh. }
      intros d_f.
      apply (squash_to_prop (map_derivable f')). { apply isapropishinh. }
      intros d_f'.
      apply (squash_to_prop (map_derivable g)). { apply isapropishinh. }
      intros d_g.
      apply (take_context_representative ΔΔ). { apply isapropishinh. }
      intros Δ.
      apply hinhpr; intros Γ Θ.
      simple refine (comp_raw_context_cong_l _ _ _ (e_f _ _) _);
        auto using derivation_wellformed_context.
    - (* respecting equality in [g] *)
      intros f g g'. cbn.
      apply factor_through_squash. { apply isapropishinh. } intros e_g.
      apply (squash_to_prop (map_derivable f)). { apply isapropishinh. }
      intros d_f.
      apply (take_context_representative ΔΔ). { apply isapropishinh. }
      intros Δ.
      apply hinhpr; intros Γ Θ.
      simple refine (comp_raw_context_cong_r _ _ (e_g _ _));
        auto using derivation_wellformed_context.
  Defined.

  (* TODO: define identity context map

     These will make use of the variable and substitution structural rules, plus lemma above about derivability of well-typed contexts. *)

  (* TODO: lemmas on associativity etc.  Should be immediate from the similar lemmas on raw ones in [SyntaxLemmas]. *)

  (* TODO: “empty” and “extension” context maps. *)

End Context_Maps.

Section Category.

  Definition syntactic_category : category.
  Admitted.

End Category.

Section Split_Typecat.

  Definition syntactic_typecat : split_typecat.
  Admitted.

End Split_Typecat.
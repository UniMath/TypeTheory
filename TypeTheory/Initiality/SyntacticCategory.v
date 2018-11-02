(** This file defines the syntactic category of our toy type theory, and the logical structure on it.

As a matter of organisation: all concrete lemmas involving derivations should live upstream in [TypingLemmas]; this file should simply package them up into the appropriate categorical structure. *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.All.

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

End Auxiliary.

Section Context_Equality.
(* Probably this (or some of it) should be upstreamed to with the other “auxiliary judgements” in [TypingLemmas]. *)

  Definition wellformed_context_of_length (n : nat) : UU
  := ∑ (Γ : context_of_length n), [! |- Γ !].

  Coercion context_of_wellformed_context {n} (Γ : wellformed_context_of_length n)
    : context_of_length n
  := pr1 Γ.

  (** We only compare contexts of the same length for equality.

  Two contexts are equal if they _both_ believe all their types are equal.

  (Note: one direction wouldn’t suffice, for general type theories.  E.g.
  in ETT with the reflection rule, define a predicate [P] over [nat] with
  [ P 0 ] false, and [ P 1 ] true.  Then [ P 0 ] proves that [ 0 === 1 : nat ]
  and hence that [ P 0 === P 1 ], but [ P 1 ] doesn’t prove this, so for the
  contexts [ x0 : P 0 ] and [ x0 : P 1 ], one direction of the below conditions
  will hold, but not both. *)
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

  (* TODO: raise issue upstream: shoud [pr1] of [eqrel] coerce to [hrel], not directly to [Funclass]? *)
End Context_Equality.

Section Contexts_Modulo_Equality.

  Definition context_mod_eq
  := ∑ (n:nat), setquot (@derivable_cxteq n).

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

End Contexts_Modulo_Equality.

Section Context_Maps.

  Local Definition map (ΓΓ ΔΔ : context_mod_eq) : UU
    := ∑ (f : raw_context_map (length ΓΓ) (length ΔΔ)),
       forall (Γ : ΓΓ) (Δ : ΔΔ), [! |- f ::: Γ ---> Δ !].

  (* TODO: lemma that here (and in later similar definitions) it’s sufficient to show typing for _some_ representative, to get it for all representatives. *)

  Coercion raw_of_context_map {ΓΓ ΔΔ} (f : map ΓΓ ΔΔ)
    : raw_context_map _ _
  := pr1 f.

  Local Definition derivation_of_map {ΓΓ ΔΔ} (f : map ΓΓ ΔΔ)
    : forall (Γ : ΓΓ) (Δ : ΔΔ), [! |- f ::: Γ ---> Δ !]
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

  (* TODO: define identity context map, composition.

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
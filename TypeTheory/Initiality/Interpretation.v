(** This file defines the interpretation function, from the syntax of our toy type theory into any split type-cat with suitable structure. *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.All.

(* TODO: raise issue upstream: notation "_ ∘ _" is used for function-order composition of functions, but for diagrammatic-order composition of morphisms in categories! *)

Require Import TypeTheory.Auxiliary.Partial.
Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.Initiality.SplitTypeCat_Maps.
Require Import TypeTheory.Initiality.SplitTypeCat_Structure.
Require Import TypeTheory.Initiality.Syntax.

Section Auxiliary.

  (* TODO: upstream! *)
  Definition partial_map X Y := X -> partial Y.
  Notation "X ⇢ Y" := (partial_map X Y) (at level 99) : type_scope.

  (* TODO: upstream! *)
  Definition compose_partial {X Y Z} (f : X ⇢ Y) (g : Y ⇢ Z) : X ⇢ Z
    := fun x => bind_partial (f x) g.
  Notation "f ∘ g" := (compose_partial f g) : partial_map_scope.
  (** This notation uses diagrammatic order, following UniMath’s notation
  [ (_ ∘ _)%Cat ] for morphisms in categories, _not_ consistent with
  UniMath’s notation [ (_ ∘ _)%functions ] for functions. *)

End Auxiliary.

Section Environments.
(** _Environments_: the semantic proxy for a context, in a split type-category, giving the information needed to construct the (partial) interpretation of terms/types from some context over some object of the type-cat. *)

  Context {C : split_typecat}.

  (* TODO: perhaps upstream? *)
  Definition term_with_type (Γ:C) := ∑ (A : C Γ), tm A.

  Definition type_of {Γ} (Aa : term_with_type Γ) := pr1 Aa.

  Coercion term_of {Γ} (Aa : term_with_type Γ) : tm (type_of Aa)
    := pr2 Aa.

  Definition reind_term_with_type {Γ Γ'} (f : Γ' --> Γ)
    : term_with_type Γ -> term_with_type Γ'
  := fun a => ((type_of a)⦃f⦄,, reind_tm f a).
  
  (** An _environment_ over [Γ]: a map giving, for each variable from some potential context, a type and a term of that type.

  Motivating example: if [Γ] is the interpretation of some actual context, then each type of the context should be interpreted as some type over Γ, and each the corresponding variable can be extracted to a term of that type. *)

  Definition environment (Γ:C) (n:nat)
    := dB_vars n -> term_with_type Γ.
  
  Definition extend_environment
      {Γ:C} {n:nat} (E : environment Γ n) (A : C Γ)
    : environment (Γ ◂ A) (S n).
  Proof.
    refine (dB_Sn_rect _ _ _).
    - exists (A ⦃dpr_typecat A⦄).
      admit. (* the “universal term of type A” *)
    - intro i.
      exact (reind_term_with_type (dpr_typecat A) (E i)).
  Admitted.

End Environments.

Section Partial_Interpretation.
(** In this section, we construct the partial interpretation function. *)

  Context {C : split_typecat}.

  Fixpoint
    partial_interpretation_ty
      {Γ:C} {n:nat} (E : environment Γ n) (e : ty_expr n)
    : partial (C Γ)
  with
    partial_interpretation_tm
      {Γ:C} {n:nat} (E : environment Γ n) (A : C Γ) (e : tm_expr n)
    : partial (tm A).
  Proof.
    (* TODO! *)
  Admitted.
  

  (* Note: alternatively, we could give the interpretation of terms as 
   [ partial_interpretation_tm
       {Γ:C} {n:nat} (E : environment Γ n) (e : tm_expr n)
     : partial (term_with_type Γ). ]
  I think either should work fine; I’m not sure which will work more cleanly. *)

End Partial_Interpretation.
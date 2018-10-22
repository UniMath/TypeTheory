(** This file defines:

- logical structure on split type-categories, intended to correspond to the type theory presented in [Initiality.Syntax], [Initiality.Typing];
- and what it means for maps of split type-cats to preserve this logical structure. *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.All.

Require Import TypeTheory.Auxiliary.CategoryTheoryImports.
Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.Initiality.SplitTypeCat_Maps.


(* Define basic structures on a CwF: for now only a base type and a
dependent family on the base type *)
Section basic_structs.

Context (C : split_typecat).

Definition basetype_struct : UU :=
  ∑ U : ∏ Γ, C Γ, ∏ Δ Γ (σ : Δ --> Γ), U Δ = U Γ ⦃σ⦄.

Definition basetype_struct_pr1 : basetype_struct → ∏ Γ, C Γ := pr1.

Coercion basetype_struct_pr1 : basetype_struct >-> Funclass.

Definition deptype_struct (U : basetype_struct) : UU.
Proof.
use (∑ (D : ∏ Γ, C (Γ ⋆ U Γ)), _).
use (∏ Δ Γ (σ : C ⟦ Δ, Γ ⟧), _).
apply (D Γ ⦃comp_ext_compare (pr2 U _ _ σ) · q_typecat (U Γ) σ⦄ = D Δ).
    (* Version of the equation using transport *)
    (* transportf (λ x : C Δ, C (Δ ⋆ x)) (pr2 U Δ Γ σ) *)
    (*            (D Γ ⦃q_typecat (U Γ) σ⦄) = D Δ. *)
Defined. 

End basic_structs.


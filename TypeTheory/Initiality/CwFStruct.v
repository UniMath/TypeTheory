
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Adjunctions.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.equivalences.
Require Import UniMath.CategoryTheory.RightKanExtension.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.eqdiag.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.ElementsOp.

Require Import TypeTheory.Auxiliary.CategoryTheoryImports.
Require Import TypeTheory.Auxiliary.Auxiliary.

(* We stick to this definition of CwF *)
Require Import TypeTheory.ALV1.TypeCat.

(* Lots of useful lemmas *)
(* Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Defs. *)
(* Require Import TypeTheory.ALV1.TypeCat_Reassoc. *)


(* This one was annoying to use *)
(* Require Import TypeTheory.OtherDefs.CwF_Pitts. *)

Local Open Scope cat.

(* Define nicer notations *)
Local Notation "A ⦃ s ⦄" := (reind_typecat A s) (at level 40, format "A  ⦃ s ⦄").
Local Notation "Γ ⋆ A" := (ext_typecat Γ A) (at level 30).

(* Define basic structures on a CwF: for now only a base type and a
dependent family on the base type *)
Section basic_structs.

Context {CT : precategory} (C : typecat_structure CT).

Definition basetype_struct : UU :=
  ∑ U : ∏ Γ, C Γ, ∏ Δ Γ (σ : Δ --> Γ), U Δ = U Γ ⦃σ⦄.

Definition basetype_struct_pr1 : basetype_struct → ∏ Γ, C Γ := pr1.

Coercion basetype_struct_pr1 : basetype_struct >-> Funclass.

(* Trick inspired by TypeTheory.ALV1.CwF_SplitTypeCat_Defs *)
Definition comp_ext_compare {C : precategory} {X : typecat_structure C}
  {Γ : C} {A A' : X Γ} (e : A = A') :
   Γ ◂ A --> Γ ◂ A' := idtoiso (maponpaths (ext_typecat Γ) e).

Definition deptype_struct (U : basetype_struct) : UU.
Proof.
use (∑ (D : ∏ Γ, C (Γ ⋆ U Γ)), _).
use (∏ Δ Γ (σ : CT ⟦ Δ, Γ ⟧), _).
apply (D Γ ⦃comp_ext_compare (pr2 U _ _ σ) · q_typecat (U Γ) σ⦄ = D Δ).
    (* Version of the equation using transport *)
    (* transportf (λ x : C Δ, C (Δ ⋆ x)) (pr2 U Δ Γ σ) *)
    (*            (D Γ ⦃q_typecat (U Γ) σ⦄) = D Δ. *)
Defined. 

End basic_structs.


Definition ty {CT : precategory} (C : split_typecat_structure CT) : PreShv CT.
Proof.
use mk_functor.
- use mk_functor_data.
  intros x.
  exists (ty_typecat C x).
  now apply isaset_types_typecat, is_split_from_split_typecat.
intros a b f x.
simpl in *.
exact (@reind_typecat CT C a x b f).
- admit.
Admitted.

Section morphisms.

Context {CT DT : category} (C : split_typecat_structure CT) (D : split_typecat_structure DT).

(* This consists of a pair of 

- a functor F : CT -> DT
- a natural transformation F_Ty : Ty C -> Ty D

strictness everywhere except isomorphism

ϕ : F(Γ.A) ≃ F(Γ).F_Ty(A)

satisfying naturality square. 

*)


Definition typecat_mor : UU.
Proof.
About nat_trans.
use (∑ (F : functor CT DT), _).
use (∑ (FTy : nat_trans (pr1 (ty C)) (pr1 (functor_compose _ _ (functor_opp F) (ty D)))), _).
now apply has_homsets_opp, homset_property.

admit.


End morphisms.
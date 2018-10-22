
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
  + intros x.
    exists (ty_typecat C x).
    abstract (now apply isaset_types_typecat, is_split_from_split_typecat).
  + intros a b f x.
    exact (@reind_typecat CT C a x b f).
- use tpair.
  + intros x.
    apply funextfun; intros y; simpl.
    now apply reind_id_type_typecat, is_split_from_split_typecat.
  + intros x y z f g; cbn.
    apply funextfun; intros a.
    now apply reind_comp_type_typecat, is_split_from_split_typecat.
Defined.

Section morphisms.

Context {CT DT : category}
        (C : split_typecat_structure CT)
        (D : split_typecat_structure DT).

(* This consists of a pair of 

- a functor F : CT -> DT
- a natural transformation F_Ty : Ty C -> Ty D

strictness everywhere except isomorphism

ϕ : F(Γ.A) ≃ F(Γ).F_Ty(A)

satisfying naturality pentagon...

*)

Definition typecat_mor : UU.
Proof.
use (∑ (F : functor CT DT), _).

use (∑ (FTy : PreShv CT ⟦ty C, functor_opp F ∙ ty D⟧), _).

use (∑ (extiso : ∑ (i : ∏ (Γ : CT) (A : C Γ), iso (F (Γ ⋆ A)) (F Γ ⋆ pr1 FTy _ A)),
                 ∏ (Γ Γ' : CT) (A : C Γ) (f : Γ' --> Γ),
                  # F (q_typecat A f) · i _ _ =
                  i _ _ ·
                  comp_ext_compare (eqtohomot (nat_trans_ax FTy _ _ f) A) ·
                  q_typecat (pr1 FTy _ A) (# F f)), _).

(* TODO: express what it means to preserve the rest of the structure *)

  (* C : precategory ; *)

  (* ty : C -> Type   
       where "C ⟨ Γ ⟩" := (ty Γ); *)

  (* ext : ∏ Γ, C⟨Γ⟩ -> C
       where "Γ ◂ A" := (ext Γ A); *)

  (* dpr : ∏ Γ (A : C⟨Γ⟩), Γ ◂ A --> Γ
       where "'π' A" := (dpr _ A); *)

  (* reind : ∏ Γ (A : C⟨Γ⟩) Γ' (f : Γ' --> Γ), C⟨Γ'⟩
       where "A {{ f }}" := (reind _ A _ f)  ; *)

  (* q : ∏ {Γ} (A : ty Γ) {Γ'} (f : Γ' --> Γ), *)
  (*         (Γ' ◂ (A {{f }}) --> Γ ◂ A) ; *)

  (* dpr_q : ∏ Γ (A : C⟨Γ⟩) Γ' (f : Γ' --> Γ),  *)
  (*         (q A f) ;; (π A) = (π (A{{f}})) ;; f ; *)

  (* reind_pb : ∏ Γ (A : ty Γ) Γ' (f : Γ' --> Γ), *)
  (*     isPullback _ _ _ _ (!dpr_q _ A _ f) *)
Admitted.

End morphisms.
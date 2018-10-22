
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
Require Import TypeTheory.ALV1.TypeCat.

Local Open Scope cat.

(** We base our models on _split type-categories_, i.e. [split_typecat] as defined in [TypeTheory.ALV1.TypeCat] following Pitts and van den Berg–Garner.
(Roughly the same as what Hofmann calls CwA’s.) *)

(** Notations for working in split type cats *)
Local Notation "A ⦃ s ⦄" := (reind_typecat A s) (at level 40, format "A  ⦃ s ⦄").
Local Notation "Γ ⋆ A" := (ext_typecat Γ A) (at level 30, only parsing).

Section Auxiliary.
(** General interface functions for working in split type-cats;
could well be upstreamed to [TypeTheory.ALV1.TypeCat]. *)

Section Comp_Ext_Compare.
  (* History note: nased on same-named functions in [TypeTheory.ALV1.CwF_SplitTypeCat_Defs], given there for a reassociated version of split type-categories. *)

  Definition comp_ext_compare {C : typecat}
      {Γ : C} {A A' : C Γ} (e : A = A')
    : iso (Γ ◂ A) (Γ ◂ A')
  := idtoiso (maponpaths (ext_typecat Γ) e).

  Lemma comp_ext_compare_id {C : typecat}
      {Γ : C} (A : C Γ)
    : (comp_ext_compare (idpath A) : _ --> _) = identity (Γ ◂ A).
  Proof.
    apply idpath.
  Qed.

  Lemma comp_ext_compare_id_general {C : split_typecat}
      {Γ : C} {A : C Γ} (e : A = A)
    : (comp_ext_compare e : _ --> _) = identity (Γ ◂ A).
  Proof.
    apply @pathscomp0 with (comp_ext_compare (idpath _)).
    - apply maponpaths, maponpaths, (isaset_types_typecat C).
    - apply idpath.
  Qed.

  Lemma comp_ext_compare_comp {C : split_typecat}
    {Γ : C} {A A' A'' : C Γ} (e : A = A') (e' : A' = A'')
  : (comp_ext_compare (e @ e') : _ --> _)
    = comp_ext_compare e ;; comp_ext_compare e'.
  Proof.
    apply pathsinv0.
    etrans. { apply idtoiso_concat_pr. }
    unfold comp_ext_compare. apply maponpaths, maponpaths.
    apply pathsinv0, maponpathscomp0. 
  Qed.

End Comp_Ext_Compare.

  Definition ty (C : split_typecat) : PreShv C.
  Proof.
    use mk_functor.
    - use mk_functor_data.
      + intros x.
        exists (ty_typecat C x).
        abstract (apply isaset_types_typecat, C).
      + simpl; intros Γ Γ' f A.
        exact (reind_typecat A f).
    - use tpair.
      + intros Γ.
        abstract (apply funextfun; intros y; simpl;
                  apply reind_id_type_typecat, C).
      + cbn; intros Γ Γ' Γ'' f g.
        abstract (apply funextfun; intros A;
                  apply reind_comp_type_typecat, C).
  Defined.

End Auxiliary.

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

Section morphisms.

Context (C D : split_typecat).

(* This consists of a pair of 

- a functor F : CT -> DT
- a natural transformation F_Ty : Ty C -> Ty D

strictness everywhere except isomorphism

ϕ : F(Γ.A) ≃ F(Γ).F_Ty(A)

satisfying naturality pentagon...

*)

Definition typecat_mor : UU.
Proof.
use (∑ (F : functor C D), _).

use (∑ (FTy : PreShv C ⟦ty C, functor_opp F ∙ ty D⟧), _).

use (∑ (extiso : ∑ (i : ∏ (Γ : C) (A : C Γ), iso (F (Γ ⋆ A)) (F Γ ⋆ pr1 FTy _ A)),
                 ∏ (Γ Γ' : C) (A : C Γ) (f : Γ' --> Γ),
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
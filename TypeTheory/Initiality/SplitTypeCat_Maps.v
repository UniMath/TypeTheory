(** This file defines _maps_ of split type-categories. *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.All.

Require Import TypeTheory.Auxiliary.CategoryTheoryImports.
Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.Initiality.SplitTypeCat_General.

Local Open Scope cat.

(** We base our models on _split type-categories_, i.e. [split_typecat] as defined in [TypeTheory.ALV1.TypeCat] following Pitts and van den Berg–Garner.
(Roughly the same as what Hofmann calls CwA’s.) *)

Section morphisms.

Context (C D : split_typecat).

(* The definition of a morphism between split typecategories
constsists of (modulo ^op):

- a functor F : C -> D
- a natural transformation FTy : Ty C -> Ty D
- a familry of isomorphisms ϕ : F(Γ.A) ≃ F(Γ).F_Ty(A)

satisfying triangle:

           ϕ
F (Γ · A) --> F Γ · FTy A
      \         /
       \       /
    F p \     / p
         \   /
          \ /
           V
          F Γ

and a pentagon stating that the following morphisms are equal:

                  F q                        ϕ
F (Γ' ⋆ A⦃f⦄) ----------> F (Γ ⋆ A) ---------------> F Γ ⋆ FTy A


F (Γ' ⋆ A⦃f⦄) ------> F Γ' ⋆ (F A)⦃f⦄ -----> F Γ' ⋆ F A⦃f⦄ ------> F Γ ⋆ FTy A
                 ϕ                       =                     q

*)
Definition typecat_mor : UU
  := ∑ (F : functor C D)
       (FTy : PreShv C ⟦ty C, functor_opp F ∙ ty D⟧)
       (ϕ : ∏ (Γ : C) (A : C Γ), iso (F (Γ ⋆ A)) (F Γ ⋆ pr1 FTy _ A)),
         (∏ Γ (A : C Γ), # F (dpr_typecat A) = ϕ _ A · dpr_typecat (pr1 FTy _ A))
       × (∏ Γ Γ' (A : C Γ) (σ : Γ' --> Γ),
            # F (q_typecat A σ) · ϕ Γ A =
            ϕ Γ' _ · comp_ext_compare (eqtohomot (nat_trans_ax FTy σ) A) ·
              q_typecat (pr1 FTy _ A) (# F σ)).

Definition mk_typecat_mor
  (F : functor C D)
  (FTy : PreShv C ⟦ty C, functor_opp F ∙ ty D⟧)
  (ϕ : ∏ (Γ : C) (A : C Γ), iso (F (Γ ⋆ A)) (F Γ ⋆ pr1 FTy _ A))
  (H1 : ∏ Γ (A : C Γ), # F (dpr_typecat A) = ϕ _ A · dpr_typecat (pr1 FTy _ A))
  (H2 : ∏ Γ Γ' (A : C Γ) (σ : Γ' --> Γ),
        # F (q_typecat A σ) · ϕ Γ A =
        ϕ Γ' _ · comp_ext_compare (eqtohomot (nat_trans_ax FTy σ) A) ·
          q_typecat (pr1 FTy _ A) (# F σ)) : typecat_mor.
Proof.
exists F, FTy, ϕ; split; [ apply H1 | apply H2 ].
Defined.

Definition typecat_mor_functor {f : typecat_mor} : functor C D := pr1 f.
Coercion typecat_mor_functor : typecat_mor >-> functor.

Definition typecat_mor_Ty (f : typecat_mor) :
  PreShv C ⟦ty C, functor_opp f ∙ ty D⟧ := pr12 f.

Definition typecat_mor_nat_trans (f : typecat_mor) :
  nat_trans (pr1 (ty C)) (functor_opp f ∙ ty D) := typecat_mor_Ty f.

Definition typecat_mor_iso (f : typecat_mor) {Γ} (A : C Γ) :
  iso (f (Γ ⋆ A)) (f Γ ⋆ typecat_mor_nat_trans f Γ A) := pr122 f Γ A.

Definition typecar_mor_triangle (f : typecat_mor) {Γ} (A : C Γ) :
  # f (dpr_typecat A) = typecat_mor_iso f A · dpr_typecat (typecat_mor_nat_trans f _ A) := pr1 (pr222 f) Γ A.

Definition typecat_mor_pentagon (f : typecat_mor) {Γ Γ'} (A : C Γ) (σ : Γ' --> Γ) :
  # f (q_typecat A σ) · typecat_mor_iso f A =
  typecat_mor_iso f _ · comp_ext_compare (eqtohomot (nat_trans_ax (typecat_mor_nat_trans f) σ) A) ·
    q_typecat (typecat_mor_nat_trans f Γ A) (# f σ) := pr2 (pr222 f) Γ Γ' A σ.

End morphisms.
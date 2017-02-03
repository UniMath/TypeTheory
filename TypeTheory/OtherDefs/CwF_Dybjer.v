
(**

 Ahrens, Lumsdaine, Voevodsky, 2015

  Contents:

    - Definition of a precategory with families, as presented in Dybjer's *Internal type theory*, http://www.cse.chalmers.se/~peterd/papers/InternalTT.pdf (page=

*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.category_hset.
Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.
Require Import TypeTheory.Categories.category_FAM.

Local Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op").
Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "C ⦃ a , b ⦄" := (precategory_morphisms (C:=C) a b) (at level 50).
(** * A "preview" of the definition *)

Module Record_Preview.

Reserved Notation "C ⟨ Γ ⟩" (at level 60).
Reserved Notation "C ⟨ Γ ⊢ A ⟩" (at level 60).
Reserved Notation "A [ γ ]" (at level 40).
Reserved Notation "a ⟦ γ ⟧" (at level 40).
Reserved Notation "Γ ∙ A" (at level 20).
Reserved Notation "'π' A" (at level 20).
Reserved Notation "'ν' A" (at level 15).
Reserved Notation "γ ♯ a" (at level 25).

Notation "A ₁" := (index_type _ A)(at level 3).
Notation "A ₂" := (index_func _ A)(at level 3).

Record precwf_record : Type := {
  C :> precategory ;
  T : functor C^op (FAM(HSET))  where "C ⟨ Γ ⟩" := ((T Γ) ₁);
                                  (* "C ⟨ Γ ⊢ A ⟩" := ((T Γ) ₂ A) *)
  comp_obj : ∏ Γ (A : C⟨Γ⟩), C where "Γ ∙ A" := (comp_obj Γ A) ;
  proj_mor : ∏ Γ (A : C⟨Γ⟩), C ⦃Γ ∙ A, Γ⦄ where "'π' A" := (proj_mor _ A) ;
  q : ∏ Γ (A : C ⟨Γ⟩), pr1 ((T _)₂ (pr1 (# T (π A)) A));
  univ_prop : ∏ Γ (A : C ⟨Γ⟩) Δ (γ : C⦃Δ, Γ⦄) (a : pr1 ((T _)₂ (pr1 (# T γ) A))),
        iscontr (∑ (θ : Δ --> Γ ∙ A),
                 ∑ (e : θ ;; π A = γ),
                 pr2 (# T θ) _ (q _ A)
                 = 
                  transportf (fun f => pr1 ((T Δ)₂ (pr1 f A)))
                             (functor_comp T _ _ _ _ _)
                  (transportb (fun f => pr1 ((T Δ)₂ (pr1 (# T f) A))) e
                 a))
 }.

End Record_Preview.

(** This file defines:

- logical structure on split type-categories, intended to correspond to the type theory presented in [Initiality.Syntax], [Initiality.Typing];
- and what it means for maps of split type-cats to preserve this logical structure. *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.All.

Require Import TypeTheory.Auxiliary.CategoryTheoryImports.
Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.Initiality.SplitTypeCat_Maps.

Section Bare_Universe_Structure.
(** The structure of a “bare à-la-Tarski universe” in a split type-cat: a base type (the universe) with a family of types over it (the “El” family).  *)

  Context (C : split_typecat).

  Definition basetype_struct : UU
  :=  ∑ U : (forall Γ, C Γ),
        forall Γ Δ (σ : Δ --> Γ), U Γ ⦃σ⦄ = U Δ.

  Definition basetype_struct_pr1 : basetype_struct -> ∏ Γ, C Γ := pr1.
  Coercion basetype_struct_pr1 : basetype_struct >-> Funclass.
  
  Definition basetype_natural {U : basetype_struct} {Γ Γ'} (f : Γ' --> Γ)
    :  U Γ ⦃f⦄ = U Γ'
  := pr2 U _ _ f.

  Definition deptype_struct (U : basetype_struct) : UU.
  Proof.
    use (∑ (D : ∏ Γ, C (Γ ◂ U Γ)), _).
    use (∏ Δ Γ (σ : C ⟦ Δ, Γ ⟧), _).
    exact (D Γ ⦃q_typecat (U Γ) σ⦄
           = D Δ ⦃ comp_ext_compare (basetype_natural σ) ⦄).
  Defined.

  Definition deptype_struct_pr1 {U} (El : deptype_struct U) := pr1 El.
  Coercion deptype_struct_pr1 : deptype_struct >-> Funclass.

  Definition deptype_struct_natural {U} (El : deptype_struct U) := pr2 El.
End Bare_Universe_Structure.

Section Pi_Structure.
(** The structure to model Pi-types in a split type-category. *)

  Context (C : split_typecat).

  Definition pi_form_struct : UU
  := ∑ (Π : forall (Γ : C) (A : C Γ) (B : C (Γ ◂ A)), C Γ),
       (forall (Γ Γ' : C) (f : Γ' --> Γ) (A : C Γ) (B : C (Γ ◂ A)),
         (Π Γ A B) ⦃ f ⦄ = Π Γ' (A⦃f⦄) (B⦃q_typecat _ _⦄)).

  Definition pi_form_struct_pr1 (Π : pi_form_struct) := pr1 Π.
  Coercion pi_form_struct_pr1 : pi_form_struct >-> Funclass.

  Definition pi_form_struct_natural {Π : pi_form_struct}
      {Γ Γ'} (f : Γ' --> Γ) (A : C Γ) B
    : (Π _ A B) ⦃ _ ⦄ = Π Γ' _ _ 
  := pr2 Π _ _ f A B.
  
  Definition pi_intro_struct (Π : pi_form_struct) : UU
  := ∑ (lambda : forall (Γ : C) (A : C Γ) (B : C (Γ ◂ A)) (b : tm B),
         tm (Π _ A B)),
       (forall (Γ Γ' : C) (f : Γ' --> Γ) A B b,
         reind_tm f (lambda Γ A B b)
         = tm_transportb (pi_form_struct_natural _ _ _)
           (lambda Γ' _ _ (reind_tm _ b))).

  Definition pi_intro_struct_pr1 {Π} (lam : pi_intro_struct Π) := pr1 lam.
  Coercion pi_intro_struct_pr1 : pi_intro_struct >-> Funclass.

  Definition pi_intro_struct_natural {Π} (lam : pi_intro_struct Π)
      {Γ Γ'} (f : Γ' --> Γ) A B b
    : reind_tm f (lam _ A B b)
      = tm_transportb _ (lam Γ' _ _ _) 
  := pr2 lam _ _ f A B b.

  Lemma pi_app_struct_aux 
        {Γ Γ' : C} (f : Γ' --> Γ)
        {A : C Γ} (B : C (Γ ◂ A)) (a : tm A)
    : (B ⦃a⦄) ⦃f⦄ = (B ⦃q_typecat A f⦄) ⦃reind_tm f a⦄.
  Proof.
    refine (!reind_comp_typecat C _ _ _ _ _ _ @
             _ @ reind_comp_typecat C _ _ _ _ _ _).
    apply maponpaths.
    admit. (* should be lemma about [reind_tm] *)
  Admitted.

  Definition pi_app_struct (Π : pi_form_struct) : UU
  := ∑ (app : forall (Γ : C) (A : C Γ) (B : C (Γ ◂ A))
                     (p : tm (Π _ A B)) (a : tm A),
         tm (B⦃a⦄)),
     (forall (Γ Γ' : C) (f : Γ' --> Γ) A B p a,
       reind_tm f (app Γ A B p a)
       = tm_transportb (pi_app_struct_aux _ _ _)
         (app Γ' _ _ 
           (tm_transportf (pi_form_struct_natural _ _ _) (reind_tm f p))
           (reind_tm f a))).

  Definition pi_app_struct_pr1 {Π} (app : pi_app_struct Π) := pr1 app.
  Coercion pi_app_struct_pr1 : pi_app_struct >-> Funclass.

  Definition pi_app_struct_natural {Π} (app : pi_app_struct Π)
      {Γ Γ'} (f : Γ' --> Γ) {A} {B} p a
    : reind_tm f (app Γ A B p a)
    = tm_transportb _ (app _ _ _ _ _)
  := pr2 app _ _ f A B p a.

  Definition pi_comp_struct
      {Π} (lam : pi_intro_struct Π) (app : pi_app_struct Π)
    : UU
  := forall (Γ : C) (A : C Γ) (B : C (Γ ◂ A)) (b : tm B) (a : tm A),
      app Γ A B (lam _ _ _ b) a = reind_tm a b.

End Pi_Structure.

(** This file defines:

- logical structure on split type-categories, intended to correspond to the type theory presented in [Initiality.Syntax], [Initiality.Typing];
- and what it means for maps of split type-cats to preserve this logical structure. *)

Require Import UniMath.MoreFoundations.All.

Require Import TypeTheory.Auxiliary.CategoryTheoryImports.
Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.Initiality.SplitTypeCat_General.
Require Import TypeTheory.Initiality.SplitTypeCat_Maps.

Section Bare_Universe_Structure.
(** The structure of a “bare à-la-Tarski universe” in a split type-cat: a base type (the universe) with a family of types over it (the “El” family).  *)

  Context (C : typecat).

  Definition basetype_struct : UU
  :=  ∑ U : (forall Γ, C Γ),
        forall Γ Δ (f: Δ --> Γ), U Γ ⦃f⦄ = U Δ.

  Definition basetype_struct_pr1 : basetype_struct -> ∏ Γ, C Γ := pr1.
  Coercion basetype_struct_pr1 : basetype_struct >-> Funclass.
  
  Definition basetype_natural {U : basetype_struct} {Γ Γ'} (f : Γ' --> Γ)
    :  U Γ ⦃f⦄ = U Γ'
  := pr2 U _ _ f.

  Definition deptype_struct (U : basetype_struct) : UU.
  Proof.
    use (∑ (D : ∏ Γ (a : tm (U Γ)), C Γ), _).
    use (∏ Δ Γ (f : C ⟦ Δ, Γ ⟧) (a : tm (U Γ)), _).
    refine ((D Γ a) ⦃f⦄ = D Δ _).
    exact (tm_transportf (basetype_natural f) (reind_tm f a)).
  Defined.

  Definition deptype_struct_pr1 {U} (El : deptype_struct U) := pr1 El.
  Coercion deptype_struct_pr1 : deptype_struct >-> Funclass.

  Definition deptype_struct_natural {U} (El : deptype_struct U) := pr2 El.

  Definition universe_struct
  := ∑ (U : basetype_struct), deptype_struct U.

  Coercion universe (U : universe_struct) : basetype_struct := pr1 U.

  Definition universe_natural (U : universe_struct) := @basetype_natural U.

  Definition elements {U : universe_struct} : deptype_struct U := pr2 U.

  Definition elements_natural {U : universe_struct}
    := deptype_struct_natural (@elements U).

End Bare_Universe_Structure.

Arguments elements {_ _}.

Section Universe_Preservation.

  Definition preserves_basetype_struct
      {C : split_typecat} (U : basetype_struct C)
      {C' : split_typecat} (U' : basetype_struct C')
      (F : typecat_mor C C')
    : UU
  := forall (Γ : C), typecat_mor_Ty F _ (U Γ)
                     = U' (F Γ).

  Identity Coercion id_preserves_basetype_struct
    : preserves_basetype_struct >-> Funclass.

  Definition preserves_deptype_struct
      {C : split_typecat} {U : basetype_struct C} (El : deptype_struct C U)
      {C' : split_typecat} {U' : basetype_struct C'} (El' : deptype_struct C' U')
      (F : typecat_mor C C') (F_U : preserves_basetype_struct U U' F)
    : UU
  := forall (Γ : C) (a : tm (U Γ)),
            typecat_mor_Ty F _ (El _ a)
            = El' _ (tm_transportf (F_U _) (fmap_tm F a)).

  Identity Coercion id_preserves_deptype_struct
    : preserves_deptype_struct >-> Funclass.

  Definition preserves_universe_struct
      {C : split_typecat} (U : universe_struct C)
      {C' : split_typecat} (U' : universe_struct C')
      (F : typecat_mor C C')
  := ∑ F_U, preserves_deptype_struct (@elements _ U) (@elements _ U') F F_U.

  Definition fmap_universe
      {C : split_typecat} {U : universe_struct C}
      {C' : split_typecat} {U' : universe_struct C'}
      {F : typecat_mor C C'} (F_U : preserves_universe_struct U U' F)
  := pr1 F_U : preserves_basetype_struct _ _ _.

  Definition fmap_elements
      {C : split_typecat} {U : universe_struct C}
      {C' : split_typecat} {U' : universe_struct C'}
      {F : typecat_mor C C'} (F_U : preserves_universe_struct U U' F)
  : forall (Γ : C) (a : tm (U Γ)),
            typecat_mor_Ty F _ (elements _ a)
            = elements _ (tm_transportf (fmap_universe F_U _) (fmap_tm F a))
  := pr2 F_U.

End Universe_Preservation.

Section Pi_Structure.
(** The structure to model Pi-types in a split type-category. *)

  Context (C : split_typecat).

  Definition pi_form_struct : UU
  := ∑ (Π : forall (Γ : C) (A : C Γ) (B : C (Γ ◂ A)), C Γ),
       (forall (Γ Γ' : C) (f : Γ' --> Γ) (A : C Γ) (B : C (Γ ◂ A)),
         (Π Γ A B) ⦃ f ⦄ = Π Γ' (A⦃f⦄) (B⦃q_typecat A f⦄)).

  Definition pi_form_struct_pr1 (Π : pi_form_struct) := pr1 Π.
  Coercion pi_form_struct_pr1 : pi_form_struct >-> Funclass.

  Definition pi_form_struct_natural {Π : pi_form_struct}
      {Γ Γ'} (f : Γ' --> Γ) (A : C Γ) B
    : (Π _ A B) ⦃ f ⦄ = Π Γ' _ _ 
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
    refine (!reind_comp_typecat _ _ _ _ _ _ @
             _ @ reind_comp_typecat _ _ _ _ _ _).
    now apply maponpaths; rewrite (reind_tm_q f).
  Qed.
  
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

  Definition pi_struct : UU
  := ∑ (Π : pi_form_struct)
       (lam_app : (pi_intro_struct Π) × (pi_app_struct Π)),
     (pi_comp_struct (pr1 lam_app) (pr2 lam_app)).

  Coercion pi_form (Π : pi_struct) : pi_form_struct := pr1 Π.

  Definition pi_intro (Π : pi_struct) : pi_intro_struct Π := pr112 Π.

  Definition pi_app (Π : pi_struct) : pi_app_struct Π := pr212 Π.

  Definition pi_comp (Π : pi_struct) : pi_comp_struct (pi_intro Π) (pi_app Π)
    := pr22 Π.

End Pi_Structure.

Arguments pi_form {_} _.
Arguments pi_intro {_} _.
Arguments pi_app {_} _.
Arguments pi_comp {_} _.

Section Pi_Preservation.

  Definition preserves_pi_form_struct
      {C} (Π : pi_form_struct C)
      {C'} (Π' : pi_form_struct C')
      (F : typecat_mor C C')
    : UU
  := forall Γ A B,
    typecat_mor_Ty F _ (Π Γ A B)
    = Π' (F Γ) 
         (typecat_mor_Ty F _ A)
         ((typecat_mor_Ty F _ B) ⦃inv_from_iso (typecat_mor_iso F A)⦄).

  Definition preserves_pi_intro_struct
      {C} {Π : pi_form_struct C} (lam : pi_intro_struct C Π)
      {C'} {Π' : pi_form_struct C'} (lam' : pi_intro_struct C' Π')
      {F : typecat_mor C C'} (F_Π : preserves_pi_form_struct Π Π' F)
    : UU
  := forall Γ A B b,
    fmap_tm F (lam Γ A B b)
    = tm_transportb (F_Π _ _ _)
      (lam' (F Γ)
         (typecat_mor_Ty F _ A)
         ((typecat_mor_Ty F _ B) ⦃inv_from_iso (typecat_mor_iso F A)⦄)
         (reind_tm (inv_from_iso (typecat_mor_iso F A))
           (fmap_tm F b))).

  Definition preserves_pi_app_struct
      {C} {Π : pi_form_struct C} (app : pi_app_struct C Π)
      {C'} {Π' : pi_form_struct C'} (app' : pi_app_struct C' Π')
      {F : typecat_mor C C'} (F_Π : preserves_pi_form_struct Π Π' F)
    : UU
  := forall Γ A B t a,
    fmap_tm F (app Γ A B t a)
    = tm_transportb (reindex_fmap_ty _ _ _
                    @ maponpaths _ (fmap_tm_as_map _ _)
                    @ reind_comp_typecat _ _ _ _ _ _)
      (app' (F Γ)
         (typecat_mor_Ty F _ A)
         ((typecat_mor_Ty F _ B) ⦃inv_from_iso (typecat_mor_iso F A)⦄)
         (tm_transportf (F_Π _ _ _) (fmap_tm F t)) 
         (fmap_tm F a)).

  Definition preserves_pi_struct
      {C} (Π : pi_struct C)
      {C'} (Π' : pi_struct C')
      (F : typecat_mor C C')
    : UU
  := ∑ (F_Π : preserves_pi_form_struct Π Π' F),
       (preserves_pi_intro_struct (pi_intro Π) (pi_intro Π') F_Π)
         × (preserves_pi_app_struct (pi_app Π) (pi_app Π') F_Π).

  Definition fmap_pi_form
      {C} {Π : pi_struct C}
      {C'} {Π' : pi_struct C'}
      {F : typecat_mor C C'} (F_Π : preserves_pi_struct Π Π' F)
  := pr1 F_Π.

  Definition fmap_pi_intro
      {C} {Π : pi_struct C}
      {C'} {Π' : pi_struct C'}
      {F : typecat_mor C C'} (F_Π : preserves_pi_struct Π Π' F)
  := pr12 F_Π : preserves_pi_intro_struct _ _ (fmap_pi_form F_Π).

  Definition fmap_pi_app
      {C} {Π : pi_struct C}
      {C'} {Π' : pi_struct C'}
      {F : typecat_mor C C'} (F_Π : preserves_pi_struct Π Π' F)
  := pr22 F_Π : preserves_pi_app_struct _ _ (fmap_pi_form F_Π).

End Pi_Preservation.
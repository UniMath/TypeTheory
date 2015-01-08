
Require Export Systems.UnicodeNotations.
Require Export UniMath.Foundations.hlevel2.hSet.
Require Export UniMath.RezkCompletion.precategories.

Local Notation "a ⇒ b" := (precategory_morphisms a b)(at level 50).
Local Notation "f ∙ g" := (compose f g)(at level 50).


(* it might be better to map to UU (the universe), and give the 
hSet condition later *)

Definition tt_structure (C : precategory) :=
  Σ f : C → hSet, ∀ c : C, f c → hSet.

Definition tt_precat : UU := Σ C : precategory, tt_structure C.
Definition precat_from_tt_precat (C : tt_precat) : precategory := pr1 C.
Coercion precat_from_tt_precat : tt_precat >-> precategory.

Definition type (C : tt_precat) : C → hSet := pr1 (pr2 C).

Notation "C ⟨ Γ ⟩" := (type C Γ) (at level 60).

Definition term (C : tt_precat) : ∀ Γ : C, C⟨Γ⟩ → hSet := pr2 (pr2 C).

Notation "C ⟨ Γ ⊢ A ⟩" := (term C Γ A) (at level 60).

(* reindexing *)

Definition reindx_structure (C : tt_precat) := 
   Σ (rtype : ∀ {Γ Γ' : C} (A : C⟨Γ⟩) (γ : Γ' ⇒ Γ), C⟨Γ'⟩),
        ∀ (Γ Γ' : C) (A : C⟨Γ⟩) (a : C⟨Γ⊢A⟩) (γ : Γ' ⇒ Γ), C⟨Γ'⊢rtype A γ⟩.

Definition reindx_precat := Σ (C : tt_precat), reindx_structure C.

Definition tt_precat_from_reindx_precat (C : reindx_precat) : tt_precat := pr1 C.
Coercion tt_precat_from_reindx_precat : reindx_precat >-> tt_precat.

Definition rtype {C : reindx_precat} : ∀ {Γ Γ' : C} (A : C⟨Γ⟩) (γ : Γ' ⇒ Γ), C⟨Γ'⟩ := 
   pr1 (pr2 C).

Notation "A [ γ ]" := (rtype A γ) (at level 50).

Definition rterm {C : reindx_precat} : ∀ {Γ Γ' : C} {A : C⟨Γ⟩} 
    (a : C⟨Γ⊢A⟩) (γ : Γ' ⇒ Γ), C⟨Γ'⊢ A[γ]⟩ := 
    pr2 (pr2 C).

Notation "a ⟦ γ ⟧" := (rterm a γ) (at level 50).

(* and now a lot of laws *)
(* think about how to package them *)

Definition reindx_laws_type (C : reindx_precat) : UU :=
    (∀ Γ (A : C⟨Γ⟩), A[identity Γ] = A) ×
    (∀ Γ Γ' Γ'' (γ : Γ' ⇒ Γ) (γ' : Γ'' ⇒ Γ') (A : C⟨Γ⟩), A [γ' ∙ γ] = A[γ][γ']). 

 (* needs type reindexing law to typecheck *) 
Definition reindx_laws_terms (C : reindx_precat) (t : reindx_laws_type C) :=
    (∀ Γ (A : C⟨Γ⟩) (a : C⟨Γ⊢A⟩), a⟦identity Γ⟧ = 
          transportf (λ B, C⟨Γ ⊢ B⟩) (!pr1 t _ _) a) ×
    (∀ Γ Γ' Γ'' (γ : Γ' ⇒ Γ) (γ' : Γ'' ⇒ Γ') (A : C⟨Γ⟩) (a : C⟨Γ⊢A⟩),
            a⟦γ' ∙ γ⟧ = 
          transportf (λ B, C⟨Γ'' ⊢ B⟩) (!pr2 t _ _ _ _ _ _ )  (a⟦γ⟧⟦γ'⟧)).
          

(* comprehension *)

Definition comp_struct_1 (C : reindx_precat) :=
  ∀ Γ (A : C⟨Γ⟩), Σ (ΓAπ : Σ ΓA, ΓA ⇒ Γ), C ⟨pr1 ΓAπ ⊢ A [pr2 ΓAπ]⟩.

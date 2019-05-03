(** This file provides a category [VSET]. Under certain assumptions,
    it is shown that [VSET] has CwF structure and is a split type-category.

    The file was created at the UniMath workshop, Birmingham, 2019.*)

Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.MoreFoundations.Univalence.

Require Import TypeTheory.Auxiliary.CategoryTheoryImports.
Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.OtherDefs.CwF_Pitts.

Local Open Scope cat.

Definition Vuni : UU := ∑ (A : hSet), A → hSet.

Definition pr1Vuni : Vuni -> hSet := pr1.
Coercion pr1Vuni : Vuni >-> hSet.

Definition El {V : Vuni} : V → hSet := pr2 V.

(** Given a [V : Vuni], there is a category [VSET V]. The objects are
    elements of [V], i.e. elements of [pr1Vuni V]. The morphisms [a → b],
    for [a,b : V] objects in [VSET V], are the functions [El a → El b]. *)

Section VSET.

Variable V : Vuni.

Definition VSET_precategory : precategory.
Proof.
use tpair.
- use tpair.
  + exists V. exact (λ a b, El a → El b). (* Objects and morphisms. *)
  + use tpair.
    * exact (λ _ a, a).               (* Identity morphisms. *)
    * exact (λ _ _ _ f g x, g (f x)). (* Composition morphisms. *)
- repeat use tpair; cbn; intros; reflexivity. (* Is precategory witness. *)
Defined.

Definition VSET : category.
Proof.
  exists VSET_precategory. intros a b. apply isaset_set_fun_space.
Defined.

End VSET.

(** Let [V : Vuni]. Suppose that for any object [a : V] in [VSET V]
    and function [b : El a → V] there is an object [σ] in [VSET V],
    such that

    <<
      El σ = ( ∑ (x : El a), El (b x) )%set.
    >>

    Then [VSET V] is a split type-category.
*)

Section VSET_TypeCat.

Variable V : Vuni.

Variable Vsig : ∏ (a : V), (El a → V) → V.

Variable Vsig_El :
  ∏ (a : V) (b : El a → V), (∑ (x : El a), El (b x))%set = El (Vsig a b).

Local Notation "Γ ⊢" := (El Γ → VSET V) (at level 50).
Local Notation "Γ ⊢ A" := (∏ (x : El Γ), El (A x)) (at level 50).
Local Notation "A ⦃ s ⦄" := (λ c, A (s c)) (at level 40, format "A ⦃ s ⦄").
Local Notation "Γ ⋆ A" := (Vsig Γ A : ob (VSET V)) (at level 30).

Definition VSET_ctx_proj {Γ : VSET V} {A : Γ ⊢} : Γ ⋆ A --> Γ.
Proof.
cbn. induction (Vsig_El Γ A). exact pr1.
Defined.

Definition VSET_p_gen {Γ Δ : VSET V} {A : Δ ⊢} (σ : Δ --> Γ) : Δ ⋆ A --> Γ.
Proof.
intro a. induction (Vsig_El Δ A). exact (σ (pr1 a)).
Defined.

Definition VSET_q_gen {Γ Δ : VSET V} {A : Γ ⊢} (σ : Δ --> Γ) : (Δ ⋆ (A⦃σ⦄)) ⊢ A⦃VSET_p_gen σ⦄.
Proof.
unfold VSET_p_gen. induction (Vsig_El Δ (A⦃σ⦄)). exact pr2.
Defined.

Definition VSET_subst_pair {Γ Δ : VSET V} {A : Γ ⊢} (σ : Δ --> Γ) (r : Δ ⊢ A⦃σ⦄) : Δ --> Γ ⋆ A.
Proof.
intro a. induction (Vsig_El Γ A). exact (σ a,, r a).
Defined.

Definition VSET_q_gen_mor {Γ Δ : VSET V} (A : Γ ⊢) (σ : Δ --> Γ) : Δ ⋆ (A⦃σ⦄) --> Γ ⋆ A :=
  VSET_subst_pair (VSET_p_gen σ) (VSET_q_gen σ).

Lemma VSET_q_gen_mor_p {Γ Δ : VSET V} (A : Γ ⊢) (σ : Δ --> Γ) :
  VSET_q_gen_mor A σ · VSET_ctx_proj = VSET_ctx_proj · σ.
Proof.
unfold VSET_q_gen_mor, VSET_ctx_proj, VSET_subst_pair, VSET_q_gen, VSET_p_gen.
cbn in *. now do 2 induction Vsig_El.
Defined.

Lemma VSET_isPullback_q_gen_mor {Γ Δ : VSET V} (A : Γ ⊢) (σ : Δ --> Γ) :
  isPullback _ _ _ _ (VSET_q_gen_mor_p A σ).
Proof.
unfold VSET_q_gen_mor, VSET_subst_pair, VSET_ctx_proj, VSET_q_gen, VSET_p_gen.
intros Z h k p. cbn in *.
do 2 induction Vsig_El. cbn in *.
set (tr f (p : pr1⦃h⦄ = f) z := transportf (λ f, El (A (f z))) p (pr2 (h z))).
use tpair.
- exists (λ z, k z,, tr (σ⦃k⦄) p z). split; [| reflexivity].
  exact (paths_rect _ _ (λ f p, (λ z, f z,, tr f p z) = h) (idpath _) _ p).
- intro G. induction G as [g G]. unshelve eapply total2_paths2_f.
  + induction (pr1 G).
    induction (pr2 G).
    now induction (uip (isaset_set_fun_space (El Z) (El Γ)) (idpath _) p).
  + unshelve eapply total2_paths_f; apply uip.
    * apply (isaset_set_fun_space _ (∑ x, El (A x))%set).
    * apply isaset_set_fun_space.
Defined.

Definition VSET_typecat_structure : typecat_structure (VSET V).
Proof.
use tpair.
- exists (λ Γ, Γ ⊢).
  exists (λ Γ A, Γ ⋆ A).
  intros Γ A Δ σ. exact (A⦃σ⦄).
- exists (λ Γ A, VSET_ctx_proj).
  exists (λ Γ A Δ σ, VSET_q_gen_mor A σ).
  exists (λ Γ A Δ σ, VSET_q_gen_mor_p A σ).
  intros Γ A Δ σ.
  apply is_symmetric_isPullback.
  + intros a b. apply isaset_set_fun_space.
  + exact (VSET_isPullback_q_gen_mor A σ).
Defined.

Definition VSET_typecat : typecat := VSET V,, VSET_typecat_structure.

Lemma VSET_q_gen_mor_reind_id (Γ : V) (A : Γ ⊢) :
  VSET_q_gen_mor A (idfun _) = (idfun _).
Proof.
unfold idfun, VSET_q_gen_mor, VSET_subst_pair, VSET_ctx_proj, VSET_q_gen, VSET_p_gen.
cbn in *. change (λ c : El Γ, A c) with A. now induction (Vsig_El Γ A).
Defined.

Lemma VSET_q_gen_mor_reind_comp (Γ : V) (A : Γ ⊢) (Γ' : V) (f : El Γ' → El Γ)
                                (Γ'' : V) (g : El Γ'' → El Γ') :
  VSET_q_gen_mor A (f⦃g⦄) = VSET_q_gen_mor A f⦃VSET_q_gen_mor (A⦃f⦄) g⦄.
Proof.
unfold VSET_q_gen_mor, VSET_subst_pair, VSET_ctx_proj, VSET_q_gen, VSET_p_gen.
do 3 (cbn in *; induction Vsig_El).
reflexivity.
Defined.

Lemma VSET_is_split_typecat : is_split_typecat VSET_typecat.
Proof.
split; [intros; apply isaset_set_fun_space |]. split.
- exists (λ _ _, idpath _). exact VSET_q_gen_mor_reind_id.
- exists (λ _ _ _ _ _ _, idpath _). exact VSET_q_gen_mor_reind_comp.
Defined.

Definition VSET_split_typecat : split_typecat := VSET_typecat,, VSET_is_split_typecat.

End VSET_TypeCat.

(** Let [V : Vuni]. Suppose that for any object [a : V] in [VSET V]
    and function [b : El a → V] there is an object [σ] in [VSET V],
    such that

    <<
      El σ = ( ∑ (x : El a), El (b x) )%set.
    <<

    Then [VSET V] has CwF structure.
*)

Section VSET_CwF.

Variable V : Vuni.

Variable Vsig : ∏ (a : V), (El a → V) → V.

Variable Vsig_El :
  ∏ (a : V) (b : El a → V), (∑ (x : El a), El (b x))%set = El (Vsig a b).

Definition VSET_tt_structure : tt_structure (VSET V).
Proof.
use tpair.
- intro Γ. exact (El Γ -> V).
- intros Γ A. exact (∏ c : El Γ, El (A c)).
Defined.

Lemma VSET_reindx_structure : reindx_structure VSET_tt_structure.
Proof.
use tpair.
- intros Δ Γ A σ c. exact (A (σ c)).
- intros Δ Γ A a σ d. exact (a (σ d)).
Defined.

Definition VSET_tt_reindx_type_struct : tt_reindx_type_struct (VSET V).
Proof.
use tpair.
- use tpair.
  + exact (VSET_tt_structure,, VSET_reindx_structure).
  + intros Γ A.
    exists (Vsig Γ A).
    exact (transportf (λ z, z →  El Γ) (base_paths _ _ (Vsig_El Γ A)) pr1).
- intros Γ A. cbn. split.
  + unfold pr1hSet in *. apply transportD. exact pr2.
  + intros. exact (transportf (λ z, z) (base_paths _ _ (Vsig_El Γ A)) (γ X,, a X)).
Defined.

Lemma VSET_reindx_laws : reindx_laws VSET_tt_reindx_type_struct.
Proof.
use tpair; easy.
Defined.

Lemma VSET_reindx_comp_laws_1_2 : comp_laws_1_2 VSET_reindx_laws.
Proof.
unfold comp_laws_1_2. intros. cbn. use tpair; now induction Vsig_El.
Defined.

Lemma VSET_reindx_comp_law_3 : comp_law_3 VSET_reindx_laws.
Proof. easy. Defined.

Lemma VSET_reindx_comp_law_4 : comp_law_4 VSET_reindx_laws.
Proof.
unfold comp_law_4. intros. cbn. now induction Vsig_El.
Defined.

Definition VSET_CwF : cwf_struct (VSET V).
Proof.
exists VSET_tt_reindx_type_struct. use tpair.
- exists VSET_reindx_laws. split.
  + apply VSET_reindx_comp_laws_1_2.
  + split; [apply VSET_reindx_comp_law_3 | apply VSET_reindx_comp_law_4].
- split.
  + intros Γ Δ. apply isaset_set_fun_space.
  + split; intros; apply isaset_forall_hSet.
Defined.

End VSET_CwF.

(**

This file is a simplification of Presheaves.v, but for [SET]. It proves
that [SET] forms a type category ([SET_TypeCat]). As the collection of
types in context Γ don't form an hset it is not possible to instantiate
the CwF structure, however all of the other axioms of a CwF have been
formalized.

Contexts, written Γ ⊢, are modelled as HSETs and substitutions are
modelled by maps σ : Δ → Γ. So the identity substitution is given by
the identity map 1 : Γ → Γ and composition of substitutions are given
by composition of maps σ · δ (note that the order is diagrammatic). So
we automatically get the equations:

<<
      1 · σ = σ · 1 = σ        (σ · δ) · τ = σ · (δ · τ)
>>

Types in context Γ, usually written Γ ⊢ A and written A : Γ ⊢ in the
formalization, are defined as families of HSETs over Γ. 
So A : Γ ⊢ means A : Γ -> HSET.

Terms a of type A in context Γ, usually written Γ ⊢ a : A and written
a : Γ ⊢ A in the formalization, are defined as sections of A. 

This is equivalent to sections s : Γ → Γ.A of the projection map p : Γ.A → Γ.

The operations then defined are:

<<
              Γ ⊢ A    σ : Δ → Γ
            ---------------------- ([SET_subst_type])
                   Δ ⊢ Aσ


             Γ ⊢ a : A    σ : Δ → Γ
           -------------------------- ([SET_subst_term)]
                 Δ ⊢ aσ : Aσ


                    Γ ⊢ A
                 ----------- ([SET_ctx_ext])
                   Γ ⋆ A ⊢


                    Γ ⊢ A
               ----------------- ([SET_ctx_proj])
                 p : Γ ⋆ A → Γ


                    Γ ⊢ A
              ------------------ ([SET_ctx_last])
                Γ ⋆ A ⊢ q : Ap


             σ : Δ → Γ   Γ ⊢ A   Δ ⊢ a : Aσ
          ----------------------------------- ([SET_subst_pair])
                (σ,a) : Δ → Γ ⋆ A


                  σ : Δ → Γ    Δ ⊢ A
                ---------------------- ([SET_p_gen])
                  p_gen : Δ ⋆ A → Γ


                  σ : Δ → Γ    Γ ⊢ A
             ----------------------------- ([SET_q_gen])
               Δ ⋆ Aσ ⊢ q_gen : A(p_gen)
>>

These satisfy the following equations:

<<
                       A1 = A            ([SET_subst_type_id])

                    (Aσ)δ = A(σδ)        ([SET_subst_type_comp])

                       a1 = a            ([SET_subst_term_id])

                    (aσ)δ = a(σδ)        ([SET_subst_term_comp])

                δ · (σ,a) = (δ · σ,aδ)   ([SET_subst_pair_subst])

                (σ,a) · p = σ            ([SET_subst_pair_p])

                   q(σ,a) = a            ([SET_subst_pair_q])

                    (p,q) = 1            ([SET_subst_pair_id])

        (p_gen,q_gen) · p = p · σ        ([SET_q_gen_mor_p])
>>

And the last square is a pullback square ([SET_isPullback_q_gen_mor]).

This file was created at the UniMath workshop, Birmingham, 2019.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import TypeTheory.Auxiliary.CategoryTheoryImports.
Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheory.
Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.OtherDefs.CwF_Pitts.

Local Open Scope cat.

Local Notation "'1'" := (idfun _).

Local Notation "Γ ⊢" := (pr1 Γ → HSET) (at level 50).
Local Notation "Γ ⊢ A" :=  (∏ (c : pr1 Γ), pr1 (A c)) (at level 50).
Local Notation "A ⦃ s ⦄" := (λ c, A (s c)) (at level 40, format "A ⦃ s ⦄"). 
Local Notation "Γ ⋆ A" := (@total2_hSet Γ A : ob HSET) (at level 30).

Definition SET_subst_type {Γ Δ : HSET} (A : Γ ⊢) (σ : Δ --> Γ) : Δ ⊢ := (A ∘ σ)%functions.

Definition SET_subst_term {Γ Δ : HSET} (σ : Δ --> Γ) {A : Γ ⊢} (a : Γ ⊢ A) : Δ ⊢ A⦃σ⦄ :=
  (a ∘ σ)%functions.

Definition SET_ctx_ext {Γ : HSET} (A : Γ ⊢) : HSET := (∑ x : pr1 Γ, A x)%set.

Definition SET_ctx_proj {Γ : HSET} {A : Γ ⊢} : Γ ⋆ A --> Γ := pr1.

Definition SET_ctx_last {Γ : HSET} {A : Γ ⊢} : Γ ⋆ A ⊢ A⦃SET_ctx_proj⦄ := pr2.

Definition SET_p_gen {Γ Δ : HSET} {A : Δ ⊢} (σ : Δ --> Γ) : Δ ⋆ A --> Γ := λ a, σ (pr1 a).

Definition SET_q_gen {Γ Δ : HSET} {A : Γ ⊢} (σ : Δ --> Γ) : (Δ ⋆ (A⦃σ⦄)) ⊢ A⦃SET_p_gen σ⦄ := pr2.

Definition SET_subst_pair {Γ Δ : HSET} {A : Γ ⊢} (σ : Δ --> Γ) (a : Δ ⊢ A⦃σ⦄) : Δ --> Γ ⋆ A :=
  λ d, σ d,, a d.

Definition SET_q_gen_mor {Γ Δ : HSET} (A : Γ ⊢) (σ : Δ --> Γ) : Δ ⋆ (A⦃σ⦄) --> Γ ⋆ A :=
  SET_subst_pair (SET_p_gen σ) (SET_q_gen σ).

Lemma SET_subst_type_id {Γ : HSET} (A : Γ ⊢) : A⦃1⦄ = A.
Proof. reflexivity. Defined.

Lemma SET_subst_type_comp {Γ Δ Θ : HSET} (σ1 : Θ --> Δ) (σ2 : Δ --> Γ) (A : Γ ⊢) :
  A⦃σ1 · σ2⦄ = A⦃σ2⦄⦃σ1⦄.
Proof. reflexivity. Defined.

Lemma SET_subst_term_id {Γ : HSET} {A : Γ ⊢} (a : Γ ⊢ A) :
  SET_subst_term 1 a = transportb (λ A, Γ ⊢ A) (SET_subst_type_id A) a.
Proof. reflexivity. Defined.

Lemma SET_subst_term_comp {Γ Δ Θ : HSET} (σ1 : Θ --> Δ) (σ2 : Δ --> Γ) {A : Γ ⊢} (a : Γ ⊢ A) :
  SET_subst_term (σ1 · σ2) a =
  transportb (λ x, Θ ⊢ x) (SET_subst_type_comp σ1 σ2 A) (SET_subst_term σ1 (SET_subst_term σ2 a)).
Proof. reflexivity. Defined.

Lemma SET_subst_pair_subst {Γ Δ Θ : HSET} (σ1 : Δ --> Γ) (σ2 : Θ --> Δ)
  {A : Γ ⊢} (a : Δ ⊢ A⦃σ1⦄) :
  σ2 · SET_subst_pair σ1 a =
  SET_subst_pair (σ2 · σ1) (transportb (λ x : Θ ⊢, Θ ⊢ x)
                           (SET_subst_type_comp σ2 σ1 A) (SET_subst_term σ2 a)).
Proof. reflexivity. Defined.

Lemma SET_subst_pair_p {Γ Δ : HSET} (σ : Δ --> Γ) {A : Γ ⊢} (a : Δ ⊢ A⦃σ⦄) :
  SET_subst_pair σ a · SET_ctx_proj = σ.
Proof. reflexivity. Defined.

Lemma SET_subst_type_pair_p {Γ Δ : HSET} (σ : Δ --> Γ) {A : Γ ⊢} (a : Δ ⊢ A⦃σ⦄) :
  (A⦃SET_ctx_proj⦄)⦃SET_subst_pair σ a⦄ = A⦃σ⦄.
Proof. reflexivity. Defined.

Lemma SET_subst_pair_q {Γ Δ : HSET} (σ : Δ --> Γ) {A : Γ ⊢} (a : Δ ⊢ A⦃σ⦄) :
  transportf (λ x, Δ ⊢ x) (SET_subst_type_pair_p σ a)
                          (SET_subst_term (SET_subst_pair σ a) SET_ctx_last) = a.
Proof. reflexivity. Defined.

Lemma SET_subst_pair_id {Γ : HSET} {A : Γ ⊢} :
  SET_subst_pair (A:=A) SET_ctx_proj SET_ctx_last = 1.
Proof. reflexivity. Defined.

Lemma SET_q_gen_mor_p {Γ Δ : HSET} (A : Γ ⊢) (σ : Δ --> Γ) :
  SET_q_gen_mor A σ · SET_ctx_proj = SET_ctx_proj · σ.
Proof. reflexivity. Defined.

Lemma SET_isPullback_q_gen_mor {Γ Δ : HSET} (A : Γ ⊢) (σ : Δ --> Γ) :
  isPullback (SET_q_gen_mor_p A σ).
Proof.
intros Z h k p.
set (tr f (p : pr1⦃h⦄ = f) z := transportf (λ f, pr1 (A (f z))) p (pr2 (h z))).
use tpair.
- exists (λ z, k z,, tr (σ⦃k⦄) p z). split; [| reflexivity].
  exact (paths_rect _ _ (λ f p, (λ z, f z,, tr f p z) = h) (idpath _) _ p).
- intro G. induction G as [g G]. unshelve eapply total2_paths2_f.
  + induction (pr1 G).
    induction (pr2 G).
    now induction (uip (isaset_set_fun_space (pr1 Z) Γ) (idpath _) p).
  + unshelve eapply total2_paths_f; apply uip; apply isaset_set_fun_space.
Defined.

Definition SET_TypeCat : typecat_structure SET.
Proof.
use tpair.
- exists (λ Γ, Γ ⊢).
  exists (λ Γ A, Γ ⋆ A).
  intros Γ A Δ σ.
  exact (A⦃σ⦄).
- exists (λ Γ A, SET_ctx_proj).
  exists (λ Γ A Δ σ, SET_q_gen_mor A σ).
  exists (λ Γ A Δ σ, SET_q_gen_mor_p A σ).
  intros Γ A Δ σ.
  apply is_symmetric_isPullback.
  + exact (SET_isPullback_q_gen_mor A σ).
Defined.

Definition SET_tt_structure : tt_structure SET.
Proof.
use tpair.
- exact (λ Γ, pr1 Γ → SET).
- exact (λ Γ A, ∏ (c : pr1 Γ), pr1 (A c)).
Defined.

Lemma SET_reindx_structure : reindx_structure SET_tt_structure.
Proof.
use tpair.
- intros Δ Γ A σ c. exact (A (σ c)).
- intros Δ Γ A a σ d. exact (a (σ d)).
Defined.

Definition SET_tt_reindx_type_struct : tt_reindx_type_struct SET.
Proof.
use tpair. exists (SET_tt_structure,, SET_reindx_structure).
- intros Γ A. use tpair; [exact (total2_hSet A) | exact pr1].
- intros Γ A. exists pr2. intros Δ σ a d. exact (σ d,, a d).
Defined.
    
Lemma SET_reindx_laws : reindx_laws SET_tt_reindx_type_struct.
Proof.
use tpair; easy.
Defined.

(* The following cannot be completed because SET is not an h-set *)
Definition SET_CwF : cwf_struct SET.
Proof.
  exists SET_tt_reindx_type_struct. split.
  - exists SET_reindx_laws. split.
    + intros Γ A Γ' γ a. use tpair; reflexivity.
    + use tpair; easy.
  - use tpair.
    + cbn. intro Γ. admit. (* does not hold! *)
    + intros Γ A. apply isaset_forall_hSet.
Abort.

(* Indeed, we can show SET is _not_ a CwF (with the given type-category structure): *)
Definition SET_CwF_laws_fail : ¬ cwf_laws SET_tt_reindx_type_struct.
Proof.
  apply or_neg_to_neg_and. apply inr.
  apply or_neg_to_neg_and. apply inl.
  apply total2_neg_to_neg_forall. simpl.
  exists unitset.
  eapply negf. { eapply isaset_weqf. apply weqfunfromunit. }
  apply hSet_not_set.
Defined.

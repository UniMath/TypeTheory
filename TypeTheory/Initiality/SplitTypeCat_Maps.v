(** This file defines _maps_ of split type-categories. *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.All.

Require Import TypeTheory.Auxiliary.CategoryTheoryImports.
Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.TypeCat.

(* This should be upstreamed *)
Arguments nat_trans_ax {C C'} {F F'} a {x x'} f.

Local Open Scope cat.

(** We base our models on _split type-categories_, i.e. [split_typecat] as defined in [TypeTheory.ALV1.TypeCat] following Pitts and van den Berg–Garner.
(Roughly the same as what Hofmann calls CwA’s.) *)

(** Notations for working in split type cats *)
Notation "A ⦃ s ⦄" := (reind_typecat A s) (at level 40, format "A  ⦃ s ⦄").
Notation "Γ ⋆ A" := (ext_typecat Γ A) (at level 30, only parsing).

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

Section Types_and_Terms.

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

  (* TODO: upstream to [Auxiliary]? *)
  Definition section {C : precategory} {X Y : C} (f : X --> Y)
    := ∑ (s : Y --> X), s ;; f = identity _.

  (* TODO: upstream with [section]. *)
  Coercion section_pr1 {C : precategory} {X Y : C} (f : X --> Y)
    : section f -> (Y --> X)
  := pr1.

  Definition tm {C : typecat} {Γ} (A : C Γ) : UU
    := section (dpr_typecat A).
  Identity Coercion section_of_term : tm >-> section.

  Definition reind_tm {C : typecat} {Γ Γ'} (f : Γ' --> Γ) {A : C Γ}
    : tm A -> tm (A⦃f⦄).
  (* uses the pullback structure *)
  Admitted.

  (** A concrete construction of “transport” of terms, by composing with [comp_ext_compare]. *)
  Definition tm_transportf {C : typecat} {Γ} {A A' : C Γ} (e : A = A')
    : tm A ≃ tm A'.
  Admitted.

  Definition tm_transportb {C : typecat} {Γ} {A A' : C Γ} (e : A = A')
    : tm A' ≃ tm A
  := invweq (tm_transportf e).

  (* TODO: maybe make an equality of equivalences? *)
  Definition transportf_tm {C : typecat}
      {Γ} {A A' : C Γ} (e : A = A') (s : tm A)
    : transportf tm e s = tm_transportf e s.
  Admitted.

End Types_and_Terms.

End Auxiliary.

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
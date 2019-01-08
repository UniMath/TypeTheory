(** This file defines _maps_ of split type-categories. *)

Require Import UniMath.MoreFoundations.All.

Require Import TypeTheory.Auxiliary.CategoryTheoryImports.
Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.Initiality.SplitTypeCat_General.

Local Open Scope cat.

(** We base our models on _split type-categories_, i.e. [split_typecat] as defined in [TypeTheory.ALV1.TypeCat] following Pitts and van den Berg–Garner.
(Roughly the same as what Hofmann calls CwA’s.) *)

Section morphisms.

(* The definition of a morphism between split typecategories
consists of (modulo ^op):

- a functor F : C -> D
- a natural transformation FTy : Ty C -> Ty D
- a family of isomorphisms ϕ : F(Γ.A) ≃ F(Γ).F_Ty(A)

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
Definition typecat_mor (C D : split_typecat) : UU
  := ∑ (F : functor C D)
       (FTy : PreShv C ⟦ty C, functor_opp F ∙ ty D⟧)
       (ϕ : ∏ (Γ : C) (A : C Γ), iso (F (Γ ⋆ A)) (F Γ ⋆ pr1 FTy _ A)),
         (∏ Γ (A : C Γ), # F (dpr_typecat A) = ϕ _ A · dpr_typecat (pr1 FTy _ A))
       × (∏ Γ Γ' (A : C Γ) (σ : Γ' --> Γ),
            # F (q_typecat A σ) · ϕ Γ A =
            ϕ Γ' _ · comp_ext_compare (eqtohomot (nat_trans_ax FTy σ) A) ·
              q_typecat (pr1 FTy _ A) (# F σ)).

Definition mk_typecat_mor
  {C D : split_typecat}
  (F : functor C D)
  (FTy : PreShv C ⟦ty C, functor_opp F ∙ ty D⟧)
  (ϕ : ∏ (Γ : C) (A : C Γ), iso (F (Γ ⋆ A)) (F Γ ⋆ pr1 FTy _ A))
  (H1 : ∏ Γ (A : C Γ), # F (dpr_typecat A) = ϕ _ A · dpr_typecat (pr1 FTy _ A))
  (H2 : ∏ Γ Γ' (A : C Γ) (σ : Γ' --> Γ),
        # F (q_typecat A σ) · ϕ Γ A =
        ϕ Γ' _ · comp_ext_compare (eqtohomot (nat_trans_ax FTy σ) A) ·
          q_typecat (pr1 FTy _ A) (# F σ))
  : typecat_mor C D.
Proof.
exists F, FTy, ϕ; split; [ apply H1 | apply H2 ].
Defined.

Definition typecat_mor_functor {C D} {f : typecat_mor C D}
  : functor C D := pr1 f.
Coercion typecat_mor_functor : typecat_mor >-> functor.

Definition typecat_mor_Ty {C D}  (f : typecat_mor C D)
  : nat_trans (ty C : functor _ _) (functor_opp f ∙ ty D)
:= pr12 f.

Definition typecat_mor_iso {C D} (f : typecat_mor C D)
    {Γ} (A : C Γ)
  : iso (f (Γ ⋆ A)) (f Γ ⋆ typecat_mor_Ty f Γ A)
:= pr122 f Γ A.

Definition typecat_mor_triangle {C D} (f : typecat_mor C D)
    {Γ} (A : C Γ)
  : # f (dpr_typecat A)
    = typecat_mor_iso f A · dpr_typecat (typecat_mor_Ty f _ A)
:= pr1 (pr222 f) Γ A.

Definition typecat_mor_pentagon {C D} (f : typecat_mor C D)
    {Γ Γ'} (A : C Γ) (σ : Γ' --> Γ)
  : # f (q_typecat A σ)
    · typecat_mor_iso f A
  = typecat_mor_iso f _
    · comp_ext_compare (eqtohomot (nat_trans_ax (typecat_mor_Ty f) σ) A)
    · q_typecat (typecat_mor_Ty f Γ A) (# f σ)
:= pr2 (pr222 f) Γ Γ' A σ.

End morphisms.

Section Derived_Actions.

  (* Call this [fmap_tm] for consistency with later defs, or [typecat_mor_tm] for consistency with primitive components? *)
  Definition fmap_tm
      {C D : split_typecat} (F : typecat_mor C D)
      {Γ:C} {A : C Γ} (a : tm A)
    : tm (typecat_mor_Ty F _ A).
  Proof.
    exists (# F a · typecat_mor_iso F A).
    abstract (cbn; eapply pathscomp0; [ apply pathsinv0, assoc |];
      eapply pathscomp0; [ apply maponpaths, pathsinv0, typecat_mor_triangle|];
      eapply pathscomp0; [ apply pathsinv0, functor_comp|];
      eapply pathscomp0; [ apply maponpaths, section_property|];
      apply functor_id).
  Defined.

  Lemma fmap_tm_as_map 
      {C C' : split_typecat} (F : typecat_mor C C')
      {Γ:C} {A: C Γ} (a : tm A)
    : # F a = fmap_tm F a · inv_from_iso (typecat_mor_iso F A).
  Proof.
    now apply iso_inv_on_left.
  Qed.
  
  (* Other possible names: [typecat_mor_reind_ty], [typecat_mor_Ty_nat] *)
  Definition reindex_fmap_ty
      {C C' : split_typecat} (F : typecat_mor C C')
      {Γ:C} (A: C Γ) {Γ' : C} (f : Γ' --> Γ)
    : typecat_mor_Ty F _ (A ⦃f⦄) = (typecat_mor_Ty F _ A) ⦃ # F f ⦄
    := eqtohomot (nat_trans_ax (typecat_mor_Ty F) f) A.

  Lemma reindex_fmap_tm {C D : split_typecat} (F : typecat_mor C D) {Γ Γ' : C}
        (f : C ⟦ Γ', Γ ⟧) {A : C Γ} (a : tm A) :
    tm_transportf (reindex_fmap_ty F A f) (fmap_tm F (reind_tm f a)) =
    reind_tm (# F f) (fmap_tm F a).
  Proof.
    apply paths_tm, PullbackArrowUnique; cbn; simpl;
      set (pb := mk_Pullback _ _ _ _ _ _ _); rewrite <-!assoc.
    - etrans; [apply maponpaths, maponpaths, comp_ext_compare_dpr_typecat|].
      etrans; [apply maponpaths, (!typecat_mor_triangle F (A ⦃f⦄))|].
      now rewrite <- functor_comp, (PullbackArrow_PullbackPr1 pb), functor_id.
    - etrans; [apply maponpaths; rewrite assoc;
               apply (!typecat_mor_pentagon F A f)|].
      now rewrite !assoc, <- !functor_comp, (PullbackArrow_PullbackPr2 pb).
  Qed.
  
End Derived_Actions.

Section Composition.

  Definition id_typecat (C : split_typecat)
    : typecat_mor C C.
  Proof.
    use mk_typecat_mor.
    - (* functor *)
      apply functor_identity.
    - (* naturality *)
      use tpair.
      + intros Γ A; exact A.
      + intros ? ? ?; apply idpath.
    - (* comparison isomorphisms *)
      intros; apply identity_iso.
    - (* axiom [typecat_mor_triangle] *)
      intros; simpl. apply pathsinv0, id_left.
    - (* axiom [typecat_mor_pentagon] *)
      intros; cbn.
      etrans. { apply id_right. }
      apply pathsinv0.
      etrans. { apply maponpaths_2, id_right. }
      apply id_left.
  Defined.

  Definition compose_typecat {C C' C'' : split_typecat}
      (F : typecat_mor C C') (F' : typecat_mor C' C'')
    : typecat_mor C C''.
  Admitted. (* [compose_typecat]: should be self-contained *)

  (* TODO: also will need at least [id_left] for the proof of initiality *)

End Composition.

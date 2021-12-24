(** This file defines _maps_ of split type-categories. *)

Require Import UniMath.MoreFoundations.All.

Require Import TypeTheory.Auxiliary.CategoryTheoryImports.
Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheory.
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
Definition typecat_mor_data (C D : split_typecat) : UU
  := ∑ (F : functor C D)
       (FTy : PreShv C ⟦ty C, functor_opp F ∙ ty D⟧),
       (∏ (Γ : C) (A : C Γ), iso (F (Γ ⋆ A)) (F Γ ⋆ pr1 FTy _ A)).

Definition typecat_mor_functor {C D} {F : typecat_mor_data C D}
  : functor C D := pr1 F.
Coercion typecat_mor_functor : typecat_mor_data >-> functor.

Definition typecat_mor_Ty {C D}  (F : typecat_mor_data C D)
  : nat_trans (ty C : functor _ _) (functor_opp F ∙ ty D)
:= pr12 F.

Definition typecat_mor_iso {C D} (F : typecat_mor_data C D)
    {Γ} (A : C Γ)
  : iso (F (Γ ⋆ A)) (F Γ ⋆ typecat_mor_Ty F Γ A)
:= pr22 F Γ A.

Definition typecat_mor_axioms
    {C D : split_typecat} (F : typecat_mor_data C D) : UU
  := (∏ Γ (A : C Γ),
        # F (dpr_typecat A)
        = typecat_mor_iso F A · dpr_typecat (typecat_mor_Ty F _ A))
   × (∏ Γ Γ' (A : C Γ) (f : Γ' --> Γ),
        # F (q_typecat A f) · typecat_mor_iso F A
        = typecat_mor_iso F _
          · comp_ext_compare (eqtohomot (nat_trans_ax (typecat_mor_Ty F) f) A)
          · q_typecat (typecat_mor_Ty F _ A) (# F f)).


Definition typecat_mor (C D : split_typecat) : UU
  := ∑ (F : typecat_mor_data C D), typecat_mor_axioms F.

Definition make_typecat_mor
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
  exact ((F,,(FTy,,ϕ)),,(H1,,H2)).
Defined.

Coercion typecat_mor_data_of_typecat_mor {C D} (F : typecat_mor C D)
  : typecat_mor_data C D
:= pr1 F.

Definition typecat_mor_triangle {C D} (F : typecat_mor C D)
    {Γ} (A : C Γ)
  : # F (dpr_typecat A)
    = typecat_mor_iso F A · dpr_typecat (typecat_mor_Ty F _ A)
:= pr1 (pr2 F) Γ A.

Definition typecat_mor_pentagon {C D} (F : typecat_mor C D)
    {Γ Γ'} (A : C Γ) (σ : Γ' --> Γ)
  : # F (q_typecat A σ)
    · typecat_mor_iso F A
  = typecat_mor_iso F _
    · comp_ext_compare (eqtohomot (nat_trans_ax (typecat_mor_Ty F) σ) A)
    · q_typecat (typecat_mor_Ty F Γ A) (# F σ)
:= pr2 (pr2 F) Γ Γ' A σ.

Lemma isaprop_typecat_mor_axioms {C D} (F : typecat_mor_data C D) :
  isaprop (typecat_mor_axioms F).
Proof.
  apply isapropdirprod; repeat (apply impred_isaprop; intro); apply homset_property.
Qed.

  Lemma comp_ext_compare_typecat_mor_iso
      {C C' : split_typecat} (F : typecat_mor C C')
      (Γ : C) (A A' : C Γ) (e : A = A')
    : # F (comp_ext_compare e) ;; typecat_mor_iso F A'
      = typecat_mor_iso F A ;; comp_ext_compare (maponpaths _ e).
  Proof.
    destruct e; cbn.
    rewrite functor_id, id_left.
    apply pathsinv0, id_right.
  Qed.

End morphisms.

Section Composition.

  Definition id_typecat (C : split_typecat)
    : typecat_mor C C.
  Proof.
    use make_typecat_mor.
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

  Definition compose_typecat_data {C C' C'' : split_typecat}
      (F : typecat_mor C C') (F' : typecat_mor C' C'')
    : typecat_mor_data C C''.
  Proof.
    exists (functor_composite F F').
    use tpair.
    - refine (_ ;; _).
      { exact (typecat_mor_Ty F). }
      simple refine (_ ;; _).
      { exact (functor_opp F ∙ (functor_opp F' ∙ ty C'')). }
      { apply pre_whisker, typecat_mor_Ty. }
      (* TODO: the following should exist as a lemma somewhere *)
      use tpair.
      + intros Γ A; exact A.
      + intros ? ? ?; apply idpath.
    - (* [typecat_mor_iso] *)
      intros Γ A; simpl.
      refine (iso_comp _ _).
      2: { apply typecat_mor_iso. }
      apply functor_on_iso, typecat_mor_iso.
  Defined.

  Definition compose_typecat_axioms {C C' C'' : split_typecat}
      (F : typecat_mor C C') (F' : typecat_mor C' C'')
    : typecat_mor_axioms (compose_typecat_data F F').
  Proof.
    split.
    - (* axiom [typecat_mor_triangle] *)
      intros Γ A; cbn.
      etrans. { apply maponpaths, typecat_mor_triangle. }
      etrans. { apply functor_comp. }
      etrans. 2: { apply assoc. }
      apply maponpaths, typecat_mor_triangle.
    - (* axiom [typecat_mor_pentagon] *)
      intros Γ Γ' A f; cbn.
      etrans. { apply assoc. } 
      etrans. { apply maponpaths_2.
        etrans. { apply pathsinv0. apply (functor_comp F'). }
        etrans. { apply maponpaths, typecat_mor_pentagon. }
        apply (functor_comp F'). }
      etrans. { apply pathsinv0, assoc. }
      etrans. { apply maponpaths, typecat_mor_pentagon. }
      etrans. { apply maponpaths_2, functor_comp. }
      etrans. { apply assoc. }
      apply maponpaths_2.
      etrans. { apply pathsinv0, assoc. }
      etrans. 2: { apply assoc. }
      apply maponpaths.
      etrans. { apply assoc. }
      etrans. { apply maponpaths_2, comp_ext_compare_typecat_mor_iso. }
      etrans. { apply pathsinv0, assoc. } apply maponpaths.
      etrans. { apply pathsinv0, comp_ext_compare_comp. }
      apply comp_ext_compare_irrelevant.
  Qed.

  Definition compose_typecat {C C' C'' : split_typecat}
      (F : typecat_mor C C') (F' : typecat_mor C' C'')
    : typecat_mor C C''.
  Proof.
    exists (compose_typecat_data F F').
    apply compose_typecat_axioms.
  Defined.

(* TODO: also will need at least [id_left] for the proof of initiality *)

End Composition.

Section Derived_Actions.

  (* Alias of [typecat_mor_Ty], to fit a more consistent naming convention.
   TODO: consider making this the primitive name of the field? *)
  Definition fmap_ty {C D} (F : typecat_mor C D)
    := typecat_mor_Ty F.

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
      set (pb := make_Pullback _ _); rewrite <-!assoc.
    - etrans; [apply maponpaths, maponpaths, dpr_typecat_typeeq|].
      etrans; [apply maponpaths, (!typecat_mor_triangle F (A ⦃f⦄))|].
      now rewrite <- functor_comp, (PullbackArrow_PullbackPr1 pb), functor_id.
    - etrans; [apply maponpaths; rewrite assoc;
               apply (!typecat_mor_pentagon F A f)|].
      now rewrite !assoc, <- !functor_comp, (PullbackArrow_PullbackPr2 pb).
  Qed.

  Definition fmap_type_with_term {C C'} (F : typecat_mor C C')
      {Γ:C} (Aa : type_with_term Γ)
    : type_with_term (F Γ).
  Proof.
    exact (typecat_mor_Ty F _ (type_of Aa),,fmap_tm F Aa).
  Defined.

  Lemma var_with_type_fmap_type
      {C C'} (F : typecat_mor C C')
      {Γ} (A : C Γ)
    : var_with_type (fmap_ty F Γ A)
    = reind_type_with_term (inv_from_iso (typecat_mor_iso F A))
                           (fmap_type_with_term F (var_with_type A)).
  Proof.
    apply pathsinv0.
    use paths_type_with_term.
    - simpl.
      etrans. { eapply (maponpaths (fun X => reind_typecat X _)).
           exact (reindex_fmap_ty F _ (dpr_typecat A)). }
      etrans. { apply pathsinv0, reind_comp_typecat. }
      apply maponpaths, iso_inv_on_right, typecat_mor_triangle.
    - apply PullbackArrowUnique.
      + etrans. { apply pathsinv0, assoc. }
        etrans. { apply maponpaths, dpr_typecat_typeeq. }
        apply section_property.
      + (* NOTE: the next step is just asking to apply [cbn] to the subterm
         beginning [PullbackPr2].  [simpl PullbackPr2] applies [simpl] to this
         subterm, but [simpl] doesn’t simplify enough in this case. *)
        etrans. { apply maponpaths. cbn. apply idpath. }
        rewrite comp_ext_compare_comp.
        rewrite comp_ext_compare_comp.
        etrans. { apply pathsinv0, assoc. }
        etrans.
        { apply maponpaths.
          etrans. { apply pathsinv0, assoc. }
          etrans. { apply maponpaths, pathsinv0, assoc. }
          etrans. { apply maponpaths, maponpaths, q_typecat_mapeq. }
          etrans. { apply maponpaths, pathsinv0, q_q_typecat. }
          etrans. { apply assoc. }
          apply maponpaths_2, q_typecat_typeeq.
        }
        etrans. { apply assoc. }
        etrans. { apply maponpaths_2, assoc. }
        etrans. { apply maponpaths_2, maponpaths_2.
          refine (PullbackArrow_PullbackPr2 (make_Pullback _ _) _ _ _ _). }
        simpl pr1.
        etrans. { apply maponpaths_2, maponpaths_2, assoc. }
        etrans. { apply pathsinv0, assoc. }
        etrans. { apply pathsinv0, assoc. }
        etrans. { apply maponpaths, assoc. }
        etrans. { apply maponpaths, pathsinv0, typecat_mor_pentagon. }
        etrans. { apply pathsinv0, assoc. }
        etrans. { apply maponpaths, assoc. }
        etrans.
        { apply maponpaths, maponpaths_2. 
          etrans. { apply pathsinv0, functor_comp. }
          etrans.
          { apply maponpaths.
            refine (PullbackArrow_PullbackPr2 (make_Pullback _ _) _ _ _ _).
          }
          apply functor_id.
        }
        etrans. { apply maponpaths, id_left. }
        apply iso_after_iso_inv.
  Qed.
  (* TODO: can we speed this proof up, perhaps by factoring out some lemma(s)? *)

End Derived_Actions.


(**
  [TypeTheory.ALV2.TypeCat_ComprehensionCat]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**
This module defines a comprehension category induced by a (non-split) type category.

Main definition is

- [typecat_to_comprehension_cat] - comprehension category induced by a type category;

Important parts are:

- [typecat_disp] - displayed category induced by a type category (or rather by its object extension substructure);
- [typecat_disp_is_disp_univalent] - induced displayed category is univalent when [typecat_idtoiso_triangle] is an equivalence;
- [cleaving_typecat_disp] - induced displayed category is a fibration;

- [typecat_disp_functor] - a comprehension functor induced by a type category;
- [typecat_disp_functor_ff] - induced displayed functor is fully faithful;
- [typecat_disp_functor_is_cartesian] - induced displayed functor is cartesian.

*)

Require Import UniMath.MoreFoundations.PartA.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.TypeCat.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.ComprehensionC.

Section Auxiliary.

  (* TODO: move upstream? *)
  Lemma isPullback_swap
        {C : precategory}
        {a b c d : C} {f : b --> a} {g : c --> a}
        {p1 : d --> b} {p2 : d --> c} {H : p1 · f = p2 · g}
        (pb : isPullback f g p1 p2 H)
  : isPullback _ _ _ _ (! H).
  Proof.
    use make_isPullback.
    intros e h k H'.
    use (iscontrweqf _ (pb e k h (! H'))).
    use (weqtotal2 (idweq _)).
    intros ?. apply weqdirprodcomm.
  Defined.

  (* TODO: move upstream? *)
  Definition pr1_transportb
             {A : UU} {B : A → UU} (P : ∏ a : A, B a → UU) {a a' : A}
             (e : a = a') (xs : ∑ b : B a', P a' b)
    : pr1 (transportb (λ x : A, ∑ b : B x, P x b) e xs) =
      transportb (λ x : A, B x) e (pr1 xs).
  Proof.
    induction e.
    apply idpath.
  Defined.

End Auxiliary.

Section TypeCat_ObjExt.

  (* Object extension structure is part of the definition of type category that includes:
   * - the type family [ty_typecat] : C → UU;
   * - for every Γ : C and A : Ty(Γ):
   *   - context extension [Γ ◂ A];
   *   - for every morphism f : Γ' --> Γ, reindexing mapping [reind_typecat];
   *   - projection morphism [dpr_typecat_obj_ext]: Γ ◂ A --> Γ.
   *)
  Definition typecat_obj_ext_structure (C : precategory) 
    := ∑ TC : typecat_structure1 C,
              ∏ Γ (A : TC Γ), Γ ◂ A --> Γ.

  Definition typecat1_from_typecat_obj_ext (C : precategory)
             (TC : typecat_obj_ext_structure C) 
    : typecat_structure1 _  := pr1 TC.
  Coercion typecat1_from_typecat_obj_ext : typecat_obj_ext_structure >-> typecat_structure1.

  Definition dpr_typecat_obj_ext {C : precategory}
             {TC : typecat_obj_ext_structure C} {Γ} (A : TC Γ)
    : (Γ ◂ A) --> Γ
    := pr2 TC Γ A.
  
  Definition typecat_obj_ext_from_typecat (C : precategory) (TC : typecat_structure C) 
    : typecat_obj_ext_structure _  := (pr1 TC ,, @dpr_typecat _ TC).
  Coercion typecat_obj_ext_from_typecat : typecat_structure >-> typecat_obj_ext_structure.

End TypeCat_ObjExt.

Local Notation "'π' A" := (dpr_typecat_obj_ext A) (at level 5).

Section TypeCat_Comp_Ext_Compare.

  Context {C : precategory}.
  Context (TC : typecat_obj_ext_structure C).

  Definition typecat_comp_ext_compare
             {Γ : C} {A B : TC Γ}
    : (A = B) → iso (Γ ◂ A) (Γ ◂ B).
  Proof.
    intros p. induction p.
    apply identity_iso.
  Defined.

  Definition typecat_iso_triangle
             {Γ : C} (A B : TC Γ)
    := ∑ (i : iso (Γ ◂ A) (Γ ◂ B)),
       i ;; π B = π A.

  Definition typecat_iso_triangle_swap
             {Γ : C} {A B : TC Γ}
    : typecat_iso_triangle A B → typecat_iso_triangle B A.
  Proof.
    intros tr.
    exists (iso_inv_from_iso (pr1 tr)).
    etrans. apply maponpaths, pathsinv0, (pr2 tr).
    etrans. apply assoc.
    etrans. apply maponpaths_2, iso_after_iso_inv.
    apply id_left.
  Defined.

  Definition typecat_idtoiso_triangle
             {Γ : C} (A B : TC Γ)
    : (A = B) → typecat_iso_triangle A B.
  Proof.
    intros p. induction p.
    use tpair.
    - apply typecat_comp_ext_compare, (idpath _).
    - apply id_left.
  Defined.

End TypeCat_Comp_Ext_Compare.

Section TypeCat_Disp.

  (* Type category (or rather its object extension part)
   * induces a displayed category over C with
   * - objects over Γ : C being types A : Ty(Γ)
   * - morphisms from A' to A over f : Γ' --> Γ being a morphism
         ff : Γ.A' --> Γ.A making the square with projections and f commute.
   *)
  Definition typecat_disp_ob_mor
             {C : precategory} (TC : typecat_obj_ext_structure C)
  : disp_cat_ob_mor C.
  Proof.
    use tpair.
    - apply TC.
    - intros Γ' Γ A' A f.
      exact (∑ ff : Γ' ◂ A' --> Γ ◂ A,
                    ff ;; π A = π A' ;; f).
  Defined.

  Definition typecat_disp_id_comp
             {C : precategory} (TC : typecat_obj_ext_structure C)
    : disp_cat_id_comp _ (typecat_disp_ob_mor TC).
    split.
    + intros Γ A; cbn in *.
      use tpair.
      * apply identity.
      * cbn. etrans. apply id_left. apply pathsinv0, id_right.
    + intros ? ? ? ? ? ? ? ? ff gg; cbn in *.
      use tpair.
      * apply (pr1 ff ;; pr1 gg).
      * simpl.
        etrans. apply assoc'.
        etrans. apply maponpaths, (pr2 gg).
        etrans. apply assoc.
        etrans. apply maponpaths_2, (pr2 ff).
        apply assoc'.
  Defined.

  Definition typecat_disp_data
             {C : precategory} (TC : typecat_obj_ext_structure C)
    : disp_cat_data C
    := (typecat_disp_ob_mor TC,, typecat_disp_id_comp TC).

  (* NOTE: copied with slight modifications from https://github.com/UniMath/TypeTheory/blob/ad54ca1dad822e9c71acf35c27d0a39983269462/TypeTheory/Displayed_Cats/DisplayedCatFromCwDM.v#L78-L107  *)
  Definition typecat_disp_axioms
             {C : category} (TC : typecat_obj_ext_structure C)
    : disp_cat_axioms _ (typecat_disp_data TC).
  Proof.
    repeat apply tpair; intros; try apply homset_property.
    - (* id_left_disp *) 
      apply subtypePath.
      { intro. apply homset_property. }
      etrans. apply id_left.
      apply pathsinv0.
      etrans. refine (pr1_transportf (C⟦_,_⟧) _ _ _ _ _ _ ).
      use transportf_const.
    - (* id_right_disp *) 
      apply subtypePath.
      { intro. apply homset_property. }
      etrans. apply id_right.
      apply pathsinv0.
      etrans. refine (pr1_transportf (C⟦_,_⟧) _ _ _ _ _ _ ).
      use transportf_const.
    - (* assoc_disp *) 
      apply subtypePath.
      { intro. apply homset_property. }
      etrans. apply assoc.
      apply pathsinv0.
      etrans. unfold mor_disp.
      refine (pr1_transportf (C⟦_,_⟧) _ _ _ _ _ _ ).
      use transportf_const.
    - (* homsets_disp *)
      apply (isofhleveltotal2 2).
      + apply homset_property.
      + intro. apply isasetaprop. apply homset_property.
  Qed.

  Definition typecat_disp
             {C : category} (TC : typecat_obj_ext_structure C)
    : disp_cat C
    := (typecat_disp_data TC,, typecat_disp_axioms TC).

  Section TypeCat_Disp_is_univalent.

    Context {C : category}.
    Context (TC : typecat_obj_ext_structure C).

    Definition typecat_is_triangle_to_idtoiso_fiber_disp
               {Γ : C} (A B : TC Γ)
      : typecat_iso_triangle _ A B → @iso_disp C (typecat_disp TC) _ _ (identity_iso Γ) A B.
    Proof.
      intros tr.
      set (i        := pr1 (pr1 tr) : C ⟦ Γ ◂ A, Γ ◂ B ⟧ ).
      set (iB_A     := pr2 tr : i ;; π B = π A).

      set (tr' := typecat_iso_triangle_swap TC tr).
      set (inv_i    := pr1 (pr1 tr') : C ⟦ Γ ◂ B, Γ ◂ A ⟧).
      set (inv_iA_B := pr2 tr' : inv_i ;; π A = π B).

      set (i_inv_i  := iso_inv_after_iso (pr1 tr) : i ;; inv_i = identity _).
      set (inv_i_i  := iso_after_iso_inv (pr1 tr) : inv_i ;; i = identity _).

      repeat use tpair.
      - exact i.
      - etrans. apply iB_A. apply pathsinv0, id_right.
      - exact inv_i.
      - simpl. etrans. apply inv_iA_B. apply pathsinv0, id_right.
      - use total2_paths_f.
        2: apply homset_property.
        etrans. apply inv_i_i.
        apply pathsinv0.
        etrans. apply (pr1_transportb (λ _ (_ : C ⟦ Γ ◂ B, Γ ◂ B ⟧), _)).
        apply (maponpaths (λ f, f _) (transportb_const _ _)).
      - use total2_paths_f.
        2: apply homset_property.
        etrans. apply i_inv_i.
        apply pathsinv0.
        etrans. apply (pr1_transportb (λ _ (_ : C ⟦ Γ ◂ A, Γ ◂ A ⟧), _)).
        apply (maponpaths (λ f, f _) (transportb_const _ _)).
    Defined.

    Definition idtoiso_fiber_disp_to_typecat_is_triangle
               {Γ : C} (A B : TC Γ)
      : @iso_disp C (typecat_disp TC) _ _ (identity_iso Γ) A B → typecat_iso_triangle _ A B.
    Proof.
      intros tr.
      set (i        := pr1 (pr1 tr) : C ⟦ Γ ◂ A, Γ ◂ B ⟧ ).
      set (iB_A     := pr2 (pr1 tr) : i ;; π B = π A ;; identity _).
      set (inv_i    := pr1 (pr1 (pr2 tr)) : C ⟦ Γ ◂ B, Γ ◂ A ⟧).
      set (inv_iA_B := pr2 (pr1 (pr2 tr))
                       : inv_i ;; π A = π B ;; identity _).
      set (inv_i_i  := maponpaths pr1 (pr1 (pr2 (pr2 tr))) : _).
      set (i_inv_i  := maponpaths pr1 (dirprod_pr2 (pr2 (pr2 tr))) : _).

      repeat use tpair.
      - exact i.
      - apply is_iso_from_is_z_iso.
        repeat use tpair.
        + apply inv_i.
        + etrans. apply i_inv_i.
          etrans.
          use (pr1_transportb (λ _ (_ : C ⟦ Γ ◂ A, Γ ◂ A ⟧), _)).
          simpl. apply (maponpaths (λ f, f _) (transportb_const _ _)).
        + etrans. apply inv_i_i.
          etrans.
          use (pr1_transportb (λ _ (_ : C ⟦ Γ ◂ B, Γ ◂ B ⟧), _)).
          simpl. apply (maponpaths (λ f, f _) (transportb_const _ _)).
      - etrans. apply iB_A. apply id_right.
    Defined.

    Definition typecat_is_triangle_idtoiso_fiber_disp_isweq
               {Γ : C} (A B : TC Γ)
      : isweq (typecat_is_triangle_to_idtoiso_fiber_disp A B).
    Proof.
      use isweq_iso.
      - apply idtoiso_fiber_disp_to_typecat_is_triangle.
      - intros tr.
        use total2_paths_f.
        + apply eq_iso, idpath.
        + apply homset_property.
      - intros tr.
        apply eq_iso_disp.
        use total2_paths_f.
        + apply idpath.
        + apply homset_property.
    Defined.

    Definition typecat_is_triangle_idtoiso_fiber_disp_weq
               {Γ : C} (A B : TC Γ)
      : typecat_iso_triangle _ A B ≃ @iso_disp C (typecat_disp TC) _ _ (identity_iso Γ) A B
    := (_,, typecat_is_triangle_idtoiso_fiber_disp_isweq A B).

    Definition typecat_disp_is_disp_univalent
               (w' : ∏ (Γ : C) (A B : TC Γ), isweq (typecat_idtoiso_triangle _ A B))
      : is_univalent_disp (typecat_disp TC).
    Proof.
      apply is_univalent_disp_from_fibers.
      intros Γ A B.
      set (f := typecat_is_triangle_idtoiso_fiber_disp_weq A B).
      set (g := (typecat_idtoiso_triangle _ A B,, w' _ A B)).
      use weqhomot.
      - apply (weqcomp g f).
      - intros p. induction p.
        use total2_paths_f.
        + use total2_paths_f.
          * apply idpath.
          * apply homset_property.
        + apply proofirrelevance.
          apply isaprop_is_iso_disp.
    Defined.

    Definition typecat_disp_is_disp_univalent_implies_typecat_idtoiso_triangle_isweq
               (D_is_univalent : is_univalent_disp (typecat_disp TC))
      : ∏ (Γ : C) (A B : TC Γ), isweq (typecat_idtoiso_triangle _ A B).
    Proof.
      intros Γ A B.
      set (f := typecat_is_triangle_idtoiso_fiber_disp_weq A B).
      set (g := (idtoiso_fiber_disp ,, is_univalent_in_fibers_from_univalent_disp _ D_is_univalent _ A B)).
      use weqhomot.
      - apply (weqcomp g (invweq f)).
      - intros p. induction p.
        use total2_paths_f.
        + apply eq_iso, idpath.
        + apply homset_property.
    Defined.

  End TypeCat_Disp_is_univalent.

  Section TypeCat_Disp_Cleaving.

    Context {C : category}.

    (* NOTE: copied with slight modifications from https://github.com/UniMath/TypeTheory/blob/ad54ca1dad822e9c71acf35c27d0a39983269462/TypeTheory/Displayed_Cats/DisplayedCatFromCwDM.v#L114-L143 *)
    Definition pullback_is_cartesian
               (TC : typecat_obj_ext_structure C)
               {Γ Γ' : C} {f : Γ' --> Γ}
               {A : typecat_disp TC Γ} {A' : typecat_disp TC Γ'} (ff : A' -->[f] A)
      : (isPullback _ _ _ _ (pr2 ff)) -> is_cartesian ff.
    Proof.
      intros Hpb Δ g B hh.
      eapply iscontrweqf.
      2: { 
        use Hpb.
        + exact (Δ ◂ B).
        + exact (pr1 hh).
        + simpl in B. refine (π B ;; g).
        + etrans. apply (pr2 hh). apply assoc.
      }
      eapply weqcomp.
      2: apply weqtotal2asstol.
      apply weq_subtypes_iff.
      - intro. apply isapropdirprod; apply homset_property.
      - intro. apply (isofhleveltotal2 1). 
        + apply homset_property.
        + intros. apply homsets_disp.
      - intros gg; split; intros H.
        + exists (pr2 H).
          apply subtypePath.
          intro; apply homset_property.
          exact (pr1 H).
        + split.
          * exact (maponpaths pr1 (pr2 H)).
          * exact (pr1 H).
    Defined.

    Lemma cleaving_typecat_disp
          (TC : typecat_structure C)
      : cleaving (typecat_disp TC).
    Proof.
      intros Γ Γ' f A.
      unfold cartesian_lift.
      exists (reind_typecat A f).
      use tpair.
      + use tpair.
        * use q_typecat.
        * apply dpr_q_typecat.
      + apply pullback_is_cartesian.
        apply (isPullback_swap (reind_pb_typecat A f)).
    Defined.
  End TypeCat_Disp_Cleaving.

End TypeCat_Disp.

Section TypeCat_Disp_Functor.

  Context {C : category}.

  Definition typecat_disp_functor_data
             (TC : typecat_obj_ext_structure C)
    : disp_functor_data
        (functor_identity C)
        (typecat_disp TC) (disp_codomain C).
  Proof.
    use tpair.
    - intros Γ A. exists (Γ ◂ A). apply dpr_typecat_obj_ext.
    - intros Γ' Γ A' A f ff. apply ff.
  Defined.

  Definition typecat_disp_functor_axioms
             (TC : typecat_obj_ext_structure C)
    : disp_functor_axioms (typecat_disp_functor_data TC).
  Proof.
    use make_dirprod.
    - intros Γ A. cbn.
      apply maponpaths.
      apply homset_property.
    - intros Γ Δ Γ' A B A' f g ff gg.
      apply maponpaths.
      use total2_paths_f.
      + apply idpath.
      + apply homset_property.
  Defined.

  Definition typecat_disp_functor
             (TC : typecat_obj_ext_structure C)
    : disp_functor (functor_identity C) (typecat_disp TC) (disp_codomain C)
    := (typecat_disp_functor_data TC ,, typecat_disp_functor_axioms TC).

  Definition typecat_disp_functor_ff
             (TC : typecat_obj_ext_structure C)
    : disp_functor_ff (typecat_disp_functor TC).
  Proof.
    unfold disp_functor_ff.
    intros Γ Γ' A A' f.
    use isweq_iso.
    - apply idfun.
    - intros ff.
      use total2_paths_f.
      + apply idpath.
      + apply homset_property.
    - intros ff.
      use total2_paths_f.
      + apply idpath.
      + apply homset_property.
  Defined.

  Section TypeCat_Disp_Functor_is_cartesian.

    Definition typecat_disp_functor_is_cartesian
               (TC : typecat_structure C)
    : is_cartesian_disp_functor (typecat_disp_functor TC).
    Proof.
      use cartesian_functor_from_cleaving.
      { apply (cleaving_typecat_disp TC). }
      intros Γ Γ' f A.
      intros Δ g k hh.
      use iscontrweqf.
      3: {
        use (reind_pb_typecat A f (pr1 k)).
        - apply (pr2 k ;; g).
        - apply (pr1 hh).
        - etrans. apply assoc'. apply (! pr2 hh).
      }

      eapply weqcomp.
      2: apply weqtotal2asstol.
      apply weq_subtypes_iff.
      - intro. apply isapropdirprod; apply homset_property.
      - intro. apply (isofhleveltotal2 1). 
        + apply homset_property.
        + intros. apply homsets_disp.
      - intros gg; split; intros H.
        + exists (pr1 H).
          apply subtypePath.
          intro; apply homset_property.
          exact (pr2 H).
        + split.
          * exact (pr1 H).
          * exact (maponpaths pr1 (pr2 H)).
    Defined.

  End TypeCat_Disp_Functor_is_cartesian.

End TypeCat_Disp_Functor.

Section TypeCat_ComprehensionCat.

  Definition typecat_to_comprehension_cat_structure
             {C : category}
  : typecat_structure C → comprehension_cat_structure C.
  Proof.
    intros TC.
    exists (typecat_disp TC).
    exists (cleaving_typecat_disp _).
    exists (typecat_disp_functor _).
    apply typecat_disp_functor_is_cartesian.
  Defined.

  (* TODO: move upstream *)
  Definition comprehension_cat := ∑ (C : category), (comprehension_cat_structure C).

  Definition typecat_to_comprehension_cat
    : typecat → comprehension_cat.
  Proof.
    intros TC.
    exists (pr1 TC).
    apply (typecat_to_comprehension_cat_structure (pr2 TC)).
  Defined.

End TypeCat_ComprehensionCat.

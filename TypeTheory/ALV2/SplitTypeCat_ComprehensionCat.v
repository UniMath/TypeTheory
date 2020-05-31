(* TODO: module documentation *)

Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.Foundations.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.ALV2.FullyFaithfulDispFunctor.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.ComprehensionC.

Section Auxiliary.

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
  Definition unique_lift_is_cartesian
             {C : category}
             {D : discrete_fibration C} {c c'}
             (f : c' --> c) (d : D c)
    : is_cartesian (pr2 (pr1 (unique_lift f d))).
  Proof.
    apply (pr2 (pr2 (fibration_from_discrete_fibration _ D _ _ f d))).
  Defined.

End Auxiliary.

Definition discrete_comprehension_cat_structure (C : category) : UU
  := ∑ (D : disp_cat C)
       (is_discrete_fibration_D : is_discrete_fibration D)
       (FF : disp_functor (functor_identity _) D (disp_codomain C)), 
     is_cartesian_disp_functor FF.

Definition discrete_comprehension_cat : UU
  := ∑ (C : category), discrete_comprehension_cat_structure C.

Section A.

  Section DiscreteComprehensionCat_from_SplitTypeCat.

    Context {C : category}.

    Context (TC : split_typecat_structure C).

    Definition disp_cat_ob_mor_from_split_typecat_structure
        : disp_cat_ob_mor C.
    Proof.
        exists TC.
        intros Γ Γ' A A' f.
        exact (A' {{f}} = A).
    Defined.

    Definition disp_cat_id_comp_from_split_typecat_structure
        : disp_cat_id_comp C disp_cat_ob_mor_from_split_typecat_structure.
    Proof.
        use make_dirprod.
        - intros Γ A. apply (pr1 (pr1 (dirprod_pr2 (pr2 TC)))).
        - intros Γ Γ' Γ'' f g A A' A'' ff gg. 
          simpl.
          set (reind_comp := pr1 (dirprod_pr2 (dirprod_pr2 (pr2 TC)))).
          etrans. apply reind_comp.
          etrans. apply (maponpaths (λ B, B {{f}}) gg).
          apply ff.
    Defined.

    Definition disp_cat_data_from_split_typecat_structure
        : disp_cat_data C
        := (_ ,, disp_cat_id_comp_from_split_typecat_structure).

    Definition disp_cat_axioms_from_split_typecat_structure
        : disp_cat_axioms C disp_cat_data_from_split_typecat_structure.
    Proof.
        repeat use make_dirprod.
        - intros. apply (pr1 (pr2 TC)).
        - intros. apply (pr1 (pr2 TC)).
        - intros. apply (pr1 (pr2 TC)).
        - intros. apply isasetaprop. apply (pr1 (pr2 TC)).
    Defined.

    Definition disp_precat_from_split_typecat_structure
        : disp_precat C
        := (_ ,, disp_cat_axioms_from_split_typecat_structure).

    Definition disp_cat_from_split_typecat_structure
        : disp_cat C
        := disp_precat_from_split_typecat_structure.

    Definition is_discrete_fibration_disp_cat_from_split_typecat_structure
      : is_discrete_fibration disp_cat_from_split_typecat_structure.
    Proof.
      use make_dirprod. 2: apply (pr1 (pr2 TC)).
      intros Γ Γ' f A.
      use tpair.
      - exists (A {{f}}). apply idpath.
      - intros X.
        use total2_paths_f.
        + apply (! pr2 X).
        + apply (pr1 (pr2 TC)).
    Defined.

    Definition discrete_fibration_from_split_typecat_structure
      : discrete_fibration C
      := (_ ,, is_discrete_fibration_disp_cat_from_split_typecat_structure).
    
    Definition disp_functor_data_from_split_typecat_structure
      : disp_functor_data (functor_identity C)
                          disp_cat_from_split_typecat_structure
                          (disp_codomain C).
    Proof.
      use tpair.
      - intros Γ A.
        exists (Γ ◂ A).
        apply (dpr_typecat A).
      - intros Γ Γ' A A' f ff.
        use tpair.
        + set (k := inv_from_iso (idtoiso (maponpaths (λ B, Γ ◂ B) ff))).
          eapply compose. apply k. apply q_typecat.
        + induction ff. simpl.
          etrans. apply assoc'.
          etrans. apply maponpaths, dpr_q_typecat.
          apply id_left.
    Defined.

    Definition disp_functor_axioms_from_split_typecat_structure
      : disp_functor_axioms disp_functor_data_from_split_typecat_structure.
    Proof.
      use make_dirprod.
      - intros Γ A.
        use total2_paths_f.
        + simpl.
          etrans. apply maponpaths, (pr2 (pr1 (pr2 (pr2 TC)))).
          apply iso_after_iso_inv.
        + apply homset_property.
      - intros Γ Γ' Γ'' A A' A'' f g ff gg.
        use total2_paths_f.
        + simpl.
          induction ff.
          induction gg.
          etrans. apply maponpaths_2, maponpaths, maponpaths, maponpaths.
          apply pathscomp0rid.
          etrans. apply maponpaths, (pr2 (dirprod_pr2 (pr2 (pr2 TC)))).
          etrans. apply maponpaths, assoc'.
          etrans. apply assoc.
          etrans. apply maponpaths_2, iso_after_iso_inv.
          etrans. apply id_left.

          apply pathsinv0.
          etrans. apply maponpaths_2, id_left.
          etrans. apply maponpaths, id_left.
          apply idpath.
        + apply homset_property.
    Defined.

    Definition disp_functor_from_split_typecat_structure
      : disp_functor (functor_identity C)
                     disp_cat_from_split_typecat_structure
                     (disp_codomain C)
      := (_,, disp_functor_axioms_from_split_typecat_structure).

    Definition disp_functor_from_split_typecat_structure_is_cartesian
      : is_cartesian_disp_functor disp_functor_from_split_typecat_structure.
    Proof.
      intros Γ Γ' f A A' ff ff_is_cartesian.
      intros Δ g k k_comm.
      use iscontrweqf.
      3: {
        use (reind_pb_typecat A f).
        - exact (pr1 k).
        - exact (pr2 k ;; g).
        - exact (pr1 k_comm).
        - etrans. apply assoc'. apply (! pr2 k_comm).
      }

      induction ff.

      eapply weqcomp.
      2: apply weqtotal2asstol.
      apply weq_subtypes_iff.
      -- intro. apply isapropdirprod; apply homset_property.
      -- intro. apply (isofhleveltotal2 1). 
         ++ apply homset_property.
         ++ intros. apply homsets_disp.
      -- intros gg; split; intros H.
         ++ exists (pr1 H).
            apply subtypePath.
            intro; apply homset_property.
            simpl. etrans. apply maponpaths, id_left.
            exact (pr2 H).
         ++ split.
            ** exact (pr1 H).
            ** etrans. 2: apply (maponpaths pr1 (pr2 H)).
               simpl. apply maponpaths.
               apply pathsinv0, id_left.
    Defined.

    Definition discrete_comprehension_cat_structure_from_split_typecat_structure
      : discrete_comprehension_cat_structure C
      := ( _ ,, is_discrete_fibration_disp_cat_from_split_typecat_structure ,,
             _ ,, disp_functor_from_split_typecat_structure_is_cartesian).

  End DiscreteComprehensionCat_from_SplitTypeCat.

  Section SplitTypeCat_from_DiscreteComprehensionCat.

    Context {C : category}.

    Context (DC : discrete_comprehension_cat_structure C).

    Let D := pr1 DC : disp_cat C.
    Let is_discrete_fibration_D := pr1 (pr2 DC) : is_discrete_fibration D.
    Let FF := pr1 (pr2 (pr2 DC)) : disp_functor (functor_identity C) D (disp_codomain C).
    Let is_cartesian_FF := pr2 (pr2 (pr2 DC)) : is_cartesian_disp_functor FF.

    Definition typecat_structure1_from_discrete_comprehension_cat_structure
      : typecat_structure1 C.
    Proof.
      exists D.
      use make_dirprod.
      - intros Γ A. exact (pr1 (disp_functor_on_objects FF A)).
      - intros Γ A Γ' f. 
        exact (pr1 (pr1 (pr1 is_discrete_fibration_D Γ Γ' f A))).
    Defined.

    Definition typecat_structure2_from_discrete_comprehension_cat_structure
      : typecat_structure2 typecat_structure1_from_discrete_comprehension_cat_structure.
    Proof.
      unfold typecat_structure2.
      repeat use tpair.
      - intros Γ A. exact (pr2 (disp_functor_on_objects FF A)).
      - intros Γ A Γ' f.
        set (k := pr2 (pr1 (pr1 is_discrete_fibration_D Γ Γ' f A))
                  : A {{f}} -->[f] A).
        apply (pr1 (disp_functor_on_morphisms FF k)).
      - intros Γ A Γ' f. simpl.
        set (k := pr2 (pr1 (pr1 is_discrete_fibration_D Γ Γ' f A))
                  : A {{f}} -->[f] A).
        apply (pr2 (disp_functor_on_morphisms FF k)).
      - simpl. intros Γ A Γ' f.
        apply isPullback_swap.
        use cartesian_isPullback_in_cod_disp.
        apply is_cartesian_FF.
        apply (unique_lift_is_cartesian (D := (_ ,, is_discrete_fibration_D)) f A).
    Defined.

    Definition typecat_structure_from_discrete_comprehension_cat_structure
      : typecat_structure C
      := (_ ,, typecat_structure2_from_discrete_comprehension_cat_structure).

    Definition is_split_typecat_from_discrete_comprehension_cat_structure
      : is_split_typecat typecat_structure_from_discrete_comprehension_cat_structure.
    Proof.
      repeat use make_dirprod.
      - apply (pr2 is_discrete_fibration_D).
      - use tpair.
        + intros Γ A. 
          set (p := pr2 (pr1 is_discrete_fibration_D Γ Γ (identity Γ) A)).
          apply (maponpaths pr1 (! p (A ,, id_disp A))).
        + intros Γ A.
          etrans. unfold q_typecat. cbn.
          (* WIP:
             Current problem is dealing with the identification of
             unique_lift (identity Γ) A   vs   id_disp A
           *)
          (*
          set (p := pr2 (pr1 is_discrete_fibration_D Γ Γ (identity Γ) A)).
          apply (maponpaths pr1 (! p (A ,, id_disp A))).
          apply (maponpaths pr1 (disp_functor_id FF A)).
          set (p := pr2 (pr1 is_discrete_fibration_D Γ Γ (identity Γ) A)).
          set (x := disp_functor_id FF A).
          cbn in x.
          induction (p (A ,, id_disp A)).
          simpl.
          *)
    Abort.

  End SplitTypeCat_from_DiscreteComprehensionCat.

  Definition discrete_comprehension_cat_from_split_typecat
    : split_typecat → discrete_comprehension_cat.
  Proof.
    intros STC.
    exists (pr1 (pr1 STC)).
    apply discrete_comprehension_cat_structure_from_split_typecat_structure.
    apply (pr2 (pr1 STC) ,, pr2 STC).
  Defined.

End A.

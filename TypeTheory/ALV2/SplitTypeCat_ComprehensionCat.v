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

  (* TODO: move upstream? *)
  Definition unique_lift_explicit
             {C : category}
             {D : disp_cat C}
             (is_discrete_fibration_D : is_discrete_fibration D) {c c'}
             {d : D c} {f : c' --> c} (d' : D c') (ff : d' -->[f] d)
    : ∃! (d' : D c'), d' -->[f] d.
  Proof.
    exists (d' ,, ff).
    intros X.
    etrans. apply (pr2 (pr1 is_discrete_fibration_D _ _ f d)).
    apply pathsinv0, (pr2 (pr1 is_discrete_fibration_D _ _ f d)).
  Defined.

  (* TODO: move upstream? *)
  Definition unique_lift_explicit_eq
             {C : category}
             {D : disp_cat C}
             (is_discrete_fibration_D : is_discrete_fibration D) {c c'}
             {d : D c} {f : c' --> c} (d' : D c') (ff : d' -->[f] d)
    : pr1 is_discrete_fibration_D _ _ f d
      = unique_lift_explicit is_discrete_fibration_D d' ff.
  Proof.
    apply isapropiscontr.
  Defined.

  (* TODO: move upstream? *)
  Definition unique_lift_identity
             {C : category}
             {D : disp_cat C}
             (is_discrete_fibration_D : is_discrete_fibration D) {c}
             (d : D c)
    : ∃! (d' : D c), d' -->[identity c] d.
  Proof.
    apply (unique_lift_explicit is_discrete_fibration_D d).
    apply id_disp.
  Defined.

  (* TODO: move upstream? *)
  Definition unique_lift_id
             {C : category}
             {D : disp_cat C}
             (is_discrete_fibration_D : is_discrete_fibration D) {c}
             (d : D c)
    : pr1 is_discrete_fibration_D _ _ (identity c) d
      = unique_lift_identity is_discrete_fibration_D d.
  Proof.
    apply isapropiscontr.
  Defined.

  (* TODO: move upstream? *)
  Definition unique_lift_compose
             {C : category}
             {D : disp_cat C}
             (is_discrete_fibration_D : is_discrete_fibration D) {c c' c''}
             (f : c' --> c) (g : c'' --> c')
             (d : D c)
    : ∃! (d'' : D c''), d'' -->[g ;; f] d.
  Proof.
    set (d'ff := pr1 is_discrete_fibration_D _ _ f d).
    set (d' := pr1 (pr1 d'ff)).
    set (ff := pr2 (pr1 d'ff)).
    set (d''gg := pr1 is_discrete_fibration_D _ _ g d').
    set (d'' := pr1 (pr1 d''gg)).
    set (gg := pr2 (pr1 d''gg)).

    use (unique_lift_explicit is_discrete_fibration_D d'' (gg ;; ff)%mor_disp).
  Defined.

  (* TODO: move upstream? *)
  Definition unique_lift_comp
             {C : category}
             {D : disp_cat C}
             (is_discrete_fibration_D : is_discrete_fibration D) {c c' c''}
             (f : c' --> c) (g : c'' --> c')
             (d : D c)
    : pr1 is_discrete_fibration_D _ _ (g ;; f) d
      = unique_lift_compose is_discrete_fibration_D f g d.
  Proof.
    apply isapropiscontr.
  Defined.

  (* TODO: move upstream? *)
  Definition discrete_fibration_mor
             {C : category}
             {D : disp_cat C}
             (is_discrete_fibration_D : is_discrete_fibration D) {c c'}
             (f : c' --> c) (d : D c) (d' : D c')
    : (d' -->[f] d) = (pr1 (pr1 (pr1 is_discrete_fibration_D c c' f d)) = d').
  Proof.
    apply univalenceweq.
    set (uf := pr1 is_discrete_fibration_D c c' f d).
    use weq_iso.
    - intros ff. apply (maponpaths pr1 (! pr2 uf (d' ,, ff))).
    - intros p. apply (transportf _ p (pr2 (pr1 uf))).
    - intros ff. simpl.
      induction (! unique_lift_explicit_eq is_discrete_fibration_D d' ff
                : unique_lift_explicit _ d' ff = uf).
      simpl.
      etrans. apply maponpaths_2, maponpaths, maponpaths.
      apply pathsinv0r.
      apply idpath.
    - intros ?. apply (pr2 is_discrete_fibration_D).
  Qed.

  (* TODO: move upstream? *)
  Definition isaprop_mor_disp_of_discrete_fibration
             {C : category}
             {D : disp_cat C}
             (is_discrete_fibration_D : is_discrete_fibration D) {c c'}
             (f : c' --> c) (d : D c) (d' : D c')
    : isaprop (d' -->[f] d).
  Proof.
    induction (! discrete_fibration_mor is_discrete_fibration_D f d d').
    apply (pr2 is_discrete_fibration_D).
  Qed.

  (* TODO: move upstream? *)
  Definition isaprop_disp_id_comp_of_discrete_fibration
             {C : category}
             {D : disp_cat C}
             (is_discrete_fibration_D : is_discrete_fibration D)
    : isaprop (disp_cat_id_comp C D).
  Proof.
    use isapropdirprod.
    - apply impred_isaprop. intros ?.
      apply impred_isaprop. intros ?.
      apply isaprop_mor_disp_of_discrete_fibration.
      apply is_discrete_fibration_D.
    - apply impred_isaprop. intros ?.
      apply impred_isaprop. intros ?.
      apply impred_isaprop. intros ?.
      apply impred_isaprop. intros ?.
      apply impred_isaprop. intros ?.
      apply impred_isaprop. intros ?.
      apply impred_isaprop. intros ?.
      apply impred_isaprop. intros ?.
      apply impred_isaprop. intros ?.
      apply impred_isaprop. intros ?.
      apply isaprop_mor_disp_of_discrete_fibration.
      apply is_discrete_fibration_D.
  Qed.

  (* TODO: move upstream? *)
  Definition isaprop_is_discrete_fibration
             {C : category}
             (D : disp_cat C)
    : isaprop (is_discrete_fibration D).
  Proof.
    use isapropdirprod.
    - apply impred_isaprop. intros ?.
      apply impred_isaprop. intros ?.
      apply impred_isaprop. intros ?.
      apply impred_isaprop. intros ?.
      apply isapropiscontr.
    - apply impred_isaprop. intros ?.
      apply isapropisaset.
  Qed.
             
  (* TODO: move upstream? *)
  Definition isaprop_is_cartesian_disp_functor
        {C C' : category} {F : functor C C'}
        {D : disp_cat C} {D' : disp_cat C'} {FF : disp_functor F D D'}
    : isaprop (is_cartesian_disp_functor FF).
  Proof.
    apply impred_isaprop. intros c.
    apply impred_isaprop. intros c'.
    apply impred_isaprop. intros f.
    apply impred_isaprop. intros d.
    apply impred_isaprop. intros d'.
    apply impred_isaprop. intros ff.
    apply impred_isaprop. intros ff_is_cartesian.
    apply isaprop_is_cartesian.
  Qed.

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
          set (reind_comp := pr1 (dirprod_pr2 (pr2 (pr2 TC)))).
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

    Definition disp_cat_from_split_typecat_structure_is_univalent
      : is_univalent_disp disp_cat_from_split_typecat_structure.
    Proof.
      apply is_univalent_disp_from_fibers.
      intros Γ A A'.
      use isweq_iso.
      - intros i.
        set (A'A := pr1 i : A' {{ identity _ }} = A).
        set (reind_id := pr1 (pr1 (dirprod_pr2 (pr2 TC)))).
        exact (! A'A @ reind_id Γ A').
      - intros e. apply (pr1 (pr2 TC) Γ).
      - intros i.
        use total2_paths_f.
        + apply (pr1 (pr2 TC) Γ).
        + apply isaprop_is_iso_disp.
    Defined.
    
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
        exact (transportf
                 (λ AA, ((Γ ◂ AA,, dpr_typecat AA) : disp_codomain C Γ) -->[f] (Γ' ◂ A',, dpr_typecat A'))
                 ff (q_typecat A' f ,, dpr_q_typecat A' f)).
    Defined.



    Definition disp_functor_axioms_from_split_typecat_structure
      : disp_functor_axioms disp_functor_data_from_split_typecat_structure.
    Proof.
      use make_dirprod.
      - intros Γ A.
        use total2_paths_f. 2: apply homset_property.
        simpl. etrans. apply (pr1_transportf _ (λ AA, C ⟦ Γ ◂ AA, Γ ◂ A ⟧)).
        cbn. etrans. apply maponpaths.
        apply (pr2 (pr1 (dirprod_pr2 (pr2 TC))) Γ A).
        induction (pr1 (pr1 (dirprod_pr2 (pr2 TC))) Γ A).
        apply idpath.

      - intros Γ Γ' Γ'' A A' A'' f g ff gg.
        use total2_paths_f. 2: apply homset_property.
        + simpl. etrans. apply (pr1_transportf _ (λ AA, C ⟦ Γ ◂ AA, Γ'' ◂ A'' ⟧)).
          etrans. apply maponpaths, (pr2 (dirprod_pr2 (pr2 (pr2 TC)))).
          induction ff, gg. simpl.
          etrans. apply maponpaths_2, pathscomp0rid.
          etrans. apply maponpaths, assoc'.
          etrans. apply (functtransportf (λ b : pr1 TC Γ, Γ ◂ b)
                                         ((λ x, C ⟦ x, Γ'' ◂ A'' ⟧))).
          etrans. apply pathsinv0, idtoiso_precompose.
          etrans. apply maponpaths_2, maponpaths, idtoiso_inv.
          etrans. apply assoc.
          etrans. apply maponpaths_2, iso_after_iso_inv.
          apply id_left.
    Qed.

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
            exact (pr2 H).
         ++ split.
            ** exact (pr1 H).
            ** apply (maponpaths pr1 (pr2 H)).
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

        + intros Γ A. cbn.
          induction (! unique_lift_id is_discrete_fibration_D A).
          etrans. apply maponpaths, (disp_functor_id FF A). simpl.
          apply pathsinv0.
          etrans. apply maponpaths, maponpaths, maponpaths, maponpaths, maponpaths.
          apply pathsinv0r. simpl.
          apply idpath.

      - use tpair.
        + intros Γ A Γ' f Γ'' g.

          set (A'ff := pr1 is_discrete_fibration_D _ _ f A).
          set (ff := pr2 (pr1 A'ff) : (A {{f}}) -->[f] A).
          set (A''gg := pr1 is_discrete_fibration_D _ _ g (A {{f}})).
          set (gg := pr2 (pr1 A''gg) : ((A {{f}}) {{g}}) -->[g] A {{f}}).

          set (p := pr2 (pr1 is_discrete_fibration_D _ _ (g ;; f) A)).
          apply (maponpaths pr1 (! p ((A {{f}}) {{g}} ,, (gg ;; ff)%mor_disp))).

        + intros Γ A Γ' f Γ'' g. cbn.
          induction (! unique_lift_comp is_discrete_fibration_D f g A).
          set (A'ff := pr1 (pr1 is_discrete_fibration_D _ _ f A)).
          set (A' := pr1 A'ff).
          set (ff := pr2 A'ff).
          set (gg := pr2 (pr1 (pr1 is_discrete_fibration_D _ _ g A'))).
          etrans. apply maponpaths, (disp_functor_comp FF gg ff).
          simpl.
          apply maponpaths_2.
          etrans. apply pathsinv0, id_left.
          apply maponpaths_2.

          apply pathsinv0.
          etrans. apply maponpaths, maponpaths, maponpaths, maponpaths, maponpaths.
          apply pathsinv0r. simpl.
          apply idpath.
    Defined.

    Definition split_typecat_structure_from_discrete_comprehension_cat_structure
      : split_typecat_structure C
      := (_ ,, is_split_typecat_from_discrete_comprehension_cat_structure).

  End SplitTypeCat_from_DiscreteComprehensionCat.

  Section SplitTypeCat_DiscreteComprehensionCat_Equiv.

    Context {C : category}.

    Lemma ololo
          (DC : discrete_comprehension_cat_structure C)
      : pr1 (discrete_comprehension_cat_structure_from_split_typecat_structure
          (split_typecat_structure_from_discrete_comprehension_cat_structure DC))
          = pr1 DC.
    Proof.
      set (D := pr1 DC).
      set (is_discrete_fibration_D := pr1 (pr2 DC)).
      use total2_paths_f. 2: apply isaprop_disp_cat_axioms.
      use total2_paths_f.
      2: apply isaprop_disp_id_comp_of_discrete_fibration; apply is_discrete_fibration_D.
      use total2_paths_f.
      - apply idpath.
      - apply funextsec. intros ?.
        apply funextsec. intros ?.
        apply funextsec. intros ?.
        apply funextsec. intros ?.
        apply funextsec. intros ?.
        apply pathsinv0.
        apply discrete_fibration_mor.
    Defined.

    Check total2_paths2_comp1.

    Definition helper_transportf_pr1
               {A : UU} {B P : A → UU}
               (a1 a2 : A)
               (b1 : B a1) (b2 : B a2)
               (p : a1 = a2)
               (q : transportf _ p b1 = b2)
               (z : P (pr1 (a1 ,, b1)))
      : transportf (λ (x : ∑ (a : A), B a), P (pr1 x)) (two_arg_paths_f p q) z =
        transportf (λ x : A, P x) p z.
    Proof.
      induction p, q. apply idpath.
    Defined.

    Definition split_typecat_structure_discrete_comprehension_cat_structure_weq
      : split_typecat_structure C ≃ discrete_comprehension_cat_structure C.
    Proof.
      use weq_iso.
      - apply discrete_comprehension_cat_structure_from_split_typecat_structure.
      - apply split_typecat_structure_from_discrete_comprehension_cat_structure.
      - intros TC.
        use total2_paths_f.
        + use total2_paths_f.
          * apply idpath. (* typecat_structure1 *)
          * repeat use total2_paths_f.
            -- apply idpath. (* dpr *)
            -- apply idpath. (* q *)
            -- apply funextsec. intros ?.
               apply funextsec. intros ?.
               apply funextsec. intros ?.
               apply funextsec. intros ?.
               apply homset_property.
            -- apply funextsec. intros ?.
               apply funextsec. intros ?.
               apply funextsec. intros ?.
               apply funextsec. intros ?.
               apply isaprop_isPullback.
        + apply isaprop_is_split_typecat.
          apply homset_property.

      - intros DC.
        set (D := pr1 DC : disp_cat C).
        set (is_discrete_fibration_D := pr1 (pr2 DC) : is_discrete_fibration D).
        set (FF := pr1 (pr2 (pr2 DC))
                   : disp_functor (functor_identity C) D (disp_codomain C)).

        use total2_paths_f.
        2: use dirprod_paths.
        2: apply isaprop_is_discrete_fibration.
        2: use total2_paths_f.
        3: apply isaprop_is_cartesian_disp_functor.

        + apply ololo. (* disp_cat *)
          
        +
          etrans. apply maponpaths.
          apply (pr2_transportf
                   (B2 := λ x,
                          ∑ (FF : disp_functor (functor_identity C) x (disp_codomain C)),
                          is_cartesian_disp_functor FF)
                ).
          etrans.
          apply (pr1_transportf
                   _ (λ x, disp_functor (functor_identity C) x (disp_codomain C))
                ).
          simpl.

          unfold disp_functor_from_split_typecat_structure.
          use total2_paths_f. 2: apply isaprop_disp_functor_axioms.

          etrans.
          apply (pr1_transportf
                   (disp_cat C)
                   (λ x, disp_functor_data (functor_identity C) x (disp_codomain C))
                ).

          use total2_paths_f.
          * etrans.
            apply (pr1_transportf
                     (disp_cat C)
                     (λ x, ∏ c : C, x c → disp_codomain C c)).
            apply funextsec. intros Γ.
            etrans.
            apply (!helper_A (λ c (x0 : disp_cat C), x0 c → ∑ y : C, C ⟦ y, c ⟧) _ _ _).
            simpl. cbn.
            etrans.
            apply (transportf_forall_var2
                     (disp_cat C)
                     (λ y, y Γ)
                     (λ _, ∑ y0 : C, C ⟦ y0, Γ ⟧)).
            apply funextsec. intros A.

            etrans. apply transportf_const.
            apply maponpaths.
            apply (transportb_transpose_left
                     (P := λ y : disp_cat C, y Γ) (y := A) (e := ololo DC)).
            apply pathsinv0.
            etrans. apply (helper_transportf_pr1 (P := λ (x : disp_cat_data C), x Γ)).
            etrans. apply (helper_transportf_pr1 (P := λ (x : disp_cat_ob_mor C), x Γ)).
            etrans. apply (helper_transportf_pr1 (P := λ (x : C → UU), x Γ)).
            apply (idpath_transportf (λ x : C → UU, x Γ)).
          * 
            apply funextsec; intros Γ.
            apply funextsec; intros Γ'.
            apply funextsec; intros A.
            apply funextsec; intros A'.
            apply funextsec; intros f.
            apply funextsec; intros ff.

            use total2_paths_f. 2: apply homset_property.
            -- Check pr1 (pr2 (pr1 (pr1 (pr2 (pr2 DC)))) Γ Γ' A A' f ff).
               induction (discrete_fibration_mor _ _ _ _ _).
               etrans. apply maponpaths, pathsinv0.
               apply (helper_A
                        (T := C)
                        (Y := ∏ (x5 : C), pr1 DC x5 → disp_codomain C x5)
                        (λ x0 x, ∏ (y : C) (xx : pr1 DC x0) (yy : pr1 DC y) (f : C ⟦ x0, y ⟧), xx -->[f] yy → x x0 xx -->[f] x y yy)).
               apply (!helper_A (λ x0 x, ∏ y xx yy f, xx -->[f] yy → x x0 xx -->[f] x y yy)).
              etrans. apply maponpaths.
               apply pathsinv0.
               apply (pr1_transportf
                        (∏ x : C, pr1 DC x → disp_codomain C (functor_identity C x))
                     ).
    Abort.

  End SplitTypeCat_DiscreteComprehensionCat_Equiv.

  Definition discrete_comprehension_cat_from_split_typecat
    : split_typecat → discrete_comprehension_cat.
  Proof.
    intros STC.
    exists (pr1 (pr1 STC)).
    apply discrete_comprehension_cat_structure_from_split_typecat_structure.
    apply (pr2 (pr1 STC) ,, pr2 STC).
  Defined.

  Definition split_typecat_from_discrete_comprehension_cat
    : discrete_comprehension_cat → split_typecat.
  Proof.
    intros DCC.
    set (TC := split_typecat_structure_from_discrete_comprehension_cat_structure (pr2 DCC)).
    use tpair.
    - exists (pr1 DCC).
      apply (pr1 TC).
    - apply (pr2 TC).
  Defined.

End A.

(*
  [TypeTheory.ALV2.SplitTypeCat_ComprehensionCat]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**
This module defines an equivalence of types
for [split_typecat] and [discrete_comprehension_cat].

Main definitions are

- [split_typecat_discrete_comprehension_cat_weq] — equivalence of split type categories and discrete comprehension categories;
- [split_typecat_structure_discrete_comprehension_cat_structure_weq] — equivalence of corresponding structures for a fixed base category;

Equivalence is constructed by showing an isomorphism between split typecat structure
and a formulation of discrete comprehension categories where the type of morphisms
is fixed to a equation that correspond to [A {{f}} = A'] in split type categories:

- [split_typecat_structure_discrete_comprehension_cat_structure_default_mor_weq] —
  equivalence of split typecat structures and discrete comprehension cat structures
  with a particular choice of morphisms (which is equivalent to an arbitrary one);

This formulation is equivalent to the usual one, which proves the equivalence between the usual definitions of structures.

The maps between [split_typecat_structure] and [discrete_comprehension_cat_structure_with_default_mor] are:

- [split_typecat_structure_from_discrete_comprehension_cat_structure_default_mor] —
  construct a split type category structure from a discrete comprehension cat structure
  (with default choice of morphisms);
- [discrete_comprehension_cat_structure_with_default_mor_from_typecat_structure] —
  construct a discrete comprehension cat structure (with default morphisms) from
  a split type category structure.

This module also defines direct maps between [split_typecat_structure] and [discrete_comprehension_cat_structure] (with arbitrary displayed morphisms). However, it is not proven that these form an isomorphism.

*)


Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.Foundations.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.ALV2.FullyFaithfulDispFunctor.
Require Import TypeTheory.ALV2.DiscreteComprehensionCat.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.ComprehensionC.

Section Auxiliary.

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
  Definition discrete_fibration_mor_weq
             {C : category}
             {D : disp_cat C}
             (is_discrete_fibration_D : is_discrete_fibration D) {c c'}
             (f : c' --> c) (d : D c) (d' : D c')
    : (d' -->[f] d) ≃ (pr1 (pr1 (pr1 is_discrete_fibration_D c c' f d)) = d').
  Proof.
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
    apply discrete_fibration_mor_weq.
  Defined.

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

Section DiscreteComprehensionCatWithDefaultMor.

  Section From_SplitTypeCat.

    Context {C : category}.
    Context (TC : split_typecat_structure C).

    Let D_ob := TC : C → UU.
    Let Fob := (λ Γ A, (Γ ◂ A ,, dpr_typecat A))
               : ∏ (Γ : C), D_ob Γ → disp_codomain C Γ.
    Let D_lift_ob := (λ Γ Γ' f A, reind_typecat A f)
      : ∏ (Γ Γ' : C), C ⟦ Γ', Γ ⟧ → D_ob Γ → D_ob Γ'.
    Let D_ob_isaset := pr1 (pr2 TC) : ∏ (Γ : C), isaset (D_ob Γ).

    Let D_mor := default_mor D_ob D_lift_ob.

    Let Fmor := (λ Γ Γ' A A' f ff,
                 transportf
                   (λ AA, ((Γ ◂ AA,, dpr_typecat AA) : disp_codomain C Γ)
                            -->[f] (Γ' ◂ A',, dpr_typecat A'))
                   ff (q_typecat A' f ,, dpr_q_typecat A' f))
                : ∏ (Γ Γ' : C) (A : D_ob Γ) (A' : D_ob Γ') (f : C ⟦ Γ, Γ' ⟧),
                  D_mor _ _ A A' f → Fob Γ A -->[ f] Fob Γ' A'.

    Definition disp_cat_id_comp_from_split_typecat_structure_default_mor
        : disp_cat_id_comp C (D_ob ,, D_mor).
    Proof.
        use make_dirprod.
        - intros Γ A. apply (pr1 (pr1 (dirprod_pr2 (pr2 TC)))).
        - intros Γ Γ' Γ'' f g A A' A'' ff gg. 
          simpl.
          set (reind_comp := pr1 (dirprod_pr2 (pr2 (pr2 TC)))).
          unfold D_mor, default_mor in *.
          simpl in *.
          apply (reind_comp _ _ _ _ _ _
                   @ maponpaths (λ B, B {{f}}) gg
                   @ ff).
    Defined.

    Definition disp_cat_data_from_split_typecat_structure_default_mor
        : disp_cat_data C
        := (_ ,, disp_cat_id_comp_from_split_typecat_structure_default_mor).

    Definition disp_cat_axioms'_from_split_typecat_structure_default_mor
        : disp_cat_axioms' C disp_cat_data_from_split_typecat_structure_default_mor.
    Proof.
        repeat use make_dirprod.
        - intros. apply (pr1 (pr2 TC)).
        - intros. apply (pr1 (pr2 TC)).
        - intros. apply (pr1 (pr2 TC)).
    Qed.

    Definition disp_cat_axioms_from_split_typecat_structure_default_mor
        : disp_cat_axioms C disp_cat_data_from_split_typecat_structure_default_mor.
    Proof.
      apply disp_cat_axioms'_weq.
      use make_dirprod.
      - apply disp_cat_axioms'_from_split_typecat_structure_default_mor.
      - apply default_mor_homsets.
        apply D_ob_isaset.
    Qed.

    Definition disp_cat_from_split_typecat_structure_default_mor
      : disp_cat C
      := (_ ,, disp_cat_axioms_from_split_typecat_structure_default_mor).

    Let FF := (Fob ,, Fmor)
              : disp_functor_data
                  (functor_identity C)
                  disp_cat_from_split_typecat_structure_default_mor
                  (disp_codomain C).

    Definition disp_functor_axioms_from_split_typecat_structure_default_mor
      : disp_functor_axioms FF.
    Proof.
      use make_dirprod.
      - intros Γ A.
        use total2_paths_f. 2: apply homset_property.
        simpl. etrans. apply (pr1_transportf _ (λ AA, C ⟦ Γ ◂ AA, _ ⟧)).
        cbn. etrans. apply maponpaths.
        apply (pr2 (pr1 (dirprod_pr2 (pr2 TC))) Γ A).
        induction (pr1 (pr1 (dirprod_pr2 (pr2 TC))) Γ A).
        apply idpath.

      - intros Γ Γ' Γ'' A A' A'' f g ff gg.
        use total2_paths_f. 2: apply homset_property.
        + simpl. etrans. apply (pr1_transportf _ (λ AA, C ⟦ Γ ◂ AA, _ ⟧)).
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

    Definition disp_functor_from_split_typecat_structure_default_mor
      : disp_functor
          (functor_identity C)
          disp_cat_from_split_typecat_structure_default_mor
          (disp_codomain C)
      := (FF,, disp_functor_axioms_from_split_typecat_structure_default_mor).

    Definition disp_functor_from_split_typecat_structure_is_cartesian_default_mor
      : is_cartesian_disp_functor disp_functor_from_split_typecat_structure_default_mor.
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
    Qed.

    Definition discrete_comprehension_cat_structure_with_default_mor_from_typecat_structure
      : discrete_comprehension_cat_structure_with_default_mor C.
    Proof.
      exists D_ob.
      exists Fob.
      exists D_lift_ob.
      exists (pr1 (pr2 TC)).
      unfold discrete_comprehension_cat_structure2.
      exists Fmor.
      exists disp_cat_id_comp_from_split_typecat_structure_default_mor.
      exists disp_cat_axioms'_from_split_typecat_structure_default_mor.
      exists disp_functor_axioms_from_split_typecat_structure_default_mor.
      exact disp_functor_from_split_typecat_structure_is_cartesian_default_mor.
    Defined.

  End From_SplitTypeCat.


End DiscreteComprehensionCatWithDefaultMor.

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
  Qed.

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
      simpl. etrans. apply (pr1_transportf _ (λ AA, C ⟦ Γ ◂ AA, _ ⟧)).
      cbn. etrans. apply maponpaths.
      apply (pr2 (pr1 (dirprod_pr2 (pr2 TC))) Γ A).
      induction (pr1 (pr1 (dirprod_pr2 (pr2 TC))) Γ A).
      apply idpath.

    - intros Γ Γ' Γ'' A A' A'' f g ff gg.
      use total2_paths_f. 2: apply homset_property.
      + simpl. etrans. apply (pr1_transportf _ (λ AA, C ⟦ Γ ◂ AA, _ ⟧)).
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
      apply is_symmetric_isPullback.
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
Section From_DiscreteComprehensionCat_Default.

  Context {C : category}.

  Context (DC : discrete_comprehension_cat_structure_with_default_mor C).

  Let D_ob := pr1 DC.
  Let F_ob := pr1 (pr2 DC).
  Let D_lift_ob := pr1 (pr2 (pr2 DC)).
  Let D_ob_isaset := pr1 (pr2 (pr2 (pr2 DC))).
  Let F_mor := pr1 (pr2 (pr2 (pr2 (pr2 DC)))).
  Let D_id_comp := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 DC))))).
  Let D_axioms' := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 DC)))))).
  Let FF_axioms := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 DC))))))).
  Let is_cartesian_FF := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 DC))))))).

  Let D
    := ((_ ,, D_id_comp)
          ,, disp_cat_axioms'_weq (D_axioms', default_mor_homsets _ _ D_ob_isaset))
       : disp_cat C.

  Let FF := (_ ,, FF_axioms)
            : disp_functor (functor_identity C)
                           D (disp_codomain C).

  Let D_lift_ob_mor := λ Γ Γ' f A, (D_lift_ob Γ Γ' f A ,, idpath _).

  Local Definition D_lift_ob_mor_unique
        { Γ Γ' : C } (f : C ⟦ Γ', Γ ⟧) (A : D_ob Γ)
    : ∏ (gg : ∑ (A' : D_ob Γ'), D_lift_ob _ _ f A = A'),
      gg = D_lift_ob_mor _ _ f A.
  Proof.
    intros gg.
    use total2_paths_f.
    - exact (! pr2 gg).
    - apply D_ob_isaset.
  Defined.

  Definition is_discrete_fibration_D_from_discrete_comprehension_cat_structure_default_mor
    : is_discrete_fibration D.
  Proof.
    use make_dirprod.
    - intros Γ Γ' f A.
      exists (D_lift_ob_mor _ _ f A).
      apply (D_lift_ob_mor_unique f A).
    - apply D_ob_isaset.
  Defined.

  Definition typecat_structure1_from_discrete_comprehension_cat_structure_default_mor
    : typecat_structure1 C.
  Proof.
    exists D_ob.
    use make_dirprod.
    - intros Γ A. exact (pr1 (F_ob _ A)).
    - intros Γ A Γ' f. exact (D_lift_ob Γ Γ' f A).
  Defined.

  Definition typecat_structure2_from_discrete_comprehension_cat_structure_default_mor
    : typecat_structure2 typecat_structure1_from_discrete_comprehension_cat_structure_default_mor.
  Proof.
    unfold typecat_structure2.
    repeat use tpair.
    - intros Γ A. exact (pr2 (F_ob _ A)).
    - intros Γ A Γ' f.
      apply (pr1 (F_mor _ _ _ _ _ (idpath _))).
    - intros Γ A Γ' f. simpl.
      apply (pr2 (F_mor _ _ _ _ _ (idpath _))).
    - simpl. intros Γ A Γ' f.
      apply is_symmetric_isPullback.
      use cartesian_isPullback_in_cod_disp.
      apply is_cartesian_FF.
      apply (unique_lift_is_cartesian (D := (_ ,, is_discrete_fibration_D_from_discrete_comprehension_cat_structure_default_mor)) f A).
  Defined.

  Definition typecat_structure_from_discrete_comprehension_cat_structure_default_mor
    : typecat_structure C
    := (_ ,, typecat_structure2_from_discrete_comprehension_cat_structure_default_mor).

  Lemma F_mor_over_idpath_to_any
        {Γ Γ' : C}
        {f : Γ --> Γ'}
        {A : D Γ'} {B : D Γ}
        (ff : B -->[f] A)
    : F_mor _ _ _ _ _ (idpath _ : (D_lift_ob _ _ f A : D Γ) -->[f] A) =
      transportb (λ B : D Γ, F_ob _ B -->[f] F_ob _ A)
                 ff (F_mor _ _ _ _ _ ff).
  Proof.
    induction ff. apply idpath. 
  Defined.

  Definition is_split_typecat_from_discrete_comprehension_cat_structure_default_mor
    : is_split_typecat typecat_structure_from_discrete_comprehension_cat_structure_default_mor.
  Proof.
    repeat use make_dirprod.
    - apply D_ob_isaset.
    - use tpair.
      + apply (@id_disp _ D).
      + intros Γ A. cbn.
        etrans. apply maponpaths, (F_mor_over_idpath_to_any (@id_disp _ D _ A)).
        etrans. apply maponpaths, maponpaths, (disp_functor_id FF A).
        
        etrans. apply maponpaths, maponpaths. apply idpath_transportb.
        unfold mor_disp, disp_codomain. cbn.
        etrans. use (pr1_transportf (pr1 DC Γ)).
        simpl.

        etrans. apply (functtransportb (λ B, pr1 (F_ob Γ B)) (λ BB, C ⟦ BB, pr1 (F_ob Γ A) ⟧)).
        etrans. 2: apply id_right.
        apply idtoiso_precompose'.

    - use tpair.
      + intros Γ A Γ' f Γ'' g. cbn.
        apply (@comp_disp _ D _ _ _ g f
                          (D_lift_ob _ _ g (D_lift_ob _ _ f A))
                          _
                          A
                          (idpath _)
                          (idpath _)
              ).
      + intros Γ A Γ' f Γ'' g. cbn.

        set (H := @disp_functor_comp
                    _ _ _ _ _ FF
                    _ _ _ _ _ A
                    g f (idpath _) (idpath _)
            ).
        simpl in H.

        etrans. apply maponpaths.
        apply (F_mor_over_idpath_to_any
                 (@comp_disp _ D _ _ _ g f
                             (D_lift_ob _ _ g (D_lift_ob _ _ f A))
                             _
                             A
                             (idpath _)
                             (idpath _)
              )).

        etrans. apply maponpaths, maponpaths. apply (disp_functor_comp FF).

        unfold mor_disp, disp_codomain. cbn.
        etrans. use (pr1_transportf (pr1 DC _)). simpl.

        etrans. apply (functtransportb (λ B, pr1 (F_ob Γ'' B)) (λ BB, C ⟦ BB, pr1 (F_ob Γ A) ⟧)).

        etrans. 2: apply assoc.
        apply idtoiso_precompose'.
  Defined.

  Definition split_typecat_structure_from_discrete_comprehension_cat_structure_default_mor
    : split_typecat_structure C
    := (_ ,, is_split_typecat_from_discrete_comprehension_cat_structure_default_mor).

End From_DiscreteComprehensionCat_Default.

Section SplitTypeCat_DiscreteComprehensionCat_Equiv.

  Context {C : category}.

  Definition split_typecat_structure_discrete_comprehension_cat_structure_default_mor_weq
    : split_typecat_structure C ≃ discrete_comprehension_cat_structure_with_default_mor C.
  Proof.
    use weq_iso.
    - apply discrete_comprehension_cat_structure_with_default_mor_from_typecat_structure.
    - apply split_typecat_structure_from_discrete_comprehension_cat_structure_default_mor.
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
    - intros DC.
      use total2_paths_f.
      2: use total2_paths_f.
      3: use total2_paths_f.
      4: use total2_paths_f.
      5: use total2_paths_f.
      + apply idpath.
      + apply idpath.
      + apply idpath.
      + apply idpath.
      + apply funextsec. intros ?.
        apply funextsec. intros ?.
        apply funextsec. intros ?.
        apply funextsec. intros ?.
        apply funextsec. intros ?.
        apply funextsec. intros ff.
        induction ff.
        apply idpath.
        
      + apply isaprop_discrete_comprehension_cat_structure2'_with_default_mor.
  Defined.

  Definition split_typecat_structure_discrete_comprehension_cat_structure_weq
    : split_typecat_structure C ≃ discrete_comprehension_cat_structure C
    := (invweq discrete_comprehension_cat_structure_with_default_mor_weq
        ∘ split_typecat_structure_discrete_comprehension_cat_structure_default_mor_weq)%weq.

End SplitTypeCat_DiscreteComprehensionCat_Equiv.

Section Cats_Equiv.
  
  Definition split_typecat_discrete_comprehension_cat_weq
  : split_typecat ≃ discrete_comprehension_cat.
  Proof.
    eapply weqcomp. apply weqtotal2asstor.
    apply (weqtotal2 (idweq _)); intros C. simpl.
    apply split_typecat_structure_discrete_comprehension_cat_structure_weq.
  Defined.

End Cats_Equiv.


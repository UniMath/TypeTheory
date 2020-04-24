(**
  [TypeTheory.ALV2.Comprehension_Cats]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**
TODO
*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.TypeCat.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.ComprehensionC.

Set Automatic Introduction.

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

Section TypeCat_to_ComprehensionCat.

  Context (C : category).

  (* TODO: we do not need full typecat to induce the displayed functor, so we should factor out the necessary part *)
  Section TypeCat_induced_DisplayedCategory_over_C.

    Context (TC : typecat_structure C).

    Definition typecat_disp_ob_mor : disp_cat_ob_mor C.
    Proof.
        use tpair.
        - apply TC.
        - intros Γ' Γ A' A f.
        exact (∑ ff : Γ' ◂ A' --> Γ ◂ A,
                        ff ;; dpr_typecat A = dpr_typecat A' ;; f).
    Defined.

    Definition typecat_disp_id_comp : disp_cat_id_comp _ typecat_disp_ob_mor.
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

    Definition typecat_disp_data : disp_cat_data C
        := (typecat_disp_ob_mor,, typecat_disp_id_comp).

    (* NOTE: copied with slight modifications from https://github.com/UniMath/TypeTheory/blob/ad54ca1dad822e9c71acf35c27d0a39983269462/TypeTheory/Displayed_Cats/DisplayedCatFromCwDM.v#L78-L107  *)
    Definition typecat_disp_axioms : disp_cat_axioms _ typecat_disp_data.
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
    Defined.

    Definition typecat_disp : disp_cat C
        := (typecat_disp_data ,, typecat_disp_axioms).

    (* NOTE: copied with slight modifications from https://github.com/UniMath/TypeTheory/blob/ad54ca1dad822e9c71acf35c27d0a39983269462/TypeTheory/Displayed_Cats/DisplayedCatFromCwDM.v#L114-L143 *)
    Definition pullback_is_cartesian
               {Γ Γ' : C} {f : Γ' --> Γ}
               {A  : typecat_disp Γ} {A' : typecat_disp Γ'} (ff : A' -->[f] A)
      : (isPullback _ _ _ _ (pr2 ff)) -> is_cartesian ff.
    Proof.
      intros Hpb Δ g B hh.
      eapply iscontrweqf.
      2: { 
        use Hpb.
        + exact (Δ ◂ B).
        + exact (pr1 hh).
        + simpl in B. refine (dpr_typecat B ;; g).
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

    Lemma is_fibration_typecat_disp : cleaving typecat_disp.
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

    Definition typecat_disp_functor_data
    : disp_functor_data (functor_identity C) typecat_disp (disp_codomain C).
    Proof.
    use tpair.
    - intros Γ A. exists (Γ ◂ A). apply dpr_typecat.
    - intros Γ' Γ A' A f ff. apply ff.
    Defined.

    Definition typecat_disp_functor_axioms
    : disp_functor_axioms typecat_disp_functor_data.
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
    : disp_functor (functor_identity C) typecat_disp (disp_codomain C)
    := (typecat_disp_functor_data ,, typecat_disp_functor_axioms).

    Definition typecat_disp_functor_ff
      : disp_functor_ff typecat_disp_functor.
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

    Definition typecat_disp_functor_is_cartesian
      : is_cartesian_disp_functor typecat_disp_functor.
    Proof.
      use cartesian_functor_from_fibration.
      intros Γ Γ' f A.
      apply hinhpr.
      exists (is_fibration_typecat_disp _ _ f A).

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

  End TypeCat_induced_DisplayedCategory_over_C.

  Definition typecat_to_comprehension_cat_structure
    : typecat_structure C → comprehension_cat_structure C.
  Proof.
    intros TC.
    exists (typecat_disp TC).
    exists (is_fibration_typecat_disp _).
    exists (typecat_disp_functor _).
    apply typecat_disp_functor_is_cartesian.
  Defined.

End TypeCat_to_ComprehensionCat.

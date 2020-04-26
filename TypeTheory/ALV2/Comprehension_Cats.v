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

    Lemma cleaving_typecat_disp : cleaving typecat_disp.
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

    Definition typecat_comp_ext_compare
               {Γ : C} {A B : TC Γ}
      : (A = B) → Γ ◂ A --> Γ ◂ B.
    Proof.
      intros p. induction p.
      apply identity.
    Defined.

    Definition typecat_idtoiso_dpr
               {Γ : C} {A B : TC Γ}
               (p : A = B)
      : idtoiso (maponpaths (λ B, Γ ◂ B) p) ;; dpr_typecat B = dpr_typecat A.
    Proof.
      induction p. apply id_left.
    Defined.

    Definition typecat_iso_triangle
               {Γ : C} (A B : TC Γ)
      := ∑ (i : z_iso (Γ ◂ A) (Γ ◂ B)),
                        i ;; dpr_typecat B = dpr_typecat A
         × inv_from_z_iso i ;; dpr_typecat A = dpr_typecat B.

    Definition typecat_idtoiso_triangle
               {Γ : C} (A B : TC Γ)
      : (A = B) → typecat_iso_triangle A B.
    Proof.
      intros p. induction p.
      use tpair.
      - apply identity_z_iso.
      - use make_dirprod. 
        + apply id_left.
        + apply id_left.
    Defined.

    Definition pr1_transportb
               {A : UU} {B : A → UU} (P : ∏ a : A, B a → UU) {a a' : A}
               (e : a = a') (xs : ∑ b : B a', P a' b)
      : pr1 (transportb (λ x : A, ∑ b : B x, P x b) e xs) =
        transportb (λ x : A, B x) e (pr1 xs).
    Proof.
      induction e.
      apply idpath.
    Defined.

    Definition typecat_is_triangle_to_idtoiso_fiber_disp
               {Γ : C} (A B : TC Γ)
      : typecat_iso_triangle A B → @iso_disp C typecat_disp _ _ (identity_iso Γ) A B.
    Proof.
      intros tr.
      set (i        := pr1 (pr1 tr) : C ⟦ Γ ◂ A, Γ ◂ B ⟧ ).
      set (inv_i    := pr1 (pr2 (pr1 tr)) : C ⟦ Γ ◂ B, Γ ◂ A ⟧).
      set (i_inv_i  := dirprod_pr1 (pr2 (pr2 (pr1 tr))) : i ;; inv_i = identity _).
      set (inv_i_i  := dirprod_pr2 (pr2 (pr2 (pr1 tr))) : inv_i ;; i = identity _).
      set (iB_A     := pr1 (pr2 tr) : i ;; dpr_typecat B = dpr_typecat A).
      set (inv_iA_B := dirprod_pr2 (pr2 tr) : inv_i ;; dpr_typecat A = dpr_typecat B).

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
      : @iso_disp C typecat_disp _ _ (identity_iso Γ) A B → typecat_iso_triangle A B.
    Proof.
      intros tr.
      set (i        := pr1 (pr1 tr) : C ⟦ Γ ◂ A, Γ ◂ B ⟧ ).
      set (iB_A     := pr2 (pr1 tr) : i ;; dpr_typecat B = dpr_typecat A ;; identity _).
      set (inv_i    := pr1 (pr1 (pr2 tr)) : C ⟦ Γ ◂ B, Γ ◂ A ⟧).
      set (inv_iA_B := pr2 (pr1 (pr2 tr))
                       : inv_i ;; dpr_typecat A = dpr_typecat B ;; identity _).
      set (inv_i_i  := maponpaths pr1 (pr1 (pr2 (pr2 tr))) : _).
      set (i_inv_i  := maponpaths pr1 (dirprod_pr2 (pr2 (pr2 tr))) : _).

      repeat use tpair.
      - exact i.
      - exact inv_i.
      - etrans. apply i_inv_i.
        etrans.
        use (pr1_transportb (λ _ (_ : C ⟦ Γ ◂ A, Γ ◂ A ⟧), _)).
        simpl. apply (maponpaths (λ f, f _) (transportb_const _ _)).
      - etrans. apply inv_i_i.
        etrans.
        use (pr1_transportb (λ _ (_ : C ⟦ Γ ◂ B, Γ ◂ B ⟧), _)).
        simpl. apply (maponpaths (λ f, f _) (transportb_const _ _)).
      - etrans. apply iB_A. apply id_right.
      - etrans. apply inv_iA_B. apply id_right.
    Defined.

    Definition typecat_is_triangle_idtoiso_fiber_disp_isweq
               {Γ : C} (A B : TC Γ)
      : isweq (typecat_is_triangle_to_idtoiso_fiber_disp A B).
    Proof.
      use isweq_iso.
      - apply idtoiso_fiber_disp_to_typecat_is_triangle.
      - intros tr.
        repeat use total2_paths_f.
        + apply idpath.
        + apply idpath.
        + apply homset_property.
        + apply homset_property.
        + apply homset_property.
        + apply homset_property.
      - intros tr.
        etrans.
        use total2_paths_f.
        + use total2_paths_f.
          * apply idpath.
          * apply homset_property.
        + use total2_paths_f.
          (* STUCK here: idpath does not work :( *)
    (*
          * apply idpath.
          * apply homset_property.
        + apply idpath.
        + apply homset_property.
        + apply (@homsets_disp _ typecat_disp).
        + apply (@homsets_disp _ typecat_disp).
    Defined.
     *)
    Abort.
    
    Definition typecat_is_triangle_idtoiso_fiber_disp_weq
               {Γ : C} (A B : TC Γ)
      : typecat_iso_triangle A B ≃ @iso_disp C typecat_disp _ _ (identity_iso Γ) A B.
    Proof.
      (* ((i,, is_z_iso i) ,, (iB_A , inv_iA_B)) *)
      (* ((i,, iB_A) ,, ((inv_i,, inv_iA_B) ,, (_ , _))) *)
      eapply weqcomp. apply weqtotal2asstor.
      eapply weqcomp. 2: apply weqtotal2asstol.
      apply (weqtotal2 (idweq _)).

      intros i.
      (* (is_z_iso i ,, (iB_A , inv_iA_B)) *)
      (* (iB_A ,, ((inv_i,, inv_iA_B) ,, (_ , _))) *)
      eapply weqcomp. simpl. apply WeakEquivalences.weqtotal2comm.
      use weqtotal2.
      - simpl. apply weqpathscomp0r, pathsinv0, id_right.
      - intros ?.
        (* ((inv_i,, _) ,, inv_iA_B) *)
        (* ((inv_i,, inv_iA_B) ,, (_ , _)) *)
        eapply weqcomp. apply weqtotal2asstor.
        eapply weqcomp. 2: apply weqtotal2asstol.
        apply (weqtotal2 (idweq _)).

        intros inv_i. unfold inv_from_z_iso. simpl.
        eapply weqcomp. apply weqdirprodcomm.
        use weqtotal2.
        + simpl. apply weqpathscomp0r, pathsinv0, id_right.
        + intros ?. simpl.
          use weq_iso.
          * intros i_is_inv.
            set (i_inv_i := dirprod_pr1 i_is_inv).
            set (inv_i_i := dirprod_pr2 i_is_inv).
            use make_dirprod.
            -- use total2_paths_f.
               2: apply homset_property.
               etrans. apply inv_i_i.
               apply pathsinv0.
               etrans. apply (pr1_transportb (λ _ (_ : C ⟦ Γ ◂ B, Γ ◂ B ⟧), _)).
               apply (maponpaths (λ f, f _) (transportb_const _ _)).
            -- use total2_paths_f.
               2: apply homset_property.
               etrans. apply i_inv_i.
               apply pathsinv0.
               etrans. apply (pr1_transportb (λ _ (_ : C ⟦ Γ ◂ A, Γ ◂ A ⟧), _)).
               apply (maponpaths (λ f, f _) (transportb_const _ _)).
          * intros i_is_inv.
            set (inv_i_i := maponpaths pr1 (dirprod_pr1 i_is_inv)).
            set (i_inv_i := maponpaths pr1 (dirprod_pr2 i_is_inv)).
            use make_dirprod.
            -- etrans. apply i_inv_i.
               etrans.
               use (pr1_transportb (λ _ (_ : C ⟦ Γ ◂ A, Γ ◂ A ⟧), _)).
               simpl. apply (maponpaths (λ f, f _) (transportb_const _ _)).
            -- etrans. apply inv_i_i.
               etrans.
               use (pr1_transportb (λ _ (_ : C ⟦ Γ ◂ B, Γ ◂ B ⟧), _)).
               simpl. apply (maponpaths (λ f, f _) (transportb_const _ _)).
          * intros e.
            use PartA.dirprod_paths.
            -- apply homset_property.
            -- apply homset_property.
          * intros e.
            use PartA.dirprod_paths.
            -- apply (@homsets_disp _ typecat_disp).
            -- apply (@homsets_disp _ typecat_disp).
    Defined.

    Definition typecat_disp_is_disp_univalent
               (w' : ∏ (Γ : C) (A B : TC Γ), isweq (typecat_idtoiso_triangle A B))
      : is_univalent_disp typecat_disp.
    Proof.
      apply is_univalent_disp_from_fibers.
      intros Γ A B.
      set (f := typecat_is_triangle_idtoiso_fiber_disp_weq A B).
      set (g := (typecat_idtoiso_triangle A B,, w' _ A B)).
      use weqhomot.
      - apply (weqcomp g f).
      - intros e.
        induction e.
        use total2_paths_f.
        + use total2_paths_f.
          * apply idpath.
          * apply homset_property.
        + apply proofirrelevance.
          apply isaprop_is_iso_disp.
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
      use cartesian_functor_from_cleaving.
      { apply cleaving_typecat_disp. }
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

  End TypeCat_induced_DisplayedCategory_over_C.

  Definition typecat_to_comprehension_cat_structure
    : typecat_structure C → comprehension_cat_structure C.
  Proof.
    intros TC.
    exists (typecat_disp TC).
    exists (cleaving_typecat_disp _).
    exists (typecat_disp_functor _).
    apply typecat_disp_functor_is_cartesian.
  Defined.

End TypeCat_to_ComprehensionCat.

(* TODO: move upstream *)
Definition comprehension_cat := ∑ (C : category), (comprehension_cat_structure C).

Definition typecat_to_comprehension_cat
  : typecat → comprehension_cat.
Proof.
  intros TC.
  exists (pr1 TC).
  apply (typecat_to_comprehension_cat_structure _ (pr2 TC)).
Defined.


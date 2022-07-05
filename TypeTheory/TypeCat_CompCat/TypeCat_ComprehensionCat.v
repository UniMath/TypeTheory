(*
  [TypeTheory.TypeCat_CompCat.TypeCat_ComprehensionCat]

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
Require Import TypeTheory.Auxiliary.CategoryTheory.
Require Import TypeTheory.Auxiliary.Pullbacks.

Require Import TypeTheory.TypeCat.TypeCat.
Require Import TypeTheory.CompCats.FullyFaithfulDispFunctor.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.ComprehensionC.

Section TypeCat_ObjExt.

  (* Object extension structure is part of the definition of type category that includes:
   * - the type family [ty_typecat] : C → UU;
   * - for every Γ : C and A : Ty(Γ):
   *   - context extension [Γ ◂ A];
   *   - for every morphism f : Γ' --> Γ, reindexing mapping [reind_typecat];
   *   - projection morphism [dpr_typecat_obj_ext]: Γ ◂ A --> Γ.
   *)
  Definition typecat_obj_ext_structure (C : precategory) 
    := ∑ (Ty : C → UU)
         (ext : ∏ (Γ : C), Ty Γ → C)
       (* dpr : *), ∏ Γ (A : Ty Γ), ext Γ A --> Γ.

  Definition Ty_obj_ext (C : precategory)
             (TC : typecat_obj_ext_structure C)
    : C → UU
    := pr1 TC.

  Coercion Ty_obj_ext : typecat_obj_ext_structure >-> Funclass.

  Definition obj_ext_typecat {C : precategory} {TC : typecat_obj_ext_structure C} 
             (Γ : C) (A : TC Γ) : C
    := pr1 (pr2 TC) Γ A.

  Definition dpr_typecat_obj_ext {C : precategory}
             {TC : typecat_obj_ext_structure C} {Γ} (A : pr1 TC Γ)
    : obj_ext_typecat Γ A --> Γ
    := pr2 (pr2 TC) Γ A.
  
  Definition typecat_obj_ext_from_typecat (C : precategory) (TC : typecat_structure C) 
    : typecat_obj_ext_structure _  := (_ ,, _ ,, @dpr_typecat _ TC).
  Coercion typecat_obj_ext_from_typecat : typecat_structure >-> typecat_obj_ext_structure.

End TypeCat_ObjExt.

Local Notation "'π' A" := (dpr_typecat_obj_ext A) (at level 5).

Section TypeCat_Comp_Ext_Compare.

  Context {C : precategory}.
  Context (TC : typecat_obj_ext_structure C).

  Definition typecat_comp_ext_compare
             {Γ : C} {A B : TC Γ}
    : (A = B) → z_iso (obj_ext_typecat Γ A) (obj_ext_typecat Γ B).
  Proof.
    intros p. induction p.
    apply identity_z_iso.
  Defined.

  Definition typecat_idtoiso_dpr
             {Γ : C} {A B : TC Γ}
             (p : A = B)
    : idtoiso (maponpaths (λ B, obj_ext_typecat Γ B) p) ;; π B = π A.
  Proof.
    induction p. apply id_left.
  Defined.

  Definition typecat_iso_triangle
             {Γ : C} (A B : TC Γ)
    := ∑ (i : z_iso (obj_ext_typecat Γ A) (obj_ext_typecat Γ B)),
       i ;; π B = π A.

  Definition typecat_iso_triangle_swap
             {Γ : C} {A B : TC Γ}
    : typecat_iso_triangle A B → typecat_iso_triangle B A.
  Proof.
    intros tr.
    exists (z_iso_inv_from_z_iso (pr1 tr)).
    etrans. apply maponpaths, pathsinv0, (pr2 tr).
    etrans. apply assoc.
    etrans. apply maponpaths_2, z_iso_after_z_iso_inv.
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
      exact (∑ ff : obj_ext_typecat Γ' A' --> obj_ext_typecat Γ A,
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
      etrans. 2: { use (transport_map (fun a : C⟦_,_⟧ => pr1)). }
      apply pathsinv0, transportf_const'.
    - (* id_right_disp *) 
      apply subtypePath.
      { intro. apply homset_property. }
      etrans. apply id_right.
      etrans. 2: { use (transport_map (fun a : C⟦_,_⟧ => pr1)). }
      apply pathsinv0, transportf_const'.
    - (* assoc_disp *) 
      apply subtypePath.
      { intro. apply homset_property. }
      etrans. apply assoc.
      etrans. 2: { use (transport_map (fun a : C⟦_,_⟧ => pr1)). }
      apply pathsinv0, transportf_const'.
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
      : typecat_iso_triangle _ A B → @z_iso_disp C (typecat_disp TC) _ _ (identity_z_iso Γ) A B.
    Proof.
      intros tr.
      set (i        := pr1 (pr1 tr) : C ⟦ obj_ext_typecat Γ A, obj_ext_typecat Γ B ⟧ ).
      set (iB_A     := pr2 tr : i ;; π B = π A).

      set (tr' := typecat_iso_triangle_swap TC tr).
      set (inv_i    := pr1 (pr1 tr') : C ⟦ obj_ext_typecat Γ B, obj_ext_typecat Γ A ⟧).
      set (inv_iA_B := pr2 tr' : inv_i ;; π A = π B).

      set (i_inv_i  := z_iso_inv_after_z_iso (pr1 tr) : i ;; inv_i = identity _).
      set (inv_i_i  := z_iso_after_z_iso_inv (pr1 tr) : inv_i ;; i = identity _).

      repeat use tpair.
      - exact i.
      - etrans. apply iB_A. apply pathsinv0, id_right.
      - exact inv_i.
      - simpl. etrans. apply inv_iA_B. apply pathsinv0, id_right.
      - use total2_paths_f.
        2: apply homset_property.
        etrans. apply inv_i_i.
        etrans. 2: { use (transport_map (fun a : C⟦_,_⟧ => pr1)). }
        apply pathsinv0, transportf_const'.
      - use total2_paths_f.
        2: apply homset_property.
        etrans. apply i_inv_i.
        etrans. 2: { use (transport_map (fun a : C⟦_,_⟧ => pr1)). }
        apply pathsinv0, transportf_const'.
    Defined.

    Definition idtoiso_fiber_disp_to_typecat_is_triangle
               {Γ : C} (A B : TC Γ)
      : @z_iso_disp C (typecat_disp TC) _ _ (identity_z_iso Γ) A B → typecat_iso_triangle _ A B.
    Proof.
      intros tr.
      set (i        := pr1 (pr1 tr) : C ⟦ obj_ext_typecat Γ A, obj_ext_typecat Γ B ⟧ ).
      set (iB_A     := pr2 (pr1 tr) : i ;; π B = π A ;; identity _).
      set (inv_i    := pr1 (pr1 (pr2 tr)) : C ⟦ obj_ext_typecat Γ B, obj_ext_typecat Γ A ⟧).
      set (inv_iA_B := pr2 (pr1 (pr2 tr))
                       : inv_i ;; π A = π B ;; identity _).
      set (inv_i_i  := maponpaths pr1 (pr1 (pr2 (pr2 tr))) : _).
      set (i_inv_i  := maponpaths pr1 (dirprod_pr2 (pr2 (pr2 tr))) : _).

      repeat use tpair.
      - exact i.
      - apply inv_i.
      - etrans. apply i_inv_i.
        etrans.
        { apply pathsinv0. use (transport_map (fun a : C⟦_,_⟧ => pr1)). }
        apply transportf_const'.
      - etrans. apply inv_i_i.
        etrans.
        { apply pathsinv0. use (transport_map (fun a : C⟦_,_⟧ => pr1)). }
        apply transportf_const'.
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
        + apply z_iso_eq, idpath.
        + apply homset_property.
      - intros tr.
        apply eq_z_iso_disp.
        use total2_paths_f.
        + apply idpath.
        + apply homset_property.
    Defined.

    Definition typecat_is_triangle_idtoiso_fiber_disp_weq
               {Γ : C} (A B : TC Γ)
      : typecat_iso_triangle _ A B ≃ @z_iso_disp C (typecat_disp TC) _ _ (identity_z_iso Γ) A B
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
      { exact (weqcomp g f). }
      intros p. induction p.
      use total2_paths_f.
      - use total2_paths_f.
        + apply idpath.
        + apply homset_property.
      - apply isaprop_is_z_iso_disp.
    Defined.

    Definition typecat_disp_is_disp_univalent_implies_typecat_idtoiso_triangle_isweq
               (D_is_univalent : is_univalent_disp (typecat_disp TC))
      : ∏ (Γ : C) (A B : TC Γ), isweq (typecat_idtoiso_triangle _ A B).
    Proof.
      intros Γ A B.
      set (f := typecat_is_triangle_idtoiso_fiber_disp_weq A B).
      set (g := (idtoiso_fiber_disp ,, is_univalent_in_fibers_from_univalent_disp _ D_is_univalent _ A B)).
      use weqhomot.
      { exact (weqcomp g (invweq f)). }
      intros p. induction p.
      use total2_paths_f.
      - apply z_iso_eq, idpath.
      - apply homset_property.
    Defined.

  End TypeCat_Disp_is_univalent.

  Section TypeCat_Disp_Cleaving.

    Context {C : category}.

    (* NOTE: copied with slight modifications from https://github.com/UniMath/TypeTheory/blob/ad54ca1dad822e9c71acf35c27d0a39983269462/TypeTheory/Displayed_Cats/DisplayedCatFromCwDM.v#L114-L143 *)
    Definition pullback_is_cartesian
               (TC : typecat_obj_ext_structure C)
               {Γ Γ' : C} {f : Γ' --> Γ}
               {A : typecat_disp TC Γ} {A' : typecat_disp TC Γ'} (ff : A' -->[f] A)
      : (isPullback (pr2 ff)) -> is_cartesian ff.
    Proof.
      intros Hpb Δ g B hh.
      eapply iscontrweqf.
      2: { 
        use Hpb.
        + exact (obj_ext_typecat Δ B).
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
        eapply @is_symmetric_isPullback, reind_pb_typecat.
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
    - intros Γ A. exists (obj_ext_typecat Γ A). apply dpr_typecat_obj_ext.
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

Section ComprehensionCat_TypeCat.
  Context {C : category}.
  Context (CC : comprehension_cat_structure C).

  Let D := pr1 CC : disp_cat C.
  Let cleaving_D   := pr1 (pr2 CC) : cleaving D.
  Let comprehension_functor
    := pr1 (pr2 (pr2 CC))
       : disp_functor _ D (disp_codomain C).
  Let comprehension_functor_is_cartesian
    := pr2 (pr2 (pr2 CC))
       : is_cartesian_disp_functor comprehension_functor.

  Definition ty_from_comprehension_cat : C → UU
    := ob_disp D.

  Definition ext_from_comprehension_cat
             (Γ : C) (A : ty_from_comprehension_cat Γ)
    : C
    := pr1 (comprehension_functor Γ A).

  Definition reind_from_comprehension_cat
             (Γ : C) (A : ty_from_comprehension_cat Γ)
             (Γ' : C) (f : Γ' --> Γ)
    : ty_from_comprehension_cat Γ'
    := pr1 (cleaving_D Γ Γ' f A).

  Definition typecat1_from_comprehension_cat
    : typecat_structure1 C.
  Proof.
    repeat use tpair.
    - exact ty_from_comprehension_cat.
    - exact ext_from_comprehension_cat.
    - exact reind_from_comprehension_cat.
  Defined.

  Definition dpr_from_comprehension_cat
             (Γ : C) (A : ty_from_comprehension_cat Γ)
    : ext_from_comprehension_cat Γ A --> Γ
    := pr2 (comprehension_functor Γ A).
  
  Definition typecat_obj_ext_structure_from_comprehension_cat
    : typecat_obj_ext_structure C.
  Proof.
    repeat use tpair.
    - exact ty_from_comprehension_cat.
    - exact ext_from_comprehension_cat.
    - exact dpr_from_comprehension_cat.
  Defined.

  Definition q_square_from_comprehension_cat
             (Γ : C) (A : ty_from_comprehension_cat Γ)
             (Γ' : C) (f : Γ' --> Γ)
    : comprehension_functor Γ' (reind_from_comprehension_cat _ A _ f)
                            -->[ f ] comprehension_functor Γ A
    := disp_functor_on_morphisms comprehension_functor
                                 (pr1 (pr2 (cleaving_D Γ Γ' f A))).

  Definition q_square_from_comprehension_cat_is_cartesian
             (Γ : C) (A : ty_from_comprehension_cat Γ)
             (Γ' : C) (f : Γ' --> Γ)
    : is_cartesian (q_square_from_comprehension_cat _ A _ f).
  Proof.
    apply comprehension_functor_is_cartesian.
    apply cartesian_lift_is_cartesian.
  Defined.
  
  Definition q_from_comprehension_cat
             (Γ : C) (A : ty_from_comprehension_cat Γ)
             (Γ' : C) (f : Γ' --> Γ)
    : ext_from_comprehension_cat
        Γ' (reind_from_comprehension_cat Γ A Γ' f)
        --> ext_from_comprehension_cat Γ A
    := pr1 (q_square_from_comprehension_cat _ A _ f).

  Definition dpr_q_from_comprehension_cat
             (Γ : C) (A : ty_from_comprehension_cat Γ)
             (Γ' : C) (f : Γ' --> Γ)
    : q_from_comprehension_cat _ A _ f ;; dpr_from_comprehension_cat _ A
      = dpr_from_comprehension_cat _ (reind_from_comprehension_cat _ A _ f) ;; f
    := pr2 (q_square_from_comprehension_cat _ A _ f).

  Definition pullback_from_comprehension_cat
             (Γ : C) (A : ty_from_comprehension_cat Γ)
             (Γ' : C) (f : Γ' --> Γ)
    : isPullback (!dpr_q_from_comprehension_cat _ A _ f).
  Proof.
    intros Δ g k H.
    eapply iscontrweqf.
    2: {
      use (q_square_from_comprehension_cat_is_cartesian _ A _ f).
      - exact Γ'.
      - exact (identity _).
      - apply (Δ,, g).
      - use tpair.
        + apply k.
        + etrans. apply pathsinv0, H.
          apply pathsinv0, maponpaths, id_left.
    }
    apply invweq.
    eapply weqcomp.
    2: apply weqtotal2asstol.
    apply weq_subtypes_iff.
    - intro. apply isapropdirprod; apply homset_property.
    - intro. apply (isofhleveltotal2 1). 
      + apply homset_property.
      + intros. apply homsets_disp.
    - intros gg; split; intros H'.
      + use tpair.
        * etrans. apply (pr1 H').
          apply pathsinv0, id_right.
        * apply subtypePath.
          intro; apply homset_property.
          exact (pr2 H').
      + split.
        * etrans. apply (pr1 H'). apply id_right.
        * etrans. apply (maponpaths pr1 (pr2 H')). apply idpath.
  Defined.

  Definition typecat_structure_from_comprehension_cat
    : typecat_structure C.
  Proof.
    exists typecat1_from_comprehension_cat.
    repeat use tpair.
    - exact dpr_from_comprehension_cat.
    - exact q_from_comprehension_cat.
    - exact dpr_q_from_comprehension_cat.
    - exact pullback_from_comprehension_cat.
  Defined.
                 
End ComprehensionCat_TypeCat.

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

  Definition typecat_to_comprehension_cat
    : typecat → comprehension_cat.
  Proof.
    intros TC.
    exists (pr1 TC).
    apply (typecat_to_comprehension_cat_structure (pr2 TC)).
  Defined.

  Definition typecat_from_comprehension_cat
    : comprehension_cat → typecat.
  Proof.
    intros CC.
    exists (pr1 CC).
    apply (typecat_structure_from_comprehension_cat (pr2 CC)).
  Defined.
    
  Definition fully_faithful_comprehension_cat_structure
             {C : category} (CC : comprehension_cat_structure C)
    := disp_functor_ff (pr1 (pr2 (pr2 CC))).

  Definition typecat_obj_ext_structure_disp_ff_functor_to_codomain_weq
             (C : category)
    : typecat_obj_ext_structure C ≃ ff_disp_functor (disp_codomain C).
  Proof.
    use weq_iso.
    - intros tc.
      exists (pr1 tc).
      intros Γ A.
      exists (obj_ext_typecat Γ A).
      apply (pr2 tc).
    - intros F.
      exists (pr1 F).
      use tpair.
      + intros Γ A.
        exact (pr1 (pr2 F Γ A)).
      + intros Γ A.
        exact (pr2 (pr2 F Γ A)).
    - intros ?. apply idpath.
    - intros ?. apply idpath.
  Defined.

End TypeCat_ComprehensionCat.

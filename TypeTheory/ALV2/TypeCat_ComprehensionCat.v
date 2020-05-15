(*
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
Require Import TypeTheory.ALV2.FullyFaithfulDispFunctor.

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

  (* TODO: move upstream? *)
  Definition weqforall_comm
             {X Y : UU}
             (P : X → Y → UU)
    : (∏ (x : X) (y : Y), P x y) ≃ (∏ (y : Y) (x : X), P x y).
  Proof.
    use weq_iso.
    - intros f. exact (λ y x, f x y).
    - intros f. exact (λ y x, f x y).
    - apply idpath.
    - apply idpath.
  Defined.

  (* TODO: move upstream? *)
  Definition weqprodtoforall
             {X : UU}
             (P Q : X → UU)
    : ((∏ x : X, P x) × (∏ x : X, Q x)) ≃ ∏ x : X, P x × Q x.
  Proof.
    use weqtotaltoforall.
  Defined.
  
  (* TODO: move upstream? *)
  Definition weqforalltoprod
             {X : UU}
             (P Q : X → UU)
    : (∏ x : X, P x × Q x) ≃ ((∏ x : X, P x) × (∏ x : X, Q x)).
  Proof.
    apply invweq, weqprodtoforall.
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
    : (A = B) → iso (obj_ext_typecat Γ A) (obj_ext_typecat Γ B).
  Proof.
    intros p. induction p.
    apply identity_iso.
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
    := ∑ (i : iso (obj_ext_typecat Γ A) (obj_ext_typecat Γ B)),
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
      set (i        := pr1 (pr1 tr) : C ⟦ obj_ext_typecat Γ A, obj_ext_typecat Γ B ⟧ ).
      set (iB_A     := pr2 tr : i ;; π B = π A).

      set (tr' := typecat_iso_triangle_swap TC tr).
      set (inv_i    := pr1 (pr1 tr') : C ⟦ obj_ext_typecat Γ B, obj_ext_typecat Γ A ⟧).
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
        etrans. apply (pr1_transportb (λ _ (_ : C ⟦ obj_ext_typecat Γ B, obj_ext_typecat Γ B ⟧), _)).
        apply (maponpaths (λ f, f _) (transportb_const _ _)).
      - use total2_paths_f.
        2: apply homset_property.
        etrans. apply i_inv_i.
        apply pathsinv0.
        etrans. apply (pr1_transportb (λ _ (_ : C ⟦ obj_ext_typecat Γ A, obj_ext_typecat Γ A ⟧), _)).
        apply (maponpaths (λ f, f _) (transportb_const _ _)).
    Defined.

    Definition idtoiso_fiber_disp_to_typecat_is_triangle
               {Γ : C} (A B : TC Γ)
      : @iso_disp C (typecat_disp TC) _ _ (identity_iso Γ) A B → typecat_iso_triangle _ A B.
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
      - apply is_iso_from_is_z_iso.
        repeat use tpair.
        + apply inv_i.
        + etrans. apply i_inv_i.
          etrans.
          use (pr1_transportb (λ _ (_ : C ⟦ obj_ext_typecat Γ A, obj_ext_typecat Γ A ⟧), _)).
          simpl. apply (maponpaths (λ f, f _) (transportb_const _ _)).
        + etrans. apply inv_i_i.
          etrans.
          use (pr1_transportb (λ _ (_ : C ⟦ obj_ext_typecat Γ B, obj_ext_typecat Γ B ⟧), _)).
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

(* TODO: move upstream *)
Definition comprehension_cat := ∑ (C : category), (comprehension_cat_structure C).

Coercion category_of_comprehension_cat (C : comprehension_cat) := pr1 C.
Coercion structure_of_comprehension_cat (C : comprehension_cat) := pr2 C.

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
    : isPullback _ _ _ _ (!dpr_q_from_comprehension_cat _ A _ f).
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

  Definition typecat_obj_ext_structure_ff_disp_functor_to_codomain_weq
             (C : category)
    : typecat_obj_ext_structure C ≃ ff_disp_functor_explicit (disp_codomain C).
  Proof.
    eapply weqcomp. apply typecat_obj_ext_structure_disp_ff_functor_to_codomain_weq.
    apply ff_disp_functor_weq2.
  Defined.

  Definition typecat_structure2' {C : category}
             (TC : typecat_obj_ext_structure C)
    : UU
    := ∑ (reind : ∏ Γ (A : TC Γ) Γ' (f : Γ' --> Γ), TC Γ')
         (q : ∏ Γ (A : TC Γ) Γ' (f : Γ' --> Γ), (obj_ext_typecat Γ' (reind _ A _ f)) --> obj_ext_typecat Γ A )
         (dpr_q : ∏ Γ (A : TC Γ) Γ' (f : Γ' --> Γ), 
                  (q _ A _ f) ;; (dpr_typecat_obj_ext A) = (dpr_typecat_obj_ext (reind _ A _ f)) ;; f),
       ∏ Γ (A : TC Γ) Γ' (f : Γ' --> Γ),
       isPullback _ _ _ _ (!dpr_q _ A _ f).

  Definition typecat_structure' (C : category) : UU
    := ∑ (TC : typecat_obj_ext_structure C),
         typecat_structure2' TC.

  Definition typecat_structure_typecat_structure'_weq
             (C : category)
    : typecat_structure C ≃ typecat_structure' C.
  Proof.
    eapply weqcomp. apply weqtotal2asstor.
    apply invweq.
    eapply weqcomp. apply weqtotal2asstor.
    apply (weqtotal2 (idweq _)). intros Ty.

    eapply weqcomp. apply weqtotal2asstor.
    apply invweq. eapply weqcomp. apply weqtotal2asstor.
    apply (weqtotal2 (idweq _)). intros ext.

    eapply weqcomp. unfold typecat_structure2. simpl.
    apply (@WeakEquivalences.weqtotal2comm
             _ _
             (λ reind dpr,
              ∑ (q : ∏ Γ (A : Ty Γ) Γ' (f : Γ' --> Γ), (ext Γ' (reind _ A _ f)) --> ext Γ A )
                (dpr_q : ∏ Γ (A : Ty Γ) Γ' (f : Γ' --> Γ), 
                         (q _ A _ f) ;; (dpr _ A) = (dpr _ (reind _ A _ f)) ;; f),
              _)).
    apply idweq.
  Defined.

  Definition typecat_structure2'' {C : category}
             (TC : typecat_obj_ext_structure C)
    : UU
    := ∏ Γ (A : TC Γ) Γ' (f : Γ' --> Γ),

      ∑ (reind : TC Γ')
         (q : obj_ext_typecat Γ' reind --> obj_ext_typecat Γ A )
         (dpr_q : q ;; (dpr_typecat_obj_ext A)
                  = dpr_typecat_obj_ext reind ;; f),
       isPullback _ _ _ _ (!dpr_q).

  Definition typecat_structure'' (C : category) : UU
    := ∑ (TC : typecat_obj_ext_structure C),
         typecat_structure2'' TC.

  Definition typecat_structure'_typecat_structure''_weq
             (C : category)
    : typecat_structure' C ≃ typecat_structure'' C.
  Proof.
    apply (weqtotal2 (idweq _)). intros TC.
    eapply weqcomp.

    apply (weqtotaltoforall4
             (λ Γ, TC Γ → ∏ Γ' : C, C ⟦ Γ', Γ ⟧ → TC Γ')
             (λ (Γ : C) reind, ∏ (A : TC Γ) (Γ' : C) (f : C ⟦ Γ', Γ ⟧),
              C ⟦ obj_ext_typecat Γ' (reind A Γ' f), obj_ext_typecat Γ A ⟧)
             (λ (Γ : C) reind q, ∏ (A : TC Γ) (Γ' : C) (f : C ⟦ Γ', Γ ⟧),
              (q A Γ' f;; π A)%mor = (π (reind A Γ' f);; f)%mor)
             (λ (Γ : C) reind q dpr_q, ∏ (A : TC Γ) (Γ' : C) (f : C ⟦ Γ', Γ ⟧),
              isPullback f π A π (reind A Γ' f) (q A Γ' f) (! dpr_q A Γ' f))).
    apply weqonsecfibers. intros Γ.

    eapply weqcomp.
    apply (weqtotaltoforall4
             (λ A, ∏ Γ' : C, C ⟦ Γ', Γ ⟧ → TC Γ')
             (λ A reind, ∏ (Γ' : C) (f : C ⟦ Γ', Γ ⟧),
              C ⟦ obj_ext_typecat Γ' (reind Γ' f), obj_ext_typecat Γ A ⟧)
             (λ A reind q, ∏ (Γ' : C) (f : C ⟦ Γ', Γ ⟧),
              (q Γ' f;; π A)%mor = (π (reind Γ' f);; f)%mor)
             (λ (A : TC Γ) reind q dpr_q, ∏ (Γ' : C) (f : C ⟦ Γ', Γ ⟧),
              isPullback f π A π (reind Γ' f) (q Γ' f) (! dpr_q Γ' f))).
    apply weqonsecfibers. intros A.
    
    eapply weqcomp.
    apply (weqtotaltoforall4
             (λ Γ', C ⟦ Γ', Γ ⟧ → TC Γ')
             (λ Γ' reind, ∏ (f : C ⟦ Γ', Γ ⟧),
              C ⟦ obj_ext_typecat Γ' (reind f), obj_ext_typecat Γ A ⟧)
             (λ Γ' reind q, ∏ (f : C ⟦ Γ', Γ ⟧),
              (q f;; π A)%mor = (π (reind f);; f)%mor)
             (λ Γ' reind q dpr_q, ∏ (f : C ⟦ Γ', Γ ⟧),
              isPullback f π A π (reind f) (q f) (! dpr_q f))).
    apply weqonsecfibers. intros Γ'.

    apply (weqtotaltoforall4
             (λ f, TC Γ')
             (λ f reind, C ⟦ obj_ext_typecat Γ' reind, obj_ext_typecat Γ A ⟧)
             (λ f reind q, (q ;; π A)%mor = (π reind ;; f)%mor)
             (λ f reind q dpr_q, isPullback f π A π reind q (! dpr_q))).
  Defined.

  Definition ff_comprehension_cat_structure (C : category) : UU
    := ∑ (F : ∑ (D : disp_cat C)
                (F : disp_functor (functor_identity _) D (disp_codomain C))
              , disp_functor_ff F),
       cleaving (pr1 F) × is_cartesian_disp_functor (pr1 (pr2 F)). 

  Lemma cartesian_functor_from_fibration_weq
        {C C' : category} {F : functor C C'}
        {D : disp_cat C} {D' : disp_cat C'} {FF : disp_functor F D D'}
        (cleaving_D : cleaving D)
    : (∏ (c c' : C) (f : c' --> c) (d : D c),
       is_cartesian (#FF (cleaving_D c c' f d)))
        ≃ is_cartesian_disp_functor FF.
  Proof.
    use weqimplimpl.
    - intros is_cartesian_image_of_cleaving.
      apply cartesian_functor_from_fibration.
      intros c c' f d.
      apply hinhpr.
      exists (cleaving_D c c' f d).
      apply is_cartesian_image_of_cleaving.
    - intros FF_is_cartesian.
      intros c c' f d.
      apply FF_is_cartesian.
      apply cartesian_lift_is_cartesian.
    - apply impred_isaprop. intros c.
      apply impred_isaprop. intros c'.
      apply impred_isaprop. intros f.
      apply impred_isaprop. intros d.
      apply isaprop_is_cartesian.
    - apply impred_isaprop. intros c.
      apply impred_isaprop. intros c'.
      apply impred_isaprop. intros f.
      apply impred_isaprop. intros d.
      apply impred_isaprop. intros d'.
      apply impred_isaprop. intros ff.
      apply impred_isaprop. intros ff_is_cartesian.
      apply isaprop_is_cartesian.
  Defined.

  Definition typecat_structure2''_cleaving_weq
             {C : category} (TC : typecat_obj_ext_structure C)
    : typecat_structure2'' TC
    ≃ ( cleaving (pr1 (typecat_obj_ext_structure_ff_disp_functor_to_codomain_weq _ TC))
      × is_cartesian_disp_functor (pr1 (pr2 (typecat_obj_ext_structure_ff_disp_functor_to_codomain_weq _ TC)))).
  Proof.
    (* Step 0: relax is_cartesian_disp_functor property *)
    eapply weqcomp.
    2: apply (weqtotal2 (idweq _) cartesian_functor_from_fibration_weq).
    
    (* Step 1: introduces context (while exchanging ∏ and × on the right) *)
    apply invweq. unfold cleaving.
    eapply weqcomp.
    apply (weqtotaltoforall
             (λ c, ∏ (c' : C) (f : C ⟦ c', c ⟧)
                    (d : pr1 (typecat_obj_ext_structure_ff_disp_functor_to_codomain_weq C TC) c),
              cartesian_lift d f)
             (λ c x, ∏ (c' : C) (f : C ⟦ c', c ⟧)
                     (d : pr1 (typecat_obj_ext_structure_ff_disp_functor_to_codomain_weq C TC) c),
              is_cartesian
                (# (pr1 (pr2 (typecat_obj_ext_structure_ff_disp_functor_to_codomain_weq C TC)))
                   (x c' f d)))).
    apply weqonsecfibers. intros Γ.
    eapply weqcomp.
    apply (weqtotaltoforall
             (λ c', ∏ (f : C ⟦ c', Γ ⟧)
                    (d : pr1 (typecat_obj_ext_structure_ff_disp_functor_to_codomain_weq C TC) Γ),
              cartesian_lift d f)
             (λ c' x, ∏ (f : C ⟦ c', Γ ⟧)
                     (d : pr1 (typecat_obj_ext_structure_ff_disp_functor_to_codomain_weq C TC) Γ),
              is_cartesian
                (# (pr1 (pr2 (typecat_obj_ext_structure_ff_disp_functor_to_codomain_weq C TC)))
                   (x f d)))).
    eapply weqcomp. 2: apply weqforall_comm.
    apply weqonsecfibers. intros Γ'.
    eapply weqcomp.
    apply (weqtotaltoforall
             (λ (f : C ⟦ Γ', Γ ⟧), ∏ (d : pr1 (typecat_obj_ext_structure_ff_disp_functor_to_codomain_weq C TC) Γ),
              cartesian_lift d f)
             (λ (f : C ⟦ Γ', Γ ⟧) x,
              ∏ (d : pr1 (typecat_obj_ext_structure_ff_disp_functor_to_codomain_weq C TC) Γ),
              is_cartesian
                (# (pr1 (pr2 (typecat_obj_ext_structure_ff_disp_functor_to_codomain_weq C TC)))
                   (x d)))).
    eapply weqcomp. 2: apply weqforall_comm.
    apply weqonsecfibers. intros f.
    eapply weqcomp.
    apply (weqtotaltoforall
             (λ (d : pr1 (typecat_obj_ext_structure_ff_disp_functor_to_codomain_weq C TC) Γ),
              cartesian_lift d f)
             (λ (d : pr1 (typecat_obj_ext_structure_ff_disp_functor_to_codomain_weq C TC) Γ) x,
              is_cartesian
                (# (pr1 (pr2 (typecat_obj_ext_structure_ff_disp_functor_to_codomain_weq C TC)))
                   x))).
    apply weqonsecfibers. intros A.

    (* Step 2: object part of cartesian lift is trivial *)
    apply invweq.
    eapply weqcomp. 2: apply weqtotal2asstol.
    apply (weqtotal2 (idweq _)). intros A'.

    (* Step 3: morphism part of cartesian lift
     * is available through equivalence of morphisms *)
    eapply weqcomp. 2: apply weqtotal2asstol.
    eapply weqcomp.
    apply (weqtotal2asstol
             (λ q, (q ;; π A)%mor = (π A' ;; f)%mor)
             (λ qq, isPullback _ _ _ _ (! pr2 qq))
          ).
    set (FF := typecat_obj_ext_structure_ff_disp_functor_to_codomain_weq _ TC).
    use (weqtotal2 (idweq _)).
    intros qq.

    (* Step 4: equivalence of pullback and cleaving *)
    apply weqimplimpl.
    3: apply isaprop_isPullback.
    3: {
      use isofhleveltotal2.
      - apply isaprop_is_cartesian.
      - intros ?. apply isaprop_is_cartesian.
    }

    - intros pb.
      use tpair.
      + intros Δ g B ggff.
        eapply iscontrweqf.
        2: {
          use pb.
          - exact (obj_ext_typecat Δ B).
          - exact (dpr_typecat_obj_ext B ;; g).
          - exact (pr1 ggff).
          - etrans. apply assoc'.
            apply pathsinv0, (pr2 ggff).
        }

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
              ** exact (maponpaths pr1 (pr2 H)).

      + intros Δ g k hh.
        use iscontrweqf.
        3: {
          use pb.
          - exact (pr1 k).
          - exact (pr2 k ;; g).
          - exact (pr1 hh).
          - etrans. apply assoc'.
            apply pathsinv0, (pr2 hh).
        }
          
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
              ** exact (maponpaths pr1 (pr2 H)).

    - intros Hcart.
      intros Δ g k H.
      eapply iscontrweqf.
      2: {
        use (pr2 Hcart).
        - exact Γ'.
        - exact (identity _).
        - exact (Δ,,g).
        - exists k. etrans. apply pathsinv0, H.
          apply maponpaths.
          apply pathsinv0, id_left.
      }

      apply invweq.
      eapply weqcomp.
      2: apply weqtotal2asstol.
      apply weq_subtypes_iff.
      + intro. apply isapropdirprod; apply homset_property.
      + intro. apply (isofhleveltotal2 1). 
        * apply homset_property.
        * intros. apply homsets_disp.
    + intros gg; split; intros H'.
      * use tpair.
        -- etrans. apply (pr1 H').
          apply pathsinv0, id_right.
        -- apply subtypePath.
          intro; apply homset_property.
          exact (pr2 H').
      * split.
        -- etrans. apply (pr1 H'). apply id_right.
        -- etrans.
           apply (maponpaths pr1 (pr2 H')).
           apply idpath.
  Defined.
  
  Definition typecat_structure''_ff_comprehension_cat_structure_weq
             (C : category)
    : typecat_structure'' C ≃ ff_comprehension_cat_structure C.
  Proof.
    use weqtotal2.
    - apply typecat_obj_ext_structure_ff_disp_functor_to_codomain_weq.
    - intros TC.
      apply typecat_structure2''_cleaving_weq.
  Defined.

  Definition typecat_ff_comprehension_cat_structure_weq (C : category)
    : typecat_structure C ≃ ff_comprehension_cat_structure C.
  Proof.
    eapply weqcomp. apply typecat_structure_typecat_structure'_weq.
    eapply weqcomp. apply typecat_structure'_typecat_structure''_weq.
    apply typecat_structure''_ff_comprehension_cat_structure_weq.
  Defined.

  Definition ff_comprehension_cat : UU
    := ∑ (C : category), ff_comprehension_cat_structure C.

  Definition typecat_ff_comprehension_cat_weq
    : typecat ≃ ff_comprehension_cat.
  Proof.
    use weqtotal2. apply idweq. intros C.
    apply typecat_ff_comprehension_cat_structure_weq.
  Defined.

End TypeCat_ComprehensionCat.

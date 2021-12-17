(*
  [TypeTheory.ALV2.FullyFaithfulDispFunctor]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**

Fully faithful displayed functors over identity functor on C
with fixed target displayed categories are completely determined
my their action on objects.

Specifically we have an equivalence [ff_disp_functor_weq] between
[ff_disp_functor] (an alias for [ff_disp_functor_on_objects])
and [ff_disp_functor_explicit] (which is a combination of
a source displayed category over C and a fully faithful functor
over identity functor on C from said category into D').

Main definitions:

- [ff_disp_functor] (same as [ff_disp_functor_on_objects]) —
  definition of fully faithful functor without (contractible) morphisms;
- [ff_disp_functor_explicit] — combination of a source displayed category
  over C and a fully faithful displayed functor (over identity functor on C)
  into D';
- [ff_disp_functor_weq] — equivalence of the two definitions;

Accessors for [ff_disp_functor]:

- [source_disp_cat_from_ff_disp_functor] — source displayed category;
- [disp_functor_from_ff_disp_functor] — displayed functor (also acts as coercion);
- [disp_functor_from_ff_disp_functor_is_ff] — proof that extracted functor is fully faithful;

*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.

Section FullyFaithfulDispFunctor.

  (* Fully faithful displayed functor (over identity functor on C) into D'
   * is completely determined by its action on objects:
   *
   * - type family of displayed objects (for the source displayed category) over objects in C
   * - mapping of said displayed objects to displayed objects in D' over C.
   * *)
  Definition ff_disp_functor_on_objects {C : category}
             (D' : disp_cat C)
    : UU
    := ∑ (ob_disp : C → UU)
       (* Fob *), ∏ (Γ : C), ob_disp Γ → D' Γ.

  Section FullyFaithfulFunctorOnMorphisms.

    Context {C : category} {D' : disp_cat C}.
    Context (D : ff_disp_functor_on_objects D').

    Definition ff_disp_functor_on_morphisms_sop : UU
      := ∑ (mord : ∏ Γ Γ', (pr1 D Γ) → (pr1 D Γ') → (Γ --> Γ') → UU)
           (functor_mord : ∏ Γ Γ' (A : pr1 D Γ) (A' : pr1 D Γ') (f : Γ --> Γ')
                           , (mord _ _ A A' f) -> (pr2 D _ A -->[ f ] pr2 D _ A'))
         , ∏ Γ Γ' (A : pr1 D Γ) (A' : pr1 D Γ') (f : Γ --> Γ')
         , isweq (functor_mord Γ Γ' A A' f).

    Definition ff_disp_functor_on_morphisms_pos : UU
      := ∏ Γ Γ' (A : pr1 D Γ) (A' : pr1 D Γ') (f : Γ --> Γ'),
         ∑ (mord : UU), mord ≃ (pr2 D _ A -->[ f ] pr2 D _ A').

    Definition ff_disp_functor_on_morphisms_sop_pos_weq
      : ff_disp_functor_on_morphisms_sop ≃ ff_disp_functor_on_morphisms_pos.
    Proof.
      eapply weqcomp.
      apply (weqtotaltoforall3
               (λ Γ, ∏ Γ', (pr1 D Γ) → (pr1 D Γ') → (Γ --> Γ') → UU)
               (λ Γ mord, ∏ Γ' (A : pr1 D Γ) (A' : pr1 D Γ') (f : Γ --> Γ')
                , (mord _ A A' f) -> (pr2 D _ A -->[ f ] pr2 D _ A'))
               (λ Γ mord functor_mord, 
                ∏ Γ' (A : pr1 D Γ) (A' : pr1 D Γ') (f : Γ --> Γ')
                , isweq (functor_mord Γ' A A' f))).
      apply weqonsecfibers. intros Γ.

      eapply weqcomp.
      apply (weqtotaltoforall3
               (λ Γ', (pr1 D Γ) → (pr1 D Γ') → (Γ --> Γ') → UU)
               (λ Γ' mord, ∏ (A : pr1 D Γ) (A' : pr1 D Γ') (f : Γ --> Γ')
                , (mord A A' f) -> (pr2 D _ A -->[ f ] pr2 D _ A'))
               (λ Γ' mord functor_mord, 
                ∏ (A : pr1 D Γ) (A' : pr1 D Γ') (f : Γ --> Γ')
                , isweq (functor_mord A A' f))).
      apply weqonsecfibers. intros Γ'.

      eapply weqcomp.
      apply (weqtotaltoforall3
               (λ A, (pr1 D Γ') → (Γ --> Γ') → UU)
               (λ A mord, ∏ (A' : pr1 D Γ') (f : Γ --> Γ')
                , (mord A' f) -> (pr2 D _ A -->[ f ] pr2 D _ A'))
               (λ A mord functor_mord, 
                ∏ (A' : pr1 D Γ') (f : Γ --> Γ')
                , isweq (functor_mord A' f))).
      apply weqonsecfibers. intros A.

      eapply weqcomp.
      apply (weqtotaltoforall3
               (λ A', (Γ --> Γ') → UU)
               (λ A' mord, ∏ (f : Γ --> Γ')
                , (mord f) -> (pr2 D _ A -->[ f ] pr2 D _ A'))
               (λ A' mord functor_mord, 
                ∏ (f : Γ --> Γ')
                , isweq (functor_mord f))).
      apply weqonsecfibers. intros A'.

      eapply weqcomp.
      apply (weqtotaltoforall3
               (λ f, UU)
               (λ f mord, mord -> (pr2 D _ A -->[ f ] pr2 D _ A'))
               (λ f mord functor_mord, isweq functor_mord)).
      apply idweq.
    Defined.

    Definition ff_disp_functor_on_morphisms_pos_iscontr
      : iscontr ff_disp_functor_on_morphisms_pos.
    Proof.
      apply impred_iscontr. intros Γ.
      apply impred_iscontr. intros Γ'.
      apply impred_iscontr. intros A.
      apply impred_iscontr. intros A'.
      apply impred_iscontr. intros f.
      use (@iscontrweqf (∑ mord : UU, mord = pr2 D Γ A -->[f] pr2 D Γ' A')).
      - use (weqtotal2 (idweq _)). intros mord. apply univalenceweq.
      - apply iscontrcoconustot.
    Defined.

    Definition ff_disp_functor_on_morphisms_pos_isaprop
      : isaprop ff_disp_functor_on_morphisms_pos.
    Proof.
      apply isapropifcontr, ff_disp_functor_on_morphisms_pos_iscontr.
    Defined.

    Definition ff_disp_functor_on_morphisms_id_pos
               (mor_weq : ff_disp_functor_on_morphisms_pos)
      : UU
      := ∏ (Γ : C) (A : pr1 D Γ),
         ∑ (mor_id : pr1 (mor_weq Γ Γ A A (identity Γ))),
         pr1 (pr2 (mor_weq Γ Γ A A (identity Γ))) mor_id
         = transportb (mor_disp (pr2 D Γ A) (pr2 D Γ A))
                      (functor_id (functor_identity C) Γ) (id_disp (pr2 D Γ A)).

    Definition ff_disp_functor_on_morphisms_id_pos_iscontr
               (mor_weq : ff_disp_functor_on_morphisms_pos)
               (mor_isaset : ∏ Γ Γ' f (A : pr1 D Γ) (A' : pr1 D Γ'), isaset (pr1 (mor_weq _ _ A A' f)))
      : iscontr (ff_disp_functor_on_morphisms_id_pos mor_weq).
    Proof.
      apply impred_iscontr. intros Γ.
      apply impred_iscontr. intros A.
      set (mord := pr1 (mor_weq Γ Γ A A (identity Γ))).
      set (mord_weq := pr2 (mor_weq Γ Γ A A (identity Γ))).
      use (@iscontrweqf (∑ mor_id : mord, mor_id = invweq mord_weq
                                                          (transportb (mor_disp (pr2 D Γ A) (pr2 D Γ A))
                                                                      (functor_id (functor_identity C) Γ) (id_disp (pr2 D Γ A))))).
      - use (weqtotal2 (idweq _)). intros mor_id. simpl.
        use weq_iso.
        + intros p. apply (maponpaths mord_weq p @ homotweqinvweq mord_weq _).
        + intros p. apply (! homotinvweqweq mord_weq _ @ maponpaths (invmap mord_weq) p).
        + intros p. apply mor_isaset.
        + intros p. apply (@homsets_disp _ D').
      - apply iscontrcoconustot.
    Defined.

    Definition ff_disp_functor_on_morphisms_comp_pos
               (mor_weq : ff_disp_functor_on_morphisms_pos)
      : UU
      := ∏ (Γ Γ' Γ'' : C)
           (A : pr1 D Γ) (A' : pr1 D Γ') (A'' : pr1 D Γ'')
           (f : Γ --> Γ') (g : Γ' --> Γ'')
           (ff : pr1 (mor_weq Γ Γ' A A' f))
           (gg : pr1 (mor_weq Γ' Γ'' A' A'' g)),
         ∑ (mor_comp : pr1 (mor_weq Γ Γ'' A A'' (f ;; g))),
         pr2 (mor_weq Γ Γ'' A A'' (f ;; g)) mor_comp
         = transportb _ (functor_comp (functor_identity C) f g)
                      (comp_disp (pr2 (mor_weq _ _ _ _ _) ff) (pr2 (mor_weq _ _ _ _ _) gg)).

    Definition ff_disp_functor_on_morphisms_comp_pos_iscontr
               (mor_weq : ff_disp_functor_on_morphisms_pos)
               (mor_isaset : ∏ Γ Γ' f (A : pr1 D Γ) (A' : pr1 D Γ'), isaset (pr1 (mor_weq _ _ A A' f)))
      : iscontr (ff_disp_functor_on_morphisms_comp_pos mor_weq).
    Proof.
      apply impred_iscontr. intros Γ.
      apply impred_iscontr. intros Γ'.
      apply impred_iscontr. intros Γ''.
      apply impred_iscontr. intros A.
      apply impred_iscontr. intros A'.
      apply impred_iscontr. intros A''.
      apply impred_iscontr. intros f.
      apply impred_iscontr. intros g.
      apply impred_iscontr. intros ff.
      apply impred_iscontr. intros gg.
      set (mord := pr1 (mor_weq Γ Γ'' A A'' (f ;; g))).
      set (mord_weq := pr2 (mor_weq Γ Γ'' A A'' (f ;; g))).
      use (@iscontrweqf (∑ mor_comp : mord,
                                      mor_comp
                                      = invweq mord_weq (transportb _ (functor_comp (functor_identity C) f g)
                                                                    (comp_disp (pr2 (mor_weq _ _ _ _ _) ff) (pr2 (mor_weq _ _ _ _ _) gg))))).
      - use (weqtotal2 (idweq _)). intros mor_id. simpl.
        use weq_iso.
        + intros p. apply (maponpaths mord_weq p @ homotweqinvweq mord_weq _).
        + intros p. apply (! homotinvweqweq mord_weq _ @ maponpaths (invmap mord_weq) p).
        + intros p. apply mor_isaset.
        + intros p. apply (@homsets_disp _ D').
      - apply iscontrcoconustot.
    Defined.

    Definition ff_disp_functor_source_mor_isaset
               (mor_weq : ff_disp_functor_on_morphisms_pos)
      : ∏ Γ Γ' f (A : pr1 D Γ) (A' : pr1 D Γ'), isaset (pr1 (mor_weq _ _ A A' f)).
    Proof.
      intros Γ Γ' f A A'.
      set (w := pr2 (mor_weq Γ Γ' A A' f)).
      use (isofhlevelweqf 2 (invweq w)).
      apply (@homsets_disp _ D').
    Defined.

    Definition ff_disp_functor_source_mor_isaset_iscontr
               (mor_weq : ff_disp_functor_on_morphisms_pos)
      : iscontr (∏ Γ Γ' f (A : pr1 D Γ) (A' : pr1 D Γ'), isaset (pr1 (mor_weq _ _ A A' f))).
    Proof.
      apply iscontraprop1.
      - apply impred_isaprop. intros Γ.
        apply impred_isaprop. intros Γ'.
        apply impred_isaprop. intros A.
        apply impred_isaprop. intros A'.
        apply impred_isaprop. intros f.
        apply isapropisaset.
      - apply ff_disp_functor_source_mor_isaset.
    Defined.

    Definition ff_disp_functor_on_morphisms_idcomp_pos : UU
      := ∑ (mor_weq : ff_disp_functor_on_morphisms_pos)
           (mor_isaset : ∏ Γ Γ' f (A : pr1 D Γ) (A' : pr1 D Γ'), isaset (pr1 (mor_weq _ _ A A' f)))
           (mor_id : ff_disp_functor_on_morphisms_id_pos mor_weq)
         , ff_disp_functor_on_morphisms_comp_pos mor_weq.

    Definition ff_disp_functor_on_morphisms_idcomp_pos_iscontr
      : iscontr ff_disp_functor_on_morphisms_idcomp_pos.
    Proof.
      apply iscontr_total2.
      - apply ff_disp_functor_on_morphisms_pos_iscontr.
      - intros mor_weq. apply iscontr_total2.
        + apply ff_disp_functor_source_mor_isaset_iscontr.
        + intros mor_isaset.
          apply iscontr_total2.
          * apply ff_disp_functor_on_morphisms_id_pos_iscontr.
            apply mor_isaset.
          * intros ?.
            apply ff_disp_functor_on_morphisms_comp_pos_iscontr.
            apply mor_isaset.
    Defined.

    Definition ff_disp_functor_on_morphisms_idcomp_sop
      := ∑ (mor_disp : ∏ {x y : C}, pr1 D x -> pr1 D y -> (x --> y) -> UU)
           (id_disp' : ∏ {x : C} (xx : pr1 D x), mor_disp xx xx (identity x))
           (comp_disp' : ∏ {x y z : C} {f : x --> y} {g : y --> z}
                           {xx : pr1 D x} {yy : pr1 D y} {zz : pr1 D z},
                         mor_disp xx yy f -> mor_disp yy zz g -> mor_disp xx zz (f ;; g))
           (homsets_disp : ∏ {x y} {f : x --> y} {xx} {yy}, isaset (mor_disp xx yy f))
           (Fmor : ∏ x y (xx : pr1 D x) (yy : pr1 D y) (f : x --> y),
                   (mor_disp xx yy f) -> (pr2 D _ xx -->[ f ] pr2 D _ yy))
           (Fid : ∏ x (xx : pr1 D x),
                  Fmor _ _ _ _ _ (id_disp' xx) = transportb _ (functor_id (functor_identity C) x) (id_disp (pr2 D _ xx)))
           (Fcomp :  ∏ x y z (xx : pr1 D x) yy zz (f : x --> y) (g : y --> z)
                       (ff : mor_disp xx yy f) (gg : mor_disp yy zz g),
                     Fmor _ _ _ _ _ (comp_disp' ff gg)
                     = transportb _ (functor_comp (functor_identity _) f g) (comp_disp (Fmor _ _ _ _ _ ff) (Fmor _ _ _ _ _ gg)))
         , ∏ x y (xx : pr1 D x) (yy : pr1 D y) (f : x --> y),
         isweq (fun ff : mor_disp xx yy f => Fmor _ _ _ _ _ ff).

    Definition ff_disp_functor_on_morphisms_idcomp_sop_pos_weq
      : ff_disp_functor_on_morphisms_idcomp_sop ≃ ff_disp_functor_on_morphisms_idcomp_pos.
    Proof.
      use weq_iso.

      - intros sop.
        set (mor_disp := pr1 sop).
        set (id_disp' := pr1 (pr2 sop)).
        set (comp_disp' := pr1 (pr2 (pr2 sop))).
        set (homsets_disp' := pr1 (pr2 (pr2 (pr2 sop)))).
        set (Fmor := pr1 (pr2 (pr2 (pr2 (pr2 sop))))).
        set (Fid := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 sop)))))).
        set (Fcomp := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 sop))))))).
        set (Fff := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 sop))))))).

        exists (λ x y xx yy f, mor_disp x y xx yy f ,, Fmor x y xx yy f,, Fff x y xx yy f).
        exists homsets_disp'.
        exists (λ x xx, (id_disp' x xx ,, Fid x xx)).
        exact (λ x y z xx yy zz f g ff gg, (comp_disp' x y z f g xx yy zz ff gg ,, Fcomp x y z xx yy zz f g ff gg)).

      - intros pos.
        set (mor_disp := λ x y xx yy f, pr1 (pr1 pos x y xx yy f)).
        set (Fmor := λ x y xx yy f, pr1 (pr2 (pr1 pos x y xx yy f))).
        set (Fff := λ x y xx yy f, pr2 (pr2 (pr1 pos x y xx yy f))).
        set (homsets_disp' := pr1 (pr2 pos)).
        set (id_disp' := λ x xx, pr1 (pr1 (pr2 (pr2 pos)) x xx)).
        set (Fid := λ x xx, pr2 (pr1 (pr2 (pr2 pos)) x xx)).
        set (comp_disp' := λ x y z f g xx yy zz ff gg, pr1 (pr2 (pr2 (pr2 pos)) x y z xx yy zz f g ff gg)).
        set (Fcomp := λ x y z xx yy zz f g ff gg, pr2 (pr2 (pr2 (pr2 pos)) x y z xx yy zz f g ff gg)).

        exists mor_disp.
        exists id_disp'.
        exists comp_disp'.
        exists homsets_disp'.
        exists Fmor.
        exists Fid.
        exists Fcomp.
        exact Fff.
      - intros ?. apply idpath.
      - intros ?. apply idpath.
    Defined.

    Definition source_disp_cat_data_of_ff_disp_functor_on_morphisms_idcomp_sop
      : ff_disp_functor_on_morphisms_idcomp_sop → disp_cat_data C.
    Proof.
      intros sop.
      set (mor_disp := pr1 sop).
      set (id_disp' := pr1 (pr2 sop)).
      set (comp_disp' := pr1 (pr2 (pr2 sop))).

      use tpair.
      - exists (pr1 D). apply mor_disp.
      - exact (id_disp' , comp_disp').
    Defined.

    Definition ff_disp_functor_mor_sop : UU
      := ∑ (mor_idcomp : ff_disp_functor_on_morphisms_idcomp_sop),
         disp_cat_axioms _ (source_disp_cat_data_of_ff_disp_functor_on_morphisms_idcomp_sop
                              mor_idcomp).
    
    Definition ff_disp_functor_mor_sop_iscontr
      : iscontr ff_disp_functor_mor_sop.
    Proof.
      apply iscontr_total2.
      - apply (iscontrweqb ff_disp_functor_on_morphisms_idcomp_sop_pos_weq).
        apply ff_disp_functor_on_morphisms_idcomp_pos_iscontr.
      - intros sop.
        apply iscontr_total2.

        + apply impred_iscontr. intros Γ.
          apply impred_iscontr. intros Γ'.
          apply impred_iscontr. intros f.
          apply impred_iscontr. intros A.
          apply impred_iscontr. intros A'.
          apply impred_iscontr. intros ff.
          apply iscontraprop1. apply (pr1 (pr2 (pr2 (pr2 sop)))).
          set (id_disp' := pr1 (pr2 sop)).
          set (comp_disp' := pr1 (pr2 (pr2 sop))).
          set (Fmor := pr1 (pr2 (pr2 (pr2 (pr2 sop))))).
          set (Fid := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 sop)))))).
          set (Fcomp := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 sop))))))).
          set (Fff := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 sop))))))).
          set (w := λ g, (Fmor _ _ A A' g,, Fff _ _ _ _ _)).
          etrans. apply pathsinv0. apply (homotinvweqweq (w _)).
          etrans. apply maponpaths. apply Fcomp.
          etrans. apply maponpaths, maponpaths, maponpaths_2. apply Fid.
          etrans. apply maponpaths, maponpaths. apply id_left_disp.
          etrans. apply maponpaths. apply transport_b_b. simpl.
          apply homot_invweq_transportb_weq.
          
        + intros ?.
          apply iscontr_total2.

          * apply impred_iscontr. intros Γ.
            apply impred_iscontr. intros Γ'.
            apply impred_iscontr. intros f.
            apply impred_iscontr. intros A.
            apply impred_iscontr. intros A'.
            apply impred_iscontr. intros ff.
            apply iscontraprop1. apply (pr1 (pr2 (pr2 (pr2 sop)))).
            set (id_disp' := pr1 (pr2 sop)).
            set (comp_disp' := pr1 (pr2 (pr2 sop))).
            set (Fmor := pr1 (pr2 (pr2 (pr2 (pr2 sop))))).
            set (Fid := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 sop)))))).
            set (Fcomp := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 sop))))))).
            set (Fff := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 sop))))))).
            set (w := λ g, (Fmor _ _ A A' g,, Fff _ _ _ _ _)).
            etrans. apply pathsinv0. apply (homotinvweqweq (w _)).
            etrans. apply maponpaths. apply Fcomp.
            etrans. apply maponpaths, maponpaths, maponpaths. apply Fid.
            etrans. apply maponpaths, maponpaths. apply id_right_disp.
            etrans. apply maponpaths. apply transport_b_b. simpl.
            apply homot_invweq_transportb_weq.

          * intros ?. apply iscontr_total2.

            -- apply impred_iscontr. intros Γ.
               apply impred_iscontr. intros Γ'.
               apply impred_iscontr. intros Γ''.
               apply impred_iscontr. intros Γ'''.
               apply impred_iscontr. intros f.
               apply impred_iscontr. intros g.
               apply impred_iscontr. intros h.
               apply impred_iscontr. intros A.
               apply impred_iscontr. intros A'.
               apply impred_iscontr. intros A''.
               apply impred_iscontr. intros A'''.
               apply impred_iscontr. intros ff.
               apply impred_iscontr. intros gg.
               apply impred_iscontr. intros hh.
               apply iscontraprop1. apply (pr1 (pr2 (pr2 (pr2 sop)))).
               set (id_disp' := pr1 (pr2 sop)).
               set (comp_disp' := pr1 (pr2 (pr2 sop))).
               set (Fmor := pr1 (pr2 (pr2 (pr2 (pr2 sop))))).
               set (Fid := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 sop)))))).
               set (Fcomp := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 sop))))))).
               set (Fff := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 sop))))))).
               set (w := λ g, (Fmor _ _ A A''' g,, Fff _ _ _ _ _)).
               etrans. apply pathsinv0. apply (homotinvweqweq (w (f ;; (g ;; h)))).
               etrans. apply maponpaths. apply Fcomp.
               etrans. apply maponpaths, maponpaths, maponpaths. apply Fcomp.
               etrans. apply maponpaths, maponpaths. apply assoc_disp.
               etrans. apply maponpaths. apply transport_b_b.
               (* WORK IN PROGRESS *)
               etrans. apply maponpaths, maponpaths, maponpaths_2, pathsinv0, Fcomp.
               etrans. apply maponpaths, maponpaths, pathsinv0, Fcomp.
               apply homot_invweq_transportb_weq.
            -- intros ?.
               set (homsets_disp' := pr1 (pr2 (pr2 (pr2 sop)))).
               apply iscontraprop1.
               ++ apply impred_isaprop. intros Γ.
                  apply impred_isaprop. intros Γ'.
                  apply impred_isaprop. intros f.
                  apply impred_isaprop. intros A.
                  apply impred_isaprop. intros A'.
                  apply isapropisaset.
               ++ apply homsets_disp'.
    Qed.

  End FullyFaithfulFunctorOnMorphisms.

  Section FullyFaithfulFunctorWithMorphisms.

    (* Fully faithful displayed functor (over identity functor on C) into D'
     * (equipped with contractible action on morphisms). *)
    Definition ff_disp_functor_with_morphisms
               {C : category} (D' : disp_cat C)
    : UU
      := ∑ (D : ff_disp_functor_on_objects D'), ff_disp_functor_mor_sop D.

    (* Source displayed category over C
     * extracted from a fully faithful displayed functor (over identity functor on C) *)
    Definition source_disp_cat_from_ff_disp_functor_with_morphisms
               {C : category} {D' : disp_cat C}
               (Fsop : ff_disp_functor_with_morphisms D')
      : disp_cat C.
    Proof.
      set (sop := pr1 (pr2 Fsop)).

      set (ob_disp := pr1 (pr1 Fsop)).
      set (axioms_d := pr2 (pr2 Fsop)).

      set (mor_disp := pr1 sop).
      set (id_disp' := pr1 (pr2 sop)).
      set (comp_disp' := pr1 (pr2 (pr2 sop))).

      exact (((ob_disp ,, mor_disp) ,, (id_disp' , comp_disp')) ,, axioms_d).
    Defined.

    Definition disp_functor_from_ff_disp_functor_with_morphisms
               {C : category} {D' : disp_cat C}
               (Fsop : ff_disp_functor_with_morphisms D')
      : disp_functor (functor_identity C) (source_disp_cat_from_ff_disp_functor_with_morphisms Fsop) D'.
    Proof.
      set (sop := pr1 (pr2 Fsop)).

      set (Fob := pr2 (pr1 Fsop)).
      set (Fmor := pr1 (pr2 (pr2 (pr2 (pr2 sop))))).
      set (Fid := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 sop)))))).
      set (Fcomp := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 sop))))))).

      exact ((Fob,,Fmor),,(Fid,Fcomp)).
    Defined.

    Coercion disp_functor_from_ff_disp_functor_with_morphisms
      : ff_disp_functor_with_morphisms >-> disp_functor.

    Definition disp_functor_from_ff_disp_functor_with_morphisms_is_ff
               {C : category} {D' : disp_cat C}
               (Fsop : ff_disp_functor_with_morphisms D')
      : disp_functor_ff (disp_functor_from_ff_disp_functor_with_morphisms Fsop).
    Proof.
      set (sop := pr1 (pr2 Fsop)).
      set (Fff := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 sop))))))).
      exact Fff.
    Defined.

    Definition ff_disp_functor_with_morphisms_eq
               {C : category} (D' : disp_cat C)
               (X Y : ff_disp_functor_with_morphisms D')
               (e : pr1 X = pr1 Y)
      : X = Y.
    Proof.
      use total2_paths_f.
      - apply e.
      - apply isapropifcontr.
        apply ff_disp_functor_mor_sop_iscontr.
    Defined.

    Definition ff_disp_functor_explicit
               {C : category} (D' : disp_cat C)
      : UU
      := ∑ (D : disp_cat C) (F : disp_functor (functor_identity _) D D'), disp_functor_ff F.

    Definition disp_functor_from_ff_disp_functor_explicit
               {C : category} (D' : disp_cat C)
               (F : ff_disp_functor_explicit D')
      : disp_functor _ _ D' := pr1 (pr2 F).

    Coercion disp_functor_from_ff_disp_functor_explicit
      : ff_disp_functor_explicit >-> disp_functor.
    
    Definition ff_disp_functor_with_morphisms_weq
               {C : category} {D' : disp_cat C}
      : ff_disp_functor_with_morphisms D' ≃ ff_disp_functor_explicit D'.
    Proof.
      use weq_iso.

      - intros Fsop.
        exists (source_disp_cat_from_ff_disp_functor_with_morphisms Fsop).
        exists (disp_functor_from_ff_disp_functor_with_morphisms Fsop).
        apply disp_functor_from_ff_disp_functor_with_morphisms_is_ff.

      - intros F.
        
        set (ob_disp := pr1 (pr1 (pr1 (pr1 F)))).
        set (mor_disp := pr2 (pr1 (pr1 (pr1 F)))).
        set (id_disp' := pr1 (pr2 (pr1 (pr1 F)))).
        set (comp_disp' := pr2 (pr2 (pr1 (pr1 F)))).
        set (axioms_d := pr2 (pr1 F)).
        set (homsets_disp' := pr2 (pr2 (pr2 axioms_d))).

        set (Fob := pr1 (pr1 (pr1 (pr2 F)))).
        set (Fmor := pr2 (pr1 (pr1 (pr2 F)))).
        set (Fid := pr1 (pr2 (pr1 (pr2 F)))).
        set (Fcomp := pr2 (pr2 (pr1 (pr2 F)))).
        set (Fff := pr2 (pr2 F)).

        exists (ob_disp ,, Fob).
        exists (mor_disp ,, id_disp' ,, comp_disp' ,, homsets_disp' ,, Fmor ,, Fid ,, Fcomp ,, Fff).
        exact axioms_d.

      - intros ?. apply ff_disp_functor_with_morphisms_eq. apply idpath.
      - intros ?. apply idpath.
    Defined.

    Definition ff_disp_functor_on_objects_ff_disp_functor_with_morphisms_weq
               {C : category} {D' : disp_cat C}
      : ff_disp_functor_on_objects D' ≃ ff_disp_functor_with_morphisms D'.
    Proof.
      apply invweq, weqpr1.
      intros D.
      apply ff_disp_functor_mor_sop_iscontr.
    Defined.

  End FullyFaithfulFunctorWithMorphisms.

  (* Fully faithful displayed functor (over identity functor on C) into D'. *)
  Definition ff_disp_functor
             {C : category} (D' : disp_cat C)
    : UU
    := ff_disp_functor_on_objects D'.

  Definition ff_disp_functor_weq
             {C : category} {D' : disp_cat C}
    : ff_disp_functor D' ≃ ff_disp_functor_explicit D'.
  Proof.
    eapply weqcomp. apply ff_disp_functor_on_objects_ff_disp_functor_with_morphisms_weq.
    apply ff_disp_functor_with_morphisms_weq.
  Defined.

  Definition source_disp_cat_from_ff_disp_functor
             {C : category} {D' : disp_cat C}
             (F : ff_disp_functor D')
    : disp_cat C
    := pr1 (ff_disp_functor_weq F).

  Definition disp_functor_from_ff_disp_functor
             {C : category} {D' : disp_cat C}
             (F : ff_disp_functor D')
    : disp_functor (functor_identity C) (source_disp_cat_from_ff_disp_functor F) D'
    := pr1 (pr2 (ff_disp_functor_weq F)).

  Coercion disp_functor_from_ff_disp_functor : ff_disp_functor >-> disp_functor.

  Definition disp_functor_from_ff_disp_functor_is_ff
             {C : category} {D' : disp_cat C}
             (F : ff_disp_functor D')
    : disp_functor_ff F
    := pr2 (pr2 (ff_disp_functor_weq F)).

  (* “Isomorphism” of displayed cats over a base. TODO: perhaps move this section upstream? *)
  Section DispCatIso.
      
    Definition is_disp_catiso
               {C : category} {D D' : disp_cat C}
               (F : disp_functor (functor_identity C) D D')
      := disp_functor_ff F × (∏ c, isweq (F c)).

    Definition disp_catiso
               {C : category} (D D' : disp_cat C)
      := ∑ (F : disp_functor _ D D'), is_disp_catiso F.

    Definition disp_functor_from_disp_catiso
               {C : category} (D D' : disp_cat C)
               (F : disp_catiso D D')
      : disp_functor _ D D' := pr1 F.

    Coercion disp_functor_from_disp_catiso : disp_catiso >-> disp_functor.

    Definition disp_cat_path_precat
               {C : category}
               (D D' : disp_cat C)
      : D = D' ≃ disp_cat_data_from_disp_cat D = D'.
    Proof.
      apply path_sigma_hprop, isaprop_disp_cat_axioms.
    Defined.

    Definition data_disp_cat_eq_1
               {C : category}
               (D D' : disp_cat_data C)
               (Fo : ob_disp D = ob_disp D')
      : UU
      := transportf (λ z, ∏ (c c' : C), z c → z c' → (c --> c') → UU) Fo (pr2 (pr1 D)) = pr2 (pr1 D').

    Definition disp_cat_eq_1
               {C : category}
               (D D' : disp_cat_data C)
      : UU
      := ∑ (F : ∑ (Fo : ob_disp D = ob_disp D'), data_disp_cat_eq_1 D D' Fo),
         (pr1 (transportf (λ x, disp_cat_id_comp C x)
                          (total2_paths_f (pr1 F) (pr2 F))
                          (pr2 D))
          = pr1 (pr2 D'))
           ×
           pr2 (transportf (λ x, disp_cat_id_comp C x)
                           (total2_paths_f (pr1 F) (pr2 F))
                           (pr2 D))
         =
         pr2(pr2 D').

    Definition disp_cat_path_to_disp_cat_eq_1
               {C : category}
               (D D' : disp_cat_data C)
      : D = D' ≃ disp_cat_eq_1 D D'.
    Proof.
      eapply weqcomp. use total2_paths_equiv.
      use weqbandf.
      - apply total2_paths_equiv.
      - intros p. cbn.
        induction D as [D HD].
        induction D' as [D' HD'].
        cbn in *.
        induction p ; cbn ; unfold idfun.
        refine (_ ∘ total2_paths_equiv _ _ _)%weq.
        use weqfibtototal.
        intros p.
        cbn.
        rewrite transportf_const.
        exact (idweq _).
    Defined.

    (** Step 3 *)
    Definition data_disp_cat_eq_2
               {C : category}
               (D D' : disp_cat_data C)
               (Fo : ob_disp D = ob_disp D')
      : UU
      := ∏ (c c' : C) (a : ob_disp D c) (a' : ob_disp D c') (f : c --> c'),
         @mor_disp _ D _ _ a a' f
         = @mor_disp _ D' _ _
                     (eqweqmap (maponpaths (λ x, x c) Fo) a)
                     (eqweqmap (maponpaths (λ x, x c') Fo) a') f.

    Definition disp_cat_eq_2
               {C : category}
               (D D' : disp_cat_data C)
      : UU
      := ∑ (F : ∑ (Fo : ob_disp D = ob_disp D'), data_disp_cat_eq_2 D D' Fo),
         (∏ (c : C) (a : D c),
          eqweqmap (pr2 F c c a a (identity _)) (id_disp a)
          = id_disp (eqweqmap (maponpaths (λ x, x c) (pr1 F)) a))
           ×
           (∏ (a b c : C) (Da : D a) (Db : D b) (Dc : D c)
              (f : C⟦a,b⟧) (g : C⟦b,c⟧) (ff : Da -->[f] Db) (gg : Db -->[g] Dc),
            eqweqmap (pr2 F a c Da Dc (f · g)) (comp_disp ff gg)
            =
            comp_disp (eqweqmap (pr2 F a b Da Db f) ff) (eqweqmap (pr2 F b c Db Dc g) gg)).

    Definition data_disp_cat_eq_1_to_2
               {C : category}
               (D D' : disp_cat_data C)
               (Fo : (ob_disp D) = ob_disp D')
      : data_disp_cat_eq_1 D D' Fo ≃ data_disp_cat_eq_2 D D' Fo.
    Proof.
      induction D as [D HD].
      induction D as [DO DM].
      induction D' as [D' HD'].
      induction D' as [D'O D'M].
      cbn in *.
      induction Fo.
      unfold data_cat_eq_1, data_cat_eq_2.
      cbn.
      eapply weqcomp. apply weqtoforallpaths.
      use weqonsecfibers. intros ?.
      eapply weqcomp. apply weqtoforallpaths.
      use weqonsecfibers. intros ?.
      eapply weqcomp. apply weqtoforallpaths.
      use weqonsecfibers. intros ?.
      eapply weqcomp. apply weqtoforallpaths.
      use weqonsecfibers. intros ?.
      apply weqtoforallpaths.
    Defined.

    Definition disp_cat_eq_1_to_disp_cat_eq_2
               {C : category}
               (D D' : disp_cat_data C)
               (DS : ∏ (c c' : C) (f : c --> c') (x : D c) (y : D c'),
                     isaset (@mor_disp _ D _ _ x y f))
      : disp_cat_eq_1 D D' ≃ disp_cat_eq_2 D D'.
    Proof.
      use weqbandf.
      - use weqfibtototal.
        intro p.
        exact (data_disp_cat_eq_1_to_2 D D' p).
      - intros p.
        induction D as [D HD].
        induction D as [DO DM].
        induction HD as [DI DD].
        induction D' as [D' HD'].
        induction D' as [D'O D'M].
        induction HD' as [D'I D'C].
        induction p as [p1 p2] ; cbn in *.
        unfold data_disp_cat_eq_1 in p2.
        induction p1 ; cbn in *.
        induction p2 ; cbn ; unfold idfun.
        use weqdirprodf.
        + use weqimplimpl.
          * intros f a.
            induction f.
            reflexivity.
          * intros f.
            apply funextsec. intro z.
            apply funextsec. intro a.
            apply f.
          * intro.
            apply impred_isaset. intro.
            apply impred_isaset. intro.
            apply DS.
          * apply impred. intro.
            apply impred. intro.
            apply DS.
        + use weqimplimpl.
          * intros p.
            induction p.
            reflexivity.
          * intros p.
            apply funextsec ; intro a.
            apply funextsec ; intro b.
            apply funextsec ; intro c.
            apply funextsec ; intro f.
            apply funextsec ; intro g.
            apply funextsec ; intro Da.
            apply funextsec ; intro Db.
            apply funextsec ; intro Dc.
            apply funextsec ; intro ff.
            apply funextsec ; intro gg.
            specialize (p a b c Da Db Dc f g ff gg).
            induction p.
            reflexivity.
          * repeat (apply impred_isaset ; intro).
            apply DS.
          * repeat (apply impred ; intro).
            apply DS.
    Defined.

    (** Step 4 *)
    Definition disp_cat_equiv
               {C : category}
               (D D' : disp_cat_data C)
      : UU
      := ∑ (F : ∑ (Fo : ∏ (c : C), D c ≃ D' c),
                ∏ (c c' : C) (a : D c) (a' : D c') (f : c --> c'),
                (a -->[f] a') ≃ (Fo c a -->[f] Fo c' a')),
         (∏ (c : C) (a : D c),
          (pr2 F c c a a (identity _)) (id_disp a) = id_disp (pr1 F c a))
           ×
           (∏ (a b c : C) (Da : D a) (Db : D b) (Dc : D c)
              (f : C⟦a,b⟧) (g : C⟦b,c⟧) (ff : Da -->[f] Db) (gg : Db -->[g] Dc),
            (pr2 F a c Da Dc (f · g)) (comp_disp ff gg)
            =
            comp_disp ((pr2 F a b Da Db f) ff) ((pr2 F b c Db Dc g) gg)).

    Definition weq_disp_cat_eq_disp_cat_equiv
               {C : category}
               (D D' : disp_cat_data C)
      : disp_cat_eq_2 D D' ≃ disp_cat_equiv D D'.
    Proof.
      use weqbandf.
      - use weqbandf.
        + eapply weqcomp. apply invweq, weqfunextsec.
          apply weqonsecfibers. intro.
          apply univalence.
        + intros p.
          unfold data_cat_eq_2.
          use weqonsecfibers. intros x.
          use weqonsecfibers. intros y.
          use weqonsecfibers. intros ?.
          use weqonsecfibers. intros ?.
          use weqonsecfibers. intros ?.
          apply univalence.
      - intros q.
        apply idweq.
    Defined.

    (** Step 5 *)
    Definition disp_cat_equiv_to_disp_catiso
               {C : category}
               (D D' : disp_cat C)
      : disp_cat_equiv D D' → disp_catiso D D'.
    Proof.
      intros F.
      use tpair.
      - use tpair.
        + use tpair.
          * exact (pr1(pr1 F)).
          * exact (pr2(pr1 F)).
        + split.
          * exact (pr1(pr2 F)).
          * exact (pr2(pr2 F)).
      - split.
        + intros a b.
          apply (pr2(pr1 F)).
        + apply (pr1(pr1 F)).
    Defined.

    Definition disp_catiso_to_disp_cat_equiv
               {C : category}
               (D D' : disp_cat C)
      : disp_catiso D D' → disp_cat_equiv D D'.
    Proof.
      intros F.
      use tpair.
      - use tpair.
        + intros c.
          use make_weq.
          * exact (@disp_functor_on_objects _ _ _ _ _ F c).
          * apply F.
        + intros c c' a b f.
          use make_weq.
          * exact (@disp_functor_on_morphisms _ _ _ _ _ F c c' a b f).
          * apply F.
      - split.
        + intros c a. apply (disp_functor_id F).
        + intros ? ? ? ? ? ? ? ? ? ?. apply (disp_functor_comp F).
    Defined.

    Definition disp_cat_equiv_to_disp_catiso_weq
               {C : category}
               (D D' : disp_cat C)
      : disp_cat_equiv D D' ≃ disp_catiso D D'.
    Proof.
      refine (disp_cat_equiv_to_disp_catiso D D' ,, _).
      use isweq_iso.
      - exact (disp_catiso_to_disp_cat_equiv D D').
      - reflexivity.
      - reflexivity.
    Defined.

    (** All in all, we get *)
    Definition disp_catiso_is_path_disp_cat
               {C : category}
               (D D' : disp_cat C)
      : D = D' ≃ disp_catiso D D'
      := ((disp_cat_equiv_to_disp_catiso_weq D D')
            ∘ weq_disp_cat_eq_disp_cat_equiv D D'
            ∘ disp_cat_eq_1_to_disp_cat_eq_2 D D' (@homsets_disp _ D)
            ∘ disp_cat_path_to_disp_cat_eq_1 D D'
            ∘ disp_cat_path_precat D D')%weq.

  End DispCatIso.

  Section TargetFullDispSubcategory.

    Definition target_disp_subcat_ob_mor
               {C : category} {D' : disp_cat C}
               (F : ff_disp_functor D')
      : disp_cat_ob_mor C.
    Proof.
      exists (λ (c : C), pr1 F c).
      set (Fob := pr2 F).
      intros c c' a b f.
      exact (Fob _ a -->[f] Fob _ b).
    Defined.

    Definition target_disp_subcat_id_comp
               {C : category} {D' : disp_cat C}
               (F : ff_disp_functor D')
      : disp_cat_id_comp C (target_disp_subcat_ob_mor F).
    Proof.
      use make_dirprod.
      - intros c a. apply id_disp.
      - intros a b c f g Da Db Dc. apply comp_disp.
    Defined.

    Definition target_disp_subcat_data
               {C : category} {D' : disp_cat C}
               (F : ff_disp_functor D')
      : disp_cat_data C
      := (_ ,, target_disp_subcat_id_comp F).

    Definition target_disp_subcat_axioms
               {C : category} {D' : disp_cat C}
               (F : ff_disp_functor D')
      : disp_cat_axioms C (target_disp_subcat_data F).
    Proof.
      repeat use make_dirprod.
      - intros c c' f a a' ff. apply id_left_disp.
      - intros c c' f a a' ff. apply id_right_disp.
      - intros ? ? ? ? ? ? ? ? ? ? ? ? ? ?. apply assoc_disp.
      - intros ? ? ? ? ?. apply homsets_disp.
    Defined.
               
    Definition target_disp_subcat
               {C : category} {D' : disp_cat C}
               (F : ff_disp_functor D')
      : disp_cat C
      := (_ ,, target_disp_subcat_axioms F).

    Definition target_disp_inclusion_functor_data
               {C : category} {D' : disp_cat C}
               (F : ff_disp_functor D')
      : disp_functor_data (functor_identity C) (target_disp_subcat F) D'.
    Proof.
      exists (pr2 F).
      intros c c' a a' f. apply idfun.
    Defined.

    Definition target_disp_inclusion_functor_axioms
               {C : category} {D' : disp_cat C}
               (F : ff_disp_functor D')
      : disp_functor_axioms (target_disp_inclusion_functor_data F).
    Proof.
      repeat use make_dirprod.
      - intros c a. apply idpath.
      - intros ? ? ? ? ? ? ? ? ? ?. apply idpath.
    Defined.

    Definition target_disp_inclusion_functor
               {C : category} {D' : disp_cat C}
               (F : ff_disp_functor D')
      : disp_functor (functor_identity C) (target_disp_subcat F) D'
      := (_ ,, target_disp_inclusion_functor_axioms F).

    Definition target_disp_inclusion_functor_is_ff
               {C : category} {D' : disp_cat C}
               (F : ff_disp_functor D')
      : disp_functor_ff (target_disp_inclusion_functor F).
    Proof.
      intros ? ? ? ? ?. apply (weqproperty (idweq _)).
    Defined.

    Definition target_disp_inclusion_functor_explicit
               {C : category} {D' : disp_cat C}
               (F : ff_disp_functor D')
      : ff_disp_functor_explicit D'
      := (_ ,, _ ,, target_disp_inclusion_functor_is_ff F).

    Definition source_disp_cat_target_disp_subcat_catiso
               {C : category} {D' : disp_cat C}
               (F : ff_disp_functor D')
      : disp_catiso (source_disp_cat_from_ff_disp_functor F) (target_disp_subcat F).
    Proof.
      use tpair.
      - use tpair.
        + use tpair.
          * intros c. apply idfun.
          * intros c c' a b f. apply (disp_functor_on_morphisms F).
        + use make_dirprod.
          * intros ? ?. apply (disp_functor_id F).
          * intros ? ? ? ? ? ? ? ? ?. apply (disp_functor_comp F).
      - use make_dirprod.
        + apply (disp_functor_from_ff_disp_functor_is_ff F).
        + intros c. apply (weqproperty (idweq _)).
    Defined.

    Definition source_disp_cat_is_target_disp_subcat
               {C : category} {D' : disp_cat C}
               (F : ff_disp_functor D')
      : source_disp_cat_from_ff_disp_functor F = target_disp_subcat F.
    Proof.
      apply disp_catiso_is_path_disp_cat.
      apply source_disp_cat_target_disp_subcat_catiso.
    Defined.

    Definition ff_disp_functor_is_target_disp_inclusion_functor
               {C : category} {D' : disp_cat C}
               (F : ff_disp_functor D')
      : ff_disp_functor_weq F = target_disp_inclusion_functor_explicit F.
    Proof.
      apply (invmaponpathsweq (invweq ff_disp_functor_weq)).
      apply idpath.
    Defined.

    Definition ff_disp_functor_explicit_eq
               {C : category} {D' : disp_cat C}
               (F G : ff_disp_functor_explicit D')
               (eq_ob : ∏ (c : C), pr1 F c = pr1 G c)
               (eq_Fob : ∏ (c : C) (d : pr1 G c),
                         F c (transportb (λ x, x) (eq_ob c) d) = G c d)
      : F = G.
    Proof.
      apply (invmaponpathsweq (invweq ff_disp_functor_weq)).
      set (w := weqtotaltoforall (λ c, UU) (λ c d, d → D' c) : ff_disp_functor D' ≃ _).
      apply (invmaponpathsweq w).
      apply funextsec. intros c. 
      use total2_paths_f.
      - apply eq_ob.
      - apply funextsec. intros d.
        etrans. { eapply (maponpaths (λ k, k d)), (transportf_forall_var _ (λ x, x)). }
        apply eq_Fob.
    Defined.

    Definition ff_disp_functor_weq2
               {C : category} {D' : disp_cat C}
      : ff_disp_functor D' ≃ ff_disp_functor_explicit D'.
    Proof.
      use weq_iso.
      - apply target_disp_inclusion_functor_explicit.
      - intros F.
        set (ob_disp := pr1 (pr1 (pr1 (pr1 F)))).
        set (Fob := pr1 (pr1 (pr1 (pr2 F)))).
        exact (ob_disp ,, Fob).
      - intros ?. apply idpath.
      - intros ?.
        use ff_disp_functor_explicit_eq.
        + intros c. apply idpath.
        + intros c. intros d. apply idpath.
    Defined.

  End TargetFullDispSubcategory.

End FullyFaithfulDispFunctor.

(*
  [TypeTheory.ALV2.TypeCat_ComprehensionCat]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**
This module defines a comprehension category induced by a (non-split) type category.

Main definition is

- [typecat_ff_comprehension_cat_weq] - (non-split) type categories are fully faithful comprehension categories;

Important parts are:

- [typecat_obj_ext_structure_disp_ff_functor_to_codomain_weq]
  - object extension structures of type category are displayed functors into displayed codomain category; this equivalence is computationally friendly and maps object extension structures to an inclusion functor (specifically [target_disp_inclusion_functor]) from a subcategory of codomain displayed category.

*)

Require Import UniMath.MoreFoundations.PartA.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.ALV2.FullyFaithfulDispFunctor.
Require Import TypeTheory.ALV2.TypeCat_ComprehensionCat.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.ComprehensionC.

Section Auxiliary.

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

End Auxiliary.

Local Notation "'π' A" := (dpr_typecat_obj_ext A) (at level 5).

Section TypeCat_ComprehensionCat_Equiv.

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
       isPullback (!dpr_q _ A _ f).

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
       isPullback (!dpr_q).

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
              isPullback (! dpr_q A Γ' f))).
    apply weqonsecfibers. intros Γ.

    eapply weqcomp.
    apply (weqtotaltoforall4
             (λ A, ∏ Γ' : C, C ⟦ Γ', Γ ⟧ → TC Γ')
             (λ A reind, ∏ (Γ' : C) (f : C ⟦ Γ', Γ ⟧),
              C ⟦ obj_ext_typecat Γ' (reind Γ' f), obj_ext_typecat Γ A ⟧)
             (λ A reind q, ∏ (Γ' : C) (f : C ⟦ Γ', Γ ⟧),
              (q Γ' f;; π A)%mor = (π (reind Γ' f);; f)%mor)
             (λ (A : TC Γ) reind q dpr_q, ∏ (Γ' : C) (f : C ⟦ Γ', Γ ⟧),
              isPullback (! dpr_q Γ' f))).
    apply weqonsecfibers. intros A.
    
    eapply weqcomp.
    apply (weqtotaltoforall4
             (λ Γ', C ⟦ Γ', Γ ⟧ → TC Γ')
             (λ Γ' reind, ∏ (f : C ⟦ Γ', Γ ⟧),
              C ⟦ obj_ext_typecat Γ' (reind f), obj_ext_typecat Γ A ⟧)
             (λ Γ' reind q, ∏ (f : C ⟦ Γ', Γ ⟧),
              (q f;; π A)%mor = (π (reind f);; f)%mor)
             (λ Γ' reind q dpr_q, ∏ (f : C ⟦ Γ', Γ ⟧),
              isPullback (! dpr_q f))).
    apply weqonsecfibers. intros Γ'.

    apply (weqtotaltoforall4
             (λ f, TC Γ')
             (λ f reind, C ⟦ obj_ext_typecat Γ' reind, obj_ext_typecat Γ A ⟧)
             (λ f reind q, (q ;; π A)%mor = (π reind ;; f)%mor)
             (λ f reind q dpr_q, isPullback (! dpr_q))).
  Defined.

  Definition ff_comprehension_cat_structure (C : category) : UU
    := ∑ (F : ∑ (D : disp_cat C)
                (F : disp_functor (functor_identity _) D (disp_codomain C))
              , disp_functor_ff F),
       cleaving (pr1 F) × is_cartesian_disp_functor (pr1 (pr2 F)). 

  (* TODO: move upstream? *)
  Definition isaprop_is_cartesian_image_of_cleaving
        {C C' : category} {F : functor C C'}
        {D : disp_cat C} {D' : disp_cat C'} {FF : disp_functor F D D'}
        (cleaving_D : cleaving D)
    : isaprop (∏ (c c' : C) (f : c' --> c) (d : D c),
               is_cartesian (#FF (cleaving_D c c' f d))).
  Proof.
    apply impred_isaprop. intros c.
    apply impred_isaprop. intros c'.
    apply impred_isaprop. intros f.
    apply impred_isaprop. intros d.
    apply isaprop_is_cartesian.
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

  (* TODO: move upstream? *)
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
    - apply isaprop_is_cartesian_image_of_cleaving.
    - apply isaprop_is_cartesian_disp_functor.
  Defined.

  (* TODO: generalize to any functor into codomain? *)
  Definition pullback_is_cartesian
             {C : category}
             {TC : typecat_obj_ext_structure C}
             {Γ Γ' : C} {f : Γ' --> Γ}
             {A : pr1 (typecat_obj_ext_structure_ff_disp_functor_to_codomain_weq _ TC) Γ}
             {A' : pr1 (typecat_obj_ext_structure_ff_disp_functor_to_codomain_weq _ TC) Γ'}
             (ff : A' -->[f] A)
    : (isPullback (! pr2 ff)) -> is_cartesian ff.
  Proof.
    - intros pb.
      intros Δ g B ggff.
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
  Defined.

  Definition pullback_is_cartesian'
             {C : category}
             {TC : typecat_obj_ext_structure C}
             {Γ Γ' : C} {f : Γ' --> Γ}
             {A : pr1 (typecat_obj_ext_structure_ff_disp_functor_to_codomain_weq _ TC) Γ}
             {A' : pr1 (typecat_obj_ext_structure_ff_disp_functor_to_codomain_weq _ TC) Γ'}
             (ff : A' -->[f] A)
    : isPullback (! pr2 ff) ->
      is_cartesian (# (typecat_obj_ext_structure_ff_disp_functor_to_codomain_weq _ TC) ff).
  Proof.
    intros pb.
    intros Δ g k hh.
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
             (λ qq, isPullback (! pr2 qq))
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
      + apply pullback_is_cartesian. apply pb.
      + intros ? ? ?. apply pullback_is_cartesian'. apply pb.

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

End TypeCat_ComprehensionCat_Equiv.

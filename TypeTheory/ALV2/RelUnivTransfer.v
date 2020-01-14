(**
  [TypeTheory.ALV2.RelUnivTransfer]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**
Transfer constructions from [TypeTheory.ALV1.RelativeUniverses] lifted to functors.

Current observation: for simple category of relative J-universe structures
transfer constructions are lifted "trivially" and the resulting functor
has all the properties of S functor. This might become a little more complicated
for the more general case of "full" category of relative J-universe structures
(where morphisms have explicit ϕ component).

TODO:
- [x] one transfer construction for "simple" (naive) category of J-universe structures
- [ ] transfer constructions for "full" category of J-universe structures
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.RelativeUniverses.
Require Import TypeTheory.ALV1.Transport_along_Equivs.
Require Import TypeTheory.ALV2.RelUniv_Cat_Simple.
Require Import TypeTheory.ALV2.RelUniv_Cat.
Require Import UniMath.CategoryTheory.catiso.

Set Automatic Introduction.

Section RelUniv_Transfer.

  (*       J
      C  -----> D
      |         |
    R |         | S
      |         |
      v         v
      C' -----> D'
           J'
   *)
  Context (C D C' D' : category).
  Context (J  : functor C D).
  Context (J' : functor C' D').
  Context (R : functor C C').
  Context (S : functor D D').

  (* the square of functors above commutes
   * up to natural isomorphism *)
  Context (α : [C, D'] ⟦ J ∙ S, R ∙ J' ⟧).
  Context (α_is_iso : is_iso α).

  (* J and J' are fully faithful *)
  Context (ff_J : fully_faithful J).
  Context (ff_J' : fully_faithful J').

  (* S preserves pullbacks *)
  Context (S_pb : maps_pb_squares_to_pb_squares _ _ S).

  Section RelUniv_Transfer_with_ess_split.

    Definition reluniv_mor_J_to_J'_with_ess_split
                (S_sf : split_full S)
                (R_es : split_ess_surj R)
                (u1 u2 : relative_universe J)
                (mor : relative_universe_mor _ u1 u2)
        : relative_universe_mor _
            (transfer_of_rel_univ_with_ess_split
            _ u1 _ _ _ _ α_is_iso S_pb R_es S_sf)
            (transfer_of_rel_univ_with_ess_split
            _ u2 _ _ _ _ α_is_iso S_pb R_es S_sf).
    Proof.
        set (u1' := transfer_of_rel_univ_with_ess_split
                    _ u1 _ _ _ _ α_is_iso S_pb R_es S_sf).
        set (u2' := transfer_of_rel_univ_with_ess_split
                    _ u2 _ _ _ _ α_is_iso S_pb R_es S_sf).
        set (F_Ũ := pr11 mor).
        set (F_U := pr21 mor).
        use tpair.
        - use make_dirprod.
          + exact (# S F_Ũ).
          + exact (# S F_U).
        - (* NOTE: we use eqweqmap to match [weq_reluniv_mor_J_to_J'_with_ess_split] *)
          use (eqweqmap _ (maponpaths (# S) (pr2 mor))).
          etrans. apply maponpaths, functor_comp.
          etrans. apply maponpaths_2, functor_comp.
          apply idpath.
    Defined.

    Definition weq_reluniv_mor_J_to_J'_with_ess_split
                (S_faithful : faithful S)
                (S_sf : split_full S)
                (R_es : split_ess_surj R)
                (u1 u2 : relative_universe J)
        : relative_universe_mor _ u1 u2
        ≃ relative_universe_mor _
            (transfer_of_rel_univ_with_ess_split
            _ u1 _ _ _ _ α_is_iso S_pb R_es S_sf)
            (transfer_of_rel_univ_with_ess_split
            _ u2 _ _ _ _ α_is_iso S_pb R_es S_sf).
    Proof.
      set (S_ff := full_and_faithful_implies_fully_faithful _ _ _
                     (full_from_split_full _ S_sf , S_faithful)).
      set (S_weq := weq_from_fully_faithful S_ff).
      use weqtotal2.
      - use weqdirprodf.
        + apply S_weq.
        + apply S_weq.
      - intros mor.
        eapply weqcomp.
        apply (maponpaths (S_weq _ _) ,, isweqmaponpaths _ _ _).
        apply eqweqmap.
        unfold is_gen_reluniv_mor; simpl.
        etrans. apply maponpaths, functor_comp.
        etrans. apply maponpaths_2, functor_comp.
        apply idpath.
    Defined.

    Goal ∏
         (S_faithful : faithful S)
         (S_sf : split_full S)
         (R_es : split_ess_surj R)
         (u1 u2 : relative_universe J),
    reluniv_mor_J_to_J'_with_ess_split S_sf R_es u1 u2
    =
    weq_reluniv_mor_J_to_J'_with_ess_split S_faithful S_sf R_es u1 u2.
    Proof.
      intros a b c d e.
      unfold reluniv_mor_J_to_J'_with_ess_split, weq_reluniv_mor_J_to_J'_with_ess_split.
      simpl. cbn.
      apply idpath.
    Qed.

    Definition reluniv_functor_data_with_ess_split
                (S_sf : split_full S)
                (R_es : split_ess_surj R)
        : functor_data (reluniv_cat J)
                    (reluniv_cat J').
    Proof.
        use make_functor_data.
        - intros u.
        apply (transfer_of_rel_univ_with_ess_split
                _ u _ _ _ _ α_is_iso S_pb R_es S_sf).
        - intros u1 u2 mor.
        apply reluniv_mor_J_to_J'_with_ess_split.
        apply mor.
    Defined.

    Definition reluniv_functor_idax_with_ess_split
                (S_sf : split_full S)
                (R_es : split_ess_surj R)
        : functor_idax (reluniv_functor_data_with_ess_split S_sf R_es).
    Proof.
        intros u.
        use gen_reluniv_mor_eq.
        - etrans. apply functor_id. apply idpath.
        - etrans. apply functor_id. apply idpath.
    Defined.

    Definition reluniv_functor_compax_with_ess_split
                (S_sf : split_full S)
                (R_es : split_ess_surj R)
        : functor_compax (reluniv_functor_data_with_ess_split S_sf R_es).
    Proof.
        intros a b c f g.
        use gen_reluniv_mor_eq.
        - etrans. apply functor_comp. apply idpath.
        - etrans. apply functor_comp. apply idpath.
    Defined.

    Definition reluniv_is_functor_with_ess_split
                (S_sf : split_full S)
                (R_es : split_ess_surj R)
        : is_functor (reluniv_functor_data_with_ess_split S_sf R_es)
        := (reluniv_functor_idax_with_ess_split S_sf R_es ,, reluniv_functor_compax_with_ess_split S_sf R_es).

    Definition reluniv_functor_with_ess_split
                (S_sf : split_full S)
                (R_es : split_ess_surj R)
        : functor (@reluniv_cat _ _ J)
                (@reluniv_cat _ _ J').
    Proof.
        use (make_functor (reluniv_functor_data_with_ess_split S_sf R_es)).
        apply (reluniv_is_functor_with_ess_split S_sf R_es).
    Defined.

    Definition reluniv_functor_with_ess_split_is_full
               (S_faithful : faithful S)
               (S_sf : split_full S)
               (R_es : split_ess_surj R)
      : full (reluniv_functor_with_ess_split S_sf R_es).
    Proof.
      intros u1 u2.
      apply issurjectiveweq.
      use (weqproperty (weq_reluniv_mor_J_to_J'_with_ess_split _ _ _ _ _)).
      apply S_faithful.
    Defined.

    Definition reluniv_functor_with_ess_split_is_faithful
               (S_faithful : faithful S)
               (S_sf : split_full S)
               (R_es : split_ess_surj R)
      : faithful (reluniv_functor_with_ess_split S_sf R_es).
    Proof.
      intros u1 u2.
      apply isinclweq.
      use (weqproperty (weq_reluniv_mor_J_to_J'_with_ess_split _ _ _ _ _)).
      apply S_faithful.
    Defined.

    Definition reluniv_functor_with_ess_split_ff
               (S_faithful : faithful S)
               (S_sf : split_full S)
               (R_es : split_ess_surj R)
      : fully_faithful (reluniv_functor_with_ess_split S_sf R_es).
    Proof.
      apply full_and_faithful_implies_fully_faithful.
      use make_dirprod.
      - apply reluniv_functor_with_ess_split_is_full, S_faithful.
      - apply reluniv_functor_with_ess_split_is_faithful, S_faithful.
    Defined.

  End RelUniv_Transfer_with_ess_split.

  Section RelUniv_Transfer_with_ess_surj.

    Definition reluniv_mor_J_to_J'_with_ess_surj
                (C'_univ : is_univalent C')
                (S_f : full S)
                (R_es : essentially_surjective R)
                (u1 u2 : relative_universe J)
                (mor : relative_universe_mor _ u1 u2)
        : relative_universe_mor _
            (transfer_of_rel_univ_with_ess_surj
            _ u1 _ _ _ _ α_is_iso S_pb R_es C'_univ ff_J' S_f)
            (transfer_of_rel_univ_with_ess_surj
            _ u2 _ _ _ _ α_is_iso S_pb R_es C'_univ ff_J' S_f).
    Proof.
        set (u1' := transfer_of_rel_univ_with_ess_surj
                    _ u1 _ _ _ _ α_is_iso S_pb R_es C'_univ ff_J' S_f).
        set (u2' := transfer_of_rel_univ_with_ess_surj
                    _ u2 _ _ _ _ α_is_iso S_pb R_es C'_univ ff_J' S_f).
        set (F_Ũ := pr11 mor).
        set (F_U := pr21 mor).
        use tpair.
        - use make_dirprod.
        + exact (# S F_Ũ).
        + exact (# S F_U).
        - unfold is_gen_reluniv_mor. simpl.
        etrans. apply pathsinv0, functor_comp.
        apply pathsinv0. etrans. apply pathsinv0, functor_comp.
        apply maponpaths, pathsinv0.
        apply (pr2 mor).
    Defined.

    Definition reluniv_functor_data_with_ess_surj
                (C'_univ : is_univalent C')
                (S_f : full S)
                (R_es : essentially_surjective R)
        : functor_data (@reluniv_cat _ _ J)
                    (@reluniv_cat _ _ J').
    Proof.
        use make_functor_data.
        - intros u.
        apply (transfer_of_rel_univ_with_ess_surj
                _ u _ _ _ _ α_is_iso S_pb R_es C'_univ ff_J' S_f).
        - intros u1 u2 mor.
        apply reluniv_mor_J_to_J'_with_ess_surj.
        apply mor.
    Defined.

    Definition reluniv_functor_idax_with_ess_surj
                (C'_univ : is_univalent C')
                (S_f : full S)
                (R_es : essentially_surjective R)
        : functor_idax (reluniv_functor_data_with_ess_surj C'_univ S_f R_es).
    Proof.
        intros u.
        use gen_reluniv_mor_eq.
        - etrans. apply functor_id. apply idpath.
        - etrans. apply functor_id. apply idpath.
    Defined.

    Definition reluniv_functor_compax_with_ess_surj
                (C'_univ : is_univalent C')
                (S_f : full S)
                (R_es : essentially_surjective R)
        : functor_compax (reluniv_functor_data_with_ess_surj C'_univ S_f R_es).
    Proof.
        intros a b c f g.
        use gen_reluniv_mor_eq.
        - etrans. apply functor_comp. apply idpath.
        - etrans. apply functor_comp. apply idpath.
    Defined.

    Definition reluniv_is_functor_with_ess_surj
                (C'_univ : is_univalent C')
                (S_f : full S)
                (R_es : essentially_surjective R)
        : is_functor (reluniv_functor_data_with_ess_surj C'_univ S_f R_es)
        := (reluniv_functor_idax_with_ess_surj C'_univ S_f R_es ,, reluniv_functor_compax_with_ess_surj C'_univ S_f R_es).

    Definition reluniv_functor_with_ess_surj
                (C'_univ : is_univalent C')
                (S_f : full S)
                (R_es : essentially_surjective R)
        : functor (@reluniv_cat _ _ J)
                (@reluniv_cat _ _ J').
    Proof.
        use (make_functor (reluniv_functor_data_with_ess_surj C'_univ S_f R_es)).
        apply (reluniv_is_functor_with_ess_surj C'_univ S_f R_es).
    Defined.

    Definition reluniv_functor_with_ess_surj_is_full
               (C'_univ : is_univalent C')
               (S_f : full S)
               (R_es : essentially_surjective R)
      : full (reluniv_functor_with_ess_surj C'_univ S_f R_es).
    Proof.
      intros u1 u2 mor.
      (* STUCK: IMPOSSIBLE TO PROVE? *)
      (* I think this will also be impossible
       * for similar reasons as in the proof of
       * [reluniv_functor_with_ess_split_is_split_full] *)
    Abort.

    Definition reluniv_functor_with_ess_surj_is_faithful
               (C'_univ : is_univalent C')
               (S_f : full S)
               (R_es : essentially_surjective R)
               (S_faithful : faithful S)
      : faithful (reluniv_functor_with_ess_surj C'_univ S_f R_es).
    Proof.
      set (F := reluniv_functor_with_ess_surj C'_univ S_f R_es).
      unfold faithful, isincl, isofhlevelf.
      intros u1 u2 Fg.
      intros [g e_Fg] [g' e_Fg'].
      use tpair.
      - use total2_paths_f.
        + use gen_reluniv_mor_eq.
          * set (Sk := RelUniv_Cat.F_Ũ _ (pr1 Fg)).
            set (k := RelUniv_Cat.F_Ũ _ (pr1 g)).
            set (k' := RelUniv_Cat.F_Ũ _ (pr1 g')).
            set (e_Sk 
                := maponpaths (λ mor, RelUniv_Cat.F_Ũ _ (pr1 mor)) e_Fg
                : # S k = Sk).
            set (e_Sk'
                := maponpaths (λ mor, RelUniv_Cat.F_Ũ _ (pr1 mor)) e_Fg'
                : # S k' = Sk).
            set (H := S_faithful _ _ _ (_ ,, e_Sk) (_ ,, e_Sk')).
            set (e_kk' := maponpaths pr1 (pr1 H)).
            exact e_kk'.
          * set (Sk := RelUniv_Cat.F_U _ (pr1 Fg)).
            set (k := RelUniv_Cat.F_U _ (pr1 g)).
            set (k' := RelUniv_Cat.F_U _ (pr1 g')).
            set (e_Sk 
                := maponpaths (λ mor, RelUniv_Cat.F_U _ (pr1 mor)) e_Fg
                : # S k = Sk).
            set (e_Sk'
                := maponpaths (λ mor, RelUniv_Cat.F_U _ (pr1 mor)) e_Fg'
                : # S k' = Sk).
            set (H := S_faithful _ _ _ (_ ,, e_Sk) (_ ,, e_Sk')).
            set (e_kk' := maponpaths pr1 (pr1 H)).
            exact e_kk'.
        + apply homset_property.
      - intros t.
        apply isaset_hfiber.
        + apply homset_property.
        + apply homset_property.
    Defined.

  End RelUniv_Transfer_with_ess_surj.

End RelUniv_Transfer.

Section RelUniv_Yo_Rezk.

  Context (C : category).
  Let RC : univalent_category := Rezk_completion C (homset_property _).

  Definition transfer_of_RelUnivYoneda_functor
  : functor (@reluniv_cat C _ Yo) (@reluniv_cat RC _ Yo).
  Proof.
    set (R := Rezk_eta C (homset_property _)).
    set (R_ff := Rezk_eta_fully_faithful C (homset_property _)).
    set (R_es := Rezk_eta_essentially_surjective C (homset_property _)).
    set (S := Transport_along_Equivs.ext R R_ff R_es).
    set (S_pb := Transport_along_Equivs.preserves_pullbacks_ext R R_ff R_es).
    set (α := Transport_along_Equivs.fi R R_ff R_es).
    use (reluniv_functor_with_ess_surj
           _ _ _ _ Yo Yo
           R S
           α
           (pr2 α)
           (yoneda_fully_faithful _ _)
           S_pb
           (pr2 RC)
           (right_adj_equiv_is_full _ _)
           R_es
        ).
  Defined.

  Definition transfer_of_RelUnivYoneda_functor_is_faithful
    : faithful transfer_of_RelUnivYoneda_functor.
  Proof.
    use (reluniv_functor_with_ess_surj_is_faithful _ _ _ _ Yo Yo).
    use right_adj_equiv_is_ff.
  Defined.

End RelUniv_Yo_Rezk.
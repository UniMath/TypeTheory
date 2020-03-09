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

    Context (S_sf : split_full S).
    Context (R_es : split_ess_surj R).

    Let transfer_of_reluniv u
      := transfer_of_rel_univ_with_ess_split _ u _ _ _ _ α_is_iso S_pb R_es S_sf.

    Definition reluniv_mor_J_to_J'_with_ess_split
               (u1 u2 : relative_universe J)
               (mor : relative_universe_mor _ u1 u2)
      : relative_universe_mor _
                              (transfer_of_reluniv u1)
                              (transfer_of_reluniv u2).
    Proof.
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
         (u1 u2 : relative_universe J),
    reluniv_mor_J_to_J'_with_ess_split u1 u2
    =
    weq_reluniv_mor_J_to_J'_with_ess_split S_faithful u1 u2.
    Proof.
      intros; apply idpath.
    Qed.

    Definition reluniv_functor_data_with_ess_split
      : functor_data (reluniv_cat J) (reluniv_cat J').
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
      : functor_idax reluniv_functor_data_with_ess_split.
    Proof.
      intros u.
      use gen_reluniv_mor_eq.
      - etrans. apply functor_id. apply idpath.
      - etrans. apply functor_id. apply idpath.
    Defined.

    Definition reluniv_functor_compax_with_ess_split
      : functor_compax reluniv_functor_data_with_ess_split.
    Proof.
      intros a b c f g.
      use gen_reluniv_mor_eq.
      - etrans. apply functor_comp. apply idpath.
      - etrans. apply functor_comp. apply idpath.
    Defined.

    Definition reluniv_is_functor_with_ess_split
      : is_functor reluniv_functor_data_with_ess_split
      := (reluniv_functor_idax_with_ess_split ,, reluniv_functor_compax_with_ess_split).

    Definition reluniv_functor_with_ess_split
      : functor (reluniv_cat J) (reluniv_cat J')
      := make_functor
           reluniv_functor_data_with_ess_split
           reluniv_is_functor_with_ess_split.

    Definition reluniv_functor_with_ess_split_is_full
               (S_faithful : faithful S)
      : full reluniv_functor_with_ess_split.
    Proof.
      intros u1 u2.
      apply issurjectiveweq.
      use (weqproperty (weq_reluniv_mor_J_to_J'_with_ess_split _ _ _)).
      apply S_faithful.
    Defined.

    Definition reluniv_functor_with_ess_split_is_faithful
               (S_faithful : faithful S)
      : faithful reluniv_functor_with_ess_split.
    Proof.
      intros u1 u2.
      apply isinclweq.
      use (weqproperty (weq_reluniv_mor_J_to_J'_with_ess_split _ _ _)).
      apply S_faithful.
    Defined.

    Definition reluniv_functor_with_ess_split_ff
               (S_faithful : faithful S)
      : fully_faithful reluniv_functor_with_ess_split.
    Proof.
      apply full_and_faithful_implies_fully_faithful.
      use make_dirprod.
      - apply reluniv_functor_with_ess_split_is_full, S_faithful.
      - apply reluniv_functor_with_ess_split_is_faithful, S_faithful.
    Defined.

  End RelUniv_Transfer_with_ess_split.

  Section RelUniv_Transfer_with_ess_surj.

    Context (C'_univ : is_univalent C').
    Context (J'_ff : fully_faithful J').
    Context (S_f : full S).
    Context (R_es : essentially_surjective R).

    Let transfer_of_reluniv u
      := transfer_of_rel_univ_with_ess_surj _ u _ _ _ _ α_is_iso S_pb R_es C'_univ J'_ff S_f.

    Definition reluniv_mor_J_to_J'_with_ess_surj
                (u1 u2 : relative_universe J)
                (mor : relative_universe_mor _ u1 u2)
        : relative_universe_mor _
            (transfer_of_reluniv u1)
            (transfer_of_reluniv u2).
    Proof.
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

    Definition weq_reluniv_mor_J_to_J'_with_ess_surj
                (S_faithful : faithful S)
                (u1 u2 : relative_universe J)
        : relative_universe_mor _ u1 u2
        ≃ relative_universe_mor _
            (transfer_of_reluniv u1)
            (transfer_of_reluniv u2).
    Proof.
      set (S_ff := full_and_faithful_implies_fully_faithful _ _ _
                     (S_f , S_faithful)).
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
         (u1 u2 : relative_universe J),
    reluniv_mor_J_to_J'_with_ess_surj u1 u2
    =
    weq_reluniv_mor_J_to_J'_with_ess_surj S_faithful u1 u2.
    Proof.
      intros; apply idpath.
    Qed.

    Definition reluniv_functor_data_with_ess_surj
        : functor_data (@reluniv_cat _ _ J)
                    (@reluniv_cat _ _ J').
    Proof.
      use make_functor_data.
      - apply transfer_of_reluniv.
      - intros u1 u2 mor.
        apply reluniv_mor_J_to_J'_with_ess_surj.
        apply mor.
    Defined.

    Definition reluniv_functor_idax_with_ess_surj
      : functor_idax reluniv_functor_data_with_ess_surj.
    Proof.
      intros u.
      use gen_reluniv_mor_eq.
      - etrans. apply functor_id. apply idpath.
      - etrans. apply functor_id. apply idpath.
    Defined.

    Definition reluniv_functor_compax_with_ess_surj
      : functor_compax reluniv_functor_data_with_ess_surj.
    Proof.
        intros a b c f g.
        use gen_reluniv_mor_eq.
        - etrans. apply functor_comp. apply idpath.
        - etrans. apply functor_comp. apply idpath.
    Defined.

    Definition reluniv_is_functor_with_ess_surj
      : is_functor reluniv_functor_data_with_ess_surj
      := (reluniv_functor_idax_with_ess_surj
            ,, reluniv_functor_compax_with_ess_surj).

    Definition reluniv_functor_with_ess_surj
      : functor (@reluniv_cat _ _ J) (@reluniv_cat _ _ J')
      := make_functor
           reluniv_functor_data_with_ess_surj
           reluniv_is_functor_with_ess_surj.

    Definition reluniv_functor_with_ess_surj_is_full
               (S_faithful : faithful S)
      : full reluniv_functor_with_ess_surj.
    Proof.
      intros u1 u2.
      apply issurjectiveweq.
      use (weqproperty (weq_reluniv_mor_J_to_J'_with_ess_surj _ _ _)).
      apply S_faithful.
    Defined.

    Definition reluniv_functor_with_ess_surj_is_faithful
               (S_faithful : faithful S)
      : faithful reluniv_functor_with_ess_surj.
    Proof.
      intros u1 u2.
      apply isinclweq.
      use (weqproperty (weq_reluniv_mor_J_to_J'_with_ess_surj _ _ _)).
      apply S_faithful.
    Defined.

    Definition reluniv_functor_with_ess_surj_ff
               (S_faithful : faithful S)
      : fully_faithful reluniv_functor_with_ess_surj.
    Proof.
      apply full_and_faithful_implies_fully_faithful.
      use make_dirprod.
      - apply reluniv_functor_with_ess_surj_is_full, S_faithful.
      - apply reluniv_functor_with_ess_surj_is_faithful, S_faithful.
    Defined.

    (* TODO: move to Auxiliary *)
    Definition functor_postcomp_iso
               {D1 D2 D3 : category}
               (F G : functor D1 D2)
               (H : functor D2 D3)
      : @iso [D1, D2] F G → @iso [D1, D3] (F ∙ H) (G ∙ H).
    Proof.
      intros i.
      use z_iso_to_iso.
      use make_z_iso.
      - use make_nat_trans.
        + intros d.
          apply (# H ((pr1 i : nat_trans _ _) d)).
        + intros d d' f.
          simpl.
          etrans. apply pathsinv0, functor_comp.
          apply pathsinv0.
          etrans. apply pathsinv0, functor_comp.
          apply maponpaths.
          apply pathsinv0.
          apply (pr2 (pr1 i)).
      - use make_nat_trans.
        + intros d.
          apply (# H ((inv_from_iso i : nat_trans _ _) d)).
        + intros d d' f.
          simpl.
          etrans. apply pathsinv0, functor_comp.
          apply pathsinv0.
          etrans. apply pathsinv0, functor_comp.
          apply maponpaths.
          apply pathsinv0.
          apply (pr2 (inv_from_iso i)).
      - use make_dirprod.
        + use total2_paths_f.
          * use funextsec. intros d. simpl.
            etrans. apply pathsinv0, functor_comp.
            etrans. apply maponpaths.
            apply (maponpaths (λ k, pr1 k d) (iso_inv_after_iso i)).
            apply functor_id.
          * apply isaprop_is_nat_trans.
            apply homset_property.
        + use total2_paths_f.
          * use funextsec. intros d. simpl.
            etrans. apply pathsinv0, functor_comp.
            etrans. apply maponpaths.
            apply (maponpaths (λ k, pr1 k d) (iso_after_iso_inv i)).
            apply functor_id.
          * apply isaprop_is_nat_trans.
            apply homset_property.
    Defined.

    Definition reluniv_functor_with_ess_surj_issurjective
               (AC : AxiomOfChoice.AxiomOfChoice)
               (R_es' : split_ess_surj R)
               (obD_isaset : isaset D)
               (D_univ : is_univalent D)
               (D'_univ : is_univalent D')
               (invS : functor D' D)
               (eta : iso (C:=[D, D, pr2 D]) (functor_identity D) (S ∙ invS))
               (eps : iso (C:=[D', D', pr2 D']) (invS ∙ S) (functor_identity D'))
               (S_ff : fully_faithful S)
               (invJ : functor D C)
               (etaJ : iso (C:=[C, C, pr2 C]) (functor_identity C) (J ∙ invJ))
               (epsJ : iso (C:=[D, D, pr2 D]) (invJ ∙ J) (functor_identity D))
      : issurjective reluniv_functor_with_ess_surj.
    Proof.
      set (invR := J' ∙ invS ∙ invJ).
      
      assert (eps_id : invS ∙ S = functor_identity _).
      {
        use (isotoid _ (is_univalent_functor_category _ _ _)).
        apply D'_univ.
        apply eps.
      }
      assert (eta_id : S ∙ invS = functor_identity _).
      {
        use (isotoid _ (is_univalent_functor_category _ _ _)).
        apply D_univ.
        apply (iso_inv_from_iso eta).
      }
      assert (α_id : J ∙ S = R ∙ J').
      {
        use (isotoid _ (is_univalent_functor_category _ _ _)).
        apply D'_univ.
        apply (α,,α_is_iso).
      }

      assert (R_J'_invS_invJ_id : nat_iso (R ∙ J' ∙ invS ∙ invJ) (functor_identity _)).
      {
        use iso_to_nat_iso.
        eapply iso_comp. apply functor_postcomp_iso, functor_postcomp_iso.
        apply (iso_inv_from_iso (α,, α_is_iso)).
        eapply iso_comp. apply functor_postcomp_iso, functor_assoc_iso.
        eapply iso_comp. apply functor_postcomp_iso, functor_precomp_iso.
        apply (iso_inv_from_iso eta).
        eapply iso_comp. apply functor_postcomp_iso.
        apply idtoiso, functor_identity_right.
        eapply iso_comp. apply (iso_inv_from_iso etaJ).
        apply identity_iso.
      }

      assert ( R_J'_invS_id : R ∙ J' ∙ invS = J ).
      {
        use (isotoid _ (is_univalent_functor_category _ _ _)).
        apply D_univ.
        eapply iso_comp. apply functor_postcomp_iso.
        apply (iso_inv_from_iso (α,, α_is_iso)).
        eapply iso_comp. apply functor_assoc_iso.
        eapply iso_comp. apply functor_precomp_iso.
        apply (iso_inv_from_iso eta).
        apply idtoiso, functor_identity_right.
      }


      intros u.
      set (U := pr1 (pr1 (pr1 u))).
      set (Ũ := dirprod_pr2 (pr1 (pr1 u))).
      set (p := pr2 (pr1 u)).
      use hinhpr.
      use tpair.
      + use tpair.
        * use tpair.
          -- use make_dirprod.
             ++ apply (invS U).
             ++ apply (invS Ũ).
          -- apply (# invS p).
        * intros X f.
          set (f' := pr1 (inv_from_iso (α,,α_is_iso)) X
                         ;; # S f
                         ;; pr11 eps U
                     : D' ⟦ J' (R X), U ⟧
                ).
          set (pb := pr2 u (R X) f').
          set (Xf := pr11 pb).
          set (Xf' := pr1 (R_es' Xf)).
          set (Xf'_iso := pr2 (R_es' Xf)).
          use tpair.
          -- use tpair.
             ++ apply Xf'.
             ++ use make_dirprod.
                ** eapply compose.
                   apply (pr1 (inv_from_iso
                                 (nat_iso_to_iso _ _ R_J'_invS_invJ_id))
                              Xf').
                   eapply compose.
                   apply (# invJ (# invS (# J' (Xf'_iso ;; pr121 pb)))).
                   apply (pr1 R_J'_invS_invJ_id X).
                ** use (_ ;; # invS (pr221 pb)).
                   use (_ ;; # (J' ∙ invS) (pr1 Xf'_iso)).
                   apply (transportf
                            (λ F, D ⟦ pr11 F Xf', _ Xf' ⟧)
                            R_J'_invS_id (identity _)).
          -- simpl.
             Print fpullback_prop.
             Print commutes_and_is_pullback.
             use make_dirprod.
             ++ apply pathsinv0.
                etrans. apply assoc'.
                etrans. apply maponpaths, pathsinv0, functor_comp.
                etrans. apply maponpaths, maponpaths.
                apply pathsinv0, (pr12 pb).

                etrans. apply maponpaths, functor_comp.
                etrans. apply assoc.
                etrans. apply maponpaths, functor_comp.
                etrans. apply maponpaths, maponpaths_2, functor_comp.

                (* FIXME: big diagram to prove for, will try to split *)
    Abort.
        
  End RelUniv_Transfer_with_ess_surj.

End RelUniv_Transfer.

Section WeakRelUniv_Transfer.

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

  (* D and D' are univalent *)
  Context (Dcat : is_univalent D).
  Context (D'cat : is_univalent D').

  (* S preserves pullbacks *)
  Context (S_pb : maps_pb_squares_to_pb_squares _ _ S).

  (* S is an equivalence *)
  Context (T : functor D' D).
  Context (η : iso (C := [D, D, pr2 D]) (functor_identity D) (S ∙ T)).
  Context (ε : iso (C := [D', D', pr2 D']) (T ∙ S) (functor_identity D')).
  Context (S_ff : fully_faithful S).

  (* R is essentially surjective and full *)
  Context (R_es : essentially_surjective R).
  Context (R_full : full R).

  Local Definition S_full : full S.
  Proof.
    apply fully_faithful_implies_full_and_faithful, S_ff.
  Defined.

  Let weq_weak_reluniv
    := weq_weak_relative_universe_transfer
         _ _ _ _ _
         α_is_iso S_pb R_es S_full
         R_full Dcat D'cat T η ε S_ff.

  Definition weq_weak_reluniv_mor_J_to_J'
             (u1 u2 : weak_relative_universe J)
    : weak_reluniv_cat J  ⟦ u1, u2 ⟧
    ≃ weak_reluniv_cat J' ⟦ weq_weak_reluniv u1, weq_weak_reluniv u2 ⟧.
  Proof.
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

  Definition weak_reluniv_functor_data
    : functor_data (weak_reluniv_cat J) (weak_reluniv_cat J').
  Proof.
    use make_functor_data.
    - apply weq_weak_reluniv.
    - apply weq_weak_reluniv_mor_J_to_J'.
  Defined.

  Definition weak_reluniv_functor_idax
    : functor_idax weak_reluniv_functor_data.
  Proof.
    intros u.
    use gen_reluniv_mor_eq.
    - etrans. apply functor_id. apply idpath.
    - etrans. apply functor_id. apply idpath.
  Defined.

  Definition weak_reluniv_functor_compax
    : functor_compax weak_reluniv_functor_data.
  Proof.
    intros a b c f g.
    use gen_reluniv_mor_eq.
    - etrans. apply functor_comp. apply idpath.
    - etrans. apply functor_comp. apply idpath.
  Defined.

  Definition weak_reluniv_is_functor
    : is_functor weak_reluniv_functor_data
    := (weak_reluniv_functor_idax ,, weak_reluniv_functor_compax).

  Definition weak_reluniv_functor
    : functor (weak_reluniv_cat J) (weak_reluniv_cat J')
    := make_functor
         weak_reluniv_functor_data
         weak_reluniv_is_functor.

  Definition weak_reluniv_functor_is_catiso
    : is_catiso weak_reluniv_functor.
  Proof.
    use tpair.
    - intros u1 u2.
      apply weq_weak_reluniv_mor_J_to_J'.
    - apply weq_weak_relative_universe_transfer.
  Defined.

End WeakRelUniv_Transfer.

Section RelUniv_Yo_Rezk.

  Context (C : category).
  Let RC : univalent_category := Rezk_completion C (homset_property _).

  Let R := Rezk_eta C (homset_property _).
  Let R_ff := Rezk_eta_fully_faithful C (homset_property _).
  Let R_es := Rezk_eta_essentially_surjective C (homset_property _).
  Let S := Transport_along_Equivs.ext R R_ff R_es.
  Let S_pb := Transport_along_Equivs.preserves_pullbacks_ext R R_ff R_es.
  Let α := Transport_along_Equivs.fi R R_ff R_es.

  Definition transfer_of_RelUnivYoneda_functor
    : functor (@reluniv_cat C _ Yo) (@reluniv_cat RC _ Yo).
  Proof.
    use (reluniv_functor_with_ess_surj
           _ _ _ _ Yo Yo
           R S
           α
           (pr2 α)
           S_pb
           (pr2 RC)
           (yoneda_fully_faithful _ _)
           (right_adj_equiv_is_full _ _)
           R_es
        ).
  Defined.

  Definition transfer_of_RelUnivYoneda_functor_ff
    : fully_faithful transfer_of_RelUnivYoneda_functor.
  Proof.
    use (reluniv_functor_with_ess_surj_ff _ _ _ _ Yo Yo).
    use right_adj_equiv_is_ff.
  Defined.

  Let T := Transport_along_Equivs.Fop_precomp R.

  Definition transfer_of_WeakRelUnivYoneda_functor
    : functor (@weak_reluniv_cat C _ Yo) (@weak_reluniv_cat RC _ Yo).
  Proof.
    use (weak_reluniv_functor
           _ _ _ _ Yo Yo
           R S
           α
           (pr2 α)
           (is_univalent_preShv _)
           (is_univalent_preShv _)
           S_pb
           T
        ).
    - apply epsinv.
    - apply etainv.
    - apply right_adj_equiv_is_ff.
    - apply R_es.
    - apply fully_faithful_implies_full_and_faithful, R_ff.
  Defined.

  Definition transfer_of_WeakRelUnivYoneda_functor_is_catiso
    : is_catiso transfer_of_WeakRelUnivYoneda_functor.
  Proof.
    apply weak_reluniv_functor_is_catiso.
  Defined.

End RelUniv_Yo_Rezk.
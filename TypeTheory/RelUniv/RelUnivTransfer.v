(**
  [TypeTheory.RelUniv.RelUnivTransfer]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**
Transfer constructions from [TypeTheory.RelUniv.Transport_along_Equivs] lifted to functors.

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
Require Import TypeTheory.Auxiliary.CategoryTheory.
Require Import TypeTheory.Auxiliary.Pullbacks.
Require Import TypeTheory.Auxiliary.SetsAndPresheaves.
Require Import TypeTheory.Auxiliary.TypeOfMorphisms.

Require Import TypeTheory.RelUniv.RelativeUniverses.
Require Import TypeTheory.RelUniv.Transport_along_Equivs.
Require Import TypeTheory.RelUniv.RelUniv_Cat_Simple.
Require Import TypeTheory.RelUniv.RelUniv_Cat.
Require Import UniMath.CategoryTheory.catiso.

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
  Context (α_is_iso : is_z_isomorphism α).

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
      := transfer_of_rel_univ_with_ess_surj
           u α_is_iso S_pb R_es C'_univ J'_ff S_f.

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

  Section Surjective_if_R_split_ess_surj.
    Context (R_ses : split_ess_surj R)
            (D'_univ : is_univalent D')
            (invS : functor D' D)
            (eta : z_iso (C:=[D, D]) (functor_identity D) (S ∙ invS))
            (eps : z_iso (C:=[D', D']) (invS ∙ S) (functor_identity D'))
            (S_ff : fully_faithful S).

    Let E := ((S,, (invS,, (pr1 eta, pr1 eps)))
                ,, ((λ d,  (pr2 (Constructions.pointwise_z_iso_from_nat_z_iso eta d )))
                    , (λ d', (pr2 (Constructions.pointwise_z_iso_from_nat_z_iso eps d')))))
            : equivalence_of_cats D D'.

    Let AE := adjointificiation E.
    Let η' := pr1 (pr121 AE) : nat_trans (functor_identity _) (S ∙ invS).
    Let ε' := pr2 (pr121 AE) : nat_trans (invS ∙ S) (functor_identity _).
    Let η := z_iso_from_nat_z_iso
               _ (η',,pr12 (adjointificiation E))
            : z_iso (C:=[D, D]) (functor_identity D) (S ∙ invS).
    Let ε := z_iso_from_nat_z_iso
                _ (ε',,pr22 (adjointificiation E))
            : z_iso (C:=[D', D']) (invS ∙ S) (functor_identity D').

    Let ηx := Constructions.pointwise_z_iso_from_nat_z_iso (z_iso_inv_from_z_iso η).
    Let αx := Constructions.pointwise_z_iso_from_nat_z_iso (α,,α_is_iso).

  Section Helpers.

    Context (u' : reluniv_cat J').

    Let p' := pr1  u' : mor_total D'.
    Let Ũ' := pr21 p' : D'.
    Let U' := pr11 p' : D'.
    Let pf' := pr2 p' : D' ⟦ Ũ', U' ⟧.

    Let U := invS U'.
    Let Ũ := invS Ũ'.
    Let pf := # invS pf'.
    Local Definition p := functor_on_mor_total invS p' : mor_total D.

    Context (X : C) (f : D ⟦ J X, U ⟧).

    Let X' := R X : C'.
    Let f' := inv_from_z_iso (αx X) ;; # S f ;; pr11 ε U'
              : D' ⟦ J' X' , U' ⟧.
    Let pb' := pr2 u' X' f' : fpullback J' p' f'.
    Let Xf' := pr11 pb'.

    Local Definition Xf := pr1 (R_ses Xf') : C.
    Let RXf_Xf'_iso := pr2 (R_ses Xf') : z_iso (R Xf) Xf'.

    Let pp' := pr121 pb' : C' ⟦ Xf', X' ⟧.
    Local Definition pp : C ⟦ Xf, X ⟧.
    Proof.
      use (invweq (weq_from_fully_faithful ff_J _ _)).
      use (pr11 η _ ;; _ ;; pr1 (inv_from_z_iso η) _).
      use (# invS _).
      apply (pr1 α Xf ;; # J' (RXf_Xf'_iso ;; pp') ;; inv_from_z_iso (αx X)).
    Defined.

    Let Q' := pr221 pb' : D' ⟦ J' Xf', Ũ' ⟧.
    Local Definition Q
      := pr11 η _ ;; # invS (pr1 α Xf ;; # J' RXf_Xf'_iso ;; Q')
         : D ⟦ J Xf, invS Ũ' ⟧.

    Let pb'_commutes := pr12 pb' : # J' pp' ;; f' = Q' ;; p'.
    Let pb'_isPullback := pr22 pb'.

    Local Definition pb_commutes_and_is_pullback
      : commutes_and_is_pullback f p (# J pp) Q.
    Proof.
      use (@commutes_and_is_pullback_transfer_z_iso
               _ _ _ _ _
               _ _ _ _
               _ _ _ (J Xf)
               f p (# J pp) Q
               _ _ _ _
               _ _ _ _
               (functor_on_square _ _ invS pb'_commutes)
            ).
      - apply identity_z_iso.
      - eapply z_iso_comp.
        apply functor_on_z_iso, z_iso_inv_from_z_iso, αx.
        apply ηx.
      - apply identity_z_iso.
      - eapply z_iso_comp. apply functor_on_z_iso, functor_on_z_iso.
        apply z_iso_inv_from_z_iso, RXf_Xf'_iso.
        eapply z_iso_comp. apply functor_on_z_iso, z_iso_inv_from_z_iso, αx.
        apply ηx.
      - unfold f', z_iso_comp.

        etrans. apply id_right.
        etrans. apply functor_comp.
        etrans. apply maponpaths_2, functor_comp.
        etrans. apply assoc'.
        apply pathsinv0.
        etrans. apply assoc'.
        apply maponpaths.

        etrans. apply pathsinv0.
        apply (nat_trans_ax (inv_from_z_iso η)).
        apply maponpaths.

        apply pathsinv0.
        etrans. apply pathsinv0, id_left.
        etrans. apply maponpaths_2, pathsinv0.
        apply (maponpaths (λ k, pr1 k (invS U'))
                          (z_iso_after_z_iso_inv η)).

        etrans. apply assoc'.
        etrans. apply maponpaths.
        set (AE_tr2 := pr2 (pr221 AE) U'
                       : pr11 η (invS U') ;; # invS (pr11 ε U')
                         = identity _).
        apply AE_tr2.
        apply id_right.

      - etrans. apply id_right.
        apply pathsinv0, id_left.

      - apply pathsinv0.
        etrans. apply maponpaths.
        apply (homotweqinvweq (weq_from_fully_faithful ff_J _ _)). (*  *)

        etrans. apply maponpaths, assoc'.
        etrans. apply maponpaths, maponpaths, maponpaths_2.
        apply (functor_comp invS).
        etrans. apply maponpaths, maponpaths, assoc'.
        etrans. apply assoc.
        etrans. apply assoc.
        apply maponpaths_2.

        unfold z_iso_comp, functor_on_z_iso. simpl.
      (*  etrans. apply maponpaths_2, maponpaths_2, maponpaths, maponpaths.
        apply id_right. *)
        etrans. apply maponpaths_2, assoc'.
        etrans. apply maponpaths_2, maponpaths, assoc'.
        etrans. apply maponpaths_2, maponpaths, maponpaths.
        apply (z_iso_after_z_iso_inv (_,,pr1 (adjointification_forms_equivalence E) (J Xf))).

        etrans. apply maponpaths_2, maponpaths, id_right.
        etrans. apply maponpaths, functor_comp.
        etrans. apply assoc.
        etrans. apply maponpaths_2, assoc'.
        etrans. apply maponpaths_2, maponpaths.
        apply pathsinv0, functor_comp.
        etrans. apply maponpaths_2, maponpaths, maponpaths.
        apply z_iso_after_z_iso_inv.

        etrans. apply maponpaths_2, pathsinv0, functor_comp.
        etrans. apply pathsinv0, functor_comp.
        apply maponpaths.

        etrans. apply maponpaths_2, id_right.
        etrans. apply pathsinv0, functor_comp.
        apply maponpaths.
        
        etrans. apply assoc.
        etrans. apply maponpaths_2, z_iso_after_z_iso_inv.
        apply id_left.

      - etrans. apply id_right.
        apply pathsinv0.

        unfold Q, z_iso_comp, functor_on_z_iso. simpl.

        etrans. apply assoc.
        etrans. apply maponpaths_2, assoc'.
        etrans. apply maponpaths_2, maponpaths, assoc'.
        etrans. apply maponpaths_2, maponpaths, maponpaths.
        apply (z_iso_after_z_iso_inv (_,,pr1 (adjointification_forms_equivalence E) (J Xf))).

        etrans. apply maponpaths_2, maponpaths.
        apply id_right.

        etrans. apply maponpaths, functor_comp.
        etrans. apply assoc.
        etrans. apply maponpaths_2, assoc'.
        etrans. apply maponpaths_2, maponpaths, maponpaths, functor_comp.
        etrans. apply maponpaths_2, maponpaths, assoc.
        etrans. apply maponpaths_2, maponpaths, maponpaths_2.
        apply pathsinv0, functor_comp.
        etrans. apply maponpaths_2, maponpaths, maponpaths_2.
        apply maponpaths, z_iso_after_z_iso_inv.

        etrans. apply maponpaths_2, maponpaths.
        apply pathsinv0, functor_comp.
        etrans. apply maponpaths_2, maponpaths.
        apply maponpaths, id_left.

        etrans. apply maponpaths_2, pathsinv0, functor_comp.
        etrans. apply pathsinv0, functor_comp.
        apply maponpaths.

        etrans. apply maponpaths_2, pathsinv0, functor_comp.
        etrans. apply maponpaths_2, maponpaths, z_iso_after_z_iso_inv.
        etrans. apply maponpaths_2, functor_id.
        apply id_left.

     - use (isPullback_image_square _ _ invS).
       + apply homset_property.
       + apply (right_adj_equiv_is_ff _ _ S AE).
       + apply (right_adj_equiv_is_ess_sur _ _ S AE).
       + apply pb'_isPullback.
    Defined.

  End Helpers.

    Definition inv_reluniv_with_ess_surj
      : reluniv_cat J' → reluniv_cat J.
    Proof.
      intros u'.
      use tpair.
      + apply (p u').
      + intros X f.
        use tpair.
        * use tpair.
          -- apply (Xf u' X f).
          -- use make_dirprod.
             ++ apply pp.
             ++ apply Q.
        * apply pb_commutes_and_is_pullback.
    Defined.

    Definition reluniv_functor_with_ess_surj_after_inv_iso
               (u' : reluniv_cat J')
      : z_iso u'
            (reluniv_functor_with_ess_surj (inv_reluniv_with_ess_surj u')).
    Proof.
      set (εx := Constructions.pointwise_z_iso_from_nat_z_iso ε).
      set (εx' := Constructions.pointwise_z_iso_from_nat_z_iso
                   (z_iso_inv_from_z_iso ε)).
      use make_z_iso.
      - use tpair.
        + use make_dirprod.
          * cbn. apply (εx' (pr211 u')).
          * cbn. apply (εx' (pr111 u')).
        + unfold is_gen_reluniv_mor.
          etrans. apply pathsinv0.
          apply (nat_trans_ax (pr1 (z_iso_inv_from_z_iso ε))).
          apply idpath.
      - use tpair.
        + use make_dirprod.
          * cbn. apply (εx (pr211 u')).
          * cbn. apply (εx (pr111 u')).
        + unfold is_gen_reluniv_mor.
          etrans. apply pathsinv0.
          apply (nat_trans_ax (pr1 ε)).
          apply idpath.
      - use make_dirprod.
        + use gen_reluniv_mor_eq.
          * apply (maponpaths (λ k, pr1 k _) (z_iso_after_z_iso_inv ε)).
          * apply (maponpaths (λ k, pr1 k _) (z_iso_after_z_iso_inv ε)).
        + use gen_reluniv_mor_eq.
          * apply (maponpaths (λ k, pr1 k _) (z_iso_inv_after_z_iso ε)).
          * apply (maponpaths (λ k, pr1 k _) (z_iso_inv_after_z_iso ε)).
    Defined.

    Definition reluniv_functor_with_ess_surj_after_inv_id
               (u' : reluniv_cat J')
      : u' = reluniv_functor_with_ess_surj (inv_reluniv_with_ess_surj u').
    Proof.
      use isotoid.
      - use reluniv_cat_is_univalent.
        + apply C'_univ.
        + apply ff_J'.
        + apply D'_univ.
      - apply reluniv_functor_with_ess_surj_after_inv_iso.
    Defined.

    Definition reluniv_functor_with_ess_surj_issurjective
      : issurjective reluniv_functor_with_ess_surj.
    Proof.
      intros u'.
      use hinhpr.
      use tpair.
      - apply (inv_reluniv_with_ess_surj u').
      - apply pathsinv0, reluniv_functor_with_ess_surj_after_inv_id.
    Defined.

  End Surjective_if_R_split_ess_surj.

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
  Context (α_is_iso : is_z_isomorphism α).

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
  Context (η : z_iso (C := [D, D]) (functor_identity D) (S ∙ T)).
  Context (ε : z_iso (C := [D', D']) (T ∙ S) (functor_identity D')).
  Context (S_full : full S).
  Context (S_faithful : faithful S).

  (* R is essentially surjective and full *)
  Context (R_es : essentially_surjective R).
  Context (R_full : full R).

  Local Definition S_ff : fully_faithful S.
  Proof.
    use full_and_faithful_implies_fully_faithful.
    use make_dirprod.
    - apply S_full.
    - apply S_faithful.
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

  Local Definition relu_J_to_relu_J'
        (C'_univ : is_univalent C')
    : functor (reluniv_cat J) (reluniv_cat J')
    := reluniv_functor_with_ess_surj
         _ _ _ _ _ _ _ _ _ α_is_iso
         S_pb C'_univ ff_J' S_full R_es.

  Definition weak_relu_square_commutes_on_mor
        (C'_univ : is_univalent C')
        (u1 u2 : reluniv_cat J)
        (mor : reluniv_cat J ⟦ u1, u2 ⟧)
    : pr21 (relu_J_to_relu_J' C'_univ ∙ weak_from_reluniv_functor J') u1 u2 mor
    = pr21 (weak_from_reluniv_functor J ∙ weak_reluniv_functor) u1 u2 mor.
  Proof.
    use gen_reluniv_mor_eq.
    - apply idpath.
    - apply idpath.
  Defined.

  Definition weak_relu_square_nat_trans
        (C'_univ : is_univalent C')
    : nat_trans
        (relu_J_to_relu_J' C'_univ ∙ weak_from_reluniv_functor J')
        (weak_from_reluniv_functor J ∙ weak_reluniv_functor).
  Proof.
    use tpair.
    + intros u.
      use tpair.
      * use tpair.
        -- apply identity.
        -- apply identity.
      * unfold is_gen_reluniv_mor.
        cbn.
        etrans. apply id_left.
        apply pathsinv0, id_right.
    + intros u1 u2 mor.
      use gen_reluniv_mor_eq.
      * simpl.
        etrans. apply id_right.
        apply pathsinv0, id_left.
      * simpl.
        etrans. apply id_right.
        apply pathsinv0, id_left.
  Defined.

  Definition weak_relu_square_nat_trans_is_nat_iso
        (C'_univ : is_univalent C')
    : is_nat_iso (weak_relu_square_nat_trans C'_univ).
  Proof.
    intros u1 wu1.
    use isweq_iso.
    - intros mor.
      apply mor.
    - intros mor.
      use id_left. (* FIXME: works, but slow for some reason *)
    - intros mor.
      use id_left. (* FIXME: works, but slow for some reason *)
  Defined.

  Definition weak_relu_square_nat_trans_is_nat_z_iso
        (C'_univ : is_univalent C')
    : is_nat_z_iso (weak_relu_square_nat_trans C'_univ).
  Proof.
    intro u.
    apply is_z_iso_from_is_iso.
    apply weak_relu_square_nat_trans_is_nat_iso.
  Defined.
    
  Definition weak_relu_square_commutes
        (C'_univ : is_univalent C')
    : nat_z_iso
        (relu_J_to_relu_J' C'_univ ∙ weak_from_reluniv_functor J')
        (weak_from_reluniv_functor J ∙ weak_reluniv_functor).
  Proof.
    use tpair.
    - apply weak_relu_square_nat_trans.
    - apply weak_relu_square_nat_trans_is_nat_z_iso.
  Defined.

  Definition weak_relu_square_commutes_identity
             (C'_univ : is_univalent C')
    : (relu_J_to_relu_J' C'_univ ∙ weak_from_reluniv_functor J')
        = (weak_from_reluniv_functor J ∙ weak_reluniv_functor).
  Proof.
    use (isotoid _ (is_univalent_functor_category _ _ _)).
    apply weak_reluniv_cat_is_univalent.
    apply D'cat.
    apply z_iso_from_nat_z_iso.
    apply weak_relu_square_commutes.
  Defined.

  Definition reluniv_functor_with_ess_surj_issurjective_AC
              (C'_univ : is_univalent C')		
              (AC : AxiomOfChoice.AxiomOfChoice)		
              (obC_isaset : isaset C)		
     : issurjective (reluniv_functor_with_ess_surj		
                       _ _ _ _ J J'		
                       R S α α_is_iso		
                       S_pb C'_univ ff_J' S_full R_es		
                    ).		
   Proof.		
     set (W := (weak_from_reluniv_functor J'		
             ,, weak_from_reluniv_functor_is_catiso J' C'_univ ff_J')		
         : catiso _ _).		
     use (Core.issurjective_postcomp_with_weq _ (catiso_ob_weq W)).		
     use (transportf (λ F, issurjective (pr11 F))		
                     (! weak_relu_square_commutes_identity C'_univ)).		
     use issurjcomp.		
     - apply weak_from_reluniv_functor_issurjective.		
       apply AC.		
       apply obC_isaset.		
     - apply issurjectiveweq.		
       apply (catiso_ob_weq (_,,weak_reluniv_functor_is_catiso)).		
   Defined.

End WeakRelUniv_Transfer.

Section RelUniv_Yo_Rezk.

  Context (C : category).
  Let RC : univalent_category := Rezk_completion C.

  Let R := Rezk_eta C.
  Let R_ff := Rezk_eta_fully_faithful C.
  Let R_es := Rezk_eta_essentially_surjective C.
  Let S := Transport_along_Equivs.ext R R_ff R_es.
  Let S_pb := Transport_along_Equivs.preserves_pullbacks_ext R R_ff R_es.
  Let α := Transport_along_Equivs.fi R R_ff R_es.

  Local Definition R_full : full R.
  Proof.
    apply fully_faithful_implies_full_and_faithful, R_ff.
  Defined.

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
           (yoneda_fully_faithful _)
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

  Definition transfer_of_RelUnivYoneda_functor_issurjective
             (AC : AxiomOfChoice.AxiomOfChoice)
             (obC_isaset : isaset C)
    : issurjective transfer_of_RelUnivYoneda_functor.
  Proof.
    use (reluniv_functor_with_ess_surj_issurjective_AC
           _ _ _ _ Yo Yo
           _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        ).
    - apply is_univalent_preShv.
    - apply is_univalent_preShv.
    - apply T.
    - apply epsinv.
    - apply etainv.
    - apply fully_faithful_implies_full_and_faithful.
      apply right_adj_equiv_is_ff.
    - apply R_full.
    - apply AC.
    - apply obC_isaset.
  Defined.

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
    - apply right_adj_equiv_is_full.
    - apply fully_faithful_implies_full_and_faithful.
      apply right_adj_equiv_is_ff.
    - apply R_es.
    - apply R_full.
  Defined.

  Definition transfer_of_WeakRelUnivYoneda_functor_is_catiso
    : is_catiso transfer_of_WeakRelUnivYoneda_functor.
  Proof.
    apply weak_reluniv_functor_is_catiso.
  Defined.

  Definition WeakRelUnivYoneda_functor_square_commutes_identity
    : (transfer_of_RelUnivYoneda_functor ∙ weak_from_reluniv_functor _)
        = (weak_from_reluniv_functor _ ∙ transfer_of_WeakRelUnivYoneda_functor).
  Proof.
    apply weak_relu_square_commutes_identity.
  Defined.

End RelUniv_Yo_Rezk.

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
                (mor : relative_universe_mor _ _ _ u1 u2)
        : relative_universe_mor _ _ _
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
        - unfold is_relative_universe_mor. simpl.
        etrans. apply pathsinv0, functor_comp.
        apply pathsinv0. etrans. apply pathsinv0, functor_comp.
        apply maponpaths, pathsinv0.
        apply (pr2 mor).
    Defined.

    Definition reluniv_functor_data_with_ess_split
                (S_sf : split_full S)
                (R_es : split_ess_surj R)
        : functor_data (@reluniv_cat _ _ J)
                    (@reluniv_cat _ _ J').
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
        use relative_universe_mor_eq.
        - etrans. apply functor_id. apply idpath.
        - etrans. apply functor_id. apply idpath.
    Defined.

    Definition reluniv_functor_compax_with_ess_split
                (S_sf : split_full S)
                (R_es : split_ess_surj R)
        : functor_compax (reluniv_functor_data_with_ess_split S_sf R_es).
    Proof.
        intros a b c f g.
        use relative_universe_mor_eq.
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

    Definition reluniv_is_functor_with_ess_split_is_split_full
               (S_sf : split_full S)
               (R_es : split_ess_surj R)
      : split_full (reluniv_functor_with_ess_split S_sf R_es).
    Proof.
      intros u1 u2 mor.
      use tpair.
      - unfold split_full in S_sf.
        set (fe' := S_sf _ _ (pr11 mor)).
        set (ge' := S_sf _ _ (pr21 mor)).
        use tpair.
        + exact (pr1 fe' , pr1 ge').
        + unfold is_relative_universe_mor.
          simpl.
          (* STUCK: IMPOSSIBLE TO PROVE? *)
          (* I think the problem is that we are not guaranteed
           * that we can find a preimage for all commutative squares
           * that would also be a commutative square *)
    Abort.

    Definition reluniv_is_functor_with_ess_split_is_faithful
               (S_sf : split_full S)
               (R_es : split_ess_surj R)
               (S_faithful : faithful S)
      : faithful (reluniv_functor_with_ess_split S_sf R_es).
    Proof.
      set (F := reluniv_functor_with_ess_split S_sf R_es).
      unfold faithful, isincl, isofhlevelf.
      intros u1 u2 Fg.
      intros [g e_Fg] [g' e_Fg'].
      use tpair.
      - use total2_paths_f.
        + use relative_universe_mor_eq.
          * set (Sk := RelUniv_Cat.F_Ũ _ _ _ (pr1 Fg)).
            set (k := RelUniv_Cat.F_Ũ _ _ _ (pr1 g)).
            set (k' := RelUniv_Cat.F_Ũ _ _ _ (pr1 g')).
            set (e_Sk 
                := maponpaths (λ mor, RelUniv_Cat.F_Ũ _ _ _ (pr1 mor)) e_Fg
                : # S k = Sk).
            set (e_Sk'
                := maponpaths (λ mor, RelUniv_Cat.F_Ũ _ _ _ (pr1 mor)) e_Fg'
                : # S k' = Sk).
            set (H := S_faithful _ _ _ (_ ,, e_Sk) (_ ,, e_Sk')).
            set (e_kk' := maponpaths pr1 (pr1 H)).
            exact e_kk'.
          * set (Sk := RelUniv_Cat.F_U _ _ _ (pr1 Fg)).
            set (k := RelUniv_Cat.F_U _ _ _ (pr1 g)).
            set (k' := RelUniv_Cat.F_U _ _ _ (pr1 g')).
            set (e_Sk 
                := maponpaths (λ mor, RelUniv_Cat.F_U _ _ _ (pr1 mor)) e_Fg
                : # S k = Sk).
            set (e_Sk'
                := maponpaths (λ mor, RelUniv_Cat.F_U _ _ _ (pr1 mor)) e_Fg'
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

  End RelUniv_Transfer_with_ess_split.

  Section RelUniv_Transfer_with_ess_surj.

    Definition reluniv_mor_J_to_J'_with_ess_surj
                (C'_univ : is_univalent C')
                (S_f : full S)
                (R_es : essentially_surjective R)
                (u1 u2 : relative_universe J)
                (mor : relative_universe_mor _ _ _ u1 u2)
        : relative_universe_mor _ _ _
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
        - unfold is_relative_universe_mor. simpl.
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
        use relative_universe_mor_eq.
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
        use relative_universe_mor_eq.
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

    Definition reluniv_is_functor_with_ess_surj_is_full
               (C'_univ : is_univalent C')
               (S_f : full S)
               (R_es : essentially_surjective R)
      : full (reluniv_functor_with_ess_surj C'_univ S_f R_es).
    Proof.
      intros u1 u2 mor.
      (* STUCK: IMPOSSIBLE TO PROVE? *)
      (* I think this will also be impossible
       * for similar reasons as in the proof of
       * [reluniv_is_functor_with_ess_split_is_split_full] *)
    Abort.

  End RelUniv_Transfer_with_ess_surj.

End RelUniv_Transfer.
(**

*)

(**
Contents:

- 
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
    : functor (@reluniv_precat_data _ _ J)
              (@reluniv_precat_data _ _ J').
  Proof.
    use (make_functor (reluniv_functor_data_with_ess_split S_sf R_es)).
    apply (reluniv_is_functor_with_ess_split S_sf R_es).
  Defined.

End RelUniv_Transfer.
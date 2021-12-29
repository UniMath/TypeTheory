
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.All.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheory.

(** * Displayed categories *)

Definition isaprop_is_cartesian_disp_functor
    {C C' : category} {F : functor C C'}
    {D : disp_cat C} {D' : disp_cat C'} {FF : disp_functor F D D'}
  : isaprop (is_cartesian_disp_functor FF).
Proof.
  do 7 (apply impred; intro).
  apply isaprop_is_cartesian.
Qed.

(** * Displayed Equivalences *)

Section Displayed_Equivalences.
(** The total equivalence of a displayed equivalence *)

Definition total_functor_comp
    {C D E : category} {F : functor C D} {G : functor D E} 
    {CC} {DD} {EE} (FF : disp_functor F CC DD) (GG : disp_functor G DD EE)
  : nat_iso
      (total_functor (disp_functor_composite FF GG))
      (functor_composite (total_functor FF) (total_functor GG)).
Proof.
  simple refine (functor_iso_from_pointwise_iso _ _ _ _ _ _ _).
  - use tpair.
    + intros c. apply identity.
    + intros c c' f.
      etrans. { apply id_right. }
      apply pathsinv0, id_left.
  - intros a. apply identity_is_iso.
Defined.

Definition total_functor_id
    {C : category}
    {CC : disp_cat C}
  : nat_iso
      (total_functor (disp_functor_identity CC))
      (functor_identity _).
Proof.
  use functor_iso_from_pointwise_iso.
  - use tpair.
    + intros c. apply identity.
    + intros c c' f.
      etrans. { apply id_right. }
      apply pathsinv0, id_left.
  - intros a. apply identity_is_iso.
Defined.

Definition total_nat_trans
    {C D : category} {F G : functor C D} {α : nat_trans F G}
    {CC} {DD} {FF : disp_functor F CC DD} {GG : disp_functor G CC DD}
    (αα : disp_nat_trans α FF GG)
  : nat_trans (total_functor FF) (total_functor GG).
Proof.
  use tpair.
  { intros c; exists (α (pr1 c)). apply αα. }
  intros c c' f.
  eapply total2_paths_b. apply disp_nat_trans_ax.
Defined.

Definition total_adjunction_data_over_id
    {C} {CC DD : disp_cat C}
    (FG : disp_adjunction_id_data CC DD)
  : adjunction_data (total_category CC) (total_category DD).
Proof.
  exists (total_functor (left_adj_over_id FG)).
  exists (total_functor (right_adj_over_id FG)).
  split.
  - exact (total_nat_trans (unit_over_id FG)).
  - exact (total_nat_trans (counit_over_id FG)).
Defined.

Definition total_forms_adjunction_over_id
    {C} {CC DD : disp_cat C}
    (FG : disp_adjunction_id CC DD)
  : form_adjunction' (total_adjunction_data_over_id FG).
Proof.
  split.
  - intros c; cbn.
    eapply total2_paths_b.
    apply triangle_1_over_id.
  - intros c; cbn.
    eapply total2_paths_b.
    apply triangle_2_over_id.
Qed.

Definition total_adjunction_over_id
    {C} {CC DD : disp_cat C}
    (FG : disp_adjunction_id CC DD)
  : adjunction (total_category CC) (total_category DD).
Proof.
  exists (total_adjunction_data_over_id FG).
  apply total_forms_adjunction_over_id.
Defined.

Definition total_equiv_over_id
    {C} {CC DD : disp_cat C}
    (E : equiv_over_id CC DD)
  : adj_equiv (total_category CC) (total_category DD).
Proof.
  use adj_equiv_from_adjunction.
  - exact (total_adjunction_over_id (adjunction_of_equiv_over_id E)).
  - intros c. simpl.
    use is_iso_total. { apply identity_is_iso. }
    apply is_iso_unit_over_id, axioms_of_equiv_over_id.
  - intros c. simpl.
    use is_iso_total. { apply identity_is_iso. }
    apply is_iso_counit_over_id, axioms_of_equiv_over_id.
Defined.

End Displayed_Equivalences.

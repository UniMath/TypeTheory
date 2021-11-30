(** Some constructions on equivalences (normal and displayed) not yet provided by the UniMath category theory library

TODO: upstream this to UniMath, and possibly propose improvements there as in the notes below. *)

Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.All.

Definition adj_equiv_from_adjunction
    {C D : category}
    (FG : adjunction C D)
    (unit_iso : forall c:C, is_iso (adjunit FG c))
    (counit_iso : forall d:D, is_iso (adjcounit FG d))
  : adj_equiv C D.
Proof.
  exists (left_functor FG).
  use tpair.
  - exists (right_functor FG).
    use tpair.
    + split.
      * exact (adjunit FG).
      * exact (adjcounit FG).
    + exact (pr2 FG).
  - split; cbn.
    + apply unit_iso.
    + apply counit_iso.
Defined.

Definition compose_adj_equiv
    {C D E : category}
    (F : adj_equiv C D)
    (G : adj_equiv D E)
  : adj_equiv C E.
Proof.
  exists (functor_composite F G).
  apply comp_adj_equivalence_of_precats;
    apply adj_equiv_of_precats_from_adj.
Defined.

Definition inv_adj_equiv
    {C D : category}
    (F : adj_equiv C D)
  : adj_equiv D C.
Proof.
  exists (adj_equivalence_inv F).
  apply adj_equivalence_of_precats_inv.
Defined.

Definition nat_trans_from_nat_iso
    {C D : category} {F G : functor C D} (α : nat_iso F G)
  : nat_trans F G
:= pr1 α.
Coercion nat_trans_from_nat_iso : nat_iso >-> nat_trans.


(** The total equivalence of a displayed equivalence *)

Definition total_functor_comp
    {C D E : category} {F : functor C D} {G : functor D E} 
    {CC} {DD} {EE} (FF : disp_functor F CC DD) (GG : disp_functor G DD EE)
  : nat_iso
      (total_functor (disp_functor_composite FF GG))
      (functor_composite (total_functor FF) (total_functor GG)).
Proof.
  use functor_iso_from_pointwise_iso.
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

(* Notes towards some possible improvements in UniMath’s treatment of adjunctions, equivalences (and a few other unrelated things in the library):

  One really confusing point is having
  [adj_equivalence_of_precats] for the property of (or structure on) a functor,
  while
  [equivalence_of_precats] is the sigma-type of this over functors.

  Suggestion:
  - [equivalence] changes to [equiv] throughout (this seems unambiguous?)

  - [adj_equivalence_of_precats]
    changes to either
    [is_adj_equiv] or [adj_equiv_structure]
    (possible also [_of_precats], but this seems reasonably implicit since it’s on a functor) 
  - [equivalence_of_precats]
    changes to [adj_equiv_of_precats]
  - lemmas about them are renamed as consistently as possible, following these.

  - consolidate with the material from [DisplayedCats.Equivalences_bis], including its adj_equiv.

  - projection from an equivalence to its functor is made a coercion?
  - in particular, the confusion about variance for adjoints should be resolved if possible!
  - coercions should respect the fact that equivalences have a primary direction, as do individual adjoints, but “adjunctions” don’t.

  - equivalences should have clear access functions to all components

  Displayed:
  - rename [disp_adjunction_id] -> [disp_adjunction_over_id]

  - add access function for triangle identities of adjunction?
    e.g. coercion [adjunction_property : adjunction -> forms_adjunction]
    and access functions [triangle_1], [triangle_2] from there?


  Unrelated:

  - improve stuff on nat isos?  Move from current location to a more core one, and give good access functions, e.g. use it in lemmase like [functor_iso_from_pointwise_iso]?
  - consolidated things with a “has_homsets” argument to have a “category” argument instead

  - Rename “transportb_transpose_right”.

  - make first arguments of [nat_trans_comp] implicit
*)

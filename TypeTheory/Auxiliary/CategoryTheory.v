(** Some constructions on equivalences not yet provided by the UniMath category theory library *)

Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.All.

(* Draft proposal for naming change in [UniMath]:
  The most confusing point is having
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
*)

Definition adj_equiv_from_adjunction
    {C D : precategory}
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
    {C D E : precategory}
    (F : adj_equiv C D)
    (G : adj_equiv D E)
  : adj_equiv C E.
Proof.
  exists (functor_composite F G).
  apply comp_adj_equivalence_of_precats;
    apply adj_equiv_of_precats_from_adj.
Defined.

Definition inv_adj_equiv
    {C D : precategory}
    (F : adj_equiv C D)
  : adj_equiv D C.
Proof.
  exists (adj_equivalence_inv F).
  apply adj_equivalence_of_precats_inv.
Defined.




(** The total equivalence of a displayed equivalence *)

Definition total_nat_trans
    {C D : category} {F G : functor C D} {α : nat_trans F G}
    {CC} {DD} {FF : disp_functor F CC DD} {GG : disp_functor G CC DD}
    (αα : disp_nat_trans α FF GG)
  : nat_trans (total_functor FF) (total_functor GG).
Proof.
  use tpair.
  { intros c; exists (α (pr1 c)). apply αα. }
  intros c c' f.
  use @total2_paths_f; cbn.
  { apply nat_trans_ax. }
  apply transportf_transpose_left, disp_nat_trans_ax.
Defined.

(* TODO: make first arguments of [nat_trans_comp] implicit *)
Definition total_adjunction_data_over_id
    {C} {CC DD : disp_cat C}
    (FG : disp_adjunction_id_data CC DD)
  : adjunction_data (total_category CC) (total_category DD).
Proof.
  exists (total_functor (left_adj_over_id FG)).
  exists (total_functor (right_adj_over_id FG)).
  split.
  - set (η := total_nat_trans (unit_over_id FG)).
    refine (nat_trans_comp _ _ _ _ (nat_trans_comp _ _ _ η _)).
    + admit. (* TODO: nat iso [total_functor_identity] *)
    + admit. (* TODO: nat iso [total_functor_composite] *)
  - set (ε := total_nat_trans (counit_over_id FG)).
    refine (nat_trans_comp _ _ _ _ (nat_trans_comp _ _ _ ε _)).
    + admit. (* TODO: nat iso [total_functor_identity] *)
    + admit. (* TODO: nat iso [total_functor_composite] *)
Admitted.

Definition total_adjunction_over_id
    {C} {CC DD : disp_cat C}
    (FG : disp_adjunction_id CC DD)
  : adjunction (total_category CC) (total_category DD).
Proof.
  exists (total_adjunction_data_over_id FG).
  admit.
Admitted.

Definition total_equiv_over_id
    {C} {CC DD : disp_cat C}
    (E : equiv_over_id CC DD)
  : adj_equiv (total_category CC) (total_category DD).
Proof.
  use adj_equiv_from_adjunction.
  - exact (total_adjunction_over_id (adjunction_of_equiv_over_id E)).
  - admit.
  - admit.
Admitted.

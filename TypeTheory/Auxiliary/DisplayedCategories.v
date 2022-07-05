
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.All.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheory.

Notation "# F" := (disp_functor_on_morphisms F)
  (at level 3) : mor_disp_scope.

(** * Displayed categories *)

Definition isaprop_is_cartesian_disp_functor
    {C C' : category} {F : functor C C'}
    {D : disp_cat C} {D' : disp_cat C'} {FF : disp_functor F D D'}
  : isaprop (is_cartesian_disp_functor FF).
Proof.
  do 7 (apply impred; intro).
  apply isaprop_is_cartesian.
Qed.

(* The following definition takes unfair advantage of the fact that  [functor_composite (functor_identity _) (functor_identity _)]
  is judgementally(!) equal to [functor_identity _]. *)
Definition disp_functor_id_composite
  {C : category}
  {CC DD EE : disp_cat C}
  (FF : disp_functor (functor_identity _) CC DD)
  (GG : disp_functor (functor_identity _) DD EE)
: disp_functor (functor_identity _) CC EE
:= disp_functor_composite FF GG.

(** * Displayed Equivalences *)

Section Displayed_Equivalences.
(** The total equivalence of a displayed equivalence *)

Definition total_functor_comp
    {C D E : category} {F : functor C D} {G : functor D E} 
    {CC} {DD} {EE} (FF : disp_functor F CC DD) (GG : disp_functor G DD EE)
  : nat_z_iso
      (total_functor (disp_functor_composite FF GG))
      (functor_composite (total_functor FF) (total_functor GG)).
Proof.
  use tpair.
  - use tpair.
    + intros c. apply identity.
    + intros c c' f.
      etrans. { apply id_right. }
      apply pathsinv0, id_left.
  - intros a. apply identity_is_z_iso.
Defined.

Definition total_functor_id
    {C : category}
    {CC : disp_cat C}
  : nat_z_iso
      (total_functor (disp_functor_identity CC))
      (functor_identity _).
Proof.
  use tpair.
  - use tpair.
    + intros c. apply identity.
    + intros c c' f.
      etrans. { apply id_right. }
      apply pathsinv0, id_left.
  - intros a. apply identity_is_z_iso.
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
    use is_z_iso_total. { apply identity_is_z_iso. }
    apply is_z_iso_unit_over_id, axioms_of_equiv_over_id.
  - intros c. simpl.
    use is_z_iso_total. { apply identity_is_z_iso. }
    apply is_z_iso_counit_over_id, axioms_of_equiv_over_id.
Defined.

End Displayed_Equivalences.

(** * Discrete fibrations *) 

Section Discrete_Fibrations.

  (* Some access functions missing upstream *)
  Definition make_discrete_fibration {C} {D} (H : is_discrete_fibration D)
    : discrete_fibration C := (D,,H).

  Coercion discrete_fibration_property {C} {D : discrete_fibration C}
    : is_discrete_fibration D := pr2 D.

  (* arguments tweaked from upstream version, for easier applicability *)
  Definition unique_lift {C} {D : disp_cat C} (H_D : is_discrete_fibration D)
      {c c'} (f : c' --> c) (d : D c)
    : ∃! d' : D c', d' -->[f] d
  := pr1 H_D c c' f d.

  Arguments unique_lift : simpl never.

  Definition lift_source {C} {D : disp_cat C} (H_D : is_discrete_fibration D)
      {c c'} (f : c' --> c) (d : D c)
    : D c'
  := pr1 (iscontrpr1 (unique_lift H_D f d)).

  Definition lift {C} {D : disp_cat C} (H_D : is_discrete_fibration D)
      {c c'} (f : c' --> c) (d : D c)
    : lift_source H_D f d -->[f] d
  := pr2 (iscontrpr1 (unique_lift H_D f d)).

  Definition isaset_fiber_is_discrete_fibration
       {C} {D : disp_cat C} (H_D : is_discrete_fibration D) (c : C)
    : isaset (D c)
  := pr2 H_D c.

  Definition unique_lift_is_cartesian
             {C : category}
             {D : discrete_fibration C} {c c'}
             (f : c' --> c) (d : D c)
    : is_cartesian (pr2 (pr1 (unique_lift D f d))).
  Proof.
    apply (pr2 (pr2 (fibration_from_discrete_fibration _ D _ _ _ _))).
  Defined.

  (* useful for situations when a particularly canonical lift is known *)
  Definition unique_lift_explicit
             {C : category}
             {D : disp_cat C}
             (is_discrete_fibration_D : is_discrete_fibration D) {c c'}
             {d : D c} {f : c' --> c} (d' : D c') (ff : d' -->[f] d)
    : ∃! (d' : D c'), d' -->[f] d.
  Proof.
    exists (d' ,, ff).
    intros X.
    apply isapropifcontr, unique_lift, is_discrete_fibration_D.
  Defined.

  Definition unique_lift_explicit_eq
             {C : category}
             {D : disp_cat C}
             (is_discrete_fibration_D : is_discrete_fibration D) {c c'}
             {d : D c} {f : c' --> c} (d' : D c') (ff : d' -->[f] d)
    : pr1 is_discrete_fibration_D _ _ f d
      = unique_lift_explicit is_discrete_fibration_D d' ff.
  Proof.
    apply isapropiscontr.
  Defined.

  Definition unique_lift_identity
             {C : category}
             {D : disp_cat C}
             (is_discrete_fibration_D : is_discrete_fibration D) {c}
             (d : D c)
    : ∃! (d' : D c), d' -->[identity c] d.
  Proof.
    apply (unique_lift_explicit is_discrete_fibration_D d).
    apply id_disp.
  Defined.

  Definition unique_lift_id
             {C : category}
             {D : disp_cat C}
             (is_discrete_fibration_D : is_discrete_fibration D) {c}
             (d : D c)
    : unique_lift is_discrete_fibration_D (identity c) d
      = unique_lift_identity is_discrete_fibration_D d.
  Proof.
    apply isapropiscontr.
  Defined.

  Definition unique_lift_compose
             {C : category}
             {D : disp_cat C}
             (is_discrete_fibration_D : is_discrete_fibration D) {c c' c''}
             (f : c' --> c) (g : c'' --> c')
             (d : D c)
    : ∃! (d'' : D c''), d'' -->[g ;; f] d.
  Proof.
    eapply unique_lift_explicit; try assumption.
    refine (_;;_)%mor_disp; apply (lift is_discrete_fibration_D).
  Defined.

  Definition unique_lift_comp
             {C : category}
             {D : disp_cat C}
             (is_discrete_fibration_D : is_discrete_fibration D) {c c' c''}
             (f : c' --> c) (g : c'' --> c')
             (d : D c)
    : unique_lift is_discrete_fibration_D (g ;; f) d
      = unique_lift_compose is_discrete_fibration_D f g d.
  Proof.
    apply isapropiscontr.
  Defined.

  Definition discrete_fibration_mor_weq
             {C : category}
             {D : disp_cat C}
             (is_discrete_fibration_D : is_discrete_fibration D) {c c'}
             (f : c' --> c) (d : D c) (d' : D c')
    : (d' -->[f] d) ≃ (lift_source is_discrete_fibration_D f d = d').
  Proof.
    set (uf := unique_lift is_discrete_fibration_D f d).
    use weq_iso.
    - intros ff. apply (maponpaths pr1 (! pr2 uf (d' ,, ff))).
    - intros p. apply (transportf _ p (pr2 (pr1 uf))).
    - intros ff. simpl.
      refine (@fiber_paths _ (λ d'', d'' -->[ f] d) _ (_,,_) _).
    - intros ?. apply isaset_fiber_is_discrete_fibration; assumption.
  Defined.

  Definition discrete_fibration_mor
             {C : category}
             {D : disp_cat C}
             (is_discrete_fibration_D : is_discrete_fibration D) {c c'}
             (f : c' --> c) (d : D c) (d' : D c')
    : (d' -->[f] d) = (lift_source is_discrete_fibration_D f d = d').
  Proof.
    apply univalenceweq.
    apply discrete_fibration_mor_weq.
  Defined.

  Definition isaprop_mor_disp_of_discrete_fibration
             {C : category}
             {D : disp_cat C}
             (is_discrete_fibration_D : is_discrete_fibration D) {c c'}
             (f : c' --> c) (d : D c) (d' : D c')
    : isaprop (d' -->[f] d).
  Proof.
    eapply isofhlevelweqb. { use discrete_fibration_mor_weq; assumption. }
    apply isaset_fiber_is_discrete_fibration; eassumption.
  Qed.

  Definition isaprop_disp_id_comp_of_discrete_fibration
             {C : category}
             {D : disp_cat C}
             (is_discrete_fibration_D : is_discrete_fibration D)
    : isaprop (disp_cat_id_comp C D).
  Proof.
    use isapropdirprod.
    - repeat (apply impred_isaprop; intro).
      apply isaprop_mor_disp_of_discrete_fibration; assumption.
    - repeat (apply impred_isaprop; intro).
      apply isaprop_mor_disp_of_discrete_fibration; assumption.
  Qed.

  Definition isaprop_is_discrete_fibration
             {C : category}
             (D : disp_cat C)
    : isaprop (is_discrete_fibration D).
  Proof.
    use isapropdirprod.
    - repeat (apply impred_isaprop; intro).
      apply isapropiscontr.
    - apply impred_isaprop; intro.
      apply isapropisaset.
  Qed.

End Discrete_Fibrations.

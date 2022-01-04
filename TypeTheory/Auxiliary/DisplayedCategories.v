
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

(** * Discrete fibrations *) 

Section Discrete_Fibrations.

  Definition unique_lift_is_cartesian
             {C : category}
             {D : discrete_fibration C} {c c'}
             (f : c' --> c) (d : D c)
    : is_cartesian (pr2 (pr1 (unique_lift f d))).
  Proof.
    apply (pr2 (pr2 (fibration_from_discrete_fibration _ D _ _ f d))).
  Defined.

  Definition unique_lift_explicit
             {C : category}
             {D : disp_cat C}
             (is_discrete_fibration_D : is_discrete_fibration D) {c c'}
             {d : D c} {f : c' --> c} (d' : D c') (ff : d' -->[f] d)
    : ∃! (d' : D c'), d' -->[f] d.
  Proof.
    exists (d' ,, ff).
    intros X.
    etrans. apply (pr2 (pr1 is_discrete_fibration_D _ _ f d)).
    apply pathsinv0, (pr2 (pr1 is_discrete_fibration_D _ _ f d)).
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
    : pr1 is_discrete_fibration_D _ _ (identity c) d
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
    set (d'ff := pr1 is_discrete_fibration_D _ _ f d).
    set (d' := pr1 (pr1 d'ff)).
    set (ff := pr2 (pr1 d'ff)).
    set (d''gg := pr1 is_discrete_fibration_D _ _ g d').
    set (d'' := pr1 (pr1 d''gg)).
    set (gg := pr2 (pr1 d''gg)).

    use (unique_lift_explicit is_discrete_fibration_D d'' (gg ;; ff)%mor_disp).
  Defined.

  Definition unique_lift_comp
             {C : category}
             {D : disp_cat C}
             (is_discrete_fibration_D : is_discrete_fibration D) {c c' c''}
             (f : c' --> c) (g : c'' --> c')
             (d : D c)
    : pr1 is_discrete_fibration_D _ _ (g ;; f) d
      = unique_lift_compose is_discrete_fibration_D f g d.
  Proof.
    apply isapropiscontr.
  Defined.

  Definition discrete_fibration_mor_weq
             {C : category}
             {D : disp_cat C}
             (is_discrete_fibration_D : is_discrete_fibration D) {c c'}
             (f : c' --> c) (d : D c) (d' : D c')
    : (d' -->[f] d) ≃ (pr1 (pr1 (pr1 is_discrete_fibration_D c c' f d)) = d').
  Proof.
    set (uf := pr1 is_discrete_fibration_D c c' f d).
    use weq_iso.
    - intros ff. apply (maponpaths pr1 (! pr2 uf (d' ,, ff))).
    - intros p. apply (transportf _ p (pr2 (pr1 uf))).
    - intros ff. simpl.
      induction (! unique_lift_explicit_eq is_discrete_fibration_D d' ff
                : unique_lift_explicit _ d' ff = uf).
      simpl.
      etrans. apply maponpaths_2, maponpaths, maponpaths.
      apply pathsinv0r.
      apply idpath.
    - intros ?. apply (pr2 is_discrete_fibration_D).
  Defined.

  Definition discrete_fibration_mor
             {C : category}
             {D : disp_cat C}
             (is_discrete_fibration_D : is_discrete_fibration D) {c c'}
             (f : c' --> c) (d : D c) (d' : D c')
    : (d' -->[f] d) = (pr1 (pr1 (pr1 is_discrete_fibration_D c c' f d)) = d').
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
    induction (! discrete_fibration_mor is_discrete_fibration_D f d d').
    apply (pr2 is_discrete_fibration_D).
  Qed.

  Definition isaprop_disp_id_comp_of_discrete_fibration
             {C : category}
             {D : disp_cat C}
             (is_discrete_fibration_D : is_discrete_fibration D)
    : isaprop (disp_cat_id_comp C D).
  Proof.
    use isapropdirprod.
    - apply impred_isaprop. intros ?.
      apply impred_isaprop. intros ?.
      apply isaprop_mor_disp_of_discrete_fibration.
      apply is_discrete_fibration_D.
    - apply impred_isaprop. intros ?.
      apply impred_isaprop. intros ?.
      apply impred_isaprop. intros ?.
      apply impred_isaprop. intros ?.
      apply impred_isaprop. intros ?.
      apply impred_isaprop. intros ?.
      apply impred_isaprop. intros ?.
      apply impred_isaprop. intros ?.
      apply impred_isaprop. intros ?.
      apply impred_isaprop. intros ?.
      apply isaprop_mor_disp_of_discrete_fibration.
      apply is_discrete_fibration_D.
  Qed.

  Definition isaprop_is_discrete_fibration
             {C : category}
             (D : disp_cat C)
    : isaprop (is_discrete_fibration D).
  Proof.
    use isapropdirprod.
    - apply impred_isaprop. intros ?.
      apply impred_isaprop. intros ?.
      apply impred_isaprop. intros ?.
      apply impred_isaprop. intros ?.
      apply isapropiscontr.
    - apply impred_isaprop. intros ?.
      apply isapropisaset.
  Qed.

End Discrete_Fibrations.

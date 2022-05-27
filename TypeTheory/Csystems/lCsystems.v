(** ** lCsystems *)

(**
by Vladimir Voevodsky, split off the file lCsystems.v on March 5, 2015.

We refer below to the paper "Subsystems and regular quotients of C-systems"
by V. Voevodsky as "Csubsystems".

The definition of an lC-system given below does not require that the types of objects or morphisms
of the underlying precategory form a set. It also does not require the
properties of the identity morphisms but does require associativity. 


The section Pullbacks (in particular Lemma q_of_f_is_pullback and
Lemma lCsystem_from_lC0system_where_q_of_f_is_pullback) has been
added by Ralph Matthes in May 2018.
*)


Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.
Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheory.
Require Export TypeTheory.Csystems.lC0systems.

Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.MoreFoundations.PartA.


(** *** The l-C-systems *)


(** **** l-C-system data *) 

Definition sf_type ( CC : lC0system_data ) :=
  forall ( Y X : CC ) ( gt0 : ll X > 0 ) ( f : Y --> X ), sec_pX ( f_star gt0 ( ftf f ) ).

Definition lCsystem_data := ∑ CC : lC0system_data, sf_type CC.

Definition lCsystem_data_constr { CC : lC0system_data }
  ( sf0 : sf_type CC ) : lCsystem_data := tpair _ _ sf0 . 

Definition lCsystem_data_pr1 : lCsystem_data -> lC0system_data := pr1.
Coercion lCsystem_data_pr1 : lCsystem_data >-> lC0system_data.

Definition sf_from_data { CC : lCsystem_data } { Y X : CC }
  ( gt0 : ll X > 0 ) ( f : Y --> X ):
  sec_pX ( f_star gt0 ( ftf f ) ) := pr2 CC Y X gt0 f.


(** **** Properties on l-C-system data that later become axioms of l-C-systems. *)


Definition sf_ax1_type { CC : lC0system } ( sf0 : sf_type CC ) :=
  forall ( Y X : CC ) ( gt0 : ll X > 0 ) ( f : Y --> X ),
    ( C0eiso gt0 ( ftf f ) ) · f = ( sf0 _ _ gt0 f ) · ( q_of_f gt0 (ftf f) ).

Definition sf_ax2_type_l1_lhs { CC : lC0system } ( sf0 : sf_type CC )
      { Y Y' U : CC } ( gt0 : ll U > 0 )
      ( g : Y' --> ft U ) ( f : Y --> f_star gt0 g ): CC :=
      f_star (C0ax5a gt0 g) (ftf f).


Definition sf_ax2_type_l1_rhs { CC : lC0system } ( sf0 : sf_type CC )
      { Y Y' U : CC } ( gt0 : ll U > 0 )
      ( g : Y' --> ft U ) ( f : Y --> f_star gt0 g ): CC :=
      f_star gt0 (ftf(f · q_of_f gt0 g)).

(* not needed later! *)
Lemma sf_ax2_type_l1_lhs_depends_only_on_ftf_f { CC : lC0system } ( sf0 : sf_type CC )
      { Y Y' U : CC } ( gt0 : ll U > 0 )
      ( g : Y' --> ft U ) ( f f' : Y --> f_star gt0 g ):
      ftf f = ftf f' ->
      sf_ax2_type_l1_lhs sf0 gt0 g f = sf_ax2_type_l1_lhs sf0 gt0 g f'.
Proof.
  intro Hyp.
  unfold sf_ax2_type_l1_lhs.
  rewrite Hyp.
  apply idpath.
Qed.

(* not needed later! *)
Lemma sf_ax2_type_l1_rhs_depends_only_on_ftf_f { CC : lC0system } ( sf0 : sf_type CC )
      { Y Y' U : CC } ( gt0 : ll U > 0 )
      ( g : Y' --> ft U ) ( f f' : Y --> f_star gt0 g ):
      ftf f = ftf f' ->
      sf_ax2_type_l1_rhs sf0 gt0 g f = sf_ax2_type_l1_rhs sf0 gt0 g f'.
Proof.
  intro Hyp.
  unfold sf_ax2_type_l1_rhs.
  apply maponpaths.
  unfold ftf.
  do 2 rewrite <- assoc.
  etrans.
  { eapply cancel_precomposition.
    apply pathsinv0.
    apply (C0ax5c gt0 g).
  }
  apply pathsinv0.
  etrans.
  { eapply cancel_precomposition.
    apply pathsinv0.
    apply (C0ax5c gt0 g).
  }
  do 4 rewrite assoc.
  unfold ftf in Hyp.
  rewrite Hyp.
  apply idpath.
Defined.



Lemma sf_ax2_type_l1 { CC : lC0system } ( sf0 : sf_type CC )
      { Y Y' U : CC } ( gt0 : ll U > 0 )
      ( g : Y' --> ft U ) ( f : Y --> f_star gt0 g ):
      sf_ax2_type_l1_lhs sf0 gt0 g f = sf_ax2_type_l1_rhs sf0 gt0 g f.
Proof.
  assert ( int1 : f_star (C0ax5a gt0 g) (ftf f) =
                  f_star gt0 ( ( ftf f ) · ( ( C0eiso gt0 g ) · g ) ) )
  by apply C0ax7a.

  assert ( int2 : f_star gt0 ( ( ftf f ) · ( ( C0eiso gt0 g ) · g ) ) =
                  f_star gt0 ( f · ( ( pX _ ) · ( ( C0eiso gt0 g ) · g ) ) ) ).
  { unfold ftf.
    rewrite <- assoc. 
    apply idpath.
  }
  assert ( int3 : f_star gt0 ( f · ( ( pX _ ) · ( ( C0eiso gt0 g ) · g ) ) ) =
                  f_star gt0 ( f · ( ( q_of_f gt0 g ) · ( pX U ) ) ) ).
  { unfold ftf.
    rewrite C0ax5c.
    apply idpath. 
  }
  assert ( int4 : f_star gt0 ( f · ( ( q_of_f gt0 g ) · ( pX U ) ) ) =
                  f_star gt0 (ftf (f · q_of_f gt0 g)) ).
  { unfold ftf.
    rewrite assoc.
    apply idpath. 
  }
  exact ( ( int1 @ int2 ) @ ( int3 @ int4 ) ). 
Defined.


Definition sf_ax2_type { CC : lC0system } ( sf : sf_type CC ) :=
  forall ( Y Y' U : CC ) ( gt0 : ll U > 0 )
    ( g : Y' --> ft U ) ( f : Y --> f_star gt0 g ),
    transportf sec_pX
               (sf_ax2_type_l1 sf gt0 g f )
               ( sf Y (f_star gt0 g) ( C0ax5a gt0 g ) f ) =
    sf Y U gt0 ( f · q_of_f gt0 g ).


(** **** The definition of the type of l-C-systems *)

Definition lCsystem :=
             ∑ (CC : lC0system) (sf0 : sf_type CC),
                        ( sf_ax1_type sf0 ) × ( sf_ax2_type sf0 ).

Definition lCsystem_pr1: lCsystem -> lC0system := pr1.
Coercion lCsystem_pr1: lCsystem >-> lC0system.

Definition lCsystem_to_lCsystem_data ( CC : lCsystem ): lCsystem_data :=
  @lCsystem_data_constr CC ( pr1 ( pr2 CC ) ).
Coercion lCsystem_to_lCsystem_data : lCsystem >-> lCsystem_data.

Definition sf { CC : lCsystem } { Y X : CC } ( gt0 : ll X > 0 ) ( f : Y --> X ):
  sec_pX ( f_star gt0 ( ftf f ) ) := ( pr1 ( pr2 CC ) ) Y X gt0 f. 

Definition sf_ax1 { CC : lCsystem } { Y X : CC } ( gt0 : ll X > 0 ) ( f : Y --> X ):
  ( C0eiso gt0 ( ftf f ) ) · f  = ( sf gt0 f ) · ( q_of_f gt0 ( ftf f ) ) :=
  pr1 ( pr2 ( pr2 CC ) ) Y X gt0 f.

Definition sf_ax2 { CC : lCsystem } { Y Y' U : CC } ( gt0 : ll U > 0 )
           ( g : Y' --> ft U ) ( f : Y --> f_star gt0 g ):
  transportf sec_pX
             (sf_ax2_type_l1 ( @sf CC ) gt0 g f )
             ( sf ( C0ax5a gt0 g ) f ) =
  sf gt0 ( f · q_of_f gt0 g ) :=
  pr2 ( pr2 ( pr2 CC ) ) Y Y' U gt0 g f.


(** **** Operation f_star_of_s *)

Definition f_star_of_s { CC : lCsystem } { Y X : CC } ( f : Y --> ft X )
  ( gt0 : ll X > 0 ) ( s : sec_pX X ): sec_pX ( f_star gt0 f ). 
Proof.
  set ( int := sf gt0 ( f · s ) ).
  assert ( inteq : ftf ( f · s ) = f ).
  { unfold ftf. 
    rewrite <- assoc.
    set ( eq := sec_pX_eq s : (s · pX X)= _).
    change ( f · (s · pX X ) = f ).
    rewrite eq.
    apply id_right. 
  }
  rewrite inteq in int. 
  exact int. 
Defined.
  

(** **** Operation fsn_star_of_s *)


Definition fsn_star_of_s { CC : lCsystem } { A X : CC } ( f : mor_to A )
  ( isab : isabove X A ) ( r : sec_pX X ) : sec_pX ( fn_star f isab ).  
Proof.
  rewrite f_star_isab.
  apply f_star_of_s. 
  exact r.
Defined.

   
(*

                                
(** *** Operations qn, fn_star and f_star_of_s and fn_star_of_s  *)


(** **** Operations qn and fn_star *)

Definition qn { CC : lC0system_data } { Y A : CC } ( f : Y --> A ) ( n : nat ) 
           { X : CC } ( gtn : ll X >= n ) ( eq : ftn n X = A )  : mor_to X .
Proof.
  intros until n . 
  induction n as [ | n IHn ] .
  intros . 
  change _ with ( X = A ) in eq . 
  apply ( mor_to_constr ( f ;; id_to_mor ( ! eq ) ) ) . 

  intros .

  set ( int := ftn_ft n X : ftn n ( ft X ) = ftn ( 1 + n ) X ) .
  set ( gt0 := natgehgthtrans _ _ _ gtn ( natgthsn0 _ ) ) . 
  apply ( q_of_f gt0 ( IHn ( ft X ) ( ll_ft_gtn gtn ) ( int @ eq ) ) ) . 

Defined.

Lemma qn_equals_qn { CC : lC0system_data } ( is : isaset CC )
      { Y A : CC } ( f : Y --> A )
      { n1 n2 : nat } ( eqn : n1 = n2 ) 
      { X : CC }
      ( gtn1 : ll X >= n1 ) ( gtn2 : ll X >= n2 )
      ( eq1 : ftn n1 X = A ) ( eq2 : ftn n2 X = A ) :
  qn f n1 gtn1 eq1 = qn f n2 gtn2 eq2 .
Proof.
  intros until n2 . 
  intro eqn . 
  rewrite eqn .
  intros until gtn2 . 
  assert ( eq : gtn1 = gtn2 ) .  apply ( proofirrelevance _ ( pr2 ( _ >= _ ) ) ) . 
  rewrite eq . 
  intros eq1 eq2 . 
  assert ( eq' : eq1 = eq2 ) .
  apply is . 
  rewrite eq' . 
  apply idpath .

Defined.



      

Definition qsn { CC : lC0system_data } { Y A : CC } ( f : Y --> A ) ( n : nat ) 
      { X : CC } ( gtsn : ll X >= S n ) ( eq : ftn (S n) X = A )  :
  qn f ( S n ) gtsn eq =
  q_of_f (natgehgthtrans _ _ _ gtsn ( natgthsn0 _ ))
         ( qn f n ( ll_ft_gtn gtsn ) ( ( ftn_ft n X ) @ eq ) ) :=
  idpath _ . 


Definition fn_star { CC : lC0system_data } { Y A : CC } ( f : Y --> A ) ( n : nat ) 
           { X : CC } ( gtn : ll X >= n ) ( eq : ftn n X = A ) : CC := pr1 ( qn f n gtn eq ) .

Definition fsn { CC : lC0system_data } { Y A : CC } ( f : Y --> A ) ( n : nat ) 
           { X : CC } ( gtsn : ll X >= S n ) ( eq : ftn ( S n ) X = A ) :
  fn_star f ( S n ) gtsn eq =
  f_star (natgehgthtrans _ _ _ gtsn ( natgthsn0 _ ))
         ( qn f n ( ll_ft_gtn gtsn ) ( ( ftn_ft n X ) @ eq ) ) :=
  idpath _ .



Lemma ll_fn_star { CC : lC0system } { Y A : CC } ( f : Y --> A ) ( n : nat ) 
      { X : CC } ( gtn : ll X >= n ) ( eq : ftn n X = A ) :
  ll ( fn_star f n gtn eq ) = ll Y + n . 
Proof.
  intros until n . induction n as [ | n IHn ] .
  intros .
  rewrite natplusr0 . apply idpath .

  intros . 
  change ( ll ( fn_star _ _ _ _ ) ) with ( ll ( f_star (natgehgthtrans _ _ _ gtn ( natgthsn0 _ ))
         ( qn f n ( ll_ft_gtn gtn ) ( ( ftn_ft n X ) @ eq ) ) ) ) . 
  rewrite ll_f_star .
  unfold fn_star in IHn . rewrite IHn .
  apply ( ! ( natplusnsm ( ll Y ) n ) ) . 

Defined.

Lemma isover_fn_star { CC : lC0system } { Y A : CC } ( f : Y --> A ) ( n : nat ) 
      { X : CC } ( gtn : ll X >= n ) ( eq : ftn n X = A ) : isover ( fn_star f n gtn eq ) Y .
Proof.
  intros until n .  induction n as [ | n IHn ] .
  intros .  apply isover_XX . 

  intros .
  refine ( isover_trans ( isover_X_ftX _ ) _ ) . 
  change (fn_star f (S n) gtn eq) with ( f_star (natgehgthtrans _ _ _ gtn ( natgthsn0 _ ))
                                                ( qn f n ( ll_ft_gtn gtn ) ( ( ftn_ft n X ) @ eq ) ) ) .
  rewrite ft_f_star .
  apply IHn . 

Defined.



  

(** **** Operation f_star_of_s *)

Definition f_star_of_s { CC : lCsystem } { Y X : CC } ( f : Y --> ft X )
           ( gt0 : ll X > 0 ) ( r : sec_pX X ) :
  sec_pX ( f_star gt0 f ) . 
Proof .
  intros . 
  assert ( int := sf gt0 ( f ;; r ) ) .  
  assert ( inteq : ftf ( f ;; r ) = f ) . 
  unfold ftf . 
  rewrite <- assoc.
  set ( eq := sec_pX_eq r : (r;; pX X)= _) . 
  change ( f ;; (r ;; pX X ) = f ) .  
  rewrite eq .
  apply id_right . 

  rewrite inteq in int . 
  apply int . 

Defined.

  

(** **** Operation fsn_start_of_s *)


Definition fsn_star_of_s { CC : lCsystem } { Y A : CC } ( f : Y --> A ) ( n : nat ) 
           { X : CC } ( gtsn : ll X >= 1 + n ) ( eq : ftn ( 1 + n ) X = A ) ( r : sec_pX X ) :
  sec_pX ( fn_star f ( 1 + n ) gtsn eq ) .  
Proof .
  intros.
  set ( int := ftn_ft n X : ftn n ( ft X ) = ftn ( 1 + n ) X ) .
  set ( gt0 := natgehgthtrans _ _ _ gtsn ( natgthsn0 _ ) ) .
  set ( qnint :=   qn f n ( ll_ft_gtn gtsn ) ( int @ eq ) : mor_to ( ft X ) ) . 
  change ( fn_star f ( 1 + n ) gtsn eq ) with ( f_star gt0 qnint ) .
  apply ( f_star_of_s qnint gt0 r ) . 

Defined.


*)

Section Pullbacks.
(** *** the square expressed in [C0ax5c_type] is even a pullback in every C-system *)

(**
  This corresponds to the direction from 2 to 1 of Prop. 2.4 of "Csubsystems".

  The other direction is dealt with further below.
*)

(** show that [g] is determined by [g · q_of_f gt0 f] and [ftf g] - unfortunately, [g] alone enters as argument of [sf_ax2_type_l1] *)
Lemma injectionprop2_4 {CC: lCsystem}{X Y Z: CC}
  (gt0: ll X > 0) (f: Y --> ft X) (g: Z --> f_star gt0 f):
  g = C0eiso_inv (C0ax5a gt0 f) (ftf g) ·
      (transportb _ (sf_ax2_type_l1 (@sf CC) gt0 f g)) (sf gt0 (g · q_of_f gt0 f)) ·
      (q_of_f (C0ax5a gt0 f) (ftf g)).
Proof.
  rewrite <- sf_ax2.
  rewrite transport_b_f.
  rewrite pathsinv0r.
  rewrite idpath_transportf.
  rewrite <- assoc.
  simpl.
  apply pathsinv0.
  apply z_iso_inv_on_right.
  apply pathsinv0.
  etrans.
  - eapply (sf_ax1 (C0ax5a gt0 f) g).
  - apply idpath.
Qed.

(** the following ought to be a simple corollary, but needs more work in the formalization than on paper since the types depend on the objects in the equations *)
Lemma injectionprop2_4_cor {CC: lCsystem}{X Y Z: CC}
  (gt0: ll X > 0)(f: Y --> ft X) (g g': Z --> f_star gt0 f):
  g · q_of_f gt0 f = g' · q_of_f gt0 f -> ftf g = ftf g' -> g = g'.
Proof.
  intros Hyp1 Hyp2.
  rewrite injectionprop2_4.
  rewrite (injectionprop2_4 _ _ g).
  do 2 rewrite <- assoc.
  etrans.
  { apply cancel_postcomposition.
    apply maponpaths. (* needed to use the specialized lemma *)
    set (piso := fun h: CC ⟦ Z, ft(f_star gt0 f) ⟧ =>
                   C0eiso_inv (C0ax5a gt0 f) h).
    apply (eq_par_iso_cor _ _ piso Hyp2).
  }
  simpl.
  rewrite maponpaths_for_constant_function.
  do 2 rewrite <- assoc.
  rewrite id_left.
  apply cancel_precomposition.
  rewrite assoc.
  etrans.
  { apply cancel_precomposition.
    set (par := fun h: CC ⟦ Z, ft (f_star gt0 f) ⟧ =>
                  mor_to_pr2 _ (q_of_f (C0ax5a gt0 f) h)).
    exact (eq_par_arrow_cor _ _ par Hyp2).

    (* I would have preferred to use the specialized lemma as follows:
    set (pmorto := fun h: CC ⟦ Z, ft (f_star gt0 f) ⟧ => q_of_f (C0ax5a gt0 f) h).
    exact (eq_p_to_mor_cor _ pmorto Hyp2).
      However, I do not know how to instruct Coq to work on the level of
      mor_to - the goal hides the coercion to the underlying morphism! *)
  }
  rewrite maponpaths_for_constant_function.
  rewrite id_right.
  rewrite <- assoc.
  apply z_iso_inv_on_right.

  do 2 rewrite assoc.
  apply cancel_postcomposition.

  etrans.
  { apply cancel_postcomposition.
    UniMath.MoreFoundations.Tactics.show_id_type.
    (* shows that the term is coerced to its underlying morphism *)
    apply maponpaths.
    apply maponpaths.
    set (psecpnX := fun h: CC ⟦ Z, X ⟧ => sf gt0 h).
    apply (eq_p_sec_pnX_cor _ psecpnX Hyp1).
  }

  etrans.
  { apply cancel_postcomposition.
    apply pathsinv0.
    set (pr := fun X: CC => sec_pnX_to_mor 1 X).
    apply (transportb_map pr).
  }
  rewrite transportb_source_target_simple.
  unfold eq_p_sec_pnX_cor_rhs; simpl.

  apply pathsinv0.
  etrans.
  { apply cancel_precomposition.
    apply pathsinv0.
    set (pr := fun X: CC => sec_pnX_to_mor 1 X).
    apply (transportb_map pr).
  }
  rewrite transportb_source_target_simple.

  apply pathsinv0.
  do 4 rewrite assoc.
  apply z_iso_inv_on_left.
  do 2 rewrite <- idtoiso_inv0.

  rewrite <- idtoiso_concat0.

  do 3 rewrite <- assoc.
  do 4 rewrite <- idtoiso_concat0.

  apply cancelidtoiso_right_cor.
  { apply (isaset_ob CC). }
  apply cancelidtoiso_left.
  { apply (isaset_ob CC). }
  apply idpath.
Qed.

(** now, the pullback property is still cumbersome *)
Definition pullback_to_q_of_f {CC: lCsystem}{X Y Z: CC}
  (gt0: ll X > 0)(f: Y --> ft X)
  (g1: Z --> ft (f_star gt0 f))(g2: Z --> X)
  (pbeq: g1 · (C0eiso gt0 f · f) = g2 · pnX 1 X): Z --> f_star gt0 f :=
  C0eiso_inv gt0 (ftf(g2)) ·
  (sf gt0 g2) ·
  z_iso_inv_from_z_iso (idtoiso (maponpaths (f_star gt0) pbeq)) ·
  z_iso_inv_from_z_iso (idtoiso (C0ax7a gt0 f g1)) ·
  (q_of_f (C0ax5a gt0 f) g1).


Lemma pullback_to_q_of_f_ok {CC: lCsystem}{X Y Z: CC}
  (gt0: ll X > 0)(f: Y --> ft X)
  (g1: Z --> ft (f_star gt0 f))(g2: Z --> X)
  (pbeq: g1 · (C0eiso gt0 f · f) = g2 · pnX 1 X):
  pullback_to_q_of_f gt0 f g1 g2 pbeq · pnX 1 (f_star gt0 f) = g1 ×
  pullback_to_q_of_f gt0 f g1 g2 pbeq · q_of_f gt0 f = g2.
Proof.
  use tpair; unfold pullback_to_q_of_f; simpl.
  - do 4 rewrite <- assoc.
    etrans.
    { do 4 apply cancel_precomposition.
      apply pathsinv0.
      apply C0ax5c.
    }
    apply z_iso_inv_on_right.
    do 4 rewrite assoc.
    apply cancel_postcomposition.

    apply pathsinv0.
    etrans.
    { apply pathsinv0.
      apply id_left. }
    apply z_iso_inv_to_right.
    etrans.
    { apply pathsinv0.
      apply (sec_pnX_eq (sf gt0 g2)). }
    do 4 rewrite <- assoc.
    apply cancel_precomposition.
    apply pathsinv0.
    do 3 rewrite assoc.
    etrans.
    { do 3 apply cancel_postcomposition.
      UniMath.MoreFoundations.Tactics.show_id_type.
      do 2 rewrite <- idtoiso_inv0.
      apply pathsinv0.
      apply idtoiso_concat0.
    }
    do 2 rewrite <- assoc.
    etrans.
    { do 2 apply cancel_precomposition.
      unfold C0ax5b_z_iso.
      rewrite <- idtoiso_inv0.
      unfold C0eiso.
      unfold C0ax5b_z_iso.
      apply pathsinv0.
      apply idtoiso_concat0.
    }
    apply pathsinv0.
    rewrite assoc.
    assert (e: f_star gt0 (ftf g2) = f_star (C0ax5a gt0 f) g1)
    by exact (! maponpaths (f_star gt0) pbeq @ ! C0ax7a gt0 f g1).
    apply (eq_par_arrow_cor_objirr (isaset_ob CC) _ _ (pnX 1) e).
  - apply (pre_comp_with_z_iso_is_inj (C0eiso gt0 (ftf g2))).
    apply pathsinv0.
    etrans.
    { apply sf_ax1. }
    repeat rewrite <- assoc.
    apply z_iso_inv_to_left.
    apply cancel_precomposition.
    apply cancel_precomposition.
    apply pathsinv0.
    apply z_iso_inv_on_right.
    change (g1 · (C0eiso gt0 f · f) = ftf g2) in pbeq.
    apply pathsinv0.
    etrans.
    { apply pathsinv0.
      set (par := fun h: CC ⟦ Z, ft X ⟧ => mor_to_pr2 _ (q_of_f gt0 h)).
      apply (eq_par_arrow _ _ par pbeq).
    }
    simpl.
    etrans.
    { apply cancel_postcomposition.
      apply pathsinv0.
      UniMath.MoreFoundations.Tactics.show_id_type.
      apply (fiber_paths (C0ax7 gt0 f g1)).
    }
    simpl.
    rewrite transportf_source_target_simple.
    do 2 rewrite maponpaths_for_constant_function.
    rewrite idtoiso_idpath.
    do 2 rewrite id_right.
    apply z_iso_inv_on_right.
    rewrite <- idtoiso_inv0.
    rewrite assoc.
    rewrite <- idtoiso_concat0.
    apply cancelidtoiso_left_cor.
    { apply (isaset_ob CC). }
    apply idpath.
Qed.

Definition q_of_f_is_pullback_type {CC: lC0system}{X Y: CC}
  (gt0: ll X > 0)(f: Y --> ft X): UU :=
  isPullback (C0ax5c gt0 f).

Lemma q_of_f_is_pullback {CC: lCsystem}{X Y: CC} (gt0: ll X > 0)(f: Y --> ft X):
  q_of_f_is_pullback_type gt0 f.
Proof.
  do 2 red.
  intros Z g1 g2 pbeq.
  use tpair.
  - exists (pullback_to_q_of_f gt0 f g1 g2 pbeq).
    apply pullback_to_q_of_f_ok.
  - simpl.
    induction t as [pb' pb'ok].
    apply subtypeInjectivity.
    + intro.
      apply isapropdirprod; apply (isaset_mor CC).
    + simpl.
      set (pbok := pullback_to_q_of_f_ok gt0 f g1 g2 pbeq).
      induction pbok as [pbok1 pbok2].
      induction pb'ok as [pb'ok1 pb'ok2].
      apply injectionprop2_4_cor.
      * etrans. { apply pb'ok2. }
        apply (! pbok2).
      * unfold ftf.
        etrans.
        apply pb'ok1.
        apply pathsinv0.
        etrans.
        apply pbok1.
        apply idpath.
Defined.

(** *** if the square expressed in [C0ax5c_type] is even a pullback, then one gets a C-system *)

(**
  This corresponds to the direction from 1 to 2 of Prop. 2.4 of "Csubsystems"
  whose proof is not carried out there.
*)


(** some preparation *)
Lemma s_pb_in_lC0system {CC: lC0system}{X Y: CC}
  (gt0: ll X > 0)(f: Y --> X)(q_of_f_is_pb: q_of_f_is_pullback_type gt0 (ftf f)):
  ∃! s : pr1 CC ⟦ ft(f_star gt0 (ftf f)), f_star gt0 (ftf f) ⟧,
       s · pnX 1 (f_star gt0 (ftf f)) = identity (ft(f_star gt0 (ftf f))) ×
       s · q_of_f gt0 (ftf f) = C0eiso gt0 (ftf f) · f.
Proof.
  assert (pbeq: identity(ft(f_star gt0 (ftf f))) · (C0eiso gt0 (ftf f) · ftf f) =
                C0eiso gt0 (ftf f) · f · pnX 1 X).
  { rewrite id_left. apply assoc. }
  exact (q_of_f_is_pb _ (identity _) (C0eiso gt0 (ftf f) · f) pbeq).
Defined.

(** construct the s operation *)
Lemma s_sec_in_lC0system {CC: lC0system}{X Y: CC} (gt0: ll X > 0)
  (f: Y --> X)(q_of_f_is_pb: q_of_f_is_pullback_type gt0 (ftf f)):
  sec_pX (f_star gt0 (ftf f)).
Proof.
  use tpair; simpl.
  + unfold funcomp; unfold idfun.
    exact (pr1 (iscontrpr1 (s_pb_in_lC0system gt0 f q_of_f_is_pb))).
  + exact (pr1 (pr2 (iscontrpr1 (s_pb_in_lC0system gt0 f q_of_f_is_pb)))).
Defined.

(** the other direction of Proposition 2.4 *)
Lemma lCsystem_from_lC0system_where_q_of_f_is_pullback {CC: lC0system}
  (q_of_f_is_pb : forall (X Y: CC)(gt0: ll X > 0)(f: Y --> X),
                     q_of_f_is_pullback_type gt0 (ftf f)): lCsystem.
Proof.
  exists CC.
  use tpair; simpl.
  - red.
    intros Y X gt0 f.
    exact (s_sec_in_lC0system gt0 f (q_of_f_is_pb X Y gt0 f)).
  - apply make_dirprod.
    + red.
      intros Y X gt0 f.
      simpl.
      apply pathsinv0.
      exact (pr2 (pr2 (iscontrpr1
        (s_pb_in_lC0system gt0
                           f
                           (q_of_f_is_pb X Y gt0 f))))).
    + red.
      intros Y Y' U gt0 g f.
      (* the strategy is as follows (not regarding the need for transport):
         -  (s_sec_in_lC0system (C0ax5a gt0 g) f (q_of_f_is_pb (f_star gt0 g) Y (C0ax5a gt0 g) f)) fulfills the two equations of s_pb_in_lC0system gt0 (f · q_of_f gt0 g) out of which the first is the property of being a section
         - by contraction and construction, it is then s_sec_in_lC0system gt0 (f · q_of_f gt0 g) (q_of_f_is_pb U Y gt0 (f · q_of_f gt0 g))
      *)
      apply eq_sec_pnX.
      { apply (isaset_mor CC). }
      (* UniMath.MoreFoundations.Tactics.show_id_type. *)
      set (s_f := s_sec_in_lC0system (C0ax5a gt0 g) f
                  (q_of_f_is_pb (f_star gt0 g) Y (C0ax5a gt0 g) f)).
      (* set (s_fq := s_sec_in_lC0system gt0 (f · q_of_f gt0 g)
                   (q_of_f_is_pb U Y gt0 (f · q_of_f gt0 g))). *)
      apply (path_to_ctr _ _
               (s_pb_in_lC0system
                  gt0
                  (f · q_of_f gt0 g)
                  (q_of_f_is_pb _ _ gt0 (f · q_of_f gt0 g)))).
      apply make_dirprod.
      * apply (sec_pnX_eq (n:=1)).
      * assert (s_f_ok := pr2 (pr2 (iscontrpr1
          (s_pb_in_lC0system (C0ax5a gt0 g)
                             f
                             (q_of_f_is_pb _ _ (C0ax5a gt0 g) f))))).
        simpl in s_f_ok.
        change (s_f · q_of_f (C0ax5a gt0 g) (ftf f) =
                C0eiso (C0ax5a gt0 g) (ftf f) · f) in s_f_ok.
        assert (ftfeq: ftf (f · q_of_f gt0 g) =
                       ftf f · ((C0eiso gt0 g) · g)).
        { unfold ftf.
          rewrite <- assoc.
          etrans.
          { apply cancel_precomposition.
            apply pathsinv0.
            apply C0ax5c. }
          apply assoc.
        }
        etrans.
        { apply cancel_precomposition.
          UniMath.MoreFoundations.Tactics.show_id_type.
          set (par := fun h: CC ⟦ Y, ft U ⟧ =>
                        mor_to_pr2 _ (q_of_f gt0 h)).
          apply (eq_par_arrow_cor _ _ par ftfeq).
        }
        rewrite maponpaths_for_constant_function.
        rewrite idtoiso_idpath.
        rewrite id_right.
        etrans.
        { do 2 apply cancel_precomposition.
          apply pathsinv0.
          UniMath.MoreFoundations.Tactics.show_id_type.
          apply (fiber_paths (C0ax7 gt0 g (ftf f))).
        }
        rewrite transportf_source_target_simple.
        rewrite maponpaths_for_constant_function.
        rewrite id_right.
        rewrite maponpathsidfun.
        simpl.
        repeat rewrite assoc.
        apply cancel_postcomposition.
        etrans.
        { do 3 apply cancel_postcomposition.
          UniMath.MoreFoundations.Tactics.show_id_type.
          set (pr := fun X: CC => sec_pnX_to_mor 1 X).
          apply pathsinv0.
          apply (transport_map pr).
        }
        rewrite transportf_source_target_simple.
        repeat rewrite <- assoc.
        apply z_iso_inv_on_right.
        rewrite <- idtoiso_inv0.
        repeat rewrite assoc.
        etrans.
        { apply cancel_postcomposition.
          repeat rewrite <- assoc.
          do 2 rewrite <- idtoiso_concat0.
          apply pathsinv0.
          apply cancelidtoiso_right_cor.
          { apply (isaset_ob CC). }
          apply idpath.
        }
        etrans.
        { exact s_f_ok. }
        unfold C0eiso.
        unfold C0ax5b_z_iso.
        rewrite <- idtoiso_concat0.
        apply cancelidtoiso_left.
        { apply (isaset_ob CC). }
        apply idpath.
Defined.

End Pullbacks.

(* End of the file lCsystems.v *)

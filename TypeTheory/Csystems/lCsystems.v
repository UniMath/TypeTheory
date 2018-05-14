(** ** lCsystems,

by Vladimir Voevodsky, split off the file lCsystems.v on March 5, 2015.

We refer below to the paper "Subsystems and regular quotients of C-systems"
by V. Voevodsky as "Csubsystems".

The definition of an lC-system given below does not require that the types of objects or morphisms
of the underlying precategory form a set. It also does not require the
properties of the identity morphisms but does require associativity. 

*)


Require Import UniMath.Foundations.All.
(* Require Import UniMath.CategoryTheory.Categories. *)
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.
Require Export TypeTheory.Csystems.lC0systems.



(** *** The l-C-systems *)


(** **** l-C-system data *) 

Definition sf_type ( CC : lC0system_data ) :=
  forall ( Y X : CC ) ( gt0 : ll X > 0 ) ( f : Y --> X ), sec_pX ( f_star gt0 ( ftf f ) ).

Definition lCsystem_data := ∑ CC : lC0system_data, sf_type CC.

Definition lCsystem_data_constr { CC : lC0system_data }
  ( sf0 : sf_type CC ) : lCsystem_data := tpair _ _ sf0 . 

Definition lCsystem_data_pr1 : lCsystem_data -> lC0system_data := pr1.
Coercion lCsystem_data_pr1 : lCsystem_data >-> lC0system_data.

Definition sf_from_data { CC : lCsystem_data } { Y X : CC } ( gt0 : ll X > 0 ) ( f : Y --> X ):
  sec_pX ( f_star gt0 ( ftf f ) ) := pr2 CC Y X gt0 f . 


(** **** Properties on l-C-system data that later become axioms of l-C-systems. *)


Definition sf_ax1_type { CC : lC0system } ( sf0 : sf_type CC ) :=
  forall ( Y X : CC ) ( gt0 : ll X > 0 ) ( f : Y --> X ),
    ( C0eiso gt0 ( ftf f ) ) ;; f = ( sf0 _ _ gt0 f ) ;; ( q_of_f gt0 ( ftf f ) ).


Definition sf_ax2_type_l1_type { CC : lC0system } ( sf0 : sf_type CC )
      { Y Y' U : CC } ( gt0 : ll U > 0 )
      ( g : Y' --> ft U ) ( f : Y --> f_star gt0 g ) :=
      f_star (C0ax5a gt0 g) (ftf f) = f_star gt0 (ftf (f ;; q_of_f gt0 g)).

(** needed for later analysis, not for the definition *)
Lemma sf_ax2_type_l1_type_depends_only_on_ftf_f { CC : lC0system } ( sf0 : sf_type CC )
      { Y Y' U : CC } ( gt0 : ll U > 0 )
      ( g : Y' --> ft U ) ( f f' : Y --> f_star gt0 g ):
      ftf f = ftf f' -> sf_ax2_type_l1_type sf0 gt0 g f = sf_ax2_type_l1_type sf0 gt0 g f'.
Proof.
  intro Hyp.
  unfold  sf_ax2_type_l1_type.
  rewrite Hyp.
  apply maponpaths.
  apply maponpaths.
  unfold ftf.
  do 2 rewrite <- assoc.
  simpl.
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
  sf_ax2_type_l1_type sf0 gt0 g f.
Proof.
  assert ( int1 : f_star (C0ax5a gt0 g) (ftf f) =
                  f_star gt0 ( ( ftf f ) ;; ( ( C0eiso gt0 g ) ;; g ) ) )
  by apply C0ax7a.

  assert ( int2 : f_star gt0 ( ( ftf f ) ;; ( ( C0eiso gt0 g ) ;; g ) ) =
                  f_star gt0 ( f ;; ( ( pX _ ) ;; ( ( C0eiso gt0 g ) ;; g ) ) ) ).
  { unfold ftf.
    rewrite <- assoc. 
    apply idpath.
  }
  assert ( int3 : f_star gt0 ( f ;; ( ( pX _ ) ;; ( ( C0eiso gt0 g ) ;; g ) ) ) =
                  f_star gt0 ( f ;; ( ( q_of_f gt0 g ) ;; ( pX U ) ) ) ).
  { unfold ftf.
    rewrite C0ax5c.
    apply idpath. 
  }
  assert ( int4 : f_star gt0 ( f ;; ( ( q_of_f gt0 g ) ;; ( pX U ) ) ) =
                  f_star gt0 (ftf (f ;; q_of_f gt0 g)) ).
  { unfold ftf.
    rewrite assoc.
    apply idpath. 
  }
  exact ( ( int1 @ int2 ) @ ( int3 @ int4 ) ). 
Defined.


Definition sf_ax2_type { CC : lC0system } ( sf : sf_type CC ) :=
  forall ( Y Y' U : CC ) ( gt0 : ll U > 0 )
    ( g : Y' --> ft U ) ( f : Y --> f_star gt0 g ),
     transportf sec_pX  (sf_ax2_type_l1 sf gt0 g f ) ( sf Y (f_star gt0 g) ( C0ax5a gt0 g ) f ) =
     sf Y U gt0 ( f ;; q_of_f gt0 g ).  


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
  ( C0eiso gt0 ( ftf f ) ) ;; f  = ( sf gt0 f ) ;; ( q_of_f gt0 ( ftf f ) ) :=
  pr1 ( pr2 ( pr2 CC ) ) Y X gt0 f.

Definition sf_ax2 { CC : lCsystem } { Y Y' U : CC } ( gt0 : ll U > 0 )
           ( g : Y' --> ft U ) ( f : Y --> f_star gt0 g ):
  transportf sec_pX  (sf_ax2_type_l1 ( @sf CC ) gt0 g f ) ( sf ( C0ax5a gt0 g ) f ) =
  sf gt0 ( f ;; q_of_f gt0 g ) :=
  pr2 ( pr2 ( pr2 CC ) ) Y Y' U gt0 g f.


(** **** Operation f_star_of_s *)

Definition f_star_of_s { CC : lCsystem } { Y X : CC } ( f : Y --> ft X )
  ( gt0 : ll X > 0 ) ( s : sec_pX X ): sec_pX ( f_star gt0 f ). 
Proof.
  set ( int := sf gt0 ( f ;; s ) ).  
  assert ( inteq : ftf ( f ;; s ) = f ). 
  { unfold ftf. 
    rewrite <- assoc.
    set ( eq := sec_pX_eq s : (s;; pX X)= _). 
    change ( f ;; (s ;; pX X ) = f ).  
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


(** *** the square expressed in [C0ax5c_type] is even a pullback in every C-system *)

(**
  This corresponds to the direction from 2 to 1 of Prop. 2.4 of "Csubsystems".
*)

Section Pullbacks.

Variable CC : lCsystem.

(** show that [g] is determined by [g;;q_of_f gt0 f] and [ftf g] - unfortunately, [g] alone enters as argument of [sf_ax2_type_l1] *)
Lemma injectionprop2_4 {X Y Z: CC} (gt0: ll X > 0) (f: Y --> ft X) (g: Z --> f_star gt0 f):
  g = C0eiso_inv (C0ax5a gt0 f) (ftf g);;
      (transportb _ (sf_ax2_type_l1 (@sf CC) gt0 f g)) (sf gt0 (g;;q_of_f gt0 f));;
      (q_of_f (C0ax5a gt0 f) (ftf g)).
Proof.
  rewrite <- sf_ax2.
  rewrite transport_b_f.
  rewrite pathsinv0r.
  rewrite idpath_transportf.
  rewrite <- assoc.
  simpl.
  apply pathsinv0.
  apply iso_inv_on_right.
  apply pathsinv0.
  etrans.
  - eapply (sf_ax1 (C0ax5a gt0 f) g).
  - apply idpath.
Defined.

(*
    Check (sec_pnX_to_mor 1 _ (sf gt0 (g;;q_of_f gt0 f))).
    Check (mor_to_pr2 _ (q_of_f (C0ax5a gt0 f) (ftf g))).
    Check (!(sf_ax2_type_l1 (@sf CC) gt0 f g)).
    Check (C0ax7a gt0 f (ftf g)).
    Check (transportf _ (!(sf_ax2_type_l1 (@sf CC) gt0 f g)) (sf gt0 (g;;q_of_f gt0 f))).
    Check ((transportf _ (!(sf_ax2_type_l1 (@sf CC) gt0 f g)) (sf gt0 (g;;q_of_f gt0 f)));;(q_of_f (C0ax5a gt0 f) (ftf g))).
    Check (C0ax5b (C0ax5a gt0 f) (ftf g)).
    Check (C0emor_inv (C0ax5a gt0 f) (ftf g)).
 *)


Lemma injectionprop2_4_cor {X Y Z: CC} (gt0: ll X > 0) (f: Y --> ft X) (g g': Z --> f_star gt0 f): g;;q_of_f gt0 f = g';;q_of_f gt0 f -> ftf g = ftf g' -> g = g'.
Proof.
  intros Hyp1 Hyp2.
  rewrite injectionprop2_4.
  rewrite (injectionprop2_4 _ _ g).
(* this should be okay since g enters the equation only in the form of ftf g or g · q_of_f gt0 f, with the exception of the argument to sf_ax2_type_l1, but this is an equation of objects whose type only depends on ftf g, as shown in sf_ax2_type_l1_type_depends_only_on_ftf_f
 *)
  do 2 rewrite <- assoc.
  etrans.
  { apply cancel_postcomposition.
    apply maponpaths. (* needed to use the specialized lemma *)
    set (artiso := fun h: CC ⟦ Z, ft(f_star gt0 f) ⟧ => C0eiso_inv (C0ax5a gt0 f) h).
    apply (eq_function_to_iso_on_morphisms_cor _ _ artiso _ _ Hyp2).
  }
  simpl.
  rewrite maponpaths_for_constant_function.
  do 2 rewrite <- assoc.
  rewrite id_left.
  apply maponpaths.
  rewrite assoc.
  etrans.
  { apply cancel_precomposition.
    set (art := fun h: CC ⟦ Z, ft (f_star gt0 f) ⟧ => pr2(q_of_f (C0ax5a gt0 f) h)).
    exact (eq_function_on_morphisms_cor _ _ art _ _ Hyp2).

    (* I would have preferred to use the specialized lemma as follows:
    set (artmorto := fun h: CC ⟦ Z, ft (f_star gt0 f) ⟧ => q_of_f (C0ax5a gt0 f) h).
    exact (eq_function_to_mor_to_on_morphisms_cor _ artmorto _ _ Hyp2).
      However, I do not know how to instruct Coq to work on the level of
      mor_to - the goal hides the coercion to the underlying morphism! *)
  }
  etrans.
  { apply cancel_postcomposition.
    apply maponpaths.
(* and now? *)


  Admitted.

End Pullbacks.

(* End of the file lCsystems.v *)

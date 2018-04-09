(** ** lCsystems,

by Vladimir Voevodsky, split off the file lCsystems.v on March 5, 2015.

We refer below to the paper "Subsystems and regular quotients of C-systems"
by V. Voevodsky as "Csubsystems".

The definition of an lC-system given below does not require that the types of objects or morphisms
of the underlying precategory form a set. It also does not require the
proporties of the identity morphisms but does require associativity. 

 *)



Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import TypeTheory.Csystems.prelim.
Require Import TypeTheory.Csystems.lTowers.

Require Import TypeTheory.Csystems.ltowers_over.


(* Require Import UniMath.CategoryTheory.Categories. *)
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.
Require Import TypeTheory.Csystems.hSet_ltowers.
Require Import TypeTheory.Csystems.lC0systems.



(** *** The l-C-systems *)


(** **** l-C-system data *) 

Definition sf_type ( CC : lC0system_data ) :=
  forall ( Y X : CC ) ( gt0 : ll X > 0 ) ( f : Y --> X ) , sec_pX ( f_star gt0 ( ftf f ) ) .

Definition lCsystem_data := ∑ CC : lC0system_data, sf_type CC.

Definition lCsystem_data_constr { CC : lC0system_data } ( sf0 : sf_type CC ) : lCsystem_data :=
  tpair _ _ sf0 . 

Definition lCsystem_data_pr1 : lCsystem_data -> lC0system_data := pr1 .
Coercion lCsystem_data_pr1 : lCsystem_data >-> lC0system_data .

Definition sf_from_data { CC : lCsystem_data } { Y X : CC } ( gt0 : ll X > 0 ) ( f : Y --> X ) :
  sec_pX ( f_star gt0 ( ftf f ) ) :=
  pr2 CC Y X gt0 f . 






(** **** Properties on l-C-system data 

that later become axioms of l-C-systems. *)


Definition sf_ax1_type { CC : lC0system } ( sf0 : sf_type CC ) :=
  forall ( Y X : CC ) ( gt0 : ll X > 0 ) ( f : Y --> X ) ,
    ( C0emor gt0 ( ftf f ) ) ;; f = ( sf0 _ _ gt0 f ) ;; ( q_of_f gt0 ( ftf f ) ) .

Lemma sf_ax2_type_l1 { CC : lC0system } ( sf0 : sf_type CC )
      { Y Y' U : CC } ( gt0 : ll U > 0 )
      ( g : Y' --> ft U ) ( f : Y --> f_star gt0 g ) :
  f_star (C0ax5a gt0 g) (ftf f) = f_star gt0 (ftf (f ;; q_of_f gt0 g)) .
Proof.
  assert ( int1 : f_star (C0ax5a gt0 g) (ftf f) =
                  f_star gt0 ( ( ftf f ) ;; ( ( C0emor gt0 g ) ;; g ) ) ) .
  apply C0ax7a.

  assert ( int2 : f_star gt0 ( ( ftf f ) ;; ( ( C0emor gt0 g ) ;; g ) ) =
                  f_star gt0 ( f ;; ( ( pX _ ) ;; ( ( C0emor gt0 g ) ;; g ) ) ) ) . 
  unfold ftf . rewrite <- assoc . 
  apply idpath . 

  assert ( int3 : f_star gt0 ( f ;; ( ( pX _ ) ;; ( ( C0emor gt0 g ) ;; g ) ) ) =
                  f_star gt0 ( f ;; ( ( q_of_f gt0 g ) ;; ( pX U ) ) ) ) .
  unfold ftf . rewrite C0ax5c .
  apply idpath . 

  assert ( int4 : f_star gt0 ( f ;; ( ( q_of_f gt0 g ) ;; ( pX U ) ) ) =
                  f_star gt0 (ftf (f ;; q_of_f gt0 g)) ) .
  unfold ftf . rewrite assoc .
  apply idpath . 

  exact ( ( int1 @ int2 ) @ ( int3 @ int4 ) ) . 

Defined.

Definition sf_ax2_type { CC : lC0system } ( sf : sf_type CC ) :=
  forall ( Y Y' U : CC ) ( gt0 : ll U > 0 )
         ( g : Y' --> ft U ) ( f : Y --> f_star gt0 g ) ,
     transportf sec_pX  (sf_ax2_type_l1 sf gt0 g f ) ( sf Y _ ( C0ax5a gt0 g ) f ) =
     sf Y _ gt0 ( f ;; q_of_f gt0 g ) .  


(** **** The definition of the type of l-C-systems *)


Definition lCsystem :=
             ∑ (CC : lC0system) (sf0 : sf_type CC),
                        ( sf_ax1_type sf0 ) × ( sf_ax2_type sf0 ).

Definition lCsystem_pr1 : lCsystem -> lC0system := pr1 .
Coercion lCsystem_pr1 : lCsystem >-> lC0system .

Definition lCsystem_to_lCsystem_data ( CC : lCsystem ) : lCsystem_data :=
  @lCsystem_data_constr CC ( pr1 ( pr2 CC ) ) .
Coercion lCsystem_to_lCsystem_data : lCsystem >-> lCsystem_data .

Definition sf { CC : lCsystem } { Y X : CC } ( gt0 : ll X > 0 ) ( f : Y --> X ) :
  sec_pX ( f_star gt0 ( ftf f ) ) := ( pr1 ( pr2 CC ) ) Y X gt0 f . 

Definition sf_ax1 { CC : lCsystem } { Y X : CC } ( gt0 : ll X > 0 ) ( f : Y --> X ) :
  ( C0emor gt0 ( ftf f ) ) ;; f  = ( sf gt0 f ) ;; ( q_of_f gt0 ( ftf f ) ) :=
  pr1 ( pr2 ( pr2 CC ) ) Y X gt0 f .

Definition sf_ax2 { CC : lCsystem } { Y Y' U : CC } ( gt0 : ll U > 0 )
           ( g : Y' --> ft U ) ( f : Y --> f_star gt0 g ) :
  transportf sec_pX  (sf_ax2_type_l1 ( @sf CC ) gt0 g f ) ( sf ( C0ax5a gt0 g ) f ) =
  sf gt0 ( f ;; q_of_f gt0 g ) :=
  pr2 ( pr2 ( pr2 CC ) ) Y Y' U gt0 g f .




  

(** **** Operation f_star_of_s *)

Definition f_star_of_s { CC : lCsystem } { Y X : CC } ( f : Y --> ft X )
           ( gt0 : ll X > 0 ) ( r : sec_pX X ) :
  sec_pX ( f_star gt0 f ) . 
Proof .
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

  

(** **** Operation fsn_star_of_s *)


Definition fsn_star_of_s { CC : lCsystem } { A X : CC } ( f : mor_to A ) ( isab : isabove X A )
           ( r : sec_pX X ) : sec_pX ( fn_star f isab ) .  
Proof.
  rewrite f_star_isab .
  apply f_star_of_s . 
  exact r .

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


(* End of the file lCsystems.v *)
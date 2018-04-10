(** * Operations T and Tt on carriers of lB-systems and their properties TT and TTt.

by Vladimir Voevodsky, file created on Jan. 6, 2015 *)


Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import TypeTheory.Csystems.prelim.
Require Import TypeTheory.Csystems.lTowers.
Require Import TypeTheory.Csystems.ltowers_over.
Require Import TypeTheory.Csystems.hSet_ltowers.

Require Import TypeTheory.Bsystems.lB_carriers.


(** ** Operation(s) T.

Including constructions related to their domains of definition. 

Compare with Definitions 2.1 and 2.5 on pre-B-systems in arXiv:1410.5389v1; the
presentation is very different, but the notion is meant to be equivalent.


*)

(** *** Domains of definition of operations of type T *)

Definition T_dom { BB : lBsystem_carrier } ( X1 X2 : BB ) :=
  ( ll X1 > 0 ) × ( isabove X2 ( ft X1 ) ) .

Definition T_dom_constr { BB : lBsystem_carrier } { X1 X2 : BB }
           ( gt0 : ll X1 > 0 ) ( isab : isabove X2 ( ft X1 ) ) : T_dom X1 X2 :=
  tpair _ gt0 isab .
  
Definition T_dom_gt0 { BB : lBsystem_carrier } { X1 X2 : BB } ( inn : T_dom X1 X2 ) :
  ll X1 > 0 := pr1 inn .

Definition T_dom_gth { BB : lBsystem_carrier } { X1 X2 : BB } ( inn : T_dom X1 X2 ) :
  ll X2 > ll ( ft X1 ) := isabove_gth ( pr2 inn ) .

Definition T_dom_isabove { BB : lBsystem_carrier } { X1 X2 : BB } ( inn : T_dom X1 X2 ) :
  isabove X2 ( ft X1 ) := pr2 inn . 

Definition T_dom_geh { BB : lBsystem_carrier } { X1 X2 : BB } ( inn : T_dom X1 X2 ) :
  ll X2 >= ll X1 .
Proof .
  assert ( gt := T_dom_gth inn ) . 
  assert ( gte := natgthtogehsn _ _ gt ) . 
  use ( istransnatgeh _ _ _ gte) . 
  rewrite ll_ft . 
  change ( 1 + ( ll X1 - 1 ) >= ll X1 ) . 
  rewrite natpluscomm . 
  exact ( minusplusnmmineq _ _ ) . 

Defined.

Lemma T_dom_gt0_2 { BB : lBsystem_carrier } { X1 X2 : BB } ( inn : T_dom X1 X2 ) :
  ll X2 > 0 .
Proof .
  exact ( isabove_gt0 ( T_dom_isabove inn ) ) .
          
Defined.
          

  
  
Lemma isaprop_T_dom { BB : lBsystem_carrier } ( X1 X2 : BB ) : isaprop ( T_dom X1 X2 ) . 
Proof.
  apply isapropdirprod . 
  apply ( pr2 ( _ > _ ) ) .
  
  exact ( isaprop_isabove _ _ ) . 

Defined.

Lemma noparts_T_dom { BB : lBsystem_carrier } { X1 X2 : BB } ( inn1 inn2 : T_dom X1 X2 ) :
  inn1 = inn2 .
Proof .
  apply ( proofirrelevance _ ( isaprop_T_dom X1 X2 ) ) .
Defined .

Definition T_dom_refl { BB : lBsystem_carrier } ( X : BB ) ( gt0 : ll X > 0 ) : T_dom X X :=
  T_dom_constr gt0 ( isabove_X_ftX X gt0 ) . 

Definition T_dom_comp { BB : lBsystem_carrier } { X1 X2 X3 : BB }
           ( inn12 : T_dom X1 X2 ) ( inn23 : T_dom X2 X3 ) : T_dom X1 X3 .
Proof.
  assert ( gt0 := T_dom_gt0 inn12 ) . 
  assert ( is21 := T_dom_isabove inn12 ) . assert ( is32 := T_dom_isabove inn23 ) .
  use T_dom_constr. 
  exact gt0 .

  exact ( isabov_trans is32 ( isover_ft' is21 ) ) . 

Defined.

Lemma T_dom_ftn { BB : lBsystem_carrier } { X1 X2 : BB } ( n : nat ) ( inn : T_dom X1 X2 )
      ( isab : isabove ( ftn n X2 ) ( ft X1 ) ) : T_dom X1 ( ftn n X2 ) .
Proof .
  exact ( T_dom_constr ( T_dom_gt0 inn ) isab ) . 

Defined.



(** *** The type objects of which are candidates for operations T on an lB-system. *)
 
Definition T_ops_type ( BB : lBsystem_carrier ) :=
  forall ( X1 X2 : BB ) ( inn : T_dom X1 X2 ) , BB .

(** Notice that the indices in [BB] are not specified here, see [T_ax0_type] below. *)

Identity Coercion T_ops_to_Fun : T_ops_type >-> Funclass .



Lemma T_equals_T { BB : lBsystem_carrier } { X1 X2 X2' : BB } ( T : T_ops_type BB )
      ( eq : X2 = X2' ) ( inn : T_dom X1 X2 ) ( inn' : T_dom X1 X2' )  :
  T X1 X2 inn = T X1 X2' inn' .
Proof.
  revert inn inn'.
  rewrite eq . 
  intros . rewrite ( noparts_T_dom inn inn' ) . 
  apply idpath . 

Defined.


  

(** *** The zeroth property (later an axiom) of an operation of type T *)

Definition T_ax0_type { BB : lBsystem_carrier } ( T : T_ops_type BB ) :=
  forall ( X1 X2 : BB ) ( inn : T_dom X1 X2 ) , ll ( T X1 X2 inn ) = 1 + ( ll X2 ) .

(** This definition gives the missing element of Definition 2.1.4(a) in arXiv:1410.5389v1 *)

Identity Coercion T_ax0_to_Fun : T_ax0_type >-> Funclass . 

Lemma ll_T_gt0 { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax0 :  T_ax0_type T )
      { X1 X2 : BB } ( inn : T_dom X1 X2 ) : ll ( T X1 X2 inn ) > 0 .
Proof.
  rewrite ax0 . 
  exact ( natgthsn0 _ ) .

Defined.


(** *** The first property (later an axiom) of an operation of type T *)


Lemma T_ax1a_dom { BB : lBsystem_carrier } { X1 X2 : BB } ( inn : T_dom X1 X2 )
      ( isab : isabove ( ft X2 ) ( ft X1 ) ) : T_dom X1 ( ft X2 ) .
Proof .
  exact ( T_dom_constr ( T_dom_gt0 inn ) isab ) . 

Defined.

Definition T_ax1a_type { BB : lBsystem_carrier } ( T : T_ops_type BB ) :=
  forall ( X1 X2 : BB ) ( inn : T_dom X1 X2 ) ( isab : isabove ( ft X2 ) ( ft X1 ) ) ,
    ft ( T X1 X2 inn ) = T X1 ( ft X2 ) ( T_ax1a_dom inn isab ) .

(** This definition corresponds to the first case in Definition 2.5.2 in arXiv:1410.5389v1 *)

Identity Coercion T_ax1a_to_Fun: T_ax1a_type >-> Funclass . 


Definition T_ax1b_type { BB : lBsystem_carrier } ( T : T_ops_type BB ) :=
  forall ( X1 X2 : BB ) ( inn : T_dom X1 X2 ) , isabove ( T X1 X2 inn ) X1 .

(** This is not the second case in Definition 2.5.2 in arXiv:1410.5389v1 *)

Identity Coercion T_ax1b_to_Fun: T_ax1b_type >-> Funclass . 


(** *** The computation of the iterated [ft] of (T X1 X2)  *)



Lemma ftn_T { BB : lBsystem_carrier } { T : T_ops_type BB } ( ax1a : T_ax1a_type T )
      ( n : nat ) { X1 X2 : BB } ( isab : isabove ( ftn n X2 ) ( ft X1 ) )
      ( inn : T_dom X1 X2 ) :
  ftn n ( T X1 X2 inn ) = T X1 ( ftn n X2 ) ( T_dom_ftn n inn isab ) .
Proof .
  revert X1 X2 isab inn. induction n as [ | n IHn ] .
  + intros .
    rewrite ( noparts_T_dom inn (T_dom_ftn 0 inn isab) ) . 
    apply idpath . 
  + intros .
    change ( ftn (S n) (T X1 X2 inn) ) with ( ft ( ftn n (T X1 X2 inn) ) ) .
    assert ( isab' : isabove ( ftn n X2 ) ( ft X1 ) ) by exact ( isabove_ft_inv isab ) . 
    rewrite ( IHn X1 X2 isab' inn ) . 
    use ax1a. 
Defined.

(** Now get the second case in Definition 2.5.2 in arXiv:1410.5389v1 from [T_ax1b_type] *)

Lemma ft_T { BB : lBsystem_carrier } { T : T_ops_type BB } { X1 X2 : BB } ( ax0 : T_ax0_type T )
      ( ax1b : T_ax1b_type T ) ( iseq : ft X2 = ft X1 ) ( inn : T_dom X1 X2 ) :
  ft ( T X1 X2 inn ) = X1 .
Proof.
  assert ( isov := ax1b X1 X2 inn : isover (T X1 X2 inn) X1  ) .
  unfold isover in isov . rewrite ax0 in isov .  rewrite ( natassocpmeq _ _ _ ( T_dom_geh inn ) )
                                                         in isov . 
  assert ( eq : ll X2 = ll X1 ) .
  assert ( eq' : ll X2 - 1 = ll X1 - 1 ) . repeat rewrite <- ll_ft .  rewrite iseq .
  apply idpath .

  assert ( eq1 : ( ll X1 - 1 ) + 1 = ll X1 ) . refine ( minusplusnmm _ _ _ ) .
  exact ( natgthtogehsn _ _ (T_dom_gt0 inn ) ) .

  assert ( eq2 : ( ll X2 - 1 ) + 1 = ll X2 ) . refine ( minusplusnmm _ _ _ ) .
  exact ( istransnatgeh _ _ _ ( T_dom_geh inn ) ( natgthtogehsn _ _ (T_dom_gt0 inn ) ) ) .

  assert ( eq'' := maponpaths ( fun n => n + 1 ) eq' ) . 
  lazy beta in eq'' . 
  rewrite eq1 in eq'' . rewrite eq2 in eq'' . exact eq'' .

  rewrite eq in isov . 
  rewrite natminusnn in isov . 
  exact ( ! isov ) . 

Defined.





(** *** The isover and isabove properties of the expressions T X1 X2 *)
(** We prove just monotonicity in the second argument with respect to [isover] and [isabove] *)

  
Lemma isover_T_T_2 { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax0 :  T_ax0_type T ) ( ax1a : T_ax1a_type T )
      { X1 X2 X2' : BB } ( inn : T_dom X1 X2 ) ( inn' : T_dom X1 X2' )
      ( is : isover X2 X2' ) : isover ( T X1 X2 inn ) ( T X1 X2' inn' ) .
Proof .
  unfold isover in * .
  do 2 rewrite ax0 .
  simpl .
  assert ( isab : isabove ( ftn ( ll X2 - ll X2') X2 ) ( ft X1 ) ) .
  rewrite <- is .

(*  Set Printing All . *)
  
  exact ( T_dom_isabove inn' ) . 

  rewrite ( ftn_T ax1a _ isab inn ) .
  exact ( T_equals_T _ is _ _ ) . 

Defined.


Lemma isabove_T_T_2 { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax0 :  T_ax0_type T ) ( ax1a : T_ax1a_type T )
      { X1 X2 X2' : BB } ( inn : T_dom X1 X2 ) ( inn' : T_dom X1 X2' )
      ( is : isabove X2 X2' ) : isabove ( T X1 X2 inn ) ( T X1 X2' inn' ) .
Proof .
  use isabove_constr.
  do 2 rewrite ax0 . 
  exact ( isabove_gth is ) . 

  exact ( isover_T_T_2 ax0 ax1a _ _ is ) . 
  
Defined.








(** ** Operation(s) Tt (T tilde in the paper) .

Including constructions related to their domains of definition. *)

(** *** Domains of definition of operations of type Tt *)


Definition Tt_dom { BB : lBsystem_carrier } ( X : BB ) ( s : Tilde BB ) := T_dom X ( dd s ) .


(** *** The type objects of which are candidates for operations Tt on an lB-system. *)
 
              
Definition Tt_ops_type ( BB : lBsystem_carrier ) :=
  forall ( X : BB ) ( s : Tilde BB ) ( inn : Tt_dom X s ) , Tilde BB .

(** Notice that the indices in [Tilde BB] are not specified here, see [Tt_ax0_type] below. *)

Identity Coercion Tt_ops_to_Fun: Tt_ops_type >-> Funclass . 

(** *** The zeroth property (later an axiom) of an operation of type Tt
 
It will be shown to be a corollary of the first property of Tt and the zeroth property of T. 
However it is convenient to have it separately for the use in the definition of a pre-lB-system. *)

Definition Tt_ax0_type { BB : lBsystem_carrier } ( Tt : Tt_ops_type BB ) :=
  forall ( X : BB ) ( s : Tilde BB ) ( inn : Tt_dom X s ) ,
    ll ( dd ( Tt X s inn ) ) = 1 + ll ( dd s ) .

(** This definition gives the missing element of Definition 2.1.4(b) in arXiv:1410.5389v1 *)


(** *** The first property (later an axiom) of an operation of type Tt *)


Definition Tt_ax1_type { BB : lBsystem_carrier } ( T : T_ops_type BB ) ( Tt : Tt_ops_type BB ) :=
  forall ( X : BB ) ( s : Tilde BB ) ( inn : Tt_dom X s ) ,
    dd ( Tt X s inn ) = T X ( dd s ) inn .

(** This definition corresponds to Definition 2.5.3 in arXiv:1410.5389v1 *)

Identity Coercion Tt_ax1_to_Fun: Tt_ax1_type >-> Funclass .

(** As announced above, [Tt_ax0_type] is somewhat redundant *)

Lemma Tt_ax1_to_Tt_ax0 { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax0 : T_ax0_type T )
      { Tt : Tt_ops_type BB } ( ax1 : Tt_ax1_type T Tt ) : Tt_ax0_type Tt .
Proof .
  unfold Tt_ax0_type . 
  intros . 
  rewrite ax1 . 
  exact ( ax0 _ _ _ ) . 

Defined.





(** ** The properties TT and TTt *)


  
  
(** *** Two implications of the zeroth and first properties of operations of type T that are required for the formulation of the property TT *) 


Lemma T_dom_12_23_to_T12_T13 { BB : lBsystem_carrier } { T : T_ops_type BB }
      ( ax0 :  T_ax0_type T ) ( ax1a : T_ax1a_type T ) ( ax1b : T_ax1b_type T )
           { X1 X2 X3 : BB } ( inn12 : T_dom X1 X2 ) ( inn23 : T_dom X2 X3 ) :
  T_dom ( T X1 X2 inn12 ) ( T X1 X3 ( T_dom_comp inn12 inn23 ) ) .
Proof . 
  assert ( is21 := T_dom_isabove inn12 ) .
  assert ( is32 := T_dom_isabove inn23 ) .
  refine ( T_dom_constr _ _ ) .
  + apply (ll_T_gt0 ax0).
  + destruct ( isabove_choice is21 ) as [ isab | eq ] .
    * rewrite ( ax1a _ _ _ isab ) . 
      exact ( isabove_T_T_2 ax0 ax1a _ _ is32) .
    * rewrite ( ft_T ax0 ax1b ( ! eq ) _ ) .
      apply ax1b . 
Defined.

 

Lemma T_dom_12_23_to_T1T23 { BB : lBsystem_carrier }
           { T : T_ops_type BB } ( ax1b : T_ax1b_type T ) 
           { X1 X2 X3 : BB } ( inn12 : T_dom X1 X2 ) ( inn23 : T_dom X2 X3 ) :
  T_dom X1 ( T X2 X3 inn23 ) .
Proof .
  use T_dom_constr. 
  + exact ( T_dom_gt0 inn12 ) . 
  + use ( isabov_trans ( ax1b _ _ _ ) ) . 
    exact ( T_dom_isabove inn12 ) .
Defined.






(** *** The property (later an axiom) TT *)

Definition TT_type { BB : lBsystem_carrier } { T : T_ops_type BB }
           ( ax0 : T_ax0_type T ) ( ax1a : T_ax1a_type T ) ( ax1b : T_ax1b_type T ) :=
  forall ( X1 X2 X3 : BB ) ( inn12 : T_dom X1 X2 ) ( inn23 : T_dom X2 X3 ) ,
    T ( T X1 X2 inn12 ) ( T X1 X3 ( T_dom_comp inn12 inn23 ) )
      ( T_dom_12_23_to_T12_T13 ax0 ax1a ax1b inn12 inn23 ) =
    T X1 ( T X2 X3 inn23 ) ( T_dom_12_23_to_T1T23 ax1b inn12 inn23 ) .

(** This definition corresponds to Definition 3.1.1(a) in arXiv:1410.5389v1 *)

Identity Coercion TT_to_Fun: TT_type >-> Funclass . 



  

  
(** *** Two implications of the zeroth and first properties of operations of type T and Tt that are required for the formulation of the property TTt *) 

Lemma Tt_dom_12_2r_to_T12_Tt1r { BB : lBsystem_carrier } { T : T_ops_type BB }
      ( ax0 : T_ax0_type T ) ( ax1a : T_ax1a_type T ) ( ax1b : T_ax1b_type T )
           { Tt : Tt_ops_type BB } ( ax1at : Tt_ax1_type T Tt )
           { X1 X2 : BB } { r : Tilde BB } ( inn12 : T_dom X1 X2 ) ( inn2r : Tt_dom X2 r ) :
  Tt_dom ( T X1 X2 inn12 ) ( Tt X1 r ( T_dom_comp inn12 inn2r ) ) .
Proof.
  unfold Tt_dom .
  rewrite ax1at . 
  apply ( T_dom_12_23_to_T12_T13 ax0 ax1a ax1b inn12 inn2r ) . 
Defined.


Lemma Tt_dom_12_2r_to_Tt1Tt2r { BB : lBsystem_carrier } { T : T_ops_type BB }
      ( ax0 : T_ax0_type T ) ( ax1b : T_ax1b_type T )
      { Tt : Tt_ops_type BB } ( ax1at : Tt_ax1_type T Tt )
      { X1 X2 : BB } { r : Tilde BB } ( inn12 : T_dom X1 X2 ) ( inn2r : Tt_dom X2 r ) :
  Tt_dom X1 ( Tt X2 r inn2r ) .
Proof.
  unfold Tt_dom.
  rewrite ax1at . 
  apply ( T_dom_12_23_to_T1T23 ax1b inn12 inn2r ) .
Defined.





  
(** *** The property TTt *)

Definition TTt_type { BB : lBsystem_carrier } { T : T_ops_type BB }
           ( ax0 : T_ax0_type T ) ( ax1a : T_ax1a_type T ) ( ax1b : T_ax1b_type T )
           { Tt : Tt_ops_type BB } ( ax1t : Tt_ax1_type T Tt ) :=
  forall ( X1 X2 : BB ) ( r : Tilde BB ) ( inn12 : T_dom X1 X2 ) ( inn2r : Tt_dom X2 r ) ,
    Tt ( T X1 X2 inn12 ) ( Tt X1 r ( T_dom_comp inn12 inn2r ) )
      ( Tt_dom_12_2r_to_T12_Tt1r ax0 ax1a ax1b ax1t inn12 inn2r ) =
    Tt X1 ( Tt X2 r inn2r ) ( Tt_dom_12_2r_to_Tt1Tt2r ax0 ax1b ax1t inn12 inn2r ) .

(** This definition corresponds to Definition 3.1.1(b) in arXiv:1410.5389v1 *)

Identity Coercion TTt_to_Fun: TTt_type >-> Funclass . 








(* End of the file T_Tt.v *)




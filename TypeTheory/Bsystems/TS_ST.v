(** * The properties TS, TtS and StT, StTt of quadruples of operations T, Tt, S, St. 

By Vladimir Voevodsky, started on Jan. 10, 2015 *)


Require Import UniMath.Foundations.All.

Require Import TypeTheory.Csystems.hSet_ltowers.

Require Export TypeTheory.Bsystems.T_Tt .
Require Export TypeTheory.Bsystems.S_St .



(** *** Mixed properties of domains of definitions of operations T, Tt, S, St *)

Lemma S_T_dom_comp { BB : lBsystem_carrier }
       { r : Tilde BB } { X1 X2 : BB }
       ( innr1 : S_dom r X1 ) ( inn12 : T_dom X1 X2 ) : S_dom r X2 .
Proof .   
  unfold S_dom in * . 
  exact ( isabov_trans ( T_dom_isabove inn12 ) ( isover_ft' innr1 ) ) . 
Defined.

Definition  S_Tt_dom_comp { BB : lBsystem_carrier }
           { r s : Tilde BB } { X1 : BB }
           ( innr1 : S_dom r X1 ) ( inn1s : Tt_dom X1 s ) : St_dom r s .
Proof .
  exact ( S_T_dom_comp innr1 inn1s ) .
Defined.

Definition  Tt_S_dom_comp { BB : lBsystem_carrier }
           { r : Tilde BB } { X1 X2 : BB }
           ( inn1r : Tt_dom X1 r ) ( innr2 : S_dom r X2 ) : T_dom X1 X2 .
Proof .
  use T_dom_constr. 
  + exact ( T_dom_gt0 inn1r ) . 
  + exact ( isabove_trans innr2 ( T_dom_isabove inn1r ) ) .
Defined.

Definition Tt_St_dom_comp { BB : lBsystem_carrier }
           { r s : Tilde BB } { X1 : BB }
           ( inn1r : Tt_dom X1 r ) ( innrs : St_dom r s ) : Tt_dom X1 s . 
Proof .
  exact ( Tt_S_dom_comp inn1r innrs ) .
Defined.

  





  

(** *** Implications of the zeroth and first properties of operations of type T, Tt, S and St that are required for the formulation of the property TS and TtS. *)

Lemma T_dom_r1_12_to_Sr1_Sr2 { BB : lBsystem_carrier }
      { S : S_ops_type BB } ( Sax0 : S_ax0_type S ) ( Sax1a : S_ax1a_type S )
      ( Sax1b : S_ax1b_type S )
      { r : Tilde BB } { X1 X2 : BB }
      ( innr1 : S_dom r X1 ) ( inn12 : T_dom X1 X2 ) :
  T_dom ( S r X1 innr1 ) ( S r X2 ( S_T_dom_comp innr1 inn12 ) ) .
Proof.
  use T_dom_constr.
  + rewrite Sax0 . 
    exact ( minusgth0 _ _ ( S_dom_gt1 innr1 ) ) .
  + destruct ( isabove_choice innr1 ) as [ isab | iseq ] .
    * rewrite ( Sax1a _ _ innr1 isab ) . 
      exact ( isabove_S_S_2 Sax0 Sax1a _ _ ( T_dom_isabove inn12 ) ) .
    * rewrite ( ft_S Sax0 Sax1b ( ! iseq ) _ ) . 
      exact ( Sax1b _ _ _ ) . 
Defined.


Lemma Tt_dom_r1_1s_to_Sr1_Strs { BB : lBsystem_carrier }
      { S : S_ops_type BB } ( Sax0 : S_ax0_type S ) ( Sax1a : S_ax1a_type S )
      ( Sax1b : S_ax1b_type S )
      { St : St_ops_type BB } ( Stax1 : St_ax1_type S St ) 
      { r s : Tilde BB } { X1 : BB }
      ( innr1 : S_dom r X1 ) ( inn1s : Tt_dom X1 s ) :
  Tt_dom ( S r X1 innr1 ) ( St r s ( S_Tt_dom_comp innr1 inn1s ) ) . 
Proof.
  unfold Tt_dom . 
  rewrite Stax1 . 
  exact ( T_dom_r1_12_to_Sr1_Sr2 Sax0 Sax1a Sax1b _ _ ) . 
Defined.

  


Lemma  S_dom_r1_12_to_r_T12 { BB : lBsystem_carrier }
       { T : T_ops_type BB } ( Tax1b : T_ax1b_type T )        
       { r : Tilde BB } { X1 X2 : BB }
       ( innr1 : S_dom r X1 ) ( inn : T_dom X1 X2 ) :
  S_dom r ( T X1 X2 inn ) .
Proof .
  unfold S_dom .
  exact ( isabove_trans ( Tax1b _ _ inn ) innr1 ) . 
Defined.


Lemma St_dom_r1_1s_to_r_Tt1s { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( Tax1b : T_ax1b_type T )
      { Tt : Tt_ops_type BB } ( Ttax1 : Tt_ax1_type T Tt )        
      { r s : Tilde BB } { X1 : BB }
      ( innr1 : S_dom r X1 ) ( inn1s : Tt_dom X1 s ) :
  St_dom r ( Tt X1 s inn1s ) .
Proof .
  unfold St_dom . 
  rewrite Ttax1 . 
  exact ( S_dom_r1_12_to_r_T12 Tax1b innr1 inn1s ) . 
Defined.

  


(** *** Property TS *)

Definition TS_type { BB : lBsystem_carrier }
           { T : T_ops_type BB } ( Tax1b : T_ax1b_type T )
           { S : S_ops_type BB } ( Sax0 : S_ax0_type S ) ( Sax1a : S_ax1a_type S )
           ( Sax1b : S_ax1b_type S ) :=
  forall ( r : Tilde BB ) ( X1 X2 : BB ) ( innr1 : S_dom r X1 ) ( inn12 : T_dom X1 X2 ) ,
    T ( S r X1 innr1 ) ( S r X2 ( S_T_dom_comp innr1 inn12 ) )
      ( T_dom_r1_12_to_Sr1_Sr2 Sax0 Sax1a Sax1b innr1 inn12 ) =
    S r ( T X1 X2 inn12 ) ( S_dom_r1_12_to_r_T12 Tax1b innr1 inn12 ) .

(** This definition corresponds to Definition 3.1.4(a) in arXiv:1410.5389v1.
    Notice that the paper calls this an ST-condition. *)

Identity Coercion TS_to_Fun: TS_type >-> Funclass . 



(** *** Property TtS *)

Definition TtS_type { BB : lBsystem_carrier }
           { T : T_ops_type BB } ( Tax1b : T_ax1b_type T )
           { Tt : Tt_ops_type BB } ( Ttax1 : Tt_ax1_type T Tt )
           { S : S_ops_type BB } ( Sax0 : S_ax0_type S ) ( Sax1a : S_ax1a_type S )
           ( Sax1b : S_ax1b_type S )
           { St : St_ops_type BB } ( Stax1 : St_ax1_type S St ) :=
  forall ( r s : Tilde BB ) ( X1 : BB ) ( innr1 : S_dom r X1 ) ( inn1s : Tt_dom X1 s ) ,
    Tt ( S r X1 innr1 ) ( St r s ( S_Tt_dom_comp innr1 inn1s ) )
       ( Tt_dom_r1_1s_to_Sr1_Strs Sax0 Sax1a Sax1b Stax1 innr1 inn1s ) =
    St r ( Tt X1 s inn1s ) ( St_dom_r1_1s_to_r_Tt1s Tax1b Ttax1 innr1 inn1s ) .

(** This definition corresponds to Definition 3.1.4(b) in arXiv:1410.5389v1.
    Notice that the paper calls this an ST-condition. *)

Identity Coercion TtS_to_Fun: TtS_type >-> Funclass . 



(** *** Implications of the zeroth and first properties of operations of type T, Tt, S and St that are required for the formulation of the property STt and StTt. *)


Lemma S_dom_1r_r2_to_Tt1r_T12 { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( Tax0 : T_ax0_type T ) ( Tax1a : T_ax1a_type T )
      { Tt : Tt_ops_type BB } ( Ttax1 : Tt_ax1_type T Tt )        
      { r : Tilde BB } { X1 X2 : BB }
      ( inn1r : Tt_dom X1 r ) ( innr2 : S_dom r X2 ) :
  S_dom ( Tt X1 r inn1r ) ( T X1 X2 ( Tt_S_dom_comp inn1r innr2 ) ) .
Proof .
  unfold S_dom . 
  rewrite Ttax1 . 
  exact ( isabove_T_T_2 Tax0 Tax1a _ _ innr2 ) . 
Defined.

Lemma St_dom_1r_rs_to_Tt1r_Tt1s { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( Tax0 : T_ax0_type T ) ( Tax1a : T_ax1a_type T )
      { Tt : Tt_ops_type BB } ( Ttax1 : Tt_ax1_type T Tt )
      { r s : Tilde BB } { X1 : BB }
      ( inn1r : Tt_dom X1 r ) ( innrs : St_dom r s ) :
  St_dom ( Tt X1 r inn1r ) ( Tt X1 s ( Tt_St_dom_comp inn1r innrs ) ) .
Proof.
  unfold St_dom . 
  rewrite Ttax1 . 
  exact ( S_dom_1r_r2_to_Tt1r_T12 Tax0 Tax1a Ttax1 _ _ ) .
Defined.



Lemma  T_dom_1r_r2_to_1_Sr2 { BB : lBsystem_carrier }
       { S : S_ops_type BB } ( Sax1b : S_ax1b_type S ) 
       { r : Tilde BB } { X1 X2 : BB }
       ( inn1r : Tt_dom X1 r ) ( innr2 : S_dom r X2 ) : T_dom X1 ( S r X2 innr2 ) .
Proof.
  use T_dom_constr.
  + exact ( T_dom_gt0 inn1r ) . 
  + exact ( isabov_trans ( Sax1b _ _ _ ) ( isover_ft' ( T_dom_isabove inn1r ) ) ) .  
Defined.

Lemma  Tt_dom_1r_rs_to_1_Strs { BB : lBsystem_carrier }
       { S : S_ops_type BB } ( Sax1b : S_ax1b_type S )
       { St : St_ops_type BB } ( Stax1 : St_ax1_type S St )
       { r s : Tilde BB } { X1 : BB }
       ( inn1r : Tt_dom X1 r ) ( innrs : St_dom r s ) : Tt_dom X1 ( St r s innrs )  .
Proof .
  unfold Tt_dom .
  rewrite Stax1 . 
  exact ( T_dom_1r_r2_to_1_Sr2 Sax1b inn1r _ ) . 
Defined.

  


(** *** Property STt *)

Definition STt_type { BB : lBsystem_carrier }
           { T : T_ops_type BB } ( Tax0 : T_ax0_type T ) ( Tax1a : T_ax1a_type T )
           { Tt : Tt_ops_type BB } ( Ttax1 : Tt_ax1_type T Tt )
           { S : S_ops_type BB } ( Sax1b : S_ax1b_type S ) :=
  forall ( r : Tilde BB ) ( X1 X2 : BB ) ( inn1r : Tt_dom X1 r ) ( innr2 : S_dom r X2 ) ,
    S ( Tt X1 r inn1r ) ( T X1 X2 ( Tt_S_dom_comp inn1r innr2 ) )
      ( S_dom_1r_r2_to_Tt1r_T12  Tax0 Tax1a Ttax1 inn1r innr2 ) =
    T X1 ( S r X2 innr2 ) ( T_dom_1r_r2_to_1_Sr2 Sax1b inn1r innr2 ) .

(** This definition corresponds to Definition 3.1.3(a) in arXiv:1410.5389v1.
    Notice that the paper calls this a TS-condition. *)

Identity Coercion STt_to_Fun: STt_type >-> Funclass . 



(** *** Property StTt *)


Definition StTt_type { BB : lBsystem_carrier }
           { T : T_ops_type BB } ( Tax0 : T_ax0_type T ) ( Tax1a : T_ax1a_type T )
           { Tt : Tt_ops_type BB } ( Ttax1 : Tt_ax1_type T Tt )
           { S : S_ops_type BB } ( Sax1b : S_ax1b_type S )
           { St : St_ops_type BB } ( Stax1 : St_ax1_type S St ) :=
  forall ( r s : Tilde BB ) ( X1 : BB ) ( inn1r : Tt_dom X1 r ) ( innrs : St_dom r s ) ,
    St ( Tt X1 r inn1r ) ( Tt X1 s ( Tt_St_dom_comp inn1r innrs ) )
       ( St_dom_1r_rs_to_Tt1r_Tt1s Tax0 Tax1a Ttax1 inn1r innrs ) =
    Tt X1 ( St r s innrs ) ( Tt_dom_1r_rs_to_1_Strs Sax1b Stax1 inn1r innrs ) .

(** This definition corresponds to Definition 3.1.3(b) in arXiv:1410.5389v1.
    Notice that the paper calls this a TS-condition. *)

Identity Coercion StTt_to_Fun: StTt_type >-> Funclass . 






(* End of the file TS_ST.v *)

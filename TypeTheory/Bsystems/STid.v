(** * The properties STid and StTtid of quadruples of operations T, Tt, S, St. 

By Vladimir Voevodsky, started on Jan. 10, 2015 *)



Require Import UniMath.Foundations.All.

Require Import TypeTheory.Csystems.hSet_ltowers.
Require Export TypeTheory.Bsystems.T_Tt .
Require Export TypeTheory.Bsystems.S_St .

(** *** Properties of the domains of definition of operations S and St required to formulate the properties STid and StTtid *)

Lemma  S_dom_STid { BB : lBsystem_carrier }
           { T : T_ops_type BB } ( Tax1b : T_ax1b_type T )
           { r : Tilde BB } { X : BB }
           ( inn : T_dom ( dd r ) X ) : S_dom r ( T ( dd r ) X inn ) . 
Proof .
  unfold S_dom . 
  exact ( Tax1b _ _ _ ) . 
Defined.

Lemma St_dom_StTtid { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( Tax1b : T_ax1b_type T )
      { Tt : Tt_ops_type BB } ( Ttax1 : Tt_ax1_type T Tt ) 
      { r s : Tilde BB } 
      ( inn : Tt_dom ( dd r ) s ) : St_dom r ( Tt ( dd r ) s inn ) . 
Proof .
  unfold St_dom .
  rewrite Ttax1 . 
  exact (  S_dom_STid Tax1b inn ) . 
Defined.


(** *** The property STid *)

Definition STid_type { BB : lBsystem_carrier }
           { T : T_ops_type BB } ( Tax1b : T_ax1b_type T )
           ( S : S_ops_type BB ) :=
  forall ( r : Tilde BB ) ( X : BB ) ( inn : T_dom ( dd r ) X ) ,
    S r ( T ( dd r ) X inn ) ( S_dom_STid Tax1b inn ) = X .

(** This definition corresponds to Definition 3.1.5(a) in arXiv:1410.5389v1. *)

Identity Coercion STid_to_Fun: STid_type >-> Funclass . 


(** *** The property StTtid *)

Definition StTtid_type { BB : lBsystem_carrier }
           { T : T_ops_type BB } ( Tax1b : T_ax1b_type T )
           { Tt : Tt_ops_type BB } ( Ttax1 : Tt_ax1_type T Tt ) 
           ( St : St_ops_type BB ) :=
  forall ( r s : Tilde BB ) ( inn : Tt_dom ( dd r ) s ) ,
    St r ( Tt ( dd r ) s inn ) ( St_dom_StTtid Tax1b Ttax1 inn ) = r .

(** This definition corresponds to Definition 3.1.5(b) in arXiv:1410.5389v1. *)

Identity Coercion StTtid_to_Fun: StTtid_type >-> Funclass . 



  



(* End of the file STid.v *)

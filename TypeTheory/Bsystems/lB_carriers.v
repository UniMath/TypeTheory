(** * Carriers of the lB-systems defined in terms of two sorts and the length function 

by Vladimir Voevodsky, file created on Jan. 6, 2015 *)


Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import TypeTheory.Csystems.prelim.
Require Import TypeTheory.Csystems.lTowers.
Require Import TypeTheory.Csystems.ltowers_over .

Require Import TypeTheory.Csystems.hSet_ltowers.



(** **** lB-system carriers *)

Definition lBsystem_carrier :=
  ∑ (B :  hSet_pltower)(TildeB : hSet)( dd : TildeB -> B ),
                                   forall r : TildeB , ll ( dd r ) > 0.


(** Note: the condition that the carrier of an lB-system is based on an h-set is used for the first
time in the formulation of the condition TT (later an axiom TT of the lB-systems). It is possible to avoid 
the use of the h-set condition in the formulation of the TT and other axioms at the cost of making the 
domains of applicability of these axioms to have a much longer description or of introducing additional
axioms to ensure that Lemma isover_T_T_2 and similar lemmas needed for the formulation of other axioms 
hold. *)



Definition lBsystem_carrier_constr { B : hSet_pltower } { TildeB : hSet }
           ( dd : TildeB -> B ) ( is : forall r : TildeB, ll ( dd r ) > 0 ) : lBsystem_carrier .
Proof .
  split with B . 

  split with TildeB . 

  exact ( tpair _ dd is ) .

Defined.

Definition lBsystem_carrier_to_ltower : lBsystem_carrier -> ltower := fun T => pr1 ( pr1 T ) .
Coercion  lBsystem_carrier_to_ltower : lBsystem_carrier >-> ltower . 

Definition lBsystem_carrier_pr1 : lBsystem_carrier -> hSet_pltower := pr1 .
Coercion  lBsystem_carrier_pr1 : lBsystem_carrier >-> hSet_pltower .
                                                                     
                               
Definition Tilde : lBsystem_carrier -> UU := fun BB => pr1 ( pr2 BB ) .

Definition dd { BB : lBsystem_carrier } : Tilde BB -> BB := pr1 ( pr2 ( pr2 BB ) ) .

Definition Tilde_dd { BB : lBsystem_carrier } ( X : BB ) :=
  ∑ r : Tilde BB, dd r = X.

Definition Tilde_dd_pr1 { BB : lBsystem_carrier } { X : BB } : Tilde_dd X -> Tilde BB := pr1 .
Coercion Tilde_dd_pr1 : Tilde_dd >-> Tilde . 


Definition isasetBt ( BB : lBsystem_carrier ) : isaset ( Tilde BB ) :=
  pr2 ( pr1 ( pr2 BB ) ) . 


(** We can define a family BBn : nat -> UU by the formula

BBn BB := fun n => total2 ( fun X : BB => ll X = 0 ) 

The subobject in lBsystem_carrier defined by the condition 

iscontr ( BBn BB 0 ) 

is equivalent to the type of type-and-term structures, i.e. presheaves on the category H 
from the paper by Richard Garner, "Combinatorial structure of type dependency".

*)
                                        

Definition ll_dd { BB : lBsystem_carrier } ( r : Tilde BB ) : ll ( dd r ) > 0 :=
  pr2 ( pr2 ( pr2 BB ) ) r .




(** **** Useful lemmas *)



Definition ll_dd_geh { BB : lBsystem_carrier } ( r : Tilde BB ) : ll ( dd r ) >= 1 :=
  natgthtogehsn _ _ ( ll_dd r ) . 




(** **** lBsystem carriers over an object *)















   
(* End of the file lB_carriers.v *)

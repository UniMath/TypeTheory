(** * Unital lB0-systems

By Vladimir Voevodsky, split off lB0systems.v on March 3, 2015 *)

Unset Automatic Introduction.

Require Export TypeTheory.Bsystems.lB0_non_unital.



(** *** The layer associated with operations dlt *)

Definition dlt_layer { BB : lBsystem_carrier } ( T : T_ops_type BB ) :=
  total2 ( fun dlt : dlt_layer_0 BB => dlt_ax1_type T dlt ) .

Definition dlt_layer_pr1 { BB : lBsystem_carrier }
           ( T : T_ops_type BB )
           ( dlt : dlt_layer T ) : dlt_layer_0 BB := pr1 dlt .
Coercion dlt_layer_pr1 : dlt_layer >-> dlt_layer_0 .

Definition dlt_ax1 { BB : lBsystem_carrier } { T : T_ops_type BB } ( dlt : dlt_layer T ) :
  dlt_ax1_type T dlt := pr2 dlt . 



(** *** Complete definition of a unital lB0-system *)


Definition lB0system :=
  total2 ( fun BB : lB0system_non_unital => dlt_layer ( @T_op BB ) ) .

(** This definition corresponds to the addition of Definition 2.6 in arXiv:1410.5389v1
    of the axiom [dlt_ax1_type], only the packaging order is different in irrelevant ways
    ([lB0system_to_prelBystem] below is not just a projection). *)

Definition lB0system_pr1 : lB0system -> lB0system_non_unital := pr1 .
Coercion lB0system_pr1 : lB0system >-> lB0system_non_unital .

Definition lB0system_pr2 ( BB : lB0system ) : dlt_layer ( @T_op BB ) := pr2 BB .
Coercion lB0system_pr2 : lB0system >-> dlt_layer .

Definition lB0system_to_prelBystem ( BB : lB0system ) : prelBsystem :=
  tpair ( fun X : prelBsystem_non_unital => _ ) BB ( pr1 ( pr2 BB ) ) .
Coercion lB0system_to_prelBystem : lB0system >-> prelBsystem . 






(* End of the file lB0.v *)

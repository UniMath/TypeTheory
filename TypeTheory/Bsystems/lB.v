(** * The type of the unital lBsystems

By Vladimir Voevodsky, started on Jan. 18, 2015 *)

Unset Automatic Introduction.

Require Export TypeTheory.Bsystems.lB_non_unital.
Require Export TypeTheory.Bsystems.lB0.


(** Condition dltT *)

Definition dltT_type { BB : lB_nu } ( dlt : dlt_layer ( @T_op BB ) ) :=
  dlt.dltT_type ( @T_ax0 BB ) ( @T_ax1b BB ) ( @Tt_op BB ) ( dlt_ax1 dlt ) . 

(** Condition dltS *)

Definition dltS_type { BB : lB_nu } ( dlt : dlt_layer ( @T_op BB ) ) :=
  dlt.dltS_type ( @T_ax1b BB ) ( @S_ax0 BB ) ( @St_op BB ) ( dlt_ax1 dlt ) .


(** Condition SdltT *)

Definition SdltT_type { BB : lB_nu } ( dlt : dlt_layer ( @T_op BB ) ) :=
  dlt.SdltT_type ( @T_ax0 BB ) ( @T_ax1a BB ) ( dlt_ax1 dlt ) ( @S_op BB ) .

(** Condition StdltTt *)

Definition StdltTt_type { BB : lB_nu } ( dlt : dlt_layer ( @T_op BB ) ) :=
  dlt.StdltTt_type ( @T_ax0 BB ) ( @T_ax1a BB ) ( dlt_ax1 dlt ) ( @Tt_ax1 BB ) ( @St_op BB ) .

(** Condition dltSid *)

Definition dltSid_type { BB : lB_nu } ( dlt : dlt_layer ( @T_op BB ) ) :=
  dlt.dltSid_type ( @T_ax1b BB ) ( dlt_ax1 dlt ) ( @St_op BB ) .


(** Unital lBsystem *)

Definition lB :=
  total2 ( fun BB : lB_nu =>
             total2 ( fun dlt : dlt_layer ( @T_op BB ) =>
             dirprod
               ( dirprod
                   ( dirprod ( dltT_type dlt ) ( dltS_type dlt ) )
                   ( dirprod ( SdltT_type dlt ) ( StdltTt_type dlt ) ) )
               ( dltSid_type dlt ) ) ) . 


Definition lB_to_lB_nu : lB -> lB_nu := pr1 .
Coercion lB_to_lB_nu : lB >-> lB_nu .

Definition lB_to_lB0 ( BB : lB ) : lB0system :=
  tpair ( fun BB : lB0system_non_unital => dlt_layer ( @T_op BB ) ) BB ( pr1 ( pr2 BB ) ) . 
Coercion lB_to_lB0 : lB >-> lB0system .


Definition dltT { BB : lB } : dltT_type BB := pr1 ( pr1 ( pr1 ( pr2 ( pr2 BB ) ) ) ) . 

Definition dltS { BB : lB } : dltS_type BB := pr2 ( pr1 ( pr1 ( pr2 ( pr2 BB ) ) ) ) .

Definition SdltT { BB : lB } : SdltT_type BB := pr1 ( pr2 ( pr1 ( pr2 ( pr2 BB ) ) ) ) . 

Definition StdltTt { BB : lB } : StdltTt_type BB := pr2 ( pr2 ( pr1 ( pr2 ( pr2 BB ) ) ) ) . 

Definition dltSid { BB : lB } : dltSid_type BB := pr2 ( pr2 ( pr2 BB ) ) . 








(* End of the file lB.v *)
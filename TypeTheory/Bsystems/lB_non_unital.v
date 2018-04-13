(** * Non-unital lB-systems

By Vladimir Voevodsky, started on Jan. 16, 2015 *)



Require Import UniMath.Foundations.All.

Require Import TypeTheory.Csystems.hSet_ltowers.
Require Export TypeTheory.Bsystems.TS_ST.
Require Export TypeTheory.Bsystems.STid .
Require Export TypeTheory.Bsystems.lB0. 




(** *** Conditions TT and TTt *)

Definition TT_type { BB : lB0system_non_unital } :=
  T_Tt.TT_type ( @T_ax0 BB ) ( @T_ax1a BB ) ( @T_ax1b BB ) .

Definition TTt_type { BB : lB0system_non_unital } :=
  T_Tt.TTt_type ( @T_ax0 BB ) ( @T_ax1a BB ) ( @T_ax1b BB ) ( @Tt_ax1 BB ) .

Definition TT_TTt_layer ( BB : lB0system_non_unital ) := ( @TT_type BB ) × ( @TTt_type BB ) . 
                   


(** *** Conditions SSt and StSt *)

Definition SSt_type { BB : lB0system_non_unital } :=
  S_St.SSt_type ( @S_ax0 BB ) ( @S_ax1a BB ) ( @S_ax1b BB ) ( @St_ax1 BB ) .

Definition StSt_type { BB : lB0system_non_unital } :=
  S_St.StSt_type ( @S_ax0 BB ) ( @S_ax1a BB ) ( @S_ax1b BB ) ( @St_ax1 BB ) .

Definition SSt_StSt_layer ( BB : lB0system_non_unital ) := ( @SSt_type BB ) × ( @StSt_type BB ) . 



(** *** Conditions TS and TtS *)

Definition TS_type { BB : lB0system_non_unital } :=
  TS_ST.TS_type ( @T_ax1b BB ) ( @S_ax0 BB ) ( @S_ax1a BB ) ( @S_ax1b BB ) .

Definition TtS_type { BB : lB0system_non_unital } :=
  TS_ST.TtS_type ( @T_ax1b BB ) ( @Tt_ax1 BB )
                           ( @S_ax0 BB ) ( @S_ax1a BB ) ( @S_ax1b BB ) ( @St_ax1 BB ) .

Definition TS_TtS_layer ( BB : lB0system_non_unital ) := ( @TS_type BB ) × ( @TtS_type BB ) .



(** *** Conditions STt and StTt *)

Definition STt_type { BB : lB0system_non_unital } :=
  TS_ST.STt_type ( @T_ax0 BB ) ( @T_ax1a BB ) ( @Tt_ax1 BB ) ( @S_ax1b BB ) . 

Definition StTt_type { BB : lB0system_non_unital } :=
  TS_ST.StTt_type ( @T_ax0 BB ) ( @T_ax1a BB ) ( @Tt_ax1 BB )  ( @S_ax1b BB ) ( @St_ax1 BB ) .

Definition ST_StTt_layer ( BB : lB0system_non_unital ) := ( @STt_type BB ) × ( @StTt_type BB ) .



(** *** Conditions STid and StTtid *) 

Definition STid_type { BB : lB0system_non_unital } :=
  STid.STid_type ( @T_ax1b BB ) ( @S_op BB ) . 

Definition StTtid_type { BB : lB0system_non_unital } :=
  STid.StTtid_type ( @T_ax1b BB ) ( @Tt_ax1 BB ) ( @St_op BB ) .

Definition STid_layer ( BB : lB0system_non_unital ) := ( @STid_type BB ) × ( @StTtid_type BB ) .





(** *** Complete definition of non-unital lB-system *)


Definition lB_nu :=
  ∑ BB : lB0system_non_unital,
               ( ( ( TT_TTt_layer BB ) × ( SSt_StSt_layer BB ) ) ×
                 ( ( TS_TtS_layer BB ) × ( ST_StTt_layer BB ) ) )
                 × ( STid_layer BB ).

(** This definition corresponds to Definition 3.1 in arXiv:1410.5389v1. *)
                                                             
                                                             
Definition lB_nu_pr1 : lB_nu -> lB0system_non_unital := pr1 .
Coercion lB_nu_pr1 : lB_nu >-> lB0system_non_unital .


Definition TT { BB : lB_nu } : @TT_type BB := pr1 ( pr1 ( pr1 ( pr1 ( pr2 BB ) ) ) ) .

Definition TTt { BB : lB_nu } : @TTt_type BB := pr2 ( pr1 ( pr1 ( pr1 ( pr2 BB ) ) ) ) .

Definition SSt { BB : lB_nu } : @SSt_type BB := pr1 ( pr2 ( pr1 ( pr1 ( pr2 BB ) ) ) ) .

Definition StSt { BB : lB_nu } : @StSt_type BB := pr2 ( pr2 ( pr1 ( pr1 ( pr2 BB ) ) ) ) . 

Definition TS { BB : lB_nu } : @TS_type BB := pr1 ( pr1 ( pr2 ( pr1 ( pr2 BB ) ) ) ) .  

Definition TtS { BB : lB_nu } : @TtS_type BB := pr2 ( pr1 ( pr2 ( pr1 ( pr2 BB ) ) ) ) .   

Definition STt { BB : lB_nu } : @STt_type BB := pr1 ( pr2 ( pr2 ( pr1 ( pr2 BB ) ) ) ) .    

Definition StTt { BB : lB_nu } : @StTt_type BB := pr2 ( pr2 ( pr2 ( pr1 ( pr2 BB ) ) ) ) . 

Definition STid_ax { BB : lB_nu } : @STid_type BB := pr1 ( pr2 ( pr2 BB ) ) .  

Definition StTtid { BB : lB_nu } : @StTtid_type BB := pr2 ( pr2 ( pr2 BB ) ) .  





(* End of the file lB_non_unital.v *)

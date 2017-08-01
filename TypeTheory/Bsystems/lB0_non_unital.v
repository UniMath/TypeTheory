(** ** lB0-systems

By Vladimir Voevodsky, started on Jan. 24, 2015 *)

Unset Automatic Introduction.

Require Export TypeTheory.Bsystems.prelB. 
Require Export TypeTheory.Bsystems.TS_ST.
Require Export TypeTheory.Bsystems.STid .
Require Export TypeTheory.Bsystems.dlt .



(** ** Non-unital lB0-systems *)

(** *** Definitions of the main layers *)

(** **** The layer associated with operations T *)

Definition T_layer ( BB : lBsystem_carrier ) :=
  total2 ( fun T : T_layer_0 BB => dirprod ( T_ax1a_type T ) ( T_ax1b_type T ) ) .

Definition T_layer_to_T_layer_0 ( BB : lBsystem_carrier ) : T_layer BB -> T_layer_0 BB :=
  pr1 . 
Coercion T_layer_to_T_layer_0 : T_layer >-> T_layer_0 . 
 


(** **** The layer associated with operations Tt *)


Definition Tt_layer { BB : lBsystem_carrier } ( T : T_ops_type BB ) :=
  total2 ( fun Tt : Tt_ops_type BB => Tt_ax1_type T Tt ) .

Definition Tt_layer_to_Tt_ops_type ( BB : lBsystem_carrier ) ( T : T_ops_type BB )
  ( Tt : Tt_layer T ) : Tt_ops_type BB := pr1 Tt .
Coercion Tt_layer_to_Tt_ops_type : Tt_layer >-> Tt_ops_type . 


(** **** The structure formed by operations T and Tt *)

Definition T_Tt_layer ( BB : lBsystem_carrier ) :=
  total2 ( fun T : T_layer BB => Tt_layer T ) .

Definition T_Tt_layer_to_T_layer { BB : lBsystem_carrier } ( T_Tt : T_Tt_layer BB ) :
  T_layer BB := pr1 T_Tt .
Coercion T_Tt_layer_to_T_layer : T_Tt_layer >->  T_layer .

Definition T_Tt_layer_to_Tt_layer { BB : lBsystem_carrier } ( T_Tt : T_Tt_layer BB ) :
  Tt_layer T_Tt := pr2 T_Tt .
Coercion T_Tt_layer_to_Tt_layer : T_Tt_layer >-> Tt_layer .  


(** **** The layer associated with operations S *)


Definition S_layer ( BB : lBsystem_carrier ) :=
  total2 ( fun S : S_layer_0 BB =>  dirprod ( S_ax1a_type S ) ( S_ax1b_type S ) ) .

Definition S_layer_to_S_layer_0 ( BB : lBsystem_carrier ) :
  S_layer BB -> S_layer_0 BB := pr1 .
Coercion S_layer_to_S_layer_0 : S_layer >-> S_layer_0 . 


(** **** The layer associated with operations St *)


Definition St_layer { BB : lBsystem_carrier } ( S : S_ops_type BB ) :=
  total2 ( fun St : St_ops_type BB => St_ax1_type S St ) .

Definition St_layer_to_St_ops_type ( BB : lBsystem_carrier ) ( S : S_ops_type BB )
  ( St : St_layer S ) : St_ops_type BB := pr1 St.
Coercion St_layer_to_St_ops_type : St_layer >-> St_ops_type .


(** **** The structure formed by operations S and St *)

Definition S_St_layer ( BB : lBsystem_carrier ) :=
  total2 ( fun S : S_layer BB => St_layer S ) .

Definition S_St_layer_to_S_layer { BB : lBsystem_carrier } ( S_St : S_St_layer BB ) :
  S_layer BB := pr1 S_St .
Coercion S_St_layer_to_S_layer : S_St_layer >->  S_layer .

Definition S_St_layer_to_St_layer { BB : lBsystem_carrier } ( S_St : S_St_layer BB ) :
  St_layer S_St := pr2 S_St .
Coercion S_St_layer_to_St_layer : S_St_layer >-> St_layer .  


(** **** Complete definition of a non-unital lB0-system *)

Definition T_ax1_type ( BB : prelBsystem_non_unital ) :=
  dirprod ( T_ax1a_type ( @T_op BB ) ) ( T_ax1b_type ( @T_op BB ) ) .

Definition Tt_ax1_type' ( BB : prelBsystem_non_unital ) :=
  Tt_ax1_type ( @T_op BB ) ( @Tt_op BB ) .

Definition S_ax1_type ( BB : prelBsystem_non_unital ) :=
  dirprod ( S_ax1a_type ( @S_op BB ) ) ( S_ax1b_type ( @S_op BB ) ) .

Definition St_ax1_type' ( BB : prelBsystem_non_unital ) :=
  St_ax1_type ( @S_op BB ) ( @St_op BB ) .

Definition lB0system_non_unital :=
  total2 ( fun BB : prelBsystem_non_unital =>
             dirprod
               ( dirprod ( T_ax1_type BB ) ( Tt_ax1_type' BB ) )
               ( dirprod ( S_ax1_type BB ) ( St_ax1_type' BB ) ) ) . 

Definition lB0system_non_unital_pr1 : lB0system_non_unital -> prelBsystem_non_unital := pr1 .
Coercion lB0system_non_unital_pr1 : lB0system_non_unital >-> prelBsystem_non_unital .


(** *** Access functions to the axioms *)

 
Definition T_ax1a { BB : lB0system_non_unital } : T_ax1a_type ( @T_op BB ) :=
  pr1 ( pr1 ( pr1 ( pr2 BB ) ) ) .

Definition T_ax1b { BB : lB0system_non_unital } : T_ax1b_type ( @T_op BB ) :=
  pr2 ( pr1 ( pr1 ( pr2 BB ) ) ) .

Definition Tt_ax1 { BB : lB0system_non_unital } : Tt_ax1_type ( @T_op BB ) ( @Tt_op BB ) :=
  pr2 ( pr1 ( pr2 BB ) ) .

Definition Tt_ax0 { BB : lB0system_non_unital } : Tt_ax0_type ( @Tt_op BB ) :=
  Tt_ax1_to_Tt_ax0 ( @T_ax0 BB ) ( @Tt_ax1 BB ) .  


Definition S_ax1a { BB : lB0system_non_unital } : S_ax1a_type ( @S_op BB ) :=
  pr1 ( pr1 ( pr2 ( pr2 BB ) ) ) .

Definition S_ax1b { BB : lB0system_non_unital } : S_ax1b_type ( @S_op BB ) :=
  pr2 ( pr1 ( pr2 ( pr2 BB ) ) ) .

Definition St_ax1 { BB : lB0system_non_unital } : St_ax1_type ( @S_op BB ) ( @St_op BB ) :=
  pr2 ( pr2 ( pr2 BB ) ) .

Definition St_ax0 { BB : lB0system_non_unital } : St_ax0_type ( @St_op BB ) :=
  St_ax1_to_St_ax0 ( @S_ax0 BB ) ( @St_ax1 BB ) .



(** *** Derived operations re-defined in a more streamlined form *)


(** **** Derived operations related to operation T *)



Definition T_fun { BB : lB0system_non_unital } ( X : BB ) ( gt0 : ll X > 0 ) :
  ltower_fun ( ltower_over ( ft X ) ) ( ltower_over X ) :=
  T_fun.T_fun ( @T_ax0 BB ) ( @T_ax1a BB ) ( @T_ax1b BB ) gt0 . 
  
Definition Tj_fun { BB : lB0system_non_unital } { A X1 : BB } ( isov : isover X1 A ) :
  ltower_fun ( ltower_over A ) ( ltower_over X1 ) :=
  T_fun.Tj_fun ( @T_ax0 BB ) ( @T_ax1a BB ) ( @T_ax1b BB ) isov .

Definition Tj_fun_compt { BB : lB0system_non_unital } { X Y : BB } ( isab : isabove X Y ) :
  Tj_fun isab = ltower_funcomp ( Tj_fun ( isover_ft' isab ) ) ( T_fun X ( isabove_gt0 isab ) ) :=
  Tj_fun_compt ( @T_ax0 BB ) ( @T_ax1a BB ) ( @T_ax1b BB ) isab . 

Definition Tj { BB : lB0system_non_unital } { X A Y : BB }
           ( isov1 : isover X A ) ( isov2 : isover Y A ) : BB :=
  pocto ( Tj_fun isov1 (  obj_over_constr isov2 ) ) .

Definition isover_Tj { BB : lB0system_non_unital } { X A Y : BB }
           ( isov1 : isover X A ) ( isov2 : isover Y A ) : isover ( Tj isov1 isov2 ) X :=
  pr2 ( Tj_fun isov1 (  obj_over_constr isov2 ) ) .

Definition Tj_compt { BB : lB0system_non_unital } { X A Y : BB }
           ( isab : isabove X A ) ( isov2 : isover Y A ) :
  Tj isab isov2 =
  T_ext X ( Tj ( isover_ft' isab ) isov2 ) ( isabove_gt0 isab ) ( isover_Tj ( isover_ft' isab ) isov2 ) . 
Proof.
  intros.
  unfold Tj .  
  rewrite Tj_fun_compt . 
  apply idpath . 

Defined.


Definition Tprod_over { BB : lB0system_non_unital } ( X1 : BB ) :
  ltower_fun BB ( ltower_over X1 ) :=
  T_fun.Tprod_fun ( @T_ax0 BB ) ( @T_ax1a BB ) ( @T_ax1b BB ) X1 .  
           

Definition Tprod { BB : lB0system_non_unital } ( X Y : BB ) : BB := pocto ( Tprod_over X Y ) .

Definition isover_Tprod { BB : lB0system_non_unital } ( X Y : BB ) :
  isover ( Tprod X Y ) X := pr2 ( Tprod_over X Y ) .

Lemma ll_Tprod { BB : lB0system_non_unital } ( X Y : BB ) : ll ( Tprod X Y ) = ll X + ll Y .
Proof.
  intros.
  unfold Tprod .
  rewrite ll_pocto .
  rewrite natpluscomm . 
  rewrite ( @ll_ltower_fun BB _ ( Tprod_over X ) ) . 
  apply idpath . 

Defined.



Definition Tprod_compt { BB : lB0system_non_unital } ( X Y : BB ) ( gt0 : ll X > 0 ) :
  Tprod X Y = T_ext X ( Tprod ( ft X ) Y ) gt0 ( isover_Tprod _ _ ) .
Proof.
  intros.
  assert ( int :=
             T_fun.Tprod_compt
               ( @T_ax0 BB ) ( @T_ax1a BB ) ( @T_ax1b BB ) X Y gt0 ).
  exact ( maponpaths pocto int ) . 

Defined.


(** **** Derived operations related to operation S *)



Lemma ll_S_ext { BB : lB0system_non_unital }
      ( r : Tilde BB ) ( X : BB ) ( inn : isover X ( dd r )  ) : ll ( S_ext r X inn ) = ll X - 1.
Proof.
  intros.
  apply S_fun.ll_S_ext .
  apply ( @S_ax0 BB ) .

  apply ( @S_ax1b BB ) . 

Defined.

  

Definition S_fun { BB : lB0system_non_unital } ( r : Tilde BB ) :
  ltower_fun ( ltower_over ( dd r ) ) ( ltower_over ( ft ( dd r ) ) ) :=
  ltower_fun_S ( @S_ax0 BB ) ( @S_ax1a BB ) ( @S_ax1b BB ) r . 










(* End of the file lB0_non_unital.v *)


(** ** The functions of the over-towers defined by S

by Vladimir Voevodsky, started on Feb. 1, 2015 *)

Unset Automatic Introduction.

Require Export TypeTheory.Bsystems.S_St .


(** *** The definition of an extended operation S and its elementary properties. *)

Definition S_ext_dom { BB : lBsystem_carrier } ( r : Tilde BB ) ( X : BB ) := isover X ( dd r ) .

Identity Coercion S_dom_to_isabove : S_ext_dom >-> isover .


Definition S_ext { BB : lBsystem_carrier } ( S : S_ops_type BB )
           { r : Tilde BB } { X : BB } ( inn : S_ext_dom r X ) : BB .
Proof .
  intros. 
  destruct ( ovab_choice inn ) as [ isab | eq ] . 
  exact ( S _ _ isab ) . 

  exact ( ft ( dd r ) ) .

Defined.

Lemma isover_S_ext { BB : lBsystem_carrier }
      ( S : S_ops_type BB ) ( ax1b : S_ax1b_type S )
      { r : Tilde BB } { X : BB } ( inn : S_ext_dom r X ) :
  isover ( S_ext S inn ) ( ft ( dd r ) ) .
Proof .
  intros .
  unfold S_ext . 
  destruct ( ovab_choice inn ) as [ isab | eq ] .
  exact ( ax1b _ _ _ ) . 

  exact ( isover_XX _ ) . 

Defined.


Lemma ll_S_ext { BB : lBsystem_carrier }
      { S : S_ops_type BB } ( ax0 : S_ax0_type S ) ( ax1b : S_ax1b_type S )
      ( r : Tilde BB ) ( X : BB ) ( inn : S_ext_dom r X ) : ll ( S_ext S inn ) = ll X - 1.
Proof.
  intros .
  unfold S_ext . 
  simpl . 
  destruct ( ovab_choice inn ) as [ isab | eq ] . 
  apply ax0 . 

  rewrite ll_ft .  
  rewrite eq . 
  apply idpath .

Defined.



Lemma isover_S_ext_S_ext_2 { BB : lBsystem_carrier }
      { S : S_ops_type BB } ( ax0 :  S_ax0_type S ) ( ax1a : S_ax1a_type S ) ( ax1b : S_ax1b_type S )
      { r : Tilde BB } { X2 X2' : BB } ( inn : S_ext_dom r X2 ) ( inn' : S_ext_dom r X2' )
      ( is : isover X2 X2' ) : isover ( S_ext S inn ) ( S_ext S inn' ) .
Proof .
  intros . unfold S_ext .
  destruct ( ovab_choice inn ) as [ isab | eq ] .
  destruct ( ovab_choice inn' ) as [ isab' | eq' ] .
  apply ( isover_S_S_2 ax0 ax1a _ _ is ) . 

  exact ( ax1b _ _ _ ) . 

  destruct ( ovab_choice inn' ) as [ isab' | eq' ] .
  assert ( absd : empty ) .
  rewrite eq in is . 
  assert ( ge := isover_geh is ) .  
  assert ( gt := isabove_gth isab' ) . 
  exact ( natgthnegleh gt ge ) . 

  destruct absd . 

  exact ( isover_XX _ ) . 

Defined.




(** *** The over-monotone function S_fun of the over-towers defined by the extended operation S *)



Definition S_fun { BB : lBsystem_carrier }
      { S : S_ops_type BB } ( ax1b : S_ax1b_type S )
      ( r : Tilde BB ) ( X2' : ltower_over ( dd r ) ) : ltower_over ( ft ( dd r ) ) .
Proof .
  intros .
  set ( X2 := pr1 X2' ) . set ( isov := pr2 X2' : isover X2 ( dd r ) ) .
  split with ( S_ext S isov )  .

  apply ( isover_S_ext S ax1b ) .

Defined.


Lemma isovmonot_S_fun { BB : lBsystem_carrier }
      { S : S_ops_type BB } ( ax0 : S_ax0_type S ) ( ax1a : S_ax1a_type S ) ( ax1b : S_ax1b_type S )
      ( r : Tilde BB )
      ( X3' X2' : ltower_over ( dd r ) ) ( isov : isover X3' X2' ) :
  isover ( S_fun ax1b r X3' ) ( S_fun ax1b r X2' ) .
Proof .
  intros .
  apply isinvovmonot_pocto .
  unfold S_fun . simpl .
  apply ( isover_S_ext_S_ext_2 ax0 ax1a ax1b ) .
  apply isovmonot_pocto . 
  exact isov . 

Defined.

Definition ovmonot_S_fun { BB : lBsystem_carrier }
      { S : S_ops_type BB } ( ax0 : S_ax0_type S ) ( ax1a : S_ax1a_type S ) ( ax1b : S_ax1b_type S )
      ( r : Tilde BB ) : ovmonot_fun ( ltower_over ( dd r ) ) ( ltower_over ( ft ( dd r ) ) ) :=
  ovmonot_fun_constr _ ( isovmonot_S_fun ax0 ax1a ax1b r ) .


Lemma ll_S_fun { BB : lBsystem_carrier }
      { S : S_ops_type BB } ( ax0 : S_ax0_type S ) ( ax1b : S_ax1b_type S )
      { r : Tilde BB } ( X2' : ltower_over ( dd r ) ) : ll ( S_fun ax1b r X2' ) = ll X2' .
Proof.
  intros .
  change _ with ( ll ( pr1 ( S_fun ax1b r X2' ) ) - ll ( ft ( dd r ) ) = ll ( pr1 X2' ) - ll ( dd r ) ) .  
  unfold S_fun . unfold S_ext . 
  simpl . 
  destruct ( ovab_choice (pr2 X2') ) as [ isab | eq ] . 
  rewrite ax0 . 
  rewrite ll_ft . 
  apply natmiusmius1mminus1 . 
  apply ( isabove_gt0 isab ) . 

  apply ll_dd . 

  rewrite natminusnn . 
  rewrite eq . 
  rewrite natminusnn . 
  apply idpath .

Defined.


Lemma isllmonot_S_fun { BB : lBsystem_carrier }
      { S : S_ops_type BB } ( ax0 : S_ax0_type S ) ( ax1b : S_ax1b_type S )
      ( r : Tilde BB ) : isllmonot ( S_fun ax1b r ) .
Proof.
  intros. unfold isllmonot. intros X Y .
  repeat rewrite ll_S_fun .
  apply idpath .

  apply ax0.

  apply ax0.

Defined.


Lemma isbased_S_fun { BB : lBsystem_carrier }
      { S : S_ops_type BB } ( ax0 : S_ax0_type S ) ( ax1b : S_ax1b_type S )
      ( r : Tilde BB ) : isbased ( S_fun ax1b r ) .
Proof.
  intros. unfold isbased. intros X eq0 .
  rewrite ll_S_fun . 

  exact eq0.

  exact ax0.

Defined.


Definition ltower_fun_S { BB : lBsystem_carrier }
      { S : S_ops_type BB } ( ax0 : S_ax0_type S ) ( ax1a : S_ax1a_type S ) ( ax1b : S_ax1b_type S )
      ( r : Tilde BB ) :
  ltower_fun ( ltower_over ( dd r ) ) ( ltower_over ( ft ( dd r ) ) ) :=
  ltower_fun_constr ( isovmonot_S_fun ax0 ax1a ax1b r )
                    ( isllmonot_S_fun ax0 ax1b r )
                    ( isbased_S_fun ax0 ax1b r ) . 












  



  

(* The end of the file S_fun.v *)

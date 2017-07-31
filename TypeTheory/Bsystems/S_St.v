(** * Operations S and St on carriers of lB-systems and 
their properties SSt and StSt .

by Vladimir Voevodsky, file created on Jan. 6, 2015 *)

Unset Automatic Introduction.

Require Export TypeTheory.Bsystems.lB_carriers.






(* **** Operation(s) S  

Note: both the domain of definition of operations S and the type of the axiom 1a of operations 
S are obtainable from the same for operations T by removing the condition T_dom_gt0 and 
replacing ( ft X1 ) by ( dd r ). This leads to the possibility of almost direct copy-and_paste
of many proofs concerning T into the context of S. 

Operations T and S are different in the forms of axiom 0 and axiom 1b . 

*)

(** Domains of definition of operations of type S *)


Definition S_dom { BB : lBsystem_carrier } ( r : Tilde BB ) ( X : BB ) :=
  isabove X ( dd r ) .

Identity Coercion S_dom_to_isabove : S_dom >-> isabove . 

Notation S_dom_constr := isabove_constr .
Notation S_dom_gth := isabove_gth .

Definition S_dom_gt1 { BB : lBsystem_carrier } { r : Tilde BB } { Y : BB } ( inn : S_dom r Y ) :
  ll Y > 1 .
Proof .
  intros . exact ( natgthgehtrans _ _ _ ( isabove_gth inn ) ( natgthtogehsn _ _ ( ll_dd _ ) ) ) . 

Defined.


Definition S_dom_gt0 { BB : lBsystem_carrier } { r : Tilde BB } { Y : BB } ( inn : S_dom r Y ) :
  ll Y > 0 .
Proof .
  intros .  exact ( istransnatgth _ _ _ ( isabove_gth inn ) ( ll_dd _ ) )  . 

Defined.

Definition S_dom_ge1 { BB : lBsystem_carrier } { r : Tilde BB } { Y : BB } ( inn : S_dom r Y ) :
  ll Y >= 1 .
Proof .
  intros .  exact ( natgthtogehsn _ _ ( S_dom_gt0 inn ) ) . 

Defined.


Lemma isaprop_S_dom { BB : lBsystem_carrier } ( r : Tilde BB ) ( Y : BB ) :
  isaprop ( S_dom r Y ) . 
Proof.
  intros . apply isaprop_isabove . 
Defined.


Lemma noparts_S_dom { BB : lBsystem_carrier } { r : Tilde BB } { Y : BB }
      ( inn1 inn2 : S_dom r Y ) : inn1 = inn2 .
Proof .
  intros . apply ( proofirrelevance _ ( isaprop_S_dom r Y ) ) .
Defined .  


(** The type objects of which are candidates for operations S on an lB-system. *)
 

Definition S_ops_type ( BB : lBsystem_carrier ) :=
  forall ( r : Tilde BB ) ( Y : BB ) ( inn : S_dom r Y ) , BB .

Lemma S_equals_2 { BB : lBsystem_carrier } { r : Tilde BB } { Y Y' : BB } ( S : S_ops_type BB )
      ( eq : Y = Y' ) ( inn : S_dom r Y ) ( inn' : S_dom r Y' )  :
  S r Y inn = S r Y' inn' .
Proof.
  intros BB r Y Y' S eq .
  rewrite eq . 
  intros . rewrite ( noparts_S_dom inn inn' ) . 
  apply idpath . 

Defined.



(** The zeros property (later an axiom) of an operation of type S *)

Definition S_ax0_type { BB : lBsystem_carrier } ( S : S_ops_type BB ) :=
  forall ( r : Tilde BB ) ( Y : BB ) ( inn : S_dom r Y ) , ll ( S r Y inn ) = ll Y - 1 .
Identity Coercion S_ax0_to_Fun: S_ax0_type >-> Funclass . 

Lemma ll_S_gt0 { BB : lBsystem_carrier }
      { S : S_ops_type BB } ( ax0 :  S_ax0_type S )
      { r : Tilde BB } { X : BB } ( inn : S_dom r X ) : ll ( S r X inn ) > 0 .
Proof.
  intros .
  rewrite ax0 .
  exact ( minusgth0 _ _ ( S_dom_gt1 inn ) ) . 

Defined.


(** The first property (later an axiom) of an operation of type S *)

Definition S_ax1a_type { BB : lBsystem_carrier } ( S : S_ops_type BB ) :=
  forall ( r : Tilde BB ) ( Y : BB ) ( inn : S_dom r Y ) ( isab : isabove ( ft Y ) ( dd r ) ) ,
    ft ( S r Y inn ) = S r ( ft Y ) isab .
Identity Coercion S_ax1a_to_Fun: S_ax1a_type >-> Funclass . 

Definition S_ax1b_type { BB : lBsystem_carrier } ( S : S_ops_type BB ) :=
  forall ( r : Tilde BB ) ( Y : BB ) ( inn : S_dom r Y ) ,
    isabove ( S r Y inn ) ( ft ( dd r ) ) .
Identity Coercion S_ax1b_to_Fun: S_ax1b_type >-> Funclass . 



(** The computation of the iterated ft of ( S r Y ) .  *)
          
Lemma ftn_S { BB : lBsystem_carrier } { S : S_ops_type BB } ( ax1a : S_ax1a_type S )
      ( n : nat ) { r : Tilde BB } { Y : BB } ( isab : isabove ( ftn n Y ) ( dd r ) )
      ( inn : S_dom r Y ) :
  ftn n ( S r Y inn ) = S r ( ftn n Y ) isab .
Proof .
  intros BB S ax1a n . induction n as [ | n IHn ] .
  intros .
  rewrite ( noparts_S_dom inn isab ) . 
  apply idpath . 

  intros .
  change ( ftn (Datatypes.S n) (S r Y inn) ) with ( ft ( ftn n (S r Y inn) ) ) .
  assert ( isab' : isabove ( ftn n Y ) ( dd r ) ) .
  exact ( isabove_ft_inv isab ) . 
  
  rewrite ( IHn r Y isab' inn ) . 
  refine ( ax1a _ _ _ _ ) . 

Defined.

Lemma ft_S { BB : lBsystem_carrier } { S : S_ops_type BB } { r : Tilde BB } { Y : BB }
      ( ax0 : S_ax0_type S ) ( ax1b : S_ax1b_type S ) ( iseq : ft Y = dd r )
      ( inn : S_dom r Y ) : ft ( S r Y inn ) = ft ( dd r ) .
Proof.
  intros .
  assert ( isov := ax1b r Y inn : isover ( S r Y inn ) ( ft ( dd r ) ) ) .
  unfold isover in isov . 
  rewrite ll_ft in isov .  rewrite ax0 in isov . rewrite <- ll_ft  in isov .
  rewrite iseq in isov . 
  assert ( int : (ll (dd r) - (ll (dd r) - 1)) = 1 ) . refine ( natminusmmk _ ) .
  exact ( natgthtogehsn _ _ ( ll_dd _ ) ) .

  rewrite int in isov . 
  exact ( ! isov ) . 

Defined.


(** The isover and isabove properties of the expressions S r Y *)


Lemma isover_S_S_2 { BB : lBsystem_carrier }
      { S : S_ops_type BB } ( ax0 :  S_ax0_type S ) ( ax1a : S_ax1a_type S )
      { r : Tilde BB } { Y Y' : BB } ( inn : S_dom r Y ) ( inn' : S_dom r Y' )
      ( is : isover Y Y' ) : isover ( S r Y inn ) ( S r Y' inn' ) .
Proof .
  intros . 
  unfold isover in * .
  repeat rewrite ax0 .
  simpl .
  assert ( isab : isabove ( ftn ( ll Y - ll Y') Y ) ( dd r ) ) .
  rewrite <- is . 
  exact inn' . 

  rewrite ( natmiusmius1mminus1 ( S_dom_gt0 inn ) ( S_dom_gt0 inn' ) ) . 
  rewrite ( ftn_S ax1a _ isab inn ) .
  exact ( S_equals_2 _ is _ _ ) . 

Defined.


Lemma isabove_S_S_2 { BB : lBsystem_carrier }
      { S : S_ops_type BB } ( ax0 :  S_ax0_type S ) ( ax1a : S_ax1a_type S )
      { r : Tilde BB } { Y Y' : BB } ( inn : S_dom r Y ) ( inn' : S_dom r Y' )
      ( is : isabove Y Y' ) : isabove ( S r Y inn ) ( S r Y' inn' ) .
Proof .
  intros .
  refine ( isabove_constr _ _ ) .
  repeat rewrite ax0 .
  refine ( natgthandminusinvr _ _ ) .
  exact ( isabove_gth is ) .

  exact ( S_dom_ge1 inn' ) . 

  exact ( isover_S_S_2 ax0 ax1a _ _ is ) . 

Defined.



(** **** Operation(s) St  *)


(** Domains of definition of operations of type St *)


Definition St_dom { BB : lBsystem_carrier } ( r : Tilde BB ) ( s : Tilde BB ) :=
  S_dom r ( dd s ) .

Identity Coercion St_dom_to_S_dom : St_dom >-> S_dom . 

Notation St_dom_constr := S_dom_constr .
Notation St_dom_gth := S_dom_gth .

Lemma St_S_dom_comp { BB : lBsystem_carrier } { r s : Tilde BB } { Y : BB }
      ( innrs : St_dom r s ) ( inn : S_dom s Y ) : S_dom r Y .
Proof .
  intros .
  exact ( isabove_trans inn innrs ) .
  
Defined.

Lemma St_St_dom_comp { BB : lBsystem_carrier } { r s t : Tilde BB }
      ( innrs : St_dom r s ) ( innst : St_dom s t ) : St_dom r t .
Proof .
  intros .
  unfold St_dom in * . 
  unfold S_dom in * . 
  exact ( isabove_trans innst innrs ) . 

Defined.

  




(** The type objects of which are candidates for operations St on an lB-system. *)
 

Definition St_ops_type ( BB : lBsystem_carrier ) :=
  forall ( r : Tilde BB ) ( s : Tilde BB ) ( inn : St_dom r s ) , Tilde BB .
Identity Coercion St_ops_to_Fun: St_ops_type >-> Funclass . 


(** The zeros property (later an axiom) of an operation of type St 
It will be shown to be a corollary of the first property of St and the zeros property of S. 
However it is convenient to have it separately for the use in the definition of a prelBsystem. *)

Definition St_ax0_type { BB : lBsystem_carrier } ( St : St_ops_type BB ) :=
  forall ( r s : Tilde BB ) ( inn : St_dom r s ) ,
    ll ( dd ( St r s inn ) ) = ll ( dd s ) - 1 .

(** The first property (later an axiom) of an operation of type St *)


Definition St_ax1_type { BB : lBsystem_carrier }
           ( S : S_ops_type BB )
           ( St : St_ops_type BB ) := 
  forall ( r : Tilde BB ) ( s : Tilde BB ) ( inn : St_dom r s ) ,
    dd ( St r s inn ) = S r ( dd s ) inn .
Identity Coercion St_ax1_to_Fun: St_ax1_type >-> Funclass .

Lemma St_ax1_to_St_ax0 { BB : lBsystem_carrier }
      { S : S_ops_type BB } ( ax0 : S_ax0_type S )
      { St : St_ops_type BB } ( ax1 : St_ax1_type S St ) : St_ax0_type St .
Proof .
  intros .
  unfold St_ax0_type . 
  intros . 
  rewrite ax1 . 
  exact ( ax0 _ _ _ ) . 

Defined.


(** Implications of the zeros and first properties of operations of type S and St
that are required for the formulation of the properties StS and StSt *)


Lemma ll_dd_St { BB : lBsystem_carrier } { S : S_ops_type BB } { St : St_ops_type BB }
      ( ax0 : S_ax0_type S ) ( ax1 : St_ax1_type S St )
      { r s : Tilde BB } ( inn : St_dom r s ) :
  ll ( dd ( St r s inn ) ) = ll ( dd s ) - 1 . 
Proof .
  intros .
  rewrite ax1 . 
  exact ( ax0 _ _ inn ) . 

Defined .


Lemma S_dom_rs_sY_to_Strs_SrY { BB : lBsystem_carrier } { S : S_ops_type BB }
           ( ax0 : S_ax0_type S ) ( ax1a : S_ax1a_type S ) 
           { St : St_ops_type BB } ( ax1t : St_ax1_type S St )
           { r s : Tilde BB } { Y : BB } ( innrs : St_dom r s ) ( inn : S_dom s Y ) :
  S_dom ( St r s innrs ) ( S r Y ( St_S_dom_comp innrs inn ) ) .
Proof .
  intros .
  unfold S_dom . 
  rewrite ax1t . 
  exact ( isabove_S_S_2 ax0 ax1a _ _ inn ) . 

Defined.

Lemma S_dom_rs_sY_to_r_SsY { BB : lBsystem_carrier } { S : S_ops_type BB }
      ( ax1b : S_ax1b_type S ) { r s : Tilde BB } { Y : BB }
      ( innrs : St_dom r s ) ( inn : S_dom s Y ) :
  S_dom r ( S s Y inn ) .
Proof .
  intros . 
  unfold S_dom . 
  refine ( isabov_trans ( ax1b _ _ _ ) _ ) . 
  exact ( isover_ft' innrs ) . 

Defined.

Lemma  St_dom_rs_st_to_Strs_Strt { BB : lBsystem_carrier } { S : S_ops_type BB }
           ( ax0 : S_ax0_type S ) ( ax1a : S_ax1a_type S ) 
           { St : St_ops_type BB } ( ax1t : St_ax1_type S St )
           { r s t : Tilde BB } ( innrs : St_dom r s ) ( innst : St_dom s t ) :
  St_dom ( St r s innrs ) ( St r t ( St_St_dom_comp innrs innst ) ) .
Proof .
  intros .
  unfold St_dom .
  rewrite ax1t . 
  exact ( S_dom_rs_sY_to_Strs_SrY ax0 ax1a ax1t innrs innst ) . 

Defined. 

Lemma St_dom_rs_st_to_r_Stst { BB : lBsystem_carrier }
      { S : S_ops_type BB } ( ax1b : S_ax1b_type S )
      { St : St_ops_type BB } ( ax1t : St_ax1_type S St )
      { r s t : Tilde BB } ( innrs : St_dom r s ) ( innst : St_dom s t ) :
  St_dom r ( St s t innst ) .
Proof .
  intros . 
  unfold St_dom . 
  rewrite ax1t . 
  exact ( S_dom_rs_sY_to_r_SsY ax1b innrs innst ) . 

Defined.








(** Property SSt *)

Definition SSt_type { BB : lBsystem_carrier } { S : S_ops_type BB }
           ( ax0 : S_ax0_type S ) ( ax1a : S_ax1a_type S ) ( ax1b : S_ax1b_type S )
           { St : St_ops_type BB } ( ax1t : St_ax1_type S St ) :=
  forall ( r s : Tilde BB ) ( Y : BB ) ( innrs : St_dom r s ) ( inn : S_dom s Y ) ,
    S ( St r s innrs ) ( S r Y ( St_S_dom_comp innrs inn ) )
      ( S_dom_rs_sY_to_Strs_SrY ax0 ax1a ax1t innrs inn ) =
    S r ( S s Y inn ) ( S_dom_rs_sY_to_r_SsY ax1b innrs inn ) .
Identity Coercion SSt_to_Fun: SSt_type >-> Funclass . 


(** Property StSt *)

Definition StSt_type { BB : lBsystem_carrier } { S : S_ops_type BB }
           ( ax0 : S_ax0_type S ) ( ax1a : S_ax1a_type S ) ( ax1b : S_ax1b_type S )
           { St : St_ops_type BB } ( ax1t : St_ax1_type S St ) :=
  forall ( r s t : Tilde BB ) ( innrs : St_dom r s ) ( innst : St_dom s t ) ,
    St ( St r s innrs ) ( St r t ( St_St_dom_comp innrs innst ) )
      ( St_dom_rs_st_to_Strs_Strt ax0 ax1a ax1t innrs innst ) =
    St r ( St s t innst ) ( St_dom_rs_st_to_r_Stst ax1b ax1t innrs innst ) . 
Identity Coercion StSt_to_Fun: StSt_type >-> Funclass . 











(* End of the file lBsystems_S_St.v *)
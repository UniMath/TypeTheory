Definition T_dom_constr' { BB : lBsystem_carrier } { X1 X2 : BB }
           ( gt0 : ll X1 > 0 ) ( gte : ll X2 >= ll X1 )
           ( isov : isover X2 ( ft X1 ) ) : T_dom X1 X2 .
Proof.
  intros . refine ( T_dom_constr _ _ _ ) .
  exact gt0 .

  rewrite ll_ft . 
  refine ( natgehgthtrans _ _ _ gte _ ) .
  exact ( natgthnnmius1 gt0 ) . 

  exact isov . 

Defined.

Lemma T_dom_ft { BB : lBsystem_carrier } { X1 X2 : BB } ( gt : ll X2 > ll X1 )
      ( inn : T_dom X1 X2 ) : T_dom X1 ( ft X2 ) .
Proof.
  intros . assert ( gt0 := T_dom_gt0 inn ) . 
  refine ( T_dom_constr _ _ ) . 
  
  exact  gt0 .

  refine ( isabove_constr _ _ ) . 
  
  
  repeat ( rewrite ll_ft ) . apply natgthrightminus .
  exact ( natgthtogehsn _ _ gt0 ) .

  exact ( natgehgthtrans _ _ _ ( minusplusnmmineq _ _ ) gt ) .

  apply ( isover_ft ( T_dom_isover inn ) ) .
  rewrite ll_ft . 
  exact ( natgthgehtrans _ _ _ gt ( natminuslehn _ _ ) ) . 

Defined.



Lemma T_dom_ftn { BB : lBsystem_carrier } ( n : nat ) { X1 X2 : BB } ( ge : ll X2 - ll X1 >= n )
      ( inn : T_dom X1 X2 ) : T_dom X1 ( ftn n X2 ) .
Proof .
  intros . assert ( gt0 := T_dom_gt0 inn ) . assert ( gt := T_dom_gth inn ) .
  assert ( isov := T_dom_isover inn ) . 

  refine ( T_dom_constr _ _ _ ) .
  exact gt0 .

  rewrite ( ll_ftn _ _ ) .
  refine ( natgehgthtrans _ ( ll X1 ) _ _ _ ) .
  refine ( natgehleftminusminus _ _ _ _ _ ) .
  rewrite ll_ft in gt .
  exact ( natgthminus1togeh gt ) .
  
  exact ge .

  rewrite ll_ft . 
  exact ( natgthnnmius1 gt0 )  .

  refine ( isover_ftn _ _ ) .
  exact isov .

  refine ( istransnatgeh _ _ _ _ ge ) .
  refine ( natgehandminusl _ _ _ _ ) . 
  rewrite ll_ft .
  exact ( natminuslehn _ _ ) . 

Defined.


Definition ftT { BB : lBsystem_carrier } ( T : T_ops_type BB ) ( X1 X2 : BB )
           ( inn : T_dom X1 X2 ) : BB .
Proof .
  intros .  assert ( gte := T_dom_geh inn ) . 
  destruct ( natgehchoice _ _  gte ) as [ gt | e ] . 
  exact ( T _ _ ( T_dom_ft gt inn ) ) . 
  exact ( X1 ) .
Defined.

Definition T_ax1_type { BB : lBsystem_carrier } ( T : T_ops_type BB ) :=
  forall ( X1 X2 : BB ) ( inn : T_dom X1 X2 ) , ft ( T X1 X2 inn ) = ftT T X1 X2 inn .


Definition ftnT { BB : lBsystem_carrier } ( n : nat ) ( T : T_ops_type BB ) ( X1 X2 : BB )
           ( inn : T_dom X1 X2 ) : BB .
Proof .
  intros . destruct ( natlthorgeh ( ll X2 - ll X1 ) n ) as [ lt | ge ] .
  exact ( ftn (( n - 1 ) - ( ll X2 - ll X1 )) X1 ) .
  exact ( T X1 ( ftn n X2 ) ( T_dom_ftn n ge inn ) ) .
Defined .


Lemma ftn_T { BB : lBsystem_carrier } ( T : T_ops_type BB ) ( ax1 : T_ax1_type T )
      ( n : nat ) { X1 X2 : BB } ( inn : T_dom X1 X2 ) :
  ftn n ( T X1 X2 inn ) = ftnT X1 X2 inn .
Proof .
  intros BB T ax1 n . induction n as [ | n IHn ] .
  intros . apply idpath .  unfold ftnT . destruct ( natlthorgeh (ll X2 - ll X1) 0 ) as [ lt | ge ] .
  destruct ( natgehn0 _ lt ) .
  
  rewrite ( noparts_T_dom (T_dom_ftn 0 ge inn) inn ) . apply idpath . 

  intros . simpl . change ( (ft circ ftn n) (T X1 X2 inn) ) with ( ft ( ftn n ( T X1 X2 inn ))) .
  rewrite ( IHn _ _ inn ) . unfold ftnT at 1 .
  destruct ( natlthorgeh (ll X2 - ll X1) n ) as [ lt | ge ] .
  unfold ftnT . destruct ( natlthorgeh (ll X2 - ll X1) ( S n ) ) as [ slt | sge ] .
  change ( ft (ftn (n - 1 - (ll X2 - ll X1)) X1) ) with
  ( ftn ( 1 + ( ( n - 1 ) - (ll X2 - ll X1) ) ) X1 )  . 
  assert ( eint := ( natassocpmeq 1 _ _ ( natgthtominus1geh lt ))) . rewrite ( ! eint ) . 
  destruct n as [ | n ] .  destruct ( natgehn0 _ lt ) . 

  simpl . rewrite ( natminuseqn _ ) .  apply idpath . 

  assert ( ltint := natlehlthtrans _ _ _ sge lt ) . assert ( leint := natlthtoleh _ _ ltint ) .
  destruct ( leint ( natgthsnn n ) ) . 

  rewrite ax1 . unfold ftT . destruct
                               ( natgehchoice (ll (ftn n X2)) (ll X1)
                                              (T_dom_geh (T_dom_ftn n ge inn))) as [ gt | e ] .
  set ( inn' := (T_dom_ft gt (T_dom_ftn n ge inn))) .
  change (T_dom_ft gt (T_dom_ftn n ge inn)) with inn' . generalize inn' . clear inn' .
  intro inn' . rewrite ( ll_ftn n X2 ) in gt .
  unfold ftnT .  destruct ( natlthorgeh (ll X2 - ll X1) (S n)) as [ slt | sge ] .
  assert ( ge' := natgthtogehsn _ _ ( natgthleftminusminus _ _ _ gt ) ) . 
  destruct ( ge' slt ) . 

  assert (int : inn' = (T_dom_ftn (S n) sge inn) ) . exact ( noparts_T_dom _ _ ) . 
  rewrite int .  apply idpath . 

  rewrite ( ll_ftn n X2 ) in e .  unfold ftnT .
  destruct (natlthorgeh (ll X2 - ll X1) (S n)) as [ lt | ge' ] . 
  assert ( int : n - ( ll X2 - ll X1 ) = 0 ) . exact ( minuseq0 _ _ ge ) .
  simpl . rewrite ( natminuseqn _ ) . rewrite int . apply idpath . 

  assert ( gt : ll X2 - n > ll X1 ) .
  exact ( natgthleftminusminus _ _ _ ( natgehsntogth _ _ ge' ) ) . 

  rewrite e in gt . destruct ( isirreflnatgth _ gt ) . 

Defined.

Lemma isover_T { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax0 :  T_ax0_type T ) ( ax1 : T_ax1_type T )
      { X1 X2 : BB } ( inn : T_dom X1 X2 ) : isover ( T X1 X2 inn ) X1 .
Proof .
  intros . assert ( ge := T_dom_geh inn ) .  unfold isover . 
  rewrite ax0 . 
  rewrite ( ftn_T T ax1 _ inn ) . 
  unfold ftnT . 
  destruct ( natlthorgeh (ll X2 - ll X1) (1 + ll X2 - ll X1) ) as [ lt | ge' ] .
  rewrite ( natassocpmeq _ _ _ ge ) . 
  change ( 1 + ( _ - _ ) - 1 ) with ( ( ll X2 - ll X1 ) - 0 ) . 
  rewrite ( natminuseqn _ ) . 
  rewrite natminusnn . 
  apply idpath . 

  assert ( absd : empty ) .
  rewrite ( natassocpmeq _ _ _ ge ) in ge' . 
  exact ( ge' ( natgthsnn _ ) ) .
  
  destruct absd .

Defined.



Definition Tt_dom_constr { BB : lBsystem_carrier } { X : BB } { r : Tilde BB }
           ( gt0 : ll X > 0 ) ( gt : ll ( dd r ) > ll ( ft X ) )
           ( isov : isover ( dd r ) ( ft X ) ) : Tt_dom X r :=
  T_dom_constr gt0 isab .

Definition Tt_dom_constr' { BB : lBsystem_carrier } { X : BB } { r : Tilde BB }
           ( gt0 : ll X > 0 ) ( gte : ll ( dd r ) >= ll X )
           ( isov : isover ( dd r ) ( ft X ) ) : Tt_dom X r :=
  T_dom_constr' gt0 gte isov . 
  



(** Domain of definition of operations of type S and operation ft *)


Lemma S_dom_ft { BB : lBsystem_carrier } { r : Tilde BB } { Y : BB }
      ( gt : ll Y > 1 + ll ( dd r ) ) ( inn : S_dom r Y ) : S_dom r ( ft Y ) .
Proof.
  intros. assert ( iseq := pr2 inn ) .
  refine ( tpair _ _ _ ) .
  rewrite ( ll_ft Y ) . exact ( natgthandminus1 gt ) .
  
  apply ( pathscomp0 iseq ) .  rewrite ( ll_ft Y ) . rewrite ( ftn_ft _ ) .
  assert ( int :  ( ll Y - ll ( dd r )) = ( 1 + ( ll Y - 1 - ll ( dd r )))) .
  exact ( lB_2014_12_07_l1 ( istransnatgth _ _ _ gt ( natgthsnn _ ) ) ) .
  
  rewrite int . apply idpath .

Defined.


Lemma S_dom_ftn { BB : lBsystem_carrier } ( n : nat ) { r : Tilde BB } { Y : BB }
      ( gt : ll Y - ll ( dd r ) > n ) ( inn : S_dom r Y ) : S_dom r ( ftn n Y ) .
Proof .
  intros.  assert ( gte := pr1 inn ) .
  assert ( eq := pr2 inn ) . lazy beta in * .

  refine ( S_dom_constr _ _ ) .
  rewrite ll_ftn . 
  exact ( natgthtogehsn _ _ ( natgthleftminusminus _ _ _ gt ) ) .

  rewrite ftn_ftn . 
  refine ( eq @ _ ) . 
  assert ( int : (ll Y - ll (dd r)) =
                 (ll (ftn n Y) - ll ( dd r )) + n ).
  rewrite ( ll_ftn _ _ ) . 
  rewrite ( natminusassoc _ _ _ ) .
  assert ( int : ll Y - (n + ll ( dd r )) + n = ll Y - ( n + ll ( dd r ) - n ) ) .
  refine ( natassocmpeq _ _ _ _ _ ) .
  refine ( natgehrightplus _ _ _ _ _ ) .
  exact ( istransnatgeh _ _ _ gte ( natgehsnn _ ) )  .

  exact ( natgthtogeh _ _ gt ) .

  exact ( natgehplusnmn _ _ ) .
  
  rewrite int .  rewrite ( natpluscomm _ _ ) . rewrite ( plusminusnmm _ _ ) . 
  apply idpath .

  rewrite int .  apply idpath . 

Defined.

Definition ftS { BB : lBsystem_carrier } ( S : S_ops_type BB ) ( r : Tilde BB ) ( Y : BB )
           ( inn : S_dom r Y ) : BB .
Proof .
  intros .  assert ( gte := pr1 inn ) . destruct ( natgehchoice _ _  gte ) as [ gt | e ] . 
  exact ( S _ _ ( S_dom_ft gt inn ) ) . 
  exact ( ft ( dd r ) ) .
Defined.


Lemma S_ax1a_dom { BB : lBsystem_carrier } { r : Tilde BB } { Y : BB } ( inn : S_dom r Y )
      ( isab : isabove ( ft X2 ) ( dd r ) ) : S_dom r ( ft Y ) .
Proof .
  intros. exact ( T_dom_constr ( T_dom_gt0 inn ) isab ) . 

Defined.


Definition ftnS { BB : lBsystem_carrier } ( n : nat ) ( S : S_ops_type BB ) ( r : Tilde BB )
           ( Y : BB ) ( inn : S_dom r Y ) : BB .
Proof .
  intros . destruct ( natgthorleh ( ll Y - ll ( dd r ) ) n ) as [ gt | le ] .
  exact ( S r ( ftn n Y ) ( S_dom_ftn n gt inn ) ) .
  exact ( ftn ( ( n + 1 ) - ( ll Y - ll ( dd r ) )) ( dd r ) ) .
Defined .

Lemma S_l1 { BB : lBsystem_carrier } ( S : S_ops_type BB ) ( ax1a : S_ax1a_type S )
      ( n : nat ) { r : Tilde BB } { Y : BB } ( inn : S_dom r Y ) :
  ftn n ( S r Y inn ) = ftnS n S r Y inn .
Proof .
  intros BB S ax1a n . induction n as [ | n IHn ] .
  intros . unfold ftnS . destruct ( natgthorleh (ll Y - ll (dd r)) 0  ) as [ gt | le ] .

  rewrite ( noparts_S_dom (S_dom_ftn 0 gt inn) inn ) . apply idpath .

  assert ( ge := pr1 inn ) . assert ( gt := natgehsntogth _ ( ll ( dd r ) ) ge ) .
  destruct ( le ( minusgth0 _ _ gt ) ) .

  intros . simpl . change ( (ft circ ftn n) (S r Y inn) ) with ( ft ( ftn n ( S r Y inn ))) .
  rewrite ( IHn _ _ inn ) . unfold ftnS at 1 .
  destruct ( natgthorleh (ll Y - ll ( dd r ) ) n ) as [ gt | le ] .
  
  unfold ftnS .
  destruct ( natgthorleh (ll Y - ll (dd r)) (Datatypes.S n) ) as [ gt' | le' ] .
  rewrite ax1a. unfold ftS. 
  destruct ( natgehchoice (ll (ftn n Y)) (1 + ll (dd r)) (pr1 (S_dom_ftn n gt inn)) ) as
      [ gt'' | eq ] .
  rewrite ( noparts_S_dom (S_dom_ft gt'' (S_dom_ftn n gt inn))
                        (S_dom_ftn (Datatypes.S n) gt' inn) ) . 
  apply idpath . 

  rewrite ll_ftn in eq .

  assert ( absd : empty ) . 
  assert ( gt'' := natgthrightplus _ _ _ gt' ) .
  rewrite natpluscomm in gt'' . 
  change ( Datatypes.S n ) with ( 1 + n ) in gt'' . rewrite ( ! ( natplusassoc _ _ _ ) ) in gt''. 
  assert ( gt''' := natgthleftminus _ _ _ gt'' ) . 
  rewrite eq in gt''' .  rewrite natpluscomm in gt''' . 
  exact ( isirreflnatgth _ gt''' ) . 

  destruct absd .

  rewrite ax1a . unfold ftS . 
  destruct ( natgehchoice (ll (ftn n Y)) (1 + ll (dd r)) (pr1 (S_dom_ftn n gt inn)) )
    as [ gt' | e ] . 
  assert ( absd : empty ) . rewrite ll_ftn in gt' . 
  assert ( gt'' : ll Y - ll ( dd r ) > Datatypes.S n ) .
  assert ( gt''' := natgthrightplus _ _ _ gt' ) . 
  rewrite natplusassoc in gt''' . 
  rewrite ( natpluscomm _ n ) in gt''' . 
  rewrite ( ! natplusassoc _ _ _ ) in gt''' . 
  exact ( natgthleftminus _ _ _ gt''' ) . 

  exact ( le' gt'' ) .

  destruct absd . 

  assert ( int : 1 = Datatypes.S n + 1 - (ll Y - ll (dd r))) . 
  apply natleftplustorightminus . 
  assert ( e' := isantisymmnatgeh _ _ ( natgthtogehsn _ _ gt ) le' ) . 
  rewrite e' . 
  exact ( natpluscomm _ _ ) .

  rewrite <- int . 
  apply idpath . 

  unfold ftnS .
  destruct ( natgthorleh (ll Y - ll (dd r)) (Datatypes.S n) ) as [ gt | le' ] .
  assert ( absd : empty ) .
  exact ( le ( istransnatgth _ _ _ gt ( natgthsnn _ ) ) ) . 

  destruct absd . 

  assert ( int : 1 + (( n + 1 ) - (ll Y - ll (dd r))) =
                      Datatypes.S n + 1 - (ll Y - ll (dd r))).
  rewrite <- natassocpmeq . 
  rewrite <- ( natplusassoc 1 n 1 ) . 
  apply idpath .

  rewrite natpluscomm . 
  exact le' . 

  rewrite <- int . 
  apply idpath . 

Defined.



(* Jan. 18, 2015 *)


Definition TT_layer_to_T_layer_1 ( BB : lBsystem_carrier ) ( T : TT_layer BB ) :
  T_layer_1 BB := pr1 T .
Coercion TT_layer_to_T_layer_1 : TT_layer >-> T_layer_1 .

Definition TT_ax { BB : lBsystem_carrier } ( T : TT_layer BB ) :
  TT_type ( T_ax0 T ) ( T_ax1a T ) ( T_ax1b T ) := pr2 T .


Definition TTt_layer_to_Tt_layer_1 { BB : lBsystem_carrier } { T : T_layer_1 BB }
           ( Tt : TTt_layer T ) : Tt_layer_1 T := pr1 Tt . 
Coercion TTt_layer_to_Tt_layer_1 :  TTt_layer >-> Tt_layer_1 . 


(* Jan. 26, 2015 *)


Lemma Tj_int { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax1b : T_ax1b_type T )
      ( j : nat ) { A X1 X2 : BB } ( ell : ll X1 = ll A + j ) 
      ( e : A = ftn j X1 ) ( isov : isover X1 A ) ( isab : isabove X2 A ) : BB .
Proof .
  intros BB T ax1b j . induction j as [ | j IHj ] .
  intros . exact X2 .

  intros .
  assert ( inn : T_dom ( ftn j X1 ) X2 ) .
  refine ( T_dom_constr _ _ ) . 
  rewrite ll_ftn . 
  rewrite ell .
  rewrite natassocpmeq . 
  change ( S j - j ) with ( ( 1 + j ) - j ) .  rewrite ( plusminusnmm 1 j ) .
  rewrite natpluscomm . exact ( natgthsn0 _ ) . 

  exact ( natgehsnn _ ) .
  
  change (ft (ftn j X1)) with ( ftn ( S j ) X1 ) . 
  rewrite <- e .
  exact isab . 

  refine ( IHj ( ftn j X1 ) X1 ( T ( ftn j X1 ) X2 inn ) _ _ _ _ ) .
  rewrite ll_ftn . 
  assert (gte : ll X1 >= j ) . 
  rewrite ell .  exact ( istransnatgeh _ _ _ ( natgehplusnmm _ _ ) ( natgehsnn _ ) ) . 

  exact ( ! ( minusplusnmm _ _ gte ) ) . 

  exact ( idpath _ ) .

  exact ( isover_X_ftnX _ _ ) .
 
  exact ( ax1b _ _ _ ) .

Defined.


Lemma Tj_int_fun { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax1b : T_ax1b_type T )
      { A X1 X2 : BB }
      { j j' : nat } 
      ( ell : ll X1 = ll A + j ) ( ell' : ll X1 = ll A + j' )
      ( e : A = ftn j X1 ) ( e' : A = ftn j' X1 ) 
      ( isov isov' : isover X1 A ) ( isab isab' : isabove X2 A ) :
  Tj_int ax1b j ell e isov isab = Tj_int ax1b j' ell' e' isov' isab' .
Proof .
  intros BB T ax1b A X1 X2 j j' ell ell' .
  assert ( eqj : j = j' ) . apply ( natpluslcan _ _ ( ll A ) ) .
  exact ( ( ! ell ) @ ell' ) .

  generalize ell. 
  clear ell . 
  generalize ell'.
  clear ell'.
  rewrite eqj . 
  clear eqj . 

  intros ell ell' .
  assert ( eqell : ell = ell' ) . apply isasetnat . 
  rewrite eqell . 
  clear ell eqell .

  intros e e'.
  assert ( eqe : e = e' ) . apply isasetB . 
  rewrite eqe . 
  clear e eqe .

  intros isov isov' . assert ( eqov : isov = isov' ) . apply isaprop_isover . rewrite eqov . 

  intros isab isab' . assert ( eqab : isab = isab' ) . apply isaprop_isabove . rewrite eqab .

  apply idpath . 

Defined.






  

(* 

Lemma isabove_Tj_int { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax1b : T_ax1b_type T )
      ( j : nat ) { A X1 X2 : BB } ( e : ll X1 = ll A + j ) 
      ( e' : A = ftn j X1 ) ( isov : isover X1 A ) ( isab : isabove X2 A ) :
  isabove ( Tj_int ax1b j e e' isov isab ) X1 .
Proof.
  intros BB T ax1b j . induction j as [ | j IHj ] .
  intros . 
  simpl .
  assert ( eq : X1 = A ) . 
  unfold isover in isov . 
  rewrite natplusr0 in e . 
  rewrite e in isov . 
  rewrite natminusnn in isov . 
  exact ( ! isov ) . 

  rewrite eq .
  exact isab .

  intros . 
  simpl . 
  






  
Defined.

*)








  

Definition Tj { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax1b : T_ax1b_type T )
      { A X1 X2 : BB } ( isov : isover X1 A ) ( isab : isabove X2 A ) : BB .
Proof .
  intros .
  set ( j := ll X1 - ll A ) .
  refine ( Tj_int ax1b j _ _ isov isab ) .
  unfold j . 
  rewrite natpluscomm . 
  refine ( ! ( minusplusnmm _ _ _ ) ) . 
  exact ( isover_geh isov ) . 

  unfold isover in isov .
  exact isov . 

Defined.


Lemma Tj_fun { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax1b : T_ax1b_type T )
      { A X1 X2 : BB } ( isov isov' : isover X1 A ) ( isab isab' : isabove X2 A ) :
  Tj ax1b isov isab = Tj ax1b isov' isab' .
Proof .
  intros . 
  apply Tj_int_fun . 

Defined.


(* Jan. 30 2015 *)
















(** ** l-towers of (h-)sets. 

by Vladimir Voevodsky. File created on January 30, 2015. *)

Unset Automatic Introduction.

Require Export TypeTheory.Csystems.ltowers_over .



Definition hSet_ltower := total2 ( fun T : ltower => isaset T ) .

Definition hSet_ltower_constr ( T : ltower ) ( is : isaset T ) : hSet_ltower :=
  tpair _ T is . 

Definition hSet_ltower_pr1 : hSet_ltower -> ltower := pr1 . 
Coercion hSet_ltower_pr1 : hSet_ltower >-> ltower .

Definition isasetB ( T : hSet_ltower ) : isaset T := pr2 T .

Lemma isaprop_isover { T : hSet_ltower } ( X A : T ) : isaprop ( isover X A ) .
Proof .
  intros . exact ( isasetB _ _ _ ) . 

Defined.

Lemma isaprop_isabove { T : hSet_ltower } ( X A : T ) : isaprop ( isabove X A ) . 
Proof. 
  intros . 
  apply isapropdirprod . 
  exact ( pr2 ( _ > _ ) ) .

  exact ( isaprop_isover _ _ ) . 

Defined .

Definition hSet_pltower := total2 ( fun T : hSet_ltower => ispointed_type T ) .

Definition hSet_pltower_constr ( T : hSet_ltower ) ( is : ispointed_type T ) : hSet_pltower :=
  tpair _ T is . 


Definition hSet_pltowers_to_pltowers : hSet_pltower -> pltower :=
  fun T => pltower_constr ( pr2 T ) . 
Coercion hSet_pltowers_to_pltowers : hSet_pltower >-> pltower . 

Definition hSet_pltowers_pr1 : hSet_pltower -> hSet_ltower := pr1 . 
Coercion hSet_pltowers_pr1 : hSet_pltower >-> hSet_ltower . 



Lemma isinvovmonot_pocto { T : hSet_ltower } { A : T } { X Y : ltower_over A }
      ( isov : isover ( pocto X ) ( pocto Y ) ) : isover X Y .  
Proof .
  intros . 
  refine ( invmaponpathsincl pr1 _ _ _ _ ) . 
  apply isinclpr1 . 
  intro x . 
  apply isaprop_isover .

  rewrite ll_over_minus_ll_over . 
  rewrite ltower_over_ftn . 
  exact isov . 

  change ( ll X ) with ( ll ( pr1 X ) - ll A ) . 
  apply natgehandminusl . 
  exact ( isover_geh ( isov_isov Y ) ) . 

Defined.



Lemma isaset_ltower_over { T : hSet_ltower } ( X : T ) : isaset ( ltower_over X ) .
Proof .
  intros . 
  apply ( isofhleveltotal2 2 ) . 
  exact ( pr2 T ) . 

  intro x .
  apply isasetaprop . 
  apply isaprop_isover . 

Defined.



Definition hSet_ltower_over { T : hSet_ltower } ( X : T ) : hSet_ltower :=
  tpair ( fun T : ltower => isaset T ) ( ltower_over X ) ( isaset_ltower_over X ) . 


Definition hSet_pltower_over { T : hSet_ltower } ( X : T ) : hSet_pltower :=
  tpair _ ( hSet_ltower_over X ) ( pr2 ( pltower_over X ) ) . 



(** **** Completing construction of the function to_ltower_over *)

  
Lemma isovmonot_to_ltower_over { T : hSet_pltower }
      { X Y : T } ( isov : isover X Y ) : isover ( to_ltower_over X ) ( to_ltower_over Y ) .
Proof .
  intros .
  refine ( @isinvovmonot_pocto T ( cntr T ) (to_ltower_over X) (to_ltower_over Y) isov ) . 

Defined.


Definition ltower_fun_to_ltower_over { T : hSet_pltower }  :
  ltower_fun T ( hSet_ltower_over ( cntr T ) ) :=
  ltower_fun_constr ( @isovmonot_to_ltower_over T )
                     ( @isllmonot_to_ltower_over T ) ( @isbased_to_ltower_over T ) . 





(** **** The function lft *)


Definition lft { T : hSet_ltower }
           { X : T } { X' : ltower_over X } ( X'' : ltower_over ( pocto X' ) ) : ltower_over X' .
Proof .
  intros .
  simple refine (obj_over_constr _ ) .
  split with ( pocto X'' ) . 
  apply ( isover_trans ( isov_isov X'' ) ( isov_isov X' ) ) .
  apply isinvovmonot_pocto . 
  simpl .
  exact ( isov_isov X'' ) . 

Defined.

Lemma ll_lft { T : hSet_ltower }
      { X : T } { X' : ltower_over X } ( X'' : ltower_over ( pocto X' ) ) :
  ll ( lft X'' ) = ll X'' .
Proof.
  intros .
  change _ with
  ( ll ( pr1 X'' ) - ll X - ( ll ( pr1 X' ) - ll X ) = ll ( pr1 X'' ) - ll ( pr1 X' ) ) .
  rewrite natminusassoc . 
  rewrite natpluscomm . 
  rewrite ( minusplusnmm _ _ ( isover_geh ( isov_isov X' ) ) ) . 
  apply idpath . 

Defined.

  

Lemma isovmonot_lft { T : hSet_ltower }
      { X : T } ( X' : ltower_over X ) : isovmonot ( @lft _ _ X' ) .
Proof .
  intros . unfold isovmonot . 
  intros X0 Y isov . 
  apply ( @isinvovmonot_pocto ( hSet_ltower_over X ) ) .
  simpl . 
  apply isinvovmonot_pocto. 
  simpl . 
  apply ( isovmonot_pocto _ isov ) . 

Defined.



Lemma isllmonot_lft { T : hSet_ltower }
      { X : T } ( X' : ltower_over X ) : isllmonot ( @lft _ _ X' ) .
Proof .
  intros .
  unfold isllmonot . intros .
  repeat rewrite ll_lft . 
  apply idpath . 

Defined.

Lemma isbased_lft { T : hSet_ltower }
      { X : T } ( X' : ltower_over X ) : isbased ( @lft _ _ X' ) .
Proof.
  intros. unfold isbased. intros X0 eq0. rewrite ll_lft. exact eq0 .

Defined.





Definition ovmonot_lft { T : hSet_ltower } { X : T } ( X' : ltower_over X ) :
  ovmonot_fun ( ltower_over ( pocto X' ) ) ( ltower_over X' ) :=
  ovmonot_fun_constr _ ( isovmonot_lft X' ) .


Definition ltower_fun_lft { T : hSet_ltower } { X : T } ( X' : ltower_over X ) :
  ltower_fun ( ltower_over ( pocto X' ) ) ( ltower_over X' ) :=
  ltower_fun_constr ( isovmonot_lft X' ) ( isllmonot_lft X' ) ( isbased_lft X' ) . 



(** **** The functions ovmonot_over and ltower_fun_over *)


Definition ovmonot_over { T1 T2 : hSet_ltower } ( f : ovmonot_fun T1 T2 )
           ( X : T1 ) : ovmonot_fun ( ltower_over X ) ( ltower_over ( f X ) ) .
Proof .
  intros . 
  simple refine ( ovmonot_fun_constr _ _ ) .
  intro X' . 
  split with ( f ( pocto X' ) ) . 
  apply ( pr2 f ) . 
  apply ( isov_isov X' ) . 

  intros X0 Y isov . simpl .
  apply isinvovmonot_pocto . 
  simpl .
  apply ( pr2 f ) . 
  apply ( isovmonot_pocto _ isov ) . 

Defined.


Lemma isllmonot_ovmonot_over { T1 T2 : hSet_ltower } { f : ovmonot_fun T1 T2 } ( isf : isllmonot f )
      ( X : T1 ) : isllmonot ( ovmonot_over f X ) .
Proof.
  intros.
  unfold isllmonot .
  intros X0 Y . 
  change _ with ( ll ( f ( pr1 X0 ) ) - ll ( f X ) - ( ll ( f ( pr1 Y ) ) - ll ( f X ) ) =
                  ll X0 - ll Y ) . 
  repeat rewrite isf . 
  apply idpath .

Defined.

Lemma isbased_ovmonot_over { T1 T2 : hSet_ltower }
      { f : ovmonot_fun T1 T2 } ( isf : isllmonot f ) 
      ( X : T1 ) : isbased ( ovmonot_over f X ) .
Proof.
  intros. unfold isbased. intros X0 eq0 . 
  change _ with ( ll ( pr1 X0 ) - ll X = 0 ) in eq0 . 
  change _ with ( ll ( f ( pr1 X0 ) ) - ll ( f X ) = 0 ) .
  rewrite isf . 
  exact eq0 .

Defined.



Definition ltower_fun_over { T1 T2 : hSet_ltower } ( f : ovmonot_fun T1 T2 ) ( isf : isllmonot f )
           ( X : T1 ) : ltower_fun ( ltower_over X ) ( ltower_over ( f X ) ) :=
  ltower_fun_constr ( pr2 ( ovmonot_over f X )  )
                    ( isllmonot_ovmonot_over isf X ) ( isbased_ovmonot_over isf X ) . 




  

(** **** The function to_over_pocto *)





Definition to_over_pocto  { T : hSet_ltower } { X : T } ( X' : ltower_over X )
           ( X'' : ltower_over X' ) : ltower_over ( pocto X' ) .
Proof .
  intros .
  split with ( pocto ( pocto X'' ) ) . 
  apply isovmonot_pocto . 
  apply ( isov_isov X'' ) .

Defined.



Lemma isovmonot_to_over_pocto { T : hSet_ltower } { X : T } ( X' : ltower_over X ) :
  isovmonot ( to_over_pocto X' ) . 
Proof .
  intros.
  unfold isovmonot. 
  intros X0 Y isov .
  simpl .
  apply isinvovmonot_pocto . 
  simpl .
  apply isovmonot_pocto .  apply isovmonot_pocto . 
  apply isov . 

Defined.


Definition ovmonot_to_over_pocto  { T : hSet_ltower } { X : T } ( X' : ltower_over X ) :
  ovmonot_fun ( ltower_over X' ) ( ltower_over ( pocto X' ) ) :=
  ovmonot_fun_constr _ ( isovmonot_to_over_pocto X' ) .


Lemma ll_to_over_pocto { T : hSet_ltower } { X : T } ( X' : ltower_over X )
      ( X'' : ltower_over X' ) : ll ( to_over_pocto X' X'' ) = ll X'' .
Proof .
  intros .
  change _ with ( ll ( pr1 ( pr1 X'' ) ) - ll ( pr1 X' ) =
                ll ( pr1 ( pr1 X'' ) ) - ll X - ( ll ( pr1 X' ) - ll X ) ) . 
  rewrite natminusassoc . 
  rewrite natpluscomm . 
  rewrite ( minusplusnmm _ _ ( isover_geh ( isov_isov X' ) ) ) . 
  apply idpath . 

Defined.


Lemma isllmonot_to_over_pocto { T : hSet_ltower } { X : T } ( X' : ltower_over X ) :
  isllmonot ( to_over_pocto X' ) .
Proof .
  intros .
  unfold isllmonot . intros X0 Y .
  repeat rewrite ll_to_over_pocto . 
  apply idpath . 

Defined.


Lemma isbased_to_over_pocto { T : hSet_ltower } { X : T } ( X' : ltower_over X ) :
  isbased ( to_over_pocto X' ) .
Proof.
  intros. unfold isbased .  intros X0 eq0 . 
  rewrite ll_to_over_pocto . 
  exact eq0 .

Defined.



Definition ltower_fun_to_over_pocto { T : hSet_ltower } { X : T } ( X' : ltower_over X ) :
  ltower_fun ( ltower_over X' ) ( ltower_over ( pocto X' ) ) :=
  ltower_fun_constr ( isovmonot_to_over_pocto X' )
                    ( isllmonot_to_over_pocto X' ) ( isbased_to_over_pocto X' ) . 



(** **** The function ltower_fun_second *)


  

Definition ovmonot_second { T : hSet_ltower }
           { X Y : T } ( f : ovmonot_fun ( ltower_over X ) ( ltower_over Y ) )
           ( X' : ltower_over X ) :
  ovmonot_fun ( ltower_over ( pocto X' ) ) ( ltower_over ( pocto ( f X' ) ) ) .
Proof .
  intros .
  set ( int1 :=
          ovmonot_funcomp ( ovmonot_lft X' )
                          ( @ovmonot_over ( hSet_ltower_over X ) ( hSet_ltower_over Y ) f X' ) ) .  
  apply ( ovmonot_funcomp int1 ( ovmonot_to_over_pocto _ ) ) .

Defined.


Lemma isllmonot_ovmonot_second { T : hSet_ltower }
      { X Y : T }
      ( f : ovmonot_fun ( ltower_over X ) ( ltower_over Y ) ) ( isf : isllmonot f ) 
      ( X' : ltower_over X ) : isllmonot ( ovmonot_second f X' ) .
Proof .
  intros .
  refine ( isllmonot_funcomp _ _ ) . refine ( isllmonot_funcomp _ _ ) . 
  apply isllmonot_lft . 

  refine ( @isllmonot_ovmonot_over ( hSet_ltower_over _ ) ( hSet_ltower_over _ ) _ isf X' ) . 

  apply isllmonot_to_over_pocto . 

Defined.


Lemma isbased_second { T : hSet_ltower }
           { X Y : T } ( f : ltower_fun ( ltower_over X ) ( ltower_over Y ) )
           ( X' : ltower_over X ) :
  isbased ( ovmonot_second f X' ) .
Proof.
  intros. unfold isbased. intros X0 eq0 .
  unfold ovmonot_second .
  apply isbased_funcomp. 
  apply isbased_funcomp.
  apply isbased_lft . 

  apply ( @isbased_ovmonot_over ( hSet_ltower_over X ) ( hSet_ltower_over Y ) ) .

  apply ( isllmonot_pr f ) . 

  apply ( isbased_to_over_pocto ) .

  exact eq0 . 

Defined.


Definition ltower_fun_second { T : hSet_ltower }
           { X Y : T } ( f : ltower_fun ( ltower_over X ) ( ltower_over Y ) )
           ( X' : ltower_over X ) :
  ltower_fun ( ltower_over ( pocto X' ) ) ( ltower_over ( pocto ( f X' ) ) ) :=
  ltower_fun_constr ( pr2 ( ovmonot_second f X' ) )
                    ( isllmonot_ovmonot_second f ( isllmonot_pr f ) X' )
                    ( isbased_second f X' ) .




(** **** The induction principle for isover *)


Definition isover_ind_int { BB : ltower }
           ( P : forall ( X Y : BB ) , UU )
           ( P0 : forall ( X : BB ) , P X X )
           ( Pft : forall ( X : BB ) ( gt0 : ll X > 0 ) , P X ( ft X ) )
           ( Pcomp : forall ( X Y : BB ) , P X ( ft X ) -> P ( ft X ) Y -> P X Y ) :
  forall ( n : nat ) ( X Y : BB ) ( eq : Y = ftn n X ) , P X Y .
Proof.
  intros until n .  induction n as [ | n IHn ] .
  intros . change _ with ( Y = X ) in eq . 
  rewrite eq . 
  apply P0 .

  intros .
  destruct ( natgehchoice _ _ ( natgehn0 ( ll X ) ) ) as [ gt0 | eq0 ] .
  
  apply Pcomp . 
  apply Pft . 
  apply gt0 . 
  assert ( eq' : Y = ftn n ( ft X ) ) . 
  rewrite ftn_ft . 
  apply eq .

  apply ( IHn _ _ eq' ) .
  rewrite ftnX_eq_X in eq . 
  rewrite eq . 
  apply P0 .

  apply eq0.

Defined.

Lemma isover_ind_int_XX { BB : hSet_ltower }
           ( P : forall ( X Y : BB ) , UU )
           ( P0 : forall ( X : BB ) , P X X )
           ( Pft : forall ( X : BB ) ( gt0 : ll X > 0 ) , P X ( ft X ) )
           ( Pcomp : forall ( X Y : BB ) , P X ( ft X ) -> P ( ft X ) Y -> P X Y )
           ( n : nat ) ( eq0 : n = 0 ) ( X : BB ) ( eq : X = ftn n X ) :
  isover_ind_int P P0 Pft Pcomp n X X eq = P0 X .
Proof. 
  intros .
  set ( Y := X ) . 
  change _ with ( Y = ftn n X ) in eq . 
  change _ with (isover_ind_int P P0 Pft Pcomp n X Y eq = P0 X).
  generalize eq . 
  rewrite eq0 . 
  intro eq1. assert ( eqq : eq1 = idpath X ) .  apply isasetB .
  simpl . rewrite eqq .
  apply idpath . 

Defined.



Lemma isover_ind_int_isab_eq_in_BB { BB : hSet_ltower }
      { n m : nat } ( eqn : n = S m ) { X Y : BB } ( eq : Y = ftn n X ) :
  Y = ftn m ( ft X ) .
Proof .
  intros .
  rewrite ftn_ft . 
  change ( 1 + m ) with ( S m ) . 
  rewrite <- eqn . 
  exact eq .

Defined.


Lemma isover_ind_int_isab { BB : hSet_ltower }
           ( P : forall ( X Y : BB ) , UU )
           ( P0 : forall ( X : BB ) , P X X )
           ( Pft : forall ( X : BB ) ( gt0 : ll X > 0 ) , P X ( ft X ) )
           ( Pcomp : forall ( X Y : BB ) , P X ( ft X ) -> P ( ft X ) Y -> P X Y )
           ( n m : nat ) ( eqn : n = S m ) ( X Y : BB ) ( gt0 : ll X > 0 )
           ( eq : Y = ftn n X ) ( eq' : Y = ftn m ( ft X ) ) :
  isover_ind_int P P0 Pft Pcomp n X Y eq =
  Pcomp _ _ ( Pft X gt0 ) ( isover_ind_int P P0 Pft Pcomp m ( ft X ) Y eq' ) .
Proof. 
  intros until m .  intro eqn . rewrite eqn .
  intros .
  simpl .
  destruct (natgehchoice (ll X) 0 (natgehn0 (ll X))) as [ gt0' | eq0 ] . 
  assert ( int : gt0 = gt0' ) . apply proofirrelevance . apply ( pr2 ( _ > _ ) ) . 
  rewrite int .
(*
  assert ( int' : (uu0a.internal_identity_rew_r BB (ftn m (ft X)) 
           ((ft circ ftn m) X) (fun l : BB => Y = l) eq 
           (ftn_ft m X)) = eq' ) .
*)
  assert ( int' : (internal_paths_rew_r BB (ftn m (ft X)) 
           ((ft ∘ ftn m) X) (fun l : BB => Y = l) eq 
           (ftn_ft m X)) = eq' ) .
  { apply isasetB . }
  rewrite int' .
  apply idpath .

  assert ( gt0' : ll X > 0 ) . apply gt0 .

  rewrite eq0 in gt0' . destruct ( negnatgthnn _ gt0' ) . 

Defined.




Lemma isover_ind_int_X_ftX { BB : hSet_ltower }
           ( P : forall ( X Y : BB ) , UU )
           ( P0 : forall ( X : BB ) , P X X )
           ( Pft : forall ( X : BB ) ( gt0 : ll X > 0 ) , P X ( ft X ) )
           ( Pcomp : forall ( X Y : BB ) , P X ( ft X ) -> P ( ft X ) Y -> P X Y )
           ( Pcomp_eq : forall ( X : BB ) ( gt0 : ll X > 0 ) ,
                          Pcomp _ _ ( Pft _ gt0 ) ( P0 ( ft X ) ) = ( Pft _ gt0 ) )
           ( n : nat ) ( eq1 : n = 1 ) ( X : BB ) ( eq : ft X = ftn n X ) ( gt0 : ll X > 0 ) :
  isover_ind_int P P0 Pft Pcomp n X ( ft X ) eq = Pft X gt0 .
Proof.
  intros until n. intro eq1 . rewrite eq1 . 
  intros X eq . assert ( eqq : eq = idpath _ ) . apply isasetB . 
  rewrite eqq . intro . 
  simpl .
  destruct (natgehchoice (ll X) 0 (natgehn0 (ll X))) as [ gt0' | eq0 ] .
  assert ( eq' : gt0 = gt0' ) . apply proofirrelevance .  apply ( pr2 ( _ > _ ) ) . 
  rewrite eq' . apply Pcomp_eq . 

  assert ( absd : empty ) . rewrite eq0 in gt0 . 
  apply ( negnatgthnn _ gt0 ) . 

  destruct absd .

Defined.

  
Definition isover_ind { BB : ltower }
           ( P : forall ( X Y : BB ) , UU )
           ( P0 : forall ( X : BB ) , P X X )
           ( Pft : forall ( X : BB ) ( gt0 : ll X > 0 ) , P X ( ft X ) )
           ( Pcomp : forall ( X Y : BB ) , P X ( ft X ) -> P ( ft X ) Y -> P X Y ) :
  forall ( X Y : BB ) ( isov : isover X Y ) , P X Y :=
  fun X Y isov => isover_ind_int P P0 Pft Pcomp ( ll X - ll Y ) X Y isov .


Lemma isover_ind_XX { BB : hSet_ltower }
           ( P : forall ( X Y : BB ) , UU )
           ( P0 : forall ( X : BB ) , P X X )
           ( Pft : forall ( X : BB ) ( gt0 : ll X > 0 ) , P X ( ft X ) )
           ( Pcomp : forall ( X Y : BB ) , P X ( ft X ) -> P ( ft X ) Y -> P X Y )
           ( X : BB ) ( isov : isover X X ) : isover_ind P P0 Pft Pcomp X X isov = P0 X .
Proof.
  intros.
  apply isover_ind_int_XX . 
  apply natminusnn . 

Defined.

Opaque isover_ind_XX .


Lemma isover_ind_isab { BB : hSet_ltower }
           ( P : forall ( X Y : BB ) , UU )
           ( P0 : forall ( X : BB ) , P X X )
           ( Pft : forall ( X : BB ) ( gt0 : ll X > 0 ) , P X ( ft X ) )
           ( Pcomp : forall ( X Y : BB ) , P X ( ft X ) -> P ( ft X ) Y -> P X Y )
           ( X Y : BB ) ( isab : isabove X Y ) :
  isover_ind P P0 Pft Pcomp X Y isab =
  Pcomp _ _ ( Pft X ( isabove_gt0 isab ) ) ( isover_ind P P0 Pft Pcomp ( ft X ) Y ( isover_ft' isab ) ) .
Proof.
  intros .
  apply isover_ind_int_isab .
  rewrite ll_ft . 
  apply lB_2014_12_07_l1 . 
  apply ( isabove_gth isab ) . 

Defined.

Opaque isover_ind_isab .


Lemma isover_ind_X_ftX { BB : hSet_ltower }
           ( P : forall ( X Y : BB ) , UU )
           ( P0 : forall ( X : BB ) , P X X )
           ( Pft : forall ( X : BB ) ( gt0 : ll X > 0 ) , P X ( ft X ) )
           ( Pcomp : forall ( X Y : BB ) , P X ( ft X ) -> P ( ft X ) Y -> P X Y )
           ( Pcomp_eq : forall ( X : BB ) ( gt0 : ll X > 0 ) ,
                          Pcomp _ _ ( Pft _ gt0 ) ( P0 ( ft X ) ) = ( Pft _ gt0 ) )
           ( X : BB ) ( gt0 : ll X > 0 ) :
  isover_ind P P0 Pft Pcomp X ( ft X ) ( isover_X_ftX X ) = Pft X gt0 .
Proof.
  intros. apply isover_ind_int_X_ftX .
  intros . apply Pcomp_eq . 

  rewrite ll_ft .
  apply natminusmmk . 
  apply ( gth0_to_geh1 gt0 ) . 

Defined.


  

(** **** Stronger induction principle for isover *)


Definition isover_strong_ind_int { BB : hSet_ltower }
           ( P : forall ( X Y : BB ) ( isov : isover X Y ) , UU )
           ( P0 : forall ( X : BB ) , P X X ( isover_XX X ) )
           ( Pft : forall ( X : BB ) ( gt0 : ll X > 0 ) , P X ( ft X ) ( isover_X_ftX X ) )
           ( Pcomp : forall ( X Y : BB ) ,
                       ( forall isov1 , P X ( ft X ) isov1 ) ->
                       ( forall isov2 , P ( ft X ) Y isov2 ) ->
                       forall ( isab : isabove X Y ) , P X Y isab )  :
  forall ( n : nat ) ( X Y : BB ) ( eq : Y = ftn n X ) ( isov : isover X Y ) , P X Y isov .
Proof.
  intros until n .  induction n as [ | n IHn ] .
  intros . change _ with ( Y = X ) in eq .
  generalize isov . clear isov . 
  rewrite eq .
  intro isov .
  assert ( eq1: isov = isover_XX X ) . 
  apply proofirrelevance .  apply isaprop_isover . rewrite eq1 . apply P0 .
  
  intros .
  destruct ( natgehchoice _ _ ( natgehn0 ( ll X ) ) ) as [ gt0 | eq0 ] . 
  assert ( int1 : forall isov1 : isover X (ft X), P X (ft X) isov1).
  intros. 
  assert ( int11 := Pft X gt0 ) .
  assert ( eq1: isov1 = isover_X_ftX X ) . 
  apply proofirrelevance .  apply isaprop_isover . rewrite eq1 . apply int11 .

  assert ( int2 : forall isov2 : isover (ft X) Y, P (ft X) Y isov2).
  intros.
  refine ( IHn ( ft X ) Y _ _ ) . 
  rewrite ftn_ft . 
  apply eq .

  assert ( gt : ll X > ll Y ) . 
  rewrite eq . 
  rewrite ll_ftn . apply ( natgthgehtrans _ ( ll X - 1 ) _ ) .
  apply natminuslthn . 
  apply gt0 . 

  apply idpath .

  change ( ll X - S n ) with ( ll X - ( 1 + n ) ) . 
  rewrite <- natminusassoc . 
  apply natminuslehn . 

  exact ( Pcomp _ _ int1 int2 ( isabove_constr gt isov ) ) . 
  (* assert ( int3 := Pcomp _ _ int1 int2 ) . 
  set ( int31 := pr1 int3 ) . assert ( int32 := pr2 int3 ) .
  assert ( eq1: isov = int31 ) . 
  apply proofirrelevance .  apply isaprop_isover . rewrite eq1 . 
  exact int32.*)

  rewrite ftnX_eq_X in eq . 
  generalize isov .
  rewrite eq . 
  clear isov . intro isov .
  assert ( eq1: isov = isover_XX X ) . 
  apply proofirrelevance .  apply isaprop_isover . rewrite eq1 . apply P0 .
  exact eq0 . 

Defined.










Definition isover_strong_ind { BB : hSet_ltower }
           ( P : forall ( X Y : BB ) ( isov : isover X Y ) , UU )
           ( P0 : forall ( X : BB ) , P X X ( isover_XX X ) )
           ( Pft : forall ( X : BB ) ( gt0 : ll X > 0 ) , P X ( ft X ) ( isover_X_ftX X ) )
           ( Pcomp : forall ( X Y : BB ) ,
                       ( forall isov1 , P X ( ft X ) isov1 ) ->
                       ( forall isov2 , P ( ft X ) Y isov2 ) ->
                       forall isov3 , P X Y isov3 )  :
  forall ( X Y : BB ) ( isov : isover X Y ) , P X Y isov .
Proof.
  intros.
  apply ( isover_strong_ind_int P P0 Pft Pcomp ( ll X - ll Y ) X Y isov isov ) .  

Defined.


(* Definition isover_strong_compt0 { BB : hSet_ltower }
           ( P : forall ( X Y : BB ) ( isov : isover X Y ) , UU )
           ( P0 : forall ( X : BB ) , P X X ( isover_XX X ) )
           ( Pft : forall ( X : BB ) ( gt0 : ll X > 0 ) , P X ( ft X ) ( isover_X_ftX X ) )
           ( Pcomp : forall ( X Y : BB ) ,
                       ( forall isov1 , P X ( ft X ) isov1 ) ->
                       ( forall isov2 , P ( ft X ) Y isov2 ) ->
                       total2 ( fun isov3 => P X Y isov3 ) )
           ( X : BB ) :  isover_strong_ind P P0 Pft Pcomp X X ( isover_XX X ) = P0 X .
Proof.
  intros.
  unfold isover_strong_ind .
  rewrite natminusnn . 
 
  forall ( X : BB ) ( isov : isover X X ) , P X Y isov .
Proof.
  intros.
  apply ( isover_strong_ind_int P P0 Pft Pcomp ( ll X - ll Y ) X Y isov isov ) .  

Defined.*)
  

  

(* End of the file hSet_ltowers.v *)
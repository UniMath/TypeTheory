(** ** Presentation of towers through the length function

by Vladimir Voevodsky, started on Jan. 22, 2015, most material migrated from 
lBsystems_carriers.v 

 *)

Require Import UniMath.Foundations.All.
Require Export TypeTheory.Csystems.prelim.


(** To uu0a.v *)

Lemma iscontrpathsfrom { T : UU } ( A : T ): iscontr (∑ X : T, A = X).
Proof.
  exists ( tpair _ A ( idpath A ) ).
  intro t. 
  induction t as [ t e ].
  induction e. 
  apply idpath. 
Defined.
  

(** We formalize the sequences of types ...->B_{n+1}->B_n->...->B_0 as one type B with a length function ll and an endomorphism ft. *)

Definition ltower_str_data ( T : UU ):= ( T -> nat ) × ( T -> T ).

Definition ltower_str ( T : UU ):=
  ∑ str : ltower_str_data T,
         ( forall X : T , ( pr1 str ) ( pr2 str X ) = pr1 str X - 1 ) ×
         ( forall ( X : T ) ( e : pr1 str X = 0 ) , pr2 str X = X ).


Definition ltower := ∑ T : UU, ltower_str T.

Definition ltower_constr { T : UU } ( ll : T -> nat ) ( ft : T -> T )
           ( ll_ft_eq : forall X : T , ll ( ft X ) = ll X - 1 )
           ( ll0_eq : forall ( X : T ) ( e : ll X = 0 ) , ft X = X ): ltower.
Proof.
  exists T.
  exists (ll ,, ft).
  exact (ll_ft_eq ,, ll0_eq ). 
Defined.


  
(** The type ltower is constructively equivalent to the type of pretowers defined as follows:

Definition pretowerfam := ( fun T : nat -> UU => forall n : nat , T ( S n  ) -> T n ) .
Definition pretower := total2 pretowerfam . 

See pretowers.v 

*)

Definition ltower_data_pr1: ltower -> UU := pr1.
Coercion ltower_data_pr1: ltower >-> UU.

Definition ll { X : ltower }: X -> nat := pr1 ( pr1 ( pr2 X ) ).

Definition ft { X : ltower }: X -> X := pr2 ( pr1 ( pr2 X ) ).

Definition ftn { X : ltower } ( n : nat ): X -> X := iteration ( @ft X ) n.


Definition ll_ft { T : ltower } ( X : T ): ll ( ft X ) = ll X - 1 :=
  pr1 ( pr2 ( pr2 T ) ) X.

Definition ftX_eq_X { T : ltower } { X : T } ( e : ll X = 0 ): ft X = X :=
  pr2 ( pr2 ( pr2 T ) ) X e.


(** Some useful lemmas about ltower *)

Lemma ll_ftn { BB : ltower } ( n : nat ) ( X : BB ): ll ( ftn n X ) = ll X - n. 
Proof.
  revert X.
  induction n as [ | n IHn ]; intro X.
  - rewrite natminuseqn.
    apply idpath. 
  - change ( ftn ( S n ) X ) with ( ft ( ftn n X ) ).
    rewrite ( ll_ft _ ). 
    rewrite ( IHn X ).
    rewrite ( natminusassoc _ _ _ ).
    rewrite ( natpluscomm n 1 ). 
    apply idpath.
Defined .

  
Lemma ftn_ft { BB : ltower } ( n : nat ) ( X : BB ):
  ftn n ( ft X ) = ftn ( 1 + n ) X.
Proof.
  induction n as [ | n IHn ].
  - apply idpath. 
  - apply ( maponpaths ( @ft BB ) IHn ). 
Defined.


Lemma ftn_ftn { BB : ltower } ( m n : nat ) ( X : BB ):
  ftn m ( ftn n X ) = ftn ( m + n ) X.
Proof.
  induction m as [ | m IHm ]. 
  - exact ( idpath _ ).
  - apply ( maponpaths ft ). 
    exact IHm.
Defined.


Lemma lltowergehll { BB : ltower } { X1 X2 : BB } ( gt : ll X2 > ll X1 ):
  ll ( ft X2 ) >= ll X1.
Proof.
  rewrite ( ll_ft X2 ).
  apply ( natgthtominus1geh gt ). 
Defined.


Lemma llgehll { BB : ltower } { X1 X2 : BB } ( gt : ll X2 > ll ( ft X1 ) ):
  ll X2 >= ll X1.
Proof.
  rewrite ( ll_ft X1 ) in gt.
  apply ( natgthminus1togeh gt ). 
Defined.


Lemma ll_ft_gtn { T : ltower } { X : T } { n : nat } ( gtsn : ll X >= S n ): ll ( ft X ) >= n.
Proof.
  rewrite ll_ft. 
  set ( int := natgehandminusr _ _ 1 gtsn ). 
  change ( S n - 1 ) with ( n - 0 ) in int.
  rewrite natminuseqn in int. 
  apply int.
Defined.


Lemma S_ll_ft { T : ltower } { X : T } ( gt0 : ll X > 0 ) : 1 + ll ( ft X ) = ll X .
Proof.
  rewrite ll_ft .
  rewrite natpluscomm .
  apply ( minusplusnmm _ _ ( gth0_to_geh1 gt0 ) ) .

Defined.

Definition ftnX_eq_X { T : ltower } ( n : nat ) { X : T } ( eq : ll X = 0 ) : ftn n X = X .
Proof.
  revert X eq. induction n as [ | n IHn ] .
  intros .  apply idpath . 

  intros .  
  rewrite <- ftn_ft . 
  assert ( int : ftn n ( ft X ) = ft X ) .
  apply IHn . 
  rewrite ll_ft . 
  rewrite eq . apply idpath .
  rewrite int . 
  apply ftX_eq_X . 
  apply eq .

Defined.









  
(* **** The predicate isover and its properties *)


Definition isover { BB : ltower } ( X A : BB ) := ( A = ftn ( ll X - ll A ) X ) .


Lemma isover_geh { BB : ltower } { X A : BB } ( is : isover X A ) :
  ll X >= ll A .
Proof.
  unfold isover in is . 
  assert ( int : ll A = ll ( ftn (ll X - ll A) X ) ) . exact ( maponpaths ll is ) .

  rewrite int . rewrite ll_ftn . exact ( natminuslehn _ _ ) .
  
Defined.

Lemma isover_XX { BB : ltower } ( X : BB ) : isover X X .
Proof.
   unfold isover . rewrite natminusnn . apply idpath . 

Defined.

Lemma isover_trans { BB : ltower } { X A A' : BB } :
  isover X A -> isover A A' -> isover X A' .
Proof.
  unfold isover in * .
  set ( llA := ll A ) . set ( llA' := ll A' ) . 
  intro is1 . intro is2 .
  assert ( gte1 := isover_geh is1 ) .
  assert ( gte2 := isover_geh is2 ) . 
  rewrite is2 . rewrite is1 .  
  rewrite ftn_ftn . 
  assert (int : (llA - llA' + (ll X - llA)) = (ll X - llA')) .
  rewrite natpluscomm . 
  exact ( ! ( natminusinter gte1 gte2 ) ) . 

  rewrite int .
  apply idpath .
  
Defined.

Lemma isover_X_ftX { BB : ltower } ( X : BB ) : isover X ( ft X ) .
Proof.
  unfold isover .
  destruct ( natgehchoice _ _ ( natgehn0 ( ll X ) ) )  as [ gt | eq ] . 
  rewrite ll_ft . 
  assert ( eq : ll X - ( ll X - 1 ) = 1 ) . refine ( natminusmmk _ ) . 
  exact ( natgthtogehsn _ _ gt ) . 

  rewrite eq .
  apply idpath . 

  rewrite eq . 
  simpl . 
  exact ( ftX_eq_X eq ) . 

Defined.

Lemma isover_X_ftnX { BB : ltower } ( X : BB ) ( n : nat ) : isover X ( ftn n X ) .
Proof .
  induction n as [ | n IHn ] . 
  exact ( isover_XX _ ) . 

  exact ( isover_trans IHn ( isover_X_ftX _ ) ) . 

Defined.



  
Lemma isover_X_ftA { BB : ltower } { X A : BB }
      ( is : isover X A ) : isover X ( ft A ) .
Proof.
  exact ( isover_trans is ( isover_X_ftX _ ) ) . 

Defined.



Lemma isover_ft { BB : ltower } { X A : BB }
      ( is : isover X A ) ( gt : ll X > ll A ) : isover ( ft X ) A .
Proof.
  unfold isover in * . 
  rewrite ftn_ft . rewrite ll_ft . rewrite <- lB_2014_12_07_l1 .
  exact is .

  exact gt .

Defined.

Lemma isover_ftn { BB : ltower } { n : nat } { X A : BB } 
      ( is : isover X A ) ( gte : ll X - ll A >= n ) : isover ( ftn n X ) A .
Proof.
  revert X A is gte. induction n as [ | n IHn ] .
  intros .  exact is .

  intros . simpl .
  refine ( isover_ft _ _ ) .
  refine ( IHn _ _ _ _ ) . 
  exact is .

  exact ( istransnatgeh _ _ _ gte ( natgehsnn n ) ) .

  rewrite ll_ftn . 
  refine ( natgthleftminus _ _ _ _ ) . 
  assert ( int := natgehgthtrans _ _ _ gte ( natgthsnn n ) ) . 
  rewrite natpluscomm . 
  exact ( natgthrightplus _ _ _ int ) .

Defined .


Lemma isover_choice { BB : ltower } { X A : BB }
      ( is : isover X A ) : coprod ( isover ( ft X ) A ) ( A = X ) .
Proof .
  destruct ( natgehchoice _ _ ( isover_geh is ) ) as [ gt | eq ] . 
  exact ( ii1 ( isover_ft is gt ) ) . 

  unfold isover in is . 
  rewrite eq in is . 
  rewrite natminusnn in is . 
  exact ( ii2 is ) .

Defined.



  
(** **** The predicate isabove and its properties *)


Definition isabove { BB : ltower } ( X A : BB ) :=
  ( ll X > ll A ) × ( isover X A ) .

Definition isabove_constr { BB : ltower } { X A : BB }
           ( gt : ll X > ll A ) ( isov : isover X A ) : isabove X A :=
  gt ,, isov . 

Definition isabove_gth { BB : ltower } { X A : BB } ( is : isabove X A ) :
  ll X > ll A := pr1 is .

Lemma isabove_gt0 { BB : ltower } { X A : BB } ( is : isabove X A ) : ll X > 0 .
Proof .
  exact ( natgthgehtrans _ _ _ ( isabove_gth is ) ( natgehn0 _ ) ) .

Defined.

  
Definition isabove_to_isover { BB : ltower } { X A : BB } :
  isabove X A -> isover X A := pr2 .
Coercion isabove_to_isover : isabove >-> isover .



Lemma isabove_X_ftX { BB : ltower } ( X : BB ) ( gt0 : ll X > 0 ) : isabove X ( ft X ) .
Proof .
  refine ( isabove_constr _ _ ) .
  rewrite ll_ft . 
  exact ( natgthnnmius1 gt0 ) . 

  exact ( isover_X_ftX _ ) . 

Defined.

Lemma isabove_X_ftnX { BB : ltower } { X : BB } { n : nat } ( gt0' : n > 0 ) ( gt0 : ll X > 0 ) :
  isabove X ( ftn n X ) .
Proof.
  induction n as [ | n IHn ] .
  destruct ( negnatgthnn _ gt0' ) .

  refine ( isabove_constr _ _ ) .
  rewrite ll_ftn .
  apply natminuslthn . 
  exact gt0 . 

  exact gt0'.

  apply isover_X_ftnX . 

Defined.



  

  
Lemma isabove_X_ftA { BB : ltower } { X A : BB }
      ( is : isabove X A ) : isabove X ( ft A ) .
Proof .
  refine ( isabove_constr _ _ ) .
  rewrite ll_ft . 
  exact ( natgthgehtrans _ _ _ ( isabove_gth is ) ( natminuslehn _ 1 ) ) . 

  exact (isover_X_ftA is ) .

Defined.


Lemma isabove_X_ftA' { BB : ltower } { X A : BB }
      ( is : isover X A ) ( gt0 : ll A > 0 ) : isabove X ( ft A ) .
Proof .
  refine ( isabove_constr _ _ ) .
  rewrite ll_ft .
  refine ( natgehgthtrans _ _ _ ( isover_geh is ) _ ) .
  exact ( natgthnnmius1 gt0 ) . 

  exact ( isover_X_ftA is ) . 

Defined.



Lemma isabove_trans { BB : ltower } { X A A' : BB } :
  isabove X A -> isabove A A' -> isabove X A' .
Proof.
  intros is is' . refine ( isabove_constr _ _ ) .
  exact ( istransnatgth _ _ _ ( isabove_gth is ) ( isabove_gth is' ) ) .

  exact ( isover_trans is is' ) .

Defined.

Lemma isabov_trans { BB : ltower } { X A A' : BB } :
  isabove X A -> isover A A' -> isabove X A' .
Proof.
  intros is is' . refine ( isabove_constr _ _ ) .
  exact ( natgthgehtrans _ _ _ ( isabove_gth is ) ( isover_geh is' ) ) .

  exact ( isover_trans is is' ) .

Defined.

Lemma isovab_trans { BB : ltower } { X A A' : BB } :
  isover X A -> isabove A A' -> isabove X A' .
Proof.
  intros is is' . refine ( isabove_constr _ _ ) .
  exact ( natgehgthtrans _ _ _ ( isover_geh is ) ( isabove_gth is' ) ) .

  exact ( isover_trans is is' ) .

Defined.











Lemma isover_ft' { BB : ltower } { X A : BB } ( is : isabove X A ) :
  isover ( ft X ) A .
Proof .
  exact ( isover_ft is ( isabove_gth is ) ) . 

Defined.

Lemma isabove_ft_inv { BB : ltower } { X A : BB } ( is : isabove ( ft X ) A ) :
  isabove X A .
Proof .
  exact ( isovab_trans ( isover_X_ftX _ ) is ) .  

Defined.


Lemma ovab_choice { BB : ltower } { X A : BB } ( isov : isover X A ) :
  coprod ( isabove X A ) ( X = A ) .
Proof .
  destruct ( natgehchoice _ _ ( isover_geh isov ) ) as [ gth | eq ] . 
  exact ( ii1 ( tpair _ gth isov ) ) .

  unfold isover in isov . 
  rewrite eq in isov . 
  rewrite natminusnn in isov . 
  exact ( ii2 ( ! isov ) ) . 

Defined.

  
Lemma isabove_choice { BB : ltower } { X A : BB } ( isab : isabove X A ) :
  coprod ( isabove ( ft X ) A ) ( A = ft X ) . 
Proof.
  assert ( isov := isover_ft' isab ) . 
  assert ( gte : ll ( ft X ) >= ll A ) .
  exact ( lltowergehll ( isabove_gth isab ) ) .

  destruct ( natgehchoice _ _ gte ) as [ gt | eq ] .
  exact ( ii1 ( isabove_constr gt isov ) ) . 

  unfold isover in isov . 
  rewrite eq in isov . 
  rewrite natminusnn in isov . 
  exact ( ii2 isov ) . 

Defined.

Lemma isabove_choice_n { BB : ltower } ( n : nat ) { X A : BB } ( isab : isabove X A ) :
  coprod ( isabove ( ftn n X ) A ) ( isover A ( ftn n X ) ) .
Proof .
  revert X A isab. induction n as [ | n IHn ] .
  intros . 
  exact ( ii1 isab ) . 

  intros . 
  assert ( int := IHn X A isab ) . 
  destruct int as [ isab' | isov ] . 
  destruct ( isabove_choice isab' ) as [ isab'' | iseq ] .
  exact ( ii1 isab'' ) .

  refine ( ii2 _ ) . 
  unfold isover .
  rewrite iseq . 
  rewrite natminusnn . 
  apply idpath . 

  exact ( ii2 ( isover_X_ftA isov ) ) . 

Defined.






(** *** Functions between l-towers that are monotone relative to the predicate isover *)

(** **** The basic definitions *)

Definition isovmonot { T1 T2 : ltower } ( f : T1 -> T2 ) :=
  forall ( X Y : T1 ) , isover X Y -> isover ( f X ) ( f Y ) .

Definition ovmonot_fun ( T1 T2 : ltower ) :=
  ∑ f : T1 -> T2, isovmonot f . 

Definition ovmonot_fun_constr { T1 T2 : ltower }
           ( f : T1 -> T2 ) ( is : forall ( X Y : T1 ) , isover X Y -> isover ( f X ) ( f Y ) ) :
  ovmonot_fun T1 T2 := f ,, is .


Definition ovmonot_fun_pr1 ( T1 T2 : ltower ) : ovmonot_fun T1 T2 -> ( T1 -> T2 ) := pr1 . 
Coercion ovmonot_fun_pr1 : ovmonot_fun >-> Funclass .



(** **** Composition of over-monotone functions is over-monotone *)

Definition isovmonot_funcomp { T1 T2 T3 : ltower } { f : T1 -> T2 } { g : T2 -> T3 }
           ( isf : isovmonot f ) ( isg : isovmonot g ) : isovmonot ( funcomp f g ) .
Proof .
  unfold isovmonot .  
  intros X Y is . 
  apply isg . 
  apply isf . 
  apply is . 

Defined.


Definition ovmonot_funcomp { T1 T2 T3 : ltower } ( f : ovmonot_fun T1 T2 ) ( g : ovmonot_fun T2 T3 ) :
  ovmonot_fun T1 T3 :=
  ovmonot_fun_constr ( funcomp f g ) ( isovmonot_funcomp ( pr2 f ) ( pr2 g ) ) . 


(** **** The ll-monot property of over-monotone functions *)

Definition isllmonot { T1 T2 : ltower } ( f : T1 -> T2 ) : UU :=
  forall ( X Y : T1 ) , ll ( f X ) - ll ( f Y ) = ll X - ll Y . 

Lemma isllmonot_funcomp { T1 T2 T3 : ltower } { f : T1 -> T2 } { g : T2 -> T3 }
      ( isf : isllmonot f ) ( isg : isllmonot g ) : isllmonot ( funcomp f g ) .
Proof.
  unfold isllmonot.
  intros X Y .
  assert ( int1 : ll ( g ( f X ) ) - ll ( g ( f Y ) ) = ll ( f X ) - ll ( f Y ) ) .
  apply isg . 

  assert ( int2 : ll ( f X ) - ll ( f Y ) = ll X - ll Y ) .
  apply isf . 

  exact ( int1 @ int2 ) . 

Defined.


Lemma ft_f_X { T1 T2 : ltower } ( f : T1 -> T2 ) ( is1 : isovmonot f ) ( is2 : isllmonot f )
      { X : T1 } ( gt0 : ll X > 0 ) : ft ( f X ) = f ( ft X ) .
Proof.
  assert ( isov := isover_X_ftX X ) . 
  assert ( isov' := is1 _ _ isov ) .
  unfold isover in isov' . 
  change _ with ( f ( ft X ) = ftn ( ll ( f X ) - ll ( f ( ft X ) ) ) ( f X ) ) in isov' . 
  rewrite is2 in isov' . 
  rewrite ll_ft in isov' . 
  rewrite natminusmmk in isov' . 
  exact ( ! isov' ) . 

  apply ( @natgthminus1togeh 1 _ gt0 ) . 

Defined.


(** **** The based functions - the functions that take objects of length zero to objects of length zero *)

Definition isbased { T1 T2 : ltower } ( f : T1 -> T2 ) : UU :=
  forall ( X : T1 ) ( eq0 : ll X = 0 ) , ll ( f X ) = 0 .

Lemma isbased_funcomp { T1 T2 T3 : ltower } { f : T1 -> T2 } { g : T2 -> T3 }
      ( isf : isbased f ) ( isg : isbased g ) : isbased ( funcomp f g ) .
Proof.
  unfold isbased. intros X0 eq0 . unfold funcomp.  
  apply isg . 
  apply isf .
  exact eq0 .

Defined.






  
(** **** Morphisms of l-towers - l-tower functions. *)



Definition isltower_fun { T1 T2 : ltower } ( f : T1 -> T2 ) : UU :=
  ( isovmonot f ) ×
          ( ( isllmonot f ) × ( isbased f ) ) .


Definition ltower_fun ( T1 T2 : ltower ) :=
  ∑ f : T1 -> T2, isltower_fun f .

Definition ltower_fun_to_ovmonot_fun ( T1 T2 : ltower ) ( f : ltower_fun T1 T2 ) :
  ovmonot_fun T1 T2 := ovmonot_fun_constr _ ( pr1 ( pr2 f ) ) . 
Coercion ltower_fun_to_ovmonot_fun : ltower_fun >-> ovmonot_fun .

Definition isovmonot_pr { T1 T2 : ltower } ( f : ltower_fun T1 T2 ) : isovmonot f :=
  pr1 ( pr2 f ) . 


Definition isllmonot_pr { T1 T2 : ltower } ( f : ltower_fun T1 T2 ) : isllmonot f :=
  pr1 ( pr2 ( pr2 f ) ) . 

Definition isbased_pr { T1 T2 : ltower } ( f : ltower_fun T1 T2 ) : isbased f :=
  pr2 ( pr2 ( pr2 f ) ) .



  

Definition ltower_fun_constr { T1 T2 : ltower } { f : T1 -> T2 }
           ( is1 : isovmonot f ) ( is2 : isllmonot f ) ( is3 : isbased f ) :
  ltower_fun T1 T2 :=
  f ,, ( is1 ,, ( is2 ,, is3 ) ) . 



Definition ltower_funcomp { T1 T2 T3 : ltower } ( f : ltower_fun T1 T2 ) ( g : ltower_fun T2 T3 ) :
  ltower_fun T1 T3 .
Proof.
  use ltower_fun_constr. 
  apply ( funcomp f g ) . 

  apply ( isovmonot_funcomp ( isovmonot_pr f ) ( isovmonot_pr g ) ) . 

  apply ( isllmonot_funcomp ( isllmonot_pr f ) ( isllmonot_pr g ) ) . 

  apply ( isbased_funcomp ( isbased_pr f ) ( isbased_pr g ) ) . 

Defined.

Definition ltower_idfun ( T : ltower ) : ltower_fun T T .
Proof.
  use ltower_fun_constr. 
  apply idfun . 

  unfold isovmonot . 
  intros X Y isov . apply isov .

  unfold isllmonot . 
  intros . 
  apply idpath .

  unfold isbased . 
  intros X eq . 
  apply eq .

Defined.










  
(** *** Pointed ltowers

A pointed ltower is an ltower such that the type of its elements of length 0 is contractible. 

 *)


Definition ispointed_type ( T : ltower ) :=
  iscontr ( ∑ X : T, ll X = 0 ) .

Definition pltower := ∑ T : ltower, ispointed_type T.

Definition pltower_constr { T : ltower } ( is : ispointed_type T ) : pltower := tpair _ _ is . 

Definition pltower_pr1 : pltower -> ltower := pr1 .
Coercion pltower_pr1 : pltower >-> ltower .

Definition ispointed ( T : pltower ) : ispointed_type T := pr2 T .  

Definition pltower_to_ltower { T : pltower } ( X : T ) : pltower_pr1 T := X . 

Definition cntr ( T : pltower ) : T :=
  pr1 ( pr1 ( pr2 T ) ) .

Definition ll_cntr ( T : pltower ) : ll ( cntr T ) = 0 :=
  pr2 ( pr1 ( pr2 T ) ) .

Definition ft_cntr ( T : pltower ) : ft ( cntr T ) = cntr T .
Proof .
  intros .
  apply ftX_eq_X .
  apply ll_cntr . 

Defined.

Lemma isoverll0 { T : pltower } 
      { X1 : T } ( eq0 : ll X1 = 0 )
      ( X2 : T ) : isover X2 X1 .
Proof .
  set ( is := pr2 T ) . 
  unfold isover . 
  assert ( eq0' : ll ( ftn ( ll X2 - ll X1 ) X2 ) = 0 ) . 
  rewrite ll_ftn . 
  rewrite eq0 . rewrite natminuseqn.
  exact ( natminusnn _ ) . 

  assert ( eq : tpair ( fun X : T => ll X = 0 ) _ eq0 = tpair ( fun X : T => ll X = 0 ) _ eq0' ) .
  exact ( proofirrelevancecontr is _ _ ) .

  exact ( maponpaths ( @pr1 _ ( fun X : T => ll X = 0 ) ) eq ) . 

Defined.

Definition isover_cntr { T : pltower } ( X : T ) : isover X ( cntr T ) :=
  isoverll0 ( ll_cntr T ) X . 

Lemma noparts_ispointed { T : pltower }
      { X Y : T } ( eqX : ll X = 0 ) ( eqY : ll Y = 0 ) : X = Y .
Proof .
  set ( is := pr2 T ) . 
  set ( int := proofirrelevancecontr is ( tpair _ _ eqX ) ( tpair _ _ eqY ) ) . 
  apply ( maponpaths pr1 int ) . 

Defined.

      

Definition ll_ltower_fun { T1 : pltower } { T2 : ltower } ( f : ltower_fun T1 T2 ) ( X : T1 ) :
  ll ( f X ) = ll X . 
Proof.
  intros.  
  rewrite <- natminuseqn .
  rewrite <- ( ll_cntr T1 ) . 
  rewrite <- ( natminuseqn ( ll ( f X ) ) ) . 
  assert ( eq := isbased_pr f _ ( ll_cntr T1 ) ) .
  rewrite <- eq . 
  exact ( isllmonot_pr f _ _ ) . 

Defined.

Lemma ft_ltower_fun { T1 : pltower } { T2 : ltower } ( f : ltower_fun T1 T2 ) ( X : T1 ) :
  ft ( f X ) = f ( ft X ) .
Proof.
  intros.
  assert ( isov : isover ( f X ) ( f ( ft X ) ) ) . 
  apply ( isovmonot_pr f _ _ ( isover_X_ftX X ) ) . 
  unfold isover in isov . 
  rewrite ( ll_ltower_fun f ) in isov .
  rewrite ( ll_ltower_fun f ) in isov .
  rewrite ll_ft in isov . 
  destruct ( natgehchoice _ _ ( natgehn0 ( ll X ) ) ) as [ gt0 | eq0 ] . 

  assert ( eq1 : ll X - ( ll X - 1 ) = 1 ) .
  apply natminusmmk .
  apply ( @natgthminus1togeh 1 _ gt0 ) .

  rewrite eq1 in isov . 
  exact ( ! isov ) . 

  assert ( eq : ft X = X ) .  apply ( ftX_eq_X eq0 ) .

  rewrite eq. 
  assert ( eq0' : ll ( f X ) = 0 ) . apply ( isbased_pr f _ eq0 ) .

  apply ( ftX_eq_X eq0' ) . 

Defined.


  


  
  
(* End of the file ltowers.v *)
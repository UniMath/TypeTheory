(** ** Constructions related to ltowers over an object  

by Vladimir Voevodsky, started on Feb. 3, 2015.

*)


Require Import UniMath.Foundations.All.
Require Export TypeTheory.Csystems.lTowers.








(** ltowers of objects over an object *)


Definition ltower_over_carrier { T : ltower } ( A : T ) :=
  ∑ X : T, isover X A .

Definition obj_over_constr { T : ltower } { A : T } { X : T } ( isov : isover X A ) :
  ltower_over_carrier A := tpair ( fun X : T => isover X A ) _ isov .

Definition isov_isov { T : ltower } { A : T } ( X : ltower_over_carrier A ) :
  isover ( pr1 X ) A := pr2 X . 

Definition ltower_over_ll { T : ltower } { A : T } ( X : ltower_over_carrier A ) : nat :=
  ll ( pr1 X ) - ll A .
      
Definition ltower_over_ft { T : ltower } { A : T } ( X : ltower_over_carrier A ) :
  ltower_over_carrier A .
Proof .
  destruct ( isover_choice ( isov_isov X ) ) as [ isov | eq ] .
  exact ( tpair _ ( ft ( pr1 X ) )  isov ) .

  exact ( tpair ( fun X : T => isover X A ) A ( isover_XX A ) ) . 

Defined.

Lemma ltower_over_ll_ft_eq { T : ltower } { A : T } ( X : ltower_over_carrier A ) :
  ltower_over_ll ( ltower_over_ft X ) = ltower_over_ll X - 1 .
Proof .
  unfold ltower_over_ft . 
  destruct ( isover_choice ( isov_isov X ) ) as [ isov | eq ] .
  unfold ltower_over_ll .  
  simpl .
  rewrite ll_ft . 
  rewrite natminusassoc . 
  rewrite natpluscomm . 
  rewrite <- natminusassoc . 
  apply idpath . 

  unfold ltower_over_ll .
  simpl . 
  rewrite natminusnn . 
  rewrite <- eq . 
  rewrite natminusnn .
  apply idpath . 

Defined.


Lemma ispointed_ltower_over_int { T : ltower } ( A : T ) :
  iscontr ( ∑ X : ltower_over_carrier A ,
                       ltower_over_ll X = 0 ) .
Proof.
  assert ( weq1 : weq ( total2 ( fun X : ltower_over_carrier A =>
                                   ltower_over_ll X = 0 ) )
                      ( total2 ( fun X : T => dirprod
                                                ( isover X A ) ( ll X - ll A = 0 ) ) ) ) .
  apply weqtotal2asstor . 

  assert ( weq2 : weq ( total2 ( fun X : T => dirprod
                                                ( isover X A ) ( ll X - ll A = 0 ) ) )
                      ( total2 ( fun X : T => A = X ) ) ) .
  refine ( weqfibtototal _ _ _ ) . 
  intro X . 
  assert ( weq3 : weq (dirprod (isover X A) (ll X - ll A = 0))
                      (dirprod (ll X - ll A = 0) (isover X A)) ) .
  apply weqdirprodcomm . 

  assert ( weq4 : weq (dirprod (ll X - ll A = 0) (isover X A))
                      (dirprod (ll X - ll A = 0) ( A = X ) ) ) .
  refine ( weqfibtototal _ _ _ ) . 
  intro eq . 
  unfold isover . 
  rewrite eq . 
  apply idweq.

  assert ( weq5 : weq (dirprod (ll X - ll A = 0) (A = X))
                      (dirprod (A = X)(ll X - ll A = 0))).
  apply weqdirprodcomm . 

  assert ( weq6 : weq (dirprod (A = X) (ll X - ll A = 0))
                      ( A = X ) ) .
  apply weqpr1 . 
  intro eq . 
  rewrite eq . 
  rewrite natminusnn . 
  apply iscontraprop1 . 
  apply isasetnat . 

  apply idpath . 

  apply ( weqcomp weq3 ( weqcomp weq4 ( weqcomp weq5 weq6 ) ) ) .  

  assert ( weq := weqcomp weq1 weq2 ) . 
  apply ( iscontrweqb weq ) .

  apply iscontrpathsfrom .

Defined.

  

         


Lemma ltower_over_ll0_eq { T : ltower } { A : T }
      ( X : ltower_over_carrier A ) ( eq0 : ltower_over_ll X = 0 ) : 
  ltower_over_ft X = X .
Proof .
  assert ( eq0' : ltower_over_ll ( ltower_over_ft X ) = 0 ) . 
  rewrite ltower_over_ll_ft_eq . 
  rewrite eq0 . 
  apply idpath .

  assert ( int : tpair ( fun X' => ltower_over_ll X' = 0 ) _ eq0' =
                 tpair ( fun X' => ltower_over_ll X' = 0 ) X eq0 ) .
  apply ( proofirrelevancecontr ( ispointed_ltower_over_int _ ) _ _ ) .

  apply ( maponpaths ( @pr1 _ ( fun X' => ltower_over_ll X' = 0 ) ) int ) .

Defined.


  

Definition ltower_over { T : ltower } ( A : T ) : ltower :=
  ltower_constr ( @ltower_over_ll _ A ) ( @ltower_over_ft _ A )
                ( @ltower_over_ll_ft_eq _ A ) ( @ltower_over_ll0_eq _ A ) .

  

(** The name of the following function comes from the word octothrope that is the official name for the 
"pound sign". This symbol, as a subscript, is used sometimes to denote the left adjoint to the pull-back 
functor that takes a presheaf represneted by p : X -> B over B to the presheaf represented by X. *)

Definition pocto { T : ltower } { A : T } ( X : ltower_over A ) : T := pr1 X . 

Definition ll_pocto { T : ltower } { A : T } ( X : ltower_over A ) :
  ll ( pocto X ) = ll X + ll A .
Proof.
  intros .
  change ( ll X ) with ( ltower_over_ll X ) . 
  unfold ltower_over_ll .
  rewrite minusplusnmm . 
  apply idpath . 

  apply ( isover_geh ( pr2 X ) ) . 

Defined.


  
Definition ispointed_ltower_over { T : ltower } ( A : T ) : ispointed_type ( ltower_over A ) :=
  ispointed_ltower_over_int A .

Definition pltower_over { T : ltower } ( A : T ) : pltower := pltower_constr ( ispointed_ltower_over A ) . 

Definition ltower_over_to_pltower_over { T : ltower } ( A : T ) ( X : ltower_over A ) :
  pltower_over A := X .

Lemma ltower_over_ftn { T : ltower } { A : T } ( n : nat )
      ( X : ltower_over A ) ( ge : ll X >= n ) : pr1 ( ftn n X ) = ftn n ( pr1 X ) .
Proof .
  revert X ge. 
  induction n .
  + intros . 
    apply idpath . 

  + intros. 
    rewrite <- ftn_ft . 
    rewrite <- ftn_ft . 
    assert ( int : ft ( pr1 X ) = pr1 ( ft X ) ) . 
    - change ( ft X ) with ( ltower_over_ft X ) . 
      unfold ltower_over_ft . 
      destruct ( isover_choice (isov_isov X) ) as [ isov | eq ] . 
      *  simpl . 
         apply idpath . 

      *  change ( ll X ) with ( ll ( pr1 X ) - ll A ) in ge .
         rewrite <- eq in ge . 
         rewrite natminusnn in ge .
         destruct (nopathsfalsetotrue ge).
    -  rewrite int . 
       refine ( IHn ( ft X ) _ ) . 
       apply ( ll_ft_gtn ge ) . 
Defined.


(** **** Standard constructions of over-objects *)

Definition X_over_X { T : ltower } ( X : T ) : ltower_over X :=
  obj_over_constr ( isover_XX X ) .

Lemma ll_X_over_X { T : ltower } ( X : T ) : ll ( X_over_X X ) = 0 .
Proof.
  change _ with ( ll X - ll X = 0 ) .
  apply natminusnn . 

Defined.


  

Definition X_over_ftX { T : ltower } ( X : T ) : ltower_over ( ft X ) :=
  obj_over_constr ( isover_X_ftX X ) .

Lemma ll_X_over_ftX { T : ltower } { X : T } ( gt0 : ll X > 0 ) :
  ll ( X_over_ftX X ) = 1 .
Proof.
  change _ with ( ltower_over_ll (X_over_ftX X) = 1 ) . 
  unfold ltower_over_ll .
  rewrite ll_ft . 
  change _ with ( ll X - ( ll X - 1 ) = 1 ) . 
  apply natminusmmk . 
  apply ( @natgthminus1togeh 1 _ gt0 ) . 

Defined.



(** The projection pocto from the over-tower to the tower is over-monotone *)



Lemma ll_over_minus_ll_over { T : ltower } { A : T } ( X1 X2 : ltower_over A ) :
  ll X1 - ll X2 = ll ( pocto X1 ) - ll ( pocto X2 ) . 
Proof .
  destruct X1 as [ X1 isov1 ] . destruct X2 as [ X2 isov2 ] . 
  unfold ll . 
  simpl . 
  unfold ltower_over_ll .  simpl . 
  change _ with ( ( ll X1 - ll A ) - ( ll X2 - ll A ) = ( ll X1 - ll X2 ) ) . 
  rewrite natminusassoc . 
  rewrite natpluscomm . 
  rewrite ( minusplusnmm _ _ ( isover_geh isov2 ) ) . 
  apply idpath . 

Defined.


Definition isovmonot_pocto { T : ltower } ( A : T ) { X Y : ltower_over A } ( isov : isover X Y ) :
isover ( pocto X ) ( pocto Y ) .  
Proof .
  destruct X as [ X isovX ] .
  destruct Y as [ Y isovY ] .
  simpl . 
  assert ( int := maponpaths pr1 isov ) . 
  simpl in int .
  rewrite ltower_over_ftn in int . 
  simpl in int . 
  rewrite ll_over_minus_ll_over in int . 
  simpl in int . 
  exact int . 

  exact ( natminuslehn _ _ ) . 

Defined.



Lemma isllmonot_pocto { T : ltower } { A : T } : isllmonot ( @pocto T A ) . 
Proof .
  unfold isllmonot .
  intros X Y .
  apply ( ! ( ll_over_minus_ll_over X Y ) ) .

Defined.


(** **** The projection pocto and ft *)

Lemma ft_pocto { T : ltower } { A : T } { X : ltower_over A } ( gt0 : ll X > 0 ) :
  ft ( pocto X ) = pocto ( ft X ) .
Proof.
  change ( ft X ) with ( ltower_over_ft X ) . 
  unfold ltower_over_ft .
  destruct (isover_choice (isov_isov X)) as [ isov | eq ] . 
  simpl . 
  apply idpath . 

  assert ( absd : empty ) . 
  assert ( eq0 : ll X = 0 ) .  change _ with ( ll ( pr1 X ) - ll A = 0 ) . 
  rewrite <- eq . 
  apply natminusnn .

  rewrite eq0 in gt0 . apply ( negnatgthnn _ gt0 ) . 

  destruct absd .

Defined.



  
(** **** Some functions between over-towers *)


Definition to_ltower_over { T : pltower } ( X : T ) : ltower_over ( cntr T ) .
Proof .
  exact ( obj_over_constr ( isoverll0 ( ll_cntr T ) X ) ) .

Defined.


Lemma ll_to_ltower_over { T : pltower } ( X : T ) :
  ll ( to_ltower_over X ) = ll X .
Proof .
  unfold ll . 
  simpl .
  unfold ltower_over_ll . 
  rewrite ll_cntr . 
  rewrite natminuseqn .
  apply idpath . 

Defined.

  
Lemma isllmonot_to_ltower_over ( T : pltower )  :
  isllmonot ( @to_ltower_over T ) .
Proof .
  unfold isllmonot . intros .
  repeat rewrite ll_to_ltower_over . apply idpath . 
  
Defined.


Lemma isbased_to_ltower_over ( T : pltower ) :
  isbased ( @to_ltower_over T ) .
Proof .
  unfold isbased. intros X eq0 .
  rewrite ll_to_ltower_over . 
  exact eq0 .

Defined.




  
(** The following constructions probably work for all ltowers 
but we only give a proof for ltowers of sets in the file hSet_ltowers.v . 

Definition ovmonot_to_over_pocto  { T : ltower } { X : T } { X' : ltower_over X } :
  ovmonot_fun ( ltower_over X' ) ( ltower_over ( pocto X' ) ) .

Definition ovmonot_over { T1 T2 : ltower } ( f : ovmonot_fun T1 T2 )
           ( X : T1 ) : ovmonot_fun ( ltower_over X ) ( ltower_over ( f X ) ) .

Definition lft { T : hSet_ltower }
           { X : T } { X' : ltower_over X } ( X'' : ltower_over ( pocto X' ) ) : ltower_over X' .

Definition ovmonot_second { T : ltower }
           { X Y : T } ( f : ovmonot_fun ( ltower_over X ) ( ltower_over Y ) )
           ( X' : ltower_over X ) :
  ovmonot_fun ( ltower_over ( pocto X' ) ) ( ltower_over ( pocto ( f X' ) ) ) .


Lemma isovmonot_to_ltower_over { T : ltower } ( is : ispointed T ) : isovmonot ( to_ltower_over is ) . 

*)





(* End of the file ltowers_over.v *)
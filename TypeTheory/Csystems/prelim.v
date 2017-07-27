(** * Preliminaries to lBsystems. To be moved to upstream files later. 

by Vladimir Voevodsky, file created on Jan. 6, 2015 *)


Unset Automatic Introduction.

Require Export UniMath.Combinatorics.StandardFiniteSets.


(* To upsetream files *)


Notation isaproptotal2 := ( isofhleveltotal2 1 )  .


Lemma gth0_to_geh1 { n : nat } ( gt0 : n > 0 ) : n >= 1 .
Proof.
  intros.
  induction n as [ | n IHn ] .
  assert ( absd : empty ) .
  apply ( negnatgthnn _ gt0 ) . 
  destruct absd .

  apply ( natgehn0 n ) . 

Defined.


Lemma geh1_to_gth0 { n : nat } ( geh1 : n >= 1 ) : n > 0 .
Proof.
  intros .
  apply ( natgehgthtrans _ _ _ geh1 ( natgthsnn 0 ) ) .

Defined.

Lemma natminusind ( m n : nat ) : m - S n = ( m - 1 ) - n . 
Proof . intros .
        induction m as [ | m IHm ] .  apply idpath . simpl .  rewrite ( natminuseqn m ) . 
        apply idpath .
Defined.




Lemma natgthnnmius1 { n : nat } ( gt : n > 0 ) : n > n - 1 .
Proof.
  intros . induction n as [ | n ] . 
  induction ( negnatgthnn _ gt ) . 

  change ( S n > n - 0 ) . 
  rewrite natminuseqn . 
  exact ( natgthsnn _ ) .

Defined.

Lemma natminusnn ( n : nat ) : n - n = 0 .
Proof.
  intro . induction n as [ | n IHn ] .
  exact ( idpath _ ) .

  exact IHn . 

Defined.


Lemma natminusmequalsn { m n : nat } ( ge : n >= m ) ( eq0 : n - m = 0 ) : n = m .
Proof .
  intro m . induction m as [ | m IHm ] .
  + intros . 

    rewrite natminuseqn in eq0 . 
    exact eq0 .

  + intros .
    induction n as [ | n ] .
    * destruct (nopathsfalsetotrue ge).
    * apply ( maponpaths S ) . exact ( IHm n ge eq0 ) . 

Defined.


Lemma natmiusmius1mminus1 { n m : nat } ( gt1 : n > 0 ) ( gt2 : m > 0 ) :
  ( n - 1 ) - ( m - 1 ) = n - m .
Proof .
  intro n . induction n as [ | n IHn ] .
  intros . 
  destruct ( negnatgthnn _ gt1 ) . 

  intros .
  simpl . rewrite natminuseqn . induction m as [ | m ] .
  destruct ( negnatgthnn _ gt2 ) . 

  simpl . rewrite natminuseqn . apply idpath .

Defined.

Lemma natgthtominus1geh { m n : nat } : m > n -> m - 1 >= n .
Proof.
  intro m . induction m as [ | m IHm ] .
  + intros n gt . 
    destruct (nopathsfalsetotrue gt).
  + intros n gt .
    change ( m - 0 >= n ) . rewrite ( natminuseqn m ) . apply natgthsntogeh . exact gt .
  
Defined .

Lemma natgthminus1togeh { n m : nat } : m > n - 1 -> m >= n .
Proof.
  intro n . induction n as [ | n IHn ] .
  intros m gt . exact ( natgehn0 _ ) .
  
  intros m gt .
  change ( S n - 1 ) with ( n - 0 ) in gt . rewrite ( natminuseqn n ) in gt .
  apply natgthtogehsn . exact gt .
  
Defined .

Lemma nat1plusminusgt { n m : nat } ( gt : 1 + m > n ) : ( 1 + m ) - n = 1 + ( m - n ) .
Proof.
  intros .
  apply ( natplusrcan _ _ n ) . rewrite ( natplusassoc _ _ n ) .
  rewrite ( minusplusnmm _ n ( natgthtogeh _ _ gt ) ) .
  rewrite ( minusplusnmm _ n ) . 
  apply idpath .

  apply ( natgthsntogeh _ _ gt ) . 

Defined.


Lemma lB_2014_12_07_l1 { m n : nat } ( gt : m > n ) : m - n = 1 + (( m - 1 ) - n ) .
Proof.
  intros. induction m as [ | m IHm ] .

  + destruct (nopathsfalsetotrue gt).

  + clear IHm. change ( S m - n = S ( m - 0 - n ) ) . rewrite  ( natminuseqn m ) . 
  exact ( nat1plusminusgt gt ) .
Defined.


Lemma natminusmmk { m k : nat } ( ge : m >= k ) : m - ( m - k ) = k .
Proof.
  intros .
  apply ( natplusrcan _ _ ( m - k ) ) .
  rewrite minusplusnmm . 
  rewrite natpluscomm . 
  rewrite minusplusnmm .
  apply idpath . 

  apply ge . 

  apply natminuslehn. 

Defined.

 
  
Lemma natleftplustorightminus ( n m k : nat ) : n + m = k -> n = k - m .
Proof.
  intros n m k e .
  assert ( ge : k >= m ) . rewrite <- e . exact ( natgehplusnmm _ _ ) .  

  apply ( natplusrcan _ _ m ) . rewrite ( minusplusnmm _ _ ge ) . 
  exact e .

Defined.




Definition natassocpmeq ( n m k : nat ) ( ge : m >= k ) : ( n + m ) - k =  n + ( m - k ) .
Proof.
  intros.  apply ( natplusrcan _ _ k ) . rewrite ( natplusassoc n _ k ) .
  rewrite ( minusplusnmm _ k ge ) .
  set ( ge' := istransnatgeh _ _ _ ( natgehplusnmm n m ) ge ) .
  rewrite ( minusplusnmm _ k ge' ) . apply idpath.
  
Defined.

Definition natassocmpeq ( n m k : nat ) ( isnm : n >= m ) ( ismk : m >= k ) :
  ( n - m ) + k = n - ( m - k ) .
Proof. intros.  apply ( natplusrcan _ _ ( m - k ) ) . 
       assert ( is' : natleh ( m - k ) n ) .
       apply ( istransnatleh (natminuslehn _ _ ) isnm ) .
       rewrite ( minusplusnmm _ _ is' ) . rewrite (natplusassoc _ k _ ) .
       rewrite ( natpluscomm k _ ) . rewrite ( minusplusnmm _ _ ismk ) .
       rewrite ( minusplusnmm _ _ isnm ) . apply idpath.
Defined.


Definition natminusassoc ( n m k : nat ) : ( n  - m ) - k = n - ( m + k ) .
Proof. intros n m . revert n . 

       induction m as [ | m IHm ] .  intros  . simpl .  rewrite ( natminuseqn n ) . apply idpath .
       intros .  rewrite ( natminusind n m ) .  rewrite ( IHm ( n - 1 ) k ) .
       rewrite ( ! ( natminusind _ _ ) ) .  apply idpath . 
Defined.


Definition natminuscomm ( n m k : nat ) : ( n - m ) - k = ( n - k ) - m .
Proof .
  intros .
  rewrite natminusassoc . 
  rewrite natminusassoc . 
  rewrite natpluscomm . 
  apply idpath .

Defined.
 



Definition natminusinter { n m k : nat } ( ge1 : n >= m ) ( ge2 : m >= k ) :
  n - k = ( n - m ) + ( m - k ) .
Proof.
  intros .
  assert ( int1 : n - m + (m - k) = n - ( m - ( m - k ))).   refine ( natassocmpeq _ _ _ _ _ ) . 
  exact ge1 . 

  exact ( natminuslehn _ _ ) . 

  assert ( int2 : m - ( m - k ) = k ) . exact ( natminusmmk ge2 ) .

  rewrite int2 in int1 . exact ( ! int1 ) . 
Defined.


(** [ nateq ] *)

Notation nateqandplusrinv := natplusrcan .

Notation nateqandpluslinv := natpluslcan .

Definition nateqandplusr ( n m k : nat ) : n = m -> n + k = m + k :=
  maponpaths ( fun x => x + k ) .

Definition nateqandplusl ( n m k : nat ) : n = m -> k + n = k + m :=
  maponpaths ( fun x => k + x ) .




(** **** Cancellation properties of minus on nat *)

Lemma natminusrcan { n m k : nat } ( ge1 : n >= k ) ( ge2 : m >= k ) ( is : n - k = m - k ) :
  n = m .
Proof .
  intros .
  assert ( is' := nateqandplusr _ _ k is ) .
  rewrite ( minusplusnmm _ _ ge1 ) in is' .
  rewrite ( minusplusnmm _ _ ge2 ) in is' .
  exact is' .

Defined.



  

(* **** Greater and minus *)


Definition natgthrightminus ( n m k : nat ) ( ge : k >= m ) : n + m > k -> n > k - m .
Proof . intros n m k ge gt . apply ( natgthandplusrinv _ _ m ) .
        rewrite ( minusplusnmm _ _ ge ) .
        exact gt .
Defined.

Definition natgthrightplus ( n m k : nat ) : n - m > k -> n > k + m .
Proof .
  intros n m k gt . assert ( ge : n >= m ) . apply natgthtogeh .
  
  apply minusgth0inv .  apply ( natgthgehtrans _ _ _ gt ( natgehn0 k ) ) .
  assert ( gt' : ( n - m ) + m > k + m ) . apply ( natgthandplusr _ _ _ gt ) .
  
  rewrite ( minusplusnmm _ _ ge ) in gt' . exact gt' .
Defined.
  
Definition natgthleftminus ( n m k : nat ) : n > m + k -> n - k > m .
Proof.
  intros n m k gt .  apply ( natgthandplusrinv _ _ k ) .
  assert ( ge' : n >= k ) . apply natgthtogeh .
  exact ( natgthgehtrans _ _ _ gt ( natgehplusnmm _ _ ) ) .
  
  rewrite ( minusplusnmm _ _ ge' ) . 
  exact gt .
Defined.


Definition natgthleftplus ( n m k : nat ) : n > m - k -> n + k > m .
Proof .
  intros n m k gt .
  assert ( gt' : n + k > m - k + k ) .  exact ( natgthandplusr _ _ k gt ) . 
  exact ( natgthgehtrans _ _ _ gt' ( minusplusnmmineq _ _ ) ) . 
Defined .

Definition natgthleftminusminus ( n m k : nat ) : n - m > k -> n - k > m .
Proof .
  intros n m k gt . assert ( gt' : n > k + m ) . exact ( natgthrightplus _ _ _ gt ) .

  rewrite ( natpluscomm _ _ ) in gt' . exact ( natgthleftminus _ _ _ gt' ) . 
Defined.


  

(* **** Greater or equal and minus *)

Definition natgehrightminus ( n m k : nat ) ( ge : k >= m ) : n + m >= k -> n >= k - m .
Proof.
  intros n m k ge ge' . apply ( natgehandplusrinv _ _ m ) .  rewrite ( minusplusnmm _ _ ge ) .
  exact ge' .
Defined.


Definition natgehrightplus ( n m k : nat ) ( ge : n >= m ) : n - m >= k -> n >= k + m .
Proof.
  intros n m k ge ge' .  rewrite ( ! minusplusnmm _ _ ge ) .  apply ( natgehandplusr _ _ _ ) . 
  exact ge' .
Defined.

Definition natgehleftminus ( n m k : nat ) : n >= m + k ->  n - k >= m .
Proof.
  intros n m k ge .  apply ( natgehandplusrinv _ _ k ) .
  assert ( ge' : n >= k ) . exact ( istransnatgeh _ _ _ ge ( natgehplusnmm _ _ ) ) .
  rewrite ( minusplusnmm _ _ ge' ) . 
  exact ge .
Defined.

Definition natgehleftplus ( n m k : nat ) : n >= m - k -> n + k  >= m .
Proof.
  intros n m k ge .
  assert ( ge' : n + k >= m - k + k ) .  exact ( natgehandplusr _ _ k ge ) . 
  exact ( istransnatgeh _ _ _ ge' ( minusplusnmmineq _ _ ) ) . 
Defined .

Definition natgehleftminusminus ( n m k : nat ) ( ge : n >= m ) : n - m >= k -> n - k >= m .
Proof .
  intros n m k ge ge' . assert ( ge'' : n >= k + m ) . exact ( natgehrightplus _ _ _ ge ge' ) .

  rewrite ( natpluscomm _ _ ) in ge'' . exact ( natgehleftminus _ _ _ ge'' ) . 
Defined.


(* Two-sided minus and greater *)

Definition natgthandminusinvr { n m k : nat } ( is : n > m ) ( is' : m >= k ) :
  n - k > m - k .
Proof .
  intro n. induction n as [ | n IHn ] .
  intros . destruct ( negnatgth0n _ is ) .
  
  intro m . induction k as [ | k ] . intros .
  repeat rewrite natminuseqn .
  exact is .

  intros . induction m as [ | m ] .
  destruct ( negnatgeh0sn _ is' ) .

  exact ( IHn m k is is' ) .

Defined.





(* Two-sided minus and greater or equal *) 

Definition natgehandminusl ( n m k : nat ) ( ge : n >= m ) : k - m >= k - n .
Proof.
  intro n. induction n as [ | n IHn ] .
  intros .  rewrite ( nat0gehtois0 _ ge ) . apply isreflnatleh .

  intro m . induction m as [ | m ] . intros . induction k as [ | k ] .
  apply natminuslehn .

  apply natminuslehn .

  intro k . induction k as [ | k ] . intro is .
  apply isreflnatleh .

  intro is .  apply ( IHn m k ) . apply is .

Defined.


Definition natgthandminuslinv { n m k : nat } ( gt : n - k > n - m ) : m > k .
Proof .
  intros .
  apply negnatlehtogth . 
  intro ge . 
  assert ( ge' : n - m >= n - k ) by
  exact ( natgehandminusl _ _ _ ge ) .

  exact (natgthnegleh gt ge') . 

Defined.

  

(* Decrement function on nat *)

Definition dec ( n : nat ) : nat :=
  match n with
      O => O |
    S n' => n'
  end .


(* End of the file lBsystems_prelim.v *)
(** ** lC0-systems 

by Vladimir Voevodsky, started Dec. 4, 2014, continued Jan. 22, 2015, Feb. 11, 2015 

We refer below to the paper "Subsystems and regular quotients of C-systems"
by V. Voevodsky as "Csubsystems".

*)

Require Import UniMath.Foundations.All.

(* Require Import UniMath.CategoryTheory.Categories. *)
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.           
Require Import UniMath.CategoryTheory.limits.terminal.
Require Export TypeTheory.Csystems.hSet_ltowers.


Section Upstream.

Lemma idtoisoinvcancelleft {CC: precategory}{A B C: CC} (eq: B = A)(f: A --> C)(g: B --> C):  g = idtoiso eq ;; f -> iso_inv_from_iso (idtoiso eq);; g = f.
Proof.
  induction eq.
  intro Hyp.
  simpl.
  rewrite id_left.
  rewrite id_left in Hyp.
  exact Hyp.
Defined.

(** in the following, [s] and [t] stand for source and target of the "arrow transformer" [art] *) 
Lemma eq_function_on_morphisms {CC: precategory}{A B: CC}
      ( s t: CC ⟦ A , B ⟧ -> ob CC )
      ( art: forall g: CC ⟦ A , B ⟧, CC ⟦ s g , t g ⟧)
      ( g g': A --> B )(e : g = g'):
  art g ;; idtoiso (maponpaths t e) = idtoiso (maponpaths s e) ;; art g'.
Proof.
  induction e.
  simpl.
  rewrite id_left.
  rewrite id_right.
  apply idpath.
Defined.


End Upstream.




(* Notation "a --> b" := (precategory_morphisms a b)(at level 50). *)

(* Notation "f ;; g" := (compose f g)(at level 50). *)


Definition mor_from { C : precategory_ob_mor } ( X : C ) := ∑ A : C, X --> A.
(* compare with UniMath.CategoryTheory.coslicecat.coslicecat_ob *)

Definition mor_from_pr2 { C : precategory_ob_mor } ( X : C ):
  forall f : mor_from X, precategory_morphisms X ( pr1 f ) := pr2.  
Coercion mor_from_pr2 : mor_from >-> precategory_morphisms.
(* compare with UniMath.CategoryTheory.coslicecat.coslicecat_ob_morphism *)

Definition mor_from_constr { C : precategory_ob_mor } { X A : C } ( f : X --> A ):
  mor_from X := tpair _ _ f. 


Definition mor_to { C : precategory_ob_mor } ( X : C ) := ∑ A : C, A --> X.
(* compare with UniMath.CategoryTheory.slicecat.slicecat_ob *)

Definition mor_to_pr2 { C : precategory_ob_mor } ( X : C ):
  forall f : mor_to X , precategory_morphisms ( pr1 f ) X := pr2.  
Coercion mor_to_pr2 : mor_to >-> precategory_morphisms.
(* compare with UniMath.CategoryTheory.slicecat.slicecat_ob_morphism *)

Definition mor_to_constr { C : precategory_ob_mor } { X A : C } ( f : A --> X ):
  mor_to X := tpair ( fun A : C => A --> X ) _ f.

 
(** reminder from UniMath.CategoryTheory.Categories *)
(*
Definition isaset_ob ( C : setcategory ): isaset C := pr1 ( pr2 C ).

Definition isaset_mor ( C : setcategory ): has_homsets C := pr2 ( pr2 C ). 
*)


(** *** The C0-systems

The following sequence of definitions is a formalization of Definition 2.1 in Csubsystems *)

(** **** The carrier of an lC0-system 

as a set precategory whose objects form a pointed hSet-ltower with the additional structure of
the canonical projections pX : X --> ft X . *)



(** **** l-tower precategories *)


Definition ltower_precat := ∑ C : setcategory, ltower_str C. 

Definition ltower_precat_to_ltower ( CC : ltower_precat ): hSet_ltower :=
  hSet_ltower_constr
    ( tpair ( fun C : UU => ltower_str C ) ( pr1 CC ) ( pr2 CC ) )
    ( pr1 ( pr2 ( pr1  CC ) ) ).
Coercion ltower_precat_to_ltower: ltower_precat >-> hSet_ltower.

Definition ltower_precat_pr1: ltower_precat -> setcategory := pr1.
Coercion ltower_precat_pr1: ltower_precat >-> setcategory.

Definition ltower_precat_and_p :=
  ∑ CC : ltower_precat, forall X : CC, X --> ft X.

Definition ltower_precat_and_p_pr1: ltower_precat_and_p -> ltower_precat := pr1. 
Coercion ltower_precat_and_p_pr1: ltower_precat_and_p >-> ltower_precat. 
                                                          
Definition pX { CC : ltower_precat_and_p } ( X : CC ): X --> ft X := pr2 CC X.




(** **** Some constructions *)

Definition pnX { CC : ltower_precat_and_p } ( n : nat ) ( X : CC ): X --> ftn n X. 
Proof.
  induction n as [ | n IHn ].
  - exact ( identity X ). 
  - destruct n as [ | n ].
    + exact ( pX X ). 
    + exact ( IHn ;; pX ( ftn ( S n ) X ) ).
Defined.


Definition sec_pnX { CC : ltower_precat_and_p } ( n : nat ) ( X : CC ) :=
  ∑ s : ftn n X --> X, s ;; pnX n X = identity ( ftn n X ). 

Definition sec_pnX_to_mor { CC : ltower_precat_and_p } ( n : nat ) ( X : CC ):
  sec_pnX n X -> ftn n X --> X := pr1.
Coercion sec_pnX_to_mor : sec_pnX >-> precategory_morphisms.

Definition sec_pnX_eq { CC : ltower_precat_and_p } { n : nat } { X : CC } ( s : sec_pnX n X ):
  s ;; pnX n X = identity ( ftn n X ) := pr2 s. 
  
Notation sec_pX := (sec_pnX 1).

Notation sec_pX_eq := (@sec_pnX_eq _ 1 _ ).


Definition ftf { CC : ltower_precat_and_p } { X Y : CC } ( f : X --> Y ): X --> ft Y :=
  f ;; pX Y. 


Definition Ob_tilde_over { CC : ltower_precat_and_p  } ( X : CC ) :=
  ∑ r : ft X --> X, r ;; ( pX X ) = identity ( ft X ).

Local Lemma Ob_tilde_over_is_sec_pX { CC : ltower_precat_and_p  } ( X : CC ):
  Ob_tilde_over X = sec_pX X.
Proof.
  apply idpath.
Qed.

Definition Ob_tilde_over_to_mor_to { CC : ltower_precat_and_p } ( X : CC ) ( r : Ob_tilde_over X ):
  mor_to X := mor_to_constr ( pr1 r ).
Coercion Ob_tilde_over_to_mor_to: Ob_tilde_over >-> mor_to. 

Definition Ob_tilde_over_to_mor_from { CC : ltower_precat_and_p  } ( X : CC ) ( r : Ob_tilde_over X ):
  mor_from ( ft X ) := mor_from_constr ( pr1 r ).
Coercion Ob_tilde_over_to_mor_from: Ob_tilde_over >-> mor_from.

Definition Ob_tilde_over_eq { CC : ltower_precat_and_p  } { X : CC } ( r : Ob_tilde_over X ):
  r ;; ( pX X ) = identity ( ft X ) := pr2 r. 



(** **** Pointed ltower precategories *)


Definition pltower_precat_and_p :=
  ∑ CC : ltower_precat_and_p, ispointed_type CC.

Definition pltower_precat_and_p_pr1 :
  pltower_precat_and_p -> ltower_precat_and_p := pr1.
Coercion pltower_precat_and_p_pr1 :
  pltower_precat_and_p >-> ltower_precat_and_p.

Definition pltower_precat_and_p_to_pltower: pltower_precat_and_p -> pltower :=
  fun X => pltower_constr ( pr2 X ). 
Coercion pltower_precat_and_p_to_pltower: pltower_precat_and_p >-> pltower.


(** **** l-C0-system data *)


Definition q_data_type ( CC : ltower_precat_and_p ) := 
  forall ( X Y : CC ) ( gt0 : ll X > 0 ) ( f : Y --> ft X ), mor_to X. 
Identity Coercion from_q_data_type: q_data_type >-> Funclass.  

Definition lC0system_data := ∑ CC : pltower_precat_and_p, q_data_type CC.

Definition lC0system_data_pr1: lC0system_data -> pltower_precat_and_p := pr1.
Coercion lC0system_data_pr1: lC0system_data >-> pltower_precat_and_p.

Definition codom { CC : lC0system_data } { X : CC } ( f : mor_from X ): CC := pr1 f.

Definition dom { CC : lC0system_data } { X : CC } ( f : mor_to X ): CC := pr1 f.


Definition q_of_f { CC : lC0system_data }  
           { X Y : CC } ( gt0 : ll X > 0 ) ( f : Y --> ft X ) : mor_to X :=
  pr2 CC _ _ gt0 f . 

Definition f_star { CC : lC0system_data }  
           { X Y : CC } ( gt0 : ll X > 0 ) ( f : Y --> ft X ): CC := 
  dom ( q_of_f gt0 f ).

(** Formulation of q_of_f as a function from mor_to to mor_to *)

Definition q_of_mor_to { CC : lC0system_data } { X : CC } ( gt0 : ll X > 0 )
  ( f : mor_to ( ft X ) ): mor_to X := q_of_f gt0 f .

Definition mor_to_star { CC : lC0system_data } { X : CC } ( gt0 : ll X > 0 )
  ( f : mor_to ( ft X ) ): CC := f_star gt0 f.



(** **** Properties on l-C0-system data 

that later become axioms of an lC0-system. The numbering of the conditions below is according to 
the Csubsystems paper.

The conditions 1-3 are consequences of the definition of a pointed l-tower (pltower) *)

Definition C0ax4_type ( CC : pltower_precat_and_p ) :=  isTerminal _ (cntr CC).         
(*
Definition C0ax4_type ( CC : pltower_precat_and_p ) :=
  forall X : CC, iscontr ( X --> cntr CC ).
*)

Definition C0ax5a_type ( CC : lC0system_data ) :=
  forall ( X Y : CC ) ( gt0 : ll X > 0 ) ( f : Y --> ft X ), ll ( f_star gt0 f ) > 0.

Definition C0ax5b_type ( CC : lC0system_data ) :=
  forall ( X Y : CC ) ( gt0 : ll X > 0 ) ( f : Y --> ft X ), ft ( f_star gt0 f ) = Y.

(** A construction needed to formulate further properties of the C0-system data. *)

Definition C0ax5b_iso { CC : lC0system_data } ( ax5b : C0ax5b_type CC )
  { X Y : CC } ( gt0 : ll X > 0 ) ( f : Y --> ft X ):
  iso (ft ( f_star gt0 f )) Y := idtoiso ( ax5b X Y gt0 f ).

(** the following definition is only used for work with the definitions *)
Definition C0ax5b_iso_inv { CC : lC0system_data } ( ax5b : C0ax5b_type CC )
           { X Y : CC } ( gt0 : ll X > 0 ) ( f : Y --> ft X ):
  iso Y (ft ( f_star gt0 f )) := iso_inv_from_iso (C0ax5b_iso ax5b gt0 f).


(** The description of properties continues *)

Definition C0ax5c_type { CC : lC0system_data } ( ax5b : C0ax5b_type CC ) := 
  forall ( X Y : CC ) ( gt0 : ll X > 0 ) ( f : Y --> ft X ), 
    pX ( f_star gt0 f ) ;; ( ( C0ax5b_iso ax5b gt0 f ) ;; f ) = ( q_of_f gt0 f ) ;; ( pX X ).

Definition C0ax6_type ( CC : lC0system_data ) :=
  forall ( X : CC ) ( gt0 : ll X > 0 ),
    q_of_f gt0 ( identity ( ft X ) ) = mor_to_constr ( identity X ). 

Definition C0ax7_type { CC : lC0system_data } 
  ( ax5a : C0ax5a_type CC ) ( ax5b : C0ax5b_type CC ) :=
  forall ( X Y Z : CC ) ( gt0 : ll X > 0 ) ( f : Y --> ft X ) ( g : Z --> ft ( f_star gt0 f ) ),
    mor_to_constr ( ( q_of_f ( ax5a _ _ gt0 f ) g ) ;; ( q_of_f gt0 f ) ) =
    q_of_f gt0 ( g ;; ( ( C0ax5b_iso ax5b gt0 f ) ;; f ) ).



(** **** The type of l-C0-systems *)


Definition lC0system :=
  ∑ CC : lC0system_data,
                     ( C0ax4_type CC ) ×
                     ( ∑ axs : ( C0ax5a_type CC ) ×
                               ( ∑ ax5b : C0ax5b_type CC, C0ax5c_type ax5b ), 
                          ( C0ax6_type CC ) ×
                          ( C0ax7_type ( pr1 axs ) ( pr1 ( pr2 axs ) ) ) ).

Definition lC0system_pr1: lC0system -> lC0system_data := pr1.
Coercion lC0system_pr1: lC0system >-> lC0system_data.

(* Definition C0_isaset_Ob ( CC : lC0system ) : isaset CC := pr1 ( pr1 ( pr2 CC ) ) .

Definition C0_has_homsets ( CC : lC0system ) : has_homsets CC := pr2 ( pr1 ( pr2 CC ) ) . *)

Definition C0ax4 ( CC : lC0system ): C0ax4_type CC := pr1 ( pr2 CC ). 

Definition C0ax5a { CC : lC0system } { X Y : CC } ( gt0 : ll X > 0 ) ( f : Y --> ft X ):
  ll ( f_star gt0 f ) > 0 := pr1 ( pr1 ( pr2 ( pr2 CC ) ) ) X Y gt0 f.

Definition C0ax5b { CC : lC0system } { X Y : CC } ( gt0 : ll X > 0 ) ( f : Y --> ft X ):
  ft ( f_star gt0 f ) = Y := pr1 ( pr2 ( pr1 ( pr2 ( pr2 CC )))) X Y gt0 f.

Notation ft_f_star := C0ax5b. 

Definition C0eiso { CC : lC0system } { X Y : CC } ( gt0 : ll X > 0 ) ( f : Y --> ft X ):
  iso (ft ( f_star gt0 f )) Y := C0ax5b_iso ( @C0ax5b CC ) gt0 f.

Definition C0eiso_inv { CC : lC0system } { X Y : CC } ( gt0 : ll X > 0 ) ( f : Y --> ft X ):
  iso Y (ft ( f_star gt0 f )) := C0ax5b_iso_inv ( @C0ax5b CC ) gt0 f.


Definition C0ax5c { CC : lC0system }
           { X Y : CC } ( gt0 : ll X > 0 ) ( f : Y --> ft X ): 
  pX ( f_star gt0 f ) ;; ( ( C0eiso gt0 f ) ;; f ) =
  ( q_of_f gt0 f ) ;; ( pX X ) :=
  pr2 ( pr2 ( pr1 ( pr2 ( pr2 CC )))) X Y gt0 f. 


Definition C0ax6 { CC : lC0system } { X : CC } ( gt0 : ll X > 0 ):
  q_of_f gt0 ( identity ( ft X ) ) = mor_to_constr ( identity X ) :=
  pr1 ( pr2 ( pr2 ( pr2 CC ))) X gt0.

Definition C0ax6a { CC : lC0system } { X : CC } ( gt0 : ll X > 0 ):
  f_star gt0 ( identity ( ft X ) ) = X := maponpaths pr1 ( C0ax6 gt0 ).

Definition C0ax7 { CC : lC0system } { X Y Z : CC }
  ( gt0 : ll X > 0 ) ( f : Y --> ft X ) ( g : Z --> ft ( f_star gt0 f ) ):
  mor_to_constr ( ( q_of_f ( C0ax5a gt0 f ) g ) ;; ( q_of_f gt0 f ) ) =
  q_of_f gt0 ( g ;; ( ( C0eiso gt0 f ) ;; f ) ) :=
  pr2 ( pr2 ( pr2 ( pr2 CC ))) X Y Z gt0 f g.

Definition C0ax7a { CC : lC0system } { X Y Z : CC }
  ( gt0 : ll X > 0 ) ( f : Y --> ft X ) ( g : Z --> ft ( f_star gt0 f ) ):
  f_star ( C0ax5a gt0 f ) g = f_star gt0 ( g ;; ( ( C0eiso gt0 f ) ;; f ) ) :=
  maponpaths pr1 ( C0ax7 gt0 f g ).

(** **** Some simple properties of lC0systems *)

Lemma ll_f_star { CC : lC0system } { X Y : CC } ( gt0 : ll X > 0 ) ( f : Y --> ft X ):
  ll ( f_star gt0 f ) = 1 + ll Y.
Proof.
  assert ( gt0': ll ( f_star gt0 f ) > 0 ) by apply C0ax5a.
  rewrite <- ( S_ll_ft gt0' ).
  rewrite C0ax5b.
  apply idpath.
Defined.


Lemma isover_f_star { CC : lC0system } { X Y : CC } ( gt0 : ll X > 0 ) ( f : Y --> ft X ):
  isover ( f_star gt0 f ) Y.
Proof.
  set ( eq := C0ax5b gt0 f ).
  unfold isover. 
  assert ( eq1 : ll ( f_star gt0 f ) - ll Y = 1 ).
  { rewrite ll_f_star. 
    apply plusminusnmm.
  }
  rewrite eq1. 
  exact ( ! eq ). 
Defined.
  


(** *** Operations qn, fn_star and f_star_of_s and fn_star_of_s  *)


(** **** Operations qn and fn_star *)

Definition qn { CC : lC0system_data } { A X : CC } ( f : mor_to A ) ( isov : isover X A ):
  mor_to X :=
  isover_ind ( fun X Y : CC => mor_to Y -> mor_to X )
             ( fun X => idfun _ )
             ( fun X gt0 => q_of_mor_to gt0 )
             ( fun X Y f g => funcomp g f )
             X A isov f. 


(* Definition qn { CC : lC0system_data } { Y A : CC } ( f : Y --> A ) ( n : nat ) 
           { X : CC } ( gtn : ll X >= n ) ( eq : ftn n X = A )  : mor_to X .
Proof.
  intros until n . 
  induction n as [ | n IHn ] .
  intros . 
  change _ with ( X = A ) in eq . 
  apply ( mor_to_constr ( f ;; id_to_mor ( ! eq ) ) ) . 

  intros .

  set ( int := ftn_ft n X : ftn n ( ft X ) = ftn ( 1 + n ) X ) .
  set ( gt0 := natgehgthtrans _ _ _ gtn ( natgthsn0 _ ) ) . 
  apply ( q_of_f gt0 ( IHn ( ft X ) ( ll_ft_gtn gtn ) ( int @ eq ) ) ) . 

Defined. *)


Definition fn_star { CC : lC0system_data } { X A : CC }
  ( f : mor_to A ) ( isov : isover X A ): CC := dom ( qn f isov ).



(** **** Properties of operations qn and fn_star *)


(* Lemma qn_equals_qn { CC : lC0system_data } ( is : isaset CC )
      { Y A : CC } ( f : Y --> A )
      { n1 n2 : nat } ( eqn : n1 = n2 ) 
      { X : CC }
      ( gtn1 : ll X >= n1 ) ( gtn2 : ll X >= n2 )
      ( eq1 : ftn n1 X = A ) ( eq2 : ftn n2 X = A ) :
  qn f n1 gtn1 eq1 = qn f n2 gtn2 eq2 .
Proof.
  intros until n2 . 
  intro eqn . 
  rewrite eqn .
  intros until gtn2 . 
  assert ( eq : gtn1 = gtn2 ) .  apply ( proofirrelevance _ ( pr2 ( _ >= _ ) ) ) . 
  rewrite eq . 
  intros eq1 eq2 . 
  assert ( eq' : eq1 = eq2 ) .
  apply is . 
  rewrite eq' . 
  apply idpath .

Defined. *)


Lemma q_XX { CC : lC0system_data } { X : CC } ( f : mor_to X ) ( isov : isover X X ):
  qn f isov = f.
Proof.
  unfold qn.
  set ( int := @isover_ind_XX CC ( fun X Y : CC => mor_to Y -> mor_to X )
                            ( fun X => idfun _ )
                            ( fun X gt0 => q_of_mor_to gt0 )
                            ( fun X Y f g => funcomp g f ) X isov ).
  apply ( maponpaths ( fun g => g f ) int ).
Defined.

Opaque q_XX.


Lemma q_isab { CC : lC0system_data } { X A : CC } ( f : mor_to A ) ( isab : isabove X A ):
  qn f isab = q_of_mor_to ( isabove_gt0 isab ) ( qn f ( isover_ft' isab ) ). 
Proof.
  set ( int := isover_ind_isab ( fun X Y : CC => mor_to Y -> mor_to X )
                            ( fun X => idfun _ )
                            ( fun X gt0 => q_of_mor_to gt0 )
                            ( fun X Y f g => funcomp g f ) X A isab ).
  apply ( maponpaths ( fun g => g f ) int ).
Defined.

Opaque q_isab.


Lemma q_X_ftX { CC : lC0system_data } { X : CC } ( f : mor_to ( ft X ) ) ( gt0 : ll X > 0 ):
  qn f ( isover_X_ftX X ) = q_of_mor_to gt0 f.
Proof.
  unfold qn. 
  apply ( maponpaths ( fun g => g f ) ).
  use isover_ind_X_ftX.
  intros X0 gt1. 
  apply idpath. 
Defined.

Opaque q_X_ftX. 



Lemma f_star_XX { CC : lC0system_data } { X : CC } ( f : mor_to X ) ( isov : isover X X ):
  fn_star f isov =  dom f.
Proof.
  apply ( maponpaths dom ).
  apply q_XX. 
Defined.

Opaque f_star_XX.


Lemma f_star_isab { CC : lC0system_data } { X A : CC } 
      ( f : mor_to A ) ( isab : isabove X A ) :
  fn_star f isab = f_star ( isabove_gt0 isab ) ( qn f ( isover_ft' isab ) ). 
Proof.
  apply ( maponpaths dom ).
  apply q_isab. 
Defined.

Opaque f_star_isab.


Lemma f_star_X_ftX { CC : lC0system_data } { X : CC } ( f : mor_to ( ft X ) ) ( gt0 : ll X > 0 ):
  fn_star f ( isover_X_ftX X ) = f_star gt0 f.
Proof.
  apply ( maponpaths dom ). 
  apply q_X_ftX.
Defined.



(* Definition qsn_strict { CC : lC0system_data } { Y A : CC } ( f : Y --> A ) ( n : nat ) 
      { X : CC } ( gtsn : ll X >= S n ) ( eq : ftn (S n) X = A )  :
  qn f ( S n ) gtsn eq =
  q_of_f (natgehgthtrans _ _ _ gtsn ( natgthsn0 _ ))
         ( qn f n ( ll_ft_gtn gtsn ) ( ( ftn_ft n X ) @ eq ) ) :=
  idpath _ .

Definition qsn_new_eq { T : ltower } { A X : T } { n m : nat }
           ( eq : ftn n X = A ) ( eqnat : n = S m ) : ftn ( S m ) X = A .
Proof .
  intros .
  apply ( ( maponpaths ( fun i => ftn i X ) ( ! eqnat ) ) @ eq ) . 

Defined.


Definition qsn_new_gtn { T : ltower } { X : T } { n m : nat }
           ( gtn : ll X >= n ) ( eqnat : n = S m ) : ll X >= S m .
Proof.
  intros.
  rewrite eqnat in gtn . apply gtn .

Defined.


Lemma qn_to_qsm { CC : lC0system } { Y A : CC } ( f : Y --> A ) { n : nat } 
      { X : CC } ( gtn : ll X >= n ) ( eq : ftn n X = A )
      { m : nat } ( eqnat : n = S m ) :
  qn f n gtn eq =
  qn f ( S m ) ( qsn_new_gtn gtn eqnat ) ( qsn_new_eq eq eqnat ) .
Proof.
  intros .
  apply qn_equals_qn .
  
  apply C0_isaset_Ob .

  apply eqnat .

Defined.



Definition fsn_strict { CC : lC0system_data } { Y A : CC } ( f : Y --> A ) ( n : nat ) 
           { X : CC } ( gtsn : ll X >= S n ) ( eq : ftn ( S n ) X = A ) :
  fn_star f ( S n ) gtsn eq =
  f_star (natgehgthtrans _ _ _ gtsn ( natgthsn0 _ ))
         ( qn f n ( ll_ft_gtn gtsn ) ( ( ftn_ft n X ) @ eq ) ) :=
  idpath _ .


Definition fn_star_to_fsm_star { CC : lC0system } { Y A : CC } ( f : Y --> A ) { n : nat } 
      { X : CC } ( gtn : ll X >= n ) ( eq : ftn n X = A )
      { m : nat } ( eqnat : n = S m ) :
  fn_star f n gtn eq =
  fn_star f ( S m ) ( qsn_new_gtn gtn eqnat ) ( qsn_new_eq eq eqnat ) :=
  maponpaths pr1 ( qn_to_qsm _ _ _ _ ) . 

*)


Lemma ll_fn_star { CC : lC0system } { A X : CC } ( f : mor_to A ) ( isov : isover X A ):
  ll ( fn_star f isov ) + ll A  = ll ( dom f ) + ll X. 
Proof.
  set ( P := fun ( X0 Y0 : CC ) ( isov0 : isover X0 Y0 ) =>
               forall ( f0 : mor_to Y0 ), ll ( fn_star f0 isov0 ) + ll Y0  = ll ( dom f0 ) + ll X0 ).
  assert ( P0 : forall X0 , P X0 X0 ( isover_XX X0 ) ).
  { intro.
    unfold P.
    intro. 
    rewrite f_star_XX.
    apply idpath.
  }
  assert ( Pft : forall X0 ( gt0 : ll X0 > 0 ), P X0 ( ft X0 ) ( isover_X_ftX X0 ) ).    
  { intros.
    unfold P.
    intro f0.
    rewrite ( f_star_X_ftX f0 gt0 ).
    rewrite ( ll_f_star gt0 f0 ). 
    rewrite ( natpluscomm 1 _ ). 
    rewrite natplusassoc. 
    apply ( maponpaths ( fun x => ll (dom f0) + x ) ).
    apply S_ll_ft. 
    apply gt0.
  }
  assert ( Pcomp : forall ( X Y : CC ),
                       ( forall isov1, P X ( ft X ) isov1 ) ->
                       ( forall isov2, P ( ft X ) Y isov2 ) ->
                       forall ( isab : isabove X Y ), P X Y isab ). 
  { intros X0 Y0 F0 G0 isab. 
    unfold P. 
    intro f0. 
    rewrite f_star_isab. 
    rewrite ll_f_star. 
    assert ( eq := G0 (isover_ft' isab) ).
    { unfold P in eq.
      change (pr1 (qn f0 (isover_ft' isab))) with ( fn_star f0 (isover_ft' isab) ). 
      rewrite natplusassoc.
      rewrite ( eq f0 ). 
      rewrite ( natpluscomm ( ll ( dom f0 ) ) ).
      rewrite <- natplusassoc.
      rewrite S_ll_ft. 
      - apply natpluscomm. 
      - apply ( isabove_gt0 isab ). 
    }
  }
  apply ( isover_strong_ind_int P P0 Pft Pcomp _ _ _ isov _ ). 
Defined.
 

Lemma isover_fn_star { CC : lC0system } { X A : CC } ( f : mor_to A ) ( isov : isover X A ):
  isover ( fn_star f isov ) ( dom f ).
Proof.
  set ( P := fun ( X0 Y0 : CC ) ( isov0 : isover X0 Y0 ) =>
               forall ( f0 : mor_to Y0 ) , isover ( fn_star f0 isov0 ) ( dom f0 ) ).
  assert ( P0 : forall X0 , P X0 X0 ( isover_XX X0 ) ).
  { intro.
    unfold P.
    intro. 
    rewrite f_star_XX.
    apply isover_XX.
  }
  assert ( Pft : forall X0 ( gt0 : ll X0 > 0 )  , P X0 ( ft X0 ) ( isover_X_ftX X0 ) ).    
  { intros.
    unfold P.
    intro f0.
    rewrite ( f_star_X_ftX f0 gt0 ).
    apply isover_f_star. 
  }  
  assert ( Pcomp : forall ( X Y : CC ),
                       ( forall isov1, P X ( ft X ) isov1 ) ->
                       ( forall isov2, P ( ft X ) Y isov2 ) ->
                       forall ( isab : isabove X Y ), P X Y isab ). 
  { intros X0 Y0 F0 G0 isab. 
    unfold P. 
    intro f0. 
    rewrite f_star_isab.
    use isover_trans.
    - apply ( dom (qn f0 (isover_ft' isab)) ). 
    - apply isover_f_star.
    - apply G0. 
  }
  apply ( isover_strong_ind_int P P0 Pft Pcomp _ _ _ isov _ ). 
Defined.




(* End of the file lC0systems.v *)
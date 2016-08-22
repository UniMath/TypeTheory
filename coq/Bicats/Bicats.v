
(**
A module for bicategories, based over UniMath’s [CategoryTheory] library.

Contents:

  - Prebicategories
    Main definition: [prebicategory] 
  - Examples
    - The prebicategory of precategories: [PRECAT]
    - Locally discrete prebicats on a precat:
      [LocallyDiscretePreBicat]
*)

Require Import UniMath.CategoryTheory.UnicodeNotations.

Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.

Require Import Systems.UnicodeNotations.
Require Import Systems.Displayed_Cats.Auxiliary.

Local Set Automatic Introduction.
(* only needed since imports globally unset it *)

(** * Prebicategories *)

Section Bicategory_definition.

(** The definition of a prebicategory is split up into four stages, each comprising 2 or 3 components.  Most of these components are themselves precategories, functors, or natural transformations.  In rough overview, the groups/components are:

- [prebicategory_obmor]
  - [ob_bicat : Type];
  - [hom1 : forall (X Y : ob_bicat), precategory];
- [prebicategory_idcomp]
  - [identity1 : forall X, hom1 X X];
  - [compose1 : forall {X Y Z}, functor (hom1 X Y × hom1 Y Z) (hom1 X Z)];
- [prebicategory_associd]
  - [assoc_bicat : ](associativity natural transformation for [compose1])
  - [id_left_bicat : ](left unitor natural transformation)
  - [id_right_bicat : ](right unitor natural transformation)
- [prebicategory_coherence_axioms]
  - [pentagon_bicat : ](pentagon axiom for [assoc_bicat])
  - [triangle_bicat : ]([id_left_bicat] and [id_right_bicat] agree on [identity1])

Within each group apart from [obmor], the components are independent.

See Jean Bénabou, _Introduction to bicategories_, 1967, <http://doi.org/10.1007/BFb0074299> (paywalled),
or Tom Leinster, _Basic Bicategories_, 1998, <http://arxiv.org/abs/math/9810017>. *)
(* TODO: change names to [ob_mor] etc. to fit with precat names? *)

Definition prebicategory_obmor : Type
  := Σ (ob : Type), (forall (X Y : ob), Precategory).

Definition ob_bicat (BB : prebicategory_obmor) := pr1 BB.
Coercion ob_bicat : prebicategory_obmor >-> Sortclass.
Definition hom1 (BB : prebicategory_obmor) := pr2 BB.
Coercion hom1 : prebicategory_obmor >-> Funclass.
Global Arguments hom1 [_] _ _.

Definition prebicategory_idcomp (BB : prebicategory_obmor) : Type
:= (forall X, BB X X)
 × (forall X Y Z, functor (BB X Y × BB Y Z) (BB X Z)).

Definition prebicategory_data1 := Σ BB0, prebicategory_idcomp BB0.

Definition prebicat_obmor (BB : prebicategory_data1) := pr1 BB.
Coercion prebicat_obmor : prebicategory_data1 >-> prebicategory_obmor.
Definition identity1 (BB : prebicategory_data1) := pr1 (pr2 BB).
Global Arguments identity1 [BB] X.
Definition compose1 (BB : prebicategory_data1) := pr2 (pr2 BB).
Global Arguments compose1 [BB X Y Z].

Definition prebicategory_associd (BB : prebicategory_data1) : Type
:= 
  (forall X Y Z W : BB, nat_trans
    (functor_composite
      (prod_functor (functor_identity _) (@compose1 _ Y Z W))
      (@compose1 _ X Y W))
    (functor_composite
      (prod_precategory_assoc _ _ _)
      (functor_composite
        (prod_functor (@compose1 _ X Y Z) (functor_identity _))
        (@compose1 _ X Z W))))
× 
  ((forall X Y : BB, nat_trans
    (functor_composite 
      (pair_functor 
        (functor_composite 
           (unit_functor _) (ob_as_functor (identity1 X)))
        (functor_identity _))
      (@compose1 _ X X Y))
    (functor_identity _))
×
  (forall X Y : BB, nat_trans
    (functor_composite 
      (pair_functor 
        (functor_identity _)
        (functor_composite 
           (unit_functor _) (ob_as_functor (identity1 Y))))
      (@compose1 _ X Y Y))
    (functor_identity _)))%type.

Definition prebicategory_data2 : Type := Σ BB1, prebicategory_associd BB1.

Definition prebicat_data1 (BB : prebicategory_data2) := pr1 BB.
Coercion prebicat_data1 : prebicategory_data2 >-> prebicategory_data1.
Definition assoc_bicat (BB : prebicategory_data2) := pr1 (pr2 BB).
Global Arguments assoc_bicat [BB X Y Z W].
Definition id_left_bicat (BB : prebicategory_data2) := pr1 (pr2 (pr2 BB)).
Global Arguments id_left_bicat [BB X Y].
Definition id_right_bicat (BB : prebicategory_data2) := pr2 (pr2 (pr2 BB)).
Global Arguments id_right_bicat [BB X Y].

(** The axioms could be specified either as equalities/iso-ness of natural transformations, or pointwise.  We choose pointwise, for two reasons: firstly, it is easier to write (not requiring so much machinery for composition of natural transformations); secondly, in the absence of function extensionality, the pointwise notion is the correct one.  *) 
Definition prebicategory_coherence_axioms (BB : prebicategory_data2) : Type
:=
  ((forall X Y Z W V (A : BB X Y) (B : BB Y Z) (C : BB Z W) (D : BB W V),
    (@functor_on_morphisms _ _ (compose1) (_,_) (_,_)
      (identity A, assoc_bicat (B , (C , D)) )
    ;; assoc_bicat (A , ( compose1 (B, C) , D))
    ;; @functor_on_morphisms _ _ (compose1) (_,_) (_,_)
      (assoc_bicat (A , (B , C)) , identity D))
  =
    assoc_bicat (A , (B , compose1 (C , D)))
    ;; assoc_bicat (compose1 (A, B), (C , D)))
×
  (forall X Y Z (A : BB X Y) (B : BB Y Z),
    (assoc_bicat (A , (identity1 Y, B)))
    ;; (@functor_on_morphisms _ _ (compose1) (_,_) (_,_)
      (id_right_bicat A , identity B))
  = 
    @functor_on_morphisms _ _ (compose1) (_,_) (_,_)
      (identity A, id_left_bicat B )))%type.

Definition prebicategory_iso_axioms (BB : prebicategory_data2) : Type
:=
  ((forall (X Y Z W : BB) FGH, is_iso (@assoc_bicat _ X Y Z W FGH))
×
  ((forall (X Y : BB) (F : BB X Y), is_iso (id_left_bicat F))
×
  (forall (X Y : BB) (F : BB X Y), is_iso (id_right_bicat F))))%type.

(** The main definition: *)
Definition prebicategory : Type :=
  Σ BB2, (prebicategory_iso_axioms BB2 × prebicategory_coherence_axioms BB2)%type.

Definition prebicat_data2 (BB : prebicategory) := pr1 BB.
Coercion prebicat_data2 : prebicategory >-> prebicategory_data2.
Definition assoc_bicat_is_iso (BB : prebicategory) := pr1 (pr1 (pr2 BB)).
Global Arguments assoc_bicat [BB X Y Z W].
Definition id_left_bicat_is_iso (BB : prebicategory) := pr1 (pr2 (pr1 (pr2 BB))).
Global Arguments id_left_bicat [BB X Y].
Definition id_right_bicat_is_iso (BB : prebicategory) := pr2 (pr2 (pr1 (pr2 BB))).
Global Arguments id_right_bicat [BB X Y].
Definition pentagon_bicat (BB : prebicategory) := pr1 (pr2 (pr2 BB)).
Global Arguments pentagon_bicat [BB X Y Z W V] A B C D.
Definition triangle_bicat (BB : prebicategory) := pr2 (pr2 (pr2 BB)).
Global Arguments triangle_bicat [BB X Y Z] A B.

End Bicategory_definition.

(** * Examples *)

(** ** The prebicategory of precategories *)
Section Precat_as_prebicat.

(** Forming the functor precategory from _C_ to _D_ requires that the hom-types of _D_ are sets.  Without this, [id_left], [id_right] and [assoc] for this precat would require extra axioms on the natural transformations, corresponding to the id and comp constraints classically taken for the 2-cells of a pseudo-natural transformation. 

To form a prebicategory, therefore, we have to restrict to precategories with hom-sets; so we used not [precategory], but [Precategory] from [Ktheory.Precategories], which comes with the hom-set property added. *)

Definition PRECAT_ob_mor : prebicategory_obmor.
Proof.
  (* ob_bicat *) exists Precategory.
  (* hom1 *) intros C D. exact (functorPrecategory C D).
Defined.

(** Note: the interaction of reduction and coercions causes a slightly irritating issue here.  (The same issue arises with other (bi-)categories of structured objects whose access functions rely on cascading coercions.)

  Given [ X : ob_bicat (PRECAT_ob_mor) ], we can’t write [ functor_identity X ]: the coercions [Precategory >-> … >-> precategory_data ] don’t trigger, since [ob_bicat (PRECAT_ob_mor)] is not of the *syntactic* form to which they apply.

  Three workarounds: annotate it as [  (X : Precategory) ], making the coercions trigger; issue [ simpl in X ] to reduce its type in the context to [ Precategory ]; or write [ pr1 X ], which again pulls [ X ] into a type on which the coercions trigger. *)

Section Comp_Functor.
  Context (C D E : Precategory).

  Definition nat_trans_horiz_comp {F F' : functor C D} {G G' : functor D E}
    (α : nat_trans F F') (β : nat_trans G G')
    : nat_trans (functor_composite F G) (functor_composite F' G').
  Proof.
    exists (fun x => functor_on_morphisms G (α x) ;; β (F' x)).
    intros x y f; simpl.
    eapply pathscomp0. apply assoc.
    eapply pathscomp0. apply cancel_postcomposition.
      eapply pathscomp0. eapply pathsinv0, functor_comp.
      apply maponpaths. apply nat_trans_ax.
    eapply pathscomp0. apply cancel_postcomposition, functor_comp.
    eapply pathscomp0. eapply pathsinv0, assoc.
    eapply pathscomp0. Focus 2. eapply assoc.
    apply maponpaths, nat_trans_ax.
  Defined.

  Definition comp_functor_data : functor_data
    (functorPrecategory C D × functorPrecategory D E)
    (functorPrecategory C E).
  Proof.
    (* ob *) exists (fun FG => functor_composite (pr1 FG) (pr2 FG)).
    (* mor *) intros FG FG' αβ. exact (nat_trans_horiz_comp (pr1 αβ) (pr2 αβ)).
  Defined.

  Definition comp_functor_is_functor : is_functor comp_functor_data.
  Proof.
    split.
    (* functor_idax *) intros FG. apply nat_trans_eq. apply homset_property.
      intros x; simpl.
      eapply pathscomp0. apply id_right. apply functor_id.
    (* functor_compax *) intros FG1 FG' FG'' αβ αβ'. 
      apply nat_trans_eq. apply homset_property. intros x; simpl.
      eapply pathscomp0. apply cancel_postcomposition, functor_comp.
      eapply pathscomp0. eapply pathsinv0, assoc.
      eapply pathscomp0. Focus 2. apply assoc. apply maponpaths.
      eapply pathscomp0. apply assoc.
      eapply pathscomp0. apply cancel_postcomposition, nat_trans_ax.
      apply pathsinv0, assoc.
    (* NB: this [functor_compax] amounts to the interchange law between horizontal and vertical composition of natural transformations. *)
  Defined.

  Definition comp_functor 
    : functor (functorPrecategory C D × functorPrecategory D E)
              (functorPrecategory C E).
  Proof.
    exists comp_functor_data. apply comp_functor_is_functor.
  Defined.

End Comp_Functor.

Definition PRECAT_data1 : prebicategory_data1.
Proof.
  exists PRECAT_ob_mor. split; intros.
  (* identity1 *) simpl. exact (functor_identity (X : Precategory)).
  (* compose1 *) apply comp_functor.
Defined.

(* NOTE: compare [functor_identity_left], [functor_identity_right], [functor_assoc].  Not sure whether it is better to work in terms of those here, or simply construct the isos directly, for a more elementary definition. For now, doing the latter. *)

Definition functor_assoc_nat_trans {X Y Z W : precategory} {HW : has_homsets W} 
  (F : functor X Y) (G : functor Y Z) (H : functor Z W)
: nat_trans (functor_composite F (functor_composite G H))
            (functor_composite (functor_composite F G) H).

Proof.
  exists (fun x => identity _).
  intros x y f; simpl. refine (id_right _ @ !(id_left _)).
Defined.

Definition functor_assoc_nat_trans_2 {X Y Z W : Precategory} 
  : nat_trans
     (@functor_composite
        ((pr1 PRECAT_data1) X Y
         × ((pr1 PRECAT_data1) Y Z × (pr1 PRECAT_data1) Z W))
        ((pr1 PRECAT_data1) X Y × (pr1 PRECAT_data1) Y W)
        ((pr1 PRECAT_data1) X W)
        (prod_functor (functor_identity ((pr1 PRECAT_data1) X Y)) compose1)
        compose1)
     (@functor_composite
        ((pr1 PRECAT_data1) X Y
         × ((pr1 PRECAT_data1) Y Z × (pr1 PRECAT_data1) Z W))
        (((pr1 PRECAT_data1) X Y × (pr1 PRECAT_data1) Y Z)
         × (pr1 PRECAT_data1) Z W) ((pr1 PRECAT_data1) X W)
        (prod_precategory_assoc ((pr1 PRECAT_data1) X Y)
           ((pr1 PRECAT_data1) Y Z) ((pr1 PRECAT_data1) Z W))
        (@functor_composite
           (((pr1 PRECAT_data1) X Y × (pr1 PRECAT_data1) Y Z)
            × (pr1 PRECAT_data1) Z W)
           ((pr1 PRECAT_data1) X Z × (pr1 PRECAT_data1) Z W)
           ((pr1 PRECAT_data1) X W)
           (prod_functor compose1 (functor_identity ((pr1 PRECAT_data1) Z W)))
           compose1)).
Proof.
  exists (fun FGH => @functor_assoc_nat_trans _ _ _ _ (homset_property W) _ _ _).
  (* Since we don’t care about the computational content of the naturality, nothing is lost by destructing here: *) 
  intros [F [G H]]; simpl. intros [F' [G' H']]; simpl. intros [α [β δ]]; simpl.
  apply nat_trans_eq. apply homset_property. intros x; simpl.
  eapply pathscomp0. apply id_right.
  eapply pathscomp0. Focus 2. eapply pathsinv0, id_left.
  eapply pathscomp0. apply assoc. apply cancel_postcomposition.
  apply pathsinv0, functor_comp.
Defined.

Definition functor_id_left_nat_trans (X Y : Precategory)
: nat_trans
     (@functor_composite ((pr1 PRECAT_data1) X Y)
        ((pr1 PRECAT_data1) X X × (pr1 PRECAT_data1) X Y)
        ((pr1 PRECAT_data1) X Y)
        (pair_functor
           (@functor_composite ((pr1 PRECAT_data1) X Y) unit_precategory
              ((pr1 PRECAT_data1) X X)
              (unit_functor ((pr1 PRECAT_data1) X Y))
              (ob_as_functor (@identity1 PRECAT_data1 X)))
           (functor_identity ((pr1 PRECAT_data1) X Y))) compose1)
     (functor_identity ((pr1 PRECAT_data1) X Y)).
Proof.
  use tpair. intros F; simpl.
    exists (fun x => identity _).
    intros x y f; simpl. exact (id_right _ @ !(id_left _)).
  intros F G α; simpl.
  apply nat_trans_eq. apply homset_property. intros x; simpl.
  eapply pathscomp0. apply id_right.
  apply cancel_postcomposition, functor_id.
Defined.

Definition functor_id_right_nat_trans (X Y : Precategory)
: nat_trans
   (@functor_composite ((pr1 PRECAT_data1) X Y)
      ((pr1 PRECAT_data1) X Y × (pr1 PRECAT_data1) Y Y)
      ((pr1 PRECAT_data1) X Y)
      (pair_functor (functor_identity ((pr1 PRECAT_data1) X Y))
         (@functor_composite ((pr1 PRECAT_data1) X Y) unit_precategory
            ((pr1 PRECAT_data1) Y Y) (unit_functor ((pr1 PRECAT_data1) X Y))
            (ob_as_functor (@identity1 PRECAT_data1 Y)))) compose1)
   (functor_identity ((pr1 PRECAT_data1) X Y)).
Proof.
    use tpair. intros F; simpl.
      exists (fun x => identity _).
      intros x y f; simpl. exact (id_right _ @ !(id_left _)).
    intros F G α; simpl.
    apply nat_trans_eq. apply homset_property. intros x; simpl.
    eapply pathscomp0. apply id_right.
    eapply pathscomp0. apply id_right.
    apply pathsinv0, id_left.
Defined.

Definition PRECAT_data2 : prebicategory_data2.
Proof.
  exists PRECAT_data1. apply dirprodpair; try apply dirprodpair.
  (* assoc_bicat *) intros X Y Z W. apply functor_assoc_nat_trans_2.
  (* id_left_bicat *) intros X Y.
    apply functor_id_left_nat_trans.
  (* id_right_bicat *) intros X Y.
    apply functor_id_right_nat_trans.
Defined.

(* NOTE: factoring out components here does *not* seem to affect performance significantly.  However, using [apply dirprodpair] instead of [split] for the coherence axioms *does* make a significant difference, as does the placement of [simpl]. *)
Definition PRECAT : prebicategory.
Proof.
  exists PRECAT_data2. split. split.
  (* assoc_bicat_is_iso *) intros X Y Z W FGH.
    apply functor_iso_if_pointwise_iso.
    intros x; simpl. apply identity_is_iso.
  split.
  (* id_left_bicat_is_iso *) intros X Y F.
    apply functor_iso_if_pointwise_iso.
    intros x; simpl. apply identity_is_iso.
  (* id_right_bicat_is_iso *) intros X Y F.
    apply functor_iso_if_pointwise_iso.
    intros x; simpl. apply identity_is_iso.
  apply dirprodpair; simpl.
  (* pentagon_bicat *) intros X Y Z W V F G H K.
    apply nat_trans_eq; simpl. apply homset_property. intros x.
    eapply pathscomp0. apply maponpaths.
      eapply pathscomp0. apply id_right. apply functor_id.
    eapply pathscomp0. apply id_right.
    eapply pathscomp0. apply id_right.
    apply cancel_postcomposition.
    eapply pathscomp0. apply maponpaths. 
      eapply pathscomp0. apply maponpaths. 
        apply functor_id.
      apply functor_id.
    apply functor_id.
  (* triangle_bicat *) intros X Y Z F G.
    apply nat_trans_eq; simpl. apply homset_property. intros x.
    apply id_left.
Defined.

End Precat_as_prebicat.

(** ** The locally discrete prebicategory on a precategory *)
Section Loc_discrete_prebicat.

Variable C : Precategory.

Definition LocallyDiscretePreBicat_ob_mor : prebicategory_obmor.
Proof.
  (* objects *) exists (ob C).
  (* morphisms *) intros x y. use discrete_precat.
    exists (x --> y); apply homset_property.
Defined.

Definition LocallyDiscretePreBicat_data1 : prebicategory_data1.
Proof.
  exists LocallyDiscretePreBicat_ob_mor. split; intros.
  - (* identity1 *) apply identity.
  - (* compose1 *)
    eapply functor_composite.
      apply prod_discrete_precat.
    apply fmap_discrete_precat.
    apply uncurry, compose.
Defined.

Definition LocallyDiscretePreBicat_data2 : prebicategory_data2.
Proof.
  exists LocallyDiscretePreBicat_data1.
  apply dirprodpair; try apply dirprodpair;
  intros; apply discrete_precat_nat_trans; simpl; unfold uncurry, id.
  - (* assoc_bicat *)
    intros [f [g h]]; simpl.
    apply assoc.
  - (* id_left_bicat *)
    intro f; simpl. apply id_left.
  - (* id_right_bicat *)
    intro f; simpl. apply id_right.
Defined.

Definition LocallyDiscretePreBicat : prebicategory.
  exists LocallyDiscretePreBicat_data2.
  split.
  - (* iso axioms *)
    repeat split; intros; apply is_pregroupoid_path_pregroupoid.
  - (* coherence axioms *) split; intros; apply setproperty.
Defined.

End Loc_discrete_prebicat. 

(** TODOs:

- consider removing [pre] from most of the component/group names (since they are components of bicats just as much as of prebicats, and _prebicategory_ is a bit of a mouthful);
- add definition of (non-pre) bicats!
- naming: [obmor] vs [ob_mor] etc? (here and elsewhere)
*)
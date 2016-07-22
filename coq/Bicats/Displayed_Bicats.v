(**
A module for “displayed bicategories”, based over UniMath’s [CategoryTheory] library.

See [Systems.Displayed_Precats] for an overview of the idea and motivation of displayed categories.  Displayed bicategories are exactly analogous.
In particular, we aim to use displayed bicategories to construct and work with the bicategories of CwF’s, etc.

*)

Require Import UniMath.CategoryTheory.UnicodeNotations.

Require Import Systems.Displayed_Cats.Core.
Require Import Systems.Bicats.Bicats.

(** * Displayed (pre)bicategories 

The definition of a displayed (pre)bicategory is organised in parallel with that of a bicategory:

- [disp_bicat_obmor]
  - [ob_disp_bicat]
  - [hom1_disp_bicat]
- [disp_bicat_idcomp]
  - [id1_disp_bicat]
  - [comp1_disp_bicat]
- [disp_bicat_associd]
  - [assoc_disp_bicat]
  - [id_left_disp_bicat]
  - [id_right_disp_bicat]
- [disp_bicat_coherence_axioms]
  - [pentagon_disp_bicat] 
  - [triangle_disp_bicat]

These groups are then tupled up cumulatively as

- [disp_bicat_data1]: [disp_bicat_obmor] + [disp_bicat_idcomp]
- [disp_bicat_data2]: adds [disp_bicat_associd]
- [disp_prebicategory]: adds [disp_bicat_axioms]
 
*)
Section Disp_Bicat_Definition.

Definition disp_bicat_obmor (C : prebicategory_obmor) : Type
  := Σ (Dob : C -> Type),
         (Π (X Y : C) (XX : Dob X) (YY : Dob Y), disp_precat (hom1 X Y)).

Definition ob_disp_bicat {C} (D : disp_bicat_obmor C) := pr1 D.
Coercion ob_disp_bicat : disp_bicat_obmor >-> Funclass.
Definition hom1_disp {C} (D : disp_bicat_obmor C) := pr2 D.
Global Arguments hom1_disp [_] _ [_ _] _ _.

Notation "XX ⇒1[ F ] YY" := (hom1_disp _ XX YY F)
  (at level 50, YY at next level) : type_scope.

Definition disp_bicat_idcomp {C : prebicategory_data1} (D : disp_bicat_obmor C) : Type
:= (forall X (XX : D X), XX ⇒1[ identity1 X ] XX).

(** composition component of a bicategory:  [× (forall X Y Z, functor (BB X Y × BB Y Z) (BB X Z)).]

To upgrade this to the displayed setting, need (a) product of displayed categories, over the product of their bases; (b) functors between displayed cats _over_ a given functor between bases.
*)

(* Remaining to be upgraded to the displayed setting:

Definition disp_bicat_data1 := Σ BB0, disp_bicat_idcomp BB0.

Definition prebicat_obmor (BB : disp_bicat_data1) := pr1 BB.
Coercion prebicat_obmor : disp_bicat_data1 >-> disp_bicat_obmor.
Definition identity1 (BB : disp_bicat_data1) := pr1 (pr2 BB).
Global Arguments identity1 [BB] X.
Definition compose1 (BB : disp_bicat_data1) := pr2 (pr2 BB).
Global Arguments compose1 [BB X Y Z].

Definition disp_bicat_associd (BB : disp_bicat_data1) : Type
:= 
  (forall X Y Z W : BB, nat_trans
    (functor_composite _ _ _
      (prod_functor (functor_identity _) (@compose1 _ Y Z W))
      (@compose1 _ X Y W))
    (functor_composite _ _ _
      (prod_precategory_assoc _ _ _)
      (functor_composite _ _ _
        (prod_functor (@compose1 _ X Y Z) (functor_identity _))
        (@compose1 _ X Z W))))
× 
  ((forall X Y : BB, nat_trans
    (functor_composite _ _ _
      (pair_functor 
        (functor_composite _ _ _
           (unit_functor _) (ob_as_functor (identity1 X)))
        (functor_identity _))
      (@compose1 _ X X Y))
    (functor_identity _))
×
  (forall X Y : BB, nat_trans
    (functor_composite _ _ _
      (pair_functor 
        (functor_identity _)
        (functor_composite _ _ _
           (unit_functor _) (ob_as_functor (identity1 Y))))
      (@compose1 _ X Y Y))
    (functor_identity _)))%type.

Definition disp_bicat_data2 : Type := Σ BB1, disp_bicat_associd BB1.

Definition prebicat_data1 (BB : disp_bicat_data2) := pr1 BB.
Coercion prebicat_data1 : disp_bicat_data2 >-> disp_bicat_data1.
Definition assoc_disp_bicat (BB : disp_bicat_data2) := pr1 (pr2 BB).
Global Arguments assoc_disp_bicat [BB X Y Z W].
Definition id_left_disp_bicat (BB : disp_bicat_data2) := pr1 (pr2 (pr2 BB)).
Global Arguments id_left_disp_bicat [BB X Y].
Definition id_right_disp_bicat (BB : disp_bicat_data2) := pr2 (pr2 (pr2 BB)).
Global Arguments id_right_disp_bicat [BB X Y].

(** The axioms could be specified either as equalities/iso-ness of natural transformations, or pointwise.  We choose pointwise, for two reasons: firstly, it is easier to write (not requiring so much machinery for composition of natural transformations); secondly, in the absence of function extensionality, the pointwise notion is the correct one.  *) 
Definition disp_bicat_coherence_axioms (BB : disp_bicat_data2) : Type
:=
  ((forall X Y Z W V (A : BB X Y) (B : BB Y Z) (C : BB Z W) (D : BB W V),
    (@functor_on_morphisms _ _ (compose1) (_,_) (_,_)
      (identity A, assoc_disp_bicat (B , (C , D)) )
    ;; assoc_disp_bicat (A , ( compose1 (B, C) , D))
    ;; @functor_on_morphisms _ _ (compose1) (_,_) (_,_)
      (assoc_disp_bicat (A , (B , C)) , identity D))
  =
    assoc_disp_bicat (A , (B , compose1 (C , D)))
    ;; assoc_disp_bicat (compose1 (A, B), (C , D)))
×
  (forall X Y Z (A : BB X Y) (B : BB Y Z),
    (assoc_disp_bicat (A , (identity1 Y, B)))
    ;; (@functor_on_morphisms _ _ (compose1) (_,_) (_,_)
      (id_right_disp_bicat A , identity B))
  = 
    @functor_on_morphisms _ _ (compose1) (_,_) (_,_)
      (identity A, id_left_disp_bicat B )))%type.

Definition disp_bicat_iso_axioms (BB : disp_bicat_data2) : Type
:=
  ((forall (X Y Z W : BB) FGH, is_iso (@assoc_disp_bicat _ X Y Z W FGH))
×
  ((forall (X Y : BB) (F : BB X Y), is_iso (id_left_disp_bicat F))
×
  (forall (X Y : BB) (F : BB X Y), is_iso (id_right_disp_bicat F))))%type.

(** The main definition: *)
Definition disp_bicat : Type :=
  Σ BB2, (disp_bicat_iso_axioms BB2 × disp_bicat_coherence_axioms BB2)%type.

Definition prebicat_data2 (BB : disp_bicat) := pr1 BB.
Coercion prebicat_data2 : disp_bicat >-> disp_bicat_data2.
Definition assoc_disp_bicat_is_iso (BB : disp_bicat) := pr1 (pr1 (pr2 BB)).
Global Arguments assoc_disp_bicat [BB X Y Z W].
Definition id_left_disp_bicat_is_iso (BB : disp_bicat) := pr1 (pr2 (pr1 (pr2 BB))).
Global Arguments id_left_disp_bicat [BB X Y].
Definition id_right_disp_bicat_is_iso (BB : disp_bicat) := pr2 (pr2 (pr1 (pr2 BB))).
Global Arguments id_right_disp_bicat [BB X Y].
Definition pentagon_disp_bicat (BB : disp_bicat) := pr1 (pr2 (pr2 BB)).
Global Arguments pentagon_disp_bicat [BB X Y Z W V] A B C D.
Definition triangle_disp_bicat (BB : disp_bicat) := pr2 (pr2 (pr2 BB)).
Global Arguments triangle_disp_bicat [BB X Y Z] A B.
*)

End Disp_Bicat_Definition.



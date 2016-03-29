
(**

 Ahrens, Lumsdaine, Voevodsky, 2015 - 2016

*)

Require Import Systems.Auxiliary.
Require Import Systems.UnicodeNotations.
Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.more_on_pullbacks.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.rezk_completion.
Require Import Systems.RelUnivStructure.
Require Import Systems.Structures.

Section fix_category.

Variable C : precategory.
Variable hsC : has_homsets C.

Let RC := Rezk_completion C hsC.
Let hsRC : has_homsets RC := pr2 (pr2 (RC)).

Local Notation "'Yo'" := (yoneda _ hsC).
Local Notation "'Yo^-1'" :=  (invweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ ))).

Local Notation "'YoR'" := (yoneda _ hsRC).
Local Notation "'YoR^-1'" :=  (invweq (weqpair _ (yoneda_fully_faithful _ hsRC _ _ ))).

Hypothesis X : relative_universe_structure _ _ Yo.

Let YoR_ff : fully_faithful YoR := yoneda_fully_faithful _ hsRC.

Definition R1 := rel_univ_struct_functor _ _ Yo X _ _ YoR YoR_ff (pr2 RC).

Lemma foo : is_category
                 (functor_precategory RC^op HSET (pr2 is_category_HSET)).
Proof.
  apply is_category_functor_category.
Defined.

Definition R2 :=  R1 foo (Rezk_eta _ _ ).

Check R2.

Definition ext :
 functor (functor_precategory C^op HSET (pr2 is_category_HSET))
              (functor_precategory RC^op HSET (pr2 is_category_HSET)).
Proof.
  simpl.
  set (T:= Rezk_op_adj_equiv C hsC HSET is_category_HSET).
  apply (equivalences.right_adjoint (pr1 T)).
Defined.
Definition R3 := R2 ext.

Check R3.


(* TODO 

Definition foo : (forall c : C, F c ≃ G c) -> iso F G 

Definition bla : (forall c : C, iso (F c) (G c)) -> iso F G


*)

Definition fi_pointwise : ∀ 
  (x : C)
  (x0 : RC^op)
  ,
   HSET ⟦ ((functor_composite Yo ext) x : functor _ _ ) x0,
   ((functor_composite (Rezk_eta C hsC) YoR) x : functor _ _ ) x0 ⟧.
Proof.
Abort.

Definition fi : nat_trans (functor_composite Yo ext)
                                  (functor_composite (Rezk_eta C hsC) YoR).
Proof.
Abort.    

End fix_category.


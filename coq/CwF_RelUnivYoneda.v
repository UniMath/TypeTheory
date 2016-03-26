
(**

 Ahrens, Lumsdaine, Voevodsky, 2015 - 2016

*)

Require Import Systems.Auxiliary.
Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.more_on_pullbacks.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import Systems.RelUnivStructure.
Require Import Systems.CwF_SplitTypeCat_Equivalence.

Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).
Local Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op").
Local Notation "a ⇒ b" := (precategory_morphisms a b)(at level 50).


Local Definition preShv C := [C^op , HSET , pr2 is_category_HSET].


Section fix_category.

Variable C : precategory.
Variable hsC : has_homsets C.

Local Notation "'Yo'" := (yoneda C hsC).
Local Notation "'Yo^-1'" :=  (invweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ ))).


(** a CwF as a relative univ structure on Yo is
    - two presheaves tU, U
    - a morphism of presheaves p : tU -> U
    - for any X : C and f : Yo X -> U
       - an object (X,f) in C
       - a dependent projection (X,f) -> X in C
       - a morphism of presheaves yo(X,f) -> tU
       - such that the square commutes and is a pb square

  The comprehension structure (third point) is a proposition,
  since [preShv C] is a category.

*)

Local Definition CwF : UU
 := relative_universe_structure C (preShv C) Yo.



(** a CwF' as below is
    - a triple (Ty, ◂, π) of object extension
    - a triple (Tm, p, Q) where
      - Tm is a presheaf,
      - p is a morphism of presheaves Tm -> Ty
      - Q is a family, for any X : C and A : Ty(X),
          Q(A) : yo(X◂A) -> Tm
    - such that squares commute and are pbs

  Parentheses are
   ( (Ty, ◂, π), ( (Tm,(p,Q)), props) )

*)

Local Definition CwF' : UU
 := Σ (X : type_structure C), families_structure _ hsC X.


(** Plan: a reasonable intermediate structure seems to be 
          one that can be obtained from [CwF'] by shuffling
          the components:
   ( (Ty, Tm, p), ( (◂ , π , Q), props ) )

     We then can show that the second component of that thing
     - is a prop and
     - is logically equivalent to the comprehension structure
       of a CwF 

    Alternatively, we can fiddle with interchanging Σ and ∀ and
    the yoneda isomorphism in two places, but maybe that's 
    more cumbersome? Those two places are quantifications in
    - Q
    - the pullback condition


*)

Definition foobar : CwF ≃ CwF'.
Abort.

End fix_category.
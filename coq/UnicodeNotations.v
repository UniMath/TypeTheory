
Require Export UniMath.CategoryTheory.precategories.
Require Export UniMath.CategoryTheory.functor_categories.
Require Export UniMath.CategoryTheory.opp_precat.


(** * (Unicode) Notation for various types and operations  *)

Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op").
Notation "a ⇒ b" := (precategory_morphisms a b)(at level 50).



Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.UnicodeNotations.


(** * (Unicode) Notation for various types and operations  *)

Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op").
(* Redeclaring in [mor_scope].  *)
Notation "# F" := (functor_on_morphisms F) (at level 3) : mor_scope.


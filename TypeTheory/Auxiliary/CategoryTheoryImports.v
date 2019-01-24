(**
  [TypeTheory.Auxiliary.CategoryTheoryImports]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(** A wrapper, re-exporting the modules from [UniMath] that we frequently use, to reduce clutter in imports. *)

Require Export UniMath.CategoryTheory.limits.pullbacks.
Require Export UniMath.Foundations.Propositions.
Require Export UniMath.CategoryTheory.Core.Categories.
Require Export UniMath.CategoryTheory.Core.Functors.
Require Export UniMath.CategoryTheory.Core.NaturalTransformations.
Require Export UniMath.CategoryTheory.Core.Univalence.
Require Export UniMath.CategoryTheory.Core.Isos.
Require Export UniMath.CategoryTheory.opp_precat.
Require Export UniMath.CategoryTheory.whiskering.
Require Export UniMath.CategoryTheory.Adjunctions.Core.
Require Export UniMath.CategoryTheory.Equivalences.Core.
Require Export UniMath.CategoryTheory.precomp_fully_faithful.
Require Export UniMath.CategoryTheory.rezk_completion.
Require Export UniMath.CategoryTheory.yoneda.
Require Export UniMath.CategoryTheory.categories.HSET.Core.

Open Scope cat.
Open Scope cat_deprecated.
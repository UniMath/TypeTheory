(**
  [TypeTheory.Auxiliary.CategoryTheoryImports]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(** A wrapper, re-exporting the modules from [UniMath] that we frequently use, to reduce clutter in imports. *)

Require Export UniMath.CategoryTheory.Limits.Pullbacks.
Require Export UniMath.Foundations.Propositions.
Require Export UniMath.CategoryTheory.Core.Prelude.
Require Export UniMath.CategoryTheory.opp_precat.
Require Export UniMath.CategoryTheory.whiskering.
Require Export UniMath.CategoryTheory.Adjunctions.Core.
Require Export UniMath.CategoryTheory.Equivalences.Core.
Require Export UniMath.CategoryTheory.precomp_fully_faithful.
(* Require Export UniMath.CategoryTheory.RezkCompletions.Construction. *)
Require Export UniMath.CategoryTheory.yoneda.
Require Export UniMath.CategoryTheory.Categories.HSET.Core.
Require Export UniMath.CategoryTheory.Categories.HSET.Univalence.
Require Export UniMath.CategoryTheory.Presheaf.
Require Export UniMath.CategoryTheory.catiso.
Require Export UniMath.CategoryTheory.ArrowCategory.
Require Export UniMath.CategoryTheory.Equivalences.CompositesAndInverses.

Export Unset Universe Checking.

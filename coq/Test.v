
(**

 Ahrens, Lumsdaine, Voevodsky, 2015 - 2016

Contents:

- Import of all the files containing important results
- Checking the types of main constructions and 
  of their assumptions

*)

Require Import Systems.Auxiliary.
Require Import Systems.UnicodeNotations.
Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.more_on_pullbacks.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.equivalences.
Require Import UniMath.CategoryTheory.precomp_fully_faithful.
Require Import UniMath.CategoryTheory.rezk_completion.
Require Import Systems.RelUnivStructure.
Require Import Systems.Structures.
Require Import Systems.RelUnivYonedaCompletion.
Require Import Systems.CwF_RelUnivYoneda.
Require Import Systems.CwF_SplitTypeCat_Equivalence.

Check Rezk_on_RelUnivYoneda.
Print Assumptions Rezk_on_RelUnivYoneda.

Check weq_RelUnivYo_CwF.
Print Assumptions Rezk_on_RelUnivYoneda.

Check weq_CwF_SplitTypeCat.
Print Assumptions weq_CwF_SplitTypeCat.


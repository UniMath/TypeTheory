(**
  [TypeTheory.ALV2.CwF_SplitTypeCat_Equiv_Comparison]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(** This file compares the two equivalences constructed between the types of term structures and _q_-morphism structures over a given object-extension structure:
- one given directly, in [CwF_SplitTypeCat_Equivalence]
- one deduced from an equivalence of categories, in [CwF_SplitTypeCat_Equiv_Cats]

Main result: [compare_term_qq_equivs].
*)




Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheory.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Defs.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Maps.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Equivalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Equivalences.
Require Import TypeTheory.ALV2.CwF_SplitTypeCat_Cats.
Require Import TypeTheory.ALV2.CwF_SplitTypeCat_Univalent_Cats.
Require Import TypeTheory.ALV2.CwF_SplitTypeCat_Equiv_Cats.


Section Auxiliary.

(* TODO: this must be in the library somewhere!  Find it!*)
Lemma eq_weq {A B} (e e' : A ≃ B)
  : pr1weq e = pr1weq e' -> e = e'.
Proof.
  apply subtypePath; intro; apply isapropisweq.
Defined.

End Auxiliary.

Section Fix_Context.

Context {C : category}.

(** * Equivalence of types of term-structures and _q_-morphism structures, constructed categorically *)
Section Equiv_of_Types_from_Cats.

Definition term_struc_to_qq_struc_equiv_types (X : obj_ext_cat C)
  : term_fun_structure C X ≃ qq_morphism_structure X.
Proof.
  use (weq_on_objects_from_adj_equiv_of_cats _ _ _ _ _ 
         (term_struc_to_qq_struc_is_equiv _)).
  - apply is_univalent_fiber, is_univalent_term_fun_structure.
  - apply is_univalent_fiber, is_univalent_qq_morphism.
Defined.

(* Print Assumptions term_struc_to_qq_struc_equiv_types. *)

End Equiv_of_Types_from_Cats.

(** ** Comparison with the non-categorically constructed equivalence. *)
Section Compare_Equivs_of_Types.

Context (X : obj_ext_cat C).
 
Theorem compare_term_qq_equivs
  : term_struc_to_qq_struc_equiv_types X = weq_term_qq X.
Proof.
  apply eq_weq, idpath.
Defined.

(* An alternative approach that doesn’t rely so much on computational behaviour, so would be more robust under refactoring, could use the following lemma: *)
Lemma qq_compat_implies_eq (Y : term_fun_structure C X) {Z Z'}
  : iscompatible_term_qq Y Z -> iscompatible_term_qq Y Z'
  -> Z = Z'.
Proof.
  intros W W'.
  use (@maponpaths _ _ pr1 (Z,,W) (Z',,W')).
  apply isapropifcontr, iscontr_compatible_split_comp_structure.
Defined.

End Compare_Equivs_of_Types.

End Fix_Context.

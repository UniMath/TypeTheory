(**
  [Articles.ALV_2018]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**

Eventual contents:

- Import the files containing results of the paper 
- Give statements/types of main results/constructions,
  in order to type-check the exported versions.

While the formalisation is work in progress, this file contains placeholder results and statements, with [Admitted.], giving a roadmap of the paper.

*)

Require Import UniMath.Foundations.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import TypeTheory.Auxiliary.Auxiliary.

Require Import TypeTheory.ALV2.CwF_SplitTypeCat_Cats.

(** * Categories of the structures under consideration *)

Definition split_typecat_structure_cat (C : category) : category.
Admitted.

Definition split_typecat'_structure_cat (C : category) : category.
Admitted.

Definition cwf_structure_cat (C : category) : category.
Admitted.

Definition cwf'_structure_cat (C : category) : category.
Admitted.

Definition compatible_qq_morphism_structure_cat {C : category}
  : disp_cat (cwf'_structure_cat C).
Admitted.

Definition compatible_term_structure_cat {C : category}
  : disp_cat (split_typecat'_structure_cat C).
Admitted.

Definition rep_map_cat (C : category) : category.
Admitted.

Definition rel_univ_structure_cat (C : category) : category.
Admitted.

Definition wk_rel_univ_structure_cat (C : category) : category.
Admitted.

(**** Below here: cannibalised from ALV_2017.v ****)
(** * Equivalence of categories between split type structures and families structures *)

(** ** Equivalence between two versions of cwf structures *)

Definition equiv_cat_cwf_cwf'_structure (C : category)
  : equivalence_of_cats (cwf_structure_cat C) (cwf'_structure_cat C).
Admitted.

(** ** Equivalence between two versions of split typecat structures *)

Definition equiv_cat_standalone_to_regrouped (C : category)
  : equivalence_of_cats
      (split_typecat_structure_cat C) (split_typecat'_structure_cat C).
Admitted.

(** ** Auxiliary equivalence between the reordered structures *)

Definition weq_cwf'_sty' (C : category)
  : equivalence_of_cats
      (cwf'_structure_cat C) (split_typecat'_structure_cat C).
Admitted.

(** ** Main construction: equivalence between split typecat structures and cwf structures *)

Definition weq_sty_cwf (C : category)
  : equivalence_of_cats
      (split_typecat_structure_cat C) (cwf_structure_cat C).
Admitted.


(** * Map from [cwf_structure C] to [rep_map C] *)
(** and proof that the map is an equivalence when [C] is univalent *)  

Definition functor_cwf_to_rep (C : category)
  : cwf_structure_cat C ⟶ rep_map_cat C. 
Admitted.

Proposition fully_faithful_cwf_to_rep (C : category)
  : fully_faithful (functor_cwf_to_rep C).
Admitted.

Definition isweq_from_cwf_to_rep {C : category} (C_univ : is_univalent C)
  : adj_equivalence_of_cats (functor_cwf_to_rep C).
Admitted.

(** * Transfer of [cwf_structure]s along weak equivalences *)

Definition transfer_cwf_weak_equivalence {C D : category} (F : C ⟶ D)
  : fully_faithful F → essentially_surjective F
    → is_univalent D → 
    cwf_structure_cat C ⟶ cwf_structure_cat D.
Admitted.
(* TODO: perhaps show functorial in F also. *)

(** * Transfer of [rep_map]s along weak equivalences *)

Definition transfer_rep_map_weak_equivalence
  {C D : category} (F : C ⟶ D) 
  : fully_faithful F → essentially_surjective F
  → equivalence_of_cats (rep_map_cat C) (rep_map_cat D).
Admitted.

(** * Equivalence between [rep_map C] and [cwf (Rezk_completion C)] *)

Definition equiv_cat_rep_map_cwf_Rezk (C : category)
  : equivalence_of_cats
      (rep_map_cat C)
      (cwf_structure_cat (Rezk_completion C)).
Admitted.







(**
  [Articles.ALV_2017]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**

Contents:

- Import of all the files containing important results
- Checking the types of main constructions and 
  of their assumptions

*)

Require Import UniMath.Foundations.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.
Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheory.

Require Import TypeTheory.ALV1.RelativeUniverses.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Defs.
Require Import TypeTheory.ALV1.RelUnivYonedaCompletion.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Maps.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Equivalence.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Cats_Standalone.
Require Import TypeTheory.ALV1.CwF_def.
Require Import TypeTheory.TypeCat.TypeCat.
Require Import TypeTheory.ALV1.TypeCat_Reassoc.
Require Import TypeTheory.ALV1.CwF_Defs_Equiv.
Require Import TypeTheory.ALV1.RepMaps.


(** * Equivalence of types between split type structures and families structures *)


(** ** Equivalence between two versions of cwf structures *)

Definition weq_cwf_cwf'_structure (C : category)
  : cwf_structure C ≃ cwf'_structure C.
Proof.
  exact (weq_cwf_cwf'_structure _ ).
Defined.

(** ** Equivalence between two versions of split typecat structures *)

Definition weq_standalone_to_regrouped (C : category)
  : split_typecat_structure C ≃ split_typecat'_structure C.
Proof.
  exact weq_standalone_to_regrouped.
Defined.

(** ** Compatible [qq] from term structure and vice versa *)

Definition compatible_qq_from_term {C : category} 
           {X : obj_ext_structure C} (Y : term_fun_structure C X)
  : compatible_qq_morphism_structure Y.
Proof.
  apply compatible_qq_from_term.
Defined.

Definition compatible_term_from_qq {C : category} 
           {X : obj_ext_structure C} (Z : qq_morphism_structure X)
  : compatible_term_structure Z.
Proof.
  apply compatible_term_from_qq.
Defined.

(** ** Auxiliary equivalence between the reordered structures *)

Definition weq_cwf'_sty' (C : category)
  : cwf'_structure C ≃ split_typecat'_structure C.
Proof.
  apply weq_cwf'_sty'.
Defined.

(** ** Main construction: equivalence between split typecat structures and cwf structures *)

Definition weq_sty_cwf (C : category)
  : split_typecat_structure C ≃ cwf_structure C.
Proof.
  eapply weqcomp. apply weq_standalone_to_regrouped.
  eapply weqcomp. eapply invweq. apply weq_cwf'_sty'.
  apply invweq, weq_cwf_cwf'_structure.
Defined.





(** * Map from [cwf_structure C] to [rep_map C] *)
(** and proof that the map is an equivalence when [C] is univalent *)  

Definition from_cwf_to_rep (C : category)
  : cwf_structure C → rep_map C. 
Proof. 
  exact (from_cwf_to_rep_map C).
Defined.

Definition isweq_from_cwf_to_rep (C : category) (Ccat: is_univalent C)
  : isweq (weq_cwf_rep_map C Ccat).
Proof.
  use isweqhomot.
  - apply (weq_cwf_rep_map _ Ccat).
  - intro. apply idpath.
  - apply weqproperty.
Defined.

(** * Transfer of [cwf_structure]s along weak equivalences *)

Definition transfer_cwf_weak_equivalence {C D : category} (F : C ⟶ D)
  : fully_faithful F → essentially_surjective F
    → is_univalent D → 
    cwf_structure C → cwf_structure D.
Proof.
  apply transfer_cwf_weak_equiv.
Defined.

(** * Transfer of [rep_map]s along weak equivalences *)

Definition transfer_rep_map_weak_equivalence {C D : category} 
           (F : C ⟶ D) 
  : fully_faithful F → essentially_surjective F → rep_map C ≃ rep_map D.
Proof.
  apply transfer_rep_map_weak_equiv.
Defined.

(** * Equivalence between [rep_map C] and [cwf (Rezk_completion C)] *)

Definition weq_rep_map_cwf_Rezk (C : category)
  : rep_map C ≃ cwf_structure (Rezk_completion C).
Proof.
  eapply weqcomp.
    apply Rezk_on_rep_map.
  apply invweq.
  use (make_weq _ (isweq_from_cwf_to_rep _ _ )).
  apply univalent_category_is_univalent.
Defined.








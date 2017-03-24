(**
  [TypeTheory.ALV1.Summary]

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

Require Import TypeTheory.ALV1.RelativeUniverses.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Defs.
Require Import TypeTheory.ALV1.RelUnivYonedaCompletion.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Equivalence.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Cats_Standalone.
Require Import TypeTheory.ALV1.CwF_def.
Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.ALV1.TypeCat_Reassoc.
Require Import TypeTheory.ALV1.CwF_Defs_Equiv.
Require Import TypeTheory.ALV1.RepMaps.

(** * Equivalence of types between split type structures and families structures *)

Definition weq_sty_cwf (C : Precategory)
  : split_type_struct C ≃ cwf_structure C.
Proof.
  eapply weqcomp. apply weq_standalone_to_regrouped.
  eapply weqcomp. eapply invweq. apply weq_cwf'_sty'.
  apply weq_cwf'_cwf_structure.
Defined.

(** * Map from [cwf_structure C] to [rep_map C] *)
(** and proof that the map is an equivalence when [C] is univalent *)  

Definition from_cwf_to_rep (C : Precategory)
  : cwf_structure C → rep_map C. 
Proof. 
  exact (from_cwf_to_rep_map C).
Defined.

Definition isweq_from_cwf_to_rep (C : Precategory) (Ccat: is_category C)
  : isweq (weq_cwf_rep_map C Ccat).
Proof.
  use isweqhomot.
  - apply (weq_cwf_rep_map _ Ccat).
  - intro. apply idpath.
  - apply weqproperty.
Defined.

(** * Transfer of [cwf_structure]s along weak equivalences *)

Definition transfer_cwf_weak_equivalence {C D : Precategory} (F : C ⟶ D)
  : fully_faithful F → essentially_surjective F
    → is_category D → 
    cwf_structure C → cwf_structure D.
Proof.
  apply transfer_cwf_weak_equiv.
Defined.

(** * Transfer of [rep_map]s along weak equivalences *)

Definition transfer_rep_map_weak_equivalence {C D : Precategory} 
           (F : C ⟶ D) 
  : fully_faithful F → essentially_surjective F → rep_map C ≃ rep_map D.
Proof.
  apply transfer_rep_map_weak_equiv.
Defined.

(** * Transfer of relative universe from Yoneda on a category to Yoneda on its Rezk completion *)
Definition Rezk_on_RelUnivYoneda
     : ∏ C : Precategory,
       relative_universe (yoneda C (homset_property C))
       → relative_universe
           (yoneda (Rezk_completion C (homset_property C))
              (homset_property (Rezk_completion C (homset_property C)))).
Proof.
  exact Rezk_on_RelUnivYoneda.
Defined.
(* Print Assumptions Rezk_on_RelUnivYoneda. *)
(**
<<
Axioms:
univalenceAxiom : univalenceStatement
isweqtoforallpathsAxiom : isweqtoforallpathsStatement
funcontrAxiom : funcontrStatement
Theory:
Type hierarchy is collapsed (logic is inconsistent)
>>
*)

(** * Equivalence between type of CwF structures on [C] and of rel univs on [Yo C] *)
Definition weq_cwf_structure_RelUnivYo
     : ∏ C : Precategory, cwf_structure C ≃ @relative_universe C _ Yo.
Proof.
  exact weq_cwf_structure_RelUnivYo.
Defined.
(* Print Assumptions weq_cwf_structure_RelUnivYo. *)
(** 
<<
Axioms:
univalenceAxiom : univalenceStatement
isweqtoforallpathsAxiom : isweqtoforallpathsStatement
funcontrAxiom : funcontrStatement
Theory:
Type hierarchy is collapsed (logic is inconsistent)
>>
*)

(** * Transfer of CwF structure from a category to its Rezk completion*)
Definition Rezk_on_cwf_structures (C : Precategory) 
           (H : CwF_def.cwf_structure C) 
  : CwF_def.cwf_structure (Rezk_completion C (homset_property _)) .
Proof.
  apply (invmap (weq_cwf_structure_RelUnivYo _)).
  apply (Rezk_on_RelUnivYoneda C).
  apply (weq_cwf_structure_RelUnivYo _).
  exact H.
Defined.
(* Print Assumptions Rezk_on_cwf_structures. *)
(** 
<<
Axioms:
univalenceAxiom : univalenceStatement
isweqtoforallpathsAxiom : isweqtoforallpathsStatement
funextcontrAxiom : funextcontrStatement
funcontrAxiom : funcontrStatement
Theory:
Type hierarchy is collapsed (logic is inconsistent)
>>
*)




(** * Equivalence of types between term structures and _q_-morphism structures *)
Definition weq_term_fun_qq_morphisms_structures
     : ∏ (C : Precategory) (X : obj_ext_structure C),
       term_fun_structure C X ≃ qq_morphism_structure X.
Proof.
  exact @weq_term_qq.
Defined.
(* Print Assumptions weq_term_fun_qq_morphisms_structures. *)
(** 
<<
Axioms:
univalenceAxiom : univalenceStatement
isweqtoforallpathsAxiom : isweqtoforallpathsStatement
funcontrAxiom : funcontrStatement
Theory:
Type hierarchy is collapsed (logic is inconsistent)
>>
*)

(** * Equivalence of categories between term structures and _q_-morphism structures, over a fixed object extension structure *)
Definition equiv_of_category_of_cwf_split_type_structures
     : ∏ (C : Precategory) (X : obj_ext_structure C),
       adj_equivalence_of_precats
         (functor_composite
            (right_adjoint
               (Auxiliary.left_adj_from_adj_equiv
                  (compat_structures_precategory C X)
                  (term_fun_precategory C X)
                  (compat_structures_pr1_functor C X) 
                  (pr1_equiv C X))) (compat_structures_pr2_functor C X)).
Proof.
  exact equiv_of_structures.
Defined.
(* Print Assumptions equiv_of_category_of_cwf_split_type_structures. *)
(** 
<<
Axioms:
isweqtoforallpathsAxiom : isweqtoforallpathsStatement
funcontrAxiom : funcontrStatement
Theory:
Type hierarchy is collapsed (logic is inconsistent)
>>
*)

(** * Equivalence of types between term structures and _q_-morphism structures, over a fixed object extension structures  *)
Definition equiv_of_types_of_cwf_split_type_structures
     : ∏ (C : Precategory) (X : obj_ext_structure C),
       term_fun_precategory C X ≃ qq_structure_precategory C X.
Proof.
  exact equiv_of_types_of_structures.
Defined.
(* Print Assumptions equiv_of_types_of_cwf_split_type_structures. *)
(** 
<<
Axioms:
univalenceAxiom : univalenceStatement
isweqtoforallpathsAxiom : isweqtoforallpathsStatement
funcontrAxiom : funcontrStatement
Theory:
Type hierarchy is collapsed (logic is inconsistent)
>>
*)
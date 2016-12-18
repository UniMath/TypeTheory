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

Require Import UniMath.Foundations.Basics.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.ALV1.RelativeUniverses.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Defs.
Require Import TypeTheory.ALV1.RelUnivYonedaCompletion.
Require Import TypeTheory.ALV1.CwF_RelUnivYoneda.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Equivalence.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Cats_Standalone.


(** * Transfer of relative universe from Yoneda on a category to Yoneda on its Rezk completion *)
Definition Rezk_on_RelUnivYoneda
     : Π C : Precategory,
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
Definition weq_RelUnivYo_cwf_structures
     : Π C : Precategory, RelUnivYo C ≃ cwf_structure C.
Proof.
  exact weq_RelUnivYo_CwF.
Defined.
(* Print Assumptions weq_RelUnivYo_cwf_structures. *)
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
           (H : cwf_structure C) 
  : cwf_structure (Rezk_completion C (homset_property _)) .
Proof.
  apply weq_RelUnivYo_CwF.
  apply (Rezk_on_RelUnivYoneda C).
  apply (invmap (weq_RelUnivYo_CwF _)).
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
     : Π (C : Precategory) (X : obj_ext_structure C),
       term_fun_structure C X ≃ qq_morphism_structure X.
Proof.
  exact @weq_CwF_SplitTypeCat.
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
     : Π (C : Precategory) (X : obj_ext_structure C),
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
     : Π (C : Precategory) (X : obj_ext_structure C),
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
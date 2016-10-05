
(**

 Ahrens, Lumsdaine, Voevodsky, 2015 - 2016

Contents:

- Import of all the files containing important results
- Checking the types of main constructions and 
  of their assumptions

*)

Require Import UniMath.Foundations.Basics.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.ALV1.RelUnivStructure.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Defs.
Require Import TypeTheory.ALV1.RelUnivYonedaCompletion.
Require Import TypeTheory.ALV1.CwF_RelUnivYoneda.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Equivalence.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Cats_Standalone.


(** * Transfer of relative universe structure from Yoneda on a category to Yoneda on its Rezk completion *)
Check Rezk_on_RelUnivYoneda.
Print Assumptions Rezk_on_RelUnivYoneda.
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

(** * Equivalence between type of CwF structures on C and of rel universe structures on Yoneda*)
Check weq_RelUnivYo_CwF.
Print Assumptions Rezk_on_RelUnivYoneda.
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
Definition Rezk_on_CwF (C : Precategory) 
           (H : cwf_structure C) 
  : cwf_structure (Rezk_completion C (homset_property _)) .
Proof.
  apply weq_RelUnivYo_CwF.
  apply (Rezk_on_RelUnivYoneda C).
  apply (invmap (weq_RelUnivYo_CwF _)).
  exact H.
Defined.
Print Assumptions Rezk_on_CwF.
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

(** * Equivalence of types between cartesian generator structures and cartesian q-morphisms structures *)
Check weq_CwF_SplitTypeCat.
Print Assumptions weq_CwF_SplitTypeCat.
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

(** * Equivalence of categories between cartesian generator structures and cartesian q-morphisms structures *)
Check equiv_of_structures.
Print Assumptions equiv_of_structures.
(** 
<<
Axioms:
isweqtoforallpathsAxiom : isweqtoforallpathsStatement
funcontrAxiom : funcontrStatement
Theory:
Type hierarchy is collapsed (logic is inconsistent)
>>
*)

(** * Equivalence of categories between cartesian generator structures and cartesian q-morphisms structures *)
Check equiv_of_types_of_structures.
Print Assumptions equiv_of_types_of_structures.
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
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



Section CwF_RC_recover.

Context {C : Precategory} (T : CwF_def.cwf_structure C).

Let RC : category := Rezk_completion C (homset_property _ ).
Let T' : CwF_def.cwf_structure RC := Rezk_on_cwf_structures C T.
Let Tm : preShv C := CwF_def.Tm _ (pr1 T).
Let Tm' : preShv RC := CwF_def.Tm _ (pr1 T').
Let Ty : preShv C := CwF_def.Ty _ (pr1 T).
Let Ty' : preShv RC := CwF_def.Ty _ (pr1 T').

Let pp : _ ⟦ Tm , Ty ⟧ := pr1 T.
Let pp' : _ ⟦ Tm' , Ty' ⟧ := pr1 T'.

Let hsRCop : has_homsets (opp_precat RC) := has_homsets_opp (homset_property _).

Let ηη : functor (preShv RC) (preShv C) :=
  pre_composition_functor _ _ _ hsRCop (has_homsets_HSET) (functor_opp (Rezk_eta C _ )).

Lemma Tm_Rezk_completion_recover : 
 (*  Tm = functor_composite (functor_opp (Rezk_eta C _ )) Tm'.*)
      Tm = ηη Tm'.
Proof.
  set (XR := Rezk_opp_weq C (homset_property C) HSET is_category_HSET).
  assert (XT := homotweqinvweq XR Tm).
  apply pathsinv0.
  apply XT.
Defined.  

Lemma Ty_Rezk_completion_recover : 
(*   Ty = functor_composite (functor_opp (Rezk_eta C _ )) Ty'. *)
   Ty = ηη Ty'.
Proof.
  set (XR := Rezk_opp_weq C (homset_property C) HSET is_category_HSET).
  assert (XT := homotweqinvweq XR Ty).
  apply pathsinv0.
  apply XT.
Defined.  


Let RCequiv : adj_equivalence_of_precats _  := Rezk_op_adj_equiv C (homset_property C) 
          HSET is_category_HSET.

Lemma has_homsets_preShv (D : precategory) : has_homsets (preShv D).
Proof.
  apply functor_category_has_homsets.
Defined.

Definition pp'_eta : 
  preShv C ⟦ ηη Tm' , ηη Ty' ⟧.
Proof.
  apply (# ηη pp').
Defined.

Definition Tm_iso : iso (ηη Tm') Tm.
Proof.
  set (XR':=  counit_pointwise_iso_from_adj_equivalence RCequiv Tm).
  apply XR'.
Defined.

Definition Ty_iso : iso (ηη Ty') Ty.
Proof.
  set (XR':=  counit_pointwise_iso_from_adj_equivalence RCequiv Ty).
  apply XR'.
Defined.



Lemma RC_morphism_of_presheaves_recover : Tm_iso ;; pp = pp'_eta ;; Ty_iso.
Proof.
  assert (XR := nat_trans_ax (counit_from_left_adjoint RCequiv) _ _ pp).
  apply pathsinv0.
  etrans.  Focus 2. apply XR.
  clear XR.
  set (TT := #(right_adjoint RCequiv) pp).
  set (TTT := #ηη TT).
  apply maponpaths_2.
  pathvia (TTT). 
  - apply maponpaths. unfold pp'. 
    unfold TT.
    unfold T'.
    apply idpath.
  - apply idpath.
Qed.

End CwF_RC_recover.



(** * Equivalence of types between term structures and _q_-morphism structures *)
Definition weq_term_fun_qq_morphisms_structures
     : ∏ (C : Precategory) (X : obj_ext_structure C),
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
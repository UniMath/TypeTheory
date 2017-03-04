(**
  [TypeTheory.ALV1.CwF_def]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**
Contents:

- definition of a representable map of presheaves

*)

Require Import UniMath.Foundations.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.
Require Import TypeTheory.ALV1.CwF_def.

Set Automatic Introduction.


(** * Definition of a representable map of presheaves

A representable map of presheaves consists of 

- a base category C;
- a morphism Tm —p—> Ty of presheaves on C;
- existence of a representation of p.

*)

Section Fix_Category.

(** ** Representations of maps of presheaves 

A *representation* of a map Tm —p—> Ty of presheaves consists of data exhibiting, for each (A : Ty Γ), the fiber of p over A as represented by some object Γ.A over Γ. *)


(** ** Natural model structure is equivalent to cwf structure when 
       underlying category is univalent *)

Variable C : Precategory.

Definition natural_model_structure : UU 
  := ∑ pp : mor_total (preShv C),
            ∏ Γ (A : Ty C pp Γ : hSet), ∥ cwf_fiber_representation C pp A ∥.

Definition from_cwf_to_natural_model 
  : cwf_structure C -> natural_model_structure.
Proof.
  intro H.
  exists (pr1 H).
  intros Γ A.
  exact (hinhpr (pr2 H Γ A)).
Defined.

Definition cwf_natural_model_weq : 
  is_category C -> cwf_structure C ≃ natural_model_structure.
Proof.
  intro H.
  apply weqfibtototal.
  intro x.
  apply weqonsecfibers. intro Γ.
  apply weqonsecfibers. intro A.
  apply truncation_weq.
  apply isaprop_cwf_fiber_representation.
  apply H.
Defined.

Lemma cwf_natural_model_weq_def (H : is_category C) (X : cwf_structure C)
      : cwf_natural_model_weq H X = from_cwf_to_natural_model X.
Proof.
  apply idpath.
Defined.


(** TODO: define a truncated version of relative universes
    and construct an equivalence between
    - representable maps of presheaves on C and
    - truncated relative universes on Yoneda(C)
*)

End Fix_Category.


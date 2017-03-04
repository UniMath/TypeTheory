(**
  [TypeTheory.ALV1.CwF_def]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**
Contents:

- definition of a representable map of presheaves as per

  Steve Awodey: Natural models of homotopy type theory,
  Mathematical Structures in Computer Science, 1--46, 2016
  https://arxiv.org/abs/1406.3219

*)

Require Import UniMath.Foundations.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.
Require Import TypeTheory.ALV1.CwF_def.
Require Import TypeTheory.ALV1.RelativeUniverses.

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

Definition mere_cwf_representation (pp : mor_total (preShv C)) : UU
  := ∏ Γ (A : Ty C pp Γ : hSet), ∥ cwf_fiber_representation C pp A ∥.

Definition rep_map : UU 
  := ∑ pp : mor_total (preShv C), mere_cwf_representation pp.


Definition from_cwf_to_rep_map
  : cwf_structure C -> rep_map.
Proof.
  intro H.
  exists (pr1 H).
  intros Γ A.
  exact (hinhpr (pr2 H Γ A)).
Defined.

Definition cwf_rep_map_weq : 
  is_category C -> cwf_structure C ≃ rep_map.
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

Lemma cwf_natural_rep_map_def (H : is_category C) (X : cwf_structure C)
      : cwf_rep_map_weq H X = from_cwf_to_rep_map X.
Proof.
  apply idpath.
Defined.

(** Equivalence between representable maps of presheaves and mere relative universes *)

Lemma weq_mere_cwf_representation_is_universe_relative (pp : mor_total (preShv C))
  : mere_cwf_representation pp ≃ is_universe_relative_to Yo pp.
Proof.
  unfold mere_cwf_representation.
  unfold is_universe_relative_to.
  apply weqonsecfibers. intro Γ.
  eapply weqcomp.
    Focus 2. eapply invweq.
    refine (weqonsecbase _ _). apply yy.
  apply weqonsecfibers. intro A.
  apply weqimplimpl.
  - apply hinhfun. apply weq_cwf_fiber_representation_fpullback.
  - apply hinhfun. apply (invmap (weq_cwf_fiber_representation_fpullback _ _ _ _ )).
  - apply propproperty.
  - apply propproperty.
Defined.

Definition weq_rep_map_mere_relative_universe_Yo
  : rep_map ≃ @mere_relative_universe C _ Yo.
Proof.
  apply weqfibtototal.
  intro pp.
  apply weq_mere_cwf_representation_is_universe_relative.
Defined.

(** TODO: define a truncated version of relative universes
    and construct an equivalence between
    - representable maps of presheaves on C and
    - truncated relative universes on Yoneda(C)
*)

End Fix_Category.


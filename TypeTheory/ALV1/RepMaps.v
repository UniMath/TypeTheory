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
Require Import TypeTheory.ALV1.RelUnivYonedaCompletion.
Require Import TypeTheory.ALV1.Transport_along_Equivs.

Set Automatic Introduction.


(** * Definition of a representable map of presheaves

A representable map of presheaves consists of 

- a base category C;
- a morphism Tm —p—> Ty of presheaves on C;
- existence of a representation of p.

*)

Section Fix_Category.

(** ** Representations of maps of presheaves 

A *representation* of a map Tm —p—> Ty of presheaves consists of data exhibiting, 
  for each (A : Ty Γ), the fiber of p over A as represented by some object Γ.A over Γ. 

*)


Variable C : Precategory.

Definition mere_cwf_representation (pp : mor_total (preShv C)) : UU
  := ∏ Γ (A : Ty pp Γ : hSet), ∥ cwf_fiber_representation pp A ∥.

(** The important fact: being representable is a proposition, by use of truncation.
    Put differently: the type of representable presheaves is a subtype
    of the type of presheaves.
    In particular, two representable maps of presheaves are equal if
    their underlying maps of presheaves are equal.
 *)

Lemma isaprop_mere_cwf_representation (pp : mor_total (preShv C))
  : isaprop (mere_cwf_representation pp).
Proof.
  do 2 (apply impred; intro).
  apply propproperty.
Qed.

Definition rep_map : UU 
  := ∑ pp : mor_total (preShv C), mere_cwf_representation pp.

(** From a [cwf_structure] on [C], we get a representable map
    of presheaves on [C], given by
    - the identity on the first component (the objects and the morphism between them)
    - a prop-truncation projection on the second component
*)

Definition from_cwf_to_rep_map
  : cwf_structure C -> rep_map.
Proof.
  use bandfmap.
  - apply idfun.
  - intros pp H.
    intros Γ A.
    exact (hinhpr (H Γ A)).
Defined.


(** The map from [cwf_structure C] to [rep_map C] is
    an equivalence if [C] is univalent.
*)

Definition weq_cwf_rep_map : 
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

(** Perhaps not obviously, the equivalence [weq_cwf_rep_map] is 
    pointwise definitionally equal to the map [from_cwf_to_rep_map] 
    defined by hand.
*)

Lemma cwf_natural_rep_map_def (H : is_category C) (X : cwf_structure C)
      : weq_cwf_rep_map H X = from_cwf_to_rep_map X.
Proof.
  apply idpath.
Defined.


(** ** Equivalence between representable maps of presheaves and mere relative universes *)

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
  - apply hinhfun. apply (invmap (weq_cwf_fiber_representation_fpullback _ _)).
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

End Fix_Category.

(** ** Equivalence between rep. maps of presheaves on [C] and on its Rezk completion
*)

Definition transfer_rep_map_weak_equiv {C D : Precategory} (F : C ⟶ D)
           (F_ff : fully_faithful F) (F_es : essentially_surjective F)
  : rep_map C ≃ rep_map D.
Proof.
  eapply weqcomp.
    apply weq_rep_map_mere_relative_universe_Yo.
  eapply weqcomp.
    apply (Transfer_of_MereRelUnivYoneda F F_ff F_es).
  apply invweq. apply weq_rep_map_mere_relative_universe_Yo.
Defined.

(** This could be made an instance of the above *)

Definition Rezk_on_rep_map (C : Precategory)
  : rep_map C ≃ rep_map (Rezk_completion C (homset_property _)).
Proof.
  eapply weqcomp.
    apply weq_rep_map_mere_relative_universe_Yo.
  eapply weqcomp.
     apply Rezk_on_RepMaps.
  apply invweq.
  apply weq_rep_map_mere_relative_universe_Yo.
Defined.


(** ** Commutativity of a diagram *)
(**
<<<
  cwf(C) ------> rep_map(C)
   |                |
   v                v
  cwf(RC) -----> rep_map(RC)
>>>
*)

Lemma cwf_repmap_diagram (C : Precategory) (X : cwf_structure C) 
  : from_cwf_to_rep_map _ (Rezk_on_cwf_structures X)
    = 
    Rezk_on_rep_map _ (from_cwf_to_rep_map _ X).
Proof.
  apply subtypeEquality.
  { intro. apply isaprop_mere_cwf_representation. }
  apply idpath.
Qed.

(* *)
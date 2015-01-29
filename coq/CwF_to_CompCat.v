
Require Import Systems.UnicodeNotations.
Require Import Systems.CompCats.
Require Import Systems.cwf.

Local Notation "a ⇒ b" := (precategory_morphisms a b)(at level 50).
  (* \=> in Agda input method *)

Local Notation "g ∘ f" := (compose f g)(at level 50).
  (* \circ or \o in Agda input method *)

Local Notation "Γ ; a" := (comp_obj _ Γ a) (at level 45, left associativity).


Section CompPreCat_of_PreCwF.

Context (C : pre_cwf).

Definition comp_precat1_of_precwf : comp_precat1.
Proof.
  exists C.
  unfold comp_precat_structure1.
  exists (type C).
  exists (comp_obj C).  
  exact (fun Γ a Γ' f => @rtype C Γ Γ' a f).
Defined.

Definition q_precwf Γ (a : type C Γ) Γ' (f : Γ' ⇒ Γ)
  : (comp_obj _ Γ' (rtype a f)) ⇒ (comp_obj _ Γ a).
Proof.
  apply (pairing C Γ a (comp_obj _ Γ' (rtype a f)) (f ∘ proj_mor _ Γ' _)).
  refine (transportb (term C (Γ' ; (a [f])) ) (reindx_type_comp C _ _ a) _).
  apply gen_elem.
Defined.
 
Definition comp_precat_of_precwf : comp_precat.
Proof.
  exists comp_precat1_of_precwf.
  unfold comp_precat_structure2.
  exists (proj_mor C).
  exists q_precwf.
Abort.

End CompPreCat_of_PreCwF.

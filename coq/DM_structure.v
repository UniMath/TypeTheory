
(** * (Pre)categories with families *)
(**
  Contents:

    - Definition of a precategory with families

  The definition is based on Pitts, *Nominal Presentations of the Cubical Sets
  Model of Type Theory*, Def. 3.1: 
  http://www.cl.cam.ac.uk/~amp12/papers/nompcs/nompcs.pdf (page=9)
*)

Require Export Systems.Auxiliary.
Require Export Systems.UnicodeNotations.
Require Export UniMath.Foundations.hlevel2.hSet.
Require Export UniMath.RezkCompletion.precategories.
Require Export UniMath.RezkCompletion.limits.pullbacks.

Module Record_Preview.

Reserved Notation "C ⟨ Γ ⟩" (at level 60).
Reserved Notation "C ⟨ Γ ⊢ A ⟩" (at level 60).
Reserved Notation "A [ γ ]" (at level 40).
Reserved Notation "a ⟦ γ ⟧" (at level 40).
Reserved Notation "Γ ∙ A" (at level 20).
Reserved Notation "'π' A" (at level 20).
Reserved Notation "'ν' A" (at level 15).
Reserved Notation "γ ♯ a" (at level 25).

(* TODO *)

End Record_Preview.


Definition dm_sub_struct (CC : precategory)
  : UU
  := ∀ {Γ Γ' : CC} , Γ ⇒ Γ' → UU.

Definition DM_type {C : precategory} (H : dm_sub_struct C) {Γ Γ'} (γ : Γ ⇒ Γ')
           := H Γ Γ' γ.

Definition DM {C : precategory}(H : dm_sub_struct C) (Γ Γ' : C) : UU :=
  Σ f : Γ ⇒ Γ', DM_type H f.

Coercion arrow_from_DM {C : precategory} (H : dm_sub_struct C)(Γ Γ' : C) (δ : DM H Γ Γ') : Γ ⇒ Γ' := pr1 δ.

Definition dm_sub_closed_under_iso {CC : precategory} (DM : dm_sub_struct CC)
  : UU
  := ∀ Γ Γ' (γ : Γ ⇒ Γ'), DM _ _ γ →
                          ∀ Δ Δ' (δ : Δ ⇒ Δ'),
                            ∀ (f : iso Γ Δ) (g : iso Γ' Δ'), γ ;; g = f ;; δ → DM _ _ δ.


(*

  __________Γ
 |          |
 |          | γ ∈ DM
 |__________|
 Δ    f     Γ'

*)

Definition pb_of_DM_struct {CC : precategory} (H : dm_sub_struct CC)
: UU
  := ∀ Γ Γ' (γ : DM H Γ Γ'), ∀ Δ (f : Δ ⇒ Γ'),
     Σ (pb : CC)
       (f' : pb ⇒ Γ)
       (γ' : pb ⇒ Δ)
       (sqr_comm : f' ;; γ = γ' ;; f),
  isPullback _ γ f f' γ' sqr_comm.

Definition dm_sub_pb (CC : precategory) : UU :=
  Σ DM : dm_sub_struct CC, pb_of_DM_struct DM.

Coercion dm_sub_of_dm_sub_pb {CC : precategory} (C : dm_sub_pb CC) : dm_sub_struct CC := pr1 C.
Coercion pb_of_dm_sub_pb {CC : precategory} (C : dm_sub_pb CC) : pb_of_DM_struct C := pr2 C.


Definition pb_ob_of_DM {CC : precategory} {C : dm_sub_pb CC}
           {Γ Γ'} (γ : DM C Γ Γ') {Δ} (f : Δ ⇒ Γ')
: CC
  := pr1 (pr2 C _ _ γ _  f).

Notation "γ ⋆ f" := (pb_ob_of_DM γ f) (at level 45).
(* written "\st" in Agda input mode *)
                        
Definition pb_mor_or_DM {CC : precategory} {C : dm_sub_pb CC}
           {Γ Γ'} (γ : DM C Γ Γ') {Δ} (f : Δ ⇒ Γ')
: γ ⋆ f ⇒ Δ
:= pr1 (pr2 (pr2 (pr2 C _ _ γ _ f))).


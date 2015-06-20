
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
  := ∀ {Δ Γ : CC} , Δ ⇒ Γ → UU.

Definition DM_type {C : precategory} (H : dm_sub_struct C) {Δ Γ} (γ : Δ ⇒ Γ)
           := H Δ Γ γ.

Definition DM {C : precategory}(H : dm_sub_struct C) (Δ Γ : C) : UU :=
  Σ f : Δ ⇒ Γ, DM_type H f.

Coercion arrow_from_DM {C : precategory} (H : dm_sub_struct C)(Δ Γ : C) (δ : DM H Δ Γ) : Δ ⇒ Γ := pr1 δ.

Definition dm_sub_closed_under_iso {CC : precategory} (C : dm_sub_struct CC)
  : UU
  := ∀ Δ Γ (γ : DM C Δ Γ),
                          ∀ Δ' (δ : Δ' ⇒ Γ), 
                          ∀ (h : iso Δ Δ'), h ;; δ = γ → DM_type C δ.


(*

  __________Γ
 |          |
 |          | γ ∈ DM
 |__________|
 Δ    f     Γ'

*)

Definition pb_of_DM_struct {CC : precategory} (H : dm_sub_struct CC)
: UU
  := ∀ Δ Γ (γ : DM H Δ Γ), ∀ Γ' (f : Γ' ⇒ Γ),
     Σ (pb : CC)
       (γ' : pb ⇒ Γ')
       (f' : pb ⇒ Δ)
       (sqr_comm : f' ;; γ  = γ' ;; f),
  isPullback _ γ f f' γ' sqr_comm.

Definition dm_sub_pb (CC : precategory) : UU :=
  Σ DM : dm_sub_struct CC, pb_of_DM_struct DM.

Coercion dm_sub_of_dm_sub_pb {CC : precategory} (C : dm_sub_pb CC) : dm_sub_struct CC := pr1 C.
Coercion pb_of_dm_sub_pb {CC : precategory} (C : dm_sub_pb CC) : pb_of_DM_struct C := pr2 C.


Definition pb_ob_of_DM {CC : precategory} {C : dm_sub_pb CC}
           {Δ Γ} (γ : DM C Δ Γ) {Γ'} (f : Γ' ⇒ Γ)
: CC
  := pr1 (pr2 C _ _ γ _  f).

Notation "γ ⋆ f" := (pb_ob_of_DM γ f) (at level 45, format "γ ⋆ f").
(* written "\st" in Agda input mode *)
                        
Definition pb_mor_of_DM {CC : precategory} {C : dm_sub_pb CC}
           {Δ Γ} (γ : DM C Δ Γ) {Γ'} (f : Γ' ⇒ Γ)
: γ⋆f ⇒ Γ'
:= pr1 (pr2 (pr2 C _ _ γ _ f)).

Definition pb_mor_of_mor {CC : precategory} {C : dm_sub_pb CC}
           {Δ Γ} (γ : DM C Δ Γ) {Γ'} (f : Γ' ⇒ Γ)
: γ⋆f ⇒ Δ
  := pr1 (pr2 (pr2 (pr2 C _ _ γ _ f))).

Definition sqr_comm_of_dm_sub_pb {CC : precategory} {C : dm_sub_pb CC}
           {Δ Γ} (γ : DM C Δ Γ) {Γ'} (f : Γ' ⇒ Γ)
: _ ;; _ = _ ;; _
:= pr1 (pr2 (pr2 (pr2 (pr2 C _ _ γ _ f )))).

Definition isPullback_of_dm_sub_pb {CC : precategory} {C : dm_sub_pb CC}
           {Δ Γ} (γ : DM C Δ Γ) {Γ'} (f : Γ' ⇒ Γ)
: isPullback _ _ _ _ _ _
:= pr2 (pr2 (pr2 (pr2 (pr2 C _ _ γ _ f )))).


Definition dm_closed_under_pb {CC : precategory} (C : dm_sub_pb CC)
: UU
    := ∀ Δ Γ (γ : DM C Δ Γ) Γ' (f : Γ' ⇒ Γ), DM_type C (pb_mor_of_DM γ f).


Definition DM_structure (CC : precategory) : UU
  := Σ C : dm_sub_pb CC,
           dm_closed_under_pb C
        ×  dm_sub_closed_under_iso C
        ×  ∀ Γ Γ' (γ : Γ ⇒ Γ'), isaprop (DM_type C γ).

Coercion dm_sub_pb_from_DM_structure CC (C : DM_structure CC) : dm_sub_pb CC := pr1 C.

Definition pb_DM_of_DM {CC} {C : DM_structure CC}  {Δ Γ} (γ : DM C Δ Γ) {Γ'} (f : Γ' ⇒ Γ)
: DM C (γ⋆f) Γ'.
Proof.
  exists (pb_mor_of_DM γ f).
  apply (pr1 (pr2 C)).
Defined.

Definition pb_arrow_of_arrow {CC} {C : DM_structure CC}  {Δ Γ} (γ : DM C Δ Γ) {Γ'} (f : Γ' ⇒ Γ)
: γ⋆f ⇒ Δ.
Proof.
  apply pb_mor_of_mor.
Defined.

Definition sqr_comm_of_DM {CC} {C : DM_structure CC}  {Δ Γ} (γ : DM C Δ Γ) {Γ'} (f : Γ' ⇒ Γ)
:  pb_arrow_of_arrow _ _  ;; γ = pb_DM_of_DM γ f  ;; f.
Proof. 
  apply sqr_comm_of_dm_sub_pb.
Defined.

Definition isPullback_of_DM {CC} {C : DM_structure CC} {Δ Γ} (γ : DM C Δ Γ) {Γ'} (f : Γ' ⇒ Γ)
: isPullback CC _ _ _ _ (sqr_comm_of_DM γ f).
Proof.
  apply isPullback_of_dm_sub_pb.
Defined.

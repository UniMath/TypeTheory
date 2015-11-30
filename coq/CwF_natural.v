
(**

 Ahrens, Lumsdaine, Voevodsky, 2015

  Contents:

    - Definition of a precategory with families
    - Proof that reindexing forms a pullback

  The definition is based on Pitts, *Nominal Presentations of the Cubical Sets
  Model of Type Theory*, Def. 3.1: 
  http://www.cl.cam.ac.uk/~amp12/papers/nompcs/nompcs.pdf (page=9)
*)

Require Export Systems.Auxiliary.
Require Export Systems.UnicodeNotations.
Require Export UniMath.Foundations.Sets.
Require Export UniMath.CategoryTheory.functor_categories.
Require Export UniMath.CategoryTheory.category_hset.
Require Export UniMath.CategoryTheory.opp_precat.
Require Export UniMath.CategoryTheory.yoneda.
Require Export UniMath.CategoryTheory.UnicodeNotations.
Require Export UniMath.CategoryTheory.limits.pullbacks.


Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op").


(** * A "preview" of the definition *)

Module Preview.

(*
Reserved Notation "C ⟨ Γ ⟩" (at level 60).
Reserved Notation "C ⟨ Γ ⊢ A ⟩" (at level 60).
Reserved Notation "A [ γ ]" (at level 40).
Reserved Notation "a ⟦ γ ⟧" (at level 40).
Reserved Notation "Γ ∙ A" (at level 20).
Reserved Notation "'π' A" (at level 20).
Reserved Notation "'ν' A" (at level 15).
Reserved Notation "γ ♯ a" (at level 25).
*)

Variable C : precategory.
Variable hs : has_homsets C.
Variable Ty : functor C^op HSET.
Variable Tm : functor C^op HSET. (* needs to be written as ob in a precat *)
Variable p : nat_trans Tm Ty. (* needs to be written as mor in a precat *)

Variable comp : forall (Γ : C) (A : pr1hSet (Ty Γ)), C.
Variable pi : forall (Γ : C) (A : pr1hSet (Ty Γ)), comp Γ A ⇒ Γ.
Variable q : forall (Γ : C) (A : pr1hSet (Ty Γ)), pr1hSet (Tm (comp Γ A)).

Definition yoTy (Γ : C) : pr1hSet (Ty Γ) ≃ nat_trans (yoneda_objects C hs Γ) Ty.
Proof.
  apply invweq.
  apply yoneda_weq.
Defined.

Definition yoTm (Γ : C) : pr1hSet (Tm Γ) ≃ nat_trans (yoneda_objects C hs Γ) Tm.
Proof.
  apply invweq.
  apply yoneda_weq.
Defined.

Variable comp_comm : forall Γ (A : pr1hSet (Ty Γ)),
    nat_trans_comp _ _ _ (yoTm _ (q Γ A)) p =
    nat_trans_comp _ _ _ (yoneda_morphisms _ _ _ _ (pi Γ A)) (yoTy _ A).

End Preview.
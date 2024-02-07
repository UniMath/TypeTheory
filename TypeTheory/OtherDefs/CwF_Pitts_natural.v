
(**

 Ahrens, Lumsdaine, Voevodsky, 2015

  Contents:

    - Definition of a precategory with families
    - Proof that reindexing forms a pullback

  The definition is based on Pitts, *Nominal Presentations of the Cubical Sets
  Model of Type Theory*, Def. 3.1:
  http://www.cl.cam.ac.uk/~amp12/papers/nompcs/nompcs.pdf (page=9)
*)

Require Import UniMath.Foundations.All.

Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheory.
Require Import TypeTheory.Auxiliary.SetsAndPresheaves.

Local Open Scope precat.

(** * A "preview" of the definition *)

Module Preview.

Variable C : category.
Variable Ty Tm: [C^op, HSET]. (* functor C^op HSET. *)
Variable p : _ ⟦Tm, Ty⟧. (* needs to be written as mor in a precat *)

Variable comp : forall (Γ : C) (A : Ty $p Γ), C.
Variable pi : forall (Γ : C) (A : Ty $p Γ), comp Γ A --> Γ.
Variable q : forall (Γ : C) (A : Ty $p Γ), Tm $p (comp Γ A).

Definition yoTy (Γ : C)
  : Ty $p Γ ≃ _ ⟦(yoneda C Γ) , Ty ⟧.
Proof.
  apply invweq.
  apply yoneda_weq.
Defined.

Definition yoTm (Γ : C)
  : Tm $p Γ ≃ _ ⟦yoneda C Γ, Tm⟧.
Proof.
  apply invweq.
  apply yoneda_weq.
Defined.

Variable comp_comm :
  forall Γ (A : Ty $p Γ),
    yoTm _ (q Γ A) ;; p =
    #(yoneda _ ) (pi Γ A) ;; yoTy _ A.

Variable ispullback_comp_comm :
  forall Γ (A : Ty $p Γ),
    isPullback (comp_comm Γ A).

End Preview.

Section definition.

Variable C : category.

Definition tt_structure : UU :=
  ∑ TyTm : [C^op, HSET] × [C^op, HSET],
           _ ⟦pr2 TyTm, pr1 TyTm⟧.

Definition Ty (X : tt_structure) : [C^op, HSET] := pr1 (pr1 X).
Definition Tm (X : tt_structure) : [C^op, HSET] := pr2 (pr1 X).
Definition p (X : tt_structure) :  _ ⟦Tm X, Ty X⟧ := pr2 X.

Definition comp_structure (X : tt_structure) : UU :=
  forall Γ (A : Ty X $p Γ),
    ∑ (comp : C) (pi : _ ⟦comp, Γ⟧),
         Tm X $p comp.

Definition comp {X : tt_structure} (Y : comp_structure X) :
  forall (Γ : C) (A : Ty X $p Γ), C
  := fun Γ A => pr1 (Y Γ A).

Definition pi {X : tt_structure} (Y : comp_structure X) :
  forall (Γ : C) (A : Ty X $p Γ), comp _ Γ A --> Γ
  := fun Γ A => pr1 (pr2 (Y Γ A)).

Definition q {X : tt_structure} (Y : comp_structure X) :
  forall (Γ : C) (A : Ty X $p Γ), Tm X $p (comp Y Γ A)
  := fun Γ A => pr2 (pr2 (Y Γ A)).

Definition pullback_structure {X : tt_structure} (Y : comp_structure X) : UU
  := forall Γ (A : Ty X $p Γ),
       ∑ H :
          invmap (yoneda_weq C _ (Tm X)) (q Y Γ A) ;; p X
          =
          #(yoneda _ ) (pi Y Γ A) ;; invmap (yoneda_weq _ _ (Ty X)) A ,
         isPullback(C:=[(C^op), SET]) H.

Definition comp_comm {X : tt_structure } {Y : comp_structure X} (Z : pullback_structure Y)
  : forall Γ (A : Ty X $p Γ),
      invmap (yoneda_weq _ _ (Tm X)) (q Y Γ A) ;; p X
          =
          #(yoneda _ ) (pi Y Γ A) ;; invmap (yoneda_weq _ _ (Ty X)) A
  := fun Γ A => pr1 (Z Γ A).

Definition is_Pullback_comp {X : tt_structure } {Y : comp_structure X} (Z : pullback_structure Y)
  : forall Γ (A : Ty X $p Γ),
      isPullback(C:=[(C^op), SET]) (comp_comm Z _ _ )
  := fun Γ A => pr2 (Z Γ A).

Definition is_natural_CwF : UU
  := ∑ (X : tt_structure) (Y : comp_structure X), pullback_structure Y.

Coercion tt_structure_from_is_natural_CwF (X : is_natural_CwF) : tt_structure := pr1 X.
Coercion comp_structure_from_is_natural_CwF (X : is_natural_CwF) :
  comp_structure (tt_structure_from_is_natural_CwF X) := pr1 (pr2 X).
Coercion pullback_structure_from_is_natural_CwF (X : is_natural_CwF) :
  pullback_structure (comp_structure_from_is_natural_CwF X) := pr2 (pr2 X).


End definition.

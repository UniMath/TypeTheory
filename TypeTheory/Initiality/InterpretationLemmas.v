(** Further lemmas on the interpretation function, separated here in order to keep [TypeTheory.Initiality.Interpretation] itself reasonably streamlined *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.All.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.Partial.
Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.Initiality.SplitTypeCat_General.
Require Import TypeTheory.Initiality.SplitTypeCat_Structure.
Require Import TypeTheory.Initiality.SplitTypeCat_Maps.
Require Import TypeTheory.Initiality.Syntax.
Require Import TypeTheory.Initiality.Typing.
Require Import TypeTheory.Initiality.Interpretation.

Section Functoriality.
(** Key property of the interpretation: if [F : C --> D] is a map of split type-cats with logical structure, and some expression [e] is interpretable in [C] in some environment [E] with value [a], then [e] is also interpretable in [D] in environment [F E], with value [F a]. *)

  Context {C} {U : universe_struct C} {Π : pi_struct C}
          {C'} {U' : universe_struct C'} {Π' : pi_struct C'}
          (F : typecat_mor C C'). (* NOTE: [F] will need to preserve the structure as well *)

  Definition fmap_tm
      {Γ:C} {A : C Γ} (a : tm A)
    : tm ((typecat_mor_Ty _ _ F : nat_trans _ _) _ A).
  Proof.
    admit.
  Admitted.

  Definition fmap_type_with_term {Γ:C} (Aa : type_with_term Γ)
    : type_with_term (F Γ).
  Proof.
    exists ((typecat_mor_Ty _ _ F : nat_trans _ _) _ (type_of Aa)).
    (* TODO: make [typecat_mor_Ty] more usable! *)
    exact (fmap_tm Aa).
  Defined.

  Definition fmap_environment {Γ:C} {n:nat} (E : environment Γ n)
    : environment (F Γ) n.
  Proof.
    intros i. exact (fmap_type_with_term (E i)). 
  Defined.

  Fixpoint
    fmap_partial_interpretation_ty
      {Γ:C} {n:nat} (E : environment Γ n) (e : ty_expr n)
    : leq_partial
        (fmap_partial (fun A => (typecat_mor_Ty _ _ F : nat_trans _ _) _ A)
           (partial_interpretation_ty U Π E e))
        (partial_interpretation_ty U' Π' (fmap_environment E) e)
  with
    fmap_partial_interpretation_tm
      {Γ:C} {n:nat} (E : environment Γ n) (A : C Γ) (e : tm_expr n)
    : leq_partial
        (fmap_partial (fun a => fmap_tm a)
           (partial_interpretation_tm U Π E A e))
        (partial_interpretation_tm U' Π' (fmap_environment E)
                                   ((typecat_mor_Ty _ _ F : nat_trans _ _) _ A)
                                   e).
  Proof.
    (* TODO: should be a direct induction over syntax, analogous to earlier ones like [partial_interpretation_rename_ty], […tm]. *)
  Admitted.

End Functoriality.
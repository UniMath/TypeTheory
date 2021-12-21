(** This file defines further logical structure on split type-categories,
not yet integrated into the type theory of [Initiality.Syntax] and the statement/proof of initiality. *)

Require Import UniMath.MoreFoundations.All.

Require Import TypeTheory.Auxiliary.CategoryTheoryImports.
Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.Initiality.SplitTypeCat_General.
Require Import TypeTheory.Initiality.SplitTypeCat_Structure.

Section Pi_eta_structure.

  Context (C : split_typecat) (Π : pi_struct C).

  Definition Pi_eta : UU.
  Proof.
    refine (forall (Γ : C) (A : C Γ) (B : C (Γ ◂ A)) (p : tm (Π _ A B)),
               p = _).
    (* now we have to construct the eta-expansion of [p],
     which in object-theory pseudocode is [lam x (app p x)] *)
    refine (pi_intro _ _ _ _ _). (* [pi_intro] is lambda-abstraction *)
    Fail refine (pi_app _ _ _ _ _ _).
    (* fails, but informatively:
       [pi_app] gives a term in a reindexing of B, not B itself.
    So we need to add a a [transportf].
    (In the object theory, the type-coercion rule). *)
    simple refine (transportf _ _ (pi_app Π _ _ _ _ _)).
    (* In the object theory, the application we want is [ app p x ].
    But note that this [p] is weakened from [Γ] to [Γ ◂ A],
    so we need to give that weakening explicitly,
    i.e. reindexing [p] along the rependent projection from [Γ ◂ A]. *)
    4: {
      Fail refine (reind_tm (dpr_typecat A) p).
    (* informative again: the reindexed pi-type is not definitionally a pi-type *)
      refine (transportf _ _ (reind_tm (dpr_typecat A) p)).
      apply pi_form_struct_natural.
    }
    (* now supply the argument: the “new variable” / generic term *)
    2: { apply var_typecat. }
    (* now some algebra to justify this type-reindexing equality *)
    eapply pathscomp0. { apply pathsinv0, reind_comp_typecat. }
    eapply pathscomp0. 2: { apply reind_id_typecat. }
    apply maponpaths. 
    (* look at the definition of the generic term, as a map into a pullback *)
    unfold var_typecat. apply Auxiliary.Pb_map_commutes_2.
  Defined.

End Pi_eta_structure.

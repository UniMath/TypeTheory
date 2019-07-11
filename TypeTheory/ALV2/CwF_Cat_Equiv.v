(**
  [TypeTheory.ALV1.CwF_Cats]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**
Contents:

- 
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.CwF_def.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Defs.
Require Import TypeTheory.ALV1.CwF_Defs_Equiv.

Require Import TypeTheory.ALV2.CwF_Cats.
Require Import TypeTheory.ALV2.CwF_SplitTypeCat_Cats.
Require Import UniMath.CategoryTheory.catiso.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Equivalences.


Set Automatic Introduction.

Section CwF_Cat_Equiv.

  Context (C : category).

  Definition cwf_to_cwf'_structure
    : cwf_structure C → cwf'_structure C
    := weq_cwf_cwf'_structure C.

  Definition cwf'_structure_mor (X Y : cwf'_structure C) : UU
    := ∑ (ext : obj_ext_mor (pr1 X) (pr1 Y)),
       term_fun_mor X Y ext.

  Local Notation "Γ ◂ A" := (comp_ext _ Γ A) (at level 30).

  (*
  Definition obj_ext_mor_data (X X' : obj_ext_structure C)
    := ∑ F_TY : pr1 X --> pr1 X',
        ∏ {Γ:C} {A : (pr1 X : functor _ _) Γ : hSet},
        Γ ◂ A --> Γ ◂ ((F_TY : nat_trans _ _) _ A).

  Definition cwf'_structure_mor_data (X Y : cwf'_structure C) : UU
    := obj_ext_mor_data (pr1 X) (pr1 Y)
        ×
       (pr112 X --> pr112 Y).
*)
  

  (*
  TODO: try define an equivalence of
            cwf_structure_mor and cwf'_structure_mor
        similarly to how weq_cwf_cwf'_structure is defined
  *)

  (* FIXME: fix this definition, remove corresponsing axiom *)
  Definition weq_cwf_cwf'_structure_mor_ty_STUCK
             (X Y : cwf_structure C)
  : (∑ (x : cwf_structure_mor_ty_data X Y),
    cwf_structure_mor_weakening_axiom X Y x)
      ≃ obj_ext_mor (pr1 (cwf_to_cwf'_structure X))
                    (pr1 (cwf_to_cwf'_structure Y)).
  Proof.
    unfold obj_ext_mor, cwf_structure_mor_ty_data.
    refine (_ ∘ weqtotal2asstor _ _)%weq.
    apply weqfibtototal. intros F_TY.

    (* === STUCK HERE ===

       tried to apply

       - sec_total2_distributivity to LHS
       - weqsecovertotal2 to RHS

       - weqtotaltoforall to LHS
       - weqforalltototal to RHS
       
       however, both approaches fail (see most successful attempt below)
     *)

   (* almost there: *)

    eapply weqcomp.
    unfold cwf_structure_mor_weakening_axiom. cbn. (* NOTE: here cbn does not hang! *)
    apply invweq.
    set (T := @sec_total2_distributivity
                _ 
                (fun Γ : C => ∏ (A : (TY X : functor _ _ ) Γ : hSet),
                              C ⟦ cwf_extended_context X Γ A, cwf_extended_context Y Γ ((F_TY : nat_trans _ _ ) Γ  A) ⟧)).
    cbn in T.
    
    transparent assert (CC : (∏ a : C,
                                    (∏ A : (TY X : functor _ _ ) a : hSet, C ⟦ cwf_extended_context X a A, cwf_extended_context Y a ((F_TY : nat_trans _ _ ) a A) ⟧) → UU)).
    {
      intro Gamma'. intro phi'.
      cbn in phi'.
      exact (∏ (A : (TY X : functor _ _ ) Gamma' : hSet), phi' A;; cwf_projection Y Gamma' ((F_TY : nat_trans _ _ ) Gamma' A) = cwf_projection X Gamma' A).
      
    }
    
    set (T' := T CC).
    apply T'.
  Abort.

  (* FIXME: create a definition instead of this axiom *)
  Axiom weq_cwf_cwf'_structure_mor_ty
    : ∏ (X Y : cwf_structure C),
      (∑ (x : cwf_structure_mor_ty_data X Y),
    cwf_structure_mor_weakening_axiom X Y x)
      ≃ obj_ext_mor (pr1 (cwf_to_cwf'_structure X))
                    (pr1 (cwf_to_cwf'_structure Y)).
  
  (* FIXME: create a definition instead of this axiom *)
  Axiom weq_cwf_cwf'_structure_mor_weakening_axiom
    : ∏ (X Y : cwf_structure C)
        (F_TM : PreShv C ⟦ TM X, TM Y ⟧)
        (x : ∑ (x' : cwf_structure_mor_ty_data X Y),
             cwf_structure_mor_weakening_axiom X Y x'),
      (F_TM ;; pr1 Y = pr1 X ;; pr1 (pr1 x))
        ≃ (F_TM ;; pp (cwf_to_cwf'_structure Y) = pp (cwf_to_cwf'_structure X) ;; obj_ext_mor_TY ((weq_cwf_cwf'_structure_mor_ty X Y) x)).

  (* NOTE: definition of this Axiom HANGS!!! *)
  (*
  Axiom weq_cwf_cwf'_structure_mor_term_axiom
    : ∏ (X Y : cwf_structure C)
        (F_TM : PreShv C ⟦ TM X, TM Y ⟧)
        (x : ∑ (x' : cwf_structure_mor_ty_data X Y),
             cwf_structure_mor_weakening_axiom X Y x'),
  cwf_structure_mor_term_axiom X Y (F_TM,, pr1 x)
  ≃ (∏ (Γ : C) (A : (CwF_SplitTypeCat_Defs.TY (cwf_to_cwf'_structure X) : functor _ _) Γ : hSet),
     (F_TM : nat_trans _ _) (Γ ◂ A) (CwF_SplitTypeCat_Defs.te (cwf_to_cwf'_structure X) A) =
     # (CwF_SplitTypeCat_Defs.TM (cwf_to_cwf'_structure Y) : functor _ _)
       (obj_ext_mor_φ ((weq_cwf_cwf'_structure_mor_ty X Y) x) A)
       (CwF_SplitTypeCat_Defs.te (cwf_to_cwf'_structure Y)
          ((obj_ext_mor_TY ((weq_cwf_cwf'_structure_mor_ty X Y) x)) Γ A))).
   *)

  (* Equivalence of CwF morphisms
     (for two different definitions) *)
  Definition weq_cwf_cwf'_structure_mor
             (X Y : cwf_structure C)
    : cwf_structure_mor X Y ≃ cwf'_structure_mor
                        (cwf_to_cwf'_structure X)
                        (cwf_to_cwf'_structure Y).
  Proof.
    unfold cwf_structure_mor, cwf'_structure_mor.
    unfold term_fun_mor, cwf_structure_mor_data.

    (* Factor out F_TM *)
    refine (_ ∘ weqtotal2dirprodassoc _)%weq.
    refine (weqtotal2comm ∘ _)%weq.
    apply weqfibtototal. intros F_TM.

    (* pack axiom 1 together with type-relevant data of morphism *)
    (* this allows us to use weqtotal2 and split proof *)
    refine (_ ∘ weqtotal2asstol' _ _)%weq.
    use weqtotal2.
    - (* prove equivalence for type-relevant parts *)
      apply weq_cwf_cwf'_structure_mor_ty. (* FIXME: using axiom here! *)
    - (* prove equivalence for term-relevant parts *)
      (* FIXME: cbn/simpl do not work :( *)
      intros.
      use weqdirprodf.
      + (* prove equivalence for typing axiom *)
        (* FIXME: using axiom here! *)
        use weq_cwf_cwf'_structure_mor_weakening_axiom.
      + (* prove equivalence for term axiom *)
        (* FIXME: STUCK HERE *)
        (* Can't even factor out an axiom — it hangs (see above)! *)
        Search (_ ≃ _).
  Defined.

End CwF_Cat_Equiv.
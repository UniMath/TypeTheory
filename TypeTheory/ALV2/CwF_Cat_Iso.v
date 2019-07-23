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

  (* A mapping from one definition of CwF structure to another *)
  Definition cwf_to_cwf'_structure
    : cwf_structure C → cwf'_structure C
    := weq_cwf_cwf'_structure C.

  (* Morphisms of CwF' structures *)
  Definition cwf'_structure_mor (X Y : cwf'_structure C) : UU
    := ∑ (ext : obj_ext_mor (pr1 X) (pr1 Y)),
       term_fun_mor X Y ext.

  (* Extended context notation for CwF' structures *)
  Local Notation "Γ ◂ A" := (comp_ext _ Γ A) (at level 30).

  (* obj_ext data part of CwF' structure morphisms *)
  Definition obj_ext_mor_data (X X' : obj_ext_structure C)
    := ∑ F_TY : pr1 X --> pr1 X',
        ∏ {Γ:C} {A : (pr1 X : functor _ _) Γ : hSet},
        Γ ◂ A --> Γ ◂ ((F_TY : nat_trans _ _) _ A).

  (* data part of CwF' structure morphisms *)
  Definition cwf'_structure_mor_data (X Y : cwf'_structure C) : UU
    := obj_ext_mor_data (pr1 X) (pr1 Y)
        ×
       (pr112 X --> pr112 Y).

  Print sec_total2_distributivity.

  (*
  Definition iso_cwf_extended_contexts
             (X : cwf_structure C)
             (Γ : C)
             (A : (TY X : functor _ _) Γ : hSet)
    : iso (cwf_extended_context X Γ A)
          (comp_ext (cwf_to_cwf'_structure X) Γ A).
  Proof.
    Search iso.
    Search weq.
    apply identity_iso.
  Defined.
  *)
  
  (* Equivalence of typing parts for CwF and CwF' structures *)
  Definition weq_cwf_cwf'_structure_mor_ty
             (X Y : cwf_structure C)
  : (∑ (x : cwf_structure_mor_ty_data X Y),
    cwf_structure_mor_weakening_axiom X Y x)
      ≃ obj_ext_mor (pr1 (cwf_to_cwf'_structure X))
                    (pr1 (cwf_to_cwf'_structure Y)).
  Proof.
    unfold obj_ext_mor, cwf_structure_mor_ty_data. (* Unfold definitions *)
    refine (_ ∘ weqtotal2asstor _ _)%weq. (* Reassociate LHS *)
    apply weqfibtototal. intros F_TY. (* Factor out F_TY component *)

    (* Focus on LHS and simplify it *)
    eapply weqcomp.
    unfold cwf_structure_mor_weakening_axiom.
    cbn. (* NOTE: here cbn does not hang! *)
    apply invweq.

    (* NOTE: at this point we have as a goal
       an equivalence of this form:

       ∑ (_ : ∏ (Γ : _) (A : _), _), _
       ≃
       ∏ (Γ : _) (A : _), ∑ (_ : _), _

       So we want to factor out Γ and A
       by applying [sec_total2_distributivity].

       Unfortunately, Coq is unable to infer our intentions
       (most likely because we have 2 arguments, not 1),
       so we have to spell out most arguments.
    *)
    Check @sec_total2_distributivity.

    (* Factor out Γ *)
    set (CC := λ (Γ : C), λ (p : _),
               ∏ (A : (TY X : functor _ _) Γ : hSet),
               p A ;; cwf_projection Y Γ ((F_TY : nat_trans _ _) Γ A)
               = cwf_projection X Γ A).
    apply (@sec_total2_distributivity _ _ CC).
    apply weqonsecfibers.
    intros Γ.

    (* Factor out A *)
    eapply weqcomp. apply invweq.
    apply (@sec_total2_distributivity
             _ _
             (λ (A : _), λ (p : _),
              p ;; cwf_projection Y Γ ((F_TY : nat_trans _ _) Γ A)
              = cwf_projection X Γ A)).
    apply weqonsecfibers.
    intros A.

    (* NOTE: now we have the same structure *)

    (* STUCK: however, idweq does not work here.
     * This is because Coq does not understand that
     *
     * cwf_extended_context X = comp_ext (cwf_to_cwf'_structure X)
     *
     * (it cannot derive it from weq_cwf_cwf'_structure definition)
     *)
    
    (* STUCK: below are some attempts to get insight into this *)
    Check @weqtotal2.
    use weqtotal2.
    - Search weq.
      Check iso_comp_right_weq.
      Check iso_comp_left_weq.
      unfold cwf_extended_context, comp_ext.
      unfold cwf_to_cwf'_structure.
      exact (idweq _).
      unfold weq_cwf_cwf'_structure.
      unfold invweq, make_weq.

  Defined.

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
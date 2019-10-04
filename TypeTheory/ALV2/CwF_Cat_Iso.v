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
(* Require Import TypeTheory.ALV1.CwF_Defs_Equiv. *)

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

  Definition cwf_to_cwf'_structure : cwf_structure C → cwf'_structure C.
  Proof.
    intros [[[Ty Tm] p] ΓAπ_te_axiom_isPullback].
    set (ΓAπ      := λ Γ A, pr1 (ΓAπ_te_axiom_isPullback Γ A)).
    set (te       := λ Γ A, pr1 (pr1 (pr2 (ΓAπ_te_axiom_isPullback Γ A)))).
    set (te_axiom := λ Γ A, pr2 (pr1 (pr2 (ΓAπ_te_axiom_isPullback Γ A)))).
    set (pullback := λ Γ A, pr2 (pr2 (ΓAπ_te_axiom_isPullback Γ A))).
    set (axioms   := λ Γ A, (te_axiom Γ A, pullback Γ A)).
    exact ((Ty ,, ΓAπ) ,, ((Tm ,, p ,, te) ,, axioms)).
  Defined.
  
  Definition cwf'_to_cwf_structure : cwf'_structure C → cwf_structure C.
  Proof.
    intros [[Ty ΓAπ] [[Tm [p te]] axioms]].
    set (te_axiom := λ Γ A, pr1 (axioms Γ A)).
    set (pullback := λ Γ A, pr2 (axioms Γ A)).
  
    set (pp := ((Ty ,, Tm) ,, p) : mor_total (preShv C)).
    set (r := (λ Γ A,
               (ΓAπ Γ A ,, (te Γ A ,, te_axiom Γ A) ,, pullback Γ A))
              : cwf_representation pp).
    exact (pp ,, r).
  Defined.
  
  Definition isweq_cwf_to_cwf'_structure : isweq cwf_to_cwf'_structure.
  Proof.
    apply (isweq_iso cwf_to_cwf'_structure cwf'_to_cwf_structure).
    - intros x. apply idpath.
    - intros x. apply idpath.
  Defined.
  
  Definition weq_cwf_cwf'_structure
    : cwf_structure C ≃ cwf'_structure C.
  Proof.
    use tpair.
    - apply cwf_to_cwf'_structure.
    - apply isweq_cwf_to_cwf'_structure.
  Defined.

  (* Morphisms of CwF' structures *)
  Definition cwf'_structure_mor (X Y : cwf'_structure C) : UU
    := ∑ (ext : obj_ext_mor (pr1 X) (pr1 Y)),
       term_fun_mor X Y ext.

  Section mor.
    
    Context (X Y : cwf_structure C).

    Definition X' := cwf_to_cwf'_structure X.
    Definition Y' := cwf_to_cwf'_structure Y.

    Definition cwf_to_cwf'_structure_mor
      : cwf_structure_mor X Y → cwf'_structure_mor X' Y'.
    Proof.
      intros [[F_TM [F_TY p]] [ax1 [ax2 ax3]]].
      set (ext := (F_TY ,, λ Γ A, (p Γ A ,, ax1 Γ A))
                  : obj_ext_mor (pr1 X') (pr1 Y')).
      set (tfm := (F_TM ,, ax2 ,, ax3) : term_fun_mor X' Y' ext).
      exact (ext ,, tfm).
    Defined.

    Definition cwf'_to_cwf_structure_mor
      : cwf'_structure_mor X' Y' → cwf_structure_mor X Y.
    Proof.
      intros [[F_TY p_ax1] [F_TM [ax2 ax3]]].
      set (p   := λ Γ A, pr1 (p_ax1 Γ A)).
      set (ax1 := λ Γ A, pr2 (p_ax1 Γ A)).
      exact ((F_TM ,, F_TY ,, p) ,, (ax1 ,, ax2 ,, ax3)).
    Defined.

    Definition isweq_cwf_to_cwf'_structure_mor : isweq cwf_to_cwf'_structure_mor.
    Proof.
        apply (isweq_iso cwf_to_cwf'_structure_mor cwf'_to_cwf_structure_mor).
        - intros x. apply idpath.
        - intros x. apply idpath.
    Defined.

    Definition weq_cwf_cwf'_structure_mor
        : cwf_structure_mor X Y ≃ cwf'_structure_mor X' Y'.
    Proof.
        use tpair.
        - apply cwf_to_cwf'_structure_mor.
        - apply isweq_cwf_to_cwf'_structure_mor.
    Defined.

  End mor.

  Definition cwf_to_cwf'_functor_data
    : functor_data (@cwf_structure_cat C) (term_fun_structure_precat C).
  Proof.
    use make_functor_data.
    - apply cwf_to_cwf'_structure.
    - apply cwf_to_cwf'_structure_mor.
  Defined.

  Definition cwf_to_cwf'_functor_idax
    : functor_idax cwf_to_cwf'_functor_data.
  Proof.
    intros c. 
    use total2_paths_f.
    + apply idpath.                 (* F_TY p ax1 *)
    + use term_fun_mor_eq.
      intros Γ A.
      apply idpath.

      (* alternative proof *)
      (*
      use total2_paths_f.
      * apply idpath.               (* F_TM *)
      * use total2_paths_f.
        -- apply idpath.                   (* ax2 *)
        -- apply impred_isaprop. intros Γ. (* ax3 *)
           apply impred_isaprop. intros A.
           apply setproperty.
      *)
  Defined.

  Definition cwf_to_cwf'_functor_compax
    : functor_compax cwf_to_cwf'_functor_data.
  Proof.
    intros a b c.
    intros f g.

    use total2_paths_f.
    + use total2_paths_f.
      * apply idpath.                (* F_Ty *)
      * apply funextsec. intros Γ.
        apply funextsec. intros A.
        use total2_paths_f.
        -- apply idpath.             (* p *)
        -- apply homset_property.    (* ax1 *)
    + use term_fun_mor_eq.
      intros Γ A.
      (* STUCK HERE for now *)

      use total2_paths_f.
      * use total2_paths_f.
        -- apply funextsec. intros Γ.
           cbn. apply idpath.
        Check nat_trans_comp.
        Check (pr11 f).
        Check (isaset_nat_trans _ (TM a : functor _ _) (TM c : functor _ _)).
        Print cwf_structure_mor_typing_axiom.
        Print cwf_structure_mor_data.
        apply isaproptotal2.
        -- unfold isPredicate.
           intros x.
           
        Search paths.
        apply isaset_nat_trans.
  Defined.

  Definition cwf_to_cwf'_is_functor
    : is_functor cwf_to_cwf'_functor_data
    := (cwf_to_cwf'_functor_idax ,, cwf_to_cwf'_functor_compax).
  
  Definition cwf_to_cwf'_functor
    : functor (@cwf_structure_precategory_data C) (term_fun_structure_precat C).
  Proof.
    use (make_functor cwf_to_cwf'_functor_data).
  Defined.

End CwF_Cat_Equiv.
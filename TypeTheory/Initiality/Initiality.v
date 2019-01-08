Require Import UniMath.MoreFoundations.All.
Require Import UniMath.MoreFoundations.Propositions.
(* [MoreFoundations.Propositions] seems to need individual importing
to provide notation [∃!] as [iscontr_hProp] instead of just [iscontr]. *)
(* TODO: figure out why; perhaps raise issue upstream? *)
Require Import UniMath.CategoryTheory.All.


Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.Partial.
Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.Initiality.SplitTypeCat_Structure.
Require Import TypeTheory.Initiality.SplitTypeCat_Maps.
Require Import TypeTheory.Initiality.SplitTypeCat_Contextual.
Require Import TypeTheory.Initiality.Typing.
Require Import TypeTheory.Initiality.SyntacticCategory.
Require Import TypeTheory.Initiality.Interpretation.


Section Interpretation_Stratified_Contexts.
(* TODO: upstream to [InterpretationLemmas]? *)

  Context {C : split_typecat}
          (U : universe_struct C)
          (Π : pi_struct C)
          (X : C).

  (* TODO: upstream *)
  Definition empty_environment
    : environment X 0.
  Proof.
    intros [].
  Defined.

  Definition environment_of_extension {n}
      (AA : extension_of_length n X)
    : environment (ext_extension X AA) n.
  Proof.
    induction n as [ | n' IH].
    - exact empty_environment.
    - use extend_environment.
      apply IH.
  Defined.

  Definition partial_interpretation_strat_cxt {n}
      (Γ : stratified_context_of_length n)
    : partial (extension_of_length n X).
  Proof.
    induction n as [ | n' IH].
    - apply return_partial. exact tt.
    - apply (bind_partial (IH (context_rest Γ))).
      intros interp_Γ.
      apply (bind_partial (partial_interpretation_ty U Π
                  (environment_of_extension interp_Γ) (context_last Γ))).
      intros interp_A.
      apply return_partial.
      eauto using extension_extend.
  Defined.
  Arguments partial_interpretation_strat_cxt : simpl nomatch.

  Definition strat_cxt_partial_interpretation_respects_type {n}
      (Γ : stratified_context_of_length n)
      (Γ_def : is_defined (partial_interpretation_strat_cxt Γ))
    : environment_respects_type U Π Γ
                             (environment_of_extension (evaluate Γ_def)).
  Proof.
    induction n as [ | n' IH].
    - intros [].
    (* TODO: perhaps factor out [empty_environment_respects_type]. *)
    - destruct Γ_def as [Γ'_def [A_def []]]; cbn in Γ'_def, A_def |- *.
      refine (extend_environment_respects_type _ _ (IH _ Γ'_def) _).
  Qed.

  Definition derivable_strat_cxt_is_interpretable {n}
      (Γ : stratified_context_of_length n)
      (d_Γ : ∥ [! |- Γ !] ∥)
    : is_defined (partial_interpretation_strat_cxt Γ).
  Proof.
    refine (factor_through_squash _ _ d_Γ). { apply propproperty. }
    clear d_Γ; intros d_Γ.
    induction n as [ | n' IH].
    - constructor.
    - destruct d_Γ as [d_Γ' d_A].
      specialize (IH _ d_Γ').
      exists IH. cbn.
      refine (_,,tt).
      refine (@derivable_judgement_is_interpretable _ U Π
                               [! context_rest Γ |- _ !] _ _ (_,,_));
        auto using hinhpr.
      apply strat_cxt_partial_interpretation_respects_type.
  Qed.

  Definition derivable_strat_cxteq_is_interpretable {n}
      (Γ Δ : stratified_context_of_length n)
      (e_ΓΔ : ∥ [! |- Γ === Δ !] ∥)
      (Γ_def : is_defined (partial_interpretation_strat_cxt Γ))
      (Δ_def : is_defined (partial_interpretation_strat_cxt Δ))
    : evaluate Γ_def = evaluate Δ_def.
  Proof.
    refine (factor_through_squash _ _ e_ΓΔ).
    { apply isaset_extension_of_length. }
    clear e_ΓΔ; intros e_ΓΔ.
    induction n as [ | n' IH].
    - apply isapropunit.
    - destruct Γ_def as [Γ'_def [A_def []]]; simpl in Γ'_def, A_def. 
      destruct Δ_def as [Δ'_def [B_def []]]; simpl in Δ'_def, B_def. 
      destruct e_ΓΔ as [e_ΓΔ' e_AB].
      cbn.
      specialize (IH _ _ Γ'_def Δ'_def e_ΓΔ').
      set (interp_Γ' := evaluate Γ'_def) in *.
      simple refine (idpath (extension_extend _ (evaluate A_def)) @ _).
      set (interp_Δ' := evaluate Δ'_def) in *.
      simple refine (_ @ idpath (extension_extend _ (evaluate B_def))).
      assert (H: environment_respects_type U Π (context_rest Γ)
                                 (environment_of_extension interp_Γ')).
      { apply strat_cxt_partial_interpretation_respects_type. }
      clearbody interp_Γ' interp_Δ'.
      clear Γ'_def Δ'_def.
      destruct IH.
      apply maponpaths.
      refine (@derivable_judgement_is_interpretable _ U Π
                           [! context_rest Γ |- _ === _!] _ _ (_,,_) _ _);
        auto using hinhpr.
  Qed.

End Interpretation_Stratified_Contexts.

Section Existence.

  Context (C : contextual_cat)
          (U : universe_struct C)
          (Π : pi_struct C).

  Definition interpretation_map
    : typecat_mor syntactic_typecat C.
  Proof.
  (* should be able to put this together component-by-component,
     as the corresponding components of the syntactic typecat are
     defined, using the total interpretation. *) 
  Admitted.

  (* TODO: add lemmas that it preserves [U] and [Π] *)
End Existence.

Section Uniqueness.

  Context {C : contextual_cat}
          {U : universe_struct C}
          {Π : pi_struct C}.

  Definition interpretation_unique
      (f : typecat_mor syntactic_typecat C)
      (* TODO: and hypotheses that [f] preserves [U] and [Π] *)
    : f = interpretation_map C U Π.
  Proof.
  (* this should come from a couple of lemmas, to be proven not here but
  upstream in [Interpretation], or perhaps a separate file
  [interpretation_2] or something:

  - functoriality of the partial interpretation under typecat maps:
    [fmap_partial_interpretation_ty] and […tm] in [InterpretationLemmas].

  - the total interpretation function into the syntactic category is the
    same as the canonical quotient inclusion.  This should be a single
    induction over derivations.

  Then here, we can put these together to show that [f] is equal to the
  interpretation map into [C].
  *) 
  Admitted.

End Uniqueness.
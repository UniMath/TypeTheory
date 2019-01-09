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
Require Import TypeTheory.Initiality.SyntacticCategory_Structure.
Require Import TypeTheory.Initiality.Environments.
Require Import TypeTheory.Initiality.Interpretation.

Section Interpretation_Stratified_Contexts.
(* TODO: upstream to [InterpretationLemmas]? *)

  Context {C : split_typecat}
          (U : universe_struct C)
          (Π : pi_struct C)
          (X : C).

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

  Definition interpretation_map
      (C : contextual_cat) (U : universe_struct C) (Π : pi_struct C)
    : typecat_mor syntactic_typecat C.
  Proof.
  (* should be able to put this together component-by-component,
     as the corresponding components of the syntactic typecat are
     defined, using the total interpretation. *) 
  Admitted.

  Lemma interpretation_map_preserves_universe
      (C : contextual_cat) (U : universe_struct C) (Π : pi_struct C)
    : preserves_universe_struct
        SyntacticCategory_Structure.univ
        U
        (interpretation_map C U Π).
  Proof.
  Admitted.

  Lemma interpretation_map_preserves_pi
      (C : contextual_cat) (U : universe_struct C) (Π : pi_struct C)
    : preserves_pi_struct
        SyntacticCategory_Structure.pi
        Π
        (interpretation_map C U Π).
  Proof.
  Admitted.

  Lemma interpretation_map_natural
      {C : contextual_cat} {U : universe_struct C} {Π : pi_struct C}
      {C' : contextual_cat} {U' : universe_struct C'} {Π' : pi_struct C'}
      (F : typecat_mor C C')
      (F_U : preserves_universe_struct U U' F)
      (F_Π : preserves_pi_struct Π Π' F)
    : interpretation_map C' U' Π'
    = compose_typecat (interpretation_map C U Π) F.
  Proof.
  Admitted. (* [interpretation_map_natural]: depends on at least [interpretation_map], [compose_typecat]. Sketch proof: after giving each component of the construction of [interpretation_map] above, show that that component is natural; then assemble it all here.  Should mostly be a formal repackaging of [fmap_interpretation], from [InterpretationLemmas]. *)

  Lemma interpretation_map_id
    : interpretation_map
        syntactic_contextual_cat
        SyntacticCategory_Structure.univ
        SyntacticCategory_Structure.pi
    = id_typecat syntactic_typecat.
  Proof.
  Admitted. (* [intepretation_map_id]: proof-irrelevant; depends on [interpretation_map].  Proof sketch: go via a version of this statement in [InterpretationLemmas], something like “for any derivable judgement, its interpretation is just [setquotpr] of it”, which should be provable by an induction over raw syntax, or possibly derivations. *)

End Existence.


Section Uniqueness.

  Context {C : contextual_cat}
          {U : universe_struct C}
          {Π : pi_struct C}.

  Definition interpretation_unique
      (f : typecat_mor syntactic_typecat C)
      (f_U : preserves_universe_struct SyntacticCategory_Structure.univ U f)
      (f_Π : preserves_pi_struct SyntacticCategory_Structure.pi Π f)
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
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
Require Import TypeTheory.Initiality.Typing.
Require Import TypeTheory.Initiality.SyntacticCategory.
Require Import TypeTheory.Initiality.Interpretation.

Section Extensions.
(** Context extensions in type-categories, i.e. suitable sequences of types *)
(* TODO: upstream somewhere! And connect to [CSystems] files? *)

  Fixpoint
      extension_aux {C : typecat} (Γ:C) (n:nat) {struct n}
    : ∑ E : UU, E -> C.
  Proof.
    destruct n as [ | n'].
    - exists unit. intros e; exact Γ.
    - set (E_R := extension_aux C Γ n'). 
      exists (∑ (E : pr1 E_R), C (pr2 E_R E)).
      intros AA_B. exact (ext_typecat _ (pr2 AA_B)).
  Defined.

  Definition extension_of_length {C:typecat} (n:nat) (Γ:C) : UU
    := pr1 (extension_aux Γ n).
  Arguments extension_of_length : simpl nomatch.

  Definition ext_extension_of_length {C:typecat} {n:nat} (Γ:C)
      (AA : extension_of_length n Γ)
    : C
  := pr2 (extension_aux Γ n) AA.
  Arguments ext_extension_of_length : simpl nomatch.

  Definition extension_rest {C:typecat} {n:nat} {Γ:C}
      (AA : extension_of_length (S n) Γ)
    : extension_of_length n Γ
  := pr1 AA.

  Definition extension_last {C:typecat} {n:nat} {Γ:C}
      (AA : extension_of_length (S n) Γ)
    : C (ext_extension_of_length Γ (extension_rest AA))
  := pr2 AA.

  Definition extension_extend {C : typecat} {n} {Γ:C}
      (AA : extension_of_length n Γ)
      (B : C (ext_extension_of_length Γ AA))
    : extension_of_length (S n) Γ
  := (AA,,B).

  Definition extension {C:typecat} (Γ:C) : UU
  := ∑ n:nat, extension_of_length n Γ.

  Definition extension_length {C:typecat} {Γ:C}
  : extension Γ -> nat := pr1.

  Definition extension_pr2 {C:typecat} {Γ:C} (AA : extension Γ)
    : extension_of_length (extension_length AA) Γ
  := pr2 AA.
  Coercion extension_pr2 : extension >-> extension_of_length.

  Definition make_extension {C:typecat} {n} {Γ:C}
    : extension_of_length n Γ -> extension Γ
  := fun AA => (n,,AA).
  Coercion make_extension : extension_of_length >-> extension.

  Definition ext_extension {C:typecat}
      (Γ:C) (AA : extension Γ)
    : C
  := ext_extension_of_length Γ AA. 
  Arguments ext_extension : simpl nomatch.

  Fixpoint dpr_extension {C:typecat} {n:nat} {Γ:C}
      (AA : extension_of_length n Γ) {struct n}
    : (ext_extension Γ AA) --> Γ.
  Proof.
    destruct n as [ | n'].
    - use identity.
    - exact (dpr_typecat (extension_last AA)
            ;; dpr_extension _ _ _ (extension_rest AA)).
  Defined.

  Lemma isaset_extension_of_length {C:split_typecat} (n:nat) (Γ:C)
    : isaset (extension_of_length n Γ).
  Proof.
    induction n as [ | n' IH].
    - apply isasetunit.
    - apply isaset_total2; try apply IH.
      intros; apply isaset_types_typecat.
  Qed.

  Lemma isaset_extension {C:split_typecat} (Γ:C)
    : isaset (extension Γ).
  Proof.
    apply isaset_total2.
    - apply isasetnat.
    - intros; apply isaset_extension_of_length.
  Qed.

End Extensions.

Section Contextual_Cats.
(** A split type-categoy is _contextual_ if it has some base object, such that every object arises uniquely as an extension of this base object. 

Note that such a base object is necessarily unique: see [isaprop_is_contextual]. *)

  Definition is_contextual (C : split_typecat)
  := ∑ Γ0 : C,
       isTerminal C Γ0
       ×
       ∀ Γ:C, ∃! AA : extension Γ0, ext_extension Γ0 AA = Γ.
  (** The second component could be written as
  [isweq (ext_extension Γ0)], but we spell it out for readability. *)

  Definition empty_contextual {C} (H : is_contextual C) : C
  := pr1 H.

  Definition isTerminal_empty_contextual {C} {H : is_contextual C}
    : isTerminal C (empty_contextual H)
  := pr1 (pr2 H).

  Definition unique_extension_contextual {C} {H : is_contextual C} (Γ : C)
    : ∃! AA : extension (empty_contextual H),
              ext_extension (empty_contextual H) AA = Γ
  := pr2 (pr2 H) Γ.

  Definition isweq_ext_extension_empty_contextual {C} (H : is_contextual C)
    : isweq (ext_extension (empty_contextual H))
  := pr2 (pr2 H).

  Lemma isaprop_is_contextual {C : split_typecat}
    : isaprop (is_contextual C).
  Proof.
    apply invproofirrelevance; intros H H'.
    apply subtypeEquality.
    { intros Γ0; apply isapropdirprod.
    - admit. (* couldn’t find in library for either [isTerminal]
                or [limits.terminal.isTerminal]. *)
    - apply propproperty. }
    destruct H as [Γ0 [K H]], H' as [Γ0' [K' H']]; cbn; clear K K'.
    destruct (H Γ0') as [[AA e] _], (H' Γ0) as [[AA' e'] _].
    admit.
    (* sketch:
    - define concatenation of extensions
    - conclude [ext_extension Γ0 (AA+AA') = Γ0] 
    - by uniqueness part of [H Γ0], conclude [AA+AA' = extension_empty]
    - conclude [AA = extension_empty]
    - conclude [Γ0' = Γ0]. *)
  Admitted. (* [isaprop_is_contextual]: low-priority, since probably not
             actually needed, just included to justify un-truncated def of
             [is_contextual]. *)

  Definition contextual_cat : UU
    := ∑ C : split_typecat, is_contextual C.

  Coercion pr1_contextual_cat := pr1 : contextual_cat -> split_typecat.
  Coercion pr2_contextual_cat := pr2 
    : forall C : contextual_cat, is_contextual C.

  Lemma isaset_ob_contextual_cat {C : contextual_cat}
    : isaset (ob C).
  Proof.
    refine (isofhlevelweqf 2 _ _).
    - exists (ext_extension (empty_contextual C)).
      apply isweq_ext_extension_empty_contextual.
    - apply isaset_extension.
  Qed.

End Contextual_Cats.

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
     as the corresponding components of the snytactic typecat are
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
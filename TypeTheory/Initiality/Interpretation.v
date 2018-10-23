(** This file defines the interpretation function, from the syntax of our toy type theory into any split type-cat with suitable structure. *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.All.

(* TODO: raise issue upstream: notation "_ ∘ _" is used for function-order composition of functions, but for diagrammatic-order composition of morphisms in categories! *)

Require Import TypeTheory.Auxiliary.Partial.
Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.Initiality.SplitTypeCat_Maps.
Require Import TypeTheory.Initiality.SplitTypeCat_Structure.
Require Import TypeTheory.Initiality.Syntax.
Require Import TypeTheory.Initiality.Typing.

Section Auxiliary.

  (* TODO: upstream! *)
  Definition partial_map X Y := X -> partial Y.
  Notation "X ⇢ Y" := (partial_map X Y) (at level 99) : type_scope.

  (* TODO: upstream! *)
  Definition compose_partial {X Y Z} (f : X ⇢ Y) (g : Y ⇢ Z) : X ⇢ Z
    := fun x => bind_partial (f x) g.
  Notation "f ∘ g" := (compose_partial f g) : partial_map_scope.
  (** This notation uses diagrammatic order, following UniMath’s notation
  [ (_ ∘ _)%Cat ] for morphisms in categories, _not_ consistent with
  UniMath’s notation [ (_ ∘ _)%functions ] for functions. *)

  (* TODO: work out better way to treat this and the following *)
  Definition mor_paths_hProp {C : category} {X Y : C} (f g : X --> Y)
    : hProp
  := hProppair (f = g) (homset_property C _ _ _ _).

  (* TODO: work out better way to treat this *)
  Definition type_paths_hProp {C : split_typecat} {Γ : C} (A B : C Γ)
    : hProp
  := hProppair (A = B) (isaset_types_typecat C _ _ _).

End Auxiliary.

Section Environments.
(** _Environments_: the semantic proxy for a context, in a split type-category, giving the information needed to construct the (partial) interpretation of terms/types from some context over some object of the type-cat. *)

  Context {C : split_typecat}.

  (* TODO: perhaps upstream? *)
  Definition term_with_type (Γ:C) := ∑ (A : C Γ), tm A.

  Definition type_of {Γ} (Aa : term_with_type Γ) := pr1 Aa.

  Coercion term_of {Γ} (Aa : term_with_type Γ) : tm (type_of Aa)
    := pr2 Aa.

  Definition reind_term_with_type {Γ Γ'} (f : Γ' --> Γ)
    : term_with_type Γ -> term_with_type Γ'
  := fun a => ((type_of a)⦃f⦄,, reind_tm f a).
  
  (*TODO: look for this upstream! *)
  (** the “universal term of type A” *)
  Definition var_typecat (Γ:C) (A:C Γ)
  : tm (A ⦃dpr_typecat A⦄).
  Admitted.

  (** An _environment_ over [Γ]: a map giving, for each variable from some potential context, a type and a term of that type.

  Motivating example: if [Γ] is the interpretation of some actual context, then each type of the context should be interpreted as some type over Γ, and each the corresponding variable can be extracted to a term of that type. *)

  Definition environment (Γ:C) (n:nat)
    := dB_vars n -> term_with_type Γ.
  
  Definition extend_environment
      {Γ:C} {n:nat} (E : environment Γ n) (A : C Γ)
    : environment (Γ ◂ A) (S n).
  Proof.
    refine (dB_Sn_rect _ _ _).
    - exists (A ⦃dpr_typecat A⦄).
      apply var_typecat.
    - intro i.
      exact (reind_term_with_type (dpr_typecat A) (E i)).
  Defined.

End Environments.

Section Partial_Interpretation.
(** In this section, we construct the partial interpretation function. *)

  Context {C : split_typecat} (U : universe_struct C) (Π : pi_struct C).

  Fixpoint
    partial_interpretation_ty
      {Γ:C} {n:nat} (E : environment Γ n) (e : ty_expr n)
    : partial (C Γ)
  with
    partial_interpretation_tm
      {Γ:C} {n:nat} (E : environment Γ n) (T : C Γ) (e : tm_expr n)
    : partial (tm T). (* See note below re type. *)
  Proof.
    - (* type expressions *)
      destruct e as [ m | m a | m A B ].
      + (* universe *)
        apply return_partial, U.
      + (* [El_expr a] *)
        get_partial (partial_interpretation_tm _ _ E (U _) a) interp_a.
        apply return_partial. exact (@elements _ U _ interp_a).
      + (* [Pi_expr A B] *)
        get_partial (partial_interpretation_ty _ _ E A) interp_A.
        set (E_A := extend_environment E interp_A).
        get_partial (partial_interpretation_ty _ _ E_A B) interp_B.
        apply return_partial. exact (Π _ interp_A interp_B).
    - (* term expressions *)
      destruct e as [ m i | m A B b | m A B f a ].
      + (* [var_expr i] *)
        assume_partial (type_paths_hProp (type_of (E i)) T) e_Ei_T.
        apply return_partial.
        exact (tm_transportf e_Ei_T (E i)).
      + (* lambda *)
        get_partial (partial_interpretation_ty _ _ E A) interp_A.
        set (E_A := extend_environment E interp_A).
        get_partial (partial_interpretation_ty _ _ E_A B) interp_B.
        get_partial (partial_interpretation_tm _ _ E_A interp_B b) interp_b.
        assume_partial (type_paths_hProp T (Π _ interp_A interp_B)) e_T_ΠAB.
        apply return_partial.
        refine (tm_transportb e_T_ΠAB _).
        exact (pi_intro _ _ _ _ _ interp_b).
      + (* [app_expr A B f a] *)
        get_partial (partial_interpretation_ty _ _ E A) interp_A.
        set (E_A := extend_environment E interp_A).
        get_partial (partial_interpretation_ty _ _ E_A B) interp_B.
        set (Π_A_B := Π _ interp_A interp_B).
        get_partial (partial_interpretation_tm _ _ E interp_A a) interp_a.
        get_partial (partial_interpretation_tm _ _ E Π_A_B f) interp_f. 
        assume_partial (type_paths_hProp T (interp_B ⦃interp_a⦄)) e_T_Ba.
        apply return_partial.
        refine (tm_transportb e_T_Ba _).
        refine (pi_app _ _ _ _ _ interp_f interp_a).
  Defined.

  (** Note: alternatively, we could give the interpretation of terms as 
   [ partial_interpretation_tm
       {Γ:C} {n:nat} (E : environment Γ n) (e : tm_expr n)
     : partial (term_with_type Γ). ]
  I think either should work fine; I’m not sure which will work more cleanly. *)

  Global Arguments partial_interpretation_tm : simpl nomatch.
  Global Arguments partial_interpretation_ty : simpl nomatch.

End Partial_Interpretation.

Section Totality.

  Context {C : split_typecat} (U : universe_struct C) (Π : pi_struct C).

  Definition environment_respects_type
      {X : C} (Γ : context) (E : environment X Γ)
    : UU
  := forall i : Γ,
    ∑ (d : is_defined (partial_interpretation_ty U Π E (Γ i))),
      (type_of (E i) = evaluate d).

  Definition typed_environment (X : C) (Γ : context)
    := ∑ (E : environment X Γ), environment_respects_type Γ E.

  Coercion environment_of_typed_environment {X} {Γ}
    (E : typed_environment X Γ) : environment X Γ
  := pr1 E.

  Definition typed_environment_respects_types {X} {Γ}
    (E : typed_environment X Γ) (i : Γ)
  := pr2 E i.

  Local Open Scope judgement_scope.

  Definition is_interpretable (J : judgement) : hProp
  := match J with
     | [! |- Γ !] => htrue
     | [! Γ |- A !]
       => ∀ (X:C) (E : typed_environment X Γ),
         is_defined (partial_interpretation_ty U Π E A)         
     | [! Γ |- A === A' !]
       => ∀ (X:C) (E : typed_environment X Γ)
            (d_A : is_defined (partial_interpretation_ty U Π E A))   
            (d_A' : is_defined (partial_interpretation_ty U Π E A)),
         type_paths_hProp (evaluate d_A) (evaluate d_A') 
     | [! Γ |- a ::: A !]
       => ∀ (X:C) (E : typed_environment X Γ)
            (d_A : is_defined (partial_interpretation_ty U Π E A)), 
         is_defined (partial_interpretation_tm U Π E (evaluate d_A) a)
     | [! Γ |- a === a' ::: A !]
       => ∀ (X:C) (E : typed_environment X Γ)
          (d_A : is_defined (partial_interpretation_ty U Π E A))
          (d_a : is_defined (partial_interpretation_tm U Π E (evaluate d_A) a)) 
          (d_a' : is_defined (partial_interpretation_tm U Π E (evaluate d_A) a)), 
         mor_paths_hProp (evaluate d_a) (evaluate d_a')
  end.
  (* Note: we DON’T expect to need any inductive information for context judgements!

  Essentially, our rules have been set up carefully enough that (hopefully) the context judgement could be removed entirely without loss. *)

  Lemma is_interpretable_is_prop {J} : isaprop (is_interpretable J).
  Proof.
    destruct J; eauto using propproperty. 
  Defined.
  
  Local Lemma interpret_context_rules
    : cases_for_context_rules (fun J _ => is_interpretable J).
  Proof.
    split; intros; cbn; constructor.
  Defined.

  Local Lemma interpret_var_rule
    : case_for_var_rule (fun J _ => is_interpretable J).
  Proof.
    intros ? ? ? H_Γ ? H_Γi.
    intros X E Γi_interpretable.
    refine (_,,tt); cbn.
    eapply pathscomp0. { apply typed_environment_respects_types. }
    apply maponpaths, propproperty.
  Defined.

  Local Lemma interpret_equiv_rel_rules
    : cases_for_equiv_rel_rules (fun J _ => is_interpretable J).
  Admitted.

  Local Lemma interpret_conv_rules
    : cases_for_conv_rules (fun J _ => is_interpretable J).
  Admitted.

  Local Lemma interpret_subst_rules
    : cases_for_subst_rules (fun J _ => is_interpretable J).
  Admitted.

  Local Lemma interpret_substeq_rules
    : cases_for_substeq_rules (fun J _ => is_interpretable J).
  Admitted.

  Local Lemma interpret_universe_rules
    : cases_for_universe_rules (fun J _ => is_interpretable J).
  Proof.
    split.
    - (* universe formation *)
      intros; intros X E; auto.
    - (* elements formation *)
      intros; intros X E.
      refine (_,,tt).
      refine (p_a _ _ tt).
    - (* elements congruence *)
      intros; intros X E d_A d_A'.
      apply maponpaths, propproperty.
  Defined.

  Local Lemma interpret_pi_rules
    : cases_for_pi_rules (fun J _ => is_interpretable J).
  Admitted.

  Local Lemma interpret_pi_cong_rules
    : cases_for_pi_cong_rules (fun J _ => is_interpretable J).
  Admitted.

  Fixpoint interpretable_from_derivation {J : judgement}
    : derivation J -> is_interpretable J.
  Proof.
    revert J. apply derivation_rect_grouped.
    - apply interpret_context_rules.
    - apply interpret_var_rule.
    - apply interpret_equiv_rel_rules.
    - apply interpret_conv_rules.
    - apply interpret_subst_rules.
    - apply interpret_substeq_rules.
    - apply interpret_universe_rules.
    - apply interpret_pi_rules.
    - apply interpret_pi_cong_rules.
  Defined.

  Lemma derivable_judgement_is_interpretable {J : judgement}
    : ∥ derivation J ∥ -> is_interpretable J.
  Proof.
    apply factor_through_squash.
    - apply is_interpretable_is_prop.
    - apply interpretable_from_derivation.
  Defined.

End Totality.
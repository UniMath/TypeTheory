(** In this file, we show admissibility of the substitution rule(s) for derivations.

(NOTE: currently, the substitution rules still given explicitly; so for now, the file defines the transformation of derivations into a substitution-free form, with the intention of later removing those rules. *)

Require Import UniMath.MoreFoundations.All.

Require Import TypeTheory.Auxiliary.Auxiliary.

Require Import TypeTheory.Initiality.Syntax.
Require Import TypeTheory.Initiality.SyntaxLemmas.
Require Import TypeTheory.Initiality.Typing.

Local Open Scope judgement_scope.
Local Open Scope context_scope.

Section Auxiliary_Judgements.

  (** The context judgement [! |- Γ !] is almost entirely used just for one
  consequence: that all types are well-typed over it. 

  We quite happily could (and perhaps should) omit the context judgement
  entirely in the definition of derivations, and then define this as an
  auxiliary judgement afterwards, as we do for context morphisms. 

  The only place where the extra “stratification” information carried by
  [! |- Γ !] is needed is in the construction of the _contextual_ syntactic
  category below; but that too can be instead done by defining stratification
  as an auxiliary notion just when it’s really needed. *)
  Definition derivation_flat_context (Γ : context)
    := forall i:Γ, [! Γ |- Γ i !].

  Notation "[! |f- Γ !]" := (derivation_flat_context Γ)
                              (format "[!  |f-  Γ  !]") : judgement_scope.

  (* TODO: perhaps rename existing [context] to [raw_context], for consistency, and use [context] for either this or the later stratified notion. *) 
  Definition flat_context
    := ∑ (Γ : context), [! |f- Γ !].

  Coercion context_of_flat_context (Γ : flat_context) : context
    := pr1 Γ.

  Definition derivation_from_flat_context (Γ : flat_context) (i : Γ)
    : [! Γ |- Γ i !]
  := pr2 Γ i.

  (** We want to prove that the context judgment implies this: *)
  Definition flat_from_context_judgement {Γ : context} 
    : [! |- Γ !] -> [! |f- Γ !].
  Abort.
  (** However, we first need to show admissibility of weakening;
   or, more generally, admissibility of “typed renaming”.

   Specifically, we prove that admissibility as [rename_derivation]
   below, and then prove [flat_from_context_judgement]. *)

  Definition derivation_map
      (Δ Γ : context) (f : raw_context_map Δ Γ) : UU
  := forall i:Γ, [! Δ |- f i ::: subst_ty f (Γ i) !].

  Identity Coercion id_derivation_map
    : derivation_map >-> Funclass.

  Notation "[! |- f ::: Δ ---> Γ !]" := (derivation_map Δ Γ f)
                    (format "[! |- f ::: Δ ---> Γ !]") : judgement_scope.


  (** As with [ [! |f- Γ !] ], the actual key lemmas about
  [ [! |- f ::: Δ -> Γ !] ] can’t be given until after admissibility of
  weakening, [rename_derivation]. *)

  Definition context_map (Δ Γ : context) : UU
    := ∑ (f : raw_context_map Δ Γ), [! |- f ::: Δ ---> Γ !].

  Definition context_map_pr1 {Γ Δ} (f : context_map Γ Δ) := pr1 f
    : raw_context_map _ _.
  Coercion context_map_pr1 : context_map >-> raw_context_map.

  Definition derivation_from_context_map {Γ Δ} (f : context_map Γ Δ) (i : Δ)
    : derivation _
  := pr2 f i.

  Definition derivation_mapeq
    (Δ Γ : context) (f g : raw_context_map Δ Γ) : UU
  := forall i:Γ, [! Δ |- f i === g i ::: subst_ty f (Γ i) !].

  Notation "[! |- f === g ::: Δ ---> Γ !]" := (derivation_mapeq Δ Γ f g)
                    (format "[! |- f === g ::: Δ ---> Γ !]") : judgement_scope.

End Auxiliary_Judgements.

(** Re-declaring notations from section *)
Notation "[! |f- Γ !]" := (derivation_flat_context Γ)
                                (format "[!  |f-  Γ  !]") : judgement_scope.
Notation "[! |- f ::: Δ ---> Γ !]" := (derivation_map Δ Γ f)
                (format "[!  |-  f  :::  Δ  --->  Γ  !]") : judgement_scope.
Notation "[! |- f === g ::: Δ ---> Γ !]" := (derivation_mapeq Δ Γ f g)
        (format "[!  |-  f  ===  g  :::  Δ  --->  Γ  !]") : judgement_scope.


(** Admissibility of weakening will be obtained as an instance of the general
fact that one can rename variables throughout a derivation, providing the renaming
respects the types (for now, up to literal syntactic equality). *)
Section Typed_Renaming.

  (** A _typed renaming_ between contexts: a renaming function for their
  variables, respecting types up to syntactic equality. *)
  Definition typed_renaming (Γ Δ : context) : UU
    := ∑ (f : Γ -> Δ),
       forall i:Γ, Δ (f i) = rename_ty f (Γ i).

  Definition typed_renaming_pr1 {Γ Δ} (f : typed_renaming Γ Δ) : Γ -> Δ
    := pr1 f.
  Coercion typed_renaming_pr1 : typed_renaming >-> Funclass.

  Definition typed_renaming_commutes {Γ Δ} (f : typed_renaming Γ Δ) (i : Γ)
    : Δ (f i) = rename_ty f (Γ i)
  := pr2 f i.

  Definition weaken_typed_renaming
    {Γ Δ} (f : typed_renaming Γ Δ) (A : ty_expr Γ)
    : typed_renaming (Γ ;; A) (Δ ;; rename_ty f A). 
  Proof.
    exists (fmap_dB_S f).
    use dB_Sn_rect; cbn.
    - eapply pathscomp0. 2: { apply rename_comp_ty. } 
      refine (!rename_comp_ty _ _ _).
    - intros i; cbn.
      eapply pathscomp0. 2: { apply rename_comp_ty. } 
      eapply pathscomp0. { apply maponpaths, typed_renaming_commutes. }
      refine (!rename_comp_ty _ _ _).
  Defined.

  Definition dB_next_typed_renaming (Γ:context) (A : ty_expr Γ)
    : typed_renaming Γ (Γ;;A).
  Proof.
    exists dB_next. intros; apply idpath.
  Defined.
  
End Typed_Renaming.

Section Renaming_Judgements.

  Definition context_of_judgement (J : judgement) : context
  := match J with
     | [! |- Γ !] => Γ
     | [! Γ |- A !] => Γ
     | [! Γ |- A === A' !] => Γ
     | [! Γ |- a ::: A !] => Γ
     | [! Γ |- a === a' ::: A !] => Γ
  end.

  Definition rename_judgement
      (J : judgement) {Δ : context} 
    : (context_of_judgement J -> Δ)
    -> judgement.
  Proof.
    destruct J as [ Γ | Γ A | Γ A A' | Γ A a | Γ A a a' ]; intros f.
    - exact [! |- Δ !].
    - exact [! Δ |- rename_ty f A !].
    - exact [! Δ |- rename_ty f A === rename_ty f A' !].
    - exact [! Δ |- rename_tm f a ::: rename_ty f A !].
    - exact [! Δ |- rename_tm f a === rename_tm f a' ::: rename_ty f A !].
  Defined.

  (** The general admissibility of weakening/typed renaming:
  one can rename variables throughout a derivation. *)
(* Note: if the context judgement is removed in definition of derivations,
then the hypothesis [d_Δ] should be unnecessary here (but compare 
[substeq_derivation] below). *)
  Definition rename_derivation
      (J : judgement) (d_J : derivation J)
      {Δ} (f : typed_renaming (context_of_judgement J) Δ)
      (d_Δ : [! |- Δ !])
    : derivation (rename_judgement J f).
  Proof.
    revert J d_J Δ f d_Δ.
    use derivation_rect_grouped.
    - split; auto. (* context rules *)
    - (* var rule *)
      intros Γ; cbn; intros i _ _ d_Γi IH_Γi Δ f d_Δ.
      specialize (IH_Γi Δ f d_Δ). 
      set (e := typed_renaming_commutes f i). destruct e.
      apply derive_var; assumption.
    - split. (* equiv_rel_rules *)
      + intros. apply derive_tyeq_refl; eauto. 
      + intros. apply derive_tyeq_sym; eauto.
      + intros ? ? A1 ? ? ? ? ? ? ? ? ? ? ? ? f ?.
        apply derive_tyeq_trans with (rename_ty f A1); eauto.
      + intros. apply derive_tmeq_refl; eauto.
      + intros. apply derive_tmeq_sym; eauto.
      + intros ? ? ? a1 ? ? ? ? ? ? ? ? ? ? ? ? f ?.
        apply derive_tmeq_trans with (rename_tm f a1); eauto.
    - split. (* conv rules *)
      + intros ? A ? ? ? ? ? ? ? ? ? ? ? f ?.
        apply derive_tm_conv with (rename_ty f A); eauto.
      + intros ? A ? ? ? ? ? ? ? ? ? ? ? ? f ?.
        apply derive_tmeq_conv with (rename_ty f A); eauto.
    - split. (* universe rules *)
      + intros; apply derive_U; auto.
      + intros; apply derive_El; eauto.
      + intros; apply derive_El_cong; eauto.
    - split. (* Pi rules *)
      + cbn. intros; apply derive_Pi; auto.
        refine (p_B _ (weaken_typed_renaming _ _) _).
        apply derive_cxt_extend; auto.
      + cbn. intros; apply derive_lam; auto;
        set (fA := weaken_typed_renaming f A).
        * refine (p_B _ fA _); auto using derive_cxt_extend.
        * refine (p_b _ fA _); auto using derive_cxt_extend.        
      + cbn. intros ? A ? ? ? ? ? ? ? ? p_B ? ? ? ? ? f ?.
        refine (transportb _ _ _). 
        { eapply maponpaths_2, rename_subst_top_ty. }
        apply derive_app; eauto.
        refine (p_B _ (weaken_typed_renaming f A) _);
          auto using derive_cxt_extend.
      + cbn. intros ? A ? ? ? ? ? ? ? ? p_B ? p_b ? ? ? f ?.
        refine (transportb _ _ _). 
        { eapply maponpaths_13. 
          - apply rename_subst_top_ty.
          - apply rename_subst_top_tm. }
        apply derive_beta; eauto.
        * refine (p_B _ (weaken_typed_renaming f A) _);
            auto using derive_cxt_extend.
        * refine (p_b _ (weaken_typed_renaming f A) _);
            auto using derive_cxt_extend.
    - split. (* congruences for pi-constructors *)
      + cbn. intros ? A ? ? ? ? ? ? ? ? ? ? p_BB ? f ?.
        apply derive_Pi_cong; auto.
        refine (p_BB _ (weaken_typed_renaming _ _) _).
        apply derive_cxt_extend; eauto.
      + cbn. intros ? A ? ? ? ? ? ? ? ? ? ? ? ? p_BB ? p_bb ? f ?.
        apply derive_lam_cong; auto.
        * refine (p_BB _ (weaken_typed_renaming _ _) _).
          apply derive_cxt_extend; eauto.
        * refine (p_bb _ (weaken_typed_renaming _ _) _).
          apply derive_cxt_extend; eauto.
      + cbn. intros ? A ? ? ? ? ? ? ? ? ? ? ? ? ? ? p_BB ? ? ? ? ? f ?.
        refine (transportb _ _ _). 
        { eapply maponpaths_3, rename_subst_top_ty. }
        apply derive_app_cong; auto.
        refine (p_BB _ (weaken_typed_renaming _ _) _).
        apply derive_cxt_extend; eauto.
  Defined.

End Renaming_Judgements.

(** With [rename_derivation], we can prove the basic lemmas about flat contexts
and context maps. *)

Section Flat_Contexts.

  Definition flat_from_context_judgement {Γ : context} 
    : [! |- Γ !] -> [! |f- Γ !].
  Proof.
    transparent assert (generalised_goal : (forall J, derivation J -> UU)).
    { intros [ Δ | | | | ] d; [ exact [! |f- Δ !] | | | | ]; exact unit. }
    assert (generalised_proof : forall J d, generalised_goal J d).
    2: { apply generalised_proof. } 
    clear Γ.
    apply derivation_rect; try (intros; exact tt).
    (* only 2 cases to consider *) 
    - intros [].
    - cbn; intros Γ A d_Γ IH_Γ d_A _ i; cbn.
      refine (rename_derivation [! _ |- _ !] _
                                       (dB_next_typed_renaming _ _) _);
        cbn.
      2: { use derive_cxt_extend; assumption. }
      revert i; use dB_Sn_rect; cbn; auto.
  Qed.

End Flat_Contexts.

Section Context_Maps.

  (** The eventual [weaken_derivation_map] shouldn’t need the
   hypothesis [ [! Δ |- subst_ty f A !] ]. However, that requires admissibility
   of substitution, which in turn uses this preliminary version. *)
  Local Definition weaken_derivation_map_prelim
      {Δ Γ : context} (f : raw_context_map Δ Γ) (A : ty_expr Γ)
    : [! |- Δ !]
      -> [! |- f ::: Δ ---> Γ !]
      -> [! Δ |- subst_ty f A !]
      -> [! |- weaken_raw_context_map f ::: Δ ;; subst_ty f A ---> Γ ;; A !].
  Proof.
    intros d_Δ d_f d_fA i.
    eapply transportb.
    { apply maponpaths_2.
      eapply pathscomp0. { use subst_rename_ty. } 
      apply pathsinv0. use rename_subst_ty. }
    destruct i as [ | i]; cbn.
    - refine (derive_var (_;;_) dB_top _ _).
      { apply derive_cxt_extend; auto. }
      refine (rename_derivation [! _ |- _ !] _
                                       (dB_next_typed_renaming _ _) _);
        auto using derive_cxt_extend.
    - refine (rename_derivation [! _ |- _ ::: _ !] _
                                       (dB_next_typed_renaming _ _) _);
        eauto using derive_cxt_extend.
  Defined.

End Context_Maps.

Section Substitute_Judgements.

  Definition subst_judgement
      (J : judgement) {Δ : context} 
    : raw_context_map Δ (context_of_judgement J)
    -> judgement.
  Proof.
    destruct J as [ Γ | Γ A | Γ A A' | Γ A a | Γ A a a' ]; intros f.
    - exact [! |- Δ !].
    - exact [! Δ |- subst_ty f A !].
    - exact [! Δ |- subst_ty f A === subst_ty f A' !].
    - exact [! Δ |- subst_tm f a ::: subst_ty f A !].
    - exact [! Δ |- subst_tm f a === subst_tm f a' ::: subst_ty f A !].
  Defined.

  Definition subst_derivation
      (J : judgement) (d_J : derivation J)
      {Δ : context} (d_Δ : [! |- Δ !])
(* Note: if the context judgement is removed in definition of derivations,
then the hypothesis [d_Δ] should be unnecessary here (but compare 
[substeq_derivation] below). *)
      {f : raw_context_map Δ (context_of_judgement J)}
      (d_f : [! |- f ::: Δ ---> context_of_judgement J !])
    : derivation (subst_judgement J f).
  Proof.
    revert J d_J Δ d_Δ f d_f.
    use derivation_rect_grouped.
    - split; auto. (* context rules *)
    - (* var rule *)
      intros Γ; cbn; intros i _ _ d_Γi IH_Γi Δ d_Δ f d_f.
      specialize (IH_Γi Δ d_Δ f d_f). 
      apply d_f.
    - split. (* equiv_rel_rules *)
      + intros. apply derive_tyeq_refl; eauto. 
      + intros. apply derive_tyeq_sym; eauto.
      + intros ? ? A1 ? ? ? ? ? ? ? ? ? ? ? ? ? f ?.
        apply derive_tyeq_trans with (subst_ty f A1); eauto.
      + intros. apply derive_tmeq_refl; eauto.
      + intros. apply derive_tmeq_sym; eauto.
      + intros ? ? ? a1 ? ? ? ? ? ? ? ? ? ? ? ? ? f ?.
        apply derive_tmeq_trans with (subst_tm f a1); eauto.
    - split. (* conv rules *)
      + intros ? A ? ? ? ? ? ? ? ? ? ? ? ? f ?.
        apply derive_tm_conv with (subst_ty f A); eauto.
      + intros ? A ? ? ? ? ? ? ? ? ? ? ? ? ? f ?.
        apply derive_tmeq_conv with (subst_ty f A); eauto.
    - split. (* universe rules *)
      + intros; apply derive_U; auto.
      + intros; apply derive_El; eauto.
      + intros; apply derive_El_cong; eauto.
    - split. (* Pi rules *)
      + cbn. intros; apply derive_Pi; auto.
        refine (p_B _ _ _ _);
          auto using weaken_derivation_map_prelim, derive_cxt_extend.
      + cbn. intros; apply derive_lam; auto.
        * refine (p_B _ _ _ _);
          auto using weaken_derivation_map_prelim, derive_cxt_extend.
        * refine (p_b _ _ _ _);
          auto using weaken_derivation_map_prelim, derive_cxt_extend.
      + cbn. intros ? A ? ? ? ? ? ? ? ? p_B ? ? ? ? ? ? f ?.
        refine (transportb _ _ _). 
        { eapply maponpaths_2, subst_subst_top_ty. }
        apply derive_app; eauto.
        refine (p_B _ _ _ _);
          auto using weaken_derivation_map_prelim, derive_cxt_extend.
      + cbn. intros ? A ? ? ? ? ? ? ? ? p_B ? p_b ? ? ? ? f ?.
        refine (transportb _ _ _). 
        { eapply maponpaths_13. 
          - apply subst_subst_top_ty.
          - apply subst_subst_top_tm. }
        apply derive_beta; eauto.
        * refine (p_B _ _ _ _);
          auto using weaken_derivation_map_prelim, derive_cxt_extend.
        * refine (p_b _ _ _ _);
          auto using weaken_derivation_map_prelim, derive_cxt_extend.
    - split. (* congruences for pi-constructors *)
      + cbn. intros ? A ? ? ? ? ? ? ? ? ? ? p_BB ? ? f ?.
        apply derive_Pi_cong; auto.
        refine (p_BB _ _ _ _);
          auto using weaken_derivation_map_prelim, derive_cxt_extend.
      + cbn. intros ? A ? ? ? ? ? ? ? ? ? ? ? ? p_BB ? p_bb ? ? f ?.
        apply derive_lam_cong; auto.
        * refine (p_BB _ _ _ _);
          auto using weaken_derivation_map_prelim, derive_cxt_extend.
        * refine (p_bb _ _ _ _);
          auto using weaken_derivation_map_prelim, derive_cxt_extend.
      + cbn. intros ? A ? ? ? ? ? ? ? ? ? ? ? ? ? ? p_BB ? ? ? ? ? ? f ?.
        refine (transportb _ _ _). 
        { eapply maponpaths_3, subst_subst_top_ty. }
        apply derive_app_cong; auto.
        refine (p_BB _ _ _ _);
          auto using weaken_derivation_map_prelim, derive_cxt_extend.
  Defined.

End Substitute_Judgements.

Section Compose_Derivations.

  Local Definition weaken_derivation_map
      {Δ Γ : context} (f : raw_context_map Δ Γ) (A : ty_expr Γ)
    : [! |- Δ !]
      -> [! |- f ::: Δ ---> Γ !]
      -> [! Γ |- A !]
      -> [! |- weaken_raw_context_map f ::: Δ ;; subst_ty f A ---> Γ ;; A !].
  Proof.
    intros; apply weaken_derivation_map_prelim; auto.
    refine (subst_derivation [! _ |- _ !] _ _ _); auto.
  Defined.

  (* TODO: probably doesn’t belong here *)
  Local Definition weaken_context_map
    {Δ Γ : context} (f : context_map Δ Γ) (A : ty_expr Γ)
    (d_Δ : [! |- Δ !])
    (d_A : [! Γ |- A !])
    : context_map (Δ ;; subst_ty f A) (Γ ;; A)
  := (_,, weaken_derivation_map
            f A  d_Δ (derivation_from_context_map f) d_A).

  (* NOTE: if context judgements were abolished from derivations, a “flat”
  hypothesis [ [! |f- Γ !] ] would suffice here. *)
  Definition derivation_idmap_context {Γ : context} (d_Γ : [! |- Γ !]) 
    : [! |- idmap_raw_context Γ ::: Γ ---> Γ !] .
  Proof.
    intros i.
    refine (transportb _ _ _).
    { apply maponpaths_2, subst_idmap_ty. }
    use derive_var; try apply flat_from_context_judgement; auto.
  Defined.

  Definition derivation_comp_raw_context
      {Γ Δ Θ : context }
      (d_Γ : [! |- Γ !])
      {f : raw_context_map Γ Δ} {g : raw_context_map Δ Θ}
      (d_f : [! |- f ::: Γ ---> Δ !])
      (d_g : [! |- g ::: Δ ---> Θ !]) 
    : [! |- comp_raw_context f g ::: Γ ---> Θ !].
  Proof.
    intros i. cbn. unfold comp_raw_context at 2.
    refine (transportb _ _ _).
    { apply maponpaths_2, pathsinv0, subst_subst_ty. }
    refine (subst_derivation [! _ |- _ ::: _ !] _ _ _); auto.
  Defined.
  
  (* TODO: consider naming, organisation *)
  Lemma derivation_idmap_extend_equal_types
      {Γ} (d_Γ : [! |- Γ !])
      {A B} (d_A : [! Γ |- A !]) (d_B : [! Γ |- B !])
      (d_AB : [! Γ |- A === B !])
    : [! |- idmap_raw_context (Γ;;A) ::: Γ;;A ---> Γ;;B !].
  Proof.
    intros i. eapply transportb. { apply maponpaths_2, subst_idmap_ty. }
    pose derive_cxt_extend.
    revert i. use dB_Sn_rect; cbn; intros.
    - refine (derive_tm_conv (_;;_) (rename_ty dB_next A) _ _ _ _ _ _).
      + refine (rename_derivation [! _ |- _ !] _
                                  (dB_next_typed_renaming _ _) _); auto.
      + refine (rename_derivation [! _ |- _ !] _
                                  (dB_next_typed_renaming _ _) _); auto.
      + refine (rename_derivation [! _ |- _ === _ !] _
                                  (dB_next_typed_renaming _ _) _); auto.
      + use (derive_var (_;;_) dB_top); auto.
        refine (rename_derivation [! _ |- _ !] _
                                  (dB_next_typed_renaming _ _) _); auto.
    - refine (derive_var (_;;_) (dB_next i) _ _); auto.
      refine (rename_derivation [! _ |- _ !] _
                                (dB_next_typed_renaming _ _) _); auto.
      apply flat_from_context_judgement; auto.
  Defined.

  (* TODO: consider naming, organisation *)
  Lemma derivation_map_equal_extension
      {Γ} (d_Γ : [! |- Γ !])
      {A B} (d_A : [! Γ |- A !]) (d_B : [! Γ |- B !])
      (d_AB : [! Γ |- A === B !])
      {Δ} {f} (d_f : [! |- f ::: Γ;;B ---> Δ !])
    : [! |- f ::: Γ;;A ---> Δ !].
  Proof.
    pose derive_cxt_extend.
    eapply transportb. { apply pathsinv0, id_left_raw_context. }
    use (@derivation_comp_raw_context _ (Γ;; B));
      auto using weaken_derivation_map.
    apply derivation_idmap_extend_equal_types; auto.
  Defined.

  (* TODO: consider naming, organisation *)
  Lemma derivation_weaken_mapeq
      {Γ Δ : context} (d_Δ : [! |- Δ !])
      {f g : raw_context_map Δ Γ}
      (d_f : [! |- f ::: Δ ---> Γ !])
      (d_fg : [! |- f === g ::: Δ ---> Γ !])
      {A} (d_A : [! Γ |- A !])
    : [! |- weaken_raw_context_map f === weaken_raw_context_map g
                               ::: Δ;; subst_ty f A ---> Γ;; A !].
  Proof.
    pose derive_cxt_extend.
    assert [! Δ |- subst_ty f A !].
    { apply (subst_derivation [! _ |- _ !]); auto. }
    intros i; cbn.
    eapply transportb. { apply maponpaths_3, subst_weaken_rename_ty. }
    revert i; use dB_Sn_rect; cbn.
    - apply derive_tmeq_refl.
      use (derive_var (_;;_) dB_top); auto.
      refine (rename_derivation [! _ |- _ !] _
                                (dB_next_typed_renaming _ _) _); auto.
    - intros i. refine (rename_derivation [! _ |- _ === _ ::: _ !] _
                                (dB_next_typed_renaming _ _) _); auto.
  Defined.

End Compose_Derivations.

Section Substeq_Judgements.

  Definition substeq_judgement
      (J : judgement) {Δ : context}
      (f g : raw_context_map Δ (context_of_judgement J))
    : UU.
  Proof.
    revert f g; destruct J as [ Γ | Γ A | Γ | Γ A a | Γ ]; intros f g.
    - exact unit.
    - exact [! Δ |- subst_ty f A === subst_ty g A !].
    - exact unit.
    - exact [! Δ |- subst_tm f a === subst_tm g a ::: subst_ty f A !].
    - exact unit.
  Defined.

  Definition substeq_derivation
      {J : judgement} (d_J : derivation J)
      {Δ : context} (d_Δ : [! |- Δ !])
      {f g : raw_context_map Δ (context_of_judgement J)}
      (d_f : [! |- f ::: Δ ---> context_of_judgement J !])
      (d_g : [! |- g ::: Δ ---> context_of_judgement J !])
      (d_fg : [! |- f === g ::: Δ ---> context_of_judgement J !])
(* Note: if context judgement is removed from derivations, then this hypothesis
[d_Δ] will probably still be needed (due to use of term-conv rule below), but
as a flat context judgement [ [! |f- Δ !] ]. *)       
    : substeq_judgement J f g.
  Proof.
    pose derive_cxt_extend. (* frequently used by [auto] throughout *)
    revert J d_J Δ f g d_f d_g d_fg d_Δ.
    use derivation_rect_grouped.
    - split; cbn; intros; exact tt. (* context rules *)
    - intro; cbn; auto. (* var rule *)
    - split; cbn; intros; exact tt. (* equiv_rel rules *)
    - split; cbn. (* conv rules *)
      + intros ? ? ? a ? _ ? _ ? _ _ p_a ? f ? ? ? ? ?. 
        apply derive_tmeq_conv with (subst_ty f A).
        * refine (subst_derivation [! _ |- _ !] _ _ _); auto.
        * refine (subst_derivation [! _ |- _ !] _ _ _); auto.
        * refine (subst_derivation [! _ |- _ === _ !] _ _ _); auto.
        * auto.
      + intros; exact tt.
    - split; cbn; intros. (* universe rules *)
      + apply derive_tyeq_refl, derive_U; assumption.
      + apply derive_El_cong; auto.
      + exact tt.
    - split; cbn. (* pi rules *)
      + (* pi-formation *)
        intros. 
        assert [! Δ |- subst_ty f A !].
        { apply (subst_derivation [! _ |- _ !]); auto. }
        assert [! Δ |- subst_ty g A !].
        { apply (subst_derivation [! _ |- _ !]); auto. }
        apply derive_Pi_cong; auto.
        use p_B; auto.
        * auto using weaken_derivation_map.
        * apply derivation_map_equal_extension with (subst_ty g A);
            auto using weaken_derivation_map.
        * apply derivation_weaken_mapeq; auto.
      + (* lambda-abstraction *)
        intros. 
        assert [! Δ |- subst_ty f A !].
        { apply (subst_derivation [! _ |- _ !]); auto. }
        assert [! Δ |- subst_ty g A !].
        { apply (subst_derivation [! _ |- _ !]); auto. }
        apply derive_lam_cong; auto.
        * use p_B; auto.
          -- auto using weaken_derivation_map.
          -- apply derivation_map_equal_extension with (subst_ty g A);
               auto using weaken_derivation_map.
          -- apply derivation_weaken_mapeq; auto.
        * use p_b; auto.
          -- auto using weaken_derivation_map.
          -- apply derivation_map_equal_extension with (subst_ty g A);
               auto using weaken_derivation_map.
          -- apply derivation_weaken_mapeq; auto.
      + (* application *)
        intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? f g ? ? ? ?.
        assert [! Δ |- subst_ty f A !].
        { apply (subst_derivation [! _ |- _ !]); auto. }
        assert [! Δ |- subst_ty g A !].
        { apply (subst_derivation [! _ |- _ !]); auto. }
        eapply transportb.
        { apply maponpaths_3, subst_subst_top_ty. }
        apply derive_app_cong; auto.
        * use p_B; auto.
          -- auto using weaken_derivation_map.
          -- apply derivation_map_equal_extension with (subst_ty g A);
               auto using weaken_derivation_map.
          -- apply derivation_weaken_mapeq; auto.
      + intros; exact tt.
    - split; intros; exact tt. (* pi cong rules *)
  Defined.

End Substeq_Judgements.


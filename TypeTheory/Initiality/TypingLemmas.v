(** In this file, we show admissibility of the substitution rule(s) for derivations, and several other key derivability constructions. *)

Require Import UniMath.MoreFoundations.All.

Require Import TypeTheory.Auxiliary.Auxiliary.

Require Import TypeTheory.Initiality.Syntax.
Require Import TypeTheory.Initiality.SyntaxLemmas.
Require Import TypeTheory.Initiality.Typing.

Local Open Scope judgement_scope.
Local Open Scope context_scope.

(** We will define several “auxiliary judgement forms”, from the basic ones:

- flat contexts and flat context equality, [! |f- Γ !] and [! |f- Γ === Δ !]
- context maps (aka substitutions) and their equality, [! |- f ::: Γ ---> Δ !]
- (stratified) context equality, [! |- Γ === Δ !] (stronger than flat cxt-eq)

Besides these and their basic properties, the main results of this file are:

- admissibility of substitution

*)

Section Flat_Contexts.
  (** The basic context judgement [! |- Γ !] is almost entirely used just for
  one consequence: that all its types are well-typed over it. 

  We call that fact the _flat_ context judgement, written [! |f- Γ !], since
  it discards the _ordering_ or _stratification_ carried by [! |- Γ !].

  We quite happily could (and perhaps should) omit the context judgement
  entirely in the definition of derivations, and then define it as an
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

  (** We would like to prove that the original context judgment implies
  the flat one: *)
  Definition flat_from_context_judgement {Γ : context} 
    : [! |- Γ !] -> [! |f- Γ !].
  Abort.
  (** However, we first need to show admissibility of weakening;
   or, more generally, admissibility of “typed renaming”.

   Specifically, we prove that admissibility as [rename_derivation]
   below, and then prove [flat_from_context_judgement]. *)

  (** Context equality (flat or stratified) is not needed for any directly
  syntactic purposes, but it is required when forming the syntactic category:
  types must be quotiended to form a presheaf, so for context extension to be
  well-defined, contexts must be quotiented as well.

  However, we only need to compare contexts of equal lengths for equality.

  As with the basic context judgement, context equality has both a _flat_ form
  [! |f- Γ === Δ !], and a slightly stronger _stratified_ form [! |- Γ === Δ !].

  Two contexts are flatly equal if they both believe all their types are equal;
  they are stratified-equal if at each stage of construction, they believe this.

  For example, in ETT with reflection, the contexts [ x:N, e:Id(x,0) ] and
  [ x:N, e:Id(0,x) ] would be flatly-equal, since over either of those contexts,
  [ |- Id(0,x) === Id(x,0) ], but not stratified-equal, since over just [ x:N ],
  [ Id(0,x) ] and [ Id(x,0) ] are not judgementally equal.

  As with the main context judgement, flat context equality is simpler and
  suffices for almost all purposes, but the stratified one is needed in defining
  the syntactic category in order for it to be _contextual_, i.e. with each
  context uniquely constructible (up to the chosen equality) from a sequence of
  types (up to judg. eq.). *)
  Definition derivation_cxteq {n} (Γ Δ : context_of_length n) : UU
  :=   (forall i, [! Γ |- Γ i === Δ i !])
     × (forall i, [! Δ |- Δ i === Γ i !])
     × (forall i, [! Γ |- Δ i !])     (* This should not be necessary? *)
     × (forall i, [! Δ |- Γ i !]).     (* This should not be necessary? *)
  (* Note: one direction wouldn’t suffice, for general type theories.
  E.g.  in ETT with the reflection rule, define a predicate [P] over
  [nat] with [ P 0 ] false, and [ P 1 ] true.  Then [ P 0 ] proves
  that [ 0 === 1 : nat ] and hence that [ P 0 === P 1 ], but [ P 1 ]
  doesn’t prove this, so for the contexts [ x0 : P 0 ] and [ x0 : P 1
  ], one direction of the below conditions will hold, but not both. *)
  
  Notation "[! |- Δ === Γ !]" := (derivation_cxteq Δ Γ)
                    (format "[!  |-  Δ  ===  Γ  !]") : judgement_scope.

End Flat_Contexts.

(** Re-declaring notations from section *)
Notation "[! |f- Γ !]" := (derivation_flat_context Γ)
                                (format "[!  |f-  Γ  !]") : judgement_scope.
Notation "[! |- Δ === Γ !]" := (derivation_cxteq Δ Γ)
                    (format "[!  |-  Δ  ===  Γ  !]") : judgement_scope.

Section Context_Maps.

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

End Context_Maps.

(** Re-declaring notations from section *)
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

Section Flat_Contexts_2.

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

End Flat_Contexts_2.

Section Context_Maps_2.

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

End Context_Maps_2.

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
      (J : judgement) (d_J : derivation J)
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

Section Presuppositions.

  Definition presuppositions (J : judgement) : UU.
  Proof.
    destruct J as [ Γ | Γ A | Γ A A' | Γ A a | Γ A a a' ].
    - exact unit.
    - exact unit.
    - exact ( [! Γ |- A !] × [! Γ |- A' !]).
    - exact [! Γ |- A !].
    - exact ( [! Γ |- A !] × [! Γ |- a ::: A !] × [! Γ |- a' ::: A !]).
  Defined.

  (** Note: assumption of (flat) well-formedness of the context is needed
  in order to apply [subst_derivation] for the presuppositions of the
  [pi_app] and [pi_comp] rules. *)
  Definition derive_presuppositions
      (J : judgement) (d_J : derivation J) (d_Γ : [! |f- context_of_judgement J !])
    : presuppositions J.
  Proof.
    revert J d_J d_Γ; use derivation_rect_grouped.
    - (* context rules *)
      split; intros; exact tt.
    - (* var rules *)
      intros Γ i _ _ d_Γi _ _; exact d_Γi. 
    - (* equiv_rel rules *)
      split; try (intros; split; assumption).
      + (* tyeq_sym *)
        intros ? ? ? _ p ?; split; try apply p; assumption. 
      + (* tmeq_refl *)
        intros ? ? ? ? p ?; repeat split; try apply p; assumption. 
      + (* tmeq_sym *)
        intros ? ? ? ? _ p ?; repeat split; try apply p; assumption.
      + (* tmeq_trans *)
        intros ? ? ? ? ? ? p; intros; repeat split; try apply p; assumption.
    - (* conv rules *)
      split; try (intros; assumption).
      (* [tmeq_conv] *)
      intros ? ? ? ? ? _ _ ? _ d_AA' _ _ p d_Γ;
        repeat split;
        try refine (derive_tm_conv _ _ _ _ _ _ d_AA' _);
        try apply p; assumption.
    - (* universe rules *)
      split; try (intros; exact tt).
      (* [El_cong] *)
      intros ? ? ? ? ? ? p ?. split; try apply derive_El; try apply p; assumption.
    - (* pi rules *)
      split.
      + (* pi-form *)
        intros; exact tt.
      + (* pi-lam *)
        intros; apply derive_Pi; assumption.
      + (* pi-app *)
        intros.
        refine (subst_derivation [! _;;_ |- _ !] _ _ _); try assumption.
        admit. (* lemma derive_tm_as_raw_context_map *)
      + (* pi-comp *)
        intros; repeat split.
        * refine (subst_derivation [! _;;_ |- _ !] _ _ _); try assumption.
          admit. (* lemma derive_tm_as_raw_context_map *)
        * auto using derive_app, derive_lam.
        * refine (subst_derivation [! _;;_ |- _ ::: _ !] _ _ _); try assumption.
          admit. (* lemma derive_tm_as_raw_context_map *)
    - (* pi-cong rules *)
      split.
      + (* Pi-cong *)
        intros ? ? ? ? ? ? _ ? _ d_AA' p_AA' _ p_BB' _.
        split; apply derive_Pi; try apply p_BB'; try assumption.
        * apply flat_from_context_judgement, derive_cxt_extend; assumption.
        * apply p_AA', flat_from_context_judgement; assumption.
        * admit. (* respect extension by equal types *)
      + (* lam-cong *)
        intros ? ? ? ? ? ? ? ? _ ? _ d_AA' p_AA' ? p_BB' _ p_bb' _.
        assert [! |f- Γ;;A !].
        { apply flat_from_context_judgement, derive_cxt_extend; assumption. }
        assert [! Γ |- Pi_expr A B !].
        { apply derive_Pi; try apply p_BB'; assumption. }
        repeat split; try assumption.
        * apply derive_lam; try apply p_BB'; try apply p_bb'; assumption.
        * apply (derive_tm_conv _ (Pi_expr A' B')); try assumption.
          -- apply derive_Pi; try assumption.
             apply p_AA', flat_from_context_judgement; assumption.
             admit. (* as in Pi-cong above *)
          -- apply derive_tyeq_sym, derive_Pi_cong; try assumption.
          -- apply derive_lam; try apply p_AA'; try apply p_BB'; try assumption;
               admit.
  Admitted.

End Presuppositions.

Section Flat_Context_Equality.
(** Here we show the key basic properties of flat context equality:

- all hypothetical judgements (basic and auxiliary) respect it;
- it is an equivalence relation
*)

  (* TODO: maybe weaken assumption [e_Γ] (only one direction should be needed). *)
  Lemma derivation_idmap_gen
      {n} {Γ Γ' : context_of_length n}
      (d_Γ : [! |- Γ !]) (d_Γ' : [! |- Γ' !])
      (e_Γ : [! |- Γ === Γ' !])
    : [! |- idmap_raw_context Γ ::: Γ ---> Γ' !].
  Proof.
    intros i.
    unfold idmap_raw_context.
    rewrite subst_idmap_ty.
    apply (@derive_tm_conv Γ (Γ' i) _).
    (* need presuppositions theorem *)
  Admitted.

  (* TODO: rename, clean up, and generalise to other judgement forms *)
  Lemma foo {n} {Γ Δ : context_of_length n} {A : ty_expr n}
    : [! |- Γ !] -> [! |- Δ !] 
    -> [! |- Γ === Δ !] → [! Γ |- A !] → [! Δ |- A !].
  Proof.
    intros d_Γ d_Δ [H1 [H2 [H3 H4]]] ΓA.
    rewrite <- (@subst_idmap_ty _ A).
    apply (@subst_derivation (ty_judgement Γ A) ΓA Δ d_Δ).
    cbn.
    intros i.
    unfold idmap_raw_context.
    rewrite subst_idmap_ty.
    apply (@derive_tm_conv Δ (Δ i) (Γ i)); auto.
    - apply (flat_from_context_judgement d_Δ).
    (* - apply (bar _ _ _ _ (H2 i)). *)
    - apply derive_var.
      + apply d_Δ.
      + apply flat_from_context_judgement, d_Δ.
  Defined.

  Lemma foo2 {n} {Γ Δ : context_of_length n} {A B : ty_expr n}
    : [! |- Γ !] -> [! |- Δ !]
    -> [! |- Γ === Δ !] → [! Γ |- A === B !] → [! Δ |- A === B !].
  Admitted.
  


  (** While the definition of flat context equality works for arbitrary raw
  contexts, the proof that it is an equivalence relation requires requires the
  contexts to be well-formed too. *)
  Lemma derivation_cxteq_refl {Γ : context} (d_Γ : [! |f- Γ !])
    : [! |- Γ === Γ !].
  Proof.
    repeat split; auto using derive_tyeq_refl.
  Qed.

  Lemma derivation_cxteq_sym {n} {Γ Δ : context_of_length n}
    (d_Γ : [! |f- Γ !]) (d_Δ : [! |f- Δ !])
    : [! |- Γ === Δ !] → [! |- Δ === Γ !].
  Proof.
    now intros [H1 [H2 [H3 H4]]].
  Qed.

  (* This is a mess... should be cleaned once the above has been cleaned *)
  Lemma  derivation_cxteq_trans {n} {Γ Δ Θ : context_of_length n}
    : [! |- Γ !] -> [! |- Δ !] -> [! |- Θ !]
    -> [! |- Γ === Δ !] → [! |- Δ === Θ !] → [! |- Γ === Θ !].
  Proof.
    intros d_Γ d_Δ d_Θ H1 H2.
    assert (H3 := derivation_cxteq_sym (flat_from_context_judgement d_Γ)
                                       (flat_from_context_judgement d_Δ) H1).
    assert (H4 := derivation_cxteq_sym (flat_from_context_judgement d_Δ)
                                       (flat_from_context_judgement d_Θ) H2).
    destruct H1 as [H1 [H1' [H1'' H1''']]].
    destruct H2 as [H2 [H2' [H2'' H2''']]].
    destruct H3 as [H3 [H3' [H3'' H3''']]].
    destruct H4 as [H4 [H4' [H4'' H4''']]].
    repeat split; intro i.
    + eapply derive_tyeq_trans; trivial; simpl in *.
      * apply (flat_from_context_judgement d_Γ).
      * apply (foo d_Δ d_Γ (H3,,H3',,H3'',,H3''')); auto.
      * eapply (foo2 d_Δ d_Γ); trivial. apply (H3,,H3',,H3'',,H3''').
    + eapply derive_tyeq_trans; trivial; simpl in *.
      * apply (flat_from_context_judgement d_Θ).
      * apply (foo d_Δ d_Θ (H2,,H2',,H2'',,H2''')); auto.
      * eapply (foo2 d_Δ d_Θ); trivial; apply (H2,,H2',,H2'',,H2''').
    + apply (foo d_Δ d_Γ (H3,,H3',,H3'',,H3''')); auto.
    + apply (foo d_Δ d_Θ (H2,,H2',,H2'',,H2''')); auto.
  Qed.
  
End Flat_Context_Equality.

Section Category_Laws.

  (* TODO: left and right unitality of composition *)

  (* TODO: associativity of composition *)

  Lemma comp_raw_context_cong_l
      {Γ Δ Θ : context} (d_Γ : [! |- Γ !])
      {f f' : raw_context_map Γ Δ}
      (d_f : [! |- f ::: Γ ---> Δ !]) (d_f' : [! |- f' ::: Γ ---> Δ !])
      (e_f : [! |- f === f' ::: Γ ---> Δ !])
      {g : raw_context_map Δ Θ} (d_g : [! |- g ::: Δ ---> Θ !])
    : [! |- comp_raw_context f g === comp_raw_context f' g ::: Γ ---> Θ !].
  Proof.
    intros i; unfold comp_raw_context.
    eapply transportb.
    { apply maponpaths_3, pathsinv0, subst_subst_ty. }
    use (substeq_derivation [! _ |- _ ::: _ !]); auto.
  Defined.

  Lemma comp_raw_context_cong_r
      {Γ Δ Θ : context} (d_Γ : [! |- Γ !])
      {f : raw_context_map Γ Δ} (d_f : [! |- f ::: Γ ---> Δ !])
      {g g' : raw_context_map Δ Θ}
      (e_g : [! |- g === g' ::: Δ ---> Θ !])
    : [! |- comp_raw_context f g === comp_raw_context f g' ::: Γ ---> Θ !].
  Proof.
    intros i; unfold comp_raw_context.
    eapply transportb.
    { apply maponpaths_3, pathsinv0, subst_subst_ty. }
    use (subst_derivation [! _ |- _ === _ ::: _ !]); auto.
  Defined.

End Category_Laws.

Section Split_Typecat_Laws.

  (* TODO: reindexing on types respects equality in both args *)

  (* TODO: functoriality of reindexing on types *)

  (* TODO: dependent projections, and respecting equality *)

End Split_Typecat_Laws.
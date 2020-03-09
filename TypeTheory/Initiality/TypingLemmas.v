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
- (stratified) context equality, [! |f- Γ === Δ !] (stronger than flat cxt-eq)

Besides these and their basic properties, the main results of this file are:

- admissibility of renaming (hence weakening) and substitution
- the presuppositions lemma
- the derivations that will be needed for the syntactic category 
*)

Section Flat_Contexts.
  (** The traditional context judgement [! |- Γ !] is almost entirely used just for
  one consequence: that all its types are well-typed over it. 

  We call that fact the _flat_ context judgement, written [! |f- Γ !], since
  it discards the _ordering_ or _stratification_ carried by [! |- Γ !].

  The only place where the extra “stratification” information carried by
  [! |- Γ !] is needed is in the construction of the _contextual_ syntactic
  category; we therefore leave the definition of [! |- Γ !] until then, and for
  the lemmas of this file, we define and use juse [! |f- Γ !]. *)
  Definition derivation_flat_context (Γ : context) : UU
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

  (** Context equality (flat or stratified) is not needed for any directly
  syntactic purposes, but it is required when forming the syntactic category:
  types must be quotiended to form a presheaf, so for context extension to be
  well-defined, contexts must be quotiented as well.

  However, we only need to compare contexts of equal lengths for equality.

  As with the basic context judgement, context equality has both a _flat_ form
  [! |f- Γ === Δ !], and a slightly stronger _stratified_ form [! |f- Γ === Δ !].

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
  Definition derivation_flat_cxteq {n} (Γ Δ : context_of_length n) : UU
  :=   (forall i, [! Γ |- Γ i === Δ i !])
     × (forall i, [! Δ |- Δ i === Γ i !]).
  (* Note: one direction wouldn’t suffice, for general type theories.
  E.g.  in ETT with the reflection rule, define a predicate [P] over
  [nat] with [ P 0 ] false, and [ P 1 ] true.  Then [ P 0 ] proves
  that [ 0 === 1 : nat ] and hence that [ P 0 === P 1 ], but [ P 1 ]
  doesn’t prove this, so for the contexts [ x0 : P 0 ] and [ x0 : P 1 ],
  one direction of the given conditions will hold, but not both. *)
  
  Notation "[! |f- Δ === Γ !]" := (derivation_flat_cxteq Δ Γ)
                    (format "[!  |f-  Δ  ===  Γ  !]") : judgement_scope.

End Flat_Contexts.

(** Re-declaring notations from section *)
Notation "[! |f- Γ !]" := (derivation_flat_context Γ)
                                (format "[!  |f-  Γ  !]") : judgement_scope.
Notation "[! |f- Δ === Γ !]" := (derivation_flat_cxteq Δ Γ)
                    (format "[!  |f-  Δ  ===  Γ  !]") : judgement_scope.

Section Context_Maps.

  Definition derivation_map
      (Δ Γ : context) (f : raw_context_map Δ Γ) : UU
  := forall i:Γ, [! Δ |- f i ::: subst_ty f (Γ i) !].

  Identity Coercion id_derivation_map : derivation_map >-> Funclass.

  Notation "[! |- f ::: Δ ---> Γ !]" := (derivation_map Δ Γ f)
                    (format "[! |- f ::: Δ ---> Γ !]") : judgement_scope.


  (** As with [ [! |f- Γ !] ], the actual key lemmas about
  [ [! |- f ::: Δ -> Γ !] ] can’t be given until after admissibility of
  weakening, [rename_derivation]. *)

  (* TODO: probably move this to [SyntacticCategory]. *)
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
    destruct J as [ Γ A | Γ A A' | Γ A a | Γ A a a' ]; intros f.
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
    : derivation (rename_judgement J f).
  Proof.
    revert J d_J Δ f.
    use derivation_rect_grouped.
    - (* var rule *)
      intros Γ; cbn; intros i d_Γi IH_Γi Δ f.
      specialize (IH_Γi Δ f). 
      set (e := typed_renaming_commutes f i). destruct e.
      apply derive_var; assumption.
    - split. (* equiv_rel_rules *)
      + intros. apply derive_tyeq_refl; eauto. 
      + intros. apply derive_tyeq_sym; eauto.
      + intros ? ? A1 ? ? ? ? ? ? ? ? ? ? ? ? f.
        apply derive_tyeq_trans with (rename_ty f A1); eauto.
      + intros. apply derive_tmeq_refl; eauto.
      + intros. apply derive_tmeq_sym; eauto.
      + intros ? ? ? a1 ? ? ? ? ? ? ? ? ? ? ? ? f.
        apply derive_tmeq_trans with (rename_tm f a1); eauto.
    - split. (* conv rules *)
      + intros ? A ? ? ? ? ? ? ? ? ? ? ? f.
        apply derive_tm_conv with (rename_ty f A); eauto.
      + intros ? A ? ? ? ? ? ? ? ? ? ? ? ? f.
        apply derive_tmeq_conv with (rename_ty f A); eauto.
    - split. (* universe rules *)
      + intros; apply derive_U; auto.
      + intros; apply derive_El; eauto.
      + intros; apply derive_El_cong; eauto.
    - split. (* Pi rules *)
      + cbn. intros; apply derive_Pi; auto.
        refine (p_B _ (weaken_typed_renaming _ _)).
      + cbn. intros; apply derive_lam; auto;
        set (fA := weaken_typed_renaming f A).
        * refine (p_B _ fA).
        * refine (p_b _ fA).        
      + cbn. intros ? A ? ? ? ? ? ? p_B ? ? ? ? ? f.
        refine (transportb _ _ _). 
        { eapply maponpaths_2, rename_subst_top_ty. }
        apply derive_app; eauto.
        refine (p_B _ (weaken_typed_renaming f A)).
      + cbn. intros ? A ? ? ? ? ? ? p_B ? p_b ? ? ? f.
        refine (transportb _ _ _). 
        { eapply maponpaths_13. 
          - apply rename_subst_top_ty.
          - apply rename_subst_top_tm. }
        apply derive_beta; eauto.
        * refine (p_B _ (weaken_typed_renaming f A)).
        * refine (p_b _ (weaken_typed_renaming f A)).
    - split. (* congruences for pi-constructors *)
      + cbn. intros ? A ? ? ? ? ? ? ? ? p_BB ? f.
        apply derive_Pi_cong; auto.
        refine (p_BB _ (weaken_typed_renaming _ _)).
      + cbn. intros ? A ? ? ? ? ? ? ? ? ? ? p_BB ? p_bb ? f.
        apply derive_lam_cong; auto.
        * refine (p_BB _ (weaken_typed_renaming _ _)).
        * refine (p_bb _ (weaken_typed_renaming _ _)).
      + cbn. intros ? A ? ? ? ? ? ? ? ? ? ? ? ? p_BB ? ? ? ? ? f.
        refine (transportb _ _ _). 
        { eapply maponpaths_3, rename_subst_top_ty. }
        apply derive_app_cong; auto.
        refine (p_BB _ (weaken_typed_renaming _ _)).
  Defined.

End Renaming_Judgements.

(** With [rename_derivation], we can prove the basic lemmas about flat contexts
and context maps. *)

Section Flat_Contexts_2.

  Definition derive_flat_extend_context {Γ : context} {A : ty_expr Γ}
    : [! |f- Γ !] -> [! Γ |- A !] -> [! |f- Γ;;A !].
  Proof.
    cbn; intros d_Γ d_A i; cbn.
    refine (rename_derivation [! _ |- _ !] _
                                    (dB_next_typed_renaming _ _));
        cbn.
    revert i; use dB_Sn_rect; auto. 
  Defined.

End Flat_Contexts_2.

Section Context_Maps_2.

  (* TODO: rename [add_to_raw_context_map] to [extend…] upstream *)
  Lemma derive_extend_context_map
      {Γ Δ : context}
      {f : raw_context_map Δ Γ} (d_f : [! |- f ::: Δ ---> Γ !])
      {A} {a} (d_a : [! Δ |- a ::: subst_ty f A !])
    : [! |- add_to_raw_context_map f a ::: Δ ---> Γ;;A !].
  Proof.
    intros i; cbn.
    eapply transportb.
    { apply maponpaths_2.
      eapply pathscomp0. { apply subst_rename_ty. }
      apply maponpaths_2. exact (idpath f). }
    destruct i as [ | i]; cbn.
    - apply d_a.
    - apply d_f.
  Defined.

  (** The eventual [derive_weaken_map] shouldn’t need the
   hypothesis [ [! Δ |- subst_ty f A !] ]. However, that requires admissibility
   of substitution, which in turn uses this preliminary version. *)
  Local Definition derive_weaken_map_prelim
      {Δ Γ : context} (f : raw_context_map Δ Γ) (A : ty_expr Γ)
    :    [! |- f ::: Δ ---> Γ !]
      -> [! Δ |- subst_ty f A !]
      -> [! |- weaken_raw_context_map f ::: Δ ;; subst_ty f A ---> Γ ;; A !].
  Proof.
    intros d_f d_fA i.
    eapply transportb.
    { apply maponpaths_2.
      eapply pathscomp0. { use subst_rename_ty. } 
      apply pathsinv0. use rename_subst_ty. }
    destruct i as [ | i]; cbn.
    - refine (derive_var (_;;_) dB_top _).
      refine (rename_derivation [! _ |- _ !] _ (dB_next_typed_renaming _ _));
        auto.
    - refine (rename_derivation [! _ |- _ ::: _ !] _
                                           (dB_next_typed_renaming _ _)); auto.
  Defined.

End Context_Maps_2.

Section Substitute_Derivations.

  Definition subst_judgement
      (J : judgement) {Δ : context} 
    : raw_context_map Δ (context_of_judgement J)
    -> judgement.
  Proof.
    destruct J as [ Γ A | Γ A A' | Γ A a | Γ A a a' ]; intros f.
    - exact [! Δ |- subst_ty f A !].
    - exact [! Δ |- subst_ty f A === subst_ty f A' !].
    - exact [! Δ |- subst_tm f a ::: subst_ty f A !].
    - exact [! Δ |- subst_tm f a === subst_tm f a' ::: subst_ty f A !].
  Defined.

  Definition subst_derivation
      (J : judgement) (d_J : derivation J)
      {Δ : context} {f : raw_context_map Δ (context_of_judgement J)}
      (d_f : [! |- f ::: Δ ---> context_of_judgement J !])
    : derivation (subst_judgement J f).
  Proof.
    revert J d_J Δ f d_f.
    use derivation_rect_grouped.
    - (* var rule *)
      intros Γ; cbn; intros i d_Γi IH_Γi Δ f d_f.
      specialize (IH_Γi Δ f d_f). 
      apply d_f.
    - split. (* equiv_rel_rules *)
      + intros. apply derive_tyeq_refl; eauto. 
      + intros. apply derive_tyeq_sym; eauto.
      + intros ? ? A1 ? ? ? ? ? ? ? ? ? ? ? ? f ?.
        apply derive_tyeq_trans with (subst_ty f A1); eauto.
      + intros. apply derive_tmeq_refl; eauto.
      + intros. apply derive_tmeq_sym; eauto.
      + intros ? ? ? a1 ? ? ? ? ? ? ? ? ? ? ? ? f ?.
        apply derive_tmeq_trans with (subst_tm f a1); eauto.
    - split. (* conv rules *)
      + intros ? A ? ? ? ? ? ? ? ? ? ? ? f ?.
        apply derive_tm_conv with (subst_ty f A); eauto.
      + intros ? A ? ? ? ? ? ? ? ? ? ? ? ? f ?.
        apply derive_tmeq_conv with (subst_ty f A); eauto.
    - split. (* universe rules *)
      + intros; apply derive_U; auto.
      + intros; apply derive_El; eauto.
      + intros; apply derive_El_cong; eauto.
    - split. (* Pi rules *)
      + cbn. intros; apply derive_Pi; auto.
        refine (p_B _ _ _); auto using derive_weaken_map_prelim.
      + cbn. intros; apply derive_lam; auto.
        * refine (p_B _ _ _); auto using derive_weaken_map_prelim.
        * refine (p_b _ _ _); auto using derive_weaken_map_prelim.
      + cbn. intros ? A ? ? ? ? ? ? p_B ? ? ? ? ? f ?.
        refine (transportb _ _ _). 
        { eapply maponpaths_2, subst_subst_top_ty. }
        apply derive_app; eauto.
        refine (p_B _ _ _); auto using derive_weaken_map_prelim.
      + cbn. intros ? A ? ? ? ? ? ? p_B ? p_b ? ? ? f ?.
        refine (transportb _ _ _). 
        { eapply maponpaths_13. 
          - apply subst_subst_top_ty.
          - apply subst_subst_top_tm. }
        apply derive_beta; eauto.
        * refine (p_B _ _ _); auto using derive_weaken_map_prelim.
        * refine (p_b _ _ _); auto using derive_weaken_map_prelim.
    - split. (* congruences for pi-constructors *)
      + cbn. intros ? A ? ? ? ? ? ? ? ? p_BB ? f ?.
        apply derive_Pi_cong; auto.
        refine (p_BB _ _ _); auto using derive_weaken_map_prelim.
      + cbn. intros ? A ? ? ? ? ? ? ? ? ? ? p_BB ? p_bb ? f ?.
        apply derive_lam_cong; auto.
        * refine (p_BB _ _ _); auto using derive_weaken_map_prelim.
        * refine (p_bb _ _ _); auto using derive_weaken_map_prelim.
      + cbn. intros ? A ? ? ? ? ? ? ? ? ? ? ? ? p_BB ? ? ? ? ? f ?.
        refine (transportb _ _ _). 
        { eapply maponpaths_3, subst_subst_top_ty. }
        apply derive_app_cong; auto.
        refine (p_BB _ _ _); auto using derive_weaken_map_prelim.
  Defined.

End Substitute_Derivations.

Section Misc.

  Definition derive_idmap {Γ : context} (d_Γ : [! |f- Γ !]) 
    : [! |- idmap_raw_context Γ ::: Γ ---> Γ !] .
  Proof.
    intros i.
    refine (transportb _ _ _).
    { apply maponpaths_2, subst_idmap_ty. }
    use derive_var; auto.
  Defined.

  Lemma derive_tm_as_raw_context_map {Γ : context} (d_Γ : [! |f- Γ !])
       {A} {a} (d_a : [! Γ |- a ::: A !])
    : [! |- tm_as_raw_context_map a ::: Γ ---> Γ;;A !].
  Proof.
    apply derive_extend_context_map.
    - apply derive_idmap; assumption.
    - eapply transportb. { apply maponpaths_2, subst_idmap_ty. }
      assumption.
  Defined.

  Definition derive_weaken_map
      {Δ Γ : context} (f : raw_context_map Δ Γ) (A : ty_expr Γ)
    : [! |- f ::: Δ ---> Γ !]
      -> [! Γ |- A !]
      -> [! |- weaken_raw_context_map f ::: Δ ;; subst_ty f A ---> Γ ;; A !].
  Proof.
    intros; apply derive_weaken_map_prelim; auto.
    refine (subst_derivation [! _ |- _ !] _ _); auto.
  Defined.

  (* TODO: probably doesn’t belong here *)
  Local Definition weaken_context_map
    {Δ Γ : context} (f : context_map Δ Γ) (A : ty_expr Γ)
    (d_A : [! Γ |- A !])
    : context_map (Δ ;; subst_ty f A) (Γ ;; A)
  := (_,, derive_weaken_map f A (derivation_from_context_map f) d_A).

  Definition derive_comp
      {Γ Δ Θ : context }
      {f : raw_context_map Γ Δ} {g : raw_context_map Δ Θ}
      (d_f : [! |- f ::: Γ ---> Δ !])
      (d_g : [! |- g ::: Δ ---> Θ !]) 
    : [! |- comp_raw_context f g ::: Γ ---> Θ !].
  Proof.
    intros i. cbn. unfold comp_raw_context at 2.
    refine (transportb _ _ _).
    { apply maponpaths_2, pathsinv0, subst_subst_ty. }
    refine (subst_derivation [! _ |- _ ::: _ !] _ _); auto.
  Defined.
  
  (* TODO: consider naming, organisation *)
  (* TODO: could make more sense to replace this by a pair of lemmas:
  - the _weakenings_ of a context map by equal types are equal;
  - a weakening of idmap is syntactically equal to idmap
  which together suffice for the iterated version of this, needed if we
  had constructors binding more than one variable. *) 
  Lemma derive_idmap_extend_equal_types
      {Γ} (d_Γ : [! |f- Γ !])
      {A B} (d_A : [! Γ |- A !]) (d_B : [! Γ |- B !])
      (d_AB : [! Γ |- A === B !])
    : [! |- idmap_raw_context (Γ;;A) ::: Γ;;A ---> Γ;;B !].
  Proof.
    intros i. eapply transportb. { apply maponpaths_2, subst_idmap_ty. }
    revert i. use dB_Sn_rect; cbn; intros.
    - refine (derive_tm_conv (_;;_) (rename_ty dB_next A) _ _ _ _ _ _).
      + refine (rename_derivation [! _ |- _ !] _
                                  (dB_next_typed_renaming _ _)); auto.
      + refine (rename_derivation [! _ |- _ !] _
                                  (dB_next_typed_renaming _ _)); auto.
      + refine (rename_derivation [! _ |- _ === _ !] _
                                  (dB_next_typed_renaming _ _)); auto.
      + use (derive_var (_;;_) dB_top); auto.
        refine (rename_derivation [! _ |- _ !] _
                                  (dB_next_typed_renaming _ _)); auto.
    - refine (derive_var (_;;_) (dB_next i) _); auto.
      refine (rename_derivation [! _ |- _ !] _
                                (dB_next_typed_renaming _ _)); cbn; auto.
  Defined.

  (* TODO: consider naming, organisation *)
  Lemma derive_map_equal_extension
      {Γ} (d_Γ : [! |f- Γ !])
      {A B} (d_A : [! Γ |- A !]) (d_B : [! Γ |- B !])
      (d_AB : [! Γ |- A === B !])
      {Δ} {f} (d_f : [! |- f ::: Γ;;B ---> Δ !])
    : [! |- f ::: Γ;;A ---> Δ !].
  Proof.
    eapply transportb. { apply pathsinv0, id_left_raw_context. }
    use (@derive_comp _ (Γ;; B));
      auto using derive_weaken_map.
    apply derive_idmap_extend_equal_types; auto.
  Defined.

  (* TODO: consider naming, organisation *)
  Lemma derive_weaken_mapeq
      {Γ Δ : context} (d_Δ : [! |f- Δ !])
      {f g : raw_context_map Δ Γ}
      (d_f : [! |- f ::: Δ ---> Γ !])
      (d_fg : [! |- f === g ::: Δ ---> Γ !])
      {A} (d_A : [! Γ |- A !])
    : [! |- weaken_raw_context_map f === weaken_raw_context_map g
                               ::: Δ;; subst_ty f A ---> Γ;; A !].
  Proof.
    assert [! Δ |- subst_ty f A !].
    { apply (subst_derivation [! _ |- _ !]); auto. }
    intros i; cbn.
    eapply transportb. { apply maponpaths_3, subst_weaken_rename_ty. }
    revert i; use dB_Sn_rect; cbn.
    - apply derive_tmeq_refl.
      use (derive_var (_;;_) dB_top); auto.
      refine (rename_derivation [! _ |- _ !] _
                                (dB_next_typed_renaming _ _)); auto.
    - intros i. refine (rename_derivation [! _ |- _ === _ ::: _ !] _
                                (dB_next_typed_renaming _ _)); auto.
  Defined.

End Misc.

Section CxtEq_Conv.
(** Here we will show that _stratified_-equal contexts carry the same
    judgements. *)

(* TODO: find better naming conventions *)
(* TODO: define stratified context equality, and rephrase section in terms of that? *)

  Lemma derive_ty_conv_extend_equal_types
      {Γ} (d_Γ : [! |f- Γ !])
      {A A'} (d_A : [! Γ |- A !]) (d_A' : [! Γ |- A' !])
      (d_AA' : [! Γ |- A === A' !])
      {B}
    : [! Γ ;; A |- B !] -> [! Γ ;; A' |- B !].
  Proof.
    intros d_B.
    eapply transportf. { apply maponpaths, subst_idmap_ty. }
    refine (subst_derivation _ d_B _);
      eauto using derive_tyeq_sym, derive_idmap_extend_equal_types.
  Defined.

  Lemma derive_tm_conv_extend_equal_types
      {Γ} (d_Γ : [! |f- Γ !])
      {A A'} (d_A : [! Γ |- A !]) (d_A' : [! Γ |- A' !])
      (d_AA' : [! Γ |- A === A' !])
      {B} {b}
    : [! Γ ;; A |- b ::: B !] -> [! Γ ;; A' |- b ::: B !].
  Proof.
    intros d_b.
    eapply transportf.
    { apply maponpaths_12; [ apply subst_idmap_ty | apply subst_idmap_tm ]. }
    refine (subst_derivation _ d_b _);
      eauto using derive_tyeq_sym, derive_idmap_extend_equal_types.
  Defined.

End CxtEq_Conv.

Section Substeq_Judgements.

  Definition substeq_judgement
      (J : judgement) {Δ : context}
      (f g : raw_context_map Δ (context_of_judgement J))
    : UU.
  Proof.
    revert f g; destruct J as [ Γ A | Γ | Γ A a | Γ ]; intros f g.
    - exact [! Δ |- subst_ty f A === subst_ty g A !].
    - exact unit.
    - exact [! Δ |- subst_tm f a === subst_tm g a ::: subst_ty f A !].
    - exact unit.
  Defined.

(* Note: think hard about whether the hypothesis [! |f- Δ !] is really necessary for this, or whether it could be eliminated. *)       
  Definition substeq_derivation
      (J : judgement) (d_J : derivation J)
      {Δ : context} (d_Δ : [! |f- Δ !])
      {f g : raw_context_map Δ (context_of_judgement J)}
      (d_f : [! |- f ::: Δ ---> context_of_judgement J !])
      (d_g : [! |- g ::: Δ ---> context_of_judgement J !])
      (d_fg : [! |- f === g ::: Δ ---> context_of_judgement J !])
    : substeq_judgement J f g.
  Proof.
    pose @derive_flat_extend_context. (* frequently used by [auto] below *)
    revert J d_J Δ f g d_f d_g d_fg d_Δ.
    use derivation_rect_grouped.
    - intro; cbn; auto. (* var rule *)
    - split; cbn; intros; exact tt. (* equiv_rel rules *)
    - split; cbn. (* conv rules *)
      + intros ? ? ? a ? _ ? _ ? _ _ p_a ? f ? ? ? ? ?. 
        apply derive_tmeq_conv with (subst_ty f A).
        * refine (subst_derivation [! _ |- _ !] _ _); auto.
        * refine (subst_derivation [! _ |- _ !] _ _); auto.
        * refine (subst_derivation [! _ |- _ === _ !] _ _); auto.
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
        * auto using derive_weaken_map.
        * apply derive_map_equal_extension with (subst_ty g A);
            auto using derive_weaken_map.
        * apply derive_weaken_mapeq; auto.
      + (* lambda-abstraction *)
        intros. 
        assert [! Δ |- subst_ty f A !].
        { apply (subst_derivation [! _ |- _ !]); auto. }
        assert [! Δ |- subst_ty g A !].
        { apply (subst_derivation [! _ |- _ !]); auto. }
        apply derive_lam_cong; auto.
        * use p_B; auto.
          -- auto using derive_weaken_map.
          -- apply derive_map_equal_extension with (subst_ty g A);
               auto using derive_weaken_map.
          -- apply derive_weaken_mapeq; auto.
        * use p_b; auto.
          -- auto using derive_weaken_map.
          -- apply derive_map_equal_extension with (subst_ty g A);
               auto using derive_weaken_map.
          -- apply derive_weaken_mapeq; auto.
      + (* application *)
        intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? f g ? ? ? ?.
        assert [! Δ |- subst_ty f A !].
        { apply (subst_derivation [! _ |- _ !]); auto. }
        assert [! Δ |- subst_ty g A !].
        { apply (subst_derivation [! _ |- _ !]); auto. }
        eapply transportb.
        { apply maponpaths_3, subst_subst_top_ty. }
        apply derive_app_cong; auto.
        * use p_B; auto.
          -- auto using derive_weaken_map.
          -- apply derive_map_equal_extension with (subst_ty g A);
               auto using derive_weaken_map.
          -- apply derive_weaken_mapeq; auto.
      + intros; exact tt.
    - split; intros; exact tt. (* pi cong rules *)
  Defined.

End Substeq_Judgements.

Section Misc_2.
(* TODO: think about where these lemmas really belong *)
(* Note: the assumption [! |f- Γ !] really shouldn’t be necessary throughout;
think about how to eliminate it. *)

  Lemma derive_subst_top_ty {Γ : context} (d_Γ : [! |f- Γ !])
       {A} {a} (d_a : [! Γ |- a ::: A !])
       {B} (d_B : [! Γ;;A |- B !] )
    : [! Γ |- subst_top_ty a B !].
  Proof.
    apply (subst_derivation [! _;;_ |- _ !]); try assumption.
    apply derive_tm_as_raw_context_map; assumption.
  Defined.

  Lemma derive_subst_top_tyeq {Γ : context} (d_Γ : [! |f- Γ !])
       {A} {a} (d_a : [! Γ |- a ::: A !])
       {B B'} (d_BB' : [! Γ;;A |- B === B' !] )
    : [! Γ |- subst_top_ty a B === subst_top_ty a B' !].
  Proof.
    apply (subst_derivation [! _;;_ |- _ === _ !]); try assumption.
    apply derive_tm_as_raw_context_map; assumption.
  Defined.

  Lemma derive_subst_top_tm {Γ : context} (d_Γ : [! |f- Γ !])
       {A} {a} (d_a : [! Γ |- a ::: A !])
       {B} {b} (d_d : [! Γ;;A |- b ::: B !] )
    : [! Γ |- subst_top_tm a b ::: subst_top_ty a B !].
  Proof.
    apply (subst_derivation [! _;;_ |- _ ::: _ !]); try assumption.
    apply derive_tm_as_raw_context_map; assumption.
  Defined.

  Lemma derive_subst_top_tmeq {Γ : context} (d_Γ : [! |f- Γ !])
       {A} {a} (d_a : [! Γ |- a ::: A !])
       {B} {b b'} (d_bb' : [! Γ;;A |- b === b' ::: B !] )
    : [! Γ |- subst_top_tm a b === subst_top_tm a b' ::: subst_top_ty a B !].
  Proof.
    apply (subst_derivation [! _;;_ |- _ === _ ::: _ !]); try assumption.
    apply derive_tm_as_raw_context_map; assumption.
  Defined.

  Lemma derive_substeq_top_ty {Γ : context} (d_Γ : [! |f- Γ !])
       {A} (d_A : [! Γ |- A !])
       {a} (d_a : [! Γ |- a ::: A !]) {a'} (d_a' : [! Γ |- a' ::: A !])
       (d_aa' : [! Γ |- a === a' ::: A !])
       {B} (d_B : [! Γ;;A |- B !] )
    : [! Γ |- subst_top_ty a B === subst_top_ty a' B !].
  Proof.
    apply (substeq_derivation [! _;;_ |- _ !]);
    try apply derive_tm_as_raw_context_map; try assumption.
    (* TODO: perhaps abstract following as lemma, [tmeq_as_context_mapeq]? *)
    intros [ | i]; cbn.
    - refine (transportb _ _ d_aa'). apply maponpaths_3.
      eapply pathscomp0. { apply subst_rename_ty. }
      apply subst_idmap_ty.
    - eapply transportb.
      { apply maponpaths_3.
        eapply pathscomp0. { apply subst_rename_ty. }
        apply subst_idmap_ty. }
      apply derive_tmeq_refl, derive_var; auto.
  Defined.

End Misc_2.

Section Presuppositions.

  Definition presuppositions (J : judgement) : UU.
  Proof.
    destruct J as [ Γ A | Γ A A' | Γ A a | Γ A a a' ].
    - exact unit.
    - exact ( [! Γ |- A !] × [! Γ |- A' !]).
    - exact [! Γ |- A !].
    - exact ( [! Γ |- A !] × [! Γ |- a ::: A !] × [! Γ |- a' ::: A !]).
  Defined.

  (** Note: assumption of (flat) well-formedness of the context is needed
  in order to apply [subst_derivation] for the presuppositions of the
  [pi_app] and [pi_comp] rules. 

   This shouldn’t really be necessary!  Think about how it can be eliminated. *)
  Definition derive_presuppositions
      (J : judgement) (d_J : derivation J)
      (d_Γ : [! |f- context_of_judgement J !])
    : presuppositions J.
  Proof.
    revert J d_J d_Γ; use derivation_rect_grouped.
    - (* var rules *)
      intros ? ? d_Γi _ _; exact d_Γi. 
    - (* equiv_rel rules *)
      split; try (intros; repeat split; assumption).
      + (* tyeq_sym *)
        intros ? ? ? _ p ?; split; try apply p; assumption. 
      + (* tmeq_refl *)
        intros ? ? ? ? p ?; repeat split; try apply p; assumption.
      + (* tmeq_sym *)
        intros ? ? ? ? _ p ?; repeat split; try apply p; assumption.
      + (* tmeq_trans *)
        intros ? ? ? ? ? ? p _ _ ? _ _ _ _ _ ?;
               repeat split; try apply p; assumption.
    - (* conv rules *)
      split; try (intros; assumption).
      (* [tmeq_conv] *)
      intros ? ? ? ? ? _ _ ? _ d_AA' _ _ p ?; repeat split;
        try refine (derive_tm_conv _ _ _ _ _ _ d_AA' _);
        try apply p; assumption.
    - (* universe rules *)
      split; try (intros; exact tt).
      (* [El_cong] *)
      intros ? ? ? ? p ?.
      split; try apply derive_El; try apply p; assumption.
    - (* pi rules *)
      split.
      + (* pi-form *)
        intros; exact tt.
      + (* pi-lam *)
        intros; apply derive_Pi; assumption.
      + (* pi-app *)
        intros. apply derive_subst_top_ty; auto.
      + (* pi-comp *)
        intros; repeat split.
        * apply derive_subst_top_ty; assumption.
        * auto using derive_app, derive_lam.
        * apply derive_subst_top_tm; assumption.
    - (* pi-cong rules *)
      split.
      + (* Pi-cong *)
        intros ? ? ? ? ? ? _ d_AA' p_AA' _ p_BB' ?.
        assert [! |f- Γ;;A !] as d_ΓA.
        { apply derive_flat_extend_context; assumption. }
        destruct (p_AA' d_Γ) as [? ?], (p_BB' d_ΓA) as [? ?].
        split; apply derive_Pi; try assumption.
        use derive_ty_conv_extend_equal_types; assumption.
      + (* lam-cong *)
        intros ? ? ? ? ? ? ? ? _ d_AA' p_AA' ? p_BB' _ p_bb' d_Γ.
        assert [! |f- Γ;;A !] as d_ΓA.
        { apply derive_flat_extend_context; assumption. }
        destruct (p_AA' d_Γ) as [? ?], (p_BB' d_ΓA) as [? ?],
                                       (p_bb' d_ΓA) as [? [? ?]].
        assert [! Γ |- Pi_expr A B !]. { apply derive_Pi; assumption. }
        repeat split; try apply derive_lam; try assumption.
        * apply (derive_tm_conv _ (Pi_expr A' B')); try assumption.
          -- apply derive_Pi; try assumption.
             use derive_ty_conv_extend_equal_types; assumption.
          -- apply derive_tyeq_sym, derive_Pi_cong; try assumption.
          -- apply derive_lam; auto.
            ++ use derive_ty_conv_extend_equal_types; assumption.
            ++ use derive_tm_conv_extend_equal_types;
               try apply (derive_tm_conv _ B); assumption.
      + (* app-cong *)
        intros ? ? ? ? ? ? ? ? ? ? _ ? p_AA' ? p_BB' _ p_tt' ? p_aa' d_Γ.
        assert [! |f- Γ;;A !] as d_ΓA.
        { apply derive_flat_extend_context; assumption. }
        destruct (p_AA' d_Γ) as [? ?], (p_BB' d_ΓA) as [? ?],
                 (p_tt' d_Γ) as [? [? ?]], (p_aa' d_Γ) as [? [? ?]].
        assert [! Γ |- Pi_expr A B !]. { apply derive_Pi; assumption. }
        assert [! Γ;;A' |- B' !].
        { use derive_ty_conv_extend_equal_types; assumption. }
        assert [! Γ |- Pi_expr A' B' !]. { apply derive_Pi; assumption. }
        repeat split;
          [ apply derive_subst_top_ty; assumption
          | apply derive_app; assumption | ].
        apply (derive_tm_conv _ (subst_top_ty a' B'));
          try apply derive_subst_top_ty; try assumption.
        * apply derive_tyeq_sym, (derive_tyeq_trans _ _ (subst_top_ty a B'));
            try apply derive_subst_top_ty; try assumption.
          -- apply derive_subst_top_tyeq; assumption.
          -- apply derive_substeq_top_ty; assumption.
        * apply derive_app; try assumption.
          -- apply (derive_tm_conv _ (Pi_expr A B));
               try apply derive_Pi_cong; assumption.
          -- apply (derive_tm_conv _ A); assumption.
  Defined.

End Presuppositions.

Section Flat_Context_Equality.
(** Here we show the key basic properties of flat context equality:

- all hypothetical judgements (basic and auxiliary) respect it;
- it is an equivalence relation
*)

  (** When two contexts are (flatly) equal, the “identity” map forms a context
   map between them *)
  (* TODO: maybe weaken assumption [e_Γ] (only one direction is really needed). *)
  Lemma derive_idmap_gen
      {n} {Γ Γ' : context_of_length n}
      (d_Γ' : [! |f- Γ' !])
      (e_Γ : [! |f- Γ === Γ' !])
    : [! |- idmap_raw_context Γ ::: Γ' ---> Γ !].
  Proof.
    intros i.
    eapply transportb. { apply maponpaths_2, subst_idmap_ty. }
    pose (e_Γi := pr2 e_Γ i).
    destruct (derive_presuppositions _ e_Γi); try assumption. 
    apply (derive_tm_conv Γ' (Γ' i)); try assumption.
    use derive_var; assumption.
  Defined.

  (** By substituting along this “identity” map between equal contexts,
  we get that when two contexts are equal, the same judgements are derivable
  over them. *)

  Lemma derive_ty_conv_cxteq
      {n} Γ {Δ : context_of_length n}
      (d_Δ : [! |f- Δ !]) (d_ΓΔ : [! |f- Γ === Δ !])
      {A : ty_expr n} (d_A : [! Γ |- A !])
    : [! Δ |- A !].
  Proof.
    rewrite <- (@subst_idmap_ty _ A).
    use (subst_derivation [! Γ |- A !]); try assumption.
    apply derive_idmap_gen; assumption.
  Defined.

  Lemma derive_tyeq_conv_cxteq
      {n} {Γ Δ : context_of_length n}
      (d_Δ : [! |f- Δ !]) (d_ΓΔ : [! |f- Γ === Δ !])
      {A B : ty_expr n} (d_AB : [! Γ |- A === B !])
    : [! Δ |- A === B !].
  Proof.
    intros.
    rewrite <- (@subst_idmap_ty _ A), <- (@subst_idmap_ty _ B).
    use (subst_derivation [! Γ |- A === B !]); try assumption.
    apply derive_idmap_gen; assumption.
  Defined.

  Lemma derive_tm_conv_cxteq
      {n} {Γ Δ : context_of_length n}
      (d_Δ : [! |f- Δ !]) (d_ΓΔ : [! |f- Γ === Δ !])
      {A : ty_expr n} {a : tm_expr n} (d_a : [! Γ |- a ::: A !])
    : [! Δ |- a ::: A !].
  Proof.
    rewrite <- (@subst_idmap_ty _ A), <- (@subst_idmap_tm _ a).
    use (subst_derivation [! Γ |- a ::: A !]); try assumption.
    apply derive_idmap_gen; assumption.
  Defined.

  Lemma derive_tmeq_conv_cxteq
      {n} {Γ Δ : context_of_length n}
      (d_Δ : [! |f- Δ !]) (d_ΓΔ : [! |f- Γ === Δ !])
      {A : ty_expr n} {a a' : tm_expr n} (d_aa' : [! Γ |- a === a' ::: A !])
    : [! Δ |- a === a' ::: A !].
  Proof.
    rewrite <- (@subst_idmap_ty _ A),
            <- (@subst_idmap_tm _ a), <- (@subst_idmap_tm _ a').
    use (subst_derivation [! Γ |- a === a' ::: A !]); try assumption.
    apply derive_idmap_gen; assumption.
  Defined.

  Arguments derive_ty_conv_cxteq [_] _ [_] _ _ [_] _.
  Arguments derive_tyeq_conv_cxteq [_] _ [_] _ _ [_ _] _.
  Arguments derive_tm_conv_cxteq [_] _ [_] _ _ [_ _] _.
  Arguments derive_tmeq_conv_cxteq [_] _ [_] _ _ [_ _ _] _.

  (** We can now show that flat context equality is an equivalence relation. *)
  Lemma derive_flat_cxteq_refl {Γ : context} (d_Γ : [! |f- Γ !])
    : [! |f- Γ === Γ !].
  Proof.
    repeat split; auto using derive_tyeq_refl.
  Qed.

  Lemma derive_flat_cxteq_sym {n} {Γ Δ : context_of_length n}
    (d_Γ : [! |f- Γ !]) (d_Δ : [! |f- Δ !])
    : [! |f- Γ === Δ !] → [! |f- Δ === Γ !].
  Proof.
    now intros [H1 H2].
  Qed.

  Lemma  derive_flat_cxteq_trans {n} {Γ Δ Θ : context_of_length n}
    : [! |f- Γ !] -> [! |f- Δ !] -> [! |f- Θ !]
    -> [! |f- Γ === Δ !] → [! |f- Δ === Θ !] → [! |f- Γ === Θ !].
  Proof.
    intros d_Γ d_Δ d_Θ d_ΓΔ d_ΔΘ.
    assert (d_ΔΓ := derive_flat_cxteq_sym d_Γ d_Δ d_ΓΔ).
    assert (d_ΘΔ := derive_flat_cxteq_sym d_Δ d_Θ d_ΔΘ).
    repeat split; intro i.
    - eapply (derive_tyeq_trans Γ _ (Δ i));
        eauto using derive_ty_conv_cxteq.
      + apply d_ΓΔ.
      + apply (derive_tyeq_conv_cxteq Δ); auto; apply d_ΔΘ.
    - eapply (derive_tyeq_trans Θ _ (Δ i));
        eauto using derive_ty_conv_cxteq.
      + apply d_ΘΔ.
      + apply (derive_tyeq_conv_cxteq Δ); auto; apply d_ΔΓ.
  Qed.
  
  (** Context extension respects flat equality *)
  Lemma derive_extend_flat_cxteq
      {n} {Γ Δ : context_of_length n}
      (d_Γ : [! |f- Γ !]) (d_Δ : [! |f- Δ !]) (d_ΓΔ : [! |f- Γ === Δ !])
      {A B : ty_expr n} (d_AB : [! Γ |- A === B !])
    : [! |f- Γ;;A === Δ;;B !].
  Proof.
    assert [! |f- Γ;;A !].
    { apply derive_flat_extend_context; try assumption.
      apply (derive_presuppositions _ d_AB); assumption. }
    assert [! |f- Δ;;B !].
    { apply derive_flat_extend_context; try assumption.
      apply (@derive_ty_conv_cxteq _ Γ); try assumption. 
      apply (derive_presuppositions _ d_AB); assumption. }
    split.
    - use dB_Sn_rect.
      + (* top *)
        refine (rename_derivation _ d_AB (dB_next_typed_renaming _ _)); auto.
      + intros i.
        refine (rename_derivation [! Γ |- _ === _ !] _
                                  (dB_next_typed_renaming _ _)); auto.        
        apply d_ΓΔ.
    - use dB_Sn_rect.
      + (* top *)
        refine (rename_derivation [! Δ |- _ === _ !] _
                                  (dB_next_typed_renaming _ _)); auto.
        apply derive_tyeq_sym.
        apply (@derive_tyeq_conv_cxteq _ Γ); auto.
        (* TODO: make argument [Γ] explicit in [derive_FOO_conv_cxteq]? *)
      + intros i. hnf.
        refine (rename_derivation [! Δ |- _ === _ !] _
                                  (dB_next_typed_renaming _ _)); auto.
        apply d_ΓΔ.
  Defined.

End Flat_Context_Equality.

Arguments derive_ty_conv_cxteq [_] _ [_] _ _ [_] _.
Arguments derive_tyeq_conv_cxteq [_] _ [_] _ _ [_ _] _.
Arguments derive_tm_conv_cxteq [_] _ [_] _ _ [_ _] _.
Arguments derive_tmeq_conv_cxteq [_] _ [_] _ _ [_ _ _] _.


Section Category_Laws.

  (* TODO: left and right unitality of composition *)

  (* TODO: associativity of composition *)

  Lemma comp_raw_context_cong_l
      {Γ Δ Θ : context} (d_Γ : [! |f- Γ !])
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
      {Γ Δ Θ : context} (d_Γ : [! |f- Γ !])
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

Section Map_Equality.
(** Results on the map-equality judgement [! |- f == g ::: Γ === Δ !]:

- it’s an equivalence relation
- it respects (flat) context equality

assuming whenever necessary that the maps and contexts involved are themselves
well-typed.
*)

  Definition derive_mapeq_refl
      {Γ Δ : context} {f : raw_context_map Γ Δ}
      (d_f : [! |- f ::: Γ ---> Δ !])
    : [! |- f === f ::: Γ ---> Δ !].
  Proof.
    intros i. apply derive_tmeq_refl, d_f.
  Defined.

  Definition derive_mapeq_sym
      {Γ Δ : context} {f g : raw_context_map Γ Δ}
      (d_Γ : [! |f- Γ !]) (d_Δ : [! |f- Δ !])
      (d_f : [! |- f ::: Γ ---> Δ !]) (d_g : [! |- g ::: Γ ---> Δ !])
      (d_fg : [! |- f === g ::: Γ ---> Δ !])
    : [! |- g === f ::: Γ ---> Δ !].
  Proof.
    intros i. apply derive_tmeq_sym.
    refine (derive_tmeq_conv _ _ _ _ _ _ _ _ (d_fg i));
      try apply (subst_derivation [! _ |- _ !]); auto.
    apply (substeq_derivation [! _ |- _ !]); auto.
  Defined.

  Definition derive_mapeq_trans
      {Γ Δ : context} {f g h : raw_context_map Γ Δ}
      (d_Γ : [! |f- Γ !]) (d_Δ : [! |f- Δ !])
      (d_f : [! |- f ::: Γ ---> Δ !])
      (d_g : [! |- g ::: Γ ---> Δ !])
      (d_h : [! |- h ::: Γ ---> Δ !])
      (d_fg : [! |- f === g ::: Γ ---> Δ !])
      (d_gh : [! |- g === h ::: Γ ---> Δ !])
    : [! |- f === h ::: Γ ---> Δ !].
  Proof.
    intros i. apply derive_tmeq_trans with (g i); auto.
    - refine (derive_tm_conv _ _ _ _ _ _ _ (d_g i));
        try apply (subst_derivation [! _ |- _ !]); auto.
      apply derive_tyeq_sym, (substeq_derivation [! _ |- _ !]); auto.
    - refine (derive_tm_conv _ _ _ _ _ _ _ (d_h i));
        try apply (subst_derivation [! _ |- _ !]); auto.
      apply derive_tyeq_trans with (subst_ty g (Δ i));
        try apply (subst_derivation [! _ |- _ !]); auto;
        apply derive_tyeq_sym, (substeq_derivation [! _ |- _ !]); auto.
    - refine (derive_tmeq_conv _ _ _ _ _ _ _ _ (d_gh i));
      try apply (subst_derivation [! _ |- _ !]); auto.
      apply derive_tyeq_sym, (substeq_derivation [! _ |- _ !]); auto.
  Defined.

  (** cf. [derive_ty_conv_cxteq], etc. *)
  Definition derive_map_conv_cxteq_dom
      {n} {Γ Γ' : context_of_length n} {Δ : context} {f : raw_context_map Γ Δ}
      (d_Γ : [! |f- Γ !]) (d_Γ' : [! |f- Γ' !]) (e_Γ : [! |f- Γ === Γ' !])
      (d_Δ : [! |f- Δ !])
      (d_f : [! |- f ::: Γ ---> Δ !])
    : [! |- f ::: Γ' ---> Δ !].
  Proof.
    rewrite <- (id_left_raw_context f).
    refine (derive_comp _ d_f).
    apply derive_idmap_gen; assumption.
  Defined.

  Definition derive_map_conv_cxteq_cod
      {n} {Γ : context} {Δ Δ' : context_of_length n} {f : raw_context_map Γ Δ}
      (d_Γ : [! |f- Γ !])
      (d_Δ : [! |f- Δ !]) (d_Δ' : [! |f- Δ' !]) (e_Δ : [! |f- Δ === Δ' !])
      (d_f : [! |- f ::: Γ ---> Δ !])
    : [! |- f ::: Γ ---> Δ' !].
  Proof.
    rewrite <- (id_right_raw_context f).
    refine (derive_comp d_f _).
    refine (derive_idmap_gen _ _); auto using derive_flat_cxteq_sym.
  Defined.

  Definition derive_mapeq_conv_cxteq_dom
      {n} {Γ Γ' : context_of_length n} {Δ : context}
      {f g : raw_context_map Γ Δ}
      (d_Γ : [! |f- Γ !]) (d_Γ' : [! |f- Γ' !]) (e_Γ : [! |f- Γ === Γ' !])
      (d_Δ : [! |f- Δ !])
      (d_f : [! |- f ::: Γ ---> Δ !]) (d_g : [! |- g ::: Γ ---> Δ !])
      (d_fg : [! |- f === g ::: Γ ---> Δ !])
    : [! |- f === g ::: Γ' ---> Δ !].
  Proof.
    rewrite <- (id_left_raw_context f), <- (id_left_raw_context g).
    refine (comp_raw_context_cong_r _ _ _); auto.
    apply derive_idmap_gen; assumption.
  Defined.

  Definition derive_mapeq_conv_cxteq_cod
      {n} {Γ : context} {Δ Δ' : context_of_length n}
      {f g : raw_context_map Γ Δ}
      (d_Γ : [! |f- Γ !])
      (d_Δ : [! |f- Δ !]) (d_Δ' : [! |f- Δ' !]) (e_Δ : [! |f- Δ === Δ' !])
      (d_f : [! |- f ::: Γ ---> Δ !]) (d_g : [! |- g ::: Γ ---> Δ !])
      (d_fg : [! |- f === g ::: Γ ---> Δ !])
    : [! |- f === g ::: Γ ---> Δ' !].
  Proof.
    rewrite <- (id_right_raw_context f), <- (id_right_raw_context g).
    refine (comp_raw_context_cong_l _ _ _ _ _); auto.
    refine (derive_idmap_gen _ _); auto using derive_flat_cxteq_sym.
  Defined.

End Map_Equality.

Section Split_Typecat_Laws.

  (* TODO: reindexing on types respects equality in both args *)

  (* TODO: functoriality of reindexing on types *)

  (* TODO: dependent projections, and respecting equality *)

  (** Just an alias. *)
  (* TODO: consider naming: which is better? or do we want both, to fit both conventions? *)
  Definition derive_weaken_raw_context_map {Γ} {A} {Γ'} {f}
             (d_Γ : [! |f- Γ !]) (d_A : [! Γ |- A !]) (d_Γ' : [! |f- Γ' !])
             (d_f : [! |- f ::: Γ' ---> Γ !])
     : [! |- weaken_raw_context_map f ::: Γ' ;; subst_ty f A --->  Γ ;; A !].
  Proof.
    now use derive_weaken_map.
  Defined.
  Opaque derive_weaken_raw_context_map.

  Definition derive_weaken_raw_context_mapeq {Γ} {A} {Γ'} {f g}
      (d_Γ : [! |f- Γ !]) (d_A : [! Γ |- A !]) (d_Γ' : [! |f- Γ' !])
      (d_f : [! |- f ::: Γ' ---> Γ !]) (d_g : [! |- g ::: Γ' ---> Γ !])
      (d_fg : [! |- f === g ::: Γ' ---> Γ !])
    : [! |- weaken_raw_context_map f === weaken_raw_context_map g
                                   ::: Γ' ;; subst_ty g A ---> Γ ;; A !].
  Proof.
    (* TODO: this proof can almost certainly be simplified, with a bit of
       thought, e.g. by adapting the proof of [derive_weaken_mapeq]. *) 
    assert (H := derive_weaken_mapeq d_Γ' d_f d_fg d_A).
    eapply (@derive_mapeq_conv_cxteq_dom (S _) (Γ';;_) (Γ';;_));
      try apply derive_weaken_raw_context_map;
      try apply derive_flat_extend_context; 
      try apply (subst_derivation [! _ |- _ !]);
      auto.
    - apply derive_extend_flat_cxteq; auto using derive_flat_cxteq_refl.
      apply (substeq_derivation [! _ |- _ !]); auto.
    - use (@derive_map_conv_cxteq_dom _ (Γ';;subst_ty g A));
      try apply derive_weaken_raw_context_map;
      try apply derive_flat_extend_context;
      try apply derive_extend_flat_cxteq;
      try apply (subst_derivation [! _ |- _ !]);
      try apply (substeq_derivation [! _ |- _ !]);
      auto using derive_flat_cxteq_refl, derive_mapeq_sym.
  Defined.
  Opaque derive_weaken_raw_context_mapeq.

  Definition derive_dB_next_context_map {Γ} {A}
      (d_Γ : [! |f- Γ !]) (d_A : [! Γ |- A !])
    : [! |- dB_next_context_map Γ ::: Γ;;A ---> Γ !].
  Proof.
    intros i.
    eapply transportb.
    { apply maponpaths_2, pathsinv0, rename_as_subst_ty. }
    refine (derive_var (_;;_) (dB_next i) _).
    refine (derive_flat_extend_context _ _ (dB_next i)); assumption.
  Defined.
  Opaque derive_dB_next_context_map.

End Split_Typecat_Laws.
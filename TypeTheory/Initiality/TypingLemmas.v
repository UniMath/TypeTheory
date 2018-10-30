(** In this file, we show admissibility of the substitution rule(s) for derivations.

(NOTE: currently, the substitution rules still given explicitly; so for now, the file defines the transformation of derivations into a substitution-free form, with the intention of later removing those rules. *)

Require Import UniMath.MoreFoundations.All.

Require Import TypeTheory.Auxiliary.Auxiliary.

Require Import TypeTheory.Initiality.Syntax.
Require Import TypeTheory.Initiality.SyntaxLemmas.
Require Import TypeTheory.Initiality.Typing.

Local Open Scope judgement_scope.

Section Typed_Renaming.

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

  Definition rename_derivation
      {J : judgement} (d_J : derivation J)
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

(* TODO: upstream? *)
Section Context_Maps.

  Definition derivation_context_map
      (Δ Γ : context) (f : raw_context_map Δ Γ) : UU
  := forall i:Γ, [! Δ |- f i ::: subst_ty f (Γ i) !].

  Identity Coercion id_derivation_context_map
    : derivation_context_map >-> Funclass.

  (** The eventual [weaken_derivation_context_map] doesn’t need the
   hypothesis [ [! Δ |- subst_ty f A !] ]. However, that requires admissibility
   of substitution, which in turn uses this preliminary version. *)
  Definition weaken_derivation_context_map_prelim
      {Δ Γ : context} (f : raw_context_map Δ Γ) (A : ty_expr Γ)
    : derivation_context_map Δ Γ f
      -> [! |- Δ !]
      -> [! Δ |- subst_ty f A !]
      -> derivation_context_map
           (Δ ;; subst_ty f A) (Γ ;; A) (weaken_raw_context_map f).
  Proof.
    intros d_f d_Δ d_fA i.
    eapply transportb.
    { apply maponpaths_2.
      eapply pathscomp0. { use subst_rename_ty. } 
      apply pathsinv0. use rename_subst_ty. }
    destruct i as [ | i]; cbn.
    - refine (derive_var (_;;_) dB_top _ _).
      { apply derive_cxt_extend; auto. }
      refine (@rename_derivation [! _ |- _ !]
                                   _ _ (dB_next_typed_renaming _ _) _);
        auto using derive_cxt_extend.
    - refine (@rename_derivation [! _ |- _ ::: _ !]
                                   _ _ (dB_next_typed_renaming _ _) _);
        eauto using derive_cxt_extend.
  Defined.  

  Definition context_map (Δ Γ : context) : UU
    := ∑ (f : raw_context_map Δ Γ), derivation_context_map Δ Γ f.

  Definition context_map_pr1 {Γ Δ} (f : context_map Γ Δ) := pr1 f
    : raw_context_map _ _.
  Coercion context_map_pr1 : context_map >-> raw_context_map.

  Definition derivation_from_context_map {Γ Δ} (f : context_map Γ Δ) (i : Δ)
    : derivation _
  := pr2 f i.

  (** Like [weaken_derivation_context_map_prelim], we will be able to give a
  stronger version of this later, following admissibility of substitution. *)
  Definition weaken_context_map_prelim
    {Δ Γ : context} (f : context_map Δ Γ) (A : ty_expr Γ)
    (d_Δ : [! |- Δ !])
    (d_fA : [! Δ |- subst_ty f A !])
    : context_map (Δ ;; subst_ty f A) (Γ ;; A)
  := (_,, weaken_derivation_context_map_prelim
            f A (derivation_from_context_map f) d_Δ d_fA).

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
      {Δ : context} (f : context_map Δ (context_of_judgement J))
      (d_Δ : [! |- Δ !])
    : derivation (subst_judgement J f).
  Proof.
    revert J d_J Δ f d_Δ.
    use derivation_rect_grouped.
    - split; auto. (* context rules *)
    - (* var rule *)
      intros Γ; cbn; intros i _ _ d_Γi IH_Γi Δ f d_Δ.
      specialize (IH_Γi Δ f d_Δ). 
      set (e := derivation_from_context_map f i). apply e.
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
        refine (p_B _ (weaken_context_map_prelim _ _ _ _) _);
          auto using derive_cxt_extend.
      + cbn. intros; apply derive_lam; auto.
        * refine (p_B _ (weaken_context_map_prelim _ _ _ _) _);
            auto using derive_cxt_extend.
        * refine (p_b _ (weaken_context_map_prelim _ _ _ _) _);
            auto using derive_cxt_extend.        
      + cbn. intros ? A ? ? ? ? ? ? ? ? p_B ? ? ? ? ? f ?.
        refine (transportb _ _ _). 
        { eapply maponpaths_2, subst_subst_top_ty. }
        apply derive_app; eauto.
        refine (p_B _ (weaken_context_map_prelim _ _ _ _) _);
          auto using derive_cxt_extend.
      + cbn. intros ? A ? ? ? ? ? ? ? ? p_B ? p_b ? ? ? f ?.
        refine (transportb _ _ _). 
        { eapply maponpaths_13. 
          - apply subst_subst_top_ty.
          - apply subst_subst_top_tm. }
        apply derive_beta; eauto.
        * refine (p_B _ (weaken_context_map_prelim _ _ _ _) _);
            auto using derive_cxt_extend.
        * refine (p_b _ (weaken_context_map_prelim _ _ _ _) _);
            auto using derive_cxt_extend.        
    - split. (* congruences for pi-constructors *)
      + cbn. intros ? A ? ? ? ? ? ? ? ? ? ? p_BB ? f ?.
        apply derive_Pi_cong; auto.
        refine (p_BB _ (weaken_context_map_prelim _ _ _ _) _);
          auto using derive_cxt_extend.
      + cbn. intros ? A ? ? ? ? ? ? ? ? ? ? ? ? p_BB ? p_bb ? f ?.
        apply derive_lam_cong; auto.
        * refine (p_BB _ (weaken_context_map_prelim _ _ _ _) _);
            auto using derive_cxt_extend.
        * refine (p_bb _ (weaken_context_map_prelim _ _ _ _) _);
            auto using derive_cxt_extend.        
      + cbn. intros ? A ? ? ? ? ? ? ? ? ? ? ? ? ? ? p_BB ? ? ? ? ? f ?.
        refine (transportb _ _ _). 
        { eapply maponpaths_3, subst_subst_top_ty. }
        apply derive_app_cong; auto.
        refine (p_BB _ (weaken_context_map_prelim _ _ _ _) _);
          auto using derive_cxt_extend.
  Defined.

End Substitute_Judgements.

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

(*
  Lemma
    {Γ Δ} (f : raw_context_map Δ Γ) (A : ty_expr Γ)
    : forall i : Γ, subst_ty (weaken_raw_context_map f A) (Γ ;; A i)
                             = subs *)

  Definition substeq_derivation
      {J : judgement} (d_J : derivation J)
      {Δ : context} (f g : raw_context_map Δ (context_of_judgement J))
      (d_f : derivation_context_map Δ (context_of_judgement J) f)
      (d_g : derivation_context_map Δ (context_of_judgement J) g)
      (d_fg : forall i, [! Δ |- f i === g i ::: subst_ty f (context_of_judgement J i) !])
      (d_Δ : [! |- Δ !])
    : substeq_judgement J f g.
  Proof.
    revert J d_J Δ f g d_f d_g d_fg d_Δ.
    use derivation_rect_grouped.
    - split; cbn; intros; exact tt. (* context rules *)
    - intro; cbn; auto. (* var rule *)
    - split; cbn; intros; exact tt. (* equiv_rel rules *)
    - split; cbn. (* conv rules *)
      + intros ? ? ? a ? _ ? _ ? _ _ p_a ? f ? ? ? ? ?. 
        apply derive_tmeq_conv with (subst_ty f A).
        * refine (subst_derivation [! _ |- _ !] _ (_,,_) _); auto.
        * refine (subst_derivation [! _ |- _ !] _ (_,,_) _); auto.
        * refine (subst_derivation [! _ |- _ === _ !] _ (_,,_) _); auto.
        * auto.
      + intros; exact tt.
    - split; cbn; intros. (* universe rules *)
      + apply derive_tyeq_refl, derive_U; assumption.
      + apply derive_El_cong; auto.
      + exact tt.
    - split; cbn. (* pi rules *)
      + intros. apply derive_Pi_cong; auto.
        { refine (subst_derivation [! _ |- _ !] _ (_,,_) _); auto. }
        use p_B.
        * use weaken_derivation_context_map_prelim; auto.
          refine (subst_derivation [! _ |- _ !] _ (_,,_) _); auto.
        * intros i. (* TODO: abstract as lemma [derive_context_map_conv] *)
          apply derive_tm_conv
            with (subst_ty (weaken_raw_context_map f) ((Γ;;A)%context i)).
          -- (* PROBLEM: I don’t think we have enough assumptions to do this.
   Will need to fundamentally clean up the treatment of context judgements. *)
            admit.
          -- admit.
          -- admit.
          -- admit.
        * admit.
        * admit.
      + admit.
      + admit.
      + intros; exact tt.
    - split; intros; exact tt. (* pi cong rules *)
  Admitted.

End Substeq_Judgements.
(** In this file, we show admissibility of the substitution rule(s) for derivations.

(NOTE: currently, the substitution rules still given explicitly; so for now, the file defines the transformation of derivations into a substitution-free form, with the intention of later removing those rules. *)

Require Import UniMath.MoreFoundations.All.

Require Import TypeTheory.Auxiliary.Auxiliary.

Require Import TypeTheory.Initiality.Syntax.
Require Import TypeTheory.Initiality.SyntaxLemmas.
Require Import TypeTheory.Initiality.Typing.

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

  Definition extend_typed_renaming
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

End Typed_Renaming.

Section Renaming_Judgements.

  Local Open Scope judgement_scope.

  Definition context_of_judgement (J : judgement) : context
  := match J with
     | [! |- Γ !] => Γ
     | [! Γ |- A !] => Γ
     | [! Γ |- A === A' !] => Γ
     | [! Γ |- a ::: A !] => Γ
     | [! Γ |- a === a' ::: A !] => Γ
  end.

  Definition rename_judgement
      (J : judgement) {Δ} 
    : typed_renaming (context_of_judgement J) Δ
    -> judgement.
  Proof.
    destruct J as [ Γ | Γ A | Γ A A' | Γ A a | Γ A a a' ]; intros f.
    - exact [! |- Δ !].
    - exact [! Δ |- rename_ty f A !].
    - exact [! Δ |- rename_ty f A === rename_ty f A' !].
    - exact [! Δ |- rename_tm f a ::: rename_ty f A !].
    - exact [! Δ |- rename_tm f a === rename_tm f a' ::: rename_ty f A !].
  Defined.

  (* TODO: upstream *)
  Lemma rename_tm_as_raw_context_map {m n : nat} (f : m -> n) (a : tm_expr m)
    : rename_tm f ∘ tm_as_raw_context_map a
    = tm_as_raw_context_map (rename_tm f a) ∘ fmap_dB_S f.
  Proof.
    use funextfun; use dB_Sn_rect; intros; apply idpath.
  Defined. 

  (* TODO: upstream *)
  Lemma rename_subst_top_ty {m n : nat} (f : m -> n)
      (A : ty_expr (S m)) (a : tm_expr m)
    : rename_ty f (subst_top_ty a A)
      = subst_top_ty (rename_tm f a) (rename_ty (fmap_dB_S f) A). 
  Proof.
    unfold subst_top_ty.
    eapply pathscomp0. { apply rename_subst_ty. }
    eapply pathscomp0. 2: { apply pathsinv0, subst_rename_ty. }
    apply maponpaths_2, rename_tm_as_raw_context_map.
  Defined.

  (* TODO: upstream *)
  Lemma rename_subst_top_tm {m n : nat} (f : m -> n)
      (A : tm_expr (S m)) (a : tm_expr m)
    : rename_tm f (subst_top_tm a A)
      = subst_top_tm (rename_tm f a) (rename_tm (fmap_dB_S f) A). 
  Proof.
    unfold subst_top_tm.
    eapply pathscomp0. { apply rename_subst_tm. }
    eapply pathscomp0. 2: { apply pathsinv0, subst_rename_tm. }
    apply maponpaths_2, rename_tm_as_raw_context_map.
  Defined.


  Definition rename_derivation
      {J : judgement} (d_J : derivation J)
      {Δ} (f : typed_renaming (context_of_judgement J) Δ)
      (d_Δ : derivation [! |- Δ !])
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
    - admit. (* subst rules *)
    - admit. (* subst_eq rules *)
    - split. (* universe rules *)
      + intros; apply derive_U; auto.
      + intros; apply derive_El; eauto.
      + intros; apply derive_El_cong; eauto.
    - split. (* Pi rules *)
      + cbn. intros; apply derive_Pi; auto.
        refine (p_B _ (extend_typed_renaming _ _) _).
        apply derive_cxt_extend; auto.
      + cbn. intros; apply derive_lam; auto;
        set (fA := extend_typed_renaming f A).
        * refine (p_B _ fA _); auto using derive_cxt_extend.
        * refine (p_b _ fA _); auto using derive_cxt_extend.        
      + cbn. intros ? A ? ? ? ? ? ? ? ? p_B ? ? ? ? ? f ?.
        refine (transportb _ _ _). 
        { eapply maponpaths_2, rename_subst_top_ty. }
        apply derive_app; eauto.
        refine (p_B _ (extend_typed_renaming f A) _);
          auto using derive_cxt_extend.
      + cbn. intros ? A ? ? ? ? ? ? ? ? p_B ? p_b ? ? ? f ?.
        refine (transportb _ _ _). 
        { eapply maponpaths_13. 
          - apply rename_subst_top_ty.
          - apply rename_subst_top_tm. }
        apply derive_beta; eauto.
        * refine (p_B _ (extend_typed_renaming f A) _);
            auto using derive_cxt_extend.
        * refine (p_b _ (extend_typed_renaming f A) _);
            auto using derive_cxt_extend.
    - split.
      + cbn. intros ? A ? ? ? ? ? ? ? ? ? ? p_BB ? f ?.
        apply derive_Pi_cong; auto.
        refine (p_BB _ (extend_typed_renaming _ _) _).
        apply derive_cxt_extend; eauto.
      + cbn. intros ? A ? ? ? ? ? ? ? ? ? ? ? ? p_BB ? p_bb ? f ?.
        apply derive_lam_cong; auto.
        * refine (p_BB _ (extend_typed_renaming _ _) _).
          apply derive_cxt_extend; eauto.
        * refine (p_bb _ (extend_typed_renaming _ _) _).
          apply derive_cxt_extend; eauto.
      + cbn. intros ? A ? ? ? ? ? ? ? ? ? ? ? ? ? ? p_BB ? ? ? ? ? f ?.
        refine (transportb _ _ _). 
        { eapply maponpaths_3, rename_subst_top_ty. }
        apply derive_app_cong; auto.
        refine (p_BB _ (extend_typed_renaming _ _) _).
        apply derive_cxt_extend; eauto.
  Admitted.

End Renaming_Judgements.

(** Some general infrastructure for split type-categories,
  used in this package.

Note: much of this essentially duplicates material given already in the [ALV1] package, since everything there is given not for [split_typecat] itself but for the reassociated definition [split_typecat'], and the equivalence doesn’t compute straightforwardly enough to allow them to be used here.

Probably much of this really should belong in a different pagckage. *)

Require Import UniMath.MoreFoundations.All.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.TypeCat.

(* This should be upstreamed *)
Arguments nat_trans_ax {C C'} {F F'} a {x x'} f.

Local Open Scope cat.

(** Notations for working in split type cats *)
Notation "A ⦃ s ⦄" := (reind_typecat A s) (at level 40, format "A  ⦃ s ⦄").
Notation "Γ ⋆ A" := (ext_typecat Γ A) (at level 30, only parsing).

Section Comp_Ext_Compare.

  Definition comp_ext_compare {C : typecat}
      {Γ : C} {A A' : C Γ} (e : A = A')
    : iso (Γ ◂ A) (Γ ◂ A')
  := idtoiso (maponpaths (ext_typecat Γ) e).

  Lemma comp_ext_compare_id {C : typecat}
      {Γ : C} (A : C Γ)
    : (comp_ext_compare (idpath A) : _ --> _) = identity (Γ ◂ A).
  Proof.
    apply idpath.
  Qed.

  Lemma comp_ext_compare_id_general {C : split_typecat}
      {Γ : C} {A : C Γ} (e : A = A)
    : (comp_ext_compare e : _ --> _) = identity (Γ ◂ A).
  Proof.
    apply @pathscomp0 with (comp_ext_compare (idpath _)).
    - apply maponpaths, maponpaths, isaset_types_typecat.
    - apply idpath.
  Qed.

  Lemma comp_ext_compare_comp {C : split_typecat}
    {Γ : C} {A A' A'' : C Γ} (e : A = A') (e' : A' = A'')
  : (comp_ext_compare (e @ e') : _ --> _)
    = comp_ext_compare e ;; comp_ext_compare e'.
  Proof.
    apply pathsinv0.
    etrans. { apply idtoiso_concat_pr. }
    unfold comp_ext_compare. apply maponpaths, maponpaths.
    apply pathsinv0, maponpathscomp0.
  Qed.

End Comp_Ext_Compare.

Section Terms.

  Definition ty (C : split_typecat) : PreShv C.
  Proof.
    use mk_functor.
    - use mk_functor_data.
      + intros x.
        exists (ty_typecat C x).
        abstract (apply isaset_types_typecat).
      + simpl; intros Γ Γ' f A.
        exact (reind_typecat A f).
    - use tpair.
      + intros Γ.
        abstract (apply funextfun; intros y; simpl;
                  apply reind_id_type_typecat).
      + cbn; intros Γ Γ' Γ'' f g.
        abstract (apply funextfun; intros A;
                  apply reind_comp_type_typecat).
  Defined.

  (* TODO: upstream this and following material on general sections to [TypeTheory.Auxiliary]? *)
  Definition section {C : precategory} {X Y : C} (f : X --> Y)
    := ∑ (s : Y --> X), s ;; f = identity _.

  Coercion section_pr1 {C : precategory} {X Y : C} (f : X --> Y)
    : section f -> (Y --> X)
  := pr1.

  Definition section_property {C : precategory}
      {X Y : C} {f : X --> Y} (s : section f)
    : s ;; f = identity _
  := pr2 s.

  Definition paths_section {C : category} {X Y : C} {f : X --> Y}
      {s s' : section f}
    : ((s : Y --> X) = s') -> s = s'.
  Proof.
    apply subtypeEquality.
    intro; apply homset_property.
  Qed.

  Definition isaset_section {C : category} {X Y : C} {f : X --> Y}
    : isaset (section f).
  Proof.
    apply isaset_total2.
    - apply homset_property.
    - intros; apply isasetaprop, homset_property.
  Qed.

  Definition tm {C : typecat} {Γ} (A : C Γ) : UU
    := section (dpr_typecat A).
  Identity Coercion section_of_term : tm >-> section.

  Lemma paths_tm {C : typecat} {Γ} {A : C Γ} (a a' : tm A)
    : ((a : _ --> _) = a') -> a = a'.
  Proof.
    apply paths_section.
  Qed.

  Lemma isaset_tm {C : split_typecat} {Γ : C} {A : C Γ}
    : isaset (tm A).
  Proof.
    apply isaset_section.
  Qed.

  Definition reind_tm {C : typecat} {Γ Γ'} (f : Γ' --> Γ) {A : C Γ}
    (x : tm A) : tm (A⦃f⦄) := pb_of_section _ (reind_pb_typecat A f) _ (pr2 x).

  Lemma reind_tm_q {C : typecat} {Γ Γ'} (f : Γ' --> Γ)
      {A : C Γ} (a : tm A)
    : reind_tm f a ;; q_typecat A f = f ;; a.
  Proof.
    simpl.
    set (pb := mk_Pullback _ _ _ _ _ _ _).
    now rewrite (PullbackArrow_PullbackPr2 pb).
  Qed.

  (** A concrete construction of “transport” of terms, by composing with [comp_ext_compare]. *)
  Definition tm_transportf {C : typecat} {Γ} {A A' : C Γ} (e : A = A')
    : tm A ≃ tm A'.
  Proof.
    use weqbandf.
    + use tpair.
      - intros t.
        exact (t · comp_ext_compare e).
      - abstract (now induction e; use (isweq_iso _ (idfun _));
                  intros x; unfold idfun; simpl; apply id_right).
    + abstract (now intros x; induction e; simpl;
                  rewrite <-assoc, id_left; apply idweq).
  Defined.

  Global Arguments tm_transportf : simpl never.

  Definition tm_transportb {C : typecat} {Γ} {A A' : C Γ} (e : A = A')
    : tm A' ≃ tm A
  := tm_transportf (!e).

  (* TODO: maybe make an equality of equivalences? *)
  Definition transportf_tm {C : typecat}
      {Γ} {A A' : C Γ} (e : A = A') (s : tm A)
    : transportf tm e s = tm_transportf e s.
  Proof.
    induction e.
    apply subtypeEquality.
    + now intros x; apply homset_property.
    + now unfold tm_transportf; cbn; rewrite id_right.
  Defined.

  Lemma tm_transportf_idpath {C : typecat} {Γ} {A : C Γ} (t : tm A)
    : tm_transportf (idpath A) t = t.
  Proof.
    apply paths_tm, id_right.
  Defined.

  Lemma tm_transportb_idpath {C : typecat} {Γ} {A : C Γ} (t : tm A)
    : tm_transportb (idpath A) t = t.
  Proof.
    apply paths_tm, id_right.
  Defined.

  Lemma tm_transportf_irrelevant {C : split_typecat} {Γ} {A A' : C Γ} (e e' : A = A')
      (t : tm A)
    : tm_transportf e t = tm_transportf e' t.
  Proof.
    apply (maponpaths (fun e => tm_transportf e t)).
    apply isaset_types_typecat.
  Defined.

  Lemma tm_transportf_idpath_gen {C : split_typecat}
      {Γ} {A : C Γ} (e : A = A) (t : tm A)
    : tm_transportf e t = t.
  Proof.
    eapply pathscomp0; [apply tm_transportf_irrelevant|].
    eapply tm_transportf_idpath.
  Defined.

  Definition reind_id_tm {C : split_typecat}
      {Γ : C}{A : C Γ} (a : tm A)
    : reind_tm (identity _) a
      = tm_transportb (reind_id_type_typecat _ _) a.
  Proof.
    apply subtypeEquality; [ intros x; apply homset_property|]; simpl.
    set (pb := mk_Pullback _ _ _ _ _ _ _).
    (* Why is there a ' version of this lemma??? *)
    apply pathsinv0, (PullbackArrowUnique' _ _ pb).
    - rewrite <-assoc.
      etrans; [eapply maponpaths, idtoiso_dpr_typecat|].
      exact (pr2 a).
    - unfold comp_ext_compare; cbn.
      now rewrite reind_id_term_typecat, id_left,
                  <-assoc, idtoiso_concat_pr, <- maponpathscomp0,
                  pathsinv0l, id_right.
  Qed.

  Lemma tm_transportf_compose {C : split_typecat}
      {Γ: C} {A A' A'' : C Γ} (e : A = A') (e' : A' = A'') (a : tm A)
    : tm_transportf (e @ e') a = tm_transportf e' (tm_transportf e a).
  Proof.
    induction e, e'.
    now rewrite !tm_transportf_idpath_gen.
  Qed.

  Lemma reind_compose_tm {C : split_typecat}
      {Γ Γ' Γ'' : C} (f : Γ' --> Γ) (g : Γ'' --> Γ') {A : C Γ} (a : tm A)
    : reind_tm (g ;; f) a
      = tm_transportb (reind_comp_typecat _ _ _ _ _ _)
          (reind_tm g (reind_tm f a)).
  Proof.
    apply subtypeEquality; [ intros x; apply homset_property|]; simpl.
    set (pb := mk_Pullback _ _ _ _ _ _ _).
    set (pb' := mk_Pullback _ _ _ _ _ _ _).
    set (pb'' := mk_Pullback _ _ _ _ _ _ _).
    apply pathsinv0, (PullbackArrowUnique' _ _ pb).
    - rewrite <- assoc.
      etrans; [eapply maponpaths, idtoiso_dpr_typecat|].
      apply (PullbackArrow_PullbackPr1 pb').
    - unfold comp_ext_compare; cbn.
      rewrite <- assoc, (reind_comp_term_typecat _ A).
      etrans; [eapply maponpaths|].
      rewrite !assoc, idtoiso_concat_pr, <- maponpathscomp0, pathsinv0l, <-assoc.
      apply id_left.
      rewrite assoc, (PullbackArrow_PullbackPr2 pb'), <-!assoc.
      now apply maponpaths, (PullbackArrow_PullbackPr2 pb'').
  Qed.

  Lemma reind_compose_tm' {C : split_typecat}
      {Γ Γ' Γ'' : C} (f : Γ' --> Γ) (g : Γ'' --> Γ') {A : C Γ} (a : tm A)
    : tm_transportf (reind_comp_typecat _ _ _ _ _ _)
        (reind_tm (g ;; f) a)
      = reind_tm g (reind_tm f a).
  Proof.
    rewrite reind_compose_tm; unfold tm_transportb.
    now rewrite <- tm_transportf_compose, pathsinv0l, tm_transportf_idpath.
  Qed.
  
  Lemma maponpaths_2_reind_tm {C : split_typecat}
      {Γ Γ' : C} {f f' : Γ' --> Γ} (e : f = f') {A : C Γ} (a : tm A)
    : reind_tm f a = tm_transportb (maponpaths _ e) (reind_tm f' a).
  Proof.
    induction e.
    rewrite maponpaths_eq_idpath; [|apply idpath].
    now rewrite tm_transportb_idpath.
  Qed.

  (** the “universal term of type A” *)
  Definition var_typecat {C : typecat} {Γ : C} (A : C Γ)
    : tm (A ⦃dpr_typecat A⦄).
  Proof.
    use tpair.
    + eapply (map_into_Pb _ _ _ _ _ (reind_pb_typecat A _) _ _ (idpath (identity _ ;; _))).
    + apply Pb_map_commutes_1.
  Defined.
  
  Definition reind_tm_var_typecat {C : split_typecat} {Γ : C} {A : C Γ} (a : tm A)
    (e : A = (A ⦃dpr_typecat A⦄) ⦃a⦄
      := ! reind_id_type_typecat _ _
           @ maponpaths _ (! section_property a)
           @ reind_comp_typecat _ _ _ _ _ _)
  : reind_tm a (var_typecat A)
    = tm_transportf e a.  
  Proof.
  Admitted.

  Definition reind_tm_var_typecat' {C : split_typecat} {Γ:C} {A:C Γ} (a : tm A)
    (e : A = (A ⦃dpr_typecat A⦄) ⦃a⦄
      := ! reind_id_type_typecat _ _
           @ maponpaths _ (! section_property a)
           @ reind_comp_typecat _ _ _ _ _ _)
  : tm_transportb e (reind_tm a (var_typecat A))
    = a.
  Admitted.

  Definition reind_tm_var_typecat_gen {C : split_typecat} {Γ:C} {A:C Γ} (a : tm A)
    (e : A = (A ⦃dpr_typecat A⦄) ⦃a⦄)
  : reind_tm a (var_typecat A)
    = tm_transportf e a.
  Proof.
    eauto using pathscomp0, tm_transportf_irrelevant, reind_tm_var_typecat.
  Defined.

End Terms.

Section Types_with_Terms.

  Context {C : split_typecat}.

  Definition type_with_term (Γ:C) := ∑ (A : C Γ), tm A.

  Definition type_of {Γ} (Aa : type_with_term Γ) := pr1 Aa.

  Coercion term_of {Γ} (Aa : type_with_term Γ) : tm (type_of Aa)
    := pr2 Aa.

  Definition paths_type_with_term {Γ} {Aa Bb : type_with_term Γ}
      (e_ty : type_of Aa = type_of Bb)
      (e_tm : term_of Aa ;; comp_ext_compare e_ty = term_of Bb)
    : Aa = Bb.
  Proof.
    destruct Aa as [A a], Bb as [B b]; cbn in *.
    destruct e_ty; cbn in *.
    apply maponpaths, paths_tm.
    refine (_ @ e_tm). apply pathsinv0, id_right.
  Defined.

  Definition reind_type_with_term {Γ Γ'} (f : Γ' --> Γ)
    : type_with_term Γ -> type_with_term Γ'
  := fun a => ((type_of a)⦃f⦄,, reind_tm f a).

  Definition reind_idmap_type_with_term
      {Γ} (Aa : type_with_term Γ)
    : reind_type_with_term (identity _) Aa = Aa.
  Proof.
  Admitted.

  Definition reind_compose_type_with_term
      {Γ Γ' Γ''} (f : Γ' --> Γ) (f' : Γ'' --> Γ')
      (Aa : type_with_term Γ)
    : reind_type_with_term (f' ;; f) Aa
      = reind_type_with_term f' (reind_type_with_term f Aa).
  Proof.
  Admitted.

  Definition var_with_type {Γ} (A : C Γ)
    : type_with_term (Γ ◂ A)
  := (A⦃dpr_typecat A⦄,, var_typecat A).

  Lemma reind_type_with_term_q_var {Γ Γ'} (f : Γ' --> Γ) (A : C Γ)
    : reind_type_with_term (q_typecat A f) (var_with_type A)
    = var_with_type (A ⦃f⦄).
  Proof.
      use paths_type_with_term.
      + eapply pathscomp0. { apply pathsinv0, reind_comp_typecat. }
        eapply pathscomp0. 2: { apply reind_comp_typecat. }
        apply maponpaths, dpr_q_typecat.
      + cbn. admit. (* lemma about [var_typecat] *)
  Admitted.

  Lemma reind_term_var_with_type {Γ} {A : C Γ} (a : tm A)
    : reind_type_with_term a (var_with_type A) = (A,,a).
  Proof.
    use paths_type_with_term.
    + eapply pathscomp0. { apply pathsinv0, reind_comp_typecat. }
      eapply pathscomp0. 2: { apply reind_id_type_typecat. }
      apply maponpaths, section_property.
    + use (@maponpaths _ _ (section_pr1 _) (tm_transportf _ _) _ _).
      refine (_ @ reind_tm_var_typecat' a).
      apply tm_transportf_irrelevant.
  Qed.

End Types_with_Terms.
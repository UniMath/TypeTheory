(** Some general infrastructure for split type-categories,
  used in this package.

Note: much of this essentially duplicates material given already in the [CwF_SplitTypeCat] package, since everything there is given not for [split_typecat] itself but for the reassociated definition [split_typecat'], and the equivalence doesn’t compute straightforwardly enough to allow them to be used here.

Probably much of this really should belong in a different package. *)

Require Import UniMath.MoreFoundations.All.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheory.
Require Import TypeTheory.Auxiliary.Pullbacks.

Require Import TypeTheory.TypeCat.TypeCat.

Local Open Scope cat.

(** Notations for working in split type cats *)
Notation "A ⦃ s ⦄" := (reind_typecat A s) (at level 40, format "A  ⦃ s ⦄").
Notation "Γ ⋆ A" := (ext_typecat Γ A) (at level 30, only parsing).

Section Comp_Ext_Compare.

  Definition comp_ext_compare {C : typecat}
      {Γ : C} {A A' : C Γ} (e : A = A')
    : z_iso (Γ ◂ A) (Γ ◂ A')
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
    etrans. 2: { apply idtoiso_concat_pr. }
    unfold comp_ext_compare. apply maponpaths, maponpaths.
    apply maponpathscomp0.
  Qed.

  Lemma comp_ext_compare_inv {C : typecat}
      {Γ : C} {A A' : C Γ} (e : A = A')
    : (comp_ext_compare (!e) : _ --> _) = inv_from_z_iso (comp_ext_compare e).
  Proof.
    destruct e; apply idpath.
  Qed.

  Lemma comp_ext_compare_irrelevant {C : split_typecat}
      {Γ : C} {A A' : C Γ} (e e' : A = A')
    : (comp_ext_compare e : _ --> _) = comp_ext_compare e'.
  Proof.
    apply maponpaths, maponpaths, isaset_types_typecat.
  Qed.

  Definition dpr_typecat_typeeq {C : typecat}
      {Γ} {A A' : C Γ} (e : A = A')
    : comp_ext_compare e
        ;; dpr_typecat A'
      = dpr_typecat A.
  Proof.
    destruct e; apply id_left.
  Qed.

  Definition q_typecat_mapeq {C : typecat}
      {Γ Γ'} {f f' : Γ' --> Γ} (e : f = f') (A : C Γ)
    : comp_ext_compare (maponpaths _ e)
        ;; q_typecat A f'
      = q_typecat A f.
  Proof.
    destruct e; apply id_left.
  Qed.

  Lemma q_typecat_typeeq {C : typecat} {Γ:C}
        {A A' : C Γ} (e : A = A')
        {Γ' : C} (f : Γ' --> Γ)
    : comp_ext_compare (maponpaths (fun X => X {{ f }}) e) ;; q_typecat A' f
    = q_typecat A f ;; comp_ext_compare e.
  Proof.
    destruct e; cbn.
    rewrite id_right; apply id_left.
  Qed.

End Comp_Ext_Compare.

Section Terms.

  Definition ty (C : split_typecat) : PreShv C.
  Proof.
    use make_functor.
    - use make_functor_data.
      + intros x.
        exists (ty_typecat C x).
        abstract (apply isaset_types_typecat).
      + simpl; intros Γ Γ' f A.
        exact (reind_typecat A f).
    - use tpair.
      + intros Γ.
        abstract (apply funextfun; intros y; simpl;
                  apply reind_id_typecat).
      + cbn; intros Γ Γ' Γ'' f g.
        abstract (apply funextfun; intros A;
                  apply reind_comp_typecat).
  Defined.

  Definition tm {C : typecat} {Γ} (A : C Γ) : UU
    := section (dpr_typecat A).
  Identity Coercion section_of_term : tm >-> section.

  Lemma paths_tm {C : typecat} {Γ} {A : C Γ} (a a' : tm A)
    : ((a : _ --> _) = a') -> a = a'.
  Proof.
    apply paths_section.
  Qed.

  Lemma isaset_tm {C : split_typecat} {Γ : C} (A : C Γ)
    : isaset (tm A).
  Proof.
    apply isaset_section.
  Qed.

  Definition tm_hSet {C : split_typecat} {Γ : C} (A : C Γ) : hSet
  := make_hSet (tm A) (isaset_tm A).

  Definition reind_tm {C : typecat} {Γ Γ'} (f : Γ' --> Γ) {A : C Γ}
    (x : tm A) : tm (A⦃f⦄) := pb_of_section _ (reind_pb_typecat A f) _ (pr2 x).

  Lemma reind_tm_q {C : typecat} {Γ Γ'} (f : Γ' --> Γ)
      {A : C Γ} (a : tm A)
    : reind_tm f a ;; q_typecat A f = f ;; a.
  Proof.
    simpl.
    set (pb := make_Pullback _ _).
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
                  intros x; apply id_right).
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
    apply subtypePath.
    + now intros x; apply homset_property.
    + now unfold tm_transportf; cbn; rewrite id_right.
  Qed.

  Lemma tm_transportf_idpath {C : typecat} {Γ} {A : C Γ} (t : tm A)
    : tm_transportf (idpath A) t = t.
  Proof.
    apply paths_tm, id_right.
  Qed.

  Lemma tm_transportb_idpath {C : typecat} {Γ} {A : C Γ} (t : tm A)
    : tm_transportb (idpath A) t = t.
  Proof.
    apply paths_tm, id_right.
  Qed.

  Lemma tm_transportf_irrelevant {C : split_typecat} {Γ} {A A' : C Γ} (e e' : A = A')
      (t : tm A)
    : tm_transportf e t = tm_transportf e' t.
  Proof.
    apply (maponpaths (fun e => tm_transportf e t)).
    apply isaset_types_typecat.
  Qed.

  Lemma tm_transportf_idpath_gen {C : split_typecat}
      {Γ} {A : C Γ} (e : A = A) (t : tm A)
    : tm_transportf e t = t.
  Proof.
    eapply pathscomp0; [apply tm_transportf_irrelevant|].
    eapply tm_transportf_idpath.
  Qed.

  Definition reind_id_tm {C : split_typecat}
      {Γ : C}{A : C Γ} (a : tm A)
    : reind_tm (identity _) a
      = tm_transportb (reind_id_typecat _) a.
  Proof.
    apply subtypePath; [ intros x; apply homset_property|]; simpl.
    set (pb := make_Pullback _ _).
    (* TODO: is there a ' version of [PullbackArrowUnique']?? *)
    apply pathsinv0, (PullbackArrowUnique' _ _ _ pb).
    - rewrite <-assoc.
      etrans; [eapply maponpaths, idtoiso_dpr_typecat|].
      exact (pr2 a).
    - unfold comp_ext_compare; cbn.
      now rewrite q_id_typecat, id_left,
                  <-assoc, <- idtoiso_concat_pr, <- maponpathscomp0,
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
      = tm_transportb (reind_comp_typecat _ _ _) (reind_tm g (reind_tm f a)).
  Proof.
    apply subtypePath; [ intros x; apply homset_property|]; simpl.
    set (pb := make_Pullback _ _).
    set (pb' := make_Pullback _ _).
    set (pb'' := make_Pullback _ _).
    apply pathsinv0, (PullbackArrowUnique' _ _ _ pb).
    - rewrite <- assoc.
      etrans; [eapply maponpaths, idtoiso_dpr_typecat|].
      apply (PullbackArrow_PullbackPr1 pb').
    - unfold comp_ext_compare; cbn.
      rewrite <- assoc, (q_comp_typecat A).
      etrans; [eapply maponpaths|].
      rewrite !assoc, <- idtoiso_concat_pr, <- maponpathscomp0, pathsinv0l, <-assoc.
      apply id_left.
      rewrite assoc, (PullbackArrow_PullbackPr2 pb'), <-!assoc.
      now apply maponpaths, (PullbackArrow_PullbackPr2 pb'').
  Qed.

  Lemma reind_compose_tm' {C : split_typecat}
      {Γ Γ' Γ'' : C} (f : Γ' --> Γ) (g : Γ'' --> Γ') {A : C Γ} (a : tm A)
    : tm_transportf (reind_comp_typecat _ _ _) (reind_tm (g ;; f) a)
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
    + eapply (map_into_Pb (reind_pb_typecat A _) _ _ (idpath (identity _ ;; _))).
    + apply Pb_map_commutes_1.
  Defined.

  (** naturality of [var_typecat] in the context *)
  Definition reind_var_typecat {C : split_typecat}
      {Γ Γ'} (f : Γ' --> Γ) (A : C Γ)
      (e : (A ⦃dpr_typecat A⦄) ⦃q_typecat A f⦄ = (A ⦃f⦄) ⦃dpr_typecat (A ⦃f⦄)⦄
        := ! reind_comp_typecat _ _ _
           @ maponpaths _ (dpr_q_typecat _ _)
           @ reind_comp_typecat _ _ _ )
    : reind_tm (q_typecat A f) (var_typecat A)
      = tm_transportb e (var_typecat (A ⦃f⦄)).
  Proof.
    apply subtypePath; [ intros x; apply homset_property|].
    apply pathsinv0, PullbackArrowUnique.
    { apply (section_property (tm_transportb _ _)). }
    apply pathsinv0.
    etrans. { refine (postCompWithPullbackArrow _ _ _ _
                                       (make_Pullback _ _) _ _ _). }
    apply pathsinv0, PullbackArrowUnique; cbn; refine (_ @ ! id_right _).
    - rewrite <- assoc.
      etrans. { apply maponpaths, dpr_q_typecat. }
      rewrite assoc.
      etrans. { apply maponpaths_2.
                refine (section_property (tm_transportb _ _)). }
      apply id_left.
    - unfold tm_transportb, e.
      rewrite ! pathscomp_inv, ! tm_transportf_compose, pathsinv0inv0.
      unfold tm_transportf; simpl.
      repeat rewrite <- assoc.
      etrans.
      { do 3 apply maponpaths; rewrite assoc. apply pathsinv0, q_comp_typecat. }
      etrans.
      { rewrite <- maponpathsinv0.
        apply maponpaths, maponpaths, q_typecat_mapeq. }
      etrans. { apply maponpaths, pathsinv0, q_q_typecat. }
      rewrite assoc.
      etrans. { apply maponpaths_2, Pb_map_commutes_2. }
      apply id_left.
  Qed.

  Definition reind_var_typecat_gen {C : split_typecat}
      {Γ Γ'} (f : Γ' --> Γ) (A : C Γ)
      (e : (A ⦃dpr_typecat A⦄) ⦃q_typecat A f⦄ = (A ⦃f⦄) ⦃dpr_typecat (A ⦃f⦄)⦄)
    : reind_tm (q_typecat A f) (var_typecat A)
      = tm_transportb e (var_typecat (A ⦃f⦄)).
  Proof.
    etrans. { apply reind_var_typecat. }
    apply tm_transportf_irrelevant.
  Qed.

  (** reindexing [var_typecat] along a term is the term itself  *)
  Definition reind_tm_var_typecat {C : split_typecat}
      {Γ : C} {A : C Γ} (a : tm A)
      (e : A = (A ⦃dpr_typecat A⦄) ⦃a⦄
        := ! reind_id_typecat _
           @ maponpaths _ (! section_property a)
           @ reind_comp_typecat _ _ _)
    : reind_tm a (var_typecat A) = tm_transportf e a.
  Proof.
    induction a as [a af]; cbn in *.
    apply subtypePath; [ intros x; apply homset_property|]; simpl.
    apply pathsinv0, PullbackArrowUnique; cbn.
    + now induction e; rewrite <-assoc, id_left.
    + unfold map_into_Pb.
      set (pb := make_Pullback _ _).
      rewrite <-assoc, (postCompWithPullbackArrow _ _ _ _ pb).
      apply PullbackArrowUnique; cbn.
    - rewrite <-!assoc, dpr_q_typecat; induction e.
      now rewrite id_left, assoc, af, id_left, id_right.
    - rewrite <-!assoc; apply maponpaths.
      unfold e, comp_ext_compare.
      rewrite !maponpathscomp0, !idtoiso_concat_pr, <-!assoc.
      etrans; [ do 2 eapply maponpaths; rewrite assoc;
                    apply (!q_comp_typecat A (dpr_typecat A) a)|].
      now rewrite af, id_left, q_id_typecat,
                  <- idtoiso_concat_pr, <-maponpathscomp0, pathsinv0l.
  Qed.

  Definition reind_tm_var_typecat' {C : split_typecat}
      {Γ:C} {A:C Γ} (a : tm A)
      (e : A = (A ⦃dpr_typecat A⦄) ⦃a⦄
        := ! reind_id_typecat _
           @ maponpaths _ (! section_property a)
           @ reind_comp_typecat _ _ _)
    : tm_transportb e (reind_tm a (var_typecat A)) = a.
  Proof.
    unfold tm_transportb.
    rewrite reind_tm_var_typecat, <- tm_transportf_compose.
    now rewrite pathsinv0r, tm_transportf_idpath.
  Qed.

  Definition reind_tm_var_typecat_gen {C : split_typecat} {Γ:C} {A:C Γ} (a : tm A)
    (e : A = (A ⦃dpr_typecat A⦄) ⦃a⦄)
  : reind_tm a (var_typecat A)
    = tm_transportf e a.
  Proof.
    rewrite reind_tm_var_typecat; apply tm_transportf_irrelevant.
  Qed.

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
    induction Aa as [A a], Bb as [B b]; cbn in *.
    induction e_ty; cbn in *.
    apply maponpaths, paths_tm.
    refine (_ @ e_tm). apply pathsinv0, id_right.
  Defined.

  Definition paths_type_with_term2 {Γ} {Aa Bb : type_with_term Γ}
      (e_ty : type_of Aa = type_of Bb)
      (e_tm : transportf _ e_ty (term_of Aa) = term_of Bb)
    : Aa = Bb.
  Proof.
    use (paths_type_with_term e_ty).
    induction Aa as [A a], Bb as [B b]; cbn in *.
    induction e_ty; cbn in *.
    rewrite id_right.
    now induction e_tm.
  Qed.

  Definition reind_type_with_term {Γ Γ'} (f : Γ' --> Γ)
    : type_with_term Γ -> type_with_term Γ'
  := fun a => ((type_of a)⦃f⦄,, reind_tm f a).

  Definition reind_idmap_type_with_term
      {Γ} (Aa : type_with_term Γ)
    : reind_type_with_term (identity _) Aa = Aa.
  Proof.
    induction Aa as [A a]; cbn in *.
    use total2_paths2_f; [apply reind_id_typecat|].
    etrans; [ eapply maponpaths, reind_id_tm |].
    unfold tm_transportb.
    now rewrite <- transportf_tm, transport_f_f, pathsinv0l.
  Qed.

  Definition reind_compose_type_with_term
      {Γ Γ' Γ''} (f : Γ' --> Γ) (f' : Γ'' --> Γ')
      (Aa : type_with_term Γ)
    : reind_type_with_term (f' ;; f) Aa
      = reind_type_with_term f' (reind_type_with_term f Aa).
  Proof.
    induction Aa as [A a]; cbn in *.
    use total2_paths2_f; [apply reind_comp_typecat|].
    rewrite reind_compose_tm; unfold tm_transportb.
    now rewrite <- transportf_tm, transport_f_f, pathsinv0l.
  Qed.

  Definition var_with_type {Γ} (A : C Γ)
    : type_with_term (Γ ◂ A)
    := (A⦃dpr_typecat A⦄,, var_typecat A).

  Lemma reind_type_with_term_q_var {Γ Γ'} (f : Γ' --> Γ) (A : C Γ)
    : reind_type_with_term (q_typecat A f) (var_with_type A)
    = var_with_type (A ⦃f⦄).
  Proof.
    use paths_type_with_term2.
    + eapply pathscomp0. { apply pathsinv0, reind_comp_typecat. }
      eapply pathscomp0. 2: { apply reind_comp_typecat. }
      apply maponpaths, dpr_q_typecat.
    + set (e := (! _ @ _)); cbn.
      rewrite (reind_var_typecat_gen _ _ e).
      unfold tm_transportb.
      now rewrite <- transportf_tm, transport_f_f, pathsinv0l.
  Qed.

  Lemma reind_term_var_with_type {Γ} {A : C Γ} (a : tm A)
    : reind_type_with_term a (var_with_type A) = (A,,a).
  Proof.
    use paths_type_with_term.
    + eapply pathscomp0. { apply pathsinv0, reind_comp_typecat. }
      eapply pathscomp0. 2: { apply reind_id_typecat. }
      apply maponpaths, section_property.
    + use (@maponpaths _ _ _ (tm_transportf _ _) _ _).
      refine (_ @ reind_tm_var_typecat' a).
      apply tm_transportf_irrelevant.
  Qed.

End Types_with_Terms.

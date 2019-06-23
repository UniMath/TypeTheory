(**
  [TypeTheory.ALV1.CwF_Cats]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**
Contents:

- 
*)

Require Import UniMath.Foundations.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.CwF_def.

Set Automatic Introduction.

Section Auxiliary.

  (* TODO: switch to a more general version *)
  (* Switch between composition and application
     for natural transformations of presheaves *)
  Lemma nat_trans_compose_ap
        {C : category}
        (F G H : preShv C) (a: C)
        (f : F --> G) (g : G --> H) (x : (F : functor _ _) a : hSet)
    : ((f ;; g) : nat_trans _ _) _ x = (g : nat_trans _ _) _ ((f : nat_trans _ _) _ x) .
  Proof.
    unfold compose. cbn. apply idpath.
  Qed.

  (* Switch between composition and application for morphisms *)
  Lemma compose_ap
        (a b c : SET)
        (f : a --> b) (g : b --> c) (x : a : hSet)
    : (f ;; g) x = g (f x).
  Proof.
    unfold compose. cbn. apply idpath.
  Qed.

End Auxiliary.

Section CwF_structure_cat.
  Context {C : category}.

  Definition TM (X : cwf_structure C) : [C^op, SET]
    := Tm (pr1 X).

  Definition TY (X : cwf_structure C) : [C^op, SET]
    := Ty (pr1 X).

  Definition cwf_extended_context
             (X : cwf_structure C)
             (Γ : C)
             (A : (TY X : functor _ _) Γ : hSet)
    : C
    := pr1 (pr1 (pr2 X _ A)).

  Local Notation "Γ ◂ A" := (cwf_extended_context _ Γ A) (at level 40).

  Definition cwf_projection
             (X : cwf_structure C)
             (Γ : C)
             (A : (TY X : functor _ _) Γ : hSet)
    : Γ ◂ A --> Γ
    := pr2 (pr1 (pr2 X _ A)).

  Local Notation "'π' A" := (cwf_projection _ _ A) (at level 40).

  Definition cwf_extended_context_term
             (X : cwf_structure C)
             (Γ : C)
             (A : (TY X : functor _ _) Γ : hSet)
    : (TM X : functor _ _) (Γ ◂ A) : hSet
    := pr1 (pr1 (pr2 (pr2 X _ A))).

  Local Notation "'te' A" := (cwf_extended_context_term _ _ A) (at level 40).

  Definition cwf_structure_mor (X X' : cwf_structure C)
    : UU
    := ∑ (F_TM : TM X --> TM X')
         (F_TY : TY X --> TY X'),
       ∏ (Γ : C) (A : (TY X : functor _ _) Γ : hSet),
       ∑ (ϕ : Γ ◂ A --> Γ ◂ ((F_TY : nat_trans _ _) _ A)),
            (* coherence for extended context Γ ◂ A and weakening π *)
            ϕ ;; π ((F_TY : nat_trans _ _) _ A) = π A
            × (* coherence for "typing" natural transformation *)
            F_TM ;; pr1 X' = pr1 X ;; F_TY
            × (* coherence for term (te A) in extended context *)
            ((F_TM : nat_trans _ _) _ (te A))
            = # (TM X' : functor _ _) ϕ (te _).

  Definition cwf_structure_precategory_ob_mor : precategory_ob_mor
    := make_precategory_ob_mor
         (cwf_structure C) cwf_structure_mor.

  Definition cwf_structure_precategory_data : precategory_data.
  Proof.
    apply (make_precategory_data cwf_structure_precategory_ob_mor).

    + (* Identity morphisms *)
      intros X.
      exists (identity (TM X)). (* F_TM = identity *)
      exists (identity (TY X)). (* F_TY = identity *)
      intros Γ A.
      exists (identity _). (* ϕ = identity *)
      use tpair.
      - apply id_left.
      - use tpair.
        * etrans. apply id_left. apply @pathsinv0, id_right.
        * cbn. exact (!maponpaths (λ f, f (te A)) (functor_id (TM X) _)).
          (* TODO: make previous line nicer! *)

    + (* Composition of morphisms *)
      intros X Y Z.
      intros [F_TM [F_TY f]] [F_TM' [F_TY' f']].
      exists (F_TM ;; F_TM'). (* reuse composition of nat_trans *)
      exists (F_TY ;; F_TY'). (* reuse composition of nat_trans *)
      intros Γ A.
      set (A' := (F_TY : nat_trans _ _) _ A).
      destruct (f  Γ A)  as [ϕ  [f1 [f2 f3]]].
      destruct (f' Γ A') as [ϕ' [g1 [g2 g3]]].
      exists (ϕ ;; ϕ'). (* reuse composition of morphisms *)
      use tpair.
      - rewrite assoc'.
        refine (maponpaths (λ p, ϕ  ;; p) _ @ f1).
        refine (maponpaths (λ p, ϕ' ;; p) _ @ g1).
        set (e := (nat_trans_compose_ap _ _ _ _ F_TY F_TY' A)).
        exact (transportf (λ x, π _ = π x) e (idpath _)).
      - use tpair.
        * rewrite assoc', g2.
          rewrite <- assoc', <- assoc'.
          exact (maponpaths (λ p, p ;; F_TY') f2).
        * cbn.
          refine (maponpaths _ f3 @ _).
          rewrite <- compose_ap, nat_trans_ax, compose_ap.
          refine (maponpaths _ g3 @ _).
          rewrite <- compose_ap, <- functor_comp.
          apply idpath. (* XXX: how does this work?! *)
  Defined.

End CwF_structure_cat.

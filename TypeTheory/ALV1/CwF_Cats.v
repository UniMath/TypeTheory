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

  (* Extract the terms presheaf from a CwF structure. *)
  Definition TM (X : cwf_structure C) : [C^op, SET]
    := Tm (pr1 X).

  (* Extract the types presheaf from a CwF structure. *)
  Definition TY (X : cwf_structure C) : [C^op, SET]
    := Ty (pr1 X).

  (* Extract the extended context Γ.A
     given Γ and A in a given CwF structure. *)
  Definition cwf_extended_context
             (X : cwf_structure C)
             (Γ : C)
             (A : (TY X : functor _ _) Γ : hSet)
    : C
    := pr1 (pr1 (pr2 X _ A)).

  Local Notation "Γ ◂ A" := (cwf_extended_context _ Γ A) (at level 40).

  (* Extract the weakening projection π A : Γ ◂ A --> Γ *)
  Definition cwf_projection
             (X : cwf_structure C)
             (Γ : C)
             (A : (TY X : functor _ _) Γ : hSet)
    : Γ ◂ A --> Γ
    := pr2 (pr1 (pr2 X _ A)).

  Local Notation "'π' A" := (cwf_projection _ _ A) (at level 40).

  (* Extract the term in the extended context Γ.A *)
  Definition cwf_extended_context_term
             (X : cwf_structure C)
             (Γ : C)
             (A : (TY X : functor _ _) Γ : hSet)
    : (TM X : functor _ _) (Γ ◂ A) : hSet
    := pr1 (pr1 (pr2 (pr2 X _ A))).

  Local Notation "'te' A" := (cwf_extended_context_term _ _ A) (at level 40).

  (* CwF morphism:
     - a natural transformation of terms presheaves;
     - a natural transformation of types presheaves;
     - a morphism in C moving context from one CwF to another;
     - coherence conditions.
  *)
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

  (* TM part of CwF morphism:
     a natural transformation of terms presheaves. *)
  Definition cwf_structure_mor_TM
             {X X' : cwf_structure C}
             (f : cwf_structure_mor X X')
    : TM X --> TM X'
    := pr1 f.

  (* TY part of CwF morphism:
     a natural transformation of types presheaves. *)
  Definition cwf_structure_mor_TY
             {X X' : cwf_structure C}
             (f : cwf_structure_mor X X')
    : TY X --> TY X'
    := pr1 (pr2 f).

  (* ϕ part of CwF morphism:
     a morphism in C moving context from one CwF to another. *)
  Definition cwf_structure_mor_ϕ
             {X X' : cwf_structure C}
             (f : cwf_structure_mor X X')
             (Γ : C) (A : (TY X : functor _ _) Γ : hSet)
    : (Γ ◂ A --> Γ ◂ ((cwf_structure_mor_TY f : nat_trans _ _) _ A))
    := pr1 (pr2 (pr2 f) Γ A).

  (* Convert extended contexts given that
     natural transformations of type presheaves are equal
     for given Γ and A. *)
  Definition cwf_extended_context_compare
             { Γ : C }
             { X X' : cwf_structure C }
             { f g : nat_trans (TY X : functor _ _) (TY X' : functor _ _) }
             { A : (TY X : functor _ _) Γ : hSet }
             ( e : f Γ A = g Γ A )
    : Γ ◂ f Γ A --> Γ ◂ g Γ A.
  Proof.
    apply idtoiso.
    apply (maponpaths (cwf_extended_context _ _)).
    exact e.
  Defined.

  (* Definitions of objects and morphisms for
     the category of CwF structures. *)
  Definition cwf_structure_precategory_ob_mor : precategory_ob_mor
    := make_precategory_ob_mor
         (cwf_structure C) cwf_structure_mor.

  (* Precategory data for CwF structures:
     - definitions of objects & morphisms;
     - definition of identity morphisms;
     - definition of morphism composition.

     All definitions are straighforward and based on
     composition of corresponding natural transformations and morphisms.
   *)
  Definition cwf_structure_precategory_data : precategory_data.
  Proof.
    apply (make_precategory_data cwf_structure_precategory_ob_mor).

    + (* Identity morphisms *)
      intros X.
      exists (identity (TM X)). (* F_TM = identity *)
      exists (identity (TY X)). (* F_TY = identity *)
      intros Γ A.
      exists (identity _). (* ϕ = identity *)
      use make_dirprod.
      - apply id_left.
      - use make_dirprod.
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
      use make_dirprod.
      - rewrite assoc'.
        refine (maponpaths (λ p, ϕ  ;; p) _ @ f1).
        refine (maponpaths (λ p, ϕ' ;; p) _ @ g1).
        set (e := (nat_trans_compose_ap _ _ _ _ F_TY F_TY' A)).
        exact (transportf (λ x, π _ = π x) e (idpath _)).
      - use make_dirprod.
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

  (* Prove that two morphisms of CwF structures are equal
     given their constituent parts are equal pairwise. *)
  Definition cwf_structure_mor_eq (X X' : cwf_structure C)
             (f g : cwf_structure_mor X X')
             (* equality of TM components *)
             (e_TM : ∏ (Γ : C^op) (t : (TM X : functor _ _) Γ : hSet),
                     (cwf_structure_mor_TM f : nat_trans _ _) Γ t
                     = (cwf_structure_mor_TM g : nat_trans _ _) Γ t)
             (* equality of TY components *)
             (e_TY : ∏ (Γ : C^op) (A : (TY X : functor _ _) Γ : hSet),
                     (cwf_structure_mor_TY f : nat_trans _ _) Γ A
                     = (cwf_structure_mor_TY g : nat_trans _ _) Γ A)
             (* equality of ϕ components *)
             (e_ϕ : ∏ (Γ : C^op) (A : (TY X : functor _ _) Γ : hSet),
                    cwf_structure_mor_ϕ f Γ A
                        ;; cwf_extended_context_compare (e_TY Γ A)
                    = cwf_structure_mor_ϕ g Γ A)
    : f = g.
  Proof.
    use total2_paths_f.
    - (* proving that F_TM parts are equal *)
      apply nat_trans_eq. apply has_homsets_HSET.
      intros Γ. apply funextsec. intros A.
      exact (e_TM Γ A).
    - (* goal UNREADABLE from here onwards *)
      use total2_paths_f.
      + (* proving that F_TY parts are equal *)
        etrans. use (pr1_transportf (nat_trans _ _)).
        etrans. use transportf_const. (* no dependency on first part *)
        apply nat_trans_eq. apply has_homsets_HSET.
        intros Γ. apply funextsec. intros A.
        exact (e_TY Γ A).
      + (* !!! goal DOES NOT FIT the screen anymore !!! *)
        apply funextsec. intros Γ.
        apply funextsec. intros A.
        use total2_paths_f.
        * (* prove ϕ parts are equal *)
          refine (_ @ e_ϕ Γ A).
          etrans. apply maponpaths.
          refine (toforallpaths _ _ _ _ _).
          etrans. refine (toforallpaths _ _ _ _ _).
          refine (transportf_forall _ _ _).
          refine (transportf_forall _ _ _).
          etrans. use (pr1_transportf (nat_trans _ _)).
          etrans. use (@functtransportf (nat_trans _ _)).
          (* !!! STUCK HERE for now !!! *)
  Defined.

  (* Axioms for CwF structure morphisms:
     - identity · f = f
     - f · identity = f
     - f · (g · h) = (f · g) · h
   *)
  Definition cwf_structure_precategory_axioms
    : is_precategory cwf_structure_precategory_data.
  Proof.
    use make_is_precategory_one_assoc.
    + (* Left identity: identity · f = f *)
      intros a b f.
      use total2_paths2_f.
      - apply id_left.
      - use total2_paths2_f.
        * (* !!! we need cwf_structure_mor_eq for easier proofs !!! *)
          apply id_left.
          (* !!! STUCK for now !!! *)
  Defined.

End CwF_structure_cat.

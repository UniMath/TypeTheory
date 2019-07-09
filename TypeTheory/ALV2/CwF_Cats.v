(**
  [TypeTheory.ALV1.CwF_Cats]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**
Contents:

- 
*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.CwF_def.

Set Automatic Introduction.

Section Auxiliary.

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

  (* CwF morphism type-related data:
     - a natural transformation of types presheaves;
     - a morphism in C moving context from one CwF to another.
  *)
  Definition cwf_structure_mor_ty_data (X X' : cwf_structure C) : UU
    := ∑ (F_TY : TY X --> TY X'),
       ∏ (Γ : C) (A : (TY X : functor _ _) Γ : hSet),
       (Γ ◂ A --> Γ ◂ ((F_TY : nat_trans _ _) _ A)).

  (* CwF morphism data:
     - a natural transformation of terms presheaves;
     - a natural transformation of types presheaves;
     - a morphism in C moving context from one CwF to another.
  *)
  Definition cwf_structure_mor_data (X X' : cwf_structure C) : UU
    := (TM X --> TM X') × cwf_structure_mor_ty_data X X'.

  (* TM part of CwF morphism:
     a natural transformation of terms presheaves. *)
  Definition cwf_structure_mor_TM
             {X X' : cwf_structure C}
             (f : cwf_structure_mor_data X X')
    : TM X --> TM X'
    := pr1 f.

  (* TY part of CwF morphism:
     a natural transformation of types presheaves. *)
  Definition cwf_structure_mor_TY
             {X X' : cwf_structure C}
             (f : cwf_structure_mor_data X X')
    : TY X --> TY X'
    := pr1 (pr2 f).

  (* ϕ part of CwF morphism:
     a morphism in C moving context from one CwF to another. *)
  Definition cwf_structure_mor_ϕ
             {X X' : cwf_structure C}
             (f : cwf_structure_mor_data X X')
             (Γ : C^op) (A : (TY X : functor _ _) Γ : hSet)
    : (Γ ◂ A --> Γ ◂ ((cwf_structure_mor_TY f : nat_trans _ _) _ A))
    := pr2 (pr2 f) Γ A.

  (* coherence for extended context Γ ◂ A and weakening π *)
  Definition cwf_structure_mor_weakening_axiom
             (X X' : cwf_structure C)
             (ty_data : cwf_structure_mor_ty_data X X')
    : UU
    := ∏ (Γ : C) (A : (TY X : functor _ _) Γ : hSet),
       pr2 ty_data Γ A ;; π ((pr1 ty_data : nat_trans _ _) _ A) = π A.

  (* coherence for "typing" natural transformation *)
  Definition cwf_structure_mor_typing_axiom
             (X X' : cwf_structure C)
             (mor : cwf_structure_mor_data X X')
    : UU
    := pr1 mor ;; pr1 X' = pr1 X ;; pr1 (pr2 mor).

  (* coherence for term (te A) in extended context *)
  Definition cwf_structure_mor_term_axiom
             (X X' : cwf_structure C)
             (mor : cwf_structure_mor_data X X')
    : UU
    := ∏ (Γ : C) (A : (TY X : functor _ _) Γ : hSet),
       ((pr1 mor : nat_trans _ _) _ (te A))
       = # (TM X' : functor _ _) (pr2 (pr2 mor) Γ A) (te _).

  Definition is_cwf_structure_mor
             (X X' : cwf_structure C)
             (mor : cwf_structure_mor_data X X')
    : UU
    := cwf_structure_mor_weakening_axiom X X' (pr2 mor)
       ×
       cwf_structure_mor_typing_axiom X X' mor
       ×
       cwf_structure_mor_term_axiom X X' mor.

  Lemma isaprop_is_cwf_structure_mor
        (X X' : cwf_structure C)
        (mor : cwf_structure_mor_data X X')
    : isaprop (is_cwf_structure_mor X X' mor).
  Proof.
    use isapropdirprod.
    - apply impred_isaprop. intros Γ.
      apply impred_isaprop. intros A.
      apply homset_property.
    - use isapropdirprod.
      + apply homset_property.
      + apply impred_isaprop. intros Γ.
        apply impred_isaprop. intros A.
        apply setproperty.
  Qed.
                                         
  (* CwF morphism:
     - a natural transformation of terms presheaves;
     - a natural transformation of types presheaves;
     - a morphism in C moving context from one CwF to another;
     - coherence conditions.
  *)
  Definition cwf_structure_mor (X X' : cwf_structure C) : UU
    := ∑ (mor : cwf_structure_mor_data X X'),
       is_cwf_structure_mor X X' mor.

  Coercion cwf_structure_mor_to_data
           (X X' : cwf_structure C)
           (mor : cwf_structure_mor X X')
    : cwf_structure_mor_data X X'
    := pr1 mor.
           

  Definition make_cwf_structure_mor
             {X X' : cwf_structure C}
             (mor : cwf_structure_mor_data X X')
             (e_weakening : cwf_structure_mor_weakening_axiom X X' (pr2 mor))
             (e_typing : cwf_structure_mor_typing_axiom X X' mor)
             (e_term : cwf_structure_mor_term_axiom X X' mor)
    : cwf_structure_mor X X'
    := (mor ,, (e_weakening ,, (e_typing ,, e_term))).

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
      use make_cwf_structure_mor.
      - exists (identity (TM X)). (* F_TM = identity *)
        exists (identity (TY X)). (* F_TY = identity *)
        intros Γ A.
        exact (identity _). (* ϕ = identity *)
      - intros Γ A. cbn. apply id_left.
      - etrans. apply id_left. apply @pathsinv0, id_right.
      - intros Γ A. cbn. rewrite (functor_id (TM X)). apply idpath.

    + (* Composition of morphisms *)
      intros X Y Z.
      intros [[F_TM  [F_TY  ϕ ]] [f1 [f2 f3]]]
             [[F_TM' [F_TY' ϕ']] [g1 [g2 g3]]].
      use make_cwf_structure_mor.
      - exists (F_TM ;; F_TM').
        exists (F_TY ;; F_TY').
        intros Γ A.
        set (A' := (F_TY : nat_trans _ _) _ A).
        exact (ϕ Γ A ;; ϕ' Γ A').
      - intros Γ A. simpl.
        set (A' := (F_TY : nat_trans _ _) _ A).
        rewrite assoc'.
        refine (_ @ f1 Γ A). simpl.
        apply (maponpaths (λ p, ϕ Γ A ;; p)).
        exact (g1 Γ A').
      - unfold cwf_structure_mor_typing_axiom. simpl.
        unfold cwf_structure_mor_typing_axiom in f2, g2.
        simpl in f2, g2.
        rewrite (assoc' F_TM).
        etrans. apply maponpaths. exact g2.
        rewrite <- assoc'.
        rewrite <- (assoc' (pr1 X)).
        apply (maponpaths (λ p, p ;; F_TY')).
        exact f2.
      - intros Γ A. simpl.
        set (A' := (F_TY : nat_trans _ _) _ A).
        unfold cwf_structure_mor_term_axiom in f3, g3. simpl in f3, g3.
        refine (maponpaths _ (f3 Γ A) @ _).
        etrans. apply (toforallpaths _ _ _ (nat_trans_ax F_TM' _ _ _)).
        refine (maponpaths _ (g3 Γ A') @ _).
        rewrite <- compose_ap, <- (functor_comp (TM Z)).
        apply idpath.
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
    - (* proving that data parts are equal *)
      use dirprod_paths.
      + apply nat_trans_eq. apply has_homsets_HSET.
        intros Γ. apply funextsec. intros A.
        exact (e_TM Γ A).
      + use total2_paths_f.
        * apply nat_trans_eq. apply has_homsets_HSET.
          intros Γ. apply funextsec. intros A.
          exact (e_TY Γ A).
        * apply funextsec. intros Γ.
          apply funextsec. intros A.
          rewrite transportf_forall, transportf_forall.
          rewrite functtransportf.
          etrans. apply pathsinv0, idtoiso_postcompose.
          refine (_ @ e_ϕ Γ A).
          apply maponpaths.
          unfold cwf_extended_context_compare.
          etrans. apply maponpaths, maponpaths.
          apply pathsinv0.
          use (@maponpathscomp (nat_trans _ _)).
          apply (maponpaths cwf_extended_context_compare), setproperty.
    - apply isaprop_is_cwf_structure_mor.
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
    - (* Left identity: identity · f = f *)
      intros a b f.
      use cwf_structure_mor_eq.
      + intros Γ t. apply idpath.
      + intros Γ A. apply idpath.
      + intros Γ A. cbn.
        rewrite id_left, id_right.
        apply idpath.
    - (* Right identity: f · identity = f *)
      intros a b f.
      use cwf_structure_mor_eq.
      + intros Γ t. apply idpath.
      + intros Γ A. apply idpath.
      + intros Γ A. cbn.
        rewrite id_right, id_right.
        apply idpath.
    - (* Associativity: f · (g · h) = (f · g) · h *)
      intros a b c d.
      intros f g h.
      use cwf_structure_mor_eq.
      + intros Γ t. apply idpath.
      + intros Γ A. apply idpath.
      + intros Γ A. cbn.
        (* TODO: define accessor functions for cwf_structure_mor_data *)
        (* TODO: add Coercion for cwf_structure_mor_data *)
        (* TODO: check if it helps here with nested pr1/pr2 *)
        rewrite id_right, assoc'.
        apply idpath.
  Defined.

  (* Precategory of CwF-structures *)
  Definition cwf_structure_precat : precategory
    := (_,, cwf_structure_precategory_axioms).

  Lemma isaset_cwf_structure_mor
           (X X' : cwf_structure C)
     : isaset (cwf_structure_mor X X').
  Proof.
    apply isaset_total2.
    - apply isaset_dirprod.
      + apply homset_property.
      + apply isaset_total2.
        * apply homset_property.
        * intros F_TY.
          apply impred_isaset. intros Γ.
          apply impred_isaset. intros A.
          apply homset_property.
    - intros f.
      apply isaset_dirprod.
      + apply impred_isaset. intros Γ.
        apply impred_isaset. intros A.
        apply isasetaprop.
        apply homset_property.
      + apply isaset_dirprod.
        * apply isasetaprop.
          apply homset_property.
        * apply impred_isaset. intros Γ.
          apply impred_isaset. intros A.
          apply isasetaprop.
          apply setproperty.
  Qed.

  Definition cwf_structure_has_homsets
    : has_homsets cwf_structure_precategory_data.
  Proof.
    unfold has_homsets.
    intros X X'. cbn in *.
    apply isaset_cwf_structure_mor.
  Defined.

  (* Category of CwF-structures *)
  Definition cwf_structure_cat : category
    := (cwf_structure_precat ,, cwf_structure_has_homsets).

End CwF_structure_cat.

(* TODO: send a link to Benedikt once I fix all TODOs *)
(*
  [TypeTheory.ALV2.DiscreteComprehensionCat]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**
This module defines discrete comprehension category in two forms:

- [discrete_comprehension_cat_structure] and [discrete_comprehension_cat]
  define the "usual" notion of discrete comprehension category, which
  is based on a discrete fibration together with a cartesian displayed functor
  into [disp_codomain];
- [discrete_comprehension_cat_structure_with_default_mor] is a rephrasing
  of that definition where the type family of morphisms is set to equations
  about displayed objects in the discrete fibration.

Main definition:

- [discrete_comprehension_cat_structure_with_default_mor_weq] — equivalence of
  the two definitions of discrete comprehension category structure.
*)


Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.Foundations.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.ALV2.FullyFaithfulDispFunctor.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.ComprehensionC.

Section Auxiliary.

  (* TODO: move upstream? *)
  Definition isaprop_is_cartesian_disp_functor
        {C C' : category} {F : functor C C'}
        {D : disp_cat C} {D' : disp_cat C'} {FF : disp_functor F D D'}
    : isaprop (is_cartesian_disp_functor FF).
  Proof.
    apply impred_isaprop. intros c.
    apply impred_isaprop. intros c'.
    apply impred_isaprop. intros f.
    apply impred_isaprop. intros d.
    apply impred_isaprop. intros d'.
    apply impred_isaprop. intros ff.
    apply impred_isaprop. intros ff_is_cartesian.
    apply isaprop_is_cartesian.
  Qed.

  (* TODO: move upstream? *)
  Definition iscontr_irrelevant
             {A : UU} {P : A → UU}
             (iscontr_A : iscontr A)
    : ∏ (a' : A), P a' = P (pr1 iscontr_A).
  Proof.
    intros a'.
    apply (maponpaths P (pr2 iscontr_A a')).
  Defined.

  (* TODO: move upstream? *)
  Definition iscontr_total2_irrelevant
             {A : UU} {P : A → UU}
             (iscontr_A : iscontr A)
    : (∑ (a : A), P a) ≃ P (pr1 iscontr_A).
  Proof.
    eapply weqcomp.
    use (weqtotal2 (Q := λ _, P (pr1 iscontr_A)) (idweq _) _).
    - intros a. apply eqweqmap, maponpaths, (pr2 iscontr_A).
    - apply invweq, WeakEquivalences.dirprod_with_contr_l, iscontr_A.
  Defined.

  Lemma fiber_paths_from_total2_paths
        {A : UU} {B : A → UU}
        (x y : ∑ (a : A), B a)
        (p : x = y)
  : transportb B (maponpaths pr1 p) (pr2 y) = pr2 x.
  Proof.
    induction p. apply idpath.
  Defined.

  Lemma unique_pr2_weq
        {A : UU} {B : A → UU}
        (isaset_A : isaset A)
        (a : A)
    : ((∏ aa : A, isaset (B aa)) × ∑ (b : B a), ∏ (x : ∑ (aa : A), B aa), x = (a,, b))
        ≃ (∏ aa, B aa ≃ (a = aa)).
  Proof.
    use weq_iso.

    - intros f aa.
      set (b := pr1 (dirprod_pr2 f)).
      use weq_iso.
      * intros bb.
        apply (! maponpaths pr1 (pr2 (dirprod_pr2 f) (aa,, bb))).
      * intros p.
        apply (transportf _ p b).
      * intros bb. simpl.
        apply (fiber_paths_from_total2_paths (aa,,bb) (a,,b)).
      * intros p. simpl. apply isaset_A.

    - intros g.
      set (b := invweq (g a) (idpath a)).
      use make_dirprod.
      + intros aa.
        set (f' := pr1 (g aa)).
        set (f'_isweq := pr2 (g aa)).
        apply (isasetsubset f').
        * apply isasetaprop. apply isaset_A.
        * apply isinclweq, f'_isweq.

      + exists b.
        intros ab.
        use total2_paths_f.
        * apply (! g (pr1 ab) (pr2 ab)).
        * set (f := pr1 (g a)).
          set (f_isweq := pr2 (g a)).
          apply (isapropinclb f (isinclweq _ _ f f_isweq)).
          apply isaset_A.

    - intros X.
      use dirprod_paths.
      + apply funextsec; intros aa.
        apply isapropisaset.
      + use total2_paths_f.
        * apply idpath.
        * apply funextsec; intros x.
          apply isaset_total2.
          -- apply isaset_A.
          -- apply (pr1 X).

    - intros Y. simpl.
      apply funextsec; intros aa.
      apply isapropweqtoprop.
      apply isaset_A.
  Defined.

End Auxiliary.

Section MorWithUniqueLift.

  Context
    {C : category}
    (D_ob : C → UU)
    (D_lift_ob : ∏ {Γ Γ' : C}, C ⟦ Γ', Γ ⟧ → D_ob Γ → D_ob Γ').

  Definition default_mor
    : ∏ (Γ Γ' : C), D_ob Γ → D_ob Γ' → C ⟦ Γ, Γ' ⟧ → UU
    := λ Γ Γ' A A' f, D_lift_ob _ _ f A' = A.

  Context
    (D_ob_isaset : ∏ Γ : C, isaset (D_ob Γ)).

  Definition isaprop_default_mor
             {Γ Γ' : C} {A : D_ob Γ} {A' : D_ob Γ'} {f : Γ --> Γ'}
    : isaprop (default_mor Γ Γ' A A' f).
  Proof.
    apply D_ob_isaset.
  Qed.

  Definition default_mor_homsets
             (Γ Γ' : C) (f : C ⟦ Γ, Γ' ⟧) (A : D_ob Γ) (A' : D_ob Γ')
    : isaset (default_mor _ _ A A' f).
  Proof.
    intros. apply isasetaprop. apply D_ob_isaset.
  Qed.

  Context
    (Fob : ∏ Γ : C, D_ob Γ → disp_codomain C Γ).

  Definition mor_with_unique_lift
    : UU
    := ∑ (D_mor : ∏ {Γ Γ' : C}, D_ob Γ → D_ob Γ' → C ⟦ Γ, Γ' ⟧ → UU)
         (D_homsets : ∏ {Γ Γ' : C} (f : C ⟦ Γ, Γ' ⟧) (A : D_ob Γ) (A' : D_ob Γ'),
                      isaset (D_mor A A' f)),
       (* D_unique_lift : *)
       ∏ (Γ Γ' : C) (f : C ⟦ Γ', Γ ⟧) (A : D_ob Γ),
       ∑ (ff : D_mor (D_lift_ob _ _ f A) A f),
       ∏ (gg : ∑ (B : D_ob Γ'), D_mor B A f),
       gg = (D_lift_ob _ _ f A ,, ff).

  Definition default_mor_with_unique_lift
    : mor_with_unique_lift.
  Proof.
    exists default_mor.
    exists default_mor_homsets.
    intros Γ Γ' f A.
    exists (idpath _).
    intros gg.
    use total2_paths_f.
    - apply (! pr2 gg).
    - apply D_ob_isaset.
  Defined.

  Definition mor_with_unique_lift'
    : UU
    := ∏ {Γ Γ' : C} (f : C ⟦ Γ', Γ ⟧) (A : D_ob Γ),
       ∑ (D_mor : D_ob Γ' → UU)
         (D_homsets : ∏ (A' : D_ob Γ'), isaset (D_mor A')),
       (* D_unique_lift : *)
       ∑ (ff : D_mor (D_lift_ob _ _ f A)),
       ∏ (gg : ∑ (B : D_ob Γ'), D_mor B),
       gg = (D_lift_ob _ _ f A ,, ff).

  Definition mor_with_unique_lift'_weq
    : mor_with_unique_lift ≃ mor_with_unique_lift'.
  Proof.
    use weq_iso.
    - intros X Γ Γ' f A.
      set (D_mor := λ A', pr1 X Γ' Γ A' A f).
      set (D_homsets := λ A', pr1 (pr2 X) Γ' Γ f A' A).
      set (D_unique_lift := pr2 (pr2 X) Γ Γ' f A).
      exact (D_mor ,, (D_homsets , D_unique_lift)).
    - intros X.
      set (D_mor := λ Γ Γ' A A' f, pr1 (X Γ' Γ f A') A).
      set (D_homsets := λ Γ Γ' f A A', pr1 (pr2 (X Γ' Γ f A')) A).
      set (D_unique_lift := λ Γ Γ' f A, pr2 (pr2 (X Γ Γ' f A))).
      exact (D_mor ,, (D_homsets , D_unique_lift)).
    - apply idpath.
    - apply idpath.
  Defined.

  Definition mor_with_unique_lift''
    : UU
    := ∏ {Γ Γ' : C} (f : C ⟦ Γ', Γ ⟧) (A : D_ob Γ),
       ∑ (D_mor : D_ob Γ' → UU),
       ∏ (B : D_ob Γ'), D_mor B ≃ (D_lift_ob _ _ f A = B).

  Definition mor_with_unique_lift''_weq
    : mor_with_unique_lift' ≃ mor_with_unique_lift''.
  Proof.
    apply weqonsecfibers; intros Γ.
    apply weqonsecfibers; intros Γ'.
    apply weqonsecfibers; intros f.
    apply weqonsecfibers; intros A.
    apply (weqtotal2 (idweq _)); intros D_mor.

    apply unique_pr2_weq, D_ob_isaset.
  Defined.

  Definition mor_with_unique_lift'''
    : UU
    := ∑ (D_mor : ∏ {Γ Γ' : C}, D_ob Γ → D_ob Γ' → C ⟦ Γ, Γ' ⟧ → UU),
       ∏ {Γ Γ' : C} (A : D_ob Γ) (A' : D_ob Γ') (f : C ⟦ Γ, Γ' ⟧),
       D_mor A A' f ≃ (D_lift_ob _ _ f A' = A).

  Definition mor_with_unique_lift'''_weq
    : mor_with_unique_lift'' ≃ mor_with_unique_lift'''.
  Proof.
    use weq_iso.
    - intros X.
      set (D_mor := λ Γ Γ' A A' f, pr1 (X Γ' Γ f A') A).
      set (D_mor_weq := λ Γ Γ' A A' f, pr2 (X Γ' Γ f A') A).
      exact (D_mor ,, D_mor_weq).
    - intros X Γ Γ' f A.
      set (D_mor := λ A', pr1 X Γ' Γ A' A f). 
      set (D_mor_weq := λ A', pr2 X Γ' Γ A' A f).
      exact (D_mor ,, D_mor_weq).
    - apply idpath.
    - apply idpath.
  Defined.

  Definition default_mor_with_unique_lift'''
    : mor_with_unique_lift'''
    := (default_mor ,, λ _ _ _ _ _, idweq _).

  Definition mor_with_unique_lift'''_default_mor
             (D_mor : mor_with_unique_lift''')
    : pr1 D_mor = default_mor.
  Proof.
    apply funextsec; intros Γ.
    apply funextsec; intros Γ'.
    apply funextsec; intros A.
    apply funextsec; intros A'.
    apply funextsec; intros f.
    apply univalenceweq.
    apply (pr2 D_mor).
  Defined.

  Definition mor_with_unique_lift'''_eq_default
             (D_mor : mor_with_unique_lift''')
    : D_mor = default_mor_with_unique_lift'''.
  Proof.
    use total2_paths_f.
    - apply funextsec; intros Γ.
      apply funextsec; intros Γ'.
      apply funextsec; intros A.
      apply funextsec; intros A'.
      apply funextsec; intros f.
      apply univalenceweq.
      apply (pr2 D_mor).
    - apply funextsec; intros Γ.
      apply funextsec; intros Γ'.
      apply funextsec; intros A.
      apply funextsec; intros A'.
      apply funextsec; intros f.
      apply isapropweqtoprop.
      apply D_ob_isaset.
  Qed.

  Definition iscontr_mor_with_unique_lift'''
    : iscontr mor_with_unique_lift'''.
  Proof.
    exists default_mor_with_unique_lift'''.
    apply mor_with_unique_lift'''_eq_default.
  Defined.

  Definition mor_with_unique_lift_weq
    : mor_with_unique_lift ≃ mor_with_unique_lift'''
    := (mor_with_unique_lift'''_weq
          ∘ mor_with_unique_lift''_weq
          ∘ mor_with_unique_lift'_weq)%weq.

  Definition mor_with_unique_lift_mor_weq
             (mor : mor_with_unique_lift)
             {Γ Γ' : C} {f : C ⟦ Γ, Γ' ⟧}
             {A : D_ob Γ} {A' : D_ob Γ'}
    : pr1 mor Γ Γ' A A' f ≃ default_mor Γ Γ' A A' f.
  Proof.
    set (uf := pr2 (pr2 mor) Γ' Γ f A').
    use weq_iso.
    - intros ff.
      exact (! maponpaths pr1 (pr2 uf (A ,, ff))).
    - intros p.
      exact (transportf (λ B, pr1 mor Γ Γ' B A' f) p (pr1 uf)).
    - abstract (
          intros ff;
          apply (transportf_pathsinv0' (λ B, pr1 mor Γ Γ' B A' f));
          apply pathsinv0;
          apply (transportf_transpose_right
                   (P := λ B, pr1 mor Γ Γ' B A' f)
                );
          apply (fiber_paths_from_total2_paths
                   (B := λ x, pr1 mor Γ Γ' x A' f)
                   (A ,, ff)
                   (D_lift_ob Γ' Γ f A' ,, pr1 uf))
        ).
    - abstract (intros p; apply D_ob_isaset).
  Defined.

  Definition isaprop_mor_with_unique_lift_mor
             (mor : mor_with_unique_lift)
             {Γ Γ' : C} {f : C ⟦ Γ, Γ' ⟧}
             {A : D_ob Γ} {A' : D_ob Γ'}
    : isaprop (pr1 mor Γ Γ' A A' f).
  Proof.
    apply (isapropinclb (mor_with_unique_lift_mor_weq mor)).
    - apply isinclweq, (pr2 (mor_with_unique_lift_mor_weq mor)).
    - apply isaprop_default_mor.
  Qed.

  Definition iscontr_mor_with_unique_lift'
    : iscontr mor_with_unique_lift.
  Proof.
    apply (iscontrweqf (invweq mor_with_unique_lift_weq)).
    apply iscontr_mor_with_unique_lift'''.
  Defined.

  (* Like [iscontr_mor_with_unique_lift'] but with a better point (namely [default_mor_with_unique_lift]). *)
  Definition iscontr_mor_with_unique_lift
    : iscontr mor_with_unique_lift.
  Proof.
    exists default_mor_with_unique_lift.
    intros t.
    exact (pr2 iscontr_mor_with_unique_lift' t
               @ ! pr2 iscontr_mor_with_unique_lift' default_mor_with_unique_lift).
  Defined.

  Definition mor_with_unique_lift_reformulation
             (mor : mor_with_unique_lift)
             {Γ Γ' : C} {f : C ⟦ Γ', Γ ⟧} {A : D_ob Γ}
             (P : ∏ (A' : D_ob Γ'), pr1 mor _ _ A' A f → UU)
    : P (D_lift_ob Γ Γ' f A) (invweq (mor_with_unique_lift_mor_weq mor) (idpath _))
        ≃ (∏ (A' : D_ob Γ') (ff : pr1 mor Γ' Γ A' A f), P A' ff).
  Proof.
    use weq_iso.
    - intros p.
      
  Abort.

End MorWithUniqueLift.

Section DiscreteComprehensionCats.

  (* "Natural" definition of discrete comprehension cat structure *)
  Definition discrete_comprehension_cat_structure (C : category) : UU
    := ∑ (D : disp_cat C)
         (is_discrete_fibration_D : is_discrete_fibration D)
         (FF : disp_functor (functor_identity _) D (disp_codomain C)), 
       is_cartesian_disp_functor FF.

  Definition discrete_comprehension_cat : UU
    := ∑ (C : category), discrete_comprehension_cat_structure C.

  (* Like [disp_cat_axioms] but without [homsets_disp} *)
  Definition disp_cat_axioms' (C : precategory) (D : disp_cat_data C)
    : UU
    := (∏ x y (f : x --> y) (xx : D x) yy (ff : xx -->[f] yy),
        (id_disp _ ;; ff)%mor_disp
        = transportb _ (id_left _) ff)
         × (∏ x y (f : x --> y) (xx : D x) yy (ff : xx -->[f] yy),
            (ff ;; id_disp _)%mor_disp
            = transportb _ (id_right _) ff)
         × (∏ x y z w f g h (xx : D x) (yy : D y) (zz : D z) (ww : D w)
              (ff : xx -->[f] yy) (gg : yy -->[g] zz) (hh : zz -->[h] ww),
            (ff ;; (gg ;; hh))%mor_disp
            = transportb _ (assoc _ _ _) ((ff ;; gg) ;; hh))%mor_disp.

  Definition isaprop_disp_cat_axioms' {C : precategory} {D : disp_cat_data C}
             (D_homsets : ∏ x y f (xx : D x) (yy : D y), isaset (xx -->[f] yy))
    : isaprop (disp_cat_axioms' C D).
  Proof.
    repeat apply isapropdirprod.
    - repeat (apply impred_isaprop; intros ?). apply D_homsets.
    - repeat (apply impred_isaprop; intros ?). apply D_homsets.
    - repeat (apply impred_isaprop; intros ?). apply D_homsets.
  Qed.

  Definition disp_cat_axioms'_weq {C : precategory} {D : disp_cat_data C}
    : (disp_cat_axioms' C D × (∏ x y f (xx : D x) (yy : D y), isaset (xx -->[f] yy)))
                       ≃ disp_cat_axioms _ D.
  Proof.
    eapply weqcomp. apply weqdirprodasstor.
    apply (weqdirprodf (idweq _)).
    apply weqdirprodasstor.
  Qed.

  Definition discrete_comprehension_cat_structure2' {C : category}
             (D_ob : C → UU)
             (Fob : ∏ Γ : C, D_ob Γ → disp_codomain C Γ)
             (D_lift_ob : ∏ {Γ Γ' : C}, C ⟦ Γ', Γ ⟧ → D_ob Γ → D_ob Γ')
             (D_ob_isaset : ∏ Γ : C, isaset (D_ob Γ))
             (D_mor : mor_with_unique_lift D_ob (@D_lift_ob))
             (Fmor : ∏ (Γ Γ' : C) (A : D_ob Γ) (A' : D_ob Γ') (f : C ⟦ Γ, Γ' ⟧),
                     pr1 D_mor _ _ A A' f → Fob Γ A -->[ f] Fob Γ' A')
    : UU 
    := ∑ (D_id_comp : disp_cat_id_comp C (D_ob ,, pr1 D_mor))
         (D_axioms' : disp_cat_axioms' C (_ ,, D_id_comp))
         (FF_axioms : @disp_functor_axioms
                        _ _ (functor_identity C)
                        (_ ,, disp_cat_axioms'_weq (D_axioms' , pr1 (pr2 D_mor))) _
                        (Fob,, Fmor)),

       is_cartesian_disp_functor
         ((_ ,, FF_axioms)
          : disp_functor (functor_identity C) (_ ,, disp_cat_axioms'_weq (D_axioms', pr1 (pr2 D_mor))) (disp_codomain C)).

  Definition isaprop_discrete_comprehension_cat_structure2'_with_default_mor {C : category}
             (D_ob : C → UU)
             (Fob : ∏ Γ : C, D_ob Γ → disp_codomain C Γ)
             (D_lift_ob : ∏ {Γ Γ' : C}, C ⟦ Γ', Γ ⟧ → D_ob Γ → D_ob Γ')
             (D_ob_isaset : ∏ Γ : C, isaset (D_ob Γ))
             (Fmor : ∏ (Γ Γ' : C) (A : D_ob Γ) (A' : D_ob Γ') (f : C ⟦ Γ, Γ' ⟧),
                     default_mor D_ob (@D_lift_ob) _ _ A A' f → Fob Γ A -->[ f] Fob Γ' A')
    : isaprop (discrete_comprehension_cat_structure2' D_ob Fob (@D_lift_ob) D_ob_isaset (default_mor_with_unique_lift D_ob (@D_lift_ob) D_ob_isaset) Fmor).
  Proof.
    apply Propositions.isaproptotal2.
    - intros D_id_comp. apply Propositions.isaproptotal2.
      + intros D_axioms'. apply Propositions.isaproptotal2.
        * intros F_axioms. apply isaprop_is_cartesian_disp_functor.
        * intros. apply isaprop_disp_functor_axioms.
      + intros. apply isaprop_disp_cat_axioms'.
        apply (pr1 (pr2 (default_mor_with_unique_lift D_ob (@D_lift_ob) D_ob_isaset))).
    - intros. use total2_paths_f.
      + repeat (apply funextsec; intros ?). apply D_ob_isaset.
      + repeat (apply funextsec; intros ?). apply D_ob_isaset.
  Qed.
  
  Definition discrete_comprehension_cat_structure2 {C : category}
             (D_ob : C → UU)
             (Fob : ∏ Γ : C, D_ob Γ → disp_codomain C Γ)
             (D_lift_ob : ∏ {Γ Γ' : C}, C ⟦ Γ', Γ ⟧ → D_ob Γ → D_ob Γ')
             (D_ob_isaset : ∏ Γ : C, isaset (D_ob Γ))
             (D_mor : mor_with_unique_lift D_ob (@D_lift_ob))
    : UU 
    := ∑ (Fmor : ∏ (Γ Γ' : C) (A : D_ob Γ) (A' : D_ob Γ') (f : C ⟦ Γ, Γ' ⟧),
                 pr1 D_mor _ _ A A' f → Fob Γ A -->[ f] Fob Γ' A'),
       discrete_comprehension_cat_structure2' D_ob Fob (@D_lift_ob) D_ob_isaset D_mor Fmor.

  (* A variation of [discrete_comprehension_cat_structure] with a convenient rearrangement of fields *)
  Definition discrete_comprehension_cat_structure1 (C : category) : UU
    := ∑ (D_ob : C → UU)
         (Fob : ∏ Γ : C, D_ob Γ → disp_codomain C Γ)
         (D_lift_ob : ∏ {Γ Γ' : C}, C ⟦ Γ', Γ ⟧ → D_ob Γ → D_ob Γ')
         (D_ob_isaset : ∏ Γ : C, isaset (D_ob Γ))

         (D_mor : mor_with_unique_lift D_ob (@D_lift_ob)),

       discrete_comprehension_cat_structure2 D_ob Fob (@D_lift_ob) D_ob_isaset D_mor.

  Section DiscCompCat1_Accessors.

    Definition discrete_comprehension_cat_structure1_D_ob
                {C : category}
                (DC : discrete_comprehension_cat_structure1 C)
        : C → UU
        := pr1 DC.

    Definition discrete_comprehension_cat_structure1_F_ob
                {C : category}
                (DC : discrete_comprehension_cat_structure1 C)
        : ∏ {Γ : C},
        discrete_comprehension_cat_structure1_D_ob DC Γ
        → disp_codomain C Γ
        := pr1 (pr2 DC).

    Definition discrete_comprehension_cat_structure1_D_lift_ob
                {C : category}
                (DC : discrete_comprehension_cat_structure1 C)
        : ∏ {Γ Γ' : C},
        C ⟦ Γ', Γ ⟧
        → discrete_comprehension_cat_structure1_D_ob DC Γ
        → discrete_comprehension_cat_structure1_D_ob DC Γ'
        := pr1 (pr2 (pr2 DC)).

    Definition discrete_comprehension_cat_structure1_D_ob_isaset
                {C : category}
                (DC : discrete_comprehension_cat_structure1 C)
        : ∏ (Γ : C), isaset (discrete_comprehension_cat_structure1_D_ob DC Γ)
        := pr1 (pr2 (pr2 (pr2 DC))).

    Definition discrete_comprehension_cat_structure1_D_mor_with_unique_lift
                {C : category}
                (DC : discrete_comprehension_cat_structure1 C)
      : mor_with_unique_lift (pr1 DC) (pr1 (pr2 (pr2 DC)))
      := pr1 (pr2 (pr2 (pr2 (pr2 DC)))).

    Definition discrete_comprehension_cat_structure1_D_mor
                {C : category}
                (DC : discrete_comprehension_cat_structure1 C)
      : ∏ (Γ Γ' : C), pr1 DC Γ → pr1 DC Γ' → C ⟦ Γ, Γ' ⟧ → UU
      := pr1 (pr1 (pr2 (pr2 (pr2 (pr2 DC))))).

    Definition discrete_comprehension_cat_structure1_D_id
                {C : category}
                (DC : discrete_comprehension_cat_structure1 C)
      : ∏ (Γ : C) (A : discrete_comprehension_cat_structure1_D_ob DC Γ),
        discrete_comprehension_cat_structure1_D_mor DC _ _ A A (identity Γ)
        := pr1 (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 DC))))))).

    Definition discrete_comprehension_cat_structure1_D_comp
                {C : category}
                (DC : discrete_comprehension_cat_structure1 C)
      : _
        := pr2 (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 DC))))))).

    Definition discrete_comprehension_cat_structure1_F_mor
                {C : category}
                (DC : discrete_comprehension_cat_structure1 C)
      : _
        := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 DC))))).


  End DiscCompCat1_Accessors.

  Definition discrete_comprehension_cat_structure1_weq {C : category}
    : discrete_comprehension_cat_structure C ≃ discrete_comprehension_cat_structure1 C.
  Proof.
    use weq_iso.
    - intros DC.
      set (D := pr1 DC).
      set (is_discrete_fibration_D := pr1 (pr2 DC)).
      set (FF := pr1 (pr2 (pr2 DC))).
      set (is_cartesian_FF := pr2 (pr2 (pr2 DC))).
      exists D.
      exists FF.
      exists (λ Γ Γ' f A', pr1 (pr1 (pr1 is_discrete_fibration_D Γ Γ' f A'))).
      exists (pr2 is_discrete_fibration_D).
      use tpair.
      + exists (pr2 (D : disp_cat_ob_mor C)).
        exists (@homsets_disp C D).
        intros Γ Γ' f A.
        set (uf := pr1 is_discrete_fibration_D Γ Γ' f A).
        exists (pr2 (pr1 uf)).
        exact (pr2 uf).
      + exists (@disp_functor_on_morphisms _ _ _ _ _ FF).
        exists (pr2 (pr1 D)).
        exists (pr1 (invweq disp_cat_axioms'_weq (pr2 D))).
        exists (pr2 FF).
        exact is_cartesian_FF.

    - intros DC.
      set (D_ob := pr1 DC).
      set (D_lift_ob := pr1 (pr2 (pr2 DC))).
      set (D_ob_isaset := pr1 (pr2 (pr2 (pr2 DC)))).
      set (D_mor := pr1 (pr1 (pr2 (pr2 (pr2 (pr2 DC)))))).
      set (D_homsets := pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 DC))))))).
      set (D_unique_lift := pr2 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 DC))))))).
      set (D_axioms := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 DC)))))))).
      set (FF_axioms := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 DC))))))))).
      set (is_cartesian_FF := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 DC))))))))).

      exists (_ ,, disp_cat_axioms'_weq (D_axioms , D_homsets)).
      exists (λ Γ Γ' f A',
              ((D_lift_ob _ _ f A' ,, pr1 (D_unique_lift _ _ f A'))
                 ,, pr2 (D_unique_lift _ _ f A'))
             , D_ob_isaset).
      exists (_ ,, FF_axioms).
      exact is_cartesian_FF.

    - apply idpath.
    - apply idpath.
  Defined.

  (* A variation of [discrete_comprehension_cat_structure] with a convenient rearrangement of fields *)
  Definition discrete_comprehension_cat_structure_with_default_mor (C : category) : UU
    := ∑ (D_ob : C → UU)
         (Fob : ∏ Γ : C, D_ob Γ → disp_codomain C Γ)
         (D_lift_ob : ∏ {Γ Γ' : C}, C ⟦ Γ', Γ ⟧ → D_ob Γ → D_ob Γ')
         (D_ob_isaset : ∏ Γ : C, isaset (D_ob Γ)),

       discrete_comprehension_cat_structure2
         D_ob Fob (@D_lift_ob) D_ob_isaset
         (default_mor_with_unique_lift D_ob (@D_lift_ob) D_ob_isaset).

  Section DiscCompCat_DefaultMor_Accessors.

    Definition discrete_comprehension_cat_structure_with_default_mor_D_ob
                {C : category}
                (DC : discrete_comprehension_cat_structure_with_default_mor C)
        : C → UU
        := pr1 DC.

    Definition discrete_comprehension_cat_structure_with_default_mor_F_ob
                {C : category}
                (DC : discrete_comprehension_cat_structure_with_default_mor C)
        : ∏ {Γ : C},
        discrete_comprehension_cat_structure_with_default_mor_D_ob DC Γ
        → disp_codomain C Γ
        := pr1 (pr2 DC).

    Definition discrete_comprehension_cat_structure_with_default_mor_D_lift_ob
                {C : category}
                (DC : discrete_comprehension_cat_structure_with_default_mor C)
        : ∏ {Γ Γ' : C},
        C ⟦ Γ', Γ ⟧
        → discrete_comprehension_cat_structure_with_default_mor_D_ob DC Γ
        → discrete_comprehension_cat_structure_with_default_mor_D_ob DC Γ'
        := pr1 (pr2 (pr2 DC)).

    Definition discrete_comprehension_cat_structure_with_default_mor_D_ob_isaset
                {C : category}
                (DC : discrete_comprehension_cat_structure_with_default_mor C)
        : ∏ (Γ : C), isaset (discrete_comprehension_cat_structure_with_default_mor_D_ob DC Γ)
        := pr1 (pr2 (pr2 (pr2 DC))).

    Definition discrete_comprehension_cat_structure_with_default_mor_D_id
                {C : category}
                (DC : discrete_comprehension_cat_structure_with_default_mor C)
      : ∏ (Γ : C) (A : discrete_comprehension_cat_structure_with_default_mor_D_ob DC Γ),
        discrete_comprehension_cat_structure_with_default_mor_D_lift_ob DC (identity Γ) A = A
        := pr1 (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 DC)))))).

    Definition discrete_comprehension_cat_structure_with_default_mor_D_comp
                {C : category}
                (DC : discrete_comprehension_cat_structure_with_default_mor C)
      : _
        := pr2 (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 DC)))))).

    Definition discrete_comprehension_cat_structure_with_default_mor_F_mor
                {C : category}
                (DC : discrete_comprehension_cat_structure_with_default_mor C)
      : _
        := pr1 (pr2 (pr2 (pr2 (pr2 DC)))).

  End DiscCompCat_DefaultMor_Accessors.

  Definition discrete_comprehension_cat_structure_with_default_mor_weq1
             {C : category}
    : discrete_comprehension_cat_structure1 C
        ≃ discrete_comprehension_cat_structure_with_default_mor C.
  Proof.
    apply (weqtotal2 (idweq _)); intros D_ob.
    apply (weqtotal2 (idweq _)); intros Fob.
    apply (weqtotal2 (idweq _)); intros D_lift_ob.
    apply (weqtotal2 (idweq _)); intros D_ob_isaset.
    exact (iscontr_total2_irrelevant (iscontr_mor_with_unique_lift D_ob D_lift_ob D_ob_isaset)).
  Defined.

  Definition discrete_comprehension_cat_structure_with_default_mor_weq
             {C : category}
    : discrete_comprehension_cat_structure C
        ≃ discrete_comprehension_cat_structure_with_default_mor C
    := (discrete_comprehension_cat_structure_with_default_mor_weq1
          ∘ discrete_comprehension_cat_structure1_weq)%weq.

End DiscreteComprehensionCats.

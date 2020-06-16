(* TODO: module documentation *)

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

  Lemma l0
        {A : UU} {B : A → UU}
        (x y : ∑ (a : A), B a)
        (p : x = y)
  : transportb B (maponpaths pr1 p) (pr2 y) = pr2 x.
  Proof.
    induction p. apply idpath.
  Defined.

  Lemma l1
        {A : UU} {B : A → UU}
        (isaset_A : isaset A)
        (a : A)
    : ((∏ aa : A, isaset (B aa)) × ∑ (b : B a), ∏ (x : ∑ (aa : A), B aa), x = (a,, b))
        ≃ (∏ aa, B aa ≃ (aa = a)).
  Proof.
    use weq_iso.

    - intros f aa.
      set (b := pr1 (dirprod_pr2 f)).
      use weq_iso.
      * intros bb.
        apply (maponpaths pr1 (pr2 (dirprod_pr2 f) (aa,, bb))).
      * intros p.
        apply (transportb _ p b).
      * intros bb. simpl.
        apply (l0 (aa,,bb) (a,,b)).
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
        * apply (g (pr1 ab) (pr2 ab)).
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
    := λ Γ Γ' A A' f, A = D_lift_ob _ _ f A'.

  Context
    (D_ob_isaset : ∏ Γ : C, isaset (D_ob Γ)).

  Definition default_mor_homsets
             (Γ Γ' : C) (f : C ⟦ Γ, Γ' ⟧) (A : D_ob Γ) (A' : D_ob Γ')
    : isaset (default_mor _ _ A A' f).
  Proof.
    intros. apply isasetaprop. apply D_ob_isaset.
  Defined.

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
    - apply (pr2 gg).
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
       ∏ (B : D_ob Γ'), D_mor B ≃ (B = D_lift_ob _ _ f A).

  Definition mor_with_unique_lift''_weq
    : mor_with_unique_lift' ≃ mor_with_unique_lift''.
  Proof.
    apply weqonsecfibers; intros Γ.
    apply weqonsecfibers; intros Γ'.
    apply weqonsecfibers; intros f.
    apply weqonsecfibers; intros A.
    apply (weqtotal2 (idweq _)); intros D_mor.

    apply l1, D_ob_isaset.
  Defined.

  Definition mor_with_unique_lift'''
    : UU
    := ∑ (D_mor : ∏ {Γ Γ' : C}, D_ob Γ → D_ob Γ' → C ⟦ Γ, Γ' ⟧ → UU),
       ∏ {Γ Γ' : C} (A : D_ob Γ) (A' : D_ob Γ') (f : C ⟦ Γ, Γ' ⟧),
       D_mor A A' f ≃ (A = D_lift_ob _ _ f A').

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
  Defined.

  Definition mor_with_unique_lift'''_irrelevant
             (P : (∏ {Γ Γ'}, D_ob Γ → D_ob Γ' → C ⟦ Γ, Γ' ⟧ → UU) → UU)
             (D_mor : mor_with_unique_lift''')
    : P (pr1 D_mor) ≃ P default_mor.
  Proof.
    use weq_iso.
    - intros PP.
      set (p := mor_with_unique_lift'''_default_mor D_mor).
      exact (transportf _ p PP).
    - intros PP.
      set (p := mor_with_unique_lift'''_default_mor D_mor).
      exact (transportb _ p PP).
    - intros X. apply transportbfinv.
    - intros X. apply transportfbinv.
  Defined.

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

  Definition mor_with_unique_lift_irrelevant
             (P : (∏ {Γ Γ'}, D_ob Γ → D_ob Γ' → C ⟦ Γ, Γ' ⟧ → UU) → UU)
             (D_mor : mor_with_unique_lift)
    : P (pr1 D_mor) ≃ P default_mor.
  Proof.
    apply (mor_with_unique_lift'''_irrelevant _ (mor_with_unique_lift_weq D_mor)).
  Defined.

  Definition iscontr_mor_with_unique_lift
    : iscontr mor_with_unique_lift.
  Proof.
    apply (iscontrweqf (invweq mor_with_unique_lift_weq)).
    apply iscontr_mor_with_unique_lift'''.
  Defined.

  Definition iscontr_mor_with_unique_lift'
    : iscontr mor_with_unique_lift.
  Proof.
    exists default_mor_with_unique_lift.
    intros t.
    exact (pr2 iscontr_mor_with_unique_lift t
               @ ! pr2 iscontr_mor_with_unique_lift default_mor_with_unique_lift).
  Defined.

  Definition mor_with_unique_lift_irrelevant'
             (P : (∏ {Γ Γ'}, D_ob Γ → D_ob Γ' → C ⟦ Γ, Γ' ⟧ → UU) → UU)
    : (∑ (D_mor : mor_with_unique_lift), P (pr1 D_mor)) ≃ P default_mor.
  Proof.
    eapply weqcomp.
    apply (weqtotal2 (Q := λ _, P default_mor) (idweq _) (mor_with_unique_lift_irrelevant P)).
    apply invweq.
    apply WeakEquivalences.dirprod_with_contr_l.
    apply iscontr_mor_with_unique_lift.
  Defined.

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

  Definition disp_cat_axioms'_weq {C : precategory} {D : disp_cat_data C}
    : (disp_cat_axioms' C D × (∏ x y f (xx : D x) (yy : D y), isaset (xx -->[f] yy)))
                       ≃ disp_cat_axioms _ D.
  Proof.
    eapply weqcomp. apply weqdirprodasstor.
    apply (weqdirprodf (idweq _)).
    apply weqdirprodasstor.
  Defined.
  
  Definition discrete_comprehension_cat_structure2 {C : category}
             (D_ob : C → UU)
             (Fob : ∏ Γ : C, D_ob Γ → disp_codomain C Γ)
             (D_lift_ob : ∏ {Γ Γ' : C}, C ⟦ Γ', Γ ⟧ → D_ob Γ → D_ob Γ')
             (D_ob_isaset : ∏ Γ : C, isaset (D_ob Γ))
             (D_mor : mor_with_unique_lift D_ob (@D_lift_ob))
    : UU 
    := ∑ (Fmor : ∏ (Γ Γ' : C) (A : D_ob Γ) (A' : D_ob Γ') (f : C ⟦ Γ, Γ' ⟧),
                 pr1 D_mor _ _ A A' f → Fob Γ A -->[ f] Fob Γ' A')

         (D_id_comp : disp_cat_id_comp C (D_ob ,, pr1 D_mor))
         (D_axioms' : disp_cat_axioms' C (_ ,, D_id_comp))
         (FF_axioms : @disp_functor_axioms
                        _ _ (functor_identity C)
                        (_ ,, disp_cat_axioms'_weq (D_axioms' , pr1 (pr2 D_mor))) _
                        (Fob,, Fmor)),

       is_cartesian_disp_functor
         ((_ ,, FF_axioms)
          : disp_functor (functor_identity C) (_ ,, disp_cat_axioms'_weq (D_axioms', pr1 (pr2 D_mor))) (disp_codomain C)).

  (* A variation of [discrete_comprehension_cat_structure] with a convenient rearrangement of fields *)
  Definition discrete_comprehension_cat_structure1 (C : category) : UU
    := ∑ (D_ob : C → UU)
         (Fob : ∏ Γ : C, D_ob Γ → disp_codomain C Γ)
         (D_lift_ob : ∏ {Γ Γ' : C}, C ⟦ Γ', Γ ⟧ → D_ob Γ → D_ob Γ')
         (D_ob_isaset : ∏ Γ : C, isaset (D_ob Γ))

         (D_mor : mor_with_unique_lift D_ob (@D_lift_ob)),

       discrete_comprehension_cat_structure2 D_ob Fob (@D_lift_ob) D_ob_isaset D_mor.

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

  Definition iscontr_irrelevant
             {A : UU} {P : A → UU}
             (iscontr_A : iscontr A)
    : ∏ (a' : A), P a' = P (pr1 iscontr_A).
  Proof.
    intros a'.
    apply (maponpaths P (pr2 iscontr_A a')).
  Defined.

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

  Definition discrete_comprehension_cat_structure_with_default_mor_weq
             {C : category}
    : discrete_comprehension_cat_structure1 C
        ≃ discrete_comprehension_cat_structure_with_default_mor C.
  Proof.
    apply (weqtotal2 (idweq _)); intros D_ob.
    apply (weqtotal2 (idweq _)); intros Fob.
    apply (weqtotal2 (idweq _)); intros D_lift_ob.
    apply (weqtotal2 (idweq _)); intros D_ob_isaset.
    exact (iscontr_total2_irrelevant (iscontr_mor_with_unique_lift' D_ob D_lift_ob D_ob_isaset)).
  Defined.

Lemma l1
      {A : UU} {B : A → UU}
      (isaset_A : isaset A)
      (isaset_B : ∏ (a : A), isaset (B a))
      (a : A)
  : (∑ (b : B a), ∏ (x : ∑ (aa : A), B aa), x = (a,, b))
      ≃ (∏ aa, B aa ≃ (aa = a)).
Proof.
  use weq_iso.

  - intros f aa.
    use weq_iso.
    * intros bb.
      apply (maponpaths pr1 (pr2 f (aa,, bb))).
    * intros p.
      apply (transportb _ p (pr1 f)).
    * intros bb. simpl.
      apply (l0 (aa,,bb) (a,,pr1 f)).
    * intros p. simpl. apply isaset_A.

  - intros g.
    set (b := invweq (g a) (idpath a)).
    exists b.
    intros ab.
    use total2_paths_f.
    + apply (g (pr1 ab) (pr2 ab)).
    + set (f := pr1 (g a)).
      set (f_isweq := pr2 (g a)).
      apply (isapropinclb f (isinclweq _ _ f f_isweq)).
      apply isaset_A.

  - intros X.
    use total2_paths_f.
    + apply idpath.
    + apply funextsec; intros x.
      apply isaset_total2.
      * apply isaset_A.
      * apply isaset_B.

  - intros Y. simpl.
    apply funextsec; intros aa.
    apply isapropweqtoprop.
    apply isaset_A.
Defined.

Lemma ooo
  : (∑ (B : A → UU), (∏ aa, B aa ≃ B' aa) × Q B)
      ≃ (∑ (b' : B' a), Q B').

Lemma l1
      {A : UU} {B : A → UU}
      (isaset_A : isaset A) (isaset_B : ∏ (a : A), isaset (B a))
      (a : A) (b : B a)
  : (∏ (x : ∑ (aa : A), B aa), x = (a,, b))
      ≃
      (∏ aa, B aa ≃ (aa = a)) × (∏ (bb : B a), bb = b).
Proof.
  use weq_iso.

  - intros f.
    use make_dirprod.
    + intros aa.
      use weq_iso.
      * intros bb.
        apply (maponpaths pr1 (f (aa,, bb))).
      * intros p.
        apply (transportb _ p b).
      * intros bb. simpl.
        apply (l0 (aa,,bb) (a,,b)).
      * intros p. simpl. apply isaset_A.
    + intros bb.
      apply (pair_inj isaset_A (f (a,,bb))).

  - intros g ab.
    use total2_paths_f.
    + apply (pr1 g (pr1 ab) (pr2 ab)).
    + apply (dirprod_pr2 g).

  - intros X. simpl.
    apply funextsec; intros x.
    apply isaset_total2.
    + apply isaset_A.
    + apply isaset_B.

  - intros Y. simpl.
    use dirprod_paths.
    + apply funextsec; intros aa.
      apply isapropweqtoprop.
      apply isaset_A.
    + apply funextsec; intros bb.
      apply isaset_B.
Defined.

Search total2.

Lemma l2
      : ∑

Lemma l1
      {A : UU} (a : A) (isaset_A : isaset A)
  : (∑ (B : A → UU), ∃! (x : A), B x) ≃ ∃! (x : A), x = a.

Lemma iscontr_lemma
      {A : UU} (a : A) (isaset_A : isaset A)
  : ∃! (B : A → UU), ∃! (x : A), B x.
Proof.
  use tpair.
  - exists (λ x, x = a).
    use tpair.
    + exists a. apply idpath.
    + intros t.
      use total2_paths_f.
      * apply (pr2 t).
      * apply isaset_A.
  - intros t.
    use total2_paths_f.
    + apply funextsec; intros x.
      apply univalenceweq.
      use weq_iso.
      * 
  
  intros X Y.
  use tpair.
  - use total2_paths_f.
    + 
  use tpair.
  - exists (λ a', a
Defined.

Definition mor_with_unique_lift
           {C : category}
           (D_ob : C → UU)
           (D_lift_ob : ∏ {Γ Γ' : C}, C ⟦ Γ', Γ ⟧ → D_ob Γ → D_ob Γ')
  : UU
  := ∑ (D_mor : ∏ {Γ Γ' : C}, D_ob Γ → D_ob Γ' → C ⟦ Γ, Γ' ⟧ → UU),
       (* D_unique_lift : *)
     ∏ (Γ Γ' : C) (f : C ⟦ Γ', Γ ⟧) (A : D_ob Γ),
     ∑ (ff : D_mor (D_lift_ob f A) A f),
     ∏ (gg : ∑ (B : D_ob Γ'), D_mor B A f),
     gg = (D_lift_ob f A ,, ff).

Lemma mor_with_unique_lift_is_equation
      {C : category}
      (D_ob : C → UU)
      (D_lift_ob : ∏ {Γ Γ' : C}, C ⟦ Γ', Γ ⟧ → D_ob Γ → D_ob Γ')
      (m : mor_with_unique_lift D_ob (@D_lift_ob))
  : ∏ {Γ Γ' : C} (A : D_ob Γ) (A' : D_ob Γ') (f : C ⟦ Γ, Γ' ⟧),
    pr1 m _ _ A A' f = (D_lift_ob f A' = A).
Proof.
  intros Γ Γ' A A' f.
  set (uf := pr2 m Γ' Γ f A').
  apply univalenceweq.
  use weq_iso.
  - intros ff.
    exact (! (maponpaths pr1 (pr2 uf (A ,, ff)))).
  - intros A'A.
    exact (transportf (λ B, pr1 m Γ Γ' B A' f) A'A (pr1 uf)).
  - intros ff. simpl.
    etrans. apply (transportf_pathsinv0' (λ B, pr1 m Γ Γ' B A' f)).
    is_discrete_fibration
    Search transportf.
    etrans. apply pathsinv0.
    apply (functtransportf pr1 (λ B, pr1 m Γ Γ' B A' f) (pr2 uf (A ,, ff))).
    Seach transportf.
    Check (functtransportf pr1 (λ B, pr1 m Γ Γ' B A' f) (pr2 uf (A ,, ff))).
    Search transportf.
    induction (! (maponpaths pr1 (pr2 uf (A ,, ff)))).
Defined.


Lemma iscontr_mor_with_unique_lift
      {C : category}
      (D_ob : C → UU)
      (D_lift_ob : ∏ {Γ Γ' : C}, C ⟦ Γ', Γ ⟧ → D_ob Γ → D_ob Γ')
      (D_ob_isaset : ∏ Γ : C, isaset (D_ob Γ))
  : iscontr (mor_with_unique_lift D_ob (@D_lift_ob)).
Proof.
  use tpair.
  - unfold mor_with_unique_lift.
    use tpair.
    + intros Γ Γ' A A' f. exact (D_lift_ob _ _ f A' = A).
    + intros Γ Γ' A f.
      use tpair.
      * apply idpath.
      * intros gg.
        use total2_paths_f.
        -- exact (! pr2 gg).
        -- apply D_ob_isaset.
  - intros t.
    use total2_paths_f.
    + apply funextsec; intros Γ.
      apply funextsec; intros Γ'.
      apply funextsec; intros A.
      apply funextsec; intros A'.
      apply funextsec; intros f.
      apply univalenceweq.
      
Abort.


Definition



Definition discrete_comprehension_cat_structure'' (C : category) : UU
  := ∑ (D_ob : C → UU)
       (Fob : ∏ Γ : C, D_ob Γ → disp_codomain C Γ)

       (lift_ob : ∏ Γ Γ' (f : Γ' --> Γ) A, D_ob Γ')
       (D_ob_isaset : ∏ Γ, isaset (D_ob Γ))

       (Fmor : ∏ (Γ Γ' : C) (A : D_ob Γ) (A' : D_ob Γ') (f : C ⟦ Γ, Γ' ⟧),
               A = lift_ob f → Fob Γ A -->[ f] Fob Γ' A')

       

       (D_id_comp : disp_cat_id_comp C (D_ob ,, D_mor))
       (D_axioms : disp_cat_axioms C (_ ,, D_id_comp))
       (FF_axioms : @disp_functor_axioms
                      _ _ (functor_identity C)
                      (_ ,, D_axioms) _
                      (Fob,, Fmor)),
     is_cartesian_disp_functor
       ((_ ,, FF_axioms)
        : disp_functor (functor_identity C) (_ ,, D_axioms) (disp_codomain C)).


Definition discrete_comprehension_cat_structure'_weq {C : category}
  : discrete_comprehension_cat_structure' C ≃ discrete_comprehension_cat_structure C.
Proof.
  eapply weqcomp. 2: apply weqtotal2asstol.
  eapply weqcomp. 2: apply weqtotal2asstol.
  eapply weqcomp. 2: apply weqtotal2asstol.
  apply (weqtotal2 (idweq _)). intros D_ob.
  eapply weqcomp. apply WeakEquivalences.weqtotal2comm.
  apply (weqtotal2 (idweq _)). intros D_mor.
  eapply weqcomp. apply weqtotal2asstol'.
  eapply weqcomp. apply WeakEquivalences.weqtotal2comm.
  apply (weqtotal2 (idweq _)). intros D_id_comp.
  eapply weqcomp. apply WeakEquivalences.weqtotal2comm.
  apply (weqtotal2 (idweq _)). intros D_axioms.
  eapply weqcomp. apply WeakEquivalences.weqtotal2comm.
  apply (weqtotal2 (idweq _)). intros D_is_discrete_fibration.
  apply weqtotal2asstol.
Defined.

Section A.

  Section DiscreteComprehensionCat_from_SplitTypeCat.

    Context {C : category}.

    Context (TC : split_typecat_structure C).

    Definition disp_cat_ob_mor_from_split_typecat_structure
        : disp_cat_ob_mor C.
    Proof.
        exists TC.
        intros Γ Γ' A A' f.
        exact (A' {{f}} = A).
    Defined.

    Definition disp_cat_id_comp_from_split_typecat_structure
        : disp_cat_id_comp C disp_cat_ob_mor_from_split_typecat_structure.
    Proof.
        use make_dirprod.
        - intros Γ A. apply (pr1 (pr1 (dirprod_pr2 (pr2 TC)))).
        - intros Γ Γ' Γ'' f g A A' A'' ff gg. 
          simpl.
          set (reind_comp := pr1 (dirprod_pr2 (pr2 (pr2 TC)))).
          etrans. apply reind_comp.
          etrans. apply (maponpaths (λ B, B {{f}}) gg).
          apply ff.
    Defined.

    Definition disp_cat_data_from_split_typecat_structure
        : disp_cat_data C
        := (_ ,, disp_cat_id_comp_from_split_typecat_structure).

    Definition disp_cat_axioms_from_split_typecat_structure
        : disp_cat_axioms C disp_cat_data_from_split_typecat_structure.
    Proof.
        repeat use make_dirprod.
        - intros. apply (pr1 (pr2 TC)).
        - intros. apply (pr1 (pr2 TC)).
        - intros. apply (pr1 (pr2 TC)).
        - intros. apply isasetaprop. apply (pr1 (pr2 TC)).
    Qed.

    Definition disp_precat_from_split_typecat_structure
        : disp_precat C
        := (_ ,, disp_cat_axioms_from_split_typecat_structure).

    Definition disp_cat_from_split_typecat_structure
        : disp_cat C
        := disp_precat_from_split_typecat_structure.

    Definition disp_cat_from_split_typecat_structure_is_univalent
      : is_univalent_disp disp_cat_from_split_typecat_structure.
    Proof.
      apply is_univalent_disp_from_fibers.
      intros Γ A A'.
      use isweq_iso.
      - intros i.
        set (A'A := pr1 i : A' {{ identity _ }} = A).
        set (reind_id := pr1 (pr1 (dirprod_pr2 (pr2 TC)))).
        exact (! A'A @ reind_id Γ A').
      - intros e. apply (pr1 (pr2 TC) Γ).
      - intros i.
        use total2_paths_f.
        + apply (pr1 (pr2 TC) Γ).
        + apply isaprop_is_iso_disp.
    Defined.
    
    Definition is_discrete_fibration_disp_cat_from_split_typecat_structure
      : is_discrete_fibration disp_cat_from_split_typecat_structure.
    Proof.
      use make_dirprod. 2: apply (pr1 (pr2 TC)).
      intros Γ Γ' f A.
      use tpair.
      - exists (A {{f}}). apply idpath.
      - intros X.
        use total2_paths_f.
        + apply (! pr2 X).
        + apply (pr1 (pr2 TC)).
    Defined.

    Definition discrete_fibration_from_split_typecat_structure
      : discrete_fibration C
      := (_ ,, is_discrete_fibration_disp_cat_from_split_typecat_structure).

    Definition disp_functor_data_from_split_typecat_structure
      : disp_functor_data (functor_identity C)
                          disp_cat_from_split_typecat_structure
                          (disp_codomain C).
    Proof.
      use tpair.
      - intros Γ A.
        exists (Γ ◂ A).
        apply (dpr_typecat A).
      - intros Γ Γ' A A' f ff.
        exact (transportf
                 (λ AA, ((Γ ◂ AA,, dpr_typecat AA) : disp_codomain C Γ) -->[f] (Γ' ◂ A',, dpr_typecat A'))
                 ff (q_typecat A' f ,, dpr_q_typecat A' f)).
    Defined.



    Definition disp_functor_axioms_from_split_typecat_structure
      : disp_functor_axioms disp_functor_data_from_split_typecat_structure.
    Proof.
      use make_dirprod.
      - intros Γ A.
        use total2_paths_f. 2: apply homset_property.
        simpl. etrans. apply (pr1_transportf _ (λ AA, C ⟦ Γ ◂ AA, Γ ◂ A ⟧)).
        cbn. etrans. apply maponpaths.
        apply (pr2 (pr1 (dirprod_pr2 (pr2 TC))) Γ A).
        induction (pr1 (pr1 (dirprod_pr2 (pr2 TC))) Γ A).
        apply idpath.

      - intros Γ Γ' Γ'' A A' A'' f g ff gg.
        use total2_paths_f. 2: apply homset_property.
        + simpl. etrans. apply (pr1_transportf _ (λ AA, C ⟦ Γ ◂ AA, Γ'' ◂ A'' ⟧)).
          etrans. apply maponpaths, (pr2 (dirprod_pr2 (pr2 (pr2 TC)))).
          induction ff, gg. simpl.
          etrans. apply maponpaths_2, pathscomp0rid.
          etrans. apply maponpaths, assoc'.
          etrans. apply (functtransportf (λ b : pr1 TC Γ, Γ ◂ b)
                                         ((λ x, C ⟦ x, Γ'' ◂ A'' ⟧))).
          etrans. apply pathsinv0, idtoiso_precompose.
          etrans. apply maponpaths_2, maponpaths, idtoiso_inv.
          etrans. apply assoc.
          etrans. apply maponpaths_2, iso_after_iso_inv.
          apply id_left.
    Qed.

    Definition disp_functor_from_split_typecat_structure
      : disp_functor (functor_identity C)
                     disp_cat_from_split_typecat_structure
                     (disp_codomain C)
      := (_,, disp_functor_axioms_from_split_typecat_structure).

    Definition disp_functor_from_split_typecat_structure_is_cartesian
      : is_cartesian_disp_functor disp_functor_from_split_typecat_structure.
    Proof.
      intros Γ Γ' f A A' ff ff_is_cartesian.
      intros Δ g k k_comm.
      use iscontrweqf.
      3: {
        use (reind_pb_typecat A f).
        - exact (pr1 k).
        - exact (pr2 k ;; g).
        - exact (pr1 k_comm).
        - etrans. apply assoc'. apply (! pr2 k_comm).
      }

      induction ff.

      eapply weqcomp.
      2: apply weqtotal2asstol.
      apply weq_subtypes_iff.
      -- intro. apply isapropdirprod; apply homset_property.
      -- intro. apply (isofhleveltotal2 1). 
         ++ apply homset_property.
         ++ intros. apply homsets_disp.
      -- intros gg; split; intros H.
         ++ exists (pr1 H).
            apply subtypePath.
            intro; apply homset_property.
            exact (pr2 H).
         ++ split.
            ** exact (pr1 H).
            ** apply (maponpaths pr1 (pr2 H)).
    Defined.

    Definition discrete_comprehension_cat_structure_from_split_typecat_structure
      : discrete_comprehension_cat_structure C
      := ( _ ,, is_discrete_fibration_disp_cat_from_split_typecat_structure ,,
             _ ,, disp_functor_from_split_typecat_structure_is_cartesian).

  End DiscreteComprehensionCat_from_SplitTypeCat.

  Section DiscreteComprehensionCat'_from_SplitTypeCat.

    Context {C : category}.

    Context (TC : split_typecat_structure C).

    Definition discrete_comprehension_cat_structure'_from_split_typecat_structure
      : discrete_comprehension_cat_structure' C.
    Proof.
      exists TC.
      use tpair. 2: use tpair. 3: use tpair. 4: use tpair. 5: use tpair. 6: use tpair.
      7: use tpair.
      - intros Γ A.
        exists (Γ ◂ A).
        apply (dpr_typecat A).
      - intros Γ Γ' A A' f. exact (A' {{f}} = A).
      - intros Γ Γ' A A' f ff. simpl in *.
        exact (transportf
                 (λ AA, ((Γ ◂ AA,, dpr_typecat AA) : disp_codomain C Γ) -->[f] (Γ' ◂ A',, dpr_typecat A'))
                 ff (q_typecat A' f ,, dpr_q_typecat A' f)).

      - apply disp_cat_id_comp_from_split_typecat_structure.
      - apply disp_cat_axioms_from_split_typecat_structure.
      - apply is_discrete_fibration_disp_cat_from_split_typecat_structure.
      - apply disp_functor_axioms_from_split_typecat_structure.
      - apply disp_functor_from_split_typecat_structure_is_cartesian.
    Defined.

  End DiscreteComprehensionCat'_from_SplitTypeCat.

  Section SplitTypeCat_from_DiscreteComprehensionCat.

    Context {C : category}.

    Context (DC : discrete_comprehension_cat_structure C).

    Let D := pr1 DC : disp_cat C.
    Let is_discrete_fibration_D := pr1 (pr2 DC) : is_discrete_fibration D.
    Let FF := pr1 (pr2 (pr2 DC)) : disp_functor (functor_identity C) D (disp_codomain C).
    Let is_cartesian_FF := pr2 (pr2 (pr2 DC)) : is_cartesian_disp_functor FF.

    Definition typecat_structure1_from_discrete_comprehension_cat_structure
      : typecat_structure1 C.
    Proof.
      exists D.
      use make_dirprod.
      - intros Γ A. exact (pr1 (disp_functor_on_objects FF A)).
      - intros Γ A Γ' f. 
        exact (pr1 (pr1 (pr1 is_discrete_fibration_D Γ Γ' f A))).
    Defined.

    Definition typecat_structure2_from_discrete_comprehension_cat_structure
      : typecat_structure2 typecat_structure1_from_discrete_comprehension_cat_structure.
    Proof.
      unfold typecat_structure2.
      repeat use tpair.
      - intros Γ A. exact (pr2 (disp_functor_on_objects FF A)).
      - intros Γ A Γ' f.
        set (k := pr2 (pr1 (pr1 is_discrete_fibration_D Γ Γ' f A))
                  : A {{f}} -->[f] A).
        apply (pr1 (disp_functor_on_morphisms FF k)).
      - intros Γ A Γ' f. simpl.
        set (k := pr2 (pr1 (pr1 is_discrete_fibration_D Γ Γ' f A))
                  : A {{f}} -->[f] A).
        apply (pr2 (disp_functor_on_morphisms FF k)).
      - simpl. intros Γ A Γ' f.
        apply isPullback_swap.
        use cartesian_isPullback_in_cod_disp.
        apply is_cartesian_FF.
        apply (unique_lift_is_cartesian (D := (_ ,, is_discrete_fibration_D)) f A).
    Defined.

    Definition typecat_structure_from_discrete_comprehension_cat_structure
      : typecat_structure C
      := (_ ,, typecat_structure2_from_discrete_comprehension_cat_structure).

    Definition is_split_typecat_from_discrete_comprehension_cat_structure
      : is_split_typecat typecat_structure_from_discrete_comprehension_cat_structure.
    Proof.
      repeat use make_dirprod.
      - apply (pr2 is_discrete_fibration_D).
      - use tpair.
        + intros Γ A. 
          set (p := pr2 (pr1 is_discrete_fibration_D Γ Γ (identity Γ) A)).
          apply (maponpaths pr1 (! p (A ,, id_disp A))).

        + intros Γ A. cbn.
          induction (! unique_lift_id is_discrete_fibration_D A).
          etrans. apply maponpaths, (disp_functor_id FF A). simpl.
          apply pathsinv0.
          etrans. apply maponpaths, maponpaths, maponpaths, maponpaths, maponpaths.
          apply pathsinv0r. simpl.
          apply idpath.

      - use tpair.
        + intros Γ A Γ' f Γ'' g.

          set (A'ff := pr1 is_discrete_fibration_D _ _ f A).
          set (ff := pr2 (pr1 A'ff) : (A {{f}}) -->[f] A).
          set (A''gg := pr1 is_discrete_fibration_D _ _ g (A {{f}})).
          set (gg := pr2 (pr1 A''gg) : ((A {{f}}) {{g}}) -->[g] A {{f}}).

          set (p := pr2 (pr1 is_discrete_fibration_D _ _ (g ;; f) A)).
          apply (maponpaths pr1 (! p ((A {{f}}) {{g}} ,, (gg ;; ff)%mor_disp))).

        + intros Γ A Γ' f Γ'' g. cbn.
          induction (! unique_lift_comp is_discrete_fibration_D f g A).
          set (A'ff := pr1 (pr1 is_discrete_fibration_D _ _ f A)).
          set (A' := pr1 A'ff).
          set (ff := pr2 A'ff).
          set (gg := pr2 (pr1 (pr1 is_discrete_fibration_D _ _ g A'))).
          etrans. apply maponpaths, (disp_functor_comp FF gg ff).
          simpl.
          apply maponpaths_2.
          etrans. apply pathsinv0, id_left.
          apply maponpaths_2.

          apply pathsinv0.
          etrans. apply maponpaths, maponpaths, maponpaths, maponpaths, maponpaths.
          apply pathsinv0r. simpl.
          apply idpath.
    Defined.

    Definition split_typecat_structure_from_discrete_comprehension_cat_structure
      : split_typecat_structure C
      := (_ ,, is_split_typecat_from_discrete_comprehension_cat_structure).

  End SplitTypeCat_from_DiscreteComprehensionCat.

  Section SplitTypeCat_from_DiscreteComprehensionCat'.

    Context {C : category}.

    Context (DC : discrete_comprehension_cat_structure' C).

    Definition split_typecat_structure_from_discrete_comprehension_cat_structure'
      : split_typecat_structure C.
    Proof.
      apply split_typecat_structure_from_discrete_comprehension_cat_structure.
      apply discrete_comprehension_cat_structure'_weq.
      apply DC.
    Defined.

  End SplitTypeCat_from_DiscreteComprehensionCat'.

  Section SplitTypeCat_DiscreteComprehensionCat_Equiv.

    Context {C : category}.

    Definition split_typecat_structure_discrete_comprehension_cat_structure'_weq
      : split_typecat_structure C ≃ discrete_comprehension_cat_structure' C.
    Proof.
      use weq_iso.
      - apply discrete_comprehension_cat_structure'_from_split_typecat_structure.
      - apply split_typecat_structure_from_discrete_comprehension_cat_structure'.
      - intros TC.
        use total2_paths_f.
        + use total2_paths_f.
          * apply idpath. (* typecat_structure1 *)
          * repeat use total2_paths_f.
            -- apply idpath. (* dpr *)
            -- apply idpath. (* q *)
            -- apply funextsec. intros ?.
               apply funextsec. intros ?.
               apply funextsec. intros ?.
               apply funextsec. intros ?.
               apply homset_property.
            -- apply funextsec. intros ?.
               apply funextsec. intros ?.
               apply funextsec. intros ?.
               apply funextsec. intros ?.
               apply isaprop_isPullback.
        + apply isaprop_is_split_typecat.
          apply homset_property.

      - intros DC.
        use total2_paths_f. 2: use total2_paths_f. 3: use total2_paths_f. 4: use total2_paths_f.
        + apply idpath.
        + apply idpath.
        + apply funextsec. intros ?.
          apply funextsec. intros ?.
          apply funextsec. intros ?.
          apply funextsec. intros ?.
          apply funextsec. intros ?.
          apply pathsinv0.
          apply (discrete_fibration_mor (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 DC)))))))).
        + apply funextsec; intros Γ.
          apply funextsec; intros Γ'.
          apply funextsec; intros A.
          apply funextsec; intros A'.
          apply funextsec; intros f.
          apply funextsec; intros ff.
          
          
          use total2_paths_f.
          etrans. apply maponpaths.
          apply pr1_transportf.
    Defined.

    Lemma ololo
          (DC : discrete_comprehension_cat_structure C)
      : pr1 (discrete_comprehension_cat_structure_from_split_typecat_structure
          (split_typecat_structure_from_discrete_comprehension_cat_structure DC))
          = pr1 DC.
    Proof.
      set (D := pr1 DC).
      set (is_discrete_fibration_D := pr1 (pr2 DC)).
      use total2_paths_f. 2: apply isaprop_disp_cat_axioms.
      use total2_paths_f.
      2: apply isaprop_disp_id_comp_of_discrete_fibration; apply is_discrete_fibration_D.
      use total2_paths_f.
      - apply idpath.
      - apply funextsec. intros ?.
        apply funextsec. intros ?.
        apply funextsec. intros ?.
        apply funextsec. intros ?.
        apply funextsec. intros ?.
        apply pathsinv0.
        apply discrete_fibration_mor.
    Defined.

    Check total2_paths2_comp1.

    Definition helper_transportf_pr1
               {A : UU} {B P : A → UU}
               (a1 a2 : A)
               (b1 : B a1) (b2 : B a2)
               (p : a1 = a2)
               (q : transportf _ p b1 = b2)
               (z : P (pr1 (a1 ,, b1)))
      : transportf (λ (x : ∑ (a : A), B a), P (pr1 x)) (two_arg_paths_f p q) z =
        transportf (λ x : A, P x) p z.
    Proof.
      induction p, q. apply idpath.
    Defined.

    Definition split_typecat_structure_discrete_comprehension_cat_structure_weq
      : split_typecat_structure C ≃ discrete_comprehension_cat_structure C.
    Proof.
      use weq_iso.
      - apply discrete_comprehension_cat_structure_from_split_typecat_structure.
      - apply split_typecat_structure_from_discrete_comprehension_cat_structure.
      - intros TC.
        use total2_paths_f.
        + use total2_paths_f.
          * apply idpath. (* typecat_structure1 *)
          * repeat use total2_paths_f.
            -- apply idpath. (* dpr *)
            -- apply idpath. (* q *)
            -- apply funextsec. intros ?.
               apply funextsec. intros ?.
               apply funextsec. intros ?.
               apply funextsec. intros ?.
               apply homset_property.
            -- apply funextsec. intros ?.
               apply funextsec. intros ?.
               apply funextsec. intros ?.
               apply funextsec. intros ?.
               apply isaprop_isPullback.
        + apply isaprop_is_split_typecat.
          apply homset_property.

      - intros DC.
        set (D := pr1 DC : disp_cat C).
        set (is_discrete_fibration_D := pr1 (pr2 DC) : is_discrete_fibration D).
        set (FF := pr1 (pr2 (pr2 DC))
                   : disp_functor (functor_identity C) D (disp_codomain C)).

        use total2_paths_f.
        2: use dirprod_paths.
        2: apply isaprop_is_discrete_fibration.
        2: use total2_paths_f.
        3: apply isaprop_is_cartesian_disp_functor.

        + apply ololo. (* disp_cat *)
          
        +
          etrans. apply maponpaths.
          apply (pr2_transportf
                   (B2 := λ x,
                          ∑ (FF : disp_functor (functor_identity C) x (disp_codomain C)),
                          is_cartesian_disp_functor FF)
                ).
          etrans.
          apply (pr1_transportf
                   _ (λ x, disp_functor (functor_identity C) x (disp_codomain C))
                ).
          simpl.

          unfold disp_functor_from_split_typecat_structure.
          use total2_paths_f. 2: apply isaprop_disp_functor_axioms.

          etrans.
          apply (pr1_transportf
                   (disp_cat C)
                   (λ x, disp_functor_data (functor_identity C) x (disp_codomain C))
                ).

          use total2_paths_f.
          * etrans.
            apply (pr1_transportf
                     (disp_cat C)
                     (λ x, ∏ c : C, x c → disp_codomain C c)).
            apply funextsec. intros Γ.
            etrans.
            apply (!helper_A (λ c (x0 : disp_cat C), x0 c → ∑ y : C, C ⟦ y, c ⟧) _ _ _).
            simpl. cbn.
            etrans.
            apply (transportf_forall_var2
                     (disp_cat C)
                     (λ y, y Γ)
                     (λ _, ∑ y0 : C, C ⟦ y0, Γ ⟧)).
            apply funextsec. intros A.

            etrans. apply transportf_const.
            apply maponpaths.
            apply (transportb_transpose_left
                     (P := λ y : disp_cat C, y Γ) (y := A) (e := ololo DC)).
            apply pathsinv0.
            etrans. apply (helper_transportf_pr1 (P := λ (x : disp_cat_data C), x Γ)).
            etrans. apply (helper_transportf_pr1 (P := λ (x : disp_cat_ob_mor C), x Γ)).
            etrans. apply (helper_transportf_pr1 (P := λ (x : C → UU), x Γ)).
            apply (idpath_transportf (λ x : C → UU, x Γ)).
          * 
            apply funextsec; intros Γ.
            apply funextsec; intros Γ'.
            apply funextsec; intros A.
            apply funextsec; intros A'.
            apply funextsec; intros f.
            apply funextsec; intros ff.

            use total2_paths_f. 2: apply homset_property.
            -- Check pr1 (pr2 (pr1 (pr1 (pr2 (pr2 DC)))) Γ Γ' A A' f ff).
               induction (discrete_fibration_mor _ _ _ _ _).
               etrans. apply maponpaths, pathsinv0.
               apply (helper_A
                        (T := C)
                        (Y := ∏ (x5 : C), pr1 DC x5 → disp_codomain C x5)
                        (λ x0 x, ∏ (y : C) (xx : pr1 DC x0) (yy : pr1 DC y) (f : C ⟦ x0, y ⟧), xx -->[f] yy → x x0 xx -->[f] x y yy)).
               apply (!helper_A (λ x0 x, ∏ y xx yy f, xx -->[f] yy → x x0 xx -->[f] x y yy)).
              etrans. apply maponpaths.
               apply pathsinv0.
               apply (pr1_transportf
                        (∏ x : C, pr1 DC x → disp_codomain C (functor_identity C x))
                     ).
    Abort.

  End SplitTypeCat_DiscreteComprehensionCat_Equiv.

  Definition discrete_comprehension_cat_from_split_typecat
    : split_typecat → discrete_comprehension_cat.
  Proof.
    intros STC.
    exists (pr1 (pr1 STC)).
    apply discrete_comprehension_cat_structure_from_split_typecat_structure.
    apply (pr2 (pr1 STC) ,, pr2 STC).
  Defined.

  Definition split_typecat_from_discrete_comprehension_cat
    : discrete_comprehension_cat → split_typecat.
  Proof.
    intros DCC.
    set (TC := split_typecat_structure_from_discrete_comprehension_cat_structure (pr2 DCC)).
    use tpair.
    - exists (pr1 DCC).
      apply (pr1 TC).
    - apply (pr2 TC).
  Defined.

End A.

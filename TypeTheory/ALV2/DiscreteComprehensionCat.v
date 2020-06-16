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

    apply unique_pr2_weq, D_ob_isaset.
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

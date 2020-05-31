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

Section A.

  Context {C : category}.

  Context (TC : split_typecat_structure C).

  Section DispCat_from_SplitTypeCat.

    Definition disp_cat_ob_mor_from_split_typecat_structure
        : disp_cat_ob_mor C.
    Proof.
        exists TC.
        intros Γ Γ' A A'.
        exact (@mor_disp _ (disp_codomain C) _ _
                        (Γ ◂ A ,, dpr_typecat A)
                        (Γ' ◂ A' ,, dpr_typecat A')).
    Defined.

    Definition disp_cat_id_comp_from_split_typecat_structure
        : disp_cat_id_comp C disp_cat_ob_mor_from_split_typecat_structure.
    Proof.
        use make_dirprod.
        - intros Γ A. apply id_disp.
        - intros Γ Γ' Γ'' f g A A' A'' ff gg. apply (comp_disp (D:=disp_codomain C) ff gg).
    Defined.

    Definition disp_cat_data_from_split_typecat_structure
        : disp_cat_data C
        := (_ ,, disp_cat_id_comp_from_split_typecat_structure).

    Definition disp_cat_axioms_from_split_typecat_structure
        : disp_cat_axioms C disp_cat_data_from_split_typecat_structure.
    Proof.
        repeat use make_dirprod.
        - intros. apply id_left_disp.
        - intros. apply id_right_disp.
        - intros. apply assoc_disp.
        - intros. apply homsets_disp.
    Defined.

    Definition disp_precat_from_split_typecat_structure
        : disp_precat C
        := (_ ,, disp_cat_axioms_from_split_typecat_structure).

    Definition disp_cat_from_split_typecat_structure
        : disp_cat C
        := disp_precat_from_split_typecat_structure.

    Definition is_discrete_fibration_disp_cat_from_split_typecat_structure
      : is_discrete_fibration disp_cat_from_split_typecat_structure.
    Proof.
      use make_dirprod. 2: apply (pr1 (pr2 TC)).
      intros Γ Γ' f A.
      use tpair.
      - exists (A {{f}}).
        use tpair.
        + apply q_typecat. 
        + apply dpr_q_typecat.
      - intros X.
        set (A' := pr1 X).
        set (q' := pr1 (pr2 X)).
        set (dpr_q' := pr2 (pr2 X)).
        simpl in *.

        

      use iscontrweqf.
      3: {
        use (reind_pb_typecat A f).
        - exact (Γ' ◂ A {{f}}).
        - exact (dpr_typecat (A {{f}})).
        - apply q_typecat.
        - apply pathsinv0, dpr_q_typecat.
      }

      use weq_iso.
      - intros X.
        set (hk := pr1 X).
        set (hk_dpr := pr1 (pr2 X)).
        set (hk_q := dirprod_pr2 (pr2 X)).
        exists (A {{f}}).
        use tpair.
        + apply hk.

      eapply weqcomp. apply weqtotal2asstor.
    Defined.

  End DispCat_from_SplitTypeCat.
  
End A.



Section T.

  Context {C : category}.

  Definition preShv_ob
             (Ty : preShv C)
    : ∏ (Γ : C), hSet
    := (Ty : functor _ _).

  Definition preShv_mor
             (Ty : preShv C)
             {Γ Γ' : C}
    : ∏ (f : Γ' --> Γ), preShv_ob Ty Γ → preShv_ob Ty Γ'
    := # (Ty : functor _ _).

  Definition preShv_mor_identity
             (Ty : preShv C)
             (Γ : C)
    : preShv_mor Ty (identity Γ) = idfun _.
  Proof.
    apply (functor_id Ty).
  Defined.

  Locate "∘".

  Definition preShv_mor_comp
             (Ty : preShv C)
             {Γ Γ' Γ'' : C}
             (f' : Γ'' --> Γ') (f : Γ' --> Γ)
    : preShv_mor Ty (f' ;; f) = (preShv_mor Ty f' ∘ preShv_mor Ty f)%functions.
  Proof.
    apply (functor_comp Ty).
  Defined.

  Definition preShv_reind_identity
             (Ty : preShv C)
             (Γ : C) (A : preShv_ob Ty Γ)
    : preShv_mor Ty (identity Γ) A = A.
  Proof.
    apply (maponpaths (λ f, f A) (preShv_mor_identity Ty Γ)).
  Defined.
  
  Definition preShv_reind_comp
             (Ty : preShv C)
             {Γ Γ' Γ'' : C}
             (f' : Γ'' --> Γ') (f : Γ' --> Γ)
             (A : preShv_ob Ty Γ)
    : preShv_mor Ty (f' ;; f) A = preShv_mor Ty f' (preShv_mor Ty f A).
  Proof.
    apply (maponpaths (λ f, f A) (preShv_mor_comp Ty f' f)).
  Defined.

  Definition split_typecat_over_preShv
             (Ty : preShv C)
    : UU
    := ∑ (ext : ∏ (Γ : C), preShv_ob Ty Γ → C)
         (dpr : ∏ (Γ : C) (A : preShv_ob Ty Γ), ext Γ A --> Γ)
         (q : ∏ (Γ : C) (A : preShv_ob Ty Γ) (Γ' : C) (f : Γ' --> Γ),
              ext Γ' (preShv_mor Ty f A) --> ext Γ A)
         (qdpr : ∏ (Γ : C) (A : preShv_ob Ty Γ) (Γ' : C) (f : Γ' --> Γ),
              q _ A _ f ;; dpr _ A = dpr _ (preShv_mor Ty f A) ;; f)
         (q_pullback : ∏ (Γ : C) (A : preShv_ob Ty Γ) (Γ' : C) (f : Γ' --> Γ),
                       isPullback _ _ _ _ (! qdpr _ A _ f)),
       (∏ (Γ : C) (A : preShv_ob Ty Γ),
        q _ A _ (identity Γ) =
        idtoiso (maponpaths (ext Γ) (preShv_reind_identity _ _ _)))
         ×
         (∏ (Γ Γ' Γ'' : C) (f' : Γ'' --> Γ') (f : Γ' --> Γ) (A : preShv_ob Ty Γ),
          q _ A _ (f' ;; f) =
          idtoiso (maponpaths (ext Γ'') (preShv_reind_comp _ _ _ _) )
          ;; q _ (preShv_mor Ty f A) _ f'
          ;; q _ A _ f).

  Definition split_typecat_structure'
    := ∑ (Ty : preShv C), split_typecat_over_preShv Ty.


  Definition split_typecat_structure_from_split_typecat_structure'
    : split_typecat_structure' → split_typecat_structure C.
  Proof.
    intros S.
    set (TY := pr1 S : functor _ _).

    set (Ty := λ (Γ : C), pr1 (functor_on_objects TY Γ)).
    set (ext := pr1 (pr2 S)).
    set (dpr := pr1 (pr2 (pr2 S))).
    set (reind := λ (Γ : C) (A : Ty Γ) (Γ' : C) (f : Γ' --> Γ), preShv_mor TY f A).
    set (q := pr1 (pr2 (pr2 (pr2 S)))).
    set (dpr_q := pr1 (pr2 (pr2 (pr2 (pr2 S))))).
    set (pb_q := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 S)))))).
    set (Ty_isaset := λ (Γ : C), pr2 (functor_on_objects TY Γ)).

    set (q_id := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 S))))))).
    set (q_comp := dirprod_pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 S))))))).

    use tpair.
    - exact ((Ty ,, ext ,, reind) ,, dpr ,, q ,, dpr_q ,, pb_q).
    - use make_dirprod.
      + exact Ty_isaset.
      + use make_dirprod.
        * exists (preShv_reind_identity TY).
          exact q_id.
        * exists (λ Γ A Γ' f Γ'' g, preShv_reind_comp TY g f A).
          exact (λ Γ A Γ' f Γ'' g, q_comp Γ Γ' Γ'' g f A).
  Defined.
  
  Definition split_typecat_structure'_from_split_typecat_structure
    : split_typecat_structure C → split_typecat_structure'.
  Proof.
    intros S.

    set (Ty := pr1 (pr1 (pr1 S))).
    set (ext := pr1 (pr2 (pr1 (pr1 S)))).
    set (reind := λ (Γ Γ' : C) (f : Γ' --> Γ) (A : Ty Γ), pr2 (pr2 (pr1 (pr1 S))) Γ A Γ' f).
    set (dpr := pr1 (pr2 (pr1 S))).
    set (q := pr1 (pr2 (pr2 (pr1 S)))).
    set (dpr_q := pr1 (pr2 (pr2 (pr2 (pr1 S))))).
    set (pb_q := pr2 (pr2 (pr2 (pr2 (pr1 S))))).

    set (Ty_isaset := pr1 (pr2 S)).
    set (reind_id := pr1 (pr1 (pr2 (pr2 S)))).
    set (q_id := pr2 (pr1 (pr2 (pr2 S)))).
    set (reind_comp := pr1 (pr2 (pr2 (pr2 S)))).
    set (q_comp := pr2 (pr2 (pr2 (pr2 S)))).

    set (Ty_ob := λ (Γ : C), (Ty Γ ,, Ty_isaset Γ)).

    use tpair.
    - use make_functor.
      + exact (Ty_ob ,, reind).
      + use tpair.
        * intros Γ. apply funextsec. intros A. apply reind_id.
        * intros Γ Γ' Γ'' f g. apply funextsec. intros A. apply reind_comp.
    - exists ext.
      exists dpr.
      exists q.
      exists dpr_q.
      exists pb_q.
      use make_dirprod.
      + intros Γ A. etrans. apply q_id.
        apply maponpaths, maponpaths, maponpaths.
        apply pathsinv0. etrans.
        unfold preShv_reind_identity, preShv_mor_identity, functor_id.
        simpl.
        apply (Univalence.maponpaths_funextsec
                 (reind _ _ (identity _))
                 (identity (Ty_ob Γ : HSET_univalent_category))).
        apply idpath.
      + intros Γ Γ' Γ'' g f A. etrans. apply q_comp.
        apply maponpaths_2, maponpaths_2.
        apply maponpaths, maponpaths, maponpaths.
        apply pathsinv0. etrans.
        unfold preShv_reind_comp, preShv_mor_comp, functor_comp.
        simpl.
        apply (@Univalence.maponpaths_funextsec
                 (Ty Γ) (λ _, Ty Γ'')
                 (reind _ _ (g;; f)%mor)
                 (reind _ _ g ∘ reind _ _ f)%functions
              ).
        apply idpath.
  Defined.

  Definition split_typecat_structure'_weq
    : split_typecat_structure' ≃ split_typecat_structure C.
  Proof.
    eapply weqcomp. apply weqtotal2asstor.
    eapply weqcomp. apply weqtotal2asstor.
    eapply weqcomp. 2: apply weqtotal2asstol.
    eapply weqcomp. 2: apply weqtotal2asstol.
    apply (weqtotal2 (idweq _)).
    unfold split_typecat_structure.
  Defined.

  Definition split_typecat_structure'_weq
    : split_typecat_structure' ≃ split_typecat_structure C.
  Proof.
    use weq_iso.
    - apply split_typecat_structure_from_split_typecat_structure'.
    - apply split_typecat_structure'_from_split_typecat_structure.
    - intros S.
      use total2_paths_f.
      + use total2_paths_f.
        * apply idpath.
        * apply isaprop_is_functor. apply homset_property.          
      + use total2_paths_f.
        * etrans. use pr1_transportf.
          cbn.
  Defined.

End T.
  

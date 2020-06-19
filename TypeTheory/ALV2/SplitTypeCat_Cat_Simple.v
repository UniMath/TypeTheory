(**
    TODO
*)

Require Import UniMath.Foundations.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Defs.
Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.ALV1.TypeCat_Reassoc.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.

Section SplitTypeCat_Cat_Simple.

  Context (C : category).

  Definition TY'
    : split_typecat_structure C → preShv C.
  Proof.
    intros TC.
    use tpair.
    - use tpair.
      + intros Γ.
        exists (TC Γ).
        apply (pr1 (pr2 TC)).
      + intros Γ Γ' f A.
        apply (reind_typecat A f).
    - use make_dirprod.
      + intros Γ. simpl. 
        use funextsec; intros A.
        apply (pr1 (pr1 (pr2 (pr2 TC)))).
      + intros Γ Γ' Γ'' f g. simpl. 
        use funextsec; intros A.
        apply (pr1 (pr2 (pr2 (pr2 TC)))).
  Defined.

  Definition TY'_TY_eq
             (TC : split_typecat_structure C)
    : TY' TC = TY (weq_standalone_to_regrouped TC).
  Proof.
    use total2_paths_f.
    - apply idpath.
    - apply isaprop_is_functor. apply homset_property.
  Defined.

  Definition SplitTy_ob_mor
    : precategory_ob_mor.
  Proof.
    use tpair.
    - apply (split_typecat_structure C).
    - intros X Y. exact (TY' X --> TY' Y).
  Defined.

  Definition SplitTy_id_comp
    : precategory_id_comp SplitTy_ob_mor.
  Proof.
    use make_dirprod.
    - intros X. apply identity.
    - intros X Y Z. apply compose.
  Defined.

  Definition SplitTy_precat_data
    : precategory_data
    := (SplitTy_ob_mor ,, SplitTy_id_comp).

  Definition SplitTy_precat_axioms
    : is_precategory SplitTy_precat_data.
  Proof.
    repeat use make_dirprod.
    - intros; apply id_left.
    - intros; apply id_right.
    - intros; apply assoc.
    - intros; apply assoc'.
  Defined.

  Definition SplitTy_precat : precategory
    := (_ ,, SplitTy_precat_axioms).

  Definition SplitTy_precat_homsets : has_homsets SplitTy_precat.
  Proof.
    unfold has_homsets.
    intros. apply homset_property.
  Defined.

  Definition SplitTy_cat : category
    := (SplitTy_precat ,, SplitTy_precat_homsets).
  
End SplitTypeCat_Cat_Simple.

Section SplitTypeCat'_Cat_Simple.

  Context (C : category).

  Definition SplitTy'_ob_mor
    : precategory_ob_mor.
  Proof.
    use tpair.
    - apply (split_typecat'_structure C).
    - intros X Y. exact (TY X --> TY Y).
  Defined.

  Definition SplitTy'_id_comp
    : precategory_id_comp SplitTy'_ob_mor.
  Proof.
    use make_dirprod.
    - intros X. apply identity.
    - intros X Y Z. apply compose.
  Defined.

  Definition SplitTy'_precat_data
    : precategory_data
    := (SplitTy'_ob_mor ,, SplitTy'_id_comp).

  Definition SplitTy'_precat_axioms
    : is_precategory SplitTy'_precat_data.
  Proof.
    repeat use make_dirprod.
    - intros; apply id_left.
    - intros; apply id_right.
    - intros; apply assoc.
    - intros; apply assoc'.
  Defined.

  Definition SplitTy'_precat : precategory
    := (_ ,, SplitTy'_precat_axioms).

  Definition SplitTy'_precat_homsets : has_homsets SplitTy'_precat.
  Proof.
    unfold has_homsets.
    intros. apply homset_property.
  Defined.

  Definition SplitTy'_cat : category
    := (SplitTy'_precat ,, SplitTy'_precat_homsets).

End SplitTypeCat'_Cat_Simple.

Section SplitTy'_mor_with_ϕ.

  

End SplitTy'_mor_with_ϕ.

Section SplitTy_SplitTy'_catiso.

  Context (C : category).

  Definition SplitTy_SplitTy'_catiso
    : catiso (SplitTy_cat C) (SplitTy'_cat C).
  Proof.
    use tpair.
    - use tpair.
      + use tpair.
        * apply weq_standalone_to_regrouped.
        * intros X Y. apply (idweq _).
      + use tpair.
        * intros X. apply idpath.
        * intros X Y Z f g. apply idpath.
    - use tpair.
      + intros X Y. apply idisweq.
      + apply (pr2 weq_standalone_to_regrouped).
  Defined.
  
End SplitTy_SplitTy'_catiso.

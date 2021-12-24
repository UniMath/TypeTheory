
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.All.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheory.
Require Import TypeTheory.Auxiliary.Partial.
Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.Initiality.SplitTypeCat_General.
Require Import TypeTheory.Initiality.SplitTypeCat_Contextual.
Require Import TypeTheory.Initiality.SplitTypeCat_Maps.
Require Import TypeTheory.Initiality.Syntax.

Section Environments.
(** _Environments_: the semantic proxy for a context, in a split type-category, giving the information needed to construct the (partial) interpretation of terms/types from some context over some object of the type-cat. *)

  (** An _environment_ over [Γ]: a map giving, for each variable from some potential context, a type and a term of that type.

  Motivating example: if [Γ] is the interpretation of some actual context, then each type of the context should be interpreted as some type over Γ, and each the corresponding variable can be extracted to a term of that type. *)

  Definition environment {C : split_typecat} (Γ:C) (n:nat)
    := dB_vars n -> type_with_term Γ.
  
  Definition fmap_environment {C C'} (F : typecat_mor C C')
      {Γ:C} {n:nat} (E : environment Γ n)
    : environment (F Γ) n.
  Proof.
    intros i. exact (fmap_type_with_term F (E i)).
  Defined.

  Definition add_to_environment {C : split_typecat}
      {Γ:C} {n} (E : environment Γ n) (Aa : type_with_term Γ)
    : environment Γ (S n).
  Proof.
    refine (dB_Sn_rect _ _ _).
    - exact Aa.
    - exact E.
  Defined.

  Lemma fmap_add_to_environment
        {C C'} (F : typecat_mor C C')
        {Γ:C} {n} (E : environment Γ n) (Aa : type_with_term Γ)
    : fmap_environment F (add_to_environment E Aa)
    = add_to_environment (fmap_environment F E) (fmap_type_with_term F Aa).
  Proof.
    apply funextfun. use dB_Sn_rect; intros; apply idpath.
  Qed.

  Definition reind_environment {C : split_typecat}
       {Γ Γ' : C} {n} (f : Γ' --> Γ) (E : environment Γ n)
    : environment Γ' n
  := fun i => (reind_type_with_term f (E i)).

  Lemma fmap_reind_environment
      {C C'} (F : typecat_mor C C')
      {Γ Γ' : C} (f : Γ' --> Γ) {n} (E : environment Γ n)
    : fmap_environment F (reind_environment f E)
    = reind_environment (# F f) (fmap_environment F E).
  Proof.
    apply funextsec; intros i.
    use paths_type_with_term2.
    - apply reindex_fmap_ty.
    - rewrite transportf_tm.
      apply reindex_fmap_tm.
  Defined.

  Definition reind_idmap_environment {C : split_typecat}
      {Γ : C} {n} (E : environment Γ n)
    : reind_environment (id _) E = E.
  Proof.
    apply funextfun; intros i; apply reind_idmap_type_with_term.
  Qed.

  Definition reind_compose_environment {C : split_typecat}
      {Γ Γ' Γ'' : C} (f : Γ' --> Γ) (f' : Γ'' --> Γ') {n} (E : environment Γ n)
    : reind_environment (f';;f) E
    = reind_environment f' (reind_environment f E).
  Proof.
    apply funextfun; intros i; apply reind_compose_type_with_term.
  Qed.

  Definition reind_add_to_environment {C : split_typecat}
      {Γ Γ' : C} (f : Γ' --> Γ)
      {n} (E : environment Γ n) (Aa : type_with_term Γ)
    : reind_environment f (add_to_environment E Aa)
      = add_to_environment (reind_environment f E)
                           (reind_type_with_term f Aa).
  Proof.
    apply funextfun; refine (dB_Sn_rect _ _ _).
    - apply idpath.
    - intros i; apply idpath.
  Qed.

  Definition empty_environment {C : split_typecat} (Γ : C)
    : environment Γ 0.
  Proof.
    intros [].
  Defined.

  Definition extend_environment {C : split_typecat}
      {Γ:C} {n:nat} (E : environment Γ n) (A : C Γ)
    : environment (Γ ◂ A) (S n)
  := add_to_environment (reind_environment (dpr_typecat A) E)
                        (var_with_type A).

  Lemma fmap_extend_environment {C C'} (F : typecat_mor C C')
      {Γ} {n} (E : environment Γ n) (A : C Γ)
    : extend_environment (fmap_environment F E) (fmap_ty F _ A)
    = reind_environment (inv_from_iso (typecat_mor_iso F _))
      (fmap_environment F (extend_environment E A)).
  Proof.
    apply pathsinv0.
    eapply pathscomp0. { apply maponpaths, fmap_add_to_environment. }
    eapply pathscomp0. { apply reind_add_to_environment. }
    apply (maponpaths_12 add_to_environment).
    - eapply pathscomp0. { apply maponpaths, fmap_reind_environment. }
      eapply pathscomp0. { apply pathsinv0, reind_compose_environment. }
      apply maponpaths_2. apply iso_inv_on_right, typecat_mor_triangle.
    - apply pathsinv0, var_with_type_fmap_type.
  Qed.

  Definition reind_extend_environment {C : split_typecat}
      {Γ Γ':C} (f : Γ' --> Γ)
      {n} (E : environment Γ n) (A : C Γ)
    : reind_environment (q_typecat A f) (extend_environment E A)
      = extend_environment (reind_environment f E) (reind_typecat A f).
  Proof.
    eapply pathscomp0. { apply reind_add_to_environment. }
    apply (maponpaths_12 add_to_environment).
    - eapply pathscomp0. { apply pathsinv0, reind_compose_environment. }
      eapply pathscomp0. 2: { apply reind_compose_environment. }
      apply maponpaths_2, dpr_q_typecat.
    - apply reind_type_with_term_q_var.
  Qed.

  Definition environment_of_extension {C : split_typecat} {Γ:C} {n}
      (AA : extension_of_length n Γ)
    : environment (ext_extension Γ AA) n.
  Proof.
    induction n as [ | n' IH].
    - apply empty_environment.
    - use extend_environment.
      apply IH.
  Defined.

End Environments.


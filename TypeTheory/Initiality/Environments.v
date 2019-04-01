
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.All.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.Partial.
Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.Initiality.SplitTypeCat_General.
Require Import TypeTheory.Initiality.SplitTypeCat_General.
Require Import TypeTheory.Initiality.SplitTypeCat_Contextual.
Require Import TypeTheory.Initiality.Syntax.

Section Environments.
(** _Environments_: the semantic proxy for a context, in a split type-category, giving the information needed to construct the (partial) interpretation of terms/types from some context over some object of the type-cat. *)

  Context {C : split_typecat}.

  (** An _environment_ over [Γ]: a map giving, for each variable from some potential context, a type and a term of that type.

  Motivating example: if [Γ] is the interpretation of some actual context, then each type of the context should be interpreted as some type over Γ, and each the corresponding variable can be extracted to a term of that type. *)

  Definition environment (Γ:C) (n:nat)
    := dB_vars n -> type_with_term Γ.
  
  Definition add_to_environment
      {Γ:C} {n} (E : environment Γ n) (Aa : type_with_term Γ)
    : environment Γ (S n).
  Proof.
    refine (dB_Sn_rect _ _ _).
    - exact Aa.
    - exact E.
  Defined.

  Definition reind_environment
       {Γ Γ'} {n} (f : Γ' --> Γ) (E : environment Γ n)
    : environment Γ' n
  := fun i => (reind_type_with_term f (E i)).

  Definition reind_idmap_environment
      {Γ} {n} (E : environment Γ n)
    : reind_environment (id _) E = E.
  Proof.
    apply funextfun; intros i; apply reind_idmap_type_with_term.
  Qed.

  Definition reind_compose_environment
      {Γ Γ' Γ''} (f : Γ' --> Γ) (f' : Γ'' --> Γ') {n} (E : environment Γ n)
    : reind_environment (f';;f) E = reind_environment f' (reind_environment f E).
  Proof.
    apply funextfun; intros i; apply reind_compose_type_with_term.
  Qed.

  Definition reind_add_to_environment
      {Γ Γ':C} (f : Γ' --> Γ)
      {n} (E : environment Γ n) (Aa : type_with_term Γ)
    : reind_environment f (add_to_environment E Aa)
      = add_to_environment (reind_environment f E)
                           (reind_type_with_term f Aa).
  Proof.
    apply funextfun; refine (dB_Sn_rect _ _ _).
    - apply idpath.
    - intros i; apply idpath.
  Qed.

  Definition empty_environment (Γ : C)
    : environment Γ 0.
  Proof.
    intros [].
  Defined.

  Definition extend_environment
      {Γ:C} {n:nat} (E : environment Γ n) (A : C Γ)
    : environment (Γ ◂ A) (S n)
  := add_to_environment (reind_environment (dpr_typecat A) E)
                        (var_with_type A).

  Definition reind_extend_environment
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

  Definition environment_of_extension {Γ:C} {n}
      (AA : extension_of_length n Γ)
    : environment (ext_extension Γ AA) n.
  Proof.
    induction n as [ | n' IH].
    - apply empty_environment.
    - use extend_environment.
      apply IH.
  Defined.

End Environments.


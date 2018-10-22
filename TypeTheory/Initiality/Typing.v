(**
  [TypeTheory.Initiality.Typing]

  Part of the [Initiality] package for the [UniMath.TypeTheory] library

  This file sets up the contexts, judgements, and derivations of the toy type theory under consideration. 
*)

Require Import UniMath.All.
Require Import TypeTheory.Initiality.Syntax.

Section Contexts.
  (** Note: for now, we take the type expressions of a context to be over
  _all_ variables of the context, not just the earlier ones.  *)
  (* TODO: add more explanation of this choice. *)
  Definition context_of_length n := dB_vars n -> ty_expr n.
  Identity Coercion id_context_of_length : context_of_length >-> Funclass.

  Definition context
    := { n : nat & context_of_length n }.

  Definition context_length : context -> nat := pr1.
  Coercion context_length : context >-> nat.

  Definition context_types : forall Γ : context, _ := pr2.
  Coercion context_types : context >-> context_of_length.

  Definition make_context {n} : context_of_length n -> context
    := fun Γ => (n,,Γ).
  Coercion make_context : context_of_length >-> context.

  Definition empty_context : context
    := make_context (dB_0_rect _).

  Definition context_extend (Γ : context) (A : ty_expr Γ) : context.
  Proof.
    exists (S (context_length Γ)).
    refine (dB_Sn_rect _ _ _).
    - exact (rename_ty dB_next A).
    - intros i. exact (rename_ty dB_next (Γ i)).
  Defined.

End Contexts.

Delimit Scope context_scope with context.
Bind Scope context_scope with context.
Bind Scope context_scope with context_of_length.
Notation "[: :]" := (empty_context) (format "[: :]") : context_scope.
Notation "Γ ; A"
  := (context_extend Γ A) (at level 50, left associativity) : context_scope. 
(* TODO: not sure what level to use here; try it and see… *)
Notation "[: A ; .. ; Z :] "
  := (context_extend .. (context_extend (empty_context) A) .. Z) : context_scope.

Section Judgements.

  Inductive judgement
  :=
    | cxt_judgement {n} (Γ : context_of_length n)
    | ty_judgement {n} (Γ : context_of_length n) (A : ty_expr n)
    | tyeq_judgement {n} (Γ : context_of_length n) (A A' : ty_expr n)
    | tm_judgement {n} (Γ : context_of_length n) (A : ty_expr n) (a : tm_expr n)
    | tmeq_judgement {n} (Γ : context_of_length n) (A : ty_expr n) (a a' : tm_expr n).

End Judgements.

Delimit Scope judgement_scope with judgement.
Bind Scope judgement_scope with judgement.
Notation "[! |- Γ !]" := (cxt_judgement Γ) : judgement_scope.
Notation "[! Γ |- A === B !]" := (tyeq_judgement Γ A B) : judgement_scope.
Notation "[! Γ |- A !]" := (ty_judgement Γ A) : judgement_scope.
Notation "[! Γ |- a ::: A !]" := (tm_judgement Γ A a) : judgement_scope.
Notation "[! Γ |- a === a' ::: A !]" := (tmeq_judgement Γ A a a') : judgement_scope.
(* NOTE: these [===], [:::] are horrible!  But I can’t make it work with just e.g. [=], since parsing fails as [=] is already a binary notation (even if the scope of that notation is closed).  Is it possible to use better scoping to allow just [=] here, and so on? *) 

Section Derivations.

  Inductive derivation : judgement -> UU
  :=
    (** context formation rules *)
    | derive_cxt_empty
      : derivation [! |- [::] !]
    | derive_cxt_extend (Γ : context) (A : ty_expr Γ)
      : derivation [! |- Γ !]
      -> derivation [! Γ |- A !]
      -> derivation [! |- Γ ; A !]
    (** variable rule *)
    | derive_var (Γ : context) (i : Γ)
      : derivation [! |- Γ !]
      -> derivation [! Γ |- Γ i !] 
      -> derivation [! Γ |- (var_expr i) ::: Γ i !]
    (** structural rules for equality: equiv rels, plus type-conversion *)
    | derive_tyeq_refl (Γ : context) (A : _)
      : derivation [! Γ |- A !]
      -> derivation [! Γ |- A === A !]
    | derive_tyeq_sym (Γ : context) (A A' : _)
      : derivation [! Γ |- A === A' !]
      -> derivation [! Γ |- A' === A !]
    | derive_tyeq_trans (Γ : context) (A0 A1 A2 : _)
      : derivation [! Γ |- A0 === A1 !]
      -> derivation [! Γ |- A1 === A2 !]
      -> derivation [! Γ |- A0 === A2 !]
    | derive_tmeq_refl (Γ : context) (A : _) (a : _)
      : derivation [! Γ |- a ::: A !]
      -> derivation [! Γ |- a === a ::: A !]
    | derive_tmeq_sym (Γ : context) (A : _) (a a' : _)
      : derivation [! Γ |- a === a' ::: A !]
      -> derivation [! Γ |- a' === a ::: A !]
    | derive_tmeq_trans (Γ : context) (A : _) (a0 a1 a2 : _)
      : derivation [! Γ |- a0 === a1 ::: A !]
      -> derivation [! Γ |- a1 === a2 ::: A !]
      -> derivation [! Γ |- a0 === a2 ::: A !]
    | derive_tm_conv (Γ : context) (A A' : _) (a : _)
      : derivation [! Γ |- A === A' !]
      -> derivation [! Γ |- a ::: A !]
      -> derivation [! Γ |- a ::: A' !]
    | derive_tmeq_conv (Γ : context) (A A' : _) (a a' : _)
      : derivation [! Γ |- A === A' !]
      -> derivation [! Γ |- a === a' ::: A !]
      -> derivation [! Γ |- a === a' ::: A' !]
    (** substitution rules *)
    | derive_subst_ty
        (Γ Γ' : context) (f : raw_context_map Γ' Γ) (A : _)
      : derivation [! |- Γ !]
    -> (forall i:Γ, derivation [! Γ' |- f i ::: subst_ty f (Γ i) !])
      -> derivation [! Γ |- A !]
      -> derivation [! Γ' |- subst_ty f A !]
    | derive_subst_tyeq
        (Γ Γ' : context) (f : raw_context_map Γ' Γ) (A A' : _)
      : derivation [! |- Γ !]
      -> (forall i:Γ, derivation [! Γ' |- f i ::: subst_ty f (Γ i) !])
      -> derivation [! Γ |- A === A' !]
      -> derivation [! Γ' |- subst_ty f A === subst_ty f A' !]
    | derive_subst_tm
        (Γ Γ' : context) (f : raw_context_map Γ' Γ) (A : _) (a : _)
      : derivation [! |- Γ !]
      -> (forall i:Γ, derivation [! Γ' |- f i ::: subst_ty f (Γ i) !])
      -> derivation [! Γ |- a ::: A !]
      -> derivation [! Γ' |- subst_tm f a ::: (subst_ty f A) !]
    | derive_subst_tmeq
        (Γ Γ' : context) (f : raw_context_map Γ' Γ) (A : _) (a a' : _)
      : derivation [! |- Γ !]
      -> (forall i:Γ, derivation [! Γ' |- f i ::: subst_ty f (Γ i) !])
      -> derivation [! Γ |- a === a' ::: A !]
      -> derivation [! Γ' |- subst_tm f a === subst_tm f a' ::: subst_ty f A !]
    (** substitution-equality rules *)
    | derive_substeq_ty
        (Γ Γ' : context) (f f' : raw_context_map Γ' Γ) (A : _)
      : derivation [! |- Γ !]
      -> (forall i:Γ, derivation [! Γ' |- f i === f' i ::: subst_ty f (Γ i) !])
      -> derivation [! Γ |- A !]
      -> derivation [! Γ' |- subst_ty f A === subst_ty f' A !] 
    | derive_substeq_tm
        (Γ Γ' : context) (f f' : raw_context_map Γ' Γ) (A : _) (a : _)
      : derivation [! |- Γ !]
      -> (forall i:Γ, derivation [! Γ' |- f i === f' i ::: subst_ty f (Γ i) !])
      -> derivation [! Γ |- a ::: A !]
      -> derivation [! Γ' |- subst_tm f a === subst_tm f' a ::: subst_ty f A !] 
    (** logical rules  *)
    | derive_U (Γ : context) 
      : derivation [! |- Γ !]
        -> derivation [! Γ |- U_expr !]
    | derive_El (Γ : context) (a : _)
      : derivation [! |- Γ !]
        -> derivation [! Γ |- a ::: U_expr !]
        -> derivation [! Γ |- El_expr a !]
    | derive_Pi (Γ : context) (A : _) (B : _)
      : derivation [! |- Γ !]
        -> derivation [! Γ |- A !]
        -> derivation [! Γ ; A |- B !]
        -> derivation [! Γ |- Pi_expr A B !]
    | derive_lam (Γ : context) A B b
      : derivation [! |- Γ !]
        -> derivation [! Γ |- A !]
        -> derivation [! Γ ; A |- B !]
        -> derivation [! Γ ; A |- b ::: B !]
        -> derivation [! Γ |- lam_expr A B b ::: Pi_expr A B !]
    | derive_app (Γ : context) A B f a
      : derivation [! |- Γ !]
        -> derivation [! Γ |- A !]
        -> derivation [! Γ ; A |- B !]
        -> derivation [! Γ |- f ::: Pi_expr A B !]
        -> derivation [! Γ |- a ::: A !]
        -> derivation [! Γ |- app_expr A B f a ::: subst_ty_top a B !]
    | derive_beta (Γ : context) A B b a
      : derivation [! |- Γ !]
        -> derivation [! Γ |- A !]
        -> derivation [! Γ ; A |- B !]
        -> derivation [! Γ ; A |- b ::: B !]
        -> derivation [! Γ |- a ::: A !]
        -> derivation
             [! Γ |- app_expr A B (lam_expr A B b) a === subst_tm_top a b 
                                                     ::: subst_ty_top a B !]
    (** congruence rules for constructors *)
    (* no congruence rule needed for U *)
    | derive_El_cong (Γ : context) (a a' : _)
      : derivation [! |- Γ !]
        -> derivation [! Γ |- a === a' ::: U_expr !]
        -> derivation [! Γ |- El_expr a === El_expr a' !]
    | derive_Pi_cong (Γ : context) (A A' : _) (B B' : _)
      : derivation [! |- Γ !]
        -> derivation [! Γ |- A === A' !]
        -> derivation [! Γ ; A |- B === B' !]
        -> derivation [! Γ |- Pi_expr A B === Pi_expr A' B' !]
    | derive_lam_cong (Γ : context) A A' B B' b b'
      : derivation [! |- Γ !]
        -> derivation [! Γ |- A === A' !]
        -> derivation [! Γ ; A |- B === B' !]
        -> derivation [! Γ ; A |- b === b' ::: B !]
        -> derivation [! Γ |- lam_expr A B b === lam_expr A' B' b' ::: Pi_expr A B !]
    | derive_app_cong (Γ : context) A A' B B' f f' a a'
      : derivation [! |- Γ !]
        -> derivation [! Γ |- A === A' !]
        -> derivation [! Γ ; A |- B === B' !]
        -> derivation [! Γ |- f === f' ::: Pi_expr A B !]
        -> derivation [! Γ |- a === a' ::: A !]
        -> derivation [! Γ |- app_expr A B f a === app_expr A' B' f' a'
                                                   ::: subst_ty_top a B !]
  .
End Derivations.
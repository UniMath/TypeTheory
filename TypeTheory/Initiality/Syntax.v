(**
  [TypeTheory.Initiality.Syntax]

  Part of the [Initiality] package for the [UniMath.TypeTheory] library

  Goal: as elementary as possible a proof of initiality, for a specific fairly straightforward type theory, but written with an eye to extensibility.

  This file constructs raw syntax, along the main constructions on it (variable-renaming, substitution).

  It aims to give as streamlined as possible a path to the definition of judgements/derivations, so basic lemmas about substitution etc are deferred to [Initiality.SyntaxLemmas]. 
*)


Require Import UniMath.All.
Require Import TypeTheory.Auxiliary.Auxiliary.

Section deBruijn.
  (** We first set up the machinery for handling variables, represented by de Bruijn indices. *)

  Definition dB_empty : UU := empty.

  Inductive dB_plusone (X : UU) : UU := dB_top_internal | dB_next_internal (x:X).

  Global Arguments dB_top_internal {_}.
  Global Arguments dB_next_internal {_} _.

  (** [dB_vars n]: the set of variables in scope over a context of length [n]. 

  As far as possible, this should be interfaced with just through [dB_top], [dB_next], and [dB_rect] below. *)
  Fixpoint dB_vars (n : nat) : UU
    := match n with
       | O => dB_empty
       | S n => dB_plusone (dB_vars n)
       end.

  Global Arguments dB_vars !_ .

  Coercion dB_vars : nat >-> UU.

  Definition dB_top {n} : dB_vars (S n)
    := dB_top_internal.

  Definition dB_next {n} : dB_vars n -> dB_vars (S n)
    := dB_next_internal.

(** We should always interface with [dB_vars] just through [dB_top], [dB_next], and the following two recursors. *)
  Definition dB_0_rect
      (P : dB_vars 0 -> Type)
    : forall i, P i.
  Proof.
    intros [].
  Defined.

  Definition dB_Sn_rect {n}
      (P : dB_vars (S n) -> Type)
      (p_top : P dB_top)
      (p_next : forall i, P (dB_next i))
    : forall i, P i.
  Proof.
    exact (dB_plusone_rect _ P p_top p_next).
  Defined.

  Arguments dB_Sn_rect : simpl nomatch.

  (** We check that [dB_Sn_rect] computes appropriately, concluding with [Abort] since we don’t need to save the results. *) 
  Definition dB_Sn_rect_comp1 {n}
      (P : dB_vars (S n) -> Type)
      (p_top : P dB_top)
      (p_next : forall i, P (dB_next i))
    : dB_Sn_rect P p_top p_next dB_top = p_top.
  Proof.
    intros. apply idpath.
  Abort. (* Proof a test only, not for saving. *)

  Definition dB_Sn_rect_comp2 {n}
      (P : dB_vars (S n) -> Type)
      (p_top : P dB_top)
      (p_next : forall i, P (dB_next i))
    : forall i, dB_Sn_rect P p_top p_next (dB_next i) = p_next i.
  Proof.
    intros. apply idpath.
  Abort. (* Proof a test only, not for saving. *) 

  (** Further auxiliary constructions *)
  Definition fmap_dB_S {m n} (f : dB_vars m -> dB_vars n)
    : dB_vars (S m) -> dB_vars (S n).
  Proof.
    apply dB_Sn_rect.
    - apply dB_top.
    - intros i. apply dB_next, f, i.
  Defined.

End deBruijn.

Section Expressions.

  Inductive ty_expr : nat -> UU
  :=
    | U_expr {n} : ty_expr n
    | El_expr {n} : tm_expr n -> ty_expr n
    | Pi_expr {n} : ty_expr n -> ty_expr (S n) -> ty_expr n
    | Nat_expr {n} : ty_expr n
  with tm_expr : nat -> UU
  :=
    | var_expr {n} : dB_vars n -> tm_expr n
    | lam_expr {n} : ty_expr n -> ty_expr (S n) -> tm_expr (S n)
                      -> tm_expr n
    | app_expr {n} : ty_expr n -> ty_expr (S n)
                      -> tm_expr n -> tm_expr n
                      -> tm_expr n
    | zero_expr {n} : tm_expr n
    | suc_expr {n} : tm_expr n -> tm_expr n
    | natrec_expr {n} : ty_expr (S n)
                        -> tm_expr n -> tm_expr (S (S n))
                        -> tm_expr n
                        -> tm_expr n.
                              
End Expressions.

Section Renaming.
(** Renaming variables in raw expressions.  This can be seen as a special case of substitution, or as the functoriality of expressions in the variables of the context.  Functoriality lemmas are given in [Initiality.SyntaxLemmas]. *)

  Fixpoint
    rename_ty {m n : nat} (f : m -> n) (e : ty_expr m) : ty_expr n
  with
    rename_tm {m n : nat} (f : m -> n) (e : tm_expr m) : tm_expr n.
  Proof.
    - (* rename_ty *)
      destruct e as [ m | m a | m A B | m ].
      + (* case [U_expr] *)
        exact U_expr.
      + (* case [El_expr] *)
        exact (El_expr (rename_tm _ _ f a)).
      + (* case [Pi_expr] *)
        refine (Pi_expr (rename_ty _ _ f A) _).
        refine (rename_ty _ _ (fmap_dB_S f) B).
      + (* case [Nat_expr] *)
        exact Nat_expr.
    - (* rename_tm *)
      destruct e as [ m i | m A B b | m A B g a
                    | m | m a | m P dZ dS a ].
      + (* case [var_expr] *)
        apply var_expr, f, i.
      + (* case [lam_expr] *)
        refine (lam_expr _ _ _).
        * exact (rename_ty _ _ f A).
        * exact (rename_ty _ _ (fmap_dB_S f) B).
        * exact (rename_tm _ _ (fmap_dB_S f) b).
      + (* case [app_expr] *)
        refine (app_expr _ _ _ _).
        * exact (rename_ty _ _ f A).
        * exact (rename_ty _ _ (fmap_dB_S f) B).
        * exact (rename_tm _ _ f g).
        * exact (rename_tm _ _ f a).
      + (* case [zero_expr] *)
        exact zero_expr.
      + (* case [suc_expr] *)
        apply suc_expr, (rename_tm _ _ f), a.
      + (* case [natrec_expr] *)
        refine (natrec_expr _ _ _ _).
        * exact (rename_ty _ _ (fmap_dB_S f) P).
        * exact (rename_tm _ _ f dZ).
        * exact (rename_tm _ _ (fmap_dB_S (fmap_dB_S f)) dS).
        * exact (rename_tm _ _ f a).
  Defined.

End Renaming.

Section Raw_Context_Maps.
(** AKA “substitutions”. *)

  Definition raw_context_map n m := dB_vars m -> tm_expr n.

  Identity Coercion id_raw_context_map : raw_context_map >-> Funclass.

  Definition idmap_raw_context n : raw_context_map n n.
  Proof.
    exact var_expr.
  Defined.

  Definition add_to_raw_context_map
      {m n} (f : raw_context_map n m) (a : tm_expr n)
    : raw_context_map n (S m)
  := dB_Sn_rect _ a f.

  Definition weaken_raw_context_map {n m}
      : raw_context_map n m -> raw_context_map (S n) (S m).
  Proof.
    intros f. refine (add_to_raw_context_map _ _).
    - intros i. exact (rename_tm dB_next (f i)).
    - apply var_expr, dB_top.
  Defined.

End Raw_Context_Maps.

Section Substitution.

  Fixpoint
    subst_ty {m n} (f : raw_context_map n m) (e : ty_expr m) {struct e} : ty_expr n
  with
    subst_tm {m n} (f : raw_context_map n m) (e : tm_expr m) {struct e} : tm_expr n.
  Proof.
    - (* subst_ty *)
      destruct e as [ m | m a | m A B | m ].
      + (* case [U_expr] *)
        exact U_expr.
      + (* case [El_expr] *)
        exact (El_expr (subst_tm _ _ f a)).
      + (* case [Pi_expr] *)
        refine (Pi_expr (subst_ty _ _ f A) _).
        refine (subst_ty _ _ (weaken_raw_context_map f) B).
      + (* case [Nat_expr] *)
        exact Nat_expr.
    - (* subst_tm *)
      destruct e as [ m i | m A B b | m A B g a
                    | m | m a | m P dZ dS a ].
      + (* case [var_expr] *)
        apply f, i.
      + (* case [lam_expr] *)
        refine (lam_expr _ _ _).
        * exact (subst_ty _ _ f A).
        * exact (subst_ty _ _ (weaken_raw_context_map f) B).
        * exact (subst_tm _ _ (weaken_raw_context_map f) b).
      + (* case [app_expr] *)
        refine (app_expr _ _ _ _).
        * exact (subst_ty _ _ f A).
        * exact (subst_ty _ _ (weaken_raw_context_map f) B).
        * exact (subst_tm _ _ f g).
        * exact (subst_tm _ _ f a).
      + (* case [zero_expr] *)
        exact zero_expr.
      + (* case [suc_expr] *)
        apply suc_expr, (subst_tm _ _ f), a.
      + (* case [natrec_expr] *)
        refine (natrec_expr _ _ _ _).
        * exact (subst_ty _ _ (weaken_raw_context_map f) P).
        * exact (subst_tm _ _ f dZ).
        * exact (subst_tm _ _ (weaken_raw_context_map
                                 (weaken_raw_context_map f)) dS).
        * exact (subst_tm _ _ f a).
  Defined.



  (** Some auxiliary functions for common special cases *)

  (** Substituting just the “top” variable, as in the typing rule for [app],
   or the conclusion of beta-reduction. *)
  Definition tm_as_raw_context_map {n} (a : tm_expr n)
    : raw_context_map n (S n)
  := add_to_raw_context_map (idmap_raw_context _) a.

  Definition subst_top_ty {n} (a : tm_expr n) (e : ty_expr (S n)) : ty_expr n
    := subst_ty (tm_as_raw_context_map a) e.

  Definition subst_top_tm {n} (a : tm_expr n) (e : tm_expr (S n)) : tm_expr n
    := subst_tm (tm_as_raw_context_map a) e.

End Substitution.

(**
  [TypeTheory.Initiality.Syntax]

  Part of the [Initiality] package for the [UniMath.TypeTheory] library

  Goal: as elementary as possible a proof of initiality, for a specific fairly straightforward type theory, but written with an eye to extensibility.
*)

Require Import UniMath.All.

Section deBruijn.

  Definition dB_vars : nat -> UU
    := stn.

  Coercion dB_vars : nat >-> UU.

  (** UniMath defines [stn] using [<], which is based on [natgtb],
  which takes 0 as its base case.  So we take 0 to be the “most recent” variable,
  i.e. de Bruij _indices_ not de Bruijn _levels_. *)
  Definition dB_top {n} : dB_vars (S n)
    := (0,, idpath _).

  Definition dB_next {n} : dB_vars n -> dB_vars (S n)
    := fun k_p => (S (pr1 k_p) ,, pr2 k_p).

  (** We should always interface with [dB_vars] just through [dB_top], [dB_next], and the following two recursors. *)
  Definition dB_0_rect
      (P : dB_vars 0 -> Type)
    : forall i, P i.
  Proof.
    intros [k lt_k_0]. cbn in lt_k_0.
    destruct (nopathsfalsetotrue lt_k_0).
  Defined.

  Definition dB_Sn_rect {n}
      (P : dB_vars (S n) -> Type)
      (p_top : P dB_top)
      (p_next : forall i, P (dB_next i))
    : forall i, P i.
  Proof.
    intros [k lt_k_n].
    destruct k as [ | k']; simpl in lt_k_n.
    - refine (transportf _ _ p_top).
      unfold dB_top; eapply maponpaths.
      apply isasetbool.
    - exact (p_next (k',, lt_k_n)).
  Defined.

  (** We check that [dB_Sn_rect] computes appropriately, concluding with [Abort] since we don’t need to save the results. *) 
  Definition dB_Sn_rect_comp1 {n}
      (P : dB_vars (S n) -> Type)
      (p_top : P dB_top)
      (p_next : forall i, P (dB_next i))
    : dB_Sn_rect P p_top p_next dB_top = p_top.
  Proof.
    intros. apply idpath.
  Abort.

  Definition dB_Sn_rect_comp2 {n}
      (P : dB_vars (S n) -> Type)
      (p_top : P dB_top)
      (p_next : forall i, P (dB_next i))
    : forall i, dB_Sn_rect P p_top p_next (dB_next i) = p_next i.
  Proof.
    intros. apply idpath.
  Abort.

  (** Further constructions *)
  Definition fmap_dB_S {m n} (f : stn m -> stn n) : stn (S m) -> stn (S n).
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
  with tm_expr : nat -> UU
  :=
    | var_expr {n} : dB_vars n -> tm_expr n
    | lam_expr {n} : ty_expr n -> ty_expr (S n) -> tm_expr (S n)
                      -> tm_expr n
    | app_expr {n} : ty_expr n -> ty_expr (S n)
                      -> tm_expr n -> tm_expr n
                      -> tm_expr n.
End Expressions.

Section Renaming.

  Fixpoint
    rename_ty {m n} (f : stn m -> stn n) (e : ty_expr m) : ty_expr n
  with
    rename_tm {m n} (f : stn m -> stn n) (e : tm_expr m) : tm_expr n.
  Proof.
    - (* rename_ty *)
      destruct e as [ m | m a | m A B ].
      + (* case [U_expr] *)
        exact U_expr.
      + (* case [El_expr] *)
        exact (El_expr (rename_tm _ _ f a)).
      + (* case [Pi_expr] *)
        refine (Pi_expr (rename_ty _ _ f A) _).
        refine (rename_ty _ _ (fmap_dB_S f) B).
    - (* rename_tm *)
      destruct e as [ m i | m A B b | m A B g a ].
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
  Defined.

End Renaming.

Section Substitution.

  Definition raw_context_map n m := stn m -> tm_expr n.

  Definition weaken_raw_context_map {n m}
      : raw_context_map n m -> raw_context_map (S n) (S m).
  Proof.
    intros f. refine (dB_Sn_rect _ _ _).
    - apply var_expr, dB_top.
    - intros i. exact (rename_tm dB_next (f i)).
  Defined.

  Fixpoint
    subst_ty {m n} (f : stn m -> tm_expr n) (e : ty_expr m) : ty_expr n
  with
    subst_tm {m n} (f : stn m -> tm_expr n) (e : tm_expr m) : tm_expr n.
  Proof.
    - (* subst_ty *)
      destruct e as [ m | m a | m A B ].
      + (* case [U_expr] *)
        exact U_expr.
      + (* case [El_expr] *)
        exact (El_expr (subst_tm _ _ f a)).
      + (* case [Pi_expr] *)
        refine (Pi_expr (subst_ty _ _ f A) _).
        refine (subst_ty _ _ (weaken_raw_context_map f) B).
    - (* subst_tm *)
      destruct e as [ m i | m A B b | m A B g a ].
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
  Defined.

End Substitution.

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

Section Judgements.

  Inductive judgement
  :=
    | cxt_judgement {n} (Γ : context_of_length n)
    | ty_judgement {n} (Γ : context_of_length n) (A : ty_expr n)
    | tyeq_judgement {n} (Γ : context_of_length n) (A A' : ty_expr n)
    | tm_judgement {n} (Γ : context_of_length n) (A : ty_expr n) (a : tm_expr n)
    | tmeq_judgement {n} (Γ : context_of_length n) (A : ty_expr n) (a a' : tm_expr n).

End Judgements.

Section Derivations.

  Inductive derivation : judgement -> UU
  :=
    (** context formation rules *)
    | derive_cxt_empty
      : derivation (cxt_judgement empty_context)
    | derive_cxt_extend (Γ : context) (A : ty_expr Γ)
      : derivation (cxt_judgement Γ)
      -> derivation (ty_judgement Γ A)
      -> derivation (cxt_judgement (context_extend Γ A))
    (** variable rule *)
    | derive_var (Γ : context) (i : Γ)
      : derivation (cxt_judgement Γ)
      -> derivation (ty_judgement Γ (Γ i))
      -> derivation (tm_judgement Γ (Γ i) (var_expr i))
    (** substitution rules *)
    | derive_subst_ty
        (Γ Γ' : context) (f : raw_context_map Γ' Γ)
        (A : _)
      : (forall i:Γ, derivation (tm_judgement Γ' (subst_ty f (Γ i)) (f i)))
        -> derivation (ty_judgement Γ A)
        -> derivation (ty_judgement Γ' (subst_ty f A))
    | derive_subst_tyeq
        (Γ Γ' : context) (f : raw_context_map Γ' Γ)
        (A A' : _)
      : (forall i:Γ, derivation (tm_judgement Γ' (subst_ty f (Γ i)) (f i)))
        -> derivation (tyeq_judgement Γ A A')
        -> derivation (tyeq_judgement Γ' (subst_ty f A) (subst_ty f A'))
    | derive_subst_tm
        (Γ Γ' : context) (f : raw_context_map Γ' Γ)
        (A : _) (a : _)
      : (forall i:Γ, derivation (tm_judgement Γ' (subst_ty f (Γ i)) (f i)))
        -> derivation (tm_judgement Γ A a)
        -> derivation (tm_judgement Γ' (subst_ty f A) (subst_tm f a))
    | derive_subst_tmeq
        (Γ Γ' : context) (f : raw_context_map Γ' Γ)
        (A : _) (a a' : _)
      : (forall i:Γ, derivation (tm_judgement Γ' (subst_ty f (Γ i)) (f i)))
        -> derivation (tmeq_judgement Γ A a a')
        -> derivation (tmeq_judgement Γ' (subst_ty f A) (subst_tm f a) (subst_tm f a'))
  . 


End Derivations.
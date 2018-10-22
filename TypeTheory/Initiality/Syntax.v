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
  i.e. de Bruijn _indices_ not de Bruijn _levels_. *)
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
    (** typing rules for constructors  *)
    (* TODO *)
    (** congruence rules for constructors *)
    (* TODO *)
  .


End Derivations.
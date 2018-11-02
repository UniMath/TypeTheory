(**
  [TypeTheory.Initiality.SyntaxLemmas]

  Part of the [Initiality] package for the [UniMath.TypeTheory] library

  This file proves the various structural lemmas on renaming and substitution in the syntax, that (among other uses) will become the axioms for the syntactic category.
*)

Require Import UniMath.All.
Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Initiality.Syntax.

Section deBruijn.

  Definition fmap_idfun_dB_S {n} : fmap_dB_S (idfun (dB_vars n)) = idfun _.
  Proof.
    apply funextsec. refine (dB_Sn_rect _ _ _); auto.
  Defined.

  Definition fmap_compose_dB_S {m n p : nat} (f : m -> n) (g : n -> p)
    : fmap_dB_S (g ∘ f) = (fmap_dB_S g) ∘ (fmap_dB_S f).
  Proof.
    apply funextsec. refine (dB_Sn_rect _ _ _); auto.
  Defined.

End deBruijn.


Section Renaming.

  Fixpoint
    rename_ty_idfun {n} (e : ty_expr n) : rename_ty (idfun _) e = e
  with 
    rename_tm_idfun {n} (e : tm_expr n) : rename_tm (idfun _) e = e.
  Proof.
    - (* rename_ty_idfun *)
      destruct e as [ m | m a | m A B ];
        cbn;
        eauto using maponpaths, maponpaths_12, pathscomp0, fmap_idfun_dB_S.
    - (* rename_tm_idfun *)
      destruct e as [ m i | m A B b | m A B g a ]; cbn; 
        [ idtac | apply maponpaths_123 | apply maponpaths_1234 ];
        eauto using pathscomp0, maponpaths_2, fmap_idfun_dB_S.
  Defined.

  Fixpoint
    rename_comp_ty {m n p : nat } (f : m -> n) (g : n -> p)
      (e : ty_expr m)
    : rename_ty (g ∘ f) e = rename_ty g (rename_ty f e)
  with 
    rename_comp_tm {m n p : nat } (f : m -> n) (g : n -> p)
      (e : tm_expr m)
    : rename_tm (g ∘ f) e = rename_tm g (rename_tm f e).
  Proof.
    - (* rename_ty_idfun *)
      destruct e as [ m | m a | m A B ];
        cbn;
        [ idtac | apply maponpaths | apply maponpaths_12 ];
        eauto using pathscomp0, maponpaths_2, fmap_compose_dB_S.
    - (* rename_tm_idfun *)
      destruct e as [ m i | m A B b | m A B t a ];
        cbn;
        [ idtac | apply maponpaths_123 | apply maponpaths_1234 ];
        eauto using pathscomp0, maponpaths_2, fmap_compose_dB_S.
  Defined.

End Renaming.

(** Identity and composition of raw context maps. *)
Section Raw_Context_Category_Operations.

  (** [idmap_raw_context] already defined in [Initiality.Syntax]. *)

  Definition comp_raw_context {m n p}
      (f : raw_context_map m n)
      (g : raw_context_map n p)
    : raw_context_map m p
  := fun i => subst_tm f (g i).

  Definition weaken_idmap {n}
      : weaken_raw_context_map (idmap_raw_context n) = idmap_raw_context _.
  Proof.
    apply funextsec. refine (dB_Sn_rect _ _ _); auto.
  Defined.

End Raw_Context_Category_Operations.

(** Interaction of substitution with renaming/weakening *)
Section Substitution.

  Fixpoint
    subst_idmap_ty {n} (e : ty_expr n)
      : subst_ty (idmap_raw_context n) e = e
  with 
    subst_idmap_tm {n} (e : tm_expr n)
    : subst_tm (idmap_raw_context n) e = e.
  Proof.
    - (* rename_ty_idfun *)
      destruct e as [ m | m a | m A B ];
        cbn;
        [ idtac | apply maponpaths | apply maponpaths_12 ];
        eauto using maponpaths, maponpaths_12, pathscomp0, weaken_idmap.
    - (* rename_tm_idfun *)
      destruct e as [ m i | m A B b | m A B g a ];
        cbn;
        [ idtac | apply maponpaths_123 | apply maponpaths_1234 ];
        eauto using maponpaths, maponpaths_12, pathscomp0, weaken_idmap.
  Defined.

(** This lemma [weaken_precomp_renaming] can be seen as a special case of [weaken_comp] (i.e. [weaken_raw_context_map] preserving composition), when one of the maps in the composite is just a renaming of variables. *)
  Lemma weaken_precomp_renaming
      {m n p : nat} (f : m -> n) (g : raw_context_map p n)
    : weaken_raw_context_map g ∘ fmap_dB_S f =
      weaken_raw_context_map (g ∘ f).
  Proof.
    apply funextsec.
    refine (dB_Sn_rect _ _ _); intros; apply idpath.
  Defined.

  Fixpoint
    subst_rename_ty {m n p : nat} (f : m -> n) (g : raw_context_map p n)
      (e : ty_expr m)
    : subst_ty g (rename_ty f e)
      = subst_ty (g ∘ f) e
  with
    subst_rename_tm {m n p : nat} (f : m -> n) (g : raw_context_map p n)
      (e : tm_expr m)
    : subst_tm g (rename_tm f e)
      = subst_tm (g ∘ f) e.
  Proof.
    - (* type case *)
      destruct e as [ m | m a | m A B ];
        cbn;
        [ idtac | apply maponpaths | apply maponpaths_12 ];
        eauto using pathscomp0, maponpaths_2, weaken_precomp_renaming. 
    - (* term case *)
      destruct e as [ m i | m A B b | m A B t a ];
        cbn;
        [ idtac | apply maponpaths_123 | apply maponpaths_1234 ];
        eauto using pathscomp0, maponpaths_2, weaken_precomp_renaming. 
  Defined.

(** This lemma [weaken_postcomp_renaming] can be seen as a special case of [weaken_comp] (i.e. [weaken_raw_context_map] preserving composition), when one of the maps in the composite is just a renaming of variables. *)
  Lemma weaken_postcomp_renaming
      {m n p : nat} (f : raw_context_map n m) (g : n -> p)
    : rename_tm (fmap_dB_S g) ∘ weaken_raw_context_map f =
    weaken_raw_context_map (rename_tm g ∘ f).
  Proof.
    apply funextsec.
    refine (dB_Sn_rect _ _ _). { apply idpath. }
    intros i.
    refine (_ @ rename_comp_tm _ _ _).
    refine (!rename_comp_tm _ _ _).
  Defined.
  
  Fixpoint
    rename_subst_ty {m n p : nat} (f : raw_context_map n m) (g : n -> p)
      (e : ty_expr m)
    : rename_ty g (subst_ty f e)
      = subst_ty ((rename_tm g) ∘ f) e
  with
    rename_subst_tm {m n p : nat} (f : raw_context_map n m) (g : n -> p)
      (e : tm_expr m)
    : rename_tm g (subst_tm f e)
      = subst_tm ((rename_tm g) ∘ f) e.
  Proof.
    - (* type case *)
      destruct e as [ m | m a | m A B ];
        cbn;
        [ idtac | apply maponpaths | apply maponpaths_12 ];
        eauto using pathscomp0, maponpaths_2, weaken_postcomp_renaming. 
    - (* term case *)
      destruct e as [ m i | m A B b | m A B t a ];
        cbn;
        [ idtac | apply maponpaths_123 | apply maponpaths_1234 ];
        eauto using pathscomp0, maponpaths_2, weaken_postcomp_renaming.
  Defined.

  (** A functoriality property for [weaken_raw_context_map]. *)
  Lemma weaken_comp
      {m n p : nat} (g : raw_context_map p n) (f : raw_context_map n m)
    : comp_raw_context
        (weaken_raw_context_map g) (weaken_raw_context_map f) =
      weaken_raw_context_map (comp_raw_context g f).
  Proof.
    apply funextsec.
    refine (dB_Sn_rect _ _ _). { apply idpath. }
    intros i.
    cbn. eapply pathscomp0. { apply subst_rename_tm. }
    apply pathsinv0. apply rename_subst_tm.
  Defined.

  Fixpoint
    subst_subst_ty {m n p} (f : raw_context_map n m) (g : raw_context_map p n)
      (e : ty_expr m)
    : subst_ty g (subst_ty f e)
      = subst_ty (comp_raw_context g f) e
  with
    subst_subst_tm {m n p} (f : raw_context_map n m) (g : raw_context_map p n)
      (e : tm_expr m)
    : subst_tm g (subst_tm f e)
      = subst_tm (comp_raw_context g f) e.
  Proof.
    - (* type case *)
      destruct e as [ m | m a | m A B ];
        cbn;
        [ idtac | apply maponpaths | apply maponpaths_12 ];
        eauto using pathscomp0, maponpaths_2, weaken_comp. 
    - (* term case *)
      destruct e as [ m i | m A B b | m A B t a ];
        cbn;
        [ idtac | apply maponpaths_123 | apply maponpaths_1234 ];
        eauto using pathscomp0, maponpaths_2, weaken_comp. 
  Defined.

End Substitution.

(** The lemmas which will become the axioms of the category of raw contexts.

These follow almost directly from the lemmas in [Substitution] above. *)
Section Raw_Context_Category_Axioms.

  Lemma id_right_raw_context {m n} (f : raw_context_map m n)
    : comp_raw_context f (idmap_raw_context _) = f.
  Proof.
    apply idpath.
  Defined.

  Lemma id_left_raw_context {m n} (f : raw_context_map m n)
    : comp_raw_context (idmap_raw_context _) f = f.
  Proof.
    apply funextsec; intro i.
    apply subst_idmap_tm.
  Defined.

  Lemma assoc_raw_context
        {m n p q} (f : raw_context_map m n)
        (g : raw_context_map n p) (h : raw_context_map p q)
    : comp_raw_context (comp_raw_context f g) h
    = comp_raw_context f (comp_raw_context g h).
  Proof.
    apply funextsec; intro i.
    apply pathsinv0, subst_subst_tm.
  Defined.

End Raw_Context_Category_Axioms.

Section Miscellaneous.

  Lemma rename_tm_as_raw_context_map {m n : nat} (f : m -> n) (a : tm_expr m)
    : rename_tm f ∘ tm_as_raw_context_map a
    = tm_as_raw_context_map (rename_tm f a) ∘ fmap_dB_S f.
  Proof.
    use funextfun; use dB_Sn_rect; intros; apply idpath.
  Defined. 

  Lemma comp_tm_as_raw_context_map
      {m n : nat} (f : raw_context_map m n) (a : tm_expr n)
    : comp_raw_context f (tm_as_raw_context_map a)
    = comp_raw_context (tm_as_raw_context_map (subst_tm f a))
                       (weaken_raw_context_map f).
  Proof.
    use funextfun; use dB_Sn_rect; cbn.
    - apply idpath.
    - intros i. apply pathsinv0.
      eapply pathscomp0. { apply subst_rename_tm. }
      use subst_idmap_tm.
  Defined.

  Lemma rename_subst_top_ty {m n : nat} (f : m -> n)
      (A : ty_expr (S m)) (a : tm_expr m)
    : rename_ty f (subst_top_ty a A)
      = subst_top_ty (rename_tm f a) (rename_ty (fmap_dB_S f) A). 
  Proof.
    unfold subst_top_ty.
    eapply pathscomp0. { apply rename_subst_ty. }
    eapply pathscomp0. 2: { apply pathsinv0, subst_rename_ty. }
    apply maponpaths_2, rename_tm_as_raw_context_map.
  Defined.

  Lemma rename_subst_top_tm {m n : nat} (f : m -> n)
      (A : tm_expr (S m)) (a : tm_expr m)
    : rename_tm f (subst_top_tm a A)
      = subst_top_tm (rename_tm f a) (rename_tm (fmap_dB_S f) A). 
  Proof.
    unfold subst_top_tm.
    eapply pathscomp0. { apply rename_subst_tm. }
    eapply pathscomp0. 2: { apply pathsinv0, subst_rename_tm. }
    apply maponpaths_2, rename_tm_as_raw_context_map.
  Defined.

  Lemma subst_subst_top_ty {n m : nat} (f :raw_context_map n m)
      (A : ty_expr (S m)) (a : tm_expr m)
    : subst_ty f (subst_top_ty a A)
      = subst_top_ty (subst_tm f a) (subst_ty (weaken_raw_context_map f) A). 
  Proof.
    unfold subst_top_ty.
    eapply pathscomp0. { apply subst_subst_ty. }
    eapply pathscomp0. 2: { apply pathsinv0, subst_subst_ty. }
    apply maponpaths_2, comp_tm_as_raw_context_map.
  Defined.

  Lemma subst_subst_top_tm {n m : nat} (f :raw_context_map n m)
      (A : tm_expr (S m)) (a : tm_expr m)
    : subst_tm f (subst_top_tm a A)
      = subst_top_tm (subst_tm f a) (subst_tm (weaken_raw_context_map f) A). 
  Proof.
    unfold subst_top_tm.
    eapply pathscomp0. { apply subst_subst_tm. }
    eapply pathscomp0. 2: { apply pathsinv0, subst_subst_tm. }
    apply maponpaths_2, comp_tm_as_raw_context_map.
  Defined.

  Lemma subst_weaken_rename_ty
      {m n} (f : raw_context_map m n) (A : ty_expr n)
    : subst_ty (weaken_raw_context_map f) (rename_ty dB_next A)
      = rename_ty dB_next (subst_ty f A).
  Proof.
    eapply pathscomp0. { apply subst_rename_ty. }
    apply pathsinv0, rename_subst_ty.
  Defined.

  Lemma subst_weaken_rename_tm
      {m n} (f : raw_context_map m n) (a : tm_expr n)
    : subst_tm (weaken_raw_context_map f) (rename_tm dB_next a)
      = rename_tm dB_next (subst_tm f a).
  Proof.
    eapply pathscomp0. { apply subst_rename_tm. }
    apply pathsinv0, rename_subst_tm.
  Defined.

End Miscellaneous.

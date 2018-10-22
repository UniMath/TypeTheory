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
  Admitted.

End Renaming.

(** Identity and composition of raw context maps. *)
Section Raw_Context_Category_Operations.

  Local Definition idmap_raw_context n : raw_context_map n n.
  Proof.
    exact var_expr.
  Defined.

  Local Definition comp_raw_context {m n p}
      (f : raw_context_map m n)
      (g : raw_context_map n p)
    : raw_context_map m p
  := fun i => subst_tm f (g i).

End Raw_Context_Category_Operations.

(** Lemmas phrased explicitly about interaction of substitution with other constructions *)
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
        eauto using maponpaths, maponpaths_12, pathscomp0, weaken_var_expr.
    - (* rename_tm_idfun *)
      destruct e as [ m i | m A B b | m A B g a ];
        cbn;
        [ idtac | apply maponpaths_123 | apply maponpaths_1234 ];
        eauto using maponpaths, maponpaths_12, pathscomp0, weaken_var_expr.
  Defined.

(* the following lemma is a naturality for weakening w.r.t. renaming:
  hom(n,m) ———— g ; _ ————> hom(p,n)
     |                         |
     V                         V
 hom(Sn,Sm) —— S g ; _ ——> hom(Sp,Sm)
*)
  Lemma rename_weaken
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
        eauto using pathscomp0, maponpaths_2, rename_weaken. 
    - (* term case *)
      destruct e as [ m i | m A B b | m A B t a ];
        cbn;
        [ idtac | apply maponpaths_123 | apply maponpaths_1234 ];
        eauto using pathscomp0, maponpaths_2, rename_weaken.
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
  Admitted.

  Fixpoint
    subst_comp_ty {m n p} (f : raw_context_map n m) (g : raw_context_map p n)
      (e : ty_expr m)
    : subst_ty g (subst_ty f e)
      = subst_ty (comp_raw_context g f) e
  with
    subst_comp_tm {m n p} (f : raw_context_map n m) (g : raw_context_map p n)
      (e : tm_expr m)
    : subst_tm g (subst_tm f e)
      = subst_tm (comp_raw_context g f) e.
  Proof.
  Admitted.

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
    apply pathsinv0, subst_comp_tm.
  Defined.

End Raw_Context_Category_Axioms.
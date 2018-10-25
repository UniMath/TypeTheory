(** This file defines the interpretation function, from the syntax of our toy type theory into any split type-cat with suitable structure. *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.All.

(* TODO: raise issue upstream: notation "_ ∘ _" is used for function-order composition of functions, but for diagrammatic-order composition of morphisms in categories! *)

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.Partial.
Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.Initiality.SplitTypeCat_Maps.
Require Import TypeTheory.Initiality.SplitTypeCat_Structure.
Require Import TypeTheory.Initiality.Syntax.
Require Import TypeTheory.Initiality.Typing.

Local Open Scope functions.
Local Arguments funcomp {_ _ _} _ / . (* perhaps upstream? *)

Section Auxiliary.

  (** Functions giving path types in various hsets directly as hprops. *)
  (* TODO: work out better way to treat them? *)
  Definition mor_paths_hProp {C : category} {X Y : C} (f g : X --> Y)
    : hProp
  := hProppair (f = g) (homset_property C _ _ _ _).

  Definition type_paths_hProp {C : split_typecat} {Γ : C} (A B : C Γ)
    : hProp
  := hProppair (A = B) (isaset_types_typecat C _ _ _).

  Definition tm_paths_hProp {C : split_typecat} {Γ : C} {A : C Γ} (s t : tm A)
    : hProp
  := hProppair (s = t) (isaset_tm _ _).

  Context {C : split_typecat}.

  (* TODO: perhaps upstream the following group? *)
  Definition term_with_type (Γ:C) := ∑ (A : C Γ), tm A.

  Definition type_of {Γ} (Aa : term_with_type Γ) := pr1 Aa.

  Coercion term_of {Γ} (Aa : term_with_type Γ) : tm (type_of Aa)
    := pr2 Aa.

  Definition reind_term_with_type {Γ Γ'} (f : Γ' --> Γ)
    : term_with_type Γ -> term_with_type Γ'
  := fun a => ((type_of a)⦃f⦄,, reind_tm f a).
  
End Auxiliary.

Section Environments.
(** _Environments_: the semantic proxy for a context, in a split type-category, giving the information needed to construct the (partial) interpretation of terms/types from some context over some object of the type-cat. *)

  Context {C : split_typecat}.

  (** An _environment_ over [Γ]: a map giving, for each variable from some potential context, a type and a term of that type.

  Motivating example: if [Γ] is the interpretation of some actual context, then each type of the context should be interpreted as some type over Γ, and each the corresponding variable can be extracted to a term of that type. *)

  Definition environment (Γ:C) (n:nat)
    := dB_vars n -> term_with_type Γ.
  
  Definition extend_environment
      {Γ:C} {n:nat} (E : environment Γ n) (A : C Γ)
    : environment (Γ ◂ A) (S n).
  Proof.
    refine (dB_Sn_rect _ _ _).
    - exists (A ⦃dpr_typecat A⦄).
      apply var_typecat.
    - intro i.
      exact (reind_term_with_type (dpr_typecat A) (E i)).
  Defined.

  Definition reind_environment
      {Γ Γ'} (f : Γ' --> Γ) {n} (E : environment Γ n)
    : environment Γ' n
  := fun i => (reind_term_with_type f (E i)).

  Definition reind_extend_environment
      {Γ Γ':C} (f : Γ' --> Γ)
      {n} (E : environment Γ n) (A : C Γ)
    : reind_environment (q_typecat A f) (extend_environment E A)
      = extend_environment (reind_environment f E) (reind_typecat A f).
  Proof.
    apply funextfun; refine (dB_Sn_rect _ _ _); admit.
  Admitted.

End Environments.

Section Partial_Interpretation.
(** In this section, we construct the partial interpretation function. *)

  Fixpoint
    partial_interpretation_ty {C} (U : universe_struct C) (Π : pi_struct C)
      {Γ:C} {n:nat} (E : environment Γ n) (e : ty_expr n)
    : partial (C Γ)
  with
    partial_interpretation_tm {C} (U : universe_struct C) (Π : pi_struct C)
      {Γ:C} {n:nat} (E : environment Γ n) (T : C Γ) (e : tm_expr n)
    : partial (tm T). (* See note below re type. *)
  Proof.
    - (* type expressions *)
      destruct e as [ m | m a | m A B ].
      + (* [U_expr] *)
        apply return_partial, U.
      + (* [El_expr a] *)
        get_partial (partial_interpretation_tm _ U Π _ _ E (U _) a) interp_a.
        apply return_partial. exact (@elements _ U _ interp_a).
      + (* [Pi_expr A B] *)
        get_partial (partial_interpretation_ty _ U Π _ _ E A) interp_A.
        set (E_A := extend_environment E interp_A).
        get_partial (partial_interpretation_ty _ U Π _ _ E_A B) interp_B.
        apply return_partial. exact (Π _ interp_A interp_B).
    - (* term expressions *)
      destruct e as [ m i | m A B b | m A B f a ].
      + (* [var_expr i] *)
        assume_partial (type_paths_hProp (type_of (E i)) T) e_Ei_T.
        apply return_partial.
        exact (tm_transportf e_Ei_T (E i)).
      + (* [lam_expr A B b] *)
        get_partial (partial_interpretation_ty _ U Π _ _ E A) interp_A.
        set (E_A := extend_environment E interp_A).
        get_partial (partial_interpretation_ty _ U Π _ _ E_A B) interp_B.
        get_partial (partial_interpretation_tm _ U Π _ _ E_A interp_B b) interp_b.
        assume_partial (type_paths_hProp (Π _ interp_A interp_B) T) e_ΠAB_T.
        apply return_partial.
        refine (tm_transportf e_ΠAB_T _).
        exact (pi_intro _ _ _ _ _ interp_b).
      + (* [app_expr A B f a] *)
        get_partial (partial_interpretation_ty _ U Π _ _ E A) interp_A.
        set (E_A := extend_environment E interp_A).
        get_partial (partial_interpretation_ty _ U Π _ _ E_A B) interp_B.
        set (Π_A_B := Π _ interp_A interp_B).
        get_partial (partial_interpretation_tm _ U Π _ _ E interp_A a) interp_a.
        get_partial (partial_interpretation_tm _ U Π _ _ E Π_A_B f) interp_f. 
        assume_partial (type_paths_hProp (interp_B ⦃interp_a⦄) T) e_Ba_T.
        apply return_partial.
        refine (tm_transportf e_Ba_T _).
        refine (pi_app _ _ _ _ _ interp_f interp_a).
  Defined.

  (** Note: alternatively, we could give the interpretation of terms as 
   [ partial_interpretation_tm
       {Γ:C} {n:nat} (E : environment Γ n) (e : tm_expr n)
     : partial (term_with_type Γ). ]
  I think either should work fine; I’m not sure which will work more cleanly. *)

  Context {C} (U : universe_struct C) (Π : pi_struct C).
  (** Note: the section variables are assumed only _after_ the definition of the partial interpretation, since otherwise after they are generalized, it explodes under [simpl]/[cbn]. *)

  (** We start with several (lax) naturality properties for the partial
  interpretation: naturality with respect to context maps and renaming of
  variables. *)

  Lemma tm_transportf_partial_interpretation_tm 
      {Γ:C} {n:nat} (E : environment Γ n) {T T' : C Γ} (e_T_T' : T = T')
      (e : tm_expr n)
    : fmap_partial (tm_transportf e_T_T')
        (partial_interpretation_tm U Π E T e)
      = partial_interpretation_tm U Π E T' e.
  Proof.
    destruct e_T_T'.
    eapply pathscomp0.
    2: { refine (toforallpaths _ _ _ (fmap_idmap_partial _) _). }
    apply maponpaths_2, funextfun. use @tm_transportf_idpath.
  Qed.

  Lemma tm_transportf_partial_interpretation_tm_leq
      {Γ:C} {n:nat} (E : environment Γ n) {T T' : C Γ} (e_T_T' : T = T')
      (e : tm_expr n)
    : leq_partial
        (fmap_partial (tm_transportf e_T_T')
          (partial_interpretation_tm U Π E T e))
        (partial_interpretation_tm U Π E T' e).
  Proof.
    apply leq_partial_of_path,
    tm_transportf_partial_interpretation_tm.
  Qed.

  (** Naturality of the partial interpretation,
  with respect to indexing along maps of the model.

  NOTE: the proof is written carefully to make the structure of cases
  as modular and uniform as possible.  Roughly, there is a section for each
  [bind_partial] and [assume_partial] in the definition of the partial
  interpretation; [fmap_partial] is always pushed on through these to the end.
  At the end of each case, one should find essentially the naturality equation
  for the constuctor under consideration, modulo some occurrences of
  [tm_transportf] which must be wrangled away. *)
  (* TODO: can these patterns be abstracted as lemmas? *)
  Fixpoint
    reindex_partial_interpretation_ty
      {Γ Γ':C} (f : Γ' --> Γ)
      {n:nat} (E : environment Γ n) (e : ty_expr n)
    : leq_partial
        (fmap_partial (fun A => reind_typecat A f)
           (partial_interpretation_ty U Π E e))
        (partial_interpretation_ty U Π (reind_environment f E) e)
  with
    reindex_partial_interpretation_tm
      {Γ Γ':C} (f : Γ' --> Γ)
      {n:nat} (E : environment Γ n) (T : C Γ) (e : tm_expr n)
    : leq_partial
        (fmap_partial (fun t => reind_tm f t)
           (partial_interpretation_tm U Π E T e))
        (partial_interpretation_tm U Π (reind_environment f E) (T⦃f⦄) e).
  Proof.
    - (* type expressions *)
      destruct e as [ m | m a | m A B ].
      + (* [U_expr] *)
        cbn. apply leq_partial_of_path.
        eapply pathscomp0. { apply fmap_return_partial. }
        apply maponpaths, universe_natural.
      + (* [El_expr a] *)
        assert (IH_a := fun T =>
          reindex_partial_interpretation_tm Γ Γ' f m E T a).
        (* part for [a] argument *)
        cbn. eapply leq_partial_trans.
        { apply leq_partial_of_path, fmap_bind_partial. }
        eapply leq_partial_trans.
        2: { eapply bind_leq_partial_1. 
          eapply leq_partial_trans.
          2: { refine (tm_transportf_partial_interpretation_tm_leq _ _ _).
               apply universe_natural. }
             apply fmap_leq_partial, IH_a. }
        eapply leq_partial_trans.
        2: { apply leq_partial_of_path, pathsinv0.
             eapply pathscomp0; apply bind_fmap_partial_1. }
        apply bind_leq_partial_2; intros a_interp; cbn.
        (* final naturality part *)
        apply leq_partial_of_path.
        eapply pathscomp0. { apply fmap_return_partial. }
        apply maponpaths, elements_natural.
      + (* [Pi_expr A B] *)
        assert (IH_A := 
                  reindex_partial_interpretation_ty Γ Γ' f m E A).
        assert (IH_B := fun Γ Γ' f E =>
                          reindex_partial_interpretation_ty Γ Γ' f (S m) E B).
        (* part for [A] argument *)
        cbn. eapply leq_partial_trans.
        { apply leq_partial_of_path, fmap_bind_partial. }
        eapply leq_partial_trans.
        2: { eapply bind_leq_partial_1, IH_A. }
        eapply leq_partial_trans.
        2: { apply leq_partial_of_path, pathsinv0, bind_fmap_partial_1. }
        apply bind_leq_partial_2; intros A_interp; cbn.
        (* part for [B] argument *)
        eapply leq_partial_trans.
        { apply leq_partial_of_path, fmap_bind_partial. }
        eapply leq_partial_trans.
        2: { eapply bind_leq_partial_1.
             eapply leq_partial_trans.
             2: { apply leq_partial_of_path.
                  apply maponpaths_2, reind_extend_environment. }
             apply (IH_B _ _ (q_typecat A_interp f)). }
        eapply leq_partial_trans.
        2: { apply leq_partial_of_path, pathsinv0, bind_fmap_partial_1. }
        apply bind_leq_partial_2; intros B_interp; cbn.
        (* final naturality part *)
        apply leq_partial_of_path.
        eapply pathscomp0. { apply fmap_return_partial. }
        apply maponpaths, pi_form_struct_natural.
    - (* term expressions *)
      destruct e as [ m i | m A B b | m A B t a ].
      + (* [var_expr i] *)
        cbn. eapply leq_partial_trans.
        { apply leq_partial_of_path, fmap_assume_partial. }
        use assume_partial_leq. { exact (maponpaths (fun A => A ⦃ f ⦄)). }
        cbn. intros e_T; destruct e_T.
        apply leq_partial_of_path.
        eapply pathscomp0. { apply fmap_return_partial. }
        apply maponpaths. cbn.
        eapply pathscomp0. { apply maponpaths, tm_transportf_idpath. }
        apply pathsinv0, tm_transportf_idpath.
      + (* [lam_expr A B b] *)
        assert (IH_A := 
          reindex_partial_interpretation_ty Γ Γ' f m E A).
        assert (IH_B := fun Γ Γ' f E =>
          reindex_partial_interpretation_ty Γ Γ' f (S m) E B).
        assert (IH_b := fun Γ Γ' f E T =>
          reindex_partial_interpretation_tm Γ Γ' f (S m) E T b).
        (* Note: the beginning of this, dealing with the [A B] inputs,
           is almost exactly a copy-paste from the [Pi_expr A B] case
           (and similarly for the [app_expr] case below). *)
        (* part for [A] argument *)
        cbn. eapply leq_partial_trans.
        { apply leq_partial_of_path, fmap_bind_partial. }
        eapply leq_partial_trans.
        2: { eapply bind_leq_partial_1, IH_A. }
        eapply leq_partial_trans.
        2: { apply leq_partial_of_path, pathsinv0, bind_fmap_partial_1. }
        apply bind_leq_partial_2; intros A_interp; cbn.
        (* part for [B] argument *)
        eapply leq_partial_trans.
        { apply leq_partial_of_path, fmap_bind_partial. }
        eapply leq_partial_trans.
        2: { eapply bind_leq_partial_1.
             eapply leq_partial_trans.
             2: { apply leq_partial_of_path.
                  apply maponpaths_2, reind_extend_environment. }
             apply (IH_B _ _ (q_typecat A_interp f)). }
        eapply leq_partial_trans.
        2: { apply leq_partial_of_path, pathsinv0, bind_fmap_partial_1. }
        apply bind_leq_partial_2; intros B_interp; cbn.
        (* part for [b] argument *)
        eapply leq_partial_trans.
        { apply leq_partial_of_path, fmap_bind_partial. }
        eapply leq_partial_trans.
        2: { eapply bind_leq_partial_1.
          eapply leq_partial_trans.
          2: { apply leq_partial_of_path.
            eapply (maponpaths (fun E => partial_interpretation_tm _ _ E _ _)),
                   reind_extend_environment. }
          apply (IH_b _ _ (q_typecat A_interp f)). }
        eapply leq_partial_trans.
        2: { apply leq_partial_of_path, pathsinv0, bind_fmap_partial_1. }
        apply bind_leq_partial_2; intros b_interp; cbn.
        (* part for assumption on [T] *)
        eapply leq_partial_trans.
        { eapply leq_partial_of_path, fmap_assume_partial. }
        use assume_partial_leq.
        { cbn; intros e_T.
          eapply pathscomp0. 2: { eapply (maponpaths (fun A => A ⦃f⦄)), e_T. }
          apply pathsinv0, pi_form_struct_natural. }
        cbn. intros e_T; destruct e_T.
        (* final naturality part *)
        apply leq_partial_of_path. cbn.
        eapply pathscomp0. { apply fmap_return_partial. }
        apply maponpaths. rewrite tm_transportf_idpath.
        eapply pathscomp0. { apply pi_intro_struct_natural. }
        apply tm_transportf_irrelevant.
      + (* [app_expr A B t a] *)
        assert (IH_A := 
          reindex_partial_interpretation_ty Γ Γ' f m E A).
        assert (IH_B := fun Γ Γ' f E =>
          reindex_partial_interpretation_ty Γ Γ' f (S m) E B).
        assert (IH_t := fun T =>
          reindex_partial_interpretation_tm Γ Γ' f m E T t).
        assert (IH_a := fun T =>
          reindex_partial_interpretation_tm Γ Γ' f m E T a).
        (* part for [A] argument *)
        cbn. eapply leq_partial_trans.
        { apply leq_partial_of_path, fmap_bind_partial. }
        eapply leq_partial_trans.
        2: { eapply bind_leq_partial_1, IH_A. }
        eapply leq_partial_trans.
        2: { apply leq_partial_of_path, pathsinv0, bind_fmap_partial_1. }
        apply bind_leq_partial_2; intros A_interp; cbn.
        (* part for [B] argument *)
        eapply leq_partial_trans.
        { apply leq_partial_of_path, fmap_bind_partial. }
        eapply leq_partial_trans.
        2: { eapply bind_leq_partial_1.
             eapply leq_partial_trans.
             2: { apply leq_partial_of_path.
                  apply maponpaths_2, reind_extend_environment. }
             apply (IH_B _ _ (q_typecat A_interp f)). }
        eapply leq_partial_trans.
        2: { apply leq_partial_of_path, pathsinv0, bind_fmap_partial_1. }
        apply bind_leq_partial_2; intros B_interp; cbn.
        (* part for [a] argument *)
        eapply leq_partial_trans.
        { apply leq_partial_of_path, fmap_bind_partial. }
        eapply leq_partial_trans.
        2: { eapply bind_leq_partial_1, IH_a. }
        eapply leq_partial_trans.
        2: { apply leq_partial_of_path, pathsinv0, bind_fmap_partial_1. }
        apply bind_leq_partial_2; intros a_interp; cbn.
        (* part for [t] argument *)
        eapply leq_partial_trans.
        { apply leq_partial_of_path, fmap_bind_partial. }
        eapply leq_partial_trans.
        2: { eapply bind_leq_partial_1.
          eapply leq_partial_trans.
          2: { refine (tm_transportf_partial_interpretation_tm_leq _ _ _). 
               apply pi_form_struct_natural. }
          apply fmap_leq_partial, IH_t. }
        eapply leq_partial_trans.
        2: { apply leq_partial_of_path, pathsinv0.
             eapply pathscomp0; apply bind_fmap_partial_1. }
        apply bind_leq_partial_2; intros t_interp; cbn.
        (* assumption on [T] *)
        eapply leq_partial_trans.
        { eapply leq_partial_of_path, fmap_assume_partial. }
        use assume_partial_leq.
        { cbn; intros e_T.
          eapply pathscomp0. 2: { eapply (maponpaths (fun A => A ⦃f⦄)), e_T. }
          eapply pathscomp0. { apply pathsinv0, (reind_comp_typecat C). }
          eapply pathscomp0. 2: { apply (reind_comp_typecat C). }
          (* TODO: unify duplicate access functions [reind_comp_typecat],
             [reind_comp_type_typecat]. *)
          apply maponpaths, reind_tm_q. }
        cbn. intros e_T; destruct e_T.
        (* final naturality part *)
        apply leq_partial_of_path. cbn.
        eapply pathscomp0. { apply fmap_return_partial. }
        apply maponpaths. rewrite tm_transportf_idpath.
        eapply pathscomp0. { apply pi_app_struct_natural. }
        apply tm_transportf_irrelevant.
  Qed.

  Fixpoint
    partial_interpretation_rename_ty
      {Γ} {m n:nat} (f : m -> n)
      (E : environment Γ n) (e : ty_expr m)
    : leq_partial
        (partial_interpretation_ty U Π (E ∘ f) e)
        (partial_interpretation_ty U Π E (rename_ty f e))
  with
    partial_interpretation_rename_tm
      {Γ} {m n:nat} (f : m -> n)
      (E : environment Γ n) (T : C Γ) (e : tm_expr m)
    : leq_partial
        (partial_interpretation_tm U Π (E ∘ f) T e)
        (partial_interpretation_tm U Π E T (rename_tm f e)).
  Proof.
    - (* type expressions *)
      destruct e as [ m | m a | m A B ].
      + (* [U_expr] *)
        apply leq_partial_refl.
      + (* [El_expr a] *)
        cbn. apply bind_leq_partial_1.
        apply partial_interpretation_rename_tm.
      + (* [Pi_expr A B] *)
        cbn. eapply bind_leq_partial.
        { apply partial_interpretation_rename_ty. }
        intros A_interp. apply bind_leq_partial_1.
        eapply leq_partial_trans.
        2: { apply partial_interpretation_rename_ty. }
        apply leq_partial_of_path, maponpaths_2, funextfun.
        refine (dB_Sn_rect _ _ _); intros; apply idpath.
    - (* term expressions *)
      destruct e as [ m i | m A B b | m A B t a ].
      + (* [var_expr i] *)
        apply leq_partial_refl.
      + (* [lam_expr A B b] *)
        simpl. eapply bind_leq_partial.
        { apply partial_interpretation_rename_ty. }
        intros A_interp.
        assert (e : (extend_environment (E ∘ f) A_interp
                     = extend_environment E A_interp ∘ fmap_dB_S f)).
        { apply funextfun. refine (dB_Sn_rect _ _ _); intros; apply idpath. }
        eapply bind_leq_partial.
        { eapply leq_partial_trans.
          2: { apply partial_interpretation_rename_ty. }
          apply leq_partial_of_path, maponpaths_2, e.
        }
        intros B_interp.
        eapply bind_leq_partial.
        { eapply leq_partial_trans.
          2: { apply partial_interpretation_rename_tm. }
          apply leq_partial_of_path.
          refine (maponpaths (fun F => _ F _ _) e).
        }
        intros b_interp.
        apply leq_partial_refl.
      + (* [app_expr A B f a] *)
        simpl. eapply bind_leq_partial.
        { apply partial_interpretation_rename_ty. }
        intros A_interp.
        assert (e : (extend_environment (E ∘ f) A_interp
                     = extend_environment E A_interp ∘ fmap_dB_S f)).
        { apply funextfun. refine (dB_Sn_rect _ _ _); intros; apply idpath. }
        eapply bind_leq_partial.
        { eapply leq_partial_trans.
          2: { apply partial_interpretation_rename_ty. }
          apply leq_partial_of_path, maponpaths_2, e.
        }
        intros B_interp.
        eapply bind_leq_partial.
        { apply partial_interpretation_rename_tm. }
        intros a_interp.
        eapply bind_leq_partial.
        { apply partial_interpretation_rename_tm. }
        intros t_interp.
        apply leq_partial_refl.
  Defined.

End Partial_Interpretation.

Section Partial_Interpretation_Substitution.
(** The interaction of the partial interpretation with substitution requires
a little more work to state. *)

  Context {C} (U : universe_struct C) (Π : pi_struct C).

  (* TODO: consider naming, placement, life choices, etc *)
  Definition subst_environment 
      {X} {m n:nat} (f : raw_context_map m n) (A : n -> C X)
      (E : environment X m)
    : partial (environment X n). 
  Proof.
    assume_partial
      (∀ (i:n), is_defined (partial_interpretation_tm U Π E (A i) (f i)))
      H.
    apply return_partial.
    intros i. exists (A i). exact (evaluate (H i)).
  Defined.

  Fixpoint
    partial_interpretation_subst_ty
      {X} {m n:nat} (f : raw_context_map m n) (T : n -> C X)
      (E : environment X m) (fE_def : is_defined (subst_environment f T E))
      (e : ty_expr n)
    : leq_partial
        (partial_interpretation_ty U Π (evaluate fE_def) e)
        (partial_interpretation_ty U Π E (subst_ty f e))
  with
    partial_interpretation_subst_tm
      {X} {m n:nat} (f : raw_context_map m n) (T : n -> C X)
      (E : environment X m) (fE_def : is_defined (subst_environment f T E))
      (S : C X) (e : tm_expr n)
    : leq_partial
        (partial_interpretation_tm U Π (evaluate fE_def) S e)
        (partial_interpretation_tm U Π E S (subst_tm f e)).
  Proof.
    - (* type expressions *)
      destruct e as [ n | n a | n A B ]; cbn.
      + (* [U_expr] *)
        apply leq_partial_refl.
      + (* [El_expr a] *)
        apply bind_leq_partial_1.
        apply partial_interpretation_subst_tm.
      + (* [Pi_expr A B] *)
        cbn. eapply bind_leq_partial.
        { apply partial_interpretation_subst_ty. }
        intros A_interp. apply bind_leq_partial_1.
        admit. (* need lemma on extending environment,
        should be provable from [reindex_partial_interpretation]
        together with [partial_interpretation_rename]. *)
    - (* term expressions *)
      destruct e as [ n i | n A B b | n A B t a ]; admit.
  Admitted.

End Partial_Interpretation_Substitution.

Section Totality.

  Context {C : split_typecat} (U : universe_struct C) (Π : pi_struct C).
 
  Definition environment_respects_type
      {X : C} (Γ : context) (E : environment X Γ)
    : UU
  := forall i : Γ,
    ∑ (d : is_defined (partial_interpretation_ty U Π E (Γ i))),
      (type_of (E i) = evaluate d).

  Definition typed_environment (X : C) (Γ : context)
    := ∑ (E : environment X Γ), environment_respects_type Γ E.

  Coercion environment_of_typed_environment {X} {Γ}
    (E : typed_environment X Γ) : environment X Γ
  := pr1 E.

  Definition typed_environment_respects_types {X} {Γ}
    (E : typed_environment X Γ) (i : Γ)
  := pr2 E i.

  Local Open Scope judgement_scope.

  (** We show a fairly _weak_ sense of interpretatbility for judgements:
  given an interpretation of their boundary, we get one of their conclusion.

  This works smoothly in many ways, but requires quite “paranoid” formulations
  of the derivation rules.  A stronger definition of “interpretatability” could
  allow the proof to work with less paranoid formulations of the rules. 

  Note we also don’t ask anything for interpretability of the context judgement. *)
  Definition is_interpretable (J : judgement) : hProp
  := match J with
     | [! |- Γ !] => htrue
     | [! Γ |- A !]
       => ∀ (X:C) (E : typed_environment X Γ),
         is_defined (partial_interpretation_ty U Π E A)         
     | [! Γ |- A === A' !]
       => ∀ (X:C) (E : typed_environment X Γ)
            (d_A : is_defined (partial_interpretation_ty U Π E A))   
            (d_A' : is_defined (partial_interpretation_ty U Π E A')),
         type_paths_hProp (evaluate d_A) (evaluate d_A') 
     | [! Γ |- a ::: A !]
       => ∀ (X:C) (E : typed_environment X Γ)
            (d_A : is_defined (partial_interpretation_ty U Π E A)), 
         is_defined (partial_interpretation_tm U Π E (evaluate d_A) a)
     | [! Γ |- a === a' ::: A !]
       => ∀ (X:C) (E : typed_environment X Γ)
          (d_A : is_defined (partial_interpretation_ty U Π E A))
          (d_a : is_defined (partial_interpretation_tm U Π E (evaluate d_A) a)) 
          (d_a' : is_defined (partial_interpretation_tm U Π E (evaluate d_A) a')), 
         tm_paths_hProp (evaluate d_a) (evaluate d_a')
  end.
  (* Note: we DON’T expect to need any inductive information for context judgements!

  Essentially, our rules have been set up carefully enough that (hopefully) the context judgement could be removed entirely without loss. *)

  Lemma is_interpretable_is_prop {J} : isaprop (is_interpretable J).
  Proof.
    destruct J; eauto using propproperty. 
  Defined.
  
  Local Lemma interpret_context_rules
    : cases_for_context_rules (fun J _ => is_interpretable J).
  Proof.
    split; intros; cbn; constructor.
  Defined.

  Local Lemma interpret_var_rule
    : case_for_var_rule (fun J _ => is_interpretable J).
  Proof.
    intros ? ? ? H_Γ ? H_Γi.
    intros X E Γi_interpretable.
    refine (_,,tt); cbn.
    eapply pathscomp0. { apply typed_environment_respects_types. }
    apply maponpaths, propproperty.
  Defined.

  Local Lemma interpret_equiv_rel_rules
    : cases_for_equiv_rel_rules (fun J _ => is_interpretable J).
  Proof.
    split.
    - intros; intros ? ? ? ?.
      apply maponpaths, propproperty.
    - intros ? ? ? ? p_AA' ? ? ? ?.
      apply pathsinv0; use p_AA'. 
    - intros ? ? ? ? ? ? ? p1 ? ? ? p01 ? p12 ? ? ? ?.
      eapply pathscomp0; [ use p01 | use p12 ]. use p1.
    - intros; intros ? ? ? ? ?.
      apply maponpaths, propproperty.
    - intros ? ? ? ? ? p_aa' ? ? ? ? ?.
      apply pathsinv0; use p_aa'. 
    - intros ? ? ? ? ? ? ? ? p1 ? ? ? p01 ? p12 ? ? ? ? ?.
      eapply pathscomp0; [ use p01 | use p12 ]. use p1.
  Defined.

  Local Lemma interpret_conv_rules
    : cases_for_conv_rules (fun J _ => is_interpretable J).
  Proof.
    split.
    - (* tm_conv *)
      intros; intros X E A1_interpretable.
      simple refine (transportf
        (fun T => is_defined (partial_interpretation_tm _ _ _ T a))
        _
        (p_a _ _ (p_A _ E))).
      refine (p_AA' _ _ _ _).
    - (* tmeq_conv *)
      intros; intros X E A'_intble.
      simple refine (transportf
        (fun T => forall (p : is_defined (partial_interpretation_tm _ _ _ T a))
                         (p' : is_defined (partial_interpretation_tm _ _ _ T a')),
             evaluate p = evaluate p')
        _ (p_aa' _ _ (p_A _ E))).
      simple refine (p_AA' _ _ _ _).
  Defined.

  Local Lemma interpret_subst_rules
    : cases_for_subst_rules (fun J _ => is_interpretable J).
  Proof.
    split.
    - intros; intros X E.
      admit. (* Not currently enough information for this!
        Possible fixes:
        - use the “Sigma” definition of interpretability of term judgements, instead of “Pi” 
        - maybe also the “Sigma” definition of partial interpretation of terms
        - add hypotheses in the subst rules for the presups of d_f. *)
    - admit. 
    - admit.
    - admit.
  Admitted.

  Local Lemma interpret_substeq_rules
    : cases_for_substeq_rules (fun J _ => is_interpretable J).
  Admitted.

  Local Lemma interpret_universe_rules
    : cases_for_universe_rules (fun J _ => is_interpretable J).
  Proof.
    split.
    - (* universe formation *)
      intros; intros X E; auto.
    - (* elements formation *)
      intros; intros X E.
      cbn. refine (_,,tt).
      refine (p_a _ _ tt).
    - (* elements congruence *)
      intros; intros X E d_a d_a'.
      cbn; apply maponpaths.
      use p_aa'; auto.
  Defined.

  Local Lemma interpret_pi_rules
    : cases_for_pi_rules (fun J _ => is_interpretable J).
  Admitted.

  Local Lemma interpret_pi_cong_rules
    : cases_for_pi_cong_rules (fun J _ => is_interpretable J).
  Admitted.

  Fixpoint interpretable_from_derivation {J : judgement}
    : derivation J -> is_interpretable J.
  Proof.
    revert J. apply derivation_rect_grouped.
    - apply interpret_context_rules.
    - apply interpret_var_rule.
    - apply interpret_equiv_rel_rules.
    - apply interpret_conv_rules.
    - apply interpret_subst_rules.
    - apply interpret_substeq_rules.
    - apply interpret_universe_rules.
    - apply interpret_pi_rules.
    - apply interpret_pi_cong_rules.
  Defined.

  Lemma derivable_judgement_is_interpretable {J : judgement}
    : ∥ derivation J ∥ -> is_interpretable J.
  Proof.
    apply factor_through_squash.
    - apply is_interpretable_is_prop.
    - apply interpretable_from_derivation.
  Defined.

End Totality.

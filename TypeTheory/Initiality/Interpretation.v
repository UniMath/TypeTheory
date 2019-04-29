(** This file defines the interpretation function, from the syntax of our toy type theory into any split type-cat with suitable structure. *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.All.

(* TODO: raise issue upstream: notation "_ ∘ _" is used for function-order composition of functions, but for diagrammatic-order composition of morphisms in categories! *)

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.Partial.
Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.Initiality.SplitTypeCat_General.
Require Import TypeTheory.Initiality.SplitTypeCat_Structure.
Require Import TypeTheory.Initiality.Syntax.
Require Import TypeTheory.Initiality.Typing.
Require Import TypeTheory.Initiality.Environments.

Local Open Scope functions.

Section Auxiliary.

  (** Functions giving path types in various hsets directly as hprops. *)
  (* TODO: work out better way to treat them? *)
  Definition mor_paths_hProp {C : category} {X Y : C} (f g : X --> Y)
    : hProp
  := make_hProp (f = g) (homset_property C _ _ _ _).

  Definition type_paths_hProp {C : split_typecat} {Γ : C} (A B : C Γ)
    : hProp
  := make_hProp (A = B) (isaset_types_typecat _ _ _).

  Definition tm_paths_hProp {C : split_typecat} {Γ : C} {A : C Γ} (s t : tm A)
    : hProp
  := make_hProp (s = t) (isaset_tm _ _).

End Auxiliary.

Section Partial_Interpretation.
(** In this section, we construct the partial interpretation function. *)

  Fixpoint
    partial_interpretation_ty {C : split_typecat} (U : universe_struct C) (Π : pi_struct C)
      {Γ:C} {n:nat} (E : environment Γ n) (e : ty_expr n) {struct e}
    : partial (C Γ)
  with
    partial_interpretation_tm {C : split_typecat} (U : universe_struct C) (Π : pi_struct C)
      {Γ:C} {n:nat} (E : environment Γ n) (T : C Γ) (e : tm_expr n) {struct e}
    : partial (tm T). (* See note below re type. *)
  Proof.
    - (* type expressions *)
      destruct e as [ m | m a | m A B ].
      + (* [U_expr] *)
        apply return_partial, U.
      + (* [El_expr a] *)
        get_partial (partial_interpretation_tm _ U Π _ _ E (U _) a) interp_a.
        apply return_partial. exact (elements _ interp_a).
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
        exact (pi_intro _ _ _ _ interp_b).
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
        refine (pi_app _ _ _ _ interp_f interp_a).
  Defined.

  (** Note: alternatively, we could give the interpretation of terms as 
   [ partial_interpretation_tm
       {Γ:C} {n:nat} (E : environment Γ n) (e : tm_expr n)
     : partial (type_with_term Γ). ]
  I think either should work fine; I’m not sure which will work more cleanly. *)

  Context {C : split_typecat} {U : universe_struct C} {Π : pi_struct C}.
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
          eapply pathscomp0. { apply pathsinv0, reind_comp_typecat. }
          eapply pathscomp0. 2: { apply reind_comp_typecat. }
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
    : partial_interpretation_ty U Π (E ∘ f) e
    = partial_interpretation_ty U Π E (rename_ty f e)
  with
    partial_interpretation_rename_tm
      {Γ} {m n:nat} (f : m -> n)
      (E : environment Γ n) (T : C Γ) (e : tm_expr m)
    : partial_interpretation_tm U Π (E ∘ f) T e
    = partial_interpretation_tm U Π E T (rename_tm f e).
  Proof.
    - (* type expressions *)
      destruct e as [ m | m a | m A B ].
      + (* [U_expr] *)
        apply idpath.
      + (* [El_expr a] *)
        cbn. apply maponpaths_2, partial_interpretation_rename_tm.
      + (* [Pi_expr A B] *)
        cbn. apply maponpaths_12.
        { apply partial_interpretation_rename_ty. }
        apply funextfun; intros i. apply maponpaths_2. 
        eapply pathscomp0. 2: { apply partial_interpretation_rename_ty. }
        apply maponpaths_2, funextfun.
        refine (dB_Sn_rect _ _ _); auto.
    - (* term expressions *)
      destruct e as [ m i | m A B b | m A B t a ].
      + (* [var_expr i] *)
        apply idpath.
      + (* [lam_expr A B b] *)
        cbn. apply maponpaths_12.
        { apply partial_interpretation_rename_ty. }
        apply funextfun; intros A_interp.
        assert (e_EA : (extend_environment (E ∘ f) A_interp
                      = extend_environment E A_interp ∘ fmap_dB_S f)).
        { apply funextfun. refine (dB_Sn_rect _ _ _); auto. }
        apply maponpaths_12.
        { eapply pathscomp0. 2: { apply partial_interpretation_rename_ty. }
          apply maponpaths_2, e_EA. }
        apply funextfun; intros B_interp. apply maponpaths_2.
        eapply pathscomp0. 2: { apply partial_interpretation_rename_tm. }
        apply (maponpaths (fun F => _ F _ _) e_EA).
      + (* [app_expr A B t a] *)
        cbn. apply maponpaths_12.
        { apply partial_interpretation_rename_ty. }
        apply funextfun; intros A_interp.
        assert (e_EA : (extend_environment (E ∘ f) A_interp
                      = extend_environment E A_interp ∘ fmap_dB_S f)).
        { apply funextfun. refine (dB_Sn_rect _ _ _); auto. }
        apply maponpaths_12.
        { eapply pathscomp0. 2: { apply partial_interpretation_rename_ty. }
          apply maponpaths_2, e_EA. }
        apply funextfun; intros B_interp. apply maponpaths_12.
        { apply partial_interpretation_rename_tm. }
        apply funextfun; intros t_interp. apply maponpaths_2.
        { apply partial_interpretation_rename_tm. }
  Qed.

End Partial_Interpretation.

Section Environment_Maps.
(** A framework for putting together the lemmas about interaction of the
partial interpretation with (syntactic) renaming and (semantic) reindexing). *)

  Context {C : split_typecat} {U : universe_struct C} {Π : pi_struct C}.

(** A _map of environments_ consists of a map between their underlying objects,
and a _backwards_ map of their sets of variables, respecting the types/terms
of the environments.
  
To understand the slightly surprising variance, consider the key example:
there is a map from [extend_environment E A] to [E], tracking
[dpr_typecat A] on the semantic side and [dB_next] on variables, and showing
that anything interpretable over [E] is interpretable over
[extend_environment E A]. 

For now, we keep the definition parametrised, not packaged. *)
  Definition environment_map_over
      {X Y : C} (f : X --> Y)
      {m n : nat} (g : n -> m)
      (EX : environment X m) (EY : environment Y n)
    : UU
  := reind_environment f EY = EX ∘ g.

  Definition partial_interpretation_environment_map_ty
      {X:C} {m:nat} {EX : environment X m}
      {Y:C} {n:nat} {EY : environment Y n} 
      {f_ob : X --> Y} {f_vars : n -> m} (f : environment_map_over f_ob f_vars EX EY)
      (e : ty_expr n)
    : leq_partial
        (fmap_partial (λ A : C Y, A ⦃f_ob⦄) (partial_interpretation_ty U Π EY e))
        (partial_interpretation_ty U Π EX (rename_ty f_vars e)).
  Proof.
    eapply leq_partial_trans.
    { apply reindex_partial_interpretation_ty. }
    apply leq_partial_of_path.
    eapply pathscomp0. 2: { apply partial_interpretation_rename_ty. }
    apply maponpaths_2, f.
  Qed.

  Definition partial_interpretation_environment_map_tm
      {X:C} {m:nat} {EX : environment X m}
      {Y:C} {n:nat} {EY : environment Y n} 
      (f_ob : X --> Y) (f_vars : n -> m) (f : environment_map_over f_ob f_vars EX EY)
      (T : C Y)
      (e : tm_expr n)
    : leq_partial
        (fmap_partial (λ t : tm T, reind_tm f_ob t)
                      (partial_interpretation_tm U Π EY T e))
        (partial_interpretation_tm U Π EX (T ⦃ f_ob ⦄) (rename_tm f_vars e)).
  Proof.
    eapply leq_partial_trans.
    { apply reindex_partial_interpretation_tm. }
    apply leq_partial_of_path.
    eapply pathscomp0. 2: { apply partial_interpretation_rename_tm. }
    exact (maponpaths (fun E => partial_interpretation_tm _ _ E _ _) f). 
  Qed.

  Definition dpr_environment
      {X : C} {n} (E : environment X n) (A : C X)
    : environment_map_over (dpr_typecat A) (dB_next)
                           (extend_environment E A) E.
  Proof.
    apply idpath.
  Qed.

End Environment_Maps.

Section Partial_Interpretation_Substitution.
(** The interaction of the partial interpretation with substitution requires
a little more work to state. *)

  Context {C : split_typecat} {U : universe_struct C} {Π : pi_struct C}.

  (* Note: perhaps this should really just be the terms, with a function
     afterward assembling them into a partial environment.  But the partial
     environment seems all that’s needed for now. *)
  Definition partial_interpretation_raw_context_map
      {X} {m n:nat} (E : environment X m) (A : n -> C X)
      (f : raw_context_map m n)
    : partial (environment X n). 
  Proof.
    refine (forall_partial _); intros i.
    refine (fmap_partial _ (partial_interpretation_tm U Π E (A i) (f i))).
    intros t; exact (A i,,t).
  Defined.

  Definition partial_interpretation_idmap_raw_context
      {X} {n:nat} (E : environment X n)
    : leq_partial
        (return_partial E)
        (partial_interpretation_raw_context_map E
          (type_of ∘ E) (idmap_raw_context n)).
  Proof.
    apply make_leq_partial'; cbn; intros _.
    use tpair.
    - intros i; repeat constructor.
    - apply funextfun; intros i.
      apply (maponpaths (tpair _ _)).
      apply tm_transportf_idpath.
  Defined.

  Definition partial_interpretation_add_to_raw_context_map
      {X} {m n:nat} (E : environment X m) (As : n -> C X) (B : C X)
      (f : raw_context_map m n) (b : tm_expr m)
    : leq_partial
        (bind_partial (partial_interpretation_raw_context_map E As f)
          (fun F => fmap_partial (fun b_interp => add_to_environment F (B,,b_interp))
                                 (partial_interpretation_tm U Π E B b)))
        (partial_interpretation_raw_context_map E
          (dB_Sn_rect _ B As)
          (add_to_raw_context_map f b)).
  Proof.
    apply make_leq_partial'; cbn; intros [f_def b_def].
    use tpair.
    - refine (dB_Sn_rect _ _ _); assumption.
    - apply funextfun. refine (dB_Sn_rect _ _ _); auto.
  Defined.

  Definition partial_interpretation_tm_as_raw_context_map
      {X} {n:nat} (E : environment X n) (A : C X)
      (a : tm_expr n)
    : leq_partial
        (fmap_partial (fun a_interp => add_to_environment E (A,,a_interp))
                                 (partial_interpretation_tm U Π E A a))
        (partial_interpretation_raw_context_map E
          (dB_Sn_rect _ A (type_of ∘ E))
          (tm_as_raw_context_map a)).
  Proof.
    eapply leq_partial_trans.
    2: { apply partial_interpretation_add_to_raw_context_map. }
    eapply leq_partial_trans.
    2: { eapply bind_leq_partial_1, partial_interpretation_idmap_raw_context. }
    refine (pr2 (bind_return_partial _ _)).
  Defined.

  Lemma partial_interpretation_weaken_raw_context_map
      {X} {m n:nat} (E : environment X m) (A : n -> C X) (B : C X)
      (f : raw_context_map m n)
    : leq_partial
        (fmap_partial (fun E => extend_environment E B)
          (partial_interpretation_raw_context_map E A f))
        (partial_interpretation_raw_context_map
          (extend_environment E B)
          (dB_Sn_rect _ (B ⦃dpr_typecat B⦄) (fun i => A i ⦃dpr_typecat B⦄))
          (weaken_raw_context_map f)).
  Proof.
    apply make_leq_partial'. cbn.
    intros fs_def.
    use tpair.
    - refine (dB_Sn_rect _ _ _).
      + cbn. repeat constructor.
      + cbn. intros i.
        refine (partial_interpretation_environment_map_tm _ _ _ _ _ (fs_def i)).
        apply dpr_environment.
    - apply funextfun. refine (dB_Sn_rect _ _ _).
      + cbn. apply (maponpaths (tpair _ _)), tm_transportf_idpath.
      + intros i; cbn. apply (maponpaths (tpair _ _)).
        refine (leq_partial_commutes _ _).
  Qed.

  Fixpoint
    partial_interpretation_subst_ty
      {X} {m n:nat} (E : environment X m)
      (f : raw_context_map m n) (T : n -> C X)
      (f_def : is_defined (partial_interpretation_raw_context_map E T f))
      (e : ty_expr n) {struct e}
    : leq_partial
        (partial_interpretation_ty U Π (evaluate f_def) e)
        (partial_interpretation_ty U Π E (subst_ty f e))
  with
    partial_interpretation_subst_tm
      {X} {m n:nat} (E : environment X m)
      (f : raw_context_map m n) (T : n -> C X)
      (f_def : is_defined (partial_interpretation_raw_context_map E T f))
      (S : C X) (e : tm_expr n) {struct e}
    : leq_partial
        (partial_interpretation_tm U Π (evaluate f_def) S e)
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
        eapply leq_partial_trans.
        2: { refine (partial_interpretation_subst_ty _ _ _ _ _ _ _ _).
          apply (partial_interpretation_weaken_raw_context_map E T A_interp). 
          apply f_def. }
        apply leq_partial_of_path, maponpaths_2.
        refine (!leq_partial_commutes
                  (partial_interpretation_weaken_raw_context_map _ _ _ _) _).
    - (* term expressions *)
      destruct e as [ n i | n A B b | n A B t a ].
      + (* [var_expr i] *)
        cbn. apply show_assume_leq_partial; intros e_S. destruct e_S.
        use show_return_leq_partial.
        * exact (f_def i).
        * cbn. apply pathsinv0, tm_transportf_idpath.
      + (* [lam_expr A B b] *)
        cbn. eapply bind_leq_partial.
        { apply partial_interpretation_subst_ty. }
        intros A_interp. apply bind_leq_partial.
        { eapply leq_partial_trans.
          2: { refine (partial_interpretation_subst_ty _ _ _ _ _ _ _ _).
            apply (partial_interpretation_weaken_raw_context_map E T A_interp). 
            apply f_def. }
          apply leq_partial_of_path, maponpaths_2.
          refine (!leq_partial_commutes
                  (partial_interpretation_weaken_raw_context_map _ _ _ _) _). }
        intros B_interp. apply bind_leq_partial_1.
        eapply leq_partial_trans.
        2: { refine (partial_interpretation_subst_tm _ _ _ _ _ _ _ _ _).
          apply (partial_interpretation_weaken_raw_context_map E T A_interp). 
          apply f_def. }
        apply leq_partial_of_path. 
        eapply (maponpaths (fun E => partial_interpretation_tm _ _ E _ _)).
        refine (!leq_partial_commutes
                 (partial_interpretation_weaken_raw_context_map _ _ _ _) _).
      + (* [app_expr A B f a] *)
        cbn. eapply bind_leq_partial.
        { apply partial_interpretation_subst_ty. }
        intros A_interp. apply bind_leq_partial.
        { eapply leq_partial_trans.
          2: { refine (partial_interpretation_subst_ty _ _ _ _ _ _ _ _).
            apply (partial_interpretation_weaken_raw_context_map E T A_interp). 
            apply f_def. }
          apply leq_partial_of_path, maponpaths_2.
          refine (!leq_partial_commutes
                  (partial_interpretation_weaken_raw_context_map _ _ _ _) _). }
        intros B_interp. apply bind_leq_partial.
        { apply partial_interpretation_subst_tm. }
        intros a_interp. apply bind_leq_partial_1.
        apply partial_interpretation_subst_tm.
  Qed.

  (* TODO: consider naming! *)
  Definition raw_context_map_tracks_environments
      {X Y} (f : Y --> X)
      {m n:nat} (ts : raw_context_map n m)
      (F : environment Y n) (E : environment X m)
    : UU 
  := forall (i:m), 
       ∑ (ti_def : is_defined
           (partial_interpretation_tm U Π F (type_of (E i) ⦃f⦄) (ts i))),
         evaluate ti_def = reind_tm f (term_of (E i)).

  Definition partial_interpretation_raw_context_map_tracks_environments
      {X Y} (f : Y --> X)
      {m n:nat} (ts : raw_context_map n m)
      {F : environment Y n} {E : environment X m}
    : (raw_context_map_tracks_environments f ts F E)
    <->
      leq_partial
        (return_partial (reind_environment f E))
        (partial_interpretation_raw_context_map F
                    (type_of ∘ reind_environment f E) ts).
  Proof.
    split.
    - intros ts_track.
      apply make_leq_partial'; cbn; intros _.
      use tpair.
      + intros i; apply ts_track.
      + cbn. apply funextfun; intros i.
        apply (maponpaths (tpair _ _)).
        apply ts_track.
    - intros l.
      destruct (apply_leq_partial_pair l tt) as [ts_def H]; clear l.
      cbn in ts_def, H.
      intros i. exists (ts_def i).
      eapply pathscomp0. 2: { exact (fiber_paths (toforallpaths _ _ _ H i)). }
      simple refine (_ @ _).
      { exact (transportf _ (idpath _) (evaluate (ts_def i))). }
      + apply idpath.
      + apply maponpaths_2, isaset_types_typecat.
  (* This is a little tricky, because [partial_interpretation_raw_context_map]
  contains an equality of environments, i.e. equalities of types-and-terms,
  where the type part is redundant, and really the term part is the desired
  content.  In particular, [isaset_types_typecat] is required: in a non-split
  type-cat, the definition with an equality of environments would be wrong. *)
  Qed.

  (* TODO: consider naming! *)
  Definition add_to_raw_context_map_tracks_environments
      {X Y} {f : Y --> X}
      {m n:nat} {ts : raw_context_map n m} {a : tm_expr n} 
      {F : environment Y n} {E : environment X m} {A : C X}
      (ts_track : raw_context_map_tracks_environments f ts F E)
      (a_def : is_defined (partial_interpretation_tm U Π F (A ⦃f⦄) a))
      (a_interp : tm A) (e_a : evaluate a_def = reind_tm f a_interp)
    : raw_context_map_tracks_environments
        f (add_to_raw_context_map ts a)
        F (add_to_environment E ((A,, a_interp) : type_with_term X)).
  Proof.
    refine (dB_Sn_rect _ _ _); intros; cbn.
    - use tpair; assumption.
    - apply ts_track.
  Defined.

  (* TODO: consider naming! *)
  Definition tm_as_raw_context_map_tracks_environments
      {X} {n:nat} {E : environment X n} {A : C X}
      {a} (a_def : is_defined (partial_interpretation_tm U Π E A a))
    : raw_context_map_tracks_environments
        (evaluate a_def) (tm_as_raw_context_map a)
        E (extend_environment E A).
  Proof.
    use add_to_raw_context_map_tracks_environments.   
    - intros i. 
(* can this be simplified with [tm_transportf_partial_interpretation_tm_leq]? *)
      use tpair; cbn.
      + refine (_,,tt). cbn; apply pathsinv0.
        eapply pathscomp0. { apply pathsinv0, reind_comp_typecat. }
        eapply pathscomp0. 2: { apply reind_id_type_typecat. }
        apply maponpaths, section_property.
      + cbn. eapply pathscomp0. 2: { apply reind_compose_tm'. }
        eapply pathscomp0.
        2: { apply maponpaths. refine (! maponpaths_2_reind_tm _ _).
          apply section_property. }
        eapply pathscomp0. 2: { apply tm_transportf_compose. }
        eapply pathscomp0. 2: { apply maponpaths, pathsinv0, reind_id_tm. }
        eapply pathscomp0. 2: { apply tm_transportf_compose. }
        apply tm_transportf_irrelevant.
    - refine (tm_transportf_partial_interpretation_tm_leq _ _ _ a_def). 
      eapply pathscomp0. 2: { apply reind_comp_typecat. }
      eapply pathsinv0, pathscomp0. 2: { apply reind_id_type_typecat. } 
      apply maponpaths, section_property.
    - eapply pathscomp0. apply leq_partial_commutes.
      cbn. eapply pathscomp0. 2: { apply pathsinv0, reind_tm_var_typecat. }
      apply tm_transportf_irrelevant.
  Defined.

  Definition reind_partial_interpretation_subst_ty
      {X Y} (f : Y --> X)
      {m n:nat} (ts : raw_context_map n m)
      {E : environment X m} {F : environment Y n}
      (ts_track : raw_context_map_tracks_environments f ts F E)
      (e : ty_expr m)
    : leq_partial
        (fmap_partial (fun A => A ⦃f⦄) (partial_interpretation_ty U Π E e))
        (partial_interpretation_ty U Π F (subst_ty ts e)).
  Proof.
    eapply leq_partial_trans.
    { apply reindex_partial_interpretation_ty. }
    eapply leq_partial_trans.
    2: { refine (partial_interpretation_subst_ty _ _ _ _ _). 
         eapply partial_interpretation_raw_context_map_tracks_environments.
         { apply ts_track. } 
         apply tt. }
    apply leq_partial_of_path, maponpaths_2.
    apply pathsinv0. refine (leq_partial_commutes _ _).
  Qed.

  Definition  reind_partial_interpretation_subst_tm
      {X Y} (f : Y --> X)
      {m n:nat} (ts : raw_context_map n m)
      {E : environment X m} {F : environment Y n}
      (ts_track : raw_context_map_tracks_environments f ts F E)
      {S : C X} {S' : C Y} (e_S : S⦃f⦄ = S')
      (e : tm_expr m)
    : leq_partial
        (fmap_partial (tm_transportf e_S ∘ reind_tm f)
                      (partial_interpretation_tm U Π E S e))
        (partial_interpretation_tm U Π F S' (subst_tm ts e)).
  Proof.
    eapply leq_partial_trans.
    { apply leq_partial_of_path, pathsinv0, fmap_compose_partial_applied. }
    eapply leq_partial_trans.
    2: { refine (tm_transportf_partial_interpretation_tm_leq _ e_S _). }
    apply fmap_leq_partial. eapply leq_partial_trans.
    { apply reindex_partial_interpretation_tm. }
    eapply leq_partial_trans.
    2: { refine (partial_interpretation_subst_tm _ _ _ _ _ _). 
         eapply partial_interpretation_raw_context_map_tracks_environments.
         { apply ts_track. } 
         apply tt. }
    apply leq_partial_of_path.
    eapply (maponpaths (fun E => partial_interpretation_tm _ _ E _ _)).
    apply pathsinv0. refine (leq_partial_commutes _ _).
  Qed.

End Partial_Interpretation_Substitution.

Section Totality.

  Context {C : split_typecat} (U : universe_struct C) (Π : pi_struct C).
 
  Definition environment_respects_type
      {X : C} (Γ : context) (E : environment X Γ)
    : UU
  := forall i : Γ,
    ∑ (d : is_defined (partial_interpretation_ty U Π E (Γ i))),
      (evaluate d = type_of (E i)).
  (* TODO: perhaps refactor with [forall_leq_partial]? *)

  Definition extend_environment_respects_type
      {X : C} {Γ : context} {E : environment X Γ}
      (R : environment_respects_type Γ E)
      {A : ty_expr Γ} (A_def : is_defined (partial_interpretation_ty U Π E A))
    : environment_respects_type
        (context_extend Γ A)
        (extend_environment E (evaluate A_def)).
  Proof.
    use dB_Sn_rect.
    - cbn. use tpair.
      + refine (leq_partial_of_path _ _ _ _).
        { apply partial_interpretation_rename_ty. }
        refine (reindex_partial_interpretation_ty (dpr_typecat _) E _ A_def).
      + cbn. eapply pathscomp0. { apply leq_partial_commutes. }
        use leq_partial_commutes.
    - cbn; intros i. use tpair.
      + refine (leq_partial_of_path _ _ _ _).
        { apply partial_interpretation_rename_ty. }
        refine (reindex_partial_interpretation_ty (dpr_typecat _) E _ _).
        apply R.
      + cbn. 
        eapply pathscomp0. { apply leq_partial_commutes. }
        eapply pathscomp0. { apply leq_partial_commutes. }
        cbn. apply (maponpaths (fun T => T ⦃_⦄)). 
        exact (pr2 (R i)).
  Qed.

  Definition typed_environment (X : C) (Γ : context)
    := ∑ (E : environment X Γ), environment_respects_type Γ E.

  Coercion environment_of_typed_environment {X} {Γ}
    (E : typed_environment X Γ) : environment X Γ
  := pr1 E.

  Definition typed_environment_respects_types {X} {Γ}
    (E : typed_environment X Γ) (i : Γ)
  := pr2 E i.

  Definition extend_typed_environment
      {X : C} {Γ : context} (E : typed_environment X Γ)
      {A : ty_expr Γ} (A_def : is_defined (partial_interpretation_ty U Π E A))
    : typed_environment (X ◂ evaluate A_def) (context_extend Γ A).
  Proof.
    eapply tpair.
    exact (extend_environment_respects_type
             (typed_environment_respects_types E) A_def).
  Defined.

  Local Open Scope judgement_scope.

  (** We show a fairly _weak_ sense of interpretatbility for judgements:
  given an interpretation of their boundary, we get one of their conclusion.

  This works smoothly in many ways, but requires quite “paranoid” formulations
  of the derivation rules.  A stronger definition of “interpretatability” could
  allow the proof to work with less paranoid formulations of the rules. 

  Note we also don’t ask anything for interpretability of the context judgement. *)
  Definition is_interpretable (J : judgement) : hProp
  := match J with
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
  
  Local Lemma interpret_var_rule
    : case_for_var_rule (fun J _ => is_interpretable J).
  Proof.
    intros ? ? ? H_Γi.
    intros X E Γi_interpretable.
    refine (_,,tt); cbn.
    eapply pathscomp0. { apply pathsinv0, typed_environment_respects_types. }
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

  Local Lemma interpret_universe_rules
    : cases_for_universe_rules (fun J _ => is_interpretable J).
  Proof.
    split.
    - (* universe formation *)
      intros; intros X E; exact tt.
    - (* elements formation *)
      intros; intros X E.
      cbn. refine (_,,tt).
      refine (p_a _ _ tt).
    - (* elements congruence *)
      intros; intros X E d_a d_a'.
      cbn; apply maponpaths.
      use p_aa'; exact tt.
  Defined.

  Section Pi_Rules.
  (** We break out the interpretation of the pi-type rules as lemmas,
  so that the later ones can refer back to the earlier ones. *)

    Context (Γ : context) (A : ty_expr Γ) (B : ty_expr (Γ;; A)%context).
  
    Local Lemma interpret_pi
      : is_interpretable [! Γ |- A !]
        -> is_interpretable [! Γ;; A |- B !]
        -> is_interpretable [! Γ |- Pi_expr A B !].
    Proof.
      intros p_A p_B; intros X E; cbn.
      simple refine (_,,(_,,tt)).
      + use p_A.
      + refine (p_B _ (extend_typed_environment _ _)).
    Defined.
    
    Local Lemma interpret_lam
      : forall (b : tm_expr (Γ;; A)%context),
        is_interpretable [! Γ |- A !]
        -> is_interpretable [! Γ;; A |- B !] 
        -> is_interpretable [! Γ;; A |- b ::: B !]
        -> is_interpretable [! Γ |- lam_expr A B b ::: Pi_expr A B !].
    Proof.
      intros b p_A p_B p_b; intros X E Pi_def. cbn.
      use tpair. { use p_A. }
      use tpair. { refine (p_B _ (extend_typed_environment _ _)). }
      use tpair. { refine (p_b _ (extend_typed_environment _ _) _). }
      refine (_,,tt).
      refine (compat_partial_refl
        (partial_interpretation_ty _ _ _ (Pi_expr _ _)) (_,,(_,,tt)) _).
    Defined.
    
    Local Lemma interpret_app
      : forall (f a : tm_expr Γ),
        is_interpretable [! Γ |- A !]
        -> is_interpretable [! Γ;; A |- B !]
        -> is_interpretable [! Γ |- f ::: Pi_expr A B !]
        -> is_interpretable [! Γ |- a ::: A !]
        -> is_interpretable [! Γ |- app_expr A B f a ::: subst_top_ty a B !].
    Proof.
      intros f a p_A p_B p_f p_a; intros X E Ba_def. cbn.
      exists (p_A _ _). 
      exists (p_B _ (extend_typed_environment _ _)). 
      exists (p_a _ _ _). 
      exists (p_f _ _ (_,,(_,,tt))). 
      refine (_,,tt).
      refine (compat_of_leq_partial
        (reind_partial_interpretation_subst_ty _ _ _ _) _ _).
      apply tm_as_raw_context_map_tracks_environments.
    Defined.

    Local Lemma interpret_pi_comp 
      : forall (b : tm_expr (Γ;; A)%context) (a : tm_expr Γ),
        is_interpretable [! Γ |- A !]
        -> is_interpretable [! Γ;; A |- B !]
        -> is_interpretable [! Γ;; A |- b ::: B !]
        -> is_interpretable [! Γ |- a ::: A !]
        -> is_interpretable [! Γ |- app_expr A B (lam_expr A B b) a === 
                                             subst_top_tm a b ::: subst_top_ty a B !].
    Proof.
      intros b a p_A p_B p_b p_a; intros X E Ba_def app_def ba_def.
      set (A_def := p_A _ E).
      set (B_def := p_B _ (extend_typed_environment E (A_def))).
      set (b_def := p_b _ _ B_def).
      set (a_def := p_a _ E A_def).
      set (a_tracks := tm_as_raw_context_map_tracks_environments a_def).
      Local Arguments evaluate {_} _ _. apply idfun.
      (* Outline of the argument:
         1. LHS must be as constructed in preceding cases;
         2. RHS must be a reindexing, by reindexing lemma;
         3. semantic pi-comp shows these agree. *)
      (* Step 1: determine the LHS as an app *)
      eapply pathscomp0.
      { use compat_partial_refl.
        refine (interpret_app _ a p_A p_B _ p_a X E Ba_def).
        apply interpret_lam; assumption. }
      eapply pathscomp0.
      (* Step 2: determine the RHS as a reindexing of an app *)
      2: { refine (compat_of_leq_partial
              (reind_partial_interpretation_subst_tm _ _ a_tracks _ _) b_def _).
           refine (compat_of_leq_partial
                       (reind_partial_interpretation_subst_ty _ _ _ _) _ _).
           apply tm_as_raw_context_map_tracks_environments. }
      (* Step 3: apply the semantic pi-comp, modulo a little wrangling transports *)
      cbn. eapply maponpaths, pathscomp0.
      { eapply (maponpaths (fun t => pi_app Π _ _ _ t _)).
        apply tm_transportf_idpath_gen. }
      apply pi_comp.
    Qed.

  End Pi_Rules.

  Local Lemma interpret_pi_rules
    : cases_for_pi_rules (fun J _ => is_interpretable J).
  Proof.
    split.
    - auto using interpret_pi.
    - auto using interpret_lam.
    - auto using interpret_app.
    - auto using interpret_pi_comp.
  Defined.

  Local Lemma interpret_pi_cong_rules
    : cases_for_pi_cong_rules (fun J _ => is_interpretable J).
  Proof.
    split.
    - intros Γ A A' B B' _ _ _ p_A_A' _ p_B_B' X E.
      apply compat_bind_partial'; fold (@partial_interpretation_ty).
      { use p_A_A'. }
      intros A_def. apply compat_bind_partial.
      { use (p_B_B' _ (extend_typed_environment E (A_def))). }
      intros; apply compat_partial_refl.
    - intros Γ A A' B B' b b' _ _ _ p_A_A' _ p_B_B' _ p_b_b' X E A_def_0.
      apply compat_bind_partial';
        fold @partial_interpretation_ty @partial_interpretation_tm.
      { use p_A_A'. }
      intros A_def. apply compat_bind_partial'.
      { use (p_B_B' _ (extend_typed_environment E A_def)). }
      intros B_def. apply compat_bind_partial.
      { use (p_b_b' _ (extend_typed_environment E A_def)). }
      intros; apply compat_partial_refl.
    - intros Γ A A' B B' f f' a a' 
             _ _ _ p_A_A' _ p_B_B' _ p_f_f' _ p_a_a' X E Ba_def_0.
      apply compat_bind_partial';
        fold @partial_interpretation_ty @partial_interpretation_tm.
      { use p_A_A'. }
      intros A_def. apply compat_bind_partial'.
      { use (p_B_B' _ (extend_typed_environment E A_def)). }
      intros B_def. apply compat_bind_partial'.
      { use p_a_a'. }
      intros a_def. apply compat_bind_partial'.
      { transparent assert (Pi_def
        : (is_defined (partial_interpretation_ty U Π E (Pi_expr A B)))).
        { exists A_def. exists B_def. constructor. }
        use (p_f_f' _ _ Pi_def). }
      intros; apply compat_partial_refl.
  Qed.

  Fixpoint interpretable_from_derivation {J : judgement}
    : derivation J -> is_interpretable J.
  Proof.
    revert J. apply derivation_rect_grouped.
    - apply interpret_var_rule.
    - apply interpret_equiv_rel_rules.
    - apply interpret_conv_rules.
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

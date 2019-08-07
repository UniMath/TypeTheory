(** Further lemmas on the interpretation function, separated here in order to keep [TypeTheory.Initiality.Interpretation] itself reasonably streamlined *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.PAdics.lemmas. (* just for [setquotprpathsandR] *)

Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.Partial.
Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.Initiality.SplitTypeCat_General.
Require Import TypeTheory.Initiality.SplitTypeCat_Structure.
Require Import TypeTheory.Initiality.SplitTypeCat_Maps.
Require Import TypeTheory.Initiality.Syntax.
Require Import TypeTheory.Initiality.SyntaxLemmas.
Require Import TypeTheory.Initiality.Typing.
Require Import TypeTheory.Initiality.TypingLemmas.
Require Import TypeTheory.Initiality.Environments.
Require Import TypeTheory.Initiality.Interpretation.
Require Import TypeTheory.Initiality.SyntacticCategory.
Require Import TypeTheory.Initiality.SyntacticCategory_Structure.

Section Functoriality.
(** Key property of the interpretation: if [F : C --> D] is a map of split type-cats with logical structure, and some expression [e] is interpretable in [C] in some environment [E] with value [a], then [e] is also interpretable in [D] in environment [F E], with value [F a]. *)

  Context {C : split_typecat} {U : universe_struct C} {Π : pi_struct C}
          {C' : split_typecat} {U' : universe_struct C'} {Π' : pi_struct C'}
          {F : typecat_mor C C'}
          (F_U : preserves_universe_struct U U' F)
          (F_Π : preserves_pi_struct Π Π' F).

  Fixpoint
    fmap_partial_interpretation_ty
      {Γ:C} {n:nat} (E : environment Γ n) (e : ty_expr n) {struct e}
    : leq_partial
        (fmap_partial (fun A => typecat_mor_Ty F _ A)
           (partial_interpretation_ty U Π E e))
        (partial_interpretation_ty U' Π' (fmap_environment F E) e)
  with
    fmap_partial_interpretation_tm
      {Γ:C} {n:nat} (E : environment Γ n) (T : C Γ) (e : tm_expr n) {struct e}
    : leq_partial
        (fmap_partial (fun a => fmap_tm F a)
           (partial_interpretation_tm U Π E T e))
        (partial_interpretation_tm U' Π' (fmap_environment F E)
                                   (typecat_mor_Ty F _ T)
                                   e).
  Proof.
    (* Note: entire proof closely parallels that of [reindex_partial_interpretation], essentially since reindexing is a map of CwA’s and the reindexing axioms say precisely that it is structure_preserving. *)
    - (* type expressions *)
      destruct e as [ n | n a | n A B ].
      + (* [U_expr] *)
        apply leq_partial_of_path.
        eapply pathscomp0. { apply fmap_return_partial. }
        apply (maponpaths return_partial), (fmap_universe F_U).
      + (* [El_expr a] *)
        (* part for [a] argument *)
        eapply leq_partial_trans.
        { apply leq_partial_of_path.
          apply (fmap_bind_partial (partial_interpretation_tm _ _ _ _ _)). }
        eapply leq_partial_trans.
        2: { eapply (@bind_leq_partial_1 _ _ _
                        (partial_interpretation_tm _ _ _ _ _)).
          eapply leq_partial_trans.
          2: { refine (tm_transportf_partial_interpretation_tm_leq _ _ _).
               apply (fmap_universe F_U). }
          apply fmap_leq_partial.
          apply fmap_partial_interpretation_tm. }
        eapply leq_partial_trans.
        2: { apply leq_partial_of_path, pathsinv0.
             eapply pathscomp0; apply bind_fmap_partial_1. }
        apply bind_leq_partial_2; intros a_interp.
        (* final naturality part *)
        apply leq_partial_of_path.
        eapply pathscomp0. { apply fmap_return_partial. }
        apply (maponpaths return_partial), fmap_elements.
      + (* [Pi_expr A B] *)
        assert (IH_A := fmap_partial_interpretation_ty Γ n E A).
        assert (IH_B := fun Γ E => fmap_partial_interpretation_ty Γ (S n) E B).
        (* part for [A] argument *)
        eapply leq_partial_trans.
        { apply leq_partial_of_path.
          apply (fmap_bind_partial (partial_interpretation_ty _ _ _ _)
                  (λ iA, bind_partial (partial_interpretation_ty _ _ _ _) _)). }
        eapply leq_partial_trans.
        2: { refine (@bind_leq_partial_1 _ _ _
                  (partial_interpretation_ty _ _ _ _) _
                  (λ iA, bind_partial (partial_interpretation_ty _ _ _ _) _)).
             apply IH_A. }
        eapply leq_partial_trans.
        2: { apply leq_partial_of_path, pathsinv0, bind_fmap_partial_1. }
        apply bind_leq_partial_2; intros A_interp.
        (* part for [B] argument *)
        eapply leq_partial_trans.
        { apply leq_partial_of_path, fmap_bind_partial. }
        eapply leq_partial_trans.
        2: { eapply bind_leq_partial_1, leq_partial_trans.
             2: { apply leq_partial_of_path.
                  apply maponpaths_2, pathsinv0, fmap_extend_environment. }
             eapply leq_partial_trans.
             2: { apply reindex_partial_interpretation_ty. }
             apply fmap_leq_partial, IH_B. }
        eapply leq_partial_trans.
        2: { apply leq_partial_of_path, pathsinv0.
             eapply pathscomp0; apply bind_fmap_partial_1. }
        apply bind_leq_partial_2; intros B_interp.
        (* final naturality part *)
        apply leq_partial_of_path.
        eapply pathscomp0. { apply fmap_return_partial. }
        apply (maponpaths return_partial), (fmap_pi_form F_Π).
    - (* term expressions *)
      destruct e as [ n i | n A B b | n A B t a ].
      + (* [var_expr i] *)
        eapply leq_partial_trans.
        { apply leq_partial_of_path, fmap_assume_partial. }
        use assume_partial_leq. { exact (maponpaths _). }
        intros e_T; destruct e_T.
        apply leq_partial_of_path.
        eapply pathscomp0. { apply fmap_return_partial. }
        apply maponpaths.
        eapply pathscomp0. { apply maponpaths, tm_transportf_idpath. }
        apply pathsinv0, tm_transportf_idpath.
      + (* [lam_expr A B b] *)
        assert (IH_A := fmap_partial_interpretation_ty Γ n E A).
        assert (IH_B := fun Γ E => fmap_partial_interpretation_ty Γ (S n) E B).
        assert (IH_b := fun Γ T E
                        => fmap_partial_interpretation_tm Γ (S n) E T b).
        (* part for [A] argument *)
        eapply leq_partial_trans.
        { apply leq_partial_of_path.
          apply (fmap_bind_partial (partial_interpretation_ty _ _ _ _)
                   (λ iA, bind_partial (partial_interpretation_ty _ _ _ _)
                   (λ iB, bind_partial (partial_interpretation_tm _ _ _ _ _)
                                       _)) _). }
        eapply leq_partial_trans.
        2: { refine (@bind_leq_partial_1 _ _ _
                      (partial_interpretation_ty _ _ _ _) _
                      (λ iA, bind_partial (partial_interpretation_ty _ _ _ _)
                      (λ iB, bind_partial (partial_interpretation_tm _ _ _ _ _)
                                            _))).
             apply IH_A. }
        eapply leq_partial_trans.
        2: { apply leq_partial_of_path, pathsinv0, bind_fmap_partial_1. }
        apply bind_leq_partial_2; intros A_interp.
        (* part for [B] argument *)
        eapply leq_partial_trans.
        { apply leq_partial_of_path, fmap_bind_partial. }
        eapply leq_partial_trans.
        2: { eapply bind_leq_partial_1.
          eapply leq_partial_trans.
          2: { apply leq_partial_of_path.
               apply maponpaths_2, pathsinv0, fmap_extend_environment. }
          eapply leq_partial_trans.
          2: { apply reindex_partial_interpretation_ty. }
          apply fmap_leq_partial, IH_B. }
        eapply leq_partial_trans.
        2: { apply leq_partial_of_path, pathsinv0.
          eapply pathscomp0; apply bind_fmap_partial_1. }
        apply bind_leq_partial_2; intros B_interp.
        (* part for [b] argument *)
        eapply leq_partial_trans.
        { apply leq_partial_of_path, fmap_bind_partial. }
        eapply leq_partial_trans.
        2: { eapply bind_leq_partial_1.
          eapply leq_partial_trans.
          2: { apply leq_partial_of_path.
             eapply (maponpaths (fun E => partial_interpretation_tm _ _ E _ _)),
                    pathsinv0, fmap_extend_environment. }
          eapply leq_partial_trans.
          2: { apply reindex_partial_interpretation_tm. }
          apply fmap_leq_partial, IH_b. }
        eapply leq_partial_trans.
        2: { apply leq_partial_of_path, pathsinv0.
             eapply pathscomp0; apply bind_fmap_partial_1. }
        apply bind_leq_partial_2; intros b_interp.
        (* part for assumption on [T] *)
        eapply leq_partial_trans.
        { eapply leq_partial_of_path, fmap_assume_partial. }
        use assume_partial_leq.
        { intros e_T.
          eapply pathscomp0. 2: { apply maponpaths, e_T. }
          apply pathsinv0, fmap_pi_form, F_Π. }
        intros e_T; destruct e_T.
        (* final naturality part *)
        apply leq_partial_of_path.
        eapply pathscomp0. { apply fmap_return_partial. }
        apply maponpaths. rewrite tm_transportf_idpath.
        eapply pathscomp0. { apply (fmap_pi_intro F_Π). }
        apply tm_transportf_irrelevant.
      + (* [app_expr A B t a] *)
        assert (IH_A := fmap_partial_interpretation_ty Γ n E A).
        assert (IH_B := fun Γ E => fmap_partial_interpretation_ty Γ (S n) E B).
        assert (IH_t := fun T => fmap_partial_interpretation_tm Γ n E T t).
        assert (IH_a := fun T => fmap_partial_interpretation_tm Γ n E T a).
        (* part for [A] argument *)
        eapply leq_partial_trans.
        { apply leq_partial_of_path.
          apply (fmap_bind_partial (partial_interpretation_ty _ _ _ _)
                (λ interp_A, bind_partial (partial_interpretation_ty _ _ _ _)
                (λ interp_B, bind_partial (partial_interpretation_tm _ _ _ _ _)
                (λ interp_a, bind_partial (partial_interpretation_tm _ _ _ _ _)
                                            _)))).
        }
        eapply leq_partial_trans.
        2: { refine (@bind_leq_partial_1 _ _ _
                (partial_interpretation_ty _ _ _ _) _
                (λ interp_A, bind_partial (partial_interpretation_ty _ _ _ _)
                (λ interp_B, bind_partial (partial_interpretation_tm _ _ _ _ _)
                (λ interp_a, bind_partial (partial_interpretation_tm _ _ _ _ _)
                                           _)))).
             apply IH_A. }
        eapply leq_partial_trans.
        2: { apply leq_partial_of_path, pathsinv0, bind_fmap_partial_1. }
        apply bind_leq_partial_2; intros A_interp.
        (* part for [B] argument *)
        eapply leq_partial_trans.
        { apply leq_partial_of_path, fmap_bind_partial. }
        eapply leq_partial_trans.
        2: { eapply bind_leq_partial_1.
          eapply leq_partial_trans.
          2: { apply leq_partial_of_path.
            apply maponpaths_2, pathsinv0, fmap_extend_environment. }
          eapply leq_partial_trans.
          2: { apply reindex_partial_interpretation_ty. }
          apply fmap_leq_partial, IH_B. }
        eapply leq_partial_trans.
        2: { apply leq_partial_of_path, pathsinv0.
          eapply pathscomp0; apply bind_fmap_partial_1. }
        apply bind_leq_partial_2; intros B_interp.
        (* part for [a] argument *)
        eapply leq_partial_trans.
        { apply leq_partial_of_path. cbn.
          apply (fmap_bind_partial (partial_interpretation_tm U Π E _ a)
                   (λ ia, bind_partial
                            (partial_interpretation_tm _ _ _ _ _) _) _). }
        eapply leq_partial_trans.
        2: { eapply bind_leq_partial_1, IH_a. }
        eapply leq_partial_trans.
        2: { apply leq_partial_of_path, pathsinv0, bind_fmap_partial_1. }
        apply bind_leq_partial_2; intros a_interp.
        (* part for [t] argument *)
        eapply leq_partial_trans.
        { apply leq_partial_of_path.
          apply (fmap_bind_partial
                   (partial_interpretation_tm _ _ _ _ _)). }
        eapply leq_partial_trans.
        2: { eapply bind_leq_partial_1.
          eapply leq_partial_trans.
          2: { refine (tm_transportf_partial_interpretation_tm_leq _ _ _).
               apply (fmap_pi_form F_Π). }
          apply fmap_leq_partial, IH_t. }
        eapply leq_partial_trans.
        2: { apply leq_partial_of_path, pathsinv0.
             eapply pathscomp0; apply bind_fmap_partial_1. }
        apply bind_leq_partial_2; intros t_interp.
        (* assumption on [T] *)
        eapply leq_partial_trans.
        { eapply leq_partial_of_path, fmap_assume_partial. }
        use assume_partial_leq.
        { intros e_T.
          eapply pathscomp0. 2: { eapply maponpaths, e_T. }
          apply pathsinv0.
          eapply pathscomp0. 2: { apply reind_comp_typecat. }
          eapply pathscomp0. 2: { apply maponpaths, fmap_tm_as_map. }
          apply reindex_fmap_ty. }
        intros e_T; destruct e_T.
        (* final naturality part *)
        apply leq_partial_of_path.
        eapply pathscomp0. { apply fmap_return_partial. }
        apply maponpaths. rewrite tm_transportf_idpath.
        eapply pathscomp0. { apply (fmap_pi_app F_Π). }
        apply tm_transportf_irrelevant.
  Time Defined.

(* Notes re slowdown here:

- Moving context variables to be parameters in the theorem does
  _not_ seem to help typechecking speed here.

- [cbn] is used very sparingly: it slows down the [Defined], but can sometimes
  speed up individual steps enough to be worthwhile.

- Things get faster if we give Coq some more information in
  [fmap_bind_partial] and [bind_leq_partial_1]. If we don't tell Coq
  where [partial_interpretation_tm] and [partial_interpretation_ty]
  should be Coq picks unfolded versions of these two functions which
  blows up term sizes. Maybe we can control this some other way? Maybe
  using locking?
*)

Time End Functoriality.

Section Trivial_Interpretation.

  (** Each object of the syntactic category carries a “canonical environment”,
   with types/terms just the types/variables of the context. *)
  Definition canonical_environment
      {n} (Γ : wellformed_context_of_length n)
    : @environment syntactic_typecat (context_class Γ) n.
  Proof.
    intros i. use tpair.
    - apply (@ty_expr_as_type _ Γ (Γ i)).
      refine (hinhfun _ (context_derivable Γ)); intros d_Γ.
      apply derive_flat_cxt_from_strat, d_Γ.
    - refine (@tm_expr_as_term _ Γ (Γ i) _ (var_expr i) _).
      refine (hinhfun _ (context_derivable Γ)); intros d_Γ.
      apply derive_var, derive_flat_cxt_from_strat, d_Γ.
  Defined.

  (* TODO: triviality of the interpretation into the syntactic category:

  Fixpoint trivial_int erpretation_ty
    (ΓΓ : syntactic_typecat) 
  with trivial_interpretation_tm

  Surprisingly unclear how best to state this.  Something like:

  Over any (well-formed, stratified) context, with its canonical environment…

  - if a type/term is derivable and interpretable, then its interpretation is “itself” (by induction on expressions)?
  - if a type/term is interpretable, then it is derivable, and its interpretation is “itself”?  (by induction on expressions)
  - for any derivable judgement, its interpretation its “itself”? (by induction on derivations)?

  Probably go for the middle option — “if a type/term is interpretable in the canonical environmnent (and at some type), then it’s derivable, and its interpretation is itself”.   This can be phrased nicely in terms of [partial_leq] and [tm_/ty_expr_as_partial_type/_term], which may help organise the proof.

  The following is therefore a first attempt, which may turn out not to be the best approach.
*)
  Fixpoint trivial_interpretation_ty
      {n} (Γ : wellformed_context_of_length n)
      (e : ty_expr n)
      : leq_partial
          (partial_interpretation_ty
             SyntacticCategory_Structure.univ
             SyntacticCategory_Structure.pi
             (canonical_environment Γ) e)
          (ty_expr_as_partial_type Γ e)
  with trivial_interpretation_tm
      {n} (Γ : wellformed_context_of_length n)
      {T : ty_expr n} (isd_T : ∥ [! Γ |- T !] ∥)
      (e : tm_expr n)
      : leq_partial
          (partial_interpretation_tm
             SyntacticCategory_Structure.univ
             SyntacticCategory_Structure.pi
             (canonical_environment Γ)
             (ty_expr_as_type Γ isd_T)
             e)
          (tm_expr_as_partial_term Γ isd_T e).
  Proof.
    - (* rename_ty *)
      destruct e as [ m | m a | m A B ].
      + (* case [U_expr] *)
        use show_return_leq_partial.
        * apply hinhpr, derive_U.
        * cbn. 
          apply iscompsetquotpr.
          use typeeq_for_some_rep; apply hinhpr.
          exists (context_as_context_representative _).
          apply derive_tyeq_refl.
          apply derive_U.
      + (* case [El_expr] *)
        admit.
      + (* case [Pi_expr] *)
        admit.
    - (* rename_tm *)
      destruct e as [ m i | m A B b | m A B g a ].
      + (* case [var_expr] *)
        cbn.
        apply show_assume_leq_partial.
        intros e_Γi_T; cbn in e_Γi_T.
        use show_return_leq_partial.
        * cbn.
          assert (isd_Γi_T : ∥ [! Γ |- Γ i === T !] ∥).
          { refine (setquotprpathsandR _ _ _ e_Γi_T
                                       (context_as_context_representative Γ)). }
          refine (hinhfun3 _ (context_derivable Γ) isd_T isd_Γi_T);
            intros d_Γ d_T d_Γi_T.
          apply (derive_tm_conv Γ (Γ i));
            try apply derive_var; try apply derive_flat_cxt_from_strat;
            auto.
        * cbn. apply pathsinv0, tm_transportf_tm_expr_as_term_gen.
      + (* case [lam_expr] *)
        admit.
      + (* case [app_expr] *)
        admit.
  Admitted. (* [trivial_interpretation_ty], […tm]: substantial proof required here *)

  
End Trivial_Interpretation.
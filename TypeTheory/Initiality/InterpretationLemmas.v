(** Further lemmas on the interpretation function, separated here in order to keep [TypeTheory.Initiality.Interpretation] itself reasonably streamlined *)

Require Import UniMath.MoreFoundations.All.

Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.Partial.
Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.Initiality.SplitTypeCat_General.
Require Import TypeTheory.Initiality.SplitTypeCat_Structure.
Require Import TypeTheory.Initiality.SplitTypeCat_Maps.
Require Import TypeTheory.Initiality.Syntax.
Require Import TypeTheory.Initiality.Typing.
Require Import TypeTheory.Initiality.Environments.
Require Import TypeTheory.Initiality.Interpretation.

Section Functoriality_General.
(** Preparatory for section [Functoriality] below: some generalities on functoriality, independent of the logical structure. *)

  Context {C C'} (F : typecat_mor C C').

  (* TODO: consider naming/existence; probably upstream at least to with [fmap_tm], etc. *)
  Local Definition fmap_ty := typecat_mor_Ty F.

  (* TODO: upstream to with definition of [type_with_term] *)
  Definition fmap_type_with_term {Γ:C} (Aa : type_with_term Γ)
    : type_with_term (F Γ).
  Proof.
    exact (typecat_mor_Ty F _ (type_of Aa),,fmap_tm F Aa).
  Defined.

  (* TODO: upstream to [Environments] *)
  Definition fmap_environment {Γ:C} {n:nat} (E : environment Γ n)
    : environment (F Γ) n.
  Proof.
    intros i. exact (fmap_type_with_term (E i)).
  Defined.

  (* TODO: upstream to [Environments] *)
  Lemma fmap_reind_environment
      {Γ Γ' : C} (f : Γ' --> Γ) {n} (E : environment Γ n)
    : fmap_environment (reind_environment f E)
    = reind_environment (# F f) (fmap_environment E).
  Proof.
    apply funextsec; intros i.
    use paths_type_with_term2.
    - apply reindex_fmap_ty.
    - rewrite transportf_tm.
      apply reindex_fmap_tm.
  Defined.

  (* TODO: upstream to follow [var_with_type] *)
  Lemma var_with_type_fmap_type
      {Γ} (A : C Γ)
    : var_with_type (fmap_ty Γ A)
    = reind_type_with_term (inv_from_iso (typecat_mor_iso F A))
                           (fmap_type_with_term (var_with_type A)).
  Proof.
    use paths_type_with_term.
    + simpl.
      etrans; [|exact (maponpaths (fun X => reind_typecat X _) (!reindex_fmap_ty F _ (dpr_typecat A)))].
      etrans; [|apply reind_comp_type_typecat].
      apply maponpaths, pathsinv0, iso_inv_on_right, (typecat_mor_triangle F A).
    + apply PullbackArrowUnique; cbn.
    - rewrite <- assoc.
      etrans; [apply maponpaths, comp_ext_compare_dpr_typecat|].
      unfold map_into_Pb.
      set (pb := Auxiliary.Pbb _ _ _ _ _ _ _ _ _ _ _).
      apply (PullbackArrow_PullbackPr1 pb).
    - apply pathsinv0, iso_inv_on_right.
      set (f1 := map_into_Pb _ _ _ _ _ _ _ _ _).
      set (f2 := map_into_Pb _ _ _ _ _ _ _ _ _).
      rewrite comp_ext_compare_comp.
      rewrite comp_ext_compare_comp.
      admit. (* this is complicated... *)
  Admitted.

  (* TODO: upstream to with [fmap_environment] *)
  Lemma fmap_add_to_environment
        {Γ:C} {n} (E : environment Γ n) (Aa : type_with_term Γ)
    : fmap_environment (add_to_environment E Aa)
    = add_to_environment (fmap_environment E) (fmap_type_with_term Aa).
  Proof.
    apply funextfun. use dB_Sn_rect; intros; apply idpath.
  Qed.

  (* TODO: upstream to follow [extend_environment] *)
  Lemma fmap_extend_environment {Γ} {n} (E : environment Γ n) (A : C Γ)
    : extend_environment (fmap_environment E) (fmap_ty _ A)
    = reind_environment (inv_from_iso (typecat_mor_iso F _))
      (fmap_environment (extend_environment E A)).
  Proof.
    apply pathsinv0.
    eapply pathscomp0. { apply maponpaths, fmap_add_to_environment. }
    eapply pathscomp0. { apply reind_add_to_environment. }
    apply (maponpaths_12 add_to_environment).
    - eapply pathscomp0. { apply maponpaths, fmap_reind_environment. }
      eapply pathscomp0. { apply pathsinv0, reind_compose_environment. }
      apply maponpaths_2. apply iso_inv_on_right, typecat_mor_triangle.
    - apply pathsinv0, var_with_type_fmap_type.
  Qed.

End Functoriality_General.

Section Functoriality.
(** Key property of the interpretation: if [F : C --> D] is a map of split type-cats with logical structure, and some expression [e] is interpretable in [C] in some environment [E] with value [a], then [e] is also interpretable in [D] in environment [F E], with value [F a]. *)

  Context {C} {U : universe_struct C} {Π : pi_struct C}
          {C'} {U' : universe_struct C'} {Π' : pi_struct C'}
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

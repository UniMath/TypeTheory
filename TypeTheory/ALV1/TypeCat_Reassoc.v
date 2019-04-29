
(** 

 Ahrens, Lumsdaine, Voevodsky, 2015–

Contents:

  - Equivalence [weq_standalone_regrouped] between split type-categories, and their reassociated version based on object-extension structures.

The equivalence is a bit more involved than one might hope; it proceeds in two main steps:

- Firstly, perform a big permutation/reassociation of the various components.  This is proven as a purely structural lemma, with the actual concrete types abstracted away — all that is needed is to know which components depend on which earlier ones.

- Secondly, with the components in the right order, massage away the slight differences in the statements of individual components, by repeated use of [weqbandf].

*)

Require Import UniMath.Foundations.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.

Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Defs.
Require Import TypeTheory.ALV1.TypeCat.

(** ** Structural permutation/reassociation lemma

We give, purely structurally, a weak equivalence [weq_reassoc_direct] between an iterated sigma-type with components ordered/associated as in [split_type_struct] (the standalone definition of a split type-category structure) and one with the same components ordered/associated as in [split_typecat_structure] (the definition based on object-extension structures). *)

Section Structural_Reassoc.

Context
  (T_ty : UU)
  (T_ext : T_ty -> UU)
  (T_dpr : ∏ ty, T_ext ty -> UU)
  (T_reind : T_ty -> UU)
  (T_q_etc : ∏ ty ext, (T_dpr ty ext) -> (T_reind ty) -> UU)
  (T_set : T_ty -> UU)
  (T_reind_id : ∏ ty, T_reind ty -> UU)
  (T_q_id : ∏ ty ext dpr reind,
    (T_q_etc ty ext dpr reind) -> (T_reind_id ty reind) -> UU)
  (T_reind_comp : ∏ ty, T_reind ty -> UU)
  (T_q_comp : ∏ ty ext dpr reind, 
    (T_q_etc ty ext dpr reind) -> (T_reind_comp ty reind) -> UU).

Arguments T_dpr [_] _.
Arguments T_q_etc [_ _] _ _.
Arguments T_reind_id [_] _.
Arguments T_q_id [_ _ _ _] _ _.
Arguments T_reind_comp [_] _.
Arguments T_q_comp [_ _ _ _] _ _.

(* Parallel the way a split type-cat is built up: *)

Definition struct1 : UU
  := ∑ ty (ext : T_ext ty), T_reind ty.

Definition struct2 (S1 : struct1)
  (ty := pr1 S1) (ext := pr1 (pr2 S1)) (reind := pr2 (pr2 S1))
:= ∑ dpr, @T_q_etc ty ext dpr reind.

Definition struct_total := ∑ S1, struct2 S1.

Definition is_split (S : struct_total)
  (ty := pr1 (pr1 S)) (reind := pr2 (pr2 (pr1 S))) (q_etc := pr2 (pr2 S))
:= T_set ty
  × (∑ reind_id, T_q_id q_etc reind_id)
  × (∑ reind_comp, T_q_comp q_etc reind_comp).

Definition split_struct := ∑ S, is_split S.

(* Reassociated version, close to the version involving object-extension structures *)

Definition pshf_data
:= ∑ (Ty : ∑ (ty : T_ty), T_set ty), T_reind (pr1 Ty).

Definition pshf_axioms (F : pshf_data)
  (reind := pr2 F)
:= T_reind_id reind × T_reind_comp reind.

Definition pshf
:= ∑ F, pshf_axioms F.

Definition ext_struct (F : pshf_data)
  (ty := pr1 (pr1 F)) (reind := pr2 F)
:= ∑ (ext : T_ext ty), T_dpr ext.

Definition obj_ext_struct
:= ∑ (F : pshf), ext_struct (pr1 F).

Definition gen_q_mor_data (X : obj_ext_struct)
  (ext := pr1 (pr2 X)) (dpr := pr2 (pr2 X))
  (reind := pr2 (pr1 (pr1 X))) 
:= T_q_etc dpr reind.

Definition gen_q_mor_axs {X : obj_ext_struct} (q_etc : gen_q_mor_data X)
  (A := pr2 (pr1 X)) (reind_id := pr1 A) (reind_comp := pr2 A)
:= T_q_id q_etc reind_id × T_q_comp q_etc reind_comp.

Definition gen_q_mor_struct (X : obj_ext_struct)
:= ∑ (q_etc : gen_q_mor_data X), gen_q_mor_axs q_etc.

Definition reassoc_split_struct
:= ∑ X, gen_q_mor_struct X.


(* Timing test *)

(*
Definition temp : reassoc_split_struct -> reassoc_split_struct.
Proof.
Time intros [[[[[ty set] reind] [reind_id reind_comp]] [ext dpr]] [q_etc [q_id q_comp]]].
Abort.

Definition temp : split_struct -> split_struct.
Proof.
  Time intros [[[ty [ext reind]] [dpr q_etc]] [set [[reind_id q_id] [reind_comp q_comp]]]].
Abort.
*)

(* Equivalence between original and reassociated versions *)

Definition l_to_r_reassoc_direct : split_struct -> reassoc_split_struct.
Proof.
  intros S.
  use tpair.
  - use tpair.
    + exists ((pr1 (pr1 (pr1 S)),, pr1 (pr2 S)),, pr2 (pr2 (pr1 (pr1 S)))).
      exact (pr1 (pr1 (pr2 (pr2 S))),, pr1 (pr2 (pr2 (pr2 S)))).
    + exact (pr1 (pr2 (pr1 (pr1 S))),, pr1 (pr2 (pr1 S))).
  - exists (pr2 (pr2 (pr1 S))).
    exact (pr2 (pr1 (pr2 (pr2 S))),, pr2 (pr2 (pr2 (pr2 S)))).
Defined.

Definition r_to_l_reassoc_direct : reassoc_split_struct -> split_struct.
Proof.
  intros S.
  use tpair.
  - exists (pr1 (pr1 (pr1 (pr1 (pr1 S)))) ,,
                (pr1 (pr2 (pr1 S)) ,, (pr2 (pr1 (pr1 (pr1 S)))))).
    exact (pr2 (pr2 (pr1 S)),, pr1 (pr2 S)).
  - repeat apply make_dirprod; simpl.
    + exact (pr2 (pr1 (pr1 (pr1 (pr1 S))))).
    + exact (pr1 (pr2 (pr1 (pr1 S))),, pr1 (pr2 (pr2 S))).
    + exact (pr2 (pr2 (pr1 (pr1 S))),, pr2 (pr2 (pr2 S))).
Defined.

Theorem weq_reassoc_direct : split_struct ≃ reassoc_split_struct.
Proof.
  use (weq_iso l_to_r_reassoc_direct r_to_l_reassoc_direct).
  - intros [[[ty [ext reind]] [dpr q_etc]] [set [[reind_id q_id] [reind_comp q_comp]]]].
    apply idpath.
  - intros [[[[[ty set] reind] [reind_id reind_comp]] [ext dpr]] [q_etc [q_id q_comp]]].
    apply idpath.
Defined.

End Structural_Reassoc.

Section Fix_Category.

Context {CC : category}.

(** ** Equivalence between split type-cat structures and their structurally-abstracted version 

This is in fact a judgemental equality; but recognising this in practice is rather slow, so we explicitly declare the equivalence [weq_standalone_structural] between them. *)

Section Split_Type_Cat_as_Structural.

Definition T_ty
  := (CC -> UU).
Definition T_ext
  := (λ ty, ∏ Γ : CC, ty Γ -> CC).
Definition T_dpr
  := (λ ty ext, ∏ (Γ : CC) (A : ty Γ), ext Γ A --> Γ ).
Definition T_reind
  := (λ ty, ∏ (Γ : CC) (A : ty Γ) (Γ' : CC), (Γ' --> Γ) -> ty Γ').
Definition T_q_etc
  := (λ ty ext (dpr : T_dpr ty ext) (reind : T_reind ty), 
     ∑ (q : ∏ (Γ:CC) (A : ty Γ) Γ' (f : Γ' --> Γ),
         (ext Γ' (reind _ A _ f)) --> (ext Γ A))
       (dpr_q : ∏ Γ (A : ty Γ) Γ' (f : Γ' --> Γ),
         q _ A _ f ;; dpr Γ A = dpr Γ' (reind _ A _ f) ;; f),
       (∏ Γ (A : ty Γ) Γ' (f : Γ' --> Γ),
         isPullback _ _ _ _ (!dpr_q _ A _ f))).
Definition T_set
  := (λ ty : T_ty, ∏ Γ, isaset (ty Γ)).
Definition T_reind_id
  := (λ ty (reind : T_reind ty), ∏ Γ A, reind _ A _ (identity Γ) = A).
Definition T_q_id
  := (λ ty ext dpr reind (q_etc : T_q_etc ty ext dpr reind)
                         (reind_id : T_reind_id ty reind),
       ∏ Γ A, (pr1 q_etc) _ A _ (identity Γ)
              = idtoiso (maponpaths (ext Γ) (reind_id Γ A))).
Definition T_reind_comp
  := (λ ty (reind : T_reind ty),
       ∏ Γ A Γ' (f : Γ' --> Γ) Γ'' (g : Γ'' --> Γ'),
         reind _ A _ (g ;; f) = reind _ (reind _ A _ f) _ g).
Definition T_q_comp
  := (λ ty ext dpr reind (q_etc : T_q_etc ty ext dpr reind)
                         (reind_comp : T_reind_comp ty reind),
       ∏ Γ A Γ' (f : Γ' --> Γ) Γ'' (g : Γ'' --> Γ'),
         (pr1 q_etc) _ A _ (g ;; f)
         = idtoiso (maponpaths (ext Γ'') (reind_comp _ A _ f _ g))
               ;; (pr1 q_etc) _ (reind _ A _ f) _ g
               ;; (pr1 q_etc) _ A _ f).

Definition eq_standalone_structural
  : split_typecat_structure CC
    = split_struct
        T_ty T_ext T_dpr T_reind T_q_etc
        T_set T_reind_id T_q_id T_reind_comp T_q_comp.
Proof.
  apply idpath.
Defined.

Definition weq_standalone_structural
  : split_typecat_structure CC
    ≃ split_struct
        T_ty T_ext T_dpr T_reind T_q_etc
        T_set T_reind_id T_q_id T_reind_comp T_q_comp.
Proof.
  apply eqweqmap, eq_standalone_structural.
Defined.

(** Alternate construction of [weq_standalone_structural], retained in case it gives better computational behaviour: *)

Definition standalone_to_structural
  : split_typecat_structure CC
    -> split_struct
        T_ty T_ext T_dpr T_reind T_q_etc
        T_set T_reind_id T_q_id T_reind_comp T_q_comp.
Proof.
  intros S. exact (transportf (fun X => X) eq_standalone_structural S).
Defined.

Definition structural_to_standalone
  : split_struct
        T_ty T_ext T_dpr T_reind T_q_etc
        T_set T_reind_id T_q_id T_reind_comp T_q_comp
  -> split_typecat_structure CC.
Proof.
  intros S. exact (transportb (fun X => X) eq_standalone_structural S).
Defined.

Definition weq_standalone_structural_explicit
  : split_typecat_structure CC
    ≃ split_struct
        T_ty T_ext T_dpr T_reind T_q_etc
        T_set T_reind_id T_q_id T_reind_comp T_q_comp.
Proof.
  use (weq_iso standalone_to_structural structural_to_standalone).
  - intros; apply idpath.
  - intros; apply idpath.
Defined.

End Split_Type_Cat_as_Structural.

(** ** Equivalence between the structural and object-extension versions 

Here we build up an equivalence [weq_structural_regrouped] between (RHS) the regrouped object-extension structure definition of split type-category structures, and (LHS) the structurally-abstracted definition, with the types of components taken from the standalone definition, but re-ordered and re-grouped to match (RHS).

Since the ordering/association of the sigma-type matches, this equivalence could in principle be done in a single declaration by repeated use of [weqbandf].  However, the compilation time becomes infeasaible, so instead we split it up into multiple declarations. *)
Section Structural_to_Regrouped.

Definition weq_structural_pshf_data
  : pshf_data T_ty T_reind T_set
  ≃ functor_data CC^op HSET_univalent_category.
Proof.
  use weqbandf.
    apply weqtotaltoforall.
  simpl. intros. unfold T_reind.
  apply weqonsecfibers; intro Γ.
  eapply weqcomp. apply weq_exchange_args.
  apply weqonsecfibers; intro Γ'.
  apply weq_exchange_args.
Defined.

Definition weq_structural_pshf_axioms
    (x : pshf_data T_ty T_reind T_set)
  : pshf_axioms _ _ _ T_reind_id T_reind_comp x
  ≃ is_functor (weq_structural_pshf_data x).
Proof.
  apply weqdirprodf.
  - cbn. unfold bandfmap, weqforalltototal, maponsec.
    cbn. unfold totaltoforall, T_reind_id, functor_idax. 
    apply weqonsecfibers; intro Γ.
    apply weqfunextsec.
  - cbn. unfold bandfmap, weqforalltototal, maponsec.
    cbn. unfold totaltoforall, T_reind_comp, functor_compax. 
    apply weqonsecfibers; intro Γ.
    eapply weqcomp. apply weq_exchange_args.
    apply weqonsecfibers; intro Γ'.
    eapply weqcomp. 
      apply weqonsecfibers; intro A. apply weq_exchange_args.
    eapply weqcomp. apply weq_exchange_args.
    apply weqonsecfibers; intro Γ''.
    eapply weqcomp. apply weq_exchange_args.
    apply weqonsecfibers; intro f.
    eapply weqcomp. apply weq_exchange_args.
    apply weqonsecfibers; intro g.
    apply weqfunextsec.
Qed.

Definition weq_structural_pshf
  : pshf T_ty T_reind T_set T_reind_id T_reind_comp
  ≃ preShv CC.
Proof.
  use weqbandf.
  apply weq_structural_pshf_data.
  apply weq_structural_pshf_axioms.
Defined.

Definition weq_structural_obj_ext
  : obj_ext_struct T_ty T_ext T_dpr T_reind T_set T_reind_id T_reind_comp
  ≃ obj_ext_structure CC.
Proof.
  use weqbandf.
    apply weq_structural_pshf.
  intro F. simpl. unfold ext_struct, T_ext, T_dpr.
  eapply weqcomp.
    exact (@weqtotaltoforall CC
      (λ Γ, (pr1 (pr1 (pr1 F)) Γ → CC))
      (λ Γ extΓ, ∏ (A : pr1 (pr1 (pr1 F)) Γ), extΓ A --> Γ)).
  apply weqonsecfibers; intro Γ.
  exact (@weqtotaltoforall _ _ (λ A ΓA, ΓA --> Γ)).
Defined.

Definition weq_structural_q_mor_data
    (X : obj_ext_struct
           T_ty T_ext T_dpr T_reind T_set T_reind_id T_reind_comp)
  : gen_q_mor_data _ _ _ _ T_q_etc T_set _ _ X
  ≃ qq_morphism_data (weq_structural_obj_ext X).
Proof.
    cbn. unfold bandfmap, weqforalltototal, maponsec.
    cbn. unfold totaltoforall, gen_q_mor_data, T_q_etc, qq_morphism_data.
    cbn.
    use weqbandf.
      apply weqonsecfibers; intro Γ.
      eapply weqcomp. apply weq_exchange_args.
      apply weqonsecfibers; intro Γ'.
      apply weq_exchange_args.
    cbn. intro q.
    eapply weqcomp.
      exact (@weqtotaltoforall CC
        (λ Γ, _)
        (λ Γ dpr_q_Γ, ∏ A Γ' f, isPullback _ _ _ _ (!dpr_q_Γ A Γ' f))).
    apply weqonsecfibers; intro Γ.
    eapply weqcomp.
      exact (@weqtotaltoforall (pr1 (pr1 (pr1 (pr1 X))) Γ)
        (λ A, _)
        (λ A dpr_q_Γ_A, ∏ Γ' f, isPullback _ _ _ _ (!dpr_q_Γ_A Γ' f))).
    eapply weqcomp.
      apply weqonsecfibers; intro A.
      eapply weqcomp.
        exact (@weqtotaltoforall CC
          (λ Γ', _)
          (λ Γ' dpr_q_Γ_A_Γ', ∏ f, isPullback _ _ _ _ (!dpr_q_Γ_A_Γ' f))).
      apply weqonsecfibers; intro Γ'.
      exact (@weqtotaltoforall _
        (λ f, _)
        (λ f dpr_q_Γ_A_Γ'_f, isPullback _ _ _ _ (!dpr_q_Γ_A_Γ'_f))).
    simpl.
    eapply weqcomp. apply weq_exchange_args.
    apply weqonsecfibers; intro Γ'.
    apply weq_exchange_args.
Defined.

Definition weq_structural_regrouped
  : reassoc_split_struct
      T_ty T_ext T_dpr T_reind T_q_etc
      T_set T_reind_id T_q_id T_reind_comp T_q_comp
  ≃ split_typecat'_structure CC.
Proof.
  use weqbandf. apply weq_structural_obj_ext. intro X. 
  use weqbandf. apply weq_structural_q_mor_data. intros q_etc.
  unfold qq_morphism_axioms. cbn.
  unfold bandfmap, weqforalltototal, maponsec. cbn.
  apply weqdirprodf.
  - apply weqonsecfibers; intro Γ.
    apply weqonsecfibers; intro A.
    apply weqpathscomp0r.
    unfold comp_ext_compare. 
    apply maponpaths, maponpaths, maponpaths.
    apply (pr2 (pr1 (pr1 (pr1 X)))). (* the hset assumption on ty *)
  - apply weqonsecfibers; intro Γ.
    eapply weqcomp. apply weq_exchange_args.
    apply weqonsecfibers; intro Γ'.
    eapply weqcomp. 
      apply weqonsecfibers; intro A. apply weq_exchange_args.
    eapply weqcomp. apply weq_exchange_args.
    apply weqonsecfibers; intro Γ''.
    eapply weqcomp. apply weq_exchange_args.
    apply weqonsecfibers; intro f.
    eapply weqcomp. apply weq_exchange_args.
    apply weqonsecfibers; intro g.
    apply weqonsecfibers; intro A.
    apply weqpathscomp0r.
    apply maponpaths_2, maponpaths_2.
    unfold comp_ext_compare. 
    apply maponpaths, maponpaths, maponpaths.
    apply (pr2 (pr1 (pr1 (pr1 X)))). (* the hset assumption on ty *)
Defined.

End Structural_to_Regrouped.

Section Standalone_to_Regrouped.

Definition weq_standalone_to_regrouped
  : split_typecat_structure CC
  ≃ split_typecat'_structure CC.
Proof.
  eapply weqcomp. apply weq_standalone_structural.
  eapply weqcomp. apply weq_reassoc_direct.
  apply weq_structural_regrouped.
Defined.

End Standalone_to_Regrouped.

End Fix_Category.


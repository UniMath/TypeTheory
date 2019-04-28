(**
  [TypeTheory.Initiality.Typing]

  Part of the [Initiality] package for the [UniMath.TypeTheory] library

  This file sets up the contexts, judgements, and derivations of the toy type theory under consideration. 
*)

Require Import UniMath.MoreFoundations.All.
Require Import TypeTheory.Initiality.Syntax.

Section Contexts.
  (** Note: for now, we take the type expressions of a context to be over
  _all_ variables of the context, not just the earlier ones.  *)
  (* TODO: add more explanation of this choice. *)
  Definition context_of_length n := dB_vars n -> ty_expr n.
  Identity Coercion id_context_of_length : context_of_length >-> Funclass.

  Definition context
    := ∑ (n : nat), context_of_length n.

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
    refine (rename_ty dB_next ∘ _).
    refine (dB_Sn_rect _ _ _).
    - exact A.
    - intros i. exact (Γ i).
  Defined.

End Contexts.

Delimit Scope context_scope with context.
Bind Scope context_scope with context.
Bind Scope context_scope with context_of_length.
Notation "[: :]" := (empty_context) (format "[: :]") : context_scope.
Notation "Γ ;; A"
  := (context_extend Γ A) (at level 50, left associativity) : context_scope. 
(* TODO: not sure what level to use here; try it and see… *)
Notation "[: A ; .. ; Z :] "
  := (context_extend .. (context_extend (empty_context) A) .. Z) : context_scope.

Section Judgements.

(** NOTE: we take as primitive just the four main hypothetical judgements.

Other judgements, such as well-formed contexts and context maps, will be “auxiliary” judgements defined in terms of these afterwards.

The inductive definition of derivability involves only the primitive judgements. *)
  Inductive judgement
  :=
    | ty_judgement (Γ : context) (A : ty_expr Γ)
    | tyeq_judgement (Γ : context) (A A' : ty_expr Γ)
    | tm_judgement (Γ : context) (A : ty_expr Γ) (a : tm_expr Γ)
    | tmeq_judgement (Γ : context) (A : ty_expr Γ) (a a' : tm_expr Γ).

End Judgements.

Delimit Scope judgement_scope with judgement.
Bind Scope judgement_scope with judgement.
Open Scope judgement_scope.

Notation "[! Γ |- A === B !]" := (tyeq_judgement Γ A B) (format "[!  Γ  |-  A  ===  B  !]")  : judgement_scope.
Notation "[! Γ |- A !]" := (ty_judgement Γ A) (format "[!  Γ  |-  A  !]")  : judgement_scope.
Notation "[! Γ |- a ::: A !]" := (tm_judgement Γ A a) (format "[!  Γ  |-  a  :::  A  !]")  : judgement_scope.
Notation "[! Γ |- a === a' ::: A !]" := (tmeq_judgement Γ A a a') (format "[!  Γ  |-  a  ===  a'  :::  A  !]")  : judgement_scope.
(* NOTE: these [===], [:::] are horrible!  But I can’t make it work with just e.g. [=], since parsing fails as [=] is already a binary notation (even if the scope of that notation is closed).  Is it possible to use better scoping to allow just [=] here, and so on? *) 

Section Derivations.

  Inductive derivation : judgement -> UU
  :=
    (** variable rule *)
    | derive_var (Γ : context) (i : Γ)
      :    derivation [! Γ |- Γ i !] 
      -> derivation [! Γ |- (var_expr i) ::: Γ i !]
    (** structural rules for equality: equiv rels, plus type-conversion *)
    | derive_tyeq_refl (Γ : context) (A : _)
      :    derivation [! Γ |- A !]
      -> derivation [! Γ |- A === A !]
    | derive_tyeq_sym (Γ : context) (A A' : _)
      :    derivation [! Γ |- A === A' !]
      -> derivation [! Γ |- A' === A !]
    | derive_tyeq_trans (Γ : context) (A0 A1 A2 : _)
      :    derivation [! Γ |- A0 !]
        -> derivation [! Γ |- A1 !]
        -> derivation [! Γ |- A2 !]
        -> derivation [! Γ |- A0 === A1 !]
        -> derivation [! Γ |- A1 === A2 !]
      -> derivation [! Γ |- A0 === A2 !]
    | derive_tmeq_refl (Γ : context) (A : _) (a : _)
      :    derivation [! Γ |- a ::: A !]
      -> derivation [! Γ |- a === a ::: A !]
    | derive_tmeq_sym (Γ : context) (A : _) (a a' : _)
      :    derivation [! Γ |- a === a' ::: A !]
      -> derivation [! Γ |- a' === a ::: A !]
    | derive_tmeq_trans (Γ : context) (A : _) (a0 a1 a2 : _)
      :    derivation [! Γ |- a0 ::: A !]
        -> derivation [! Γ |- a1 ::: A !]
        -> derivation [! Γ |- a2 ::: A !]
        -> derivation [! Γ |- a0 === a1 ::: A !]
        -> derivation [! Γ |- a1 === a2 ::: A !]
      -> derivation [! Γ |- a0 === a2 ::: A !]
    | derive_tm_conv (Γ : context) (A A' : _) (a : _)
      :    derivation [! Γ |- A !]
        -> derivation [! Γ |- A' !]
        -> derivation [! Γ |- A === A' !]
        -> derivation [! Γ |- a ::: A !]
      -> derivation [! Γ |- a ::: A' !]
    | derive_tmeq_conv (Γ : context) (A A' : _) (a a' : _)
      :    derivation [! Γ |- A !]
        -> derivation [! Γ |- A' !]
        -> derivation [! Γ |- A === A' !]
        -> derivation [! Γ |- a === a' ::: A !]
      -> derivation [! Γ |- a === a' ::: A' !]

    (** logical rules  *)
    | derive_U (Γ : context) 
      : derivation [! Γ |- U_expr !]
    | derive_El (Γ : context) (a : _)
      :    derivation [! Γ |- a ::: U_expr !]
      -> derivation [! Γ |- El_expr a !]
    | derive_Pi (Γ : context) (A : _) (B : _)
      :    derivation [! Γ |- A !]
        -> derivation [! Γ ;; A |- B !]
      -> derivation [! Γ |- Pi_expr A B !]
    | derive_lam (Γ : context) A B b
      :    derivation [! Γ |- A !]
        -> derivation [! Γ ;; A |- B !]
        -> derivation [! Γ ;; A |- b ::: B !]
      -> derivation [! Γ |- lam_expr A B b ::: Pi_expr A B !]
    | derive_app (Γ : context) A B f a
      :    derivation [! Γ |- A !]
        -> derivation [! Γ ;; A |- B !]
        -> derivation [! Γ |- f ::: Pi_expr A B !]
        -> derivation [! Γ |- a ::: A !]
      -> derivation [! Γ |- app_expr A B f a ::: subst_top_ty a B !]
    | derive_beta (Γ : context) A B b a
      :    derivation [! Γ |- A !]
        -> derivation [! Γ ;; A |- B !]
        -> derivation [! Γ ;; A |- b ::: B !]
        -> derivation [! Γ |- a ::: A !]
      -> derivation
             [! Γ |- app_expr A B (lam_expr A B b) a === subst_top_tm a b 
                                                     ::: subst_top_ty a B !]

    (** congruence rules for constructors *)
    (* no congruence rule needed for U *)
    | derive_El_cong (Γ : context) (a a' : _)
      :    derivation [! Γ |- a === a' ::: U_expr !]
      -> derivation [! Γ |- El_expr a === El_expr a' !]
    | derive_Pi_cong (Γ : context) (A A' : _) (B B' : _)
      :    derivation [! Γ |- A !] 
        -> derivation [! Γ |- A === A' !]
        -> derivation [! Γ ;; A |- B === B' !]
      -> derivation [! Γ |- Pi_expr A B === Pi_expr A' B' !]
    | derive_lam_cong (Γ : context) A A' B B' b b'
      :    derivation [! Γ |- A !] 
        -> derivation [! Γ |- A === A' !]
        -> derivation [! Γ ;; A |- B === B' !]
        -> derivation [! Γ ;; A |- b === b' ::: B !]
      -> derivation [! Γ |- lam_expr A B b === lam_expr A' B' b'
                                                 ::: Pi_expr A B !]
    | derive_app_cong (Γ : context) A A' B B' f f' a a'
      :    derivation [! Γ |- A !] 
        -> derivation [! Γ |- A === A' !]
        -> derivation [! Γ ;; A |- B === B' !]
        -> derivation [! Γ |- f === f' ::: Pi_expr A B !]
        -> derivation [! Γ |- a === a' ::: A !]
      -> derivation [! Γ |- app_expr A B f a === app_expr A' B' f' a'
                                                   ::: subst_top_ty a B !]
  .

  Coercion derivation : judgement >-> UU.
 
End Derivations.

Section Derivation_Helpers.
(** Some utility functions to make inductions over derivations more manageable.*)

  Local Open Scope context_scope.

  Context (P : forall J:judgement, derivation J -> Type).
  Local Arguments P {_} _.

  Definition case_for_var_rule
  := forall (Γ : context) (i : Γ)
            (d_Γi : [! Γ |- Γ i !]) (p_Γi : P d_Γi),
    P (derive_var Γ i d_Γi).

  Record cases_for_equiv_rel_rules
  := {
    case_tyeq_refl
    : forall (Γ : context) (A : ty_expr Γ)
             (d : [! Γ |- A !]) (p : P d),
        P (derive_tyeq_refl Γ A d)
  ; case_teq_sym
    : forall (Γ : context) (A A' : ty_expr Γ)
             (d : [! Γ |- A === A' !]) (p : P d),
      P (derive_tyeq_sym Γ A A' d)
  ; case_tyeq_trans
    : forall (Γ : context) (A0 A1 A2 : ty_expr Γ)
             (d0 : [! Γ |- A0 !]) (p0 : P d0)
             (d1 : [! Γ |- A1 !]) (p1 : P d1)
             (d2 : [! Γ |- A2 !]) (p2 : P d2)
             (d01 : [! Γ |- A0 === A1 !]) (p01 : P d01)
             (d12 : [! Γ |- A1 === A2 !]) (p12 : P d12),
      P (derive_tyeq_trans Γ A0 A1 A2 d0 d1 d2 d01 d12)
  ; case_tmeq_refl
    : forall (Γ : context) (A : ty_expr Γ) (a : tm_expr Γ)
             (d : [! Γ |- a ::: A !]) (p : P d),
      P (derive_tmeq_refl Γ A a d)
  ; case_tmeq_sym
    : forall (Γ : context) (A : ty_expr Γ) (a a' : tm_expr Γ)
             (d : [! Γ |- a === a' ::: A !]) (p : P d),
      P (derive_tmeq_sym Γ A a a' d)
  ; case_tmeq_trans
    : forall (Γ : context) (A : ty_expr Γ) (a0 a1 a2 : tm_expr Γ)
             (d0 : [! Γ |- a0 ::: A !]) (p0 : P d0)
             (d1 : [! Γ |- a1 ::: A !]) (p1 : P d1)
             (d2 : [! Γ |- a2 ::: A !]) (p2 : P d2)
             (d01 : [! Γ |- a0 === a1 ::: A !]) (p01 : P d01)
             (d12 : [! Γ |- a1 === a2 ::: A !]) (p12 : P d12),
      P (derive_tmeq_trans Γ A a0 a1 a2 d0 d1 d2 d01 d12)
  }.

  Record cases_for_conv_rules
  := {
    case_tm_conv
    : forall (Γ : context) (A A' : ty_expr Γ) (a : tm_expr Γ)
             (d_A : [! Γ |- A !]) (p_A : P d_A)
             (d_A' : [! Γ |- A' !]) (p_A' : P d_A')
             (d_AA' : [! Γ |- A === A' !]) (p_AA' : P d_AA')
             (d_a : [! Γ |- a ::: A !]) (p_a : P d_a),
        P (derive_tm_conv Γ A A' a d_A d_A' d_AA' d_a)
  ; case_tmeq_conv
    : forall (Γ : context) (A A' : ty_expr Γ) (a a' : tm_expr Γ)
             (d_A : [! Γ |- A !]) (p_A : P d_A)
             (d_A' : [! Γ |- A' !]) (p_A' : P d_A')
             (d_AA' : [! Γ |- A === A' !]) (p_AA' : P d_AA')
             (d_aa' : [! Γ |- a === a' ::: A !]) (p_aa' : P d_aa'),
      P (derive_tmeq_conv Γ A A' a a' d_A d_A' d_AA' d_aa')
  }.

  Record cases_for_universe_rules
  := {
    case_for_U
    : forall (Γ : context),
        P (derive_U Γ)
  ; case_for_El
    : forall (Γ : context) (a : tm_expr Γ)
             (d_a : [! Γ |- a ::: U_expr !]) (p_a : P d_a),
      P (derive_El Γ a d_a)
  ; case_for_El_cong
    : forall (Γ : context) (a a' : tm_expr Γ)
             (d_aa' : [! Γ |- a === a' ::: U_expr !]) (p_aa' : P d_aa'),
      P (derive_El_cong Γ a a' d_aa')
  }.

  Record cases_for_pi_rules
  := {
    case_for_Pi
    : forall (Γ : context) (A : ty_expr Γ) (B : ty_expr (Γ ;; A))
             (d_A : [! Γ |- A !]) (p_A : P d_A)
             (d_B : [! Γ ;; A |- B !]) (p_B : P d_B),
      P (derive_Pi Γ A B d_A d_B)
  ; case_for_lam
    : forall (Γ : context) (A : ty_expr Γ) (B : ty_expr (Γ ;; A))
             (b : tm_expr (Γ ;; A))
             (d_A : [! Γ |- A !]) (p_A : P d_A)
             (d_B : [! Γ ;; A |- B !]) (p_B : P d_B)
             (d_b : [! Γ ;; A |- b ::: B !]) (p_b : P d_b),
      P (derive_lam Γ A B b  d_A d_B d_b)
  ; case_for_app
    : forall (Γ : context) (A : ty_expr Γ) (B : ty_expr (Γ ;; A))
             (f a : tm_expr Γ)
             (d_A : [! Γ |- A !]) (p_A : P d_A)
             (d_B : [! Γ ;; A |- B !]) (p_B : P d_B)
             (d_f : [! Γ |- f ::: Pi_expr A B !]) (p_f : P d_f)
             (d_a : [! Γ |- a ::: A !]) (p_a : P d_a),
      P (derive_app Γ A B f a d_A d_B d_f d_a)
  ; case_for_beta
    : forall (Γ : context) (A : ty_expr Γ) (B : ty_expr (Γ ;; A))
             (b : tm_expr (Γ ;; A)) (a : tm_expr Γ)
             (d_A : [! Γ |- A !]) (p_A : P d_A)
             (d_B : [! Γ ;; A |- B !]) (p_B : P d_B)
             (d_b : [! Γ ;; A |- b ::: B !]) (p_b : P d_b)
             (d_a : [! Γ |- a ::: A !]) (p_a : P d_a),
      P (derive_beta Γ A B b a d_A d_B d_b d_a)
  }.

  Record cases_for_pi_cong_rules
  := {
    case_for_Pi_cong
    : forall (Γ : context) (A A' : ty_expr Γ) (B B' : ty_expr (Γ ;; A))
        (d_A : [! Γ |- A !]) (p_A : P d_A)
        (d_AA : [! Γ |- A === A' !]) (p_AA : P d_AA)
        (d_BB : [! Γ ;; A |- B === B' !]) (p_BB : P d_BB),
      P (derive_Pi_cong Γ A A' B B' d_A d_AA d_BB)
  ; case_for_lam_cong
    : forall (Γ : context) (A A' : ty_expr Γ) (B B' : ty_expr (Γ ;; A))
        (b b' : tm_expr (Γ ;; A)) 
        (d_A : [! Γ |- A !]) (p_A : P d_A)
        (d_AA : [! Γ |- A === A' !]) (p_AA : P d_AA)
        (d_BB : [! Γ ;; A |- B === B' !]) (p_BB : P d_BB)
        (d_bb : [! Γ ;; A |- b === b' ::: B !]) (p_bb : P d_bb),
      P (derive_lam_cong Γ A A' B B' b b' d_A d_AA d_BB d_bb)
  ; case_for_app_cong
    : forall (Γ : context) (A A' : ty_expr Γ) (B B' : ty_expr (Γ ;; A))
        (f f' a a' : tm_expr Γ)
        (d_A : [! Γ |- A !]) (p_A : P d_A)
        (d_AA : [! Γ |- A === A' !]) (p_AA : P d_AA)
        (d_BB : [! Γ ;; A |- B === B' !]) (p_BB : P d_BB)
        (d_ff : [! Γ |- f === f' ::: Pi_expr A B !]) (p_ff : P d_ff)
        (d_aa : [! Γ |- a === a' ::: A !]) (p_aa : P d_aa),
      P (derive_app_cong Γ A A' B B' f f' a a' d_A d_AA d_BB d_ff d_aa)
    }.

  Definition derivation_rect_grouped
      (H_var_rule : case_for_var_rule)               (* 1 case *)
      (H_equiv_rel_rules : cases_for_equiv_rel_rules) (* 6 cases *)
      (H_conv_rules : cases_for_conv_rules)           (* 2 cases *)
      (H_universe_rules : cases_for_universe_rules)   (* 3 cases *)
      (H_pi_rules : cases_for_pi_rules)               (* 4 cases *)
      (H_pi_cong_rules : cases_for_pi_cong_rules)     (* 3 cases *)
    : forall J (d : derivation J), P d.
  Proof.
    destruct H_equiv_rel_rules, H_conv_rules, 
      H_universe_rules, H_pi_rules, H_pi_cong_rules.
    apply derivation_rect; eauto.
  Defined.

End Derivation_Helpers.
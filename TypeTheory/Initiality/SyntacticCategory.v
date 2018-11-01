(** This file defines the syntactic category of our toy type theory, and the logical structure on it. *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.All.

Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.Initiality.SplitTypeCat_Maps.
Require Import TypeTheory.Initiality.SplitTypeCat_Structure.
Require Import TypeTheory.Initiality.Syntax.
Require Import TypeTheory.Initiality.SyntaxLemmas.
Require Import TypeTheory.Initiality.Typing.
Require Import TypeTheory.Initiality.TypingLemmas.

Local Open Scope judgement.

Section Typed_Syntax.

  Definition ty_with_derivation (Γ : context) : UU
    := ∑ (A : ty_expr Γ), [! Γ |- A !].

  Coercion ty_expr_of_ty_with_derivation {Γ} (A : ty_with_derivation Γ) :
    ty_expr Γ := pr1 A.

  Definition tm_with_derivation (Γ : context) (A : ty_expr Γ) : UU
    := ∑ (a : tm_expr Γ), [! Γ |- a ::: A !].

  Coercion tm_expr_of_tm_with_derivation {Γ} {A : ty_with_derivation Γ}
    (a : tm_with_derivation Γ A) : tm_expr Γ := pr1 a.

End Typed_Syntax.

(** Identity and composition of _typed_ context maps. *)
Section Typed_Context_Category_Operations.

  Definition derivation_idmap_context (Γ : flat_context)
    : derivation_context_map Γ Γ (idmap_raw_context Γ).
  Proof.
    intros i.
    refine (transportb _ _ _).
    { apply maponpaths_2, subst_idmap_ty. }
    use derive_var; eauto using derivation_from_flat_context.
    admit. (* TODO: either abolish context judgements, or add them in def of flat contexts *)
  Admitted.

  Definition idmap_context {Γ : flat_context}
    : context_map Γ Γ
  := (idmap_raw_context Γ,, derivation_idmap_context Γ).

  Definition derivation_comp_raw_context {Γ Δ Θ : flat_context }
      {f : raw_context_map Γ Δ} {g : raw_context_map Δ Θ}
      (d_f : derivation_context_map Γ Δ f)
      (d_g : derivation_context_map Δ Θ g) 
    : derivation_context_map Γ Θ (comp_raw_context f g).
  Proof.
    intros i. cbn. unfold comp_raw_context at 2.
    refine (transportb _ _ _).
    { apply maponpaths_2, pathsinv0, subst_subst_ty. }
    refine (@subst_derivation [! _ |- _ ::: _ !] _ _ _ (_,,_)).
    - apply d_g.
    - admit. (* TODO: either abolish context judgements, or add them in def of flat contexts *)
    - apply d_f.
  Admitted.
  
  Definition comp_raw_context {Γ Δ Θ : flat_context }
      {f : context_map Γ Δ} {g : context_map Δ Θ}
    : context_map Γ Θ
  := (comp_raw_context f g,, 
     derivation_comp_raw_context (derivation_from_context_map f)
                                    (derivation_from_context_map g)).

End Typed_Context_Category_Operations.



Section Stratified_Contexts.
(** Here we define (well-typed) contexts, in the usual sense of being ordered + stratified. *)

(* TODO: perhaps rename [context] upstream to e.g. [raw_context] or
[flat_context], so these can just be [context]? *)

  Fixpoint stratified_context_aux (n : nat)
    : ∑ (X : Type), X -> context_of_length n.
  Proof.
    destruct n as [ | n].
    - exists unit. (* unique empty context *)
      intros _; exact empty_context.
    - set (cxt_n := pr1 (stratified_context_aux n)).
      set (realise := pr2 (stratified_context_aux n) : cxt_n -> _).
      exists (∑ (Γ : cxt_n), ty_with_derivation (realise Γ)).
      intros Γ_A.
      exact (context_extend (realise (pr1 Γ_A)) (pr2 Γ_A)).
  Defined.

  Definition stratified_context_of_length (n : nat)
  := pr1 (stratified_context_aux n).

  Definition realise_stratified_context {n}
    : stratified_context_of_length n -> context_of_length n
  := pr2 (stratified_context_aux n).

  Coercion realise_stratified_context
    : stratified_context_of_length >-> context_of_length.

  Definition stratified_context : UU
  := ∑ (n : nat), stratified_context_of_length n.

  Definition stratified_context_length : stratified_context -> nat := pr1.
  Coercion stratified_context_length : stratified_context >-> nat.

  Definition stratified_context_types : forall Γ : stratified_context, _ := pr2.
  Coercion stratified_context_types : stratified_context >-> stratified_context_of_length.

  Definition make_stratified_context {n}
    : stratified_context_of_length n -> stratified_context
  := fun Γ => (n,,Γ).
  Coercion make_stratified_context : stratified_context_of_length >-> stratified_context.

  (* any well-typed context is indeed derivably a context. *)
  Lemma stratified_context_derivable (Γ : stratified_context) : [! |- Γ !].
  Proof.
    destruct Γ as [n Γ].
    induction n as [|n IHn].
    - now apply derive_cxt_empty.
    - destruct Γ as [Γ A].
      now apply (derive_cxt_extend (realise_stratified_context Γ) A (IHn _)), A.
  Defined.

End Stratified_Contexts.

Section Context_Maps.
  (* Maybe all this section can be inlined into section [Category] below, depending how long it turns out. *)

  (* TODO: define: context maps are raw context maps, plus suitable typing information (but truncate derivations!); then quotient by judgemental equality!

  To behave well, they should be assumed to go between contexts that are at least well-typed (but “stratifiedness” shouldn’t really be needed). *)

  (* TODO: define identity context map, composition.

     These will make use of the variable and substitution structural rules, plus lemma above about derivability of well-typed contexts. *)

  (* TODO: lemmas on associativity etc.  Should be immediate from the similar lemmas on raw ones in [SyntaxLemmas]. *)

  (* TODO: “empty” and “extension” context maps. *)

End Context_Maps.

Section Category.

  Definition syntactic_category : category.
  Admitted.

End Category.

Section Split_Typecat.

  Definition syntactic_typecat : split_typecat.
  Admitted.

End Split_Typecat.
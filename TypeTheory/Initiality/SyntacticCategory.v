(** This file defines the syntactic category of our toy type theory, and the logical structure on it. *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.All.

Require Import TypeTheory.Auxiliary.Partial.
Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.Initiality.SplitTypeCat_Maps.
Require Import TypeTheory.Initiality.SplitTypeCat_Structure.
Require Import TypeTheory.Initiality.Syntax.
Require Import TypeTheory.Initiality.Typing.

Section Types_and_Terms.
  
  Definition ty (Γ : context) : UU
    := ∑ (A : ty_expr Γ), ∥ derivation [! Γ |- A !] ∥.

  Coercion ty_expr_of_ty {Γ} (A : ty Γ) : ty_expr Γ := pr1 A.

  (* todo: [tm]! *)
End Types_and_Terms.

Section Typed_Contexts.
(** Here we define (well-typed) contexts, in the usual sense. *)
(* TODO: perhaps rename [context] upstream to e.g. [raw_context] or [flat_context], so these can just be [context]? *)

(* TODO: we could reasonably disentangle the “well-typed” aspect, in the sense of all the types being derivable types, and the “stratified” aspect. This shouldn’t be essential, but might make things clearer. *)

  Fixpoint typed_context_aux (n:nat)
    : ∑ (X : Type), X -> context_of_length n.
  Proof.
    destruct n as [ | n].
    - exists unit. (* unique empty context *)
      intros _; exact empty_context.
    - set (cxt_n := pr1 (typed_context_aux n)).
      set (realise := pr2 (typed_context_aux n) : cxt_n -> _).
      exists (∑ (Γ : cxt_n), ty (realise Γ)).
      intros Γ_A.
      exact (context_extend (realise (pr1 Γ_A)) (pr2 Γ_A)).
  Defined.

  Definition typed_context_of_length (n:nat)
  := pr1 (typed_context_aux n).

  Definition realise_typed_context {n}
    : typed_context_of_length n -> context_of_length n
  := pr2 (typed_context_aux n).

  Coercion realise_typed_context
    : typed_context_of_length >-> context_of_length.

  Definition typed_context : UU
  := ∑ (n:nat), typed_context_of_length n.

  Definition typed_context_length : typed_context -> nat := pr1.
  Coercion typed_context_length : typed_context >-> nat.

  Definition typed_context_types : forall Γ : typed_context, _ := pr2.
  Coercion typed_context_types : typed_context >-> typed_context_of_length.

  Definition make_typed_context {n}
    : typed_context_of_length n -> typed_context
  := fun Γ => (n,,Γ).
  Coercion make_typed_context : typed_context_of_length >-> typed_context.
 
  (* TODO: lemma: any well-typed context is indeed derivably a context. *)
End Typed_Contexts.

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
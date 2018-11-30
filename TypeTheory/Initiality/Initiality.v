Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.All.



Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.Initiality.SplitTypeCat_Structure.
Require Import TypeTheory.Initiality.SplitTypeCat_Maps.
Require Import TypeTheory.Initiality.SyntacticCategory.
Require Import TypeTheory.Initiality.Interpretation.
 
Section Existence.

  Context (C : split_typecat)
          (U : universe_struct C)
          (Π : pi_struct C).

  Definition interpretation_map
    : typecat_mor syntactic_typecat C.
  Proof.
  (* should be able to put this together component-by-component,
     as the corresponding components of the snytactic typecat are
     defined, using the total interpretation. *) 
  Admitted.

  (* TODO: add lemmas that it preserves [U] and [Π] *)
End Existence.

Section Uniqueness.

  Context {C : split_typecat}
          {U : universe_struct C}
          {Π : pi_struct C}.

  Definition interpretation_unique
      (f : typecat_mor syntactic_typecat C)
      (* TODO: and hypotheses that [f] preserves [U] and [Π] *)
    : f = interpretation_map C U Π.
  Proof.
  (* this should come from a couple of lemmas, to be proven not here but
  upstream in [Interpretation], or perhaps a separate file
  [interpretation_2] or something:

  - the partial interpretation function is _natural_: given a typecat
    map [ f : C -> C' ] and a piece of syntax, then [f] applied to its
    interpretation in [C] is ≤ its its interpretation in [D].  This should
    be a single induction on raw syntax.

  - the total interpretation function into the symtactic category is the
    same as the canonical quotient inclusion.  This should be a single
    induction over derivations.

  Then here, we can put these together to show that [f] is equal to the
  interpretation map into [C].
  *) 
  Admitted.

End Uniqueness.
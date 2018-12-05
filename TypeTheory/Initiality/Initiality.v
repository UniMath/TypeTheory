Require Import UniMath.MoreFoundations.All.
Require Import UniMath.MoreFoundations.Propositions.
(* [MoreFoundations.Propositions] seems to need individual importing
to provide notation [∃!] as [iscontr_hProp] instead of just [iscontr]. *)
(* TODO: figure out why; perhaps raise issue upstream? *)
Require Import UniMath.CategoryTheory.All.


Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.Initiality.SplitTypeCat_Structure.
Require Import TypeTheory.Initiality.SplitTypeCat_Maps.
Require Import TypeTheory.Initiality.SyntacticCategory.
Require Import TypeTheory.Initiality.Interpretation.

Section Extensions.
(** Context extensions in type-categories, i.e. suitable sequences of types *)
(* TODO: upstream somewhere! And connect to [CSystems] files? *)

  Fixpoint
      extension_aux {C : typecat} (Γ:C) (n:nat) {struct n}
    : ∑ E : UU, E -> C.
  Proof.
    destruct n as [ | n'].
    - exists unit. intros e; exact Γ.
    - set (E_R := extension_aux C Γ n'). 
      exists (∑ (E : pr1 E_R), C (pr2 E_R E)).
      intros AA_B. exact (ext_typecat _ (pr2 AA_B)).
  Defined.

  Definition extension_of_length {C:typecat} (n:nat) (Γ:C) : UU
    := pr1 (extension_aux Γ n).
  Arguments extension_of_length : simpl nomatch.

  Definition ext_extension {C:typecat} {n:nat} (Γ:C)
      (AA : extension_of_length n Γ)
    : C
  := pr2 (extension_aux Γ n) AA.
  Arguments ext_extension : simpl nomatch.

  Definition extension_rest {C:typecat} {n:nat} {Γ:C}
      (AA : extension_of_length (S n) Γ)
    : extension_of_length n Γ
  := pr1 AA.

  Definition extension_last {C:typecat} {n:nat} {Γ:C}
      (AA : extension_of_length (S n) Γ)
    : C (ext_extension Γ (extension_rest AA))
  := pr2 AA.

  Definition extension_extend {C : typecat} {n} {Γ:C}
      (AA : extension_of_length n Γ)
      (B : C (ext_extension Γ AA))
    : extension_of_length (S n) Γ
  := (AA,,B).

  Fixpoint dpr_extension {C:typecat} {n:nat} {Γ:C}
      (AA : extension_of_length n Γ) {struct n}
    : (ext_extension Γ AA) --> Γ.
  Proof.
    destruct n as [ | n'].
    - use identity.
    - exact (dpr_typecat (extension_last AA)
            ;; dpr_extension _ _ _ (extension_rest AA)).
  Defined.

  Definition extension {C:typecat} (Γ:C) : UU
  := ∑ n:nat, extension_of_length n Γ.

  Definition extension_length {C:typecat} {Γ:C}
  : extension Γ -> nat := pr1.

  Definition extension_pr2 {C:typecat} {Γ:C} (AA : extension Γ)
    : extension_of_length (extension_length AA) Γ
  := pr2 AA.
  Coercion extension_pr2 : extension >-> extension_of_length.

  Definition make_extension {C:typecat} {Γ:C} {n}
    : extension_of_length n Γ -> extension Γ
  := fun AA => (n,,AA).
  Coercion make_extension : extension_of_length >-> extension.

End Extensions.

Section Contextual_Cats.
(** A split type-categoy is _contextual_ if it has some base object, such that every object arises uniquely as an extension of this base object. 

Note that such a base object is necessarily unique: see [isaprop_is_contextual]. *)
(* TODO: is the base object automatically terminal? If not, add hypothesis that it is. *)

  Definition is_contextual (C : split_typecat)
  := ∑ Γ0 : C,
       isTerminal C Γ0
       ×
       ∀ Γ:C, ∃! AA : extension Γ0, ext_extension Γ0 AA = Γ.

  Definition empty_contextual {C} (H : is_contextual C) : C
  := pr1 H.

  Lemma isaprop_is_contextual {C : split_typecat}
    : isaprop (is_contextual C).
  Proof.
    apply invproofirrelevance; intros H H'.
    apply subtypeEquality.
    { intros Γ0; apply isapropdirprod.
    - admit. (* couldn’t find in library for either [isTerminal]
                or [limits.terminal.isTerminal]. *)
    - apply propproperty. }
    destruct H as [Γ0 [K H]], H' as [Γ0' [K' H']]; cbn; clear K K'.
    destruct (H Γ0') as [[AA e] _], (H' Γ0) as [[AA' e'] _].
    admit.
    (* sketch:
    - define concatenation of extensions
    - conclude [ext_extension Γ0 (AA+AA') = Γ0] 
    - by uniqueness part of [H Γ0], conclude [AA+AA' = extension_empty]
    - conclude [AA = extension_empty]
    - conclude [Γ0' = Γ0]. *)
  Admitted. (* [isaprop_is_contextual]: low-priority, since probably not
             actually needed, just included to justify un-truncated def of
             [is_contextual]. *)

  Definition contextual_cat : UU
    := ∑ C : split_typecat, is_contextual C.

  Coercion pr1_contextual_cat := pr1 : contextual_cat -> split_typecat.
  Coercion pr2_contextual_cat := pr2 
    : forall C : contextual_cat, is_contextual C.

End Contextual_Cats.

Section Existence.

  Context (C : contextual_cat)
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

  Context {C : contextual_cat}
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

  - functoriality of the partial interpretation under typecat maps:
    [fmap_partial_interpretation_ty] and […tm] in [InterpretationLemmas].

  - the total interpretation function into the syntactic category is the
    same as the canonical quotient inclusion.  This should be a single
    induction over derivations.

  Then here, we can put these together to show that [f] is equal to the
  interpretation map into [C].
  *) 
  Admitted.

End Uniqueness.

(** This file provides a definition (and basic development) of contextual categories as split type-cats/CwA’s in which every object is uniquely expressible as an iterated extension of a chosen terminal object. *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.MoreFoundations.Propositions.
(* [MoreFoundations.Propositions] seems to need individual importing
to provide notation [∃!] as [iscontr_hProp] instead of just [iscontr]. *)
(* TODO: figure out why; perhaps raise issue upstream? *)
Require Import UniMath.CategoryTheory.All.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.Partial.
Require Import TypeTheory.ALV1.TypeCat.

(* These two lemmas should be upstreamed to UniMath/CategoryTheory/limits/terminal.v and initial.v *)
Section upstream.

  Lemma isaprop_isTerminal {C : precategory} (x : C) : isaprop (isTerminal C x).
  Proof.
    repeat (apply impred; intro).
    apply isapropiscontr.
  Qed.

  Lemma isaprop_isInitial {C : precategory} (x : C) : isaprop (isInitial C x).
  Proof.
    repeat (apply impred; intro).
    apply isapropiscontr.
  Qed.
    
End upstream.


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

  Definition ext_extension_of_length {C:typecat} {n:nat} (Γ:C)
      (AA : extension_of_length n Γ)
    : C
  := pr2 (extension_aux Γ n) AA.
  Arguments ext_extension_of_length : simpl nomatch.

  Definition extension_rest {C:typecat} {n:nat} {Γ:C}
      (AA : extension_of_length (S n) Γ)
    : extension_of_length n Γ
  := pr1 AA.

  Definition extension_last {C:typecat} {n:nat} {Γ:C}
      (AA : extension_of_length (S n) Γ)
    : C (ext_extension_of_length Γ (extension_rest AA))
  := pr2 AA.

  Definition extension_extend {C : typecat} {n} {Γ:C}
      (AA : extension_of_length n Γ)
      (B : C (ext_extension_of_length Γ AA))
    : extension_of_length (S n) Γ
  := (AA,,B).

  Definition extension {C:typecat} (Γ:C) : UU
  := ∑ n:nat, extension_of_length n Γ.

  Definition extension_length {C:typecat} {Γ:C}
  : extension Γ -> nat := pr1.

  Definition extension_pr2 {C:typecat} {Γ:C} (AA : extension Γ)
    : extension_of_length (extension_length AA) Γ
  := pr2 AA.
  Coercion extension_pr2 : extension >-> extension_of_length.

  Definition make_extension {C:typecat} {n} {Γ:C}
    : extension_of_length n Γ -> extension Γ
  := fun AA => (n,,AA).
  Coercion make_extension : extension_of_length >-> extension.

  Definition ext_extension {C:typecat}
      (Γ:C) (AA : extension Γ)
    : C
  := ext_extension_of_length Γ AA. 
  Arguments ext_extension : simpl nomatch.

  Fixpoint dpr_extension {C:typecat} {n:nat} {Γ:C}
      (AA : extension_of_length n Γ) {struct n}
    : (ext_extension Γ AA) --> Γ.
  Proof.
    destruct n as [ | n'].
    - use identity.
    - exact (dpr_typecat (extension_last AA)
            ;; dpr_extension _ _ _ (extension_rest AA)).
  Defined.

  Lemma isaset_extension_of_length {C:split_typecat} (n:nat) (Γ:C)
    : isaset (extension_of_length n Γ).
  Proof.
    induction n as [ | n' IH].
    - apply isasetunit.
    - apply isaset_total2; try apply IH.
      intros; apply isaset_types_typecat.
  Qed.

  Lemma isaset_extension {C:split_typecat} (Γ:C)
    : isaset (extension Γ).
  Proof.
    apply isaset_total2.
    - apply isasetnat.
    - intros; apply isaset_extension_of_length.
  Qed.

End Extensions.

Section Contextual_Cats.
(** A split type-category is _contextual_ if it has some base object, such that every object arises uniquely as an extension of this base object. 

Note that such a base object is necessarily unique: see [isaprop_is_contextual]. *)

  Definition is_contextual (C : split_typecat)
  := ∑ Γ0 : C,
       isTerminal C Γ0
       ×
       ∀ Γ:C, ∃! AA : extension Γ0, ext_extension Γ0 AA = Γ.
  (** The second component could be written as
  [isweq (ext_extension Γ0)], but we spell it out for readability. *)

  Definition empty_contextual {C} (H : is_contextual C) : C
  := pr1 H.

  Definition isTerminal_empty_contextual {C} {H : is_contextual C}
    : isTerminal C (empty_contextual H)
  := pr1 (pr2 H).

  Definition unique_extension_contextual {C} {H : is_contextual C} (Γ : C)
    : ∃! AA : extension (empty_contextual H),
              ext_extension (empty_contextual H) AA = Γ
  := pr2 (pr2 H) Γ.

  Definition isweq_ext_extension_empty_contextual {C} (H : is_contextual C)
    : isweq (ext_extension (empty_contextual H))
  := pr2 (pr2 H).

  Lemma isaprop_is_contextual {C : split_typecat}
    : isaprop (is_contextual C).
  Proof.
    apply invproofirrelevance; intros H H'.
    apply subtypePath.
    { intros Γ0; apply isapropdirprod.
      - apply isaprop_isTerminal.
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

  Lemma isaset_ob_contextual_cat {C : contextual_cat}
    : isaset (ob C).
  Proof.
    refine (isofhlevelweqf 2 _ _).
    - exists (ext_extension (empty_contextual C)).
      apply isweq_ext_extension_empty_contextual.
    - apply isaset_extension.
  Qed.

End Contextual_Cats.
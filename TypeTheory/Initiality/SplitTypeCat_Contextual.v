
(** This file provides a definition (and basic development) of contextual categories as split type-cats/CwA’s in which every object is uniquely expressible as an iterated extension of a chosen terminal object. *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.All.
Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheory.
Require Import TypeTheory.Auxiliary.Partial.
Require Import TypeTheory.ALV1.TypeCat.

Require Import TypeTheory.Initiality.SplitTypeCat_General.

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

  (* To define concatenation of extensions, we also need to mutually define some comparison between the extension by the concatenation (Γ + (AA + BB)) and the two-stage extension ((Γ + AA) + BB).
     
   This comparison could be given as an equality; however we avoid taking that as primary, to minimise use of equality on objects, and instead give it just as the morphism required, and show afterwards that it’s an equality. *)
  Definition concat_extension_aux {C : typecat} {Γ:C}
    {n} (AA : extension_of_length n Γ)
    {m} (BB : extension_of_length m (ext_extension Γ AA))
  : ∑ (AABB : extension_of_length (m+n) Γ),
      ext_extension Γ AABB --> ext_extension _ BB. 
  Proof.
    induction m as [ | m' IH]; simpl.
    - (* m = 0, BB empty *)
      exists AA. apply identity.
    - (* m = S m', BB = BB';;B *)
      set (B := extension_last BB); set (BB' := extension_rest BB) in *.
      set (AABB'_f := IH BB'); set (AABB' := pr1 AABB'_f).
      simple refine (_,,_).
      + refine (extension_extend AABB' _).
        refine (B {{ pr2 AABB'_f }}).
      + apply q_typecat.
        (* more verbose/explanatory version:
        cbn. change BB with (extension_extend BB' B).
        unfold extension_extend, ext_extension, ext_extension_of_length; cbn.
        apply q_typecat.
        *)
  Defined.

  Definition concat_extension {C : typecat} {Γ:C}
      {n} (AA : extension_of_length n Γ)
      {m} (BB : extension_of_length m (ext_extension Γ AA))
    : extension_of_length (m+n) Γ
  := pr1 (concat_extension_aux AA BB).
  
  Definition compare_concat_extension {C : typecat} {Γ:C}
      {n} (AA : extension_of_length n Γ)
      {m} (BB : extension_of_length m (ext_extension Γ AA))
    : ext_extension Γ (concat_extension AA BB)
      --> ext_extension (ext_extension Γ AA) BB 
  := pr2 (concat_extension_aux AA BB).

  Definition path_ext_typecat {C : split_typecat}
      {Γ Γ' : C} (e_Γ : Γ = Γ')
      {A : C Γ} {A' : C Γ'} (e_A : A = A' {{ idtoiso e_Γ }})
    : ext_typecat Γ A = ext_typecat Γ' A'.
  Proof.
    destruct e_Γ. apply maponpaths.
    etrans. { apply e_A. }
    apply reind_id_typecat.
  Defined.

  Definition idtoiso_path_ext_typecat {C : split_typecat}
      {Γ Γ' : C} (e_Γ : Γ = Γ')
      {A : C Γ} {A' : C Γ'} (e_A : A = A' {{ idtoiso e_Γ }})
    : (idtoiso (path_ext_typecat e_Γ e_A) : _ --> _)
      = comp_ext_compare e_A ;; q_typecat A' (idtoiso e_Γ).
  Proof.
    destruct e_Γ; cbn in *.
    etrans. { apply maponpaths, maponpaths, maponpathscomp0. }
    etrans. { apply idtoiso_concat_pr. }
    apply maponpaths.
    apply pathsinv0, q_id_typecat.
  Defined.

  Definition ext_concat_extension_aux {C : split_typecat} {Γ:C}
    {n} (AA : extension_of_length n Γ)
    {m} (BB : extension_of_length m (ext_extension Γ AA))
  : ∑ (e : ext_extension Γ (concat_extension AA BB) = (ext_extension _ BB)),
    compare_concat_extension AA BB = idtoiso e.
  Proof.
    induction m as [ | m' IH]; simpl.
    - (* m = 0, BB empty *)
      use tpair; apply idpath. 
    - (* m = S m', BB = BB';;B *)
      set (B := extension_last BB); set (BB' := extension_rest BB) in *.
      destruct (IH BB') as [e1 e2]; clear IH.
      unfold ext_extension, ext_extension_of_length; simpl.
      use tpair. 
      + use path_ext_typecat.
        * exact e1.
        * apply maponpaths, e2.
      + simpl. apply pathsinv0.
        etrans. { apply idtoiso_path_ext_typecat. }
        unfold compare_concat_extension. simpl pr2.
        apply q_typecat_mapeq.
  Defined.

  Definition ext_concat_extension {C : split_typecat} {Γ:C}
      {n} (AA : extension_of_length n Γ)
      {m} (BB : extension_of_length m (ext_extension Γ AA))
    : ext_extension Γ (concat_extension AA BB) = (ext_extension _ BB).
  Proof.
    exact (pr1 (ext_concat_extension_aux AA BB)).
  Defined.  

End Extensions.

Section Contextual_Cats.
(** A split type-category is _contextual_ if it has some base object, such that every object arises uniquely as an extension of this base object. 

Note that such a base object is necessarily unique: see [isaprop_is_contextual]. *)

  Definition is_contextual (C : split_typecat)
  := ∑ Γ0 : C,
       isTerminal C Γ0
       ×
       ∀ Γ:C, (∃! AA : extension Γ0, (ext_extension Γ0 AA = Γ)%type)%logic.
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
    (* First part: note it suffices to show the two “contextual structures” have the same “empty context”, since the rest of the data is obviously propositional. *)
    apply invproofirrelevance; intros H H'.
    apply subtypePath.
    { intros Γ0; apply isapropdirprod.
      - apply isaprop_isTerminal.
      - apply propproperty. }
    destruct H as [Γ0 [K H]], H' as [Γ0' [K' H']]; cbn; clear K K'.
    destruct (H Γ0') as [[AA e] _], (H' Γ0) as [[AA' e'] _].
    (* Second part: notice that
    [ Γ0 = Γ0' ◂◂ AA' = (Γ0 ◂◂ AA) ◂◂ AA' = Γ0 ◂◂ (AA + AA') ]
    and so by uniqueness [ AA + AA' ] is empty, so [AA] is empty and Γ0' = Γ0. *)
    destruct e.
    assert (p : ext_extension Γ0 (concat_extension AA AA') = Γ0).
    { etrans. { apply ext_concat_extension. } exact e'. }
    assert (exts_trivial : (concat_extension AA AA' : extension Γ0) = (0,,tt)).
    { simple refine (maponpaths pr1 (_ : (_,,_) = (_,,_))).
      - exact (fun BB => ext_extension Γ0 BB = Γ0).
      - exact p.
      - apply idpath.
      - apply isapropifcontr, (H Γ0).
    }
    apply (maponpaths pr1) in exts_trivial; cbn in exts_trivial.
    destruct AA as [n AA].
    apply plusmn0n0, pathsinv0 in exts_trivial; cbn in exts_trivial.
    destruct exts_trivial.
    apply idpath.
  Defined.

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

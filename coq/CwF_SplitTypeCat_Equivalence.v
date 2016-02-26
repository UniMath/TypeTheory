
(**

 Ahrens, Lumsdaine, Voevodsky, 2015 - 2016

*)

Require Export Systems.Auxiliary.
Require Export Systems.UnicodeNotations.
Require Export UniMath.Foundations.Basics.Sets.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.more_on_pullbacks.
Require Export UniMath.CategoryTheory.UnicodeNotations.
Require Export UniMath.CategoryTheory.functor_categories.
Require Export UniMath.CategoryTheory.opp_precat.
Require Export UniMath.CategoryTheory.category_hset.
Require Export UniMath.CategoryTheory.yoneda.
Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).
Local Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op").

Local Definition preShv C := [C^op , HSET , pr2 is_category_HSET].

Section fix_a_category.

Variable C : precategory.
Variable hsC : has_homsets C.

Local Definition yy {F : preShv C} {c : C} : ((F : functor _ _) c : hSet) ≃ _ ⟦ yoneda _ hsC c, F⟧.
Proof.
  apply invweq.
  apply yoneda_weq.
Defined.

(** * Type of type structures *)

Definition type_structure : UU :=
  Σ Ty : preShv C,
        ∀ (Γ : C) (A : (Ty : functor _ _ ) Γ : hSet ), Σ (ΓA : C), C⟦ΓA, Γ⟧.

Definition TY (X : type_structure) : preShv _ := pr1 X.

Definition comp_ext {X : type_structure} Γ A : C := pr1 (pr2 X Γ A).
Notation "Γ ◂ A" := (comp_ext Γ A) (at level 30).
Definition π {X : type_structure} {Γ} A : C ⟦Γ ◂ A, Γ⟧ := pr2 (pr2 X _ A).

(** * Type of families structures over a type structure *)

Section some_structures.

Context {X : type_structure}.

Definition families_data_structure : UU :=
  Σ Tm : preShv C, _ ⟦ Tm, TY X ⟧ × (∀ Γ (A : (TY X : functor _ _ ) Γ : hSet), _ ⟦ yoneda _ hsC (Γ ◂ A) , Tm⟧ ).

Definition TM (Y : families_data_structure) : preShv C := pr1 Y.
Definition pp Y : _ ⟦TM Y, TY X⟧ := pr1 (pr2 Y).
Definition Q Y {Γ} A : _ ⟦ _ , TM Y⟧ := pr2 (pr2 Y) Γ A.

Definition families_prop_structure (Y : families_data_structure) :=
  ∀ Γ (A : (TY X : functor _ _ ) Γ : hSet), 
        Σ (e : Q Y A ;; pp Y = #(yoneda _ hsC) (π A) ;; yy A), isPullback _ _ _ _ e.

Definition families_structure : UU :=
  Σ Y : families_data_structure, families_prop_structure Y.
Coercion families_data_from_families (Y : families_structure) : _ := pr1 Y.


(** * Type of split comprehension structures over a types structure *)

Notation "A [ f ]" := (# (TY X : functor _ _ ) f A) (at level 4).

Definition comprehension_structure : UU :=
  Σ q : ∀ {Γ Γ'} (f : C⟦Γ', Γ⟧) (A : (TY X:functor _ _ ) Γ : hSet), 
           C ⟦Γ' ◂ A [ f ], Γ ◂ A⟧, 
    (∀ Γ Γ' (f : C⟦Γ', Γ⟧) (A : (TY X:functor _ _ ) Γ : hSet), 
        Σ e : q f A ;; π _ = π _ ;; f, isPullback _ _ _ _ e).

Definition qq (Y : comprehension_structure) {Γ Γ'} (f : C ⟦Γ', Γ⟧)
              (A : (TY X:functor _ _ ) Γ : hSet) 
  : C ⟦Γ' ◂ A [ f ], Γ ◂ A⟧
  := pr1 Y _ _ f A.

Definition is_split_comprehension_structure (Y : comprehension_structure) : UU
  := 
    (∀ Γ A, qq Y (identity Γ) A = idtoiso (maponpaths (fun B => Γ ◂ B) 
                                                      (toforallpaths _ _ _ (functor_id (TY X) _ ) _ )) )
 ×
   (∀ Γ Γ' Γ'' (f : C⟦Γ', Γ⟧) (g : C ⟦Γ'', Γ'⟧) (A : (TY X:functor _ _ ) Γ : hSet),
       qq Y (g ;; f) A = idtoiso (maponpaths (fun B => Γ'' ◂ B)
                                             (toforallpaths _ _ _ (functor_comp (TY X) _ _ _  f g) A))
                          ;; qq Y g (A [f]) 
                          ;; qq Y f A).

Definition compatible_scomp_families (Y : families_structure)(Z : comprehension_structure) : UU
  := ∀ Γ Γ' A (f : C⟦Γ', Γ⟧) , Q Y A[f] = #(yoneda _ hsC) (qq Z f A) ;; Q Y A.

Definition compatible_fam_structure (Z : comprehension_structure) : UU
  := Σ Y : families_structure, compatible_scomp_families Y Z.

Definition compatible_comp_structure (Y : families_structure) : UU
  := Σ Z : comprehension_structure, compatible_scomp_families Y Z.



Section compatible_comp_structure_from_fam.

Variable Y : families_structure.

(*
Definition qq_fam :   
*)

End compatible_comp_structure_from_fam.

(* needs splitness? *)
Lemma iscontr_compatible_fam_structure (Z : comprehension_structure)
: iscontr (compatible_fam_structure Z).
Proof.
Abort.




Lemma iscontr_compatible_comp_structure (Y : families_structure)
: iscontr (compatible_comp_structure Y).
Proof.
Abort.



End some_structures.


End fix_a_category.
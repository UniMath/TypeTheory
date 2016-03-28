(**

 Ahrens, Lumsdaine, Voevodsky, 2015 - 2016

*)

Require Export UniMath.Foundations.Basics.Sets.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.more_on_pullbacks.
Require Export UniMath.CategoryTheory.UnicodeNotations.
Require Export UniMath.CategoryTheory.functor_categories.
Require Export UniMath.CategoryTheory.opp_precat.
Require Export UniMath.CategoryTheory.category_hset.
Require Export UniMath.CategoryTheory.yoneda.

Require Export Systems.Auxiliary.
Require Export Systems.UnicodeNotations.


Section fix_a_category.

Context {C : precategory} {hsC : has_homsets C}.

Local Notation "'Yo'" := (yoneda C hsC).
Local Notation "'Yo^-1'" :=  (invweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ ))).

Definition yy {F : preShv C} {c : C} : ((F : functor _ _) c : hSet) ≃ _ ⟦ Yo c, F⟧.
Proof.
  apply invweq.
  apply yoneda_weq.
Defined.

Lemma yy_natural (F : preShv C) (c : C) (A : (F:functor _ _) c : hSet) 
                  c' (f : C⟦c', c⟧) :
        yy (# (F : functor _ _) f A) = # Yo f ;; yy A.
Proof.
  assert (XTT := is_natural_yoneda_iso_inv _ hsC F _ _ f).
  apply (toforallpaths _ _ _ XTT).
Qed.

(** * Type of type structures *)

Definition type_structure : UU :=
  Σ Ty : preShv C,
        ∀ (Γ : C) (A : (Ty : functor _ _ ) Γ : hSet ), Σ (ΓA : C), C⟦ΓA, Γ⟧.

Definition TY (X : type_structure) : preShv _ := pr1 X.

Definition comp_ext {X : type_structure} Γ A : C := pr1 (pr2 X Γ A).
Notation "Γ ◂ A" := (comp_ext Γ A) (at level 30).
Definition π {X : type_structure} {Γ} A : C ⟦Γ ◂ A, Γ⟧ := pr2 (pr2 X _ A).

Lemma idtoiso_π {X : type_structure} (Γ : C) (A A' : (TY X : functor _ _ ) Γ : hSet) (e : A = A')
  :
    idtoiso (maponpaths (λ B, Γ ◂ B) e) ;; π _ = π _ .
Proof.
  induction e.
  apply id_left.
Qed.

(** * Type of families structures over a type structure *)

Section some_structures.

Context {X : type_structure}.

(* Notation "A [ f ]" := (# (TY X : functor C^op HSET) f A)(at level 30). *)

Definition families_data_structure : UU :=
  Σ Tm : preShv C, _ ⟦ Tm, TY X ⟧ × (∀ Γ (A : (TY X : functor _ _ ) Γ : hSet), _ ⟦Yo (Γ ◂ A) , Tm⟧ ).

Definition TM (Y : families_data_structure) : preShv C := pr1 Y.
Definition pp Y : _ ⟦TM Y, TY X⟧ := pr1 (pr2 Y).
Definition Q Y {Γ} A : _ ⟦ _ , TM Y⟧ := pr2 (pr2 Y) Γ A.

Lemma idtoiso_Q Y Γ (A A' : (TY X : functor _ _ ) Γ : hSet) (e : A = A') : 
  #Yo (idtoiso (maponpaths (fun B => Γ ◂ B) e )) ;; Q Y A' = Q Y A . 
Proof.
  induction e. 
  etrans. apply cancel_postcomposition. apply functor_id.
  apply id_left.
Defined.

Definition families_prop_structure (Y : families_data_structure) :=
  ∀ Γ (A : (TY X : functor _ _ ) Γ : hSet), 
        Σ (e : #Yo (π A) ;; yy A = Q Y A ;; pp Y), isPullback _ _ _ _ e.

Lemma isaprop_families_prop_structure Y
  : isaprop (families_prop_structure Y).
Proof.
  do 2 (apply impred; intro).
  apply isofhleveltotal2.
  - apply functor_category_has_homsets.
  - intro. apply isaprop_isPullback.
Qed.

Definition families_structure : UU :=
  Σ Y : families_data_structure, families_prop_structure Y.
Coercion families_data_from_families (Y : families_structure) : _ := pr1 Y.

Definition Q_pp (Y : families_structure) Γ (A : (TY X : functor _ _ ) Γ : hSet) 
  : #Yo (π A) ;; yy A = Q Y A ;; pp Y.
Proof.
  apply (pr1 (pr2 Y _ _ )).
Defined.

Definition isPullback_Q_pp (Y : families_structure) Γ (A : (TY X : functor _ _ ) Γ : hSet) 
  : isPullback _ _ _ _ (Q_pp Y _ A ). 
Proof.
  apply (pr2 (pr2 Y _ _ )).
Defined.

(** * Type of split comprehension structures over a types structure *)

Notation "A [ f ]" := (# (TY X : functor _ _ ) f A) (at level 4).

Definition comprehension_structure : UU :=
  Σ q : ∀ {Γ Γ'} (f : C⟦Γ', Γ⟧) (A : (TY X:functor _ _ ) Γ : hSet), 
           C ⟦Γ' ◂ A [ f ], Γ ◂ A⟧, 
    (∀ Γ Γ' (f : C⟦Γ', Γ⟧) (A : (TY X:functor _ _ ) Γ : hSet), 
        Σ e :  π _ ;; f = q f A ;; π _ , isPullback _ _ _ _ e).

Definition qq (Y : comprehension_structure) {Γ Γ'} (f : C ⟦Γ', Γ⟧)
              (A : (TY X:functor _ _ ) Γ : hSet) 
  : C ⟦Γ' ◂ A [ f ], Γ ◂ A⟧
  := pr1 Y _ _ f A.

(* Access function *)
Lemma qq_π (Y : comprehension_structure) {Γ Γ'} (f : Γ' ⇒ Γ) (A : _ ) : π _ ;; f = qq Y f A ;; π A.
Proof.
  exact (pr1 (pr2 Y _ _ f A)).
Qed.

(* Access function *)
Lemma qq_π_Pb (Y : comprehension_structure) {Γ Γ'} (f : Γ' ⇒ Γ) (A : _ ) : isPullback _ _ _ _ (qq_π Y f A).
Proof.
  exact (pr2 (pr2 Y _ _ f A)).
Qed.

Definition idtoiso_qq (Y : comprehension_structure) {Γ Γ'} (f f' : C ⟦Γ', Γ⟧)
              (e : f = f')
              (A : (TY X:functor _ _ ) Γ : hSet) 
  : idtoiso (maponpaths (comp_ext Γ') (maponpaths (λ k : C⟦Γ', Γ⟧, A [k]) e))
                ;; qq Y f' A = qq Y f A.
Proof.
  induction e.
  apply id_left.
Qed.

Definition pullback_from_comp (Y : comprehension_structure) 
  {Γ Γ'} (f : C⟦Γ', Γ⟧) (A : (TY X:functor _ _ ) Γ : hSet) : 
        Σ e : π _ ;; f = qq Y f A ;; π _ , isPullback _ _ _ _ e
:= pr2 Y _ _ f A.

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

Lemma isaprop_is_split_comprehension_structure
  (Y : comprehension_structure)
  : isaprop (is_split_comprehension_structure Y).
Proof.
  apply isofhleveldirprod.
  - do 2 (apply impred; intro).
    apply hsC.
  - do 6 (apply impred; intro).
    apply hsC.    
Qed.


(* Since [Ty X] is always an hset, the splitness properties hold with any equality replacing the canonical ones. This is sometimes handy, one may want to opacify the canonical equalities in later proofs. *)
Lemma split_comprehension_structure_comp_general
  {Y : comprehension_structure} (Z : is_split_comprehension_structure Y)
  {Γ Γ' Γ'' : C}
  {f : C ⟦ Γ', Γ ⟧} {g : C ⟦ Γ'', Γ' ⟧} {A : ((TY X : functor _ _) Γ : hSet)}
  (p : A [g ;; f]
       = # (TY X : functor C^op HSET) g (# (TY X : functor C^op HSET) f A)) 
: qq Y (g ;; f) A
  = idtoiso
         (maponpaths (λ B : ((pr1 X : functor _ _) Γ'' : hSet), Γ'' ◂ B)
            p) ;; 
       qq Y g (A [f]) ;; qq Y f A.
Proof.
  eapply pathscomp0. apply (pr2 Z).
  repeat apply (maponpaths (fun h => h ;; _)).
  repeat apply maponpaths. apply uip. exact (pr2 ((TY X : functor _ _) _)).
Qed.


Definition split_comprehension_structure : UU
  := Σ Z : comprehension_structure,
           is_split_comprehension_structure Z.

Definition comprehension_from_split_comprehension :
   split_comprehension_structure -> comprehension_structure := pr1.
Coercion comprehension_from_split_comprehension :
   split_comprehension_structure >-> comprehension_structure.

End some_structures.

End fix_a_category.

Arguments type_structure _ : clear implicits.
Arguments families_data_structure [_] _ _ : clear implicits.
Arguments families_prop_structure [_] _ _ _ : clear implicits.
Arguments families_structure [_] _ _ : clear implicits.
Arguments comprehension_structure [_] _ : clear implicits.
Arguments split_comprehension_structure [_] _ : clear implicits.

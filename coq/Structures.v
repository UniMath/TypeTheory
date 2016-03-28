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

Section Fix_Base_Category.

Context {C : precategory} {hsC : has_homsets C}.

Local Notation "'Yo'" := (yoneda _ hsC).
Local Notation "'Yo^-1'" :=  (invweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ ))).

(** * Object-extension structures 

We start by fixing the common core of families structures and split type-category structures: an _object-extension structure_, a presheaf together with “extension” and “dependent projection” operations.

Components:

- [TY Γ : hSet]
- [comp_ext X Γ A : C].  Notation: [Γ ◂ A]
- [π A : Γ ◂ A ⇒  A ⟧ *)

Definition obj_ext_structure : UU
  := Σ Ty : preShv C,
        ∀ (Γ : C) (A : (Ty : functor _ _ ) Γ : hSet ), Σ (ΓA : C), ΓA ⇒ Γ.

Definition TY (X : obj_ext_structure) : preShv _ := pr1 X.

Definition comp_ext (X : obj_ext_structure) Γ A : C := pr1 (pr2 X Γ A).
Notation "Γ ◂ A" := (comp_ext _ Γ A) (at level 30).

Definition π {X : obj_ext_structure} {Γ} A : Γ ◂ A ⇒ Γ := pr2 (pr2 X _ A).

Lemma idtoiso_π {X : obj_ext_structure} (Γ : C) (A A' : (TY X : functor _ _ ) Γ : hSet) (e : A = A')
  :
    idtoiso (maponpaths (λ B, Γ ◂ B) e) ;; π _ = π _ .
Proof.
  induction e.
  apply id_left.
Qed.

(** The definitions of families structures and split type structures will all be relative to a fixed object-extension structure. *)

Section Fix_Obj_Ext_Structure.

Context {X : obj_ext_structure}.

(** * Families structures 

We now define the extra structure, over an object-extension structure, which constitutes a _category with families_ in the sense of Dybjer, as reformulated by Fiore. 

Components of [Y : families_structure X]:

- [TM Y : preShv C] 
- [pp Y : TM Y ⇒ TY X]
- [Q Y A :  Yo (Γ ◂ A) ⇒ TM Y]
- [Q_pp Y A : #Yo (π A) ;; yy A = Q Y A ;; pp Y]
- [isPullback_Q_pp Y A : isPullback _ _ _ _ (Q_pp Y A)]
*)

Definition families_structure_data : UU
  := Σ Tm : preShv C, 
        (Tm ⇒ TY X)
        × (∀ Γ (A : (TY X : functor _ _ ) Γ : hSet), Yo (Γ ◂ A) ⇒ Tm).

Definition TM (Y : families_structure_data) : preShv C := pr1 Y.
Definition pp Y : TM Y ⇒ TY X := pr1 (pr2 Y).
Definition Q Y {Γ} A : _ ⇒ TM Y := pr2 (pr2 Y) Γ A.

Lemma idtoiso_Q Y Γ (A A' : (TY X : functor _ _ ) Γ : hSet) (e : A = A') : 
  #Yo (idtoiso (maponpaths (fun B => Γ ◂ B) e )) ;; Q Y A' = Q Y A . 
Proof.
  induction e. 
  etrans. apply cancel_postcomposition. apply functor_id.
  apply id_left.
Defined.

Definition families_structure_axioms (Y : families_structure_data) :=
  ∀ Γ (A : (TY X : functor _ _ ) Γ : hSet), 
        Σ (e : #Yo (π A) ;; yy A = Q Y A ;; pp Y), isPullback _ _ _ _ e.

Lemma isaprop_families_structure_axioms Y
  : isaprop (families_structure_axioms Y).
Proof.
  do 2 (apply impred; intro).
  apply isofhleveltotal2.
  - apply functor_category_has_homsets.
  - intro. apply isaprop_isPullback.
Qed.

Definition families_structure : UU :=
  Σ Y : families_structure_data, families_structure_axioms Y.
Coercion families_data_from_families (Y : families_structure) : _ := pr1 Y.

Definition Q_pp (Y : families_structure) {Γ} (A : (TY X : functor _ _ ) Γ : hSet) 
  : #Yo (π A) ;; yy A = Q Y A ;; pp Y
:= pr1 (pr2 Y _ _ ).

Definition isPullback_Q_pp (Y : families_structure) {Γ} (A : (TY X : functor _ _ ) Γ : hSet)
  : isPullback _ _ _ _ (Q_pp Y A)
:= pr2 (pr2 Y _ _ ).

(** * Split type structures 

On the other hand, _cartesian q-structure_ (over an object-extension structure) is what is required to constitute a _split type-category_.

These are essentially the _type-categories_ of Andy Pitts, _Categorical Logic_, 2000, Def. 6.3.3
#(<a href="https://synrc.com/publications/cat/Category%%20Theory/Categorical%%20Logic/Pitts%%20A.M.%%20Categorical%%20Logic.pdf##page=73">link</a>).#

Our terminology follows van den Berg and Garner, _Topological and simplicial models_, Def 2.2.1 #(<a href="http://arxiv.org/abs/1007.4638">arXiv</a>)# 
in calling this notion a _split_ type-category, and reserving _type-category_ (unqualified) for the weaker version without hSet/splitness assumptions.  We formalise non-split type-categories elsewhere, since they do not extend object-extension structures.

Components of [Z : qq_morphism_structure X]:

- [qq Z f A : Γ' ◂ A[f] ⇒ Γ ◂ A]
- [qq_π Y f A : π _ ;; f = qq Y f A ;; π A]
- [qq_π_Pb Y f A : isPullback _ _ _ _ (qq_π Y f A)]
- [qq_id], [qq_comp]: functoriality for [qq] (not currently given)
*)

Local Notation "A [ f ]" := (# (TY X : functor _ _ ) f A) (at level 4).

Definition qq_morphism_data : UU :=
  Σ q : ∀ {Γ Γ'} (f : C⟦Γ', Γ⟧) (A : (TY X:functor _ _ ) Γ : hSet), 
           C ⟦Γ' ◂ A [ f ], Γ ◂ A⟧, 
    (∀ Γ Γ' (f : C⟦Γ', Γ⟧) (A : (TY X:functor _ _ ) Γ : hSet), 
        Σ e :  π _ ;; f = q f A ;; π _ , isPullback _ _ _ _ e).

Definition qq (Y : qq_morphism_data) {Γ Γ'} (f : C ⟦Γ', Γ⟧)
              (A : (TY X:functor _ _ ) Γ : hSet) 
  : C ⟦Γ' ◂ A [ f ], Γ ◂ A⟧
:= pr1 Y _ _ f A.

(* TODO: consider changing the direction of this equality? *)
Lemma qq_π (Y : qq_morphism_data) {Γ Γ'} (f : Γ' ⇒ Γ) (A : _ ) : π _ ;; f = qq Y f A ;; π A.
Proof.
  exact (pr1 (pr2 Y _ _ f A)).
Qed.

Lemma qq_π_Pb (Y : qq_morphism_data) {Γ Γ'} (f : Γ' ⇒ Γ) (A : _ ) : isPullback _ _ _ _ (qq_π Y f A).
Proof.
  exact (pr2 (pr2 Y _ _ f A)).
Qed.

Lemma idtoiso_qq (Y : qq_morphism_data) {Γ Γ'} (f f' : C ⟦Γ', Γ⟧)
              (e : f = f')
              (A : (TY X:functor _ _ ) Γ : hSet) 
  : idtoiso (maponpaths (comp_ext _ Γ') (maponpaths (λ k : C⟦Γ', Γ⟧, A [k]) e))
                ;; qq Y f' A
  = qq Y f A.
Proof.
  induction e.
  apply id_left.
Qed.

Definition pullback_from_comp (Y : qq_morphism_data) 
  {Γ Γ'} (f : C⟦Γ', Γ⟧) (A : (TY X:functor _ _ ) Γ : hSet) : 
        Σ e : π _ ;; f = qq Y f A ;; π _ , isPullback _ _ _ _ e
:= pr2 Y _ _ f A.

Definition qq_morphism_axioms (Y : qq_morphism_data) : UU
  := 
    (∀ Γ A,
    qq Y (identity Γ) A
    = idtoiso (maponpaths (fun B => Γ ◂ B) 
                  (toforallpaths _ _ _ (functor_id (TY X) _ ) _ )) )
  ×
    (∀ Γ Γ' Γ'' (f : C⟦Γ', Γ⟧) (g : C ⟦Γ'', Γ'⟧) (A : (TY X:functor _ _ ) Γ : hSet),
    qq Y (g ;; f) A
    = idtoiso (maponpaths (fun B => Γ'' ◂ B)
                (toforallpaths _ _ _ (functor_comp (TY X) _ _ _  f g) A))
      ;; qq Y g (A [f]) 
      ;; qq Y f A).

Lemma isaprop_qq_morphism_axioms
  (Y : qq_morphism_data)
  : isaprop (qq_morphism_axioms Y).
Proof.
  apply isofhleveldirprod.
  - do 2 (apply impred; intro).
    apply hsC.
  - do 6 (apply impred; intro).
    apply hsC.    
Qed.

(* Since [Ty X] is always an hset, the splitness properties hold with any path in place of the canonical ones. This is sometimes handy, as one may want to opacify the canonical equalities in examples. *)
Lemma qq_morphism_structure_comp_general
  {Y : qq_morphism_data} (Z : qq_morphism_axioms Y)
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


Definition qq_morphism_structure : UU
  := Σ Z : qq_morphism_data,
           qq_morphism_axioms Z.

Definition qq_morphism_data_from_axioms :
   qq_morphism_structure -> qq_morphism_data := pr1.
Coercion qq_morphism_data_from_axioms :
   qq_morphism_structure >-> qq_morphism_data.

End Fix_Obj_Ext_Structure.

End Fix_Base_Category.

Arguments obj_ext_structure _ : clear implicits.
Arguments families_structure_data [_] _ _ : clear implicits.
Arguments families_structure_axioms [_] _ _ _ : clear implicits.
Arguments families_structure [_] _ _ : clear implicits.
Arguments qq_morphism_data [_] _ : clear implicits.
Arguments qq_morphism_structure [_] _ : clear implicits.

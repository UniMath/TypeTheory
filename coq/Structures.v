(**

 Ahrens, Lumsdaine, Voevodsky, 2015 - 2016

Key definitions:

- _object-extension structures_, [obj_ext_structure], the common core of CwF’s and split type-categories;
- _families structures_, [families_structure], for building CwF’s;
- _q-morphism structures_, [qq_morphism_structure], for building split type-categories

*)

Require Export UniMath.Foundations.Basics.Sets.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Export UniMath.CategoryTheory.UnicodeNotations.
Require Export UniMath.CategoryTheory.functor_categories.
Require Export UniMath.CategoryTheory.opp_precat.
Require Export UniMath.CategoryTheory.category_hset.
Require Export UniMath.CategoryTheory.yoneda.

Require Export Systems.Auxiliary.
Require Export Systems.UnicodeNotations.

Set Automatic Introduction.

Section Fix_Base_Category.

Context {C : precategory} {hsC : has_homsets C}.

Local Notation "'Yo'" := (yoneda _ hsC).
Local Notation "'Yo^-1'" :=  (invweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ ))).

(** * Object-extension structures 

We start by fixing the common core of families structures and split type-category structures: an _object-extension structure_, a presheaf together with “extension” and “dependent projection” operations.

Components of [X : obj_ext_structure C]:

- [TY Γ : hSet]
- [comp_ext X Γ A : C].  Notation: [Γ ◂ A]
- [π A : Γ ◂ A -->  A ⟧ *)
Section Obj_Ext_Structures.

Definition obj_ext_structure : UU
  := Σ Ty : preShv C,
        Π (Γ : C) (A : (Ty : functor _ _ ) Γ : hSet ), Σ (ΓA : C), ΓA --> Γ.

Definition TY (X : obj_ext_structure) : preShv _ := pr1 X.
Local Notation "'Ty'" := (fun X Γ => (TY X : functor _ _) Γ : hSet) (at level 10).

Definition comp_ext (X : obj_ext_structure) Γ A : C := pr1 (pr2 X Γ A).
Local Notation "Γ ◂ A" := (comp_ext _ Γ A) (at level 30).

Definition π {X : obj_ext_structure} {Γ} A : Γ ◂ A --> Γ := pr2 (pr2 X _ A).

(** ** Extensions by equal types *)

(* One frequently needs to deal with isomorphisms between context extensions [Γ ◂ A ≃ Γ ◂ A'] induced by type equalities [e : A = A']; so we collect lemmas for them, and notate them as [Δ e]. *)

Section Comp_Ext_Compare.

Definition comp_ext_compare {X : obj_ext_structure}
    {Γ : C} {A A' : Ty X Γ} (e : A = A')
  : Γ ◂ A --> Γ ◂ A'
:= idtoiso (maponpaths (comp_ext X Γ) e).

Lemma comp_ext_compare_id {X : obj_ext_structure}
    {Γ : C} (A : Ty X Γ)
  : comp_ext_compare (idpath A) = identity (Γ ◂ A).
Proof.
  apply idpath.
Qed.

Lemma comp_ext_compare_id_general {X : obj_ext_structure}
    {Γ : C} {A : Ty X Γ} (e : A = A)
  : comp_ext_compare e = identity (Γ ◂ A).
Proof.
  apply @pathscomp0 with (comp_ext_compare (idpath _)).
  apply maponpaths, setproperty.
  apply idpath.
Qed.

Lemma comp_ext_compare_comp {X : obj_ext_structure}
    {Γ : C} {A A' A'' : Ty X Γ} (e : A = A') (e' : A' = A'')
  : comp_ext_compare (e @ e') = comp_ext_compare e ;; comp_ext_compare e'.
Proof.
  apply pathsinv0.
  etrans. apply idtoiso_concat_pr. 
  unfold comp_ext_compare. apply maponpaths, maponpaths.
  apply pathsinv0, maponpathscomp0. 
Qed.

Lemma comp_ext_compare_π {X : obj_ext_structure}
    {Γ : C} {A A' : Ty X Γ} (e : A = A')
  : comp_ext_compare e ;; π A' = π A.
Proof.
  destruct e; cbn. apply id_left.
Qed.

Lemma comp_ext_compare_comp_general {X : obj_ext_structure}
    {Γ : C} {A A' A'' : Ty X Γ} (e : A = A') (e' : A' = A'') (e'' : A = A'')
  : comp_ext_compare e'' = comp_ext_compare e ;; comp_ext_compare e'.
Proof.
  refine (_ @ comp_ext_compare_comp _ _).
  apply maponpaths, setproperty.
Qed.

End Comp_Ext_Compare.

End Obj_Ext_Structures.

Local Notation "Γ ◂ A" := (comp_ext _ Γ A) (at level 30).
Local Notation "'Ty'" := (fun X Γ => (TY X : functor _ _) Γ : hSet) (at level 10).

(** The definitions of families structures and split type-category structures will all be relative to a fixed object-extension structure. *)

Section Fix_Obj_Ext_Structure.

Context {X : obj_ext_structure}.

(** * Families structures 

We now define the extra structure, over an object-extension structure, which constitutes a _category with families_ in the sense of Dybjer, as reformulated by Fiore. 

Components of [Y : families_structure X]:

- [TM Y : preShv C] 
- [pp Y : TM Y --> TY X]
- [Q Y A :  Yo (Γ ◂ A) --> TM Y]
- [Q_pp Y A : #Yo (π A) ;; yy A = Q Y A ;; pp Y]
- [isPullback_Q_pp Y A : isPullback _ _ _ _ (Q_pp Y A)]
*)

Definition families_structure_data : UU
  := Σ Tm : preShv C, 
        (Tm --> TY X)
        × (Π Γ (A : Ty X Γ), Yo (Γ ◂ A) --> Tm).

Definition TM (Y : families_structure_data) : preShv C := pr1 Y.
Definition pp Y : TM Y --> TY X := pr1 (pr2 Y).
Definition Q Y {Γ} A : _ --> TM Y := pr2 (pr2 Y) Γ A.
Local Notation "'Tm'" := (fun Y Γ => (TM Y : functor _ _) Γ : hSet) (at level 10).

Lemma comp_ext_compare_Q Y Γ (A A' : Ty X Γ) (e : A = A') : 
  #Yo (comp_ext_compare e) ;; Q Y A' = Q Y A . 
Proof.
  induction e. 
  etrans. apply cancel_postcomposition. apply functor_id.
  apply id_left.
Qed.

Definition families_structure_axioms (Y : families_structure_data) :=
  Π Γ (A : Ty X Γ), 
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

Definition Q_pp (Y : families_structure) {Γ} (A : Ty X Γ) 
  : #Yo (π A) ;; yy A = Q Y A ;; pp Y
:= pr1 (pr2 Y _ _ ).

(* TODO: rename this to [Q_pp_Pb], or [qq_π_Pb] to [isPullback_qq_π]? *)
Definition isPullback_Q_pp (Y : families_structure) {Γ} (A : Ty X Γ)
  : isPullback _ _ _ _ (Q_pp Y A)
:= pr2 (pr2 Y _ _ ).

Definition Q_pp_Pb_pointwise (Y : families_structure) (Γ' Γ : C) (A : Ty X Γ)
  := isPullback_preShv_to_pointwise hsC (isPullback_Q_pp Y A) Γ'.

Definition Q_pp_Pb_univprop (Y : families_structure) (Γ' Γ : C) (A : Ty X Γ)
  := pullback_HSET_univprop_elements _ (Q_pp_Pb_pointwise Y Γ' Γ A).

Definition Q_pp_Pb_unique (Y : families_structure) (Γ' Γ : C) (A : Ty X Γ)
  := pullback_HSET_elements_unique (Q_pp_Pb_pointwise Y Γ' Γ A).

(** ** Terms as sections *)

(* In any families structure, “terms” correspond to sections of dependent projections.  For now, we do not need this full isomorphism, but we construct the beginning of the correspondence. *)
  
Lemma term_to_section_aux {Y : families_structure} {Γ:C} (t : Tm Y Γ) 
  (A := (pp Y : nat_trans _ _) _ t)
  : iscontr
    (Σ (f : Γ --> Γ ◂ A), 
         f ;; π _ = identity Γ
       × (Q Y A : nat_trans _ _) Γ f = t).
Proof.
  set (Pb := isPullback_preShv_to_pointwise hsC (isPullback_Q_pp Y A) Γ).
  simpl in Pb.
  apply (pullback_HSET_univprop_elements _ Pb).
  exact (toforallpaths _ _ _ (functor_id (TY X) _) A).
Qed.

(* TODO: unify with [bar] in […_Equivalence]? *)
Lemma term_to_section {Y : families_structure} {Γ:C} (t : Tm Y Γ) 
  (A := (pp Y : nat_trans _ _) _ t)
  : Σ (f : Γ --> Γ ◂ A), (f ;; π _ = identity Γ).
Proof.
  set (sectionplus := iscontrpr1 (term_to_section_aux t)).
  exists (pr1 sectionplus).
  exact (pr1 (pr2 sectionplus)).
Defined.

(* TODO: again, unify with lemmas following [bar] in […_Equivalence]? *)
Lemma term_to_section_recover {Y : families_structure}
  {Γ:C} (t : Tm Y Γ) (A := (pp Y : nat_trans _ _) _ t)
  : (Q Y A : nat_trans _ _) _ (pr1 (term_to_section t)) = t.
Proof.
  exact (pr2 (pr2 (iscontrpr1 (term_to_section_aux t)))).
Qed.

Lemma Q_comp_ext_compare {Y : families_structure}
    {Γ Γ':C} {A A' : Ty X Γ} (e : A = A') (t : Γ' --> Γ ◂ A)
  : (Q Y A' : nat_trans _ _) _ (t ;; comp_ext_compare e)
  = (Q Y A : nat_trans _ _) _ t.
Proof.
  destruct e. apply maponpaths, id_right.
Qed.

(** * Cartesian _q_-morphism structures, split type-categories

On the other hand, _(cartesian) q-morphism structure_ (over an object-extension structure) is what is required to constitute a _split type-category_.

These are essentially the _type-categories_ of Andy Pitts, _Categorical Logic_, 2000, Def. 6.3.3
#(<a href="https://synrc.com/publications/cat/Category%%20Theory/Categorical%%20Logic/Pitts%%20A.M.%%20Categorical%%20Logic.pdf##page=73">link</a>).#

Our terminology follows van den Berg and Garner, _Topological and simplicial models_, Def 2.2.1 #(<a href="http://arxiv.org/abs/1007.4638">arXiv</a>)# 
in calling this notion a _split_ type-category, and reserving _type-category_ (unqualified) for the weaker version without hSet/splitness assumptions.  We formalise non-split type-categories elsewhere, since they do not extend object-extension structures.

Components of [Z : qq_morphism_structure X]:

- [qq Z f A : Γ' ◂ A[f] --> Γ ◂ A]
- [qq_π Z f A : π _ ;; f = qq Y f A ;; π A]
- [qq_π_Pb Z f A : isPullback _ _ _ _ (qq_π Y f A)]
- [qq_id], [qq_comp]: functoriality for [qq]
*)

Local Notation "A [ f ]" := (# (TY X : functor _ _ ) f A) (at level 4).

Definition qq_morphism_data : UU :=
  Σ q : Π {Γ Γ'} (f : C⟦Γ', Γ⟧) (A : (TY X:functor _ _ ) Γ : hSet), 
           C ⟦Γ' ◂ A [ f ], Γ ◂ A⟧, 
    (Π Γ Γ' (f : C⟦Γ', Γ⟧) (A : (TY X:functor _ _ ) Γ : hSet), 
        Σ e :  π _ ;; f = q f A ;; π _ , isPullback _ _ _ _ e).

Definition qq (Y : qq_morphism_data) {Γ Γ'} (f : C ⟦Γ', Γ⟧)
              (A : (TY X:functor _ _ ) Γ : hSet) 
  : C ⟦Γ' ◂ A [ f ], Γ ◂ A⟧
:= pr1 Y _ _ f A.

(* TODO: consider changing the direction of this equality? *)
Lemma qq_π (Y : qq_morphism_data) {Γ Γ'} (f : Γ' --> Γ) (A : _ ) : π _ ;; f = qq Y f A ;; π A.
Proof.
  exact (pr1 (pr2 Y _ _ f A)).
Qed.

Lemma qq_π_Pb (Y : qq_morphism_data) {Γ Γ'} (f : Γ' --> Γ) (A : _ ) : isPullback _ _ _ _ (qq_π Y f A).
Proof.
  exact (pr2 (pr2 Y _ _ f A)).
Qed.

Lemma comp_ext_compare_qq (Y : qq_morphism_data)
  {Γ Γ'} {f f' : C ⟦Γ', Γ⟧} (e : f = f') (A : Ty X Γ) 
  : comp_ext_compare (maponpaths (λ k : C⟦Γ', Γ⟧, A [k]) e) ;; qq Y f' A
  = qq Y f A.
Proof.
  induction e.
  apply id_left.
Qed.

Definition qq_morphism_axioms (Y : qq_morphism_data) : UU
  := 
    (Π Γ A,
    qq Y (identity Γ) A
    = comp_ext_compare (toforallpaths _ _ _ (functor_id (TY X) _ ) _ ))
  ×
    (Π Γ Γ' Γ'' (f : C⟦Γ', Γ⟧) (g : C ⟦Γ'', Γ'⟧) (A : (TY X:functor _ _ ) Γ : hSet),
    qq Y (g ;; f) A
    = comp_ext_compare
           (toforallpaths _ _ _ (functor_comp (TY X) _ _ _ _ _) A)
      ;; qq Y g (A [f]) 
      ;; qq Y f A).

Definition qq_morphism_structure : UU
  := Σ Z : qq_morphism_data,
           qq_morphism_axioms Z.

Definition qq_morphism_data_from_structure :
   qq_morphism_structure -> qq_morphism_data := pr1.
Coercion qq_morphism_data_from_structure :
   qq_morphism_structure >-> qq_morphism_data.

Definition qq_id (Z : qq_morphism_structure)
    {Γ} (A : Ty X Γ)
  : qq Z (identity Γ) A
  = comp_ext_compare (toforallpaths _ _ _ (functor_id (TY X) _ ) _ )
:= pr1 (pr2 Z) _ _.

Definition qq_comp (Z : qq_morphism_structure)
    {Γ Γ' Γ'' : C}
    (f : C ⟦ Γ', Γ ⟧) (g : C ⟦ Γ'', Γ' ⟧) (A : Ty X Γ)
  : qq Z (g ;; f) A
  = comp_ext_compare (toforallpaths _ _ _ (functor_comp (TY X) _ _ _ _ _) A)
    ;; qq Z g (A [f]) ;; qq Z f A
:= pr2 (pr2 Z) _ _ _ _ _ _.

Lemma isaprop_qq_morphism_axioms (Z : qq_morphism_data)
  : isaprop (qq_morphism_axioms Z).
Proof.
  apply isofhleveldirprod.
  - do 2 (apply impred; intro).
    apply hsC.
  - do 6 (apply impred; intro).
    apply hsC.    
Qed.

(* Since [Ty X] is always an hset, the splitness properties hold with any path in place of the canonical ones. This is sometimes handy, as one may want to opacify the canonical equalities in examples. *)
Lemma qq_comp_general (Z : qq_morphism_structure)
  {Γ Γ' Γ'' : C}
  {f : C ⟦ Γ', Γ ⟧} {g : C ⟦ Γ'', Γ' ⟧} {A : Ty X Γ}
  (p : A [g ;; f]
       = # (TY X : functor _ _) g (# (TY X : functor _ _) f A)) 
: qq Z (g ;; f) A
  = comp_ext_compare p ;; qq Z g (A [f]) ;; qq Z f A.
Proof.
  eapply pathscomp0. apply qq_comp.
  repeat apply (maponpaths (fun h => h ;; _)).
  repeat apply maponpaths. apply uip. apply setproperty.
Qed.

End Fix_Obj_Ext_Structure.

End Fix_Base_Category.

Arguments obj_ext_structure _ : clear implicits.
Arguments families_structure_data [_] _ _ : clear implicits.
Arguments families_structure_axioms [_] _ _ _ : clear implicits.
Arguments families_structure [_] _ _ : clear implicits.
Arguments qq_morphism_data [_] _ : clear implicits.
Arguments qq_morphism_structure [_] _ : clear implicits.

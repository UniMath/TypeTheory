(**
Content :
- Unit and Universe Type on CwF
**)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.All.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.

Require Import TypeTheory.ALV1.CwF_def.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Defs.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Maps.
Require Import TypeTheory.ALV1.TypeCat.

Require Import TypeTheory.Initiality.SplitTypeCat_General.
Require Import TypeTheory.Articles.ALV_2017.

Section CwF.
Context (CwF : cwf).
Definition C : category := pr1(CwF).
Definition pp : mor_total(preShv(C)) := pr1(pr2(CwF)).
Definition Ty : functor _ _ := target pp.
Definition Tm : functor _ _ := source pp.

(* extension of context *)
Definition ext {Γ : C} (A : Ty Γ : hSet) : C := pr1(pr1(pr2(pr2(CwF)) Γ A)).
Notation "Γ.: A" :=  (ext A) (at level 24).

Definition pi {Γ :C} (A : Ty Γ : hSet) : C⟦Γ.:A,Γ⟧ := pr2 (pr1 (pr2 (pr2 CwF) _ A)).


(* just a simple to use pp as a nat_trans *)
Definition Nat_trans_morp {C : category} (Γ : C) (p : mor_total(preShv C)) :=
  (pr1(pr2(p)) Γ).
Notation "p __: Γ" := (Nat_trans_morp Γ p)  (at level 24).
Definition pp_ (Γ :C)  : ((Tm Γ : hSet) → (Ty Γ : hSet)) := pp __: Γ.


Definition CwF_tm {Γ : C} (A : Ty Γ : hSet) : UU
:= ∑ (a : Tm Γ : hSet), pp_ _ a = A.
Definition CwF_pr1_tm {Γ : C} {A : Ty Γ : hSet} (a : CwF_tm A) :  (Tm Γ : hSet) := pr1 a.
Coercion CwF_pr1_tm : CwF_tm >-> pr1hSet.

Definition reind_cwf
  {Γ : C} (A : Ty Γ : hSet) {Γ'} (f : C⟦Γ',Γ⟧)
  : Ty Γ' : hSet
  := #Ty f A.
Notation "A ⟪ f ⟫" := (reind_cwf A f) (at level 30).
Definition te {Γ :C} (A : Ty Γ : hSet) : CwF_tm (#Ty (pi A) A) :=
  pr1(pr2((pr2(pr2(CwF)) _ A))).

Definition CwF_tm_transportf {Γ} {A A' : Ty Γ : hSet} (e : A = A')
    : CwF_tm A ≃ CwF_tm A'.
  Proof.
    use weqbandf.
    exact (idweq (Tm Γ : hSet)).
    simpl. induction e. intro x. exact (idweq _).
  Defined.

Lemma ppComp1 {Γ Δ : C} {A : Ty Γ : hSet} (f : C^op ⟦Γ,Δ⟧) (a : CwF_tm A) :
  pp_ _ (# Tm f a ) = # Ty f A. 
Proof.
  apply pathsinv0, (pathscomp0(pathsinv0(maponpaths (# Ty f) (pr2(a))))),
  pathsinv0, (toforallpaths _ _ _ ((pr2(pr2(pp))) _ _ f) a) .
Qed. 
  
Definition CwF_Pullback {Γ} (A : Ty Γ : hSet) : isPullback (yy A) pp (#Yo (pi A)) (yy(te A)) _ := pr22 pr22  CwF Γ A.

Definition CwF_reind_tm {Γ Δ} (f : C^op ⟦Γ,Δ⟧) {A : Ty Γ : hSet} (x : CwF_tm A)
 : CwF_tm (A⟪f⟫) := (#Tm f x,,ppComp1 f x).

Lemma CwF_isaset_tm {Γ : C} (A : Ty Γ : hSet) : isaset (CwF_tm A).
Proof.
  apply isaset_total2.
  - apply (setproperty (Tm Γ : hSet)).
  - intro a; apply isasetaprop, (setproperty (Ty Γ : hSet)). 
Qed.

Lemma Subproof_γ {Γ : C} {A : Ty Γ : hSet} (a : CwF_tm A) :
  (identity (Yo Γ)) ;; yy A = (yy a ;;pp).
Proof.
  apply pathsinv0, (pathscomp0(yy_comp_nat_trans Tm Ty pp Γ (a))) ,pathsinv0,
  (pathscomp0(@id_left _  (Yo Γ) Ty  (yy(A)))) ,
  ((maponpaths(yy)) (pathsinv0(pr2(a)))).
Qed.

Definition γ {Γ : C} {A : Ty Γ : hSet} (a : CwF_tm A) : (preShv C)⟦Yo Γ,Yo (Γ.:A)⟧ :=
  pr11((CwF_Pullback A) (Yo Γ) (identity _) (yy a) (Subproof_γ a)).

Definition DepTypesType {Γ : C} {A : Ty Γ : hSet} (B : Ty(Γ.:A) : hSet)
  (a : CwF_tm A): (Ty Γ :hSet) :=
    ( γ a;;yy B : nat_trans _ _) Γ (identity Γ).

(** Unit Types *)
Section Unit.

Definition CwF_unit_TypeFormer : UU := ∏ (Γ : C), Ty Γ : hSet.

Definition CwF_unit_Elem (U : CwF_unit_TypeFormer) : UU := ∏  (Γ :C), CwF_tm (U Γ).

Definition CwF_unit_unity (U : CwF_unit_TypeFormer) (E : CwF_unit_Elem U) : UU :=
  ∏ (Γ : C) (b : CwF_tm (U Γ)), (E Γ) = b.

Lemma CwF_isaprop_unity (U : CwF_unit_TypeFormer) (E : CwF_unit_Elem U) :
  isaprop (CwF_unit_unity U E).
Proof.
  unfold CwF_unit_unity.
  do 2 (apply impred_isaprop; intro).
  apply CwF_isaset_tm.
Qed.

Definition CwF_unit_structure := ∑ (U : CwF_unit_TypeFormer) (E : CwF_unit_Elem U), CwF_unit_unity U E.

End Unit.

(** Universe Types*)
Section Universe.
Definition CwF_basetype_struct : UU
  :=  ∑ U : (∏ Γ, Ty Γ : hSet),
        ∏ Γ Δ (f: C⟦Δ,Γ⟧), (U Γ) ⟪f⟫ = U Δ.

Definition CwF_basetype_struct_pr1 : CwF_basetype_struct -> ∏ Γ, (Ty Γ : hSet) := pr1.
Coercion CwF_basetype_struct_pr1 : CwF_basetype_struct >-> Funclass.
  
Definition CwF_basetype_natural {U : CwF_basetype_struct} {Γ Γ'} (f : C⟦Γ',Γ⟧)
    :  U Γ ⟪f⟫ = U Γ'
  := pr2 U _ _ f.

Definition CwF_deptype_struct (U : CwF_basetype_struct) : UU.
  Proof.
    use (∑ (D : ∏ Γ (a : CwF_tm (U Γ)), Ty Γ : hSet), _).
    use (∏ Δ Γ (f : C ⟦ Δ, Γ ⟧) (a : CwF_tm (U Γ)), _).
    refine ((D Γ a) ⟪f⟫ = D Δ _).
    exact (CwF_tm_transportf (CwF_basetype_natural f) (CwF_reind_tm f a)).
  Defined.

  Definition CwF_deptype_struct_pr1 {U} (El : CwF_deptype_struct U) := pr1 El.
  Coercion CwF_deptype_struct_pr1 : CwF_deptype_struct >-> Funclass.

  Definition CwF_deptype_struct_natural {U} (El : CwF_deptype_struct U) := pr2 El.

  Definition CwF_universe_struct
  := ∑ (U : CwF_basetype_struct), CwF_deptype_struct U.

  Coercion CwF_universe (U : CwF_universe_struct) : CwF_basetype_struct := pr1 U.

  Definition CwF_universe_natural (U : CwF_universe_struct) := @CwF_basetype_natural U.

  Definition CwF_elements {U : CwF_universe_struct} : CwF_deptype_struct U := pr2 U.

  Definition CwF_elements_natural {U : CwF_universe_struct}
    := CwF_deptype_struct_natural (@CwF_elements U).
End Universe.

End CwF.
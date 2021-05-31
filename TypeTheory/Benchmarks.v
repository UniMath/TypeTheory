Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.All.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.

Require Import TypeTheory.ALV1.CwF_def.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Defs.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Maps.
Require Import TypeTheory.ALV1.TypeCat.

Require Import TypeTheory.Initiality.SplitTypeCat_General.
Require Import TypeTheory.Initiality.SplitTypeCat_Structure.
Require Import TypeTheory.Articles.ALV_2017.

Section CwF.
Context (CwF : cwf).
Local Definition C : category := pr1 CwF.
Local Definition pp : mor_total(preShv(C)) := pr12 CwF.
Local Definition Ty : functor _ _ := target pp.
Local Definition Tm : functor _ _ := source pp.

(* extension of context *)
Local Definition ext {Γ : C} (A : Ty Γ : hSet) : C := pr11(pr22 CwF Γ A).
Local Notation "Γ.: A" :=  (ext A) (at level 24).

Definition pi {Γ :C} (A : Ty Γ : hSet) : C⟦Γ.:A,Γ⟧ := pr21 (pr22 CwF _ A).

(* just a simple to use pp as a nat_trans *)
Local Definition Nat_trans_morp {C : category} (Γ : C) (p : mor_total(preShv C)) 
:= pr12 p Γ.
Notation "p __: Γ" := (Nat_trans_morp Γ p)  (at level 24).
Local Definition pp_ (Γ : C)  : (Tm Γ : hSet) → (Ty Γ : hSet) := pp __: Γ.


Definition CwF_tm {Γ : C} (A : Ty Γ : hSet) : UU
:= ∑ a : Tm Γ : hSet, pp_ _ a = A.
Definition CwF_pr1_tm {Γ : C} {A : Ty Γ : hSet} (a : CwF_tm A) : Tm Γ : hSet 
:= pr1 a.
Coercion CwF_pr1_tm : CwF_tm >-> pr1hSet.

Definition reind_cwf {Γ : C} (A : Ty Γ : hSet) {Γ'} (f : C⟦Γ',Γ⟧) : Ty Γ' : hSet
:= #Ty f A.
Notation "A ⟪ f ⟫" := (reind_cwf A f) (at level 30).
Local Definition te {Γ : C} (A : Ty Γ : hSet) : CwF_tm (#Ty (pi A) A) 
:= pr12(pr22 CwF _ A).

Definition CwF_tm_transportf {Γ} {A A' : Ty Γ : hSet} (e : A = A') 
: CwF_tm A ≃ CwF_tm A'.
Proof.
  use weqbandf.
  exact (idweq (Tm Γ : hSet)).
  simpl. induction e. intro x. exact (idweq _).
Defined.

Lemma ppComp1 {Γ Δ : C} {A : Ty Γ : hSet} (f : C^op ⟦Γ,Δ⟧) (a : CwF_tm A) 
: pp_ _ (# Tm f a ) = # Ty f A. 
Proof.
  apply pathsinv0, (pathscomp0(!(maponpaths (# Ty f) (pr2 a)))),
  pathsinv0, (toforallpaths _ _ _ (pr22 pp _ _ f) a) .
Qed. 
  
Definition CwF_Pullback {Γ} (A : Ty Γ : hSet) 
: isPullback (yy A) pp (#Yo (pi A)) (yy(te A)) _ := pr22 pr22  CwF Γ A.

Definition CwF_reind_tm {Γ Δ} (f : C^op ⟦Γ,Δ⟧) {A : Ty Γ : hSet} (x : CwF_tm A)
: CwF_tm (A⟪f⟫) := (#Tm f x,,ppComp1 f x).

Lemma CwF_isaset_tm {Γ : C} (A : Ty Γ : hSet) : isaset (CwF_tm A).
Proof.
  apply isaset_total2.
  -  apply (setproperty (Tm Γ : hSet)).
  -  intro a; apply isasetaprop, (setproperty (Ty Γ : hSet)). 
Qed.

Lemma Subproof_γ {Γ : C} {A : Ty Γ : hSet} (a : CwF_tm A) 
: (identity (Yo Γ)) ;; yy A = (yy a ;;pp).
Proof.
  apply pathsinv0, (pathscomp0(yy_comp_nat_trans Tm Ty pp Γ a)) ,pathsinv0,
  (pathscomp0(@id_left _  (Yo Γ) Ty  (yy A))) ,
  (maponpaths yy (!(pr2 a))).
Qed.

Definition γ {Γ : C} {A : Ty Γ : hSet} (a : CwF_tm A) : (preShv C)⟦Yo Γ,Yo (Γ.:A)⟧
:= pr11( (CwF_Pullback A) (Yo Γ) (identity _) (yy a) (Subproof_γ a)).

Definition DepTypesType {Γ : C} {A : Ty Γ : hSet} (B : Ty(Γ.:A) : hSet) (a : CwF_tm A)
: Ty Γ : hSet :=  (γ a;;yy B : nat_trans _ _)  Γ (identity Γ).

(** Basic Def of qq, lemma on it in the types_structure_over_cwf_branch*)
Local Definition te' {Γ : C} (A : Ty Γ : hSet) 
: pp_ _ (te A) = #Ty (pi A) A := pr212 pr22 CwF Γ A.
Let Xk {Γ : C} (A : Ty Γ : hSet) :=
  make_Pullback _ _ _ _ _ _ (pr22 pr22 CwF Γ A).

Definition qq_yoneda {Γ  Δ : C} (A : Ty Γ : hSet) (f : C^op ⟦Γ,Δ⟧)
: (preShv C) ⟦Yo (Γ.:(#Ty f A)), Yo (Γ.: A) ⟧.
Proof.
  use (PullbackArrow (Xk A)).
  -  apply (#Yo (pi _) ;; #Yo f ). 
  -  apply (yy (te _)).
  -  abstract (
        clear Xk;
        assert (XT := (cwf_square_comm (te' (#Ty f A) )));
        eapply pathscomp0; try apply XT; clear XT;
        rewrite <- assoc; apply maponpaths;
        apply pathsinv0, yy_natural
     ).
Defined.
Definition CwF_qq_term {Γ  Δ : C} (A : Ty Γ : hSet) (f : C^op ⟦Γ,Δ⟧)
: C ⟦ Γ.:(#Ty f A) , Γ.: A⟧.
Proof.
  apply (invweq (make_weq _ (yoneda_fully_faithful _ (homset_property _) _ _ ))) ,
  (qq_yoneda A f).
Defined.

End CwF.

Section Stc_Benchmarks.
Context (C : category) (Split : split_typecat_structure C).

Local Definition Sc : split_typecat := (C,,pr1 Split),,pr2 Split.
Local Definition Sc' : split_typecat' := C,,weq_standalone_to_regrouped C Split.
Local Definition X : obj_ext_structure C 
:= obj_ext_structure_of_split_typecat'_structure Sc'.
Local Definition T : term_fun_structure C X := pr2(invweq (weq_cwf'_sty' C) Sc').
Local Definition CWF : cwf := C,,weq_sty_cwf _ Split.

Lemma Type_equiv (Γ : C) : (Sc Γ) ≃ (Ty CWF Γ : hSet).
Proof.
exact (idweq _).
Qed.

Lemma Type_equiv' (Γ : C) : (Ty CWF Γ : hSet) ≃ (Sc Γ ).
Proof.
exact (idweq _).
Qed.

Lemma ext_eq_part1 (Γ : C) (A : Sc Γ) : (Γ ◂ A) = (comp_ext X Γ A).
Proof.
reflexivity.
Qed.

Lemma ext_eq_part2 (Γ : C) (A : Sc Γ) : (ext CWF A) = (comp_ext X Γ A).
Proof.
Admitted.

Lemma ext_eq (Γ : C) (A : Sc Γ) : (Γ ◂ A) = (ext CWF A).
Proof.
unfold ext.
unfold "◂".
Admitted.

Fail Lemma pi_eq (Γ : C) (A : Sc Γ) : (pi CWF A) = (dpr_typecat A).
Fail Lemma te_eq (Γ : C) (A : Sc Γ) : (te CWF A) ≃ (var_typecat A).

Definition tm_equiv {Γ : C} (A : Sc Γ) : tm A ≃ CwF_tm CWF A.
Proof.
(*Already done in equivalence_unit_universe branch *)
Admitted.

Fail Lemma γ_Yo  (Γ : C) (A : Sc Γ) (a : tm A): γ CWF (tm_equiv A a) = #Yo a.

Lemma q_eq_term (Γ Γ' : C) (A : Sc Γ) (f : C⟦Γ',Γ⟧) 
: q_typecat A f = qq_term T _ _ f A .
Proof.
Admitted.
Fail Lemma q_eq_term' (Γ Γ' : C) (A : Sc Γ) (f : C⟦Γ',Γ⟧) 
: CwF_qq_term CWF A f = qq_term T _ _ f A .

Fail Lemma q_eq (Γ Γ' : C) (A : Sc Γ) (f : C⟦Γ',Γ⟧) 
: q_typecat A f = CwF_qq_term CWF f A .

End Stc_Benchmarks.

Section Cwf_Benchmarks.
Context (C : category) (Cwf : cwf_structure C).

Local Definition CWF_ : cwf := C,,Cwf.
Local Definition CWF'_ : cwf'_structure C := weq_cwf_cwf'_structure C Cwf.
Search "obj_ext_structure".
Local Definition X_ : obj_ext_structure C 
:= obj_ext_structure_of_cwf'_structure CWF'_.
Local Definition T_ : term_fun_structure C X_ := pr2(CWF'_).
Local Definition Sc'_ : split_typecat':= C,,weq_cwf'_sty' C CWF'_.
Local Definition Split_ : split_typecat_structure C := invweq(weq_sty_cwf C) Cwf.
Local Definition Sc_ : split_typecat := (C,,pr1 Split_),,pr2 Split_. (*take a few seconds*)

Lemma Type_equiv_ (Γ : C) : (Sc_ Γ) ≃ (Ty CWF_ Γ : hSet).
Proof.
exact (idweq _).
Qed.

Definition Type_equiv'_ (Γ : C) : (Ty CWF_ Γ : hSet) ≃ (Sc_ Γ ).
Proof.
exact (idweq _).
Defined.

Lemma ext_eq_part1_ (Γ : C) (A : Ty CWF_ Γ : hSet) : (Γ ◂ (Type_equiv'_ _ A)) = (comp_ext X_ Γ (Type_equiv'_ _ A)).
Proof.
Admitted.

Lemma ext_eq_part2_ (Γ : C) (A : Ty CWF_ Γ : hSet) : (ext CWF_ A) = (comp_ext X_ Γ (Type_equiv'_ _ A)).
Proof.
Admitted.

Lemma ext_eq_ (Γ : C) (A : Ty CWF_ Γ : hSet) : (Γ ◂ (Type_equiv'_ _ A)) = (ext CWF_ A).
Proof.
unfold ext.
unfold "◂".
unfold Type_equiv'_.
Admitted.

Fail Lemma pi_eq_ (Γ : C) (A : Ty CWF_ Γ : hSet) : (pi CWF_ A) = (dpr_typecat (Type_equiv'_ _ A)).

Fail Lemma te_eq_ (Γ : C) (A : Ty CWF_ Γ : hSet) : (te CWF_ A) = (var_typecat (Type_equiv'_ _ A)).

Definition tm_equiv_ {Γ : C} (A : Ty CWF_ Γ : hSet) : CwF_tm CWF_ A ≃ tm (Type_equiv'_ _ A).
Proof.

Admitted.

Fail Lemma γ_Yo  (Γ : C) (A : Ty CWF_ Γ : hSet) (a : CwF_tm CWF_ A): γ CWF_ a = #Yo (tm_equiv_ _ a).
About comp_ext.
Fail Lemma q_eq_term (Γ Γ' : C) (A : Ty CWF_ Γ : hSet)  (f : C⟦Γ',Γ⟧) 
: q_typecat (Type_equiv'_ _ A) f = qq_term T_ _ _ f A .
Proof.

Fail Lemma q_eq_term' (Γ Γ' : C) (A : Ty CWF_ Γ : hSet) (f : C⟦Γ',Γ⟧) 
: CwF_qq_term CWF_ A f = qq_term T_ _ _ f A .

Fail Lemma q_eq (Γ Γ' : C) (A : Ty CWF_ Γ : hSet) (f : C⟦Γ',Γ⟧) 
: q_typecat A f = CwF_qq_term CWF_ f A .

End Cwf_Benchmarks.
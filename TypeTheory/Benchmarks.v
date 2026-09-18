Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.All.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.

Require Import TypeTheory.ALV1.CwF_def.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Defs.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Maps.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Equivalence.
Require Import TypeTheory.ALV1.TypeCat.

Require Import TypeTheory.Initiality.SplitTypeCat_General.
Require Import TypeTheory.Initiality.SplitTypeCat_Structure.
Require Import TypeTheory.Articles.ALV_2017.

Notation "'pr1121' x" := (pr1(pr1(pr2(pr1(x))))) (at level 30).
Notation "'pr2121' x" := (pr2(pr1(pr2(pr1(x))))) (at level 30).
Notation "'pr1111' x" := (pr1(pr1(pr1(pr1(x))))) (at level 30).
Notation "'pr2111' x" := (pr2(pr1(pr1(pr1(x))))) (at level 30).
Notation "'pr1122' x" := (pr1(pr1(pr2(pr2(x))))) (at level 30).
Notation "'pr2122' x" := (pr2(pr1(pr2(pr2(x))))) (at level 30).

Section CwF.
Context (CwF : cwf).
Local Definition C : category := pr1 CwF.
Local Definition CWF_pp : mor_total(preShv(C)) := pr12 CwF.
Local Definition Ty : functor _ _ := target CWF_pp.
Local Definition Tm : functor _ _ := source CWF_pp.

(* extension of context *)
Local Definition ext {Γ : C} (A : Ty Γ : hSet) : C := pr11(pr22 CwF Γ A).
Local Notation "Γ.: A" :=  (ext A) (at level 24).

Definition pi {Γ :C} (A : Ty Γ : hSet) : C⟦Γ.:A,Γ⟧ := pr21 (pr22 CwF _ A).

(* just a simple to use pp as a nat_trans *)
Local Definition Nat_trans_morp {C : category} (Γ : C) (p : mor_total(preShv C)) 
:= pr12 p Γ.
Notation "p __: Γ" := (Nat_trans_morp Γ p)  (at level 24).
Local Definition pp_ (Γ : C)  : (Tm Γ : hSet) → (Ty Γ : hSet) := CWF_pp __: Γ.


Definition CwF_tm {Γ : C} (A : Ty Γ : hSet) : UU
:= ∑ a : Tm Γ : hSet, pp_ _ a = A.
Definition CwF_pr1_tm {Γ : C} {A : Ty Γ : hSet} (a : CwF_tm A) : Tm Γ : hSet 
:= pr1 a.
Coercion CwF_pr1_tm : CwF_tm >-> pr1hSet.

Definition reind_cwf {Γ : C} (A : Ty Γ : hSet) {Γ'} (f : C⟦Γ',Γ⟧) : Ty Γ' : hSet
:= #Ty f A.
Notation "A ⟪ f ⟫" := (reind_cwf A f) (at level 30).
Local Definition CWF_te {Γ : C} (A : Ty Γ : hSet) : CwF_tm (#Ty (pi A) A) 
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
  pathsinv0, (toforallpaths _ _ _ (pr22 CWF_pp _ _ f) a) .
Qed. 
  
Definition CwF_Pullback {Γ} (A : Ty Γ : hSet) 
: isPullback (yy A) CWF_pp (#Yo (pi A)) (yy(CWF_te A)) _ := pr22 pr22  CwF Γ A.

Definition CwF_reind_tm {Γ Δ} (f : C^op ⟦Γ,Δ⟧) {A : Ty Γ : hSet} (x : CwF_tm A)
: CwF_tm (A⟪f⟫) := (#Tm f x,,ppComp1 f x).

Lemma CwF_isaset_tm {Γ : C} (A : Ty Γ : hSet) : isaset (CwF_tm A).
Proof.
  apply isaset_total2.
  -  apply (setproperty (Tm Γ : hSet)).
  -  intro a; apply isasetaprop, (setproperty (Ty Γ : hSet)). 
Qed.

Lemma Subproof_γ {Γ : C} {A : Ty Γ : hSet} (a : CwF_tm A) 
: (identity (Yo Γ)) ;; yy A = (yy a ;;CWF_pp).
Proof.
  apply pathsinv0, (pathscomp0(yy_comp_nat_trans Tm Ty CWF_pp Γ a)) ,pathsinv0,
  (pathscomp0(@id_left _  (Yo Γ) Ty  (yy A))) ,
  (maponpaths yy (!(pr2 a))).
Qed.

Definition γ {Γ : C} {A : Ty Γ : hSet} (a : CwF_tm A) : (preShv C)⟦Yo Γ,Yo (Γ.:A)⟧
:= pr11( (CwF_Pullback A) (Yo Γ) (identity _) (yy a) (Subproof_γ a)).

Definition DepTypesType {Γ : C} {A : Ty Γ : hSet} (B : Ty(Γ.:A) : hSet) (a : CwF_tm A)
: Ty Γ : hSet :=  (γ a;;yy B : nat_trans _ _)  Γ (identity Γ).

(** Basic Def of qq, lemma on it in the types_structure_over_cwf_branch*)
Local Definition te' {Γ : C} (A : Ty Γ : hSet) 
: pp_ _ (CWF_te A) = #Ty (pi A) A := pr212 pr22 CwF Γ A.
Let Xk {Γ : C} (A : Ty Γ : hSet) :=
  make_Pullback _ _ _ _ _ _ (pr22 pr22 CwF Γ A).

Definition qq_yoneda {Γ  Δ : C} (A : Ty Γ : hSet) (f : C^op ⟦Γ,Δ⟧)
: (preShv C) ⟦Yo (Γ.:(#Ty f A)), Yo (Γ.: A) ⟧.
Proof.
  use (PullbackArrow (Xk A)).
  -  apply (#Yo (pi _) ;; #Yo f ). 
  -  apply (yy (CWF_te _)).
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
Abort.

Lemma ext_eq (Γ : C) (A : Sc Γ) : (Γ ◂ A) = (ext CWF A).
Proof.
unfold ext.
unfold "◂".
Abort.

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

Fail Lemma te_eq_ (Γ : C) (A : Ty CWF_ Γ : hSet) : (CwF_te CWF_ A) = (var_typecat (Type_equiv'_ _ A)).

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

Section middle_structure.
Definition cwf_splTC_structure_inter {C : category} (O : obj_ext_structure C): UU
:= ∑ (TQ : term_fun_structure C O × qq_morphism_structure O),
 iscompatible_term_qq (pr1 TQ) (pr2 TQ).
Definition cwf_splTC_structure (C : category) : UU
:= ∑ (O : obj_ext_structure C), cwf_splTC_structure_inter O.
Definition cwf_splTC : UU := ∑ C : category, cwf_splTC_structure C .


Section Equiv.
Context (C : category) (O : obj_ext_structure C).
Definition Term_first : UU := ∑ O : obj_ext_structure C, T1 O.
Definition qq_first : UU := ∑ O : obj_ext_structure C, T2 O.

Lemma term_first_equiv : T1 O ≃ cwf_splTC_structure_inter O.
Proof.
    use tpair.
    - intro a; exact ((pr1 a,,pr12 a),,pr22 a).
    - use gradth.
      -- intro a; exact (pr11 a,,(pr21 a,,pr2 a)).
      -- reflexivity.
      -- reflexivity.
Qed.

Lemma qq_first_equiv : T2 O ≃ cwf_splTC_structure_inter O.
Proof.
    use tpair.
    - intro a; exact ((pr12 a,,pr1 a),,pr22 a).
    - use gradth.
      -- intro a; exact (pr21 a,,(pr11 a,,pr2 a)).
      -- reflexivity.
      -- reflexivity.
Qed.

End Equiv.

Section Coercion.
Coercion cwf_splTC_cat (C : cwf_splTC) : category := pr1 C.
Coercion structure_of_cwf_splTC (C : cwf_splTC) : cwf_splTC_structure C := pr2 C.
Coercion object_structure_of_cwf_splTC (C : cwf_splTC) : obj_ext_structure C := pr12 C.
Coercion term_structure_of_cwf_splTC (C : cwf_splTC) : term_fun_structure C C := pr1122 C.
Coercion qq_structure_of_cwf_splTC (C : cwf_splTC) : qq_morphism_structure C := pr2122 C.
End Coercion.
Section access.
Context {C : cwf_splTC}.
Definition compatibility_cwf_splTC : iscompatible_term_qq C C := pr222 C.
Definition csTy : functor _ _ := TY C.
Definition reind_ty {Γ Δ} (A : csTy Γ : hSet) (f : C^op⟦Γ,Δ⟧) := #csTy f A.
Notation "A ⌊ f ⌋" := (reind_ty A f) (at level 30, only parsing).
Definition extens Γ (A : csTy Γ : hSet) : C := comp_ext C Γ A.
Notation "Γ ¤ A" := (extens Γ A) (at level 30, only parsing).
Definition cspi {Γ} (A : csTy Γ : hSet) : C⟦Γ¤A,Γ⟧ := π A .
Definition csTm : functor _ _ := TM C.
Definition p : nat_trans csTm csTy := pp C.
Definition cstm {Γ} (A : csTy Γ : hSet) := ∑ a : csTm Γ : hSet, p _ a = A .
Coercion pr1_tm {Γ} {A : csTy Γ : hSet} (a : cstm A) : csTm Γ : hSet := pr1 a.
Coercion pr2_tm {Γ} {A : csTy Γ : hSet} (a : cstm A) : p _ a = A := pr2 a.

Definition var' {Γ} (A : csTy Γ : hSet) : csTm (Γ¤A) : hSet := te C A.
Definition var_commut {Γ} (A : csTy Γ : hSet) : p _ (var' A) = A ⌊cspi A⌋:= pp_te C A.
Definition var {Γ} (A : csTy Γ : hSet) : cstm (A⌊cspi A⌋) := (var' A,, var_commut A).

Definition Yo_var_commut {Γ} (A : csTy Γ : hSet) : #Yo (cspi A) ;; yy A = yy(var A) ;; p
:= term_fun_str_square_comm (var A).
Definition term_pullback {Γ} (A : csTy Γ : hSet)
: isPullback _ _ _ _ (Yo_var_commut A)
:= isPullback_Q_pp C A.

Definition csq {Γ Δ} (A : csTy Γ : hSet) (f : C^op⟦Γ,Δ⟧) : C⟦Δ¤(A⌊f⌋),Γ¤A⟧ := qq C f A.
Definition q_eq {Γ Δ} (A : csTy Γ : hSet) (f : C^op⟦Γ,Δ⟧) : cspi _ ;; f = csq A f ;; cspi _ := !(qq_π C f A).
Definition q_pullback {Γ Δ} (A : csTy Γ : hSet) (f : C^op⟦Γ,Δ⟧) : isPullback _ _ _ _ (q_eq A f) := qq_π_Pb C f A.
End access.

Definition splTC_equiv (C : category) : split_typecat_structure C ≃ cwf_splTC_structure C.
apply (weqcomp (weq_standalone_to_regrouped C) ).
apply weqfibtototal.
intro X. apply (weqcomp (invweq (forget_compat_term X))). exact (qq_first_equiv C X).
Defined.
Definition cwf_equiv (C : category) : cwf_structure C ≃ cwf_splTC_structure C.
apply (weqcomp (weq_cwf_cwf'_structure C) ).
apply weqfibtototal.
intro X. apply (weqcomp (invweq (forget_compat_qq X))). exact (term_first_equiv C X).
Defined.

End middle_structure.

Section middle_structure_cwf_benchmark.

Context (C : category) (CS : cwf_splTC_structure C).

Definition cs : cwf_splTC := C,,CS.
Definition Cwf : cwf := C,, invweq (cwf_equiv C) CS.

Lemma Type_equi (Γ : C) : (@csTy cs Γ : hSet ) ≃ (Ty Cwf Γ : hSet).
Proof.
exact (idweq _).
Qed.

Definition Type_equi' (Γ : C) : (Ty Cwf Γ : hSet) ≃ (@csTy cs Γ : hSet).
Proof.
exact (idweq _).
Defined.

Lemma ext_comp (Γ : C) (A : @csTy cs Γ : hSet) : (@extens cs Γ A) = (ext Cwf A).
Proof.
unfold ext.
unfold extens,comp_ext,comp_ext_disp.
Admitted.

Fail Lemma pi_eq_ (Γ : C) (A : @csTy cs Γ : hSet) : (pi Cwf A) = (cspi A).

Fail Lemma te_eq_ (Γ : C) (A : @csTy cs Γ : hSet) : (CwF_te Cwf A) = (var' A).

Definition tm_equi {Γ : C} (A : @csTy cs Γ : hSet) : CwF_tm Cwf A ≃ cstm A.
Proof.

Admitted.

Fail Lemma q_eq (Γ Γ' : C) (A : @csTy cs Γ : hSet) (f : C⟦Γ',Γ⟧) 
: csq A f = CwF_qq_term Cwf A f.

End middle_structure_cwf_benchmark.

Section middle_structure_splTC_benchmark.

Context (C : category) (CS_ : cwf_splTC_structure C).

Definition cs_ : cwf_splTC := C,,CS_.
Definition Spl : split_typecat_structure C := invweq (splTC_equiv C) CS_.
Definition spl : split_typecat := (C,,pr1 Spl),,pr2 Spl. (* take a few seconds*)


Lemma Type_equi_ (Γ : C) : (@csTy cs_ Γ : hSet ) ≃ (spl Γ).
Proof.
exact (idweq _).
Qed.

Definition Type_equi_' (Γ : C) : (spl Γ) ≃ (@csTy cs_ Γ : hSet).
Proof.
exact (idweq _).
Defined.

Lemma ext_comp_ (Γ : C) (A : @csTy cs_ Γ : hSet) : (@extens cs_ Γ A) = (Γ ◂ (Type_equi_ _ A)).
Proof.
unfold extens,comp_ext,comp_ext_disp.
Admitted.

Fail Lemma pi_eq_ (Γ : C) (A : @csTy cs_ Γ : hSet) : (dpr_typecat (Type_equi_ _ A)) = (cspi A).

Fail Lemma te_eq_ (Γ : C) (A : @csTy cs_ Γ : hSet) : (var_typecat (Type_equi_ _ A)) = (var' A).

Definition tm_equi_ {Γ : C} (A : @csTy cs_ Γ : hSet) : tm (Type_equi_ _ A) ≃ cstm A.
Proof.

Admitted.

Fail Lemma q_eq (Γ Γ' : C) (A : @csTy cs_ Γ : hSet) (f : C⟦Γ',Γ⟧) 
: csq A f = q_typecat (Type_equi_ _  A) f.

End middle_structure_splTC_benchmark.
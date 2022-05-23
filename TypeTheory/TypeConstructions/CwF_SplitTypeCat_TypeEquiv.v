(**
Content :
- Unit and Universe Type on CwF
- Unit Type on Split_Type_Category
- term equivalence over weq_sty_cwf
- unit equivalence over weq_sty_cwf
_ universe equivalence over weq_sty_cwf
**)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheory.
Require Import TypeTheory.Auxiliary.SetsAndPresheaves.
Require Import TypeTheory.Auxiliary.TypeOfMorphisms.

Require Import TypeTheory.ALV1.CwF_def.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Defs.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Maps.
Require Import TypeTheory.TypeCat.TypeCat.

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

Local Definition pi {Γ :C} (A : Ty Γ : hSet) : C⟦Γ.:A,Γ⟧ := pr21 (pr22 CwF _ A).

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
  pathsinv0, (toforallpaths (pr22 pp _ _ f) a) .
Qed. 

Definition CwF_Pullback {Γ} (A : Ty Γ : hSet) 
: isPullback _ := pr22 pr22  CwF Γ A.

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

(** Unit Types *)
Section Unit.

Definition CwF_unit_TypeFormer : UU := ∏ Γ : C, Ty Γ : hSet.

Definition CwF_unit_Elem (U : CwF_unit_TypeFormer) : UU := ∏ Γ : C, CwF_tm (U Γ).

Definition CwF_unit_unity (U : CwF_unit_TypeFormer) (E : CwF_unit_Elem U) : UU 
:= ∏ (Γ : C) (b : CwF_tm (U Γ)) , (E Γ) = b.

Lemma CwF_isaprop_unity (U : CwF_unit_TypeFormer) (E : CwF_unit_Elem U) 
: isaprop (CwF_unit_unity U E).
Proof.
  unfold CwF_unit_unity.
  do 2 (apply impred_isaprop; intro).
  apply CwF_isaset_tm.
Qed.

Definition CwF_unit_structure : UU 
:= ∑ (U : CwF_unit_TypeFormer) (E : CwF_unit_Elem U), CwF_unit_unity U E.

End Unit.

(** Universe Types*)
Section Universe.
Definition CwF_basetype_struct : UU
:=  ∑ U : ∏ Γ, Ty Γ : hSet, ∏ Γ Δ (f: C⟦Δ,Γ⟧), (U Γ) ⟪f⟫ = U Δ.

Definition CwF_basetype_struct_pr1 : CwF_basetype_struct -> ∏ Γ, Ty Γ : hSet := pr1.
Coercion CwF_basetype_struct_pr1 : CwF_basetype_struct >-> Funclass.
  
Definition CwF_basetype_natural {U : CwF_basetype_struct} {Γ Γ'} (f : C⟦Γ',Γ⟧)
:  U Γ ⟪f⟫ = U Γ' := pr2 U _ _ f.

Definition CwF_deptype_struct (U : CwF_basetype_struct) : UU.
Proof.
  use (∑ D : ∏ Γ (a : CwF_tm (U Γ)), Ty Γ : hSet, _).
  use (∏ Δ Γ (f : C ⟦Δ, Γ⟧) (a : CwF_tm (U Γ)), _).
  refine ((D Γ a) ⟪f⟫ = D Δ _).
  exact (CwF_tm_transportf (CwF_basetype_natural f) (CwF_reind_tm f a)).
Defined.

Definition CwF_deptype_struct_pr1 {U} (El : CwF_deptype_struct U) := pr1 El.
Coercion CwF_deptype_struct_pr1 : CwF_deptype_struct >-> Funclass.

Definition CwF_deptype_struct_natural {U} (El : CwF_deptype_struct U) := pr2 El.

Definition CwF_universe_struct
:= ∑ U : CwF_basetype_struct, CwF_deptype_struct U.

Coercion CwF_universe (U : CwF_universe_struct) : CwF_basetype_struct := pr1 U.
Definition CwF_universe_natural (U : CwF_universe_struct) := @CwF_basetype_natural U.
Definition CwF_elements {U : CwF_universe_struct} : CwF_deptype_struct U := pr2 U.
Definition CwF_elements_natural {U : CwF_universe_struct}
:= CwF_deptype_struct_natural (@CwF_elements U).

End Universe.

End CwF.

Section SplitTypeCat.
Context (C : split_typecat).
Section Unit.

Definition unit_TypeFormer : UU := ∏ Γ : C, C Γ.

Definition unit_Elem (U : unit_TypeFormer) : UU := ∏  Γ : C, tm (U Γ).

Definition unit_unity (U : unit_TypeFormer) (E : unit_Elem U)  : UU 
:= ∏ (Γ : C) (b : tm (U Γ)), (E Γ) = b.

Lemma isaprop_unity (U : unit_TypeFormer) (E : unit_Elem U) : isaprop (unit_unity U E).
Proof.
  unfold unit_unity.
  do 2 (apply impred_isaprop; intro).
  apply isaset_tm.
Qed.

Definition unit_structure : UU 
:= ∑ (U : unit_TypeFormer) (E : unit_Elem U), unit_unity U E.
End Unit.
End SplitTypeCat.

Section Stc_Equiv.
Context (C : category) (Split : split_typecat_structure C).

Local Definition Sc : split_typecat := (C,,pr1 Split),,pr2 Split.
Local Definition Sc' : split_typecat' := C,,weq_standalone_to_regrouped C Split.
Local Definition X : obj_ext_structure C 
:= obj_ext_structure_of_split_typecat'_structure Sc'.
Local Definition CWF : cwf := C,,weq_sty_cwf _ Split.

Section Global_Lemma.
Lemma inver {A B : UU} (f : A ≃ B) (a : A) : (∏ b : A, a = b) -> ∏ b : B, f a = b.
Proof.
  intros g b.
  apply (pathscomp0 (maponpaths f (g (invweq f b)))).
  exact (homotweqinvweq _ _).
Defined.
End Global_Lemma.


Section tm_equiv.

Definition tm_inter {Γ : C} (A : Sc Γ) := ∑ a : tm_from_qq Sc' Γ : hSet , pr1 a = A.

Definition tm_equiv_inter_1 {Γ : C} (A : Sc Γ) : tm A → tm_inter A.
Proof.
  intros [s ids].
  use tpair.
  - exact (A,,(s,,ids)).
  - reflexivity.
Defined.

Definition tm_equiv_inter_2 {Γ : C} (A : Sc Γ) : tm_inter A → tm A.
Proof.
  intros [[A0 [s ids]] pr1A].
  induction pr1A.
  exact (s,,ids).
Defined.

Definition tm_equiv_inter_12 {Γ : C} {A : Sc Γ} (a : tm A) 
: tm_equiv_inter_2 _ (tm_equiv_inter_1  _  a) = a.
Proof.
  reflexivity.
Qed.

Definition tm_equiv_inter_21 {Γ : C} {A : Sc Γ} (a : tm_inter A) :
tm_equiv_inter_1 _ (tm_equiv_inter_2  _  a) = a.
Proof.
  destruct a as [[A0 [pr1p pr2p]] path].
  induction path.
  reflexivity.
Qed.

Definition tm_equiv_inter {Γ : C} (A : Sc Γ) : tm A ≃ tm_inter A
:= tm_equiv_inter_1 _,, gradth (tm_equiv_inter_1 _) (tm_equiv_inter_2 _) 
   tm_equiv_inter_12 tm_equiv_inter_21.

(* The next two definition are useless for the code itself but useful to understand what append*)
(*Definition tm_equiv_underset {Γ : C}  (A: Sc Γ) : (tm_from_qq Sc' Γ : hSet) ≃ (Tm CWF Γ : hSet).
Proof.
apply hSet_univalence.
reflexivity.
Defined.

Definition tm_equiv_interbis {Γ : C}  (A: Sc Γ) : (tm_inter A) ≃ (CwF_tm CWF A ).
Proof.
apply eqweqmap.
reflexivity.
Defined.*)

Definition tm_equiv {Γ : C} (A : Sc Γ) : tm A ≃ CwF_tm CWF A := tm_equiv_inter A.

Definition reind_tm_inter {Γ Δ : Sc} {A: Sc Δ} (f : Sc ⟦Γ,Δ⟧) (a : tm_inter A)
: tm_inter (A ⦃f⦄).
Proof.
  use tpair.
  -  exact (#(tm_from_qq Sc') f (pr1 a)).
  -  induction (pr2 a). reflexivity.
Defined.

Lemma pb_of_section_eq {a b c d : C} {f : C ⟦b, a⟧} {g : C ⟦c, a⟧} {h : C⟦d, b⟧} {k : C⟦d,c⟧}
(H H' : h · f = k · g) (isPb  : isPullback H) (isPb' : isPullback H')
{s s' : C⟦a,c⟧} (eqS : s = s') (K : s · g = identity _) (K': s' · g = identity _) 
: pb_of_section H isPb s K = pb_of_section H' isPb' s' K'.
Proof.
  induction eqS.
  assert (eqH : H = H') by exact (pr1(pr2 C _ _ _ _ _ _)).
  induction eqH.
  assert (eqK : K = K') by exact (pr1(pr2 C _ _ _ _ _ _)).
  induction eqK.
  assert (eqPb: isPb = isPb') by exact (pr1 (isaprop_isPullback _ _ _ _ _ _ _ _)).
  induction eqPb.
  reflexivity.
Qed.

Lemma reind_tm_equiv_inter  {Γ Δ : Sc} {A : Sc Δ} (f : Sc ⟦Γ,Δ⟧) (a : tm A)
: reind_tm_inter f (tm_equiv _ a)  = tm_equiv _ (reind_tm f a).
Proof.
  refine (subtypePairEquality' _ _ ).
  -  apply pathsinv0, (pathscomp0 (idpath (A ⦃f⦄,,reind_tm f a))).
     refine (pair_path_in2 _ _).
     unfold tm_equiv.
     assert (eq1 : ((pr1 a) :C ⟦ Δ,_ ⟧) = (pr121 (tm_equiv_inter A a)))
     by (simpl; reflexivity).
     (* important for typing in order to make *)
     set (isPb := (reind_pb_typecat A f) : isPullback
     ((! dpr_q_typecat A f) : (π (#p (TY Sc') f (pr11 (tm_equiv_inter A a))) ;; f)%mor =
     (qq Sc' f (pr11 (tm_equiv_inter A a)) ;; π (pr11 (tm_equiv_inter A a)))%mor));
     set (H := (! dpr_q_typecat A f) 
     : (π (#p (TY Sc') f (pr11 (tm_equiv_inter A a))) ;; f)%mor =
     (qq Sc' f (pr11 (tm_equiv_inter A a)) ;; π (pr11 (tm_equiv_inter A a)))%mor);
     exact (pb_of_section_eq H _ isPb _ eq1 _ (pr221 (tm_equiv_inter A a))).
  -  exact (pr12 Split _ _ _).
Qed. 

Lemma reind_tm_equiv {Γ Δ : Sc} {A : Sc Δ} (f : Sc ⟦Γ,Δ⟧) (a : tm A) 
: CwF_reind_tm CWF f (tm_equiv _ a)  = tm_equiv _ (reind_tm f a).
Proof. 
  rewrite (!(reind_tm_equiv_inter f _)).
  refine (subtypePairEquality' _ _ ).
  -  reflexivity.
  -  apply (setproperty (Ty CWF Γ)).
Qed.

Lemma equiv_reind_tm {Γ Δ : Sc} {A : Sc Δ} (f : Sc ⟦Γ,Δ⟧) (a : CwF_tm CWF A) 
: invweq (tm_equiv _) (CwF_reind_tm CWF f a)  = reind_tm f (invweq (tm_equiv _) a).
Proof. 
  set (a' := (invweq (tm_equiv _) a) : tm A).
  assert (eqa : a = tm_equiv _ a') by (cbn; exact (!(tm_equiv_inter_21 _))).
  rewrite eqa.
  rewrite reind_tm_equiv.
  exact (homotinvweqweq0 (tm_equiv (A ⦃f⦄)) _).
Qed.

Lemma transportf_tm_equiv {Γ : Sc} {A A' : Sc Γ} (eq : A = A') (a' : tm A) 
: CwF_tm_transportf CWF eq (tm_equiv _ a')  =  tm_equiv _ (tm_transportf eq a').
Proof.
  refine (subtypePairEquality' _ _ ).
  -  induction eq. rewrite tm_transportf_idpath. reflexivity.
  -  apply (setproperty (Ty CWF Γ)).
Qed.

Lemma equiv_transportf_tm {Γ : Sc} {A A' : Sc Γ} (eq : A = A') (a : CwF_tm CWF A) 
: invweq (tm_equiv _) (CwF_tm_transportf CWF eq a)  =  tm_transportf eq (invweq (tm_equiv _) a).
Proof.
  set (a' := (invweq (tm_equiv _) a) : tm A).
  assert (eqa : a = tm_equiv _ a') by (cbn; exact (!(tm_equiv_inter_21 _))).
  rewrite eqa.
  rewrite transportf_tm_equiv.
  exact (homotinvweqweq0 (tm_equiv A') _).
Qed.

End tm_equiv.

Section Unit_Equiv.

Definition unit_equiv_1 : unit_structure Sc -> CwF_unit_structure CWF.
Proof.
  intro Unit.
  use tpair.
  -  exact (pr1 Unit).
  -  use tpair.
    --  intro Γ. exact (tm_equiv _ (pr12 Unit Γ)).
    --  intro Γ. exact (inver (tm_equiv _) (pr12 Unit Γ) (pr22 Unit Γ)).
Defined.

Definition unit_equiv_2 : CwF_unit_structure CWF -> unit_structure Sc.
Proof.
  intro Unit.
  use tpair.
  -  exact (pr1 Unit).
  -  use tpair.
    --  intro Γ. exact (invweq (tm_equiv _) (pr12 Unit Γ)).
    --  intro Γ. exact (inver (invweq (tm_equiv _)) (pr12 Unit Γ) (pr22 Unit Γ)).
Defined.

Lemma unit_equiv_inv1 : ∏ x : unit_structure Sc, unit_equiv_2(unit_equiv_1 x) = x.
Proof.
  intro Unit.
  apply pair_path_in2.
  assert (prj : pr2 Unit = pr12 Unit ,, pr22 Unit) by auto.
  apply pathsinv0.
  apply (pathscomp0 prj).
  refine (subtypePairEquality' _ _ ).
  -  assert (func:  pr12 Unit = λ Γ : C , pr12 Unit Γ) by auto.
     apply (pathscomp0 func).
     apply funextsec2.
     intro Γ.
     exact (homotinvweqweq0 _ _).
  -  apply isaprop_unity.
Qed.

Lemma unit_equiv_inv2 : ∏ x : CwF_unit_structure CWF, unit_equiv_1(unit_equiv_2 x) = x.
Proof.
  intro Unit.
  apply pair_path_in2.
  assert (prj : pr2 Unit = (pr12 Unit ,, pr22 Unit)) by auto.
  apply pathsinv0.
  apply (pathscomp0 prj).
  refine (subtypePairEquality' _ _ ).
  -  assert (func:  pr12 Unit = λ Γ : C , pr12 Unit Γ) by auto.
     apply (pathscomp0 func).
     apply funextsec2.
     intro Γ.
     apply pathsinv0.
     exact (homotweqinvweq _ _).
  -  apply CwF_isaprop_unity.
Qed.

Definition unit_equiv : unit_structure Sc ≃ CwF_unit_structure CWF
:= (unit_equiv_1,,gradth unit_equiv_1 unit_equiv_2 unit_equiv_inv1 unit_equiv_inv2).

End Unit_Equiv.

Section Universe_Equiv.

Definition universe_equiv_1 : universe_struct Sc -> CwF_universe_struct CWF.
Proof.
  intro Universe.
  use tpair.
  -  exact (pr1 Universe).
  -  use tpair.
     --  intros Γ a. exact (pr12 Universe  _ (invweq (tm_equiv _) a)).
     -- intros Γ Δ f a.  
        apply (pathscomp0 (pr22 Universe _ _ _ _)).
        apply maponpaths.
        apply pathsinv0.
        apply (pathscomp0 (equiv_transportf_tm _ _)).
        apply maponpaths.
        exact (equiv_reind_tm _ _).
Defined.

Definition universe_equiv_2 : CwF_universe_struct CWF -> universe_struct Sc.
Proof.
  intro Universe.
  use tpair.
  -  exact (pr1 Universe).
  -  use tpair.
     --  intros Γ a. exact (pr12 Universe  _  (tm_equiv _ a)).
    --  intros Γ Δ f a.  apply (pathscomp0 (pr22 Universe _ _ _ _)).
        apply maponpaths.
        apply pathsinv0.
        apply (pathscomp0 (!(transportf_tm_equiv _ _))).
        apply maponpaths.
        exact (!(reind_tm_equiv _ _)).
Defined.

Lemma universe_equiv_inv1 
: ∏ x : universe_struct Sc, universe_equiv_2(universe_equiv_1 x) = x.
Proof.
  intro Universe.
  apply pair_path_in2.
  assert (prj : pr2 Universe = pr12 Universe ,, pr22 Universe) by auto.
  apply pathsinv0.
  apply (pathscomp0 prj).
  refine (subtypePairEquality' _ _ ).
  -  assert (func : pr12 Universe = λ Γ : C , pr12 Universe Γ) by auto.
     apply (pathscomp0 func).
     apply funextsec2.
     intro Γ.
     assert (simplman : pr12 Universe Γ  =  λ a : _, pr12 Universe Γ a) by auto.
     rewrite simplman.
     reflexivity.
  -  do 4 (apply impred_isaprop; intro); exact (pr12 Split _ _ _).
Qed.

Lemma universe_equiv_inv2 
: ∏ x : CwF_universe_struct CWF, universe_equiv_1(universe_equiv_2 x) = x.
Proof.
  intro Universe.
  apply pair_path_in2.
  assert (prj : pr2 Universe = pr12 Universe ,, pr22 Universe) by auto.
  apply pathsinv0.
  apply (pathscomp0 prj).
  refine (subtypePairEquality' _ _ ).
  -  assert (func : pr12 Universe = λ Γ : C , pr12 Universe Γ) by auto.
     apply (pathscomp0 func).
     apply funextsec2.
     intro Γ.
     assert (simplman : pr12 Universe Γ  =  λ a : _, pr12 Universe Γ a) by auto.
     rewrite simplman.
     cbn; apply funextsec; intro a; rewrite tm_equiv_inter_21; reflexivity.
  -  do 4 (apply impred_isaprop; intro); exact (setproperty (Ty CWF _) _ _).
Qed.

Definition universe_equiv : universe_struct Sc ≃ CwF_universe_struct CWF 
:= universe_equiv_1,,gradth universe_equiv_1 universe_equiv_2 
   universe_equiv_inv1 universe_equiv_inv2.

End Universe_Equiv.

End Stc_Equiv.

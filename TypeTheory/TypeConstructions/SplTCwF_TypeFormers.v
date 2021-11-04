Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.All.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Defs.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Maps.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Equivalence.

Notation "'pr1121' x" := (pr1(pr1(pr2(pr1(x))))) (at level 30).
Notation "'pr2121' x" := (pr2(pr1(pr2(pr1(x))))) (at level 30).
Notation "'pr1111' x" := (pr1(pr1(pr1(pr1(x))))) (at level 30).
Notation "'pr2111' x" := (pr2(pr1(pr1(pr1(x))))) (at level 30).
Notation "'pr1122' x" := (pr1(pr1(pr2(pr2(x))))) (at level 30).
Notation "'pr2122' x" := (pr2(pr1(pr2(pr2(x))))) (at level 30).

Definition splTCwF_structure (C : category) : UU
:= ∑ (O : obj_ext_structure C) (TQ : term_fun_structure C O × qq_morphism_structure O),
 iscompatible_term_qq (pr1 TQ) (pr2 TQ).
Definition splTCwF : UU := ∑ C : category, splTCwF_structure C .

Section Equiv.
Context (C : category).
Definition Term_first : UU := ∑ O : obj_ext_structure C, T1 O.
Definition qq_first : UU := ∑ O : obj_ext_structure C, T2 O.

Lemma term_first_equiv : Term_first ≃ splTCwF_structure C.
Proof.
    use tpair.
    - intro a; exact (pr1 a,,((pr12 a,,pr122 a),,pr222 a)).
    - use gradth.
      -- intro a; exact (pr1 a,,(pr112 a,,(pr212 a,,pr22 a))).
      -- reflexivity.
      -- reflexivity.
Qed.

Lemma qq_first_equiv : qq_first ≃ splTCwF_structure C.
Proof.
    use tpair.
    - intro a; exact (pr1 a,,((pr122 a,,pr12 a),,pr222 a)).
    - use gradth.
      -- intro a; exact (pr1 a,,(pr212 a,,(pr112 a,,pr22 a))).
      -- reflexivity.
      -- reflexivity.
Qed.

End Equiv.

Section Coercion.

Coercion splTCwF_cat (C : splTCwF) : category := pr1 C.
Coercion structure_of_splTCwF (C : splTCwF) : splTCwF_structure C := pr2 C.
Coercion object_structure_of_splTCwF (C : splTCwF) : obj_ext_structure C := pr12 C.
Coercion term_structure_of_splTCwF (C : splTCwF) : term_fun_structure C C := pr1122 C.
Coercion qq_structure_of_splTCwF (C : splTCwF) : qq_morphism_structure C := pr2122 C.

End Coercion.

Section splTCwF.
Context {C : splTCwF}.

Section access.

Definition Ty : functor _ _ := TY C.
Definition reind_ty {Γ Δ} (A : Ty Γ : hSet) (f : C^op⟦Γ,Δ⟧) := #Ty f A.
Notation "A ⌊ f ⌋" := (reind_ty A f) (at level 30, only parsing).
Definition ext Γ (A : Ty Γ : hSet) : C := comp_ext C Γ A.
Notation "Γ ¤ A" := (ext Γ A) (at level 30, only parsing).
Definition pi {Γ} (A : Ty Γ : hSet) : C⟦Γ¤A,Γ⟧ := π A .
Definition Tm : functor _ _ := TM C.
Definition p : nat_trans Tm Ty := pp C.
Definition tm {Γ} (A : Ty Γ : hSet) := ∑ a : Tm Γ : hSet, p _ a = A .
Coercion pr1_tm {Γ} {A : Ty Γ : hSet} (a : tm A) : Tm Γ : hSet := pr1 a.
Coercion pr2_tm {Γ} {A : Ty Γ : hSet} (a : tm A) : p _ a = A := pr2 a.
Lemma ppComp1 {Γ Δ : C} {A : Ty Γ : hSet} (f : C^op ⟦Γ,Δ⟧) (a : tm A) :
  p _ (# Tm f a ) = # Ty f A. 
Proof.
  apply pathsinv0, (pathscomp0(!(maponpaths (# Ty f) (pr2 a)))).
  apply pathsinv0, (toforallpaths _ _ _ (pr2 p _ _ _) a).
Qed.
Definition reind_tm {Γ : C} {A : Ty Γ : hSet} {Γ'} (f : C⟦Γ',Γ⟧) (a : tm A) 
: tm (A ⌊f⌋) := #Tm f a,, ppComp1 f a .
Notation "a ⌈ f ⌉" := (reind_tm f a) (at level 30, only parsing).
Definition var' {Γ} (A : Ty Γ : hSet) : Tm (Γ¤A) : hSet := te C A.
Definition var_commut {Γ} (A : Ty Γ : hSet) : p _ (var' A) = A ⌊pi A⌋:= pp_te C A.
Definition var {Γ} (A : Ty Γ : hSet) : tm (A⌊pi A⌋) := (var' A,, var_commut A).

Definition Yo_var_commut {Γ} (A : Ty Γ : hSet) : #Yo (pi A) ;; yy A = yy(var A) ;; p
:= term_fun_str_square_comm (var A).
Definition term_pullback {Γ} (A : Ty Γ : hSet)
: isPullback _ _ _ _ (Yo_var_commut A)
:= isPullback_Q_pp C A.

Definition q {Γ Δ} (A : Ty Γ : hSet) (f : C^op⟦Γ,Δ⟧) : C⟦Δ¤(A⌊f⌋),Γ¤A⟧ := qq C f A.
Definition q_eq {Γ Δ} (A : Ty Γ : hSet) (f : C^op⟦Γ,Δ⟧) : pi _ ;; f = q A f ;; pi _ := !(qq_π C f A).
Definition q_pullback {Γ Δ} (A : Ty Γ : hSet) (f : C^op⟦Γ,Δ⟧) : isPullback _ _ _ _ (q_eq A f) := qq_π_Pb C f A.
Definition compatibility_splTCwF {Γ Δ : C} (A : Ty Γ : hSet) (f : C⟦Δ, Γ⟧) : # Tm (q A f) (var A) = var (A⌊f⌋) := !(pr222 C Γ Δ A f).

End access.

Notation "A ⌊ f ⌋" := (reind_ty A f) (at level 30, only parsing).
Notation "Γ ¤ A" := (ext Γ A) (at level 30, only parsing).
Notation "a ⌈ f ⌉" := (reind_tm f a) (at level 30, only parsing).

Section Yoneda.
 
(** * Few usefull lemma on yoneda **)

Lemma yonedainv {A B : C} (f : C⟦A,B⟧) : Yo^-1 (#Yo f) = f.
Proof.
  apply id_left.
Qed.

Lemma transportyo {A B : C} {f g : C⟦A,B⟧} (e : #Yo f = #Yo g) : f = g.
Proof.
  apply (pathscomp0 (!(yonedainv f))), pathsinv0
  ,(pathscomp0 (!(yonedainv g))), (!(maponpaths Yo^-1 e)).
Qed.

Lemma yonedacarac {Γ Δ : C} (f  : _ ⟦Yo Γ,Yo Δ⟧) 
: # Yo ((f :nat_trans _ _) Γ (identity Γ)) = f.
Proof.
  assert (H : (# Yo ((f : nat_trans _ _) Γ (identity Γ)) : nat_trans _ _) Γ (identity Γ)
               = (f : nat_trans _ _) Γ (identity Γ)) by apply (id_left _).
  assert (Map1 : (f : nat_trans _ _) Γ (identity Γ) = yoneda_map_1 C (pr21 C) Γ (Yo(Δ)) f)
  by reflexivity.
  assert (Map2 : # Yo ((f : nat_trans _ _) Γ (identity Γ)) = yoneda_map_2 C (pr21 C) Γ (Yo(Δ))
         ((f : nat_trans _ _) Γ (identity Γ))).                                      
  -  unfold yoneda_map_2; cbn; unfold yoneda_morphisms; unfold yoneda_morphisms_data; cbn.
     assert (nattrans : is_nat_trans_yoneda_morphisms_data C _ Γ Δ
         ((f :nat_trans _ _) Γ (identity Γ))
          = yoneda_map_2_ax C (pr21 C) Γ (yoneda_objects C _ Δ)
          ((f : nat_trans _ _) Γ (identity Γ))).
     --  assert (prop : isaprop(is_nat_trans (yoneda_objects C _ Γ)
         (yoneda_objects C (homset_property C) Δ)
         (yoneda_morphisms_data C _ Γ Δ
         ((f : nat_trans _ _) Γ (identity Γ))))) by (apply isaprop_is_nat_trans;exact (pr2 hset_category));
        exact (pr1 (prop _ _)).
     --  apply pair_path_in2; apply nattrans.
  -  rewrite Map2; rewrite Map1; apply yoneda_map_1_2.
Qed.

Lemma invyoneda {Γ Δ : C} (f  : _ ⟦Yo Γ,Yo Δ⟧) : #Yo (Yo^-1 f) = f.
Proof.
  apply yonedacarac.
Qed.


Lemma invyonedacarac {Γ Δ : C} (f  : _ ⟦Yo Γ,Yo Δ⟧) : (Yo^-1 f) = ((f :nat_trans _ _) Γ (identity Γ)).
Proof.
rewrite (!(yonedacarac _)). rewrite yonedainv ,yonedacarac. reflexivity.
Qed.

Lemma yyidentity {Γ : C} {A : Ty Γ : hSet} (B : Ty (Γ¤A) : hSet) 
: B = (@yy (pr1 C) (pr21 C) Ty (Γ¤A) B : nat_trans _ _) (Γ¤A) (identity (Γ¤A)).
Proof.
  apply pathsinv0; eapply pathscomp0.
  -  apply (toforallpaths _ (# Ty _) _ (functor_id Ty (Γ¤A))).
  -  reflexivity.
Qed.


Lemma q_eq_yoneda {Γ Δ} (A : Ty Γ : hSet) (f : C^op⟦Γ,Δ⟧) : #Yo(pi _) ;; #Yo f = #Yo (q A f) ;; #Yo (pi _).
Proof.
    rewrite (!(pr22 Yo _ _ _ (q A f) _)),(!(pr22 Yo _ _ _ _ f)).
    rewrite q_eq.
    reflexivity.
Qed.

End Yoneda.

Section Ty_Tm_lemmas.

Lemma Ty_composition {Γ Γ' Γ'' : C} (f : C⟦Γ,Γ'⟧) (g : C⟦Γ',Γ''⟧) (A : Ty Γ'' : hSet) 
: A ⌊f;;g⌋ =  (A ⌊ g ⌋) ⌊f⌋.
Proof.
  exact (!((toforallpaths _ _ _ (!(pr22 Ty _ _ _  g f))) A)).
Qed.

Lemma Tm_composition {Γ Γ' Γ'' : C} (f : C⟦Γ,Γ'⟧) (g : C⟦Γ',Γ''⟧) (A : Tm Γ'' : hSet)
: #Tm (f;;g) A = #Tm f (#Tm g A).
Proof.
  exact (!((toforallpaths _ _ _ (!(pr22 Tm _ _ _  g f))) A)).
Qed.

Lemma Ty_identity {Γ : C} (A : Ty Γ : hSet) : A = A ⌊identity Γ⌋ .
Proof.
  assert (eqA : A = (identity (pr1 Ty Γ) A)) by auto.
  rewrite eqA.
  apply (!((toforallpaths _ _ _ (pr12 Ty _ )) A)).
Qed.

Lemma compose_ty {Γ Δ Η : C} (A : Ty Γ : hSet) (f : C^op ⟦Γ,Δ⟧) (g : C^op ⟦Δ,Η⟧) : A ⌊f⌋ ⌊g⌋ = A ⌊f;;g⌋.
Proof.
unfold reind_ty.
assert (eqf : # Ty f = # (pr1 Ty) f) by auto; rewrite eqf.
assert (eqg : # Ty g = # (pr1 Ty) g) by auto; rewrite eqg.
assert (eqfg : # Ty (f;;g) = # (pr1 Ty) (f;;g)) by auto; rewrite eqfg.
rewrite (pr22 Ty _ _ _  f g).
reflexivity.
Qed.

End Ty_Tm_lemmas.

Section term_subtitution.

Lemma Subproof_γ {Γ : C} {A : Ty Γ : hSet} (a : tm A)
: identity (Yo Γ) ;; yy A = yy a ;;p.
Proof.
  apply pathsinv0, (pathscomp0(yy_comp_nat_trans Tm Ty p Γ a)) ,pathsinv0,
  (pathscomp0(id_left _ )), ((maponpaths yy) (!(pr2 a))).
Qed.

Definition γ {Γ : C} {A : Ty Γ : hSet} (a : tm A) : (preShv C)⟦Yo Γ,Yo (Γ¤A)⟧
:= pr11((term_pullback A) (Yo Γ) (identity _) (yy a) (Subproof_γ a)).

Lemma  γ_pull {Γ : C} {A : Ty Γ : hSet} (a : tm A)
: γ a ;; yy (var A) = yy a.
Proof.
  exact (pr221((term_pullback _) (Yo _) (identity _) (yy _) (Subproof_γ _))).
Qed.

Lemma pull_γ {Γ : C} {A : Ty Γ : hSet} (a : tm A) : γ a ;; #Yo (pi A) = identity _.
Proof.
  apply pathsinv0, (pathscomp0(!(pr121 (term_pullback _
        (Yo Γ) (identity (Yo Γ)) (yy a)
        (Subproof_γ a))))); auto.
Qed.

Lemma γ_pi {Γ} {A : Ty Γ: hSet} (a : tm A) : Yo^-1 (γ a) ;; pi A = identity _.
Proof.
  assert (Yoeq : #Yo(Yo^-1 (γ a) ;; pi A) = #Yo(identity Γ)).
  -  apply (pathscomp0 (pr22 Yo _ _ _  _ _ )).
     apply pathsinv0 , (pathscomp0 (pr12 Yo _)).    
     assert (simplman : identity (pr1 (yoneda C (homset_property C)) Γ) 
     = identity (Yo Γ)) by auto.
     apply (pathscomp0 simplman).
     rewrite (!(pull_γ a)).
     apply cancel_postcomposition.
     assert (simplman2 : # (pr1 (yoneda C (homset_property C))) (Yo^-1 (γ a))
     = #Yo (Yo^-1 (γ a))) by auto.
     apply pathsinv0, (pathscomp0 simplman2), invyoneda.
  -  apply (maponpaths (Yo^-1) ) in Yoeq.
     rewrite yonedainv, yonedainv in Yoeq.
     exact Yoeq.
Qed.
Lemma γNat {Γ Δ : C} {A : Ty Γ : hSet} (f : C^op ⟦Γ,Δ⟧) (a : tm A)
: (f : C⟦Δ,Γ⟧) ;; (γ a : nat_trans _ _) Γ (identity Γ) =
  (γ (a ⌈f⌉) ;; #Yo (q A f) : nat_trans _ _) Δ (identity Δ).
Proof.
  assert (Yoγ : #Yo ((f : C⟦Δ,Γ⟧) ;; (γ a : nat_trans _ _) Γ (identity Γ)) =
  #Yo((γ (a ⌈f⌉) : nat_trans _ _) Δ (identity Δ) ;; q A f)).
  -  do 2 (rewrite (pr22 (yoneda C (pr21 C)) _ _ _); rewrite yonedacarac).
     refine (MorphismsIntoPullbackEqual (term_pullback A)
     (#Yo f ;; γ a) (γ (a ⌈f⌉) ;; #Yo (q A f)) _ _).
     --  rewrite <- assoc.
         eapply pathscomp0.
         *  rewrite (cancel_precomposition _ _ _ _ _ _ _
            (pr121((term_pullback _) (Yo Γ) (identity (Yo Γ)) (yy(a)) (Subproof_γ a )))).
            apply id_right.
         *  rewrite <- assoc.
            apply pathsinv0.
            eapply pathscomp0.
            **  rewrite (!(pr22 Yo _ _ _ (q A f) _)).
                rewrite (!(q_eq _ _)).
                rewrite (pr22 Yo _ _ _ _ f).
                rewrite assoc.
                rewrite  (cancel_postcomposition _ _ _
                (pr121 ((term_pullback _) (Yo Δ) (identity (Yo Δ))
                (yy(#Tm f a)) (Subproof_γ (a ⌈f⌉) )))).
                apply (pr1 (pr121 (preShv C)) _ (Yo Γ) (#Yo f)).
            **  reflexivity.
    --  rewrite <- assoc.
        apply (pathscomp0  (cancel_precomposition _ _ _ _ _ _ _
        (pr221((term_pullback _) (Yo Γ) (identity (Yo Γ)) (yy a) (Subproof_γ a ))))).
        rewrite <- assoc.
        rewrite (!(yy_natural _ _ _ _ (q A f))).
        rewrite compatibility_splTCwF.
        rewrite γ_pull.
        exact (!(yy_natural _ _ a _ f)).
  -  apply (transportyo Yoγ).
Qed.

Lemma γPullback1 {Γ : C} (A : Ty Γ : hSet)
: γ (var A) ;; #Yo (q A (pi A)) ;; yy(var A) = identity _;; yy (var A).
Proof.
  rewrite id_left.
  assert (γ (var A) ;; yy (var (A ⌊pi A⌋)) = yy(var A)) by apply (γ_pull (var A)).
  rewrite <- assoc, <- X.
  refine (cancel_precomposition _ _ _ _ _ _ _ _).
  rewrite X.
  rewrite (!(yy_natural _ _ (var A) _ _)).
  rewrite compatibility_splTCwF.
  reflexivity.
Qed.

Lemma  γPullback2 {Γ : C} (A : Ty Γ : hSet)
: γ (var A) ;; #Yo (q A (pi A)) ;; #Yo (pi A) = identity _;;(#Yo (pi A)).
Proof.       
  rewrite <- assoc.
  apply (pathscomp0 (!(cancel_precomposition _ _ _ _ _ _ (γ (var A)) (q_eq_yoneda _ _)))).
  rewrite assoc.
  apply (pathscomp0 (cancel_postcomposition _ _ _ (pull_γ _ ))).
  reflexivity.
Qed.



(** term wiew as sections*)
Definition tm_sec {Γ : C} (A : Ty Γ : hSet) := ∑ a : C⟦Γ,Γ¤A⟧, a ;; pi A = identity _ .

Coercion tm_sec_pr1 {Γ: C} (A : Ty Γ : hSet) : tm_sec A -> C⟦Γ,Γ¤A⟧ := pr1.

Definition tm_sec_property {Γ : C} {A : Ty Γ : hSet} (a : tm_sec A)
: a ;; pi A = identity _
:= pr2 a.

Section tm_equiv. 
(**equivalence between the possible definitions of term*)
Definition tm_map_1  {Γ: C} (A : Ty Γ : hSet) : tm A -> tm_sec A.
Proof.
  intro a ; exact (Yo^-1 (γ a),,γ_pi a).
Defined.

Definition tm_map_2  {Γ: C} (A : Ty Γ : hSet) : tm_sec A -> tm A.
Proof.
  intros [a  pa]; use tpair.
  -  exact (invmap (yy) (#Yo a;; yy(var A))).
  -  abstract (set (a' := invmap (yy) (#Yo a;; yy(var A))); simpl;
     assert (eqA : @yy _ (pr21 C) _ _ A = yy a' ;; p);
     [ apply (maponpaths (#Yo )) in pa;
        unfold a';
        rewrite homotweqinvweq;
        rewrite <- assoc;
        assert ( imp : #Yo (pi A);; yy A = yy(var A);;p) 
        by exact (Yo_var_commut _);
     apply (cancel_precomposition _ _ _ _ _ _ (#Yo a)) in imp;
     rewrite assoc in imp;
     assert (simplman : # Yo (a ;; pi A) =
     # (pr1 Yo) (a ;; pi A)) by auto;
     rewrite simplman in pa;
     rewrite (pr22 Yo _ _ _ a (pi A)) in pa;
     assert (simplman2 : # Yo a =
     # (pr1 Yo) a ) by auto;
     rewrite simplman2 in imp;
     assert (simplman3 : # Yo (pi A) =
     # (pr1 Yo) (pi A) ) by auto;
     rewrite simplman3 in imp;
     apply (cancel_postcomposition _ _ (yy A)) in pa;
     assert (lem : #Yo(identity _);; yy A = # Yo a ;; (yy (var A) ;; p));
      [ apply (pathscomp0 (!pa));
        exact imp
      | apply (pathscomp0 (!(@id_left (preShv C) _ _ (yy A))));
        assert (simplman4 : identity _ ;; yy A = #Yo(identity _);; yy A);
        [ assert (simplman5 : identity (Yo Γ) = identity ((pr1 Yo) Γ)) by auto;
           apply (cancel_postcomposition _ _ (yy A)) in simplman5;
           apply (pathscomp0 simplman5);
          apply cancel_postcomposition;
          exact (!(pr12 Yo _))
          | apply (pathscomp0 simplman4);
             exact lem]]
  | assert (eqa' : @yy _ (pr21 C) _ _ (p _ a') = yy a';;p)
     by (rewrite yy_comp_nat_trans; reflexivity);
     rewrite <- eqa' in eqA;
     apply (maponpaths (invmap yy)) in eqA;
     do 2 rewrite homotinvweqweq in eqA;
     exact (!eqA)]).
Defined.

Lemma tm_map_12 {Γ: C} (A : Ty Γ : hSet) : ∏ a : tm A, tm_map_2 A (tm_map_1 A a) = a.
Proof.
intro a;
apply subtypePath.
- intro x; exact (setproperty (Ty Γ : hSet) _ _).
- assert (eqa : invmap yy (# (yoneda C (homset_property C)) (Yo^-1 (γ a)) ;; yy (var A)) = a)
   by (rewrite invyoneda,γ_pull, homotinvweqweq; reflexivity);  exact eqa.
Qed.

Lemma tm_map_21 {Γ: C} (A : Ty Γ : hSet) : ∏ a : tm_sec A, tm_map_1 A (tm_map_2 A a) = a.
Proof.
intro a;
apply subtypePath.
- intro x; apply (pr21 C).
- assert (eqa : (Yo^-1 (γ (invmap yy (# (yoneda C (homset_property C)) (pr1 a) ;; yy (var A)),,
    tm_map_2_subproof Γ A (pr1 a) (pr2 a)))) = a).
  rewrite <- (yonedainv a) ; apply maponpaths.
  refine (MorphismsIntoPullbackEqual _ _ _ _ _).
  -- exact (pr22(make_Pullback (yy A) p (yoneda C (homset_property C) (Γ¤A))
        (# (yoneda C (homset_property C)) (pi A)) (yy (var A))
        (Yo_var_commut _) (term_pullback A))).
  --  assert (eqpiA : pr121 (make_Pullback (yy A) p
      (yoneda C (homset_property C) (Γ¤A))
      (# (yoneda C (homset_property C)) 
      (pi A)) (yy (var A)) (Yo_var_commut _)
      (term_pullback A)) = #Yo(pi A)) by auto. 
      rewrite eqpiA.
      apply (pathscomp0 (pull_γ _)).
      assert (simplman2 : # Yo a = # (pr1 Yo) a ) by auto;
      rewrite simplman2;
      assert (simplman3 : # Yo (pi A) = # (pr1 Yo) (pi A) ) by auto;
      rewrite simplman3;
      assert (simplman4 : identity(Yo Γ) = identity((pr1 Yo) Γ)) by auto;
      rewrite simplman4.
      apply (pathscomp0 (!(pr12 Yo _))).
      apply pathsinv0.
      apply (pathscomp0  (!(pr22 Yo _ _ _ a (pi A)))).
      apply maponpaths. exact (pr2 a).
  --  assert (eqteA : pr221 (make_Pullback (yy A) p
      (yoneda C (homset_property C)
      (Γ¤A)) (# (yoneda C (homset_property C))
      (pi A)) (yy (var A)) (Yo_var_commut _)
      (term_pullback A)) = yy(var A)) by auto.
      rewrite eqteA.
      rewrite γ_pull.
      apply homotweqinvweq.
  -- exact eqa.
Qed.

Definition tm_equiv {Γ: C} {A : Ty Γ : hSet} : tm A ≃ tm_sec A := 
  (tm_map_1 _,,
  gradth (tm_map_1 _) (tm_map_2 _) (tm_map_12 _) (tm_map_21 _)).

Coercion tm_equiv_coer {Γ: C} {A : Ty Γ : hSet} (a : tm A) : tm_sec A := tm_equiv a.

End tm_equiv.

End term_subtitution.

Section splTCwF_lemmas.

Section comp_ext.

Definition comp_ext_compare 
{Γ : C} {A A' : Ty Γ : hSet} (e : A = A')
: iso (Γ ¤ A) (Γ ¤ A')
:= idtoiso (maponpaths (ext Γ) e).

Lemma comp_ext_compare_id 
{Γ : C} (A : Ty Γ : hSet)
: (comp_ext_compare (idpath A) : _ --> _) = identity (Γ¤A).
Proof.
  apply idpath.
Qed.

Lemma comp_ext_compare_id_general 
{Γ : C} {A : Ty Γ : hSet} (e : A = A)
: (comp_ext_compare e : _ --> _) = identity (Γ ¤ A).
Proof.
  apply @pathscomp0 with (comp_ext_compare (idpath _)).
  - apply maponpaths, maponpaths, (setproperty (Ty Γ : hSet)).
  - apply idpath.
Qed.

Lemma comp_ext_compare_comp 
{Γ : C} {A A' A'' : Ty Γ : hSet} (e : A = A') (e' : A' = A'')
: (comp_ext_compare (e @ e') : _ --> _)
= comp_ext_compare e ;; comp_ext_compare e'.
Proof.
  apply pathsinv0.
  etrans. { apply idtoiso_concat_pr. }
  unfold comp_ext_compare. apply maponpaths, maponpaths.
  apply pathsinv0, maponpathscomp0.
Qed.

Lemma comp_ext_compare_irrelevant 
{Γ : C} {A A' : Ty Γ : hSet} (e e' : A = A')
: (comp_ext_compare e : _ --> _) = comp_ext_compare e'.
Proof.
  apply maponpaths, maponpaths,(setproperty (Ty Γ : hSet)).
Qed.


End comp_ext.

Lemma q_typeeq {Γ:C}
{A A' : Ty Γ : hSet} (e : A = A')
{Δ : C} (f : C^op ⟦Γ,Δ⟧)
: comp_ext_compare (maponpaths (fun X => X ⌊f⌋) e) ;; q A' f
= q A f ;; comp_ext_compare e.
Proof.
  destruct e; cbn.
  rewrite id_right; apply id_left.
Qed.

Definition q_mapeq 
{Γ Δ} {f f' : C^op ⟦Γ,Δ⟧} (e : f = f') (A : Ty Γ : hSet)
: comp_ext_compare (maponpaths _ e)
  ;; q A f'
= q A f.
Proof.
  destruct e; apply id_left.
Qed.

Definition q_q
  : ∏ Γ  Γ' Γ''  (f : C^op ⟦Γ,Γ'⟧)  (g : C^op ⟦Γ',Γ''⟧) (A : Ty Γ : hSet),
            q A (f;;g)
            =  idtoiso (maponpaths (fun b => Γ''¤b) (!compose_ty  A f g))
               ;; q (A ⌊f⌋) g
               ;; q A f.
Proof. 
  intros.
  apply (pathscomp0 ((pr22 (qq_structure_of_splTCwF C)) _ _ _ _ _ _)).
  do 2 apply cancel_postcomposition.
  cbn.
  assert (eq : 
  (toforallpaths (λ _ : Ty Γ : hSet, Ty Γ'' : hSet) (# Ty (f;;g))
        (λ x : Ty Γ : hSet, # Ty g (# Ty f x)) (functor_comp Ty f g) A) =
        (! compose_ty A f g)) by apply (setproperty (Ty _ : hSet)).
  assert (eq2 : maponpaths (λ b : Ty Γ'' : hSet, ext Γ'' b) (! compose_ty A f g) =
  maponpaths (λ A0 : Ty Γ'' : hSet, Γ''¤A0)
  (toforallpaths (λ _ : Ty Γ : hSet, Ty Γ'' : hSet) (# Ty (f;;g))
  (λ x : Ty Γ : hSet, # Ty g (# Ty f x)) (functor_comp Ty f g) A)) by (induction eq; reflexivity).
  apply pathsinv0.
  apply (maponpaths idtoiso) in eq2.
  eapply pathscomp0.
  exact (maponpaths pr1 eq2).
  reflexivity.
Qed.

Definition q_q' 
: ∏ Γ (A : Ty Γ : hSet) Γ' (f : C^op ⟦Γ,Γ'⟧) Γ'' (g : C^op ⟦Γ',Γ''⟧),
  q (A ⌊f⌋) g ;; q A f
  = idtoiso (maponpaths (fun b => Γ''¤b) (compose_ty A f g))
    ;; q A (f;;g).
Proof.
intros. apply iso_inv_to_left, pathsinv0. 
etrans. { apply q_q. }
repeat rewrite <- assoc; apply maponpaths_2.
etrans. 2: { apply comp_ext_compare_inv. }
apply comp_ext_compare_irrelevant.
Qed.

End splTCwF_lemmas.

Section tm_lemmas.

Definition tm_transportf {Γ} {A A' : Ty Γ : hSet} (e : A = A')
: tm A ≃ tm A'.
Proof.
  use weqbandf.
  -  exact (idweq (Tm Γ : hSet)).
  -  induction e; intro x; exact (idweq _).
Defined.

Definition tm_transportb {Γ} {A A' : Ty Γ : hSet} (e : A = A')
: tm A' ≃ tm A := invweq(tm_transportf e).

Lemma tm_transportf_idpath {Γ} {A : Ty Γ : hSet} (t : tm A)
: tm_transportf (idpath A) t = t.
Proof.
  reflexivity.
Qed.

Lemma tm_transportf_idpath_gen {Γ} {A : Ty Γ : hSet} (t : tm A) (e : A = A)
: tm_transportf e t = t.
Proof.
  assert (eqe : e = idpath A) by apply (setproperty (Ty Γ : hSet)).
  rewrite eqe.
  exact (tm_transportf_idpath _).
Qed.

Lemma tm_transportb_idpath {Γ} {A : Ty Γ : hSet} (t : tm A)
: tm_transportb (idpath A) t = t.
Proof.
  reflexivity.
Qed.

Lemma tm_transportbf {Γ} {A A' : Ty Γ : hSet} (e : A = A') : tm_transportb e = tm_transportf (!e).
Proof.
  induction e.
  refine (subtypePath isapropisweq _).
  apply (idpath _).
Qed.

Lemma reind_compose_tm
{Γ Γ' Γ'' : C} (f : C⟦Γ',Γ⟧) (g : C⟦Γ'',Γ'⟧) {A : Ty Γ : hSet} (a : tm A)
: a ⌈g ;; f⌉ 
= tm_transportb (Ty_composition _ _ _) (a ⌈f⌉ ⌈g⌉).
Proof.
  apply subtypePath. 
  -  intro x; apply (setproperty (Ty Γ'' : hSet)).
  -  rewrite tm_transportbf; apply Tm_composition.
Qed.

Lemma maponpaths_2_reind_tm 
{Γ Γ' : C} {f f' : C⟦Γ',Γ⟧} (e : f = f') {A : Ty Γ : hSet} (a : tm A)
: a ⌈f⌉ = tm_transportb (maponpaths (fun g => #Ty g A) e) (a ⌈f'⌉).
Proof.
  induction e.
  rewrite maponpaths_eq_idpath; [|apply idpath].
  now rewrite tm_transportb_idpath.
Qed.

Lemma tm_transportf_compose {Γ : C} {A A' A'' : Ty Γ : hSet} (e : A = A')
(e' : A' = A'') (a : tm A) 
: tm_transportf (e @ e') a = tm_transportf e' (tm_transportf e a).
Proof.
  induction e; induction e'.
  reflexivity.
Qed.

Lemma tm_transportf_irrelevant {Γ} {A A' : Ty Γ : hSet} (e e' : A = A')
(t : tm A)
: tm_transportf e t = tm_transportf e' t.
Proof.
  apply (maponpaths (fun e => tm_transportf e t)).
  apply (setproperty (Ty Γ : hSet)).
Qed.

Lemma tm_transport_compose {Γ Γ' Γ'' : C} (f : C⟦Γ',Γ⟧) (g : C⟦Γ'',Γ'⟧) (A : Ty Γ : hSet) (a : tm A)
: tm_transportf ((Ty_composition g f A)) (a ⌈g;;f⌉) = a ⌈f⌉ ⌈g⌉.
Proof.
  rewrite reind_compose_tm.
  rewrite tm_transportbf.
  rewrite <- tm_transportf_compose ,pathsinv0l.
  reflexivity.
Qed.

Lemma tm_transportf_bind {Γ} {A A' A'': Ty Γ : hSet} {e : A' = A} {e' : A'' = A'}
{t} {t'} {t''} (ee : t = tm_transportf e t') (ee' : t' = tm_transportf e' t'')
: t = tm_transportf (e' @ e) t''.
Proof.
  etrans. 2: { apply pathsinv0, tm_transportf_compose. }
  etrans. { eassumption. }
  apply maponpaths; assumption.
Qed.
Definition tm_transportb_unfold
{Γ} {A A' : Ty Γ : hSet} (e : A = A') (a : tm A')
: (tm_transportb e a : _ --> _)
= a ;; comp_ext_compare (!e).
Proof.
  induction e.
  rewrite comp_ext_compare_id_general.
  rewrite tm_transportbf.
  rewrite tm_transportf_idpath_gen.
  apply (!(id_right _)).
Qed.

Definition tm_transportb_unfold_alter
{Γ} {A A' : Ty Γ : hSet} (e : A = A') (a : tm A')
: (tm_transportb e a : _ --> _) ;; comp_ext_compare (e)
= a .
Proof.
  rewrite tm_transportb_unfold, <- assoc, (!(comp_ext_compare_comp _ _)), comp_ext_compare_id_general, id_right.
  reflexivity.
Qed.

Lemma reind_compose_tm' 
{Γ Γ' Γ'' : C} (f : C⟦Γ',Γ⟧) (g : C⟦Γ'',Γ'⟧) {A : Ty Γ : hSet} (a : tm A)
: tm_transportf (Ty_composition _ _ _) (a ⌈g;;f⌉) = a ⌈f⌉ ⌈g⌉.
Proof.
  rewrite reind_compose_tm. rewrite tm_transportbf.
  now rewrite <- tm_transportf_compose, pathsinv0l, tm_transportf_idpath.
Qed.

Lemma reind_id_tm {Γ : C}{A : Ty Γ : hSet} (a : tm A)
: a ⌈identity _⌉
= tm_transportb ((toforallpaths _ _ _ (pr12 Ty _ )) A) a.
Proof.
  apply subtypePath. 
  -  intros x. apply (setproperty (Ty Γ : hSet)).
  -  apply ((toforallpaths _ _ _ (pr12 Tm _ )) a).
Qed.

Lemma reind_id_tm' {Γ : C} {A : Ty Γ : hSet}  (a : tm A) (b : tm A)
(e : A ⌊identity Γ⌋ = A ⌊b ;; pi A⌋) 
: tm_transportf e (a ⌈identity _⌉)
= tm_transportf ((Ty_identity _) @ e) a.
Proof.
  apply subtypePath.  
  -  intros x. apply (setproperty (Ty Γ : hSet)).
  -  apply ((toforallpaths _ _ _ (pr12 Tm _ )) a).
Qed.

Section term_subtitution_lemmas.

Definition γ_qq {Γ} {A : Ty Γ: hSet} {Γ'} (f : C⟦Γ',Γ⟧) (a : tm (A ⌊f⌋)) : C⟦Γ',Γ¤ A⟧ := (a ;; q A f).    

Lemma γ_a  {Γ} {A : Ty Γ : hSet} (a : tm A) : #Yo a = γ a.
Proof.
  assert (eq : Yo^-1(γ a) = a) by auto.
  rewrite (!eq).
  apply invyoneda.
Qed.

Lemma Ty_γ_id {Γ : C} {A : Ty Γ : hSet} (a : tm A) 
: A ⌊pi A⌋ ⌊a⌋ = A.
Proof.
  simple refine (!(Ty_composition _ _ _) @ _).
  apply (pathscomp0 ((toforallpaths  _ _ _ (maponpaths _ (γ_pi _)) )A)).
  apply ((toforallpaths _ _ _ (pr12 Ty _ )) A).
Qed.

Lemma var_subtitution {Γ} {A : Ty Γ : hSet} (a : tm A) : #Tm a (var A) = a.
Proof.
  assert (inter : @yy _ (pr21 C) _ _ (#Tm a (var A)) = yy a). 
  -  assert (eqa : Yo^-1 (γ a) = a ) by auto. 
     rewrite (!eqa), yy_natural, invyoneda. 
     exact (pr221((term_pullback _) (Yo _) (identity _) (yy _) (Subproof_γ _))).
  -  apply (maponpaths (invmap yy) ) in inter.
     do 2 rewrite homotinvweqweq in inter.
     exact inter.
Qed.

Lemma reind_tm_q {Γ Δ} (f : C^op ⟦Γ,Δ⟧)
{A : Ty Γ : hSet} (a : tm A)
: a ⌈f⌉ ;; q A f = (f : C⟦Δ,Γ⟧) ;; a.
Proof.
  assert (eqYo : #Yo(a ⌈f⌉ ;; q A f) = #Yo((f : C⟦Δ,Γ⟧) ;; a)).
  -  simple refine (MorphismsIntoPullbackEqual
     (pr22(make_Pullback (yy A) p
     (yoneda C (pr21 C) (Γ¤A))
     (# (yoneda C (pr21 C)) (pi A))
     (yy (var A))
     (Yo_var_commut _)
     (term_pullback A)))
     (#Yo(a ⌈f⌉ ;; q A f)) (#Yo((f : C⟦Δ,Γ⟧) ;; a)) _ _).
     *  assert (triv : pr121 
        (make_Pullback (yy A) p (yoneda C (pr21 C) (ext Γ A))
        (# (yoneda C (pr21 C)) (pi A)) (yy (var A)) (Yo_var_commut A) 
        (term_pullback A)) = #Yo(pi A)) by auto.
        rewrite triv.
        rewrite (pr22 Yo _ _ _  _ a).
        rewrite (pr22 Yo _ _ _  _ (q A f)).
        do 2 rewrite <- assoc.
        rewrite (!(q_eq_yoneda _ _)).
        do 2 rewrite γ_a.
        rewrite assoc.
        do 2 rewrite pull_γ.
        rewrite id_left,id_right.
        reflexivity.
     *  assert (triv : pr221 
        (make_Pullback (yy A) p (yoneda C (pr21 C) (ext Γ A))
        (# (yoneda C (pr21 C)) (pi A)) (yy (var A)) (Yo_var_commut A) 
        (term_pullback A)) = @yy _ (pr21 C) _ _ (var A)) by auto.
        rewrite triv.
        rewrite (pr22 Yo _ _ _  _ a).
        rewrite (pr22 Yo _ _ _  _ (q A f)).
        do 2 rewrite <- assoc.
        assert (evidq : # (pr1 Yo) (q A f) = # Yo (q A f) ) by auto;
        rewrite evidq;
        assert (evida : # (pr1 Yo) a = # (@yoneda _ (pr21 C)) a ) by auto;
        rewrite evida.
        eapply pathscomp0.
        exact (cancel_precomposition _ _ _ _ _ _ _ (!(yy_natural _ _ (var A) _ (q A f)))).
        apply pathsinv0.
        eapply pathscomp0.
        exact (cancel_precomposition _ _ _ _ _ _ _ (!(yy_natural _ _ (var A) _ a))).
        rewrite compatibility_splTCwF.
        rewrite var_subtitution.
        assert (evidf : # (pr1 Yo) f = # Yo f) by auto;
        rewrite evidf;
        eapply pathscomp0.
        exact (!(yy_natural _ _ a _ f)).
        assert (evidfa : # (pr1 Yo) (a ⌈f⌉) = # Yo (a ⌈f⌉)) by auto;
        rewrite evidfa;
        apply pathsinv0.
        eapply pathscomp0.
        exact (!(yy_natural _ _ _ _ (a ⌈f⌉))).
        rewrite var_subtitution.
        reflexivity.
  - apply transportyo. exact eqYo.
Qed.

End term_subtitution_lemmas.

End tm_lemmas.

Section Familly_Of_Types.

Definition DepTypesType {Γ : C} {A : Ty Γ : hSet} (B : Ty(Γ¤A) : hSet)
(a : tm A)
: Ty Γ : hSet := ( γ a;;yy B : nat_trans _ _) Γ (identity Γ).

Lemma DepTypesType_eq {Γ : C} {A : Ty Γ : hSet} (B : Ty(Γ¤A) : hSet)
(a : tm A) : DepTypesType B a =  B ⌊a⌋.
Proof. 
  reflexivity.
Qed.

Definition DepTypesElem_pr1 {Γ : C} {A : Ty Γ : hSet} {B : Ty(Γ¤A) : hSet}
(b : tm B) (a : tm A) 
: Tm Γ : hSet := (γ a;;yy b : nat_trans _ _) Γ (identity Γ).

Lemma DepTypesComp {Γ : C} { A : Ty Γ : hSet} {B : Ty(Γ¤A) : hSet}
(b : tm B) (a : tm A)
: p Γ (DepTypesElem_pr1 b a) = DepTypesType B a.
Proof.
  apply pathsinv0,(pathscomp0(maponpaths _ (!(pr2 b)))),pathsinv0.
  apply (toforallpaths _ _ _ (pr2 p _ _ _) b).
Qed.

Definition DepTypesElems {Γ : C} { A : Ty Γ : hSet} {B : Ty(Γ¤A) : hSet}
(b : tm B) (a : tm A)
: tm (DepTypesType B a) := DepTypesElem_pr1 b a ,, DepTypesComp b a.

Lemma DepTypesElems_eq {Γ : C} { A : Ty Γ : hSet} {B : Ty(Γ¤A) : hSet}
(b : tm B) (a : tm A) 
: DepTypesElems b a = b ⌈a⌉.
Proof.
  use subtypePath.
  -  intro x; apply (setproperty (Ty Γ : hSet)).
  - cbn.
    assert (eqγ : (yoneda_map_1 C (homset_property C) Γ
    (yoneda_objects C (homset_property C) (ext Γ A)) 
    (γ a)) = Yo^-1 (γ a)) by auto;
    rewrite eqγ;
    rewrite invyonedacarac.
    reflexivity.
Qed.

Lemma DepTypesNat {Γ Δ : C} {A : Ty Γ : hSet} (B : Ty (Γ¤ A) : hSet)
(f : C^op ⟦Γ,Δ⟧) (a : tm A)
: #Ty f (DepTypesType B a) = DepTypesType (#Ty (q A f) B) (reind_tm f a).
Proof.
  unfold DepTypesType, reind_tm; rewrite yy_natural, assoc.
  assert (Fucn : (# (pr1 Ty) ((γ a :nat_trans _ _) Γ (identity Γ)) ;; # (pr1 Ty) f) B =
  # Ty f (# Ty ((γ a :nat_trans _ _) Γ (identity Γ)) B)) by auto.
  apply (pathscomp0 (!Fucn)),(pathscomp0(!((toforallpaths _ _ _  
  ((pr22 Ty) _ _ _ ((γ a: nat_trans _ _) Γ (identity Γ) : C⟦Γ,Γ¤A⟧) f)) B))), 
  (pathscomp0(toforallpaths _ _ _ (maponpaths (# Ty) (γNat f a)) B)).
  reflexivity.
Qed.

Lemma DepTypesNat_bis {Γ Δ : C} {A : Ty Γ : hSet} (B : Ty (Γ¤ A) : hSet)
(f : C ⟦Δ,Γ⟧) (a : tm A)
: B ⌊a⌋ ⌊f⌋ = B ⌊q A f⌋ ⌊a ⌈f⌉⌋.
Proof.
  exact (DepTypesNat _ _ _).
Qed.

Lemma DepTypesEta {Γ : C} {A : Ty Γ : hSet} (B : Ty (Γ¤A) : hSet)
: DepTypesType (B ⌊q A (pi A)⌋) (var A) = B.
Proof.
  assert (Natu : @γ (Γ¤A) (A ⌊pi A⌋) (var A) ;; yy (B ⌊q A (pi A)⌋)
  = @γ (Γ¤A) (#Ty (pi A) A) (var A) ;; #Yo (q A (pi A)) ;; 
  (@yy C (pr21 C) Ty (Γ¤A)) B).
  -  rewrite (cancel_precomposition _ _ _ _ (yy (B ⌊q A (pi A)⌋))
     (#Yo (q A (pi A));; yy B) _).
     *  rewrite assoc; reflexivity.
     *  unfold reind_ty; rewrite yy_natural; reflexivity.
  -  assert (Id: @γ (Γ¤A) (# Ty (@pi Γ A) A) (var A) ;; #Yo (q A (pi A))
     = identity _).
     *  refine (MorphismsIntoPullbackEqual
        (pr22(make_Pullback (yy A) p
        (yoneda C (homset_property C) (Γ¤A))
        (# (yoneda C (homset_property C)) (pi A))
        (yy (var A))
        (Yo_var_commut _)
        (term_pullback A)))
        (γ (var A) ;; #Yo (q A (pi A))) (identity _) (γPullback2 A) (γPullback1 A)).
     *  rewrite Id, (id_left _) in Natu.
        unfold DepTypesType.
        rewrite Natu; exact (!(yyidentity B)).
Qed.

Lemma DepTypesEta_bis {Γ : C} {A : Ty Γ : hSet} (B : Ty (Γ¤A) : hSet)
: B ⌊q A (pi A)⌋ ⌊var A⌋ = B.
Proof.
  exact (DepTypesEta _).
Qed.

Lemma DepTypesrewrite {Γ : C} {A : Ty Γ : hSet} (B : Ty (Γ¤A) : hSet)
(a b : tm A) (e : pr1 a = pr1 b)
: DepTypesType B a = DepTypesType B b.
Proof.
  destruct a as [a pa]; destruct b as [b pb].
  cbn in e; induction e.
  assert (ProofIrr : pa = pb) by apply (setproperty( Ty Γ : hSet)).
  rewrite ProofIrr.
  reflexivity.
Qed.

Lemma DepTypesrewrite_bis {Γ : C} {A : Ty Γ : hSet} (B : Ty (Γ¤A) : hSet)
(a b : tm A) (e : pr1 a = pr1 b)
: B ⌊a⌋ = B ⌊b⌋.
Proof.
  do 2 rewrite (!(DepTypesType_eq _ _)).
  exact (DepTypesrewrite _ _ _ e).
Qed.

End Familly_Of_Types.

Section Pi_structure.

Definition PiTypeFormer : UU 
:= ∏ (Γ : C) (A : Ty Γ : hSet) (B : Ty (Γ¤A) : hSet), (Ty Γ : hSet).

Definition PiTypeNat (π : PiTypeFormer) : UU 
:= ∏ (Γ Δ : C) (f : C^op ⟦Γ,Δ⟧) (A : Ty Γ : hSet) (B : Ty(Γ¤A) : hSet),
  (π _ A B) ⌊f⌋  = π _ (A ⌊f⌋) (B ⌊q A f⌋).

Definition pi_form_struct : UU
:= ∑ pi : PiTypeFormer, PiTypeNat pi.

Definition pr1_PiFormer (π : pi_form_struct) : PiTypeFormer := pr1 π.
Coercion pr1_PiFormer : pi_form_struct >-> PiTypeFormer.

Lemma ppComp3 {Γ Δ : C} {A : Ty Γ : hSet} (f : C^op ⟦Γ,Δ⟧) {π : PiTypeFormer}
(nπ : PiTypeNat π) {B : Ty (Γ¤A) : hSet} (c : tm (π _ A B))
: p _ (c ⌈f⌉)  = (π Δ (A ⌊f⌋) (B ⌊q A f⌋)).
Proof.
  apply pathsinv0, (pathscomp0(!(nπ _ _ f A B))),
  (pathscomp0(!(maponpaths (# Ty f) (pr2 c)))),
   pathsinv0, (toforallpaths _ _ _ (pr2 p _ _ _) c) .
Qed.

Definition PiAbs (π : PiTypeFormer): UU
:= ∏ (Γ : C) (A : Ty Γ : hSet) (B : Ty (Γ¤A) : hSet) (b : tm B), tm (π _ A B) .

Definition PiAbsNat (π : PiTypeFormer) (nπ : PiTypeNat π) (Λ : PiAbs π) 
: UU := ∏ (Γ Δ : C) (f : C^op ⟦ Γ, Δ ⟧) (A : Ty Γ : hSet)
(B : Ty (Γ ¤ A) : hSet) (b : tm B), (Λ Γ A B b) ⌈f⌉ =
tm_transportf (! (! ppComp1 f (Λ Γ A B b) @ ppComp3 f nπ (Λ Γ A B b)))
(Λ Δ (A ⌊f⌋) (B ⌊q A f⌋) (b ⌈q A f⌉)).

Definition Pi_intro_struct (π : pi_form_struct) : UU
:= ∑ Λ : PiAbs π, PiAbsNat π (pr2 π) Λ.

Definition PiApp (π : PiTypeFormer) : UU
:= ∏ (Γ : C) (A : Ty Γ : hSet) (B : Ty(Γ¤A) : hSet) (c : tm (π _ A B)) (a : tm A),
tm (B ⌊a⌋).

Definition PiAppNat  (π : PiTypeFormer) (nπ : PiTypeNat π) (app : PiApp π) : UU
:= ∏ (Γ Δ : C) (f : C^op ⟦Γ,Δ⟧) (A : Ty Γ : hSet) (B : Ty(Γ¤A) : hSet) (c : tm (π _ A B)) (a : tm A),
reind_tm f (app _ _ _ c a) = (tm_transportf  (!(DepTypesNat_bis B f a))
(app _ (A ⌊f⌋) (B ⌊q A f⌋) (tm_transportf (nπ _ _ f A B) (c ⌈f⌉)) (a ⌈f⌉))).

Definition Pi_app_struct (π : pi_form_struct) : UU 
:= ∑ app : PiApp π, PiAppNat π (pr2 π) app.

Definition PiAppAbs (π : PiTypeFormer) (Λ : PiAbs π) (app : PiApp π)
:= ∏ Γ ( A : Ty Γ : hSet) (B : Ty(Γ¤A) : hSet) (b : tm B) (a : tm A),
app _ _ _ (Λ _ A _ b) a = b⌈a⌉.

Definition Pi_comp_struct (π : pi_form_struct)
(lam : Pi_intro_struct π) (app : Pi_app_struct π) : UU
:= PiAppAbs π (pr1 lam) (pr1 app).

Definition PiAbsAppComp (π : PiTypeFormer) (nπ : PiTypeNat π)
(Λ : PiAbs π) (app : PiApp π) 
: UU
:= ∏ (Γ : C) (A : Ty Γ: hSet) (B : Ty (Γ ¤ A) : hSet) (c : tm (π Γ A B)),
c = Λ Γ A B (tm_transportf (DepTypesEta_bis B)
(app (Γ ¤ A) (A ⌊pi A⌋) (B ⌊q A (pi A)⌋)
(tm_transportf (nπ Γ (Γ ¤ A) (pi A) A B) (reind_tm (pi A) c)) (var A))).

End Pi_structure.

Section Sigma_structure.

Definition SigTypeFormer : UU 
:= ∏ (Γ : C) (A : Ty Γ : hSet) (B : Ty (Γ¤A) : hSet), Ty Γ : hSet.

Definition SigTypeNat (σ : SigTypeFormer) : UU 
:= ∏ (Γ Δ : C) (f : C^op ⟦Γ,Δ⟧) (A : Ty Γ : hSet) (B : Ty(Γ¤A) : hSet),
(σ _ A B) ⌊f⌋ = σ _ (A ⌊f⌋) (B  ⌊q A f⌋).

Definition SigAbs (σ : SigTypeFormer) : UU 
:= ∏ (Γ : C) (A : Ty Γ : hSet) (B : Ty(Γ¤A) : hSet) (a : tm A)
(b : tm (B ⌊a⌋) ), tm (σ _ A B).

Definition CwF_SigAbsNat (σ : SigTypeFormer) (nσ : SigTypeNat σ)
(pair : SigAbs σ) 
: UU := ∏ (Γ Δ : C) (f : C^op ⟦ Γ, Δ ⟧) (A : Ty Γ : hSet) (B : Ty (Γ ¤ A) : hSet)
(a : tm A) (b : tm (B ⌊a⌋)), (pair Γ A B a b) ⌈f⌉=
tm_transportf (! nσ Γ Δ f A B)
(pair Δ (A ⌊f⌋) (B  ⌊q A f⌋) (a ⌈f⌉)
(tm_transportf (DepTypesNat B f a) (b ⌈f⌉))).

Definition SigPr1 (σ : SigTypeFormer) : UU
:= ∏ Γ (A : Ty Γ : hSet) (B : Ty(Γ¤A) : hSet) (c: tm (σ _ A B)), tm A.

Definition SigPr1Nat (σ : SigTypeFormer) (nσ : SigTypeNat σ) (p1 : SigPr1 σ) : UU 
:= ∏ (Γ Δ : C)  (f : C^op ⟦Γ,Δ⟧) (A : Ty Γ : hSet) (B : Ty(Γ¤A) : hSet) (c : tm (σ _ A B)),
(p1 _ _ _ c) ⌈f⌉= 
p1 _ (A ⌊f⌋) (B  ⌊q A f⌋) (tm_transportf (nσ _ _ f _ _) (c ⌈f⌉)).
 
Definition SigPr2 (σ : SigTypeFormer) (p1 : SigPr1 σ) :UU
:= ∏ Γ (A : Ty Γ : hSet) (B : Ty(Γ¤A) : hSet)
(c : tm (σ _ A B) ), tm (B ⌊(p1 _ _ _ c)⌋).

Definition SigPr2Nat (σ : SigTypeFormer) (nσ : SigTypeNat σ) (p1 : SigPr1 σ)
(np1 : SigPr1Nat σ nσ p1) (p2 : SigPr2 σ p1) 
: UU := ∏ (Γ Δ : C) (f : C^op ⟦ Γ, Δ ⟧) (A : Ty Γ : hSet) (B : Ty (Γ¤A) : hSet)
(c : tm (σ Γ A B)),
(p2 Γ A B c) ⌈f⌉ = tm_transportf (! DepTypesNat B f (p1 Γ A B c))
(tm_transportf (DepTypesrewrite (B  ⌊q A f⌋)
(p1 Δ (A ⌊f⌋) (B  ⌊q A f⌋) (tm_transportf (nσ Γ Δ f A B) (c ⌈f⌉)))
((p1 Γ A B c) ⌈f⌉) (maponpaths pr1 (! np1 Γ Δ f A B c)))
(p2 Δ (A ⌊f⌋) (B  ⌊q A f⌋) (tm_transportf (nσ Γ Δ f A B) (c ⌈f⌉)))).

Definition SigAbsPr1 (σ : SigTypeFormer) (pair : SigAbs σ) (p1 : SigPr1 σ)
: UU := ∏ Γ (A : Ty Γ : hSet) (B : Ty(Γ¤A) : hSet) (a : tm A) (b : tm (B ⌊a⌋)),
p1 _ _ _ (pair _  _ _ a b) = a.

Definition SigAbsPr2 (σ : SigTypeFormer) (pair : SigAbs σ) (p1 : SigPr1 σ)
(p2 : SigPr2 σ p1) (Ap1 : SigAbsPr1 σ pair p1)
: UU := ∏ (Γ : C^op) (A : Ty Γ : hSet) (B : Ty (Γ ¤ A) : hSet)
(a : tm A) (b : tm (B ⌊a⌋)),
b = tm_transportf
(DepTypesrewrite B (p1 Γ A B (pair Γ A B a b)) a (maponpaths pr1 (Ap1 Γ A B a b)))
(p2 Γ A B (pair Γ A B a b)).

Definition SigAbsPr (σ : SigTypeFormer) (pair : SigAbs σ)
(p1 : SigPr1 σ) (p2 : SigPr2 σ p1) : UU
:= ∏ Γ (A : Ty Γ : hSet) (B : Ty(Γ¤A) : hSet) (c : tm (σ _ A B)),
pair _ _ _ (p1 _ _ _ c) (p2 _ _ _ c ) = c.

End Sigma_structure.

Section Identity_Structure.

Definition IdTypeFormer : UU 
:= ∏ (Γ : C) (A : Ty Γ : hSet) (a b : tm A), Ty Γ : hSet.

Definition IdTypeNat (id : IdTypeFormer) : UU 
:= ∏ (Γ Δ : C) (f : C^op ⟦Γ,Δ⟧) (A : Ty Γ : hSet) (a b : tm A),
(id _ A a b) ⌊f⌋  = id _ (A ⌊f⌋) (a ⌈f⌉) (b ⌈f⌉).

Definition IdRefl (Id : IdTypeFormer) : UU 
:= ∏ Γ (A : Ty Γ :hSet) (a : tm A), tm (Id _ _ a a).

Definition IdReflNat (Id : IdTypeFormer) (nid : IdTypeNat Id)
(refl : IdRefl Id) : UU
:= ∏ (Γ Δ : C) (f : C^op ⟦Γ,Δ⟧) (A : Ty Γ : hSet) (a : tm A),
(refl _ A a) ⌈f⌉ =
tm_transportf (!(nid _ _ f _ a a)) (refl _ (A ⌊f⌋) (a ⌈f⌉)).

Definition maponpathsIdForm {Id : IdTypeFormer}
{Γ} {A A'} (e_A : A = A')
{a} {a'} (e_a : a = tm_transportb e_A a')
{b} {b'} (e_b : b = tm_transportb e_A b')
: Id Γ A a b = Id Γ A' a' b'.
Proof.
  destruct e_A.
  rewrite (tm_transportbf _) in e_a, e_b;
   cbn in e_a, e_b.
  apply Auxiliary.maponpaths_12; assumption.
Qed.

Definition IdBasedFam (Id : IdTypeFormer) {Γ : C} (A : Ty Γ : hSet) (a : tm A)
: Ty (Γ¤A) : hSet := Id _ _ (a ⌈pi A⌉) (var A).

Definition IdBasedFamNatural (Id : IdTypeFormer) (nid : IdTypeNat Id)
{Γ Δ : C} (f : C^op ⟦Γ,Δ⟧) (A : Ty Γ : hSet) (a : tm A)
: (IdBasedFam Id A a) ⌊q A f⌋ = IdBasedFam Id _ (a ⌈f⌉).
Proof.
  unfold IdBasedFam.
  etrans.
  -  exact (nid _ _ (q A f) _ _ _).
  -  use maponpathsIdForm.
     --  refine (!(Ty_composition _ _ A) @ _).
         apply pathsinv0, (pathscomp0 (!(Ty_composition _ _ A))).
         refine ((toforallpaths _ _ _ _) A).
         exact (maponpaths _ (q_eq _ _)).
     --  etrans. {apply pathsinv0, tm_transport_compose. }
         etrans. 2: { apply maponpaths, tm_transport_compose. }
         etrans. 2: {rewrite tm_transportbf; apply  tm_transportf_compose. }
         etrans. {eapply maponpaths. refine (maponpaths_2_reind_tm _ _). 
         apply (!(q_eq _ _)). }
         etrans. { rewrite tm_transportbf; apply (!(tm_transportf_compose _ _ _)). }
         apply tm_transportf_irrelevant.
     --  apply subtypePath; [intro x; apply (setproperty (Ty _ : hSet))|
         rewrite tm_transportbf ;apply compatibility_splTCwF].
Qed.

Definition Id_map {Id} (nid : IdTypeNat Id) {Γ} {A : Ty Γ : hSet} (a : tm A) (b : tm A) (eqab : tm (Id _ _ a b))
: C⟦Γ,_¤IdBasedFam Id A a⟧.
Proof.
  simple refine (γ_qq b _). unfold IdBasedFam.
  simple refine (tm_transportb _ eqab).
  abstract(
  simple refine (nid  _ _ _ _ _ _ @ _);
  use maponpathsIdForm;
  [ apply Ty_γ_id
  | rewrite tm_transportbf ;
    refine (_ @ tm_transportf_irrelevant _ _ _);
    simple refine (tm_transportf_bind (!reind_compose_tm' _ _ _) _);
    [ apply (pathscomp0 (!(Ty_γ_id b))) , (!(Ty_composition _ _ _)) |
      simple refine (maponpaths_2_reind_tm _ _ @ _);
      [exact (identity _) | apply γ_pi |
      rewrite tm_transportbf; apply (pathscomp0 (reind_id_tm' _ _ _));
      apply tm_transportf_irrelevant ]]
  | apply subtypePath;
    [  intros x; apply (setproperty (Ty Γ : hSet))
     | rewrite tm_transportbf; apply var_subtitution]]).
Defined.

Definition id_intro_q {Id} (nid : IdTypeNat Id) 
{Γ Δ} (f : C^op ⟦Γ,Δ⟧) (A : Ty Γ : hSet) a b (eqab : tm (Id _ A a b)) 
(eqab' : tm (Id _ _ (a ⌈f⌉) (b ⌈f⌉)) := (tm_transportf (nid _ _ _ _ _ _) (eqab ⌈f⌉))) 
: (f : C⟦Δ,Γ⟧) ;; eqab
= eqab'
  ;; comp_ext_compare (!nid _ _ _ _ _ _)
  ;; q _ f.
Proof.
  etrans. { apply pathsinv0, reind_tm_q. }
  apply maponpaths_2.
  unfold eqab'.
  assert (eqnat :nid Γ Δ f A a b = !(!(nid Γ Δ f A a b)) ) by apply (!(pathsinv0inv0 _)).
  rewrite eqnat, (!(tm_transportbf _)).
  rewrite (pathsinv0inv0 _).
  apply (!(tm_transportb_unfold_alter _ _)).
Qed.

Definition Id_map_natural {Id} (nid : IdTypeNat Id)
{Γ Δ} (f : C^op ⟦Γ,Δ⟧) {A : Ty Γ : hSet} (a : tm A) (b : tm A) (eqab : tm (Id _ _ a b))
(eqab' : tm (Id _ _ (a ⌈f⌉) (b ⌈f⌉)) := (tm_transportf (nid _ _ _ _ _ _) (eqab ⌈f⌉))) 
: Id_map nid (a ⌈f⌉) (b ⌈f⌉) eqab'
  ;; (comp_ext_compare (!  IdBasedFamNatural Id nid  f A a)
  ;; q (IdBasedFam Id A a) (q A f))
= (f : C⟦Δ,Γ⟧) ;; Id_map nid a b eqab.
Proof.
  unfold Id_map, γ_qq.
  repeat rewrite tm_transportb_unfold.
  etrans. 2: { apply maponpaths, assoc. }
  etrans. 2: { apply pathsinv0, assoc. }
  etrans. 2: { eapply maponpaths_2, pathsinv0, id_intro_q. }
  etrans. { apply pathsinv0, assoc. }
  etrans. { apply pathsinv0, assoc. }
  etrans. 2: { apply assoc. }
  etrans. 2: { apply assoc. }
  apply maponpaths.
  etrans.
  { apply maponpaths.
  etrans. { apply assoc. }
  etrans. { apply maponpaths_2, pathsinv0, q_typeeq. }
  etrans. { apply assoc'. }
  apply maponpaths, q_q'.
  }
  etrans.
  2: { apply pathsinv0, maponpaths.
  etrans. { apply assoc. }
  etrans. { apply maponpaths_2, pathsinv0, q_typeeq. }
  etrans. { apply assoc'. }
  apply maponpaths, q_q'. 
  }
  etrans. { apply assoc. }
  etrans. { apply maponpaths_2, pathsinv0, comp_ext_compare_comp. }
  etrans. { apply assoc. }
  etrans. { apply maponpaths_2, pathsinv0, comp_ext_compare_comp. }
  etrans. 2: { apply assoc'. }
  etrans. 2: { apply maponpaths_2, comp_ext_compare_comp. }
  etrans. 2: { apply assoc'. }
  etrans. 2: { apply maponpaths_2, comp_ext_compare_comp. }
  etrans.
  2: { apply maponpaths.
    refine (q_mapeq _ _).
    apply pathsinv0, reind_tm_q.
  }
  etrans. 2: { apply assoc'. }
  etrans. 2: { apply maponpaths_2, comp_ext_compare_comp. }
  apply maponpaths_2, comp_ext_compare_irrelevant.
Qed.

Definition Id_map_natural_op {Id} (nid : IdTypeNat Id)
{Γ Δ} (f : C^op ⟦Γ,Δ⟧) {A : Ty Γ : hSet} (a : tm A) (b : tm A) (eqab : tm (Id _ _ a b))
(eqab' : tm (Id _ _ (a ⌈f⌉) (b ⌈f⌉)) := (tm_transportf (nid _ _ _ _ _ _) (eqab ⌈f⌉))) 
: (Id_map nid a b eqab : C^op ⟦_,_⟧ );; f =
((comp_ext_compare (! IdBasedFamNatural Id nid f A a)  ;; q (IdBasedFam Id A a) (q A f) ) : C^op ⟦_,_⟧ );; 
(Id_map nid (a ⌈f⌉) (b ⌈f⌉) eqab' : C^op ⟦_,_⟧).
Proof.
  eapply pathscomp0.
  assert (eqop : (Id_map nid a b eqab : C^op ⟦_,_⟧ );; f = (f : C⟦Δ,Γ⟧) ;; Id_map nid a b eqab) by auto.
  exact (eqop @ (!(Id_map_natural _ _ _ _ _))).
  reflexivity.
Qed.

Definition IdBased_path_inducton {Id} (nid : IdTypeNat Id) (refl : IdRefl Id) := ∏ Γ (A : Ty Γ : hSet) (a : tm A)
(P : Ty (_ ¤ IdBasedFam Id A a) :  hSet)
(d : tm  (P ⌊Id_map nid a a (refl _ _ a)⌋ ))
(b : tm A) (eqab : tm (Id _ _ a b)), 
tm (#Ty (Id_map nid a b eqab) P).

Definition d' {Id} {nid : IdTypeNat Id} {refl : IdRefl Id} (nrefl : IdReflNat Id nid refl) 
 {Γ Δ} (f : C^op ⟦Γ,Δ⟧) {A : Ty Γ : hSet} {a : tm A}
{P : Ty (_ ¤ IdBasedFam Id A a) :  hSet}
(P' :  Ty (_¤ (IdBasedFam Id (A ⌊f⌋) (a ⌈f⌉))) : hSet 
:= P⌊ (comp_ext_compare (!  IdBasedFamNatural Id nid  f A a) ;; q (IdBasedFam Id A a) (q A f))⌋) 
(d : tm  (P ⌊Id_map nid a a (refl _ _ a)⌋ ))
{b : tm A} (eqab : tm (Id _ _ a b)) : 
tm (P' ⌊Id_map nid (a ⌈f⌉) (a ⌈f⌉) (refl _ _ (a ⌈f⌉))⌋).
Proof. 
  refine ((tm_transportb _) (d ⌈f⌉)).      
  apply (pathscomp0 (compose_ty _ _ _)).
  unfold P'.
  apply pathsinv0.
  apply (pathscomp0 (compose_ty _ _ _)).
  apply maponpaths.
  apply (pathscomp0 (Id_map_natural_op nid f a a (refl _ A a))).
  apply maponpaths.
  apply maponpaths.
  eapply pathscomp0.
  apply maponpaths.
  apply nrefl.
  apply (pathscomp0 (!(tm_transportf_compose _ _ _))).
  apply tm_transportf_idpath_gen.
Defined.

Lemma d_type_natural {Id} (nid : IdTypeNat Id) (refl : IdRefl Id) {Γ Δ : C} (f : C^op ⟦Γ,Δ⟧) {A : Ty Γ : hSet} {a : tm A}
(P : Ty (_ ¤ IdBasedFam Id A a) :  hSet) {b : tm A} (eqab : tm (Id _ _ a b)):
 P ⌊Id_map nid a b eqab⌋ ⌊f⌋  =
   P ⌊comp_ext_compare (! IdBasedFamNatural Id nid f A a) ;; q (IdBasedFam Id A a) (q A f)⌋ ⌊Id_map nid (reind_tm f a) (reind_tm f b)
   (tm_transportf (nid Γ Δ f A a b) (reind_tm f eqab))⌋.
Proof.
  do 2 rewrite compose_ty.
  apply maponpaths.
  apply Id_map_natural_op.
Qed.

Definition IdBased_path_induction_natural {Id} (nid : IdTypeNat Id) (refl : IdRefl Id) (nrefl : IdReflNat Id nid refl) 
: UU :=
∏ (J : IdBased_path_inducton nid refl) (Γ Δ : C) (f : C^op ⟦Γ,Δ⟧) (A : Ty Γ : hSet) (a : tm A) 
(P : Ty (_ ¤ IdBasedFam Id A a) :  hSet)
(d : tm  (P ⌊Id_map nid a a (refl _ _ a)⌋ ))
(b : tm A) (eqab : tm (Id _ _ a b)), (tm_transportf (d_type_natural nid refl f P eqab) ((J Γ A a P d b eqab) ⌈f⌉)) = 
J Δ (A⌊f⌋) (a ⌈f⌉) (P⌊_⌋) (d' nrefl f d eqab) (b ⌈f⌉) (tm_transportf (nid _ _ _ _ _ _) (eqab ⌈f⌉)).

End Identity_Structure.

End splTCwF.
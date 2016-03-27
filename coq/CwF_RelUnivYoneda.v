
(**

 Ahrens, Lumsdaine, Voevodsky, 2015 - 2016

*)

Require Import Systems.Auxiliary.
Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.more_on_pullbacks.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import Systems.RelUnivStructure.
Require Import Systems.CwF_SplitTypeCat_Equivalence.

Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).
Local Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op").
Local Notation "a ⇒ b" := (precategory_morphisms a b)(at level 50).

Arguments yy {_ _ _ _}.

Section fix_category.

Variable C : precategory.
Variable hsC : has_homsets C.

Local Notation "'Yo'" := (yoneda C hsC).
Local Notation "'Yo^-1'" :=  (invweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ ))).


(** a CwF as a relative univ structure on Yo is
    - two presheaves tU, U
    - a morphism of presheaves p : tU -> U
    - for any X : C and f : Yo X -> U
       - an object (X,f) in C
       - a dependent projection (X,f) -> X in C
       - a morphism of presheaves yo(X,f) -> tU
       - such that the square commutes and is a pb square

  The comprehension structure (third point) is a proposition,
  since [preShv C] is a category.

*)

Local Definition CwF : UU
 := relative_universe_structure C (preShv C) Yo.



(** a CwF' as below is
    - a triple (Ty, ◂ + π) of object extension
    - a triple (Tm, p, Q) where
      - Tm is a presheaf,
      - p is a morphism of presheaves Tm -> Ty
      - Q is a family, for any X : C and A : Ty(X),
          Q(A) : yo(X◂A) -> Tm
    - such that squares commute and are pbs

  Parentheses are
   ( (Ty, ◂, π), ( (Tm,(p,Q)), props) )

*)

Local Definition CwF' : UU
 := Σ (X : type_structure C), families_structure _ hsC X.


(** Plan: a reasonable intermediate structure seems to be 
          one that can be obtained from [CwF'] by shuffling
          the components:
   ( (Ty, Tm, p), ( (◂ + π , Q), props ) )

     We then can show that the second component of that thing
     - is a prop and
     - is logically equivalent to the comprehension structure
       of a CwF 

    Alternatively, we can fiddle with interchanging Σ and ∀ and
    the yoneda isomorphism in two places, but maybe that's 
    more cumbersome? Those two places are quantifications in
    - Q
    - the pullback condition


*)


(** there should be a definition of a morphism in a category,
    meaning a triple (a,b,f : a -> b)
*)

Definition mor_of_presheaves : UU := 
   Σ (Ty Tm : preShv C), preShv C ⟦Tm, Ty⟧.

Definition u (X : mor_of_presheaves) : preShv C := pr1 X.
Definition tu (X : mor_of_presheaves) : preShv C := pr1 (pr2 X).
Definition p (X : mor_of_presheaves) : preShv C ⟦tu X, u X⟧ := pr2 (pr2 X).

Definition comp_data (X : mor_of_presheaves) : UU
  := 
   Σ (dpr : ∀ (Γ : C) (A : (u X : functor _ _ ) Γ : hSet ), Σ (ΓA : C), C⟦ΓA, Γ⟧),
     ∀ Γ (A : (u X : functor _ _ ) Γ : hSet), _ ⟦Yo (pr1 (dpr Γ A)) , tu X⟧.

Definition ext {X : mor_of_presheaves} (Y : comp_data X) {Γ} A 
  : C 
  := pr1 (pr1 Y Γ A).
Definition dpr {X : mor_of_presheaves} (Y : comp_data X) {Γ} A 
  : C⟦ext Y A, Γ⟧ 
  := pr2 (pr1 Y Γ A).
Definition QQ {X : mor_of_presheaves} (Y : comp_data X) {Γ} A 
  : _ ⟦Yo (ext Y A) , tu X⟧ 
  := pr2 Y Γ A.

Definition comp_prop (X : mor_of_presheaves) (Y : comp_data X) : UU :=
  ∀ Γ (A : (u X : functor _ _ ) Γ : hSet),
        Σ (e : #Yo (dpr _ A) ;; yy A = QQ Y A ;; p X), isPullback _ _ _ _ e.

Definition comp (X : mor_of_presheaves) : UU 
  := Σ (Y : comp_data X), comp_prop _ Y.

Definition iCwF := Σ (X : mor_of_presheaves), comp X.


Arguments comp_ext {_} _ _ _ .



(** the next lemma might be proved more easily with the specialized lemmas
    [weqtotal2dirprodassoc] and [weqtotal2dirprodassoc']
*)

Definition foo : 
 (Σ X : type_structure C, families_data_structure C hsC X)
   ≃ 
 Σ X : mor_of_presheaves, comp_data X.
Proof.
  eapply weqcomp.
    unfold type_structure.
    apply weqtotal2asstor. simpl.
  eapply weqcomp. Focus 2. apply weqtotal2asstol.
  apply weqfibtototal.
  intro Ty.
  eapply weqcomp. apply weqfibtototal. intro depr.
    set (XR := @weqtotal2asstol). unfold families_data_structure.
    specialize (XR (CwF_SplitTypeCat_Equivalence.preShv C)
                   (fun x =>  x ⇒ TY C (Ty,, depr))). simpl in XR.
    specialize (XR (fun Tmp =>  (∀ (Γ : C^op) (A : (TY C (Ty,, depr):functor _ _ ) Γ : hSet), 
                                        Yo (comp_ext (Ty,,depr) Γ A) ⇒ pr1 Tmp)) ).       
    apply XR. simpl.
  eapply weqcomp. Focus 2.
    set (XR := @weqtotal2asstor  (Σ Tm : functor (opp_precat_data C) hset_precategory_data,
           nat_trans Tm Ty)  ). 
    unfold comp_data. 
    specialize (XR (fun x =>  ∀ Γ : C, ((u (Ty,, x) : functor _ _ ) Γ : hSet) → Σ ΓA : C, ΓA ⇒ Γ)).
        simpl in XR.
    specialize (XR (fun Tmpdepr =>  ∀ (Γ : C^op) (A : (u (Ty,, pr1 Tmpdepr) : functor _ _ ) Γ : hSet),
                                      Yo (pr1 (pr2 Tmpdepr Γ A)) ⇒ tu (Ty,, pr1 Tmpdepr))).
    apply XR. simpl.
   eapply weqcomp.
     set (XR:= @weqtotal2asstol (∀ Γ : C, (Ty Γ : hSet) → Σ ΓA : C, ΓA ⇒ Γ)).
     specialize (XR (fun _ =>  Σ x0 : functor (opp_precat_data C) hset_precategory_data,
                                           nat_trans x0 Ty)).
     simpl in *.
     specialize (XR (fun deprTmp =>  ∀ (Γ : C) (A : (Ty Γ : hSet)),
                    nat_trans (yoneda_ob_functor_data C hsC (comp_ext (Ty,,pr1 deprTmp) Γ A)) (pr1 (pr2 deprTmp) ))).
     apply XR.
    
    use weqbandf.
    -  apply weqdirprodcomm.
    - intro. apply idweq.
Defined.    
  
  
Definition foobar : CwF' ≃ iCwF.
Proof.
  unfold iCwF.  
  eapply weqcomp. Focus 2. 
    set (XR:= @weqtotal2asstor mor_of_presheaves (fun X => comp_data X) ).
    specialize (XR (fun XY => comp_prop (pr1 XY) (pr2 XY))).
    apply XR.
  unfold CwF'. 
  eapply weqcomp.
    set (XR:= @weqtotal2asstol (type_structure C) (fun X => families_data_structure _ hsC X) ).
    specialize (XR (fun XY => families_prop_structure _ hsC (pr1 XY) (pr2 XY))).
    apply XR.
  use weqbandf.
  - apply foo.
  - intro x.
    unfold families_prop_structure.
    unfold comp_prop.
    apply weqonsecfibers.
    intro. 
    destruct x as [Tydepr [Tm [p Q]]].
    destruct Tydepr as [Ty depr].
    simple refine (idweq _ ).
Defined.  



Definition foobarla : CwF ≃ CwF'.
Abort.

End fix_category.


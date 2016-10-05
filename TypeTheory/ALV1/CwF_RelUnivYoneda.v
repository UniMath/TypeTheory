
(**

 Ahrens, Lumsdaine, Voevodsky, 2015 - 2016

Contents:

- Main result: construction of an equivalence
  [weq_RelUnivYo_CwF]
  between relative universe structures on Yoneda
  and families structures on a fixed precategory

- Intermediate structure [iCwF] obtained by 
  shuffling the components of a [CwF] structure

*)

Require Import UniMath.Foundations.Basics.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.
Require Import TypeTheory.ALV1.RelUnivStructure.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Defs.

Set Automatic Introduction.

Undelimit Scope transport.

Section fix_category.

Variable C : Precategory.

(** a [RelUnivYo] as a [relative_universe_structure] on [Yo] is
    - two presheaves tU, U
    - a morphism of presheaves p : tU -> U
    - for any X : C and f : Yo X -> U
       - an object (X,f) in C
       - a dependent projection (X,f) -> X in C
       - a morphism of presheaves yo(X,f) -> tU
       - such that the square commutes and is a pb square

  The q-morphism structure (third point) is a proposition,
  since [preShv C] is a category.

*)

Definition RelUnivYo_structure : UU
 := @relative_universe_structure C _ Yo.

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

Definition CwF_structure : UU
 := Σ (X : obj_ext_structure C), families_structure C X.


(** Plan: a reasonable intermediate structure seems to be 
          one that can be obtained from [CwF'] by shuffling
          the components:
   ( (Ty, Tm, p), ( (◂ + π , Q), props ) )

     We then can show that the second component of that thing
     - is a prop and
     - is logically equivalent to the q-morphism structure
       of a CwF 

    Alternatively, we can fiddle with interchanging Σ and Π and
    the yoneda isomorphism in two places, but maybe that's 
    more cumbersome? Those two places are quantifications in
    - Q
    - the pullback condition
*)


(** there should be a definition of a morphism in a category,
    meaning a triple (a,b,f : a -> b)
*)

Definition mor_of_presheaves : UU := arrow (preShv C).
   
Definition u (X : mor_of_presheaves) : preShv C := target X.
Definition tu (X : mor_of_presheaves) : preShv C := source X.
Definition p (X : mor_of_presheaves) : preShv C ⟦tu X, u X⟧
  :=  morphism_from_arrow X.


(** * Definition of intermediate structure [comp] *)

Definition comp_data (X : mor_of_presheaves) : UU
  := 
   Σ (dpr : Π (Γ : C) (A : (u X : functor _ _ ) Γ : hSet ), Σ (ΓA : C), C⟦ΓA, Γ⟧),
     Π Γ (A : (u X : functor _ _ ) Γ : hSet), _ ⟦Yo (pr1 (dpr Γ A)) , tu X⟧.

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
  Π Γ (A : (u X : functor _ _ ) Γ : hSet),
        Σ (e : #Yo (dpr _ A) ;; yy A = QQ Y A ;; p X), isPullback _ _ _ _ e.

Lemma isaprop_comp_prop (X : mor_of_presheaves) (Y : comp_data X) 
  : isaprop (comp_prop X Y).
Proof.
  do 2 (apply impred; intro).
  apply isofhleveltotal2.
  - apply functor_category_has_homsets.
  - intro. apply isaprop_isPullback.
Qed.

Definition comp (X : mor_of_presheaves) : UU 
  := Σ (Y : comp_data X), comp_prop _ Y.

Definition iCwF_structure := Σ (X : mor_of_presheaves), comp X.

(** * Construction of an equivalence between [CwF] and [iCwF] *)


(** the next lemma might be proved more easily with the specialized lemmas
    [weqtotal2dirprodassoc] and [weqtotal2dirprodassoc']
*)

Definition weq_comp_fam_data : 
 (Σ X : obj_ext_structure C, families_structure_data C X)
   ≃ 
 Σ X : mor_of_presheaves, comp_data X.
Proof.
  eapply weqcomp.
    unfold obj_ext_structure.
    apply weqtotal2asstor. simpl.
  eapply weqcomp. Focus 2. apply weqtotal2asstol. simpl.
  eapply weqcomp. Focus 2. eapply invweq.
        apply weqtotal2dirprodassoc. simpl.
  apply weqfibtototal.
  intro Ty.
  eapply weqcomp. apply weqfibtototal. intro depr.
    set (XR := @weqtotal2asstol). unfold families_structure_data.
    specialize (XR (preShv C)
                   (fun x =>  x --> TY (Ty,, depr))). simpl in XR.
    specialize (XR (fun Tmp =>  Π (Γ : C^op) (A : (TY (Ty,, depr):functor _ _ ) Γ : hSet), 
                                 Yo (comp_ext (Ty,,depr) Γ A) --> pr1 Tmp) ).       
    apply XR. simpl.
  eapply weqcomp.
    set (XR:= @weqtotal2asstol (Π Γ : C, (Ty Γ : hSet) → Σ ΓA : C, ΓA --> Γ)).
    specialize (XR (fun _ =>  Σ x0 : functor (opp_precat_data C) hset_precategory_data, 
                                      nat_trans x0 Ty)).
    simpl in *.
    specialize (XR (fun deprTmp => Π (Γ : C) (A : (Ty Γ : hSet)),
                                   nat_trans (yoneda_objects C (homset_property _) (comp_ext (Ty,,pr1 deprTmp) Γ A)) 
                                             (pr1 (pr2 deprTmp) ))).
    apply XR.
  eapply weqcomp. use weqtotal2dirprodcomm. simpl.
  eapply weqcomp; apply weqtotal2asstor. (* this looks like magic *)
Defined.



Definition weq_CwF_iCwF : CwF_structure ≃ iCwF_structure.
Proof.
  eapply weqcomp. Focus 2. 
    set (XR:= @weqtotal2asstor mor_of_presheaves (fun X => comp_data X) ).
    specialize (XR (fun XY => comp_prop (pr1 XY) (pr2 XY))).
    apply XR.
  eapply weqcomp.
    set (XR:= @weqtotal2asstol (obj_ext_structure C) 
                               (fun X => families_structure_data C X) ).
    specialize (XR (fun XY => families_structure_axioms C (pr1 XY) (pr2 XY))).
    apply XR.
  use weqbandf.
  - apply weq_comp_fam_data.
  - intro x.
    apply weqonsecfibers.
    intro. 
    destruct x as [Tydepr [Tm [p Q]]].
    destruct Tydepr as [Ty depr].
    exact (idweq _ ).
Defined.  


(* This is more complicated than to show that 
   [comp] is equivalent to fcomprehension
*)
(*
Lemma isaprop_comp (y : arrow (preShv C)) : isaprop (comp y).
Proof.
  apply invproofirrelevance.
  intros x x'. apply subtypeEquality.
  - intro t. apply isaprop_comp_prop.
  - destruct x as [x H]. 
    destruct x' as [x' H']. cbn.    
    destruct x as [a m].
    destruct x' as [a' m']. cbn in *.
    simple refine (total2_paths _ _ ).
    * simpl.
      apply funextsec; intro Γ.
      apply funextsec; intro A.      
      unfold comp_prop in H, H'. simpl in H, H'.
Abort.
*)



Definition Yo_pullback (x : arrow (preShv C)) : UU :=
   Π X (A : (target x : functor _ _ ) X : hSet),
      fpullback Yo x (yy A).

Definition weq_fcomprehension_Yo_pullback (x : arrow (preShv C)) :
   fcomprehension Yo x ≃ Yo_pullback x.
Proof.
  apply weqonsecfibers.
  intro X.
  apply (weqonsecbase _ (@yy _ _ _ _ )).
Defined.

Definition comp_1_data (y : arrow (preShv C)) : UU
  := Π (Γ : C) (A : (u y : functor _ _ ) Γ : hSet),
           (Σ ΓAp : Σ ΓA : C, ΓA --> Γ, Yo (pr1 ΓAp) --> tu y).


Definition weq_comp_data (y : arrow (preShv C)) : comp_data y ≃ comp_1_data y.
Proof.
  unfold comp_data.
  eapply weqcomp.
    set (XR := @weqtotaltoforall C).
    specialize (XR (fun X => ((u y : functor _ _ ) X : hSet) → Σ ΓA : C, ΓA --> X)).
    simpl in XR.
    specialize (XR (fun X dpr =>  Π (A : (u y : functor _ _ ) X : hSet), 
                                  Yo (pr1 (dpr A)) --> tu y)).
    apply XR.
  apply weqonsecfibers. intro X.
  set (XR := @weqtotaltoforall ((u y : functor _ _ ) X : hSet) ). simpl in XR.
  specialize (XR (fun _ => Σ ΓA : C, ΓA --> X)). simpl in XR. 
  specialize (XR  (fun A ΓAp => Yo (pr1 ΓAp) --> tu y)).
  apply XR.
Defined.

Definition ext_1 {X : mor_of_presheaves} (Y : comp_1_data X) {Γ} A 
  : C 
  := pr1 (pr1 (Y Γ A)).
Definition dpr_1 {X : mor_of_presheaves} (Y : comp_1_data X) {Γ} A 
  : C⟦ext_1 Y A, Γ⟧ 
  := pr2 (pr1 (Y Γ A)).
Definition QQ_1 {X : mor_of_presheaves} (Y : comp_1_data X) {Γ} A 
  : _ ⟦Yo (ext_1 Y A) , tu X⟧ 
  := (pr2 (Y Γ A)).

Definition comp_1_prop (X : mor_of_presheaves) (Y : comp_1_data X) : UU :=
  Π Γ (A : (u X : functor _ _ ) Γ : hSet),
        Σ (e : #Yo (dpr_1 _ A) ;; yy A = QQ_1 Y A ;; p X), isPullback _ _ _ _ e.

Definition comp_1 (X : mor_of_presheaves) : UU 
  := Σ (Y : comp_1_data X), comp_1_prop _ Y.


Definition weq_comp_comp_1 x : comp x ≃ comp_1 x.
Proof.
  set (XR := weqfp (weq_comp_data x)).
  eapply weqcomp. Focus 2. apply XR.
  apply weqfibtototal. intro y.
  apply weqonsecfibers. intro X. apply weqonsecfibers. intro A.
  apply weqimplimpl.
  -  intro H.
     destruct y as [extdepr Q].
     mkpair.
     apply (pr1 H).
     apply (pr2 H).
  - intro H.
     destruct y as [extdepr Q].
     mkpair.
     apply (pr1 H).
     apply (pr2 H).
  -  apply isofhleveltotal2.
     +  apply functor_category_has_homsets.
     + intro. apply isaprop_isPullback.
  -  apply isofhleveltotal2.
     +  apply functor_category_has_homsets.
     + intro. apply isaprop_isPullback.
Defined. 

Definition weq_Yo_pullback_comp_1 (y : arrow (preShv C))
  : comp_1 y ≃ Yo_pullback y.
Proof.
  unfold Yo_pullback; unfold comp_1.
  eapply weqcomp.
    set (XR := @weqtotaltoforall C). 
    unfold comp_1_data. unfold comp_1_prop.
    specialize (XR (fun X => ((u y : functor _ _ ) X : hSet) 
                             → Σ ΓAp : Σ ΓA : C, ΓA --> X, Yo (pr1 ΓAp) --> tu y)). 
    unfold dpr_1, QQ_1.
    specialize (XR (fun X pp =>  Π  (A : ((u y : functor _ _ ) X : hSet)),
       Σ e : # Yo (pr2 (pr1 (pp A))) ;; yy A = (pr2 (pp A) : preShv _ ⟦_,_⟧ );; p y,
       isPullback (yy A) (p y) (# Yo (pr2 (pr1 (pp A)))) (pr2 (pp A)) e)).
    apply XR.
  apply weqonsecfibers. intro X.
  eapply weqcomp.
    set (XR := @weqtotaltoforall  ((target y : functor _ _ ) X : hSet)). simpl in XR.
    specialize (XR (fun _ =>  Σ ΓAp : Σ ΓA : C, ΓA --> X, Yo (pr1 ΓAp) --> tu y)).

    specialize (XR (fun A pp =>  Σ e : # Yo (pr2 (pr1 (pp ))) ;; yy A =
                                     ((pr2 pp : preShv C ⟦_,_⟧)) ;; p y, 
    isPullback (yy A) (p y) (# Yo (pr2 (pr1 (pp )))) (pr2 (pp )) e)).
    apply XR.
  apply weqonsecfibers. intro A. unfold fpullback.
  transparent assert (HXY :
      ( (Σ ΓAp : Σ ΓA : C, ΓA --> X, Yo (pr1 ΓAp) --> tu y)
         ≃
         @fpullback_data _ _ (Yo) _ (source y) _ (yy A) ) ).
  { apply weqtotal2asstor. }
  apply (weqbandf HXY).
  intro x.
  destruct x as [[XA p] Q]. exact (idweq _ ).
Defined.

Lemma weq_comp_fcomprehension:
 Π x : arrow (preShv C),
   comp x ≃ fcomprehension Yo x.
Proof.
  intro y.
  apply invweq.
  eapply weqcomp. apply weq_fcomprehension_Yo_pullback.
  eapply weqcomp. Focus 2. eapply invweq. apply weq_comp_comp_1.
  apply (invweq (weq_Yo_pullback_comp_1 _ )).
Defined.

Definition weq_iCwF_RelUnivYo : iCwF_structure ≃ RelUnivYo_structure.
Proof.
  apply weqfibtototal.
  apply weq_comp_fcomprehension.
Defined.   
 


Definition weq_RelUnivYo_CwF : RelUnivYo_structure ≃ CwF_structure.
Proof.
  eapply weqcomp.
   apply (invweq weq_iCwF_RelUnivYo).
  apply (invweq weq_CwF_iCwF).
Defined.


(** The results below are not used anywhere, 
    but we keep them because, well, why shouldn't we?
*)

Definition comp_to_fcomprehension (x : arrow (preShv C)):
   comp x → fcomprehension Yo x.
Proof.
  intro H.
  set ( t := pr1 H). set (depr := pr1 t). set (Q := pr2 t). set (Hprop := pr2 H).
  intros Γ A. set (yiA := yoneda_weq _ _ _ _ A). set (XA := depr Γ yiA).
  mkpair.
  - mkpair.
    + exact (pr1 XA). 
    + mkpair.  
      * exact (pr2 XA).
      * apply Q.
  - simpl. unfold fpullback_prop. mkpair.
    + etrans. Focus 2. apply (pr1 (Hprop Γ yiA)).
      apply maponpaths. apply pathsinv0. apply homotinvweqweq.
    + assert (XR := pr2 (Hprop Γ yiA)).
      assert (XT:= homotinvweqweq (yoneda_weq _ _ _ _ )  A).
      assert (XR2 := isPb_morphism_equal _ _ _ _ _ _ _ _ _ _ XR A (!XT) ).
      apply XR2.
Defined.


Definition fcomprehension_to_comp (x : arrow (preShv C)):
  fcomprehension Yo x → comp x.
Proof.
  intro H. mkpair.
  - mkpair.
    + intros Γ A.
      set (XR := H Γ (yy A)).
      exists (fpb_obj _ XR).
      apply (fp _ XR).
    + intros Γ A.
      set (XR := H Γ (yy A)).
      apply (fq _ XR).
  - cbn. intros Γ A.
    set (XR := H Γ (yy A)).
    assert (XRT := pr2 XR). simpl in XRT. destruct XRT as [t p0]. simpl in t.
    mkpair.
    + apply t.
    + apply p0.
Defined.     


Lemma weq_fcomprehension_comp_data (y : arrow (preShv C)):
   @fcomprehension_data _ _ Yo (target y) (source y) ≃ comp_data y.
Proof.
  unfold fcomprehension_data.
  unfold comp_data.
  simpl.
  eapply weqcomp. Focus 2.
    set (XR := @weqforalltototal C).
    specialize (XR (fun X => ((u y : functor _ _ ) X : hSet) → Σ ΓA : C, ΓA --> X)).
    simpl in XR.
    specialize (XR (fun X pX =>  Π  (A : ((u y : functor _ _ ) X : hSet)),
              nat_trans (yoneda_ob_functor_data C (homset_property _) (pr1 (pX  A))) (tu y : functor _ _ ))).
    apply XR.
  apply weqonsecfibers. intro X. simpl.
  eapply weqcomp. Focus 2.
    set (XR := @weqforalltototal ((u y : functor _ _ ) X : hSet)).
    specialize (XR (fun A =>  Σ ΓA : C, ΓA --> X)). simpl in XR.
    specialize (XR (fun A pX => nat_trans (yoneda_ob_functor_data C (homset_property _) (pr1 (pX))) (tu y : functor _ _ ))).
    apply XR. simpl. unfold fpullback_data.
  eapply weqcomp.
    eapply weqbfun. apply (invweq (yoneda_weq _ _ _ _ )).
  apply weqffun.
  set (XR:= @weqtotal2asstol (ob C) (fun XA => _ ⟦XA, X⟧)). simpl in XR.
  specialize (XR (fun Q => Yo (pr1 Q) --> source y)).
  apply XR.
Defined.  


End fix_category.


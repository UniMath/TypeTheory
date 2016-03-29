
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
Require Import Systems.Structures.

Undelimit Scope transport.

Section fix_category.

Variable C : precategory.
Variable hsC : has_homsets C.

Local Notation "'Yo'" := (yoneda _ hsC).
Local Notation "'Yo^-1'" :=  (invweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ ))).

(** a CwF as a relative univ structure on Yo is
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
 := Σ (X : obj_ext_structure C), families_structure hsC X.


(** Plan: a reasonable intermediate structure seems to be 
          one that can be obtained from [CwF'] by shuffling
          the components:
   ( (Ty, Tm, p), ( (◂ + π , Q), props ) )

     We then can show that the second component of that thing
     - is a prop and
     - is logically equivalent to the q-morphism structure
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

Definition mor_of_presheaves : UU := arrow (preShv C).
   
Definition u (X : mor_of_presheaves) : preShv C := target X.
Definition tu (X : mor_of_presheaves) : preShv C := source X.
Definition p (X : mor_of_presheaves) : preShv C ⟦tu X, u X⟧
  :=  morphism_from_arrow X.

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

Definition iCwF := Σ (X : mor_of_presheaves), comp X.

(** the next lemma might be proved more easily with the specialized lemmas
    [weqtotal2dirprodassoc] and [weqtotal2dirprodassoc']
*)

Definition foo : 
 (Σ X : obj_ext_structure C, families_structure_data hsC X)
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
                   (fun x =>  x ⇒ TY (Ty,, depr))). simpl in XR.
    specialize (XR (fun Tmp =>  (∀ (Γ : C^op) (A : (TY (Ty,, depr):functor _ _ ) Γ : hSet), 
                                        Yo (comp_ext (Ty,,depr) Γ A) ⇒ pr1 Tmp)) ).       
    apply XR. simpl.



 eapply weqcomp.
     set (XR:= @weqtotal2asstol (∀ Γ : C, (Ty Γ : hSet) → Σ ΓA : C, ΓA ⇒ Γ)).
     specialize (XR (fun _ =>  Σ x0 : functor (opp_precat_data C) hset_precategory_data,
                                           nat_trans x0 Ty)).
     simpl in *.
     specialize (XR (fun deprTmp =>  ∀ (Γ : C) (A : (Ty Γ : hSet)),
                    nat_trans (yoneda_ob_functor_data C hsC (comp_ext (Ty,,pr1 deprTmp) Γ A)) (pr1 (pr2 deprTmp) ))).
     apply XR.
   simpl. 
  eapply weqcomp. use weqtotal2dirprodcomm. simpl.
  eapply weqcomp; apply weqtotal2asstor. (* this looks like magic *)
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
    set (XR:= @weqtotal2asstol (obj_ext_structure C) (fun X => families_structure_data hsC X) ).
    specialize (XR (fun XY => families_structure_axioms hsC (pr1 XY) (pr2 XY))).
    apply XR.
  use weqbandf.
  - apply foo.
  - intro x.
    unfold families_structure_axioms.
    unfold comp_prop.
    apply weqonsecfibers.
    intro. 
    destruct x as [Tydepr [Tm [p Q]]].
    destruct Tydepr as [Ty depr].

    simple refine (idweq _ ).
Defined.  


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
Abort.

Definition comp_to_fcomprehension (x : arrow (preShv C)):
   comp x → fcomprehension C (preShv C) Yo (target x) (source x) x.
Proof.
  intro H.
  set ( t := pr1 H).
  set (depr := pr1 t).
  set (Q := pr2 t).
  set (Hprop := pr2 H).
  intros Γ A.
  set (yiA := yoneda_weq _ _ _ _ A).
  set (XA := depr Γ yiA).
  mkpair.
  - mkpair.
    + exact (pr1 XA).
    + mkpair. 
      * exact (pr2 XA).
      * apply Q.
  - simpl. unfold fpullback_prop.
    mkpair.
    + etrans. Focus 2. apply (pr1 (Hprop Γ yiA)).
      apply maponpaths. apply pathsinv0. apply homotinvweqweq.
    + assert (XR := pr2 (Hprop Γ yiA)).
      assert (XT:= homotinvweqweq (yoneda_weq _ _ _ _ )  A).
      simpl in XR.
      assert (XR2 := isPb_morphism_equal _ _ _ _ _ _ _ _ _ _ XR A (!XT) ).
      apply XR2.
Defined.

Definition fcomprehension_to_comp (x : arrow (preShv C)):
  fcomprehension C (preShv C) Yo (target x) (source x) x → comp x.
Proof.
  intro H.
  mkpair.
  - mkpair.
    + intros Γ A.
      set (XR := H Γ (yy A)).
      exists (fpb_obj _ _ _ _ _ XR).
      apply (fp _ _ _ _ _ XR).
    + intros Γ A.
      set (XR := H Γ (yy A)).
      apply (fq _ _ _ _ _ XR).
  - cbn. intros Γ A.
    set (XR := H Γ (yy A)).
    assert (XRT := pr2 XR). simpl in XRT. destruct XRT as [t p0]. simpl in t.
    mkpair.
    + apply t.
    + apply p0.
Defined.     



Lemma wtf:
 ∀ x : arrow (preShv C),
   comp x ≃ fcomprehension C (preShv C) Yo (target x) (source x) x.
Proof.
  intro y.
  exists (comp_to_fcomprehension _ ).
  apply (gradth _ (fcomprehension_to_comp _ )).
  - intro x.
    apply subtypeEquality.
    intro. apply isaprop_comp_prop.
    destruct x as [t H]. simpl.
    destruct t as [t t'].
    simpl in *.
    use total2_paths.
    + simpl.
      apply funextsec; intro Γ.
      apply funextsec; intro A.
      simpl. 
      use total2_paths.
      * simpl. 
        simpl. 
        unfold comp_to_fcomprehension.
        apply maponpaths.
        apply maponpaths.
        apply (toforallpaths _ _ _ (functor_id (u y) _  )).
      * simpl. cbn.
admit.
Admitted.

Definition foobarla : iCwF ≃ CwF.
Proof.
  unfold iCwF.
  unfold CwF. unfold relative_universe_structure.
  unfold mor_of_presheaves.
  apply weqfibtototal.
  apply wtf.
Defined.   

End fix_category.


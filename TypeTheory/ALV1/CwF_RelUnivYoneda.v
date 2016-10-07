
(**

 Ahrens, Lumsdaine, Voevodsky, 2015 - 2016

Contents:

- Main result: an equivalence [weq_RelUnivYo_CwF]
  between CwF-structures on a precategory [C]
  and relative universes for [ Yo : C -> preShv C ].
*)

Require Import UniMath.Foundations.Basics.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.
Require Import TypeTheory.ALV1.RelativeUniverses.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Defs.

Set Automatic Introduction.

Section Fix_Category.

Variable C : Precategory.

(** a [RelUnivYo] on [C] is a [relative_universe] on [Yo : C -> preShv C], i.e.
    - two presheaves [tU], [U]
    - a morphism of presheaves [p : tU -> U]
    - relative comprehension on p, i.e. for any [X : C] and [f : Yo X -> U],
       - an object [ f^*X : C ]
       - a dependent projection [ f^*X -> X in C ]
       - a morphism of presheaves  [ yo f^*X -> tU ]
       - such that the square commutes and is a pullback.
*)

Definition RelUnivYo : UU
 := @relative_universe C _ Yo.

(** a [cwf_structure] on [C] is
    - a triple (Ty, (◂ + π)) of object extension
    - a triple (Tm, p, Q) where
      - Tm is a presheaf,
      - p is a morphism of presheaves Tm -> Ty
      - Q is a family, for any X : C and A : Ty(X),
          Q(A) : yo(X◂A) -> Tm
    - such that squares commute and are pbs

  Parentheses are
   ( (Ty, ◂, π), ( (Tm,(p,Q)), props) )

*)

(** ** Outline of the equivalence:

  We start by reordering the components of [cwf_structure],
  so that like [RelUnivYo], the morphism of presheaves comes first:
   ( (Ty, Tm, p), ( ((◂ + π) , Q), props ) )

   - the type of triples (Ty,Tm,p) is just [mor_total (preShv C)];
   - the type of triples (◂ + π, Q) is called [comp_data];
   - the axioms are called [comp_axioms].

   A pair [comp_data, comp_axioms] is called [comp], and we 
   define [icwf_structure] as the type of pairs of 
   a [mor_total] and a [comp] on it.

   The equivalence [weq_cwf_icwf : cwf_structure C ≃ icwf_structure C]
   is given just (!) by shuffling components.

   Next, we give equivalence [icwf_structure C ≃ RelUnivYo C]
   by constructing, for a given [ (Ty,Tm,p) : mor_total (preShv C) ],
   an equivalence [ weq_comp_fcomprehension ] between [ comp p ] and
   [ fcomprhension Yo p ], i.e. comprehensions on [p] relative to [Yo].   
*)

Local Definition u (p : mor_total (preShv C)) : preShv C := target p.
Local Definition tu (p : mor_total (preShv C)) : preShv C := source p.

(** ** Main intermediate structures: [comp], [icwf_structure] *)

Definition comp_data (p : mor_total (preShv C)) : UU
  := 
   Σ (dpr : Π (Γ : C) (A : (u p : functor _ _ ) Γ : hSet ), Σ (ΓA : C), C⟦ΓA, Γ⟧),
     Π Γ (A : (u p : functor _ _ ) Γ : hSet), _ ⟦Yo (pr1 (dpr Γ A)) , tu p⟧.

Definition ext {p : mor_total (preShv C)} (Y : comp_data p) {Γ} A 
  : C 
  := pr1 (pr1 Y Γ A).
Definition dpr {p : mor_total (preShv C)} (Y : comp_data p) {Γ} A 
  : C⟦ext Y A, Γ⟧ 
  := pr2 (pr1 Y Γ A).
Definition QQ {p : mor_total (preShv C)} (Y : comp_data p) {Γ} A 
  : _ ⟦Yo (ext Y A) , tu p⟧ 
  := pr2 Y Γ A.

Definition comp_axioms (p : mor_total (preShv C)) (Y : comp_data p) : UU :=
  Π Γ (A : (u p : functor _ _ ) Γ : hSet),
        Σ (e : #Yo (dpr _ A) ;; yy A = QQ Y A ;; p), isPullback _ _ _ _ e.

Definition comp (p : mor_total (preShv C)) : UU 
  := Σ (Y : comp_data p), comp_axioms _ Y.

Definition icwf_structure := Σ (p : mor_total (preShv C)), comp p.

(** ** Equivalence between [cwf_structure] and [icwf_structure] *)


(* Note: the next lemma might be proved more easily with the specialized lemmas
    [weqtotal2dirprodassoc] and [weqtotal2dirprodassoc']
*)

Definition weq_comp_fam_data : 
 (Σ X : obj_ext_structure C, fibered_term_structure_data C X)
   ≃ 
 Σ p : mor_total (preShv C), comp_data p.
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
    set (XR := @weqtotal2asstol). unfold fibered_term_structure_data.
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

Definition weq_cwf_icwf : cwf_structure C ≃ icwf_structure.
Proof.
  eapply weqcomp. Focus 2. 
    set (XR:= @weqtotal2asstor (mor_total _) (fun p => comp_data p) ).
    specialize (XR (fun XY => comp_axioms (pr1 XY) (pr2 XY))).
    apply XR.
  eapply weqcomp.
    set (XR:= @weqtotal2asstol (obj_ext_structure C) 
                               (fun X => fibered_term_structure_data C X) ).
    specialize (XR (fun XY => fibered_term_structure_axioms C (pr1 XY) (pr2 XY))).
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

(** ** Remainder of the equivalence *)

(** As per the outline above, it now remains to construct,
  for a given morphism [ p : Tm --> Ty ] in [ preShv p ],
  an equivalence [ comp p ≃ fcomprehension Yo p ]. Recall:

  a relative comprehension on [p] is a function giving,
  for each [X : C] and [f : Yo X -> Ty],
    - an object [ f^*X : C ]
    - a dependent projection [ f^*X -> X in C ]
    - a morphism of presheaves  [ yo f^*X -> Tm ]
    - such that the square commutes and is a pullback.

  a [comp p] consists of:
   - [comp_data], a triple [(◂ + π, Q)] as in a CwF, so
     - [◂ + π] : for each [X:C] and [A : Ty X],
        an object [ X ◂ A : C ], and projection [ π : X ◂ A -> X ]
     - [Q] : for each [X], [A], a map of presheaves [ y (X ◂ A) -> Tm ]
   - some axioms, [comp_axioms].

  The equivalence between these goes in two steps, essentially:

  - the Yoneda lemma: the equivalence between maps
    [ f : Yo X -> Ty ] and types [ A : Ty X ];
  - some reshuffling of pi- and sigma-types.

  The first of these is tackled in [weq_fcomprehension_fcompYo]; 
  the second, in [weq_comp_comp1], and [weq_fcompYo_comp1],
  using an intermediate reshuffling [comp1]. 
*)

Definition fcompYo (p : mor_total (preShv C)) : UU
  := Π X (A : (target p : functor _ _ ) X : hSet),
       fpullback Yo p (yy A).

Definition weq_fcomprehension_fcompYo (p : mor_total (preShv C)) :
   fcomprehension Yo p ≃ fcompYo p.
Proof.
  apply weqonsecfibers.
  intro X.
  apply (weqonsecbase _ (@yy _ _ _ _ )).
Defined.

Definition comp1_data (p : mor_total (preShv C)) : UU
  := Π (Γ : C) (A : (u p : functor _ _ ) Γ : hSet),
           (Σ ΓAp : Σ ΓA : C, ΓA --> Γ, Yo (pr1 ΓAp) --> tu p).

Definition ext1 {p : mor_total (preShv C)} (Y : comp1_data p) {Γ} A 
  : C 
  := pr1 (pr1 (Y Γ A)).
Definition dpr1 {p : mor_total (preShv C)} (Y : comp1_data p) {Γ} A 
  : C⟦ext1 Y A, Γ⟧ 
  := pr2 (pr1 (Y Γ A)).
Definition QQ1 {p : mor_total (preShv C)} (Y : comp1_data p) {Γ} A 
  : _ ⟦Yo (ext1 Y A) , tu p⟧ 
  := (pr2 (Y Γ A)).

Definition comp1_axioms (p : mor_total (preShv C)) (Y : comp1_data p) : UU :=
  Π Γ (A : (u p : functor _ _ ) Γ : hSet),
        Σ (e : #Yo (dpr1 _ A) ;; yy A = QQ1 Y A ;; p), isPullback _ _ _ _ e.

Definition comp1 (p : mor_total (preShv C)) : UU 
  := Σ (Y : comp1_data p), comp1_axioms _ Y.

Definition weq_comp_data (p : mor_total (preShv C)) : comp_data p ≃ comp1_data p.
Proof.
  unfold comp_data, comp1_data.
  eapply weqcomp.
    set (XR := @weqtotaltoforall C).
    specialize (XR (fun X => ((u p : functor _ _ ) X : hSet) → Σ ΓA : C, ΓA --> X)).
    simpl in XR.
    specialize (XR (fun X dpr =>  Π (A : (u p : functor _ _ ) X : hSet), 
                                  Yo (pr1 (dpr A)) --> tu p)).
    apply XR.
  apply weqonsecfibers. intro X.
  set (XR := @weqtotaltoforall ((u p : functor _ _ ) X : hSet) ). simpl in XR.
  specialize (XR (fun _ => Σ ΓA : C, ΓA --> X)). simpl in XR. 
  specialize (XR  (fun A ΓAp => Yo (pr1 ΓAp) --> tu p)).
  apply XR.
Defined.

Definition weq_comp_comp1 (p : mor_total (preShv C)) : comp p ≃ comp1 p.
Proof.
  set (XR := weqfp (weq_comp_data p)).
  eapply weqcomp. Focus 2. apply XR.
  apply weqfibtototal. intro y.
  apply weqonsecfibers. intro X. apply weqonsecfibers. intro A.
  apply idweq.
Defined.

Definition weq_fcompYo_comp1 (p : mor_total (preShv C))
  : comp1 p ≃ fcompYo p.
Proof.
  unfold fcompYo; unfold comp1.
  eapply weqcomp.
    set (XR := @weqtotaltoforall C). 
    unfold comp1_data. unfold comp1_axioms.
    specialize (XR (fun X => ((u p : functor _ _ ) X : hSet) 
                             → Σ ΓAp : Σ ΓA : C, ΓA --> X, Yo (pr1 ΓAp) --> tu p)). 
    unfold dpr1, QQ1.
    specialize (XR (fun X pp =>  Π  (A : ((u p : functor _ _ ) X : hSet)),
       Σ e : # Yo (pr2 (pr1 (pp A))) ;; yy A = (pr2 (pp A) : preShv _ ⟦_,_⟧ );; p,
       isPullback (yy A) p (# Yo (pr2 (pr1 (pp A)))) (pr2 (pp A)) e)).
    apply XR.
  apply weqonsecfibers. intro X.
  eapply weqcomp.
    set (XR := @weqtotaltoforall  ((target p : functor _ _ ) X : hSet)). simpl in XR.
    specialize (XR (fun _ =>  Σ ΓAp : Σ ΓA : C, ΓA --> X, Yo (pr1 ΓAp) --> tu p)).

    specialize (XR (fun A pp =>  Σ e : # Yo (pr2 (pr1 (pp ))) ;; yy A =
                                     ((pr2 pp : preShv C ⟦_,_⟧)) ;; p, 
    isPullback (yy A) p (# Yo (pr2 (pr1 (pp )))) (pr2 (pp )) e)).
    apply XR.
  apply weqonsecfibers. intro A. unfold fpullback.
  transparent assert (HXY :
      ( (Σ ΓAp : Σ ΓA : C, ΓA --> X, Yo (pr1 ΓAp) --> tu p)
         ≃
         @fpullback_data _ _ (Yo) _ (source p) _ (yy A) ) ).
  { apply weqtotal2asstor. }
  apply (weqbandf HXY).
  intro x.
  destruct x as [[XA pA] Q]. exact (idweq _ ).
Defined.

Lemma weq_comp_fcomprehension (p : mor_total (preShv C))
  : comp p ≃ fcomprehension Yo p.
Proof.
  apply invweq.
  eapply weqcomp. apply weq_fcomprehension_fcompYo.
  eapply weqcomp. Focus 2. eapply invweq. apply weq_comp_comp1.
  apply (invweq (weq_fcompYo_comp1 _ )).
Defined.

Definition weq_iCwF_RelUnivYo : icwf_structure ≃ RelUnivYo.
Proof.
  apply weqfibtototal.
  apply weq_comp_fcomprehension.
Defined.   
 
(** ** Conclusion: an equivalence between [RelUnivYo] and [cwf_structure] *)

Definition weq_RelUnivYo_CwF : RelUnivYo ≃ cwf_structure C.
Proof.
  eapply weqcomp.
   apply (invweq weq_iCwF_RelUnivYo).
  apply (invweq weq_cwf_icwf).
Defined.


(** ** Some unused results *)

(** The results below are no longer used, 
    but we retain them for possible future reference.
*)

Lemma isaprop_comp_axioms (p : mor_total (preShv C)) (Y : comp_data p) 
  : isaprop (comp_axioms p Y).
Proof.
  do 2 (apply impred; intro).
  apply isofhleveltotal2.
  - apply homset_property.
  - intro. apply isaprop_isPullback.
Qed.

Definition comp_to_fcomprehension (p : mor_total (preShv C)):
   comp p → fcomprehension Yo p.
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


Definition fcomprehension_to_comp (p : mor_total (preShv C)):
  fcomprehension Yo p → comp p.
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


Lemma weq_fcomprehension_comp_data (p : mor_total (preShv C)):
   @fcomprehension_data _ _ Yo (target p) (source p) ≃ comp_data p.
Proof.
  unfold fcomprehension_data.
  unfold comp_data.
  simpl.
  eapply weqcomp. Focus 2.
    set (XR := @weqforalltototal C).
    specialize (XR (fun X => ((u p : functor _ _ ) X : hSet) → Σ ΓA : C, ΓA --> X)).
    simpl in XR.
    specialize (XR (fun X pX =>  Π  (A : ((u p : functor _ _ ) X : hSet)),
              nat_trans (yoneda_ob_functor_data C (homset_property _) (pr1 (pX  A))) (tu p : functor _ _ ))).
    apply XR.
  apply weqonsecfibers. intro X. simpl.
  eapply weqcomp. Focus 2.
    set (XR := @weqforalltototal ((u p : functor _ _ ) X : hSet)).
    specialize (XR (fun A =>  Σ ΓA : C, ΓA --> X)). simpl in XR.
    specialize (XR (fun A pX => nat_trans (yoneda_ob_functor_data C (homset_property _) (pr1 (pX))) (tu p : functor _ _ ))).
    apply XR. simpl. unfold fpullback_data.
  eapply weqcomp.
    eapply weqbfun. apply (invweq (yoneda_weq _ _ _ _ )).
  apply weqffun.
  set (XR:= @weqtotal2asstol (ob C) (fun XA => _ ⟦XA, X⟧)). simpl in XR.
  specialize (XR (fun Q => Yo (pr1 Q) --> source p)).
  apply XR.
Defined.  


End Fix_Category.


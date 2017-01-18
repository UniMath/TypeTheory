(**
  [TypeTheory.ALV1.CwF_RelUnivYoneda]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**
Contents:

- Main result: an equivalence [weq_RelUnivYo_CwF]
  between CwF-structures on a precategory [C]
  and relative universes for [ Yo : C -> preShv C ].
*)

Require Import UniMath.Foundations.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.
Require Import TypeTheory.ALV1.RelativeUniverses.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Defs.

Set Automatic Introduction.

Section Fix_Category.

Variable C : Precategory.

(** a [RelUnivYo] on [C] is a [relative_universe] on [Yo : C -> preShv C], i.e.
    - a morphism of presheaves [pp : Tm -> Ty]
    - relative comprehension on pp, i.e. for any [X : C] and [f : Yo X -> Ty],
       - an object [ f^*X : C ]
       - a dependent projection [ f^*X -> X in C ]
       - a morphism of presheaves  [ yo f^*X -> Tm ]
       - such that the square commutes and is a pullback.
*)

Definition RelUnivYo : UU
  := @relative_universe C _ Yo.

(** a [cwf_structure] on [C] is
    - a triple (Ty, (◂ + π)) (the object-extension structure)
    - a triple (Tm, pp, Q) where
      - Tm is a presheaf,
      - pp is a morphism of presheaves Tm -> Ty
      - Q is a family, for any Γ : C and A : Ty(Γ),
          Q(A) : yo(Γ◂A) -> Tm
    - such that squares commute and are pbs

  Parentheses are
   ( (Ty, ◂, π), ( (Tm,(pp,Q)), props) )

*)

(** ** Outline of the equivalence:

  We start by reordering the components of [cwf_structure],
  so that like [RelUnivYo], the morphism of presheaves comes first:
   ( (Ty, Tm, pp), ( ((◂ + π) , Q), props ) )

   - the type of triples (Ty,Tm,pp) is just [mor_total (preShv C)];
   - the type of triples (◂ + π, Q) is called [comp_data];
   - the axioms are called [comp_axioms].

   A pair [comp_data, comp_axioms] is called [comp], and we 
   define [icwf_structure] as the type of pairs of 
   a [mor_total] and a [comp] on it.

   The equivalence [weq_cwf_icwf : cwf_structure C ≃ icwf_structure C]
   is given just (!) by shuffling components.

   Next, we give equivalence [icwf_structure C ≃ RelUnivYo C]
   by constructing, for a given [ (Ty,Tm,pp) : mor_total (preShv C) ],
   an equivalence [ weq_comp_fcomprehension ] between [ comp pp ] and
   [ fcomprhension Yo pp ], i.e. comprehensions on [pp] relative to [Yo].   
*)

Local Definition Ty (pp : mor_total (preShv C)) : functor _ _ := target pp.
Local Definition Tm (pp : mor_total (preShv C)) : functor _ _ := source pp.

(** ** Main intermediate structures: [comp], [icwf_structure] *)

Definition comp_data (pp : mor_total (preShv C)) : UU
  := 
   Σ (dpr : Π (Γ : C) (A : Ty pp Γ : hSet ), Σ (ΓA : C), C⟦ΓA, Γ⟧),
     Π Γ (A : Ty pp Γ : hSet), _ ⟦Yo (pr1 (dpr Γ A)) , Tm pp⟧.

Definition ext {pp : mor_total (preShv C)} (Y : comp_data pp) {Γ} A 
  : C 
  := pr1 (pr1 Y Γ A).
Definition dpr {pp : mor_total (preShv C)} (Y : comp_data pp) {Γ} A 
  : C⟦ext Y A, Γ⟧ 
  := pr2 (pr1 Y Γ A).
Definition QQ {pp : mor_total (preShv C)} (Y : comp_data pp) {Γ} A 
  : _ ⟦Yo (ext Y A) , Tm pp⟧ 
  := pr2 Y Γ A.

Definition comp_axioms (pp : mor_total (preShv C)) (Y : comp_data pp) : UU :=
  Π Γ (A : Ty pp Γ : hSet),
        Σ (e : #Yo (dpr _ A) ;; yy A = QQ Y A ;; pp), isPullback _ _ _ _ e.

Definition comp (pp : mor_total (preShv C)) : UU 
  := Σ (Y : comp_data pp), comp_axioms _ Y.

Definition icwf_structure := Σ (pp : mor_total (preShv C)), comp pp.

(** ** Equivalence between [cwf_structure] and [icwf_structure] *)


(* Note: the next lemma might be proved more easily with the specialized lemmas
    [weqtotal2dirprodassoc] and [weqtotal2dirprodassoc']
*)

Definition weq_comp_cwf_data : 
 (Σ X : obj_ext_structure C, term_fun_structure_data C X)
   ≃ 
 Σ pp : mor_total (preShv C), comp_data pp.
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
    set (XR := @weqtotal2asstol). unfold term_fun_structure_data.
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
    set (XR:= @weqtotal2asstor (mor_total _) (fun pp => comp_data pp) ).
    specialize (XR (fun XY => comp_axioms (pr1 XY) (pr2 XY))).
    apply XR.
  eapply weqcomp.
    set (XR:= @weqtotal2asstol (obj_ext_structure C) 
                               (fun X => term_fun_structure_data C X) ).
    specialize (XR (fun XY => term_fun_structure_axioms C (pr1 XY) (pr2 XY))).
    apply XR.
  use weqbandf.
  - apply weq_comp_cwf_data.
  - intro x.
    apply weqonsecfibers.
    intro. 
    destruct x as [Tydepr [Tm [pp Q]]].
    destruct Tydepr as [Ty depr].
    exact (idweq _ ).
Defined.  

(** ** Remainder of the equivalence *)

(** As per the outline above, it now remains to construct,
  for a given morphism [ pp : Tm --> Ty ] in [ preShv pp ],
  an equivalence [ comp pp ≃ fcomprehension Yo pp ]. Recall:

  a relative comprehension on [pp] is a function giving,
  for each [Γ : C] and [f : Yo Γ -> Ty],
    - an object [ f^*Γ : C ]
    - a dependent projection [ f^*Γ -> Γ in C ]
    - a morphism of presheaves  [ yo f^*Γ -> Tm ]
    - such that the square commutes and is a pullback.

  a [comp pp] consists of:
   - [comp_data], a triple [(◂ + π, Q)] as in a CwF, so
     - [◂ + π] : for each [Γ:C] and [A : Ty Γ],
        an object [ Γ ◂ A : C ], and projection [ π : Γ ◂ A -> Γ ]
     - [Q] : for each [Γ], [A], a map of presheaves [ y (Γ ◂ A) -> Tm ]
   - some axioms, [comp_axioms].

  The equivalence between these goes in two steps, essentially:

  - the Yoneda lemma: the equivalence between maps
    [ f : Yo Γ -> Ty ] and types [ A : Ty Γ ];
  - some reshuffling of pi- and sigma-types.

  The first of these is tackled in [weq_fcomprehension_fcompYo]; 
  the second, in [weq_comp_comp1], and [weq_fcompYo_comp1],
  using an intermediate reshuffling [comp1]. 
*)

Definition fcompYo (pp : mor_total (preShv C)) : UU
  := Π Γ (A : Ty pp Γ : hSet),
       fpullback Yo pp (yy A).

Definition weq_fcomprehension_fcompYo (pp : mor_total (preShv C)) :
   fcomprehension Yo pp ≃ fcompYo pp.
Proof.
  apply weqonsecfibers.
  intro Γ.
  apply (weqonsecbase _ (@yy _ _ _ _ )).
Defined.

Definition comp1_data (pp : mor_total (preShv C)) : UU
  := Π (Γ : C) (A : Ty pp Γ : hSet),
           (Σ ΓAp : Σ ΓA : C, ΓA --> Γ, Yo (pr1 ΓAp) --> Tm pp).

Definition ext1 {pp : mor_total (preShv C)} (Y : comp1_data pp) {Γ} A 
  : C 
  := pr1 (pr1 (Y Γ A)).
Definition dpr1 {pp : mor_total (preShv C)} (Y : comp1_data pp) {Γ} A 
  : C⟦ext1 Y A, Γ⟧ 
  := pr2 (pr1 (Y Γ A)).
Definition QQ1 {pp : mor_total (preShv C)} (Y : comp1_data pp) {Γ} A 
  : _ ⟦Yo (ext1 Y A) , Tm pp⟧ 
  := (pr2 (Y Γ A)).

Definition comp1_axioms (pp : mor_total (preShv C)) (Y : comp1_data pp) : UU :=
  Π Γ (A : Ty pp Γ : hSet),
        Σ (e : #Yo (dpr1 _ A) ;; yy A = QQ1 Y A ;; pp), isPullback _ _ _ _ e.

Definition comp1 (pp : mor_total (preShv C)) : UU 
  := Σ (Y : comp1_data pp), comp1_axioms _ Y.

Definition weq_comp_data (pp : mor_total (preShv C)) : comp_data pp ≃ comp1_data pp.
Proof.
  unfold comp_data, comp1_data.
  eapply weqcomp.
    set (XR := @weqtotaltoforall C).
    specialize (XR (fun Γ => (Ty pp Γ : hSet) → Σ ΓA : C, ΓA --> Γ)).
    simpl in XR.
    specialize (XR (fun Γ dpr =>  Π (A : Ty pp Γ : hSet), 
                                  Yo (pr1 (dpr A)) --> Tm pp)).
    apply XR.
  apply weqonsecfibers. intro Γ.
  set (XR := @weqtotaltoforall (Ty pp Γ : hSet) ). simpl in XR.
  specialize (XR (fun _ => Σ ΓA : C, ΓA --> Γ)). simpl in XR. 
  specialize (XR  (fun A ΓAp => Yo (pr1 ΓAp) --> Tm pp)).
  apply XR.
Defined.

Definition weq_comp_comp1 (pp : mor_total (preShv C)) : comp pp ≃ comp1 pp.
Proof.
  set (XR := weqfp (weq_comp_data pp)).
  eapply weqcomp. Focus 2. apply XR.
  apply weqfibtototal. intro y.
  apply weqonsecfibers. intro Γ. apply weqonsecfibers. intro A.
  apply idweq.
Defined.

Definition weq_fcompYo_comp1 (pp : mor_total (preShv C))
  : comp1 pp ≃ fcompYo pp.
Proof.
  unfold fcompYo; unfold comp1.
  eapply weqcomp.
    set (XR := @weqtotaltoforall C). 
    unfold comp1_data. unfold comp1_axioms.
    specialize (XR (fun Γ => (Ty pp Γ : hSet) 
                             → Σ ΓAp : Σ ΓA : C, ΓA --> Γ, Yo (pr1 ΓAp) --> Tm pp)). 
    unfold dpr1, QQ1.
    specialize (XR (fun Γ p =>  Π  (A : (Ty pp Γ : hSet)),
       Σ e : # Yo (pr2 (pr1 (p A))) ;; yy A = (pr2 (p A) : preShv _ ⟦_,_⟧ );; pp,
       isPullback (yy A) pp (# Yo (pr2 (pr1 (p A)))) (pr2 (p A)) e)).
    apply XR.
  apply weqonsecfibers. intro Γ.
  eapply weqcomp.
    set (XR := @weqtotaltoforall  (Ty pp Γ : hSet)). simpl in XR.
    specialize (XR (fun _ =>  Σ ΓAp : Σ ΓA : C, ΓA --> Γ, Yo (pr1 ΓAp) --> Tm pp)).

    specialize (XR (fun A p =>  Σ e : # Yo (pr2 (pr1 (p ))) ;; yy A =
                                     ((pr2 p : preShv C ⟦_,_⟧)) ;; pp, 
    isPullback (yy A) pp (# Yo (pr2 (pr1 (p )))) (pr2 (p )) e)).
    apply XR.
  apply weqonsecfibers. intro A. unfold fpullback.
  transparent assert (HXY :
      ( (Σ ΓAp : Σ ΓA : C, ΓA --> Γ, Yo (pr1 ΓAp) --> Tm pp)
         ≃
         @fpullback_data _ _ (Yo) _ (Tm pp) _ (yy A) ) ).
  { apply weqtotal2asstor. }
  apply (weqbandf HXY).
  intro x.
  destruct x as [[XA pA] Q]. exact (idweq _ ).
Defined.

Lemma weq_comp_fcomprehension (pp : mor_total (preShv C))
  : comp pp ≃ fcomprehension Yo pp.
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

Lemma isaprop_comp_axioms (pp : mor_total (preShv C)) (Y : comp_data pp) 
  : isaprop (comp_axioms pp Y).
Proof.
  do 2 (apply impred; intro).
  apply isofhleveltotal2.
  - apply homset_property.
  - intro. apply isaprop_isPullback.
Qed.

Definition comp_to_fcomprehension (pp : mor_total (preShv C)):
   comp pp → fcomprehension Yo pp.
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


Definition fcomprehension_to_comp (pp : mor_total (preShv C)):
  fcomprehension Yo pp → comp pp.
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


Lemma weq_fcomprehension_comp_data (pp : mor_total (preShv C)):
   @fcomprehension_data _ _ Yo (Ty pp) (Tm pp) ≃ comp_data pp.
Proof.
  unfold fcomprehension_data.
  unfold comp_data.
  simpl.
  eapply weqcomp. Focus 2.
    set (XR := @weqforalltototal C).
    specialize (XR (fun Γ => (Ty pp Γ : hSet) → Σ ΓA : C, ΓA --> Γ)).
    simpl in XR.
    specialize (XR (fun Γ pX =>  Π  (A : (Ty pp Γ : hSet)),
              nat_trans (yoneda_ob_functor_data C (homset_property _) (pr1 (pX  A))) (Tm pp))).
    apply XR.
  apply weqonsecfibers. intro Γ. simpl.
  eapply weqcomp. Focus 2.
    set (XR := @weqforalltototal (Ty pp Γ : hSet)).
    specialize (XR (fun A =>  Σ ΓA : C, ΓA --> Γ)). simpl in XR.
    specialize (XR (fun A pX => nat_trans (yoneda_ob_functor_data C (homset_property _) (pr1 (pX))) (Tm pp))).
    apply XR. simpl. unfold fpullback_data.
  eapply weqcomp.
    eapply weqbfun. apply (invweq (yoneda_weq _ _ _ _ )).
  apply weqffun.
  set (XR:= @weqtotal2asstol (ob C) (fun XA => _ ⟦XA, Γ⟧)). simpl in XR.
  specialize (XR (fun Q => Yo (pr1 Q) --> Tm pp)).
  apply XR.
Defined.  


End Fix_Category.


(**
  [TypeTheory.ALV1.CwF_RelUnivYoneda]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**
Contents:

- Main result: an equivalence [weq_cwf_cwf']
  between the canonical definition of CwF-structures on a precategory [C] 
  and the regrouped definition based on object-extension structures.
*)

Require Import UniMath.Foundations.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.
Require Import TypeTheory.ALV1.CwF_def.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Defs.

Set Automatic Introduction.

Section Fix_Category.

Variable C : Precategory.

(** 
  A [cwf'_structure] on _C_ is
  - a triple (Ty, (◂ + π)) (the object-extension structure)
  - a triple (Tm, pp, Q) where
    - Tm is a presheaf,
    - pp is a morphism of presheaves Tm -> Ty
    - te is a term, for any Γ : C and A : Ty(Γ),
        te A : Tm (Γ◂A)
  - such (te A) has the desired type, and square are pbs

  Parentheses are
    ( (Ty, (◂ + π)), ( (Tm,(pp,Q)), props) )

  Meanwhile, as [cwf_structure] on _C_ consists of a morphism pp : Ty --> Tm of presheaves together with, for each Γ and A : Ty Γ, a _representation_ of the fiber of Tm over A, which we will inspect in more detail below.

  So the main differences, in the order we will tackle them, are:

  - ordering: _pp_ at the front together;
  - distributing ∏ over ∑: a single quantification over Γ, A on the outside, vs. quantifying within each component;
  - association/ordering of the components within the fiber-representation

**) 

(** ** Outline of the equivalence:

  We start by reordering the components of [cwf'_structure],
  so that like [cwf_structure], the morphism of presheaves comes first:
   ( (Ty, Tm, pp), ( ((◂ + π) , Q), props ) )

   - the type of triples (Ty,Tm,pp) is just [mor_total (preShv C)];
   - the type of triples (◂ + π, Q) is called [rep1_data];
   - the axioms are called [rep1_axioms].

   A pair [rep1_data, rep1_axioms] is called [rep1], and we 
   define [cwf1_structure] as the type of pairs of 
   a [mor_total] and a [rep1] on it.

   The equivalence [weq_cwf'_cwf1 : cwf'_structure C ≃ cwf1_structure C]
   is given just (!) by shuffling components.

   Next, we give equivalence [cwf1_structure C ≃ cwf_structure C]
   by constructing, for a given [ (Ty,Tm,pp) : mor_total (preShv C) ],
   an equivalence [ weq_rep1_fcomprehension ] between [ rep1 pp ] and
   [ cwf_representation pp ], i.e. representations of all fibers of [pp]. 
*)

(** ** Main intermediate structures: [rep1], [cwf1_structure] *)

Definition rep1_data (pp : mor_total (preShv C)) : UU
  := 
   ∑ (dpr : ∏ (Γ : C) (A : Ty pp Γ : hSet ), ∑ (ΓA : C), C⟦ΓA, Γ⟧),
     ∏ Γ (A : Ty pp Γ : hSet), Tm pp (pr1 (dpr Γ A)) : hSet.

Definition ext {pp : mor_total (preShv C)} (Y : rep1_data pp) Γ A 
  : C 
  := pr1 (pr1 Y Γ A).

Definition dpr {pp : mor_total (preShv C)} (Y : rep1_data pp) {Γ} A 
  : C⟦ext Y Γ A, Γ⟧ 
  := pr2 (pr1 Y Γ A).

Definition te {pp : mor_total (preShv C)} (Y : rep1_data pp) {Γ:C} A 
  : Tm pp (ext Y Γ A) : hSet
  := pr2 Y Γ A.

Definition rep1_fiber_axioms {pp : mor_total (preShv C)}
  {Γ} (A : Ty pp Γ : hSet) 
  {ΓA : C} (π : ΓA --> Γ) (te : Tm pp ΓA : hSet) : UU
:=
  ∑ (e : ((pp : _ --> _) : nat_trans _ _ ) _ te
         = (# (Ty pp) π A)),
    isPullback _ _ _ _ (cwf_square_comm (_,,_) (_,,e)).

Definition rep1_axioms {pp : mor_total (preShv C)} (Y : rep1_data pp) : UU :=
  ∏ Γ (A : Ty pp Γ : hSet), rep1_fiber_axioms A (dpr Y A) (te Y A).

Definition rep1 (pp : mor_total (preShv C)) : UU 
  := ∑ (Y : rep1_data pp), rep1_axioms Y.

Definition cwf1_structure := ∑ (pp : mor_total (preShv C)), rep1 pp.


(* TODO: upstream; and see if this can be used to more easily get other instances of [weqtotal2asstol] that currently need careful use of [specialize]. *)
Lemma weqtotal2asstol' {X : UU} (P : X → UU) (Q : forall x, P x → UU)
  : (∑ (x : X) (p : P x), Q x p) ≃ (∑ (y : ∑ x, P x), Q (pr1 y) (pr2 y)).
Proof.
  exact (weqtotal2asstol P (fun y => Q (pr1 y) (pr2 y))). 
Defined.

Lemma weqtotal2asstor' {X : UU} (P : X → UU) (Q : forall x, P x → UU)
  : (∑ (y : ∑ x, P x), Q (pr1 y) (pr2 y)) ≃ (∑ (x : X) (p : P x), Q x p).
Proof.
  exact (weqtotal2asstor P (fun y => Q (pr1 y) (pr2 y))). 
Defined.

(** ** Equivalence between [cwf_structure] and [cwf1_structure] *)

(* Note: the next lemma might be proved more easily with the specialized lemmas
    [weqtotal2dirprodassoc] and [weqtotal2dirprodassoc']
*)

Definition weq_rep1_cwf'_data : 
 (∑ X : obj_ext_structure C, term_fun_structure_data C X)
   ≃ 
 ∑ pp : mor_total (preShv C), rep1_data pp.
Proof.
  eapply weqcomp.
    unfold obj_ext_structure.
    apply weqtotal2asstor. simpl.
  eapply weqcomp. Focus 2. apply weqtotal2asstol. simpl.
  eapply weqcomp. Focus 2. eapply invweq.
        apply weqtotal2dirprodassoc. simpl.
  apply weqfibtototal.
  intro Ty.
  eapply weqcomp.
    apply weqfibtototal; intro depr.
    apply weqtotal2asstol'.
  eapply weqcomp.
    apply weqtotal2asstol'.
  eapply weqcomp. cbn. use weqtotal2dirprodcomm.
  eapply weqcomp; apply weqtotal2asstor.
Defined.

Definition weq_cwf'_cwf1 : cwf'_structure C ≃ cwf1_structure.
Proof.
  eapply weqcomp. Focus 2. apply weqtotal2asstor'.
  eapply weqcomp. apply weqtotal2asstol'.
  use weqbandf.
  - apply weq_rep1_cwf'_data.
  - intro.
    apply weqonsecfibers.
    intro. 
    exact (idweq _ ).
Defined.

(** ** Remainder of the equivalence *)



(** As per the outline above, it now remains to construct,
  for a given morphism [ pp : Tm --> Ty ] in [ preShv pp ],
  an equivalence [ rep1 pp ≃ cwf_representation pp ]. Recall:

  a representation of [pp] is a function giving,
  for each [Γ : C] and [f : Yo Γ -> Ty],
    - an object and map [ f^*Γ -> Γ in C ];
    - a term of appropriate type;
    - such that the induced square of presheaves is a pullback.

  a [rep1 pp] consists of:
   - [rep1_data], a triple [(◂ + π, Q)] as in a CwF, so
     - [◂ + π] : for each [Γ:C] and [A : Ty Γ],
        an object [ Γ ◂ A : C ], and projection [ π : Γ ◂ A -> Γ ]
     - [Q] : for each [Γ], [A], a tm [ te : Tm (Γ ◂ A) ]
   - some axioms, [rep1_axioms].

  The equivalence between these goes in two steps, essentially:
 
  - distributing the quantification over Γ, A to the outside;
  - reassociating the sigma-types.

*)

Definition rep2_data (pp : mor_total (preShv C)) : UU
  := ∏ (Γ : C) (A : Ty pp Γ : hSet),
           (∑ ΓAπ : ∑ ΓA : C, ΓA --> Γ, Tm pp (pr1 ΓAπ) : hSet).

Definition weq_rep2_rep1_data (pp : mor_total (preShv C))
  : rep2_data pp ≃ rep1_data pp.
Proof.
  unfold rep1_data, rep2_data.
  eapply weqcomp. apply weqonsecfibers; intro; apply weqforalltototal.
  refine (weqforalltototal _ _).
Defined.

Definition rep2 (pp : mor_total (preShv C)) : UU 
  := ∑ (Y : rep2_data pp), rep1_axioms (weq_rep2_rep1_data _ Y).

Definition weq_rep1_representation (pp : mor_total (preShv C))
  : rep1 pp ≃ cwf_representation pp.
Proof.
  simple refine (weqcomp _ _). { exact (rep2 pp). }
    eapply invweq, weqfp.
  unfold rep2, cwf_representation.
  eapply weqcomp. 
    unfold rep2_data, rep1_axioms.
    refine (@weqtotaltoforall C (fun Γ => (Ty pp Γ : hSet) -> _)
      (fun Γ Y => forall A, rep1_fiber_axioms A (pr2 (pr1 (Y A))) (pr2 (Y A)))).
  apply weqonsecfibers; intro Γ.
  eapply weqcomp.
    refine (@weqtotaltoforall _ _
      (fun A ΓAπt => rep1_fiber_axioms A (pr2 (pr1 ΓAπt)) (pr2 ΓAπt))).
  apply weqonsecfibers; intro A.
  unfold cwf_fiber_representation.
  (* reassociation:
     ((ΓAπ,t),(e,pb))
  ~> (ΓAπ,(t,(e,pb)))
  ~> (ΓAπ,((t,e),pb))
  *)
  eapply weqcomp.
    unfold rep1_fiber_axioms.
    use wetotal2asstor'.
  apply weqfp; intros ΓAπ.
  use wetotal2asstor'.
Defined.


Definition weq_rep1_rep2 (pp : mor_total (preShv C)) : rep1 pp ≃ rep2 pp.
Proof.
  set (XR := weqfp (weq_rep1_data pp)).
  eapply weqcomp. Focus 2. apply XR.
  apply weqfibtototal. intro y.
  apply weqonsecfibers. intro Γ. apply weqonsecfibers. intro A.
  apply idweq.
Defined.




Definition weq_cwf1_cwf : cwf1_structure ≃ cwf_structure C.
Proof.
  apply weqfibtototal.
Defined.








Definition fcompYo (pp : mor_total (preShv C)) : UU
  := ∏ Γ (A : Ty pp Γ : hSet),
       fpullback Yo pp (yy A).

Definition weq_fcomprehension_fcompYo (pp : mor_total (preShv C)) :
   fcomprehension Yo pp ≃ fcompYo pp.
Proof.
  apply weqonsecfibers.
  intro Γ.
  apply (weqonsecbase _ (@yy _ _ _ _ )).
Defined.

Definition weq_fcompYo_rep2 (pp : mor_total (preShv C))
  : rep2 pp ≃ fcompYo pp.
Proof.
  unfold fcompYo; unfold rep2.
  eapply weqcomp.
    set (XR := @weqtotaltoforall C). 
    unfold rep2_data. unfold rep2_axioms.
    specialize (XR (fun Γ => (Ty pp Γ : hSet) 
                             → ∑ ΓAp : ∑ ΓA : C, ΓA --> Γ, Yo (pr1 ΓAp) --> Tm pp)). 
    unfold dpr1, QQ1.
    specialize (XR (fun Γ p =>  ∏  (A : (Ty pp Γ : hSet)),
       ∑ e : # Yo (pr2 (pr1 (p A))) ;; yy A = (pr2 (p A) : preShv _ ⟦_,_⟧ );; pp,
       isPullback (yy A) pp (# Yo (pr2 (pr1 (p A)))) (pr2 (p A)) e)).
    apply XR.
  apply weqonsecfibers. intro Γ.
  eapply weqcomp.
    set (XR := @weqtotaltoforall  (Ty pp Γ : hSet)). simpl in XR.
    specialize (XR (fun _ =>  ∑ ΓAp : ∑ ΓA : C, ΓA --> Γ, Yo (pr1 ΓAp) --> Tm pp)).

    specialize (XR (fun A p =>  ∑ e : # Yo (pr2 (pr1 (p ))) ;; yy A =
                                     ((pr2 p : preShv C ⟦_,_⟧)) ;; pp, 
    isPullback (yy A) pp (# Yo (pr2 (pr1 (p )))) (pr2 (p )) e)).
    apply XR.
  apply weqonsecfibers. intro A. unfold fpullback.
  transparent assert (HXY :
      ( (∑ ΓAp : ∑ ΓA : C, ΓA --> Γ, Yo (pr1 ΓAp) --> Tm pp)
         ≃
         @fpullback_data _ _ (Yo) _ (Tm pp) _ (yy A) ) ).
  { apply weqtotal2asstor. }
  apply (weqbandf HXY).
  intro x.
  destruct x as [[XA pA] Q]. exact (idweq _ ).
Defined.

Lemma weq_rep1_fcomprehension (pp : mor_total (preShv C))
  : rep1 pp ≃ fcomprehension Yo pp.
Proof.
  apply invweq.
  eapply weqcomp. apply weq_fcomprehension_fcompYo.
  eapply weqcomp. Focus 2. eapply invweq. apply weq_rep1_rep2.
  apply (invweq (weq_fcompYo_rep2 _ )).
Defined.

Definition weq_cwf1_RelUnivYo : cwf1_structure ≃ RelUnivYo.
Proof.
  apply weqfibtototal.
  apply weq_rep1_fcomprehension.
Defined.   
 
(** ** Conclusion: an equivalence between [RelUnivYo] and [cwf_structure] *)

Definition weq_RelUnivYo_CwF : RelUnivYo ≃ cwf_structure C.
Proof.
  eapply weqcomp.
   apply (invweq weq_cwf1_RelUnivYo).
  apply (invweq weq_cwf_cwf1).
Defined.


(** ** Some unused results *)

(** The results below are no longer used, 
    but we retain them for possible future reference.
*)

Lemma isaprop_rep1_axioms (pp : mor_total (preShv C)) (Y : rep1_data pp) 
  : isaprop (rep1_axioms pp Y).
Proof.
  do 2 (apply impred; intro).
  apply isofhleveltotal2.
  - apply homset_property.
  - intro. apply isaprop_isPullback.
Qed.

Definition rep1_to_fcomprehension (pp : mor_total (preShv C)):
   rep1 pp → fcomprehension Yo pp.
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


Definition fcomprehension_to_rep1 (pp : mor_total (preShv C)):
  fcomprehension Yo pp → rep1 pp.
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


Lemma weq_fcomprehension_rep1_data (pp : mor_total (preShv C)):
   @fcomprehension_data _ _ Yo (Ty pp) (Tm pp) ≃ rep1_data pp.
Proof.
  unfold fcomprehension_data.
  unfold rep1_data.
  simpl.
  eapply weqcomp. Focus 2.
    set (XR := @weqforalltototal C).
    specialize (XR (fun Γ => (Ty pp Γ : hSet) → ∑ ΓA : C, ΓA --> Γ)).
    simpl in XR.
    specialize (XR (fun Γ pX =>  ∏  (A : (Ty pp Γ : hSet)),
              nat_trans (yoneda_ob_functor_data C (homset_property _) (pr1 (pX  A))) (Tm pp))).
    apply XR.
  apply weqonsecfibers. intro Γ. simpl.
  eapply weqcomp. Focus 2.
    set (XR := @weqforalltototal (Ty pp Γ : hSet)).
    specialize (XR (fun A =>  ∑ ΓA : C, ΓA --> Γ)). simpl in XR.
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


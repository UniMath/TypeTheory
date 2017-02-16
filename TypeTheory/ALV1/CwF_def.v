(**
  [TypeTheory.ALV1.CwF_def]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**
Contents:

- the canonical standalone definition of a (Fiore-style) CwF
- equivalence between this and two related ones occurring in the ALV1 paper
*)

Require Import UniMath.Foundations.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.
Require Import TypeTheory.ALV1.RelativeUniverses.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Defs.

Set Automatic Introduction.

Section Auxiliary.

(** A version of [weqtotal2asstor] with the type of the [C] argument slightly changed. Perhaps upstream? *)
Definition weqtotal2asstor' {A} {B : A -> Type} (C : ∏ a, B a -> Type)
  : (∑ (xy : ∑ x, B x), C _ (pr2 xy)) ≃ (∑ x y, C x y).
Proof.
  apply (weqtotal2asstor _ (fun xy => C (pr1 xy) (pr2 xy))).
Defined.

End Auxiliary.

(** * Definition of a CwF 

A (Fiore-style) CwF consists of:

- a base category C;
- a morphism Tm —p—> Ty of presheaves on C;
- a _representation_ of p.

*)

Section Fix_Category.

Variable C : Precategory.

Local Definition Ty (pp : mor_total (preShv C)) : functor _ _ := target pp.
Local Definition Tm (pp : mor_total (preShv C)) : functor _ _ := source pp.

(** ** Representations of maps of presheaves 

A *representation* of a map Tm —p—> Ty of presheaves consists of data exhibiting, for each (A : Ty Γ), the fiber of p over A as represented by some object Γ.A over Γ. *)

Section Representation.

Section Fiber_Representation.

Context (pp : mor_total (preShv C))
        {Γ : C}
        (A : Ty pp Γ : hSet).

Definition cwf_ext : UU := ∑ (ΓA : C), C ⟦ΓA, Γ⟧.

Definition cwf_tm (r : cwf_ext) : UU := 
  let ΓA := pr1 r in
  let π := pr2 r in
  ∑ v : (Tm pp ΓA : hSet), (morphism_from_total pp : nat_trans _ _ ) _ v = #(Ty pp) π A.

(* Lemma: convert the equality of elements of presheaves into the commutativity of a square involving representables. *)
Lemma cwf_square_comm
  (ext : cwf_ext) (ΓA := pr1 ext) (π := pr2 ext)
  (tm : cwf_tm ext) (v := pr1 tm) (e := pr2 tm)
  : #Yo π ;; yy A = yy v ;; pp.
Proof.
  apply pathsinv0.
  etrans. Focus 2. apply yy_natural.
  etrans. apply yy_comp_nat_trans.
  apply maponpaths, e.
Qed.

Definition cwf_fiber_representation : UU
  := ∑ (ΓAπ : cwf_ext) (ve : cwf_tm ΓAπ), 
     isPullback _ _ _ _ (cwf_square_comm ΓAπ ve).


Definition cwf_fiber_rep_data : UU
  := ∑ (ΓA : C), C ⟦ΓA, Γ⟧ × (Tm pp ΓA : hSet).

Section stuff.

Variable ΓAπt : cwf_fiber_rep_data.
Let ΓA : C := pr1 ΓAπt.
Let π : ΓA --> Γ := pr1 (pr2 ΓAπt).
Let v : Tm pp ΓA : hSet := pr2 (pr2 ΓAπt).

Definition _foo : (morphism_from_total pp : nat_trans _ _ ) _ v = #(Ty pp) π A
   -> #Yo π ;; yy A = yy v ;; pp.
Proof.
  intro H.
  apply pathsinv0.
  etrans. Focus 2. apply yy_natural.
  etrans. apply yy_comp_nat_trans.
  apply maponpaths, H.
Qed.

Definition cwf_fiber_rep_ax : UU 
  := ∑ (H : (morphism_from_total pp : nat_trans _ _ ) _ v = #(Ty pp) π A),
     isPullback _ _ _ _ (_foo H).

End stuff.


Definition cwf_fiber_representation' : UU
  := ∑ r : cwf_fiber_rep_data, cwf_fiber_rep_ax r.

Definition cwf_fiber_rep_data_weq 
  : cwf_fiber_rep_data ≃ ∑ (ΓA : C) (π : ΓA --> Γ), Tm pp ΓA : hSet.
Proof.
  unfold cwf_fiber_rep_data.
  set (XR := @weqtotal2asstor ). 
  specialize (XR C (fun x => x --> Γ)). cbn in XR.
  specialize (XR (fun Ap => Tm pp (pr1 Ap) : hSet)). cbn in XR.
  apply idweq.
Defined.

Definition cwf_fiber_representation_weq 
  : cwf_fiber_representation ≃ cwf_fiber_representation'.
Proof.
  unfold cwf_fiber_representation, cwf_fiber_representation'.
  eapply weqcomp.   (* (ΓA,π), ((v,e),P) *)
  eapply weqfibtototal. intro x.
    apply weqtotal2asstor. simpl. (*  (ΓA,π), (v, (e,P)) *)
  eapply weqcomp; [eapply invweq; apply weqtotal2asstol |]; simpl.  
  apply invweq.
  eapply weqcomp.
  apply weqtotal2asstor. cbn.
  apply weqfibtototal. intro ΓA.
  eapply weqcomp. apply weqtotal2asstor.
  apply idweq.
Defined.  


Definition yoneda_induction (F : preShv C) (Γ' : C) 
           (P : ((F : functor _ _ ) Γ' : hSet) -> UU) :
  (forall K : _ ⟦ Yo Γ', F ⟧, P (invmap (@yy _ _ F Γ') K)) -> 
  forall A : (F : functor _ _ ) Γ' : hSet, P A.
Proof.
  intros H A0.
  set(XR := homotinvweqweq (@yy _ (homset_property C) F Γ')).
  rewrite <- XR.
  apply H.
Defined.  


Lemma isaprop_cwf_fiber_representation' :
  is_category C -> isaprop cwf_fiber_representation'.
Proof.
  intro isC.
  apply invproofirrelevance.
  intros x x'. apply subtypeEquality.
  { intro. 
    apply isofhleveltotal2. 
    - apply setproperty.
    - intro. apply isaprop_isPullback.
  }
  destruct x as [x H]. 
  destruct x' as [x' H']. cbn.    
  destruct x as [ΓA m].
  destruct x' as [ΓA' m']. cbn in *.
  destruct H as [H isP].
  destruct H' as [H' isP'].
  simple refine (total2_paths_f _ _ ).
  - set (T1 := mk_Pullback _ _ _ _ _ _ isP).
    set (T2 := mk_Pullback _ _ _ _ _ _ isP').
    set (i := iso_from_Pullback_to_Pullback T1 T2). cbn in i.
    set (i' := invmap (weq_ff_functor_on_iso (yoneda_fully_faithful _ _ ) _ _ ) i ).
    set (TT := isotoid _ isC i').
    apply TT.
  - cbn.
    set (XT := transportf_dirprod _ (fun a' => C⟦a', Γ⟧) (fun a' => Tm pp a' : hSet)).
    cbn in XT.
    set (XT' := XT (tpair _ ΓA m : ∑ R : C, C ⟦ R, Γ ⟧ × (Tm pp R : hSet) )
                   (tpair _ ΓA' m' : ∑ R : C, C ⟦ R, Γ ⟧ × (Tm pp R : hSet) )).
    cbn in *.
    match goal with | [ |- transportf _ ?e _ = _ ] => set (TT := e) end.
    rewrite XT'.
    destruct m as [π te].
    destruct m' as [π' te'].
    cbn. 
    apply pathsdirprod.
    + unfold TT.
      rewrite transportf_isotoid.
      cbn.
      unfold precomp_with.
      rewrite id_right.
      unfold from_Pullback_to_Pullback. cbn.
      cbn in *.
      match goal with |[|- (_  ( _ ?PP _ _ _  _ ) )  _ _  ;; _ = _ ] => 
                       set (P:=PP) end.
      match goal with |[|- ( _ (PullbackArrow P ?PP ?E2 ?E3 _ )) _ _   ;; _ = _ ] 
                       => set (E1 := PP);
                         set (e1 := E1);
                         set (e2 := E2);
                         set (e3 := E3) end.
      match goal with |[|- ( _ (PullbackArrow _ _ _ _ ?E4 )) _ _   ;; _ = _ ] 
                       => set (e4 := E4) end.
      set (XR := PullbackArrow_PullbackPr1 P e1 e2 e3 e4).
      set (XR':= nat_trans_eq_pointwise XR ΓA'). 
      cbn in XR'. 
      assert (XR'':= toforallpaths _ _  _ XR').
      cbn in XR''.
      etrans. apply XR''.
      cbn. unfold yoneda_morphisms_data. apply id_left.
    + unfold TT. clear TT. clear XT' XT.
      match goal with |[|- transportf ?r  _ _ = _ ] => set (P:=r) end.
      match goal with |[|- transportf _ (_ _ _ (_ _ ?ii)) _ = _ ] => set (i:=ii) end.
      simpl in i.
      set (TR:= invmaponpathsweq (@yy _ (homset_property _ ) (Tm pp) ΓA')).
      apply TR; clear TR.
      etrans. apply transportf_yy.
      etrans. apply transportf_isotoid_functor.  
      set (XR := mk_Pullback _ _ _ _ _ _ isP).
      rewrite inv_from_iso_iso_from_fully_faithful_reflection.
      assert (XX:=homotweqinvweq (weq_from_fully_faithful 
                                    (yoneda_fully_faithful _ (homset_property C)) ΓA' ΓA )).
      etrans. apply maponpaths_2. apply XX.
      clear XX.
      etrans. apply maponpaths_2. apply id_right.
      etrans. apply maponpaths_2. unfold from_Pullback_to_Pullback. apply idpath.
      match goal with |[|- ( _ ?PP _ _ _  _ )  ;; _ = _ ] => 
                       set (PT:=PP) end.
      match goal with |[|- PullbackArrow _ ?PP ?E2 ?E3 _    ;; _ = _ ] 
                       => set (E1 := PP);
                         set (e1 := E1);
                         set (e2 := E2);
                         set (e3 := E3) end.
      match goal with |[|- PullbackArrow _ _ _ _ ?E4    ;; _ = _ ] 
                       => set (e4 := E4) end.
      set (XRT := PullbackArrow_PullbackPr2 PT e1 e2 e3 e4).
      etrans. apply XRT. apply idpath.
Qed.      

Lemma isaprop_cwf_fiber_representation :
  is_category C -> isaprop cwf_fiber_representation.
Proof.
  intro H.
  use isofhlevelweqb.
  - apply cwf_fiber_representation'.
  - apply cwf_fiber_representation_weq.
  - apply isaprop_cwf_fiber_representation'.
    apply H.
Defined.

End Fiber_Representation.

Definition cwf_representation (pp : mor_total (preShv C)) : UU 
  := ∏ Γ (A : Ty pp Γ : hSet), cwf_fiber_representation pp A.

End Representation.

(** ** Definition of CwF structure *)

Definition cwf_structure : UU := ∑ pp, (cwf_representation pp).

(** ** Natural model structure is equivalent to cwf structure when 
       underlying category is univalent *)

Definition natural_model_structure : UU 
  := ∑ pp : mor_total (preShv C),
            ∏ Γ (A : Ty pp Γ : hSet), ∥ cwf_fiber_representation pp A ∥.

Definition cwf_natural_model_weq : 
  is_category C -> cwf_structure ≃ natural_model_structure.
Proof.
  intro H.
  apply weqfibtototal.
  intro x.
  apply weqonsecfibers. intro Γ.
  apply weqonsecfibers. intro A.
  apply truncation_weq.
  apply isaprop_cwf_fiber_representation.
  apply H.
Defined.


(** ** Equivalence with relative universe structures on Yoneda *)


Lemma weq_cwf_representation_fcomprehension (pp : mor_total (preShv C))
  : cwf_representation pp ≃ fcomprehension Yo pp.
Proof.
  apply weqonsecfibers. intro Γ.
  (* convert the type argument under [yy] *) 
  eapply weqcomp.
    Focus 2. eapply invweq. 
    refine (weqonsecbase _ _). apply yy.
  apply weqonsecfibers. intro A.
  unfold cwf_fiber_representation, fpullback.
  (* reassociate the RHS to match the LHS:
       ((ΓA,(π,v)),(e,p))
    -> (((ΓA,π),v),(e,p))
    -> ((ΓA,π),(v,(e,p)))
    -> ((ΓA,π),((v,e),p))
  *)
  eapply weqcomp. Focus 2.
    refine (weqfp _ _).
    apply weqtotal2asstor'.
  eapply weqcomp. Focus 2.
    eapply weqtotal2asstol.
  eapply weqcomp. Focus 2.
    refine (weqfibtototal _ _ _).
    intro. apply weqtotal2asstor'.
  (* convert the term argument under [yy] *)
  apply weqfibtototal. intros [ΓA π]; simpl.
  simple refine (weqbandf _ _ _ _).
    simple refine (weqbandf _ _ _ _).
      apply yy.
  (* show the two forms of the equality axiom are equivalent *)
  - intros v; simpl.
    apply weqimplimpl.
    (* TODO: abstract the following, as bidirectional version of [cwf_square_comm]. *)
    + intros e. 
      refine (cwf_square_comm _ _ (_,,_) (_,,e)).
    + intros ey. 
      assert (ey' := nat_trans_eq_pointwise ey ΓA); clear ey; cbn in ey'.
      assert (ey'' := toforallpaths _ _ _ ey' (identity _)); clear ey';
      cbn in ey''.
      etrans. etrans. Focus 2. apply @pathsinv0, ey''.
      * apply maponpaths, @pathsinv0.
        apply (toforallpaths _ _ _ (functor_id (Tm pp) _)).
      * unfold yoneda_morphisms_data.
        apply maponpaths_2, id_left.
    + apply setproperty.
    + refine (homset_property (preShv C) _ _ _
        (fq _
          (ΓA,, π,, invmap (yoneda_weq C (homset_property C) ΓA (Tm pp)) v)
        ;; _)).
    (* Why does so much need to be given explicitly there? *)
  - intros [v e]; cbn.
    apply idweq.
Time Defined.


Definition weq_cwf_structure_RelUnivYo 
  : cwf_structure ≃ @relative_universe C _ Yo.
Proof.
  apply weqfibtototal.
  intro pp.
  apply weq_cwf_representation_fcomprehension.
Defined.


(** ** Representable vs represented *)

(*
    If the underlying category is univalent [is_category C],
    then the representation is unique, and hence there is no
    distinction between 'represented' and 'representable'
    morphism of presheaves
*)

Lemma isaprop_cwf_representation (is : is_category C) (pp : mor_total (preShv C))
  : isaprop (cwf_representation pp).
Proof.
  use isofhlevelweqb.
  - exact (fcomprehension Yo pp).
  - apply weq_cwf_representation_fcomprehension.
  - apply isaprop_fcomprehension. 
    + apply is.
    + apply yoneda_fully_faithful.
Qed.

End Fix_Category.


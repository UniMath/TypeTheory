(**
  [TypeTheory.ALV1.RelativeUniverses]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**

Contents:

- Definition of comprehension structure on a map, relative to a functor: [fcomprehension]
- [fcomprehension] is a proposition under saturation assumptions: [isaprop_fcomprehension]
- Definition of a relative universe: [relative_universe] (due to Vladimir Voevodsky)
- Transfer of a relative universe from one functor to another: [transfer_of_rel_univ_with_ess_surj]

*)

Require Import UniMath.Foundations.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.

Set Automatic Introduction.

Local Notation "[ C , D ]" := (functor_Precategory C D).

(** * Relative comprehension structures *)

(** Given a map [ p : Ũ —> U ] in a category [D], 
    and a functor [ F : C —> D ], _a comprehension structure for [p] 
    relative to [F]_ is an operation providing all pullbacks of [p] 
    along morphisms from objects of the form [F X]. *)

Section Relative_Comprehension.

Context {C D : precategory} (J : functor C D).
Context {U tU : D} (p : D ⟦tU, U⟧).

Definition fpullback_data {X : C} (f : D ⟦J X, U⟧) : UU 
  := ∑ Xf : C, C⟦Xf, X⟧ × D⟦J Xf, tU⟧.

Definition fpb_obj  {X : C} {f : D⟦J X, U⟧} (T : fpullback_data f) : C := pr1 T.
Definition fp {X : C} {f : D⟦J X, U⟧} (T : fpullback_data f) : C⟦fpb_obj T, X⟧ := pr1 (pr2 T).
Definition fq {X : C} {f : D⟦J X, U⟧} (T : fpullback_data f) : D⟦ J (fpb_obj T), tU⟧ := pr2 (pr2 T).

Definition fpullback_prop {X : C} {f : D ⟦J X, U⟧} (T : fpullback_data f) : UU
  := commutes_and_is_pullback f p (#J (fp T)) (fq T).

Definition fpullback {X : C} (f : D ⟦J X, U⟧) := 
  ∑ T : fpullback_data f, fpullback_prop T.

Coercion fpullback_data_from_fpullback {X : C} {f : D ⟦J X, U⟧} (T : fpullback f) :
   fpullback_data f := pr1 T.

Definition fcomprehension := ∏ X (f : D⟦J X, U⟧), fpullback f.

Definition is_universe_relative_to : UU
  := ∏ (X : C) (f : D⟦J X, _ ⟧), ∥ fpullback f ∥ .

(* TODO: add arguments declaration to make [U], [tU] explicit in this 
   def not depending on [p].  
   OR make it depend on [p] (which it conceptually should, though it formally doesn’t). *)
Definition fcomprehension_data := ∏ X (f : D⟦ J X, U⟧), fpullback_data f.
Definition fcomprehension_prop (Y : fcomprehension_data) :=
          ∏ X f, fpullback_prop (Y X f). 

(** An equivalent form of [fcomprehension], separating its data and properties by interchanging ∑ and ∏ *)
Definition fcomprehension_weq :
   fcomprehension ≃ ∑ Y : fcomprehension_data, fcomprehension_prop Y.
Proof.
  eapply weqcomp. Focus 2.
    set (XR:=@weqforalltototal (ob C)).
    specialize (XR (fun X => ∏ f : D⟦ J X, U⟧, fpullback_data f)). simpl in XR.
    specialize (XR (fun X pX => ∏ A, fpullback_prop  (pX  A))).
    apply XR.
  apply weqonsecfibers.
  intro X.
  apply weqforalltototal.
Defined.

End Relative_Comprehension.

(** ** Uniqueness lemmas regarding relative comprehension *)

Section Relative_Comprehension_Lemmas.

Context {C : precategory} {D : Precategory} (J : functor C D).
Context {U tU : D} (p : D ⟦tU, U⟧).

Lemma isaprop_fpullback_prop {X : C} {f : D ⟦J X, U⟧} (T : fpullback_data J f)
  : isaprop (fpullback_prop J p T).
Proof.
  apply isofhleveltotal2.
  - apply homset_property.
  - intros. apply isaprop_isPullback.
Qed.

Lemma isaprop_fpullback {X : C} (f : D ⟦J X, U⟧) 
      (is_c : is_category C)
      (HJ : fully_faithful J) (* NOTE: the weaker assumption “ff on isos” should be enough. *)
  : isaprop (fpullback J p f).
Proof.
  apply invproofirrelevance.
  intros x x'. apply subtypeEquality.
  - intro t. apply isaprop_fpullback_prop.
  - destruct x as [x H]. 
    destruct x' as [x' H']. cbn.    
    destruct x as [a m].
    destruct x' as [a' m']. cbn in *.
    destruct H as [H isP].
    destruct H' as [H' isP'].
    simple refine (total2_paths_f _ _ ).
    + unfold fpullback_prop in *.
      set (T1 := mk_Pullback _ _ _ _ _ _ isP).
      set (T2 := mk_Pullback _ _ _ _ _ _ isP').
      set (i := iso_from_Pullback_to_Pullback T1 T2). cbn in i.
      set (i' := invmap (weq_ff_functor_on_iso HJ a a') i ).
      set (TT := isotoid _ is_c i').
      apply TT.
    + cbn.
      set (XT := transportf_dirprod _ (fun a' => C⟦a', X⟧) (fun a' => D⟦J a', tU⟧)).
      cbn in XT.
      set (XT' := XT (tpair _ a m : ∑ a : C, C ⟦ a, X ⟧ × D ⟦ J a, tU ⟧ )
                     (tpair _ a' m' : ∑ a : C, C ⟦ a, X ⟧ × D ⟦ J a, tU ⟧ )).
      cbn in *.
      match goal with | [ |- transportf _ ?e _ = _ ] => set (TT := e) end.
      rewrite XT'.
      destruct m as [q r].
      destruct m' as [q' r'].
      cbn. 
      apply pathsdirprod.
      * unfold TT.
        rewrite transportf_isotoid.
        cbn.
        unfold precomp_with.
        rewrite id_right.
        rewrite id_right.
        unfold from_Pullback_to_Pullback. cbn.
        apply (invmaponpathsweq (weq_from_fully_faithful HJ _ _ )).
        assert (T:= homotweqinvweq (weq_from_fully_faithful HJ a' a)).
        cbn in *.
        rewrite functor_comp. rewrite T. clear T.
        clear XT' XT. clear TT. 
        assert (X1:= PullbackArrow_PullbackPr1 (mk_Pullback _ _ _ _ _ _ isP)).
        cbn in X1.
        apply X1.
      * unfold TT. clear TT. clear XT' XT.
        match goal with |[|- transportf ?r  _ _ = _ ] => set (P:=r) end.
        etrans. 
          apply (transportf_isotoid_functor).  
        cbn. unfold precomp_with. rewrite id_right. rewrite id_right.
        assert (XX:=homotweqinvweq (weq_from_fully_faithful HJ a' a  )).
        simpl in XX. rewrite XX. simpl. cbn.
        assert (X1:= PullbackArrow_PullbackPr2 (mk_Pullback _ _ _ _ _ _ isP)).
        apply X1.
Qed.

Lemma isaprop_fcomprehension  (is_c : is_category C) 
    (HJ : fully_faithful J) : isaprop (fcomprehension J p).
Proof.
  do 2 (apply impred; intro).
  apply isaprop_fpullback; assumption.
Qed.

End Relative_Comprehension_Lemmas.



(** * Relative universes *)

(** A _universe relative to a functor_ is just a map in the target category, 
    equipped with a relative comprehension structure. *)

Definition relative_universe {C D : precategory} (J : functor C D) : UU
  := ∑ X : mor_total D, fcomprehension J X.

Definition mere_relative_universe {C D : precategory} (J : functor C D) : UU
  := ∑ X : mor_total D, is_universe_relative_to J X.

(** ** Transfer of a relative universe *)

Section Rel_Univ_Structure_Transfer.

(** We give two sets of conditions under which a relative universe for one functor 
    can be transferred to one for another functor. 
    In each case, we start by assuming a commutative (up to iso) square of functors, 
    in which the right-hand functor _S_ preserves pullbacks. *)

Context
   {C : precategory} {D : Precategory}
   (J : functor C D)
   (RUJ : relative_universe J)

   {C' : precategory} {D' : Precategory}
   (J' : functor C' D')

   (R : functor C C') (S : functor D D')

   (α : [C, D'] ⟦functor_composite J S , functor_composite R J'⟧)
   (is_iso_α : is_iso α)

   (S_pb : maps_pb_squares_to_pb_squares _ _ S).

(** On top of this, we then assume either 
   - the assumptions that [R] is split essentially surjective and [S] split full; or else 
   - that [R] is essentially surjective and [S] full, plus that [J] is fully faithful 
     and [C'] saturated.  
     These last two assumptions imply uniqueness of the new comprehension structure, 
     and hence allow getting chosen inverses out of the (non-split) 
     surjectivity assumptions. 
*)

Let αiso := isopair α is_iso_α.
Let α' := inv_from_iso αiso. 
Let α'_α := nat_trans_eq_pointwise (iso_after_iso_inv αiso).
Let α_α' := nat_trans_eq_pointwise (iso_inv_after_iso αiso).

Local Definition α_iso : forall X, is_iso (pr1 α X).
Proof.
  intros.
  apply is_functor_iso_pointwise_if_iso.
  assumption.
Qed.

Local Definition α'_iso : forall X, is_iso (pr1 α' X).
Proof.
  intros.
  apply is_functor_iso_pointwise_if_iso.
  apply is_iso_inv_from_iso.
Qed.

Local Notation tU := (source (pr1 RUJ)).
Local Notation U :=  (target (pr1 RUJ)).
Local Notation pp := (morphism_from_total (pr1 RUJ)).


Definition fcomprehension_induced_with_ess_split
    (R_es : split_ess_surj R)
    (S_sf : split_full S)
  :  fcomprehension J' (# S (pr1 RUJ)).
Proof.
  cbn in α, α', α'_α.
  intros X' g.
  set (Xi := R_es X'); destruct Xi as [X i]; clear R_es.
  set (f' := (α X ;; #J' i ;; g) : D' ⟦ S (J X), S U ⟧).
  destruct (S_sf _ _ f') as [f e_Sf_f']; clear S_sf.
  set (Xf :=  (pr2 RUJ) _ f); clearbody Xf.
  destruct Xf as [H A].
  destruct H as [Xf [p q]].
  destruct A as [e isPb]. cbn in e, isPb.
  assert (Sfp := S_pb _ _ _ _ _ _ _ _ _ isPb); clear S_pb.
  set (HSfp := functor_on_square D D' S e) in *; clearbody HSfp.
  simple refine (tpair _ _ _ ).
  { exists (R Xf); split.
    - exact (#R p ;; i).
    - refine (α' Xf ;; #S q).
  }
  cbn. unfold fpullback_prop.
  simple refine (commutes_and_is_pullback_transfer_iso _ _ _ _ _ Sfp).
  - apply identity_iso.
  - refine (iso_comp _ (functor_on_iso J' i)).
    exists (α _); apply α_iso.
  - apply identity_iso.
  - cbn. exists (α _); apply α_iso.
  - cbn. rewrite id_right.
    apply e_Sf_f'.
  - rewrite id_left. apply id_right.
  - cbn. rewrite functor_comp.
    repeat rewrite assoc. apply maponpaths_2, (nat_trans_ax α).
  - cbn. rewrite id_right. apply pathsinv0.
    rewrite assoc. eapply @pathscomp0. apply maponpaths_2, α_α'.
    apply id_left.
Qed.

Definition transfer_of_rel_univ_with_ess_split 
    (R_es : split_ess_surj R)
    (S_sf : split_full S)
  : relative_universe J'.
Proof.
  exists (morphism_as_total (#S pp)).
  apply fcomprehension_induced_with_ess_split; assumption.
Defined.

Definition fpullback_induced_with_ess_surj
           (R_es : essentially_surjective R)
           (C'_sat : is_category C')
           (J'_ff : fully_faithful J')
           (* TODO: only “ff on isos” should be needed; see note at [isaprop_fpullback]. *)
           (S_full : full S)
           (X' : C')
           (g : D' ⟦ J' X', S U ⟧)
: fpullback J' (# S (pr1 RUJ)) g.
Proof.
  cbn in α, α', α'_α.
  set (Xi := R_es X').
  apply (squash_to_prop Xi).
    { apply (isaprop_fpullback J'); assumption. }
  intros [X i]; clear Xi R_es.
  set (f' := (α X ;; #J' i ;; g) : D' ⟦ S (J X), S U ⟧).
  set (fe := S_full _ _ f').
  apply (squash_to_prop fe).
    { apply (isaprop_fpullback J'); assumption. }
  intros [f e_Sf_f']; clear fe S_full.
  set (Xf :=  (pr2 RUJ) _ f); clearbody Xf.
  destruct Xf as [H A].
  destruct H as [Xf [p q]].
  destruct A as [e isPb]. cbn in e, isPb.
  assert (Sfp := S_pb _ _ _ _ _ _ _ _ _ isPb); clear S_pb.
  set (HSfp := functor_on_square D D' S e) in *; clearbody HSfp.
  simple refine (tpair _ _ _ ).
  { exists (R Xf); split.
    - exact (#R p ;; i).
    - refine (α' Xf ;; #S q).
  }
  cbn. unfold fpullback_prop.
  simple refine (commutes_and_is_pullback_transfer_iso _ _ _ _ _ Sfp).
  - apply identity_iso.
  - refine (iso_comp _ (functor_on_iso J' i)).
    exists (α _); apply α_iso.
  - apply identity_iso.
  - cbn. exists (α _); apply α_iso.
  - cbn. rewrite id_right.
    apply e_Sf_f'.
  - rewrite id_left. apply id_right.
  - cbn. rewrite functor_comp.
    repeat rewrite assoc. apply maponpaths_2, (nat_trans_ax α).
  - cbn. rewrite id_right. apply pathsinv0.
    rewrite assoc. eapply @pathscomp0. apply maponpaths_2, α_α'.
    apply id_left.
Defined.

Definition fcomprehension_induced_with_ess_surj
   (R_es : essentially_surjective R)
   (C'_sat : is_category C')
   (J'_ff : fully_faithful J')
     (* TODO: only “ff on isos” should be needed; see note at [isaprop_fpullback]. *)
   (S_full : full S)
  :  fcomprehension J' (# S (pr1 RUJ)).
Proof.
  cbn in α, α', α'_α.
  intros X' g.
  apply fpullback_induced_with_ess_surj; assumption.
Defined.

Definition transfer_of_rel_univ_with_ess_surj
    (R_es : essentially_surjective R)
    (C'_sat : is_category C')
    (J'_ff : fully_faithful J')
     (* TODO: only “ff on isos” should be needed; see note at [isaprop_fpullback]. *)
    (S_full : full S)
  : relative_universe J'.
Proof.
  exists (morphism_as_total (#S pp)).
  apply fcomprehension_induced_with_ess_surj; assumption.
Defined.


End Rel_Univ_Structure_Transfer.


(** ** Transfer of morphisms that merely are a relative universe: truncation *)

(** The next section literally copies a proof from the
    preceding section, with the exception of a truncation elimination
    in the middle of the proof.
    TODO: see if one can factor out a common lemma between the
          truncated lemma below and the untruncated lemma above.
*)
    

Section Is_universe_relative_to_Transfer.

Context
   {C : precategory} {D : Precategory}
   (J : functor C D)

   {C' : precategory} {D' : Precategory}
   (J' : functor C' D')

   (R : functor C C') (S : functor D D')

   (α : [C, D'] ⟦functor_composite J S , functor_composite R J'⟧)
   (is_iso_α : is_iso α)

   (S_pb : maps_pb_squares_to_pb_squares _ _ S).

Let αiso := isopair α is_iso_α.
Let α' := inv_from_iso αiso. 
Let α'_α := nat_trans_eq_pointwise (iso_after_iso_inv αiso).
Let α_α' := nat_trans_eq_pointwise (iso_inv_after_iso αiso).


Context
  (R_es : essentially_surjective R)
  (C'_sat : is_category C')
  (J'_ff : fully_faithful J')
  (* TODO: only “ff on isos” should be needed; see note at [isaprop_fpullback]. *)
  (S_full : full S).

Section fix_a_morphism.

Variables (U tU : D) (pp : tU --> U).

Section map_on_is_universe_relativ_to.

Hypothesis is : is_universe_relative_to J pp.


Lemma mere_fpullback_transfer {X' : C'} (g : D' ⟦ J' X', S U ⟧)
  : ∥ fpullback J' (# S pp) g ∥.
Proof.
  cbn in α, α', α'_α.
  set (Xi := R_es X').
  apply (squash_to_prop Xi).
  { apply propproperty. }
  intros [X i]; clear Xi R_es.
  set (f' := (α X ;; #J' i ;; g) : D' ⟦ S (J X), S U ⟧).
  set (fe := S_full _ _ f').
  apply (squash_to_prop fe).
  { apply propproperty. } 
  intros [f e_Sf_f']; clear fe S_full.
  set (Xf' := is _ f).
  apply (squash_to_prop Xf').
  { apply propproperty. } 
  intro Xf.
  destruct Xf as [H A].
  destruct H as [Xf [p q]].
  destruct A as [e isPb]. cbn in e, isPb.
  assert (Sfp := S_pb _ _ _ _ _ _ _ _ _ isPb); clear S_pb.
  set (HSfp := functor_on_square D D' S e) in *; clearbody HSfp.
  apply hinhpr.
  simple refine (tpair _ _ _ ).
  { exists (R Xf); split.
    - exact (#R p ;; i).
    - refine (α' Xf ;; #S q).
  }
  cbn. unfold fpullback_prop.
  simple refine (commutes_and_is_pullback_transfer_iso _ _ _ _ _ Sfp).
  - apply identity_iso.
  - refine (iso_comp _ (functor_on_iso J' i)).
    exists (α _). apply α_iso. apply is_iso_α.
  - apply identity_iso.
  - cbn. exists (α _). apply α_iso. apply is_iso_α.
  - cbn. rewrite id_right.
    apply e_Sf_f'.
  - rewrite id_left. apply id_right.
  - cbn. rewrite functor_comp.
    repeat rewrite assoc. apply maponpaths_2, (nat_trans_ax α).
  - cbn. rewrite id_right. apply pathsinv0.
    rewrite assoc. eapply @pathscomp0. apply maponpaths_2, α_α'.
    apply id_left.
Defined.


Lemma is_universe_transfer : is_universe_relative_to J' (#S pp).
Proof.
  intros X' g.
  apply (mere_fpullback_transfer g).
Defined.

End map_on_is_universe_relativ_to.

Definition αpwiso X : iso (S (J X)) (J' (R X))
  := functor_iso_pointwise_if_iso _ _ _ _ _ α is_iso_α X.


Definition isweq_is_universe_transfer 
           (R_full : full R) (* full on isos might be sufficient *)
           (S_ff : fully_faithful S) (* we need that S reflects pullbacks and 
                                        that S is full *)
  : isweq is_universe_transfer.
Proof.
  use (gradth _ _ _ _ ).
  - intro H.
    intros X f.
    set (RX := R X). set (f' := (α' : nat_trans _ _ ) X ;; #S f).
    set (Pb_RX_f' := H RX f').
    apply (squash_to_prop Pb_RX_f'). 
    { apply propproperty. }
    intro T.
    destruct T as [X1 X2].
    destruct X1 as [X' [p' q']].
    destruct X2 as [H1 H2]. cbn in H1. cbn in H2.
    unfold RX in *. clear RX. clear Pb_RX_f'.
    
    apply (squash_to_prop (R_es X')). 
    { apply propproperty. }
    intros [Xf i].
    
    (* get a preimage of [i · 'p] *)
    apply (squash_to_prop (R_full _ _ (i · p'))).
    { apply propproperty. } 
    intros [ip' Hip'].
    apply hinhpr.
    repeat mkpair.
    + apply Xf.
    + exact ip'.
    + set (hi := (α : nat_trans _ _ ) Xf). cbn in hi.
      set (XR := hi ;; functor_on_iso J' i ;; q').
      exact (invmap (weq_from_fully_faithful S_ff _ _ ) XR).
    + cbn. apply (invmaponpathsweq (weq_from_fully_faithful S_ff _ _ )).
      cbn. apply pathsinv0.
      etrans. rewrite functor_comp. apply maponpaths_2.
              apply (homotweqinvweq (weq_from_fully_faithful S_ff _ _ )).
      unfold f' in H1. unfold f' in H2. clear f'.
      etrans. eapply pathsinv0. repeat rewrite <- assoc.
              apply maponpaths. apply maponpaths. apply H1.
      rewrite functor_comp.
      repeat rewrite assoc. apply maponpaths_2.
      apply pathsinv0. rewrite <- assoc. rewrite <- assoc.
      apply (iso_inv_to_left D' _ _ _ (αpwiso Xf )).
      cbn. unfold precomp_with. rewrite id_right.
      assert (XR := nat_trans_ax α').
      apply pathsinv0. 
      etrans. Focus 2. apply XR.
      cbn.
      apply pathsinv0. 
      etrans. apply maponpaths_2. apply maponpaths. 
            apply Hip'.
      rewrite functor_comp.
      apply pathsinv0, assoc.
    + cbn. 
      match goal with |[|- isPullback _ _ _ _ (?HH)] => generalize HH end.
      intro HH.
      use (isPullback_preimage_square _ _ _ _ S_ff). 
      { apply homset_property. }
      match goal with |[|- isPullback _ _ _ _ (?HH)] => generalize HH end.
      assert (XR := homotweqinvweq (weq_from_fully_faithful S_ff (J Xf) tU )).
      simpl in XR. rewrite XR.
      clear HH XR.
      intro HH.
      use (isPullback_transfer_iso _ _ _ _ _ _ H2).
      * exact (identity_iso _ ).
      * exact (iso_inv_from_iso (αpwiso _ )).
      * exact (identity_iso _ ).
      * apply (iso_comp (functor_on_iso J' (iso_inv_from_iso i)) 
                        (iso_inv_from_iso (αpwiso _ ))).
      * cbn. rewrite id_right. 
        unfold precomp_with. rewrite id_right.
        unfold f'. apply idpath.
      * rewrite id_left. rewrite id_right. apply idpath.
      * cbn. unfold precomp_with. rewrite id_right. rewrite id_right.
        assert (XR := nat_trans_ax α').
        cbn in XR. 
        etrans. Focus 2. apply assoc.
        rewrite <- XR.
        rewrite assoc.
        apply maponpaths_2.
        rewrite <- functor_comp. 
        apply maponpaths.
        apply pathsinv0.
        etrans. apply maponpaths. 
          apply Hip'.
        rewrite assoc.
        rewrite iso_after_iso_inv.
        apply id_left.
      * cbn. rewrite id_right.
        unfold precomp_with. rewrite id_right.
        apply pathsinv0.
        do 2 rewrite assoc.
        etrans. apply maponpaths_2. apply assoc4.
        etrans. apply maponpaths_2. apply maponpaths_2. apply maponpaths.
          apply α'_α.
        rewrite id_right.
        rewrite <- functor_comp.
        rewrite iso_after_iso_inv.
        rewrite functor_id.
        apply id_left.
  - intros. apply proofirrelevance. 
    do 2 (apply impred; intro); apply propproperty.
  - intros. apply proofirrelevance. 
    do 2 (apply impred; intro); apply propproperty.
Defined.

End fix_a_morphism.

Definition mere_universe_transfer : 
  mere_relative_universe J -> mere_relative_universe J'.
Proof.
  use bandfmap.
  - apply (functor_on_mor_total S).
  - intro pp. cbn.
    apply is_universe_transfer.
Defined.


Definition isweq_mere_universe_transfer 
           (R_full : full R)
           (isD : is_category D) (isD' : is_category D')
           (T : functor D' D)
           (eta : iso (C:=[D, D, pr2 D]) (functor_identity D) (S ∙ T))
           (eps : iso (C:=[D', D', pr2 D']) (T ∙ S) (functor_identity D'))
           (S_ff : fully_faithful S) (* redundant, but that lemma is still missing *)
  : isweq mere_universe_transfer.
Proof.
  apply isweqbandfmap_var.
  - use isweq_equivalence_on_mor_total.
    + apply isD.
    + apply isD'.
    + apply T.
    + apply eta.
    + apply eps.
  - intro pp.
    apply isweq_is_universe_transfer.
    + apply R_full.
    + apply S_ff.
Defined.

Definition weq_mere_universe_transfer
           (R_full : full R)
           (isD : is_category D) (isD' : is_category D')
           (T : functor D' D)
           (eta : iso (C:=[D, D, pr2 D]) (functor_identity D) (S ∙ T))
           (eps : iso (C:=[D', D', pr2 D']) (T ∙ S) (functor_identity D'))
           (S_ff : fully_faithful S)
: mere_relative_universe J ≃ mere_relative_universe J'
:= weqpair _ (isweq_mere_universe_transfer R_full isD isD' T eta eps S_ff).

End Is_universe_relative_to_Transfer.

(* *)
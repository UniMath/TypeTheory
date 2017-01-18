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

(** Given a map [ p : Ũ —> U ] in a category [D], and a functor [ F : C —> D ], _a comprehension structure for [p] relative to [F]_ is an operation providing all pullbacks of [p] along morphisms from objects of the form [F X]. *)

Section Relative_Comprehension.

Context {C D : precategory} (J : functor C D).
Context {U tU : D} (p : D ⟦tU, U⟧).

Definition fpullback_data {X : C} (f : D ⟦J X, U⟧) : UU 
  := Σ Xf : C, C⟦Xf, X⟧ × D⟦J Xf, tU⟧.

Definition fpb_obj  {X : C} {f : D⟦J X, U⟧} (T : fpullback_data f) : C := pr1 T.
Definition fp {X : C} {f : D⟦J X, U⟧} (T : fpullback_data f) : C⟦fpb_obj T, X⟧ := pr1 (pr2 T).
Definition fq {X : C} {f : D⟦J X, U⟧} (T : fpullback_data f) : D⟦ J (fpb_obj T), tU⟧ := pr2 (pr2 T).

Definition fpullback_prop {X : C} {f : D ⟦J X, U⟧} (T : fpullback_data f) : UU
  := commutes_and_is_pullback f p (#J (fp T)) (fq T).

Definition fpullback {X : C} (f : D ⟦J X, U⟧) := 
  Σ T : fpullback_data f, fpullback_prop T.

Coercion fpullback_data_from_fpullback {X : C} {f : D ⟦J X, U⟧} (T : fpullback f) :
   fpullback_data f := pr1 T.

Definition fcomprehension := Π X (f : D⟦J X, U⟧), fpullback f.

(* TODO: add arguments declaration to make [U], [tU] explicit in this def not depending on [p].  OR make it depend on [p] (which it conceptually should, though it formally doesn’t). *)
Definition fcomprehension_data := Π X (f : D⟦ J X, U⟧), fpullback_data f.
Definition fcomprehension_prop (Y : fcomprehension_data) :=
          Π X f, fpullback_prop (Y X f). 

(** An equivalent form of [fcomprehension], separating its data and properties by interchanging Σ and Π *)
Definition fcomprehension_weq :
   fcomprehension ≃ Σ Y : fcomprehension_data, fcomprehension_prop Y.
Proof.
  eapply weqcomp. Focus 2.
    set (XR:=@weqforalltototal (ob C)).
    specialize (XR (fun X => Π f : D⟦ J X, U⟧, fpullback_data f)). simpl in XR.
    specialize (XR (fun X pX => Π A, fpullback_prop  (pX  A))).
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
    simple refine (total2_paths _ _ ).
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
      set (XT' := XT (tpair _ a m : Σ a : C, C ⟦ a, X ⟧ × D ⟦ J a, tU ⟧ )
                     (tpair _ a' m' : Σ a : C, C ⟦ a, X ⟧ × D ⟦ J a, tU ⟧ )).
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
        set (T:=@functtransportf _ _ (functor_on_objects J) (fun a' => D⟦ a', tU⟧)).
        rewrite T.
        rewrite <- functtransportf.
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

(** A _universe relative to a functor_ is just a map in the target category, equipped with a relative comprehension structure. *)

Definition relative_universe {C D : precategory} (J : functor C D) : UU
  := Σ X : mor_total D, fcomprehension J X.

(** ** Transfer of a relative universe *)

Section Rel_Univ_Structure_Transfer.

(** We give two sets of conditions under which a relative universe for one functor can be transferred to one for another functor. In each case, we start by assuming a commutative (up to iso) square of functors, in which the right-hand functor _S_ preserves pullbacks. *)

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

(** On top of this, we then assume either the assumptions that _R_ is split essentially surjective and _S_ split full; or else that _R_ is essentially surjective and _S_ full, plus that _J_ is fully faithful and _C'_ saturated.  These last two assumptions imply uniqueness of the new comprehension structure, and hence allow getting chosen inverses out of the (non-split) surjectivity assumptions. *)

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
Qed.

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
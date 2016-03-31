
(**

 Ahrens, Lumsdaine, Voevodsky, 2015 - 2016

*)

Require Export Systems.Auxiliary.
Require Export Systems.UnicodeNotations.
Require Export UniMath.Foundations.Basics.Sets.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.more_on_pullbacks.
Require Export UniMath.CategoryTheory.UnicodeNotations.
Require Export UniMath.CategoryTheory.functor_categories.

Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).

Section fix_some_stuff.

Variables C D : precategory.
Variables (hsC : has_homsets C) (hsD : has_homsets D).
Variable J : functor C D.

Section fix_a_morphism.

Variables U tU : D.
Variable pp : D ⟦tU, U⟧.

Definition fpullback_data {X : C} (f : D ⟦J X, U⟧) : UU 
  := Σ Xf : C, C⟦Xf, X⟧ × D⟦J Xf, tU⟧.

Definition fpb_obj  {X : C} {f : D⟦J X, U⟧} (T : fpullback_data f) : C := pr1 T.
Definition fp {X : C} {f : D⟦J X, U⟧} (T : fpullback_data f) : C⟦fpb_obj T, X⟧ := pr1 (pr2 T).
Definition fq {X : C} {f : D⟦J X, U⟧} (T : fpullback_data f) : D⟦ J (fpb_obj T), tU⟧ := pr2 (pr2 T).

Definition fpullback_prop {X : C} {f : D ⟦J X, U⟧} (T : fpullback_data f) : UU 
  := Σ (fe : #J(fp T) ;; f = fq T ;; pp), isPullback _ _ _ _ fe .

Lemma isaprop_fpullback_prop {X : C} {f : D ⟦J X, U⟧} (T : fpullback_data f)
  : isaprop (fpullback_prop T).
Proof.
  apply isofhleveltotal2.
  - apply hsD.
  - intros. apply isaprop_isPullback.
Qed.

Definition fpullback {X : C} (f : D ⟦J X, U⟧) := 
  Σ T : fpullback_data f, fpullback_prop T.

Coercion fpullback_data_from_fpullback {X : C} {f : D ⟦J X, U⟧} (T : fpullback f) :
   fpullback_data f := pr1 T.

Definition fcomprehension := ∀ X (f : D⟦J X, U⟧), fpullback f.

Definition fcomprehension_data := ∀ X (f : D⟦ J X, U⟧), fpullback_data f.
Definition fcomprehension_prop (Y : fcomprehension_data) :=
          ∀ X f, fpullback_prop (Y X f). 

Definition fcomprehension_weq :
   fcomprehension ≃ Σ Y : fcomprehension_data, fcomprehension_prop Y.
Proof.
  eapply weqcomp. Focus 2.
    set (XR:=@weqforalltototal (ob C)).
    specialize (XR (fun X => ∀ f : D⟦ J X, U⟧, fpullback_data f)). simpl in XR.
    specialize (XR (fun X pX => ∀ A, fpullback_prop  (pX  A))).
    apply XR.
  apply weqonsecfibers.
  intro X.
  apply weqforalltototal.
Defined.

Lemma isaprop_fpullback {X : C} (f : D ⟦J X, U⟧) (is_c : is_category C)(is_d : is_category D) 
    (HJ : fully_faithful J)
  : isaprop (fpullback f).
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
      destruct m as [p q].
      destruct m' as [p' q'].
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
        assert (Xt:=maponpaths_isotoid _ _ J is_c is_d).
        rewrite Xt.
        rewrite functor_on_iso_iso_from_fully_faithful_reflection.
        rewrite transportf_isotoid.
        unfold iso_from_Pullback_to_Pullback.
        cbn.
        unfold precomp_with.
        rewrite id_right.
        assert (X1:= PullbackArrow_PullbackPr2 (mk_Pullback _ _ _ _ _ _ isP)).
        cbn in X1.
        apply X1.
Qed.


Lemma isaprop_fcomprehension  (is_c : is_category C)(is_d : is_category D) 
    (HJ : fully_faithful J) : isaprop fcomprehension.
Proof.
  do 2 (apply impred; intro).
  apply isaprop_fpullback; assumption.
Qed.  

End fix_a_morphism.


(** to upstream *)
Definition arrow (E : precategory) : UU
  := Σ (ab : E × E), E⟦pr2 ab, pr1 ab⟧.
Definition source {E} (X : arrow E) : E := pr2 (pr1 X).
Definition target {E} (X : arrow E) : E := pr1 (pr1 X).
Definition morphism_from_arrow {E} (X : arrow E)
  : E⟦source X, target X⟧
  := pr2 X.
Coercion morphism_from_arrow : arrow >-> precategory_morphisms.

Definition relative_universe_structure : UU :=
  Σ X : arrow D, fcomprehension (target X) (source X)
      (morphism_from_arrow X).


End fix_some_stuff.

Section rel_univ_structure_and_functors.

Variables C D : precategory.
Variable J : functor C D.
Variable RUJ : relative_universe_structure _ _ J.

Variables C' D' : precategory.
Variable J' : functor C' D'.
Variable J'ff : fully_faithful J'.
Variable isC' : is_category C'.
Variable isD' : is_category D'.

Variables (R : functor C C') (S : functor D D').

Variable a :   [C, D', pr2 isD'] ⟦functor_composite J S , functor_composite R J'⟧.
Hypothesis is_iso_a : is_iso a.

Let a' := inv_from_iso (isopair a is_iso_a).  
Let TA':= iso_after_iso_inv (isopair (C:=[C, D', pr2 isD']) a is_iso_a).
Let TAA := is_functor_iso_pointwise_if_iso _ _ _ _ _ a'.
Let aiso := isopair a is_iso_a.

Local Definition a'iso : forall X, is_iso (pr1 a' X).
Proof.
  intros.
  apply TAA.
  apply (is_iso_inv_from_iso).
Qed.
  
(*
Let T := inv_from_iso (isopair (C:=[C, D', pr2 isD']) a is_iso_a).
Let TA := iso_inv_after_iso (isopair )).
*)

Hypothesis Res : essentially_surjective R.
Hypothesis Sff : fully_faithful S.
Hypothesis Spb : maps_pb_squares_to_pb_squares _ _ S.

Local Notation tU := (source (pr1 RUJ)).
Local Notation U :=  (target (pr1 RUJ)).
Local Notation pp := (morphism_from_arrow (pr1 RUJ)).

(*
Let e {X : C} (f : D ⟦J X, U⟧) (* :  #J(fp _ _ _ X) ;; f = fq X ;; pp *)
  := pr1 (pr1 (pr2 (pr2 (pr2 RUJ)) X f)).
*)

Definition fcomprehension_induced
  :  fcomprehension C' D' J' (S U) (S tU) (# S (pr1 RUJ)).
  intros X' g.
  set (preimg := Res X'). cbn. simpl.
  apply (squash_to_prop preimg).
  - apply isaprop_fpullback.
    + apply (pr2 isD').
    + apply isC'.
    + apply isD'.
    + apply J'ff.
  - intros [X i].
    set (f' := pr1 a X ;; #J' i ;; g : D' ⟦ S (J X), S U ⟧). 
    set (f := invmap (weq_from_fully_faithful Sff _ _ ) f').
    set (Xf :=  (pr2 RUJ) _ f). 
    destruct Xf as [H A].
    destruct H as [Xf [p q]].
    destruct A as [e isPb]. cbn in *.
    set (Sfp := Spb _ _ _ _ _ _ _ _ _ isPb).
    simple refine (tpair _ _ _ ).
    + simple refine (tpair _ _ _ ).
      * apply (R Xf).
      * { cbn. split.
          - apply (#R p ;; i).
          - apply (identity _ ;; (a' Xf ;; #S q)).
        }
    + cbn.
      simple refine (tpair _ _ _ ).
      * cbn.
        set (HSfp := functor_on_square D D' S e).
        rewrite id_left.
        rewrite <- assoc.
        rewrite <- HSfp. clear HSfp.
        rewrite assoc.
        assert (Ha':= nat_trans_ax a'). cbn in Ha'.
        rewrite <- Ha'. clear Ha'.
        unfold f in e. cbn in e.
        unfold f' in e.
        unfold f.
        assert (XTT:=homotweqinvweq (weq_from_fully_faithful Sff (J X) U )).
        cbn in XTT. rewrite XTT. clear XTT.
        unfold f'.
        rewrite functor_comp. 
        repeat rewrite <- assoc. 
        apply maponpaths. repeat rewrite assoc. apply cancel_postcomposition.
        assert (XXX:= nat_trans_eq_pointwise TA'). cbn in XXX.
        rewrite XXX. apply pathsinv0. apply id_left.
      * 
        cbn.
        match goal with |[|- isPullback _ _ _ _ ?eee] => generalize eee end.
        assert (XXX : g = #J' (inv_from_iso i) ;; a' _ ;; #S f).
        { clear Sfp.  clear isPb.
          unfold f.
          assert (XX:=homotweqinvweq (weq_from_fully_faithful Sff (J X) U )).
          cbn in XX. rewrite XX.
          unfold f'.
          repeat rewrite assoc.
          match goal with |[ |- _ = ?A1 ;; _ ;; _ ;; ?A2 ;; ?A3] =>
                           pathvia (A1 ;; A2 ;; A3) end.
          - rewrite <- functor_comp.
            rewrite iso_after_iso_inv. rewrite functor_id.
            apply pathsinv0. apply id_left.
          - do 2 apply cancel_postcomposition.
            rewrite <- assoc.
            assert (XXX := nat_trans_eq_pointwise TA').
            cbn in XXX. rewrite XXX.
            apply pathsinv0. apply id_right.          
        }
        rewrite XXX. clear XXX.
        rewrite <- assoc.
        clear preimg. clear TA'.
        {
        intro Hp.
        simple refine
               (isPullback_iso_of_morphisms _ _ _ _ _ _ _ _ _ _ _ _ ).
        - apply (pr2 isD').
        - apply (#J' (#R p)). 
        - repeat rewrite assoc.
          repeat rewrite assoc in Hp.
          rewrite id_left in Hp.
          rewrite <- Hp.
          rewrite functor_comp.
          do 2 apply cancel_postcomposition.
          rewrite <- assoc.
          rewrite <- functor_comp.
          rewrite iso_inv_after_iso.
          rewrite functor_id. apply pathsinv0, id_right.
        - apply (functor_on_iso_is_iso _ _ _ _ _  (iso_inv_from_iso i)).
        - apply identity_is_iso.
        - rewrite id_left.
          rewrite functor_comp. rewrite <- assoc.
          rewrite <- functor_comp. rewrite iso_inv_after_iso.
          rewrite functor_id. apply id_right.
        - match goal with |[|- isPullback _ _ _ _ ?HHH ]
                           => generalize HHH end.
          clear Hp.
          intro Hp.
          simple refine
                 (isPullback_iso_of_morphisms _ _ _ _ _ _ _ _ _ _ _ _ ).
          + apply (pr2 isD').
          + cbn. apply (#S (#J p)).
          + apply functor_on_square. assumption.
          + apply a'iso.
          + apply a'iso. 
          + apply (nat_trans_ax a').
          + apply Spb.
            assumption.
        } 
Qed.


Definition rel_univ_struct_functor : relative_universe_structure _ _ J'.
Proof.
  mkpair.
  mkpair.
  exists (S U).
  exact (S tU).
  apply (#S pp). cbn.
  apply fcomprehension_induced.
Defined.
  

End rel_univ_structure_and_functors.

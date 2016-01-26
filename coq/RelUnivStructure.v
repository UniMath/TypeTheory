
(**

 Ahrens, Lumsdaine, Voevodsky, 2015 - 2016

*)

Require Export Systems.Auxiliary.
Require Export Systems.UnicodeNotations.
Require Export UniMath.Foundations.Basics.Sets.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Export UniMath.CategoryTheory.UnicodeNotations.



Section fix_some_stuff.

Variables C D : precategory.
Variables (hsC : has_homsets C) (hsD : has_homsets D).
Variable J : functor C D.

Section fix_a_morphism.

Variables tU U : D.
Variable pp : D ⟦tU, U⟧.

Definition fpullback_data {X : C} (f : D ⟦J X, U⟧) : UU 
  := Σ Xf : C, C⟦Xf, X⟧ × D⟦J Xf, tU⟧.

Definition fpb_obj  {X : C} {f : D⟦J X, U⟧} (T : fpullback_data f) : C := pr1 T.
Definition fp {X : C} {f : D⟦J X, U⟧} (T : fpullback_data f) : C⟦fpb_obj T, X⟧ := pr1 (pr2 T).
Definition fq {X : C} {f : D⟦J X, U⟧} (T : fpullback_data f) : D⟦ J (fpb_obj T), tU⟧ := pr2 (pr2 T).

Definition fpullback_prop {X : C} {f : D ⟦J X, U⟧} (T : fpullback_data f) : UU 
  := Σ (fe : #J(fp T) ;; f = fq T ;; pp), isPullback _ _ _ _ _ fe .

Lemma isaprop_fpullback_prop {X : C} {f : D ⟦J X, U⟧} (T : fpullback_data f)
  : isaprop (fpullback_prop T).
Proof.
  apply isofhleveltotal2.
  - apply hsD.
  - intros. apply isaprop_isPullback.
Qed.

Definition fpullback {X : C} (f : D ⟦J X, U⟧) := 
  Σ T : fpullback_data f, fpullback_prop T.

Definition fcomprehension := ∀ X (f : D⟦J X, U⟧), fpullback f.

Lemma isaprop_fpullback {X : C} (f : D ⟦J X, U⟧) (is_c : is_category C)(is_d : is_category D) 
    (HJ : fully_faithful J)
  : isaprop (fpullback f).
Proof.
  apply invproofirrelevance.
  intros x x'.
  apply subtypeEquality.
  - intro t. apply isaprop_fpullback_prop.
  - destruct x as [x H]. 
    destruct x' as [x' H']. cbn.    
    destruct x as [a m].
    destruct x' as [a' m']. cbn in *.
    destruct H as [H isP].
    destruct H' as [H' isP'].
    simple refine (total2_paths _ _ ).
    + unfold fpullback_prop in *.
      set (T1 := mk_Pullback _ _ _ _ _ _ _ isP).
      set (T2 := mk_Pullback _ _ _ _ _ _ _ isP').
      set (i := iso_from_Pullback_to_Pullback  _  T1 T2). cbn in i.
      set (i' := invmap (weq_ff_functor_on_iso HJ a a') i ).
      set (TT := isotoid _ is_c i').
      apply TT.
    + cbn.
      set (XT := transportf_dirprod _ (fun a' => C⟦a', X⟧) (fun a' => D⟦J a', tU⟧)).
      cbn in XT.
      set (XT' := XT (tpair _ a m : Σ a : C, C ⟦ a, X ⟧ × D ⟦ J a, tU ⟧ )
                     (tpair _ a' m' : Σ a : C, C ⟦ a, X ⟧ × D ⟦ J a, tU ⟧ )).
      cbn in XT'.
      cbn.
      match goal with | [ |- transportf _ ?e _ = _ ] => set (TT := e) end.
      rewrite XT'.
      Search (dirprodpair _ _ = _ ).
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
        assert (X1:= PullbackArrow_PullbackPr1 _ (mk_Pullback _ _ _ _ _ _ _ isP)).
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
        assert (X1:= PullbackArrow_PullbackPr2 _ (mk_Pullback _ _ _ _ _ _ _ isP)).
        cbn in X1.
        apply X1.
Qed.


Lemma isaprop_fcomprehension : isaprop fcomprehension.
Proof.
  (* needs more hypotheses on the functor etc *)
Abort.

End fix_a_morphism.

Definition relative_universe_structure : UU :=
  Σ (tU U : D) (p : D⟦tU, U⟧), fcomprehension tU U p.


End fix_some_stuff.

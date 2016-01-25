
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
Variable p : D ⟦tU, U⟧.

Definition fpullback_data {X : C} (f : D ⟦J X, U⟧) : UU 
  := Σ Xf : C, C⟦Xf, X⟧ × D⟦J Xf, tU⟧.

Definition fpb_obj  {X : C} {f : D⟦J X, U⟧} (T : fpullback_data f) : C := pr1 T.
Definition fp {X : C} {f : D⟦J X, U⟧} (T : fpullback_data f) : C⟦fpb_obj T, X⟧ := pr1 (pr2 T).
Definition fq {X : C} {f : D⟦J X, U⟧} (T : fpullback_data f) : D⟦ J (fpb_obj T), tU⟧ := pr2 (pr2 T).

Definition fpullback_prop {X : C} {f : D ⟦J X, U⟧} (T : fpullback_data f) : UU 
  := Σ (fe : #J(fp T) ;; f = fq T ;; p), isPullback _ _ _ _ _ fe .

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

Lemma isaprop_fpullback {X : C} (f : D ⟦J X, U⟧) 
  : isaprop (fpullback f).
Proof.
  apply invproofirrelevance.
  intros x x'.
  apply subtypeEquality.
  - intro t. apply isaprop_fpullback_prop.
  - destruct x as [x t]. 
    destruct x' as [x' t']. cbn.
    
  (* needs more hypotheses on the functor etc *)
Abort.

Lemma isaprop_fcomprehension : isaprop fcomprehension.
Proof.
  (* needs more hypotheses on the functor etc *)
Abort.

End fix_a_morphism.

Definition relative_universe_structure : UU :=
  Σ (tU U : D) (p : D⟦tU, U⟧), fcomprehension tU U p.


End fix_some_stuff.

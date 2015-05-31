
(** * Category of elements *)
(**
  Contents:

    - not much yet
*)

Require Export Systems.Auxiliary.
Require Export Systems.UnicodeNotations.
Require Export UniMath.Foundations.hlevel2.hSet.

Require Export UniMath.RezkCompletion.functors_transformations.
Require Export UniMath.RezkCompletion.category_hset.
Require Export UniMath.RezkCompletion.opp_precat.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).

Section category_of_elements.

Variable C : precategory.
Variable F : functor C (opp_precat HSET).

Definition precategory_of_elements_ob_mor : precategory_ob_mor.
Proof.
  exists (Σ c : C, pr1 (F c)).
  intros ca c'a'.
  exact (Σ f : pr1 ca ⇒ pr1 c'a', #F (f) (pr2 c'a') = (pr2 ca)).
Defined.

Definition precategory_of_elements_data : precategory_data.
Proof.
  exists precategory_of_elements_ob_mor.
  split.
  - intro c. 
    exists (identity (pr1 c)).
    eapply pathscomp0. 
    + rewrite (functor_id F). apply idpath.
    + apply idpath.
  - intros a b c f g.
    exists (pr1 f ;; pr1 g).
    rewrite functor_comp. unfold compose; simpl in *.
    unfold compose. simpl.
    rewrite (pr2 g). rewrite (pr2 f).
    apply idpath.
Defined.
  
Lemma is_precategory_precategory_of_elements : is_precategory precategory_of_elements_data.
Proof.
  repeat split; intros;
  simpl in *.
  - apply total2_paths_second_isaprop.
    + apply setproperty.
    + apply id_left.
  - apply total2_paths_second_isaprop.
    + apply setproperty.
    + apply id_right.
  - apply total2_paths_second_isaprop.
    + apply setproperty.
    + apply assoc.
Qed.

Definition precategory_of_elements : precategory 
  := tpair _ _ is_precategory_precategory_of_elements.

(** first projection gives a (forgetful) functor **)

Definition proj_functor_data : functor_data precategory_of_elements C.
Proof.
  exists (@pr1 _ _ ).
  exact (λ a b, @pr1 _ _ ).
Defined.

Lemma is_functor_proj : is_functor proj_functor_data.
Proof.
  split; unfold functor_idax, functor_compax; intros;
  simpl in *; apply idpath.
Qed.

Definition proj_functor : functor _ _ := tpair _ _ is_functor_proj.


End category_of_elements.

(** * Category of elements *)
(**
  Contents:

    - category of elements of a covariant functor, including its univalence
*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.opp_precat.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheory.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

(* TODO: refactor as displayed category? *)
Section precategory_of_elements_covariant.

Context {C : precategory} (F : functor C HSET).

Definition precategory_of_elements_ob_mor : precategory_ob_mor.
Proof.
  exists (∑ c : C, pr1hSet (F c)).
  intros ca db.
  exact (∑ f : pr1 ca --> pr1 db, #F f (pr2 ca) = (pr2 db)).
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
    etrans. apply maponpaths. apply (pr2 f).
    apply (pr2 g).
Defined.
  
Lemma is_precategory_precategory_of_elements : is_precategory precategory_of_elements_data.
Proof.
  use make_is_precategory_one_assoc; intros.
  - apply subtypePath.
    + intro. apply setproperty.
    + apply id_left.
  - apply subtypePath.
    + intro; apply setproperty.
    + apply id_right.
  - apply subtypePath.
    + intro; apply setproperty.
    + apply assoc.
Qed.

Definition precategory_of_elements : precategory 
  := (_,,is_precategory_precategory_of_elements).

Lemma precategory_of_elements_has_homsets
  : has_homsets C -> has_homsets precategory_of_elements.
Proof.
  intros H ca db. apply isaset_total2.
  - apply H.
  - intros; apply isasetaprop, setproperty.
Defined.

Local Notation "∫" := precategory_of_elements.
(* written \int in agda input mode *)

(** first projection gives a (forgetful) functor **)

Definition proj_functor_data : functor_data ∫ C.
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

End precategory_of_elements_covariant.

Section category_of_elements.

Context {C : category} (F : functor C HSET).

Definition category_of_elements
  := make_category _
       (precategory_of_elements_has_homsets F (homset_property C)).

Local Notation "∫" := category_of_elements.
(* written \int in agda input mode *)

Definition Elem_cov_iso_type (ac bd : ∫) : UU
  := ∑ (f : z_iso (pr1 ac) (pr1 bd)), #F f (pr2 ac) = pr2 bd.

Definition Elem_cov_iso_type_eq {ac bd : ∫} (T T' : Elem_cov_iso_type ac bd)
  : T = T' ≃ (pr1 (pr1 T)) = (pr1 (pr1 T')).
Proof.
  eapply weqcomp.
    apply subtypeInjectivity. (*total2_paths_isaprop_equiv.*)
    intro. apply setproperty.
  apply subtypeInjectivity.
  intro. apply isaprop_is_z_isomorphism.
Defined.


Definition Elem_cov_iso_gives_z_iso (ac bd : ∫) :
  z_iso ac bd → z_iso (pr1 ac) (pr1 bd).
Proof.
  intros [[f b] [[g c] [h1 h2]]].
  exists f.
  exists g.
  split.
  - apply (maponpaths pr1 h1).
  - apply (maponpaths pr1 h2).
Defined.

Definition Elem_cov_iso_to_Elem_cov_iso_type (ac bd : ∫) :
  z_iso ac bd → Elem_cov_iso_type ac bd.
Proof.
  intro H.
  exists (Elem_cov_iso_gives_z_iso _ _ H).
  simpl.
  exact (pr2 (pr1 H)).
Defined.

Lemma iso_in_HSET (A B : HSET) (f : z_iso A B) (Y : pr1 B) (X : pr1 A) :
  pr1 f X = Y → inv_from_z_iso f Y = X.
Proof.
  intro H.
  etrans. { apply maponpaths, pathsinv0, H. }
  apply (toforallpaths (z_iso_inv_after_z_iso f)).
Qed.

Lemma Elem_cov_iso_inv (ac bd : ∫) (H : Elem_cov_iso_type ac bd) :
  # F (inv_from_z_iso (pr1 H)) (pr2 bd) = pr2 ac.
Proof.
  destruct ac as [a c].
  destruct bd as [b d].
  destruct H as [t p]; simpl in t, p |- *.
  etrans. { apply (toforallpaths (functor_on_inv_from_z_iso F t)). }
  apply iso_in_HSET, p.
Qed.

Definition Elem_cov_iso_type_to_Elem_cov_iso (ac bd : ∫) :
  Elem_cov_iso_type ac bd → z_iso ac bd .
Proof.
  intro H.
  use tpair; use tpair.
  - exact (pr1 H).
  - exact (pr2 H).
  - exists (inv_from_z_iso (pr1 H)).
    apply Elem_cov_iso_inv.
  - split; apply subtypePath; simpl.
    + intro; apply setproperty.
    + apply z_iso_inv_after_z_iso.
    + intro; apply setproperty.
    + apply z_iso_after_z_iso_inv.
Defined.

(* opacify the proof components *)
Definition Elem_cov_iso_type_equiv_Elem_cov_iso (ac bd : ∫) :
  z_iso ac bd ≃ Elem_cov_iso_type ac bd.
Proof.
  exists (Elem_cov_iso_to_Elem_cov_iso_type _ _ ).
  apply (gradth _ (Elem_cov_iso_type_to_Elem_cov_iso _ _ )).
  - intro.
    apply z_iso_eq. simpl.
    apply subtypePath.
    + intro; apply setproperty.
    + apply idpath.
  - intro.
    apply (invmap (Elem_cov_iso_type_eq _ _  )).
    apply idpath.
Defined.

Lemma elem_eq_weq_1 (H : is_univalent C) (ac bd : ∫) :
  ac = bd ≃ ∑ p : z_iso (pr1 ac) (pr1 bd), #F p (pr2 ac) = pr2 bd. 
Proof.
  eapply weqcomp.
  apply total2_paths_equiv.
  unshelve refine (weqbandf (make_weq (@idtoiso _ _ _) _ ) _ _ _ ).
  - apply H.
  - simpl. intro x.
    destruct ac. destruct bd.
    simpl in *.
    induction x. simpl.
    rewrite (functor_id F).
    apply idweq.
Defined.

Definition elem_eq_weq_2 (H : is_univalent C) (ac bd : ∫) :
  ac = bd ≃ z_iso ac bd.
Proof.
  eapply weqcomp.
  apply elem_eq_weq_1.
  apply H.
  apply invweq.
  apply Elem_cov_iso_type_equiv_Elem_cov_iso.
Defined.

(*  needs better computational behaviour in previous lemmas *)

Definition is_univalent_Elem  (H : is_univalent C) : is_univalent ∫.
Proof.
  intros a b.
  use weqhomot. { apply elem_eq_weq_2, H. }
  intro p; destruct p.
  apply z_iso_eq.
  apply subtypePath. { intro; apply setproperty. }
  cbn. apply idpath.
Defined.

End category_of_elements.

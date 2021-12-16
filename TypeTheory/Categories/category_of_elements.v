
(** * Category of elements *)
(**
  Contents:

    - category of elements of a covariant functor, including its univalence
*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.opp_precat.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

(* TODO: try upstreaming *)
Arguments toforallpaths [_ _ _ _] _ _.

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
  := ∑ (f : iso (pr1 ac) (pr1 bd)), #F f (pr2 ac) = pr2 bd.

Definition Elem_cov_iso_type_eq {ac bd : ∫} (T T' : Elem_cov_iso_type ac bd)
  : T = T' ≃ (pr1 (pr1 T)) = (pr1 (pr1 T')).
Proof.
  eapply weqcomp.
    apply subtypeInjectivity. (*total2_paths_isaprop_equiv.*)
    intro. apply setproperty.
  apply subtypeInjectivity.
  intro. apply isaprop_is_iso.
Defined.


Definition Elem_cov_iso_gives_iso (ac bd : ∫) :
  iso ac bd → iso (pr1 ac) (pr1 bd).
Proof.
  intro H.
  set (H':=is_z_iso_from_is_iso H (pr2 H)).
  exists (pr1 (pr1 H)).
  apply is_iso_from_is_z_iso.
  exists (pr1 (pr1 H')).
  split.
  - set (T:= pr1 (pr2 H')).
    apply (maponpaths pr1 T).
  - apply (maponpaths pr1 (pr2 (pr2 H'))).
Defined.

Definition Elem_cov_iso_to_Elem_cov_iso_type (ac bd : ∫) :
  iso ac bd → Elem_cov_iso_type ac bd.
Proof.
  intro H.
  exists (Elem_cov_iso_gives_iso _ _ H).
  simpl.
  exact (pr2 (pr1 H)).
Defined.

Lemma iso_in_HSET (A B : HSET) (f : iso A B) (Y : pr1 B) (X : pr1 A) :
  pr1 f X = Y → inv_from_iso f Y = X.
Proof.
  intro H.
  etrans. { apply maponpaths, pathsinv0, H. }
  apply (toforallpaths (iso_inv_after_iso f)).
Qed.

Lemma Elem_cov_iso_inv (ac bd : ∫) (H : Elem_cov_iso_type ac bd) :
  # F (inv_from_iso (pr1 H)) (pr2 bd) = pr2 ac.
Proof.
  destruct ac as [a c].
  destruct bd as [b d].
  destruct H as [t p]; simpl in t, p |- *.
  etrans. { apply (toforallpaths (functor_on_inv_from_iso F t)). }
  apply iso_in_HSET, p.
Qed.

Definition Elem_cov_iso_type_to_Elem_cov_iso (ac bd : ∫) :
  Elem_cov_iso_type ac bd → iso ac bd .
Proof.
  intro H.
  use tpair; [ | apply is_iso_from_is_z_iso]; use tpair.
  - exact (pr1 H).
  - exact (pr2 H).
  - exists (inv_from_iso (pr1 H)).
    apply Elem_cov_iso_inv.
  - split; apply subtypePath; simpl.
    + intro; apply setproperty.
    + apply iso_inv_after_iso.
    + intro; apply setproperty.
    + apply iso_after_iso_inv.
Defined.

(* opacify the proof components *)
Definition Elem_cov_iso_type_equiv_Elem_cov_iso (ac bd : ∫) :
  iso ac bd ≃ Elem_cov_iso_type ac bd.
Proof.
  exists (Elem_cov_iso_to_Elem_cov_iso_type _ _ ).
  apply (gradth _ (Elem_cov_iso_type_to_Elem_cov_iso _ _ )).
  - intro.
    apply eq_iso. simpl.
    apply subtypePath.
    + intro; apply setproperty.
    + apply idpath.
  - intro.
    apply (invmap (Elem_cov_iso_type_eq _ _  )).
    apply idpath.
Defined.

Lemma elem_eq_weq_1 (H : is_univalent C) (ac bd : ∫) :
  ac = bd ≃ ∑ p : iso (pr1 ac) (pr1 bd), #F p (pr2 ac) = pr2 bd. 
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
  ac = bd ≃ iso ac bd.
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
  apply (weqhomot _ (elem_eq_weq_2 H a b)).
  intro p; destruct p.
  apply eq_iso.
  apply subtypePath. { intro; apply setproperty. }
  cbn. apply idpath.
Defined.

End category_of_elements.


(*
Section category_of_elements.

Variable C : precategory.
Variable F : functor C (opp_precat HSET).

Definition precategory_of_elements_ob_mor : precategory_ob_mor.
Proof.
  exists (∑ c : C, pr1 (F c)).
  intros ca c'a'.
  exact (∑ f : pr1 ca --> pr1 c'a', #F (f) (pr2 c'a') = (pr2 ca)).
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

(* need that ∫ F is saturated if C is *)


(* next steps *)

(**

∫ ------> RC (∫)---> ∫ (F_RC)     with F_RC : RC(C) --> Set
|           |       /
|           |      /
v           v     /
C ------> RC (C) 

*)

(* need functoriality of RC, or at least action on functors *)


End category_of_elements.
*)

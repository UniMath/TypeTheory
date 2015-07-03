
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



Section category_of_elements_covariant.

Variable C : precategory.
Variable F : functor C HSET.

Definition precategory_of_elements_ob_mor : precategory_ob_mor.
Proof.
  exists (Σ c : C, pr1hSet (F c)).
  intros ca db.
  exact (Σ f : pr1 ca ⇒ pr1 db, #F f (pr2 ca) = (pr2 db)).
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


Definition Elem_cov_iso_type (ac bd : ∫) : UU
  := Σ (f : iso (pr1 ac) (pr1 bd)), #F f (pr2 ac) = pr2 bd.

Definition Elem_cov_iso_type_eq {ac bd : ∫} (T T' : Elem_cov_iso_type ac bd)
  : T = T' ≃ (pr1 (pr1 T)) = (pr1 (pr1 T')).
Proof.
  eapply weqcomp.
  apply total2_paths_isaprop_equiv.
  intro. apply setproperty.
  apply total2_paths_isaprop_equiv.
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
  set (T:= maponpaths (inv_from_iso f) H).
  apply pathsinv0.
  etrans. Focus 2. apply T.
  apply pathsinv0.
  set (HT:= iso_inv_after_iso f).
  set (HT':= toforallpaths _ _ _ HT).
  apply HT'.
Qed.

Lemma foo (ac bd : ∫) (H : Elem_cov_iso_type ac bd) :
  # F (inv_from_iso (pr1 H)) (pr2 bd) = pr2 ac.
Proof.
  destruct H.
  destruct ac as [a c].
  destruct bd as [b d]; simpl in *.
  set (T:= (functor_on_inv_from_iso C HSET  F _ _ t)).
  set (T':= toforallpaths _ _ _ T  d).
  etrans. apply T'. clear T' T.
  apply iso_in_HSET.
  apply p.
Qed.
  

Definition Elem_cov_iso_type_to_Elem_cov_iso (ac bd : ∫) :
  Elem_cov_iso_type ac bd → iso ac bd .
Proof.
  intro H.
  refine (tpair _ _ _ ).
  refine (tpair _ _ _ ).
  - exact (pr1 H).
  - exact (pr2 H).
  - apply is_iso_from_is_z_iso.
    refine (tpair _ _ _ ).
    exists (inv_from_iso (pr1 H)).
    apply foo.
    split.
    + apply total2_paths_second_isaprop.
      apply setproperty.
      simpl. apply iso_inv_after_iso.
    + apply total2_paths_second_isaprop.
      apply setproperty.
      simpl. apply iso_after_iso_inv.
Defined.

(* opacify the proof components *)
Definition Elem_cov_iso_type_equiv_Elem_cov_iso (ac bd : ∫) :
  iso ac bd ≃ Elem_cov_iso_type ac bd.
Proof.
  exists (Elem_cov_iso_to_Elem_cov_iso_type _ _ ).
  apply (gradth _ (Elem_cov_iso_type_to_Elem_cov_iso _ _ )).
  - intro.
    apply eq_iso. simpl.
    apply total2_paths_second_isaprop.
    + apply setproperty.
    + apply idpath.
  - intro.
    apply (invmap (Elem_cov_iso_type_eq _ _  )).
    apply idpath.
Defined.

Lemma bla (H : is_category C) (ac bd : ∫) :
  ac = bd ≃ Σ p : iso (pr1 ac) (pr1 bd), #F p (pr2 ac) = pr2 bd. 
Proof.
  eapply weqcomp.
  apply total2_paths_equiv.
  refine (weqbandf (weqpair (@idtoiso _ _ _ ) _ ) _ _ _ ).
  - apply (pr1 H).
  - simpl. intro x.
    destruct ac. destruct bd.
    simpl in *.
    induction x. simpl.
    rewrite (functor_id F).
    apply idweq.
Defined.

Definition foobar (H : is_category C) (ac bd : ∫) :
  ac = bd ≃ iso ac bd.
Proof.
  eapply weqcomp.
  apply bla.
  apply H.
  apply invweq.
  apply  Elem_cov_iso_type_equiv_Elem_cov_iso.
Defined.

(*  needs better computational behaviour in previous lemmas *)

Definition is_category_Elem  (H : is_category C) : is_category ∫.
Proof.
  split.
  - intros a b.
    set (T := isweqhomot (foobar  H a b)(@idtoiso _ a b) ).
    apply T.
    intro p.
    induction p.
    destruct a; simpl in *.
    
    simpl.
    apply eq_iso.
    simpl.
    apply total2_paths_second_isaprop. apply setproperty.
    apply idpath.
    apply pr2.
  - intros a b.
    apply (isofhleveltotal2 2).
    apply (pr2 H).
    intro. apply isasetaprop.
    apply setproperty.
Defined.

End category_of_elements_covariant.


(*
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
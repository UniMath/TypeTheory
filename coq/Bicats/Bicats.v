
(**

A module for bicategories, extending the Rezk-Completion Categories library

    - Definition of a precategory with families
    - Proof that reindexing forms a pullback

*)

Require Export UniMath.Foundations.Generalities.uu0.
Require Import UniMath.RezkCompletion.precategories.
Require Import UniMath.RezkCompletion.functors_transformations.

Require Import Systems.UnicodeNotations.

Section Background.
(* Prereqs: prods of precats *)

(* TODO: try to find this somwehre in library? *)
Definition dirprod_paths {A B : Type} {p q : A × B}
  : pr1 p = pr1 q -> pr2 p = pr2 q -> p = q.
Proof.
  destruct p as [a b], q as [a' b']; simpl. 
  intros e1 e2; destruct e1, e2; simpl. constructor.
Defined.

Definition dirprod_assoc {C0 C1 C2 : Type}
  : (C0 × (C1 × C2)) -> ((C0 × C1) × C2).
Proof.
  intros c. split. split. exact (pr1 c). exact (pr1 (pr2 c)). exact (pr2 (pr2 c)).
Defined.

Definition unit_precategory : precategory.
Proof.
  refine (tpair _ _ _). refine (tpair _ _ _).
  (* ob, mor *) exists unit. intros; exact unit.
  (* identity, comp *) split; intros; constructor.
  (* id_left *) simpl; split; try split; intros; apply isconnectedunit.
Defined.

Definition ob_as_functor {C : precategory} (c : C) : functor unit_precategory C.
Proof.
  refine (tpair _ _ _). refine (tpair _ _ _).
  (* functor_on_objects *) intros; exact c.
  (* functor_on_morphisms *) intros; apply identity.
  split.
  (* functor_id *) intros; constructor.
  (* functor_comp *) intros x y z w v; simpl. apply pathsinv0, id_left.
Defined.

Definition prod_precategory (C D : precategory) : precategory.
Proof.
  refine (tpair _ _ _). refine (tpair _ _ _).
  (* ob *) exists (C × D).
  (* mor *) intros a b. refine (_ × _).
    exact ((pr1 a) ⇒ (pr1 b)). exact ((pr2 a) ⇒ (pr2 b)).
  simpl; split.
  (* identity *) split; apply identity.
  (* comp *) intros a b c f g. split; eapply compose. 
    exact (pr1 f). exact (pr1 g). exact (pr2 f). exact (pr2 g).
  simpl; split; try split; simpl; intros.
  (* id_left *) apply dirprod_paths; simpl; apply id_left.
  (* id_right *) apply dirprod_paths; simpl; apply id_right. 
  (* assoc *) apply dirprod_paths; simpl; apply assoc.
Defined.

Local Notation "C × D" := (prod_precategory C D) (at level 80, no associativity) : precategory_scope.
Open Scope precategory_scope.
Delimit Scope precategory_scope with precat.

Definition prod_precategory_assoc_data (C0 C1 C2 : precategory)
  : functor_data (C0 × (C1 × C2)) ((C0 × C1) × C2).
Proof.
  (* functor_on_objects *) exists dirprod_assoc.
  (* functor_on_morphisms *) intros a b; apply dirprod_assoc.
Defined.

(* TODO: why are the next two so slow?
  (And much worse if inlined in [prod_precategory_assoc]!) 
  Would splitting up the components of [prod_precategory] into separate definitions help?  *)
Definition prod_precategory_assoc_idax (C0 C1 C2 : precategory)
  : functor_idax (prod_precategory_assoc_data C0 C1 C2).
Proof.
  (* functor_id *) intros c. Time simpl. apply paths_refl.
Defined.

Definition prod_precategory_assoc_compax (C0 C1 C2 : precategory)
  : functor_compax (prod_precategory_assoc_data C0 C1 C2).
Proof.
  (* functor_comp *) intros c0 c1 c2 f g. Time simpl. apply paths_refl.
Defined.

Definition prod_precategory_assoc (C0 C1 C2 : precategory)
  : functor (C0 × (C1 × C2)) ((C0 × C1) × C2).
Proof.
  exists (prod_precategory_assoc_data _ _ _); split.
  (* functor_id *) apply prod_precategory_assoc_idax.
  (* functor_comp *) apply prod_precategory_assoc_compax.
Time Defined.

End Background. 

Notation "C × D" := (prod_precategory C D)
  (at level 80, no associativity) : precategory_scope.
Open Scope precategory_scope.


Record prebicategory : Type := {
  ob_bicat :> Type;
  hom1 : forall (X Y : ob_bicat), precategory;
  hom2 := fun X Y (f g : hom1 X Y) => (f ⇒ g);
  identity_bicat : forall X, hom1 X X;
  compose_bicat : forall X Y Z,
    functor (prod_precategory (hom1 X Y) (hom1 Y Z)) (hom1 X Z);
  assoc_bicat : unit;
  idL_bicat : unit;
  idR_bicat : unit;
  pentagon_bicat : unit;
  idtri_bicat : unit
     }.
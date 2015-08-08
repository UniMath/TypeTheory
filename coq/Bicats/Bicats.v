
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

(* Fantastically useful tactic, taken from Jason Gross and Aruand Spiwack at <https://coq.inria.fr/bugs/show_bug.cgi?id=3551>. 

  Typical usage: you want to construct an instance of a big record type, where later fields depend on earlier ones, but the constructions of the earlier fields are non-trivial enough that you want to do them interactively, not write them explicitly.

  Older versions of Coq required the earlier fields to be broken out as separate lemmas, to do this.

  Out-of-the-box in current Coq, you can get this with [ refine (Build_some_big_record _ _ _ _ _) ].  However, the resulting proof-term often becomes quite slow to typecheck.

  Instead, you can do [ transparent assert ( H : record_field_type ). ], then build the field instance, and then [ refine (Build_some_big_record _ _ H _ _). ]  This can be repeated with multiple successively dependent fields; typically, until all subgoals produced by [refine] are independent.  This gains a *lot* of speed for each early field factored out.

  It is often convenient to write the construction first using a single [ refine ], since this generates all the required field types as you go along, and then afterwards to speed up compilation by refactoring into the form with [transparent assert] for as many fields as desired. *)
Tactic Notation "transparent" "assert" "(" ident(H) ":" open_constr(type) ")" :=
  refine (let H := (_ : type) in _).


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
  transparent assert (prod_precategory_ob_mor : precategory_ob_mor).
  (* ob *) exists (C × D).
  (* mor *) intros a b. refine (_ × _).
      exact ((pr1 a) ⇒ (pr1 b)). exact ((pr2 a) ⇒ (pr2 b)).
  transparent assert (prod_precategory_data : precategory_data).
  exists prod_precategory_ob_mor; split.
  (* identity *) split; apply identity.
  (* comp *) intros a b c f g. split; eapply compose. 
    exact (pr1 f). exact (pr1 g). exact (pr2 f). exact (pr2 g).
  exists prod_precategory_data.
  split; try split; try split; intros.
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

(* TODO: next two lemmas are still rather slow (though much better now that [prod_precategory] is written using [transparent assert]).

  Try (a) factoring those transparent asserts into separate lemmas; (b) grouping these lemmas into transparent asserts; see if either affects timing.  *)
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
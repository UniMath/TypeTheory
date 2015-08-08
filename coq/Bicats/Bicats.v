
(**

A module for bicategories, extending the Rezk-Completion Categories library

    - Definition of a precategory with families
    - Proof that reindexing forms a pullback

*)

Require Export UniMath.Foundations.Generalities.uu0.
Require Import UniMath.RezkCompletion.precategories.
Require Import UniMath.RezkCompletion.functors_transformations.

Require Import Systems.UnicodeNotations.

(* TODO: move to UnicodeNotations; pick level *)
Notation "( x , y , .. , z )" := (dirprodpair .. (dirprodpair x y) .. z).

(* TODO: try to get the opposite associativity, since it would seem to fit our current composition conventions better; but for some reason, it doesn’t seem to parse correctly ??
Notation "( x ; .. ; y ; z )" := (dirprodpair x .. (dirprodpair y z) .. ). *)

Section Background.

(* Very useful tactic, taken from Jason Gross and Aruand Spiwack at <https://coq.inria.fr/bugs/show_bug.cgi?id=3551>. 

  Typical usage: you want to construct an instance of a big iterated sigma-type, where later components depend on earlier ones, but the constructions of the earlier components are non-trivial enough that you want to do them interactively, not write them explicitly.

  Older versions of Coq required the earlier components to be broken out as separate lemmas for this.  In current Coq, you can get this out-of-the-box with [ refine (tpair _ _ _)].  However, the resulting proof-term often becomes quite slow to work with.

  Instead, you can do [ transparent assert ( H : whatever_type ). ], then build the component, and then [ exists H. ]  This can be repeated with multiple successively dependent components.

  This gains a *lot* of speed for each early component factored out — better performance both in the current construction itself (since not so many subgoals are being simultaneously updated), and when it is used down the line (since it allows better sharing between repeated occurrences of terms).  On the latter aspect, though, even more speed can sometimes be gained by breaking the asserts out further into standalone lemmas.

  It is often convenient to write the construction first using [ refine ], since this generates all the required field types as you go along, and then afterwards to speed up compilation by breaking fields out using [transparent assert] or as standalone lemmas. *)
Tactic Notation "transparent" "assert" "(" ident(H) ":" open_constr(type) ")" :=
  refine (let H := (_ : type) in _).

(* TODO: try to find next few [dirprod] lemmas somwhere in library? *)

(* should by UU instead of Type? *)
Definition dirprod_paths {A B : Type} {p q : A × B}
  : pr1 p = pr1 q -> pr2 p = pr2 q -> p = q.
Proof.
  destruct p as [a b], q as [a' b']; simpl. (* apply pathsdirprod. would work here*) 
  intros e1 e2; destruct e1, e2; simpl. constructor.
Defined.

Definition dirprod_assoc {C0 C1 C2 : Type}
  : (C0 × (C1 × C2)) -> ((C0 × C1) × C2).
Proof.
  intros c. exact ((pr1 c , (pr1 (pr2 c))) , pr2 (pr2 c)). (* this is total2asstol *) 
Defined.

Definition dirprod_maps {A0 A1 B0 B1} (f0 : A0 -> B0) (f1 : A1 -> B1)
  : A0 × A1 -> B0 × B1.
Proof.
  intros aa. exact (f0 (pr1 aa), f1 (pr2 aa)). (* apply (dirprodf f0 f1). *)
Defined.

Definition dirprod_pair_maps {A B0 B1} (f0 : A -> B0) (f1 : A -> B1)
  : A -> B0 × B1.
Proof.
  intros a; exact (f0 a, f1 a). (* apply (prodtofuntoprod (dirprodpair f0 f1)). *)
Defined.

Definition unit_precategory : precategory.
Proof.
  refine (tpair _ _ _). refine (tpair _ _ _).
  (* ob, mor *) exists unit. intros; exact unit.
  (* identity, comp *) split; intros; constructor.
  (* id_left *) simpl; split; try split; intros; apply isconnectedunit.
Defined.

Definition unit_functor C : functor C unit_precategory.
Proof.
  refine (tpair _ _ _). refine (tpair _ _ _).
  (* functor_on_objects *) intros; exact tt.
  (* functor_on_morphisms *) intros; apply identity.
  split.
  (* functor_id *) intros x; apply paths_refl.
  (* functor_comp *) intros x y z w v; apply paths_refl.
Defined.

(* TODO: perhaps generalise to constant functors? *)
Definition ob_as_functor {C : precategory} (c : C) : functor unit_precategory C.
Proof.
  refine (tpair _ _ _). refine (tpair _ _ _).
  (* functor_on_objects *) intros; exact c.
  (* functor_on_morphisms *) intros; apply identity.
  split.
  (* functor_id *) intros; constructor.
  (* functor_comp *) intros x y z w v; simpl. apply pathsinv0, id_left.
Defined.

Definition prod_precategory_ob_mor (C D : precategory) : precategory_ob_mor.
  (* ob *) exists (C × D).
  (* mor *) intros a b. refine (_ × _).
    exact ((pr1 a) ⇒ (pr1 b)). exact ((pr2 a) ⇒ (pr2 b)).
Defined.

Definition prod_precategory_data (C D : precategory) : precategory_data.
  exists (prod_precategory_ob_mor C D); split.
  (* identity *) split; apply identity.
  (* comp *) intros a b c f g. 
    exact ((pr1 f ;; pr1 g) , (pr2 f ;; pr2 g)).
Defined.

Definition prod_precategory (C D : precategory) : precategory.
Proof.
  exists (prod_precategory_data C D).
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

Definition prod_precategory_assoc (C0 C1 C2 : precategory)
  : functor (C0 × (C1 × C2)) ((C0 × C1) × C2).
Proof.
  exists (prod_precategory_assoc_data _ _ _). split.
  (* functor_id *) intros c. simpl; apply paths_refl.
  (* functor_comp *) intros c0 c1 c2 f g. simpl; apply paths_refl.
Defined.

Definition prod_functor_data {C0 C1 D0 D1 : precategory}
  (F0 : functor C0 D0) (F1 : functor C1 D1)
: functor_data (C0 × C1) (D0 × D1).
Proof.
  (* functor_on_objects *) exists (dirprod_maps F0 F1).
  (* functor_on_morphisms *) intros a b.
    apply dirprod_maps; apply functor_on_morphisms.
Defined.

Definition prod_functor {C0 C1 D0 D1 : precategory}
  (F0 : functor C0 D0) (F1 : functor C1 D1)
: functor (C0 × C1) (D0 × D1).
Proof.
  exists (prod_functor_data F0 F1); split.
  (* functor_id *) intros c. apply dirprod_paths; apply functor_id.
  (* functor_comp *) intros c0 c1 c2 f g.
    apply dirprod_paths; apply functor_comp.
Defined.

Definition pair_functor_data {C D0 D1 : precategory}
  (F0 : functor C D0) (F1 : functor C D1)
: functor_data C (D0 × D1).
Proof.
  (* functor_on_objects *) exists (dirprod_pair_maps F0 F1).
  (* functor_on_morphisms *) intros a b.
    apply dirprod_pair_maps; apply functor_on_morphisms.
Defined.

Definition pair_functor {C D0 D1 : precategory}
  (F0 : functor C D0) (F1 : functor C D1)
: functor C (D0 × D1).
Proof.
  exists (pair_functor_data F0 F1); split.
  (* functor_id *) intros c. apply dirprod_paths; apply functor_id.
  (* functor_comp *) intros c0 c1 c2 f g.
    apply dirprod_paths; apply functor_comp.
Defined.

End Background. 

Notation "C × D" := (prod_precategory C D)
  (at level 80, no associativity) : precategory_scope.
Open Scope precategory_scope.


Time Record prebicategory : Type := {
  ob_bicat :> Type;
  hom1 : forall (X Y : ob_bicat), precategory;
  hom2 := fun X Y (f g : hom1 X Y) => (f ⇒ g);
  identity_bicat : forall X, hom1 X X;
  compose_bicat : forall X Y Z,
    functor (prod_precategory (hom1 X Y) (hom1 Y Z)) (hom1 X Z);
  assoc_bicat : forall X Y Z W, nat_trans
    (functor_composite _ _ _
      (prod_functor (functor_identity _) (compose_bicat Y Z W))
      (compose_bicat X Y W))
    (functor_composite _ _ _
      (prod_precategory_assoc _ _ _)
      (functor_composite _ _ _
        (prod_functor (compose_bicat X Y Z) (functor_identity _))
        (compose_bicat X Z W)));
  id_left_bicat : forall X Y, nat_trans
    (functor_composite _ _ _
      (pair_functor 
        (functor_composite _ _ _ (unit_functor _) (ob_as_functor (identity_bicat X)))
        (functor_identity _))
      (compose_bicat X X Y))
    (functor_identity _);
  id_right_bicat : forall X Y, nat_trans
    (functor_composite _ _ _
      (pair_functor 
        (functor_identity _)
        (functor_composite _ _ _ (unit_functor _) (ob_as_functor (identity_bicat Y))))
      (compose_bicat X Y Y))
    (functor_identity _);
  pentagon_bicat : forall X Y Z W V
  (A : hom1 X Y) (B : hom1 Y Z) (C : hom1 Z W) (D : hom1 W V),
    (@functor_on_morphisms _ _ (compose_bicat _ _ _) (_ , _) (_ , _)
      (identity A, assoc_bicat _ _ _ _ (B , (C , D)) )
    ;; assoc_bicat _ _ _ _ (A , (compose_bicat _ _ _ (B, C) , D))
    ;; @functor_on_morphisms _ _ (compose_bicat _ _ _) (_,_) (_,_)
      (assoc_bicat _ _ _ _ (A , (B , C)) , identity D))
  =
    assoc_bicat _ _ _ _ (A , (B , compose_bicat _ _ _ (C , D)))
    ;; assoc_bicat _ _ _ _ (compose_bicat _ _ _ (A, B), (C , D));
  triangle_bicat : forall X,
    id_left_bicat _ _ (identity_bicat X)
    = id_right_bicat _ _ (identity_bicat X)
     }
.

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

(** Very useful tactic, taken from Jason Gross and Aruand Spiwack at <https://coq.inria.fr/bugs/show_bug.cgi?id=3551>. 

  Typical usage: you want to construct an instance of a big iterated sigma-type, where later components depend on earlier ones, but the constructions of the earlier components are non-trivial enough that you want to do them interactively, not write them explicitly.

  Older versions of Coq required the earlier components to be broken out as separate lemmas for this.  In current Coq, you can get this out-of-the-box with [ refine (tpair _ _ _)].  However, the resulting proof-term often becomes quite slow to work with.

  Instead, you can do [ transparent assert ( H : whatever_type ). ], then build the component, and then [ exists H. ]  This can be repeated with multiple successively dependent components.

  This gains a *lot* of speed for each early component factored out — better performance both in the current construction itself (since not so many subgoals are being simultaneously updated), and when it is used down the line (since it allows better sharing between repeated occurrences of terms).  On the latter aspect, though, even more speed can sometimes be gained by breaking the asserts out further into standalone lemmas.

  It is often convenient to write the construction first using [ refine ], since this generates all the required field types as you go along, and then afterwards to speed up compilation by breaking fields out using [transparent assert] or as standalone lemmas. *)
Tactic Notation "transparent" "assert" "(" ident(H) ":" open_constr(type) ")" :=
  refine (let H := (_ : type) in _).

Section Background.

(* TODO: try to find next few [dirprod] lemmas somwhere in library? *)

Section Dirprod_utils.
(** * Utility functions on direct products of types. *)

(** The next few are either aliases or very mild generalisations of existing functions from the UniMath libraries.  They differ generally in using projections instead of destructing, making them apply and/or reduce in more situations.  The aliases are included just to standardise local naming conventions. *)

(** Compare [pathsdirprod]. *)
Definition dirprod_paths {A B : Type} {p q : A × B}
  : pr1 p = pr1 q -> pr2 p = pr2 q -> p = q.
Proof.
  destruct p as [a b], q as [a' b']; apply pathsdirprod.
Defined.

(** Compare [total2asstol]. *) 
Definition dirprod_assoc {C0 C1 C2 : Type}
  : (C0 × (C1 × C2)) -> ((C0 × C1) × C2).
Proof.
  intros c. exact ((pr1 c , (pr1 (pr2 c))) , pr2 (pr2 c)). 
Defined.

(** Identical to [dirprodf]. *)
Definition dirprod_maps {A0 A1 B0 B1} (f0 : A0 -> B0) (f1 : A1 -> B1)
  : A0 × A1 -> B0 × B1.
Proof.
  intros aa. exact (f0 (pr1 aa), f1 (pr2 aa)).
Defined.

(** Compare [prodtofuntoprod]. *)
Definition dirprod_pair_maps {A B0 B1} (f0 : A -> B0) (f1 : A -> B1)
  : A -> B0 × B1.
Proof.
  intros a; exact (f0 a, f1 a).
Defined.

End Dirprod_utils.

Section Precategory_products.
(** * Products of precategories *)

(** Construction of finite products of precategories, including functoriality, associativity, and similar infrastructure. *)

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

End Precategory_products.

End Background. 

(** Redeclare section notations to be available globally. *)
Notation "C × D" := (prod_precategory C D)
  (at level 80, no associativity) : precategory_scope.
Open Scope precategory_scope.


Section Bicategory_definition.
(** * Definition of a prebicategory *)

(** The definition of a prebicategory is split up into four stages, each comprising 2 or 3 components.  Most of these components are themselves precategories, functors, or natural transformations.  In rough overview, the groups/components are:

precategory_obmor
  ob_bicat : Type;
  hom1 : forall (X Y : ob_bicat), prebicategory;
prebicategory_idcomp
  identity1 : forall X, hom1 X X;
  compose1 : forall {X Y Z}, functor (hom1 X Y × hom1 Y Z) (hom1 X Z);
prebicategory_associd
  assoc_bicat : (associativity natural transformation for compose1)
  id_left_bicat : (left unit natural transformation)
  id_right_bicat : (right unit natural transformation)
prebicategory_axioms
  pentagon_bicat : (pentagon axiom for assoc_bicat)
  triangle_bicat : (id_left_bicat and id_right_bicat agree on identity1)

Within each group apart from [obmor], the components are independent. *)

(* TODO: change names to [ob_mor] etc. to fit with precat names. *)

Definition prebicategory_obmor : Type
  := Σ (ob : Type), (forall (X Y : ob), precategory).

Definition ob_bicat (BB : prebicategory_obmor) := pr1 BB.
Coercion ob_bicat : prebicategory_obmor >-> Sortclass.
Definition hom1 (BB : prebicategory_obmor) := pr2 BB.
Coercion hom1 : prebicategory_obmor >-> Funclass.
Global Arguments hom1 [_] _ _.

Definition prebicategory_idcomp (BB : prebicategory_obmor) : Type
:= (forall X, BB X X)
 × (forall X Y Z, functor (BB X Y × BB Y Z) (BB X Z)).

Definition prebicategory_data1 := Σ BB0, prebicategory_idcomp BB0.

Definition prebicat_obmor (BB : prebicategory_data1) := pr1 BB.
Coercion prebicat_obmor : prebicategory_data1 >-> prebicategory_obmor.
Definition identity1 (BB : prebicategory_data1) := pr1 (pr2 BB).
Global Arguments identity1 [BB] X.
Definition compose1 (BB : prebicategory_data1) := pr2 (pr2 BB).
Global Arguments compose1 [BB X Y Z].

Definition prebicategory_associd (BB : prebicategory_data1) : Type
:= 
  (forall X Y Z W : BB, nat_trans
    (functor_composite _ _ _
      (prod_functor (functor_identity _) (@compose1 _ Y Z W))
      (@compose1 _ X Y W))
    (functor_composite _ _ _
      (prod_precategory_assoc _ _ _)
      (functor_composite _ _ _
        (prod_functor (@compose1 _ X Y Z) (functor_identity _))
        (@compose1 _ X Z W))))
× 
  ((forall X Y : BB, nat_trans
    (functor_composite _ _ _
      (pair_functor 
        (functor_composite _ _ _
           (unit_functor _) (ob_as_functor (identity1 X)))
        (functor_identity _))
      (@compose1 _ X X Y))
    (functor_identity _))
×
  (forall X Y : BB, nat_trans
    (functor_composite _ _ _
      (pair_functor 
        (functor_identity _)
        (functor_composite _ _ _
           (unit_functor _) (ob_as_functor (identity1 Y))))
      (@compose1 _ X Y Y))
    (functor_identity _)))%type.

Definition prebicategory_data2 : Type := Σ BB1, prebicategory_associd BB1.

Definition prebicat_data1 (BB : prebicategory_data2) := pr1 BB.
Coercion prebicat_data1 : prebicategory_data2 >-> prebicategory_data1.
Definition assoc_bicat (BB : prebicategory_data2) := pr1 (pr2 BB).
Global Arguments assoc_bicat [BB X Y Z W].
Definition id_left_bicat (BB : prebicategory_data2) := pr1 (pr2 (pr2 BB)).
Global Arguments id_left_bicat [BB X Y].
Definition id_right_bicat (BB : prebicategory_data2) := pr2 (pr2 (pr2 BB)).
Global Arguments id_right_bicat [BB X Y].

(* The axioms could be specified either as equalities/iso-ness of natural transformations, or pointwise.  We choose pointwise, for two reasons: firstly, it is easier to write (not requiring so much machinery for composition of natural transformations); secondly, in the absence of function extensionality, the pointwise notion is the correct one.  *) 
Definition prebicategory_coherence_axioms (BB : prebicategory_data2) : Type
:=
  ((forall X Y Z W V (A : BB X Y) (B : BB Y Z) (C : BB Z W) (D : BB W V),
    (@functor_on_morphisms _ _ (compose1) (_,_) (_,_)
      (identity A, assoc_bicat (B , (C , D)) )
    ;; assoc_bicat (A , ( compose1 (B, C) , D))
    ;; @functor_on_morphisms _ _ (compose1) (_,_) (_,_)
      (assoc_bicat (A , (B , C)) , identity D))
  =
    assoc_bicat (A , (B , compose1 (C , D)))
    ;; assoc_bicat (compose1 (A, B), (C , D)))
×
  (forall X Y Z (A : BB X Y) (B : BB Y Z),
    (assoc_bicat (A , (identity1 Y, B)))
    ;; (@functor_on_morphisms _ _ (compose1) (_,_) (_,_)
      (id_right_bicat A , identity B))
  = 
    @functor_on_morphisms _ _ (compose1) (_,_) (_,_)
      (identity A, id_left_bicat B )))%type.

Definition prebicategory_iso_axioms (BB : prebicategory_data2) : Type
:=
  ((forall (X Y Z W : BB) FGH, is_iso (@assoc_bicat _ X Y Z W FGH))
×
  ((forall (X Y : BB) (F : BB X Y), is_iso (id_left_bicat F))
×
  (forall (X Y : BB) (F : BB X Y), is_iso (id_right_bicat F))))%type.

Definition prebicategory : Type :=
  Σ BB2, (prebicategory_iso_axioms BB2 × prebicategory_coherence_axioms BB2)%type.

Definition prebicat_data2 (BB : prebicategory) := pr1 BB.
Coercion prebicat_data2 : prebicategory >-> prebicategory_data2.
Definition assoc_bicat_is_iso (BB : prebicategory) := pr1 (pr1 (pr2 BB)).
Global Arguments assoc_bicat [BB X Y Z W].
Definition id_left_bicat_is_iso (BB : prebicategory) := pr1 (pr2 (pr1 (pr2 BB))).
Global Arguments id_left_bicat [BB X Y].
Definition id_right_bicat_is_iso (BB : prebicategory) := pr2 (pr2 (pr1 (pr2 BB))).
Global Arguments id_right_bicat [BB X Y].
Definition pentagon_bicat (BB : prebicategory) := pr1 (pr2 (pr2 BB)).
Global Arguments pentagon_bicat [BB X Y Z W V] A B C D.
Definition triangle_bicat (BB : prebicategory) := pr2 (pr2 (pr2 BB)).
Global Arguments triangle_bicat [BB X Y Z] A B.

End Bicategory_definition.

Section Precat_as_prebicat.
(** * The prebicategory of precategories *)

(* Forming the functor precategory from C to D requires that the hom-types of D are sets.  Without this, [id_left], [id_right] and [assoc] for this precat would require extra axioms on the natural transformations, corresponding to the id and comp constraints classically taken for the 2-cells of a pseudo-natural transformation. 

To form a prebicategory, therefore, we have to restrict to precategories with hom-sets.*)
Definition good_precategory := Σ (C : precategory), has_homsets C.
Definition precat_of_good_precat (C : good_precategory) := pr1 C.
Coercion precat_of_good_precat : good_precategory >-> precategory.
Definition good_precat_hom_sets (C : good_precategory) := pr2 C.

Definition PRECAT_ob_mor : prebicategory_obmor.
Proof.
  (* ob_bicat *) exists good_precategory.
  (* hom1 *) intros C D. exact (functor_precategory C D (good_precat_hom_sets D)).
Defined.

(* Note: the interaction of reduction and coercions causes a sllightly irritating issue here.  (The same issue arises with other (bi-)categories of structured objects whose access functions rely on cascading coercions.)

  Given [ X : ob_bicat (PRECAT_ob_mor) ], we can’t write [ functor_identity X ]: the coercions [good_precategory >-> … >-> precategory_data ] don’t trigger, since [ob_bicat (PRECAT_ob_mor)] is not of the *syntactic* form to which they apply.

  Three workarounds: annotate it as [  (X : good_precategory) ], making the coercions trigger; issue [ simpl in X ] to reduce its type in the context to [ good_precategory ]; or write [ pr1 X ], which again pulls [ X ] into a type on which the coercions trigger. *)

Section Comp_Functor.
  Context (C D E : precategory) (HD : has_homsets D) (HE : has_homsets E).

  Definition nat_trans_horiz_comp {F F' : functor C D} {G G' : functor D E}
    (α : nat_trans F F') (β : nat_trans G G')
    : nat_trans (functor_composite _ _ _ F G) (functor_composite _ _ _ F' G').
  Proof.
    exists (fun x => functor_on_morphisms G (α x) ;; β (F' x)).
    intros x y f; simpl.
    eapply pathscomp0. apply assoc.
    eapply pathscomp0. apply cancel_postcomposition.
      eapply pathscomp0. eapply pathsinv0, functor_comp.
      apply maponpaths. apply nat_trans_ax.
    eapply pathscomp0. apply cancel_postcomposition, functor_comp.
    eapply pathscomp0. eapply pathsinv0, assoc.
    eapply pathscomp0. Focus 2. eapply assoc.
    apply maponpaths, nat_trans_ax.
  Defined.

  Definition comp_functor_data : functor_data
    (functor_precategory C D HD × functor_precategory D E HE)
    (functor_precategory C E HE).
  Proof.
    (* ob *) exists (fun FG => functor_composite _ _ _ (pr1 FG) (pr2 FG)).
    (* mor *) intros FG FG' αβ. exact (nat_trans_horiz_comp (pr1 αβ) (pr2 αβ)).
  Defined.

  Definition comp_functor_is_functor : is_functor comp_functor_data.
  Proof.
    split.
    (* functor_idax *) intros FG. apply nat_trans_eq. apply HE.
      intros x; simpl.
      eapply pathscomp0. apply id_right. apply functor_id.
    (* functor_compax *) intros FG1 FG' FG'' αβ αβ'. 
      apply nat_trans_eq. apply HE. intros x; simpl.
      eapply pathscomp0. apply cancel_postcomposition, functor_comp.
      eapply pathscomp0. eapply pathsinv0, assoc.
      eapply pathscomp0. Focus 2. apply assoc. apply maponpaths.
      eapply pathscomp0. apply assoc.
      eapply pathscomp0. apply cancel_postcomposition, nat_trans_ax.
      apply pathsinv0, assoc.
  Defined.

  Definition comp_functor 
    : functor (functor_precategory C D HD × functor_precategory D E HE)
              (functor_precategory C E HE).
  Proof.
    exists comp_functor_data. apply comp_functor_is_functor.
  Defined.

End Comp_Functor.

Definition PRECAT_data1 : prebicategory_data1.
Proof.
  exists PRECAT_ob_mor. split; intros.
  (* identity1 *) simpl. exact (functor_identity (X : good_precategory)).
  (* compose1 *) apply comp_functor.
Defined.

Definition PRECAT_data2 : prebicategory_data2.
Proof.
  exists PRECAT_data1. split; try split.
  (* assoc_bicat *) shelve.
  (* id_left_bicat *) shelve.
  (* id_right_bicat *) shelve.
Admitted.

Definition PRECAT : prebicategory.
Proof.
  exists PRECAT_data2. split; split.
  (* assoc_bicat_is_iso *) shelve.
  split.
  (* id_left_bicat_is_iso *) shelve.
  (* id_right_bicat_is_iso *) shelve.
  (* pentagon_bicat *) shelve.
  (* triangle_bicat *) shelve.
Admitted.


End Precat_as_prebicat.


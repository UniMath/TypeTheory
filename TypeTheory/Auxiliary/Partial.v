(** A library for working with partial functions; in particular, providing monadic style programming with them. *)

Require Import UniMath.All.

Section Partial.
(** Definition of partial elements, and access functions. *)

  Definition partial (X : UU) : UU
  := { a : hProp & a -> X }.

  Definition make_partial {X} {a : hProp} (f : a -> X) : partial X
  := (a,,f).
 
  Definition is_defined {X} : partial X -> hProp := pr1.
  
  Definition evaluate {X} {x : partial X} : is_defined x -> X := pr2 x.

End Partial.

Section Ordering.
(** The ordering on partial elements of any type *)

  Definition leq_partial {X} (x x' : partial X) : UU
    := ∑ (f : is_defined x -> is_defined x'),
       forall x_def, evaluate (f x_def) = evaluate x_def.

  Definition use_leq_partial {X} {x x' : partial X} (l : leq_partial x x')
    := pr1 l : is_defined x -> is_defined x'.
  Coercion use_leq_partial : leq_partial >-> Funclass.

  Definition leq_partial_commutes {X} {x x' : partial X} (l : leq_partial x x')
    := pr2 l : forall x_def, _ = _.

  Definition mk_leq_partial' {X} (x x' : partial X)
    (H : forall (x_def : is_defined x),
       ∑ (x'_def : is_defined x'), evaluate x'_def = evaluate x_def)
    : leq_partial x x'.
  Proof.
    exists (fun x_def => pr1 (H x_def)).
    exact (fun x_def => pr2 (H x_def)).
  Defined.

  Definition leq_partial_refl {X} (x : partial X)
    : leq_partial x x.
  Proof.
    exists (fun i => i); intros; apply idpath.
  Defined.

  Definition leq_partial_of_path {X} (x x' : partial X)
    : x = x' -> leq_partial x x'.
  Proof.
    intros []; apply leq_partial_refl.
  Defined.

  Definition leq_partial_trans {X}
       {x0 x1 x2 : partial X} (l01 : leq_partial x0 x1) (l12 : leq_partial x1 x2)
    : leq_partial x0 x2.
  Proof.
    exists (fun x0_def => l12 (l01 x0_def)).
    intros x_def. eauto using pathscomp0, leq_partial_commutes.
  Defined.

End Ordering.

Section Monad.
(** The monadic structure of partiality, and related utility functions *)

  Definition return_partial {X} : X -> partial X
  := fun x => make_partial (fun _ : htrue => x).

  Definition multiply_partial {X} (x : partial (partial X)) : partial X
  := make_partial
    (fun ij : total2_hProp
                (fun x_def : is_defined x => is_defined (evaluate x_def))
     => evaluate (pr2 ij)).

  Definition multiply_leq_partial
      {X} {x x' : partial (partial X)} (l : leq_partial x x')
    : leq_partial (multiply_partial x) (multiply_partial x').
  Proof.
    apply mk_leq_partial'. intros [H H'].
    use tpair.
    - exists (l H).
      refine (transportb is_defined _ H'). 
      apply leq_partial_commutes.
    - cbn.
      generalize (leq_partial_commutes l H : evaluate (l H) = _) as e.
      generalize (evaluate (l H)) as lx.
      intros lx e; destruct e. apply idpath.
  Defined.

  Definition multiply_leq_partial_2
      {X} {x x' : partial (partial X)}
      (l0 : is_defined x -> is_defined x')
      (l1 : forall x_def, leq_partial (evaluate x_def) (evaluate (l0 x_def)))
    : leq_partial (multiply_partial x) (multiply_partial x').
  Proof.
    apply mk_leq_partial'. intros [x_def x_def'].
    use tpair.
    - exists (l0 x_def).
      apply l1, x_def'.
    - cbn; apply leq_partial_commutes.
  Defined.

  Definition fmap_partial {X Y} (f : X -> Y) : partial X -> partial Y
  := fun x => make_partial (fun i : is_defined x => f (evaluate i)).

  Definition fmap_leq_partial
      {X Y} (f : X -> Y) {x x'} (l : leq_partial x x')
    : leq_partial (fmap_partial f x) (fmap_partial f x').
  Proof.
    exists l.
    intros x_def; cbn. apply maponpaths, leq_partial_commutes.
  Defined.
         
  Definition bind_partial {X Y} (x : partial X) (f : X -> partial Y)
    : partial Y
  := multiply_partial (fmap_partial f x).

  Definition bind_leq_partial_1
      {X Y} {x x'} (l : leq_partial x x') (f : X -> partial Y)
    : leq_partial (bind_partial x f) (bind_partial x' f).
  Proof.
    eauto using multiply_leq_partial, fmap_leq_partial.
  Defined.

  Definition bind_leq_partial_2
      {X Y} x {f g : X -> partial Y} (l : forall x, leq_partial (f x) (g x))
    : leq_partial (bind_partial x f) (bind_partial x g).
  Proof.
    simple refine (multiply_leq_partial_2 _ _). { exact (fun i => i). }
    intros x_def; apply l.
  Defined.

  Definition bind_leq_partial
      {X Y} {x x'} (lx : leq_partial x x')
      {f g : X -> partial Y} (lf : forall x, leq_partial (f x) (g x))
    : leq_partial (bind_partial x f) (bind_partial x' g).
  Proof.
    eauto using leq_partial_trans, bind_leq_partial_1, bind_leq_partial_2.
  Defined.

  Definition assume_partial {X} (P : hProp) (x : P -> partial X) : partial X.
  Proof.
    exists (total2_hProp (fun (H_P : P) => is_defined (x H_P))).
    intros H. exact (evaluate (pr2 H)).
  Defined.

  Definition assume_leq_partial
      {X} {P : hProp}
      {x x' : P -> partial X} (l : forall i, leq_partial (x i) (x' i))
    : leq_partial (assume_partial _ x) (assume_partial _ x').
  Proof.
    apply mk_leq_partial'.
    intros [i xi_def].
    exists (i,, l i xi_def).
    cbn. apply leq_partial_commutes.
  Defined.

End Monad.

Ltac get_partial t x := apply (bind_partial t); intros x.
(** [get_partial t x]: like Haskell’s [x <- t]. *)
Ltac destruct_partial x := apply (bind_partial x); clear x; intros x.
(** [destruct_partial]: special case of [get_partial] for variables. *)
Ltac assume_partial p x := apply (assume_partial p); intros x.

Section Partial_Maps.

  Definition partial_map X Y := X -> partial Y.
  Notation "X ⇢ Y" := (partial_map X Y) (at level 99) : type_scope.

  Definition compose_partial {X Y Z} (f : X ⇢ Y) (g : Y ⇢ Z) : X ⇢ Z
    := fun x => bind_partial (f x) g.
  Notation "f ∘ g" := (compose_partial f g) : partial_map_scope.
  (** This notation uses diagrammatic order, following UniMath’s notation
  [ (_ ∘ _)%Cat ] for morphisms in categories, _not_ consistent with
  UniMath’s notation [ (_ ∘ _)%functions ] for functions. *)

End Partial_Maps.

Notation "X ⇢ Y" := (partial_map X Y) (at level 99) : type_scope.
Notation "f ∘ g" := (compose_partial f g) : partial_map_scope.
Bind Scope partial_map with partial_map.
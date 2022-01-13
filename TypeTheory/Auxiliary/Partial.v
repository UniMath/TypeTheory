(** A library for working with partial functions; in particular, providing monadic style programming with them. *)

(* TODO: try to work out better organisation + naming conventions for the many functoriality/monotonicity lemmas in this file. *)

Require Import UniMath.MoreFoundations.All.

Section Partial.
(** Definition of partial elements, access functions, and some utility lemmas. *)

  Definition partial (X : UU) : UU
    := ∑ a : hProp, a → X.

  Definition make_partial {X} {a : hProp} (f : a -> X) : partial X
  := (a,,f).

  Definition is_defined {X} : partial X -> hProp := pr1.

  Definition evaluate {X} {x : partial X} : is_defined x -> X := pr2 x.

(** To display arguments of a specific [evaluate], use
  [change @evaluate with @evaluate_in at 17]
  (or whatever number is needed to pick out the specific occurrence). *)
Definition evaluate_in {X} x x_def := @evaluate X x x_def.

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

  Definition make_leq_partial' {X} (x x' : partial X)
    (H : forall (x_def : is_defined x),
       ∑ (x'_def : is_defined x'), evaluate x'_def = evaluate x_def)
    : leq_partial x x'.
  Proof.
    exists (fun x_def => pr1 (H x_def)).
    exact (fun x_def => pr2 (H x_def)).
  Defined.

  (* TODO: consider naming. *)
  Lemma apply_leq_partial_pair {X} {x x' : partial X} (l : leq_partial x x')
      (x_def : is_defined x)
    : ∑ (x'_def : is_defined x'), evaluate x'_def = evaluate x_def.
  Proof.
    exists (l x_def). apply leq_partial_commutes.
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

Section Compatibility.
(** Compatibility is a second important relation on partial elements:

Two partial elements are _compatible_ if, provided they are both defined, their values agree.

This extends the order relation, and is reflexive and symmetric, but not in general transitive. *)

  Definition compat_partial {X} (x y : partial X)
  := forall (x_def : is_defined x) (y_def : is_defined y),
      evaluate x_def = evaluate y_def.

  Definition compat_partial_refl {X} (x : partial X)
    : compat_partial x x.
  Proof.
    intros ? ?. apply maponpaths, propproperty.
  Qed.

  Definition compat_partial_of_path {X} {x y : partial X} (e : x = y)
    : compat_partial x y.
  Proof.
    intros ? ?. destruct e; apply compat_partial_refl.
  Qed.

  Definition compat_of_leq_partial {X} {x y : partial X}
    : leq_partial x y -> compat_partial x y
  := fun l x_def y_def =>
    ( ! leq_partial_commutes l _ @ compat_partial_refl _ _ _).

  Definition compat_partial_sym {X} (x y : partial X)
    : compat_partial x y -> compat_partial y x
  := fun H y_def x_def => (! H x_def y_def).

End Compatibility.

Section Functor.
(** Functoriality of the [partial] construction *)

  Definition fmap_partial {X Y} (f : X -> Y) : partial X -> partial Y
  := fun x => make_partial (fun i : is_defined x => f (evaluate i)).

  Definition fmap_leq_partial
      {X Y} (f : X -> Y) {x x'} (l : leq_partial x x')
    : leq_partial (fmap_partial f x) (fmap_partial f x').
  Proof.
    exists l.
    intros x_def; cbn. apply maponpaths, leq_partial_commutes.
  Defined.

  Lemma fmap_compose_partial {X Y Z : UU} (f : X -> Y) (g : Y -> Z)
      : fmap_partial g ∘ fmap_partial f = fmap_partial (g ∘ f).
  Proof.
    apply idpath.
  Defined.

  Lemma fmap_compose_partial_applied {X Y Z : UU} (f : X -> Y) (g : Y -> Z)
      : fmap_partial g ∘ fmap_partial f ~ fmap_partial (g ∘ f).
  Proof.
    apply toforallpaths, fmap_compose_partial.
  Defined.

  Lemma fmap_idmap_partial (X : UU)
      : fmap_partial (idfun X) = idfun _.
  Proof.
    apply idpath.
  Defined.

  Lemma fmap_idmap_partial_applied {X : UU} x
      : fmap_partial (idfun X) x = x.
  Proof.
    exact (toforallpaths _ _ _ (fmap_idmap_partial X) x).
  Defined.

End Functor.

Section Monad.
(** The monadic structure of partiality, and related utility functions *)

  Definition return_partial {X} : X -> partial X
  := fun x => make_partial (fun _ : htrue => x).

  (* TODO: consider naming *)
  Lemma show_return_leq_partial {X:UU} {x:X}
      {y : partial X} (y_def : is_defined y) (e_x_y : evaluate y_def = x)
    : leq_partial (return_partial x) y.
  Proof.
    exists (fun _ => y_def).
    intros ?; apply e_x_y.
  Defined.

  Lemma fmap_return_partial {X Y} (f : X -> Y) (x : X)
    : fmap_partial f (return_partial x) = return_partial (f x).
  Proof.
    apply idpath.
  Defined.

  Definition multiply_partial {X} (x : partial (partial X)) : partial X
  := make_partial
    (fun ij : total2_hProp
                (fun x_def : is_defined x => is_defined (evaluate x_def))
     => evaluate (pr2 ij)).

  Definition multiply_leq_partial
      {X} {x x' : partial (partial X)} (l : leq_partial x x')
    : leq_partial (multiply_partial x) (multiply_partial x').
  Proof.
    apply make_leq_partial'. intros [H H'].
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
    apply make_leq_partial'. intros [x_def x_def'].
    use tpair.
    - exists (l0 x_def).
      apply l1, x_def'.
    - cbn; apply leq_partial_commutes.
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

  Lemma bind_partial_as_sup {X Y} {x : partial X} (f : X -> partial Y)
      (y : partial Y)
      (H : forall (x_def : is_defined x), leq_partial (f (evaluate x_def)) y)
    : leq_partial (bind_partial x f) y.
  Proof.
    exists (fun fx_def => H (pr1 fx_def) (pr2 fx_def)).
    intros x_def. apply (leq_partial_commutes (H _)).
  Defined.

  Lemma leq_bind_partial {X Y} {x : partial X} (f : X -> partial Y)
      (x_def : is_defined x)
    : leq_partial (f (evaluate x_def)) (bind_partial x f).
  Proof.
    exists (fun fx_def => (x_def,,fx_def)).
    intros; apply idpath.
  Defined.

  Definition compat_bind_partial {X Y}
      {x x' : partial X} (c_x : compat_partial x x')
      {y y' : X -> partial Y} (c_y : forall x, compat_partial (y x) (y' x))
    : compat_partial (bind_partial x y) (bind_partial x' y').
  Proof.
    intros [x_def y_def] [x'_def y'_def].
    cbn in *. destruct (c_x x_def x'_def).
    apply c_y.
  Defined.

  (** Slight generalisation of [compat_bind_partial]. *)
  Definition compat_bind_partial' {X Y}
      {x x' : partial X} (c_x : compat_partial x x')
      {y y' : X -> partial Y}
      (c_y : forall x_def : is_defined x,
          compat_partial (y (evaluate x_def)) (y' (evaluate x_def)))
    : compat_partial (bind_partial x y) (bind_partial x' y').
  Proof.
    intros [x_def y_def] [x'_def y'_def].
    cbn in *. destruct (c_x x_def x'_def).
    apply c_y.
  Defined.

  Lemma fmap_bind_partial
      {X Y Z} (x : partial X) (f : X -> partial Y) (g : Y -> Z)
    : fmap_partial g (bind_partial x f)
    = bind_partial x (fmap_partial g ∘ f).
  Proof.
    apply idpath.
  Defined.

  (** Note: under prop univalence, is equality; but we avoid relying on this. *)
  Lemma bind_return_partial {X Y : UU} (x : X) (f : X -> partial Y)
    : leq_partial (bind_partial (return_partial x) f) (f x)
    × leq_partial (f x) (bind_partial (return_partial x) f).
  Proof.
    split.
    - exists (fun x_def => pr2 x_def).
      intros; apply idpath.
    - exists (fun x_def => (tt,,x_def)).
      intros; apply idpath.
  Defined.

  (** Note: under prop univalence, is equality; but we avoid relying on this. *)
  Lemma bind_with_return_partial {X Y : UU} (x : partial X) (f : X -> Y)
    : leq_partial (bind_partial x (return_partial ∘ f)) (fmap_partial f x)
    × leq_partial (fmap_partial f x) (bind_partial x (return_partial ∘ f)).
  Proof.
    split.
    - exists (fun x_def => pr1 x_def).
      intros; apply idpath.
    - exists (fun x_def => (x_def,,tt)).
      intros; apply idpath.
  Defined.

  Lemma bind_fmap_partial_1
      {X Y Z} {x : partial X} (f : X -> Y) (g : Y -> partial Z)
    : bind_partial (fmap_partial f x) g = bind_partial x (g ∘ f).
  Proof.
    apply idpath.
  Defined.

  Definition assume_partial {X} (P : hProp) (x : P -> partial X) : partial X.
  Proof.
    exists (total2_hProp (fun (H_P : P) => is_defined (x H_P))).
    intros H. exact (evaluate (pr2 H)).
  Defined.

  Lemma assume_partial_leq {X} {p q : hProp} (f : p -> q)
    {x : p -> partial X} {y : q -> partial X}
    (l : forall i:p, leq_partial (x i) (y (f i)))
    : leq_partial (assume_partial p x) (assume_partial q y).
  Proof.
    apply make_leq_partial'. intros [i x_def].
    exists (f i,, l i x_def); cbn.
    apply leq_partial_commutes.
  Defined.

  Definition assume_leq_partial
      {X} {P : hProp}
      {x x' : P -> partial X} (l : forall i, leq_partial (x i) (x' i))
    : leq_partial (assume_partial _ x) (assume_partial _ x')
  := assume_partial_leq (fun i => i) l.

  Lemma show_assume_leq_partial {X} {p : hProp} {x : p -> partial X}
      {y : partial X} (l : forall Hp :p, leq_partial (x Hp) y)
    : leq_partial (assume_partial p x) y.
  Proof.
    use tpair.
    - intros [Hp x_def]. exact (l Hp x_def).
    - cbn. intros. apply leq_partial_commutes.
  Defined.

  Lemma fmap_assume_partial {X Y} (f : X -> Y) {p:hProp} {x : p -> partial X}
    : fmap_partial f (assume_partial p x)
      = assume_partial p (fmap_partial f ∘ x).
  Proof.
    apply idpath.
  Defined.

End Monad.

(* TODO: make these more consistent in naming with similar monadic tactic family [unsquash]? *)
Ltac get_partial t x := apply (bind_partial t); intros x.
(** [get_partial t x]: like Haskell’s [x <- t]. *)
Ltac destruct_partial x := apply (bind_partial x); clear x; intros x.
(** [destruct_partial]: special case of [get_partial] for variables. *)
Ltac assume_partial p x := apply (assume_partial p); intros x.

Section Various.

  Definition forall_partial {X : UU} {Y : X -> UU}
      (f : forall x:X, partial (Y x))
    : partial (forall x, Y x).
  Proof.
    exists (∀ x, is_defined (f x)).
    intros f_def i. exact (evaluate (f_def i)).
  Defined.

  Definition forall_leq_partial {X : UU} {Y : X -> UU}
      {f g : forall x:X, partial (Y x)} (l : forall x, leq_partial (f x) (g x))
    : leq_partial (forall_partial f) (forall_partial g).
  Proof.
    apply make_leq_partial'. intros fs_def.
    use tpair.
    - intros x; exact (l x (fs_def x)).
    - apply funextsec; intros x. apply leq_partial_commutes.
  Defined.

End Various.

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

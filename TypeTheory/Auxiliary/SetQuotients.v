
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Unset Universe Checking.

  (* Upstream issues to possibly raise about [setquot]:
  - should [pr1] of [eqrel] coerce to [hrel], not directly to [Funclass]?
  - should [setquotfun2'] replace [setquotfun2]? [setquotfun2'] seems strictly more general and like it should behave just as well    *)

  (** Variant of [setquotuniv] with the [isaset] hypothesis separated out,
  for easier interactive use with [use], analogous to [setquotunivprop']. *)
  Definition setquotuniv' {X : UU} {R : hrel X} {Y : UU}
      (isaset_Y : isaset Y) (f : X -> Y) (f_respects_R : iscomprelfun R f)
    : setquot R -> Y.
  Proof.
    use (setquotuniv _ (_,,_)); assumption.
  Defined.

  Definition setquotuniv_isaprop {X : UU} {R : hrel X} {Y : UU}
      (isaprop_Y : isaprop Y) (f : X -> Y) : setquot R -> Y.
  Proof.
    use setquotuniv'.
    - now apply isasetaprop.
    - exact f.
    - intros x y h.
      now apply isaprop_Y.
  Defined.

  (** [setquot_rect]: the general dependent universal property of [setquot].
  To give a function into a dependent family of sets over the quotient, it suffices to construct the function on the domain of the quotient, and show your construction respects equivalence.

  Unfortunately, this currently doesn’t compute; the intended “computation” is given as a lemma, [setquot_comp.] *)
  (* TODO: with a bit more thought, could one give a version that computes nicely, like [setquotuniv]? *)
  (* TODO: possible alternative name [setquotuniv_dep] *)
  Definition setquot_rect {X:UU} {R:eqrel X}
      (P : setquot R -> UU) (isaset_P : forall xx, isaset (P xx))
      (d : forall x:X, P (setquotpr R x))
      (d_respects_R : forall (x y:X) (r : R x y),
          transportf _ (iscompsetquotpr _ _ _ r) (d x) = d y)
    : forall xx, P xx.
  Proof.
    intros xx.
    transparent assert (f : (xx -> P xx)).
    { intros x. refine (transportf _ _ (d (pr1 x))). apply setquotl0. }
    apply (pr1image f).
    apply (squash_to_prop (eqax0 (pr2 xx))).
    2: { apply prtoimage. }
    apply invproofirrelevance. intros [y Hy] [y' Hy'].
    apply subtypePath. { intro; apply isapropishinh. } simpl.
    apply (squash_to_prop Hy). { apply isaset_P. }
    clear Hy; intros [x e_xy].
    apply (squash_to_prop Hy'). { apply isaset_P. }
    clear Hy'; intros [x' e_xy'].
    destruct e_xy, e_xy'. subst f; simpl.
    assert (R_xx' : R (pr1 x) (pr1 x')).
    { apply (eqax2 (pr2 xx)); [apply x | apply x']. }
    rewrite <- (d_respects_R _ _ R_xx').
    eapply pathscomp0. 2: { apply pathsinv0, transport_f_f. }
    apply maponpaths_2, isasetsetquot.
  Defined.

  Definition setquot_rect_comp {X:UU} {R:eqrel X}
      (P : setquot R -> UU) (isaset_P : forall xx, isaset (P xx))
      (d : forall x:X, P (setquotpr R x))
      (d_respects_R : forall (x y:X) (r : R x y),
          transportf _ (iscompsetquotpr _ _ _ r) (d x) = d y)
    : forall x, (setquot_rect P isaset_P d d_respects_R) (setquotpr R x) = d x.
  Proof.
    intros x. unfold setquot_rect; simpl.
    eapply pathscomp0. 2: { apply idpath_transportf. }
    apply maponpaths_2, isasetsetquot.
  Defined.

  Definition setquot_rect_isaprop {X:UU} {R:eqrel X}
      (P : setquot R -> UU) (isaprop_P : forall xx, isaprop (P xx))
      (d : forall x:X, P (setquotpr R x))
    : forall xx, P xx.
  Proof.
    use (setquot_rect P (λ x, isasetaprop (isaprop_P x)) d).
    intros x y r.
    apply isaprop_P.
  Defined.
  
  Opaque setquot_rect setquot_rect_comp setquot_rect_isaprop.

(** A specialised eliminator for quotients, with better computational
behaviour than [setquot_rect], but not quite an instance of the simpler
eliminators: the target type is a subquotient, whose predicate and equivalence
relation may depend on the input, but whose underlying type is independent.

So this gives, in certain circumstances, a dependent eliminator with some
computational behaviour. *)
  Definition setquot_to_dependent_subquotient {X:UU} {R:eqrel X}
      {P_pre:UU}
      (P_good : setquot R -> hsubtype P_pre)
      (P_eq : forall xx, eqrel (P_good xx))
      (d_pre : X -> P_pre)
      (d_good : forall x:X, P_good (setquotpr R x) (d_pre x))
      (d_eq : forall (x y:X) (r : R x y),
          P_eq (setquotpr R y)
               (d_pre x,, transportf (fun xx => P_good xx (d_pre x))
                                     (iscompsetquotpr _ _ _ r) (d_good x))
               (d_pre y,, d_good y))
    : forall xx, setquot (P_eq xx).
  Proof.
    intros xx.
    transparent assert (f : (xx -> setquot (P_eq xx))).
    { intros x. apply setquotpr.
      exists (d_pre (pr1 x)).
      refine (transportf (fun xx => P_good xx (d_pre _)) _ (d_good _)).
      apply setquotl0. }
    apply (pr1image f).
    apply (squash_to_prop (eqax0 (pr2 xx))).
    2: { apply prtoimage. }
    apply invproofirrelevance. intros [y Hy] [y' Hy'].
    apply subtypePath. { intro; apply isapropishinh. } simpl.
    apply (squash_to_prop Hy). { apply isasetsetquot. }
    clear Hy; intros [x e_xy].
    apply (squash_to_prop Hy'). { apply isasetsetquot. }
    clear Hy'; intros [x' e_xy'].
    destruct e_xy, e_xy'. subst f; simpl.
    apply iscompsetquotpr.
    set (e := setquotl0 R xx x'); clearbody e.
    destruct x' as [x' x1']; simpl in *. clear x1'.
    destruct e. simpl.
    assert (r : R (pr1 x) x'). { apply eqrelsymm, (pr2 x). }
    refine (eqreltrans _ _ _ _ _ _).
    2: apply (d_eq _ _ r).
    apply eqreleq, maponpaths, propproperty.
  Defined.

  Definition setquot_to_dependent_subquotient_comp {X:UU} {R:eqrel X}
      {P_pre:UU}
      (P_good : setquot R -> hsubtype P_pre)
      (P_eq : forall xx, eqrel (P_good xx))
      (d_pre : X -> P_pre)
      (d_good : forall x:X, P_good (setquotpr R x) (d_pre x))
      (d_eq : forall (x y:X) (r : R x y),
          P_eq (setquotpr R y)
               (d_pre x,, transportf (fun xx => P_good xx (d_pre x))
                                     (iscompsetquotpr _ _ _ r) (d_good x))
               (d_pre y,, d_good y))
    : forall x,
       (setquot_to_dependent_subquotient P_good P_eq
                                   d_pre d_good d_eq) (setquotpr R x)
       = setquotpr (P_eq (setquotpr _ x)) (d_pre x,, d_good x).
  Proof.
    intros x. unfold setquot_to_dependent_subquotient; simpl.
    apply maponpaths, maponpaths, propproperty.
  Defined.

  Definition representative {X:UU} {R:eqrel X} (x:setquot R) : UU
  := hfiber (setquotpr R) x.

  Definition take_representative_with_isaset
      {X:UU} {R:eqrel X} (xx:setquot R)
      {Y:UU} (H_Y : isaset Y)
      (f : representative xx -> Y) (H_f : forall xx xx', f xx = f xx')
    : Y.
  Proof.
    simple refine (setquot_rect (fun xx' => (xx' = xx -> Y)) _ _ _ xx (idpath _)).
    - intros xx'. repeat (apply impred_isaset; intros); assumption.
    - intros x e. exact (f (x,, e)).
    - intros x y r.
      eapply pathscomp0. { use transportf_fun. }
      apply funextfun; intros e. simpl.
      apply H_f.
  Defined.

  Lemma take_representative_comp
      {X:UU} {R:eqrel X} (xx : setquot R)
      {Y:UU} (H_Y : isaset Y) (f : representative xx -> Y)
      (H_f : forall x x', f x = f x') (x : representative xx) 
    : take_representative_with_isaset xx H_Y f H_f = f x.
  Proof.
    unfold take_representative_with_isaset.
    destruct x as [x e]; induction e.
    now rewrite setquot_rect_comp.
  Qed.

  Lemma take_representative_comp_canon
      {X:UU} {R:eqrel X} (x : X)
      {Y:UU} (H_Y : isaset Y) (f : representative (setquotpr R x) -> Y)
      (H_f : forall xx xx', f xx = f xx')
    : take_representative_with_isaset (setquotpr R x) H_Y f H_f = f (x,,idpath _).
  Proof.
    now rewrite (take_representative_comp _ _ _ _ (x,, idpath _)).
  Defined.
  
  Definition take_representative_with_hSet
      {X:UU} {R:eqrel X} (xx:setquot R)
      (Y:hSet)
      (f : representative xx -> Y) (H_f : forall xx xx', f xx = f xx')
    : Y.
  Proof.
    use take_representative_with_isaset; auto; apply setproperty.
  Defined.

  (* TODO: perhaps add [take_representative_with_isaprop], […with_hProp] also *)

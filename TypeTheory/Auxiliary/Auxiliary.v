(**
  [TypeTheory.Auxiliary.Auxiliary]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(** 

Auxiliary background lemmas for the Ahrens/Lumsdaine/Voevodsky “Systems” project.  
Possibly some should be upstreamed to “UniMath” eventually.

*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

(** * Notation scopes

We open a few scopes that are used throughout the development, and add/tweak a few of UniMath’s notations.
*)

Undelimit Scope transport.

Notation "( x , y , .. , z )" := (make_dirprod .. (make_dirprod x y) .. z)
 : core_scope.
(** Replaces builtin notation for [pair], since we use [dirprod, make_dirprod] instead of [prod, pair]. *)


(** Redeclare this notation, along with a new scope. *)
Notation "ff ;; gg" := (compose ff gg)
  (at level 50, left associativity, format "ff  ;;  gg")
  : mor_scope.
Delimit Scope mor_scope with mor.
Bind Scope mor_scope with precategory_morphisms.
Open Scope mor_scope.

Declare Scope precat.
Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op") : precat.
Delimit Scope precat with precat.

Open Scope cat.
Open Scope cat_deprecated.


(** * Some tactics *)

Tactic Notation "etrans" := eapply pathscomp0.
Tactic Notation "rew_trans_@" := repeat (etrans ; [ apply transport_f_f |]).
Tactic Notation "sym" := apply pathsinv0.
Tactic Notation "assoc" := apply @pathsinv0, path_assoc.

(** * General type-theoretic content *)

(** ** Path-algebra: general lemmas about transport, equivalences, etc. *)

Arguments toforallpaths [_ _ _ _] _ _.

Lemma weqhomot {A B : UU} (f : A -> B) (w : A ≃ B) (H : w ~ f) : isweq f.
Proof.
  apply isweqhomot with w. apply H. apply weqproperty.
Defined.

(* General conventions would point to naming this [transportb_idpath], but we use [idpath_transportb] for consistency with [idpath_transportf] upstream. *)
Lemma idpath_transportb
      {X : UU} (P : X → UU)
      (x : X) (p : P x)
  : transportb P (idpath x) p = p.
Proof.
  apply idpath.
Defined.

(* Note: a common and useful special case of [transport_map]. *)
Lemma pr1_transportf (A : UU) (B : A -> UU) (P : ∏ a, B a -> UU)
   {a a' : A} (e : a = a') (xs : ∑ b : B a, P _ b):
   pr1 (transportf (fun x => ∑ b : B x, P _ b) e xs) = 
     transportf (fun x => B x) e (pr1 xs).
Proof.
  apply pathsinv0, (transport_map (fun a => pr1)).
Defined.

(* Included for searchability, but can always be replaced by [pr1_transportf]. *)
Definition pr1_transportb
    (A : UU) (B : A → UU) (P : ∏ a : A, B a → UU) {a a' : A}
    (e : a = a') (xs : ∑ b : B a', P a' b)
  : pr1 (transportb (λ x : A, ∑ b : B x, P x b) e xs) =
      transportb (λ x : A, B x) e (pr1 xs).
Proof.
  apply pr1_transportf.
Defined.

(* Note: this is easier to use than UniMath’s [transportf_const]  *)
Lemma transportf_const' (A B : UU) (a a' : A) (e : a = a') (b : B)
  : transportf (fun _ => B) e b = b.
Proof.
  induction e.
  apply idpath.
Defined.

Lemma fiber_paths_from_total2_paths
    {A : UU} {B : A → UU}
    (x y : ∑ (a : A), B a)
    (p : x = y)
  : transportb B (maponpaths pr1 p) (pr2 y) = pr2 x.
Proof.
  induction p; apply idpath.
Defined.


(* TODO: systematise these variants of [transportf_forall]:
- probably make [transportf_forall] the most general form, where [B] depends on [A] and [C] depends on both
- and then give the partly-reduced variants some systematic names, if possible. *)
Lemma transportf_forall {A B} (C : A -> B -> UU)
  {x0 x1 : A} (e : x0 = x1) (f : forall y:B, C x0 y)
  : transportf (fun x => forall y, C x y) e f
  = fun y => transportf (fun x => C x y) e (f y).
Proof.
  destruct e; apply idpath.
Defined.

Definition transportf_forall_var :
  ∏ (A : UU) (B : A -> UU) (C : UU)
    (a1 a2 : A) (e : a1 = a2)
    (f : B a1 -> C),
  transportf (λ x : A, ∏ y : B x, C) e f =
  (λ y : B a2 , f (transportb B e y)).
Proof.
  intros A B D a1 a2 e f.
  induction e.
  apply idpath.
Defined.

Definition transportf_forall_var2 :
  ∏ (A : UU) (B C : A -> UU) 
    (a1 a2 : A) (e : a1 = a2)
    (f : B a1 -> C a1),
  transportf (λ x : A, ∏ y : B x, C x) e f =  
  (λ y : B a2 , transportf _ e (f (transportb B e y))).
Proof.
  intros A B D a1 a2 e f.
  induction e.
  apply idpath.
Defined.

Lemma maponpaths_apply {A B} {f0 f1 : A -> B} (e : f0 = f1) (x : A)
  : maponpaths (fun f => f x) e
  = toforallpaths e x.
Proof.
  destruct e; apply idpath.
Defined.

Lemma maponpaths_eq_idpath
  : ∏ (T1 T2 : UU) (f : T1 -> T2) (t1 : T1) (e : t1 = t1)
      (H : e = idpath _ ), maponpaths f e = idpath _ .
Proof.
  intros.
  exact (maponpaths (maponpaths f) H).
Defined.

Lemma transportf_comp_lemma (X : UU) (B : X -> UU)
    {A A' A'': X} (e : A = A'') (e' : A' = A'')
    (x : B A) (x' : B A')
  : transportf _ (e @ !e') x = x'
  -> transportf _ e x = transportf _ e' x'.
Proof.
  intro H.
  eapply pathscomp0.
  2: { apply maponpaths. exact H. }
  eapply pathscomp0.
  2: { symmetry. apply transport_f_f. }
  apply (maponpaths (fun p => transportf _ p x)).
  apply pathsinv0.
  eapply pathscomp0.
  - apply @pathsinv0, path_assoc. 
  - eapply pathscomp0. 
    apply maponpaths.
    apply pathsinv0l.
    apply pathscomp0rid.
Defined.

Lemma transportf_comp_lemma_hset (X : UU) (B : X -> UU) (A : X) (e : A = A)
  {x x' : B A} (hs : isaset X)
  : x = x'
  -> transportf _ e x = x'.
Proof.
  intros ex.
  apply @pathscomp0 with (transportf _ (idpath _) x).
  - apply (maponpaths (fun p => transportf _ p x)).
    apply hs.
  - exact ex.
Qed.

Lemma transportf_pair {A B} (P : A × B -> UU)
    {a a' : A} {b b' : B}
    (eA : a = a') (eB : b = b') (p : P (a,,b)) 
  : transportf P (pathsdirprod eA eB) p
    = transportf (fun bb => P(a',,bb)) eB
       (transportf (fun aa => P(aa,,b)) eA p).
Proof.
  induction eA. induction eB. apply idpath.
Defined.

(* variant of UniMath’s [transportf_dirprod], easier to apply: paired hypotheses are split up, and one redundant component removed *)
Lemma transportf_dirprod' {A : UU} (B C : A → UU)
      {a:A} (bc : B a × C a)
      {a':A} (p : a = a')
  : transportf (λ a : A, B a × C a) p bc
    = (transportf (λ a : A, B a) p (pr1 bc),
       transportf (λ a : A, C a) p (pr2 bc)).
Proof.
  destruct p; apply idpath.
Defined.

(** ** Lemmas on equivalences and general type-algebra *)

Lemma invmap_eq {A B : UU} (f : A ≃ B) (b : B) (a : A)
  : b = f a → invmap f b = a.
Proof.
  intro H.
  apply (invmaponpathsweq f).
  etrans. apply homotweqinvweq. apply H.
Defined.

Lemma homot_invweq_transportb_weq
      (Z : UU)
      (z z' : Z)
      (X Y : Z → UU)
      (e : z = z')
      (w : ∏ z : Z, X z ≃ Y z)
      (x : X z')
  : invmap (w z) (transportb Y e (w z' x)) = transportb X e x.
Proof.
  induction e.
  etrans. apply maponpaths, idpath_transportb.
  apply homotinvweqweq.
Defined.


Definition isweqpathscomp0l {X : UU} {x x' : X} (x'' : X) (e: x = x') :
   isweq (fun (e' : x' = x'') => e @ e').
Proof.
  intros.
  apply (gradth _ (fun e'' => !e @ e'')).
  - intro p. rewrite path_assoc. rewrite pathsinv0l.
    apply idpath.
  - intro p. rewrite path_assoc. rewrite pathsinv0r.
    apply idpath.
Defined.

Definition weqpathscomp0l {X : UU} {x x'} (x'' : X) (e : x = x')
  : (x' = x'') ≃ (x = x'').
Proof.
  exact (_ ,, isweqpathscomp0l x'' e).
Defined.

Definition weqpathscomp0r {X : UU} (x:X) {x' x''} (e' : x' = x'')
  : (x = x') ≃ (x = x'').
Proof.
  exact (_ ,, isweqpathscomp0r x e').
Defined.

Definition weq_exchange_args {A B} (C : A -> B -> Type)
  : (∏ a b, C a b) ≃ (∏ b a, C a b).
Proof.
  use weq_iso.
  - intros f b a; exact (f a b).
  - intros g a b; exact (g b a).
  - intros f; apply idpath.
  - intros g; apply idpath.
Defined.

Definition isweqbandfmap_var {X Y : UU} (w : X -> Y) 
           (P : X → UU) (Q : Y → UU)
           (fw : ∏ x : X, P x -> Q (w x))
: isweq w -> (∏ x, isweq (fw x)) -> isweq (bandfmap w P Q (λ x : X, fw x)).
Proof.
  intros Hw Hfw.
  apply (isweqbandfmap (make_weq w Hw) _ _ (fun x => make_weq _ (Hfw x))).
Defined.

(* [weqtotal2asstol'] infers its arguments much more often than UniMath’s [weqtotal2asstol], so is much simpler to use in proofs.
TODO: if this is upstreamed, see if proofs using [weqtotal2asstol] can be simplified by switching to this.  *)
Lemma weqtotal2asstol' {X : UU} (P : X → UU) (Q : forall x, P x → UU)
  : (∑ (x : X) (p : P x), Q x p) ≃ (∑ (y : ∑ x, P x), Q (pr1 y) (pr2 y)).
Proof.
  exact (weqtotal2asstol P (fun y => Q (pr1 y) (pr2 y))). 
Defined.

(* [weqtotal2asstor'] infers its arguments much more often than UniMath’s [weqtotal2asstor], so is much simpler to use in proofs.
TODO: if this is upstreamed, see if proofs using [weqtotal2asstol] can be simplified by switching to this.  *)
Lemma weqtotal2asstor' {X : UU} (P : X → UU) (Q : forall x, P x → UU)
  : (∑ (y : ∑ x, P x), Q (pr1 y) (pr2 y)) ≃ (∑ (x : X) (p : P x), Q x p).
Proof.
  exact (weqtotal2asstor P (fun y => Q (pr1 y) (pr2 y))). 
Defined.

Lemma weqforalltototal3 {X : UU}
      (P1 : X → UU)
      (P2 : ∏ x : X, P1 x → UU)
      (P3 : ∏ (x : X) (y : P1 x), P2 x y → UU)
  : (∏ x : X, ∑ (p1 : P1 x) (p2 : P2 x p1), P3 x p1 p2)
  ≃ (∑ (p1 : ∏ x : X, P1 x) (p2 : ∏ x : X, P2 x (p1 x)),
          ∏ x : X, P3 x (p1 x) (p2 x)).
Proof.
  eapply weqcomp. apply weqforalltototal.
  apply (weqtotal2 (idweq _)). intros ?.
  apply weqforalltototal.
Defined.

Lemma weqtotaltoforall3 {X : UU}
      (P1 : X → UU)
      (P2 : ∏ x : X, P1 x → UU)
      (P3 : ∏ (x : X) (y : P1 x), P2 x y → UU)
  : (∑ (p1 : ∏ x : X, P1 x) (p2 : ∏ x : X, P2 x (p1 x)),
      ∏ x : X, P3 x (p1 x) (p2 x))
  ≃ (∏ x : X, ∑ (p1 : P1 x) (p2 : P2 x p1), P3 x p1 p2).
Proof.
  apply invweq, weqforalltototal3.
Defined.

Lemma weqforalltototal4 {X : UU}
      (P1 : X → UU)
      (P2 : ∏ x : X, P1 x → UU)
      (P3 : ∏ (x : X) (y : P1 x), P2 x y → UU)
      (P4 : ∏ (x : X) (y : P1 x) (z : P2 x y), P3 x y z → UU)
  : (∏ x : X, ∑ (p1 : P1 x) (p2 : P2 x p1) (p3 : P3 x p1 p2), P4 x p1 p2 p3)
  ≃ (∑ (p1 : ∏ x : X, P1 x) (p2 : ∏ x : X, P2 x (p1 x))
       (p3 : ∏ x : X, P3 x (p1 x) (p2 x)), ∏ x : X, P4 x (p1 x) (p2 x) (p3 x)).
Proof.
  eapply weqcomp. apply weqforalltototal.
  apply (weqtotal2 (idweq _)). intros ?.
  eapply weqcomp. apply weqforalltototal.
  apply (weqtotal2 (idweq _)). intros ?.
  apply weqforalltototal.
Defined.

Lemma weqtotaltoforall4 {X : UU}
      (P1 : X → UU)
      (P2 : ∏ x : X, P1 x → UU)
      (P3 : ∏ (x : X) (y : P1 x), P2 x y → UU)
      (P4 : ∏ (x : X) (y : P1 x) (z : P2 x y), P3 x y z → UU)
  : (∑ (p1 : ∏ x : X, P1 x) (p2 : ∏ x : X, P2 x (p1 x))
       (p3 : ∏ x : X, P3 x (p1 x) (p2 x)), ∏ x : X, P4 x (p1 x) (p2 x) (p3 x))
  ≃ (∏ x : X, ∑ (p1 : P1 x) (p2 : P2 x p1) (p3 : P3 x p1 p2), P4 x p1 p2 p3).
Proof.
  apply invweq, weqforalltototal4.
Defined.

Lemma iscontr_total2
      {X : UU} {P : X → UU}
  : iscontr X → (∏ x : X, iscontr (P x)) → iscontr (∑ (x : X), P x).
Proof.
  intros X_contr P_contr.
  use tpair.
  - exists (pr1 X_contr). apply P_contr.
  - intros xp.
    use total2_paths_f.
    + apply X_contr.
    + apply P_contr.
Defined.

(* eventually upstream to UniMath.Foundations.Propositions, or somewhere in MoreFoundations? (compare [fromnegcoprod] etc) *)
Definition or_neg_to_neg_and {X Y : UU} : (¬ X ⨿ ¬ Y) → ¬ (X × Y).
Proof.
  intros [nx | ny] [x y]; auto.
Defined.

(* Note: weaker than [hexistsnegtonegforall], but slightly simpler, and often what’s more directly wanted in practice *)
Definition total2_neg_to_neg_forall {X : UU} {A : X -> UU}
  : (∑ x:X, ¬ A x) → ¬ (∏ x:X, A x).
Proof.
  intros [x nax] nforall; auto.
Defined.

(** Note: this is a trivial specialisation of [isofhlevelweqf], but useful since that often doesn’t unify when goal is [isaset]. *)
Definition isaset_weqf {X Y : UU} (e : X ≃ Y) : isaset X -> isaset Y.
Proof.
  eapply (isofhlevelweqf 2); eassumption.
Defined.

(** ** Surjectivity *)

Lemma issurjective_hinhpr (A : UU) : issurjective (@hinhpr A).
Proof.
  intro a. 
  apply (squash_to_prop a).
  - apply propproperty.
  - intro aa. apply hinhpr.
    exists aa.
    apply proofirrelevance.
    apply propproperty.
Defined.

Lemma issurjective_bandfmap {X Y : UU} (f : X → Y) (P : X → UU) (Q : Y → UU)
      (fx : ∏ x : X, P x → Q (f x)) 
      (Hf : issurjective f)
      (Hfx : ∏ x, issurjective (fx x))
  : issurjective (bandfmap f _ _ fx).
Proof.
  intros [y q].
  apply (squash_to_prop (Hf y)).
  { apply propproperty. }
  intros [x Hx].
  induction Hx.
  apply (squash_to_prop (Hfx _ q)).
  { apply propproperty. }
  intros [p Hp].
  destruct Hp.
  apply hinhpr.
  exists (x,,p).
  apply idpath.
Defined.

Lemma fibers_inhab_if_pr1_issurjective {X : UU} {P : X -> UU} :
  (∏ x : X, ∥ P x ∥) <- issurjective (pr1 : (∑ x, P x) -> X).
Proof.
  intros ne x. simple refine (hinhuniv _ (ne x)).
  intros p. apply hinhpr.
  cbn in p.
  destruct p as [[a b] c].
  cbn in *.
  induction c.
  assumption.
Defined.

Lemma isaprop_fiber_if_isinclpr1
  : ∏ (X : UU) (isasetX : isaset X) (P : X → UU),
      (∏ x : X, isaprop (P x)) <- isincl (pr1 : (∑ x, P x) -> X).
Proof.
  intros X isasetX P H x.
  unfold isincl in H. unfold isofhlevelf in H.
  apply invproofirrelevance.
  intros p p'.
  assert (X0 :  x,,p = x,,p').
  { specialize (H x).
    assert (H1 :  (x,,p),, idpath _ = ((x,,p'),,idpath _ : hfiber pr1 x)).
    { apply proofirrelevance. apply H. }
    apply (base_paths _ _ H1).
  }
  set (XR := fiber_paths X0). cbn in XR.
  etrans. 2: { apply XR. }
  apply pathsinv0.
  etrans. apply maponpaths_2. apply (isasetX _ _ _ (idpath x)).
  apply idpath_transportf.
Defined.


(** ** Other general lemmas *)

(* A slightly surprising but very useful lemma for characterising identity types.

Concisely: to show that a family of functions [w : forall a b, a = b -> P a b] are equivalences, it’s enough to show they have a retraction; the retraction is then automatically a quasi-inverse, because of the fact that the coconut is contractible.
 
Often one can save a bit of work with this (since the other direction of inverseness may not be so obvious in individual cases).

TODO: move; consider naming; see if this can be used to simplify other proofs of [is_univalent] and similar? *)
Lemma eq_equiv_from_retraction {A} {P : A -> A -> UU} 
    (w : forall a b, a = b -> P a b)
    (v : forall a b, P a b -> a = b)
  : (forall a b (p : P a b), w _ _ (v _ _ p) = p)
  -> forall a b, isweq (w a b).
Proof.
  intros wv a.
  apply isweqtotaltofib. (* first of the two key steps *)
  use gradth.
  - intros bp. exists (pr1 bp). apply v, (pr2 bp).
  - intros be; apply coconusfromt_isProofIrrelevant. (* the second key step *)
  - intros bp. use total2_paths_f. apply idpath. apply wv.
Qed.

Definition truncation_weq (A : UU) (is : isaprop A) : A ≃ ∥ A ∥.
Proof.
  apply weqimplimpl.
  - apply hinhpr.
  - intro a. use (squash_to_prop a is). apply idfun.
  - apply is.
  - apply propproperty. 
Defined.

(* generalises [weqtotal2overunit] from [Foundations.PartA]; perhaps rename to e.g. [weq_total2_over_iscontr] for consistency with that? *)
Definition iscontr_total2_irrelevant
    {A : UU} {P : A → UU} (iscontr_A : iscontr A)
  : (∑ (a : A), P a) ≃ P (pr1 iscontr_A).
Proof.
  eapply weqcomp.
  use (weqtotal2 (Q := λ _, P (pr1 iscontr_A)) (idweq _) _).
  - intros a. apply eqweqmap, maponpaths, (pr2 iscontr_A).
  - apply invweq, WeakEquivalences.dirprod_with_contr_l, iscontr_A.
Defined.

(** TODO: seek further in UniMath in case this already exists *)
Definition hSet_not_set : ¬ isaset hSet.
  apply total2_neg_to_neg_forall. exists boolset.
  apply total2_neg_to_neg_forall. exists boolset.
  eapply negf. { eapply (isofhlevelweqf 1). apply hSet_univalence. }
  eapply negf. { apply proofirrelevance. }
  apply total2_neg_to_neg_forall. exists (idweq _).
  apply total2_neg_to_neg_forall. exists negb_weq.
  eapply negf. { apply (maponpaths (fun (f : _ ≃ _) => f true)). }
  simpl. exact nopathstruetofalse.
Qed.

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
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.pullbacks.
Require Export UniMath.CategoryTheory.categories.HSET.Core.
Require Export UniMath.CategoryTheory.categories.HSET.Limits.
Require Export UniMath.CategoryTheory.categories.HSET.Univalence.
Require Export UniMath.CategoryTheory.ArrowCategory.
Require Export UniMath.CategoryTheory.catiso.
Require Export UniMath.CategoryTheory.CategoryEquality.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.ComprehensionC.

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

(* ** Surjectivity *)

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


(** * Category theory *)

(** ** Isomorphism lemmas *)

Arguments functor_on_inv_from_iso {_ _} _  {_ _} f.

Lemma is_iso_comp_is_iso {C : precategory} {a b c : ob C}
  (f : C⟦a, b⟧) (g : C⟦b, c⟧) 
  : is_iso f -> is_iso g -> is_iso (f ;; g).
Proof.
  intros Hf Hg.
  apply (is_iso_comp_of_isos (make_iso f Hf) (make_iso g Hg)).
Defined.

Lemma functor_is_iso_is_iso {C C' : precategory} (F : functor C C')
    {a b : ob C} (f : C ⟦a,b⟧) (fH : is_iso f) : is_iso (#F f).
Proof.
  apply (functor_on_iso_is_iso _ _ F _ _ (make_iso f fH)).
Defined.


(* TODO: check more thoroughly if this is provided in the library; if so, use the library version, otherwise move this upstream.  Cf. also https://github.com/UniMath/UniMath/issues/279 *)
Lemma inv_from_iso_from_is_z_iso {D: precategory} {a b : D}
  (f: a --> b) (g : b --> a) (H : is_inverse_in_precat f g)
: inv_from_iso (f ,, (is_iso_from_is_z_iso _ (g ,, H))) 
  = g.
Proof.
  cbn. apply id_right.
Qed.

Definition iso_ob {C : precategory} {D : category}
          {F G : functor C D} (a : iso (C:= [C, D]) F G)
  : ∏ c, iso (F c) (G c).
Proof.
  intro c.
  use make_iso.
  - cbn. apply ((pr1 a : nat_trans _ _ ) c).
  - apply is_functor_iso_pointwise_if_iso. apply (pr2 a).
Defined.

(** ** The total type of morphisms of a precategory *)

Definition mor_total (C : precategory) : UU
  := ∑ (ab : C × C), C⟦pr2 ab, pr1 ab⟧.

Definition morphism_as_total {C : precategory} {a b : C} (f : a --> b)
  : mor_total C.
Proof.
  exists (b,,a).
  exact f.
Defined.

Definition source {C} (X : mor_total C) : C := pr2 (pr1 X).
Definition target {C} (X : mor_total C) : C := pr1 (pr1 X).
Definition morphism_from_total {C} (X : mor_total C)
  : C ⟦source X, target X⟧
  := pr2 X.
Coercion morphism_from_total : mor_total >-> precategory_morphisms.

Definition functor_on_mor_total {C D : precategory} (F : functor C D) 
           (p : mor_total C) : mor_total D.
Proof.
  exists (F (pr1 (pr1 p)) ,, F (pr2 (pr1 p)) ).
  exact (#F p).
Defined.


Definition isweq_left_adj_equivalence_on_mor_total
    {C D : category} (F : functor C D)
    (isC : is_univalent C) (isD : is_univalent D)
    (H : adj_equivalence_of_cats F) 
  : isweq (functor_on_mor_total F).
Proof.
  use (gradth _ _ _ _ ).
  - apply (functor_on_mor_total (adj_equivalence_inv H)).
  - intro p.
    use total2_paths_f.
    + cbn. destruct p as [[a b] f].
      apply pathsdirprod; cbn. 
      * apply (isotoid _ isC). 
        apply iso_inv_from_iso, (unit_pointwise_iso_from_adj_equivalence H).
      * apply (isotoid _ isC).
        apply iso_inv_from_iso, (unit_pointwise_iso_from_adj_equivalence H).
    + cbn. destruct p as [[a b] f]. cbn in *.
      etrans. apply (transportf_pair (λ x : C × C, C ⟦ pr2 x, pr1 x ⟧)).
      cbn.
      rewrite transportf_isotoid.
      rewrite transportf_isotoid'.
      cbn. unfold precomp_with. rewrite id_right.
      rewrite assoc.
      assert (XR := nat_trans_ax (unit_from_are_adjoints (pr2 (pr1 H)))).
      cbn in XR. rewrite <- XR.
      rewrite <- assoc. 
      etrans. apply maponpaths.
      apply (iso_inv_after_iso (unit_pointwise_iso_from_adj_equivalence H a)).
      apply id_right.
    - intro p.
    use total2_paths_f.
    + cbn. destruct p as [[a b] f].
      apply pathsdirprod; cbn. 
      * apply (isotoid _ isD). 
        apply (counit_pointwise_iso_from_adj_equivalence H).
      * apply (isotoid _ isD).
        apply (counit_pointwise_iso_from_adj_equivalence H).
    + cbn. destruct p as [[a b] f]. cbn in *.
      etrans. apply (transportf_pair (λ x : D × D, D ⟦ pr2 x, pr1 x ⟧)).
      cbn.
      rewrite transportf_isotoid.
      rewrite transportf_isotoid'.
      cbn. unfold precomp_with. 
      assert (XR := nat_trans_ax (counit_from_are_adjoints (pr2 (pr1 H)))).
      cbn in XR. rewrite XR. clear XR.
      rewrite assoc. 
      etrans. apply maponpaths_2.
      apply (iso_after_iso_inv (counit_pointwise_iso_from_adj_equivalence H _)).
      apply id_left.
Defined.

Definition isweq_equivalence_on_mor_total {C D : category}
           (isC : is_univalent C) (isD : is_univalent D)
           (F : functor C D) (G : functor D C)
           (eta : iso (C:= [_ , _ ]) (functor_identity C) (F ∙ G))
           (eps : iso (C:= [_ , _ ]) (G ∙ F) (functor_identity D))
: isweq (functor_on_mor_total F).
Proof.
  use (gradth _ _ _ _ ).
  - apply (functor_on_mor_total G).
  - intro p.
    use total2_paths_f.
    + cbn. destruct p as [[a b] f].
      apply pathsdirprod; cbn. 
      * apply (isotoid _ isC). 
        apply iso_inv_from_iso. apply (iso_ob eta).
      * apply (isotoid _ isC).
        apply iso_inv_from_iso. apply (iso_ob eta).
    + cbn. destruct p as [[a b] f]. cbn in *.
      etrans. apply (transportf_pair (λ x : C × C, C ⟦ pr2 x, pr1 x ⟧)).
      cbn.
      rewrite transportf_isotoid.
      rewrite transportf_isotoid'.
      cbn. unfold precomp_with. rewrite id_right.
      rewrite assoc. assert (XR := nat_trans_ax (pr1 eta)).
      cbn in XR. rewrite <- XR.
      rewrite <- assoc.
      rewrite id_right.
      etrans. apply maponpaths.
      apply (nat_trans_inv_pointwise_inv_after _ _ C _ _ (pr1 eta)).
      apply id_right.
  - intro p.
    use total2_paths_f.
    + cbn. destruct p as [[a b] f].
      apply pathsdirprod; cbn. 
      * apply (isotoid _ isD). 
        apply (iso_ob eps).
      * apply (isotoid _ isD).
        apply (iso_ob eps).
    + cbn. destruct p as [[a b] f]. cbn in *.
      etrans. apply (transportf_pair (λ x : D × D, D ⟦ pr2 x, pr1 x ⟧)).
      cbn.
      rewrite transportf_isotoid.
      rewrite transportf_isotoid'.
      cbn. unfold precomp_with. 
      assert (XR := nat_trans_ax (pr1 eps)).
      cbn in XR. rewrite XR. clear XR.
      rewrite assoc. 
      rewrite id_right.
      etrans. apply maponpaths_2.
      apply (nat_trans_inv_pointwise_inv_before _ _ D  _ _ (pr1 eps)).
      apply id_left.
Defined.


(** ** Equivalences of categories *)
(** Specifically: the composition of (adjoint) equivalences of precats. *)

Coercion left_adj_from_adj_equiv (X Y : category) (K : functor X Y)
         (HK : adj_equivalence_of_cats K)
  : is_left_adjoint K
:= pr1 HK.

Section about_equivalences.

Variables D1 D2 : category.
Variable F : functor D1 D2.
Variable GG : adj_equivalence_of_cats F.

Let G : functor D2 D1 := right_adjoint GG.
Let η := unit_from_left_adjoint GG.
Let ε := counit_from_left_adjoint GG.
Let ηinv a := iso_inv_from_iso (unit_pointwise_iso_from_adj_equivalence GG a).
Let εinv a := iso_inv_from_iso (counit_pointwise_iso_from_adj_equivalence GG a).


Lemma right_adj_equiv_is_ff : fully_faithful G.
Proof.
  intros c d.
  set (inv := (fun f : D1 ⟦G c, G d⟧ => εinv _ ;; #F f ;; ε _ )).
  simpl in inv.
  apply (gradth _ inv ).
  - intro f. simpl in f. unfold inv.
    assert (XR := nat_trans_ax ε). simpl in XR.
    rewrite <- assoc.
    etrans. apply maponpaths. apply XR.
    rewrite assoc.
    etrans. apply maponpaths_2. apply iso_after_iso_inv.
    apply id_left.
  - intro g.
    unfold inv. repeat rewrite functor_comp.
    match goal with |[|- ?f1 ;; ?f2 ;; ?f3 = _ ] =>
       intermediate_path ((f1 ;; ηinv _ ) ;; (η _ ;; f2) ;; f3) end.
    + repeat rewrite <- assoc. apply maponpaths.
      repeat rewrite assoc.
      etrans.
      2: { do 2 apply maponpaths_2. eapply pathsinv0, iso_after_iso_inv. }
      rewrite id_left. apply idpath.
    + assert (XR := nat_trans_ax η). simpl in XR. rewrite <- XR. clear XR.
      repeat rewrite <- assoc.
      etrans. 
      { do 3 apply maponpaths. apply triangle_id_right_ad. }
      rewrite id_right.
      rewrite assoc.
      etrans. 2: { apply id_left. }
      apply maponpaths_2.
      etrans. { apply maponpaths_2. apply functor_on_inv_from_iso. }
      assert (XR := triangle_id_right_ad (pr2 (pr1 GG))).
      simpl in XR.
      unfold ηinv. simpl.
      match goal with |[|- inv_from_iso ?e ;; inv_from_iso ?f = _ ] =>
         assert (XRR := maponpaths pr1 (iso_inv_of_iso_comp _ _ _ _ f e)) end. 
      simpl in XRR.
      etrans. apply (! XRR). clear XRR.
      apply pathsinv0, inv_iso_unique'.
      simpl. cbn. unfold precomp_with.
      rewrite id_right. apply XR.
Defined.
  
Lemma right_adj_equiv_is_ess_sur : essentially_surjective G.
Proof.
  intro d.
  apply hinhpr.
  exists (F d).
  exact (ηinv d).
Defined.

End about_equivalences.




Section eqv_from_ess_split_and_ff.

Definition split_ess_surj {A B : precategory}
  (F : functor A B) 
  := ∏ b : B, ∑ a : A, iso (F a) b.

Context {A B : category}
        {F : functor A B}
        (Fff : fully_faithful F)
        (Fses : split_ess_surj F).

Let Fweq {a b} f := (weq_from_fully_faithful Fff a b f).
Let Finv {a b} g := (invweq (weq_from_fully_faithful Fff a b) g).

Definition G_ff_split_data : functor_data B A.
Proof.
  use tpair.
  - intro b. exact (pr1 (Fses b)).
  - intros b b' f'; cbn.
    apply Finv.
    exact (pr2 (Fses b) ;; f' ;; inv_from_iso (pr2 (Fses b'))).
Defined.

Definition G_ff_split_ax : is_functor G_ff_split_data.
Proof.
  split.
  - intro b. cbn. rewrite id_right. simpl.
    apply invmap_eq. cbn.
    etrans. apply iso_inv_after_iso.
    apply pathsinv0, functor_id.
  - intros b b1 b2 f g.
    apply invmap_eq; cbn.
    rewrite functor_comp.
    apply pathsinv0.
    etrans. apply maponpaths.
       apply (homotweqinvweq (make_weq _ (Fff _ _ ))).
    etrans. apply maponpaths_2.
       apply (homotweqinvweq (make_weq _ (Fff _ _ ))).
    repeat rewrite <- assoc. apply maponpaths. apply maponpaths.
    repeat rewrite assoc. apply maponpaths_2.
    etrans. apply maponpaths_2.  apply iso_after_iso_inv.
    apply id_left.
Qed.

Definition G_ff_split : functor _ _ := ( _ ,, G_ff_split_ax).


Definition is_nat_trans_ε_ff_split : 
 is_nat_trans (functor_composite_data G_ff_split_data F)
    (functor_identity_data B) (λ b : B, pr2 (Fses b)).
Proof.
  intros b b' g;
  etrans; [ apply maponpaths_2 ; use homotweqinvweq |];
  repeat rewrite <- assoc; 
  apply maponpaths;
  rewrite iso_after_iso_inv;
  apply id_right.
Qed.

Definition ε_ff_split
  : nat_trans (functor_composite G_ff_split F) (functor_identity B).
Proof.
  use tpair.
  - intro b.
    exact (pr2 (Fses b)).
  - apply is_nat_trans_ε_ff_split.
Defined.

Lemma is_nat_trans_η_ff_split : 
 is_nat_trans (functor_identity_data A)
    (functor_composite_data F G_ff_split_data)
    (λ a : A, Finv (inv_from_iso (pr2 (Fses (F ((functor_identity A) a)))))).
Proof.
  intros a a' f;
  apply (invmaponpathsweq (make_weq _ (Fff _ _ )));
  cbn;
  rewrite functor_comp;
  rewrite functor_comp;
  etrans; [ apply maponpaths; use homotweqinvweq |];
  apply pathsinv0;
  etrans; [ apply maponpaths; use homotweqinvweq |];
  etrans; [ apply maponpaths_2; use homotweqinvweq |];
  repeat rewrite assoc;
  rewrite iso_after_iso_inv;
  rewrite id_left ;
  apply idpath.
Qed.


Definition η_ff_split
  : nat_trans (functor_identity A) (functor_composite F G_ff_split).
Proof.
  use tpair.
  -  intro a.
     apply Finv.
     apply (inv_from_iso (pr2 (Fses _ ))).
  - apply is_nat_trans_η_ff_split. 
Defined.
    
Lemma form_adjunction_ff_split 
  : form_adjunction F G_ff_split η_ff_split ε_ff_split.
  simpl. split.
  * intro a.
    cbn. 
    etrans. apply maponpaths_2. use homotweqinvweq. 
    apply iso_after_iso_inv.
  * intro b.
    cbn. 
    apply (invmaponpathsweq (make_weq _ (Fff _ _ ))).
    cbn.
    rewrite functor_comp.
    rewrite functor_id.
    etrans. apply maponpaths. use homotweqinvweq.
    etrans. apply maponpaths_2. use homotweqinvweq.
    repeat rewrite assoc.
    rewrite iso_after_iso_inv.
    rewrite id_left.
    apply iso_inv_after_iso.
Qed.

Definition adj_equivalence_of_cats_ff_split : adj_equivalence_of_cats F.
Proof.
  use tpair.
  - exists G_ff_split.
    use tpair.
    + exists η_ff_split. 
      exact ε_ff_split. 
    + apply form_adjunction_ff_split. 
  - split; cbn.
    + intro a. 
      use (fully_faithful_reflects_iso_proof _ _ _ Fff _ _ (make_iso _ _ )).
      apply is_iso_inv_from_iso. 
    + intro b. apply pr2.
Defined.

End eqv_from_ess_split_and_ff.

(** ** Properties of functors *)

Definition split_full {C D : precategory} (F : functor C D) : UU
  := ∏ c c' (f : F c --> F c'), hfiber (#F) f.

Lemma full_from_split_full {C D : precategory} (F : functor C D)
  : split_full F -> full F.
Proof.
  intros H c c' f.
  apply hinhpr, H.
Qed.

Lemma split_full_from_ff {C D : precategory} (F : functor C D)
  : fully_faithful F -> split_full F.
Proof.
  intros H c c' f.
  exists (fully_faithful_inv_hom H c c' f).
  apply (homotweqinvweq (weq_from_fully_faithful _ _ _)).
Qed.

Lemma full_from_ff
  {D D' : precategory} (F : functor D D')
  : fully_faithful F -> full F.
Proof.
  intros. apply full_from_split_full, split_full_from_ff; assumption.
Qed.

Lemma right_adj_equiv_is_full {D1 D2 : category}
  (F : functor D1 D2) (GG : adj_equivalence_of_cats F)
  : full (right_adjoint GG).
Proof.
  apply full_from_ff, right_adj_equiv_is_ff.
Qed.


Definition ff_on_isos {C D : precategory} (F : functor C D) : UU
  := ∏ c c', isweq (@functor_on_iso _ _ F c c').

Lemma fully_faithful_impl_ff_on_isos {C D : precategory} (F : functor C D) 
      : fully_faithful F -> ff_on_isos F.
Proof.
  intros Fff c c'.
  use gradth.
  - intro XR. exists (invmap (make_weq _ (Fff _ _ )) XR). cbn.
    apply (ff_reflects_is_iso _ _ _ Fff).
    assert (XT := homotweqinvweq (make_weq _ (Fff c c' ))).
    cbn in *.
    apply (transportb (λ i : _ --> _, is_iso i) (XT (pr1 XR) )).
    apply XR.
  - cbn. intro i. apply eq_iso. cbn.
    apply (homotinvweqweq (make_weq _ (Fff _ _ ))).
  - cbn. intro i. apply eq_iso. cbn.
    apply (homotweqinvweq (make_weq _ (Fff _ _ ))).
Defined.


Definition reflects_pullbacks {C D : category} (F : functor C D) : UU
  := ∏ {a b c d : C}{f : C ⟦b, a⟧} {g : C ⟦c, a⟧} {h : C⟦d, b⟧} {k : C⟦d,c⟧}
       (H : h · f = k · g),
     isPullback (functor_on_square _ _ F H) -> isPullback H.

Lemma ff_reflects_pullbacks {C D : category} {F : functor C D}
      (F_ff : fully_faithful F) : reflects_pullbacks F.
Proof.
  do 10 intro.
  use (isPullback_preimage_square _ _ _ _ _ _ X).
  - apply homset_property.
  - apply F_ff.
Defined.

(** ** Idtoiso and isotoid *)

Lemma idtoiso_identity_iso {C : precategory} (a : C)
  : idtoiso (idpath a) = identity_iso a.
Proof.
  apply idpath.
Defined.

Lemma idtoiso_identity {C : precategory} (a : C)
  : (idtoiso (idpath a) : _ --> _) = identity a.
Proof.
  apply idpath.
Defined.

Lemma forall_isotid (A : category) (a_is : is_univalent A) 
      (a a' : A) (P : iso a a' -> UU) :
  (∏ e, P (idtoiso e)) → ∏ i, P i.
Proof.
  intros H i.
  rewrite <- (idtoiso_isotoid _ a_is).
  apply H.
Defined.

Lemma transportf_isotoid_functor 
  (A X : category) (H : is_univalent A)
  (K : functor A X)
   (a a' : A) (p : iso a a') (b : X) (f : K a --> b) :
 transportf (fun a0 => K a0 --> b) (isotoid _ H p) f = #K (inv_from_iso p) ;; f.
Proof.
  rewrite functor_on_inv_from_iso. simpl. cbn.
  unfold precomp_with. rewrite id_right.
  generalize p.
  apply forall_isotid.
  - apply H.
  - intro e. induction e.
    cbn.
    rewrite functor_id.
    rewrite id_left.
    rewrite isotoid_identity_iso.
    apply idpath.
Defined.


Lemma idtoiso_transportf_family_of_morphisms (D : precategory)
      (A : UU) (B : A -> UU)
      (F : ∏ a, B a -> D)
      (d d' : D) (deq : d = d')
      (R : ∏ a (b : B a), D⟦ F a b, d⟧)
     
: transportf (λ x, ∏ a b, D⟦ F a b, x⟧) deq R 
  =
  λ a b, R a b ;; idtoiso deq.
Proof.
  destruct deq.
  apply funextsec.
  intro. apply funextsec. intro.
  apply pathsinv0.
  apply id_right.
Qed.


Lemma idtoiso_concat_pr (C : precategory) (a a' a'' : ob C)
  (p : a = a') (q : a' = a'') :
  idtoiso p ;; idtoiso q = idtoiso (p @ q).
Proof.
  apply pathsinv0.
  apply (base_paths _ _ (idtoiso_concat _ _ _ _ _ _ )).
Defined.

Lemma idtoiso_eq_idpath (C : precategory) (a : C) (e : a = a)
    (H : e = idpath _ )
  : (idtoiso e : _ --> _) = identity_iso _.
Proof.
  apply maponpaths, (maponpaths idtoiso H).
Qed.

Lemma idtoiso_precompose'
  : ∏ (C : precategory) (a a' b : C) (p : a' = a) (f : C ⟦ a, b ⟧),
    transportb (λ a0 : C, C ⟦ a0, b ⟧) p f = (idtoiso p;; f)%mor.
Proof.
  intros; induction p. apply pathsinv0, id_left.
Defined.

Lemma idtoiso_postcompose_idtoiso_pre {C : precategory} {a b c : C} 
      (g : a --> b) (f : a --> c)
      (p : b = c) 
  : g = f ;; idtoiso (!p) -> g ;; idtoiso p = f.
Proof.
  induction p. simpl.
  rewrite id_right.
  induction 1.
  apply id_right.
Qed.

(* Left-handed counterpart to [transportf_isotoid], which could be called [prewhisker_isotoid] analogously — neither of these is a fully general transport lemma, they’re about specific cases.

  TODO: look for dupes in library; move; consider naming conventions; rename D to C. *)
Lemma postwhisker_isotoid {D : category} (H : is_univalent D)
    {a b b' : D} (f : a --> b) (p : iso b b')
  : transportf (fun b0 => a --> b0) (isotoid _ H p) f
  = f ;; p.
Proof.
  rewrite <- idtoiso_postcompose.
  apply maponpaths, maponpaths, idtoiso_isotoid.
Qed.

(** ** Misc lemmas/definitions on (pre)categories *)

Coercion univalent_category_is_univalent : univalent_category >-> is_univalent.

Definition functor_univalent_category (C : precategory) (D : univalent_category)
  : univalent_category.
Proof.
  exists (functor_category C D).
  apply is_univalent_functor_category.
  apply D.
Defined.

Definition adj_from_equiv (D1 D2 : category) (F : functor D1 D2):
    adj_equivalence_of_cats F → is_left_adjoint F := fun x => pr1 x.
Coercion adj_from_equiv : adj_equivalence_of_cats >-> is_left_adjoint.

(** ** Functors and isomorphisms *)

Lemma inv_from_iso_iso_from_fully_faithful_reflection {C D : precategory}
      (F : functor C D) (HF : fully_faithful F) (a b : C) (i : iso (F a) (F b))
      : inv_from_iso
       (iso_from_fully_faithful_reflection HF i) = 
 iso_from_fully_faithful_reflection HF (iso_inv_from_iso i).
Proof.
  cbn.
  unfold precomp_with.
  apply id_right.
Defined.

Definition nat_iso_from_pointwise_iso (D : precategory) (E : category)
  (F G : [D, E])
  (a : ∏ d, iso ((F : functor _ _) d) ((G : functor _ _) d))
  (H : is_nat_trans _ _ a)
  : iso F G.
Proof.
  use functor_iso_from_pointwise_iso .
  use tpair.
  - intro d. apply a.
  - apply H.
  - intro d. apply (pr2 (a d)).
Defined.

Lemma iso_from_iso_with_postcomp (D E E' : category)
  (F G : functor D E) (H : functor E E')
  (Hff : fully_faithful H) : 
  iso (C:=[D, E']) (functor_composite F H) (functor_composite G H)
  ->
  iso (C:=[D, E]) F G.
Proof.
  intro a.
  use nat_iso_from_pointwise_iso.
  - intro d. simpl.
    apply (iso_from_fully_faithful_reflection Hff).
    apply (functor_iso_pointwise_if_iso _ _ _ _ _ a (pr2 a)).
  - abstract (
    simpl; intros d d' f;
    assert (XR := nat_trans_ax (pr1 a : nat_trans _ _ ));
    simpl in XR;
    apply (invmaponpathsweq (weq_from_fully_faithful Hff _ _ ));
    simpl; rewrite functor_comp; rewrite functor_comp;
    assert (XTT:=homotweqinvweq (weq_from_fully_faithful Hff (F d') (G d')  ));
    simpl in *;
    etrans; [apply maponpaths; apply XTT |];
    clear XTT;
    assert (XTT:=homotweqinvweq (weq_from_fully_faithful Hff (F d) (G d)  ));
    simpl in *;
    etrans; [| apply maponpaths_2; apply (!XTT _ )];
    apply XR
    ).
Defined.

Definition functor_assoc_iso (D1 D2 D3 : precategory) (D4 : category)
     (F : functor D1 D2) (G : functor D2 D3) (H : functor D3 D4) :
    iso (C:=[D1,D4])
         (functor_composite (functor_composite F G) H)
         (functor_composite F (functor_composite G H)).
Proof.
  use nat_iso_from_pointwise_iso.
  - intro d. apply identity_iso.
  - abstract (
        intros x x' f;
        rewrite id_left;
        rewrite id_right;
        apply idpath
     ).
Defined.

Definition functor_comp_id_iso (D1 : precategory) (D2 : category)
     (F : functor D1 D2) :
  iso (C:=[D1,D2]) (functor_composite F (functor_identity _ )) F.
Proof.
  use nat_iso_from_pointwise_iso.
  - intro. apply identity_iso.
  - abstract (
       intros x x' f;
       rewrite id_left;
       rewrite id_right;
       apply idpath
    ).
Defined.

Definition functor_precomp_iso (D1 D2 : precategory) (D3 : category)
    (F : functor D1 D2) (G H : functor D2 D3) :
    iso (C:=[D2,D3]) G H ->
    iso (C:=[D1,D3]) (functor_composite F G)
                          (functor_composite F H).
Proof.
  intro a.
  use nat_iso_from_pointwise_iso.
  - intro d. apply (functor_iso_pointwise_if_iso _ _ _ _ _ a (pr2 a)).
  - abstract (intros x x' f; apply (nat_trans_ax (pr1 a))).
Defined.



(** ** Presheaves and Yoneda *)

Arguments nat_trans_ax {C C'} {F F'} a {x x'} f.
Arguments nat_trans_comp {_ _ _ _ _} _ _.

Definition preShv C := functor_univalent_category C^op HSET_univalent_category.

Notation "'Yo'" := (yoneda _ : functor _ (preShv _)).
Notation "'Yo^-1'" := (invweq (make_weq _ (yoneda_fully_faithful _ _ _ ))).

(* TODO: perhaps rename e.g. [yoneda_eq]? *)
Definition yy {C : category}
    {F : preShv C} {c : C}
  : ((F : functor _ _) c : hSet) ≃ _ ⟦ yoneda _ c, F⟧.
Proof.
  apply invweq.
  apply yoneda_weq.
Defined.

Lemma yy_natural {C : category} 
  (F : preShv C) (c : C) (A : (F:functor _ _) c : hSet) 
                  c' (f : C⟦c', c⟧) :
        yy (# (F : functor _ _) f A) = # (yoneda _ ) f ;; yy A.
Proof.
  apply (toforallpaths (is_natural_yoneda_iso_inv _ F _ _ f)).
Qed.

Lemma yy_comp_nat_trans {C : category}
      (F F' : preShv C) (p : _ ⟦F, F'⟧)
      A (v : (F : functor _ _ ) A : hSet)
  : yy v ;; p = yy ((p : nat_trans _ _ )  _ v).
Proof.
  apply nat_trans_eq.
  - apply homset_property.
  - intro c. simpl. 
    apply funextsec. intro f. cbn.
    apply (toforallpaths (nat_trans_ax p f)).
Qed.

Lemma yoneda_postcompose {C : category} (P : preShv C)
  {y z : C} (α : P --> Yo y) (f : y --> z)
  {x:C} (p : (P : functor _ _) x : hSet)
  : ((α : nat_trans _ _) x p) ;; f
    = (α ;; yoneda_morphisms _ _ _ f : nat_trans _ _) x p.
Proof.
  apply idpath.
Defined.

Lemma transportf_yy {C : category}
      (F : preShv C) (c c' : C) (A : (F : functor _ _ ) c : hSet)
      (e : c = c'):
  yy (transportf (fun d => (F : functor _ _ ) d : hSet) e A) = 
  transportf (fun d => preShv C ⟦ yoneda _ d, F⟧) e (yy A).
Proof.
  induction e.
  apply idpath.
Defined.

Lemma transportf_pshf' {C : category} (P : preShv C)
  {c c' : C} (e : c = c')
  (x : (P : functor _ _) c : hSet)
  : transportf (fun c => (P : functor _ _) c : hSet) e x
    = # (P : functor _ _) (idtoiso (!e)) x.
Proof.
  destruct e. cbn.
  apply pathsinv0. 
  revert x; apply toforallpaths. 
  apply (functor_id P).
Qed.

(** ** Basic pullback utility functions *)

Section Pullback_Basics.

Definition map_into_Pb
    {C : precategory} {a b c d : C}
    {f : a --> b} {g : a --> c} {k : b --> d} {h : c --> d}
    {sqr_comm : f ;; k = g ;; h}
    (Pb : isPullback sqr_comm)
    {e : C} (x : e --> b) (y : e --> c) (H : x ;; k = y ;; h)
  :  e --> a.
Proof.
  eapply (PullbackArrow (make_Pullback _ Pb)).
  apply H.
Defined.

Definition Pb_map_commutes_1
    {C : precategory} {a b c d : C}
    {f : a --> b} {g : a --> c} {k : b --> d} {h : c --> d}
    {sqr_comm : f ;; k = g ;; h}
    (Pb : isPullback sqr_comm)
    {e : C} (x : e --> b) (y : e --> c) H
  : map_into_Pb Pb x y H ;; f = x.
Proof.
  apply (PullbackArrow_PullbackPr1 (make_Pullback _ _)).
Qed.

Definition Pb_map_commutes_2
    {C : precategory} {a b c d : C}
    {f : a --> b} {g : a --> c} {k : b --> d} {h : c --> d}
    {sqr_comm : f ;; k = g ;; h}
    (Pb : isPullback sqr_comm)
    {e : C} (x : e --> b) (y : e --> c) H
  : map_into_Pb Pb x y H ;; g = y.
Proof.
  apply (PullbackArrow_PullbackPr2 (make_Pullback _ _)).
Qed.

Lemma map_into_Pb_unique
    {C : precategory} {a b c d : C}
    {f : a --> b} {g : a --> c} {k : b --> d} {h : c --> d}
    {sqr_comm : f ;; k = g ;; h}
    (Pb : isPullback sqr_comm)
    {e : C} {x y : e --> a}
    (e_f : x ;; f = y ;; f) (e_g : x ;; g = y ;; g)
  : x = y.
Proof.
  etrans.
  { use (PullbackArrowUnique _ Pb); try eassumption.
    repeat rewrite <- assoc. apply maponpaths; assumption. }
  apply pathsinv0, (PullbackArrowUnique _ Pb); apply idpath.
Qed.

(* In fact this is trivial, since the equality doesn’t appear in the type of the pullback. However, it’s convenient for proof scripts. *)
Lemma isPullback_indepdent_of_path
    {C : precategory} {a b c d : C}
    {f : a --> b} {g : a --> c} {k : b --> d} {h : c --> d}
    {sqr_comm : f ;; k = g ;; h}
    (Pb : isPullback sqr_comm)
    (sqr_comm' :  f ;; k = g ;; h)
  : isPullback (sqr_comm').
Proof.
  exact Pb.
Defined.

(* Duplicate of [is_symmetric_isPullback] from UniMath, but without the un-needed [has_homsets]/[category] assumption *)
Lemma is_symmetric_isPullback
    {C : precategory}
    {a b c d : C} {f : b --> a} {g : c --> a}
    {p1 : d --> b} {p2 : d --> c} {H : p1 · f = p2 · g}
    (pb : isPullback H)
  : isPullback (! H).
Proof.
  use make_isPullback.
  intros e h k H'.
  use (iscontrweqf _ (pb e k h (! H'))).
  use (weqtotal2 (idweq _)).
  intros ?. apply weqdirprodcomm.
Defined.

(* Variant of [is_symmetric_isPullback], more convenient for applying when reasoning bottom-up. *)
Lemma is_symmetric'_isPullback
    {C : precategory}
    {a b c d : C} {f : b --> a} {g : c --> a}
    {p1 : d --> b} {p2 : d --> c} {H : p1 · f = p2 · g}
    (pb : isPullback (! H))
  : isPullback H.
Proof.
  eapply transportf. 2: { eapply is_symmetric_isPullback, pb. }
  apply pathsinv0inv0.
Defined.

End Pullback_Basics.

(** ** Pullback transfer lemmas *)

Section Pullback_transfers.
(* Various results, generally showing that perturbing a pullback squares by equalities and/or isos is still a pullback. *)

Lemma square_morphism_equal
    {C : precategory} {a b c d : C}
    {f : a --> b} {g : a --> c} {k : b --> d} {h : c --> d}
    (sqr_comm : f ;; k = g ;; h)
    {k'} (e : k' = k)
  : f ;; k' = g ;; h.
Proof.
  rewrite e. assumption.
Defined.

Lemma isPb_morphism_equal
    {C : precategory} {a b c d : C}
    {f : a --> b} {g : a --> c} {k : b --> d} {h : c --> d}
    (sqr_comm : f ;; k = g ;; h)
    (Pb : isPullback sqr_comm)
    {k'} (e : k' = k)
  : isPullback (square_morphism_equal sqr_comm e).
Proof.
  match goal with |[|- isPullback ?HH] => generalize HH end.
  rewrite e.
  intro.
  apply Pb.
Defined.

Definition commutes_and_is_pullback {C : category} {a b c d : C}
    (f : b --> a) (g : c --> a) (p1 : d --> b) (p2 : d --> c)
  : UU
:= ∑ (H : p1 ;; f = p2 ;; g), isPullback H.

(* Note: should have a dual version where [i_a], instead of [i_d], is assumed iso (and using [post_comp_with_iso_is_inj] in the proof). *)
Lemma commuting_square_transfer_iso {C : precategory}
      {a b c d : C}
      {f : b --> a} {g : c --> a} {p1 : d --> b} {p2 : d --> c}
      {a' b' c' d' : C}
      {f' : b' --> a'} {g' : c' --> a'} {p1' : d' --> b'} {p2' : d' --> c'}
      {i_a : a --> a'} {i_b : b --> b'} {i_c : c --> c'} {i_d : iso d d'}
      (i_f : f ;; i_a = i_b ;; f') (i_g : g ;; i_a = i_c ;; g')
      (i_p1 : p1 ;; i_b = i_d ;; p1') (i_p2 : p2 ;; i_c = i_d ;; p2')
   : p1 ;; f = p2;; g
   -> p1' ;; f' = p2' ;; g'.
Proof.
  intro H.
  refine (pre_comp_with_iso_is_inj _ _ _ i_d _ _ _ _).
  exact (pr2 i_d).  (* TODO: access function [is_iso_from_iso]? *)
  rewrite 2 assoc.
  rewrite <- i_p1, <- i_p2.
  rewrite <- 2 assoc.
  rewrite <- i_f, <- i_g.
  rewrite 2 assoc.
  apply maponpaths_2, H.
Qed.

(* Generalisation of [isPulback_iso_of_morphisms].
TODO: This probably should work in an arbitrary precategory, i.e. not requiring the hom-sets assumption.  Try upgrading proof to show that? *)
Lemma isPullback_transfer_iso {C : category}
      {a b c d : C}
      {f : b --> a} {g : c --> a} {p1 : d --> b} {p2 : d --> c}
      (H : p1 ;; f = p2;; g)
      {a' b' c' d' : C}
      {f' : b' --> a'} {g' : c' --> a'} {p1' : d' --> b'} {p2' : d' --> c'}
      (H' : p1' ;; f' = p2' ;; g')
      {i_a : iso a a'} {i_b : iso b b'} {i_c : iso c c'} {i_d : iso d d'}
      (i_f : f ;; i_a = i_b ;; f') (i_g : g ;; i_a = i_c ;; g')
      (i_p1 : p1 ;; i_b = i_d ;; p1') (i_p2 : p2 ;; i_c = i_d ;; p2')
   : isPullback H
   -> isPullback H'.
Proof.
  intros Hpb.
  apply (make_isPullback _ ).    
  intros X h k H''.
  simple refine (tpair _ _ _ ).
  - simple refine (tpair _ _ _ ).
    { refine ( _ ;; i_d ).
      simple refine (PullbackArrow (make_Pullback _ Hpb) _ _ _ _).
      + exact (h ;; iso_inv_from_iso i_b).
      + exact (k ;; iso_inv_from_iso i_c).
      + abstract (
          apply (post_comp_with_iso_is_inj _ _ i_a (pr2 _));
          repeat rewrite <- assoc;
          rewrite i_f, i_g;
          eapply @pathscomp0;
          [ apply maponpaths; rewrite assoc;
            apply maponpaths_2, iso_after_iso_inv
          | eapply @pathsinv0, @pathscomp0;
          [ apply maponpaths; rewrite assoc;
            apply maponpaths_2, iso_after_iso_inv
          | rewrite 2 id_left; apply @pathsinv0, H''
          ]]
        ).
    }
    cbn; split;
    abstract (
      rewrite <- assoc;
      eapply @pathscomp0;
      [ apply maponpaths, @pathsinv0;
        try apply i_p2; try apply i_p1
      | rewrite assoc;
      eapply @pathscomp0;
      [ apply maponpaths_2;
        try apply (PullbackArrow_PullbackPr2 (make_Pullback _ _));
        try apply (PullbackArrow_PullbackPr1 (make_Pullback _ _))
      | rewrite <- assoc, iso_after_iso_inv; apply id_right]] ).
  - intros hk'.
    apply subtypePath.
      intro; apply isapropdirprod; apply homset_property.
    cbn.
    apply (post_comp_with_iso_is_inj _ _ (iso_inv_from_iso i_d) (pr2 _)).
    eapply @pathscomp0.
    2: { rewrite <- assoc. cbn. rewrite iso_inv_after_iso.
         eapply pathsinv0, id_right. }
    apply PullbackArrowUnique; cbn.
    + apply (post_comp_with_iso_is_inj _ _ i_b (pr2 _)).
      repeat rewrite <- assoc.
      rewrite i_p1, iso_after_iso_inv, id_right.
      eapply @pathscomp0.
        apply maponpaths. rewrite assoc, iso_after_iso_inv. apply id_left.
      apply (pr1 (pr2 hk')).
    + apply (post_comp_with_iso_is_inj _ _ i_c (pr2 _)).
      repeat rewrite <- assoc.
      rewrite i_p2, iso_after_iso_inv, id_right.
      eapply @pathscomp0.
        apply maponpaths. rewrite assoc, iso_after_iso_inv. apply id_left.
      apply (pr2 (pr2 hk')).
  Qed.

(* Generalisation of [isPulback_iso_of_morphisms]. *)
Lemma commutes_and_is_pullback_transfer_iso {C : category}
      {a b c d : C}
      {f : b --> a} {g : c --> a} {p1 : d --> b} {p2 : d --> c}
      {a' b' c' d' : C}
      {f' : b' --> a'} {g' : c' --> a'} {p1' : d' --> b'} {p2' : d' --> c'}
      {i_a : iso a a'} {i_b : iso b b'} {i_c : iso c c'} {i_d : iso d d'}
      (i_f : f ;; i_a = i_b ;; f') (i_g : g ;; i_a = i_c ;; g')
      (i_p1 : p1 ;; i_b = i_d ;; p1') (i_p2 : p2 ;; i_c = i_d ;; p2')
      (H : p1 ;; f = p2 ;; g) (P : isPullback H)
   : commutes_and_is_pullback f' g' p1' p2'.
Proof.
  exists (commuting_square_transfer_iso i_f i_g i_p1 i_p2 H).
  exact (isPullback_transfer_iso _ _ i_f i_g i_p1 i_p2 P).
Qed.

Lemma postcomp_commutes_and_is_pb_with_iso
    {C : category} {a b c d : C}
    {f : a --> b} {g : a --> c} {k : b --> d} {h : c --> d}
    (sqr_comm : f ;; k = g ;; h)
    (Pb : isPullback sqr_comm)
    {y : C} (r : y --> d) (i : iso b y) (Hi : i ;; r = k)
  : ∑ H : f ;; i ;; r = g ;; h, isPullback H.
Proof.
  simple refine (commutes_and_is_pullback_transfer_iso _ _ _ _ _ Pb);
    try apply identity_iso;
    try rewrite id_left;
    try rewrite id_right;
    try apply idpath.
  apply pathsinv0, Hi.
Qed.

Definition postcomp_pb_with_iso
    {C : category} {a b c d : C}
    {f : a --> b} {g : a --> c} {k : b --> d} {h : c --> d}
    (sqr_comm : f ;; k = g ;; h)
    (Pb : isPullback sqr_comm)
    {y : C} (r : y --> d) (i : iso b y) (Hi : i ;; r = k)
  : isPullback _
:= pr2 (postcomp_commutes_and_is_pb_with_iso _ Pb _ i Hi).

End Pullback_transfers.

(** ** Pullbacks of sets and presheaves *)

Section Pullbacks_hSet.

(* TODO: does this already exist?

  If we had the standard pullback of hsets defined, this could be maybe better stated as the fact that P is a pullback if the map from P to the standard pullback is an iso. *)
Lemma isPullback_HSET {P A B C : HSET}
    (p1 : P --> A) (p2 : P --> B) (f : A --> C) (g : B --> C)
    (ep : p1 ;; f = p2 ;; g)
  : (∏ a b (e : f a = g b), ∃! ab, p1 ab = a × p2 ab = b)
  -> isPullback ep.
Proof.
  intros H X h k ehk.
  set (H_existence := fun a b e => pr1 (H a b e)).
  set (H_uniqueness
    := fun a b e x x' => base_paths _ _ (proofirrelevancecontr (H a b e) x x')).
  apply iscontraprop1.
  - apply invproofirrelevance.
    intros hk hk'.
    apply subtypePath. { intro. apply isapropdirprod; apply setproperty. }
    destruct hk as [hk [eh ek]], hk' as [hk' [eh' ek']]; simpl.
    apply funextsec; intro x.
    refine (H_uniqueness (h x) (k x) _ (_,,_) (_,,_));
      try split;
    revert x; apply toforallpaths; assumption.
  - use tpair. 
    + intros x. refine (pr1 (H_existence (h x) (k x) _)).
      apply (toforallpaths ehk).
    + simpl.
      split; apply funextsec; intro x.
      * apply (pr1 (pr2 (H_existence _ _ _))). 
      * apply (pr2 (pr2 (H_existence _ _ _))).
Qed.

(* TODO: unify with [isPullback_HSET]? *)
Lemma pullback_HSET_univprop_elements {P A B C : HSET}
    {p1 : HSET ⟦ P, A ⟧} {p2 : HSET ⟦ P, B ⟧}
    {f : HSET ⟦ A, C ⟧} {g : HSET ⟦ B, C ⟧}
    (ep : p1 ;; f = p2 ;; g)
    (pb : isPullback (*f g p1 p2*) ep)
  : (∏ a b (e : f a = g b), ∃! ab, p1 ab = a × p2 ab = b).
Proof.
  intros a b e.
  set (Pb := (make_Pullback _ pb)).
  apply iscontraprop1.
  - apply invproofirrelevance; intros [ab [ea eb]] [ab' [ea' eb']].
    apply subtypePath; simpl.
      intros x; apply isapropdirprod; apply setproperty.
    refine (@toforallpaths unitset _ _ _ _ tt).
    refine (MorphismsIntoPullbackEqual pb _ _ _ _ _ );
      apply funextsec; intros []; cbn;
      (eapply @pathscomp0; [ eassumption | apply pathsinv0; eassumption]).
  - simple refine (_,,_).
    refine (_ tt).
    refine (PullbackArrow Pb (unitset : HSET)
      (fun _ => a) (fun _ => b) _).
    apply funextsec; intro; exact e.
    simpl; split.
    + generalize tt; apply toforallpaths.
      apply (PullbackArrow_PullbackPr1 Pb unitset).
    + generalize tt; apply toforallpaths.
      apply (PullbackArrow_PullbackPr2 Pb unitset).
Defined.

Lemma pullback_HSET_elements_unique {P A B C : HSET}
    {p1 : HSET ⟦ P, A ⟧} {p2 : HSET ⟦ P, B ⟧}
    {f : HSET ⟦ A, C ⟧} {g : HSET ⟦ B, C ⟧}
    {ep : p1 ;; f = p2 ;; g}
    (pb : isPullback (*f g p1 p2*) ep)
    (ab ab' : P : hSet)
    (e1 : p1 ab = p1 ab') (e2 : p2 ab = p2 ab')
  : ab = ab'.
Proof.
  set (temp := proofirrelevancecontr 
    (pullback_HSET_univprop_elements _ pb (p1 ab') (p2 ab')
        (toforallpaths ep ab'))).
  refine (maponpaths pr1 (temp (ab,, _) (ab',, _))).
  - split; assumption.
  - split; apply idpath.
Qed.


(* TODO: upstream this and the following lemma, and unify them with the converse implication about pullbacks. *)
Lemma square_commutes_preShv_to_pointwise {C : category}
    {X Y Z W : preShv C}
    {f : Y --> X} {g : Z --> X} {p1 : W --> Y} {p2 : W --> Z}
    (e : p1 ;; f = p2 ;; g)
    (c : C)
  : ((p1 : nat_trans _ _) c) ;; ((f : nat_trans _ _) c)
  = ((p2 : nat_trans _ _) c) ;; ((g : nat_trans _ _) c).
Proof.
  apply (nat_trans_eq_pointwise e).
Qed.

(* TODO: unify with the converse implication;
  perhaps also generalise to all functor categories?  *)
Lemma isPullback_preShv_to_pointwise {C : category}
    {X Y Z W : preShv C}
    {f : Y --> X} {g : Z --> X} {p1 : W --> Y} {p2 : W --> Z}
    {e : p1 ;; f = p2 ;; g} (pb : isPullback e)
    (c : C)
  : isPullback (*((f : nat_trans _ _) c) ((g : nat_trans _ _) c)
      ((p1 : nat_trans _ _) c) ((p2 : nat_trans _ _) c) *)
      (square_commutes_preShv_to_pointwise e c).
Proof.
  set (XR := @isLimFunctor_is_pointwise_Lim C^op HSET
            pullback_graph).
  set (XT1 := pullback_diagram _ f g).
  specialize (XR XT1).
  transparent assert
       (XH : (∏ a : C^op,
        LimCone
          (@colimits.diagram_pointwise C^op HSET 
             pullback_graph XT1 a))).
    { intro. apply LimConeHSET.  }
    specialize (XR XH).
    specialize (XR W). 
    set (XT := PullbCone _ _ _ _ p1 p2 e).
    specialize (XR XT).
    transparent assert (XTT : (isLimCone XT1 W XT)).
    { apply @equiv_isPullback_1.
      exact pb.
    }
    specialize (XR XTT c).    
    intros S h k H.
    specialize (XR S).
    simpl in XR.
    transparent assert (HC
      :  (cone (@colimits.diagram_pointwise C^op HSET 
                    pullback_graph (pullback_diagram (preShv C) f g) c) S)).
    { use make_cone.
      apply three_rec_dep; cbn.
      - apply h.
      - simpl. apply (h ;; (pr1 f c)).
      - apply k.
      - use three_rec_dep; use three_rec_dep.
        + exact (empty_rect _ ).
        + intro. apply idpath.
        + exact (empty_rect _ ).
        + exact (empty_rect _ ).
        + exact (empty_rect _ ).
        + exact (empty_rect _ ).
        + exact (empty_rect _ ).
        + intro; apply (!H).
        + exact (empty_rect _ ).
    }
    specialize (XR HC).
    use tpair.
  - exists (pr1 (iscontrpr1 XR)).
    split.
    + apply (pr2 (pr1 XR) One).
    + apply (pr2 (pr1 XR) Three).
  - intro t.
    apply subtypePath.
    + intro. apply isapropdirprod; apply homset_property.
    + simpl.
      apply path_to_ctr.
      destruct t as [t [H1 H2]].
      use three_rec_dep.
      * apply H1.
      * destruct H1.
        apply idpath.
      * apply H2.
Qed.


End Pullbacks_hSet.

(** ** Uniqueness of pullbacks *)

Definition isaprop_Pullback (C : category) (H : is_univalent C)
           (a b c : C) (f : b --> a) (g : c --> a)
: isaprop (Pullback f g).
Proof.
  unfold Pullback.
  apply invproofirrelevance.
  unfold Pullback.
  intros Pb Pb'.
  apply subtypePath.
  - intro; apply isofhleveltotal2.
    + apply homset_property.
    + intros; apply isaprop_isPullback.
  - apply (total2_paths_f (isotoid _ H (iso_from_Pullback_to_Pullback _ _))).
    rewrite transportf_dirprod, transportf_isotoid.
    rewrite inv_from_iso_iso_from_Pullback.
    rewrite transportf_isotoid.
    rewrite inv_from_iso_iso_from_Pullback.
    destruct Pb as [Cone bla];
    destruct Pb' as [Cone' bla'];
    simpl in *.
    destruct Cone as [p [h k]];
    destruct Cone' as [p' [h' k']];
    simpl in *. 
    unfold from_Pullback_to_Pullback;
    rewrite PullbackArrow_PullbackPr2, PullbackArrow_PullbackPr1.
    apply idpath.
Qed.

(* TODO: check for results of the following section upstream *)
Section Pullback_Unique_Up_To_Iso.

(*   a'   b'
      f  /h
   a----b  b'
   |    |
 g |    | k
   |    |
   c----d
     j 

   and pb square a' b' c d, and h iso
    
   task: construct iso from a to a'

 *)
  
  Variable CC : category.
  Variables A B C D A' B' : CC.
  Variables (f : A --> B) (g : A --> C) (k : B --> D) (j : C --> D)
            (H : f ;; k = g ;; j) (pb : isPullback H).
  Variables (f' : A' --> B') (g' : A' --> C) (r : B' --> D) (h : iso B B').
  Variable (H' : f' ;; r = g' ;; j).
  Variable (pb' : isPullback H').
  Variable (T : h ;; r = k).

  Definition map_to_2nd_pb : A --> A'.
  Proof.
    use (map_into_Pb pb').
    - exact (f ;; h).
    - exact g.
    - eapply pathscomp0. 2: { apply H. }
      eapply pathscomp0. apply (!assoc _ _ _ ).
      apply maponpaths. apply T.
  Defined.

  Definition map_to_1st_pb : A' --> A.
  Proof.
    use (map_into_Pb pb).
    - exact (f';; inv_from_iso h).
    - exact g'.
    - eapply pathscomp0; [| apply H'].
      eapply pathscomp0; [ apply (!assoc _ _ _ ) |].
      apply maponpaths. apply iso_inv_on_right.
      apply (!T).
  Defined.

  Lemma inv1 : map_to_2nd_pb ;; map_to_1st_pb = identity _ .
  Proof.
    apply (map_into_Pb_unique pb).
    - rewrite id_left.
      rewrite <- assoc.
      unfold map_to_1st_pb.
      rewrite Pb_map_commutes_1.
      rewrite assoc.
      apply pathsinv0.
      apply iso_inv_on_left.
      unfold map_to_2nd_pb.
      use Pb_map_commutes_1.
    - rewrite id_left.
      rewrite <- assoc.
      unfold map_to_1st_pb.
      rewrite Pb_map_commutes_2.
      unfold map_to_2nd_pb.
      apply Pb_map_commutes_2.
  Qed.

  Lemma inv2 : map_to_1st_pb ;; map_to_2nd_pb = identity _ .
  Proof.
    apply (map_into_Pb_unique pb').
    - rewrite id_left.
      rewrite <- assoc.
      unfold map_to_2nd_pb.
      rewrite Pb_map_commutes_1.
      rewrite assoc.
      unfold map_to_1st_pb.
      rewrite Pb_map_commutes_1.
      rewrite <- assoc.
      rewrite iso_after_iso_inv.
      apply id_right.
    - rewrite id_left.
      rewrite <- assoc.
      unfold map_to_2nd_pb.
      rewrite Pb_map_commutes_2.
      unfold map_to_1st_pb.
      apply Pb_map_commutes_2.
  Qed.

  Definition iso_to_second_pb : iso A A'.
  Proof.
    exists map_to_2nd_pb.
    simple refine (is_iso_qinv _ map_to_1st_pb _ ).
    split.
    - apply inv1.
    - apply inv2.
  Defined.

End Pullback_Unique_Up_To_Iso.

(** ** Displayed categories *)

Definition isaprop_is_cartesian_disp_functor
    {C C' : category} {F : functor C C'}
    {D : disp_cat C} {D' : disp_cat C'} {FF : disp_functor F D D'}
  : isaprop (is_cartesian_disp_functor FF).
Proof.
  do 7 (apply impred; intro).
  apply isaprop_is_cartesian.
Qed.

(** ** Comprehension categories *)

Definition comprehension_cat
  := ∑ (C : category), (comprehension_cat_structure C).

Coercion category_of_comprehension_cat (C : comprehension_cat) := pr1 C.
Coercion structure_of_comprehension_cat (C : comprehension_cat) := pr2 C.


(** * Unorganised lemmas *)

(* Lemmas that probably belong in one of the sections above, but haven’t been sorted into them yet.  Mainly a temporary holding pen for lemmas being upstreamed from other files. TODO: empty this bin frequently (but keep it here for re-use). *) 
Section Unorganised.

Lemma transportf_pshf {C : category}
    {P P' : preShv C} (e : P = P')
    {c : C} (x : (P : functor _ _) c : hSet)
  : transportf (fun Q : preShv C => (Q : functor _ _) c : hSet) e x
  = ((idtoiso e : _ --> _) : nat_trans _ _) c x.
Proof.
  destruct e; apply idpath.
Qed.

Lemma transportf_isotoid_pshf {C : category}
    {P P' : preShv C} (i : iso P P')
    {c : C} (x : (P : functor _ _) c : hSet)
  : transportf (fun Q : preShv C => (Q : functor _ _) c : hSet)
      (isotoid _ (univalent_category_is_univalent (preShv C)) i) x
  = ((i : _ --> _) : nat_trans _ _) c x.
Proof.
  etrans. apply transportf_pshf.
  refine (toforallpaths _ x).
  refine (toforallpaths _ c).
  apply maponpaths, maponpaths, idtoiso_isotoid.
Qed.

Lemma transportf_dirprod_path' {C : category}
           {a b c d : C}
           (e : (a, b) = (c, d))
           (f : C ⟦ a, b ⟧)
  : transportf (λ x : C × C, C ⟦ dirprod_pr1 x, dirprod_pr2 x ⟧) e f
    = idtoiso (! pr1 (WeakEquivalences.pathsdirprodweq e)) ;; f
      ;; idtoiso (dirprod_pr2 (WeakEquivalences.pathsdirprodweq e)).
Proof.
  use (paths_rect (C × C) (a, b)
    (λ xy exy, transportf (λ uv, C ⟦ pr1 uv, pr2 uv ⟧) exy f
     = idtoiso (! pr1 (WeakEquivalences.pathsdirprodweq exy)) ;; f
       ;; idtoiso (pr2 (WeakEquivalences.pathsdirprodweq exy))) _ _ e).
  simpl.
  etrans.
  apply (@idpath_transportf _ (λ xy, C ⟦ pr1 xy, pr2 xy ⟧ ) (a, b)).
  apply pathsinv0.
  etrans. apply assoc'.
  etrans. apply id_left.
  apply id_right.
Defined.

Definition arrow_category_ids {C : category}
           (abf cdg : arrow_category C)
  : UU
  := ∑ (hk : (pr1 (pr1 abf) = pr1 (pr1 cdg))
               × (dirprod_pr2 (pr1 abf) = dirprod_pr2 (pr1 cdg))),
    pr2 abf ;; idtoiso (dirprod_pr2 hk) = idtoiso (pr1 hk) ;; pr2 cdg.

Lemma arrow_category_id_to_ids {C : category}
           {abf cdg : arrow_category C}
  : (abf = cdg) ≃ arrow_category_ids abf cdg.
Proof.
  eapply weqcomp. apply total2_paths_equiv.
  use (PartA.weqtotal2 WeakEquivalences.pathsdirprodweq).
  intros e.
  eapply weqcomp. apply invweq.
  apply (weqpathscomp0l _ (transportf_dirprod_path' _ _)).
  use weqimplimpl.
  - intros p.
    etrans. apply pathsinv0, id_left.
    etrans. apply maponpaths_2, pathsinv0.
    apply (iso_inv_after_iso (idtoiso (pr1 (pathsdirprodweq e)))).
    etrans. apply assoc'.
    apply maponpaths.
    etrans. apply maponpaths_2, pathsinv0.
    apply (maponpaths pr1 (idtoiso_inv _ _ _ _)).
    etrans. apply assoc.
    apply p.
  - intros p.
    apply pathsinv0.
    etrans. apply pathsinv0, id_left.
    etrans. apply maponpaths_2, pathsinv0.
    apply (iso_after_iso_inv (idtoiso (pr1 (pathsdirprodweq e)))).
    etrans. apply assoc'.
    etrans. apply maponpaths_2, pathsinv0.
    apply (maponpaths pr1 (idtoiso_inv _ _ _ _)).
    apply pathsinv0.
    etrans. apply assoc'.
    apply maponpaths.
    apply p.
  - apply homset_property.
  - apply homset_property.
Defined.

Definition arrow_category_is_iso {C : category}
           {abf cdg : arrow_category C}
           (a_to_c : C ⟦ pr1 (pr1 abf), pr1 (pr1 cdg) ⟧)
           (b_to_d : C ⟦ dirprod_pr2 (pr1 abf), dirprod_pr2 (pr1 cdg) ⟧)
  : UU
  := is_iso b_to_d ×
     is_iso a_to_c ×
     (pr2 abf ;; b_to_d = a_to_c ;; pr2 cdg).

Lemma isaprop_arrow_category_is_iso {C : category}
           {abf cdg : arrow_category C}
           (a_to_c : C ⟦ pr1 (pr1 abf), pr1 (pr1 cdg) ⟧)
           (b_to_d : C ⟦ dirprod_pr2 (pr1 abf), dirprod_pr2 (pr1 cdg) ⟧)
  : isaprop (arrow_category_is_iso a_to_c b_to_d).
Proof.
  use isapropdirprod.
  - apply isaprop_is_iso.
  - use isapropdirprod.
    + apply isaprop_is_iso.
    + apply homset_property.
Defined.

Definition arrow_category_is_iso_to_is_iso {C : category}
           {abf cdg : arrow_category C}
           (a_to_c : C ⟦ pr1 (pr1 abf), pr1 (pr1 cdg) ⟧)
           (b_to_d : C ⟦ dirprod_pr2 (pr1 abf), dirprod_pr2 (pr1 cdg) ⟧)
  : arrow_category_is_iso a_to_c b_to_d
    → ∑ (p : pr2 abf ;; b_to_d = a_to_c ;; pr2 cdg)
    , is_iso (((a_to_c, b_to_d),,p) : arrow_category C ⟦ abf, cdg ⟧).
Proof.
  intros h.
  set (is_iso_a_to_c := pr1 (dirprod_pr2 h)).
  set (is_iso_b_to_d := pr1 h).
  set (iso_a_to_c := (a_to_c,,is_iso_a_to_c)).
  set (iso_b_to_d := (b_to_d,,is_iso_b_to_d)).
  set (comm_square := dirprod_pr2 (dirprod_pr2 h)).
  use tpair.
  - apply comm_square.
  - use is_iso_from_is_z_iso.
    unfold is_z_isomorphism.
    use tpair.
    + use tpair.
      * use make_dirprod.
        -- apply (inv_from_iso iso_a_to_c).
        -- apply (inv_from_iso iso_b_to_d).
      * simpl.
        apply pathsinv0.
        etrans. apply pathsinv0, id_right.
        etrans. apply maponpaths, pathsinv0, (iso_inv_after_iso iso_b_to_d).
        etrans. apply assoc'.
        etrans. apply maponpaths, assoc.
        etrans. apply maponpaths, maponpaths_2, comm_square.
        etrans. apply assoc.
        etrans. apply maponpaths_2, assoc.
        etrans. apply maponpaths_2, maponpaths_2, iso_after_iso_inv.
        etrans. apply maponpaths_2, id_left.
        apply idpath.
    + use make_dirprod.
      * use total2_paths_f.
        -- use dirprod_paths.
           ++ apply (iso_inv_after_iso iso_a_to_c).
           ++ apply (iso_inv_after_iso iso_b_to_d).
        -- apply homset_property.
      * use total2_paths_f.
        -- use dirprod_paths.
           ++ apply (iso_after_iso_inv iso_a_to_c).
           ++ apply (iso_after_iso_inv iso_b_to_d).
        -- apply homset_property.
Defined.

Definition is_iso_to_arrow_category_is_iso {C : category}
           {abf cdg : arrow_category C}
           (a_to_c : C ⟦ pr1 (pr1 abf), pr1 (pr1 cdg) ⟧)
           (b_to_d : C ⟦ dirprod_pr2 (pr1 abf), dirprod_pr2 (pr1 cdg) ⟧)
  : (∑ (p : pr2 abf ;; b_to_d = a_to_c ;; pr2 cdg)
    , is_iso (((a_to_c, b_to_d),,p) : arrow_category C ⟦ abf, cdg ⟧))
    → arrow_category_is_iso a_to_c b_to_d.
Proof.
  intros hp.
  set (abf_to_cdg := ((a_to_c, b_to_d),,pr1 hp) : arrow_category C ⟦ _ , _ ⟧).
  set (h := pr2 hp : is_iso abf_to_cdg).
  set (c_to_a := pr1 (pr1 (inv_from_iso (abf_to_cdg,,h)))).
  set (d_to_b := dirprod_pr2 (pr1 (inv_from_iso (abf_to_cdg,,h)))).

  use make_dirprod.
  - use is_iso_from_is_z_iso.
    use tpair. { apply d_to_b. }
    use make_dirprod.
    * apply (maponpaths (λ k, dirprod_pr2 (pr1 k)) (iso_inv_after_iso (_,,h))).
    * apply (maponpaths (λ k, dirprod_pr2 (pr1 k)) (iso_after_iso_inv (_,,h))).
  - use make_dirprod.
    + use is_iso_from_is_z_iso.
      use tpair. { apply c_to_a. }
      use make_dirprod.
      * apply (maponpaths (λ k, pr1 (pr1 k)) (iso_inv_after_iso (_,,h))).
      * apply (maponpaths (λ k, pr1 (pr1 k)) (iso_after_iso_inv (_,,h))).
    + apply (pr2 abf_to_cdg).
Defined.

Definition arrow_category_weq_is_iso {C : category}
           {abf cdg : arrow_category C}
           (a_to_c : C ⟦ pr1 (pr1 abf), pr1 (pr1 cdg) ⟧)
           (b_to_d : C ⟦ dirprod_pr2 (pr1 abf), dirprod_pr2 (pr1 cdg) ⟧)
  : arrow_category_is_iso a_to_c b_to_d
                          ≃
    ∑ (p : pr2 abf ;; b_to_d = a_to_c ;; pr2 cdg)
    , is_iso (((a_to_c, b_to_d),,p) : arrow_category C ⟦ abf, cdg ⟧).
Proof.
  use weq_iso.
  - apply arrow_category_is_iso_to_is_iso.
  - apply is_iso_to_arrow_category_is_iso.
  - intros h. apply isaprop_arrow_category_is_iso.
  - intros h.
    use total2_paths_f.
    + apply homset_property.
    + apply isaprop_is_iso.
Defined.

Definition arrow_category_id_weq_iso {C : category}
           (C_univ : is_univalent C)
           (abf cdg : arrow_category C)
  : (abf = cdg) ≃ iso abf cdg.
Proof.
  eapply weqcomp.
  apply arrow_category_id_to_ids.

  set (a := pr1 (pr1 abf)).
  set (b := dirprod_pr2 (pr1 abf)).
  set (f := pr2 abf).
  set (c := pr1 (pr1 cdg)).
  set (d := dirprod_pr2 (pr1 cdg)).
  set (g := pr2 cdg).

  assert (weq1 :
  (∑ hk : a = c × b = d,
    pr2 abf;; idtoiso (dirprod_pr2 hk) = idtoiso (pr1 hk) ;; pr2 cdg)
    ≃
  (∑ hk : iso a c × iso b d,
   pr2 abf;; dirprod_pr2 hk = pr1 hk ;; pr2 cdg)).
  eapply weqcomp. apply weqtotal2asstor.
  apply invweq.
  eapply weqcomp. apply weqtotal2asstor.
  apply invweq.
  use PartA.weqtotal2.
  - apply (make_weq _ (C_univ a c)).
  - intros id_ac.
    use PartA.weqtotal2.
    + apply (make_weq _ (C_univ b d)).
    + intros id_bd. apply idweq.

  - eapply weqcomp. apply weq1.
    eapply weqcomp. apply weqtotal2asstor.
    eapply weqcomp. apply weqtotal2asstor.
    apply invweq.
    eapply weqcomp. apply weqtotal2asstor.
    eapply weqcomp. apply weqtotal2asstor.
    use PartA.weqtotal2.
    + apply idweq.
    + intros a_to_c.
      apply invweq.
      eapply weqcomp. apply WeakEquivalences.weqtotal2comm.
      eapply weqcomp. apply weqtotal2asstor.
      use PartA.weqtotal2.
      * apply idweq.
      * intros b_to_d. simpl.
        apply arrow_category_weq_is_iso.
Defined. 

Definition arrow_category_mor_eq {C : category}
           {abf cdg : arrow_category C}
           (f g : arrow_category C ⟦ abf, cdg ⟧)
  : pr1 (pr1 f) = pr1 (pr1 g)
    → dirprod_pr2 (pr1 f) = dirprod_pr2 (pr1 g)
    → f = g.
Proof.
  intros p1 p2.
  use total2_paths_f.
  - use dirprod_paths.
    + apply p1.
    + apply p2.
  - apply homset_property.
Defined.

Definition arrow_category_is_univalent {C : category}
           (C_univ : is_univalent C)
  : is_univalent (arrow_category C).
Proof.
  intros abf cdg.
  use isweqhomot.
  + apply arrow_category_id_weq_iso.
    apply C_univ.
  + intros p. induction p.
      apply eq_iso. 
    apply arrow_category_mor_eq.
    * apply idpath.
      * apply idpath.
  + apply (pr2 (arrow_category_id_weq_iso C_univ _ _)).
Defined.

Definition catiso_is_path_cat (C D : category)
  : (C = D) ≃ catiso C D.
Proof.
  eapply weqcomp.
  - eapply PartA.path_sigma_hprop.
    apply isaprop_has_homsets.
  - apply catiso_is_path_precat.
    apply D.
Defined.


Definition catiso_univalent (C : category) (D : category)
  : catiso D C → is_univalent C → is_univalent D.
Proof.
  intros i C_univ.
  set (D_eq_C := invweq (catiso_is_path_cat _ _ ) i).
  use (transportb _ D_eq_C).
  apply C_univ.
Defined.

End Unorganised.

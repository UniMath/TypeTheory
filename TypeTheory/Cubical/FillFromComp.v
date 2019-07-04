(**

This file formalizes one of the key theorems in the cubical set model
of univalent type theory from:

  Cubical Type Theory: a constructive interpretation of the univalence axiom
  Cyril Cohen, Thierry Coquand, Simon Huber, Anders Mörtberg
  https://arxiv.org/abs/1611.02108

This theorem says that uniform Kan filling structures ("from 0 to 1")
of CCHM can be reduced to uniform Kan composition structures ("from 0
to 1"). This file formalizes this in a quite general setting of a
category C with:

- Binary coproducts

- A subobject FF of the subobject classifier Ω in PreShv(C)

- A cylinder functor F : C -> C (representing abstraction over i : II)
  with natural transformations

  <<
    p : F ⟹ Id
    e₀ e₁ : Id ⟹ F
  >>

  satisfying:

  <<
    e₀ p = Id
    e₁ p = Id
  >>

  So that p represents the degeneracy map and e₀, e₁ are face
  maps. Furthermore, we need to assume that the naturality square for e₀
  are pullbacks (i.e. that e₀ is Cartesian).

- A connection

  <<
    m : F ∙ F ⟹ F
  >>

  satisfying

  <<
     m (e₁ F) = Id
     p m = p p
  >>

  This corresponds to the equations:

  <<
    1 ∧ i = i
    i ∧ i = i
  >>

- Natural transformations

  <<
    δ₀ : yon (I +) --> FF
  >>

  which classifies e₀ lifted to PreShv(C). Which furthermore satisfies:

  <<
    m δ₀ = (p δ₀) ∨ δ₀
  >>

  This corresponds to the equation:

  <<
    (i ∧ j) = 0   iff   (i = 0) ∨ (j = 0)
  >>


Written by: Anders Mörtberg, 2017-2018

*)

Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.Notations.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Export UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.LatticeObject.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.ElementsOp.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.yoneda.

Require Import TypeTheory.Instances.Presheaves.
Require Import TypeTheory.Auxiliary.Auxiliary.

Local Open Scope cat.

Ltac pathvia b := (eapply (@pathscomp0 _ _ b _ )).

Arguments nat_trans_ax {_ _ _ _} _ {_ _} _.
Arguments nat_trans_comp {_ _ _ _ _} _ _.
Arguments isPullback {_ _ _ _ _ _ _ _ _} _.

Section cubical.

Context {C : precategory} (hsC : has_homsets C) (BPC : BinProducts C).

(* Setup notations *)
Local Notation "Γ ⊢" := (PreShv (∫ Γ)) (at level 50).
Local Notation "Γ ⊢ A" := (@TermIn _ Γ A) (at level 50).
Local Notation "A ⦃ s ⦄" := (subst_type hsC A s) (at level 40, format "A ⦃ s ⦄").
Local Notation "Γ ⋆ A" := (@ctx_ext _ Γ A) (at level 30).
Local Notation "c '⊗' d" :=
  (BinProductObject _ (@BinProducts_PreShv C c d)) : cat.
Local Notation "f '××' g" :=
  (BinProductOfArrows _ (BinProducts_PreShv _ _) (BinProducts_PreShv _ _) f g)
  (at level 90) : cat.
Local Notation "1" := Terminal_PreShv.
Local Notation "'Id'" := (functor_identity _).

Definition binprod_delta x : x --> x ⊗ x :=
  BinProductArrow _ _ (identity x) (identity x).
Local Notation "'δ'" := (binprod_delta _).

Let Ω : bounded_latticeob BinProducts_PreShv 1 Ω_PreShv :=
  @Ω_PreShv_bounded_lattice C.

(* Assume that we have a sublattice of Ω *)
Context (FF : PreShv C) (i : FF --> Ω_PreShv) (Hi : isMonic i).
Context (meet_FF : FF ⊗ FF --> FF) (join_FF : FF ⊗ FF --> FF).
Context (bot_FF : 1 --> FF) (top_FF : 1 --> FF).
Context (Hmeet_FF : meet_FF · i = (i ×× i) · meet_mor Ω).
Context (Hjoin_FF : join_FF · i = (i ×× i) · join_mor Ω).
Context (Hbot_FF : bot_FF · i = bot_mor Ω).
Context (Htop_FF : top_FF · i = top_mor Ω).

(* Maybe package this up? *)
Definition FF_lattice : bounded_latticeob BinProducts_PreShv 1 FF :=
  sub_bounded_latticeob BinProducts_PreShv Terminal_PreShv Hi Ω
                        Hmeet_FF Hjoin_FF Hbot_FF Htop_FF.

(* Extract the top and bottom elements of the lattice (as sets)*)
Definition FF1 {I} : pr1 FF I : hSet := pr1 top_FF I tt.
Definition FF0 {I} : pr1 FF I : hSet := pr1 bot_FF I tt.

(* The map that constantly returns FF1 *)
Definition true : 1 --> FF.
Proof.
use make_nat_trans.
+ intros I _.
  exact (@FF1 I).
+ intros I J f; cbn.
  apply funextsec; intros _.
  apply (eqtohomot (nat_trans_ax top_FF f) tt).
Defined.

(* The meet and join operations *)
Definition meet_mor {Γ : PreShv C} (φ ψ : Γ --> FF) : Γ --> FF :=
  δ · (φ ×× ψ) · meet_FF.

Definition join_mor {Γ : PreShv C} (φ ψ : Γ --> FF) : Γ --> FF :=
  δ · (φ ×× ψ) · join_FF.

Local Notation "φ ∧ ψ" := (meet_mor φ ψ) (at level 80, right associativity).
Local Notation "φ ∨ ψ" := (join_mor φ ψ) (at level 85, right associativity).

Lemma comp_join {Γ Δ : PreShv C} (f : Γ --> Δ) (g h : Δ --> FF) :
  f · (g ∨ h) = (f · g ∨ f · h).
Proof.
apply (nat_trans_eq has_homsets_HSET); intro I.
now apply funextsec.
Qed.

(* Some pointwise equations for the face lattice. TODO: better notations *)
Lemma meet_FF1 (I : C) (φ : pr1 FF I : hSet) : pr1 meet_FF I (FF1,,φ) = φ.
Proof.
exact (eqtohomot (nat_trans_eq_pointwise (islunit_meet_mor_top_mor _ _ FF_lattice) I) φ).
Qed.

Lemma join_absorb_meet_FF (I : C) (φ ψ : pr1 FF I : hSet) :
  pr1 join_FF I (φ,,pr1 meet_FF I (φ,,ψ)) = φ.
Proof.
exact (eqtohomot (nat_trans_eq_pointwise (join_mor_absorb_meet_mor _ FF_lattice) I) (φ,,ψ)).
Qed.

Lemma join_FF_assoc (I : C) (x y z : pr1 FF I : hSet) :
  pr1 join_FF I (pr1 join_FF I (x,,y),, z) = pr1 join_FF I (x,,pr1 join_FF I (y,,z)).
Proof.
exact (eqtohomot (nat_trans_eq_pointwise (isassoc_join_mor _ FF_lattice) I) ((x,,y),,z)).
Qed.

Lemma join_FF1 (I : C) (x : pr1 FF I : hSet) :
  pr1 join_FF I (FF1,,x) = FF1.
Proof.
now rewrite <- (meet_FF1 _ x), join_absorb_meet_FF.
Qed.

(* Context restriction: Γ, φ |- *)
Definition ctx_restrict (Γ : PreShv C) (φ : Γ --> FF) : PreShv C.
Proof.
use make_functor.
- use tpair.
  + simpl; intros I.
    exists (∑ ρ : pr1 ((pr1 Γ) I), pr1 φ I ρ = FF1).
    abstract (apply isaset_total2; [ apply setproperty
                                   | intros ρ; apply isasetaprop, setproperty ]).
  + simpl; intros I J f ρ.
    exists (# (pr1 Γ) f (pr1 ρ)).
    abstract (
        etrans; [apply (eqtohomot (nat_trans_ax φ f) (pr1 ρ))|]; cbn;
        etrans; [apply maponpaths, (pr2 ρ)|];
        now apply (!eqtohomot (nat_trans_ax top_FF f) tt)).
- split.
  + intros I; apply funextsec; simpl; intro ρ.
    apply subtypePath; [ intros x; apply setproperty |]; simpl.
    now rewrite (functor_id Γ).
  + intros I J K f g; apply funextsec; simpl; intro ρ.
    apply subtypePath; [ intros x; apply setproperty |]; simpl.
    now rewrite (functor_comp Γ).
Defined.

Local Notation "Γ , φ" := (ctx_restrict Γ φ) (at level 30, format "Γ , φ").

(* Canonical inclusion *)
Definition ι {Γ : PreShv C} {φ : Γ --> FF} : Γ,φ --> Γ.
Proof.
use make_nat_trans.
- simpl; intros I; cbn; apply pr1.
- intros I J f; apply idpath.
Defined.

Lemma isMonic_ι (Γ : PreShv C) (φ : Γ --> FF) : isMonic (@ι _ φ).
Proof.
intros Δ σ1 σ2 H.
apply (nat_trans_eq has_homsets_HSET); intro I.
apply funextsec; intro ρ.
apply subtypePath; [ intros x; apply setproperty |]; simpl.
exact (eqtohomot (nat_trans_eq_pointwise H I) ρ).
Qed.

Definition join_subst {Γ : PreShv C} (φ ψ : Γ --> FF) : Γ,φ --> Γ,(φ ∨ ψ).
Proof.
use make_nat_trans.
- intros I ρ.
  exists (pr1 ρ).
  abstract (cbn; etrans; [apply maponpaths, (pathsdirprod (pr2 ρ) (idpath _))|];
            apply join_FF1).
- intros I J f.
  apply funextsec; intro ρ.
  now apply subtypePath; [intros x; apply setproperty|].
Defined.

Definition subst_restriction {Γ Δ : PreShv C} (σ : Δ --> Γ) (φ : Γ --> FF) :
  Δ,(σ · φ) --> Γ,φ.
Proof.
use make_nat_trans.
+ intros I u.
  apply (pr1 σ I (pr1 u),,pr2 u).
+ abstract (intros I J f; apply funextsec; intro ρ;
  apply subtypePath; [intros x; apply setproperty|]; simpl;
  apply (eqtohomot (nat_trans_ax σ f) (pr1 ρ))).
Defined.


(*************************)
(* Cylinder functor on C *)
(*************************)

Context (F : C ⟶ C).

Notation "I +" := (F I) (at level 20).

(* We assume a cylinder functor F *)
Context (p_F : F ⟹ Id) (e₀ e₁ : Id ⟹ F).
Context (Hpe₀ : nat_trans_comp e₀ p_F = nat_trans_id Id).
Context (Hpe₁ : nat_trans_comp e₁ p_F = nat_trans_id Id).

(* We further assume that the naturality squares for e₀ are pullbacks *)
Context {e₀_pb : ∏ I J (f : J --> I), isPullback (nat_trans_ax e₀ f)}.

(* We could also assume that the naturality squares of p_F are
   pullbacks. This should be a consequence if there is an interval
   presheaf in PreShv(C) *)
Lemma isPullback_pF_e₀ I J (f : J --> I) :
  isPullback (nat_trans_ax p_F f) → isPullback (nat_trans_ax e₀ f).
Proof.
intros H.
apply (isPullback_two_pullback hsC _ _ _ _ _ _ H).
intros K g h Hgh.
use (unique_exists h); simpl in *.
- rewrite <- Hgh.
  set (HI := nat_trans_eq_pointwise Hpe₀ I).
  set (HJ := nat_trans_eq_pointwise Hpe₀ J); cbn in HI, HJ.
  now rewrite HI, HJ, !id_right.
- now intros HH; apply isapropdirprod; apply hsC.
- intros h' [H1 H2].
  rewrite <- H2.
  set (HH := nat_trans_eq_pointwise Hpe₀ J); cbn in HH.
  now rewrite HH, id_right.
Qed.

(* We also assume a conjunction map m : F^2 -> F satisfying: *)
(* m e0 = e0 p *)
(* m (e0+) = e0 p *)
(* m e1 = 1 *)
(* m (e1+) = 1 *)
(* p m = p p *)

(* Some of these equations are not necessary so they are commented *)
Context (m : F ∙ F ⟹ F).
(* Context (He₀m : nat_trans_comp (post_whisker e₀ F) m = nat_trans_comp p_F e₀). *)
(* Context (He₀m' : nat_trans_comp (pre_whisker F e₀) m = nat_trans_comp p_F e₀). *)
(* Context (He₁m : nat_trans_comp (post_whisker e₁ F) m = nat_trans_id F). *)
Context (He₁m' : nat_trans_comp (pre_whisker F e₁) m = nat_trans_id F).
Context (Hmp : nat_trans_comp m p_F = nat_trans_comp (pre_whisker F p_F) p_F).

(* Instantiate the above axioms and check that they make sense *)
Goal ∏ (I : C), UU.
intros.
(* generalize (nat_trans_eq_pointwise He₁m I). *)
generalize (nat_trans_eq_pointwise He₁m' I).
(* generalize (nat_trans_eq_pointwise He₀m I). *)
(* generalize (nat_trans_eq_pointwise He₀m' I). *)
generalize (nat_trans_eq_pointwise Hmp I).
cbn.
Abort.

Lemma isMonic_e₀ I : isMonic (e₀ I).
Proof.
intros J f g H.
set (H1 := nat_trans_ax e₀ f).
set (H2 := nat_trans_ax p_F f).
set (H3 := nat_trans_eq_pointwise Hpe₀ I).
set (H4 := nat_trans_eq_pointwise Hpe₀ J).
cbn in *.
rewrite H1 in H.
generalize (cancel_postcomposition _ _ (p_F I) H); cbn.
now rewrite <-!assoc, H2, H3, assoc, H4, id_left, id_right.
Qed.

Lemma isMonic_e₁ I : isMonic (e₁ I).
Proof.
intros J f g H.
set (H1 := nat_trans_ax e₁ f).
set (H2 := nat_trans_ax p_F f).
set (H3 := nat_trans_eq_pointwise Hpe₁ I).
set (H4 := nat_trans_eq_pointwise Hpe₁ J).
cbn in *.
rewrite H1 in H.
generalize (cancel_postcomposition _ _ (p_F I) H); cbn.
now rewrite <-!assoc, H2, H3, assoc, H4, id_left, id_right.
Qed.

(* We can lift the above operations to presheaves using yoneda *)
Let yon := yoneda_functor_data C hsC.

Definition p_PreShv (I : C) : yon (I+) --> yon I := # yon (p_F I).

(* e₀ defines a natural map from yon(I) to yon(I+) *)
Definition e₀_PreShv (I : C) : yon I --> yon (I +).
Proof.
use make_nat_trans.
+ intros J f.
  exact (f · e₀ I).
+ intros J K f.
  now apply funextsec; intro x; cbn; rewrite assoc.
Defined.

Definition e₁_PreShv (I : C) : yon I --> yon (I +).
Proof.
use make_nat_trans.
+ intros J f.
  exact (f · e₁ I).
+ intros J K f.
  now apply funextsec; intro x; cbn; rewrite assoc.
Defined.

Definition m_PreShv (I : C) : yon ((I +) +) --> yon (I+).
Proof.
use make_nat_trans.
+ intros J f.
  exact (f · m I).
+ intros J K f.
  now apply funextsec; intro x; cbn; rewrite assoc.
Defined.

Lemma isMonic_e₀_PreShv I : isMonic (e₀_PreShv I).
Proof.
intros Γ σ τ H.
apply (nat_trans_eq has_homsets_HSET); intros J; apply funextsec; intro ρ.
generalize (eqtohomot (nat_trans_eq_pointwise H J) ρ).
now apply isMonic_e₀.
Qed.

Lemma isMonic_e₁_PreShv I : isMonic (e₁_PreShv I).
Proof.
intros Γ σ τ H.
apply (nat_trans_eq has_homsets_HSET); intros J; apply funextsec; intro ρ.
generalize (eqtohomot (nat_trans_eq_pointwise H J) ρ).
now apply isMonic_e₁.
Qed.

Lemma e₀_p_PreShv I : e₀_PreShv I · p_PreShv I = identity (yon I).
Proof.
apply (nat_trans_eq has_homsets_HSET); intro J.
apply funextsec; intro ρ; cbn; unfold yoneda_morphisms_data.
rewrite <-assoc.
set (H := nat_trans_eq_pointwise Hpe₀ I); cbn in H.
now rewrite H, id_right.
Qed.

Lemma e₁_p_PreShv I : e₁_PreShv I · p_PreShv I = identity (yon I).
Proof.
apply (nat_trans_eq has_homsets_HSET); intro J.
apply funextsec; intro ρ; cbn; unfold yoneda_morphisms_data.
rewrite <-assoc.
set (H := nat_trans_eq_pointwise Hpe₁ I); cbn in H.
now rewrite H, id_right.
Qed.

Lemma e₁_m_PreShv I : e₁_PreShv (I +) · m_PreShv I = identity (yon (I+)).
Proof.
apply (nat_trans_eq has_homsets_HSET); intro J.
apply funextsec; intro ρ; cbn; unfold yoneda_morphisms_data.
rewrite <-assoc.
etrans; [apply maponpaths, (nat_trans_eq_pointwise He₁m' I)|].
now apply id_right.
Qed.

Lemma m_p_PreShv I : m_PreShv I · p_PreShv I = p_PreShv (I+) · p_PreShv I.
Proof.
apply (nat_trans_eq has_homsets_HSET); intros J.
cbn; unfold yoneda_morphisms_data.
apply funextsec; intro ρ; cbn.
rewrite <-!assoc; apply maponpaths.
apply (nat_trans_eq_pointwise Hmp I).
Qed.

(* TODO: define the rest of the equations for m *)


(**************)
(* Open boxes *)
(**************)

(* Introduce δ₀ which classifies e₀_PreShv *)
Context (δ₀ : ∏ I, yon (I +) --> FF).
Context (Hδ₀ : ∏ I, e₀_PreShv I · δ₀ I = TerminalArrow _ _ · true).
Context (Hδ₀_pb : ∏ I, isPullback (Hδ₀ I)).
Context (Hδ₀_unique : ∏ (I : C) (d0 : yon (I+) --> FF)
                        (Hd0 : e₀_PreShv I · d0 = TerminalArrow _ _ · true),
                        isPullback Hd0 → d0 = δ₀ I).

(* TODO: generalize the rest so that it works in both directions *)

(* This axiom follows if we work with II. I think it is a bit stronger than
   necessary. How can we weaken it? Maybe using something along the lines of:
     box(phi) m  <=  box(box(phi))

This is like:
  (i ∧ j) = 0  iff   (i = 0) ∨ (j = 0)
*)
Context (Hmδ₀ : ∏ I, m_PreShv I · δ₀ I = (p_PreShv (I +) · δ₀ I ∨ δ₀ (I +))).

(* The box formula *)
Definition b {I : C} (φ : yon I --> FF) : yon (I +) --> FF :=
  (p_PreShv I · φ) ∨ (δ₀ I).

(* A box is a representable cube restricted by the box formula *)
Definition box (I : C) (φ : yon I --> FF) : PreShv C :=
  yon (I+), b φ.

(* This substitution is used for the box u below, hence the name *)
Definition u_subst {I : C} (φ : yon I --> FF) : yon I,φ --> box I φ.
Proof.
assert (σ1 : yon(I),φ --> yon(I), (e₁_PreShv I · (p_PreShv I · φ))).
{ use make_nat_trans.
  + intros J ρ.
    exists (pr1 ρ).
    abstract (rewrite <- (pr2 ρ); cbn; unfold yoneda_morphisms_data;
    apply maponpaths; rewrite <-assoc;
    etrans; [apply maponpaths, (nat_trans_eq_pointwise Hpe₁ I)|];
    apply id_right).
  + abstract (intros J K f; apply funextsec; intro ρ;
    now apply subtypePath; [intro x; apply setproperty|]).
  (* This is a direct definition of this substitution,
     but reasoning about it is a nightmare: *)
  (* rewrite assoc, e₁_p_PreShv, id_left. *)
  (* apply identity. *)
}
set (σ2 := subst_restriction (e₁_PreShv I) (p_PreShv I · φ)).
exact (σ1 · σ2 · join_subst _ _).
Defined.

Definition u_subst_eq {Γ : PreShv C} {I : C} (ρ : yon (I+) --> Γ)
  (φ : yon I --> FF) : u_subst φ · ι · ρ = ι · e₁_PreShv I · ρ.
Proof.
now apply (nat_trans_eq (has_homsets_HSET)); intros J; apply funextsec.
Qed.

Lemma e₀_f {I J} (f : J --> I) : e₀_PreShv J · # yon (# F f) = # yon f · e₀_PreShv I.
Proof.
apply (nat_trans_eq has_homsets_HSET); intros K; apply funextsec; intro ρ.
cbn; unfold yoneda_morphisms_data.
rewrite <-!assoc.
now apply maponpaths, (!nat_trans_ax e₀ f).
Qed.

Lemma e₀_f_pb {I J} (f : J --> I) : isPullback (e₀_f f).
Proof.
apply Auxiliary.is_symmetric'_isPullback.
apply functor_category_has_homsets.
apply pb_if_pointwise_pb; intros K.
apply Auxiliary.isPullback_HSET; intros L f1 f2.
now apply e₀_pb.
Qed.

Lemma glued_square {I J} (f : J --> I) :
  e₀_PreShv J · (# yon (# F f) · δ₀ I) = # yon f · TerminalArrow _ (yon I) · true.
Proof.
exact (glueSquares (Hδ₀ I) (e₀_f f)).
Defined.

Lemma glued_square_pb {I J} (f : J --> I) : isPullback (glued_square f).
Proof.
apply isPullbackGluedSquare.
- apply functor_category_has_homsets.
- apply Hδ₀_pb.
- apply e₀_f_pb.
Qed.

Lemma plus_δ₀_prf {I J} (f : J --> I) :
  e₀_PreShv J · (# yon (# F f) · δ₀ I) = TerminalArrow _ (yon J) · true.
Proof.
etrans; [ apply glued_square|].
apply cancel_postcomposition, TerminalArrowUnique.
(* rewrite H, <- assoc, Hδ₀. *)
(* now apply (nat_trans_eq has_homsets_HSET); intros K; apply funextsec. *)
Qed.

Lemma plus_δ₀ I J (f : J --> I) : # yon (# F f) · δ₀ I = δ₀ J.
Proof.
use Hδ₀_unique.
- apply plus_δ₀_prf.
- use (isPullback_mor_paths _ _ _ _ _ (plus_δ₀_prf f) (glued_square_pb f)); trivial.
  + apply functor_category_has_homsets.
  + apply TerminalArrowUnique.
Qed.

Definition box_subst_prf {I J : C} (f : J --> I) (φ : yon I --> FF) (K : C)
  (ρ' : pr1 (box J (# yon f · φ)) K : hSet) :
  pr1 (# yon (# F f) · (p_PreShv I · φ ∨ δ₀ I)) K (pr1 ρ') = FF1.
Proof.
rewrite comp_join.
assert (h1 : # yon (# F f) · (p_PreShv I · φ) = p_PreShv J · (# yon f · φ)).
{ rewrite !assoc.
  apply cancel_postcomposition, (nat_trans_eq has_homsets_HSET); intros L.
  apply funextsec; intro ρ''; cbn; unfold yoneda_morphisms_data.
  rewrite <-!assoc; apply maponpaths, (nat_trans_ax p_F).
}
rewrite plus_δ₀, <- (pr2 ρ').
now unfold b; rewrite <- h1.
Qed.

Definition box_subst {I J : C} (f : J --> I) (φ : yon I --> FF) :
  box J (# yon f · φ) --> box I φ.
Proof.
set (ψ := (p_PreShv I · φ ∨ δ₀ I) : yon (I+) --> FF).
use (_ · subst_restriction (# yon (# F f)) ψ).
use make_nat_trans.
- intros K ρ'.
  exists (pr1 ρ').
  apply box_subst_prf.
- intros K L g.
  apply funextsec; intro ρ''.
  apply subtypePath; trivial; intros x; apply setproperty.
Defined.

Lemma b_yon {I J} (f : J --> I) (φ : yon I --> FF) :
  b (# yon f · φ) = # yon (# F f) · b φ.
Proof.
apply (nat_trans_eq has_homsets_HSET); intro K; apply funextsec; intro ρ; cbn.
apply maponpaths; simpl.
unfold yoneda_objects_ob, yoneda_morphisms_data, prodtofuntoprod; simpl.
apply pathsdirprod.
- apply maponpaths.
  rewrite <-!assoc.
  apply maponpaths, (!nat_trans_ax p_F f).
- apply (!eqtohomot (nat_trans_eq_pointwise (plus_δ₀ I J f) K) ρ).
Qed.

(* Multiplication rule for the box formula *)
Lemma m_b (I : C) (φ : yon I --> FF) : m_PreShv I · b φ = b (b φ).
Proof.
apply pathsinv0; unfold b.
rewrite !comp_join, assoc, <- m_p_PreShv, <- assoc, Hmδ₀.
apply (nat_trans_eq has_homsets_HSET); intros J.
cbn; unfold yoneda_morphisms_data, prodtofuntoprod.
apply funextsec; intro ρ; cbn.
now apply (join_FF_assoc J _ _ _).
Qed.

Lemma box_b_subst {X Y : PreShv C} (α : X --> Y) (I : C) (φ : yon I --> FF)
  (u : box I φ --> X) : box (I +) (b φ) --> X.
Proof.
use (_ · subst_restriction (m_PreShv I) (b φ) · u).
(* Make a special lemma for this? *)
use make_nat_trans.
- intros J XX.
  exists (pr1 XX).
  abstract (now rewrite m_b, (pr2 XX)).
- intros J K f.
  apply funextsec; intro ρ.
  apply subtypePath; trivial; intros x; apply setproperty.
Defined.


(***********************************)
(* Composition and fill structures *)
(***********************************)

(* These definitions of fill and comp are a lot easier to
   work with than the ones similar to the paper *)
Section fibrant.

Local Notation "a --> b" := (precategory_morphisms a b).

Lemma fill_uniform_prf {X Y : PreShv C} {α : X --> Y} {I : C} {φ : yon I --> FF}
  {u : box I φ --> X} {v : yon (I+) --> Y} (H : u · α = ι · v)
  {J} (f : J --> I)  : box_subst f φ · u · α = ι · (# yon (# F f) · v).
Proof.
rewrite <- assoc, H.
apply (nat_trans_eq has_homsets_HSET); intros K.
now apply funextsec.
Qed.

(* Fill structure - computes diagonal map for

                  u
     box(I,phi) ------> X
         |              |
       i |              | α
         |              |
         V              V
      yon(I+) --------> Y
                  v
 *)
Definition fill_struct {X Y : PreShv C} (α : X --> Y) : UU.
Proof.
use total2.
- apply (∏ (I : C) (φ : yon I --> FF) (u : box I φ --> X)
           (v : yon (I+) --> Y) (H : u · α = ι · v), yon (I+) --> X).
- intros fill.
  use (∏ I (φ : yon I --> FF) (u : box I φ --> X)
         (v : yon (I+) --> Y) (H : u · α = ι · v), (_ × _) × _).
  + (* upper triangle *)
    apply (u = ι · fill _ _ _ _ H).
  + (* lower triangle *)
    apply (fill _ _ _ _ H · α = v).
  + (* uniformity *)
    apply (∏ J (f : J --> I),
           # yon (# F f) · fill I φ u v H =
           fill J (# yon f · φ) (box_subst f φ · u) (# yon (# F f) · v)
                   (fill_uniform_prf H f)).
Defined.


(* A comp struct - diagonal map for the extended diagram *)
Definition comp_struct {X Y : PreShv C} (α : X --> Y) : UU.
Proof.
use total2.
- apply (∏ {I} {φ : yon I --> FF} {u : box I φ --> X}
           {v : yon (I+) --> Y} (H : u · α = ι · v), yon I --> X).
- intros comp.
  use (∏ I (φ : yon I --> FF) (u : box I φ --> X)
         (v : yon (I+) --> Y) (H : u · α = ι · v), (_ × _) × _).
  + (* upper triangle *)
    apply (ι · comp _ _ _ _ H = u_subst φ · u).
  + (* lower triangle *)
    apply (comp _ _ _ _ H · α = e₁_PreShv I · v).
  + (* uniformity *)
    apply (∏ J (f : J --> I),
           # yon f · comp I φ u v H =
           comp J (# yon f · φ) (box_subst f φ · u) (# yon (# F f) · v)
                     (fill_uniform_prf H f)).
Defined.

(* Very useful lemma for comparing two comp operations
   (this is used in the proof of uniformity below) *)
Lemma comp_eq {X Y : PreShv C} (α : X --> Y)
  (comp : ∏ (I : C) (φ : yon I --> FF) (u : box I φ --> X) (v : yon (I +) --> Y),
             u · α = ι · v → yon I --> X)
  (I : C) (φ : yon I --> FF) (u1 u2 : box I φ --> X) (v1 v2 : yon (I +) --> Y)
  (H1 : u1 · α = ι · v1) (H2 : u2 · α = ι · v2)
  (Hu12 : u1 = u2) (Hv12 : v1 = v2) :
  comp I φ u1 v1 H1 = comp I φ u2 v2 H2.
Proof.
induction Hu12.
induction Hv12.
apply maponpaths, (isaset_nat_trans has_homsets_HSET).
Qed.


(** The easy direction: fill implies comp *)

(* First define the operation *)
Definition fill_to_comp_op {X Y : PreShv C} {α : X --> Y} (Fα : fill_struct α) :
  ∏ (I : C) (φ : yon I --> FF) (u : box I φ --> X)
    (v : yon (I +) --> Y), u · α = ι · v → yon I --> X.
Proof.
intros I φ u v H.
apply (e₁_PreShv I · pr1 Fα I φ u v H).
Defined.

(* Upper triangle commutes *)
Lemma fill_to_comp_comm1 {X Y : PreShv C} {α : X --> Y} (Fα : fill_struct α)
  (I : C) (φ : yon I --> FF) (u : box I φ --> X) (v : yon (I +) --> Y) (H : u · α = ι · v) :
  ι · fill_to_comp_op Fα I φ u v H = u_subst φ · u.
Proof.
unfold fill_to_comp_op; induction Fα as [fill Hfill]; simpl.
destruct (Hfill I φ u v H) as [[Hfill1 _] _].
apply pathsinv0; etrans; [apply maponpaths, Hfill1|].
now apply (nat_trans_eq (has_homsets_HSET)); intros J; apply funextsec.
Qed.

(* Lower triangle commutes *)
Lemma fill_to_comp_comm2 {X Y : PreShv C} {α : X --> Y} (Fα : fill_struct α)
  (I : C) (φ : yon I --> FF) (u : box I φ --> X) (v : yon (I +) --> Y) (H : u · α = ι · v) :
  fill_to_comp_op Fα I φ u v H · α = e₁_PreShv I · v.
Proof.
unfold fill_to_comp_op; induction Fα as [fill Hfill]; simpl.
destruct (Hfill I φ u v H) as [[_ Hfill2] _].
etrans; [apply (! (assoc (e₁_PreShv I) _ _))|].
now rewrite Hfill2.
(* etrans; [|apply maponpaths, Hfill2]. *)
(* now apply (nat_trans_eq (has_homsets_HSET)); intros J; apply funextsec. *)
Qed.

(* Uniformity *)
Lemma fill_to_comp_uniform {X Y : PreShv C} {α : X --> Y} (Fα : fill_struct α)
  (I : C) (φ : yon I --> FF) (u : box I φ --> X) (v : yon (I +) --> Y) (H : u · α = ι · v) :
  ∏ (J : C) (f : J --> I), # yon f · fill_to_comp_op Fα I φ u v H =
  fill_to_comp_op Fα J (# yon f · φ) (box_subst f φ · u)
                  (# yon (# F f) · v) (fill_uniform_prf H f).
Proof.
intros J f; unfold fill_to_comp_op; induction Fα as [fill Hfill].
destruct (Hfill I φ u v H) as [_ fill_uni].
rewrite <- fill_uni, !assoc.
apply cancel_postcomposition, (nat_trans_eq (has_homsets_HSET)); intros K.
apply funextsec; intro ρ'; cbn; unfold yoneda_morphisms_data.
now rewrite <-!assoc; apply maponpaths, (nat_trans_ax e₁).
Qed.

Lemma fill_to_comp {X Y : PreShv C} (α : X --> Y)
  (Fα : fill_struct α) : comp_struct α.
Proof.
exists (fill_to_comp_op Fα); intros I φ u v H.
split; [split|].
+ apply fill_to_comp_comm1.
+ apply fill_to_comp_comm2.
+ apply fill_to_comp_uniform.
Defined.


(* Now the harder direction *)

(* First define the operation *)
Definition comp_to_fill_op {X Y : PreShv C} {α : X --> Y} (Cα : comp_struct α) :
  ∏ (I : C) (φ : yon I --> FF) (u : box I φ --> X)
    (v : yon (I +) --> Y), u · α = ι · v → yon (I +) --> X.
Proof.
intros I φ u v H.
apply (pr1 Cα (I +) (b φ) (box_b_subst α I φ u) (m_PreShv I · v)).
abstract (apply (nat_trans_eq has_homsets_HSET); intros J; apply funextsec; intro ρ;
          apply (eqtohomot (nat_trans_eq_pointwise H J))).
Defined.

(* Upper triangle commutes *)
Lemma comp_to_fill_comm1 {X Y : PreShv C} {α : X --> Y} (Cα : comp_struct α)
  (I : C) (φ : yon I --> FF) (u : box I φ --> X) (v : yon (I +) --> Y) (H : u · α = ι · v) :
  u = ι · comp_to_fill_op Cα I φ u v H.
Proof.
unfold comp_to_fill_op; induction Cα as [comp Hcomp]; simpl.
destruct (Hcomp (I +) (b φ) (box_b_subst α I φ u) (m_PreShv I · v)
                (comp_to_fill_op_subproof X Y α I φ u v H)) as
                [[Hcomp1 Hcomp2] comp_uni].
etrans; [|apply (!Hcomp1)].
apply (nat_trans_eq has_homsets_HSET (pr1 (box I φ)) (pr1 X)); intros J.
apply funextsec; intro ρ; cbn.
apply maponpaths, subtypePath; [ intros x; apply setproperty|]; cbn.
rewrite <-assoc; apply pathsinv0.
etrans; [ apply maponpaths, (nat_trans_eq_pointwise He₁m' I)|].
now apply id_right.
Qed. (* This is slow *)

(* Lower triangle commutes *)
Lemma comp_to_fill_comm2 {X Y : PreShv C} {α : X --> Y} (Cα : comp_struct α)
  (I : C) (φ : yon I --> FF) (u : box I φ --> X) (v : yon (I +) --> Y) (H : u · α = ι · v) :
  comp_to_fill_op Cα I φ u v H · α = v.
Proof.
unfold comp_to_fill_op; induction Cα as [comp Hcomp]; simpl.
destruct (Hcomp (I +) (b φ) (box_b_subst α I φ u) (m_PreShv I · v)
                (comp_to_fill_op_subproof X Y α I φ u v H)) as
                [[Hcomp1 Hcomp2] comp_uni].
etrans; [apply Hcomp|].
now rewrite assoc, e₁_m_PreShv, id_left.
Qed.

(* Uniformity *)

Arguments functor_on_morphisms : simpl never.

Lemma ρ_eq (I K : C) (φ ψ : yon I --> FF)
  (ρ : pr1 (pr1 (box I φ) K)) (eq : φ = ψ) :
  pr1 ρ = pr1 (pr1 (pr1 (idtoiso (maponpaths (box I) eq))) K ρ).
Proof.
now induction eq.
Qed.

Lemma box_subst_comp_box_b_subst {I J} (f : J --> I) (φ : yon I --> FF)
  {X Y : PreShv C} (α : X --> Y) (u : box I φ --> X) :
  box_subst (# F f) (b φ) · box_b_subst α I φ u =
  transportf (λ x, box (J +) x --> X) (b_yon f φ)
    (box_b_subst α J (# yon f · φ) (box_subst f φ · u)).
Proof.
pathvia (transportf (λ x, x --> X) (maponpaths (box (J+)) (b_yon f φ))
                    (box_b_subst α J (# yon f · φ) (box_subst f φ · u))).
{ apply (@transportf_transpose _ (λ x, x --> X)), pathsinv0.
  etrans; [|apply idtoiso_precompose].
  rewrite pathsinv0inv0.
  apply (nat_trans_eq has_homsets_HSET); intro K; apply funextsec; intros ρ.
  apply (maponpaths (pr1 u K)).
  apply subtypePath; [ intros x; apply setproperty|].
  (* simpl. *) (* This simpl gives an EXTREMELY slow Qed *)
  etrans; [|apply assoc].
  etrans; [|eapply pathsinv0, maponpaths, (nat_trans_ax m f)].
  rewrite assoc.
  apply cancel_postcomposition, cancel_postcomposition.
  apply (ρ_eq (J +) K (b (# yon f · φ)) (# yon (# F f) · b φ) ρ (b_yon f φ)). }
{ induction (b_yon f φ).
  now rewrite idpath_transportf. }
Qed.

Lemma yon_m_v {I J} (f : J --> I) (Y : PreShv C) (v : yon (I +) --> Y) :
  # yon (# F (# F f)) · (m_PreShv I · v) = m_PreShv J · (# yon (# F f) · v).
Proof.
apply (nat_trans_eq has_homsets_HSET); intro K; apply funextsec; intro ρ; cbn.
apply maponpaths; simpl; unfold yoneda_morphisms_data.
rewrite <- !assoc.
apply maponpaths, (nat_trans_ax m f).
Qed.

Lemma comp_to_fill_uniform {X Y : PreShv C} {α : X --> Y} (Cα : comp_struct α)
  (I : C) (φ : yon I --> FF) (u : box I φ --> X) (v : yon (I +) --> Y) (H : u · α = ι · v) :
  ∏ (J : C) (f : J --> I),
  # yon (# F f) · comp_to_fill_op Cα I φ u v H =
  comp_to_fill_op Cα J (# yon f · φ) (box_subst f φ · u) (# yon (# F f) · v)
                                           (fill_uniform_prf H f).
Proof.
unfold comp_to_fill_op; induction Cα as [comp Hcomp]; intros J f; simpl.
destruct (Hcomp (I +) (b φ) (box_b_subst α I φ u) (m_PreShv I · v)
                (comp_to_fill_op_subproof X Y α I φ u v H)) as
                [[Hcomp1 Hcomp2] comp_uni].
etrans; [apply (comp_uni (J+) (# F f))|].
match goal with |-comp _ ?AA1 ?AA2 ?AA3 ?AA4 = comp _ ?BB1 ?BB2 ?BB3 ?BB4 =>
  set (A1 := AA1); set (A2 := AA2); set (A3 := AA3); set (A4 := AA4);
  set (B1 := BB1); set (B2 := BB2); set (B3 := BB3); set (B4 := BB4) end.
set (B2' := transportf (λ x, box (J +) x --> X) (b_yon f φ) B2).
assert (B4' : B2' · α = ι · A3).
{ now etrans; [eapply cancel_postcomposition, pathsinv0, box_subst_comp_box_b_subst|]. }
pathvia (comp (J+) A1 B2' A3 B4').
- apply comp_eq; trivial.
  now apply box_subst_comp_box_b_subst.
- induction (b_yon f φ).
  now apply comp_eq; trivial; apply yon_m_v.
Qed.

Lemma comp_to_fill {X Y : PreShv C} (α : X --> Y) (Cα : comp_struct α) :
  fill_struct α.
Proof.
exists (comp_to_fill_op Cα); intros I φ u v H.
split; [split|].
- apply comp_to_fill_comm1.
- apply comp_to_fill_comm2.
- apply comp_to_fill_uniform.
Defined.

End fibrant.
End cubical.
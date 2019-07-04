(**

This files proves that presheaves on a category C (contravariant
functors into HSET) forms a type category ([PreShv_TypeCat]). As the
collection of types in context Γ don't form an hset it is not possible
to instantiate the CwF structure, however all of the other axioms of a
CwF have been formalized.

Contexts, written Γ ⊢, are modelled as presheaves and substitutions
are modelled by natural transformations σ : Δ → Γ. So the identity
substitution is given by the identity natural transformation 1 : Γ → Γ
and composition of substitutions are given by composition of natural
transformations σ · δ (note that the order is diagrammatic). So we
automatically get the equations:

<<
      1 · σ = σ · 1 = σ        (σ · δ) · τ = σ · (δ · τ)
>>

Types in context Γ, usually written Γ ⊢ A and written A : Γ ⊢ in the
formalization, are defined as presheaves on the category of elements
of Γ. So A : Γ ⊢ means A : PreShv (∫ Γ).

Terms a of type A in context Γ, usually written Γ ⊢ a : A and written
a : Γ ⊢ A in the formalization, are defined as families of sets aρ in
Aρ for each set ρ in Γ(I) such that (aρ)f = a(ρf) for f : J → I (see
[TermIn]). This is equivalent to sections s : Γ → Γ.A of the
projection map p : Γ.A → Γ (see [TermIn_to_TermInSection],
[TermInSection_to_TermIn]).

The operations then defined are:

<<
              Γ ⊢ A    σ : Δ → Γ
            ---------------------- ([subst_type])
                   Δ ⊢ Aσ


             Γ ⊢ a : A    σ : Δ → Γ
           -------------------------- ([subst_term)]
                 Δ ⊢ aσ : Aσ


                    Γ ⊢ A
                 ----------- ([ctx_ext])
                   Γ ⋆ A ⊢


                    Γ ⊢ A
               ----------------- ([ctx_proj])
                 p : Γ ⋆ A → Γ


                    Γ ⊢ A
              ------------------ ([ctx_last])
                Γ ⋆ A ⊢ q : Ap


             σ : Δ → Γ   Γ ⊢ A   Δ ⊢ a : Aσ
          ----------------------------------- ([subst_pair])
                (σ,a) : Δ → Γ ⋆ A


                  σ : Δ → Γ    Δ ⊢ A
                ---------------------- ([p_gen])
                  p_gen : Δ ⋆ A → Γ


                  σ : Δ → Γ    Γ ⊢ A
             ----------------------------- ([q_gen])
               Δ ⋆ Aσ ⊢ q_gen : A(p_gen)
>>

These satisfy the following equations:

<<
                       A1 = A            ([subst_type_id])

                    (Aσ)δ = A(σδ)        ([subst_type_comp])

                       a1 = a            ([subst_term_id])

                    (aσ)δ = a(σδ)        ([subst_term_comp])

                δ · (σ,a) = (δ · σ,aδ)   ([subst_pair_subst])

                (σ,a) · p = σ            ([subst_pair_p])

                   q(σ,a) = a            ([subst_pair_q])

                    (p,q) = 1            ([subst_pair_id])

        (p_gen,q_gen) · p = p · σ        ([q_gen_mor_p])
>>

And the last square is a pullback square ([isPullback_q_gen_mor]).

Written by: Anders Mörtberg, 2017

 *)

Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.MoreFoundations.Univalence.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.RightKanExtension.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.eqdiag.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.ElementsOp.

Require Import TypeTheory.Auxiliary.CategoryTheoryImports.
Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.TypeCat.

Local Open Scope cat.

Section presheaves.

Context {C : precategory} (hsC : has_homsets C).

(** Γ ⊢ A is interpreted as a presheaf of ∫ Γ. In Coq this is written A : Γ ⊢ *)
Local Notation "Γ ⊢" := (PreShv (∫ Γ)) (at level 50).

Local Notation "'1'" := (nat_trans_id _).

(** The substitution functor *)
Definition subst_functor {Γ Δ : PreShv C} (σ : Δ --> Γ) :
  functor (PreShv (∫ Γ)) (PreShv (∫ Δ)).
Proof.
use pre_composition_functor.
- apply has_homsets_opp, has_homsets_cat_of_elems, hsC.
- apply functor_opp, (cat_of_elems_on_nat_trans σ).
Defined.

(** WARNING: Only use this for small C *)
Lemma is_left_adjoint_subst_functor {Γ Δ : PreShv C} (σ : Δ --> Γ) :
  is_left_adjoint (subst_functor σ).
Proof.
use (RightKanExtension_from_limits _ _ _ LimsHSET). (* apply is slow here... *)
Defined.

(** The right adjoint to substitution *)
Definition π {Γ Δ : PreShv C} (σ : Δ --> Γ) :=
  right_adjoint (is_left_adjoint_subst_functor σ).

(* TODO: define the left adjoint as well? *)

(** Given Γ ⊢ A and a substitution σ : Δ → Γ we get Δ ⊢ Aσ *)
Definition subst_type {Γ Δ : PreShv C} (A : Γ ⊢) (σ : Δ --> Γ) : Δ ⊢ :=
  subst_functor σ A.

Local Notation "A ⦃ s ⦄" := (subst_type A s) (at level 40, format "A ⦃ s ⦄").

(** A1 = A *)
Lemma subst_type_id {Γ : PreShv C} (A : Γ ⊢) : A⦃1⦄ = A.
Proof.
apply (functor_eq _ _ has_homsets_HSET).
use functor_data_eq.
- intros c; apply idpath.
- intros [a1 a2] [b1 b2] f; cbn.
  now apply maponpaths, subtypePath; [intros x; apply setproperty|].
Defined.

(* It is important that the above proof is the way it is so the following is provable *)
Lemma base_paths_subst_type_id {Γ : PreShv C} (A : Γ ⊢) :
  base_paths _ _ (base_paths _ _ (subst_type_id A)) =
  funextsec _ _ _ (λ c, idpath _).
Proof.
unfold subst_type_id, functor_eq, functor_data_eq.
now rewrite !base_total2_paths.
Qed.

(** A(σ1 σ2) = (A σ2) σ1 *)
Lemma subst_type_comp {Γ Δ Θ : PreShv C} (σ1 : Θ --> Δ) (σ2 : Δ --> Γ) (A : Γ ⊢) :
  A⦃σ1 · σ2⦄ = A⦃σ2⦄⦃σ1⦄.
Proof.
apply (functor_eq _ _ has_homsets_HSET).
use functor_data_eq.
- intros c; apply idpath.
- intros [a1 a2] [b1 b2] f; cbn.
  now apply maponpaths, subtypePath; [intros x; apply setproperty|].
Defined.

Lemma base_paths_subst_type_comp {Γ Δ Θ : PreShv C}
  (σ1 : Θ --> Δ) (σ2 : Δ --> Γ) (A : Γ ⊢) :
  base_paths _ _ (base_paths _ _ (subst_type_comp σ1 σ2 A)) =
  funextsec _ _ _ (λ c, idpath _).
Proof.
unfold subst_type_comp, functor_eq, functor_data_eq.
now rewrite !base_total2_paths.
Qed.

(** Direct definition of terms: Γ ⊢ a : A *)
Definition TermIn {Γ : PreShv C} (A : Γ ⊢) : UU.
Proof.
use total2.
- apply (∏ (I : C) (ρ : pr1 (pr1 Γ I)), pr1 (pr1 A (make_ob I ρ))).
- intros a.
  apply (∏ (I J : C) (f : J --> I) (ρ : pr1 (pr1 Γ I)),
           # (pr1 A) (mor_to_el_mor f ρ) (a I ρ) = a J (# (pr1 Γ) f ρ)).
Defined.

Local Notation "Γ ⊢ A" := (@TermIn Γ A) (at level 50).

Definition mkTermIn {Γ : PreShv C} (A : Γ ⊢)
  (u : ∏ (I : C) (ρ : pr1 ((pr1 Γ) I)), pr1 ((pr1 A) (make_ob I ρ)))
  (Hu : ∏ I J (f : C ⟦ J, I ⟧) (ρ : pr1 ((pr1 Γ) I)),
        # (pr1 A) (mor_to_el_mor f ρ) (u I ρ) = u J (# (pr1 Γ) f ρ)) : Γ ⊢ A.
Proof.
use tpair.
- exact u.
- abstract (exact Hu).
Defined.

Lemma TermIn_eq {Γ : PreShv C} {A : Γ ⊢} (a b : Γ ⊢ A) (H : pr1 a = pr1 b) : a = b.
Proof.
apply subtypePath; trivial.
now intros x; repeat (apply impred; intros); apply setproperty.
Qed.

(** Context extension: given a context Γ and a type Γ ⊢ A define Γ.A *)
Definition ctx_ext {Γ : PreShv C} (A : Γ ⊢) : PreShv C.
Proof.
use make_functor.
- use tpair.
  + simpl; intros I.
    use total2_hSet.
    * apply (pr1 Γ I).
    * intros ρ.
      apply (pr1 A (make_ob I ρ)).
  + cbn. intros I J f ρu.
    exists (# (pr1 Γ) f (pr1 ρu)).
    apply (# (pr1 A) (mor_to_el_mor f (pr1 ρu)) (pr2 ρu)).
- split.
  + intros I; apply funextfun; intros [ρ u].
    use total2_paths_f.
    * exact (eqtohomot (functor_id Γ I) ρ).
    * etrans; [use transportf_make_ob|].
      etrans; [apply transportf_PreShv|]; cbn.
      now rewrite (mor_to_el_mor_id ρ), transportfbinv, (functor_id A).
   + intros I J K f g; apply funextfun; intros [ρ u].
     use total2_paths_f.
     * exact (eqtohomot (functor_comp Γ f g) ρ).
     * etrans; [use transportf_make_ob|].
       etrans; [apply transportf_PreShv|].
       rewrite (mor_to_el_mor_comp _ f g), transportfbinv.
       generalize u; simpl in *.
       apply eqtohomot, (functor_comp A (mor_to_el_mor f ρ)  (mor_to_el_mor g (# (pr1 Γ) f ρ))).
Defined.

(* It would be nice to use the notation Γ.A here, but it doesn't seem to work *)
Local Notation "Γ ⋆ A" := (@ctx_ext Γ A) (at level 30).

(** Context projection *)
Definition ctx_proj {Γ : PreShv C} {A : Γ ⊢} : Γ ⋆ A --> Γ.
Proof.
use make_nat_trans.
- intros I X.
  apply (pr1 X).
- now intros I J f; apply funextsec.
Defined.

Let p {Γ : PreShv C} {A : Γ ⊢} := @ctx_proj Γ A.

(** Note that ctx_ext and p defines one part of the equivalence:
<<
     PreShv(∫ Γ) ≃ PreShv(C) / Γ
>>
by: Γ ⊢ A  ↦  (Γ ⋆ A,p)

Intuition: Γ ⋆ A is over Γ by p

*)


(** The last element of the context, often referred to as q *)
Definition ctx_last {Γ : PreShv C} {A : Γ ⊢} : Γ ⋆ A ⊢ A⦃p⦄.
Proof.
use mkTermIn.
+ intros I ρ.
  apply (pr2 ρ).
+ intros I J f ρ; cbn; apply map_on_two_paths; trivial.
  now apply cat_of_elems_mor_eq.
Defined.

Let q {Γ : PreShv C} {A : Γ ⊢} := @ctx_last Γ A.

Lemma transportf_term {Γ : PreShv C} (A : Γ ⊢) (a : Γ ⊢ A) (J : C)
  (x y : pr1 (pr1 Γ J)) (e : x = y) :
  transportf (λ x, pr1 (pr1 A (make_ob J x))) e (pr1 a J x) = pr1 a J y.
Proof.
now induction e.
Qed.

Lemma subst_term_prf {Γ Δ : PreShv C} (σ : Δ --> Γ) (A : Γ ⊢) (a : Γ ⊢ A)
  (I J : C) (f : C ⟦ J, I ⟧) (ρ : pr1 ((pr1 Δ) I)) :
  # (pr1 (A⦃σ⦄)) (mor_to_el_mor f ρ) (pr1 a I (pr1 σ I ρ)) =
  pr1 a J (pr1 σ J (# (pr1 Δ) f ρ)).
Proof.
set (eq := eqtohomot (nat_trans_ax σ I J f) ρ).
set (x := # (pr1 A) (mor_to_el_mor f (pr1 σ I ρ)) (pr1 a I (pr1 σ I ρ))).
intermediate_path (transportb (λ x, pr1 ((pr1 A) (make_ob J x))) eq x).
{ apply pathsinv0.
  etrans; [use transportf_make_ob|].
  etrans; [apply transportf_PreShv|]; cbn.
  apply map_on_two_paths; trivial.
  apply cat_of_elems_mor_eq; cbn in *.
  rewrite transportf_total2; simpl.
  rewrite (transportf_make_ob_eq _ (maponpaths _ (!eq))).
  generalize (base_paths_maponpaths_make_ob _ _ (!eq)); simpl; intros H.
  now rewrite H, idpath_transportf. }
set (w := pr1 a J (# (pr1 Γ) f (pr1 σ I ρ))).
intermediate_path (transportb (λ x, pr1 ((pr1 A) (make_ob J x))) eq w).
{ now apply maponpaths, (pr2 a I J f (pr1 σ _ ρ)). }
now apply transportf_term.
Qed.

(** Given Γ ⊢ a : A and a substitution σ : Δ → Γ we get Δ ⊢ aσ : Aσ *)
Definition subst_term {Γ Δ : PreShv C} (σ : Δ --> Γ) {A : Γ ⊢} (a : Γ ⊢ A) : Δ ⊢ A⦃σ⦄.
Proof.
use mkTermIn.
- intros I ρ.
  apply (pr1 a _ (pr1 σ I ρ)).
- apply subst_term_prf.
Defined.

Lemma transportf_TypeIn {Γ : PreShv C} (I : C) (ρ : pr1 Γ I : hSet) (A B : Γ ⊢) (e : A = B)
  (x : (pr1 A) (make_ob I ρ) : hSet) :
  transportf (λ x0 : Γ ⊢, pr1 ((pr1 x0) (make_ob I ρ))) e x =
  transportf (λ x0 : hSet, pr1 x0) (eqtohomot (base_paths _ _ (base_paths _ _ e)) (make_ob I ρ)) x.
Proof.
now induction e.
Qed.

(* This lemma is not very useful? *)
Lemma transportf_subst_type0 {Γ Δ : PreShv C} (σ : Δ --> Γ)
  {A : Γ ⊢} {B : Γ ⊢} (a : Γ ⊢ A) (e : A = B) :
    transportf (λ x, Δ ⊢ x) (maponpaths (λ x, subst_type x σ) e)
               (subst_term σ a) =
    subst_term σ (transportf TermIn e a).
Proof.
now induction e.
Qed.

(** a1 = a *)
Lemma subst_term_id {Γ : PreShv C} {A : Γ ⊢} (a : Γ ⊢ A) :
  subst_term 1 a = transportb TermIn (subst_type_id A) a.
Proof.
apply transportf_transpose, TermIn_eq.
etrans; [use pr1_transportf|].
apply funextsec; intro I; apply funextsec; intro ρ.
rewrite !transportf_forall, transportf_TypeIn, pathsinv0inv0.
now rewrite base_paths_subst_type_id, toforallpaths_funextsec, idpath_transportf.
Qed.

(** a(σ1 σ2) = (a σ2)σ1 *)
Lemma subst_term_comp {Γ Δ Θ : PreShv C} (σ1 : Θ --> Δ) (σ2 : Δ --> Γ) {A : Γ ⊢} (a : Γ ⊢ A) :
  subst_term (σ1 · σ2) a =
  transportb (λ x, Θ ⊢ x) (subst_type_comp σ1 σ2 A) (subst_term σ1 (subst_term σ2 a)).
Proof.
apply transportf_transpose, TermIn_eq.
etrans; [use pr1_transportf|].
apply funextsec; intro I; apply funextsec; intro ρ.
rewrite !transportf_forall, transportf_TypeIn, pathsinv0inv0.
now rewrite (base_paths_subst_type_comp σ1 σ2 A), toforallpaths_funextsec, idpath_transportf.
Qed.

(** Pairing of substitutions *)
Definition subst_pair {Γ Δ : PreShv C} {A : Γ ⊢} (σ : Δ --> Γ) (a : Δ ⊢ A⦃σ⦄) : Δ --> Γ ⋆ A.
Proof.
use make_nat_trans.
- intros I ρ.
  apply (pr1 σ _ ρ,,pr1 a I ρ).
- intros I J f.
  apply funextsec; intro ρ; cbn.
  apply (total2_paths2_f (eqtohomot (nat_trans_ax σ I J f) ρ)).
  etrans; [eapply maponpaths, (!(pr2 a I J f ρ))|].
  etrans; [use transportf_make_ob|].
  etrans; [apply (@transportf_PreShv (∫ Γ) A)|].
  apply map_on_two_paths; trivial.
  apply cat_of_elems_mor_eq; simpl.
  rewrite transportf_total2; simpl.
  etrans; [apply transportf_make_ob_eq|].
  etrans; [eapply map_on_two_paths; [|apply idpath]|].
    apply(base_paths_maponpaths_make_ob _ _ (eqtohomot (nat_trans_ax σ I J f) ρ)).
  now rewrite idpath_transportf.
Defined.

(** [a] = (1,a) *)
Definition subst_el {Γ : PreShv C} {A : Γ ⊢}  (a : Γ ⊢ A⦃1⦄) : Γ --> Γ ⋆ A :=
  subst_pair 1 a.

Definition term_to_subst {Γ : PreShv C} (A : Γ ⊢) (a : Γ ⊢ A) : Γ --> Γ ⋆ A.
Proof.
apply subst_el.
now rewrite subst_type_id. (* probably better to define more directly *)
Defined.

(** (σ,a) · p = σ *)
Lemma subst_pair_p {Γ Δ : PreShv C} (σ : Δ --> Γ) {A : Γ ⊢} (a : Δ ⊢ A⦃σ⦄) :
  subst_pair σ a · p = σ.
Proof.
apply (nat_trans_eq has_homsets_HSET).
now intros I; apply funextsec.
Qed.

(* It is very important that this lemma is proved this way as later
lemmas rely on the shape of the proof (it is crucial that the first
case after functor_data_eq is proved by idpath) *)
Lemma subst_type_pair_p {Γ Δ : PreShv C} (σ : Δ --> Γ) {A : Γ ⊢} (a : Δ ⊢ A⦃σ⦄) :
  (A⦃p⦄)⦃subst_pair σ a⦄ = A⦃σ⦄.
Proof.
apply (functor_eq _ _ has_homsets_HSET).
use functor_data_eq.
- intros c; apply idpath.
- intros [a1 a2] [b1 b2] f; cbn.
  now apply maponpaths, subtypePath; [intros x; apply setproperty|].
Defined.

(* The above lemma could also be proved by: *)
(* set (e := maponpaths (λ σ, A⦃σ⦄) (subst_pair_p σ a)). *)
(* set (e' := !subst_type_comp (subst_pair σ a) p A). *)
(* exact (e' @ e). *)

(* Or even: *)
(* now rewrite <- subst_type_comp, subst_pair_p. *)

(* But if the definition is not the right one above the following lemma is not easily provable *)
Lemma base_paths_subst_type_pair_p {Γ Δ : PreShv C} (σ : Δ --> Γ) {A : Γ ⊢} (a : Δ ⊢ A⦃σ⦄) :
  base_paths _ _ (base_paths _ _ (subst_type_pair_p σ a)) =
  funextsec _ _ _ (λ c, idpath _).
Proof.
unfold subst_type_pair_p, functor_eq, functor_data_eq.
now rewrite !base_total2_paths.
Qed.

(** q(σ,a) = a *)
Lemma subst_pair_q {Γ Δ : PreShv C} (σ : Δ --> Γ) {A : Γ ⊢} (a : Δ ⊢ A⦃σ⦄) :
  transportf (λ x, Δ ⊢ x) (subst_type_pair_p σ a) (subst_term (subst_pair σ a) q) = a.
Proof.
apply TermIn_eq.
etrans; [use pr1_transportf|].
apply funextsec; intro I; apply funextsec; intro ρ.
rewrite !transportf_forall, transportf_TypeIn.
now rewrite (base_paths_subst_type_pair_p σ a), toforallpaths_funextsec, idpath_transportf.
Qed.

(** σ2 · (σ1,a) = (σ2 · σ1,a σ2) *)
Lemma subst_pair_subst {Γ Δ Θ : PreShv C} (σ1 : Δ --> Γ) (σ2 : Θ --> Δ)
  {A : Γ ⊢} (a : Δ ⊢ A⦃σ1⦄) :
  σ2 · subst_pair σ1 a =
  subst_pair (σ2 · σ1) (transportb (λ x : Θ ⊢, Θ ⊢ x)
                                   (subst_type_comp σ2 σ1 A) (subst_term σ2 a)).
Proof.
apply (nat_trans_eq has_homsets_HSET); simpl; intros I.
apply funextsec; intro ρ.
apply pair_path_in2, pathsinv0; unfold transportb.
set (P := ! subst_type_comp σ2 σ1 A).
set (B := (λ a0 : Θ ⊢, ∏ (I : C) (ρ : pr1 (pr1 Θ I)), pr1 (pr1 a0 (make_ob I ρ)))).
etrans; [apply (eqtohomot (eqtohomot
                          (maponpaths pr1 (@transportf_total2 _ B _ _ _ P _)) I) ρ)|].
unfold B; simpl.
rewrite !transportf_forall.
apply pathsinv0, (@transportf_transpose _ (λ x : Θ ⊢, pr1 ((pr1 x) (make_ob I ρ))) _ _ P).
unfold transportb, P; rewrite pathsinv0inv0.
etrans; [apply (transportf_TypeIn I ρ _ _ (subst_type_comp σ2 σ1 A) _)|].
now rewrite base_paths_subst_type_comp, toforallpaths_funextsec, idpath_transportf.
Qed.

(** (p,q) = 1 *)
Lemma subst_pair_id {Γ : PreShv C} {A : Γ ⊢} : subst_pair (A:=A) p q = 1.
Proof.
apply (nat_trans_eq has_homsets_HSET); simpl; intros I.
now apply funextsec.
Qed.


(** Γ ⊢ a : A can also be interpreted as sections s : Γ --> Γ.A to p *)
Definition TermInSection {Γ : PreShv C} (A : Γ ⊢) : UU :=
  ∑ s : Γ --> Γ ⋆ A, s · p = 1.

Lemma TermIn_to_TermInSection {Γ : PreShv C} (A : Γ ⊢) : TermIn A → TermInSection A.
Proof.
intros a.
use tpair.
- apply (term_to_subst _ a).
- abstract (apply (nat_trans_eq has_homsets_HSET);
            now intros I; simpl; apply funextfun).
Defined.

Lemma TermInSection_to_TermIn {Γ : PreShv C} (A : Γ ⊢) : TermInSection A → TermIn A.
Proof.
intros a.
rewrite <-subst_type_id, <- (pr2 a), subst_type_comp.
exact (subst_term _ q).
Defined.

(* This alternative definition of q is very slow *)
(* Definition q' {Γ : PreShv C} (A : Γ ⊢) : TermInSection (A⦃@p Γ A⦄). *)
(* Proof. *)
(* mkpair. *)
(* - use make_nat_trans. *)
(*   + intros I ρ. *)
(*     exists ρ. *)
(*     apply (pr2 ρ). *)
(*   + abstract (intros I J f; apply funextsec; intro ρ; *)
(*               apply pair_path_in2; cbn; *)
(*               apply map_on_two_paths; trivial; *)
(*               now apply cat_of_elems_mor_eq). *)
(* (* This abstract is VERY slow *) *)
(* (* - abstract (apply (nat_trans_eq has_homsets_HSET); intros I; simpl; *) *)
(* (*             apply funextsec; intro ρ; apply idpath). *) *)
(* (* Defined. *) *)
(* Admitted. *)


(** Various results for instantiating TypeCat  *)

Definition p_gen {Γ Δ : PreShv C} {A : Δ ⊢} (σ : Δ --> Γ) : Δ ⋆ A --> Γ.
Proof.
use make_nat_trans.
- intros I X.
  apply (pr1 σ _ (pr1 X)).
- intros I J f; apply funextsec; intro ρ.
  apply (eqtohomot (nat_trans_ax σ I J f) (pr1 ρ)).
Defined.

Definition q_gen {Γ Δ : PreShv C} {A : Γ ⊢} (σ : Δ --> Γ) : (Δ ⋆ (A⦃σ⦄)) ⊢ A⦃p_gen σ⦄.
Proof.
use mkTermIn.
- intros I ρ.
  apply (pr2 ρ).
- intros I J f ρ; cbn.
  now apply map_on_two_paths; [apply cat_of_elems_mor_eq|].
Defined.

Definition q_gen_mor {Γ Δ : PreShv C} (A : Γ ⊢) (σ : Δ --> Γ) : Δ ⋆ (A⦃σ⦄) --> Γ ⋆ A :=
  subst_pair (p_gen σ) (q_gen σ).

Lemma q_gen_mor_p {Γ Δ : PreShv C} (A : Γ ⊢) (σ : Δ --> Γ) :
  q_gen_mor A σ · p = p · σ.
Proof.
apply (nat_trans_eq has_homsets_HSET); intro I.
now apply funextsec.
Qed.

Lemma isPullback_q_gen_mor {Γ Δ : PreShv C} (A : Γ ⊢) (σ : Δ --> Γ) :
  isPullback _ _ _ _ (q_gen_mor_p A σ).
Proof.
use pb_if_pointwise_pb.
intros I.
use isPullback_HSET.
intros a b eq.
use unique_exists.
- exists b; cbn in *.
  apply (transportf (λ x, pr1 (A (make_ob I x))) eq (pr2 a)).
- split; trivial; simpl.
  use total2_paths_f.
  + apply (!eq).
  + now cbn; rewrite transport_f_f, pathsinv0r, idpath_transportf.
- intros ρ.
  now apply isapropdirprod; apply setproperty.
- simpl; intros [x1 x2] [h1 h2].
  use total2_paths_f.
  + apply h2.
  + induction h2; induction h1; simpl.
    assert (H : eq = idpath _).
    { apply setproperty. }
    now rewrite H, !idpath_transportf.
Defined.

End presheaves.

(** * Presheaf categories are type categories *)
Section TypeCat.

Context (C : precategory) (hsC : has_homsets C).

Local Notation "Γ ⊢" := (PreShv (∫ Γ)) (at level 50).
Local Notation "Γ ⊢ A" := (@TermIn _ Γ A) (at level 50).
Local Notation "A ⦃ s ⦄" := (subst_type hsC A s) (at level 40, format "A ⦃ s ⦄").
Local Notation "Γ ⋆ A" := (@ctx_ext _ Γ A) (at level 30).

Definition PreShv_TypeCat : typecat_structure (PreShv C).
Proof.
use tpair.
- exists (λ Γ, Γ ⊢).
  exists (λ Γ A, Γ ⋆ A).
  intros Γ A Δ σ.
  exact (A⦃σ⦄).
- exists (λ Γ A, @ctx_proj _ Γ A).
  exists (λ Γ A Δ σ, q_gen_mor hsC A σ).
  exists (λ Γ A Δ σ, q_gen_mor_p hsC A σ).
  intros Γ A Δ σ.
  apply is_symmetric_isPullback.
  + apply (functor_category_has_homsets C^op).
  + exact (isPullback_q_gen_mor hsC A σ).
Defined.

End TypeCat.

(** Failed attempt to instantiate CwF structure *)
Section CwF.

Require Import TypeTheory.OtherDefs.CwF_Pitts.

Context (C : precategory) (hsC : has_homsets C).

Local Notation "Γ ⊢" := (PreShv (∫ Γ)) (at level 50).
Local Notation "Γ ⊢ A" := (@TermIn _ Γ A) (at level 50).
Local Notation "A ⦃ s ⦄" := (subst_type hsC A s) (at level 40, format "A ⦃ s ⦄").
Local Notation "Γ ⋆ A" := (@ctx_ext _ Γ A) (at level 30).

Definition PreShv_tt_structure : tt_structure (PreShv C).
Proof.
exists (λ Γ, Γ ⊢).
intros Γ A.
exact (Γ ⊢ A).
Defined.

Lemma PreShv_reindx_structure : reindx_structure PreShv_tt_structure.
Proof.
use tpair.
- intros Γ Δ A σ.
  exact (A⦃σ⦄).
- intros Γ Δ A a σ.
  exact (subst_term _ σ a).
Defined.

Definition PreShv_tt_reindx_type_struct : tt_reindx_type_struct (PreShv C).
Proof.
use tpair.
+ exists (PreShv_tt_structure,,PreShv_reindx_structure).
  intros Γ A.
  exists (Γ ⋆ A).
  apply ctx_proj.
+ intros Γ A.
  split.
  * apply ctx_last.
  * intros Δ σ a.
    exact (subst_pair hsC σ a).
Defined.

Lemma PreShv_reindx_laws : reindx_laws PreShv_tt_reindx_type_struct.
Proof.
use tpair.
- use tpair.
  + intros Γ A.
    apply subst_type_id.
  + intros Γ Δ Θ σ1 σ2 A.
    apply (subst_type_comp hsC).
- use tpair.
  + intros Γ A a.
    apply (subst_term_id hsC a).
  + intros Γ Δ Θ σ1 σ2 A a.
    exact (subst_term_comp hsC σ2 σ1 a).
Defined.

(* This is commented as we cannot complete it *)
(* Definition PreShv_CwF : cwf_struct (PreShv C). *)
(* Proof. *)
(* exists PreShv_tt_reindx_type_struct. *)
(* mkpair. *)
(* - exists PreShv_reindx_laws. *)
(*   repeat split. *)
(*   + intros Γ A Δ σ a. *)
(*     exists (subst_pair_p hsC σ a). *)
(*     intermediate_path (transportf (λ x, Δ ⊢ x) *)
(*             (subst_type_pair_p hsC σ a) (subst_term hsC (subst_pair hsC σ a) (@ctx_last _ hsC _ A))). *)
(*     admit. (* this should be provable, but painful *) *)
(*     apply subst_pair_q. *)
(*   + intros Γ A Δ Θ σ1 σ2 a. *)
(*     exact (subst_pair_subst hsC σ1 σ2 a). *)
(*   + intros Γ A. *)
(*     apply (@subst_pair_id C hsC Γ A). *)
(* - repeat split. *)
(*   + apply (functor_category_has_homsets C^op HSET has_homsets_HSET). *)
(*   + intros Γ. *)
(*     admit. (* this is not provable! *) *)
(*   + intros Γ A. *)
(*     use isaset_total2. *)
(*     * repeat (apply impred_isaset; intro); apply setproperty. *)
(*     * intros a; repeat (apply impred_isaset; intro). *)
(*       apply isasetaprop, setproperty. *)
(* Admitted. *)

End CwF.

(** Some important constructions on displayed categories

Partial contents:

- Direct products of displayed precategories (and their projections)
  - [dirprod_precat D1 D2]
  - [dirprodpr1_functor], [dirprodpr2_functor]
- Sigmas of displayed precategories
*)


Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.

Require Import Systems.Auxiliary.
Require Import Systems.UnicodeNotations.

Require Import Systems.Displayed_Cats.Auxiliary.
Require Import Systems.Displayed_Cats.Displayed_Precats.

Local Open Scope mor_disp_scope.

Local Set Automatic Introduction.
(* only needed since imports globally unset it *)

Section Auxiliary.

(** Compare [total2_paths2], [total2_paths_b]. *)
(* TODO: perhaps upstream. *)
Lemma total2_paths2_b {A : UU} {B : A → UU} 
    {a1 : A} {b1 : B a1} {a2 : A} {b2 : B a2}
    (p : a1 = a2) (q : b1 = transportb B p b2)
  : (a1,,b1) = (a2,,b2).
Proof.
  exact (@total2_paths_b _ _ (_,,_) (_,,_) p q).
Defined.

(* TODO: perhaps upstream; consider name *)
Lemma total2_reassoc_paths {A} {B : A → Type} {C : (Σ a, B a) -> Type}
    (BC : A -> Type := fun a => Σ b, C (a,,b))
    {a1 a2 : A} (bc1 : BC a1) (bc2 : BC a2)
    (ea : a1 = a2)
    (eb : transportf _ ea (pr1 bc1) = pr1 bc2)
    (ec : transportf C (total2_paths2 ea eb) (pr2 bc1) = pr2 bc2)
  : transportf _ ea bc1 = bc2.
Proof.
  destruct ea, bc1 as [b1 c1], bc2 as [b2 c2].
  cbn in *; destruct eb, ec.
  apply idpath.
Defined.

(* TODO: as for non-primed version above *)
Lemma total2_reassoc_paths' {A} {B : A → Type} {C : (Σ a, B a) -> Type}
    (BC : A -> Type := fun a => Σ b, C (a,,b))
    {a1 a2 : A} (bc1 : BC a1) (bc2 : BC a2)
    (ea : a1 = a2)
    (eb : pr1 bc1 = transportb _ ea (pr1 bc2))
    (ec : pr2 bc1 = transportb C (total2_paths2_b ea eb) (pr2 bc2))
  : bc1 = transportb _ ea bc2.
Proof.
  destruct ea, bc1 as [b1 c1], bc2 as [b2 c2].
  cbn in eb; destruct eb; cbn in ec; destruct ec.
  apply idpath.
Defined.

End Auxiliary.


(** * Products of displayed (pre)categories 

We directly define direct products of displayed categories over a base.

An alternative would be to define the direct product as the “Sigma-precategory” of the pullback to either factor.  *)
Section Dirprod.

Context {C : Precategory} (D1 D2 : disp_precat C).

Definition dirprod_disp_precat_ob_mor : disp_precat_ob_mor C.
Proof.
  exists (fun c => (D1 c × D2 c)).
  intros x y xx yy f.
  exact (pr1 xx ⇒[f] pr1 yy × pr2 xx ⇒[f] pr2 yy).
Defined.

Definition dirprod_disp_precat_id_comp
  : disp_precat_id_comp _ dirprod_disp_precat_ob_mor.
Proof.
  apply tpair.
  - intros x xx. exact (id_disp _,, id_disp _).
  - intros x y z f g xx yy zz ff gg.
    exact ((pr1 ff ;; pr1 gg),, (pr2 ff ;; pr2 gg)).
Defined.

Definition dirprod_disp_precat_data : disp_precat_data C
  := (_ ,, dirprod_disp_precat_id_comp).

Definition dirprod_disp_precat_axioms
  : disp_precat_axioms _ dirprod_disp_precat_data.
Proof.
  repeat apply tpair.
  - intros. apply dirprod_paths; refine (id_left_disp @ !_).
    + refine (pr1_transportf _ _ _ _ _ _ _).
    + apply pr2_transportf.
  - intros. apply dirprod_paths; refine (id_right_disp @ !_).
    + refine (pr1_transportf _ _ _ _ _ _ _).
    + apply pr2_transportf.
  - intros. apply dirprod_paths; refine (assoc_disp @ !_).
    + refine (pr1_transportf _ _ _ _ _ _ _).
    + apply pr2_transportf.
  - intros. apply isaset_dirprod; apply homsets_disp.
Qed.

Definition dirprod_disp_precat : disp_precat C
  := (_ ,, dirprod_disp_precat_axioms).

Definition dirprodpr1_disp_functor_data
  : functor_over_data (functor_identity C) dirprod_disp_precat (D1).
Proof.
  mkpair.
  - intros x xx; exact (pr1 xx).
  - intros x y xx yy f ff; exact (pr1 ff).
Defined.

Definition dirprodpr1_disp_functor_axioms
  : functor_over_axioms dirprodpr1_disp_functor_data.
Proof.
  split. 
  - intros; apply idpath.
  - intros; apply idpath.
Qed.

Definition dirprodpr1_disp_functor
  : functor_over (functor_identity C) dirprod_disp_precat (D1)
:= (dirprodpr1_disp_functor_data,, dirprodpr1_disp_functor_axioms).


Definition dirprodpr2_disp_functor_data
  : functor_over_data (functor_identity C) dirprod_disp_precat (D2).
Proof.
  mkpair.
  - intros x xx; exact (pr2 xx).
  - intros x y xx yy f ff; exact (pr2 ff).
Defined.

Definition dirprodpr2_disp_functor_axioms
  : functor_over_axioms dirprodpr2_disp_functor_data.
Proof.
  split. 
  - intros; apply idpath.
  - intros; apply idpath.
Qed.

Definition dirprodpr2_disp_functor
  : functor_over (functor_identity C) dirprod_disp_precat (D2)
:= (dirprodpr2_disp_functor_data,, dirprodpr2_disp_functor_axioms).

End Dirprod.

Notation "D1 × D2" := (dirprod_disp_precat D1 D2) : disp_precat_scope.
Delimit Scope disp_precat_scope with disp_precat.
Bind Scope disp_precat_scope with disp_precat.

(** * Sigmas of displayed (pre)categories *)
Section Sigma.

Context {C : Precategory}
        {D : disp_precat C}
        (E : disp_precat (total_precat D)).

Definition sigma_disp_precat_ob_mor : disp_precat_ob_mor C.
Proof.
  exists (fun c => Σ (d : D c), (E (c,,d))).
  intros x y xx yy f.
  exact (Σ (fD : pr1 xx ⇒[f] pr1 yy), 
                (pr2 xx ⇒[f,,fD] pr2 yy)).
Defined.

Definition sigma_disp_precat_id_comp
  : disp_precat_id_comp _ sigma_disp_precat_ob_mor.
Proof.
  apply tpair.
  - intros x xx.
    exists (id_disp _). exact (id_disp (pr2 xx)).
  - intros x y z f g xx yy zz ff gg.
    exists (pr1 ff ;; pr1 gg). exact (pr2 ff ;; pr2 gg).
Defined.

Definition sigma_disp_precat_data : disp_precat_data C
  := (_ ,, sigma_disp_precat_id_comp).


Definition sigma_disp_precat_axioms
  : disp_precat_axioms _ sigma_disp_precat_data.
Proof.
  repeat apply tpair.
  - intros. use total2_reassoc_paths'.
    + apply id_left_disp.
    + etrans. exact (@id_left_disp _ _ _ _ _ _ _ (pr2 ff)).
    (* TODO: why doesn’t [apply homsets_disp] work here,
       and in the other parts of this proof? *)
      apply maponpaths_2, homset_property.
  - intros. use total2_reassoc_paths'.
    + apply id_right_disp.
    + etrans. exact (@id_right_disp _ _ _ _ _ _ _ (pr2 ff)).
      apply maponpaths_2, homset_property.
  - intros. use total2_reassoc_paths'.
    + apply assoc_disp.
    + etrans. 
        exact (@assoc_disp _ _ 
                 _ _ _ _  _ _ _ 
                 _ _ _ _ (pr2 ff) (pr2 gg) (pr2 hh)).
      apply maponpaths_2, homset_property.
  - intros. apply isaset_total2; intros; apply homsets_disp.
Qed.

Definition sigma_disp_precat : disp_precat C
  := (_ ,, sigma_disp_precat_axioms).

Definition sigmapr1_disp_functor_data
  : functor_over_data (functor_identity C) sigma_disp_precat D.
Proof.
  mkpair.
  - intros x xx; exact (pr1 xx).
  - intros x y xx yy f ff; exact (pr1 ff).
Defined.

Definition sigmapr1_disp_functor_axioms
  : functor_over_axioms sigmapr1_disp_functor_data.
Proof.
  split. 
  - intros; apply idpath.
  - intros; apply idpath.
Qed.

Definition sigmapr1_disp_functor
  : functor_over (functor_identity C) sigma_disp_precat D
:= (sigmapr1_disp_functor_data,, sigmapr1_disp_functor_axioms).

(* TODO: complete [sigmapr2_disp]; will be a [functor_lifting], not a [functor_over]. *)

End Sigma.

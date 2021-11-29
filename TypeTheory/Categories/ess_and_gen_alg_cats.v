(** * Categories in essentially algebraic and generalized algebraic style *)

(** 
    Essentially algebraic categories:
    - a type of objects
    - a type of morphisms
    - composition is partially defined 

    Generalized algebraic categories:
    - a type of objects
    - a family of types of morphisms, parametrized by pairs of objects
    - composition is a dependent function

In this file, we define functions back and forth and show that 
    the two variants are equivalent
*)


Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.EssentiallyAlgebraic.
Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Categories.ess_alg_categories.

Open Scope cat.
Open Scope cat_deprecated.

(** * From generalized algebraic precategories to essentially algebraic ones.*)

(** We need extra assumption that the gen. alg. precategory is a category, i.e. has hom-sets *)

Section ess_alg_from_gen_alg.

Variable C : category.
Variable H : isaset C.

(* TODO: now we are writing compositional in diagrammatic order,
should we switch the names of [idtomor_left] and [idtomor_right]
(and similar lemmas? *) 
Lemma idtomor_left (a b : C) (f : a --> b) (e : b = b) : 
   f ;; idtomor _ _ e = f.
Proof.
  set (H1 := H b b).
  set (H2:=proofirrelevance _ H1 e (idpath _ )).
  rewrite H2. simpl.
  rewrite id_right.
  apply idpath.  
Qed.

Lemma idtomor_right (a b : C) (f : a --> b) (e : a = a) : 
   idtomor _ _ e ;; f = f.
Proof.
  set (H1 := H a a).
  set (H2:=proofirrelevance _ H1 e (idpath _ )).
  rewrite H2. simpl.
  rewrite id_left.
  apply idpath.  
Qed.

Definition obmor : UU × UU := make_dirprod (ob C) (total_morphisms C).

Definition graph_from_gen_alg : graph.
Proof.   
  exists obmor.
  exists (precategory_source C).
  exact (precategory_target C).
Defined.

Definition graph_from_gen_alg_comp : @comp_op graph_from_gen_alg.
Proof.
  intros f g e.
  exists (make_dirprod (pr1 (pr1 f)) (pr2 (pr1 g))).
  exact ((pr2 f ;; idtomor _ _ e) ;; pr2 g).
Defined.

Definition graph_w_comp_from_gen_alg : graph_w_comp := 
  tpair _ graph_from_gen_alg graph_from_gen_alg_comp.

Definition id_op1 : @id_op graph_w_comp_from_gen_alg := 
  λ c : C, tpair _ (make_dirprod c c) (identity c).

(** This proof should probably be transparent, since otherwise identity does not compute *)

Lemma ess_alg_cat_axioms_from_gen_alg : ess_alg_cat_axioms graph_w_comp_from_gen_alg.
Proof.
  split; [ | split].
  - repeat split.
    + exists id_op1.
      repeat split.
      { unfold id_comp_l_ax. simpl. intros f p.
        destruct f as [[a b] f].
        simpl in *.
        unfold target, source in p. simpl in *.
        unfold precategory_source, precategory_target in p. simpl in *.
        unfold graph_from_gen_alg_comp. simpl.
        apply maponpaths.
        rewrite id_left.
        rewrite idtomor_right.
        apply idpath. }
      { intros f p. destruct f as [[a b] f]. 
        simpl in *.
        unfold target, source in p. simpl in *.
        unfold precategory_source, precategory_target in p. simpl in *.
        unfold graph_from_gen_alg_comp. simpl.        
        apply maponpaths.
        rewrite id_right.
        rewrite idtomor_left. apply idpath. }
  - repeat split.
    intros f g h p q p' q'; simpl.
    unfold graph_from_gen_alg_comp; simpl.
    apply maponpaths; simpl.
    destruct f as [[a b] f].
    destruct g as [[b' c] g].
    destruct h as [[c' d] h].
    simpl in *. unfold target, source in *; simpl in *.
    unfold precategory_source, precategory_target in *; simpl in *. 
    repeat (match goal with | [ H : _ = _ |- _ ] => destruct H end).
    simpl.
    rewrite id_right.
    rewrite idtomor_left.
    rewrite id_right.
    rewrite idtomor_left.
    apply Categories.assoc.
 - split.
   + apply H. 
   + apply isaset_total2. apply isaset_dirprod; try assumption.
     intro x; apply homset_property.
Qed.

End ess_alg_from_gen_alg.

(** * From ess. alg. categories to gen. alg. ones *)

Section gen_alg_from_ess_alg.

Variable C : ess_alg_cat.

Definition hom (a b : C) : UU := ∑ f : mor C, source f = a × target f = b.

Lemma hom_eq (a b : C) (f f' : hom a b) : pr1 f = pr1 f' → f = f'.
Proof.
  intro H.  
  apply subtypePath; try assumption.
  intro x. apply isapropdirprod; apply (isaset_objects C (pr2 C)).
Qed.

Definition composition {a b c : C} (f : hom a b) (g : hom b c) : hom a c.
Proof.
  assert (H : target (pr1 f) = source (pr1 g)).
  { eapply pathscomp0.
    - apply (pr2 (pr2 f)).
    - apply (!pr1 (pr2 g)). }
  exists (comp (pr1 f) (pr1 g) H).
  destruct f as [f [fs ft]].
  destruct g as [g [gs gt]]. simpl in *.
  split. 
  - eapply pathscomp0.  
    + apply comp_source.
    + assumption.
  - eapply pathscomp0.
    + apply comp_target.
    + assumption.
Defined.



Definition composition_assoc (a b c d : C) (f : hom a b) (g : hom b c) (h : hom c d):
  composition f (composition g h) = composition (composition f g) h.
Proof.
  apply hom_eq, assoc.
Qed.

Definition identity (a : C) : hom a a.
Proof.
  exists (id C a).
  split.
  + apply id_source.
  + apply id_target. 
Defined.

Definition precategory_ob_mor_from_ess_alg_cat : precategory_ob_mor.
Proof.
  exists C.
  exact (λ a b, hom a b).
Defined.

Definition precategory_data_from_ess_alg_cat : precategory_data.
Proof.
  exists precategory_ob_mor_from_ess_alg_cat.
  repeat split.
  - apply identity.
  - apply @composition.
Defined.

Lemma is_precategory_precategory_data_from_ess_alg_cat : 
  is_precategory (precategory_data_from_ess_alg_cat).
Proof.
  use make_is_precategory_one_assoc; intros.
  - apply hom_eq. simpl. apply id_comp_l. 
    apply (pr1 (pr2 f)).
  - apply hom_eq, id_comp_r, (pr2 (pr2 f)).
  - apply composition_assoc.
Qed.

Definition precategory_from_ess_alg_cat : precategory := 
  (_,,is_precategory_precategory_data_from_ess_alg_cat).

End gen_alg_from_ess_alg.

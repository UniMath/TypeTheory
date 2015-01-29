
Require Import UniMath.Foundations.hlevel2.hSet.
Require Import UniMath.RezkCompletion.precategories.
Require Import Systems.ess_alg_categories.
Require Import Systems.UnicodeNotations.

Local Notation "a ⇒ b" := (precategory_morphisms a b)(at level 50).
Local Notation "g ∘ f" := (compose f g)(at level 50).

Section ess_alg_from_gen_alg.

Variable C : precategory.
Variable hs : has_homsets C.
Variable H : isaset C.

Print graph.

Lemma idtomor_left (a b : C) (f : a ⇒ b) (e : b = b) : 
   idtomor _ _ e ∘ f = f.
Proof.
  Check proofirrelevance.
  set (H1 := H b b).
  set (H2:=proofirrelevance _ H1 e (idpath _ )).
  rewrite H2. simpl.
  rewrite id_right.
  apply idpath.  
Qed.
Lemma idtomor_right (a b : C) (f : a ⇒ b) (e : a = a) : 
   f ∘ idtomor _ _ e = f.
Proof.
  Check proofirrelevance.
  set (H1 := H a a).
  set (H2:=proofirrelevance _ H1 e (idpath _ )).
  rewrite H2. simpl.
  rewrite id_left.
  apply idpath.  
Qed.



Definition obmor : UU × UU := dirprodpair (ob C) (total_morphisms C).

Definition graph_from_gen_alg : graph.
Proof.   
  exists obmor.
  exists (precategory_source C).
  exact (precategory_target C).
Defined.

Definition graph_from_gen_alg_comp : @comp_op graph_from_gen_alg.
Proof.
  intros f g e.
  exists (dirprodpair (pr1 (pr1 f)) (pr2 (pr1 g))).
  exact (pr2 g ∘ (idtomor _ _ e ∘ pr2 f)).
Defined.

Definition graph_w_comp_from_gen_alg : graph_w_comp := 
  tpair _ graph_from_gen_alg graph_from_gen_alg_comp.

Definition id_op1 : @id_op graph_w_comp_from_gen_alg := 
  λ c : C, tpair _ (dirprodpair c c) (identity c).

(*
Lemma mor_eq (f g : mor graph_from_gen_alg) : f = g.
*)

Lemma ess_alg_cat_axioms_from_gen_alg : ess_alg_cat_axioms graph_w_comp_from_gen_alg.
Proof.
  split.
  - repeat split.
    + exists id_op1.
      repeat split.
      { unfold id_comp_l. simpl. intros f p.
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
   + intros f g h p q p' q'; simpl.
     unfold graph_from_gen_alg_comp; simpl.
     apply maponpaths; simpl.
     destruct f as [[a b] f].
     destruct g as [[b' c] g].
     destruct h as [[c' d] h].
     simpl in *. unfold target, source in *; simpl in *.
     unfold precategory_source, precategory_target in *; simpl in *. 
     subst. simpl.
     rewrite id_right.
     rewrite idtomor_left.
     rewrite id_right.
     rewrite idtomor_left.
     apply precategories.assoc.
   + apply H.
 - apply (isofhleveltotal2 2).
   + apply isofhleveldirprod.
     apply H.
     apply H.
   + intro x. apply hs.
Qed.

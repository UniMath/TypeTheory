
Require Import Systems.UnicodeNotations.


Definition graph := Σ obmor : UU × UU,
    (pr2 obmor -> pr1 obmor) × (pr2 obmor -> pr1 obmor).


Definition objects (X : graph) : UU := pr1 (pr1 X).
Coercion objects : graph >-> UU.
Definition mor (X : graph) : UU := pr2 (pr1 X).
Definition source {X : graph} : mor X -> X := pr1 (pr2 X).
Definition target {X : graph} : mor X -> X := pr2 (pr2 X).

Definition comp_op {X : graph} := ∀ f g : mor X, target f = source g -> mor X.   

Definition graph_w_comp := Σ X, comp_op (X:=X).
Definition graph_from_graph_w_comp (X : graph_w_comp) := pr1 X.
Coercion graph_from_graph_w_comp : graph_w_comp >-> graph.

Definition comp {X : graph_w_comp} : comp_op (X:=X) := pr2 X.


Section axioms.

Context {C : graph_w_comp}.

Definition id_op := C -> mor C.

Variable i : id_op.

Definition id_source := ∀ c : C, source (i c) = c.
Definition id_target := ∀ c : C, target (i c) = c.
Definition id_comp_l := ∀ f : mor C, 
   ∀ p : target (i (source f)) = source f, comp (i (source f)) f  p = f.
Definition id_comp_r := ∀ f : mor C,
   ∀ p : target f = source (i (target f)), comp f (i (target f)) p = f.
Definition comp_source := ∀ f g : mor C, 
    ∀ p : target f = source g, source (comp f g p) = source f.
Definition comp_target := ∀ f g : mor C,
    ∀ p : target f = source g, target (comp f g p) = target g.
Definition assoc := ∀ f g h : mor C, 
    ∀ p : target f = source g, ∀ q : target g = source h,
      ∀ p' : target f = source (comp g h q),
        ∀ q' : target (comp f g p) = source h,
          comp f (comp g h q ) p' = comp (comp f g p) h q' .

Lemma id_comp_left (I : id_comp_l) : ∀ f : mor C, ∀ a : C,
   source f = a → ∀ p : target (i a) = source f, comp (i a) f p = f.
Proof.
  intros f a p.
  rewrite <- p.
  intros.
  apply I.
Qed.

Lemma id_comp_right (I : id_comp_r) : ∀ f : mor C, ∀ a : C,
   target f = a → ∀ p : target f = source (i a), comp f (i a) p = f.
Proof.
  intros f a p.
  rewrite <- p.
  intros. apply I.
Qed.

End axioms.

Definition ess_alg_cat_axioms (C : graph_w_comp) := 
  (Σ i : id_op (C:=C), 
    id_source i × id_target i × id_comp_l i × id_comp_r i) ×
    comp_source (C:=C) × comp_target (C:=C) × assoc (C:=C) × 
    isaset (objects C) × isaset (mor C) .



Lemma isaprop_ess_alg_cat_axioms (C : graph_w_comp) : 
   isaprop (ess_alg_cat_axioms C).
Proof.
  Search ( ( _ -> isofhlevel _ _ ) -> isofhlevel _  _).
  apply isofhlevelsn.
  intro X.
  repeat apply isapropdirprod.
  - apply invproofirrelevance.
    intros i i'.
    destruct i as [i x]. (* [i [[[oi pi] qi] ri]]. *)
    destruct i' as [i' x']. (* [[[oi' pi'] qi'] ri']].*)
    Search ( isaprop _ -> tpair _ _ _ = tpair _ _ _ ).
    apply total2_paths2_second_isaprop.
    + apply funextfun.
      intro a.
      assert (p : target (i a) = source (i' a)).
      { rewrite (pr2 (pr1 (pr1 x))). 
        rewrite (pr1 (pr1 (pr1 x'))).
        reflexivity. }
      destruct x as [[[x1 x2] x3] x4].
      destruct x' as [[[x1' x2'] x3'] x4'].
      transitivity (comp (i a) (i' a) p).      
      { rewrite (id_comp_right i'). 
        - reflexivity.
        - assumption. 
        - apply x2. }
      { rewrite (id_comp_left i).
        - reflexivity. 
        - assumption. 
        - apply x1'. }
   + clear x x'. 
     repeat apply isapropdirprod;
       repeat (apply impred; intro); try apply (pr2 (pr1 X)); try apply (pr2 X).
  - repeat (apply impred; intro).  apply (pr2 (pr1 X)). 
  - repeat (apply impred; intro).  apply (pr2 (pr1 X)). 
  - repeat (apply impred; intro).  apply (pr2 X). 
  - apply isapropisaset.
  - apply isapropisaset.
Qed.

Definition ess_alg_cat := Σ C : graph_w_comp, ess_alg_cat_axioms C.
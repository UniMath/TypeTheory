
(** Categories in essentially algebraic style *)

(** Such a category is given by
    - a type (set) of objects
    - a type (set) of morphisms
    - source and target maps
    - composition (domain defined as pullback)
    - axioms (including "identity morphism" map)
*)

Require Import UniMath.Foundations.Sets.

Unset Universe Checking.

(** * Definition of a [graph] as two types with source and target maps *)

Definition graph := ∑ obmor : UU × UU,
    (pr2 obmor -> pr1 obmor) × (pr2 obmor -> pr1 obmor).


Definition objects (X : graph) : UU := pr1 (pr1 X).
Coercion objects : graph >-> UU.
Definition mor (X : graph) : UU := pr2 (pr1 X).
Definition source {X : graph} : mor X -> X := pr1 (pr2 X).
Definition target {X : graph} : mor X -> X := pr2 (pr2 X).

(** * Definition of a graph with composition *)

Definition comp_op {X : graph} := ∏ f g : mor X, target f = source g -> mor X.   

Definition graph_w_comp := ∑ X, comp_op (X:=X).
Definition graph_from_graph_w_comp (X : graph_w_comp) := pr1 X.
Coercion graph_from_graph_w_comp : graph_w_comp >-> graph.

Definition comp {X : graph_w_comp} : comp_op (X:=X) := pr2 X.

(** Definition of the categorical axioms of a graph with composition *)

Section axioms.

Context {C : graph_w_comp}.

Definition id_op := C -> mor C.

Variable i : id_op.

Definition id_source_ax := ∏ c : C, source (i c) = c.
Definition id_target_ax := ∏ c : C, target (i c) = c.
Definition id_comp_l_ax := ∏ f : mor C, 
   ∏ p : target (i (source f)) = source f, comp (i (source f)) f  p = f.
Definition id_comp_r_ax := ∏ f : mor C,
   ∏ p : target f = source (i (target f)), comp f (i (target f)) p = f.
Definition comp_source_ax := ∏ f g : mor C, 
    ∏ p : target f = source g, source (comp f g p) = source f.
Definition comp_target_ax := ∏ f g : mor C,
    ∏ p : target f = source g, target (comp f g p) = target g.
Definition assoc_ax := ∏ f g h : mor C, 
    ∏ p : target f = source g, ∏ q : target g = source h,
      ∏ p' : target f = source (comp g h q),
        ∏ q' : target (comp f g p) = source h,
          comp f (comp g h q ) p' = comp (comp f g p) h q' .

Lemma id_comp_left (I : id_comp_l_ax) : ∏ f : mor C, ∏ a : C,
   source f = a → ∏ p : target (i a) = source f, comp (i a) f p = f.
Proof.
  intros f a p.
  rewrite <- p.
  intros.
  apply I.
Qed.

Lemma id_comp_right (I : id_comp_r_ax) : ∏ f : mor C, ∏ a : C,
   target f = a → ∏ p : target f = source (i a), comp f (i a) p = f.
Proof.
  intros f a p.
  rewrite <- p.
  intros. apply I.
Qed.

End axioms.

Definition ess_alg_cat_axioms (C : graph_w_comp)
:=
    (∑ i : id_op (C:=C), 
      id_source_ax i × id_target_ax i × id_comp_l_ax i × id_comp_r_ax i)
  ×
    (comp_source_ax (C:=C) × comp_target_ax (C:=C) × assoc_ax (C:=C))
  × 
    (isaset (objects C) × isaset (mor C)).

Definition isaset_objects (C : graph_w_comp) (T : ess_alg_cat_axioms C) : 
   isaset (objects C) := (pr1 (pr2 (pr2 T))).

Definition isaset_mor (C : graph_w_comp) (T : ess_alg_cat_axioms C) : 
   isaset (mor C) := (pr2 (pr2 (pr2 T))).


(** ** The categorical axioms are indeed a property *)


Lemma isaprop_ess_alg_cat_axioms (C : graph_w_comp) : 
   isaprop (ess_alg_cat_axioms C).
Proof.
  apply isofhlevelsn.
  intro X.
  repeat apply isapropdirprod.
  - apply invproofirrelevance.
    intros i i'.
    destruct i as [i x]. 
    destruct i' as [i' x'].
    apply subtypePairEquality'.
    + apply funextfun.
      intro a.
      assert (p : target (i a) = source (i' a)).
      { rewrite (pr1 (pr2 x)). 
        rewrite (pr1 x').
        reflexivity. }
      destruct x as [x1 [x2 [x3 x4]]].
      destruct x' as [x1' [x2' [x3' x4']]].
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
       repeat (apply impred; intro);  
            try apply isaset_objects; try apply isaset_mor; assumption. 
  - repeat (apply impred; intro).  apply isaset_objects; assumption.
  - repeat (apply impred; intro).  apply isaset_objects; assumption. 
  - repeat (apply impred; intro).  apply isaset_mor; assumption. 
  - apply isapropisaset.
  - apply isapropisaset.
Qed.

(** * A category in essentially algebraic style is a graph with composition 
      satisfying the categorical axioms *)

Definition ess_alg_cat := ∑ C : graph_w_comp, ess_alg_cat_axioms C.

Definition graph_w_comp_from_ess_alg_cat (C : ess_alg_cat) : graph_w_comp := pr1 C.
Coercion graph_w_comp_from_ess_alg_cat : ess_alg_cat >-> graph_w_comp.

Section access_functions.

Variable C : ess_alg_cat.

Definition id : id_op := (pr1 (pr1 (pr2 C))).

Definition id_source : ∏ c : C, source (id c) = c.
Proof.
  exact (pr1 (pr2 (pr1 (pr2 C)))).
Qed.

Definition id_target : ∏ c : C, target (id c) = c.
Proof.
  exact (pr1 (pr2 (pr2 (pr1 (pr2 C))))).
Qed.

Definition id_comp_l :  ∏ f : mor C, ∏ a : C,
   source f = a → ∏ p : target (id a) = source f, comp (id a) f p = f.
Proof.
  intros.
  apply id_comp_left.
  exact (pr1 (pr2 (pr2 (pr2 (pr1 (pr2 C)))))).
  assumption.
Qed.

Definition id_comp_r : ∏ f : mor C, ∏ a : C,
   target f = a → ∏ p : target f = source (id a), comp f (id a) p = f.
Proof.
  intros.
  apply id_comp_right.
  exact (pr2 (pr2 (pr2 (pr2 (pr1 (pr2 C)))))).
  assumption.
Qed.

(* TODO: update access functions (originally defined w.r.t. a different association of the sigma-type in the definition). 
Definition ess_alg_cat_axioms (C : graph_w_comp) := 
  (∑ i : id_op (C:=C), 
    id_source_ax i × id_target_ax i × id_comp_l_ax i × id_comp_r_ax i) ×
    comp_source_ax (C:=C) × comp_target_ax (C:=C) × assoc_ax (C:=C) × 
    isaset (objects C) × isaset (mor C) .
*)

Definition comp_source : ∏ f g : mor C, 
    ∏ p : target f = source g, source (comp f g p) = source f.
Proof.
  exact (pr1 (pr1 (pr2 (pr2 C)))). 
Qed.

Definition comp_target : ∏ f g : mor C,
    ∏ p : target f = source g, target (comp f g p) = target g.
Proof.
  exact (pr1 (pr2 (pr1 (pr2 (pr2 C))))). 
Qed.

Definition assoc : ∏ f g h : mor C, 
    ∏ p : target f = source g, ∏ q : target g = source h,
      ∏ p' : target f = source (comp g h q),
        ∏ q' : target (comp f g p) = source h,
          comp f (comp g h q ) p' = comp (comp f g p) h q' .
Proof.
  exact (pr2 (pr2 (pr1 (pr2 (pr2 C))))).
Qed.

End access_functions.

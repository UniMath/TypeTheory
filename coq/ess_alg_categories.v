
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

Variable C : graph_w_comp.

Definition id_op := C -> mor C.

Variable i : id_op.

Definition id_source := ∀ c : C, source (i c) = c.
Definition id_target := ∀ c : C, target (i c) = c.
Definition id_comp_l := ∀ f : mor C, 
   ∀ p : target (i (source f)) = source f, comp (i (source f)) f  p = f.
Definition id_comp_r := ∀ f : mor C,
   ∀ p : source (i (target f)) = target f, comp f (i (target f)) (!p) = f.
Definition comp_source := ∀ f g : mor C, 
    ∀ p : target f = source g, source (comp f g p) = source f.
Definition comp_target := ∀ f g : mor C,
    ∀ p : target f = source g, target (comp f g p) = target g.
Definition assoc := ∀ f g h : mor C, 
    ∀ p : target f = source g, ∀ q : target g = source h,
      ∀ p' : target f = source (comp g h q),
        ∀ q' : target (comp f g p) = source h,
          comp f (comp g h q ) p' = comp (comp f g p) h q' .

End axioms.

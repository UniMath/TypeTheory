
Require Export Systems.UnicodeNotations.
Require Export UniMath.Foundations.hlevel2.hSet.
Require Export UniMath.RezkCompletion.precategories.
Require Export UniMath.RezkCompletion.limits.pullbacks.

Local Notation "a ⇒ b" := (precategory_morphisms a b)(at level 50).
  (* \=> in Agda input method *)
Local Notation "g ∙ f" := (compose f g)(at level 50).
  (* \. in Agda input method *)

Section Prelims.

(* TODO: move to limits.pullbacks *)
Global Arguments isPullback [C a b c d] f g p1 p2 H.

End Prelims.

(* Comprehension pre-categories:

an elementary definition of a structure analogous to (full) comprehension categories, without
any saturatedness/univalence assumptions.

  This form of the definition is due to VV, and is v close to the *type-categories*
of Andy Pitts, *Categorical Logic*, 2000, Def. 
https://synrc.com/publications/cat/Category%20Theory/Categorical%20Logic/Pitts%20A.M.%20Categorical%20Logic.pdf
which are just the split form of the structure.

  NOTE: the sigmas are currently nested in the most naïve way; if performance issues arise
later, re-associating to decrease the depth may help? *)
Definition comp_precat_structure (C : precategory) :=
  Σ (ty : C -> Type)
    (ext : ∀ c, ty c -> C)
    (dpr : ∀ c a, ext c a ⇒ c)
    (reind : ∀ c (a : ty c) c' (f : c' ⇒ c), ty c')
    (q : ∀ c (a : ty c) c' (f : c' ⇒ c), ext c' (reind _ a _ f) ⇒ ext c a)
    (dpr_q : ∀ c (a : ty c) c' (f : c' ⇒ c), 
      (dpr _ a) ∙ (q _ a _ f) = f ∙ dpr _ (reind _ a _ f)),
    ∀ c (a : ty c) c' (f : c' ⇒ c),
      isPullback (dpr _ a) f (q _ a _ f) (dpr _ (reind _ a _ f)) (dpr_q _ a _ f).

Definition comp_precat : UU := Σ C : precategory, comp_precat_structure C.

Definition precat_from_comp_precat (C : comp_precat) : precategory := pr1 C.
Coercion precat_from_comp_precat : comp_precat >-> precategory.

(* Since the following functions may eventually apply to comprehension categories
just as well as precategories, we drop the [pre] in their names. *)

Definition ty_comp_cat (C : comp_precat) : C -> Type := pr1 (pr2 C).
Coercion ty_comp_cat : comp_precat >-> Funclass.

Definition ext_comp_cat {C : comp_precat} (c : C) (a : C c) : C
  := pr1 (pr2 (pr2 C)) c a.
Local Notation "c ; a" := (ext_comp_cat c a) (at level 40, left associativity).
(* NOTE: not sure what levels we want,
  but the level of this should be below the level of reindexing "A[f]",
  which should in turn be below the level of composition "f∙g",
  to allow expressions like "c;a[f∙g]". *)

Time Definition dpr_comp_cat {C : comp_precat} {c : C} (a : C c) : (c;a) ⇒ c 
  := pr1 (pr2 (pr2 (pr2 C))) c a.

Time Definition reind_comp_cat {C : comp_precat} {c } (a : C c) {c'} (f : c' ⇒ c) : C c'
  := pr1 (pr2 (pr2 (pr2 (pr2 C)))) _ a _ f.
Local Notation "a [ f ]" := (reind_comp_cat a f) (at level 45, left associativity).

Time Definition q_comp_cat {C : comp_precat} {c } (a : C c) {c'} (f : c' ⇒ c)
  : (c' ; (a[f]))  ⇒  (c ; a) 
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 C))))) _ a _ f.

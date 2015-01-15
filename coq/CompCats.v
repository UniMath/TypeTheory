
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

  This form of the definition is due to VV, and is very close to the *type-categories*
of Andy Pitts, *Categorical Logic*, 2000, Def. 
https://synrc.com/publications/cat/Category%20Theory/Categorical%20Logic/Pitts%20A.M.%20Categorical%20Logic.pdf
which are just the split form of the structure. 

  In order to avoid the nested sigma-types getting too deep, we split up the structure into two stages: [comp_precat_structure1] and [comp_precate_structure2]. *)
Section Comp_Precats.

Definition comp_precat_structure1 (C : precategory) :=
  Σ (ty : C -> Type)
    (ext : ∀ c, ty c -> C),
      ∀ c (a : ty c) c' (f : c' ⇒ c), ty c'.

Definition comp_precat1 := Σ (C : precategory), comp_precat_structure1 C.

Definition precat_from_comp_precat1 (C : comp_precat1) : precategory := pr1 C.
Coercion precat_from_comp_precat1 : comp_precat1 >-> precategory.

Definition ty_comp_cat1 (C : comp_precat1) : C -> Type := pr1 (pr2 C).
Coercion ty_comp_cat1 : comp_precat1 >-> Funclass.

Definition ext_comp_cat1 {C : comp_precat1}
  (c : C) (a : C c) : C
   := pr1 (pr2 (pr2 C)) c a.
Local Notation "c ; a" := (ext_comp_cat1 c a) (at level 45, left associativity).

(* NOTE: not sure what levels we want,
  but the level of this should be above the level of reindexing "A[f]",
  which should in turn be above the level of composition "f∙g",
  to allow expressions like "c;a[f∙g]". *)

Definition reind_comp_cat1 {C : comp_precat1}
  {c } (a : C c) {c'} (f : c' ⇒ c) : C c'
  := pr2 (pr2 (pr2 C)) c a c' f.
Local Notation "a [ f ]" := (reind_comp_cat1 a f) (at level 40).

Definition comp_precat_structure2 (C : comp_precat1) :=
  Σ (dpr : ∀ c (a : C c), c;a ⇒ c)
    (q : ∀ c (a : C c) c' (f : c' ⇒ c), (c';a[f]) ⇒ c;a )
    (dpr_q : ∀ c (a : C c) c' (f : c' ⇒ c), 
      (dpr _ a) ∙ (q _ a _ f) = f ∙ dpr _ (a [f])),
    ∀ c (a : C c) c' (f : c' ⇒ c),
      isPullback (dpr _ a) f (q _ a _ f) (dpr _ (a [f])) (dpr_q _ a _ f).

Definition comp_precat := Σ C : comp_precat1, comp_precat_structure2 C.

Definition comp_precat1_from_comp_precat (C : comp_precat) : comp_precat1 := pr1 C.
Coercion comp_precat1_from_comp_precat : comp_precat >-> comp_precat1.

(* Since the following functions may eventually apply to comprehension categories
just as well as comprehension precategories, we drop the [pre] in their names. *)

Definition dpr_comp_cat  {C : comp_precat}
  {c : C} (a : C c) : (c;a) ⇒ c
  := pr1 (pr2 C) c a.

Definition q_comp_cat {C : comp_precat} {c } (a : C c) {c'} (f : c' ⇒ c)
  : (c' ; (a[f]))  ⇒  (c ; a) 
:=
  pr1 (pr2 (pr2 C)) _ a _ f.

Definition dpr_q_comp_cat {C : comp_precat} {c } (a : C c) {c'} (f : c' ⇒ c)
  : (dpr_comp_cat a) ∙ (q_comp_cat a f) = f ∙ dpr_comp_cat (a [f])
:=
  pr1 (pr2 (pr2 (pr2 C))) _ a _ f.

Definition reind_pb_cat {C : comp_precat} {c } (a : C c) {c'} (f : c' ⇒ c)
  : isPullback (dpr_comp_cat a) f (q_comp_cat a f) (dpr_comp_cat (a [f]))
      (dpr_q_comp_cat a f)
:=
  pr2 (pr2 (pr2 (pr2 C))) _ a _ f.

Definition is_split_comp_precat (C : comp_precat)
  := (∀ c:C, isaset (C c))
     × (Σ (reind_id : ∀ c (a : C c), a [identity c] = a),
         ∀ c (a : C c), q_comp_cat a (identity c)
                        = idtoiso (maponpaths (fun b => c;b) (reind_id c a)))
     × (Σ (reind_comp : ∀ c (a : C c) c' (f : c' ⇒ c) c'' (g : c'' ⇒ c'),
                         a [f∙g] = a[f][g]),
          ∀ c (a : C c) c' (f : c' ⇒ c) c'' (g : c'' ⇒ c'),
            q_comp_cat a (f ∙ g)
            = q_comp_cat a f ∙ q_comp_cat (a[f]) g
               ∙ idtoiso (maponpaths (fun b => c'';b) (reind_comp _ a _ f _ g))).

Definition split_comp_precat := Σ C, (is_split_comp_precat C).

Definition comp_precat_of_split (C : split_comp_precat) := pr1 C.

(* TODO: define access functions for other components of [is_split_…]. *)
 
End Comp_Precats.


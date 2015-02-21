
Require Export Systems.UnicodeNotations.
Require Export UniMath.Foundations.hlevel2.hSet.
Require Export UniMath.RezkCompletion.precategories.
Require Export UniMath.RezkCompletion.limits.pullbacks.

(* Suppress these preliminaries in the Coqdoc documentation: *)
(* begin hide *)
Section Prelims.

(* TODO: move to limits.pullbacks *)
Global Arguments isPullback [C a b c d] f g p1 p2 H.

End Prelims.
(* end hide *)

(** * Comprehension pre-categories

We give here an elementary definition “comprehension pre-categories”: a structure analogous to (full) comprehension categories, without any saturatedness/univalence assumptions on the underlying category.

  This form of the definition is close to the _type-categories_ of Andy Pitts, _Categorical Logic_, 2000, Def. 6.3.3:
https://synrc.com/publications/cat/Category%20Theory/Categorical%20Logic/Pitts%20A.M.%20Categorical%20Logic.pdf#page=73
That definition includes two _strictness conditions_; we follow van den Berg and Garner, _Topological and simplicial models…_ http://arxiv.org/abs/1007.4638, Def 2.2.1, in separating these out from the rest of the definition.

  An element [comp_precat], as we define it below, is thus exactly a type-category according to the definition of van den Berg and Garner; and an element of [split_comp_precat] is a split type-category according to van den Berg and Garner, or a plain type-category in the sense of Pitts (modulo, in either case, the question of equality on objects of the category).
 
  NOTE: maybe we should be calling these type-pre-cats throughout, since our form of the definition is really closer to existing definitions of type-categories than of comprehension categories, though we believe it is also equivalent to the latter?

  In order to avoid the nested sigma-types getting too deep, we split up the structure into two stages: [comp_precat_structure1] and [comp_precate_structure2]. *)

Module Record_Preview.
(** For technical reasons, we prefer not to use record types in the development.
However, a definition as a record type is much more readable — so we give that here, for documentation purposes only, wrapped in a module to keep it out of the global namespace. *)

Record comp_precat_record : Type := {
  C : precategory ;
  ty : C -> Type ;
  ext : ∀ c, ty c -> C ;
  dpr : ∀ c (a : ty c), (ext c a) ⇒ c ;
  reind : ∀ c (a : ty c) c' (f : c' ⇒ c), ty c';
  q : ∀ c (a : ty c) c' (f : c' ⇒ c),
          (ext c' (reind _ a _ f) ⇒ ext c a) ;
  dpr_q : ∀ c (a : ty c) c' (f : c' ⇒ c), 
          (q _ a _ f) ;; (dpr _ a) = (dpr _ (reind _ a _ f)) ;; f ;
  reind_pb : ∀ c (a : ty c) c' (f : c' ⇒ c),
      isPullback _ _ _ _ (dpr_q _ a _ f)
}.

(** Here we see the components of the definition of a [comp_precat].  Under the names of their actual versions below, they are:

- [precat_of_comp_precat1] (a coercion): the underlying pre-ategory;
- [ty_comp_cat] (also a coercion): for each object [Γ], a type of “types over [Γ]”, written [C Γ];
- [ext_comp_cat]: a context extension operation, written [Γ ◂ A];
- [dpr_comp_cat]: dependent projections from context extensions; 
- [reind_comp_cat]: a reindexing operation on types, written [A[f]] or [f^*A];
- [q_comp_cat]: for [f : Γ' → Γ], and [a : C Γ], a map [ (Γ' ◂ f^* A) ⇒ (Γ ◂ A) ]; can be seen as the extension of a context morphism by a variable of a new type;
- [dpr_q_comp_cat]: reindexing commutes with dependent projections;
- [reind_pb_comp_cat]: the commutative square thus formed is a pullback. *)

End Record_Preview.


(** For the actual definition, we use iterated Σ-types.  As usual, to avoid severe performance issues with these, we have to split up the definition into several steps: [comp_precat_structure1] with the first few components, and [comp_precat_structure2] the rest.  *)
Section Comp_Precats.

Definition comp_precat_structure1 (C : precategory) :=
  Σ (ty : C -> Type)
    (ext : ∀ c, ty c -> C),
      ∀ c (a : ty c) c' (f : c' ⇒ c), ty c'.

Definition comp_precat1 := Σ (C : precategory), comp_precat_structure1 C.

Definition precat_from_comp_precat1 (C : comp_precat1) : precategory := pr1 C.
Coercion precat_from_comp_precat1 : comp_precat1 >-> precategory.

(** Since the various access functions should eventually apply directly to comprehension categories
as well as comprehension precategories (via coercion from the former to the latter), we drop the [pre] in their names. *)
Definition ty_comp_cat (C : comp_precat1) : C -> Type := pr1 (pr2 C).
Coercion ty_comp_cat : comp_precat1 >-> Funclass.

Definition ext_comp_cat {C : comp_precat1}
  (c : C) (a : C c) : C
   := pr1 (pr2 (pr2 C)) c a.
Notation "c ◂ a" := (ext_comp_cat c a) (at level 45, left associativity).
  (* \tb in Agda input method *)
(* NOTE: not sure what levels we want here,
  but the level of this should be above the level of reindexing "A[f]",
  which should in turn be above the level of composition "g;;f",
  to allow expressions like "c◂a[g;;f]". *)

Definition reind_comp_cat {C : comp_precat1}
  {c } (a : C c) {c'} (f : c' ⇒ c) : C c'
  := pr2 (pr2 (pr2 C)) c a c' f.
Notation "a [ f ]" := (reind_comp_cat a f) (at level 40).

Definition comp_precat_structure2 (C : comp_precat1) :=
  Σ (dpr : ∀ c (a : C c), c◂a ⇒ c)
    (q : ∀ c (a : C c) c' (f : c' ⇒ c), (c'◂a[f]) ⇒ c◂a )
    (dpr_q : ∀ c (a : C c) c' (f : c' ⇒ c), 
      (q _ a _ f) ;; (dpr _ a) = (dpr _ (a [f])) ;; f),
    ∀ c (a : C c) c' (f : c' ⇒ c),
      isPullback (dpr _ a) f (q _ a _ f) (dpr _ (a [f])) (dpr_q _ a _ f).
(* TODO: change name [dpr_q] to [q_dpr] throughout, now that composition is diagrammatic order? *)

Definition comp_precat := Σ C : comp_precat1, comp_precat_structure2 C.

Definition comp_precat1_from_comp_precat (C : comp_precat) : comp_precat1 := pr1 C.
Coercion comp_precat1_from_comp_precat : comp_precat >-> comp_precat1.

Definition dpr_comp_cat  {C : comp_precat}
  {c : C} (a : C c) : (c◂a) ⇒ c
  := pr1 (pr2 C) c a.

Definition q_comp_cat {C : comp_precat} {c } (a : C c) {c'} (f : c' ⇒ c)
  : (c' ◂ (a[f]))  ⇒  (c ◂ a) 
:=
  pr1 (pr2 (pr2 C)) _ a _ f.

Definition dpr_q_comp_cat {C : comp_precat} {c } (a : C c) {c'} (f : c' ⇒ c)
  : (q_comp_cat a f) ;; (dpr_comp_cat a) = (dpr_comp_cat (a [f])) ;; f
:=
  pr1 (pr2 (pr2 (pr2 C))) _ a _ f.

Definition reind_pb_comp_cat {C : comp_precat} {c } (a : C c) {c'} (f : c' ⇒ c)
  : isPullback (dpr_comp_cat a) f (q_comp_cat a f) (dpr_comp_cat (a [f]))
      (dpr_q_comp_cat a f)
:=
  pr2 (pr2 (pr2 (pr2 C))) _ a _ f.

(** A comprehension precategory [C] is _split_ if each collection of types [C Γ] is a set, reindexing is strictly functorial, and the [q] maps satisfy the evident functoriality axioms *) 
Definition is_split_comp_cat (C : comp_precat)
  := (∀ c:C, isaset (C c))
     × (Σ (reind_id : ∀ c (a : C c), a [identity c] = a),
         ∀ c (a : C c), q_comp_cat a (identity c)
                        = idtoiso (maponpaths (fun b => c◂b) (reind_id c a)))
     × (Σ (reind_comp : ∀ c (a : C c) c' (f : c' ⇒ c) c'' (g : c'' ⇒ c'),
                         a [g;;f] = a[f][g]),
          ∀ c (a : C c) c' (f : c' ⇒ c) c'' (g : c'' ⇒ c'),
            q_comp_cat a (g ;; f)
            =  idtoiso (maponpaths (fun b => c''◂b) (reind_comp _ a _ f _ g))
               ;; q_comp_cat (a[f]) g
               ;; q_comp_cat a f).

Definition split_comp_precat := Σ C, (is_split_comp_cat C).

Definition comp_precat_of_split (C : split_comp_precat) := pr1 C.

(* TODO: define access functions for other components of [is_split_…]. *)
 
End Comp_Precats.

(* Globalising notations defined within section above: *)
Notation "c ◂ a" := (ext_comp_cat c a) (at level 45, left associativity).
(* Temporarily suppressed due to levels clash with [cwf]. TODO: fix clash! *)
Notation "a [ f ]" := (reind_comp_cat a f) (at level 40).

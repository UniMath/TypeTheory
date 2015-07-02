
(** 

 Ahrens, Lumsdaine, Voevodsky, 2015

Contents:

  - Definition of Comprehension Category
  - A few convenience lemmas

*)

Require Export Systems.UnicodeNotations.
Require Export UniMath.Foundations.hlevel2.hSet.
Require Export UniMath.RezkCompletion.precategories.
Require Export UniMath.RezkCompletion.limits.pullbacks.

Section Prelims.

(* TODO: move to limits.pullbacks *)
Global Arguments isPullback [C a b c d] f g p1 p2 H.

End Prelims.

(** * Comprehension pre-categories

We give here an elementary definition “comprehension pre-categories”: 
a structure analogous to (full) comprehension categories, 
without any saturatedness/univalence assumptions on the underlying category.

  This form of the definition is close to the _type-categories_ of Andy Pitts, _Categorical Logic_, 2000, Def. 6.3.3
#(<a href="https://synrc.com/publications/cat/Category%%20Theory/Categorical%%20Logic/Pitts%%20A.M.%%20Categorical%%20Logic.pdf##page=73">link</a>).#
However, that definition includes two _strictness conditions_; 
we follow van den Berg and Garner, _Topological and simplicial models_, Def 2.2.1 #(<a href="http://arxiv.org/abs/1007.4638">arXiv</a>)# 
in separating these out from the rest of the definition.

 An element [comp_precat], as we define it below, is thus exactly a type-category according 
to the definition of van den Berg and Garner; and an element of [split_comp_precat] is a split type-category 
according to van den Berg and Garner, or a plain type-category in the sense of Pitts 
(modulo, in either case, the question of equality on objects of the category).
 
  NOTE: maybe we should be calling these type-pre-cats throughout, since our form of the definition 
is really closer to existing definitions of type-categories than of comprehension categories, 
though we believe it is also equivalent to the latter?

  In order to avoid the nested sigma-types getting too deep, 
we split up the structure into two stages: [comp_precat_structure1] and [comp_precate_structure2]. *)

(** * A "preview" of the definition *)

Module Record_Preview.
(** For technical reasons, we prefer not to use record types in the development.
However, a definition as a record type is much more readable — so we give that here, 
for documentation purposes only, wrapped in a module to keep it out of the global namespace. *)


Reserved Notation "C ⟨ Γ ⟩" (at level 60).
Reserved Notation "Γ ◂ A" (at level 45).
Reserved Notation "A [ f ]" (at level 40).
Reserved Notation "'π' A" (at level 5).

Record comp_precat_record : Type := {
  C : precategory ;
  ty : C -> Type                                        where "C ⟨ Γ ⟩" := (ty Γ);
  ext : ∀ Γ, C⟨Γ⟩ -> C                                  where "Γ ◂ A" := (ext Γ A);
  dpr : ∀ Γ (A : C⟨Γ⟩), Γ ◂ A ⇒ Γ                       where "'π' A" := (dpr _ A);
  reind : ∀ Γ (A : C⟨Γ⟩) Γ' (f : Γ' ⇒ Γ), C⟨Γ'⟩         where "A [ f ]" := (reind _ A _ f)  ;
  q : ∀ {Γ} (A : ty Γ) {Γ'} (f : Γ' ⇒ Γ),
          (Γ' ◂ (A [ f ]) ⇒ Γ ◂ A) ;
  dpr_q : ∀ Γ (A : C⟨Γ⟩) Γ' (f : Γ' ⇒ Γ), 
          (q A f) ;; (π A) = (π (A[f])) ;; f ;
  reind_pb : ∀ Γ (A : ty Γ) Γ' (f : Γ' ⇒ Γ),
      isPullback _ _ _ _ (dpr_q _ A _ f)
}.

(** Here we see the components of the definition of a [comp_precat].  Under the names of their actual versions below, they are:

- [precat_of_comp_precat1] (a coercion): the underlying pre-ategory;
- [ty_comp_cat] (also a coercion): for each object [Γ], a type of “types over [Γ]”, written [C Γ];
- [ext_comp_cat]: a context extension operation, written [Γ ◂ A];
- [dpr_comp_cat]: dependent projections from context extensions; 
- [reind_comp_cat]: a reindexing operation on types, written [A[f]] or [f^*A];
- [q_comp_cat]: for [f : Γ' → Γ], and [A : C Γ], a map [ (Γ' ◂ f^* A) ⇒ (Γ ◂ A) ]; can be seen as the extension of a context morphism by a variable of a new type;
- [dpr_q_comp_cat]: reindexing commutes with dependent projections;
- [reind_pb_comp_cat]: the commutative square thus formed is a pullback. *)

End Record_Preview.


(** For the actual definition, we use iterated Σ-types.  
As usual, to avoid severe performance issues with these, 
we have to split up the definition into several steps: 
[comp_precat_structure1] with the first few components, and [comp_precat_structure2] the rest.  *)


(** * Types, reindexing and context extension *)

Section Comp_Precats.

Definition comp_cat_struct1 (C : precategory) :=
  Σ (ty : C -> UU)
    (ext : ∀ Γ, ty Γ -> C),
      ∀ Γ (A : ty Γ) Γ' (f : Γ' ⇒ Γ), ty Γ'.
(*
Definition comp_precat1 := Σ (C : precategory), comp_precat_structure1 C.

Definition precat_from_comp_precat1 (C : comp_precat1) : precategory := pr1 C.
Coercion precat_from_comp_precat1 : comp_precat1 >-> precategory.
*)
(** Since the various access functions should eventually apply directly to comprehension categories
as well as comprehension precategories (via coercion from the former to the latter), we drop the [pre] in their names. *)

Definition ty_comp_cat {CC : precategory} (C : comp_cat_struct1 CC) : CC -> UU 
 := pr1  C.

Coercion ty_comp_cat : comp_cat_struct1 >-> Funclass.

Definition ext_comp_cat {CC : precategory} {C : comp_cat_struct1 CC} 
  (Γ : CC) (A : C Γ) : CC
   := pr1 (pr2  C) Γ A.
Notation "Γ ◂ A" := (ext_comp_cat Γ A) (at level 45, left associativity).
  (* \tb in Agda input method *)
(* NOTE: not sure what levels we want here,
  but the level of this should be above the level of reindexing "A[f]",
  which should in turn be above the level of composition "g;;f",
  to allow expressions like "c◂a[g;;f]". *)

Definition reind_comp_cat {CC : precategory} {C : comp_cat_struct1 CC}
  {Γ : CC} (A : C Γ) {Γ'} (f : Γ' ⇒ Γ) : C Γ'
  := pr2 (pr2 C) Γ A Γ' f.
Notation "A [ f ]" := (reind_comp_cat A f) (at level 40).

(** * Pullback of dependent projections *)

Definition comp_cat_struct2 {CC : precategory} (C : comp_cat_struct1 CC) :=
  Σ (dpr : ∀ Γ (A : C Γ), Γ◂A ⇒ Γ)
    (q : ∀ Γ (A : C Γ) Γ' (f : Γ' ⇒ Γ), (Γ'◂A[f]) ⇒ Γ◂A )
    (dpr_q : ∀ Γ (A : C Γ) Γ' (f : Γ' ⇒ Γ), 
      (q _ A _ f) ;; (dpr _ A) = (dpr _ (A[f])) ;; f),
    ∀ Γ (A : C Γ) Γ' (f : Γ' ⇒ Γ),
      isPullback (dpr _ A) f (q _ A _ f) (dpr _ (A[f])) (dpr_q _ A _ f).
(* TODO: change name [dpr_q] to [q_dpr] throughout, now that composition is diagrammatic order? *)

Definition comp_cat_struct (CC : precategory) 
  := Σ C : comp_cat_struct1 CC , comp_cat_struct2 C.

Definition comp_precat1_from_comp_precat (CC : precategory)(C : comp_cat_struct CC) 
  : comp_cat_struct1 _  := pr1 C.
Coercion comp_precat1_from_comp_precat : comp_cat_struct >-> comp_cat_struct1.

Definition dpr_comp_cat {CC : precategory}{C : comp_cat_struct CC} {Γ} (A : C Γ)
  : (Γ◂A) ⇒ Γ
:= pr1 (pr2 C) Γ A.

Definition q_comp_cat {CC : precategory} {C : comp_cat_struct CC} {Γ} (A : C Γ) {Γ'} (f : Γ' ⇒ Γ)
  : (Γ' ◂ A[f]) ⇒ (Γ ◂ A) 
:=
  pr1 (pr2 (pr2 C)) _ A _ f.

Definition dpr_q_comp_cat {CC : precategory} {C : comp_cat_struct CC} {Γ} (A : C Γ) {Γ'} (f : Γ' ⇒ Γ)
  : (q_comp_cat A f) ;; (dpr_comp_cat A) = (dpr_comp_cat (A[f])) ;; f
:=
  pr1 (pr2 (pr2 (pr2 C))) _ A _ f.

Definition reind_pb_comp_cat {CC : precategory} {C : comp_cat_struct CC} {Γ} (A : C Γ) {Γ'} (f : Γ' ⇒ Γ)
  : isPullback (dpr_comp_cat A) f (q_comp_cat A f) (dpr_comp_cat (A[f]))
      (dpr_q_comp_cat A f)
:=
  pr2 (pr2 (pr2 (pr2 C))) _ A _ f.

(** * Type-saturation *)

Definition is_type_saturated_comp_cat {CC : precategory} (C : comp_cat_struct CC) : UU
  := ∀ Γ, isincl (λ A : C Γ, tpair (λ X, X ⇒ Γ) (Γ ◂ A) (dpr_comp_cat A)).


(** * Splitness *)

(** A comprehension precategory [C] is _split_ if each collection of types [C Γ] is a set, reindexing is strictly functorial, and the [q] maps satisfy the evident functoriality axioms *) 
Definition is_split_comp_cat {CC : precategory} (C : comp_cat_struct CC)
  := (∀ Γ:CC, isaset (C Γ))
     × (Σ (reind_id : ∀ Γ (A : C Γ), A [identity Γ] = A),
         ∀ Γ (A : C Γ), q_comp_cat A (identity Γ)
                        = idtoiso (maponpaths (fun b => Γ◂b) (reind_id Γ A)))
     × (Σ (reind_comp : ∀ Γ (A : C Γ) Γ' (f : Γ' ⇒ Γ) Γ'' (g : Γ'' ⇒ Γ'),
                         A [g;;f] = A[f][g]),
          ∀ Γ (A : C Γ) Γ' (f : Γ' ⇒ Γ) Γ'' (g : Γ'' ⇒ Γ'),
            q_comp_cat A (g ;; f)
            =  idtoiso (maponpaths (fun b => Γ''◂b) (reind_comp _ A _ f _ g))
               ;; q_comp_cat (A[f]) g
               ;; q_comp_cat A f).

Lemma isaprop_is_split_comp_cat (CC : precategory) (hs : has_homsets CC)
       (C : comp_cat_struct CC) : isaprop (is_split_comp_cat C).
Proof.
  repeat (apply isofhleveltotal2).
  - apply impred; intro; apply isapropisaset.
  - intro H; apply (isofhleveltotal2).
    + repeat (apply impred; intro). apply H.
    + intros; repeat (apply impred; intro); apply hs.
  - intro H. apply isofhleveltotal2.
    + repeat (apply impred; intro); apply (pr1 H).
    + intros; repeat (apply impred; intro); apply hs.
Qed.

Definition split_comp_struct (CC : precategory) : UU 
  := Σ C : comp_cat_struct CC, is_split_comp_cat C.

Coercion comp_cat_from_split_comp (CC : precategory) (C : split_comp_struct CC) 
  : comp_cat_struct _ 
  := pr1 C.

Coercion is_split_from_split_comp (CC : precategory) (C : split_comp_struct CC)
  : is_split_comp_cat C
  := pr2 C.

Definition reind_comp_comp_cat {CC : precategory} {C : comp_cat_struct CC}
           (H : is_split_comp_cat C)
  : ∀ Γ (A : C Γ) Γ' (f : Γ' ⇒ Γ) Γ'' (g : Γ'' ⇒ Γ'),
      A [g;;f] = A[f][g]
  := pr1 (pr2 H).                

Definition q_comp_comp_cat {CC : precategory} {C : split_comp_struct CC}
  : ∀ Γ (A : C Γ) Γ' (f : Γ' ⇒ Γ) Γ'' (g : Γ'' ⇒ Γ'),
            q_comp_cat A (g ;; f)
            =  idtoiso (maponpaths (fun b => Γ''◂b) (reind_comp_comp_cat C _ A _ f _ g))
               ;; q_comp_cat (A[f]) g
               ;; q_comp_cat A f
  := pr2 (pr2 (pr2 C)).

(*
Definition split_comp_precat := Σ C, (is_split_comp_cat C).
*)
(*
Definition comp_precat_of_split (C : split_comp_precat) := pr1 C.
*)
(* TODO: define access functions for other components of [is_split_…]. *)
 
End Comp_Precats.


(* Globalising notations defined within section above: *)
Notation "Γ ◂ A" := (ext_comp_cat Γ A) (at level 45, left associativity).
(* Temporarily suppressed due to levels clash with [cwf]. TODO: fix clash! *)
Notation "A [ f ]" := (reind_comp_cat A f) (at level 40).

(** * Lemmas about Comprehension categories *)

Section lemmas.

Variable CC : precategory.
Variable  C : split_comp_struct CC.
Variable hs : has_homsets CC.

Lemma transportf_dpr_comp_cat (Γ : CC)
  (A B : C Γ)
  (f : Γ ⇒ Γ ◂ A)
  (p : A = B) :
   transportf (λ B : C Γ, Γ ⇒ Γ ◂ B) p f;; dpr_comp_cat B =
   f;; dpr_comp_cat A.
Proof.
  induction p.
  apply idpath.
Defined.

Lemma idtoiso_dpr_comp_cat (Γ : CC)
  (A B : C Γ)
  (p : A = B) :
   idtoiso (maponpaths (λ B : C Γ,  Γ ◂ B) p);; dpr_comp_cat B =
   dpr_comp_cat A.
Proof.
  induction p.
  apply id_left. 
Defined.


Lemma transportf_reind_comp_cat (Γ Γ' : CC) (A A' : C Γ') (e : A = A') t :
  transportf (λ B, Γ ⇒ Γ' ◂ B) e t = transportf (λ Δ, Γ ⇒ Δ) (maponpaths _ e) t.
Proof.
  induction e.
  apply idpath.
Defined.

Lemma transportf_reind_comp_cat' (Γ Γ' : CC) (A : C Γ) (i i' : Γ' ⇒ Γ) (e : i = i')  t :
   transportf (λ i0 : Γ' ⇒ Γ, Γ' ⇒ Γ' ◂ reind_comp_cat A i0) e t =
   transportf (λ B : C Γ', Γ' ⇒ Γ' ◂ B) (maponpaths _  e) t.
Proof.
  induction e.
  apply idpath.
Defined.


End lemmas.

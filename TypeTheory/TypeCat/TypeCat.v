
(** 

 Ahrens, Lumsdaine, Voevodsky, 2015–

Contents:

  - Definition of type-(pre)categories and split type-categories
  - A few convenience lemmas
*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.limits.pullbacks.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheory.

(** * Type pre-categories

We define here *Type (pre-)categories*, closely based on the _type-categories_ of Andy Pitts, _Categorical Logic_, 2000, Def. 6.3.3
#(<a href="https://synrc.com/publications/cat/Category%%20Theory/Categorical%%20Logic/Pitts%%20A.M.%%20Categorical%%20Logic.pdf##page=73">link</a>).#
However, that definition includes two _strictness conditions_; 
we follow van den Berg and Garner, _Topological and simplicial models_, Def 2.2.1 #(<a href="http://arxiv.org/abs/1007.4638">arXiv</a>)# 
in separating these out from the rest of the definition.

 An element of [typecat], as we define it below, is thus exactly a type-category according 
to the definition of van den Berg and Garner (except with an underlying _precategory_, i.e. hom-types not assumed sets); and an element of [split_typecat] is a split type-category 
according to van den Berg and Garner, or a plain type-category in the sense of Pitts.

  In order to avoid the nested sigma-types getting too deep, 
we split up the structure into two stages: [typecat_structure1] and [typecat_structure2]. *)

(** * A "preview" of the definition *)

Module Record_Preview.
(** For technical reasons, we prefer not to use record types in the development.
However, a definition as a record type is much more readable — so we give that here, 
for documentation purposes only, wrapped in a module to keep it out of the global namespace. *)


Reserved Notation "C ⟨ Γ ⟩" (at level 60).
Reserved Notation "Γ ◂ A" (at level 40).
Reserved Notation "A {{ f }}" (at level 30).
Reserved Notation "'π' A" (at level 5).

Record type_precat_record : Type := {
  C : precategory ;
  ty : C -> Type                       where "C ⟨ Γ ⟩" := (ty Γ);
  ext : ∏ Γ, C⟨Γ⟩ -> C                  where "Γ ◂ A" := (ext Γ A);
  dpr : ∏ Γ (A : C⟨Γ⟩), Γ ◂ A --> Γ     where "'π' A" := (dpr _ A);
  reind : ∏ Γ (A : C⟨Γ⟩) Γ' (f : Γ' --> Γ), C⟨Γ'⟩ 
                                       where "A {{ f }}" := (reind _ A _ f);
  q : ∏ {Γ} (A : ty Γ) {Γ'} (f : Γ' --> Γ),
          (Γ' ◂ (A {{f }}) --> Γ ◂ A) ;
  dpr_q : ∏ Γ (A : C⟨Γ⟩) Γ' (f : Γ' --> Γ), 
          (q A f) ;; (π A) = (π (A{{f}})) ;; f ;
  reind_pb : ∏ Γ (A : ty Γ) Γ' (f : Γ' --> Γ),
      isPullback (!dpr_q _ A _ f)
}.

(** Here we see the components of the definition of a [type_precat].  Under the names of their actual versions below, they are:

- [precat_of_type_precat1] (a coercion): the underlying pre-ategory;
- [ty_type_cat] (also a coercion): for each object [Γ], a type of “types over [Γ]”, written [C Γ];
- [ext_type_cat]: a context extension operation, written [Γ ◂ A];
- [dpr_type_cat]: dependent projections from context extensions; 
- [reind_type_cat]: a reindexing operation on types, written [A[f]] or [f^*A];
- [q_type_cat]: for [f : Γ' → Γ], and [A : C Γ], a map [ (Γ' ◂ f^* A) --> (Γ ◂ A) ]; can be seen as the extension of a context morphism by a variable of a new type;
- [dpr_q_type_cat]: reindexing commutes with dependent projections;
- [reind_pb_type_cat]: the commutative square thus formed is a pullback. 

One possibly surprising point is that [reind_pb] uses the square whose commutativity is witnessed by [dpr_q] itself, but by its inverse of [dpr_q].  The point is that [dpr_q] is oriented in the more computationally natural direction [(q A f) ;; (π A) = (π (A{{f}})) ;; f ], but at the same time, it’s more natural to think of [π A{{f}}] as the first projection of the pullback and [q A f] the second. *)

End Record_Preview.


(** For the actual definition, we use iterated ∑-types.  
As usual, to avoid severe performance issues with these, 
we have to split up the definition into several steps: 
[type_precat_structure1] with the first few components, and [type_precat_structure2] the rest.  *)


(** * Types, reindexing and context extension *)

Section Type_Precats.

Definition typecat_structure1 (C : precategory) :=
  ∑ (ty : C -> UU)
    (ext : ∏ Γ, ty Γ -> C),
      ∏ Γ (A : ty Γ) Γ' (f : Γ' --> Γ), ty Γ'.
(*
Definition type_precat1 := ∑ (C : precategory), type_precat_structure1 C.

Definition precat_from_type_precat1 (C : type_precat1) : precategory := pr1 C.
Coercion precat_from_type_precat1 : type_precat1 >-> precategory.
*)
(** Since the various access functions should eventually apply directly to type-categories
as well as type-precategories (via coercion from the former to the latter), we drop the [pre] in their names. *)

Definition ty_typecat {CC : precategory} (C : typecat_structure1 CC) : CC -> UU 
 := pr1  C.

Coercion ty_typecat : typecat_structure1 >-> Funclass.

Definition ext_typecat {CC : precategory} {C : typecat_structure1 CC} 
  (Γ : CC) (A : C Γ) : CC
   := pr1 (pr2  C) Γ A.
Notation "Γ ◂ A" := (ext_typecat Γ A) (at level 40, left associativity).
  (* \tb in Agda input method,
     \smallblacktriangleleft in Company Coq *)
(* NOTE: not sure what levels we want here,
  but the level of this should be above the level of reindexing "A[f]",
  and bellow the level of hom-sets "X --> Y",
  to allow expressions like "Γ'◂a[f] --> Γ ◂ A". *)

Definition reind_typecat {CC : precategory} {C : typecat_structure1 CC}
  {Γ : CC} (A : C Γ) {Γ'} (f : Γ' --> Γ) : C Γ'
  := pr2 (pr2 C) Γ A Γ' f.
Notation "A {{ f }}" := (reind_typecat A f) (at level 30).

(** * Pullback of dependent projections *)

Definition typecat_structure2 {CC : precategory} (C : typecat_structure1 CC) :=
  ∑ (dpr : ∏ Γ (A : C Γ), Γ◂A --> Γ)
    (q : ∏ Γ (A : C Γ) Γ' (f : Γ' --> Γ), (Γ'◂A{{f}}) --> Γ◂A )
    (dpr_q : ∏ Γ (A : C Γ) Γ' (f : Γ' --> Γ), 
      (q _ A _ f) ;; (dpr _ A) = (dpr _ (A{{f}})) ;; f),
    ∏ Γ (A : C Γ) Γ' (f : Γ' --> Γ),
      isPullback (!dpr_q _ A _ f).
(* TODO: change name [dpr_q] to [q_dpr] throughout, now that composition is diagrammatic order? *)

Definition typecat_structure (CC : precategory) 
  := ∑ C : typecat_structure1 CC , typecat_structure2 C.

Definition typecat1_from_typecat (CC : precategory)(C : typecat_structure CC) 
  : typecat_structure1 _  := pr1 C.
Coercion typecat1_from_typecat : typecat_structure >-> typecat_structure1.

Definition dpr_typecat {CC : precategory}
    {C : typecat_structure CC} {Γ} (A : C Γ)
  : (Γ◂A) --> Γ
:= pr1 (pr2 C) Γ A.

Definition q_typecat {CC : precategory}
    {C : typecat_structure CC} {Γ} (A : C Γ) {Γ'} (f : Γ' --> Γ)
  : (Γ' ◂ A{{f}}) --> (Γ ◂ A) 
:=
  pr1 (pr2 (pr2 C)) _ A _ f.

Definition dpr_q_typecat {CC : precategory}
    {C : typecat_structure CC} {Γ} (A : C Γ) {Γ'} (f : Γ' --> Γ)
  : (q_typecat A f) ;; (dpr_typecat A) = (dpr_typecat (A{{f}})) ;; f
:=
  pr1 (pr2 (pr2 (pr2 C))) _ A _ f.

Definition reind_pb_typecat {CC : precategory}
    {C : typecat_structure CC} {Γ} (A : C Γ) {Γ'} (f : Γ' --> Γ)
  : isPullback (!dpr_q_typecat A f)
:=
  pr2 (pr2 (pr2 (pr2 C))) _ A _ f.

(** * Type-saturation *)

Definition is_type_saturated_typecat {CC : precategory}
    (C : typecat_structure CC) : UU
:= ∏ Γ, isincl (λ A : C Γ, tpair (λ X, X --> Γ) (Γ ◂ A) (dpr_typecat A)).


(** * Splitness *)

(** A type-precategory [C] is _split_ if it is a category (i.e. has hom-sets); each collection of types [C Γ] is a set, reindexing is strictly functorial; and the [q] maps satisfy the evident functoriality axioms *) 
Definition is_split_typecat {CC : category} (C : typecat_structure CC)
  := (∏ Γ:CC, isaset (C Γ))
     × (∑ (reind_id : ∏ Γ (A : C Γ), A {{identity Γ}} = A),
         ∏ Γ (A : C Γ), q_typecat A (identity Γ)
                        = idtoiso (maponpaths (fun b => Γ◂b) (reind_id Γ A)))
     × (∑ (reind_comp : ∏ Γ (A : C Γ) Γ' (f : Γ' --> Γ) Γ'' (g : Γ'' --> Γ'),
                         A {{g;;f}} = A{{f}}{{g}}),
          ∏ Γ (A : C Γ) Γ' (f : Γ' --> Γ) Γ'' (g : Γ'' --> Γ'),
            q_typecat A (g ;; f)
            =  idtoiso (maponpaths (fun b => Γ''◂b) (reind_comp _ A _ f _ g))
               ;; q_typecat (A{{f}}) g
               ;; q_typecat A f).

Lemma isaprop_is_split_typecat (CC : category)
       (C : typecat_structure CC) : isaprop (is_split_typecat C).
Proof.
  repeat (apply isofhleveltotal2; intros).
  - apply impred; intro; apply isapropisaset.
  - repeat (apply impred; intro). apply x.
  - repeat (apply impred; intro). apply homset_property.
  - repeat (apply impred; intro). apply x.
  - intros.
    repeat (apply impred; intro). apply homset_property.
Qed.

Definition typecat := ∑ (C : category), (typecat_structure C).

Coercion category_of_typecat (C : typecat) := pr1 C.
Coercion structure_of_typecat (C : typecat) := pr2 C.

Definition split_typecat := ∑ (C : typecat), (is_split_typecat C).

Coercion typecat_of_split_typecat (C : split_typecat) := pr1 C.
Coercion split_typecat_is_split (C : split_typecat) := pr2 C.

Definition split_typecat_structure (CC : category) : UU
  := ∑ C : typecat_structure CC, is_split_typecat C.

Coercion typecat_from_split CC (C : split_typecat_structure CC)
  : typecat_structure _
  := pr1 C.

Coercion is_split_from_split_typecat CC (C : split_typecat_structure CC)
  : is_split_typecat C
  := pr2 C.

Section access_functions.

Context {C : split_typecat}.

Definition isaset_types_typecat Γ : isaset (C Γ) := pr1 (pr2 C) _.

Definition reind_id_typecat {Γ} (A : C Γ) : A {{identity Γ}} = A
  := pr1 (pr1 (pr2 (pr2 C))) _ _.

Definition reind_comp_typecat
    {Γ} (A : C Γ) {Γ'} (f : Γ' --> Γ) {Γ''} (g : Γ'' --> Γ')
  : A {{g;;f}} = A{{f}}{{g}}
:= pr1 (pr2 (pr2 (pr2 C))) _ _ _ _ _ _.

Definition q_id_typecat {Γ} (A : C Γ)
  : q_typecat A (identity Γ)
    = idtoiso (maponpaths _ (reind_id_typecat A))
  := pr2 (pr1 (pr2 (pr2 C))) _ _.

Definition q_comp_typecat
    {Γ} (A : C Γ) {Γ'} (f : Γ' --> Γ) {Γ''} (g : Γ'' --> Γ')
  : q_typecat A (g ;; f)
    = idtoiso (maponpaths _ (reind_comp_typecat A f g))
        ;; q_typecat (A{{f}}) g
        ;; q_typecat A f
:= pr2 (pr2 (pr2 (pr2 C))) _ _ _ _ _ _.

(* TODO: see if some uses of [q_comp_typecat] can be simplified with this *)
Definition q_q_typecat
  : ∏ Γ (A : C Γ) Γ' (f : Γ' --> Γ) Γ'' (g : Γ'' --> Γ'),
    q_typecat (A{{f}}) g ;; q_typecat A f
    = idtoiso (maponpaths _ (!reind_comp_typecat A f g))
      ;; q_typecat A (g ;; f).
Proof.
  intros. apply z_iso_inv_to_left, pathsinv0. 
  etrans. { apply q_comp_typecat. }
  repeat rewrite <- assoc; apply maponpaths_2.
  generalize (reind_comp_typecat A f g).
  generalize (A {{g;;f}}).
  intros t p; destruct p.
  reflexivity.
Qed.

End access_functions.

End Type_Precats.

(* Globalising notations defined within section above: *)
Notation "Γ ◂ A" := (ext_typecat Γ A) (at level 40).
Notation "A {{ f }}" := (reind_typecat A f) (at level 30).

(** * Lemmas about type-(pre)categories *)

(* TODO: unify this section with the material of [TypeCat.General]. *)

Section lemmas.

Context {CC : precategory} {C : typecat_structure CC}.

Lemma transportf_dpr_typecat
    {Γ : CC} {A B : C Γ} (p : A = B)
    (f : Γ --> Γ ◂ A) 
  : transportf (λ B : C Γ, Γ --> Γ ◂ B) p f;; dpr_typecat B
    = f ;; dpr_typecat A.
Proof.
  induction p.
  apply idpath.
Defined.

Lemma idtoiso_dpr_typecat {Γ : CC} {A B : C Γ} (p : A = B)
  : idtoiso (maponpaths (λ B : C Γ,  Γ ◂ B) p) ;; dpr_typecat B
    = dpr_typecat A.
Proof.
  induction p.
  apply id_left. 
Defined.

Lemma idtoiso_q_typecat
    {Γ : CC} (A : C Γ)
    {Γ' : CC} {f f' : Γ' --> Γ} (e : f = f')
  : q_typecat A f
    = (idtoiso (maponpaths (fun f => ext_typecat Γ' (reind_typecat A f)) e))
      ;; q_typecat A f'.
Proof.
  intros. destruct e. sym. apply id_left.
  (* Why the heck doesn’t “symmetry” work here!? *)
Defined.

(* TODO: change name *)
Lemma transportf_reind_typecat {Γ Γ' : CC} {A A' : C Γ'} (e : A = A') t
  : transportf (λ B, Γ --> Γ' ◂ B) e t
    = transportf (λ Δ, Γ --> Δ) (maponpaths _ e) t.
Proof.
  induction e.
  apply idpath.
Defined.

Lemma transportf_reind_typecat'
    {Γ Γ' : CC} (A : C Γ) {i i' : Γ' --> Γ} (e : i = i')  t
  : transportf (λ i0 : Γ' --> Γ, Γ' --> Γ' ◂ reind_typecat A i0) e t
    = transportf (λ B : C Γ', Γ' --> Γ' ◂ B) (maponpaths _  e) t.
Proof.
  induction e.
  apply idpath.
Defined.


End lemmas.

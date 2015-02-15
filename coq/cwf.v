
(** * (Pre)categories with families *)
(**
  Contents:

    - Definition of a precategory with families

  The definition is based on Pitts, *Nominal Presentations of the Cubical Sets
  Model of Type Theory*, Def. 3.1: 
  http://www.cl.cam.ac.uk/~amp12/papers/nompcs/nompcs.pdf (page=9)
*)

Require Export Systems.Auxiliary.
Require Export Systems.UnicodeNotations.
Require Export UniMath.Foundations.hlevel2.hSet.

(** ** A [tt_precategory] comes with a types, written [C⟨Γ⟩], 
   and terms [C⟨Γ ⊢ A⟩] *)

Definition tt_structure (C : precategory) :=
  Σ f : C → UU, ∀ c : C, f c → UU.

Definition tt_precat : UU := Σ C : precategory, tt_structure C.
Definition precat_from_tt_precat (C : tt_precat) : precategory := pr1 C.
Coercion precat_from_tt_precat : tt_precat >-> precategory.

Definition type (C : tt_precat) : C → UU := pr1 (pr2 C).

Notation "C ⟨ Γ ⟩" := (type C Γ) (at level 60).
  (* \< and \> in Agda input method *)

Definition term (C : tt_precat) : ∀ Γ : C, C⟨Γ⟩ → UU := pr2 (pr2 C).

Notation "C ⟨ Γ ⊢ A ⟩" := (term C Γ A) (at level 60).
  (* \<, \>, and \|- or \vdash *)

(** ** Reindexing of types [A[γ]] and terms [a⟦γ⟧] along a morphism [γ : Γ' ⇒ Γ] *)

Definition reindx_structure (C : tt_precat) := 
   Σ (rtype : ∀ {Γ Γ' : C} (A : C⟨Γ⟩) (γ : Γ' ⇒ Γ), C⟨Γ'⟩),
        ∀ (Γ Γ' : C) (A : C⟨Γ⟩) (a : C⟨Γ⊢A⟩) (γ : Γ' ⇒ Γ), C⟨Γ'⊢rtype A γ⟩.

Definition reindx_precat := Σ (C : tt_precat), reindx_structure C.

Definition tt_precat_from_reindx_precat (C : reindx_precat) : tt_precat := pr1 C.
Coercion tt_precat_from_reindx_precat : reindx_precat >-> tt_precat.

Definition rtype {C : reindx_precat} : ∀ {Γ Γ' : C} (A : C⟨Γ⟩) (γ : Γ' ⇒ Γ), C⟨Γ'⟩ := 
   pr1 (pr2 C).

Notation "A [ γ ]" := (rtype A γ) (at level 50).

Definition rterm {C : reindx_precat} : ∀ {Γ Γ' : C} {A : C⟨Γ⟩} 
    (a : C⟨Γ⊢A⟩) (γ : Γ' ⇒ Γ), C⟨Γ'⊢ A[γ]⟩ := 
    pr2 (pr2 C).

Notation "a ⟦ γ ⟧" := (rterm a γ) (at level 50).

(** **  Reindexing laws *)

(** Reindexing for types *)
Definition reindx_laws_type (C : reindx_precat) : UU :=
    (∀ Γ (A : C⟨Γ⟩), A[identity Γ] = A) ×
    (∀ Γ Γ' Γ'' (γ : Γ' ⇒ Γ) (γ' : Γ'' ⇒ Γ') (A : C⟨Γ⟩), A [γ ∘ γ'] = A[γ][γ']). 

(** Reindexing for terms needs transport along reindexing for types *) 
Definition reindx_laws_terms {C : reindx_precat} (T : reindx_laws_type C) :=
    (∀ Γ (A : C⟨Γ⟩) (a : C⟨Γ⊢A⟩), a⟦identity Γ⟧ = 
          transportf (λ B, C⟨Γ ⊢ B⟩) (!pr1 T _ _) a) ×
    (∀ Γ Γ' Γ'' (γ : Γ' ⇒ Γ) (γ' : Γ'' ⇒ Γ') (A : C⟨Γ⟩) (a : C⟨Γ⊢A⟩),
            a⟦γ ∘ γ'⟧ = 
          transportf (λ B, C⟨Γ'' ⊢ B⟩) (!pr2 T _ _ _ _ _ _ )  (a⟦γ⟧⟦γ'⟧)).
          
(** Package of reindexing for types and terms *)
Definition reindx_laws (C : reindx_precat) := 
   Σ T : reindx_laws_type C, reindx_laws_terms T.
     
Definition reindx_type_id {C : reindx_precat} (T : reindx_laws C) : 
   ∀ Γ (A : C⟨Γ⟩), A [identity Γ] = A := pr1 (pr1 T).

Definition reindx_type_comp {C : reindx_precat} (T : reindx_laws C) 
   {Γ Γ' Γ''} (γ : Γ' ⇒ Γ) (γ' : Γ'' ⇒ Γ') (A : C⟨Γ⟩) : A [γ ∘ γ'] = A[γ][γ'] :=
   pr2 (pr1 T) _ _ _ _ _ _ .

Definition reindx_term_id {C : reindx_precat} (T : reindx_laws C) : 
   ∀ Γ (A : C⟨Γ⟩) (a : C⟨Γ⊢A⟩), a⟦identity Γ⟧ = 
          transportf (λ B, C⟨Γ ⊢ B⟩) (!pr1 (pr1 T) _ _) a := pr1 (pr2 T).

Definition reindx_term_comp {C : reindx_precat} (T : reindx_laws C) : 
   ∀ {Γ Γ' Γ''} (γ : Γ' ⇒ Γ) (γ' : Γ'' ⇒ Γ') {A : C⟨Γ⟩} (a : C⟨Γ⊢A⟩),
            a⟦γ ∘ γ'⟧ = 
          transportf (λ B, C⟨Γ'' ⊢ B⟩) (!pr2 (pr1 T) _ _ _ _ _ _ )  (a⟦γ⟧⟦γ'⟧) := 
   pr2 (pr2 T).
    

(** ** Comprehension structure *)

(** Comprehension object and projection *)
Definition comp_1_struct (C : reindx_precat) :=
  ∀ Γ (A : C⟨Γ⟩), Σ (ΓAπ : Σ ΓA, ΓA ⇒ Γ), C ⟨pr1 ΓAπ ⊢ A [pr2 ΓAπ]⟩.

Definition comp_1_precat := Σ C : reindx_precat, comp_1_struct C.

Definition reindx_precat_from_comp_1_precat (C : comp_1_precat) : reindx_precat := pr1 C.
Coercion reindx_precat_from_comp_1_precat : comp_1_precat >-> reindx_precat.

Definition comp_obj (C : comp_1_precat) (Γ : C) (A : C⟨Γ⟩) : C := pr1 (pr1 (pr2 C Γ A)).
Notation "Γ ∙ A" := (comp_obj _ Γ A) (at level 20).

Definition proj_mor (C : comp_1_precat) (Γ : C) (A : C⟨Γ⟩) : Γ∙A ⇒ Γ := pr2 (pr1 (pr2 C Γ A)).
Notation "'π' A" := (proj_mor _ _ A) (at level 20).

(** Generic element and pairing *)
Definition comp_2_struct (C : comp_1_precat) := 
   ∀ Γ (A : C⟨Γ⟩), 
     C⟨Γ∙A ⊢ A[π _ ]⟩ × 
     (∀ Γ' (γ : Γ' ⇒ Γ) (a : C⟨Γ'⊢A[γ]⟩), Γ' ⇒ Γ∙A).

Definition comp_2_precat := Σ C : comp_1_precat, comp_2_struct C.

Definition comp_1_precat_from_comp_2_precat (C : comp_2_precat) : comp_1_precat := pr1 C.
Coercion comp_1_precat_from_comp_2_precat : comp_2_precat >-> comp_1_precat.

Definition gen_elem (C : comp_2_precat) (Γ : C) (A : C⟨Γ⟩) : C⟨Γ∙A ⊢ A[π _ ]⟩ := 
   pr1 (pr2 C Γ A).
Notation "'ν' A" := (gen_elem _ _ A) (at level 15).

Definition pairing (C : comp_2_precat) (Γ : C) (A : C⟨Γ⟩) Γ' (γ : Γ' ⇒ Γ) (a : C⟨Γ'⊢A[γ]⟩) : 
    Γ' ⇒ Γ∙A := pr2 (pr2 C Γ A) Γ' γ a.
Notation "γ ♯ a" := (pairing _ _ _ _ γ a) (at level 25).

(** Laws satisfied by the comprehension structure *)
Definition comp_laws_1_2 {C : comp_2_precat} (T : reindx_laws C) := 
   ∀ Γ (A : C ⟨Γ⟩) Γ' (γ : Γ' ⇒ Γ) (a : C⟨Γ'⊢ A[γ]⟩),
        Σ h : (π _) ∘ (γ ♯ a) = γ,
           transportf (λ ι, C⟨Γ'⊢ A [ι]⟩) h   
             (transportf (λ B, C⟨Γ'⊢ B⟩) (!reindx_type_comp T (π _ )(γ ♯ a) _ ) 
                (ν _ ⟦γ ♯ a⟧)) = a.

Definition comp_law_3 {C : comp_2_precat} (T : reindx_laws C) := 
   ∀ Γ (A : C ⟨Γ⟩) Γ' Γ'' (γ : Γ' ⇒ Γ) (γ' : Γ'' ⇒ Γ') (a : C⟨Γ'⊢ A[γ]⟩),
    (γ ♯ a) ∘ γ' = (γ ∘ γ') ♯ 
          (transportf (λ B, C⟨Γ''⊢ B⟩) (!reindx_type_comp T γ γ' _ ) (a⟦γ'⟧)).

Definition comp_law_4 {C : comp_2_precat} (T : reindx_laws C) :=
   ∀ Γ (A : C⟨Γ⟩), π A ♯ ν A = identity _ . 

(** ** Definition of precategory with families *)
(** A precategory with families [pre_cwf] is 
  - a precategory
  - with reindexing 
  - with comprehension structure
  - satisfying the comprehension laws
  - where types and terms are hsets
*)

Definition pre_cwf := Σ C : comp_2_precat,
    (Σ T : reindx_laws C,
       (comp_laws_1_2 T × comp_law_3 T × comp_law_4 T)) ×
    ((∀ Γ, isaset (C⟨Γ⟩)) × ∀ Γ (A : C⟨Γ⟩), isaset (C⟨Γ⊢ A⟩)). 

Definition comp_2_precat_from_pre_cwf (C : pre_cwf) : comp_2_precat
  := pr1 C.
Coercion comp_2_precat_from_pre_cwf : pre_cwf >-> comp_2_precat.
(* There is now a chain of coercions from [pre_cwf] to [precategory]. *)

Definition reindx_laws_from_pre_cwf (C : pre_cwf) : reindx_laws C
  := pr1 (pr1 (pr2 C)).
Coercion reindx_laws_from_pre_cwf : pre_cwf >-> reindx_laws.
(* This coercion allows us to write things like [reindx_type_id C]. *)

Definition pre_cwf_laws (C : pre_cwf)
  : (comp_laws_1_2 C × comp_law_3 C × comp_law_4 C)
  := pr2 (pr1 (pr2 C)).

Definition pre_cwf_law_1 (C : pre_cwf) Γ (A : C ⟨Γ⟩) Γ' (γ : Γ' ⇒ Γ) (a : C⟨Γ'⊢ A[γ]⟩)
  : (π _) ∘ (γ ♯ a) = γ
  := pr1 (pr1 (pr1 (pre_cwf_laws C)) Γ A Γ' γ a).

Definition pre_cwf_law_2 (C : pre_cwf) Γ (A : C ⟨Γ⟩) Γ' (γ : Γ' ⇒ Γ) (a : C⟨Γ'⊢ A[γ]⟩)
  : transportf (λ ι, C⟨Γ'⊢ A [ι]⟩) (pre_cwf_law_1 C Γ A Γ' γ a)
    (transportf (λ B, C⟨Γ'⊢ B⟩) (!reindx_type_comp C (π _ )(γ ♯ a) _ ) 
      ((ν A) ⟦γ ♯ a⟧))
    = a
  := pr2 (pr1 (pr1 (pre_cwf_laws C)) Γ A Γ' γ a).

Definition pre_cwf_law_3 (C : pre_cwf) : comp_law_3 C
  := pr2 (pr1 (pre_cwf_laws C)).

Definition pre_cwf_law_4 (C : pre_cwf) : comp_law_4 C
  := pr2 (pre_cwf_laws C).

Definition pre_cwf_types_isaset (C : pre_cwf) : ∀ Γ, isaset (C⟨Γ⟩)
  := pr1 (pr2 (pr2 C)).

Definition pre_cwf_terms_isaset (C : pre_cwf) : ∀ Γ A, isaset (C⟨Γ ⊢ A⟩)
  := pr2 (pr2 (pr2 C)).


(** ** General lemmas *)

Section CwF_lemmas.

Context {C : pre_cwf}.

Lemma map_to_comp_as_pair_precwf {c} {a : C⟨c⟩} {c'} (f : c' ⇒ c∙a)
  : pairing _ _ _ _ 
      (π a ∘ f)
      (transportb _ (reindx_type_comp C _ _ _) ((ν a)⟦f⟧))
  = f.
Proof.
  apply pathsinv0.
  eapply pathscomp0.
    refine (!id_right _ _ _ _).
  eapply pathscomp0.
    refine (maponpaths (fun g => g ∘ f) (!pre_cwf_law_4 _ _ _)).
  apply pre_cwf_law_3.
Qed.

Lemma pairing_mapeq {c} {a : C ⟨ c ⟩} {c'} (f f' : c' ⇒ c) (e : f = f')
                     (t : C ⟨ c' ⊢ a [f] ⟩)
  : pairing _ _ _ _ f t
    = pairing _ _ _ _ f' (transportf (fun B => C⟨c' ⊢ B⟩ ) (maponpaths _ e) t).
Proof.
  destruct e. apply idpath.
Qed.

Lemma rterm_typeeq {c} {a a': C ⟨ c ⟩} (e : a = a') {c'} (f : c' ⇒ c) (x : C ⟨ c ⊢ a ⟩)
  : transportf _ (maponpaths (fun b => b[f]) e) (x⟦f⟧)
    = (transportf _ e x) ⟦f⟧.
Proof.
  destruct e. apply idpath.
Qed.

Lemma transportf_rtype_mapeq {c} {a : C ⟨ c ⟩} {c'} (f f' : c' ⇒ c) (e : f = f')
                     (t : C ⟨ c' ⊢ a[f] ⟩)
  : transportf (fun g => C ⟨ c' ⊢ a[g] ⟩) e t
  = transportf _ (maponpaths (fun g => a[g]) e) t.
Proof.
  destruct e. apply idpath.
Qed.

Lemma rterm_mapeq {c} {a : C ⟨ c ⟩} {c'} {f f' : c' ⇒ c} (e : f = f') (t : C ⟨ c ⊢ a ⟩)
  : t ⟦ f ⟧
  = transportb _ (maponpaths (fun g => a[g]) e) (t ⟦ f' ⟧ ).
Proof.
  destruct e. apply idpath.
Qed.

(* A slightly odd statement, but very often useful.
   
   TODO: consider naming!
   TODO: try to use in proofs, instead of [transportf_pathscomp0] *)
Lemma term_typeeq_transport_lemma {c} {a a' a'': C ⟨ c ⟩} (e : a = a'') (e' : a' = a'')
  (x : C ⟨ c ⊢ a ⟩) (x' : C ⟨ c ⊢ a' ⟩)
  : transportf _ (e @ !e') x = x'
  -> transportf _ e x = transportf _ e' x'.
Proof.
  intro H.
  eapply pathscomp0. Focus 2.
    apply maponpaths. exact H.
  eapply pathscomp0. Focus 2.
    symmetry. apply transportf_pathscomp0.
  apply (maponpaths (fun p => transportf _ p x)).
  apply pre_cwf_types_isaset.
Qed.

Lemma term_typeeq_transport_lemma_2 {c} {a : C ⟨ c ⟩} (e : a = a)
  {x x' : C ⟨ c ⊢ a ⟩}
  : x = x'
  -> transportf _ e x = x'.
Proof.
  intros ex.
  apply @pathscomp0 with (transportf _ (idpath a) x).
    apply (maponpaths (fun p => transportf _ p x)).
    apply pre_cwf_types_isaset.
  exact ex.
Qed.

Lemma reindx_term_comp' {Γ Γ' Γ''} (γ : Γ' ⇒ Γ) (γ' : Γ'' ⇒ Γ') {A} (a : C ⟨ Γ ⊢ A ⟩)
  : transportf _ (reindx_type_comp C _ _ _) (a ⟦ γ ∘ γ' ⟧)
  = ((a ⟦ γ ⟧) ⟦ γ' ⟧).
Proof.
  eapply pathscomp0.
    apply maponpaths, (reindx_term_comp C).
  eapply pathscomp0. apply transportf_pathscomp0.
  apply term_typeeq_transport_lemma_2. apply idpath.
Qed.

(* TODO: consider giving this instead of current [pre_cwf_law_2] ? *)
Definition pre_cwf_law_2' Γ (A : C ⟨Γ⟩) Γ' (γ : Γ' ⇒ Γ) (a : C⟨Γ'⊢ A[γ]⟩)
  : (ν A) ⟦γ ♯ a⟧
  = transportf _ (reindx_type_comp C _ _ _)
      (transportb _ (maponpaths (fun g => A[g]) (pre_cwf_law_1 _ _ _ _ _ _))
        a). 
Proof.
  eapply pathscomp0. Focus 2.
    apply maponpaths, maponpaths. exact (pre_cwf_law_2 _ _ _ _ γ a).
  symmetry.
  (* TODO: try simplyfying with [term_typeeq_transport_lemma] *)
  eapply pathscomp0. apply transportf_pathscomp0.
  eapply pathscomp0. apply maponpaths, transportf_rtype_mapeq.
  eapply pathscomp0. apply transportf_pathscomp0.
  eapply pathscomp0. apply transportf_pathscomp0.
  refine (@maponpaths _ _ (fun e => transportf _ e _) _ (idpath _) _).
  apply pre_cwf_types_isaset.
Qed.


End CwF_lemmas.

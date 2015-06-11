
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


Module Record_Preview.

Reserved Notation "C ⟨ Γ ⟩" (at level 60).
Reserved Notation "C ⟨ Γ ⊢ A ⟩" (at level 60).
Reserved Notation "A [ γ ]" (at level 40).
Reserved Notation "a ⟦ γ ⟧" (at level 40).
Reserved Notation "Γ ∙ A" (at level 20).
Reserved Notation "'π' A" (at level 20).
Reserved Notation "'ν' A" (at level 15).
Reserved Notation "γ ♯ a" (at level 25).

Record precwf_record : Type := {
  C : precategory ;
  type : C → UU     where "C ⟨ Γ ⟩" := (type Γ) ;
  term : ∀ Γ : C, C⟨Γ⟩ → UU     where "C ⟨ Γ ⊢ A ⟩" := (term Γ A) ;
  rtype : ∀ {Γ Γ' : C} (A : C⟨Γ⟩) (γ : Γ' ⇒ Γ), C⟨Γ'⟩ where "A [ γ ]" := (rtype A γ) ;
  rterm : ∀ {Γ Γ' : C} {A : C⟨Γ⟩} (a : C⟨Γ⊢A⟩) (γ : Γ' ⇒ Γ), 
          C⟨Γ'⊢ A[γ]⟩   where "a ⟦ γ ⟧" := (rterm a γ) ;
  reindx_type_id : ∀ Γ (A : C⟨Γ⟩), A [identity Γ] = A ;
  reindx_type_comp : ∀  {Γ Γ' Γ''} (γ : Γ' ⇒ Γ) (γ' : Γ'' ⇒ Γ') (A : C⟨Γ⟩), 
          A [γ';;γ] 
          =  
          A[γ][γ'] ;
  reindx_term_id : ∀ Γ (A : C⟨Γ⟩) (a : C⟨Γ⊢A⟩), 
          a⟦identity Γ⟧ 
          =
          transportf (λ B, C⟨Γ ⊢ B⟩) (! (reindx_type_id _ _)) a ;
  reindx_term_comp : ∀ {Γ Γ' Γ''} (γ : Γ' ⇒ Γ) (γ' : Γ'' ⇒ Γ') {A : C⟨Γ⟩} (a : C⟨Γ⊢A⟩),
          a⟦γ';;γ⟧ 
          =
          transportf (λ B, C⟨Γ'' ⊢ B⟩) (!(reindx_type_comp  _ _ _ )) (a⟦γ⟧⟦γ'⟧) ;
  comp_obj : ∀ Γ (A : C⟨Γ⟩), C where "Γ ∙ A" := (comp_obj Γ A) ;
  proj_mor : ∀ Γ (A : C⟨Γ⟩), Γ ∙ A ⇒ Γ where "'π' A" := (proj_mor _ A) ;
  gen_element : ∀ Γ (A : C⟨Γ⟩), C⟨Γ∙A ⊢ A[π _ ]⟩ where "'ν' A" := (gen_element _ A) ;
  pairing : ∀ Γ (A : C⟨Γ⟩) Γ' (γ : Γ' ⇒ Γ)(a : C⟨Γ'⊢ A[γ]⟩), Γ' ⇒ Γ∙A 
     where "γ ♯ a" := (pairing _ _ _  γ a) ;
  pre_cwf_law_1 : ∀ Γ (A : C ⟨Γ⟩) Γ' (γ : Γ' ⇒ Γ) (a : C⟨Γ'⊢ A[γ]⟩), 
          (γ ♯ a) ;; (π _) 
          = 
          γ ;
  pre_cwf_law_2 : ∀ Γ (A : C ⟨Γ⟩) Γ' (γ : Γ' ⇒ Γ) (a : C⟨Γ'⊢ A[γ]⟩),
          transportf (λ ι, C⟨Γ'⊢ A [ι]⟩) (pre_cwf_law_1 Γ A Γ' γ a)
             (transportf (λ B, C⟨Γ'⊢ B⟩) (!reindx_type_comp (π _ )(γ ♯ a) _ )
                ((ν A) ⟦γ ♯ a⟧))
          = 
          a
}.

End Record_Preview.


(** ** A [tt_precategory] comes with a types, written [C⟨Γ⟩], 
   and terms [C⟨Γ ⊢ A⟩] *)

Definition tt_structure (C : precategory) :=
  Σ f : C → UU, ∀ c : C, f c → UU.

(*
Definition tt_precat : UU := Σ C : precategory, tt_structure C.
Definition precat_from_tt_precat (C : tt_precat) : precategory := pr1 C.
Coercion precat_from_tt_precat : tt_precat >-> precategory.
*)

Definition type {C : precategory} (TT : tt_structure C) : C → UU := pr1 TT.

Notation "C ⟨ Γ ⟩" := (type C Γ) (at level 60).
  (* \< and \> in Agda input method *)

Definition term {CC : precategory} (C : tt_structure CC) : ∀ Γ : CC, C⟨Γ⟩ → UU := pr2 C.

Notation "C ⟨ Γ ⊢ A ⟩" := (term C Γ A) (at level 60).
  (* \<, \>, and \|- or \vdash *)

(** ** Reindexing of types [A[γ]] and terms [a⟦γ⟧] along a morphism [γ : Γ' ⇒ Γ] *)

Definition reindx_structure {CC : precategory}(C : tt_structure CC) := 
   Σ (rtype : ∀ {Γ Γ' : CC} (A : C⟨Γ⟩) (γ : Γ' ⇒ Γ), C⟨Γ'⟩),
        ∀ (Γ Γ' : CC) (A : C⟨Γ⟩) (a : C⟨Γ⊢A⟩) (γ : Γ' ⇒ Γ), C⟨Γ'⊢rtype A γ⟩.

(*
Definition reindx_precat := Σ (C : tt_precat), reindx_structure C.

Definition tt_precat_from_reindx_precat (C : reindx_precat) : tt_precat := pr1 C.
Coercion tt_precat_from_reindx_precat : reindx_precat >-> tt_precat.
*)

Definition rtype {CC : precategory}{C : tt_structure CC} (H : reindx_structure C) 
  : ∀ {Γ Γ' : CC} (A : C⟨Γ⟩) (γ : Γ' ⇒ Γ), C⟨Γ'⟩ 
:= 
   pr1 H.

Notation "A [ γ ,, H ]" := (rtype H A γ) (at level 40).

Definition rterm {CC : precategory}{C : tt_structure CC} (H : reindx_structure C) 
  : ∀ {Γ Γ' : CC} {A : C⟨Γ⟩}  (a : C⟨Γ⊢A⟩) (γ : Γ' ⇒ Γ), C⟨Γ'⊢ A [γ,, H] ⟩ 
:= 
    pr2 H.

Notation "a ⟦ γ ,, H ⟧" := (rterm H a γ) (at level 40).

(** **  Reindexing laws *)

(** Reindexing for types *)
Definition reindx_laws_type {CC : precategory}{C : tt_structure CC}(H : reindx_structure C) : UU :=
    (∀ Γ (A : C⟨Γ⟩), A [identity Γ,, H] = A) ×
    (∀ Γ Γ' Γ'' (γ : Γ' ⇒ Γ) (γ' : Γ'' ⇒ Γ') (A : C⟨Γ⟩), A [γ';;γ,, H] = A[γ,, H][γ',, H]). 

(** Reindexing for terms needs transport along reindexing for types *) 
Definition reindx_laws_terms {CC : precategory} {C : tt_structure CC} 
    {H : reindx_structure C} (T : reindx_laws_type H) :=
    (∀ Γ (A : C⟨Γ⟩) (a : C⟨Γ⊢A⟩), a⟦identity Γ,, H⟧ = 
          transportf (λ B, C⟨Γ ⊢ B⟩) (!pr1 T _ _) a) ×
    (∀ Γ Γ' Γ'' (γ : Γ' ⇒ Γ) (γ' : Γ'' ⇒ Γ') (A : C⟨Γ⟩) (a : C⟨Γ⊢A⟩),
            a⟦γ';;γ,, H⟧ = 
          transportf (λ B, C⟨Γ'' ⊢ B⟩) (!pr2 T _ _ _ _ _ _ )  (a⟦γ,, H⟧⟦γ',, H⟧)).
          
(** Package of reindexing for types and terms *)
Definition reindx_laws {CC : precategory} {C : tt_structure CC} 
   (H : reindx_structure C) : UU := 
   Σ T : reindx_laws_type H, reindx_laws_terms T.
     
Definition reindx_type_id {CC : precategory} {C : tt_structure CC} 
   {H : reindx_structure C} (T : reindx_laws H)
  : ∀ Γ (A : C⟨Γ⟩), A [identity Γ,, H] = A 
:= pr1 (pr1 T).

Definition reindx_type_comp {CC : precategory} {C : tt_structure CC} 
   {H : reindx_structure C} (T : reindx_laws H) 
   {Γ Γ' Γ''} (γ : Γ' ⇒ Γ) (γ' : Γ'' ⇒ Γ') (A : C⟨Γ⟩) 
  : A [γ';;γ,, H] = A[γ,, H][γ',, H] 
:=
   pr2 (pr1 T) _ _ _ _ _ _ .

Definition reindx_term_id {CC : precategory} {C : tt_structure CC}
   {H : reindx_structure C} (T : reindx_laws H) 
  : ∀ Γ (A : C⟨Γ⟩) (a : C⟨Γ⊢A⟩), a⟦identity Γ,, H⟧ = 
          transportf (λ B, C⟨Γ ⊢ B⟩) (!pr1 (pr1 T) _ _) a 
:= pr1 (pr2 T).

Definition reindx_term_comp {CC : precategory} {C : tt_structure CC}
   {H : reindx_structure C} (T : reindx_laws H) 
  : ∀ {Γ Γ' Γ''} (γ : Γ' ⇒ Γ) (γ' : Γ'' ⇒ Γ') {A : C⟨Γ⟩} (a : C⟨Γ⊢A⟩),
            a⟦γ';;γ,, H⟧ = 
          transportf (λ B, C⟨Γ'' ⊢ B⟩) (!pr2 (pr1 T) _ _ _ _ _ _ )  (a⟦γ,, H⟧⟦γ',, H⟧) 
:= 
   pr2 (pr2 T).
    

(** ** Comprehension structure *)

(** Comprehension object and projection *)
Definition comp_1_struct {CC : precategory} {C : tt_structure CC}
   (H : reindx_structure C) : UU 
:=
  ∀ Γ (A : C⟨Γ⟩), Σ (ΓAπ : Σ ΓA, ΓA ⇒ Γ), C ⟨pr1 ΓAπ ⊢ A [pr2 ΓAπ,, H]⟩.

(*
Definition comp_1_precat := Σ C : reindx_precat, comp_1_struct C.

Definition reindx_precat_from_comp_1_precat (C : comp_1_precat) : reindx_precat := pr1 C.
Coercion reindx_precat_from_comp_1_precat : comp_1_precat >-> reindx_precat.
*)

Definition comp_obj {CC : precategory} {C : tt_structure CC}
   {H : reindx_structure C} (K : comp_1_struct H) (Γ : CC) (A : C⟨Γ⟩) 
  : CC 
:= pr1 (pr1 (K Γ A)).
Notation "Γ ∙ A | K" := (comp_obj K Γ A) (at level 20).
  (* \. in Adga mode *)

Definition proj_mor {CC : precategory} {C : tt_structure CC}
    {H : reindx_structure C} (K : comp_1_struct H) {Γ : CC} (A : C⟨Γ⟩) 
  : Γ ∙ A | K ⇒ Γ 
:= pr2 (pr1 (K Γ A)).

Notation "'π' K A" := (proj_mor K _ A) (at level 20).

(** Generic element and pairing *)
Definition comp_2_struct {CC : precategory} {C : tt_structure CC}
    {H : reindx_structure C} (K : comp_1_struct H) := 
   ∀ Γ (A : C⟨Γ⟩), 
     C⟨(Γ∙A | K) ⊢ (A [proj_mor K A ,, H]) ⟩ × 
     (∀ Γ' (γ : Γ' ⇒ Γ) (a : C⟨Γ'⊢A[γ,, H ]⟩), Γ' ⇒ Γ∙A| K).

(*
Definition comp_2_precat := Σ C : comp_1_precat, comp_2_struct C.

Definition comp_1_precat_from_comp_2_precat (C : comp_2_precat) : comp_1_precat := pr1 C.
Coercion comp_1_precat_from_comp_2_precat : comp_2_precat >-> comp_1_precat.
*)

Definition gen_elem  {CC : precategory} {C : tt_structure CC}
    {H : reindx_structure C} {K : comp_1_struct H} 
    (T : comp_2_struct K) {Γ : CC} (A : C⟨Γ⟩) 
  : C⟨Γ∙A | K ⊢ A[proj_mor _ _ ,, H]⟩ 
 := 
   pr1 (T Γ A).
(*
Notation "'ν' A" := (gen_elem _ _ A) (at level 15).
*)
Definition pairing  {CC : precategory} {C : tt_structure CC}
    {H : reindx_structure C} {K : comp_1_struct H} 
    (T : comp_2_struct K) {Γ : CC} (A : C⟨Γ⟩) {Γ'} (γ : Γ' ⇒ Γ) (a : C⟨Γ'⊢A[γ,,H]⟩) 
  : Γ' ⇒ Γ∙A | K 
:= pr2 (T Γ A) Γ' γ a.
(*
Notation "γ ♯ a" := (pairing _ _ _ _ γ a) (at level 25).
  (* \# in Adga mode *)
 *)

(** Laws satisfied by the comprehension structure *)

Definition comp_laws_1_2  {CC : precategory} {C : tt_structure CC}
    {H : reindx_structure C} (L : reindx_laws H) {K : comp_1_struct H} 
    (T : comp_2_struct K) : UU := 
   ∀ Γ (A : C ⟨Γ⟩) Γ' (γ : Γ' ⇒ Γ) (a : C⟨Γ'⊢ A[γ,, H]⟩),
        Σ h : (pairing T _  γ a) ;; (proj_mor _ _ ) = γ,
           transportf (λ ι, C⟨Γ'⊢ A [ι,, _ ]⟩) h   
             (transportf (λ B, C⟨Γ'⊢ B⟩) (!reindx_type_comp L (proj_mor _ _ )(pairing _ _ γ a) _ )
               (rterm H (gen_elem T _  ) (pairing T _ γ a))) = a.

Definition comp_law_3  {CC : precategory} {C : tt_structure CC}
    {H : reindx_structure C} (L : reindx_laws H) {K : comp_1_struct H} 
    (T : comp_2_struct K) := 
   ∀ Γ (A : C ⟨Γ⟩) Γ' Γ'' (γ : Γ' ⇒ Γ) (γ' : Γ'' ⇒ Γ') (a : C⟨Γ'⊢ A[γ,, H]⟩),
    γ' ;; (pairing T _ γ  a) = pairing T _ (γ' ;; γ)  
          (transportf (λ B, C⟨Γ''⊢ B⟩) (!reindx_type_comp L γ γ' _ ) (a⟦γ',, H ⟧)).

Definition comp_law_4  {CC : precategory} {C : tt_structure CC}
    {H : reindx_structure C} (L : reindx_laws H) {K : comp_1_struct H} 
    (T : comp_2_struct K) :=
   ∀ Γ (A : C⟨Γ⟩), pairing T _ (proj_mor _ A) (gen_elem T A) = identity _ . 

(** ** Definition of precategory with families *)
(** A precategory with families [pre_cwf] is 
  - a precategory
  - with reindexing 
  - with comprehension structure
  - satisfying the comprehension laws
  - where types and terms are hsets
*)


Definition cwf_data (CC : precategory) : UU
:=
   Σ C : tt_structure CC,
     Σ H : reindx_structure C, 
       Σ K : comp_1_struct H, comp_2_struct K.     

Coercion tt_from_cwf_data (CC : precategory)(C : cwf_data CC) : tt_structure CC := pr1 C.
Coercion reindx_from_cwf_data CC (C : cwf_data CC) : reindx_structure _ := pr1 (pr2 C).
Coercion comp_1_struct_from_cwf_data CC (C : cwf_data CC) : comp_1_struct _ := pr1 (pr2 (pr2 C)).
Coercion comp_2_struct_from_cwf_data CC (C : cwf_data CC) : comp_2_struct _ := pr2 (pr2 (pr2 C)).


Definition cwf_laws {CC : precategory}(C : cwf_data CC) 
     (*L : reindx_laws C*)
   :=
    (Σ T : reindx_laws C,
       (comp_laws_1_2 T C × comp_law_3 T C × comp_law_4 T C)) ×
    ((∀ Γ, isaset (C⟨Γ⟩)) × ∀ Γ (A : C⟨Γ⟩), isaset (C⟨Γ⊢ A⟩)). 

Definition cwf_struct (CC : precategory) : UU 
  := Σ C : cwf_data CC, cwf_laws C.

Coercion cwf_data_from_cwf_struct (CC : precategory) (C : cwf_struct CC) : cwf_data CC := pr1 C.
Coercion cwf_laws_from_cwf_struct (CC : precategory) (C : cwf_struct CC) : cwf_laws C := pr2 C.

(*
Definition comp_2_precat_from_pre_cwf (C : pre_cwf) : comp_2_precat
  := pr1 C.
Coercion comp_2_precat_from_pre_cwf : pre_cwf >-> comp_2_precat.
(* There is now a chain of coercions from [pre_cwf] to [precategory]. *)
*)

Coercion reindx_laws_from_cwf_struct (CC : precategory) (C : cwf_struct CC)
  : reindx_laws C
  := pr1 (pr1 (pr2 C)).
(* This coercion allows us to write things like [reindx_type_id C]. *)

Definition pre_cwf_laws {CC : precategory} (C : cwf_struct CC)
  : (comp_laws_1_2 C C × comp_law_3 C C × comp_law_4 C C)
  := pr2 (pr1 (pr2 C)).

Definition pre_cwf_law_1 {CC : precategory} (C : cwf_struct CC) 
  Γ (A : C ⟨Γ⟩) Γ' (γ : Γ' ⇒ Γ) (a : C⟨Γ'⊢ A[γ,,C]⟩)
  : (pairing C _ γ a) ;; (proj_mor _  _) = γ
  := pr1 (pr1 (pr1 (pre_cwf_laws C)) Γ A Γ' γ a).

Definition pre_cwf_law_2 {CC : precategory} (C : cwf_struct CC) 
  Γ (A : C ⟨Γ⟩) Γ' (γ : Γ' ⇒ Γ) (a : C⟨Γ'⊢ A[γ,, C]⟩)
  : transportf (λ ι, C⟨Γ'⊢ A [ι,,C]⟩) (pre_cwf_law_1 C Γ A Γ' γ a)
    (transportf (λ B, C⟨Γ'⊢ B⟩) (!reindx_type_comp C (proj_mor _ _  )(pairing C _ γ a) _ ) 
      ((gen_elem C A ) ⟦pairing C _ γ a,, C ⟧))
    = a
  := pr2 (pr1 (pr1 (pre_cwf_laws C)) Γ A Γ' γ a).

Definition pre_cwf_law_3 {CC : precategory} (C : cwf_struct CC) : comp_law_3 C C
  := pr2 (pr1 (pre_cwf_laws C)).

Definition pre_cwf_law_4 {CC : precategory} (C : cwf_struct CC) : comp_law_4 C C
  := pr2 (pre_cwf_laws C).

Definition pre_cwf_types_isaset {CC : precategory} (C : cwf_struct CC) : ∀ Γ, isaset (C⟨Γ⟩)
  := pr1 (pr2 (pr2 C)).

Definition pre_cwf_terms_isaset  {CC : precategory} (C : cwf_struct CC) : ∀ Γ A, isaset (C⟨Γ ⊢ A⟩)
  := pr2 (pr2 (pr2 C)).


(** ** General lemmas *)

Section CwF_lemmas.

Generalizable Variable CC.
Context `{C : cwf_struct CC}.

Lemma map_to_comp_as_pair_precwf {Γ} {A : C⟨Γ⟩} {Γ'} (f : Γ' ⇒ Γ∙A| C)
  : pairing C _   
      (f ;; proj_mor C  A)
      (transportb _ (reindx_type_comp C _ _ _) ((gen_elem C A)⟦f,,C⟧))
  = f.
Proof.
  apply pathsinv0.
  eapply pathscomp0.
    refine (!id_right _ _ _ _).
  eapply pathscomp0.
    refine (maponpaths (fun g => f ;; g) (!pre_cwf_law_4 _ _ _)).
  apply pre_cwf_law_3.
Qed.

Lemma pairing_mapeq {Γ} {A : C⟨Γ⟩} {Γ'} (f f' : Γ' ⇒ Γ) (e : f = f')
                     (t : C ⟨ Γ' ⊢ A [f,,C] ⟩)
  : pairing C _ f t
    = pairing C _ f' (transportf (fun B => C⟨Γ' ⊢ B⟩ ) (maponpaths _ e) t).
Proof.
  destruct e. apply idpath.
Qed.

Lemma rterm_typeeq {Γ} {A A': C⟨Γ⟩} (e : A = A') {Γ'} (f : Γ' ⇒ Γ) (x : C ⟨ Γ ⊢ A ⟩)
  : transportf _ (maponpaths (fun b => b[f,,C]) e) (x⟦f,,C⟧)
    = (transportf _ e x) ⟦f,,C⟧.
Proof.
  destruct e. apply idpath.
Qed.

Lemma transportf_rtype_mapeq {Γ} {A : C⟨Γ⟩} {Γ'} (f f' : Γ' ⇒ Γ) (e : f = f')
                     (t : C ⟨ Γ' ⊢ A[f,,C] ⟩)
  : transportf (fun g => C ⟨ Γ' ⊢ A[g,,C] ⟩) e t
  = transportf _ (maponpaths (fun g => A[g,,C]) e) t.
Proof.
  destruct e. apply idpath.
Qed.

Lemma rterm_mapeq {Γ} {A : C⟨Γ⟩} {Γ'} {f f' : Γ' ⇒ Γ} (e : f = f') (t : C ⟨ Γ ⊢ A ⟩)
  : t ⟦ f ,,C ⟧
  = transportb _ (maponpaths (fun g => A[g,, C]) e) (t ⟦ f' ,, C⟧ ).
Proof.
  destruct e. apply idpath.
Qed.

(* A slightly odd statement, but very often useful.
   
   TODO: consider naming!
   TODO: try to use in proofs, instead of [transportf_pathscomp0] *)
Lemma term_typeeq_transport_lemma {Γ} {A A' A'': C ⟨ Γ ⟩} (e : A = A'') (e' : A' = A'')
  (x : C ⟨ Γ ⊢ A ⟩) (x' : C ⟨ Γ ⊢ A' ⟩)
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

Lemma term_typeeq_transport_lemma_2 {Γ} {A : C ⟨ Γ ⟩} (e : A = A)
  {x x' : C ⟨ Γ ⊢ A ⟩}
  : x = x'
  -> transportf _ e x = x'.
Proof.
  intros ex.
  apply @pathscomp0 with (transportf _ (idpath _) x).
    apply (maponpaths (fun p => transportf _ p x)).
    apply pre_cwf_types_isaset.
  exact ex.
Qed.

Lemma reindx_term_comp' {Γ Γ' Γ''} (γ : Γ' ⇒ Γ) (γ' : Γ'' ⇒ Γ') {A} (a : C ⟨ Γ ⊢ A ⟩)
  : transportf _ (reindx_type_comp C _ _ _) (a ⟦ γ' ;; γ ,, C⟧)
  = ((a ⟦ γ ,,C ⟧) ⟦ γ' ,, C⟧).
Proof.
  eapply pathscomp0.
    apply maponpaths, (reindx_term_comp C).
  eapply pathscomp0. apply transportf_pathscomp0.
  apply term_typeeq_transport_lemma_2. apply idpath.
Qed.

(* TODO: consider giving this instead of current [pre_cwf_law_2] ? *)
Definition pre_cwf_law_2' Γ (A : C ⟨ Γ ⟩) Γ' (γ : Γ' ⇒ Γ) (a : C ⟨ Γ' ⊢ A[γ,, C] ⟩)
  : (gen_elem C A) ⟦pairing C _ γ a,, C⟧
  = transportf _ (reindx_type_comp C _ _ _)
      (transportb _ (maponpaths (fun g => A[g,,C]) (pre_cwf_law_1 _ _ _ _ _ _))
        a). 
Proof.
  eapply pathscomp0. Focus 2.
    apply maponpaths, maponpaths. exact (pre_cwf_law_2 _ _ _ _ γ a).
  apply pathsinv0.
  (* TODO: try simplyfying with [term_typeeq_transport_lemma] *)
  eapply pathscomp0. apply transportf_pathscomp0.
  eapply pathscomp0. apply maponpaths, transportf_rtype_mapeq.
  eapply pathscomp0. apply transportf_pathscomp0.
  eapply pathscomp0. apply transportf_pathscomp0.
  refine (@maponpaths _ _ (fun e => transportf _ e _) _ (idpath _) _).
  apply pre_cwf_types_isaset.
Qed.


End CwF_lemmas.

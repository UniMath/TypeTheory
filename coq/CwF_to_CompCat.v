
Require Import Systems.UnicodeNotations.
Require Import Systems.CompCats.
Require Import Systems.cwf.

Local Notation "a ⇒ b" := (precategory_morphisms a b)(at level 50).
  (* \=> in Agda input method *)

Local Notation "g ∘ f" := (compose f g)(at level 50).
  (* \circ or \o in Agda input method *)

Local Notation "Γ ; a" := (comp_obj _ Γ a) (at level 45, left associativity).

(* Locally override the notation [ γ ♯ a ], at a higher level,
  to get more informative bracketing when pairing meets composition. *) 
Local Notation "γ # a" := (pairing _ _ _ _ γ a) (at level 75).


Section CompPreCat_of_PreCwF.

Context (C : pre_cwf).

Definition comp_precat1_of_precwf : comp_precat1.
Proof.
  exists C.
  unfold comp_precat_structure1.
  exists (type C).
  exists (comp_obj C).  
  exact (fun Γ a Γ' f => a[f]).
Defined.

Definition q_precwf {Γ} (a : type C Γ) {Γ'} (f : Γ' ⇒ Γ)
  : (comp_obj _ Γ' (a[f])) ⇒ (Γ ∙ a).
Proof.
  apply (pairing _ _ _ (Γ' ∙ (a[f])) (f ∘ π _)).
  refine (transportb (term C (Γ' ; (a [f])) ) (reindx_type_comp C _ _ a) _).
  apply gen_elem.
Defined.

Definition dpr_q_precwf 
  {c} (a : comp_precat1_of_precwf c)
  {c'} (f : c' ⇒ c)
: (π a) ∘ q_precwf a f = f ∘ (π (a[f])).
Proof.
  apply pre_cwf_law_1.
Qed.

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

Lemma rtype_typeeq {c} {a a': C ⟨ c ⟩} (e : a = a') {c'} (f : c' ⇒ c) (x : C ⟨ c ⊢ a ⟩)
  : transportf _ (maponpaths (fun b => b[f]) e) (x⟦f⟧)
    = (transportf _ e x) ⟦f⟧.
Proof.
  destruct e. apply idpath.
Qed.

Lemma rterm_mapeq {c} {a : C ⟨ c ⟩} {c'} (f f' : c' ⇒ c) (e : f = f')
                     (t : C ⟨ c' ⊢ a[f] ⟩)
  : transportf (fun g => C ⟨ c' ⊢ a[g] ⟩) e t
  = transportf _ (maponpaths (fun g => a[g]) e) t.
Proof.
  destruct e. apply idpath.
Qed.

(* TODO: surely there’s a library function for this? *)
Lemma transportf_pathscomp0 {A} {B} {a a' a'' : A} (e : a = a') (e' : a' = a'') (b : B a)
  : transportf B e' (transportf B e b) = transportf B (e @ e') b.
Proof.
  destruct e; apply idpath.
Defined.

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
  eapply pathscomp0. apply transportf_pathscomp0.
  eapply pathscomp0. apply maponpaths, rterm_mapeq.
  eapply pathscomp0. apply transportf_pathscomp0.
  eapply pathscomp0. apply transportf_pathscomp0.
  refine (@maponpaths _ _ (fun e => transportf _ e _) _ (idpath _) _).
  apply pre_cwf_types_isaset.
Qed.

Definition pre_cwf_law_2 (C : pre_cwf) Γ (A : C ⟨Γ⟩) Γ' (γ : Γ' ⇒ Γ) (a : C⟨Γ'⊢ A[γ]⟩)
  : transportf (λ ι, C⟨Γ'⊢ A [ι]⟩) (pre_cwf_law_1 C Γ A Γ' γ a)
    (transportf (λ B, C⟨Γ'⊢ B⟩) (!reindx_type_comp C (π _ )(γ ♯ a) _ ) 
      ((ν A) ⟦γ ♯ a⟧))
    = a
  := pr2 (pr1 (pr1 (pre_cwf_laws C)) Γ A Γ' γ a).

Definition dpr_q_pullback_exists_precwf
  {c} (a : comp_precat1_of_precwf c)
  {c'} (f : c' ⇒ c)
  {X} (h : X ⇒ c ∙ a) (k : X ⇒ c') (H : π a ∘ h = f ∘ k)
: Σ (hk : X ⇒ c' ∙ (a[f])),
    ( q_precwf a f ∘ hk = h
    × π (a[f]) ∘ hk = k).
Proof.
  set (νah' :=
    (transportf _ (reindx_type_comp C _ _ _)
      (transportf (fun g => C ⟨ X ⊢ a[g] ⟩) H
        (transportf _ (!reindx_type_comp C _ _ _)
          ((ν a)⟦h⟧))))
    : C ⟨ X ⊢ (a [f]) [k] ⟩).
  exists (pairing C c' (a[f]) X k νah'). simpl; split.
    unfold q_precwf.
    eapply pathscomp0. Focus 2.
      apply map_to_comp_as_pair_precwf.
    eapply pathscomp0.
      apply pre_cwf_law_3.
    assert ((f ∘ π (a [f])) ∘ (k # νah') = π a ∘ h) as e1.
      eapply pathscomp0. apply assoc.
      refine (_ @ !H).
      apply (maponpaths (fun g => f ∘ g)).
      apply pre_cwf_law_1.
    eapply pathscomp0.
      apply (pairing_mapeq _ _ e1).
    apply maponpaths.
    assert (a[f][π (a[f])][k # νah'] = a[π a ∘ h]) as e3.
      refine (!reindx_type_comp C _ _ _ @ _).
      refine (!reindx_type_comp C _ _ _ @ _).
      apply maponpaths. refine (! _ @ e1). apply assoc.
    apply @pathscomp0
      with (transportf _ e3 ((ν (a [f])) ⟦ k # νah' ⟧)).
      eapply pathscomp0. apply transportf_pathscomp0.
      eapply pathscomp0. apply maponpaths. refine (! rtype_typeeq _ _ _).
      eapply pathscomp0. apply transportf_pathscomp0.
      apply (maponpaths (fun e => transportf (term C X) e _)).
      apply pre_cwf_types_isaset.
    eapply pathscomp0.
      apply maponpaths. apply pre_cwf_law_2'.
    unfold νah'.
    eapply pathscomp0. apply transportf_pathscomp0.
    eapply pathscomp0. apply transportf_pathscomp0.
    eapply pathscomp0. apply transportf_pathscomp0.
    eapply pathscomp0. apply maponpaths, rterm_mapeq.
    eapply pathscomp0. apply transportf_pathscomp0.
    eapply pathscomp0. apply transportf_pathscomp0.
    refine (maponpaths (fun e => transportf _ e _) _).
    apply pre_cwf_types_isaset.
  apply pre_cwf_law_1.
Defined.

Definition comp_precat_of_precwf : comp_precat.
Proof.
  exists comp_precat1_of_precwf.
  unfold comp_precat_structure2.
  exists (proj_mor C).
  exists @q_precwf.
  exists @dpr_q_precwf.
  unfold isPullback; intros. simpl in *.
  exists (dpr_q_pullback_exists_precwf _ _ h k H).
  intros [hk [e1 e2]].
  (* Should only need to show first components equal;
     rest will follow by morphisms being a set. *) 
Abort.

End CompPreCat_of_PreCwF.

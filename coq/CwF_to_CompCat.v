
Require Import total2_paths.

Require Import Systems.Auxiliary.
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

Context (C : pre_cwf) (homs_sets : has_homsets C).

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

Lemma rterm_univ {c} {a : C ⟨ c ⟩} {c'} (f : c' ⇒ c)
  : ν (a[f])
   = transportf _ (reindx_type_comp C _ _ _)
       (transportf _ (maponpaths (fun g => a[g]) (dpr_q_precwf a f))
         (transportb _ (reindx_type_comp C _ _ _)
            ((ν a)⟦q_precwf a f⟧))).
Proof.
  symmetry.
  eapply pathscomp0. apply transportf_pathscomp0.
  eapply pathscomp0. apply transportf_pathscomp0.
  eapply pathscomp0.
    apply maponpaths.
    apply pre_cwf_law_2'.
  eapply pathscomp0. apply transportf_pathscomp0.
  eapply pathscomp0. apply transportf_pathscomp0.
  eapply pathscomp0. apply transportf_pathscomp0.
  apply (term_typeeq_transport_lemma _ (idpath _)).
  apply term_typeeq_transport_lemma_2.
  apply idpath.
Qed.


Definition dpr_q_pbpairing_precwf
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
  (* TODO: try simplyfying with [term_typeeq_transport_lemma] *)
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
      eapply pathscomp0. apply maponpaths. refine (! rterm_typeeq _ _ _).
      eapply pathscomp0. apply transportf_pathscomp0.
      apply (maponpaths (fun e => transportf (term C X) e _)).
      apply pre_cwf_types_isaset.
    eapply pathscomp0.
      apply maponpaths. apply pre_cwf_law_2'.
    unfold νah'.
    eapply pathscomp0. apply transportf_pathscomp0.
    eapply pathscomp0. apply transportf_pathscomp0.
    eapply pathscomp0. apply transportf_pathscomp0.
    eapply pathscomp0. apply maponpaths, transportf_rtype_mapeq.
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
  exists (dpr_q_pbpairing_precwf _ _ h k H).

  intros [hk [e2 e1]].
  assert (hk = pr1 (dpr_q_pbpairing_precwf a f h k H)). simpl.
    eapply pathscomp0.
      symmetry. apply map_to_comp_as_pair_precwf.
    eapply pathscomp0.
      apply (pairing_mapeq _ _ e1 _).
    apply maponpaths.
    eapply pathscomp0.
      apply maponpaths, maponpaths. 
      apply (@maponpaths (C ⟨ c'; (a[f]) ⊢ a[f][π (a[f])] ⟩) _ (fun t => t ⟦hk⟧)).
      apply rterm_univ.
    eapply pathscomp0.
      apply maponpaths, maponpaths. 
      eapply pathscomp0.
        symmetry. apply rterm_typeeq.
      apply maponpaths.
      eapply pathscomp0.
        symmetry. apply rterm_typeeq.
      apply maponpaths.
      eapply pathscomp0.
        symmetry. apply rterm_typeeq.
      apply maponpaths.
      symmetry. apply reindx_term_comp'.
    eapply pathscomp0.
      apply maponpaths, maponpaths, maponpaths, maponpaths, maponpaths, maponpaths.
      apply (rterm_mapeq e2).
    apply term_typeeq_transport_lemma.
    symmetry. eapply pathscomp0.
      apply transportf_rtype_mapeq.
    eapply pathscomp0.
      apply transportf_pathscomp0.
    apply term_typeeq_transport_lemma.
    apply term_typeeq_transport_lemma.
    apply term_typeeq_transport_lemma.
    apply term_typeeq_transport_lemma.
    apply term_typeeq_transport_lemma.
    apply term_typeeq_transport_lemma.
    apply term_typeeq_transport_lemma.
    apply term_typeeq_transport_lemma_2.
    apply idpath.
  refine (@total2_paths _ _ (tpair _ hk (tpair _ e2 e1)) _ X _).
  refine (total2_paths _ _).
  apply homs_sets.
  apply homs_sets.
Defined.


End CompPreCat_of_PreCwF.

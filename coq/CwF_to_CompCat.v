
Require Import total2_paths.

Require Import Systems.Auxiliary.
Require Import Systems.UnicodeNotations.
Require Import Systems.CompCats.
Require Import Systems.cwf.

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

Definition q_precwf {Γ} (A : C ⟨ Γ ⟩ ) {Γ'} (f : Γ' ⇒ Γ)
  : (comp_obj _ Γ' (A[f])) ⇒ (Γ ∙ A).
Proof.
  apply (pairing _ _ _ (Γ' ∙ (A[f])) (π _ ;; f)).
  refine (transportb (term C (Γ' ∙ (A [f])) ) (reindx_type_comp C _ _ A) _).
  apply gen_elem.
Defined.

Definition dpr_q_precwf 
  {Γ} (A : C ⟨ Γ ⟩)
  {Γ'} (f : Γ' ⇒ Γ)
: (q_precwf A f) ;; (π A) = (π (A[f])) ;; f.
Proof.
  apply pre_cwf_law_1.
Qed.

Lemma rterm_univ {Γ} {A : C ⟨ Γ ⟩} {Γ'} (f : Γ' ⇒ Γ)
  : ν (A[f])
   = transportf _ (reindx_type_comp C _ _ _)
       (transportf _ (maponpaths (fun g => A[g]) (dpr_q_precwf A f))
         (transportb _ (reindx_type_comp C _ _ _)
            ((ν A)⟦q_precwf A f⟧))).
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

Definition dpr_q_pbpairing_precwf_aux
  {Γ} (A : C ⟨ Γ ⟩)
  {Γ'} (f : Γ' ⇒ Γ)
  {X} (h : X ⇒ Γ ∙ A) (k : X ⇒ Γ') (H : h ;; π A = k ;; f)
: C ⟨ X ⊢ (A [f]) [k] ⟩
:= (transportf _ (reindx_type_comp C _ _ _)
      (transportf (fun g => C ⟨ X ⊢ A[g] ⟩) H
        (transportf _ (!reindx_type_comp C _ _ _)
          ((ν A)⟦h⟧)))).

Definition dpr_q_pbpairing_commutes
  {Γ} (A : C ⟨ Γ ⟩)
  {Γ'} (f : Γ' ⇒ Γ)
  {X} (h : X ⇒ Γ ∙ A) (k : X ⇒ Γ') (H : h ;; π A = k ;; f)
  (hk := pairing C Γ' (A[f]) X k (dpr_q_pbpairing_precwf_aux A f h k H))
: (hk ;; q_precwf A f = h) × (hk ;; π (A[f]) = k).
Proof.
  split. Focus 2. apply pre_cwf_law_1.
  unfold q_precwf.
  eapply pathscomp0. Focus 2.
    apply map_to_comp_as_pair_precwf.
  eapply pathscomp0.
    apply pre_cwf_law_3.
  assert ((k # (dpr_q_pbpairing_precwf_aux A f h k H)) ;; (π (A [f]) ;; f) 
          = h ;; π A) as e1.
    eapply pathscomp0. apply assoc.
    refine (_ @ !H).
    apply (maponpaths (fun g => g ;; f)).
    apply pre_cwf_law_1.
  eapply pathscomp0. apply (pairing_mapeq _ _ e1).
  apply maponpaths.
  eapply pathscomp0. apply transportf_pathscomp0.
  eapply pathscomp0. apply maponpaths. refine (! rterm_typeeq _ _ _).
  eapply pathscomp0. apply transportf_pathscomp0.
  eapply pathscomp0. apply maponpaths, pre_cwf_law_2'.
  eapply pathscomp0. apply transportf_pathscomp0.
  eapply pathscomp0. apply transportf_pathscomp0.
  eapply pathscomp0. apply transportf_pathscomp0.
  eapply pathscomp0. apply maponpaths, transportf_rtype_mapeq.
  eapply pathscomp0. apply transportf_pathscomp0.
  eapply pathscomp0. apply transportf_pathscomp0.
  refine (maponpaths (fun e => transportf _ e _) _).
  apply pre_cwf_types_isaset.
Qed.

Definition dpr_q_pbpairing_precwf
  {Γ} (A : C ⟨ Γ ⟩)
  {Γ'} (f : Γ' ⇒ Γ)
  {X} (h : X ⇒ Γ ∙ A) (k : X ⇒ Γ') (H : h ;; π A = k ;; f)
: Σ (hk : X ⇒ Γ' ∙ (A[f])),
    ( hk ;; q_precwf A f = h
    × hk ;; π (A[f]) = k).
Proof.
  exists (pairing C Γ' (A[f]) X k (dpr_q_pbpairing_precwf_aux A f h k H)).
  apply dpr_q_pbpairing_commutes.
Defined.


Definition dpr_q_pbpairing_precwf_mapunique
  {Γ} (A : comp_precat1_of_precwf Γ)
  {Γ'} (f : Γ' ⇒ Γ)
  {X} {h : X ⇒ Γ ∙ A} {k : X ⇒ Γ'} (H : h ;; π A = k ;; f)
  (hk : X ⇒ Γ' ◂ A[f])
  (e2 : hk ;; q_precwf A f = h)
  (e1 : hk ;; π (A[f]) = k)
: hk = pr1 (dpr_q_pbpairing_precwf A f h k H).
Proof.
  eapply pathscomp0.
    symmetry. apply map_to_comp_as_pair_precwf.
  eapply pathscomp0.
    apply (pairing_mapeq _ _ e1 _).
  simpl. apply maponpaths.
  eapply pathscomp0.
    apply maponpaths, maponpaths. 
    apply (@maponpaths (C ⟨ Γ' ∙ (A[f]) ⊢ A[f][π (A[f])] ⟩) _ (fun t => t ⟦hk⟧)).
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
  apply term_typeeq_transport_lemma.
  eapply pathscomp0. apply transportf_pathscomp0.
  eapply pathscomp0. apply transportf_pathscomp0.
  eapply pathscomp0. apply transportf_pathscomp0.
  eapply pathscomp0. apply transportf_pathscomp0.
  eapply pathscomp0. apply transportf_pathscomp0.
  eapply pathscomp0.
    apply maponpaths, (rterm_mapeq e2).
  eapply pathscomp0. apply transportf_pathscomp0.
  eapply pathscomp0.
    Focus 2. symmetry. apply transportf_rtype_mapeq.
  repeat apply term_typeeq_transport_lemma. 
  apply term_typeeq_transport_lemma_2.
  apply idpath.
Qed.

Definition dpr_q_pbpairing_precwf_unique
  {Γ} (A : comp_precat1_of_precwf Γ)
  {Γ'} (f : Γ' ⇒ Γ)
  {X} (h : X ⇒ Γ ∙ A) (k : X ⇒ Γ') (H : h ;; π A = k ;; f)
  (t : Σ hk : X ⇒ Γ' ◂ A[f],
       (hk ;; q_precwf A f = h) × (hk ;; π (A[f]) = k))
: t = dpr_q_pbpairing_precwf A f h k H.
Proof.
  destruct t as [hk [e2 e1]].
  refine (@total2_paths _ _ (tpair _ hk (tpair _ e2 e1)) _ 
    (dpr_q_pbpairing_precwf_mapunique A f H hk e2 e1) _).
  refine (total2_paths _ _); apply homs_sets.
Qed.

Definition comp_precat_of_precwf : comp_precat.
Proof.
  exists comp_precat1_of_precwf.
  unfold comp_precat_structure2.
  exists (proj_mor C).
  exists @q_precwf.
  exists @dpr_q_precwf.
  unfold isPullback; intros.
  exists (dpr_q_pbpairing_precwf _ _ h k H).
  apply dpr_q_pbpairing_precwf_unique.
Defined.

End CompPreCat_of_PreCwF.

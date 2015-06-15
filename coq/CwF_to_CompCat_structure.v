
Require Import UniMath.RezkCompletion.total2_paths.

Require Import Systems.Auxiliary.
Require Import Systems.UnicodeNotations.
Require Import Systems.CompCat_structure.
Require Import Systems.cwf_structure.

(* Suppress these preliminaries in the Coqdoc documentation: *)
(* begin hide *)
(* Locally override the notation [ γ ♯ a ], at a higher level,
  to get more informative bracketing when pairing meets composition. *) 
Local Notation "γ # a" := (pairing γ a) (at level 75).

Section Prelims.

(* TODO: move to [cwf] *)
Definition pairing_transport {CC : precategory} (C : cwf_struct CC) {Γ} {A A' : C⟨Γ⟩} (e : A = A')
  {Γ'} (γ : Γ' ⇒ Γ) (a : C ⟨Γ'⊢A[γ]⟩)
: (γ # a) ;; idtoiso (maponpaths (fun (B : C⟨Γ⟩) => Γ∙B) e)
= (γ # (transportf (fun B => C ⟨ Γ' ⊢ B [γ] ⟩) e a)).
Proof.
  destruct e; simpl.
  apply id_right.
Defined.

(* TODO: generalise; really it’s about any [transportf] along any [maponpaths]. *)
Lemma transportf_maponpaths {CC : precategory} {C : cwf_struct CC} {Γ} {B B' : C⟨Γ⟩} (e : B = B')
  {Γ'} (f : Γ' ⇒ Γ) (b : C ⟨ Γ' ⊢ B[f] ⟩)
: transportf (term C Γ') (maponpaths (fun D => D[f]) e) b
  = transportf (fun D => term C Γ' (D[f])) e b.
Proof.
  apply pathsinv0.
  apply (@functtransportf _ _ (λ D : C ⟨Γ⟩, D [f])).
Defined.

End Prelims.
(* end hide *)


(** * Comprehension pre-precats from pre-cats with families

Every pre-CwF gives rise to a comprehension pre-category.

(TODO: moreover, this comprehension pre-cat should be split; and there should be a function from split comprehension pre-cats back to pre-CwFs making the two equivalent.)

Since the components of the comprehension pre-cat structure are highly successively dependent, we construct most of them individually, before putting them together in [comp_precat_of_precwf].
*)

Section CompPreCat_of_PreCwF.

(* TODO: move the [has_homsets] assumption to the definition of a [pre_cwf]? 
   TODO: discuss namine of [has_homsets]: wouldn’t e.g. [homs_are_sets] be clearer? *)
Context (CC : precategory) (C : cwf_struct CC) (homs_sets : has_homsets CC).

Definition comp_precat1_of_precwf : comp_precat_structure1 CC.
Proof.
  unfold comp_precat_structure1.
  exists (type C).
  exists (comp_obj ).  
  exact (fun Γ a Γ' f => a[f]).
Defined.

Definition q_precwf {Γ} (A : C ⟨ Γ ⟩ ) {Γ'} (f : Γ' ⇒ Γ)
  : (comp_obj  Γ' (A[f])) ⇒ (Γ ∙ A).
Proof.
  set (T:= @pairing _ C).
  apply T with (γ := π _ ;; f).
  refine (transportb (term C (Γ' ∙ (A [f])) ) (reindx_type_comp C _ _ A) _).
  apply gen_elem.
Defined.

Definition dpr_q_precwf 
  {Γ} (A : C ⟨ Γ ⟩)
  {Γ'} (f : Γ' ⇒ Γ)
: (q_precwf A f) ;; (π A) = (π (A[f])) ;; f.
Proof.
  unfold q_precwf.
  apply cwf_law_1.
Qed.


Lemma rterm_univ {Γ} {A : C ⟨ Γ ⟩} {Γ'} (f : Γ' ⇒ Γ)
  : ν (A[f])
   = transportf _ (reindx_type_comp C _ _ _)
       (transportf _ (maponpaths (fun g => A[g]) (dpr_q_precwf A f))
         (transportb _ (reindx_type_comp C _ _ _)
            ((ν A)⟦q_precwf A f⟧))).
Proof.
  sym.
  rew_trans_@.
  etrans.
  - apply maponpaths.
    apply pre_cwf_law_2'.
  - rew_trans_@.
    apply term_typeeq_transport_lemma_2.
    apply idpath.
Qed.

(** The biggest work is in showing that the square of dependent projections/reindexings is a pullback.  We split this up into several lemmas: construction of the pullback pairing function; proof that projections applied to the pairing recover the original maps; and proof that the pairing map is the unique such map. *)

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
  (hk := @pairing _ C Γ' (A[f]) X k (dpr_q_pbpairing_precwf_aux A f h k H))
: (hk ;; q_precwf A f = h) × (hk ;; π (A[f]) = k).
Proof.
  split. Focus 2. apply cwf_law_1.
  unfold q_precwf.
  etrans. Focus 2.
    apply map_to_comp_as_pair_precwf.
  etrans.
    apply cwf_law_3.
  assert ((k # (dpr_q_pbpairing_precwf_aux A f h k H)) ;; (π (A [f]) ;; f) 
          = h ;; π A) as e1.
    eapply pathscomp0. apply assoc.
    refine (_ @ !H).
    apply (maponpaths (fun g => g ;; f)).
    apply cwf_law_1.
  eapply pathscomp0. apply (pairing_mapeq _ _ e1).
  apply maponpaths.
  eapply pathscomp0. apply transportf_pathscomp0.
  eapply pathscomp0. apply maponpaths. refine (! rterm_typeeq _ _ _).
  eapply pathscomp0. apply transportf_pathscomp0.
  eapply pathscomp0. apply maponpaths, pre_cwf_law_2'.
  rew_trans_@.
  eapply pathscomp0. apply maponpaths, transportf_rtype_mapeq.
  repeat (eapply pathscomp0; [ apply transportf_pathscomp0 | ]).
  refine (maponpaths (fun e => transportf _ e _) _).
  apply cwf_types_isaset.
Qed.

Definition dpr_q_pbpairing_precwf
  {Γ} (A : C ⟨ Γ ⟩)
  {Γ'} (f : Γ' ⇒ Γ)
  {X} (h : X ⇒ Γ ∙ A) (k : X ⇒ Γ') (H : h ;; π A = k ;; f)
: Σ (hk : X ⇒ Γ' ∙ (A[f])),
    ( hk ;; q_precwf A f = h
    × hk ;; π (A[f]) = k).
Proof.
  exists (@pairing _ C Γ' (A[f]) X k (dpr_q_pbpairing_precwf_aux A f h k H)).
  apply dpr_q_pbpairing_commutes.
Defined.


Definition dpr_q_pbpairing_precwf_mapunique
  {Γ} (A : comp_precat1_of_precwf Γ)
  {Γ'} (f : Γ' ⇒ Γ)
  {X} {h : X ⇒ Γ ∙ A} {k : X ⇒ Γ'} (H : h ;; π A = k ;; f)
  (hk : X ⇒ Γ' ◂ reind_comp_cat A f)
  (e2 : hk ;; q_precwf A f = h)
  (e1 : hk ;; π (A[f]) = k)
: hk = pr1 (dpr_q_pbpairing_precwf A f h k H).
Proof.
  eapply pathscomp0.
    eapply pathsinv0. apply map_to_comp_as_pair_precwf.
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
  repeat (eapply pathscomp0; [ apply transportf_pathscomp0 |]).
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
  (t : Σ hk : X ⇒ Γ' ◂ reind_comp_cat A f,
       (hk ;; q_precwf A f = h) × (hk ;; π (A[f]) = k))
: t = dpr_q_pbpairing_precwf A f h k H.
Proof.
  destruct t as [hk [e2 e1]]. 
  refine (@total2_paths _ _ (tpair _ hk (tpair _ e2 e1)) _ 
    (dpr_q_pbpairing_precwf_mapunique A f H hk e2 e1) _).
  refine (total2_paths _ _); apply homs_sets.
Qed.

(** We can now assemble the components into a comprehension precategory: *)

Definition comp_precat_of_precwf : comp_precat_struct CC.
Proof.
  exists comp_precat1_of_precwf.
  unfold comp_precat_structure2.
  exists (@proj_mor CC C).
  exists @q_precwf.
  exists @dpr_q_precwf.
  unfold isPullback; intros.
  exists (dpr_q_pbpairing_precwf _ _ h k H).
  apply dpr_q_pbpairing_precwf_unique.
Defined.

(** Moreover, the comprehension precat of a pre-CwF is always split. *)

Definition issplit_comp_precat_of_precwf
  : is_split_comp_cat comp_precat_of_precwf.
Proof.
  unfold is_split_comp_cat.
  repeat split. 
  - (* Types over each object form a set *)
    apply cwf_types_isaset.
  - (* Reindexing along identities *)
    exists (reindx_type_id C).
    intros Γ A. 
    unfold q_comp_cat; simpl. unfold q_precwf.
    eapply pathscomp0. Focus 2. apply id_left.
    eapply pathscomp0. Focus 2.
      refine (maponpaths (fun q => q ;; _) _).
      Unfocus.
    eapply pathscomp0. Focus 2.
      symmetry. apply pairing_transport.
      Focus 2. apply cwf_law_4.
    eapply pathscomp0.
    apply (pairing_mapeq _ _ (id_right _ _ _ _)).
    apply maponpaths. simpl.
    eapply pathscomp0. apply transportf_pathscomp0.
    refine (_ @ _).
      exact (transportf (term C (Γ ◂ reind_comp_cat A (identity Γ)))
        (maponpaths (fun B => B [π (A [identity Γ])]) (reindx_type_id C Γ A))
        (ν (A [identity Γ]))).
    apply term_typeeq_transport_lemma.
    apply term_typeeq_transport_lemma_2.
    reflexivity.
    apply transportf_maponpaths.
  - (* Reindexing along composites *)
    exists (fun Γ A Γ' f Γ'' g => reindx_type_comp C f g A).
    intros Γ A Γ' f Γ'' g.
    unfold q_comp_cat. simpl. 
    match goal with [|- _ = ?e ] => 
           pathvia (identity _ ;; e); [| apply id_left] end.
    rewrite assoc.
    rewrite assoc.
    unfold ext_comp_cat. simpl.
    rewrite <- cwf_law_4.
    rewrite pairing_transport.
    unfold q_precwf. 
    rewrite cwf_law_3.
    match goal with [|- pairing ?b _ = pairing ?e _ ] => 
              set (X := b); set (X' := e)  end.
    etrans.
    + refine (pairing_mapeq _ X' _ _ ).
      unfold X; clear X; unfold X'; clear X'.
      etrans. Focus 2.  eapply pathsinv0.
            cancel_postcomposition. apply cwf_law_3.
      etrans. Focus 2. eapply pathsinv0.  apply assoc.
      etrans. apply assoc.
      cancel_postcomposition.
      etrans. Focus 2. eapply pathsinv0. apply cwf_law_1.
      etrans; [ | eapply pathsinv0; apply assoc ].
      cancel_postcomposition. sym. apply cwf_law_1.
    + apply maponpaths.
      rew_trans_@.
      apply term_typeeq_transport_lemma.
      etrans. Focus 2.
      apply rterm_typeeq.
      admit.

Admitted.

End CompPreCat_of_PreCwF.

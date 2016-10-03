
(** 
  
 Ahrens, Lumsdaine, Voevodsky, 2015

Contents:

  - Construction of a type-precategory from a precategory with Families
  - Proof that the constructed type-precategory is split

*)


Require Import UniMath.CategoryTheory.total2_paths.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.
Require Import TypeTheory.OtherDefs.TypeCat.
Require Import TypeTheory.OtherDefs.CwF_Pitts.

Set Automatic Introduction.

(* Locally override the notation [ γ ♯ a ], at a higher level,
  to get more informative bracketing when pairing meets composition. *) 
Local Notation "γ ## a" := (pairing γ a) (at level 75).

Section Prelims.

(* TODO: move to [cwf] *)
Definition pairing_transport {CC : precategory} (C : cwf_struct CC) {Γ} {A A' : C⟨Γ⟩} (e : A = A')
  {Γ'} (γ : Γ' --> Γ) (a : C ⟨Γ'⊢A[γ]⟩)
: (γ ## a) ;; idtoiso (maponpaths (fun (B : C⟨Γ⟩) => Γ∙B) e)
= (γ ## (transportf (fun B => C ⟨ Γ' ⊢ B [γ] ⟩) e a)).
Proof.
  destruct e; simpl.
  apply id_right.
Defined.

(* TODO: generalise; really it’s about any [transportf] along any [maponpaths]. *)
Lemma transportf_maponpaths {CC : precategory} {C : cwf_struct CC} {Γ} {B B' : C⟨Γ⟩} (e : B = B')
  {Γ'} (f : Γ' --> Γ) (b : C ⟨ Γ' ⊢ B[f] ⟩)
: transportf (term C Γ') (maponpaths (fun D => D[f]) e) b
  = transportf (fun D => term C Γ' (D[f])) e b.
Proof.
  apply pathsinv0.
  apply (@functtransportf _ _ (λ D : C ⟨Γ⟩, D [f])).
Defined.

End Prelims.


(** * Type-precat from precat with Families *)

(**
Every pre-CwF gives rise to a type-precategory.

(TODO: moreover, this type-precat should be split; and there should be a function from split type-precats back to pre-CwFs making the two equivalent.)

Since the components of the type-precat structure are highly successively dependent, we construct most of them individually, before putting them together in [type_precat_of_precwf].
*)


Section TypePreCat_of_PreCwF.

(* TODO: move the [has_homsets] assumption to the definition of a [pre_cwf]? 
   TODO: discuss namine of [has_homsets]: wouldn’t e.g. [homs_are_sets] be clearer? *)
Context (CC : precategory) (C : cwf_struct CC) (homs_sets : has_homsets CC).

Definition type_cat1_of_precwf : type_cat_struct1 CC.
Proof.
  unfold type_cat_struct1.
  exists (type C).
  exists (comp_obj ).  
  exact (fun Γ a Γ' f => a[f]).
Defined.

(** We can now assemble the components into a type-precategory: *)

Definition type_cat_of_precwf : type_cat_struct CC.
Proof.
  exists type_cat1_of_precwf.
  unfold type_cat_struct2.
  exists (@proj_mor CC C).
  exists (@q_precwf CC C).
  exists (@dpr_q_precwf CC C).
  apply is_pullback_reindx_cwf.
  assumption.
Defined.

(** * Splitness of the constructed TypeCat *)

(** Moreover, the type-precat of a pre-CwF is always split. *)

Definition issplit_type_precat_of_precwf
  : is_split_type_cat type_cat_of_precwf.
Proof.
  unfold is_split_type_cat.
  repeat split. 
  - (* Types over each object form a set *)
    apply cwf_types_isaset.
  - (* Reindexing along identities *)
    exists (reindx_type_id C).
    intros Γ A. 
    unfold q_type_cat; simpl. unfold q_precwf.
    eapply pathscomp0. Focus 2. apply id_left.
    eapply pathscomp0. Focus 2.
      refine (maponpaths (fun q => q ;; _) _).
      Unfocus.
    eapply pathscomp0. Focus 2.
      symmetry. apply pairing_transport.
      Focus 2. apply cwf_law_4.
    eapply pathscomp0.
    apply (pairing_mapeq _ _ (id_right _ )).
    apply maponpaths. simpl.
    eapply pathscomp0. apply transport_f_f.
    unshelve refine (_ @ _).
      exact (transportf (term C (Γ ◂ reind_type_cat A (identity Γ)))
        (maponpaths (fun B => B [π (A [identity Γ])]) (reindx_type_id C Γ A))
        (ν (A [identity Γ]))).
    apply term_typeeq_transport_lemma.
    apply term_typeeq_transport_lemma_2.
    reflexivity.
    apply transportf_maponpaths.
  - (* Reindexing along composites *)
    exists (fun Γ A Γ' f Γ'' g => reindx_type_comp C f g A).
    intros Γ A Γ' f Γ'' g.
    unfold q_type_cat. simpl. 
    match goal with [|- _ = ?e ] => 
           pathvia (identity _ ;; e); [| apply id_left] end.
    rewrite assoc.
    rewrite assoc.
    unfold ext_type_cat. simpl.
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
      match goal with |[ |- transportf _ ?e _ = transportf _ ?e' _  ] =>
                       generalize e; generalize e' end.
      intros p p'.
      rew_trans_@.
      apply term_typeeq_transport_lemma.
      etrans. Focus 2.
      apply rterm_typeeq.
      match goal with |[ |- transportf _ ?e _ = transportf _ ?e' _  ] =>
                       generalize e; generalize e' end.
      clear p p'.
      intros p p'.
      clear X'.
      rewrite  (reindx_term_comp C).
      rewrite transport_f_f.
      match goal with |[ |- transportf _ ?e _ = transportf _ ?e' _  ] =>
                       generalize e' end.
      clear p.
      intro p.
      rewrite pre_cwf_law_2'.
      unfold transportb.
      rewrite transport_f_f.
      rewrite transport_f_f.
      apply term_typeeq_transport_lemma.
      match goal with |[ |- _ = transportf _ ?e _ ⟦ _ ⟧ ] => generalize e end.
      intro q.
      etrans. Focus 2. apply rterm_typeeq.
      rewrite  pre_cwf_law_2'.
      rewrite transport_f_f.
      unfold transportb.
      rewrite transport_f_f.
      match goal with |[ |- transportf _ ?e _ = transportf _ ?e' _  ] =>
                       generalize e; generalize e' end.
      intros P P'. clear p q. clear p'.
      
      match goal with |[ |- _ = transportf _ _  (transportf _ ?e' _ ) ] =>
                       set (Q:=e') end.
    
      apply term_typeeq_transport_lemma.
      match goal with |[ |- transportf _ ?e _ = transportf _ ?e' _  ] =>
                       generalize e end.
      intro p.
      clear P P'.
      clear X.
      assert (X : p = maponpaths (fun x => x [π (A [g ;; f])]) Q).
      { apply cwf_types_isaset. }
      rewrite X.
      apply pathsinv0. apply retype_term_pi.
Qed.


End TypePreCat_of_PreCwF.


(** 
  
 Ahrens, Lumsdaine, Voevodsky, 2015

Contents:

  - Construction of a type-category from a category with Families
  - Proof that the constructed type-category is split

*)


Require Import UniMath.CategoryTheory.limits.pullbacks.

Require Import UniMath.Foundations.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.
Require Import TypeTheory.Auxiliary.Auxiliary.

Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.OtherDefs.CwF_Pitts.

(* Locally override the notation [ γ ♯ a ], at a higher level,
  to get more informative bracketing when pairing meets composition. *) 
Local Notation "γ ## a" := (pairing γ a) (at level 75).

Section Prelims.

(* TODO: move to [cwf] *)
Definition pairing_transport {CC : category} (C : cwf_struct CC) {Γ} {A A' : C⟨Γ⟩} (e : A = A')
  {Γ'} (γ : Γ' --> Γ) (a : C ⟨Γ'⊢A{{γ}}⟩)
: (γ ## a) ;; idtoiso (maponpaths (fun (B : C⟨Γ⟩) => Γ∙B) e)
= (γ ## (transportf (fun B => C ⟨ Γ' ⊢ B {{γ}}⟩) e a)).
Proof.
  destruct e; simpl.
  apply id_right.
Defined.

(* TODO: generalise; really it’s about any [transportf] along any [maponpaths]. *)
Lemma transportf_maponpaths {CC : category} {C : cwf_struct CC} {Γ} {B B' : C⟨Γ⟩} (e : B = B')
  {Γ'} (f : Γ' --> Γ) (b : C ⟨ Γ' ⊢ B{{f}} ⟩)
: transportf (term C Γ') (maponpaths (fun D => D{{f}}) e) b
  = transportf (fun D => term C Γ' (D{{f}})) e b.
Proof.
  apply pathsinv0.
  apply (@functtransportf _ _ (λ D : C ⟨Γ⟩, D {{f}})).
Defined.

End Prelims.


(** * Type-cat from cat with Families *)

(**
Every CwF gives rise to a type-category.

(TODO: moreover, this type-cat should be split; and there should be a function from split type-cats back to CwFs making the two equivalent.)

Since the components of the type-cat structure are highly successively dependent, we construct most of them individually, before putting them together in [type_cat_of_cwf].
*)


Section TypeCat_of_CwF.

Context (CC : category) (C : cwf_struct CC).

Definition type_cat1_of_cwf : typecat_structure1 CC.
Proof.
  unfold typecat_structure1.
  exists (type C).
  exists (comp_obj ).  
  exact (fun Γ a Γ' f => a{{f}}).
Defined.

(** We can now assemble the components into a type-category: *)

Definition type_cat_of_cwf : typecat_structure CC.
Proof.
  exists type_cat1_of_cwf.
  unfold typecat_structure2.
  exists (@proj_mor CC C).
  exists (@q_cwf CC C).
  exists (@dpr_q_cwf CC C).
  intros; apply @is_symmetric_isPullback. { apply homset_property. }
  apply is_pullback_reindx_cwf.
Defined.

(** * Splitness of the constructed TypeCat *)

(** Moreover, the type-cat of a CwF is always split. *)

Definition issplit_type_cat_of_cwf
  : is_split_typecat type_cat_of_cwf.
Proof.
  unfold is_split_typecat.
  repeat split. 
  - (* Types over each object form a set *)
    apply cwf_types_isaset.
  - (* Reindexing along identities *)
    exists (reindx_type_id C).
    intros Γ A. 
    unfold q_typecat; simpl. unfold q_cwf.
    eapply pathscomp0. 2: { apply id_left. }
    eapply pathscomp0.
    2: refine (maponpaths (fun q => q ;; _) _).    
    eapply pathscomp0. 2: { symmetry. apply pairing_transport. }
    2: { apply cwf_law_4. }
    eapply pathscomp0.
    apply (pairing_mapeq _ _ (id_right _ )).
    apply maponpaths. simpl.
    eapply pathscomp0. apply transport_f_f.
    unshelve refine (_ @ _).
      exact (transportf (term C (Γ ◂ reind_typecat A (identity Γ)))
        (maponpaths (fun B => B {{π (A {{identity Γ}})}}) (reindx_type_id C Γ A))
        (ν (A {{identity Γ}}))).
    apply term_typeeq_transport_lemma.
    apply term_typeeq_transport_lemma_2.
    reflexivity.
    apply transportf_maponpaths.
  - (* Reindexing along composites *)
    exists (fun Γ A Γ' f Γ'' g => reindx_type_comp C f g A).
    intros Γ A Γ' f Γ'' g.
    unfold q_typecat. simpl. 
    match goal with [|- _ = ?e ] => 
           intermediate_path (identity _ ;; e); [| apply id_left] end.
    rewrite assoc.
    rewrite assoc.
    unfold ext_typecat. simpl.
    rewrite <- cwf_law_4.
    rewrite pairing_transport.
    unfold q_cwf. 
    rewrite cwf_law_3.
    match goal with [|- pairing ?b _ = pairing ?e _ ] => 
              set (X := b); set (X' := e)  end.
    etrans.
    + refine (pairing_mapeq _ X' _ _ ).
      unfold X; clear X; unfold X'; clear X'.
      etrans. 2: { apply pathsinv0, maponpaths_2, cwf_law_3. }
      etrans. 2: { apply pathsinv0, assoc. }
      etrans. apply assoc.
      apply maponpaths_2.
      etrans. 2: { apply pathsinv0, cwf_law_1. }
      etrans. 2: { apply pathsinv0, assoc. }
      apply maponpaths_2. sym. apply cwf_law_1.
    + apply maponpaths.
      match goal with |[ |- transportf _ ?e _ = transportf _ ?e' _  ] =>
                       generalize e; generalize e' end.
      intros p p'.
      rew_trans_@.
      apply term_typeeq_transport_lemma.
      etrans. 2:{ apply rterm_typeeq. }
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
      rewrite cwf_law_2'.
      unfold transportb.
      rewrite transport_f_f.
      rewrite transport_f_f.
      apply term_typeeq_transport_lemma.
      match goal with |[ |- _ = transportf _ ?e _ ⟦ _ ⟧ ] => generalize e end.
      intro q.
      etrans. 2: { apply rterm_typeeq. }
      rewrite  cwf_law_2'.
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
      assert (X : p = maponpaths (fun x => x {{π (A {{g ;; f}})}}) Q).
      { apply cwf_types_isaset. }
      rewrite X.
      apply pathsinv0. apply retype_term_pi.
Qed.


End TypeCat_of_CwF.

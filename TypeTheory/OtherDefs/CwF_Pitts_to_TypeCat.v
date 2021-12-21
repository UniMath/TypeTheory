
(** 
  
 Ahrens, Lumsdaine, Voevodsky, 2015

Contents:

  - Construction of a type-category from a category with Families
  - Proof that the constructed type-category is split

*)


Require Import UniMath.CategoryTheory.limits.pullbacks.

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.
Require Import TypeTheory.Auxiliary.Auxiliary.

Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.OtherDefs.CwF_Pitts.

(* Locally override the notation [ γ ♯ a ], at a higher level,
  to get more informative bracketing when pairing meets composition. *) 
Local Notation "γ ## a" := (pairing γ a) (at level 75).

(** * Type-cat from cat with Families *)

(**
Every CwF gives rise to a type-category.

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
  intros; apply @is_symmetric_isPullback.
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
    eapply pathscomp0. 2: apply maponpaths_2.
    eapply pathscomp0. 2: { symmetry. apply pairing_transport. }
    2: { apply cwf_law_4. }
    eapply pathscomp0. { apply (pairing_mapeq _ _ (id_right _ )). }
    apply maponpaths.
    eapply pathscomp0. { apply transport_f_f. }
    eapply pathscomp0.
    { eapply term_typeeq_transport_lemma.
      eapply term_typeeq_transport_lemma_2.
      reflexivity. }
    apply pathsinv0, (functtransportf (fun D => D{{_}})).
  - (* Reindexing along composites *)
    exists (fun Γ A Γ' f Γ'' g => reindx_type_comp C f g A).
    intros Γ A Γ' f Γ'' g.
    unfold q_typecat. simpl. 
    eapply pathscomp0. 2: { apply id_left. }
    rewrite 2 assoc.
    unfold ext_typecat. simpl.
    rewrite <- cwf_law_4.
    rewrite pairing_transport.
    unfold q_cwf. 
    rewrite cwf_law_3.
    match goal with [|- pairing ?b _ = pairing ?e _ ] => 
              set (X := b); set (X' := e)  end.
    etrans.
    + refine (pairing_mapeq _ X' _ _ ).
      subst X X'.
      etrans. 2: { apply pathsinv0, maponpaths_2, cwf_law_3. }
      etrans. 2: { apply pathsinv0, assoc. }
      etrans. { apply assoc. }
      apply maponpaths_2.
      etrans. 2: { apply pathsinv0, cwf_law_1. }
      etrans. 2: { apply pathsinv0, assoc. }
      apply maponpaths_2. sym. apply cwf_law_1.
    + apply maponpaths.
      match goal with |[ |- transportf _ ?e _ = transportf _ ?e' _  ] =>
                       generalize e, e' end.
      intros p p'.
      rew_trans_@.
      apply term_typeeq_transport_lemma.
      etrans. 2:{ apply rterm_typeeq. }
      match goal with |[ |- transportf _ ?e _ = transportf _ ?e' _  ] =>
                       generalize e, e' end.
      clear p p' X X'; intros p p'.
      rewrite (reindx_term_comp C).
      rewrite transport_f_f.
      match goal with |[ |- transportf _ ?e _ = transportf _ ?e' _  ] =>
                       generalize e, e' end.
      clear p p'; intros p p'.
      rewrite cwf_law_2'.
      unfold transportb.
      rewrite 2 transport_f_f.
      apply term_typeeq_transport_lemma.
      match goal with |[ |- _ = transportf _ ?e _ ⟦ _ ⟧ ] => generalize e end.
      intro q.
      etrans. 2: { apply rterm_typeeq. }
      rewrite cwf_law_2'.
      unfold transportb.
      rewrite 2 transport_f_f.
      match goal with |[ |- transportf _ ?e _ = transportf _ ?e' _  ] =>
                       generalize e, e' end.
      clear p q p'; intros p p'.
      match goal with |[ |- _ = transportf _ _  (transportf _ ?e' _ ) ] =>
                       set (p'':=e') end.
      apply term_typeeq_transport_lemma.
      match goal with |[ |- transportf _ ?e _ = transportf _ ?e' _  ] =>
                       generalize e end.
      clear p p'; intro p. clearbody p''.
      eapply pathscomp0. 2: { apply pathsinv0, retype_term_pi. }
      apply maponpaths_2, cwf_types_isaset.
Qed.


End TypeCat_of_CwF.

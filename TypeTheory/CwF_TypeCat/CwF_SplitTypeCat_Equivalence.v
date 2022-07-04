(**
  [TypeTheory.CwF_TypeCat.CwF_SplitTypeCat_Equivalence]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheory.
Require Import TypeTheory.Auxiliary.SetsAndPresheaves.

Require Import TypeTheory.CwF_TypeCat.CwF_SplitTypeCat_Defs.
Require Import TypeTheory.CwF_TypeCat.CwF_SplitTypeCat_Maps.


Section Fix_Context.

Context {C : category} (X : obj_ext_structure C).

Local Notation "Γ ◂ A" := (comp_ext _ Γ A) (at level 30).
Local Notation "'Ty'" := (fun X Γ => TY X $p Γ) (at level 10).
Local Notation "A [ f ]" := (#p (TY X) f A) (at level 4).
Local Notation "'Tm'" := (fun Y Γ => TM Y $p Γ) (at level 10).

Local Notation Δ := comp_ext_compare.

Section compatible_structures.

(** * Every compatible term structure is equal to the canoncial one *)

Section canonical_TM.

Variable Z : qq_morphism_structure X.
Notation ZZ := (pr2 Z).
Variable Y : compatible_term_structure Z.

Definition canonical_TM_to_given_data
  {Γ} (Ase : tm_from_qq Z Γ : hSet) : (Tm Y Γ).
Proof.
  use (#p (TM _) _ (te _ (pr1 Ase))). 
  exact (pr1 (pr2 Ase)).
Defined.

Lemma is_nat_trans_canonical_TM_to_given 
 : is_nat_trans (tm_from_qq Z) (TM Y : functor _ _ )
     (@canonical_TM_to_given_data).
Proof.
  intros Γ Γ' f.
  apply funextsec; intros [A [s e]].
  unfold canonical_TM_to_given_data; cbn.
  etrans. apply maponpaths, (pr2 Y).
  etrans. apply pathsinv0, functor_comp_pshf.
  etrans. 2: { apply functor_comp_pshf. }
  apply maponpaths_2. 
  apply (@PullbackArrow_PullbackPr2 C _ _ _ _ _ (make_Pullback _ _)).
Qed.

Definition canonical_TM_to_given : (preShv C) ⟦tm_from_qq Z, TM (pr1 Y)⟧.
Proof.
  exists @canonical_TM_to_given_data.
  apply is_nat_trans_canonical_TM_to_given.
Defined.

(* Naturality of this direction is a bit subtle; we will deduce it below from the fact that it is pointwise inverse to [canonical_TM_to_given]. *)
Definition given_TM_to_canonical_data
  : ∏ Γ, HSET ⟦ Tm (pr1 Y) Γ, tm_from_qq Z Γ⟧.
Proof.
  intros Γ t.
  exists (pp (pr1 Y) $nt t).
  apply term_to_section.
Defined. 

Lemma given_to_canonical_to_given Γ
  : given_TM_to_canonical_data Γ ;; (canonical_TM_to_given : nat_trans _ _) Γ
  = identity _ .
Proof.
  apply funextsec; intro t.
  cbn. unfold canonical_TM_to_given_data, given_TM_to_canonical_data.
  apply term_to_section_recover.
Qed.

Lemma pp_canonical_TM_to_given
  : canonical_TM_to_given ;; pp Y
    = pp_from_qq Z.
Proof.
  apply nat_trans_eq. apply homset_property.
  intros Γ; simpl in Γ. apply funextsec; intros [A [s e]].
  cbn. unfold canonical_TM_to_given_data.
  etrans. apply nat_trans_ax_pshf. 
  etrans. cbn. apply maponpaths, pp_te.
  etrans. apply pathsinv0, functor_comp_pshf.
  etrans. apply maponpaths_2, e.
  apply functor_id_pshf.
Qed.

(* Functions between sets [f : X <--> Y : g] are inverse iff they are _adjoint_, in that [ f x = y <-> x = f y ] for all x, y.

Here we give one direction of that “adjunction”; combined with [given_to_canonical_to_given] above, it implies full inverseness. *) 
Lemma canonical_TM_to_given_paths_adjoint {Γ:C} Ase t
  : canonical_TM_to_given $nt Ase = t
  -> Ase = given_TM_to_canonical_data Γ t.
Proof.
  destruct Ase as [A [s e]].
  intros H.
  (* This [assert] is to enable the [destruct eA] below. *)
  assert (eA : pp Y $nt t = A). {
    etrans. { apply maponpaths, (!H). }
    apply (nat_trans_eq_pointwise_pshf pp_canonical_TM_to_given). }
  use total2_paths_f.
  exact (!eA).
  destruct eA; cbn.
  apply subtypePath. { intros x; apply homset_property. }
  set (temp := proofirrelevance _ (isapropifcontr (term_to_section_aux t))).
  use (maponpaths pr1 (temp (_,,_) (_,,_))).
  - cbn; split.
    + exact e.
    + exact H.
Qed.

Lemma canonical_to_given_to_canonical Γ
  : (canonical_TM_to_given : nat_trans _ _) Γ
    ;; given_TM_to_canonical_data Γ
  = identity _ .
Proof.
  apply funextsec; intro t.
  apply pathsinv0, canonical_TM_to_given_paths_adjoint, idpath.
Qed.

Lemma canonical_TM_to_given_pointwise_iso Γ
  : is_z_isomorphism ((canonical_TM_to_given : nat_trans _ _) Γ).
Proof.
  exists (given_TM_to_canonical_data Γ).
  split.
  - apply canonical_to_given_to_canonical.
  - apply given_to_canonical_to_given.
Defined.

Definition canonical_TM_to_given_iso
  : @z_iso (preShv C) (tm_from_qq Z) (TM (pr1 Y)).
Proof.
  exists canonical_TM_to_given.
  apply nat_trafo_z_iso_if_pointwise_z_iso.
  intro Γ. 
  apply (canonical_TM_to_given_pointwise_iso).
Defined.

(*
Definition given_TM_to_canonical_naturality
  : is_nat_trans (TM Y : functor _ _) (tm_from_qq Z) 
      (@given_TM_to_canonical_data).
Proof.
  use (is_nat_trans_inv_from_pointwise_inv_ext _
           canonical_TM_to_given_pointwise_iso).
  apply homset_property.
Qed.
*)
(* TODO: perhaps reorganise the above a little?  Under the current definitions, [iso_inv_from_iso canonical_TM_to_given_iso] is *not* definitionally equal to [given_TM_to_canonical], which is a little annoying downstream (lemmas about [given_TM_to_canonical] can’t be applied). *)  

Definition given_TM_to_canonical
  : (TM Y) --> (tm_from_qq Z) := pr12 canonical_TM_to_given_iso.
(*  (_ ,, given_TM_to_canonical_naturality). *)

Lemma pp_given_TM_to_canonical
  : given_TM_to_canonical ;; pp_from_qq Z
    = pp Y.
Proof.
  apply nat_trans_eq. apply homset_property.
  intros Γ; apply idpath.
Qed.

(* TODO: re-state [given_to_canonical_to_given] and [canonical_to_given_to_canonical] as composites of natural transformations? *)

Lemma canonical_TM_to_given_te {Γ:C} (A : Ty X Γ)
  : canonical_TM_to_given $nt (te_from_qq Z A) = te Y A.
Proof.
  cbn. unfold canonical_TM_to_given_data. cbn.
  etrans. apply maponpaths, (pr2 Y).
  etrans. apply pathsinv0, functor_comp_pshf.
  etrans. apply maponpaths_2; cbn.
    apply (PullbackArrow_PullbackPr2 (make_Pullback _ _)). 
  apply functor_id_pshf.
Qed.

Lemma given_TM_to_canonical_te {Γ:C} (A : Ty X Γ)
  : given_TM_to_canonical $nt (te Y A) = (te_from_qq Z A).
Proof.
  etrans.
  2: { exact (toforallpaths (canonical_to_given_to_canonical _) _). }
  cbn. apply maponpaths, @pathsinv0, canonical_TM_to_given_te.
Qed.

End canonical_TM.

Lemma compatible_term_structure_equals_canonical
  {Z : qq_morphism_structure X} (Y : compatible_term_structure Z)
  : Y = compatible_term_from_qq Z.
Proof.
  apply @pathsinv0.
  set (i := isotoid _
                   (univalent_category_is_univalent _)
                   (canonical_TM_to_given_iso Z Y)).
  apply subtypePath.
  { intro. apply isaprop_iscompatible_term_qq. } 
  destruct Y as [Y YH]. simpl.
  apply subtypePath.
  { intro. apply isaprop_term_fun_structure_axioms. }
  simpl.
  destruct Y as [Y YH']; simpl.
  use total2_paths_f.
  - apply i.
  - rewrite transportf_dirprod.
    destruct Y as [tm [p te]]; simpl.
    apply dirprodeq; simpl.
    + etrans. eapply pathsinv0.
        apply  (idtoiso_precompose (preShv C)).
      unfold i.
      rewrite idtoiso_inv.
      rewrite idtoiso_isotoid.
      unfold canonical_TM_to_given_iso. 
      apply nat_trans_eq. 
      * apply has_homsets_HSET.
      * intro Γ. apply idpath.
    + etrans. use transportf_forall.
      apply funextsec; intro Γ.
      etrans. use transportf_forall.
      apply funextsec; intro A.
      etrans. apply transportf_isotoid_pshf.
      cbn. unfold canonical_TM_to_given_data. cbn.
      etrans. apply maponpaths, YH.
      etrans. apply pathsinv0, functor_comp_pshf.
      etrans. apply maponpaths_2; cbn.
        apply (PullbackArrow_PullbackPr2 (make_Pullback _ _)). 
      apply functor_id_pshf.
Defined.

(** * Every compatible q-morphism structure is equal to the canonical one *)

(* Does this really rely on splitness of the term structure? *)
Lemma iscontr_compatible_term_structure (Z : qq_morphism_structure X)
: iscontr (compatible_term_structure Z).
Proof.
  exists (compatible_term_from_qq Z).
  intro t.
  apply compatible_term_structure_equals_canonical.
Defined.

Lemma compatible_qq_morphism_structure_equals_canonical
    {Y : term_fun_structure _ X} (t : compatible_qq_morphism_structure Y)
  : t = compatible_qq_from_term Y.
Proof.
  apply subtypePath.
  { intro. apply isaprop_iscompatible_term_qq. }
  simpl; apply subtypePath.
  { intro. apply @isaprop_qq_morphism_axioms. }
  apply subtypePath.
  { intro.
    do 4 (apply impred; intro).
    apply isofhleveltotal2. 
    - apply homset_property.
    - intro. apply isaprop_isPullback. } 
  simpl.
  (* TODO: remove these (and check for other unnecessary destructs, now we have primitive projections), but check it doesn’t affect Qed time. *)
  destruct t as [[t H1] H2]. simpl.
  destruct t as [q h]; simpl.
  apply funextsec. intro Γ.
  apply funextsec; intro Γ'.
  apply funextsec; intro f.
  apply funextsec; intro A.    
  apply (invmaponpathsweq (make_weq _ (yoneda_fully_faithful _ _ _ ))).
  apply pathsinv0.
  etrans. apply Yo_qq_term_Yo_of_qq.
  unfold Yo_of_qq.
  apply pathsinv0.
  apply PullbackArrowUnique.
  + etrans. apply maponpaths. cbn. apply idpath.
    rewrite <- functor_comp.
    etrans. eapply pathsinv0. use (functor_comp Yo).
    apply maponpaths.
    apply (pr1 (h _ _ _ _ )).
  + etrans. apply maponpaths. cbn. apply idpath.
    apply pathsinv0.
    apply (pr1 (iscompatible_iscompatible' _ _) H2).
Qed.


Lemma iscontr_compatible_split_comp_structure (Y : term_fun_structure C X)
: iscontr (compatible_qq_morphism_structure Y).
Proof.
  exists (compatible_qq_from_term Y).
  apply compatible_qq_morphism_structure_equals_canonical.
Defined.

End compatible_structures.

Section Equivalence.

Definition T1 : UU :=
  ∑ Y : term_fun_structure C X,
        compatible_qq_morphism_structure Y.

Definition T2 : UU :=
  ∑ Z : qq_morphism_structure X,
        compatible_term_structure Z.

Definition shuffle : T1 ≃ T2.
Proof.
  eapply weqcomp. { apply weqtotal2asstol'. }
  eapply weqcomp. 2: { apply weqtotal2asstor'. }
  use weqbandf.
  - apply weqdirprodcomm.
  - intros. simpl.
    apply idweq.
Defined.

Definition forget_compat_term :
  T2 ≃ qq_morphism_structure X.
Proof.
  exists pr1.
  apply isweqpr1.
  intros [z zz].
  apply iscontr_compatible_term_structure.
Defined.

Definition forget_compat_qq :
  T1 ≃ term_fun_structure C X.
Proof.
  exists pr1.
  apply isweqpr1.
  intro.
  apply iscontr_compatible_split_comp_structure.
Defined.

(** * Equivalence between term structures and q-morphism structures *)

Definition weq_term_qq : term_fun_structure C X ≃ qq_morphism_structure X.
Proof.
  eapply weqcomp.
    eapply invweq. apply forget_compat_qq.
  eapply weqcomp.
    apply shuffle.
  apply forget_compat_term.
Defined.

End Equivalence.

End Fix_Context.

(** * Equivalence between types of pairs of object extension, term and q-morphism structures *)

Definition weq_cwf'_sty' C : cwf'_structure C ≃ split_typecat'_structure C.
Proof.
  apply weqfibtototal.
  intro X. apply weq_term_qq.
Defined.

 

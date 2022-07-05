
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.All.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheory.

(** * Arrow categories *)
Section ArrowCategory.

Definition arrow_category_ids {C : category}
           (abf cdg : arrow_category C)
  : UU
  := ∑ (hk : (pr1 (pr1 abf) = pr1 (pr1 cdg))
               × (dirprod_pr2 (pr1 abf) = dirprod_pr2 (pr1 cdg))),
    pr2 abf ;; idtoiso (dirprod_pr2 hk) = idtoiso (pr1 hk) ;; pr2 cdg.

Lemma arrow_category_id_to_ids {C : category}
           {abf cdg : arrow_category C}
  : (abf = cdg) ≃ arrow_category_ids abf cdg.
Proof.
  eapply weqcomp. { apply total2_paths_equiv. }
  use (weqtotal2 pathsdirprodweq).
  intros e.
  destruct abf as [ab f], cdg as [cd g].
  set (e' := e : ab = cd). clearbody e'; clear e.
  destruct e'. cbn.
  eapply weqcomp. { eapply weqpathscomp0l. apply id_right. }
  apply weqpathscomp0r. apply pathsinv0, id_left.
Defined.

Definition arrow_category_is_iso {C : category}
           {abf cdg : arrow_category C}
           (a_to_c : C ⟦ pr1 (pr1 abf), pr1 (pr1 cdg) ⟧)
           (b_to_d : C ⟦ dirprod_pr2 (pr1 abf), dirprod_pr2 (pr1 cdg) ⟧)
  : UU
  := is_z_isomorphism b_to_d ×
     is_z_isomorphism a_to_c ×
     (pr2 abf ;; b_to_d = a_to_c ;; pr2 cdg).

Lemma isaprop_arrow_category_is_iso {C : category}
           {abf cdg : arrow_category C}
           (a_to_c : C ⟦ pr1 (pr1 abf), pr1 (pr1 cdg) ⟧)
           (b_to_d : C ⟦ dirprod_pr2 (pr1 abf), dirprod_pr2 (pr1 cdg) ⟧)
  : isaprop (arrow_category_is_iso a_to_c b_to_d).
Proof.
  use isapropdirprod.
  - apply isaprop_is_z_isomorphism.
  - use isapropdirprod.
    + apply isaprop_is_z_isomorphism.
    + apply homset_property.
Defined.

Definition arrow_category_is_iso_to_is_iso {C : category}
           {abf cdg : arrow_category C}
           (a_to_c : C ⟦ pr1 (pr1 abf), pr1 (pr1 cdg) ⟧)
           (b_to_d : C ⟦ dirprod_pr2 (pr1 abf), dirprod_pr2 (pr1 cdg) ⟧)
  : arrow_category_is_iso a_to_c b_to_d
    → ∑ (p : pr2 abf ;; b_to_d = a_to_c ;; pr2 cdg)
    , is_z_isomorphism (((a_to_c,, b_to_d),,p) : arrow_category C ⟦ abf, cdg ⟧).
Proof.
  intros h.
  set (is_iso_a_to_c := pr1 (dirprod_pr2 h)).
  set (is_iso_b_to_d := pr1 h).
  set (iso_a_to_c := (a_to_c,,is_iso_a_to_c)).
  set (iso_b_to_d := (b_to_d,,is_iso_b_to_d)).
  set (comm_square := dirprod_pr2 (dirprod_pr2 h)).
  use tpair.
  - apply comm_square.
  - unfold is_z_isomorphism.
    use tpair.
    + use tpair.
      * use make_dirprod.
        -- apply (inv_from_z_iso iso_a_to_c).
        -- apply (inv_from_z_iso iso_b_to_d).
      * simpl.
        apply pathsinv0.
        etrans. apply pathsinv0, id_right.
        etrans. apply maponpaths, pathsinv0, (z_iso_inv_after_z_iso iso_b_to_d).
        etrans. apply assoc'.
        etrans. apply maponpaths, assoc.
        etrans. apply maponpaths, maponpaths_2, comm_square.
        etrans. apply assoc.
        etrans. apply maponpaths_2, assoc.
        etrans. apply maponpaths_2, maponpaths_2, z_iso_after_z_iso_inv.
        etrans. apply maponpaths_2, id_left.
        apply idpath.
    + use make_dirprod.
      * use total2_paths_f.
        -- use dirprod_paths.
           ++ apply (z_iso_inv_after_z_iso iso_a_to_c).
           ++ apply (z_iso_inv_after_z_iso iso_b_to_d).
        -- apply homset_property.
      * use total2_paths_f.
        -- use dirprod_paths.
           ++ apply (z_iso_after_z_iso_inv iso_a_to_c).
           ++ apply (z_iso_after_z_iso_inv iso_b_to_d).
        -- apply homset_property.
Defined.

Definition is_iso_to_arrow_category_is_iso {C : category}
           {abf cdg : arrow_category C}
           (a_to_c : C ⟦ pr1 (pr1 abf), pr1 (pr1 cdg) ⟧)
           (b_to_d : C ⟦ dirprod_pr2 (pr1 abf), dirprod_pr2 (pr1 cdg) ⟧)
  : (∑ (p : pr2 abf ;; b_to_d = a_to_c ;; pr2 cdg)
    , is_z_isomorphism (((a_to_c,, b_to_d),,p) : arrow_category C ⟦ abf, cdg ⟧))
    → arrow_category_is_iso a_to_c b_to_d.
Proof.
  intros hp.
  set (abf_to_cdg := ((a_to_c,, b_to_d),,pr1 hp) : arrow_category C ⟦ _ , _ ⟧).
  set (h := pr2 hp : is_z_isomorphism abf_to_cdg).
  set (c_to_a := pr1 (pr1 (inv_from_z_iso (abf_to_cdg,,h)))).
  set (d_to_b := dirprod_pr2 (pr1 (inv_from_z_iso (abf_to_cdg,,h)))).

  use make_dirprod.
  - use tpair. { apply d_to_b. }
    use make_dirprod.
    * apply (maponpaths (λ k, dirprod_pr2 (pr1 k)) (z_iso_inv_after_z_iso (_,,h))).
    * apply (maponpaths (λ k, dirprod_pr2 (pr1 k)) (z_iso_after_z_iso_inv (_,,h))).
  - use make_dirprod.
    + use tpair. { apply c_to_a. }
      use make_dirprod.
      * apply (maponpaths (λ k, pr1 (pr1 k)) (z_iso_inv_after_z_iso (_,,h))).
      * apply (maponpaths (λ k, pr1 (pr1 k)) (z_iso_after_z_iso_inv (_,,h))).
    + apply (pr2 abf_to_cdg).
Defined.

Definition arrow_category_weq_is_iso {C : category}
           {abf cdg : arrow_category C}
           (a_to_c : C ⟦ pr1 (pr1 abf), pr1 (pr1 cdg) ⟧)
           (b_to_d : C ⟦ dirprod_pr2 (pr1 abf), dirprod_pr2 (pr1 cdg) ⟧)
  : arrow_category_is_iso a_to_c b_to_d
                          ≃
    ∑ (p : pr2 abf ;; b_to_d = a_to_c ;; pr2 cdg)
    , is_z_isomorphism (((a_to_c,, b_to_d),,p) : arrow_category C ⟦ abf, cdg ⟧).
Proof.
  use weq_iso.
  - apply arrow_category_is_iso_to_is_iso.
  - apply is_iso_to_arrow_category_is_iso.
  - intros h. apply isaprop_arrow_category_is_iso.
  - intros h.
    use total2_paths_f.
    + apply homset_property.
    + apply isaprop_is_z_isomorphism.
Defined.

Definition arrow_category_id_weq_iso {C : category}
           (C_univ : is_univalent C)
           (abf cdg : arrow_category C)
  : (abf = cdg) ≃ z_iso abf cdg.
Proof.
  eapply weqcomp.
  apply arrow_category_id_to_ids.

  set (a := pr1 (pr1 abf)).
  set (b := dirprod_pr2 (pr1 abf)).
  set (f := pr2 abf).
  set (c := pr1 (pr1 cdg)).
  set (d := dirprod_pr2 (pr1 cdg)).
  set (g := pr2 cdg).

  assert (weq1 :
  (∑ hk : a = c × b = d,
    pr2 abf;; idtoiso (dirprod_pr2 hk) = idtoiso (pr1 hk) ;; pr2 cdg)
    ≃
  (∑ hk : z_iso a c × z_iso b d,
   pr2 abf;; dirprod_pr2 hk = pr1 hk ;; pr2 cdg)).
  eapply weqcomp. apply weqtotal2asstor.
  apply invweq.
  eapply weqcomp. apply weqtotal2asstor.
  apply invweq.
  use PartA.weqtotal2.
  - apply (make_weq _ (C_univ a c)).
  - intros id_ac.
    use PartA.weqtotal2.
    + apply (make_weq _ (C_univ b d)).
    + intros id_bd. apply idweq.

  - eapply weqcomp. apply weq1.
    eapply weqcomp. apply weqtotal2asstor.
    eapply weqcomp. apply weqtotal2asstor.
    apply invweq.
    eapply weqcomp. apply weqtotal2asstor.
    eapply weqcomp. apply weqtotal2asstor.
    use PartA.weqtotal2.
    + apply idweq.
    + intros a_to_c.
      apply invweq.
      eapply weqcomp. apply WeakEquivalences.weqtotal2comm.
      eapply weqcomp. apply weqtotal2asstor.
      use PartA.weqtotal2.
      * apply idweq.
      * intros b_to_d. simpl.
        apply arrow_category_weq_is_iso. 
Defined. 

Definition arrow_category_mor_eq {C : category}
           {abf cdg : arrow_category C}
           (f g : arrow_category C ⟦ abf, cdg ⟧)
  : pr1 (pr1 f) = pr1 (pr1 g)
    → dirprod_pr2 (pr1 f) = dirprod_pr2 (pr1 g)
    → f = g.
Proof.
  intros p1 p2.
  use total2_paths_f.
  - use dirprod_paths.
    + apply p1.
    + apply p2.
  - apply homset_property.
Defined.

Definition arrow_category_is_univalent {C : category}
           (C_univ : is_univalent C)
  : is_univalent (arrow_category C).
Proof.
  intros abf cdg.
  use isweqhomot.
  + apply arrow_category_id_weq_iso.
    apply C_univ.
  + intros p. induction p.
      apply z_iso_eq.
    apply arrow_category_mor_eq.
    * apply idpath.
      * apply idpath.
  + apply (pr2 (arrow_category_id_weq_iso C_univ _ _)).
Defined.

End ArrowCategory.

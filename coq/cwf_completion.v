
(** * From preCwFs to CwFs *)
(**
  Contents:

    - not much yet
*)

Require Export Systems.Auxiliary.
Require Export Systems.UnicodeNotations.
Require Export UniMath.Foundations.hlevel2.hSet.

Require Export RezkCompletion.functors_transformations.
Require Export RezkCompletion.category_hset.
Require Export RezkCompletion.yoneda.
Require Export RezkCompletion.rezk_completion.

Require Export Systems.cwf.


Print iso.

Implicit Arguments iso  .

Definition Rezk_functor (C : precategory) (hs : has_homsets C) (D : category) 
    (F : functor C D) 
  :  functor (Rezk_completion C hs) D.
Proof.
  set (H:=Rezk_eta_Universal_Property C D hs (pr2 D)).
  apply (invmap (weqpair _  H)).
  apply F.
Defined.



Definition opp_iso2 (C : precategory) (a b : C) : iso (opp_precat C) a b → iso C b a.
Proof.
  intro f.
  set (H:= is_z_iso_from_is_iso f (pr2 f)).
  exists (pr1 f).
  apply is_iso_from_is_z_iso.
  exists (pr1 H).
  split.
  - apply (pr2 (pr2 H)).
  - apply (pr1 (pr2 H)).
Defined.

Lemma opp_iso_opp_iso2 (C : precategory) (a b : C) (f : iso (opp_precat C) a b) : 
   opp_iso (opp_iso2 _ _ _ f) = f.
Proof.
  apply eq_iso.
  apply idpath.
Qed.

Lemma opp_iso2_opp_iso (C : precategory) (a b : C) (f : iso C a b) : 
   opp_iso2 _ _ _  (opp_iso f) = f.
Proof.
  apply eq_iso.
  apply idpath.
Qed.

Definition weq_opp_iso (C : precategory) (a b : C) : 
  iso C a b ≃ iso (opp_precat C) b a.
Proof.
  exists (opp_iso).
  apply (gradth (@opp_iso _ _ _  ) (opp_iso2 _ _ _ )).
  - apply opp_iso2_opp_iso.
  - apply opp_iso_opp_iso2.
Defined.

Definition isotoid_opp (C : precategory) (H : is_category C) (a b : opp_precat C) : 
   weq (a = b) (iso (opp_precat C) a b).
Proof.
  eapply weqcomp.
  - apply weqpathsinv0.
  - eapply weqcomp.
    + apply (weqpair (@idtoiso C b a) (pr1 H b a)).
    + apply weq_opp_iso.
Defined.




Definition is_category_opp (C : precategory) (H : is_category C) : is_category (opp_precat C).
Proof.
  split; intros; simpl in *.
  Check @opp_iso.
   - set (H1:=@isweqhomot).
     set (H2 := H1 _ _ (isotoid_opp C H a b)).
     apply H2.
     intro t.
     induction t.
     simpl.
     apply eq_iso. apply idpath.
     apply (pr2 (isotoid_opp C H a b)).
  - intros a b. simpl. apply (pr2 H).
Qed.
 
Definition opp_cat (C : category) : category.
Proof.
  exists (opp_precat C).
  apply is_category_opp.
  apply (pr2 C).
Defined.


Section bla.

Variable C : pre_cwf.
Hypothesis hs : has_homsets C.

(** The "type" part of a CwF is a functor into HSET **)

Definition type_hSet (Γ : C) : hSet := hSetpair (C⟨Γ⟩) (pr1 (pr2 (pr2 C)) _ ). 

Definition type_functor_data : functor_data C (opp_precat HSET).
Proof.
  exists type_hSet.
  intros Γ Γ' γ A. exact (rtype A γ).
Defined.
  
Definition type_is_functor : is_functor type_functor_data.
Proof.
  split; intros; simpl.
  - apply funextfunax; intro A. apply reindx_type_id. 
    apply (reindx_laws_from_pre_cwf C).
  - apply funextfunax; intro A.
    apply reindx_type_comp.
    apply (reindx_laws_from_pre_cwf C).
Qed.

Definition type_functor : functor _ _ := tpair _ _ type_is_functor.

Definition RC_type_functor : functor (Rezk_completion C hs) (opp_precat HSET).
Proof.  
  apply (Rezk_functor C hs (opp_cat (tpair _ HSET is_category_HSET))).
  apply type_functor.
Defined.
  









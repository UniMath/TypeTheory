Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.


Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.pullbacks.

Require Import UniMath.CategoryTheory.categories.Cats.
Require Import UniMath.CategoryTheory.slicecat.

Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.ElementsOp.

Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.RelativeUniverses.
Require Import TypeTheory.ALV1.Transport_along_Equivs.
Require Import TypeTheory.ALV1.RelUnivYonedaCompletion.
Require Import TypeTheory.ALV1.CwF_def.

Local Open Scope cat.


Definition PreShv_diag (C : category)  (X : PreShv C)  : [(cat_of_elems X),(PreShv C)].
Proof.
  use functor_composite.
  - exact C.    
  - exact (cat_of_elems_forgetful).
  - apply yoneda. apply homset_property.
Defined.

Definition PreShv_cocone_data (C : category) (X : PreShv C) :  ∏ v : vertex ∫ X, [C^op, SET] ⟦ dob (diagram_from_functor ∫ X [C^op, SET] (PreShv_diag C X)) v, X ⟧.
Proof.
  intros. simpl. use yoneda_map_2. exact (pr2 v).
Defined.

Lemma is_cocone_data (C : category) (X : PreShv C) : ∏ (u v : vertex ∫ X) (e : edge u v),
  dmor (diagram_from_functor ∫ X [C^op, SET] (PreShv_diag C X)) e;;
       PreShv_cocone_data C X v = PreShv_cocone_data C X u.
Proof.
simpl. intros. cbn.   
    unfold nat_trans_comp. cbn.
    use (nat_trans_eq has_homsets_HSET).
    cbn.
    intros.
    apply funextfun.
    intro y.
    unfold yoneda_morphisms_data.
    symmetry.
    etrans; [eapply maponpaths, (pr2 e)|].
    apply (!eqtohomot (functor_comp X (pr1 e) y) (pr2 v)).
Qed.
  
Definition PreShv_cocone (C : category) (X : PreShv C) : cocone (diagram_from_functor _ _ (PreShv_diag C X)) X.
Proof.
  use mk_cocone.
  - exact (PreShv_cocone_data C X).
  - exact (is_cocone_data C X).
Defined.
  
Lemma is_colim (C : category)  (X : PreShv C)  : isColimCocone _ _ (PreShv_cocone C X).
Proof.
  unfold isColimCocone.
  intros X' cc.
  use unique_exists.
  - use mk_nat_trans.
    + unfold nat_trans_data.
      cbn.
      intros x a.
      apply (yoneda_map_1 C (homset_property C)).
      simpl.
      apply (coconeIn cc (x,,a)).
    + unfold is_nat_trans.
      intros.
      cbn.
      apply funextfun.
      intro a.
      set (p := !coconeInCommutes cc (x',, (# (pr1 X) f a)) (x,,a) (f,, idpath _)).
      etrans; [eapply maponpaths, p|cbn; clear p].
      unfold yoneda_morphisms_data.
      rewrite id_left.
      etrans; [ set (H := !yoneda_map_1_2 C (homset_property C) x X' (coconeIn cc (x,,a)));
                exact (eqtohomot ((eqtohomot (maponpaths pr1 H)) x') f)|].
      cbn.
      reflexivity.
  - simpl; intros.
    cbn.
    apply (nat_trans_eq has_homsets_HSET).
    intros.
    apply funextfun.
    intro f.
    cbn.
    set (p := !coconeInCommutes cc (x,, (# (pr1 X) f (pr2 v))) v (f,, idpath _)).
    etrans; [eapply maponpaths, p|clear p].
    cbn.
    unfold yoneda_morphisms_data.
    rewrite id_left.
    apply idpath. 
  - intro.
    simpl.
    apply impred_isaprop.
    intro.
    apply (isaset_nat_trans has_homsets_HSET).
  - simpl.
    intros.
    apply (nat_trans_eq has_homsets_HSET).
    cbn.    
    intros.
    apply funextfun.
    intro a.
    cbn.
    symmetry.
    etrans; [eapply maponpaths, (!(X0 (x,,a)))|].
    cbn.
    eapply maponpaths.
    etrans; [exact (eqtohomot ((pr1(pr2 X)) x) a)| ].
    reflexivity.
Qed.

Definition colim_on_functor_cocone (C C' : precategory) (D : category) (F' : functor C' D) (G : functor C C') (CocompD : Colims D) : cocone (diagram_from_functor C D (G ∙ F')) (colim (CocompD C' (diagram_from_functor C' D F'))).
Proof.
  use mk_cocone; cbn.
  - intro.
    apply coconeIn.
    use colimCocone.
  - intros.
    cbn.
    use coconeInCommutes.
Defined.


Definition colim_on_functor (C C' : precategory) (D : category) (F : functor C D) (F' : functor C' D) (G : functor C C') (eq : functor_composite G F' = F) (CocompD : Colims D) : colim ((CocompD _ (diagram_from_functor _ _ F))) --> (colim (CocompD _ (diagram_from_functor _ _ F'))).
Proof.
  rewrite <- eq.
  apply colimArrow.
  apply colim_on_functor_cocone.
Defined.

(* Definition slice_of_cat (D : category) (HsD : isaset D): precategory. *)
(* Proof. *)
(*   use slice_precat. *)
(*   - exact setcat_cat. *)
(*   - use tpair. *)
(*     + exact (pr1 D). *)
(*     + simpl. *)
(*       use tpair; simpl; [apply HsD|apply (homset_property D)]. *)
(*   - apply homset_property. *)
(* Defined. *)

(* Definition colim_functor_data (D : category) (HsD : isaset D) (CocompD : Colims D) : functor_data (slice_of_cat D HsD) D. *)
(* Proof. *)
(*   use tpair. *)
(*   - intro. *)
(*     exact (colim (CocompD _ (diagram_from_functor _ _ (pr12 X)))). *)
(*   - cbn. *)
(*     intros X Y f. *)
(*     generalize  (maponpaths pr1 (pr2 f)); cbn; intro f_eq. *)
(*     set (H := (colim_on_functor (pr11 X) (pr11 Y) D (pr12 X) (pr12 Y) (pr11 f)) (!f_eq)). *)
    
    
    
(*     generalize (H (!(pr2 f))). *)
(*     exact (colim_on_functor (pr11 X) (pr11 Y) D (pr12 X) (pr12 Y) (pr11 f) (!(pr12 f))). *)
(* Defined. *)


Lemma colim_on_functor_idax (C : precategory) (D : category) (F : functor C D) (CocompD : Colims D) : colim_on_functor C C D F F (functor_identity C) (idpath F) CocompD = identity (colim (CocompD _ (diagram_from_functor _ _ F))).
Proof.
  etrans.
  

  
  cbn.
  set (A := pr2 (CocompD _ (diagram_from_functor C D F))).
  cbn in A.
  unfold isColimCocone in A.
  admit.
Admitted.

Definition slice_eq {C C' C'' : precategory} {D : category} {F : functor C D} {F' : functor C' D} {F'' : functor C'' D} {G : functor C C'} {G' : functor C' C''} (eq1 : functor_composite G F' = F) (eq2 : functor_composite G' F'' = F') : functor_composite (functor_composite G G') F'' = F.
Proof.
  rewrite <- eq2 in eq1.
  rewrite <- eq1.
  apply functor_assoc.
Qed.

Lemma colim_on_functor_compax (C C' C'' : precategory) (D : category) (F : functor C D) (F' : functor C' D) (F'' : functor C'' D) (G : functor C C') (G' : functor C' C'') (eq1: functor_composite G F' = F) (eq2 : functor_composite G' F'' = F') (CocompD : Colims D) :
  colim_on_functor _ _ _ F F'' (functor_composite G G') (slice_eq eq1 eq2) CocompD = compose (colim_on_functor _ _ _ F F' G eq1 CocompD) (colim_on_functor _ _ _ F' F'' G' eq2 CocompD).
Proof.
  assert (cocone (diagram_from_functor _ _ F'') (colim (CocompD _ (diagram_from_functor _ _ F'')))).
  - use mk_cocone.
    + intros.


    
  apply proofirrelevance.
  






  
  admit.
Admitted.




Definition lift_data (C : category) (D : category) (CocompD : Colims D) (F : functor C D) : functor_data (PreShv C) D.
Proof.
  use tpair.
  - intro.
    exact (colim (CocompD (graph_from_precategory (cat_of_elems X)) (diagram_from_functor _ _ (functor_composite cat_of_elems_forgetful F)))).
  - simpl.
    intros X Y h.
    use colim_on_functor.
    + apply (cat_of_elems_on_nat_trans h).
    + use (functor_eq _ _ (homset_property D)).
      reflexivity.
Defined.

Lemma lift_is_functor  (C : category) (D : category) (CocompD : Colims D) (F : functor C D)  : is_functor (lift_data C D CocompD F).
Proof.
  use tpair.
  - intro.
    (* unfold lift_data. *)
    (* rewrite colim_on_functor_idax. *)
    
    (* simpl. *)
    (* unfold lift_data; cbn. *)
    (* unfold colim_on_functor; cbn. *)
    admit.
  - intros a b c f g.
    

    
    admit.
Admitted.


Definition lift (C : category) (D : category) (CocompD : Colims D)
: functor (PreShv C) D.
Proof.
  use mk_functor.
  - exact (lift_data C D CocompD).
  - exact (lift_is_functor C D CocompD).
Defined.




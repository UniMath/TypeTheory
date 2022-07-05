
(**
  
 Ahrens, Lumsdaine, Voevodsky, 2015

 Contents:

  - Construction of a category with Families from a split type-category

*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.
Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheory.
Require Import TypeTheory.Auxiliary.Pullbacks.

Require Import TypeTheory.TypeCat.TypeCat.
Require Import TypeTheory.OtherDefs.CwF_Pitts.

(** * CwF structure from split type-category structure on a category 

Every split-Comp-cat gives rise to a category with families.

Since the components of the CwF structure are highly successively dependent, we construct most of them individually, before putting them together in [cwf_of_type_cat].
 *)

Section CwF_of_Comp. 

Context (CC : category) (C : split_typecat_structure CC).

Local Definition C_sptc : split_typecat :=
  ((CC,,pr1 C),,pr2 C).
(* TODO: find or add constructor [make_split_typecat] *)

Definition tt_structure_of_typecat : tt_structure CC.
Proof.
  unfold tt_structure.
  exists (ty_typecat C).
  intros Γ A.
  exact (∑ f : Γ --> Γ ◂ A, f ;; dpr_typecat _  = identity _ ). 
Defined.

(* A handy lemma for calculations with terms of reindexed types.
TODO: consider naming; upstream/consolidate to general lemmas on type-cats (like with some other material in this file)? *)
Lemma tm_reindx_eq {Γ:CC} (A : C Γ )
    {Γ':CC} (f : Γ' --> Γ)
    (a a' : tt_structure_of_typecat ⟨ Γ' ⊢ reind_typecat A f ⟩)
    (e : pr1 a ;; q_typecat A f = pr1 a' ;; q_typecat A f)
  : a = a'.
Proof.
  apply subtypePath. { intro; apply homset_property. }
  apply (map_into_Pb_unique (@reind_pb_typecat C_sptc _ _ _ _ _)).
  2: apply e.
  exact (pr2 a @ ! pr2 a').
Defined.

(* Maybe some of the below stuff should be opaque, to avoid too much unfolding? *)
Definition reindx_struct_of_typecat : reindx_structure tt_structure_of_typecat.
Proof.
  unfold reindx_structure.
  unshelve refine (tpair _ _ _ ).
  - intros Γ Γ'.
    unfold tt_structure_of_typecat.
    simpl.
    intros A γ.
    exact (reind_typecat A γ).
  - intros Γ Γ' A H. unfold tt_structure_of_typecat in *.
    simpl in *.
    intro γ.
    unshelve refine (tpair _ _ _ ).
    + eapply map_into_Pb.
      * use reind_pb_typecat.
      * etrans. apply id_left.
        apply @pathsinv0.
        etrans. eapply pathsinv0. apply assoc.
        etrans. apply maponpaths. apply (pr2 H).
        apply id_right.
    + apply Pb_map_commutes_1.
Defined.

Definition tt_reindx_from_typecat : tt_reindx_struct CC.
Proof.
  exists tt_structure_of_typecat.
  exact reindx_struct_of_typecat.
Defined.

Lemma reindx_laws_type_of_typecat : reindx_laws_type tt_reindx_from_typecat.
Proof.
  split.
  - unfold tt_reindx_from_typecat. simpl.
    intros Γ A.
    apply (@reind_id_typecat C_sptc).
  - intros.
    apply (@reind_comp_typecat C_sptc).
Defined.  (* needs to be transparent for comp_law_3 at least *)

Lemma reindx_term_id_typecat 
  (Γ : CC)
  (A : tt_reindx_from_typecat ⟨ Γ ⟩)
  (a : tt_reindx_from_typecat ⟨ Γ ⊢ A ⟩) :
   a ⟦ identity Γ ⟧ =
   transportf (λ B : C Γ, ∑ f : Γ --> Γ ◂ B, f;; dpr_typecat B = identity Γ)
              (! (@reind_id_typecat C_sptc Γ A)) a.
Proof.
  intros. simpl. unfold tt_reindx_from_typecat in *. simpl in *.
  apply tm_reindx_eq. cbn.
  etrans. { apply Pb_map_commutes_2. }
  etrans. { apply id_left. }
  apply pathsinv0.
  rewrite transportf_total2. cbn.
  etrans. { apply maponpaths_2, (functtransportf (fun A => Γ ◂ A)). }
  etrans. { apply maponpaths_2, pathsinv0, idtoiso_postcompose. }
  etrans. { apply pathsinv0, assoc. }
  etrans. 2: { apply id_right. }
        apply maponpaths.
  etrans. { apply maponpaths, (@q_id_typecat C_sptc). }
  etrans. { apply pathsinv0, idtoiso_concat_pr. }
  apply idtoiso_eq_idpath.
  etrans. { apply pathsinv0, maponpathscomp0. }
  etrans. { apply maponpaths, pathsinv0l. }
  apply idpath.
Qed.


Lemma reindx_term_comp_typecat 
  (Γ Γ' Γ'' : CC)
  (γ : Γ' --> Γ)
  (γ' : Γ'' --> Γ')
  (A : tt_reindx_from_typecat ⟨ Γ ⟩)
  (a : tt_reindx_from_typecat ⟨ Γ ⊢ A ⟩)
  :
   a ⟦ γ';; γ ⟧ =
   transportf
     (λ B : C Γ'', ∑ f : Γ'' --> Γ'' ◂ B, f;; dpr_typecat B = identity Γ'')
     (! @reind_comp_typecat C_sptc Γ A Γ' γ Γ'' γ') 
     ((a ⟦ γ ⟧) ⟦ γ' ⟧).
Proof.
  intros.
  unfold tt_reindx_from_typecat in *.
  apply tm_reindx_eq; simpl.
  etrans. { apply Pb_map_commutes_2. }
  rewrite transportf_total2. cbn. apply pathsinv0.
  etrans. { apply maponpaths_2, (functtransportf (fun A => _ ◂ A)). }
  etrans. { apply maponpaths_2, pathsinv0, idtoiso_postcompose. }
  etrans. { apply maponpaths, (@q_comp_typecat C_sptc). }
  etrans. { apply pathsinv0, assoc. }
  etrans. { apply maponpaths.
    etrans. { apply maponpaths, pathsinv0, assoc. }
    etrans. { apply assoc. }
    apply maponpaths_2.
    etrans. { apply pathsinv0, idtoiso_concat_pr. }
    eapply idtoiso_eq_idpath.
    etrans. { apply pathsinv0, maponpathscomp0. }
    etrans. { apply maponpaths, pathsinv0l. }
    apply idpath. }
  etrans. { apply maponpaths, id_left. }
  etrans. { apply assoc. }
  etrans. { apply maponpaths_2, Pb_map_commutes_2. }
  etrans. { apply pathsinv0, assoc. }
  etrans. 2: { apply assoc. }
  apply maponpaths, Pb_map_commutes_2.
Qed.

Definition reindx_laws_terms_of_typecat : reindx_laws_terms  reindx_laws_type_of_typecat.
Proof.
  split.
  - apply reindx_term_id_typecat. 
  - intros. apply reindx_term_comp_typecat.
Qed.

Definition reindx_laws_of_typecat : reindx_laws tt_reindx_from_typecat.
Proof.
  exists reindx_laws_type_of_typecat.
  exact reindx_laws_terms_of_typecat.
Defined.  (* needs to be transparent for comp_law_3 at least *)

Definition comp_1_struct_of_typecat : comp_1_struct tt_reindx_from_typecat.
Proof.
  unfold comp_1_struct.
  intros Γ A.
  unshelve refine (tpair _ _ _ ).
  - unfold tt_reindx_from_typecat in A. simpl in A.
    exact (ext_typecat Γ A).
  - exact (dpr_typecat A).
Defined.

Definition tt_reindx_comp_1_of_typecat : tt_reindx_comp_1_struct CC .
Proof.
  exists tt_reindx_from_typecat.
  exact comp_1_struct_of_typecat.
Defined.

Definition comp_2_struct_of_typecat : comp_2_struct tt_reindx_comp_1_of_typecat.
Proof.
  split.
  - unfold tt_reindx_comp_1_of_typecat in *.
    simpl in *.
    + unshelve refine (tpair _ _ _ ).
      * { unfold comp_obj. simpl. 
          eapply map_into_Pb.
          - apply  reind_pb_typecat.
          - apply maponpaths_2.
            apply (idpath (identity _ )). }
      * apply Pb_map_commutes_1.
  - intros Γ' γ.
    intro a.
    unfold tt_reindx_comp_1_of_typecat in *.
    simpl in *.
    apply (pr1 a ;; q_typecat _ _ ).
Defined.

Definition tt_reindx_type_struct_of_typecat : tt_reindx_type_struct CC.
Proof.
  exists tt_reindx_comp_1_of_typecat.
  exact  comp_2_struct_of_typecat.
Defined.

Lemma comp_laws_1_2_of_typecat : @comp_laws_1_2 CC
   tt_reindx_type_struct_of_typecat reindx_laws_of_typecat.
Proof.
  unfold comp_laws_1_2.
  intros Γ A Γ' γ a. simpl.
  unshelve refine (tpair _ _ _ ).
  { unfold pairing; simpl.
    etrans. { apply pathsinv0, assoc. }
    etrans. { apply maponpaths, dpr_q_typecat. }
    etrans. { apply assoc. }
    etrans. { apply maponpaths_2, (pr2 a). }
    apply id_left. }
  use transportf_transpose_left.
  use (@transportf_transpose_left _ (λ B : C Γ', _)).
  apply tm_reindx_eq; simpl.
  etrans. { apply Pb_map_commutes_2. }
  apply pathsinv0.
  unfold transportb. do 2 (rewrite transportf_total2; simpl).
  rewrite (functtransportf (fun f => _ ◂ (_ f))).
  rewrite (functtransportf (fun A => _ ◂ A)).
  rewrite <- 2 idtoiso_postcompose.
  etrans. { apply maponpaths_2, assoc'. }
  rewrite <- idtoiso_concat_pr.
  rewrite <- (maponpathscomp (fun f => A {{f}}) (fun A' => Γ' ◂ A')).
  rewrite <- maponpathscomp0.
  unfold pairing. simpl.
  use (map_into_Pb_unique (reind_pb_typecat _ _)).
  - etrans. 2: { apply assoc. }
    etrans. 2: { eapply maponpaths, pathsinv0, Pb_map_commutes_1. }
    etrans. 2: { apply pathsinv0, id_right. }
    etrans. { apply assoc'. }
    etrans. { apply maponpaths, dpr_q_typecat. }
    etrans. { apply assoc. }
    etrans. 2: { apply id_left. }
    apply maponpaths_2.
    etrans. { apply assoc'. }
    etrans. { apply maponpaths, idtoiso_dpr_typecat. }
    exact (pr2 a).
  - etrans. 2: { apply assoc. }
    etrans. 2: { eapply maponpaths, pathsinv0, Pb_map_commutes_2. }
    etrans. 2: { apply pathsinv0, id_right. }
    cbn. etrans. { apply assoc'. }
    etrans. { apply maponpaths, pathsinv0. 
      eapply z_iso_inv_on_right.
      etrans. 2: { apply assoc'. }
      apply (@q_comp_typecat C_sptc). }
    etrans. { apply maponpaths, maponpaths_2, pathsinv0.
      refine (maponpaths pr1 (idtoiso_inv _ _ _ _)). }
    etrans. { apply maponpaths, maponpaths.
      refine (idtoiso_q_typecat _ _).
      etrans. { apply assoc'. }
      etrans. { apply maponpaths, dpr_q_typecat. }
      etrans. { apply assoc. }
      etrans. { apply maponpaths_2, (pr2 a). }
      apply id_left. }
    etrans. { apply maponpaths, assoc. }
    etrans. { apply assoc. }
    etrans. { apply maponpaths_2, assoc'. }
    apply maponpaths_2.
    etrans. 2: { apply id_right. }
    apply maponpaths.
    etrans. { apply maponpaths, pathsinv0, idtoiso_concat_pr. }
    etrans. { apply pathsinv0, idtoiso_concat_pr. }
    apply idtoiso_eq_idpath.
    rewrite <- maponpathsinv0.
    rewrite <- (maponpathscomp (fun f => A {{f}}) (fun A' => Γ' ◂ A')).
    repeat rewrite <- maponpathscomp0.
    (* TODO: make lemma analogous to [idtoiso_eq_idpath] for such situations *)
    refine (@maponpaths _ _ (maponpaths _) _ (idpath _) _).
    apply isaset_types_typecat.
Time Qed.

Lemma comp_law_3_of_typecat : @comp_law_3 CC tt_reindx_type_struct_of_typecat reindx_laws_of_typecat.
Proof.
  unfold comp_law_3.
  intros Γ A Γ' Γ'' γ γ' a. simpl in *.
  unfold pairing; simpl.
  destruct a as [f H]; simpl in *.
  assert (T:=@transportf_total2).
  assert (T' := T (C Γ'') (λ B, Γ'' --> Γ'' ◂ B) ); clear T.
  assert (T2 := T' (λ B f0, f0 ;; dpr_typecat B = identity Γ'')); clear T'. simpl in T2.
  assert (T3 := T2 _ _ (! reindx_type_comp reindx_laws_of_typecat γ γ' A)); clear T2; simpl in T3.
  match goal with |[ |- _ = pr1 (transportf _ _ ?x) ;; _ ] => set (X := x) end.
  assert (T4 := T3  X); clear T3.
  assert (T5:= base_paths _ _ T4). clear T4; simpl in *.
  sym.
  etrans.
  apply maponpaths_2.
  apply T5.
  clear T5. unfold X; clear X; simpl in *.
  etrans.
  apply maponpaths_2.
  apply functtransportf.
  rewrite <- idtoiso_postcompose.
  rewrite (@q_comp_typecat ((CC,,pr1 C),,pr2 C)).
  match goal with |[ |- _ ;; ?B' ;; ?C'  = _ ]  => set (B:=B'); set (D:=C') end.
  simpl in *.
  match goal with |[ |- @map_into_Pb _ _ _ _ _ _ ?B' ?C' ?D' ?E' ?F' ?G' ?Y' ?Z' ?W'  ;; _ ;; _  = _ ] => 
                   set (f':=B'); set (g:=C'); set (h:=D'); set (k:=E') end.
  match goal with |[ |- @map_into_Pb _ _ _ _ _ _ _ _ _ _ ?F' ?G' ?Y' ?Z' _  ;; _ ;; _  = _ ] => 
   set (x:=F'); set (y:=G');
                   set (Y:=Y'); set (Z:=Z')
  end.
  match goal with |[ |- @map_into_Pb _ _ _ _ _ _ _ _ _ _ _ _ _ _  ?W'  ;; _ ;; _  = _ ] => set (W:=W') end.
  assert (T2:=Pb_map_commutes_2 x Y Z W).
  unfold B.
  unfold D.
  repeat rewrite assoc.
  etrans. apply maponpaths_2.  apply maponpaths_2. eapply pathsinv0. apply assoc.
  rewrite <- idtoiso_concat_pr.

  etrans. apply maponpaths_2. apply maponpaths_2. apply maponpaths.
  apply idtoiso_eq_idpath. 
  {  rewrite <- maponpathscomp0.
     apply maponpaths_eq_idpath.
     simpl.
     unfold reindx_type_comp.
     apply pathsinv0l. }
  rewrite id_right.
  unfold f'. unfold f' in T2.
  apply maponpaths_2. apply T2.
Qed.

Lemma comp_law_4_of_typecat : @comp_law_4 _ tt_reindx_type_struct_of_typecat reindx_laws_of_typecat.
Proof.
  unfold comp_law_4.
  simpl. intros Γ A.
  unfold pairing; simpl.
  apply Pb_map_commutes_2.
Qed.


Lemma cwf_laws_of_typecat : cwf_laws tt_reindx_type_struct_of_typecat .
Proof.
  repeat split.
  - exists reindx_laws_of_typecat.
    repeat split.
    + apply comp_laws_1_2_of_typecat. 
    + apply comp_law_3_of_typecat. 
    + apply comp_law_4_of_typecat.
  - apply (@isaset_types_typecat C_sptc).
  - simpl.
    intros.
    apply (isofhleveltotal2 2).
    + apply homset_property.
    + intros.
      apply hlevelntosn.
      apply homset_property.
Qed.

Definition cwf_of_typecat : cwf_struct CC.
Proof.
  exists tt_reindx_type_struct_of_typecat.
  exact cwf_laws_of_typecat.
Defined.
    
End CwF_of_Comp.


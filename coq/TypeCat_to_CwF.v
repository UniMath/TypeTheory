
(**
  
 Ahrens, Lumsdaine, Voevodsky, 2015

 Contents:

  - Construction of a precategory with Families from Comprehension precat

*)


Require Import UniMath.RezkCompletion.total2_paths.

Require Import Systems.Auxiliary.
Require Import Systems.UnicodeNotations.
Require Import Systems.TypeCat.
Require Import Systems.CwF.


(* TODO: move *)
Lemma idtoiso_q_type_cat {CC : precategory} {C : type_cat_struct CC}
      {Γ : CC} (A : C Γ) {Γ' : CC} {f f' : Γ' ⇒ Γ} (e : f = f') :
      q_type_cat A f
      = (idtoiso (maponpaths (fun f => ext_type_cat Γ' (reind_type_cat A f)) e))
          ;; q_type_cat A f'.
Proof.
  intros. destruct e; simpl. sym. apply id_left.
  (* Why the heck doesn’t “symmetry” work here!? *)
Defined.
  


(** * wF structure from (split) comprehension structure on a precategory 

Every pre-(split)-Comp-cat gives rise to a pre-category with families.

Since the components of the pre-cat with Families structure are highly successively dependent, we construct most of them individually, before putting them together in [cwf_of_type_precat].
 *)

Section CwF_of_Comp. 

 
Context (CC : precategory) (C : split_type_struct CC) (homs_sets : has_homsets CC).

Definition tt_structure_of_type_cat : tt_structure CC.
Proof.
  unfold tt_structure.
  exists (ty_type_cat C).
  intros Γ A.
  exact (Σ f : Γ ⇒ Γ ◂ A, f ;; dpr_type_cat _  = identity _ ). 
Defined.


(* Maybe some of the below stuff should be opaque, to avoid too much unfolding? *)
Definition reindx_struct_of_type_cat : reindx_structure tt_structure_of_type_cat.
Proof.
  unfold reindx_structure.
  refine (tpair _ _ _ ).
  - intros Γ Γ'.
    unfold tt_structure_of_type_cat.
    simpl.
    intros A γ.
    exact (reind_type_cat A γ).
  - intros Γ Γ' A H. unfold tt_structure_of_type_cat in *.
    simpl in *.
    intro γ.
    refine (tpair _ _ _ ).
    + eapply (map_into_Pb _ _ (dpr_type_cat A)  γ).
      * apply reind_pb_type_cat.
      * etrans. Focus 2. eapply pathsinv0. apply id_left.
        etrans. cancel_postcomposition. apply (idpath (γ ;; pr1 H)).
    {   etrans. eapply pathsinv0. apply assoc.
        etrans. apply maponpaths. apply (pr2 H).
        apply id_right.
    }
    + simpl.
      apply Pb_map_commutes_2.
Defined.    

Definition tt_reindx_from_type_cat : tt_reindx_struct CC.
Proof.
  exists tt_structure_of_type_cat.
  exact reindx_struct_of_type_cat.
Defined.

Lemma reindx_laws_type_of_type_cat : reindx_laws_type tt_reindx_from_type_cat.
Proof.
  split.
  - unfold tt_reindx_from_type_cat. simpl.
    intros Γ A.
    unfold rtype. simpl.
    assert (X:= pr2 (pr1 (pr2 C))). simpl in X.
    apply (pr1 X).
  - intros.
    assert (X:= pr1 (pr2 (pr2 C))). simpl in X.
    apply (X).
Defined.  (* needs to be transparent for comp_law_3 at least *)

Definition reindx_laws_terms_of_type_cat : reindx_laws_terms  reindx_laws_type_of_type_cat.
Proof.
  split.
  - intros; simpl. unfold tt_reindx_from_type_cat in *. simpl in *.
    apply total2_paths_second_isaprop.
    apply homs_sets. simpl.
    apply pathsinv0.
    apply PullbackArrowUnique.
    + simpl.
      rewrite id_left.
      destruct a as [f H]; simpl in *.
      assert (X := (pr2 (pr1 (pr2 C)))). simpl in X.
      rewrite (pr2 X).

      assert (T:=@transportf_total2).
      assert (T':= T (C Γ) (λ B,  Γ ⇒ Γ ◂ B)). simpl in T'.
      assert (T'' := T' (λ B f, f ;; dpr_type_cat B = identity Γ)).
      simpl in *.
      assert (T3:= T'' _ _  (! pr1 (pr2 (pr1 (pr2 C))) Γ A)).
      assert (T4 := T3 (tpair (λ f0 : Γ ⇒ Γ ◂ A, f0;; dpr_type_cat A = identity Γ) f H)).
      clear T3 T'' T'. simpl in T4.
      assert (T5:= base_paths _ _ T4). clear T4; simpl in *.
      etrans.
      cancel_postcomposition. apply T5.

      clear T5.
      
      rewrite idtoiso_postcompose.
      etrans.
      eapply pathsinv0. apply functtransportf.
      rewrite transportf_pathscomp0.
      match goal with |[|- transportf _ ?e _ = _ ] =>
                       assert (He : e = idpath _ )  end .
      apply (pr1 (pr2 C)).
      rewrite He. apply idpath.
    +
      
      destruct a as [f H]; simpl in *.
      rewrite <- H.
      assert (T:=@transportf_total2).
      assert (T':= T (C Γ) (λ B,  Γ ⇒ Γ ◂ B)). simpl in T'.
      assert (T'' := T' (λ B f0, f0 ;; dpr_type_cat B = f ;; dpr_type_cat A)).
      simpl in *.
      assert (T3:= T'' _ _  (! pr1 (pr2 (pr1 (pr2 C))) Γ A) ).
      assert (T4 := T3  (tpair (λ f0 : Γ ⇒ Γ ◂ A, f0;; dpr_type_cat A = f;; dpr_type_cat A) f
                               (idpath (f;; dpr_type_cat A)))).
      clear T3 T'' T'. simpl in T4.
      assert (T5:= base_paths _ _ T4). clear T4; simpl in *.
      etrans.
      cancel_postcomposition. apply T5.
      clear T5.

      apply transportf_dpr_type_cat.

  -

    intros.
    unfold tt_reindx_from_type_cat in *. simpl in *.
    apply total2_paths_second_isaprop.
    apply homs_sets. simpl.
    apply pathsinv0.
    apply PullbackArrowUnique.
    + simpl.
      destruct a as [f H]; simpl in *.
      assert (X := (pr2 (pr2 (pr2 C)))). simpl in X.
      rewrite (X). clear X
      .

      assert (T:=@transportf_total2).

      rewrite assoc.
      assert (T':= T (C Γ'') (λ B,  Γ'' ⇒ Γ'' ◂ B)). simpl in T'.
      assert (T'' := T' (λ B f0, f0 ;; dpr_type_cat B = identity Γ'')).
      simpl in *.
      assert (T3:= T'' _ _  (! pr1 (pr2 (pr2 C)) Γ A Γ' γ Γ'' γ') ).

      match goal with | [ |- pr1 (transportf _ _ ?e ) ;; _ ;; _ = _ ] => set (E:=e) end.
      assert (T4 := T3 E).
      
      clear T3 T'' T'.
      assert (T5:= base_paths _ _ T4). clear T4; simpl in *.
      rewrite <- assoc.
      etrans.
      cancel_postcomposition. apply T5.

      clear T5 T.

      clear E.

      etrans. apply assoc.
      etrans. cancel_postcomposition. apply assoc.
      rewrite idtoiso_postcompose.

       etrans.
      eapply pathsinv0. cancel_postcomposition. cancel_postcomposition. apply functtransportf.
      rewrite transportf_pathscomp0.

      match goal with |[|- transportf ?a ?b ?c ;; _ ;; _ = _ ] =>
           set (a':=a); set (b':=b); set (c':=c) end.
      assert (T':= @Pb_map_commutes_1).
      assert (b' = idpath _ ).
      apply (pr1 (pr2 C)).
      rewrite X.
      simpl.
      etrans.
      cancel_postcomposition.
      apply T'.
      etrans.
      eapply pathsinv0.
      apply assoc.
      etrans. Focus 2.
      apply assoc.
      apply maponpaths.
      etrans.
      apply T'.
      apply idpath.
 
    +
      idtac.
      match goal with |[|- pr1 (transportf ?P' ?e' ?x') ;; _ = _ ] =>
                       set (P:=P') ; set (e := e') ; set (x := x') end.
      assert (T:=@transportf_total2).
      assert (T':= T (C Γ'') (λ B,  Γ'' ⇒ Γ'' ◂ B)). simpl in T'.
      assert (T'' := T' (λ B f0, f0 ;; dpr_type_cat B = identity Γ'')).
        
      simpl in *.
      assert (T3:= T'' _ _  e x).
      assert (T5:= base_paths _ _ T3). clear T3; simpl in *. clear T' T'' T.
      etrans.
      cancel_postcomposition.
      apply T5.
      clear T5.
      etrans.
        apply transportf_dpr_type_cat.
        set (T:=@Pb_map_commutes_2).
        apply T.
Qed.

Definition reindx_laws_of_type_cat : reindx_laws tt_reindx_from_type_cat.
Proof.
  exists reindx_laws_type_of_type_cat.
  exact reindx_laws_terms_of_type_cat.
Defined.  (* needs to be transparent for comp_law_3 at least *)

Definition comp_1_struct_of_type_cat : comp_1_struct tt_reindx_from_type_cat.
Proof.
  unfold comp_1_struct.
  intros Γ A.
  refine (tpair _ _ _ ).
  unfold tt_reindx_from_type_cat in A. simpl in A.
  exact (ext_type_cat Γ A).
  exact (dpr_type_cat A).
Defined.

Definition tt_reindx_comp_1_of_type_cat : tt_reindx_comp_1_struct CC .
Proof.
  exists tt_reindx_from_type_cat.
  exact comp_1_struct_of_type_cat.
Defined.

Definition comp_2_struct_of_type_cat : comp_2_struct tt_reindx_comp_1_of_type_cat.
Proof.
  split.
  - unfold tt_reindx_comp_1_of_type_cat in *.
    simpl in *.
    + refine (tpair _ _ _ ).
      * { unfold comp_obj. simpl. 
          eapply map_into_Pb.
          - apply  reind_pb_type_cat.
          - cancel_postcomposition.
            apply (idpath (identity _ )). }
      * assert (T:= @Pb_map_commutes_2).
        apply T.
  - intros Γ' γ.
    intro a.
    unfold tt_reindx_comp_1_of_type_cat in *.
    simpl in *.
    apply (pr1 a ;; q_type_cat _ _ ).
Defined.

Definition tt_reindx_type_struct_of_type_cat : tt_reindx_type_struct CC.
Proof.
  exists tt_reindx_comp_1_of_type_cat.
  exact  comp_2_struct_of_type_cat.
Defined.


Lemma comp_laws_1_2_of_type_cat : @comp_laws_1_2 CC
   tt_reindx_type_struct_of_type_cat reindx_laws_of_type_cat.
Proof.
  unfold comp_laws_1_2.
  intros Γ A Γ' γ a. unfold tt_reindx_type_struct_of_type_cat.
  simpl in * .
  refine (tpair _ _ _ ).
  * unfold pairing. simpl.
    destruct a as [a a_sec]; simpl in *.
    etrans. eapply pathsinv0. apply assoc.
    etrans. apply maponpaths. apply dpr_q_type_cat.
    etrans. apply assoc.
    etrans. cancel_postcomposition. apply a_sec.
    apply id_left.
  * simpl.
    apply total2_paths_second_isaprop.
    { apply homs_sets. }
    destruct a as [a a_sec]; simpl in *.

    (* Commute the [pr1] through the [transportf]s. *)
    match goal with |[ |- pr1 (transportf _ ?e0' (transportf _ ?e1' _)) = _ ] =>
                         set (e0:=e0'); set (e1:=e1') end.
    unfold pairing in *. simpl in *.
    etrans. apply maponpaths. refine (transportf_total2 e0 _). simpl.
    etrans. apply maponpaths, maponpaths. refine (transportf_total2 e1 _).
    match goal with
      |[ |- transportf _ _ (pr1 (tpair ?P' ?x' _)) = _]
      => set (x:=x'); set (P:=P') end.    
    change (pr1 (tpair P x _)) with x. subst x; clear P.

    (* These are maps into [Γ' ◂ A [γ]].  We will show they’re equal by comparing their composites with the pullback “projections”, i.e. by using [map_into_Pb_unique].  This will generate two proof branches, for the two pullback projections.

    There are various different ways one can tidy up the two [transportf]s on the LHS in terms of [idtoiso], [maponpaths], and composites (of paths, functions, or morphisms).  We will need them tidied up into two slightly different forms for the two proof branches; it is not obvous what it is best to tidy when.  For now, we tidy up as much as possible before applying [map_into_Pb_unique], and then reassociate as necessary in the two branches. *)

    etrans. refine (functtransportf
                      (@rtype _ tt_reindx_type_struct_of_type_cat _ _ A) _ _ _).
    etrans. apply transportf_reind_type_cat.
    etrans. apply maponpaths, transportf_reind_type_cat.
    etrans. apply transportf_pathscomp0.
    match goal with |[ |- transportf _ ?e' _ = _] => set (e:=e') end.
    etrans. symmetry; apply idtoiso_postcompose.

    eapply map_into_Pb_unique. apply reind_pb_type_cat.

    (* The second pullback projection, to [Γ'], gives the easier of the two branches: *)
    Focus 2.
      etrans. symmetry;apply assoc.
      etrans.
        apply maponpaths. cancel_postcomposition.
        apply maponpaths, maponpaths. symmetry; apply maponpathscomp0.
      etrans. apply maponpaths. apply idtoiso_dpr_type_cat.
      etrans. apply Pb_map_commutes_2.
      symmetry. exact a_sec.

    (* The first projection, to [Γ ◂ A ◂ [π A]], is harder.

    TODO: LaTeX diagram of this!  See photo from 2015-07-02. 

    The main part of the LHS, [pr1 (ν A ⟦ a;; q_type_cat A γ ⟧)], was created as a [map_into_Pb]; we need to use the first component of its definition.  So we need to get the LHS into a form where the first projection of that pullback square appears, i.e. [q_type_cat (reind_type_cat A (dpr_type_cat A)) (a;; q_type_cat A γ)]. *)
    etrans. symmetry; apply assoc.
    assert (e2 :
      (idtoiso e;; q_type_cat A γ)
      = (q_type_cat (reind_type_cat A (dpr_type_cat A)) (a;; q_type_cat A γ))
          ;; (q_type_cat A (dpr_type_cat A))).

      refine (pre_comp_with_iso_is_inj _ _ _ _ _ _ _ _ _).
      Focus 4.
        etrans. Focus 2. symmetry; apply assoc.
        etrans. Focus 2. apply q_q_type_cat.
      Unfocus.
      apply pr2.
    
      etrans. Focus 2. symmetry. apply (idtoiso_q_type_cat _ e0).
      etrans. apply assoc. cancel_postcomposition.
      etrans. apply idtoiso_concat_pr. assumption.
      apply maponpaths, maponpaths.
     
      subst e.
      etrans. symmetry. apply maponpaths, maponpathscomp0.
      etrans. symmetry. apply maponpathscomp0.
      (* TODO: make an access function for sethood of types in type cat. *)
      etrans. apply maponpaths. apply (pr1 (pr2 C)).
      apply maponpathscomp.

    etrans. apply maponpaths, e2. clear e2.
    etrans. apply assoc.
    etrans. cancel_postcomposition. apply Pb_map_commutes_1.
    
    etrans. symmetry. apply assoc.
    etrans. apply maponpaths. apply Pb_map_commutes_1.
    etrans. symmetry. apply assoc. apply maponpaths.
    apply id_right.
Qed.

Lemma comp_law_3_of_type_cat : @comp_law_3 CC tt_reindx_type_struct_of_type_cat reindx_laws_of_type_cat.
Proof.
  unfold comp_law_3.
  intros Γ A Γ' Γ'' γ γ' a. simpl in *.
  unfold pairing; simpl.
  destruct a as [f H]; simpl in *.
  assert (T:=@transportf_total2).
  assert (T' := T (C Γ'') (λ B, Γ'' ⇒ Γ'' ◂ B) ); clear T.
  assert (T2 := T' (λ B f0, f0 ;; dpr_type_cat B = identity Γ'')); clear T'. simpl in T2.
  assert (T3 := T2 _ _ (! reindx_type_comp reindx_laws_of_type_cat γ γ' A)); clear T2; simpl in T3.
  match goal with |[ |- _ = pr1 (transportf _ _ ?x) ;; _ ] => set (X := x) end.
  assert (T4 := T3  X); clear T3.
  assert (T5:= base_paths _ _ T4). clear T4; simpl in *.
  sym.
  etrans.
  cancel_postcomposition.
  apply T5.
  clear T5. unfold X; clear X; simpl in *.
  etrans.
  cancel_postcomposition.
  apply functtransportf.
  rewrite <- idtoiso_postcompose.
  rewrite q_q_type_cat.
  assert (T:=@Pb_map_commutes_1).
  match goal with |[ |- _ ;; ?B' ;; ?C'  = _ ]  => set (B:=B'); set (D:=C') end.
  simpl in *.
  match goal with |[ |- map_into_Pb ?B' ?C' ?D' ?E' ?F' ?G' ?Y' ?Z' ?W'  ;; _ ;; _  = _ ] => 
                   set (f':=B'); set (g:=C'); set (h:=D'); set (k:=E') end.
  match goal with |[ |- map_into_Pb _ _ _ _ ?F' ?G' ?Y' ?Z' _  ;; _ ;; _  = _ ] => 
   set (x:=F'); set (y:=G');
                   set (Y:=Y'); set (Z:=Z')
  end.
  match goal with |[ |- map_into_Pb _ _ _ _ _ _ _ _  ?W'  ;; _ ;; _  = _ ] => set (W:=W') end.
  assert (T2:=Pb_map_commutes_1 f' g h k x y Y Z W).
  unfold B.
  unfold D.
  repeat rewrite assoc.
  etrans. cancel_postcomposition.  cancel_postcomposition. eapply pathsinv0. apply assoc.
  rewrite idtoiso_concat_pr.

  etrans. cancel_postcomposition. cancel_postcomposition. apply maponpaths.
  eapply pathsinv0. apply idtoiso_eq_idpath. 
  {  rewrite <- maponpathscomp0.
     apply maponpaths_eq_idpath.
     simpl.
     unfold reindx_type_comp.
     apply pathsinv0l. }
  rewrite id_right.
  unfold f'. unfold f' in T2.
  etrans.
  cancel_postcomposition. apply T2.
  unfold Y. apply idpath.

  assumption.
Qed.  

Lemma comp_law_4_of_type_cat : @comp_law_4 _ tt_reindx_type_struct_of_type_cat reindx_laws_of_type_cat.
Proof.
  unfold comp_law_4.
  simpl. intros Γ A.
  unfold pairing; simpl.
  etrans.
  apply Pb_map_commutes_1.
  apply idpath.
Qed.


Lemma cwf_laws_of_type_cat : cwf_laws tt_reindx_type_struct_of_type_cat .
Proof.
  repeat split.
  - exists reindx_laws_of_type_cat.
    repeat split.
    + apply comp_laws_1_2_of_type_cat. 
    + apply comp_law_3_of_type_cat. 
    + apply comp_law_4_of_type_cat.
  -  assumption.
  - apply (pr1 (pr1 (pr2 C))). 
  - simpl.
    intros.
    apply (isofhleveltotal2 2).
    + apply homs_sets.
    + intros.
      apply hlevelntosn.
      apply homs_sets.
Qed.

Definition cwf_of_type_cat : cwf_struct CC.
Proof.
  exists tt_reindx_type_struct_of_type_cat.
  exact cwf_laws_of_type_cat.
Defined.
    
End CwF_of_Comp.















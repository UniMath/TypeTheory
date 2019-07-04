
(**
  
 Ahrens, Lumsdaine, Voevodsky, 2015

 Contents:

  - Construction of a precategory with Families from Comprehension precat

*)

Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.
Require Import TypeTheory.Auxiliary.Auxiliary.

Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.OtherDefs.CwF_Pitts.

(* TODO: move *)
Lemma idtoiso_q_typecat {CC : precategory} {C : typecat_structure CC}
      {Γ : CC} (A : C Γ) {Γ' : CC} {f f' : Γ' --> Γ} (e : f = f') :
      q_typecat A f
      = (idtoiso (maponpaths (fun f => ext_typecat Γ' (reind_typecat A f)) e))
          ;; q_typecat A f'.
Proof.
  intros. destruct e; simpl. sym. apply id_left.
  (* Why the heck doesn’t “symmetry” work here!? *)
Defined.
  


(** * wF structure from (split) comprehension structure on a precategory 

Every pre-(split)-Comp-cat gives rise to a pre-category with families.

Since the components of the pre-cat with Families structure are highly successively dependent, we construct most of them individually, before putting them together in [cwf_of_type_precat].
 *)

Section CwF_of_Comp. 

(* TODO: here and in other old files, use [category] instead of explicit [has_homsets] assumptions. *)
Context (CC : precategory) (C : split_typecat_structure CC) (homs_sets : has_homsets CC).

Definition tt_structure_of_typecat : tt_structure CC.
Proof.
  unfold tt_structure.
  exists (ty_typecat C).
  intros Γ A.
  exact (∑ f : Γ --> Γ ◂ A, f ;; dpr_typecat _  = identity _ ). 
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
    + eapply (map_into_Pb _ _ γ (dpr_typecat A)).
      * apply reind_pb_typecat.
      * etrans. apply id_left.
        apply @pathsinv0.
        etrans. eapply pathsinv0. apply assoc.
        etrans. apply maponpaths. apply (pr2 H).
        apply id_right.
    + simpl.
      apply Pb_map_commutes_1.
Defined.    

Definition tt_reindx_from_typecat : tt_reindx_struct CC.
Proof.
  exists tt_structure_of_typecat.
  exact reindx_struct_of_typecat.
Defined.

Local Definition HC : split_typecat :=
  (((CC,,homs_sets),,pr1 C),,pr2 C).

Lemma reindx_laws_type_of_typecat : reindx_laws_type tt_reindx_from_typecat.
Proof.
  split.
  - unfold tt_reindx_from_typecat. simpl.
    intros Γ A.
    apply (@reind_id_type_typecat HC).
  - intros.
    apply (@reind_comp_type_typecat HC).
Defined.  (* needs to be transparent for comp_law_3 at least *)

Lemma reindx_law_1_term_of_typecat 
  (Γ : CC)
  (A : tt_reindx_from_typecat ⟨ Γ ⟩)
  (a : tt_reindx_from_typecat ⟨ Γ ⊢ A ⟩) :
   a ⟦ identity Γ ⟧ =
   transportf (λ B : C Γ, ∑ f : Γ --> Γ ◂ B, f;; dpr_typecat B = identity Γ)
              (! (@reind_id_type_typecat HC Γ A)) a.
Proof.
  intros. simpl. unfold tt_reindx_from_typecat in *. simpl in *.
  apply subtypePath.
  intro; apply homs_sets. simpl.
  apply pathsinv0.
  apply PullbackArrowUnique.
  + destruct a as [f H]; simpl in *.
    rewrite <- H.
    assert (T:=@transportf_total2).
    assert (T':= T (C Γ) (λ B,  Γ --> Γ ◂ B)). simpl in T'.
    assert (T'' := T' (λ B f0, f0 ;; dpr_typecat B = f ;; dpr_typecat A)).
    simpl in *.
    assert (T3 := T'' _ _ (! (@reind_id_type_typecat HC Γ A))).
      (*      assert (T3:= T'' _ _  (! pr1 (pr2 (pr1 (pr2 C))) Γ A) ). *)
    assert (T4 := T3  (tpair (λ f0 : Γ --> Γ ◂ A, f0;; dpr_typecat A = f;; dpr_typecat A) f
                               (idpath (f;; dpr_typecat A)))).
    clear T3 T'' T'. simpl in T4.
    assert (T5:= base_paths _ _ T4). clear T4; simpl in *.
    etrans.
    apply maponpaths_2. apply T5.
    clear T5.
    apply (transportf_dpr_typecat (((CC,,homs_sets),,(pr1 C)),,pr2 C)).

  + simpl.
    rewrite id_left.
    destruct a as [f H]; simpl in *.
    assert (X:= @reind_id_term_typecat HC).
    simpl.
    eapply pathscomp0. apply maponpaths. apply X.
      (* rewrite X. *)
(*      assert (X := (pr2 (pr1 (pr2 C)))). simpl in X.
      rewrite (pr2 X).
*)
    assert (T:=@transportf_total2).
    assert (T':= T (C Γ) (λ B,  Γ --> Γ ◂ B)). simpl in T'.
    assert (T'' := T' (λ B f, f ;; dpr_typecat B = identity Γ)).
    simpl in *.
    assert (T3 := T'' _ _ (! (@reind_id_type_typecat HC Γ A))).
    (*      assert (T3:= T'' _ _  (! pr1 (pr2 (pr1 (pr2 C))) Γ A)).*)
    assert (T4 := T3 (tpair (λ f0 : Γ --> Γ ◂ A, f0;; dpr_typecat A = identity Γ) f H)).
    clear T3 T'' T'. simpl in T4.
    assert (T5:= base_paths _ _ T4). clear T4; simpl in *.
    etrans.
    apply maponpaths_2. apply T5.
    
    clear T5.
      
    rewrite idtoiso_postcompose.
    etrans.
    eapply pathsinv0. apply functtransportf.
    rewrite transport_f_f.
    match goal with |[|- transportf _ ?e _ = _ ] =>
                     assert (He : e = idpath _ )  end .
    apply (pr1 (pr2 C)).
    rewrite He. apply idpath.
Qed.

Lemma foo
  (Γ Γ' Γ'' : CC)
  (γ : Γ' --> Γ)
  (γ' : Γ'' --> Γ')
  (A : ( tt_reindx_from_typecat) ⟨ Γ ⟩)
  (a : ( tt_reindx_from_typecat) ⟨ Γ ⊢ A ⟩)
  :
   a ⟦ γ';; γ ⟧ =
   transportf
     (λ B : C Γ'', ∑ f : Γ'' --> Γ'' ◂ B, f;; dpr_typecat B = identity Γ'')
     (! @reind_comp_type_typecat HC Γ A Γ' γ Γ'' γ') 
     ((a ⟦ γ ⟧) ⟦ γ' ⟧).
Proof.
  intros.
  unfold tt_reindx_from_typecat in *. simpl.
  apply subtypePath.
  intro; apply homs_sets. simpl.
  apply pathsinv0.
  apply PullbackArrowUnique.
  + match goal with |[|- pr1 (transportf ?P' ?e' ?x') ;; _ = _ ] =>
                       set (P:=P') ; set (e := e') ; set (x := x') end.
    assert (T:=@transportf_total2).
    assert (T':= T (C Γ'') (λ B,  Γ'' --> Γ'' ◂ B)); clear T; simpl in T'.
    assert (T'' := T' (λ B f0, f0 ;; dpr_typecat B = identity Γ''));
      clear T'.
    assert (T3:= T'' _ _  e x); clear T''.
    assert (T5:= base_paths _ _ T3); clear T3; simpl in *.
    etrans. apply maponpaths_2. apply T5.
    clear T5.
    etrans. apply (transportf_dpr_typecat (((CC,,homs_sets),,pr1 C),,pr2 C)).
    apply (@Pb_map_commutes_1).

  + destruct a as [f H]; simpl in *.
    assert (X := @reind_comp_term_typecat HC).
    eapply pathscomp0. apply maponpaths. apply X.
(*      rewrite X. *)
(*      assert (X := (pr2 (pr2 (pr2 C)))). simpl in X.
      rewrite (X). 
*)      
    clear X.
      
    assert (T:=@transportf_total2).
    assert (T':= T (C Γ'') (λ B,  Γ'' --> Γ'' ◂ B)); clear T; simpl in T'.
    assert (T'' := T' (λ B f0, f0 ;; dpr_typecat B = identity Γ''));
      clear T'.
    simpl in T''.
    assert (T3 := T'' _ _ (! (@reind_comp_type_typecat HC Γ A Γ' γ Γ'' γ'))); clear T''.
(*      assert (T3:= T'' _ _  (! pr1 (pr2 (pr2 C)) Γ A Γ' γ Γ'' γ') ). *)
    rewrite assoc.
    match goal with | [ |- pr1 (transportf _ _ ?e ) ;; _ ;; _ = _ ] => set (E:=e) end.
    assert (T4 := T3 E); clear T3. 
    assert (T5:= base_paths _ _ T4); clear T4; simpl in *.
    rewrite <- assoc.
    etrans. apply maponpaths_2. apply T5.
      
    clear T5.
    clear E.

    etrans. apply assoc.
    etrans. apply maponpaths_2. apply assoc.
    rewrite idtoiso_postcompose.
    
    etrans. eapply pathsinv0. apply maponpaths_2.
      apply maponpaths_2. apply functtransportf.
    rewrite transport_f_f.

    match goal with |[|- transportf ?a ?b ?c ;; _ ;; _ = _ ] =>
           set (a':=a); set (b':=b); set (c':=c) end.
    assert (b' = idpath _ ).
    { apply (pr1 (pr2 C)). }
    rewrite X; clear X.
    etrans. apply maponpaths_2. apply (@Pb_map_commutes_2).
    etrans. eapply pathsinv0. apply assoc.
    etrans. Focus 2. apply assoc. apply maponpaths. apply (@Pb_map_commutes_2).
Qed.

  
Definition reindx_laws_terms_of_typecat : reindx_laws_terms  reindx_laws_type_of_typecat.
Proof.
  split.
  - apply reindx_law_1_term_of_typecat. 
  - intros. apply foo.
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
  intros Γ A Γ' γ a. unfold tt_reindx_type_struct_of_typecat.
  simpl in * .
  unshelve refine (tpair _ _ _ ).
  * unfold pairing. simpl.
    destruct a as [a a_sec]; simpl in *.
    etrans. eapply pathsinv0. apply assoc.
    etrans. apply maponpaths. apply dpr_q_typecat.
    etrans. apply assoc.
    etrans. apply maponpaths_2. apply a_sec.
    apply id_left.
  * simpl.
    apply subtypePath'.
    + destruct a as [a a_sec]; simpl in *.

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
                      (@rtype _ tt_reindx_type_struct_of_typecat _ _ A) _ _ _).
      etrans. apply (transportf_reind_typecat (((CC,,homs_sets),,pr1 C),,pr2 C)).
      etrans. apply maponpaths, transportf_reind_typecat.
      etrans. apply transport_f_f.
      match goal with |[ |- transportf _ ?e' _ = _] => set (e:=e') end.
      etrans. symmetry; apply idtoiso_postcompose.
    
      eapply map_into_Pb_unique. apply reind_pb_typecat.

    (* The first pullback projection, to [Γ'], gives the easier of the two branches: *)
      etrans. symmetry;apply assoc.
      etrans.
        apply maponpaths. apply maponpaths_2.
        apply maponpaths, maponpaths. symmetry; apply maponpathscomp0.
      etrans. apply maponpaths. apply idtoiso_dpr_typecat.
      etrans. apply Pb_map_commutes_1.
      symmetry. exact a_sec.

    (* The second projection, to [Γ ◂ A ◂ [π A]], is harder.

    TODO: LaTeX diagram of this!  See photo from 2015-07-02. 

    The main part of the LHS, [pr1 (ν A ⟦ a;; q_typecat A γ ⟧)], was created as a [map_into_Pb]; we need to use the first component of its definition.  So we need to get the LHS into a form where the first projection of that pullback square appears, i.e. [q_typecat (reind_typecat A (dpr_typecat A)) (a;; q_typecat A γ)]. *)
      etrans. symmetry; apply assoc.
      assert (e2 :
      (idtoiso e;; q_typecat A γ)
      = (q_typecat (reind_typecat A (dpr_typecat A)) (a;; q_typecat A γ))
          ;; (q_typecat A (dpr_typecat A))).

      unshelve refine (pre_comp_with_iso_is_inj _ _ _ _ _ _ _ _ _).
      Focus 4.
        etrans. Focus 2. symmetry; apply assoc.
        etrans. Focus 2. apply (@q_q_typecat (((CC,,homs_sets),,pr1 C),,pr2 C)).
      Unfocus.
      apply pr2.
    
      etrans. Focus 2. symmetry. apply (idtoiso_q_typecat _ e0).
      etrans. apply assoc. apply maponpaths_2.
      etrans. apply idtoiso_concat_pr.
      apply maponpaths, maponpaths.
     
      subst e.
      etrans. symmetry. apply maponpaths, maponpathscomp0.
      etrans. symmetry. apply maponpathscomp0.
      (* TODO: make an access function for sethood of types in type cat. *)
      etrans. apply maponpaths. apply (pr1 (pr2 C)).
      apply maponpathscomp.

    etrans. apply maponpaths, e2. clear e2.
    etrans. apply assoc.
    etrans. apply maponpaths_2. apply Pb_map_commutes_2.
    
    etrans. symmetry. apply assoc.
    etrans. apply maponpaths. apply Pb_map_commutes_2.
    etrans. symmetry. apply assoc. apply maponpaths.
    apply id_right.
    + apply homs_sets. 
Qed.

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
  rewrite (@q_q_typecat (((CC,,homs_sets),,pr1 C),,pr2 C)).
  match goal with |[ |- _ ;; ?B' ;; ?C'  = _ ]  => set (B:=B'); set (D:=C') end.
  simpl in *.
  match goal with |[ |- map_into_Pb ?B' ?C' ?D' ?E' ?F' ?G' ?Y' ?Z' ?W'  ;; _ ;; _  = _ ] => 
                   set (f':=B'); set (g:=C'); set (h:=D'); set (k:=E') end.
  match goal with |[ |- map_into_Pb _ _ _ _ ?F' ?G' ?Y' ?Z' _  ;; _ ;; _  = _ ] => 
   set (x:=F'); set (y:=G');
                   set (Y:=Y'); set (Z:=Z')
  end.
  match goal with |[ |- map_into_Pb _ _ _ _ _ _ _ _  ?W'  ;; _ ;; _  = _ ] => set (W:=W') end.
  assert (T2:=Pb_map_commutes_2 f' g h k x y Y Z W).
  unfold B.
  unfold D.
  repeat rewrite assoc.
  etrans. apply maponpaths_2.  apply maponpaths_2. eapply pathsinv0. apply assoc.
  rewrite idtoiso_concat_pr.

  etrans. apply maponpaths_2. apply maponpaths_2. apply maponpaths.
  eapply pathsinv0. apply idtoiso_eq_idpath. 
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
  -  assumption.
  - apply (@isaset_types_typecat HC).
  - simpl.
    intros.
    apply (isofhleveltotal2 2).
    + apply homs_sets.
    + intros.
      apply hlevelntosn.
      apply homs_sets.
Qed.

Definition cwf_of_typecat : cwf_struct CC.
Proof.
  exists tt_reindx_type_struct_of_typecat.
  exact cwf_laws_of_typecat.
Defined.
    
End CwF_of_Comp.











(**
  
 Ahrens, Lumsdaine, Voevodsky, 2015

 Contents:

  - Construction of a precategory with Families from Comprehension precat

*)


Require Import UniMath.RezkCompletion.total2_paths.

Require Import Systems.Auxiliary.
Require Import Systems.UnicodeNotations.
Require Import Systems.CompCat_structure.
Require Import Systems.CwF_structure.



(** * wF structure from (split) comprehension structure on a precategory 

Every pre-(split)-Comp-cat gives rise to a pre-category with families.

Since the components of the pre-cat with Families structure are highly successively dependent, we construct most of them individually, before putting them together in [cwf_of_comp_precat].
 *)

Section CwF_of_Comp. 

 
Context (CC : precategory) (C : split_comp_struct CC) (homs_sets : has_homsets CC).

Definition tt_structure_of_comp_cat : tt_structure CC.
Proof.
  unfold tt_structure.
  exists (ty_comp_cat C).
  intros Γ A.
  exact (Σ f : Γ ⇒ Γ ◂ A, f ;; dpr_comp_cat _  = identity _ ). 
Defined.


(* Maybe some of the below stuff should be opaque, to avoid too much unfolding? *)
Definition reindx_struct_of_comp_cat : reindx_structure tt_structure_of_comp_cat.
Proof.
  unfold reindx_structure.
  refine (tpair _ _ _ ).
  - intros Γ Γ'.
    unfold tt_structure_of_comp_cat.
    simpl.
    intros A γ.
    exact (reind_comp_cat A γ).
  - intros Γ Γ' A H. unfold tt_structure_of_comp_cat in *.
    simpl in *.
    intro γ.
    refine (tpair _ _ _ ).
    + eapply (map_into_Pb _ _ (dpr_comp_cat A)  γ).
      * apply reind_pb_comp_cat.
      * etrans. Focus 2. eapply pathsinv0. apply id_left.
        etrans. cancel_postcomposition. apply (idpath (γ ;; pr1 H)).
    {   etrans. eapply pathsinv0. apply assoc.
        etrans. apply maponpaths. apply (pr2 H).
        apply id_right.
    }
    + simpl.
      apply Pb_map_commutes_2.
Defined.    

Definition tt_reindx_from_comp : tt_reindx_struct CC.
Proof.
  exists tt_structure_of_comp_cat.
  exact reindx_struct_of_comp_cat.
Defined.

Lemma reindx_laws_type_of_comp_cat : reindx_laws_type tt_reindx_from_comp.
Proof.
  split.
  - unfold tt_reindx_from_comp. simpl.
    intros Γ A.
    unfold rtype. simpl.
    assert (X:= pr2 (pr1 (pr2 C))). simpl in X.
    apply (pr1 X).
  - intros.
    assert (X:= pr1 (pr2 (pr2 C))). simpl in X.
    apply (X).
Defined.  (* needs to be transparent for comp_law_3 at least *)

Definition reindx_laws_terms_of_comp_cat : reindx_laws_terms  reindx_laws_type_of_comp_cat.
Proof.
  split.
  - intros; simpl. unfold tt_reindx_from_comp in *. simpl in *.
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
      assert (T'' := T' (λ B f, f ;; dpr_comp_cat B = identity Γ)).
      simpl in *.
      assert (T3:= T'' _ _  (! pr1 (pr2 (pr1 (pr2 C))) Γ A)).
      assert (T4 := T3 (tpair (λ f0 : Γ ⇒ Γ ◂ A, f0;; dpr_comp_cat A = identity Γ) f H)).
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
      assert (T'' := T' (λ B f0, f0 ;; dpr_comp_cat B = f ;; dpr_comp_cat A)).
      simpl in *.
      assert (T3:= T'' _ _  (! pr1 (pr2 (pr1 (pr2 C))) Γ A) ).
      assert (T4 := T3  (tpair (λ f0 : Γ ⇒ Γ ◂ A, f0;; dpr_comp_cat A = f;; dpr_comp_cat A) f
                               (idpath (f;; dpr_comp_cat A)))).
      clear T3 T'' T'. simpl in T4.
      assert (T5:= base_paths _ _ T4). clear T4; simpl in *.
      etrans.
      cancel_postcomposition. apply T5.
      clear T5.

      apply transportf_dpr_comp_cat.

  -

    intros.
    unfold tt_reindx_from_comp in *. simpl in *.
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
      assert (T'' := T' (λ B f0, f0 ;; dpr_comp_cat B = identity Γ'')).
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
      assert (T'' := T' (λ B f0, f0 ;; dpr_comp_cat B = identity Γ'')).
        
      simpl in *.
      assert (T3:= T'' _ _  e x).
      assert (T5:= base_paths _ _ T3). clear T3; simpl in *. clear T' T'' T.
      etrans.
      cancel_postcomposition.
      apply T5.
      clear T5.
      etrans.
        apply transportf_dpr_comp_cat.
        set (T:=@Pb_map_commutes_2).
        apply T.
Qed.

Definition reindx_laws_of_comp_cat : reindx_laws tt_reindx_from_comp.
Proof.
  exists reindx_laws_type_of_comp_cat.
  exact reindx_laws_terms_of_comp_cat.
Defined.  (* needs to be transparent for comp_law_3 at least *)

Definition comp_1_struct_of_comp_cat : comp_1_struct tt_reindx_from_comp.
Proof.
  unfold comp_1_struct.
  intros Γ A.
  refine (tpair _ _ _ ).
  unfold tt_reindx_from_comp in A. simpl in A.
  exact (ext_comp_cat Γ A).
  exact (dpr_comp_cat A).
Defined.

Definition tt_reindx_comp_1_of_comp_cat : tt_reindx_comp_1_struct CC .
Proof.
  exists tt_reindx_from_comp.
  exact comp_1_struct_of_comp_cat.
Defined.

Definition comp_2_struct_of_comp_cat : comp_2_struct tt_reindx_comp_1_of_comp_cat.
Proof.
  split.
  - unfold tt_reindx_comp_1_of_comp_cat in *.
    simpl in *.
    + refine (tpair _ _ _ ).
      * { unfold comp_obj. simpl. 
          eapply map_into_Pb.
          - apply  reind_pb_comp_cat.
          - cancel_postcomposition.
            apply (idpath (identity _ )). }
      * assert (T:= @Pb_map_commutes_2).
        apply T.
  - intros Γ' γ.
    intro a.
    unfold tt_reindx_comp_1_of_comp_cat in *.
    simpl in *.
    apply (pr1 a ;; q_comp_cat _ _ ).
Defined.

Definition tt_reindx_comp_struct_of_comp_cat : tt_reindx_comp_struct CC.
Proof.
  exists tt_reindx_comp_1_of_comp_cat.
  exact  comp_2_struct_of_comp_cat.
Defined.


Lemma comp_laws_1_2_of_comp_cat : @comp_laws_1_2 CC
   tt_reindx_comp_struct_of_comp_cat reindx_laws_of_comp_cat.
Proof.
  unfold comp_laws_1_2.
  intros Γ A Γ' γ a. unfold tt_reindx_comp_struct_of_comp_cat.
  simpl in * .
  refine (tpair _ _ _ ).
  * unfold pairing. simpl.
    destruct a as [f H]; simpl in *.
    etrans. eapply pathsinv0. apply assoc.
    etrans. apply maponpaths. apply dpr_q_comp_cat.
    etrans. apply assoc.
    etrans. cancel_postcomposition. apply H.
    apply id_left.
  * simpl.
    apply total2_paths_second_isaprop.
    { apply homs_sets. }
    destruct a as [f H]; simpl in *.


    match goal with |[ |- pr1 (transportf ?P' ?e' (transportf ?P1' ?e1' ?x')) = _ ] =>
                         set (P := P'); set (e:=e'); set (P1 := P1') ; set (e1:=e1'); set (x:=x') end.
    simpl in *.
    unfold pairing in *. simpl in *.
    assert (T:=@transportf_total2).
    assert (T' := T (Γ' ⇒ Γ)).
    unfold rtype in f.
    assert (T'':= T' (λ i, Γ' ⇒ Γ' ◂ reind_comp_cat A i)).
    simpl in T''.
    assert (T3 := T'' (λ i f0, f0 ;; dpr_comp_cat (reind_comp_cat A i) = identity Γ')).
    simpl in *.
    assert (T4:= T3 _ _  e (transportf P1 e1 x)).  
    assert (T5:= base_paths _ _ T4). clear T3; simpl in *. clear T' T'' T.
    etrans.
    apply T5.

    clear T5. clear T4.
    assert (T:=@transportf_total2).
    assert (T':= T (C Γ') (λ B,  Γ' ⇒ Γ' ◂ B)). simpl in T'.
    assert (T'' := T' (λ B f0, f0 ;; dpr_comp_cat B = identity Γ')).
    simpl in *.
    assert (T3:= T'' _ _  e1 x).
    etrans.
    apply maponpaths.
    apply maponpaths.
    apply T3.

    clear T3 T'' T' T.
    simpl.

    clearbody e.

    match goal with |[ |- transportf _ _ ?e' = _ ] => set (x' := e') end.
      pathvia (transportf (λ B, Γ' ⇒ Γ' ◂ B) (maponpaths _ e) x').
      { apply transportf_reind_comp_cat'.  }
      unfold x'; clear x'.
      
      rewrite transportf_pathscomp0.
      rewrite transportf_reind_comp_cat.
      rewrite <- idtoiso_postcompose.


      eapply map_into_Pb_unique. apply reind_pb_comp_cat.

      Focus 2.
      match goal with |[ |- map_into_Pb ?B' ?C' ?D' ?E' ?F' ?G' ?Y' ?Z' ?W' ;; _ ;; _ = _ ] => 
                   set (f':=B'); set (g:=C'); set (h:=D'); set (k:=E') end.
      match goal with |[ |- map_into_Pb _ _ _ _ ?F' ?G' ?Y' ?Z' _   ;; _ ;;_  = _ ] => 
                      set (x1:=F'); set (y:=G');
                   set (Y:=Y'); set (Z:=Z')
     end.
      match goal with |[ |- map_into_Pb _ _ _ _ _ _ _ _  ?W' ;; _ ;; _  = _ ] => set (W:=W') end.

      etrans. Focus 2. eapply pathsinv0. apply H.
      etrans. eapply pathsinv0. apply assoc.
      etrans. apply maponpaths.
      apply idtoiso_dpr_comp_cat.
      set (T:=pr2 reindx_struct_of_comp_cat ). simpl in *.
      set (T':= T _ Γ' _ (tpair _ f H)).

      set (T2:=@Pb_map_commutes_2 _ _ _ _ _ f' g h k x1 y _ Y Z W).
      unfold g.
      etrans. apply T2.
      unfold Z. apply idpath.


       match goal with |[ |- map_into_Pb ?B' ?C' ?D' ?E' ?F' ?G' ?Y' ?Z' ?W' ;; _ ;; _ = _ ] => 
                   set (f':=B'); set (g:=C'); set (h:=D'); set (k:=E') end.
      match goal with |[ |- map_into_Pb _ _ _ _ ?F' ?G' ?Y' ?Z' _   ;; _ ;;_  = _ ] => 
                      set (x1:=F'); set (y:=G');
                   set (Y:=Y'); set (Z:=Z')
     end.
      match goal with |[ |- map_into_Pb _ _ _ _ _ _ _ _  ?W' ;; _ ;; _  = _ ] => set (W:=W') end.

      assert (T2:=@Pb_map_commutes_1 _ _ _ _ _ f' g h k x1 y _ Y Z W).
      admit.

     (*   
      
      
      
     match goal with | [ |- ?e = _ ] => set (EEE := e) end.
    
     match goal with |[ |- map_into_Pb ?B' ?C' ?D' ?E' ?F' ?G' ?Y' ?Z' ?W' ;; _  = _ ] => 
                   set (f':=B'); set (g:=C'); set (h:=D'); set (k:=E') end.
     match goal with |[ |- map_into_Pb _ _ _ _ ?F' ?G' ?Y' ?Z' _   ;; _  = _ ] => 
                      set (x1:=F'); set (y:=G');
                   set (Y:=Y'); set (Z:=Z')
     end.
     match goal with |[ |- map_into_Pb _ _ _ _ _ _ _ _  ?W' ;; _  = _ ] => set (W:=W') end.
(*     match goal with |[ |- ?e = _ ] => set (EE:=e) end. *)
     assert (T1:=Pb_map_commutes_1 f' g h k x1 y Y Z W).
     etrans. apply T1. unfold Y.

     unfold 
     
  rewrite T1.
  assert (T2:=Pb_map_commutes_2 f' g h k _ y Y Z W).

    apply pathsinv0.
    apply PullbackArrowUnique.
    
  -
    
    unfold Y.
    unfold k. 
    repeat rewrite <- assoc.
    apply maponpaths.
    unfold f'.

    admit.
    
   - admit.



(*
 (* attempt with transforming inner transport first *)
    
    match goal with |[ |- pr1 (transportf ?P' ?e' (transportf ?P1' ?e1' ?x')) = _ ] =>
                         set (P := P'); set (e:=e'); set (P1 := P1') ; set (e1:=e1'); set (x:=x') end.
    simpl in *.
    unfold pairing in *. simpl in *.
    etrans.
    apply maponpaths.
    apply maponpaths.
    assert (T:=@transportf_total2).
    assert (T':= T (C Γ') (λ B,  Γ' ⇒ Γ' ◂ B)). simpl in T'.
    assert (T'' := T' (λ B f0, f0 ;; dpr_comp_cat B = identity Γ')).
    simpl in *.
    assert (T3:= T'' _ _  e1 x).
    apply T3.
    
    match goal with |[|- pr1 (transportf _ _ ?x1') = _ ] => set (x1:= x1') end.
    assert (T:=@transportf_total2).
    assert (T' := T (Γ' ⇒ Γ)).
    unfold rtype in f.
    assert (T'':= T' (λ i, Γ' ⇒ Γ' ◂ reind_comp_cat A i)).
    simpl in T''.
    assert (T3 := T'' (λ i f0, f0 ;; dpr_comp_cat (reind_comp_cat A i) = identity Γ')).
    simpl in *.
    assert (T4:= T3 _ _  e x1).  
    assert (T5:= base_paths _ _ T4). clear T3; simpl in *. clear T' T'' T.
    etrans.
    apply T5.

    clear T5. clear T4.
    unfold x1; simpl in *. clear x1.
      clear x.
      match goal with |[ |- transportf _ _ ?e' = _ ] => set (x := e') end.
      pathvia (transportf (λ B, Γ' ⇒ Γ' ◂ B) (maponpaths _ e) x).
       { admit. }
      unfold x; clear x.
       rewrite transportf_pathscomp0.
       match goal with | [ |- transportf _ ?p _ = _ ] => set (PP:=p) end.
       match goal with |[ |- transportf _ _ (map_into_Pb ?X1 ?X2 ?X3 ?X4 _ _ _ _ _ ) = _ ] =>
           set (x1 := X1); set (x2 := X2); set (x3 := X3) ; set (x4:=X4) end.
       match goal with |[ |- transportf _ _ (map_into_Pb _ _ _ _ ?X1 ?X2 ?X3 ?X4 _ ) = _ ] =>
           set (x5 := X1); set (x6 := X2); set (x7 := X3) ; set (x8:=X4) end.
       match goal with |[ |- transportf _ _ (map_into_Pb _ _ _ _ _ _ _ _ ?X1 ) = _ ] =>
                        set (x9 := X1) end.
       assert (X10:= Pb_map_commutes_1 x1 x2 x3 x4 x5 x6 x7 x8 x9).
       rewrite X10.

       Check (e1 @ maponpaths (rtype A) e).
       rewrite <- idtoiso_postcompose.
      Check (e1 @ maponpaths _  e).
      admit.
*)
*)
Admitted.


(* does not seem to be helpful, instantiation using [apply] fails *)
Lemma bla : ∀ (A : UU) (B : A → UU) (C0 : ∀ a : A, B a → UU) 
              (x1 x2 : A) (p : x1 = x2) (*yz : Σ y : B x1, C0 x1 y*) (y : B x1) z,
        pr1
         (transportf (λ x : A, Σ y : B x, C0 x y) p
            (tpair (λ y : B x1, C0 x1 y) y z)) = transportf B p y.
Proof.
  intros.
  assert (T:=@transportf_total2 A B C0 x1 x2 p (tpair _ y z)).
  assert (T':= base_paths _ _ T).
  exact T'.
Defined.  

Lemma comp_law_3_of_comp_cat : @comp_law_3 CC tt_reindx_comp_struct_of_comp_cat reindx_laws_of_comp_cat.
Proof.
  unfold comp_law_3.
  intros Γ A Γ' Γ'' γ γ' a. simpl in *.
  unfold pairing; simpl.
  destruct a as [f H]; simpl in *.
  assert (T:=@transportf_total2).
  assert (T' := T (C Γ'') (λ B, Γ'' ⇒ Γ'' ◂ B) ); clear T.
  assert (T2 := T' (λ B f0, f0 ;; dpr_comp_cat B = identity Γ'')); clear T'. simpl in T2.
  assert (T3 := T2 _ _ (! reindx_type_comp reindx_laws_of_comp_cat γ γ' A)); clear T2; simpl in T3.
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
  rewrite (q_comp_comp_cat C).
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

Lemma comp_law_4_of_comp_cat : @comp_law_4 _ tt_reindx_comp_struct_of_comp_cat reindx_laws_of_comp_cat.
Proof.
  unfold comp_law_4.
  simpl. intros Γ A.
  unfold pairing; simpl.
  etrans.
  apply Pb_map_commutes_1.
  apply idpath.
Qed.


Lemma cwf_laws_of_comp_cat : cwf_laws tt_reindx_comp_struct_of_comp_cat .
Proof.
  repeat split.
  - exists reindx_laws_of_comp_cat.
    repeat split.
    + apply comp_laws_1_2_of_comp_cat. 
    + apply comp_law_3_of_comp_cat. 
    + apply comp_law_4_of_comp_cat.
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

Definition cwf_of_comp_cat : cwf_struct CC.
Proof.
  exists tt_reindx_comp_struct_of_comp_cat.
  exact cwf_laws_of_comp_cat.
Defined.
    
End CwF_of_Comp.















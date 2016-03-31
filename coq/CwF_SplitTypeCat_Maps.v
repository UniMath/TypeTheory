
(**

 Ahrens, Lumsdaine, Voevodsky, 2015 - 2016

*)

Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.more_on_pullbacks.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.functor_categories.

Require Import Systems.Auxiliary.
Require Import Systems.UnicodeNotations.
Require Import Systems.Structures.
Require Import Systems.Bicats.Auxiliary.

Local Set Automatic Introduction.
(* only needed since imports globally unset it *)

Section Fix_Base_Category.

Context {C : Precategory} {X : obj_ext_structure C}.

Local Notation hsC := (homset_property C).

Local Notation "'Yo'" := (yoneda C hsC).
Local Notation "'Yo^-1'" :=  (invweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ ))).

Local Notation "Γ ◂ A" := (comp_ext _ Γ A) (at level 30).
Local Notation "A [ f ]" := (# (TY X : functor _ _ ) f A) (at level 4).

(** * Definition of compatibility

We define here what it means for a families-structure and a _q_-morphism structure to be _compatible_. *)

Section Compatible_Structures.

Definition compatible_scomp_families (Y : families_structure hsC X)
         (Z : qq_morphism_structure X) : UU
  := ∀ Γ Γ' A (f : C⟦Γ', Γ⟧) , Q Y A[f] = #(yoneda _ hsC) (qq Z f A) ;; Q Y A.

Definition compatible_fam_structure (Z : qq_morphism_structure X) : UU
  := Σ Y : families_structure hsC X, compatible_scomp_families Y Z.

Definition compatible_qq_morphism_structure (Y : families_structure hsC X) : UU
  := Σ Z : qq_morphism_structure X, compatible_scomp_families Y Z.

End Compatible_Structures.

(** * Defining a (compatible) families structure, given a _q_-morphism structure *)

Section compatible_fam_structure_from_comp.

Variable Z : qq_morphism_data X.
Variable ZZ : qq_morphism_axioms Z.

Definition tm_carrier (Γ : C) : UU :=
  Σ A : (TY X : functor _ _ ) Γ : hSet,
  Σ s : C⟦Γ, Γ ◂ A⟧, s ;; π _ = identity _ .

Lemma isaset_tm_carrier Γ : isaset (tm_carrier Γ).
Proof.
  apply (isofhleveltotal2 2).
  - apply setproperty.
  - intro. apply (isofhleveltotal2 2).
    + apply hsC.
    + intro. apply isasetaprop. apply hsC.
Qed.

Definition tm Γ : hSet := hSetpair _ (isaset_tm_carrier Γ).

Definition tm_on_mor Γ Γ' (f : C⟦Γ',Γ⟧) : tm_carrier Γ → tm_carrier Γ'.
Proof.
  intro Ase.
  exists ((pr1 Ase) [f]).
  eapply pb_of_section.
  - apply (pr2 (pullback_from_comp Z f _ )).
  - apply (pr2 (pr2 Ase)).
Defined.

Definition tm_functor_data : functor_data C^op HSET.
Proof.
  exists tm.
  refine tm_on_mor.
Defined.

Lemma type_eq_from_tm_functor_eq {Γ} {t t' : (tm_functor_data Γ : hSet)}
  : t = t' -> pr1 t = pr1 t'.
Proof.
  apply base_paths.
Qed.

Lemma section_eq_from_tm_functor_eq {Γ} (t t' : (tm_functor_data Γ : hSet)) 
  (e : t = t')
  : pr1 (pr2 t)
      ;; idtoiso (maponpaths (comp_ext X Γ) (type_eq_from_tm_functor_eq e))
    = pr1 (pr2 t').
Proof.
  destruct e; simpl.
  etrans.
    apply @maponpaths, @pathsinv0, idtoiso_eq_idpath.
    apply maponpaths_eq_idpath, setproperty.
  apply id_right.
Qed.

Lemma tm_functor_eq {Γ} (t t' : (tm_functor_data Γ : hSet)) 
  (eA : pr1 t = pr1 t')
  (es : (pr1 (pr2 t)) ;; idtoiso (maponpaths (comp_ext X Γ) eA) = (pr1 (pr2 t')))
  : t = t'.
Proof.
  destruct t as [A [s e]], t' as [A' [s' e']]; simpl in *.
  use total2_paths; simpl.
    apply eA.
  apply subtypeEquality. intro; apply hsC.
  simpl. eapply pathscomp0. refine (pr1_transportf _ _ _ _ _ eA _).
  simpl. eapply pathscomp0. apply functtransportf.
  eapply pathscomp0. eapply pathsinv0. apply idtoiso_postcompose.
  exact es.
Qed.

(* A useful more specialised case of equality on terms. *)
Lemma tm_functor_eq' {Γ : C} (A : (TY X : functor _ _) Γ : hSet)
  {Γ'} {f f' : Γ' ⇒ Γ} (e_ff' : f = f')
  {s : Γ' ⇒ Γ' ◂ # (TY X : functor _ _) f A} (es : s ;; π _ = identity _)
  {s' : Γ' ⇒ Γ' ◂ # (TY X : functor _ _) f' A} (es' : s' ;; π _ = identity _)
  (e_ss' : s' = s ;; idtoiso (maponpaths (fun f => Γ' ◂ # (TY X : functor _ _) f A) e_ff'))
: (( A[f] ,, (s,, es)) : tm_functor_data Γ' : hSet)
  = (A[f'] ,, (s',, es')).
Proof.
  destruct e_ff'; simpl in *.
  apply maponpaths.
  rewrite id_right in e_ss'.
  destruct e_ss'.
  apply maponpaths. apply hsC.
Qed.

Lemma is_functor_tm : is_functor tm_functor_data.
Proof.
  split; [unfold functor_idax | unfold functor_compax].
  - intro Γ. apply funextsec.
    intro t. simpl.
    destruct t as [A [s e]]. cbn.
    use tm_functor_eq; simpl.
    + use (toforallpaths _ _ _ (functor_id (TY X) _ ) A).
    + simpl. rewrite <- (pr1 ZZ).
      match goal with |[|- PullbackArrow ?HH _ _ _ _ ;; _ = _ ] => set (XR := HH) end.
      etrans. apply (PullbackArrow_PullbackPr2 XR). apply id_left.
  - intros Γ Γ' Γ'' f g. cbn.
    apply funextsec.
    intro t.
    destruct t as [A [s e]]; simpl in *.
    unfold tm_on_mor. simpl.
    use tm_functor_eq; simpl.
    + abstract (apply (toforallpaths _ _ _ (functor_comp (TY X) _ _ _ _ _) A)).
    + { cbn.
      apply PullbackArrowUnique; cbn.
      - rewrite <- assoc.  
        rewrite (@idtoiso_π _ X).
        apply (PullbackArrow_PullbackPr1 (mk_Pullback _ _ _ _ _ _ _)).
      - cbn.
        apply (MorphismsIntoPullbackEqual (pr2 (pr2 Z _ _ _ _ ))); simpl.
        + etrans. Focus 2. apply assoc.
          etrans. Focus 2.
            apply maponpaths, @pathsinv0.
            apply (PullbackArrow_PullbackPr1 (mk_Pullback _ _ _ _ _ _ _)).
          etrans. Focus 2. apply @pathsinv0, id_right.
          etrans. apply @pathsinv0, assoc.
          etrans. eapply maponpaths, pathsinv0.
            apply (pr1 (pullback_from_comp _ _ _)).
          etrans. apply assoc.
          etrans. Focus 2. apply id_left.
          refine (maponpaths (fun h => h ;; g) _).
          etrans. apply @pathsinv0, assoc.
          rewrite (@idtoiso_π _ X).
          apply (PullbackArrow_PullbackPr1 (mk_Pullback _ _ _ _ _ _ _)).
        + repeat rewrite <- assoc.
          etrans. apply maponpaths. rewrite assoc.
            apply @pathsinv0, qq_morphism_structure_comp_general, ZZ.
          etrans. apply (PullbackArrow_PullbackPr2 (mk_Pullback _ _ _ _ _ _ _)).
          etrans. apply @pathsinv0, assoc.
          apply (maponpaths (fun h => g ;; h)).
          apply @pathsinv0. apply (PullbackArrow_PullbackPr2 (mk_Pullback _ _ _ _ _ _ _)). }
Qed.

Definition tm_functor : functor _ _  := tpair _ _ is_functor_tm.

Arguments tm_functor : simpl never.

Definition pp_carrier (Γ : C^op) : (tm_functor Γ : hSet) → (TY X : functor _ _ ) Γ : hSet.
Proof.
  exact pr1.
Defined.

Lemma is_nat_trans_pp_carrier : is_nat_trans tm_functor (TY X : functor _ _ ) pp_carrier.
Proof.
  intros Γ Γ' f.
  apply idpath.
Defined.

Definition pp_from_comp : preShv C ⟦tm_functor, TY X⟧ := tpair _ _ is_nat_trans_pp_carrier.

Arguments pp_from_comp : simpl never.

Section Q_from_comp.

Variable Γ : C.
Variable A : (TY X : functor _ _ ) Γ : hSet.

Definition Q_from_comp_data :
 ∀ x : C^op, HSET ⟦ (Yo (Γ ◂ A) : functor _ _ ) x, tm_functor x ⟧.
Proof.
  intros Γ' f. simpl in *.
  unfold yoneda_objects_ob in f.
  unfold tm_carrier. mkpair.
  + exact A[f;;π _ ].
  + apply (section_from_diagonal _ (pr2 (pullback_from_comp Z _ _ ))). 
    exists f. apply idpath.
Defined.

Lemma is_nat_trans_Q_from_comp : is_nat_trans _ _ Q_from_comp_data.
Proof.
  intros Γ' Γ'' f. simpl.
  apply funextsec. intro g.
  unfold yoneda_objects_ob. cbn.    
  use tm_functor_eq; simpl pr1.
  + etrans. apply (maponpaths (fun k => #(TY X : functor _ _ ) k A) (assoc _ _ _)).
    apply (toforallpaths _ _ _ (functor_comp (TY X) _ _ _ _ _ )).
  + apply PullbackArrowUnique.
    * cbn.
      etrans. apply (!assoc _ _ _).
      etrans. apply maponpaths, idtoiso_π.
      match goal with |[|- PullbackArrow ?HH _ _ _ _ ;; _ = _ ] => set (XR := HH) end.
      apply (PullbackArrow_PullbackPr1 XR).
    * cbn.
      {
        use (MorphismsIntoPullbackEqual (pr2 (pr2 Z _ _ _ _ ))).
        - etrans. Focus 2. apply assoc.
          match goal with [|- _ = _ ;; (PullbackArrow ?HH _ _ _ _ ;; _ )] =>
                          set (XR := HH) end.
          rewrite (PullbackArrow_PullbackPr1 XR). clear XR.
          etrans. apply (!assoc _ _ _).
          rewrite <- (pr1 (pullback_from_comp Z f _ )).
          etrans. apply assoc.
          etrans. apply assoc4.
          rewrite (@idtoiso_π _ X).
          match goal with |[|- PullbackArrow ?HH _ _ _ _ ;; _ ;; _ = _ ] => set (XR := HH) end.
          rewrite (PullbackArrow_PullbackPr1 XR).
          rewrite id_right. apply id_left.
        - etrans. Focus 2. apply assoc.
          match goal with |[|- _ = _ ;; (PullbackArrow ?HH _ _ _ _ ;; _ )] => set (XR := HH) end.
          rewrite (PullbackArrow_PullbackPr2 XR).
          clear XR.
          assert (XT:= pr2 ZZ). simpl in XT.
          specialize (XT _ _ _ (g ;; π _ ) f ).
          specialize (XT A).
          rewrite maponpathscomp0 . 
          rewrite idtoiso_concat.
          simpl.
          match goal with |[ H : ?EE =  _ |- ?DD ;; (?II ;; ?KK) ;; _  ;; _  = _ ] => 
                           set (d := DD); set (i:= II) end.
          rewrite <- assoc.
          rewrite <- assoc.
          etrans. apply maponpaths. apply (!assoc _ _ _ ).
          
          etrans. apply maponpaths. apply maponpaths. apply assoc.
          etrans. apply maponpaths. apply maponpaths. 
          apply (!XT).
          unfold i. clear i. clear XT.
          rewrite (@idtoiso_qq _ X).
          unfold d; clear d.
          match goal with [|- PullbackArrow ?HH _ _ _ _ ;; _  = _ ] =>
                          set (XR := HH) end.
          apply (PullbackArrow_PullbackPr2 XR). 
      } 
Qed.

Definition Q_from_comp : _ ⟦ Yo (Γ ◂ A), tm_functor⟧ := tpair _ _ is_nat_trans_Q_from_comp.

Arguments Q_from_comp : simpl never.

Definition Q_from_comp_commutes : # Yo (π _ ) ;; yy A = Q_from_comp ;; pp_from_comp.            
Proof.
  apply nat_trans_eq. apply has_homsets_HSET.
  intro Γ'. apply idpath.
Defined.

Definition section_qq_π  (Γ' : C) (f : C⟦ Γ', Γ⟧) 
  (s : C ⟦ Γ', Γ' ◂ A[f] ⟧)
  (e : s ;; π (A[f]) = identity Γ'):
   s ;; qq Z f A ;; π A = f.
Proof.
  etrans. apply @pathsinv0, assoc.
  etrans. apply @maponpaths, @pathsinv0, qq_π.
  etrans. apply assoc.
  etrans. eapply (maponpaths (fun g => g ;; f)). exact e.
  apply id_left.
Qed.

Lemma Q_from_comp_reconstruction
  {Γ' : C} ( ft : C ⟦ Γ', Γ ◂ A ⟧ )
: ft = pr1 (pr2 (Q_from_comp_data Γ' ft)) ;; qq Z (ft ;; π A) A.
Proof.
  cbn. apply pathsinv0, (PullbackArrow_PullbackPr2 (mk_Pullback _ _ _ _ _ _ _)).
Qed.


Lemma isPullback_Q_from_comp_commutes : isPullback _ _ _ _ Q_from_comp_commutes.
Proof.
  apply pb_if_pointwise_pb. intros Γ'.
  apply isPullback_HSET. intros f [A' [s e]] e_A_A'; simpl in e_A_A'.
  destruct e_A_A'.
  mkpair.
  - exists (s ;; qq Z f A).
    simpl; unfold yoneda_morphisms_data.
    split.
    + apply (section_qq_π _ _ _ e).
    + use tm_functor_eq'; simpl.
      apply (section_qq_π _ _ _ e).
      use (map_into_Pb_unique _ (qq_π_Pb Z _ _  )).
      * etrans. apply e.
        apply pathsinv0.
        etrans. apply @pathsinv0, assoc.
        etrans. apply @maponpaths.
          etrans. Focus 2. eapply idtoiso_π.
          eapply (maponpaths (fun p => p ;; _)).
          apply pathsinv0, maponpaths, maponpaths.
          apply (maponpathscomp (fun f => # (TY X : functor _ _) f A)).
        apply (PullbackArrow_PullbackPr1 (mk_Pullback _ _ _ _ _ _ _)).
      * apply pathsinv0. etrans. apply @pathsinv0, assoc.
        etrans. apply @maponpaths.
          etrans. Focus 2. eapply idtoiso_qq.
          eapply (maponpaths (fun p => p ;; _)).
          apply pathsinv0, maponpaths, maponpaths.
          apply (maponpathscomp (fun f => # (TY X : functor _ _) f A)).
        apply (PullbackArrow_PullbackPr2 (mk_Pullback _ _ _ _ _ _ _)).
  - intros ft.
    apply subtypeEquality. intro. apply isapropdirprod. apply hsC. apply setproperty.
    simpl. destruct ft as [ ft [ e1 e2 ] ]; simpl.
    etrans. apply Q_from_comp_reconstruction.
    etrans. eapply (maponpaths (fun g => g ;; _)).
      apply @pathsinv0. use (section_eq_from_tm_functor_eq _ _ (!e2)).
    simpl. etrans. apply @pathsinv0, assoc.
    apply maponpaths.
    etrans. Focus 2. apply idtoiso_qq.
    eapply (maponpaths (fun p => p ;; _)).
    apply pathsinv0, maponpaths, maponpaths, maponpaths.
    apply setproperty.
    Unshelve. apply pathsinv0. exact e1.
Qed.

End Q_from_comp.

Notation "'cQ'" := Q_from_comp_data.
Notation "'cQ'" := Q_from_comp.
Notation "'cTm'":= tm_functor.
Notation "'cp'" := pp_from_comp.
Arguments Q_from_comp_data { _ } _ _ _ : simpl never.
Arguments Q_from_comp { _ } _ : simpl never.
Arguments tm_functor : simpl never.
Arguments pp_from_comp : simpl never.


Lemma cQ_compatible_pw (Γ Γ' : C) (A : (TY X : functor _ _ ) Γ : hSet) (f : C ⟦ Γ', Γ ⟧) (Γ'' : C)
          (g : C ⟦ Γ'', Γ' ◂ A[f] ⟧)
   :
   Q_from_comp_data A[f] Γ'' g =
   Q_from_comp_data A Γ'' (g ;; qq Z f A).
Proof.
    simpl. cbn.
    use tm_functor_eq. 
    + unfold yoneda_morphisms_data.
      etrans. Focus 2. eapply (maponpaths (fun k => #(TY X : functor _ _ ) k A)).
                       apply (@assoc C).
      etrans. Focus 2. eapply (maponpaths (fun k => #(TY X : functor _ _ ) k A)).
                       apply maponpaths.
                       apply (pr1 (pullback_from_comp Z _ _ )).
      etrans. Focus 2.  eapply (maponpaths (fun k => #(TY X : functor _ _ ) k A)).
                       apply @pathsinv0, (@assoc C).
      apply (toforallpaths _ _ _ (!functor_comp (TY X) _ _ _ _ _ ) A).
    + simpl.
      apply PullbackArrowUnique.
      * simpl. cbn.
        etrans. apply @pathsinv0, (@assoc C).
        etrans. apply maponpaths. apply idtoiso_π.
        match goal with [|- PullbackArrow ?HH _ _ _ _ ;; _  = _ ] =>
                            set (XR := HH) end.
        apply (PullbackArrow_PullbackPr1 XR). 
      * simpl. cbn.
        etrans. apply @pathsinv0, (@assoc C).
        unfold yoneda_morphisms_data.
        rewrite maponpathscomp0.
        rewrite maponpathscomp0.
        rewrite maponpathscomp0.
        rewrite idtoiso_concat.
        rewrite idtoiso_concat.
        rewrite idtoiso_concat.
        simpl.
        etrans. apply maponpaths. apply assoc4.
        etrans. apply maponpaths. apply cancel_postcomposition. apply assoc. 
        etrans. apply maponpaths. apply (!assoc _ _ _ ).
        etrans. apply maponpaths. apply maponpaths. apply idtoiso_qq.
        etrans. apply maponpaths. apply (!assoc _ _ _ ).  
        etrans. apply maponpaths. apply maponpaths.
                apply idtoiso_qq.
        etrans. apply maponpaths. apply (!assoc _ _ _ ).
        etrans. apply maponpaths. apply maponpaths.
                apply idtoiso_qq.
        etrans. apply maponpaths. apply maponpaths. apply (pr2 ZZ).
        
        etrans. apply maponpaths. apply maponpaths. apply (!assoc _ _ _ ).
        etrans. apply maponpaths. apply assoc.
        
        match goal with [|- _ ;; (?I ;; _ ) = _ ] => set (i := I) end.
        assert (XR : i = identity _ ).
        {
          unfold i; clear i.
          apply pathsinv0. 
          etrans. Focus 2. apply (maponpaths pr1 (idtoiso_concat _ _ _ _ _ _ )).
          apply idtoiso_eq_idpath.
          rewrite <- maponpathscomp0.
          apply maponpaths_eq_idpath.
          apply setproperty. (* setproperty should not be needed *)
        }
        rewrite XR. rewrite id_left.
        rewrite assoc.
        match goal with |[ |- PullbackArrow ?HH _ _ _ _  ;; _ ;; _  = _ ] => set (XT:=HH) end.
        
        etrans. apply cancel_postcomposition. apply (PullbackArrow_PullbackPr2 XT).
        apply idpath.
Qed.



(* 
  the next statement morally reads

  cQ Γ' (# (TY X) f A) Γ'' =
  (λ g : C ⟦ Γ'', Γ' ◂ # (TY X) f A ⟧, g ;; qq Z f A) ;; cQ Γ A Γ''

  but needs many type annotations to trigger coercions
*)

Lemma cQ_commutes (Γ Γ' : C) (A : (TY X : functor _ _ ) Γ : hSet) (f : C ⟦ Γ', Γ ⟧) (Γ'' : C)
  :   (cQ A[f] : nat_trans _ _ ) Γ'' =
      ((λ g : hSetpair (C ⟦ Γ'', Γ' ◂ A[f] ⟧) (hsC _ _ ), g ;; qq Z f A) : HSET ⟦ _ , hSetpair _ (hsC _ _ ) ⟧) ;; (cQ A : nat_trans _ _ ) Γ''.
Proof.
  simpl.
  apply funextsec. 
  apply cQ_compatible_pw.
Qed.


Definition comp_fam_structure_from_comp
  : compatible_fam_structure (Z,,ZZ).
Proof.
  mkpair.
  - mkpair.
    + mkpair.
      * apply tm_functor.
      * {
          mkpair.
          - apply pp_from_comp.
          - intros. apply Q_from_comp.
        } 
    + unfold families_structure_axioms.
      intros.
      exists (Q_from_comp_commutes _ _ ).
      apply isPullback_Q_from_comp_commutes.
  - unfold compatible_scomp_families. 
    intros Γ Γ' A f.
    apply nat_trans_eq. 
    { apply has_homsets_HSET. }
    intro Γ''. 
    apply cQ_commutes.
Defined.
    
End compatible_fam_structure_from_comp.

Notation "'cQ'" := Q_from_comp_data.
Notation "'cQ'" := Q_from_comp.
Notation "'cTm'":= tm_carrier.
Notation "'cTm'":= (tm_on_mor _ _ _ ).
Notation "'cp'" := pp_from_comp.
Arguments Q_from_comp_data {_} _ {_} _ _ _ : simpl never.
Arguments Q_from_comp {_} _ {_} _ : simpl never.
Arguments tm_functor : simpl never.
Arguments pp_from_comp : simpl never.
Arguments tm_on_mor : simpl never.

(** * Defining a (compatible) _q_-morphism structure, given a families structure *)

Section compatible_comp_structure_from_fam.

Variable Y : families_structure hsC X.

Section qq_from_fam.

Variables Γ Γ' : C.
Variable f : C⟦Γ', Γ⟧.
Variable A : (TY X : functor _ _) Γ : hSet.

Let Xk := mk_Pullback _ _ _ _ _ (pr1 (pr2 Y Γ A)) (pr2 (pr2 Y Γ A)).

Definition Yo_of_qq : _ ⟦Yo (Γ' ◂ A[f]), Yo (Γ ◂ A) ⟧.
Proof.
  simple refine (PullbackArrow Xk _ _ _ _ ).
  - apply (#Yo (π _) ;; #Yo f ). 
  - apply (Q Y).
  - abstract (
        clear Xk;
        assert (XT:= pr1 (pr2 Y Γ' A[f]));
        eapply pathscomp0; try apply XT; clear XT;
        rewrite <- assoc; apply maponpaths;
        apply pathsinv0, yy_natural
    ).
Defined.

Lemma Yo_of_qq_commutes_1 : # Yo (π _ ) ;; # Yo f = Yo_of_qq ;; # Yo (π _ ) .
Proof.
  apply pathsinv0.
  apply (PullbackArrow_PullbackPr1 Xk).
Qed.

Lemma Yo_of_qq_commutes_2 : Yo_of_qq ;; Q _ A = Q Y _ .
Proof.
  apply (PullbackArrow_PullbackPr2 Xk).
Qed.  

Lemma isPullback_Yo_of_qq : isPullback _ _ _ _ Yo_of_qq_commutes_1.
Proof.
  simple refine (isPullback_two_pullback _ _ _ _ _ _ _ _ _ _ ).
  - apply functor_category_has_homsets.
  - apply (TY X).
  - apply (TM Y).
  - apply (yy A).
  - apply pp.
  - apply Q.
  - apply (pr1 (pr2 Y _ _ )).
  - apply (pr2 (pr2 Y _ _ )).
  - match goal with [|- isPullback _ _ _ _ ?HH ] => generalize HH end.
    rewrite <- yy_natural.
    rewrite Yo_of_qq_commutes_2.
    intro.
    apply (pr2 (pr2 Y _ _ )).
Defined.

Definition qq_fam :  _ ⟦Γ' ◂ A[f] , Γ ◂ A⟧.
Proof.
  apply (invweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ ))).
  apply Yo_of_qq.
Defined.

Lemma Yo_qq_fam_Yo_of_qq : # Yo qq_fam = Yo_of_qq.
Proof.
  unfold qq_fam.
  assert (XT := homotweqinvweq
     (weqpair _ (yoneda_fully_faithful _  hsC (Γ'◂ A[f]) (Γ ◂ A)  ))).
  apply XT.
Qed.

Lemma qq_commutes_1 : π _ ;; f = qq_fam ;; π _ .
Proof.
  assert (XT:= Yo_of_qq_commutes_1).
  rewrite <- Yo_qq_fam_Yo_of_qq in XT.
  do 2 rewrite <- functor_comp in XT.
  apply (invmaponpathsweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ ))).
  apply XT.
Qed.

Definition isPullback_qq : isPullback _ _ _ _ qq_commutes_1.
Proof.
  use (isPullback_preimage_square _ _ _ Yo).
  - apply hsC.
  - apply yoneda_fully_faithful.
  - assert (XT:= isPullback_Yo_of_qq).
    match goal with |[|- isPullback _ _ _ _ ?HHH] => generalize HHH end.
    rewrite Yo_qq_fam_Yo_of_qq.
    intro. assumption.
Qed.

End qq_from_fam.

Definition comp_from_fam : qq_morphism_data X.
Proof.
  mkpair.
  - intros. apply qq_fam.
  - intros. simpl.
    exists (qq_commutes_1 _ _ _ _ ).
    apply isPullback_qq.
Defined.


Lemma is_split_comp_from_fam : qq_morphism_axioms comp_from_fam.
Proof.
  split.
  - intros Γ A. simpl.
    apply (invmaponpathsweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ ))).
    etrans; [ apply (homotweqinvweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ ))) | idtac ].    
    apply pathsinv0.
    unfold Yo_of_qq.
    apply PullbackArrowUnique. 
    + etrans. apply maponpaths. cbn. apply idpath. 
      rewrite <- functor_comp.
      etrans. eapply pathsinv0. apply (functor_comp Yo).
      apply maponpaths. rewrite (@idtoiso_π _ X).
      apply pathsinv0. apply id_right.
    + etrans. apply maponpaths. cbn. apply idpath.
      apply idtoiso_Q.
  - intros.
    apply (invmaponpathsweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ ))).
    etrans; [ apply (homotweqinvweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ ))) | idtac ].    
    sym. apply PullbackArrowUnique.
    + etrans. apply maponpaths. cbn. apply idpath.
      rewrite <- functor_comp.
      etrans. eapply pathsinv0. apply (functor_comp Yo).
      apply maponpaths.
      rewrite <- assoc. rewrite <- qq_commutes_1 .
      repeat rewrite assoc.
      rewrite assoc4.
      etrans. apply cancel_postcomposition. apply maponpaths. eapply pathsinv0. apply qq_commutes_1 .
      apply cancel_postcomposition.
      repeat rewrite assoc.
      apply cancel_postcomposition.
      apply idtoiso_π.
    + etrans. apply maponpaths. cbn. apply idpath.
      etrans. apply cancel_postcomposition. apply functor_comp.
      rewrite <- assoc.
      rewrite Yo_qq_fam_Yo_of_qq.
      rewrite  Yo_of_qq_commutes_2 .
      etrans. apply cancel_postcomposition. apply functor_comp.
      rewrite <- assoc.
      etrans. apply maponpaths. apply cancel_postcomposition. apply Yo_qq_fam_Yo_of_qq.
      etrans. apply maponpaths. apply Yo_of_qq_commutes_2 .
      apply idtoiso_Q.
Qed.

Definition split_comp_structure_from_fam
  : qq_morphism_structure X.
Proof.
  exists comp_from_fam.
  apply is_split_comp_from_fam.
Defined.

Lemma comp_from_fam_compatible_scomp_families : compatible_scomp_families Y split_comp_structure_from_fam.
Proof.
  intros Γ Γ' A f.
  assert (XR:= Yo_of_qq_commutes_2).
  apply pathsinv0.
  rewrite Yo_qq_fam_Yo_of_qq.
  apply XR.
Qed.

      
End compatible_comp_structure_from_fam.

End Fix_Base_Category.

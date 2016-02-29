
(**

 Ahrens, Lumsdaine, Voevodsky, 2015 - 2016

*)

Require Export Systems.Auxiliary.
Require Export Systems.UnicodeNotations.
Require Export UniMath.Foundations.Basics.Sets.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.more_on_pullbacks.
Require Export UniMath.CategoryTheory.UnicodeNotations.
Require Export UniMath.CategoryTheory.functor_categories.
Require Export UniMath.CategoryTheory.opp_precat.
Require Export UniMath.CategoryTheory.category_hset.
Require Export UniMath.CategoryTheory.yoneda.


Undelimit Scope transport.


Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).
Local Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op").


Local Definition preShv C := [C^op , HSET , pr2 is_category_HSET].

Section fix_a_category.

Variable C : precategory.
Variable hsC : has_homsets C.

Local Notation "'Yo'" := (yoneda C hsC).

Local Definition yy {F : preShv C} {c : C} : ((F : functor _ _) c : hSet) ≃ _ ⟦ Yo c, F⟧.
Proof.
  apply invweq.
  apply yoneda_weq.
Defined.

Lemma yy_natural (F : preShv C) (c : C) (A : (F:functor _ _) c : hSet) 
                  c' (f : C⟦c', c⟧) :
        yy (# (F : functor _ _) f A) = # Yo f ;; yy A.
Proof.
  assert (XTT := is_natural_yoneda_iso_inv _ hsC F _ _ f).
  apply (toforallpaths _ _ _ XTT).
Qed.

(** * Type of type structures *)

Definition type_structure : UU :=
  Σ Ty : preShv C,
        ∀ (Γ : C) (A : (Ty : functor _ _ ) Γ : hSet ), Σ (ΓA : C), C⟦ΓA, Γ⟧.

Definition TY (X : type_structure) : preShv _ := pr1 X.

Definition comp_ext {X : type_structure} Γ A : C := pr1 (pr2 X Γ A).
Notation "Γ ◂ A" := (comp_ext Γ A) (at level 30).
Definition π {X : type_structure} {Γ} A : C ⟦Γ ◂ A, Γ⟧ := pr2 (pr2 X _ A).

Lemma idtoiso_π {X : type_structure} (Γ : C) (A A' : (TY X : functor _ _ ) Γ : hSet) (e : A = A')
  :
    idtoiso (maponpaths (λ B, Γ ◂ B) e) ;; π _ = π _ .
Proof.
  induction e.
  apply id_left.
Qed.

(** * Type of families structures over a type structure *)

Section some_structures.

Context {X : type_structure}.

Definition families_data_structure : UU :=
  Σ Tm : preShv C, _ ⟦ Tm, TY X ⟧ × (∀ Γ (A : (TY X : functor _ _ ) Γ : hSet), _ ⟦Yo (Γ ◂ A) , Tm⟧ ).

Definition TM (Y : families_data_structure) : preShv C := pr1 Y.
Definition pp Y : _ ⟦TM Y, TY X⟧ := pr1 (pr2 Y).
Definition Q Y {Γ} A : _ ⟦ _ , TM Y⟧ := pr2 (pr2 Y) Γ A.

Definition families_prop_structure (Y : families_data_structure) :=
  ∀ Γ (A : (TY X : functor _ _ ) Γ : hSet), 
        Σ (e : #Yo (π A) ;; yy A = Q Y A ;; pp Y), isPullback _ _ _ _ e.

Definition families_structure : UU :=
  Σ Y : families_data_structure, families_prop_structure Y.
Coercion families_data_from_families (Y : families_structure) : _ := pr1 Y.


(** * Type of split comprehension structures over a types structure *)

Notation "A [ f ]" := (# (TY X : functor _ _ ) f A) (at level 4).

Definition comprehension_structure : UU :=
  Σ q : ∀ {Γ Γ'} (f : C⟦Γ', Γ⟧) (A : (TY X:functor _ _ ) Γ : hSet), 
           C ⟦Γ' ◂ A [ f ], Γ ◂ A⟧, 
    (∀ Γ Γ' (f : C⟦Γ', Γ⟧) (A : (TY X:functor _ _ ) Γ : hSet), 
        Σ e :  π _ ;; f = q f A ;; π _ , isPullback _ _ _ _ e).

Definition qq (Y : comprehension_structure) {Γ Γ'} (f : C ⟦Γ', Γ⟧)
              (A : (TY X:functor _ _ ) Γ : hSet) 
  : C ⟦Γ' ◂ A [ f ], Γ ◂ A⟧
  := pr1 Y _ _ f A.

Definition idtoiso_qq (Y : comprehension_structure) {Γ Γ'} (f f' : C ⟦Γ', Γ⟧)
              (e : f = f')
              (A : (TY X:functor _ _ ) Γ : hSet) 
  : idtoiso (maponpaths (comp_ext Γ') (maponpaths (λ k : C⟦Γ', Γ⟧, #(TY X : functor _ _ ) k A) e))
                ;; qq Y f' A = qq Y f A.
Proof.
  induction e.
  apply id_left.
Qed.

Definition pullback_from_comp (Y : comprehension_structure) 
  {Γ Γ'} (f : C⟦Γ', Γ⟧) (A : (TY X:functor _ _ ) Γ : hSet) : 
        Σ e : π _ ;; f = qq Y f A ;; π _ , isPullback _ _ _ _ e
:= pr2 Y _ _ f A.

Definition is_split_comprehension_structure (Y : comprehension_structure) : UU
  := 
    (∀ Γ A, qq Y (identity Γ) A = idtoiso (maponpaths (fun B => Γ ◂ B) 
                                                      (toforallpaths _ _ _ (functor_id (TY X) _ ) _ )) )
 ×
   (∀ Γ Γ' Γ'' (f : C⟦Γ', Γ⟧) (g : C ⟦Γ'', Γ'⟧) (A : (TY X:functor _ _ ) Γ : hSet),
       qq Y (g ;; f) A = idtoiso (maponpaths (fun B => Γ'' ◂ B)
                                             (toforallpaths _ _ _ (functor_comp (TY X) _ _ _  f g) A))
                          ;; qq Y g (A [f]) 
                          ;; qq Y f A).

Definition compatible_scomp_families (Y : families_structure)(Z : comprehension_structure) : UU
  := ∀ Γ Γ' A (f : C⟦Γ', Γ⟧) , Q Y A[f] = #(yoneda _ hsC) (qq Z f A) ;; Q Y A.

Definition compatible_fam_structure (Z : comprehension_structure) : UU
  := Σ Y : families_structure, compatible_scomp_families Y Z.

Definition compatible_comp_structure (Y : families_structure) : UU
  := Σ Z : comprehension_structure, compatible_scomp_families Y Z.



Section compatible_comp_structure_from_fam.

Variable Y : families_structure.

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
        apply pathsinv0, yy_natural).
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

(** missing: splitness *)

End qq_from_fam.
      
End compatible_comp_structure_from_fam.




Section compatible_fam_structure_from_comp.

Variable Z : comprehension_structure.
Variable ZZ : is_split_comprehension_structure Z.

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

Lemma is_functor_tm : is_functor tm_functor_data.
Proof.
  split; [unfold functor_idax | unfold functor_compax].
  - intro Γ. apply funextsec.
    intro t. simpl. 
    destruct t as [A [s e]].
    cbn. simpl.
    unfold tm_on_mor.  simpl.
    use total2_paths.
    + simpl. use (toforallpaths _ _ _ (functor_id (TY X) _ ) A).
    + simpl.
      apply subtypeEquality.
      * intro. apply hsC.
      * simpl.
        eapply pathscomp0. apply (pr1_transportf ((TY X : functor _ _ )  Γ : hSet) (fun x => C⟦Γ,Γ◂ x⟧)
                      (fun A => fun b => b ;; π _ = identity _ )                 ).
        simpl.
        Search transportf maponpaths.
        rewrite functtransportf.
        rewrite <- idtoiso_postcompose.
        assert (XT := pr1 Z).
        rewrite <- (pr1 ZZ).        
        match goal with |[|- PullbackArrow ?HH _ _ _ _ ;; _ = _ ] => set (XR := HH) end.
        etrans. apply (PullbackArrow_PullbackPr2 XR). apply id_left.
  - intros Γ Γ' Γ'' f g. cbn.
    apply funextsec.
    intro t.
    destruct t as [A [s e]]; simpl in *.
    unfold tm_on_mor. simpl.
    use total2_paths.
    + simpl. apply (toforallpaths _ _ _ (functor_comp (TY X) _ _ _ _ _) A).
    + simpl. apply subtypeEquality.
      * intro. apply hsC.
      * simpl.
        eapply pathscomp0.
        apply (pr1_transportf ((TY X : functor _ _ )  Γ'' : hSet) (fun x => C⟦Γ'',Γ''◂ x⟧)
                      (fun A => fun b => b ;; π _ = identity _ )                 ).
        rewrite functtransportf.
        rewrite <- idtoiso_postcompose.
        simpl.
        cbn.
        {
        apply PullbackArrowUnique.
        - rewrite <- assoc. cbn.  
          rewrite idtoiso_π.
          match goal with |[|- PullbackArrow ?HH _ _ _ _ ;; _ = _ ] => set (XR := HH) end.
          apply (PullbackArrow_PullbackPr1 XR).
        - cbn. simpl.
          (* match goal with |[|- _ = ?eee] => set (EE:= eee) end. *)
          use (MorphismsIntoPullbackEqual (pr2 (pr2 Z _ _ _ _ ))).
          + simpl. 
            rewrite <- assoc.
            rewrite <- assoc.
            rewrite <- assoc.
            match goal with [|- _ = _ ;; (PullbackArrow ?HH _ _ _ _ ;; _ )] =>
                            set (XR := HH) end.
            rewrite (PullbackArrow_PullbackPr1 XR). clear XR.
            assert (XT:= pr2 Z _ _ g (# (TY X : functor _ _ ) f A)). simpl in XT.
            etrans. apply maponpaths.
                    apply maponpaths. apply (! (pr1 XT)).
            clear XT.
            repeat rewrite assoc.
            rewrite assoc4.
            rewrite idtoiso_π.
            match goal with |[|- PullbackArrow ?HH _ _ _ _ ;; _ ;; _ = _ ] => set (XR := HH) end.
            rewrite (PullbackArrow_PullbackPr1 XR). clear XR.
            rewrite id_right. apply id_left.
          + repeat rewrite <- assoc.
            etrans.  apply maponpaths. rewrite assoc. eapply pathsinv0. apply (pr2 ZZ).
            match goal with |[|- PullbackArrow ?HH _ _ _ _ ;; _ = _ ] => set (XR := HH) end.
            rewrite (PullbackArrow_PullbackPr2 XR). clear XR.
            repeat rewrite <- assoc. apply maponpaths.
            apply pathsinv0. 
            match goal with |[|- PullbackArrow ?HH _ _ _ _ ;; _ = _ ] => set (XR := HH) end.
            apply (PullbackArrow_PullbackPr2 XR).
        } 
Qed.

Definition tm_functor : functor _ _  := tpair _ _ is_functor_tm.

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

Section Q_from_comp.

Variable Γ : C.
Variable A : (TY X : functor _ _ ) Γ : hSet.

Definition Q_from_comp_data :
 ∀ x : C^op, HSET ⟦ (Yo (Γ ◂ A) : functor _ _ ) x, tm_functor x ⟧.
Proof.
  intros Γ' f. simpl in *.
  unfold yoneda_objects_ob in f. 
  mkpair.
  + simpl. apply A[f;;π _ ].
  + use (section_from_diagonal _ (pr2 (pullback_from_comp Z _  _ ))). 
    exists f. apply idpath.
Defined.

Lemma is_nat_trans_Q_from_comp : is_nat_trans _ _ Q_from_comp_data.
Proof.
intros Γ' Γ'' f. simpl.
    apply funextsec. intro g.
    unfold yoneda_objects_ob. cbn.    
    use total2_paths. 
    + simpl.
      etrans. apply (maponpaths (fun k => #(TY X : functor _ _ ) k A) (assoc _ _ _ _ _ _ _ _ )).
      apply (toforallpaths _ _ _ (functor_comp (TY X) _ _ _ _ _ )).
    + simpl.
      apply subtypeEquality.
      { intro. apply hsC. }     
      rewrite (pr1_transportf _ (fun a => C⟦Γ'', Γ'' ◂ a⟧)
                              (fun A => fun b => b ;; π _ = identity _ )).
      simpl.
      rewrite functtransportf.
      rewrite <- idtoiso_postcompose.
      simpl.
      apply PullbackArrowUnique.
      * cbn.
        etrans. apply (!assoc _ _ _ _ _ _ _ _ ).
        rewrite idtoiso_π.
        match goal with |[|- PullbackArrow ?HH _ _ _ _ ;; _ = _ ] => set (XR := HH) end.
        apply (PullbackArrow_PullbackPr1 XR).
      * cbn.
        {
          use (MorphismsIntoPullbackEqual (pr2 (pr2 Z _ _ _ _ ))).
          - etrans. Focus 2. apply assoc.
            match goal with [|- _ = _ ;; (PullbackArrow ?HH _ _ _ _ ;; _ )] =>
                            set (XR := HH) end.
            rewrite (PullbackArrow_PullbackPr1 XR). clear XR.
            etrans. apply (!assoc _ _ _ _ _ _ _ _ ).
            rewrite <- (pr1 (pullback_from_comp Z f _ )).
            etrans. apply assoc.
            etrans. apply assoc4.
            rewrite idtoiso_π.
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
            etrans. apply maponpaths. apply (!assoc _ _ _ _ _ _ _ _ ).
            
            etrans. apply maponpaths. apply maponpaths. apply assoc.
            etrans. apply maponpaths. apply maponpaths. 
                        apply (!XT).
            unfold i. clear i. clear XT.
            rewrite idtoiso_qq.
            unfold d; clear d.
            match goal with [|- PullbackArrow ?HH _ _ _ _ ;; _  = _ ] =>
                            set (XR := HH) end.
            apply (PullbackArrow_PullbackPr2 XR). 
        } 
Qed.

Definition Q_from_comp : _ ⟦ Yo (Γ ◂ A), tm_functor⟧ := tpair _ _ is_nat_trans_Q_from_comp.

Definition Q_from_comp_commutes : # Yo (π _ ) ;; yy A = Q_from_comp ;; pp_from_comp.            
Proof.
  apply nat_trans_eq. apply has_homsets_HSET.
  intro Γ'. apply idpath.
Defined.

Lemma isPullback_Q_from_comp_commutes : isPullback _ _ _ _ Q_from_comp_commutes.
Proof.
  apply pb_if_pointwise_pb.
  intro Γ'. simpl.
  unfold yoneda_morphisms_data. 
  apply mk_isPullback.
  intros S x y Hxy.
  mkpair.
  - mkpair. 
    + simpl in *. unfold yoneda_objects_ob in *.
      intro s.
      set (Ase := y s). unfold tm_carrier in Ase.
      set (HxyH := toforallpaths _ _ _ (!Hxy)); simpl in HxyH. cbn in HxyH.
      set (XX := (pr1 (pr2 Ase))).
      set (YY := maponpaths (fun x => Γ'◂ x) (HxyH s)). simpl in YY.
      set (iYY := idtoiso YY).
      apply (XX ;; iYY ;; qq Z _ _ ).
    + simpl. split.
      * apply funextsec. intro s.
        etrans. apply assoc4.
        set (Hxys := toforallpaths _ _ _ Hxy s). simpl in Hxys. cbn in Hxys.
        cbn in x. unfold yoneda_objects_ob in x. simpl. 
        rewrite <- assoc.
        rewrite <- assoc.
        assert (XR:= pullback_from_comp Z (x s) A).
        etrans. apply maponpaths. apply maponpaths.
        apply (! (pr1 XR)).
        admit.
      * admit.
Abort.

End Q_from_comp.

End compatible_fam_structure_from_comp.




(* needs splitness? *)
Lemma iscontr_compatible_fam_structure (Z : comprehension_structure)
: iscontr (compatible_fam_structure Z).
Proof.
Abort.




Lemma iscontr_compatible_comp_structure (Y : families_structure)
: iscontr (compatible_comp_structure Y).
Proof.
Abort.



End some_structures.


End fix_a_category.
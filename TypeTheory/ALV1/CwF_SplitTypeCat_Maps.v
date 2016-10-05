
(**

 Ahrens, Lumsdaine, Voevodsky, 2015 - 2016

*)

Require Import UniMath.Foundations.Basics.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Defs.


Local Set Automatic Introduction.
(* only needed since imports globally unset it *)

Section Fix_Base_Category.

Context {C : Precategory} {X : obj_ext_structure C}.

Local Notation "Γ ◂ A" := (comp_ext _ Γ A) (at level 30).
Local Notation "'Ty'" := (fun X Γ => (TY X : functor _ _) Γ : hSet) (at level 10).
Local Notation "A [ f ]" := (# (TY X : functor _ _ ) f A) (at level 4).
Local Notation "'Tm'" := (fun Y Γ => (TM Y : functor _ _) Γ : hSet) (at level 10).

Local Notation Δ := comp_ext_compare.

(** * Definition of compatibility

We define here what it means for a families-structure and a _q_-morphism structure to be _compatible_. *)

Section Compatible_Structures.

Definition iscompatible_fam_qq (Y : families_structure C X)
         (Z : qq_morphism_structure X) : UU
  := Π Γ Γ' A (f : C⟦Γ', Γ⟧) , Q Y A[f] = #Yo (qq Z f A) ;; Q Y A.

Lemma isaprop_iscompatible_fam_qq
  (Y : families_structure C X)
  (Z : qq_morphism_structure X)
  : isaprop (iscompatible_fam_qq Y Z).
Proof.
  do 4 (apply impred; intro).
  apply homset_property.
Qed.

Definition compatible_fam_structure (Z : qq_morphism_structure X) : UU
  := Σ Y : families_structure C X, iscompatible_fam_qq Y Z.

Definition compatible_qq_morphism_structure (Y : families_structure C X) : UU
  := Σ Z : qq_morphism_structure X, iscompatible_fam_qq Y Z.

End Compatible_Structures.

(** ** Misc lemmas *)

(* TODO: find more logical home for this below, once file is cleaned up a bit. *)
Lemma map_from_term_recover
    {Y} {Z} (W : iscompatible_fam_qq Y Z)
    {Γ' Γ : C} {A : Ty X Γ} (f : Γ' --> Γ ◂ A)
    {e : (pp Y : nat_trans _ _) Γ' ((Q Y A : nat_trans _ _) Γ' f)
         = A [ f ;; π A ]}
  : pr1 (term_to_section ((Q Y A : nat_trans _ _) Γ' f)) ;; Δ e ;; qq Z (f ;; π A) A
  = f.
Proof.
  unfold iscompatible_fam_qq in W.
  apply (Q_pp_Pb_unique Y).
  - unfold yoneda_morphisms_data; cbn.
    etrans. apply @pathsinv0, assoc.
    etrans. apply maponpaths, @pathsinv0, qq_π.
    etrans. apply @pathsinv0, assoc.
    etrans. apply maponpaths.
      etrans. apply assoc.
      apply cancel_postcomposition, comp_ext_compare_π.
    etrans. apply assoc.
    etrans. Focus 2. apply id_left. apply cancel_postcomposition.
    exact (pr2 (term_to_section _)).
  - etrans. refine (!toforallpaths _ _ _ (nat_trans_eq_pointwise (W _ _ _ _) _) _).
    etrans. apply Q_comp_ext_compare.
    apply term_to_section_recover.
Time Qed.

(** * Defining a (compatible) families structure, given a _q_-morphism structure 

Key definitions: [fam_from_qq], [iscompatible_fam_from_qq] *)

Section compatible_fam_structure_from_qq.

Variable Z : qq_morphism_structure X.
(* TODO: replaces references to [ZZ] by access functions. *)
Notation ZZ := (pr2 Z).

Definition tm_from_qq_carrier (Γ : C) : UU :=
  Σ A : Ty X Γ,
  Σ s : C⟦Γ, Γ ◂ A⟧, s ;; π _ = identity _ .

Lemma isaset_tm_from_qq Γ : isaset (tm_from_qq_carrier Γ).
Proof.
  apply (isofhleveltotal2 2).
  - apply setproperty.
  - intro. apply (isofhleveltotal2 2).
    + apply homset_property.
    + intro. apply isasetaprop. apply homset_property.
Qed.

Definition tm_from_qq_functor_ob Γ : hSet := hSetpair _ (isaset_tm_from_qq Γ).

Definition tm_from_qq_functor_mor Γ Γ' (f : C⟦Γ',Γ⟧) : tm_from_qq_carrier Γ → tm_from_qq_carrier Γ'.
Proof.
  intro Ase.
  exists ((pr1 Ase) [f]).
  eapply pb_of_section.
  - apply (qq_π_Pb Z).
  - apply (pr2 (pr2 Ase)).
Defined.

Definition tm_from_qq_functor_data : functor_data C^op HSET.
Proof.
  exists tm_from_qq_functor_ob.
  refine tm_from_qq_functor_mor.
Defined.

Lemma section_eq_from_tm_from_qq_eq {Γ} (t t' : (tm_from_qq_functor_data Γ : hSet)) 
  (e : t = t')
  : pr1 (pr2 t) ;; Δ (maponpaths pr1 e)
    = pr1 (pr2 t').
Proof.
  destruct e; simpl.
  etrans. apply maponpaths, comp_ext_compare_id_general.
  apply id_right.
Qed.

Lemma tm_from_qq_eq {Γ} (t t' : (tm_from_qq_functor_data Γ : hSet)) 
  (eA : pr1 t = pr1 t')
  (es : (pr1 (pr2 t)) ;; Δ eA = (pr1 (pr2 t')))
  : t = t'.
Proof.
  destruct t as [A [s e]], t' as [A' [s' e']]; simpl in *.
  use total2_paths; simpl.
    apply eA.
  apply subtypeEquality. intro; apply homset_property.
  simpl. eapply pathscomp0. refine (pr1_transportf _ _ _ _ _ eA _).
  simpl. eapply pathscomp0. apply functtransportf.
  eapply pathscomp0. eapply pathsinv0. apply idtoiso_postcompose.
  exact es.
Qed.

(** A useful more specialised case of equality on terms. *)

(* TODO: rephrase in terms of [Δ] instead of [idtoiso]? *)
Lemma tm_from_qq_eq' {Γ : C} (A : Ty X Γ)
  {Γ'} {f f' : Γ' --> Γ} (e_ff' : f = f')
  {s : Γ' --> Γ' ◂ A[f]} (es : s ;; π _ = identity _)
  {s' : Γ' --> Γ' ◂ A[f']} (es' : s' ;; π _ = identity _)
  (e_ss' : s' = s ;; Δ (maponpaths (fun f => A[f]) e_ff'))
: (( A[f] ,, (s,, es)) : tm_from_qq_functor_data Γ' : hSet)
  = (A[f'] ,, (s',, es')).
Proof.
  destruct e_ff'; simpl in *.
  apply maponpaths.
  rewrite id_right in e_ss'.
  destruct e_ss'.
  apply maponpaths. apply homset_property.
Qed.

Lemma is_functor_tm_from_qq : is_functor tm_from_qq_functor_data.
Proof.
  split; [unfold functor_idax | unfold functor_compax].
  - intro Γ; apply funextsec; intro t. destruct t as [A [s e]]; cbn.
    use tm_from_qq_eq; simpl.
    + exact (toforallpaths _ _ _ (functor_id (TY X) _ ) A).
    + etrans. apply maponpaths, @pathsinv0, qq_id.
      etrans. apply (PullbackArrow_PullbackPr2 (mk_Pullback _ _ _ _ _ _ _)). 
      apply id_left.
  - intros Γ Γ' Γ'' f g; apply funextsec; intro t.
    destruct t as [A [s e]]; cbn in *.
    use tm_from_qq_eq; simpl.
    + exact (toforallpaths _ _ _ (functor_comp (TY X) _ _ _ _ _) A).
    + {
      apply PullbackArrowUnique; cbn.
      - rewrite <- assoc.
        rewrite @comp_ext_compare_π.
        apply (PullbackArrow_PullbackPr1 (mk_Pullback _ _ _ _ _ _ _)).
      - apply (MorphismsIntoPullbackEqual (qq_π_Pb Z _ _)).
        + etrans. Focus 2. apply assoc.
          etrans. Focus 2.
            apply maponpaths, @pathsinv0.
            apply (PullbackArrow_PullbackPr1 (mk_Pullback _ _ _ _ _ _ _)).
          etrans. Focus 2. apply @pathsinv0, id_right.
          etrans. apply @pathsinv0, assoc.
          etrans. eapply maponpaths, pathsinv0.
            apply qq_π.
          etrans. apply assoc.
          etrans. Focus 2. apply id_left.
          apply cancel_postcomposition.
          etrans. apply @pathsinv0, assoc.
          rewrite @comp_ext_compare_π.
          apply (PullbackArrow_PullbackPr1 (mk_Pullback _ _ _ _ _ _ _)).
        + repeat rewrite <- assoc.
          etrans. apply maponpaths. rewrite assoc.
            apply @pathsinv0, qq_comp_general.
          etrans. apply (PullbackArrow_PullbackPr2 (mk_Pullback _ _ _ _ _ _ _)).
          etrans. apply @pathsinv0, assoc.
          apply maponpaths.
          apply @pathsinv0.
          apply (PullbackArrow_PullbackPr2 (mk_Pullback _ _ _ _ _ _ _)). }
Time Qed.

Definition tm_from_qq : functor _ _
  := tpair _ _ is_functor_tm_from_qq.

Arguments tm_from_qq : simpl never.

Definition pp_from_qq_data (Γ : C^op)
  : tm_from_qq Γ --> Ty X Γ.
Proof.
  exact pr1.
Defined.

(* TODO: would a [Qed] here affect anything later in file (including timing)? *) 
Lemma is_nat_trans_pp_from_qq
  : is_nat_trans _ _ pp_from_qq_data.
Proof.
  intros Γ Γ' f.
  apply idpath.
Defined.

Definition pp_from_qq : preShv C ⟦tm_from_qq, TY X⟧
  := tpair _ _ is_nat_trans_pp_from_qq.

Arguments pp_from_qq : simpl never.

Section Q_from_qq.

Variable Γ : C.
Variable A : Ty X Γ.

Definition Q_from_qq_data
  : Π Γ', HSET ⟦ (Yo (Γ ◂ A) : functor _ _ ) Γ', tm_from_qq Γ' ⟧.
Proof.
  intros Γ' f. simpl in *.
  unfold yoneda_objects_ob in f.
  unfold tm_from_qq_carrier. mkpair.
  + exact A[f;;π _ ].
  + apply (section_from_diagonal _ (qq_π_Pb Z _ _)). 
    exists f. apply idpath.
Defined.

Lemma is_nat_trans_Q_from_qq : is_nat_trans _ _ Q_from_qq_data.
Proof.
  intros Γ' Γ'' f. simpl.
  apply funextsec. intro g.
  unfold yoneda_objects_ob. cbn.    
  use tm_from_qq_eq; simpl pr1.
  + etrans. apply (maponpaths (fun k => A[k]) (assoc _ _ _)).
    apply (toforallpaths _ _ _ (functor_comp (TY X) _ _ _ _ _ )).
  + apply PullbackArrowUnique.
    * cbn.
      etrans. apply (!assoc _ _ _).
      etrans. apply maponpaths, comp_ext_compare_π.
      match goal with |[|- PullbackArrow ?HH _ _ _ _ ;; _ = _ ] => set (XR := HH) end.
      apply (PullbackArrow_PullbackPr1 XR).
    * cbn.
      {
        use (MorphismsIntoPullbackEqual (qq_π_Pb Z _ _)).
        - etrans. Focus 2. apply assoc.
          match goal with [|- _ = _ ;; (PullbackArrow ?HH _ _ _ _ ;; _ )] =>
                          set (XR := HH) end.
          rewrite (PullbackArrow_PullbackPr1 XR). clear XR.
          etrans. apply (!assoc _ _ _).
          rewrite <- (qq_π Z).
          etrans. apply assoc.
          etrans. apply assoc4.
          rewrite @comp_ext_compare_π.
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
          rewrite @comp_ext_compare_comp.
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
          rewrite (@comp_ext_compare_qq _ X).
          unfold d; clear d.
          match goal with [|- PullbackArrow ?HH _ _ _ _ ;; _  = _ ] =>
                          set (XR := HH) end.
          apply (PullbackArrow_PullbackPr2 XR). 
      } 
Time Qed.

Definition Q_from_qq : Yo (Γ ◂ A) --> tm_from_qq 
  := tpair _ _ is_nat_trans_Q_from_qq.

Arguments Q_from_qq : simpl never.

Definition Q_pp_from_qq
  : # Yo (π _) ;; yy A = Q_from_qq ;; pp_from_qq.
Proof.
  apply nat_trans_eq. apply has_homsets_HSET.
  intro Γ'. apply idpath.
Defined.

Definition section_qq_π  (Γ' : C) (f : C⟦ Γ', Γ⟧) 
    (s : C ⟦ Γ', Γ' ◂ A[f] ⟧)
    (e : s ;; π (A[f]) = identity Γ')
  : s ;; qq Z f A ;; π A = f.
Proof.
  etrans. apply @pathsinv0, assoc.
  etrans. apply @maponpaths, @pathsinv0, qq_π.
  etrans. apply assoc.
  etrans. apply cancel_postcomposition. exact e.
  apply id_left.
Qed.

Lemma Q_from_qq_reconstruction
  {Γ' : C} ( ft : C ⟦ Γ', Γ ◂ A ⟧ )
: ft = pr1 (pr2 (Q_from_qq_data Γ' ft)) ;; qq Z (ft ;; π A) A.
Proof.
  cbn. apply pathsinv0, (PullbackArrow_PullbackPr2 (mk_Pullback _ _ _ _ _ _ _)).
Qed.


Lemma isPullback_Q_pp_from_qq : isPullback _ _ _ _ Q_pp_from_qq.
Proof.
  apply pb_if_pointwise_pb. intros Γ'.
  apply isPullback_HSET. intros f [A' [s e]] e_A_A'; simpl in e_A_A'.
  destruct e_A_A'.
  use tpair.
  - exists (s ;; qq Z f A).
    simpl; unfold yoneda_morphisms_data.
    split.
    + apply (section_qq_π _ _ _ e).
    + use tm_from_qq_eq'; simpl.
      apply (section_qq_π _ _ _ e).
      use (map_into_Pb_unique _ (qq_π_Pb Z _ _  )).
      * etrans. apply e.
        apply pathsinv0.
        etrans. apply @pathsinv0, assoc.
        etrans. apply @maponpaths, comp_ext_compare_π.
        apply (PullbackArrow_PullbackPr1 (mk_Pullback _ _ _ _ _ _ _)).
      * apply pathsinv0. etrans. apply @pathsinv0, assoc.
        etrans. apply @maponpaths, comp_ext_compare_qq.
        apply (PullbackArrow_PullbackPr2 (mk_Pullback _ _ _ _ _ _ _)).
  - intros ft.
    apply subtypeEquality. intro. apply isapropdirprod. apply homset_property. apply setproperty.
    simpl. destruct ft as [ ft [ e1 e2 ] ]; simpl.
    etrans. apply Q_from_qq_reconstruction.
    etrans.
       apply cancel_postcomposition, @pathsinv0.
       exact (section_eq_from_tm_from_qq_eq _ _ (!e2)).
    simpl. etrans. apply @pathsinv0, assoc.
    apply maponpaths.
    etrans. Focus 2. apply (comp_ext_compare_qq _ (!e1)).
    apply cancel_postcomposition, maponpaths, setproperty.
Time Qed.

End Q_from_qq.

Arguments Q_from_qq_data { _ } _ _ _ : simpl never.
Arguments Q_from_qq { _ } _ : simpl never.
Arguments tm_from_qq : simpl never.
Arguments pp_from_qq : simpl never.

Definition fam_from_qq : families_structure C X.
Proof.
  mkpair.
  + exists tm_from_qq.
    exists pp_from_qq.
    intros; apply Q_from_qq.
  + unfold families_structure_axioms; intros.
    exists (Q_pp_from_qq _ _ ).
    apply isPullback_Q_pp_from_qq.
Defined.

Lemma fam_from_qq_pointwise_compatible
    {Γ Γ' : C} (A : Ty X Γ) (f : Γ'--> Γ)
    {Γ'' : C} (g : Γ''--> Γ' ◂ A[f])
  : Q_from_qq_data A[f] Γ'' g
  = Q_from_qq_data A Γ'' (g ;; qq Z f A).
Proof.
  use tm_from_qq_eq.
  + unfold yoneda_morphisms_data; simpl.
    etrans. apply (toforallpaths _ _ _ (!functor_comp (TY X) _ _ _ _ _ ) A).
    eapply (maponpaths (fun k => A[k])).
      etrans. apply @pathsinv0, (@assoc C).
      etrans. apply maponpaths, qq_π.
      apply (@assoc C).
  + simpl.
    apply PullbackArrowUnique.
    * etrans. apply @pathsinv0, assoc.
      etrans. apply maponpaths, comp_ext_compare_π.
      apply (PullbackArrow_PullbackPr1 (mk_Pullback _ _ _ _ _ _ _)). 
    * etrans. apply @pathsinv0, assoc.
      etrans. apply maponpaths.
        rewrite @comp_ext_compare_comp.
        etrans. apply @pathsinv0, assoc. 
        etrans. apply maponpaths, comp_ext_compare_qq.
        etrans. apply maponpaths, qq_comp.
        etrans. apply assoc.
        apply cancel_postcomposition.
        etrans. apply assoc.
        etrans. Focus 2. apply id_left.
        apply cancel_postcomposition.
        etrans. apply @pathsinv0, comp_ext_compare_comp.
        apply comp_ext_compare_id_general.
      etrans. apply assoc.
      apply cancel_postcomposition.
      apply (PullbackArrow_PullbackPr2 (mk_Pullback _ _ _ _ _ _ _)). 
Time Qed.

Definition iscompatible_fam_from_qq
  : iscompatible_fam_qq fam_from_qq Z.
Proof.
  intros Γ Γ' A f; apply nat_trans_eq. 
  - apply has_homsets_HSET.
  - intro; apply funextsec; unfold homot; apply fam_from_qq_pointwise_compatible.
Qed.

Definition compatible_fam_from_qq : compatible_fam_structure Z
  := (fam_from_qq,, iscompatible_fam_from_qq).
    
End compatible_fam_structure_from_qq.

Arguments Q_from_qq_data _ {_} _ _ _ : simpl never.
Arguments Q_from_qq _ {_} _ : simpl never.
Arguments tm_from_qq : simpl never.
Arguments pp_from_qq : simpl never.
Arguments tm_from_qq_functor_mor : simpl never.

(** * Defining a (compatible) _q_-morphism structure, given a families structure *)

Section compatible_comp_structure_from_fam.

Variable Y : families_structure C X.

Section qq_from_fam.

Variables Γ Γ' : C.
Variable f : C⟦Γ', Γ⟧.
Variable A : Ty X Γ.

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
  - apply homset_property.
  - apply (TY X).
  - apply (TM Y).
  - apply (yy A).
  - apply pp.
  - apply Q.
  - apply (pr1 (pr2 Y _ _ )).
  - apply (pr2 (pr2 Y _ _ )).
  - match goal with [|- isPullback _ _ _ _ ?HH ] => generalize HH end.
    rewrite <- (@yy_natural C).
    rewrite Yo_of_qq_commutes_2.
    intro.
    apply (pr2 (pr2 Y _ _ )).
Qed.

Definition qq_fam :  _ ⟦Γ' ◂ A[f] , Γ ◂ A⟧.
Proof.
  apply (invweq (weqpair _ (yoneda_fully_faithful _ (homset_property _) _ _ ))).
  apply Yo_of_qq.
Defined.

Lemma Yo_qq_fam_Yo_of_qq : # Yo qq_fam = Yo_of_qq.
Proof.
  unfold qq_fam.
  assert (XT := homotweqinvweq
     (weqpair _ (yoneda_fully_faithful _ (homset_property _) (Γ'◂ A[f]) (Γ ◂ A)))).
  apply XT.
Qed.

Lemma qq_commutes_1 : π _ ;; f = qq_fam ;; π _ .
Proof.
  assert (XT:= Yo_of_qq_commutes_1).
  rewrite <- Yo_qq_fam_Yo_of_qq in XT.
  do 2 rewrite <- functor_comp in XT.
  apply (invmaponpathsweq (weqpair _ (yoneda_fully_faithful _ (homset_property _) _ _ ))).
  apply XT.
Qed.

Definition isPullback_qq : isPullback _ _ _ _ qq_commutes_1.
Proof.
  use (isPullback_preimage_square _ _ _ Yo).
  - apply homset_property.
  - apply yoneda_fully_faithful.
  - assert (XT:= isPullback_Yo_of_qq).
    match goal with |[|- isPullback _ _ _ _ ?HHH] => generalize HHH end.
    rewrite Yo_qq_fam_Yo_of_qq.
    intro. assumption.
Qed.

End qq_from_fam.

Definition qq_from_fam_data : qq_morphism_data X.
Proof.
  mkpair.
  - intros. apply qq_fam.
  - intros. simpl.
    exists (qq_commutes_1 _ _ _ _ ).
    apply isPullback_qq.
Defined.

Lemma is_split_qq_from_fam : qq_morphism_axioms qq_from_fam_data.
Proof.
  split.
  - intros Γ A. simpl.
    apply (invmaponpathsweq (weqpair _ (yoneda_fully_faithful _ (homset_property _) _ _ ))).
    etrans; [ apply (homotweqinvweq (weqpair _ (yoneda_fully_faithful _ (homset_property _) _ _ ))) | idtac ].    
    apply pathsinv0.
    unfold Yo_of_qq.
    apply PullbackArrowUnique. 
    + etrans. apply maponpaths. cbn. apply idpath. 
      rewrite <- functor_comp.
      etrans. eapply pathsinv0. refine (functor_comp Yo _ _ _ _ _).
      apply maponpaths. rewrite (@comp_ext_compare_π _ X).
      apply pathsinv0. apply id_right.
    + etrans. apply maponpaths. cbn. apply idpath.
      apply comp_ext_compare_Q.
  - intros.
    apply (invmaponpathsweq (weqpair _ (yoneda_fully_faithful _ (homset_property _) _ _ ))).
    etrans; [ apply (homotweqinvweq (weqpair _ (yoneda_fully_faithful _ (homset_property _) _ _ ))) | idtac ].    
    sym. apply PullbackArrowUnique.
    + etrans. apply maponpaths. cbn. apply idpath.
      rewrite <- functor_comp.
      etrans. eapply pathsinv0. refine (functor_comp Yo _ _ _ _ _).
      apply maponpaths.
      rewrite <- assoc. rewrite <- qq_commutes_1 .
      repeat rewrite assoc.
      rewrite assoc4.
      etrans. apply cancel_postcomposition. apply maponpaths. eapply pathsinv0. apply qq_commutes_1 .
      apply cancel_postcomposition.
      repeat rewrite assoc.
      apply cancel_postcomposition.
      apply comp_ext_compare_π.
    + etrans. apply maponpaths. cbn. apply idpath.
      etrans. apply cancel_postcomposition. apply functor_comp.
      rewrite <- assoc.
      rewrite Yo_qq_fam_Yo_of_qq.
      rewrite  Yo_of_qq_commutes_2 .
      etrans. apply cancel_postcomposition. apply functor_comp.
      rewrite <- assoc.
      etrans. apply maponpaths. apply cancel_postcomposition. apply Yo_qq_fam_Yo_of_qq.
      etrans. apply maponpaths. apply Yo_of_qq_commutes_2 .
      apply comp_ext_compare_Q.
Time Qed.

Definition qq_from_fam
  : qq_morphism_structure X.
Proof.
  exists qq_from_fam_data.
  apply is_split_qq_from_fam.
Defined.

Lemma iscompatible_qq_from_fam : iscompatible_fam_qq Y qq_from_fam.
Proof.
  intros Γ Γ' A f.
  assert (XR:= Yo_of_qq_commutes_2).
  apply pathsinv0.
  rewrite Yo_qq_fam_Yo_of_qq.
  apply XR.
Qed.

Definition compatible_qq_from_fam : compatible_qq_morphism_structure Y
  := (qq_from_fam,, iscompatible_qq_from_fam).
    
End compatible_comp_structure_from_fam.

End Fix_Base_Category.

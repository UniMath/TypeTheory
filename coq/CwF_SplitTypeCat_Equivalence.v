
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
Local Notation "a ⇒ b" := (precategory_morphisms a b)(at level 50).

(*
Local Notation "< h , k >" := (PullbackArrow _ _ h k _ ) : pullback_scope.
Open Scope pullback_scope.
*)

Local Definition preShv C := [C^op , HSET , pr2 is_category_HSET].

Section Auxiliary.

(* TODO: move? is there already a provided easy way to apply the [isaset] of something known to be an hset? *)
(* Yes, it is called [setproperty] *)
(*
Definition pr2hSet (a : hSet) : isaset a := pr2 a.
*)

(* TODO: move? does this already exist?

  If we had the standard pullback of hsets defined, this could be maybe better stated as the fact that P is a pullback if the map from P to the standard pullback is an iso. *)
Lemma isPullback_HSET {P A B C : HSET}
  (p1 : P ⇒ A) (p2 : P ⇒ B) (f : A ⇒ C) (g : B ⇒ C) (ep : p1 ;; f = p2 ;; g) 
  : (∀ a b (e : f a = g b), ∃! ab, p1 ab = a × p2 ab = b)
  -> isPullback _ _ _ _ ep.
Proof.
  intros H X h k ehk.
  set (H_existence := fun a b e => pr1 (H a b e)).
  set (H_uniqueness := fun a b e x x' => base_paths _ _ (proofirrelevancecontr (H a b e) x x')).
  apply iscontraprop1.
  - apply invproofirrelevance.
    intros hk hk'.
    apply subtypeEquality. { intro. apply isapropdirprod; apply setproperty. }
    destruct hk as [hk [eh ek]], hk' as [hk' [eh' ek']]; simpl.
    apply funextsec; intro x.
    refine (H_uniqueness (h x) (k x) _ (_,,_) (_,,_)).
    apply (toforallpaths _ _ _ ehk).
    split. apply (toforallpaths _ _ _ eh). apply (toforallpaths _ _ _ ek).
    split. apply (toforallpaths _ _ _ eh'). apply (toforallpaths _ _ _ ek').
  - mkpair. 
    + intros x. refine (pr1 (H_existence (h x) (k x) _)). apply (toforallpaths _ _ _ ehk).
    + simpl.
      split; apply funextsec; intro x.
      apply (pr1 (pr2 (H_existence _ _ _))). apply (pr2 (pr2 (H_existence _ _ _))).
Qed.

End Auxiliary.

Section fix_a_category.

Variable C : precategory.
Variable hsC : has_homsets C.

Local Notation "'Yo'" := (yoneda C hsC).
Local Notation "'Yo^-1'" :=  (invweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ ))).

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

Context (X : type_structure).

(* Notation "A [ f ]" := (# (TY X : functor C^op HSET) f A)(at level 30). *)

Definition families_data_structure : UU :=
  Σ Tm : preShv C, _ ⟦ Tm, TY X ⟧ × (∀ Γ (A : (TY X : functor _ _ ) Γ : hSet), _ ⟦Yo (Γ ◂ A) , Tm⟧ ).

Definition TM (Y : families_data_structure) : preShv C := pr1 Y.
Definition pp Y : _ ⟦TM Y, TY X⟧ := pr1 (pr2 Y).
Definition Q Y {Γ} A : _ ⟦ _ , TM Y⟧ := pr2 (pr2 Y) Γ A.

Lemma idtoiso_Q Y Γ (A A' : (TY X : functor _ _ ) Γ : hSet) (e : A = A') : 
  #Yo (idtoiso (maponpaths (fun B => Γ ◂ B) e )) ;; Q Y A' = Q Y A . 
Proof.
  induction e. 
  etrans. apply cancel_postcomposition. apply functor_id.
  apply id_left.
Defined.

Definition families_prop_structure (Y : families_data_structure) :=
  ∀ Γ (A : (TY X : functor _ _ ) Γ : hSet), 
        Σ (e : #Yo (π A) ;; yy A = Q Y A ;; pp Y), isPullback _ _ _ _ e.

Lemma isaprop_families_prop_structure Y
  : isaprop (families_prop_structure Y).
Proof.
  do 2 (apply impred; intro).
  apply isofhleveltotal2.
  - apply functor_category_has_homsets.
  - intro. apply isaprop_isPullback.
Qed.

Definition families_structure : UU :=
  Σ Y : families_data_structure, families_prop_structure Y.
Coercion families_data_from_families (Y : families_structure) : _ := pr1 Y.

Definition Q_pp (Y : families_structure) Γ (A : (TY X : functor _ _ ) Γ : hSet) 
  : #Yo (π A) ;; yy A = Q Y A ;; pp Y.
Proof.
  apply (pr1 (pr2 Y _ _ )).
Defined.

Definition isPullback_Q_pp (Y : families_structure) Γ (A : (TY X : functor _ _ ) Γ : hSet) 
  : isPullback _ _ _ _ (Q_pp Y _ A ). 
Proof.
  apply (pr2 (pr2 Y _ _ )).
Defined.

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

(* Access function *)
Lemma qq_π (Y : comprehension_structure) {Γ Γ'} (f : Γ' ⇒ Γ) (A : _ ) : π _ ;; f = qq Y f A ;; π A.
Proof.
  exact (pr1 (pr2 Y _ _ f A)).
Qed.

(* Access function *)
Lemma qq_π_Pb (Y : comprehension_structure) {Γ Γ'} (f : Γ' ⇒ Γ) (A : _ ) : isPullback _ _ _ _ (qq_π Y f A).
Proof.
  exact (pr2 (pr2 Y _ _ f A)).
Qed.

Definition idtoiso_qq (Y : comprehension_structure) {Γ Γ'} (f f' : C ⟦Γ', Γ⟧)
              (e : f = f')
              (A : (TY X:functor _ _ ) Γ : hSet) 
  : idtoiso (maponpaths (comp_ext Γ') (maponpaths (λ k : C⟦Γ', Γ⟧, A [k]) e))
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

Lemma isaprop_is_split_comprehension_structure
  (Y : comprehension_structure)
  : isaprop (is_split_comprehension_structure Y).
Proof.
  apply isofhleveldirprod.
  - do 2 (apply impred; intro).
    apply hsC.
  - do 6 (apply impred; intro).
    apply hsC.    
Qed.


(* Since [Ty X] is always an hset, the splitness properties hold with any equality replacing the canonical ones. This is sometimes handy, one may want to opacify the canonical equalities in later proofs. *)
Lemma split_comprehension_structure_comp_general
  {Y : comprehension_structure} (Z : is_split_comprehension_structure Y)
  {Γ Γ' Γ'' : C}
  {f : C ⟦ Γ', Γ ⟧} {g : C ⟦ Γ'', Γ' ⟧} {A : ((TY X : functor _ _) Γ : hSet)}
  (p : A [g ;; f]
       = # (TY X : functor C^op HSET) g (# (TY X : functor C^op HSET) f A)) 
: qq Y (g ;; f) A
  = idtoiso
         (maponpaths (λ B : ((pr1 X : functor _ _) Γ'' : hSet), Γ'' ◂ B)
            p) ;; 
       qq Y g (A [f]) ;; qq Y f A.
Proof.
  eapply pathscomp0. apply (pr2 Z).
  repeat apply (maponpaths (fun h => h ;; _)).
  repeat apply maponpaths. apply uip. exact (pr2 ((TY X : functor _ _) _)).
Qed.


Definition split_comprehension_structure : UU
  := Σ Z : comprehension_structure,
           is_split_comprehension_structure Z.

Definition comprehension_from_split_comprehension :
   split_comprehension_structure -> comprehension_structure := pr1.
Coercion comprehension_from_split_comprehension :
   split_comprehension_structure >-> comprehension_structure.




Definition compatible_scomp_families (Y : families_structure)
         (Z : split_comprehension_structure) : UU
  := ∀ Γ Γ' A (f : C⟦Γ', Γ⟧) , Q Y A[f] = #(yoneda _ hsC) (qq Z f A) ;; Q Y A.





Definition compatible_fam_structure (Z : split_comprehension_structure) : UU
  := Σ Y : families_structure, compatible_scomp_families Y Z.

Definition compatible_split_comprehension_structure (Y : families_structure) : UU
  := Σ Z : split_comprehension_structure, compatible_scomp_families Y Z.









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

Lemma type_eq_from_tm_functor_eq {Γ} {t t' : (tm_functor_data Γ : hSet)}
  : t = t' -> pr1 t = pr1 t'.
Proof.
  apply base_paths.
Qed.

Lemma section_eq_from_tm_functor_eq {Γ} (t t' : (tm_functor_data Γ : hSet)) 
  (e : t = t')
  : pr1 (pr2 t)
      ;; idtoiso (maponpaths (comp_ext Γ) (type_eq_from_tm_functor_eq e))
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
  (es : (pr1 (pr2 t)) ;; idtoiso (maponpaths (comp_ext Γ) eA) = (pr1 (pr2 t')))
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
        rewrite idtoiso_π.
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
          etrans. apply maponpaths, idtoiso_π.
          apply (PullbackArrow_PullbackPr1 (mk_Pullback _ _ _ _ _ _ _)).
        + repeat rewrite <- assoc.
          etrans. apply maponpaths. rewrite assoc.
            apply @pathsinv0, split_comprehension_structure_comp_general, ZZ.
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
  + etrans. apply (maponpaths (fun k => #(TY X : functor _ _ ) k A) (assoc _ _ _ _ _ _ _ _ )).
    apply (toforallpaths _ _ _ (functor_comp (TY X) _ _ _ _ _ )).
  + apply PullbackArrowUnique.
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
                       apply (assoc C _ _ _ _ _ _ _ ).
      etrans. Focus 2. eapply (maponpaths (fun k => #(TY X : functor _ _ ) k A)).
                       apply maponpaths.
                       apply (pr1 (pullback_from_comp Z _ _ )).
      etrans. Focus 2.  eapply (maponpaths (fun k => #(TY X : functor _ _ ) k A)).
                       apply (!assoc C _ _ _ _ _ _ _ ).
      apply (toforallpaths _ _ _ (!functor_comp (TY X) _ _ _ _ _ ) A).
    + simpl.
      apply PullbackArrowUnique.
      * simpl. cbn.
        etrans. apply (!assoc C _ _ _ _ _ _ _ ).
        etrans. apply maponpaths. apply idtoiso_π.
        match goal with [|- PullbackArrow ?HH _ _ _ _ ;; _  = _ ] =>
                            set (XR := HH) end.
        apply (PullbackArrow_PullbackPr1 XR). 
      * simpl. cbn.
        etrans. apply (!assoc C _ _ _ _ _ _ _ ).
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
        etrans. apply maponpaths. apply (!assoc _ _ _ _ _ _ _ _ ).
        etrans. apply maponpaths. apply maponpaths. apply idtoiso_qq.
        etrans. apply maponpaths. apply (!assoc _ _ _ _ _ _ _ _ ).  
        etrans. apply maponpaths. apply maponpaths.
                apply idtoiso_qq.
        etrans. apply maponpaths. apply (!assoc _ _ _ _ _ _ _ _ ).
        etrans. apply maponpaths. apply maponpaths.
                apply idtoiso_qq.
        etrans. apply maponpaths. apply maponpaths. apply (pr2 ZZ).
        
        etrans. apply maponpaths. apply maponpaths. apply (!assoc _ _ _ _ _ _ _ _ ).
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
    + unfold families_prop_structure.
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

Section canonical_TM.

Variable Z : comprehension_structure.
Variable ZZ : is_split_comprehension_structure Z.
Variable Y : compatible_fam_structure (Z,,ZZ).

Lemma is_nat_trans_foo : 
 is_nat_trans (tm_functor Z ZZ) (TM (pr1 Y): functor _ _ )
     (λ (Γ : C^op) (Ase : tm_carrier Γ),
      (yoneda_weq C hsC Γ (TM (pr1 Y)))
        (# Yo (pr1 (pr2 Ase)) ;; Q (pr1 Y) (pr1 Ase))).
Proof.
  intros Γ Γ' f. simpl.
  unfold yoneda_morphisms_data. simpl.
  unfold yoneda_objects_ob.
  apply funextsec. intro Ase. cbn.
  rewrite id_left. rewrite id_left.
  destruct Ase as [A [s e]].
  (* now use naturality of (yoneda_weq) on the right-hand side *)
  assert (XR := nat_trans_ax (natural_trans_yoneda_iso _ hsC (TM (pr1 Y))) _ _ f). 
  assert (XR1 := toforallpaths _ _ _ XR).  simpl in XR1.
  cbn in XR1.
  set (XX := # Yo s ;; Q (pr1 Y) _ ). 
  assert (XR2 := XR1 XX).
  unfold XX in XR2.
  simpl in XR2. cbn in XR2. unfold yoneda_morphisms_data in XR2.
  do 2 rewrite id_left in XR2.
  etrans. Focus 2. apply XR2.
  clear XR2. clear XR1. clear XX. clear XR.
  (* now use compatibility of [Q (Y)] with [qq] *)
  assert (XT :=  nat_trans_eq_pointwise (pr2 Y _ _ A f)).
  simpl in XT. unfold yoneda_morphisms_data in XT. unfold yoneda_objects in XT.
  simpl in XT.
  assert (XT1 := toforallpaths _ _ _ (XT Γ')).
  etrans. apply XT1.
  etrans. cbn. apply idpath.
  apply maponpaths.

  clear XT1 XT.
  
  (* TODO : the stuff below should be a separate lemma *)
    
  simpl. 
  match goal with [|- PullbackArrow ?HH _ _ _ _ ;; _ = _ ] => set (XR := HH) end.
  apply (PullbackArrow_PullbackPr2 XR).
Qed.

Definition foo : preShv C  ⟦tm_functor Z ZZ, TM (pr1 Y)⟧.
Proof.
  mkpair.
  - intro Γ. simpl.
    intro Ase. 
    (* set (XX := # Yo (pr1 (pr2 Ase)) ;; Q (pr1 Y) _ ). *)
    exact (yoneda_weq _ _ _ _ (# Yo (pr1 (pr2 Ase)) ;; Q (pr1 Y) _ )).
       (*  y^-1 ( Yo(s) . Q) *)
  - apply is_nat_trans_foo.
Defined.    


(* TODO : we do not need naturality of [bar] below, we only 
          need to show that it is pointwise inverse to [foo] above 
*)

Definition bar : ∀ Γ, HSET ⟦ (TM (pr1 Y) : functor _ _ ) Γ, tm_functor Z ZZ Γ⟧.
Proof.
  intro Γ. simpl.
  intro s'. set (S' := yy s').
  set (ps := (pp (pr1 Y) : nat_trans _ _ )  _ s').
  assert (XR : S' ;; pp (pr1 Y) = yy ( (pp (pr1 Y) : nat_trans _ _ ) _ s')).
  { 
    abstract (
    apply nat_trans_eq; [ apply has_homsets_HSET | ];
    intro Γ' ;
    apply funextsec;
    intro g; simpl; cbn;
    assert (XR := nat_trans_ax (pp (pr1 Y)) _ _ g);
    apply (toforallpaths _ _ _ XR)
     ) .
  } 
    exists ps.
    set (Pb := pr2 (pr1 Y) Γ ps). 
    set (T:= section_from_diagonal (pr1 Pb) (pr2 Pb) (S',,XR) ).
    mkpair.
    + apply Yo^-1.
      exact (pr1 T).
    + abstract
      (
      apply (invmaponpathsweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ )));
      etrans ; [ apply functor_comp |];
      etrans ; [ apply cancel_postcomposition ;
         apply(homotweqinvweq (weqpair _ (yoneda_fully_faithful _ hsC Γ (Γ◂ps) ))) | ];
      simpl;
      match goal with |[ |- PullbackArrow ?HH _ _ _ _ ;; _ = _ ] => 
                       set (XR3:=HH) end;
      rewrite (PullbackArrow_PullbackPr1 XR3);
      apply pathsinv0; apply (functor_id Yo)
       ).
Defined.


Lemma bar_foo Γ : bar Γ ;; (foo  : nat_trans _ _ ) Γ = identity _ .
Proof.
  apply funextsec.
  intro s. simpl.
  unfold yoneda_morphisms_data.
  simpl.
  cbn. rewrite id_left.
  unfold yoneda_map_1.
  cbn. simpl.  
  match goal with |[|- _ ( ((_ (_ ?HH _ _ _ _ ) )) _  _ )  = _ ] => set (XR:= HH) end.
  assert (XR1 := PullbackArrow_PullbackPr2 XR).
  match goal with |[|- _ ( ((_ (_ ?HH ?E ?H ?K _ ) )) _  _ )  = _ ] => specialize (XR1 E H K)  end.
  match goal with |[|- _ ( ((_ (_ _ _ _ _ ?HH ) )) _  _ )  = _ ] => specialize (XR1 HH)  end.
  assert (XR2 := nat_trans_eq_pointwise XR1).
  simpl in XR2. 
  assert (XR3 := toforallpaths _ _ _ (XR2 Γ)).
  simpl in XR3.
  etrans. apply XR3.
  apply (toforallpaths _ _ _ (functor_id (TM (pr1 Y)) _ )).
Qed.

  
Lemma foo_bar Γ : (foo : nat_trans _ _ )  Γ ;; bar Γ = identity _ .
Proof.
  apply funextsec; intro Ase.
  destruct Ase as [A [s e]]. 
  use tm_functor_eq.
  -
    simpl. 
    cbn. unfold yoneda_morphisms_data.  
    etrans. apply maponpaths. apply maponpaths. apply id_left.
    assert (XR := ! Q_pp (pr1 Y) _ A).
    assert (XR1 := nat_trans_eq_pointwise XR Γ).
    assert (XR2 := toforallpaths _ _ _ XR1 s).
    simpl in XR2.
    unfold yoneda_morphisms_data in XR2. cbn in XR2.
    etrans. apply XR2.
    etrans. apply (maponpaths (fun k => # (TY X : functor _ _ ) k A) e).
    apply (toforallpaths _ _ _ (functor_id (TY X)  _ ) A).
  - (*
    rewrite maponpathscomp0.
    rewrite maponpathscomp0.
    rewrite maponpathscomp0.
    rewrite idtoiso_concat.
    rewrite idtoiso_concat.    
    rewrite idtoiso_concat.
    *)
    
    etrans. apply maponpaths. simpl. apply idpath.
    etrans. Focus 2. simpl. apply idpath.
    apply (invmaponpathsweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ ))).
    etrans. apply (functor_comp Yo).
    etrans. apply cancel_postcomposition.
            apply (homotweqinvweq
               (weqpair _ (yoneda_fully_faithful _  hsC _ _   ))).
    etrans. apply cancel_postcomposition. cbn. apply idpath. 
    match goal with |[|- PullbackArrow ?HH _ _ _ ?PP ;; _ = _ ] =>
            set (XR:= HH); generalize PP end.
    intro ee.
    use (MorphismsIntoPullbackEqual (isPullback_Q_pp (pr1 Y) _ _ )).
    + etrans. apply (!assoc _ _ _ _ _ _ _ _ ).
      etrans. apply maponpaths. apply (!functor_comp _ _ _ _ _ _ ).
      etrans. apply maponpaths. apply maponpaths.
              apply idtoiso_π.
      etrans. apply (PullbackArrow_PullbackPr1 XR).
      etrans. Focus 2. apply functor_comp.
      etrans. Focus 2. apply maponpaths. apply (!e).
      apply pathsinv0. apply (functor_id Yo).
    + etrans. apply (!assoc _ _ _ _ _ _ _ _ ).
      etrans. apply maponpaths.
              apply idtoiso_Q.
      etrans. apply (PullbackArrow_PullbackPr2 XR).
      simpl.
      Check yoneda_map_2.
      clear XR. clear ee.
      unfold yoneda_morphisms. unfold yoneda_morphisms_data.
      apply nat_trans_eq. apply (has_homsets_HSET).
      intro Γ'.
      apply funextsec.
      simpl. intro s'.
      cbn. simpl.
      rewrite id_left.
      assert (XR := nat_trans_ax (Q (pr1 Y) A) _ _ s').
      assert (XR1 := toforallpaths _ _ _ XR).
      apply pathsinv0. simpl in XR1. apply XR1.
Qed.

Lemma foo_pointwise_iso Γ : is_iso ((foo : nat_trans _ _) Γ).
Proof.
  apply (is_iso_qinv _ (bar Γ) ).
  split.
  - apply foo_bar.
  - apply bar_foo.
Defined.

Definition foo_iso :  iso (C:=preShv C) (tm_functor Z ZZ) (TM (pr1 Y)).
Proof.
  exists foo.
  apply functor_iso_if_pointwise_iso.
  apply foo_pointwise_iso.
Defined.

End canonical_TM.

Lemma unique (Z : comprehension_structure)
             (ZZ : is_split_comprehension_structure Z)
             (Y : compatible_fam_structure (Z,,ZZ))
  : comp_fam_structure_from_comp Z ZZ = Y.
Proof.
  set (i := isotoid _
                   (is_category_functor_category _ _ is_category_HSET)
                   (foo_iso _  ZZ Y)).
  apply subtypeEquality.
  { intro. do 4 (apply impred; intro).
    apply functor_category_has_homsets.
  }
  destruct Y as [Y YH]. simpl.
  apply subtypeEquality.
  { intro. apply isaprop_families_prop_structure. }
  simpl.
  destruct Y as [Y YH']. simpl.
  use total2_paths.
  - simpl.
    apply i.
  - rewrite transportf_dirprod.
    destruct Y as [Tm [p Q]].
    simpl.
    apply dirprodeq.
    + simpl.
      etrans. eapply pathsinv0.
      apply  (idtoiso_precompose (preShv C)).
      unfold i.
 
      Search (idtoiso (! _ ) = _).

      rewrite idtoiso_inv.
      rewrite idtoiso_isotoid.
      simpl.
      apply nat_trans_eq. apply has_homsets_HSET.
      intro Γ. apply idpath.
    + cbn. simpl.
(*
      apply funextsec. intro c.
*)

Lemma idtoiso_transportf_wtf (D : precategory)
      (A : UU) (B : A -> UU)
      (F : ∀ a, B a -> D)
      (d d' : D) (deq : d = d')
      (R : ∀ a (b : B a), D⟦ F a b, d⟧)
     
: transportf (λ x, ∀ a b, D⟦ F a b, x⟧)
             deq R =
  λ a b, R a b ;; idtoiso deq.
Proof.
  destruct deq.
  apply funextsec.
  intro. apply funextsec. intro.
  apply pathsinv0.
  apply id_right.
Qed.


  idtac.
  assert (XR := 
          (idtoiso_transportf_wtf (preShv C))).
  specialize (XR C (λ B, (TY X : functor _ _ ) B : hSet)).
  specialize (XR (λ Γ' B, (yoneda C hsC (Γ' ◂ B)))).
  etrans. apply XR.
  apply funextsec. intro Γ.
  apply funextsec. intro A.
  clear XR.
  unfold i. rewrite idtoiso_isotoid.
  simpl.
  apply nat_trans_eq. { apply has_homsets_HSET. }
  intro Γ'. simpl. cbn.
  apply funextsec.
  unfold yoneda_objects_ob.
  intro s.
  unfold yoneda_morphisms_data.
  rewrite id_left.

  cbn.
  
  simpl. clear i.
  specialize (YH Γ Γ' A (s ;; π _ )). simpl in YH.
  assert (XR := nat_trans_eq_pointwise YH Γ').
  assert (XR2 := toforallpaths _ _ _ XR).
  simpl in XR2. cbn in XR2.
  etrans. apply XR2.
  apply maponpaths.
  unfold yoneda_morphisms_data.
  match goal with |[|- PullbackArrow ?HH _ _ _ _ ;; _ = _ ] =>
            apply (PullbackArrow_PullbackPr2 HH) end.
Defined.



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

Definition comp_from_fam : comprehension_structure.
Proof.
  mkpair.
  - intros. apply qq_fam.
  - intros. simpl.
    exists (qq_commutes_1 _ _ _ _ ).
    apply isPullback_qq.
Defined.


Lemma is_split_comp_from_fam : is_split_comprehension_structure comp_from_fam.
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
      apply maponpaths. rewrite idtoiso_π.
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
  : split_comprehension_structure.
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




(* needs splitness? *)
Lemma iscontr_compatible_fam_structure (Z : comprehension_structure) (ZZ : is_split_comprehension_structure Z)
: iscontr (compatible_fam_structure (Z,,ZZ)).
Proof.
  exists (comp_fam_structure_from_comp Z ZZ).
  intro t.
  apply pathsinv0. apply unique.
Defined.

Lemma compat_split_comp_eq Y:
∀ t : compatible_split_comprehension_structure Y,
   t =
   (comp_from_fam Y,,
   is_split_comp_from_fam Y),, comp_from_fam_compatible_scomp_families Y.
Proof.
  intro t.
    apply subtypeEquality.
    { 
      intro.
(*      apply isofhleveldirprod. *)
      (*- apply isaprop_is_split_comprehension_structure.*)
      - do 4 (apply impred; intro).
        apply functor_category_has_homsets. 
    }
    simpl.
    apply subtypeEquality.
    { 
      intro.
      apply isaprop_is_split_comprehension_structure.
    }
    apply subtypeEquality.
    {
      intro.
      do 4 (apply impred; intro).
      apply isofhleveltotal2. 
      - apply hsC.
      - intro. apply isaprop_isPullback.
    } 
    simpl.
    destruct t as [[t H1] H2]. simpl.
    destruct t as [q h]; simpl.
    apply funextsec. intro Γ.
    apply funextsec; intro Γ'.
    apply funextsec; intro f.
    apply funextsec; intro A.
    
    apply (invmaponpathsweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ ))).
    apply pathsinv0.
    etrans. apply Yo_qq_fam_Yo_of_qq.
    unfold Yo_of_qq.
    apply pathsinv0.
    apply PullbackArrowUnique.
    + etrans. apply maponpaths. cbn. apply idpath.
      rewrite <- functor_comp.
      etrans. eapply pathsinv0. apply (functor_comp Yo).
      apply maponpaths.
      apply pathsinv0. apply (pr1 (h _ _ _ _ )).
    + etrans. apply maponpaths. cbn. apply idpath.
      apply pathsinv0.
      apply H2.
Qed.
  

Lemma iscontr_compatible_split_comp_structure (Y : families_structure)
: iscontr (compatible_split_comprehension_structure Y).
Proof.
  mkpair.
  - mkpair.
    + exists (comp_from_fam Y).
      apply is_split_comp_from_fam.
    + apply comp_from_fam_compatible_scomp_families.
  - intro. apply compat_split_comp_eq.
Defined.

End some_structures.

Print Assumptions iscontr_compatible_split_comp_structure.
Print Assumptions iscontr_compatible_fam_structure.


Section equivalence.

Variable X : type_structure.

Definition T1 : UU :=
  Σ Y : families_structure X,
        compatible_split_comprehension_structure _ Y.

Definition T2 : UU :=
  Σ Z : split_comprehension_structure X,
        compatible_fam_structure _ Z.

Definition shuffle : T1 ≃ T2.
Proof.
  eapply weqcomp.
  unfold T1.
  unfold compatible_split_comprehension_structure.
  set (XR := @weqtotal2asstol).
  specialize (XR (families_structure X)).
  specialize (XR (fun _ => split_comprehension_structure X)).
  simpl in XR.
  specialize (XR (fun YZ => compatible_scomp_families _ (pr1 YZ) (pr2 YZ))).
  apply XR.
  eapply weqcomp. Focus 2.
  unfold T2. unfold compatible_fam_structure.
  set (XR := @weqtotal2asstor).
  specialize (XR (split_comprehension_structure X)).
  specialize (XR (fun _ => families_structure X)).
  simpl in XR.
  specialize (XR (fun YZ => compatible_scomp_families _ (pr2 YZ) (pr1 YZ))).
  apply XR.
  use weqbandf.
  - apply weqdirprodcomm.
  - intros. simpl.
    apply idweq.
Defined.

Definition forget_fam :
  T2 ≃ split_comprehension_structure X.
Proof.
  exists pr1.
  apply isweqpr1.
  intros [z zz].
  apply iscontr_compatible_fam_structure.
Defined.

Definition forget_comp :
  T1 ≃ families_structure X.
Proof.
  exists pr1.
  apply isweqpr1.
  intro.
  apply iscontr_compatible_split_comp_structure.
Defined.

Definition result : families_structure X ≃ split_comprehension_structure X.
Proof.
  eapply weqcomp.
  eapply invweq.
  apply forget_comp.
  eapply weqcomp.
  apply shuffle.
  apply forget_fam.
Defined.

Print Assumptions result.

End equivalence.

End fix_a_category.



(**
  [TypeTheory.CwF_TypeCat.CwF_SplitTypeCat_Maps]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).

  Main contents:

  - definition of _compatibility_ between term-structures and _q_-morphism structures [iscompatible_term_qq]
  - construction, from any term-structure, of a compatible _q_-morphism structure [compatible_qq_from_term]
  - construction, from any _q_-morphism structure, of a compatible term-structure [compatible_term_from_qq]
*)


Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheory.
Require Import TypeTheory.Auxiliary.Pullbacks.
Require Import TypeTheory.Auxiliary.SetsAndPresheaves.

Require Import TypeTheory.CwF_TypeCat.CwF_SplitTypeCat_Defs.

Section Fix_Base_Category.

Context {C : category} {X : obj_ext_structure C}.

Local Notation "Γ ◂ A" := (comp_ext _ Γ A) (at level 30).
Local Notation "'Ty'" := (fun X Γ => TY X $p Γ) (at level 10).
Local Notation "A [ f ]" := (#p (TY X) f A) (at level 4).
Local Notation "'Tm'" := (fun Y Γ => TM Y $p Γ) (at level 10).

Local Notation Δ := comp_ext_compare.

(** * Compatibility between term-structures and q-morphism structures

We define _compatibility_ between a term-structure and a _q_-morphism structure, as a commutativity condition between the _q_-morphisms and the maps _Q_ of the term-structure.  *)

Section Compatible_Structures.

(** ** Definitions *)

Definition iscompatible_term_qq
    (Y : term_fun_structure C X)
    (Z : qq_morphism_structure X)
  : UU
:= ∏ Γ Γ' A (f : C⟦Γ', Γ⟧),
     te Y A[f] = #p (TM _) (qq Z f A) (te Y A).

Lemma isaprop_iscompatible_term_qq
  (Y : term_fun_structure C X)
  (Z : qq_morphism_structure X)
  : isaprop (iscompatible_term_qq Y Z).
Proof.
  do 4 (apply impred; intro).
  apply setproperty.
Qed.

Definition compatible_term_structure (Z : qq_morphism_structure X)
  : UU
:= ∑ Y : term_fun_structure _ X, iscompatible_term_qq Y Z.

Coercion term_structure_of_compatible {Z : qq_morphism_structure X}
  : compatible_term_structure Z -> term_fun_structure _ X
:= pr1.

Definition compatible_qq_morphism_structure (Y : term_fun_structure _ X)
  : UU
:= ∑ Z : qq_morphism_structure X, iscompatible_term_qq Y Z.

Coercion qq_morphism_structure_of_compatible {Y : term_fun_structure _ X}
  : compatible_qq_morphism_structure Y -> qq_morphism_structure X
:= pr1.

Definition iscompatible'_term_qq
    (Y : term_fun_structure C X)
    (Z : qq_morphism_structure X)
  : UU
:= ∏ Γ Γ' A (f : C⟦Γ', Γ⟧) , Q Y A[f] = #Yo (qq Z f A) ;; Q Y A.

(** ** Misc lemmas on compatibility *)

(* TODO: try to eliminate older [iscompatible'] entirely, and remove both it and this lemma.  *)
Definition iscompatible_iscompatible'
    (Y : term_fun_structure C X)
    (Z : qq_morphism_structure X)
  : iscompatible_term_qq Y Z
  <-> iscompatible'_term_qq Y Z.
Proof.
  unfold iscompatible_term_qq, iscompatible'_term_qq.
  split; intros H Γ Γ' A f; specialize (H Γ Γ' A f).
  - apply nat_trans_eq. { apply homset_property. }
    intros Γ''. cbn. unfold yoneda_objects_ob, yoneda_morphisms_data.
    apply funextsec; intros g.
    etrans. apply maponpaths, H.
    apply pathsinv0, functor_comp_pshf.
  - assert (H' := nat_trans_eq_pointwise H); clear H.
    assert (H'' := toforallpaths (H' _) (identity _)); clear H'.
    cbn in H''; unfold yoneda_morphisms_data in H''.
    refine (_ @ H'' @ _).
    + apply pathsinv0, functor_id_pshf.
    + apply maponpaths_2, id_left.
Qed.

End Compatible_Structures.

(* TODO: find more natural home for this *)
Lemma map_from_term_recover
    {Y} {Z} (W : iscompatible_term_qq Y Z)
    {Γ' Γ : C} {A : Ty X Γ} (f : Γ' --> Γ ◂ A)
    {e : (pp Y) $nt (Q Y A $nt f)
         = A [ f ;; π A ]}
  : pr1 (term_to_section (Q Y A $nt f))
      ;; Δ e ;; qq Z (f ;; π A) A
    = f.
Proof.
  assert (W' : iscompatible'_term_qq Y Z).
    apply iscompatible_iscompatible'; assumption.
  unfold iscompatible'_term_qq in W'.
  apply (Q_pp_Pb_unique Y).
  - unfold yoneda_morphisms_data; cbn.
    etrans. apply @pathsinv0, assoc.
    etrans. apply maponpaths, qq_π.
    etrans. apply @pathsinv0, assoc.
    etrans. apply maponpaths.
      etrans. apply assoc.
      apply maponpaths_2, comp_ext_compare_π.
    etrans. apply assoc.
    etrans. 2: { apply id_left. }
    apply maponpaths_2.
    exact (pr2 (term_to_section _)).
  - etrans. refine (!toforallpaths (nat_trans_eq_pointwise (W' _ _ _ _) _) _).
    etrans. apply Q_comp_ext_compare.
    apply term_to_section_recover.
Qed.

(** * Term-structures from _q_-morphism structures

Given a _q_-morphism structure, we construct from it a (compatible) term structure: its terms are just the _sections_ of the projection maps, and its _Q_-maps are constructed from the _q_-morphisms.

Key definitions: [term_from_qq], [iscompatible_term_from_qq] *)

Section compatible_term_structure_from_qq.

Variable Z : qq_morphism_structure X.

(** ** Definition of the presheaf of terms *)

(* TODO: abstract second half out as “sections”, with pr1 an access function + a coercion. *)
Definition tm_from_qq_carrier (Γ : C) : UU :=
  ∑ A : Ty X Γ,
  ∑ s : C⟦Γ, Γ ◂ A⟧, s ;; π _ = identity _ .

Lemma isaset_tm_from_qq Γ : isaset (tm_from_qq_carrier Γ).
Proof.
  apply (isofhleveltotal2 2).
  - apply setproperty.
  - intro. apply (isofhleveltotal2 2).
    + apply homset_property.
    + intro. apply isasetaprop. apply homset_property.
Qed.

Definition tm_from_qq_functor_ob Γ : hSet := make_hSet _ (isaset_tm_from_qq Γ).

Definition tm_from_qq_functor_mor Γ Γ' (f : C⟦Γ',Γ⟧)
  : tm_from_qq_carrier Γ → tm_from_qq_carrier Γ'.
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
  exact tm_from_qq_functor_mor.
Defined.

Lemma section_eq_from_tm_from_qq_eq {Γ}
  {t t' : (tm_from_qq_functor_data Γ : hSet)}
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
  use total2_paths_f; simpl.
    apply eA.
  apply subtypePath. intro; apply homset_property.
  simpl. eapply pathscomp0. use (pr1_transportf (Ty X Γ)).
  simpl. eapply pathscomp0. apply functtransportf.
  eapply pathscomp0. eapply pathsinv0. apply idtoiso_postcompose.
  exact es.
Qed.

(* A useful more specialised case of equality on terms. *)

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
    + apply functor_id_pshf.
    + etrans. apply maponpaths, @pathsinv0, qq_id.
      etrans. apply (PullbackArrow_PullbackPr2 (make_Pullback _ _)). 
      apply id_left.
  - intros Γ Γ' Γ'' f g; apply funextsec; intro t.
    destruct t as [A [s e]]; cbn in *.
    use tm_from_qq_eq; simpl.
    + apply functor_comp_pshf.
    + {
      apply PullbackArrowUnique; cbn.
      - rewrite <- assoc.
        etrans. { apply maponpaths, comp_ext_compare_π. }
        apply (PullbackArrow_PullbackPr1 (make_Pullback _ _)).
      - apply (MorphismsIntoPullbackEqual (qq_π_Pb Z _ _)).
        + etrans. 2: { apply assoc. }
          etrans.
          2: {
            apply maponpaths, @pathsinv0.
            apply (PullbackArrow_PullbackPr1 (make_Pullback _ _)).
          }
          etrans. 2: { apply @pathsinv0, id_right. }
          etrans. apply @pathsinv0, assoc.
          etrans. eapply maponpaths, qq_π.
          etrans. apply assoc.
          etrans. 2: { apply id_left. }
          apply maponpaths_2.
          etrans. apply @pathsinv0, assoc.
          etrans. { apply maponpaths, comp_ext_compare_π. }
          apply (PullbackArrow_PullbackPr1 (make_Pullback _ _)).
        + repeat rewrite <- assoc.
          etrans. apply maponpaths. rewrite assoc.
            apply @pathsinv0, qq_comp_general.
          etrans. apply (PullbackArrow_PullbackPr2 (make_Pullback _ _)).
          etrans. apply @pathsinv0, assoc.
          apply maponpaths.
          apply @pathsinv0.
          apply (PullbackArrow_PullbackPr2 (make_Pullback _ _)). }
Qed.

Definition tm_from_qq : functor _ _
  := tpair _ _ is_functor_tm_from_qq.

Arguments tm_from_qq : simpl never.

(* TODO: search for uses of [tm_from_qq_eq] to see where this can be used (should save a good few lines of code). *)
Lemma tm_from_qq_eq_reindex
    {Γ Γ' : C} (f : Γ' --> Γ)
    (Ase : tm_from_qq Γ : hSet) (Ase' : tm_from_qq Γ' : hSet)
    (eA : pr1 Ase' = #p (TY X) f (pr1 Ase))
    (es : pr1 (pr2 Ase') ;; Δ eA ;; qq Z f _ = f ;; pr1 (pr2 Ase))
  : Ase' = # tm_from_qq f Ase.
Proof.
  use tm_from_qq_eq.
  - exact eA.
  - cbn. apply PullbackArrowUnique; cbn.
    + etrans. apply @pathsinv0, assoc. 
      etrans. apply maponpaths, comp_ext_compare_π.
      apply (pr2 (pr2 Ase')).
    + apply es.
Qed.

Lemma pr2_tm_from_qq_paths
    {Γ : C} {t t' : tm_from_qq Γ : hSet} (e : t = t')
  : pr1 (pr2 t) = pr1 (pr2 t') ;; (Δ (maponpaths pr1 (!e))) .
Proof.
  destruct e. apply pathsinv0, id_right.
Qed.

Definition pp_from_qq_data (Γ : C^op)
  : tm_from_qq Γ --> Ty X Γ.
Proof.
  exact pr1.
Defined.

Lemma is_nat_trans_pp_from_qq
  : is_nat_trans _ _ pp_from_qq_data.
Proof.
  intros Γ Γ' f.
  apply idpath.
Defined. 

Definition pp_from_qq : preShv C ⟦tm_from_qq, TY X⟧
  := tpair _ _ is_nat_trans_pp_from_qq.

Arguments pp_from_qq : simpl never.

Definition te_from_qq {Γ:C} (A : Ty X Γ)
  : tm_from_qq $p (Γ ◂ A).
Proof.
  exists A [π A].
  apply (section_from_diagonal _ (qq_π_Pb Z _ _)). 
  exists (identity _). apply id_left.
Defined.

Definition term_from_qq_data : term_fun_structure_data C X.
Proof.
  exists tm_from_qq.
  exists pp_from_qq.
  intros; apply te_from_qq.
Defined.

(** ** Typing of te, and pullback property *)
Section Tm_fun_axioms_from_qq.

Variable Γ : C.
Variable A : Ty X Γ.


Definition Q_from_qq : Yo (Γ ◂ A) --> tm_from_qq.
Proof.
  simpl in A.
  apply yy, te_from_qq.
Defined.

Definition pp_te_from_qq
  : pp_from_qq $nt (te_from_qq A) = A [ π A ].
Proof.
  apply idpath.
Qed.

Definition Q_pp_from_qq
  : # Yo (π _) ;; yy A = Q_from_qq ;; pp_from_qq.
Proof.
  apply (@term_fun_str_square_comm _ _ term_from_qq_data).
  apply pp_te_from_qq.
Qed.

Definition section_qq_π  (Γ' : C) (f : C⟦ Γ', Γ⟧) 
    (s : C ⟦ Γ', Γ' ◂ A[f] ⟧)
    (e : s ;; π (A[f]) = identity Γ')
  : s ;; qq Z f A ;; π A = f.
Proof.
  etrans. apply @pathsinv0, assoc.
  etrans. apply @maponpaths, qq_π.
  etrans. apply assoc.
  etrans. apply maponpaths_2. exact e.
  apply id_left.
Qed.

Lemma Q_from_qq_reconstruction
    {Γ' : C} ( ft : C ⟦ Γ', Γ ◂ A ⟧ )
  : ft
  = pr1 (pr2 (Q_from_qq $nt ft)) ;; qq Z ft _ ;; qq Z _ A.
Proof.
  cbn.
  apply pathsinv0.
  etrans. {
    apply maponpaths_2.
    apply (PullbackArrow_PullbackPr2 (make_Pullback _ _)). }
  use (_ @ id_right _).  
  etrans. apply @pathsinv0, assoc.
  apply maponpaths.
  apply (PullbackArrow_PullbackPr2 (make_Pullback _ _)).
Qed.

(* TODO: try to speed this up! *)
Lemma isPullback_Q_pp_from_qq : isPullback Q_pp_from_qq.
Proof.
  apply pb_if_pointwise_pb. intros Γ'.
  apply isPullback_HSET. intros f [A' [s e]] e_A_A'; simpl in e_A_A'.
  destruct e_A_A'.
  use tpair.
  - exists (s ;; qq Z f A).
    simpl; unfold yoneda_morphisms_data.
    split. { apply (section_qq_π _ _ _ e). }
    use tm_from_qq_eq. cbn. 
    + etrans.
        apply @pathsinv0, functor_comp_pshf.
      apply maponpaths_2.
      cbn.
      etrans. apply @pathsinv0, assoc. 
      etrans. apply maponpaths, qq_π.
      etrans. apply assoc.
      etrans. apply maponpaths_2, e.
      apply id_left.
    + use (map_into_Pb_unique (qq_π_Pb Z _ _  )).
      * cbn.
        use (_ @ !e).
        etrans. apply @pathsinv0, assoc.
        etrans. apply @maponpaths, comp_ext_compare_π.
        apply (PullbackArrow_PullbackPr1 (make_Pullback _ _)).
      * etrans. apply @pathsinv0, assoc.
        use (maponpaths _ _ @ _).
        { use (qq Z _ _ ;; qq Z _ _). }
        -- etrans.
          2: {
            eapply z_iso_inv_on_right.
            etrans. 2: { apply @pathsinv0, assoc. }
            apply qq_comp. }
          apply @pathsinv0, z_iso_inv_on_right.
          apply @pathsinv0.
          etrans. apply assoc.
          etrans. apply maponpaths_2, @pathsinv0, comp_ext_compare_comp.
          apply comp_ext_compare_qq_general.
          apply (section_qq_π _ _ _ e).
        -- etrans. { apply assoc. }
          etrans. { apply maponpaths_2,
                  (PullbackArrow_PullbackPr2 (make_Pullback _ _)). }
          etrans. { apply @pathsinv0, assoc. }
          etrans. 2: { apply id_right. }
          apply maponpaths,
                  (PullbackArrow_PullbackPr2 (make_Pullback _ _)).
  - intros ft. apply subtypePath.
    { intro. apply isapropdirprod.
    + apply homset_property.
    + apply setproperty. }
    cbn. destruct ft as [ ft [ e1 e2 ] ]. cbn; cbn in e1.
    unfold yoneda_morphisms_data in e1.
    etrans. apply Q_from_qq_reconstruction.
    etrans. apply maponpaths_2, maponpaths_2, (pr2_tm_from_qq_paths e2).
    cbn.
    etrans. apply @pathsinv0, assoc.
    etrans. apply @pathsinv0, assoc.
    apply maponpaths.
    etrans. apply maponpaths.
      apply @pathsinv0, z_iso_inv_on_right.
      use (_ @ !assoc _ _ _).
      apply qq_comp.
    etrans. 2: { exact (comp_ext_compare_qq Z (!e1) _). }
    etrans. apply assoc.
    apply maponpaths_2.
    etrans. apply maponpaths, @pathsinv0, comp_ext_compare_inv.
    apply pathsinv0, comp_ext_compare_comp_general.
Time Qed.

End Tm_fun_axioms_from_qq.

Arguments Q_from_qq { _ } _ : simpl never.
Arguments tm_from_qq : simpl never.
Arguments pp_from_qq : simpl never.

(** ** Assembly into a compatible term-structure *)


Definition term_from_qq : term_fun_structure C X.
Proof.
  exists term_from_qq_data.
  intros ? ?.
  exists (pp_te_from_qq _ _).
  apply isPullback_Q_pp_from_qq.
Defined.

Definition iscompatible_term_from_qq
  : iscompatible_term_qq term_from_qq Z.
Proof.
  intros ? ? ? ?.
  (* TODO: use [tm_from_qq_eq'] here *)
  use tm_from_qq_eq; simpl.
  - etrans. apply pathsinv0, functor_comp_pshf.
    etrans. 2: { apply functor_comp_pshf. }
    apply maponpaths_2; cbn.
    apply @pathsinv0, qq_π.
  - apply PullbackArrowUnique.
    + cbn.
      etrans. apply @pathsinv0, assoc.
      etrans. apply maponpaths, comp_ext_compare_π.
      apply (PullbackArrow_PullbackPr1 (make_Pullback _ _)). 
    + apply (map_into_Pb_unique (qq_π_Pb Z _ _)).
      * cbn.
        etrans. apply @pathsinv0, assoc.
        etrans. apply maponpaths, qq_π.
        etrans. apply assoc.
        etrans. apply maponpaths_2.
          etrans. apply @pathsinv0, assoc.
          etrans. apply maponpaths, comp_ext_compare_π.
          apply (PullbackArrow_PullbackPr1 (make_Pullback _ _)).
        etrans. apply id_left.
        apply pathsinv0.
        etrans. apply @pathsinv0, assoc.
        etrans. apply maponpaths.
          apply (PullbackArrow_PullbackPr1 (make_Pullback _ _)).
        apply id_right.
      * cbn.
        etrans. apply @pathsinv0, assoc.
        etrans. apply @pathsinv0, assoc.
        etrans. apply maponpaths.
          etrans. apply maponpaths_2.
            etrans. apply comp_ext_compare_comp.
            etrans. apply maponpaths, comp_ext_compare_comp.
            apply assoc.
          etrans. apply @pathsinv0, assoc.
          etrans. apply maponpaths.
            etrans. apply assoc.
            apply @pathsinv0. apply qq_comp_general.
          etrans. apply @pathsinv0, assoc.
          etrans. apply maponpaths, comp_ext_compare_qq.
          etrans. apply maponpaths, qq_comp.
          apply assoc.
        etrans. apply assoc.
        etrans. apply maponpaths_2.
          etrans. apply maponpaths.
            etrans. apply assoc. 
            etrans. apply maponpaths_2.
              etrans. apply @pathsinv0, comp_ext_compare_comp.
              apply comp_ext_compare_id_general.
            apply id_left.
          apply (PullbackArrow_PullbackPr2 (make_Pullback _ _)).
        etrans. apply id_left.
        apply pathsinv0.
        etrans. apply @pathsinv0, assoc.
        etrans. apply maponpaths.
          apply (PullbackArrow_PullbackPr2 (make_Pullback _ _)).
        apply id_right.
Time Qed.

Definition compatible_term_from_qq : compatible_term_structure Z
  := (term_from_qq,, iscompatible_term_from_qq).
    
End compatible_term_structure_from_qq.

Arguments tm_from_qq : simpl never.
Arguments tm_from_qq_functor_mor : simpl never.
Arguments pp_from_qq : simpl never.
Arguments te_from_qq : simpl never.
Arguments Q_from_qq _ {_} _ : simpl never.

(** * Defining a (compatible) _q_-morphism structure, given a term structure

Key definitions: [qq_from_term], [iscompatible_qq_from_term] *)

(* TODO: see if this section can be simplified to construct the q-morphisms more directly. *)

Section compatible_comp_structure_from_term.

Variable Y : term_fun_structure C X.

Section qq_from_term.

Variables Γ Γ' : C.
Variable f : C⟦Γ', Γ⟧.
Variable A : Ty X Γ.

Let Xk := make_Pullback _ (isPullback_Q_pp Y A).

(** ** Groundwork in presheaves

We first construct maps of presheaves that will be the image of the _q_-morphisms under the Yoneda embedding. *)

Definition Yo_of_qq : _ ⟦Yo (Γ' ◂ A[f]), Yo (Γ ◂ A) ⟧.
Proof.
  use (PullbackArrow Xk).
  - apply (#Yo (π _) ;; #Yo f ). 
  - apply (Q Y).
  - abstract (
        clear Xk;
        assert (XT := Q_pp Y A[f]);
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

Lemma isPullback_Yo_of_qq : isPullback Yo_of_qq_commutes_1.
Proof.
  simple refine (isPullback_two_pullback _ _ _ _ _ _ _ _ _ _ ).
  - apply homset_property.
  - apply (TY X).
  - apply (TM Y).
  - apply (yy A).
  - apply pp.
  - apply Q.
  - apply Q_pp.
  - apply isPullback_Q_pp.
  - match goal with [|- isPullback ?HH ] => generalize HH end.
    rewrite <- (@yy_natural C).
    rewrite Yo_of_qq_commutes_2.
    intro.
    apply isPullback_Q_pp.
Qed.

(** ** Construction of the _q_-morphisms *)
Definition qq_term :  _ ⟦Γ' ◂ A[f] , Γ ◂ A⟧.
Proof.
  apply (invweq (make_weq _ (yoneda_fully_faithful _  _ _ ))).
  apply Yo_of_qq.
Defined.

Lemma Yo_qq_term_Yo_of_qq : # Yo qq_term = Yo_of_qq.
Proof.
  unfold qq_term.
  assert (XT := homotweqinvweq
     (make_weq _ (yoneda_fully_faithful _ (Γ'◂ A[f]) (Γ ◂ A)))).
  apply XT.
Qed.

Lemma qq_commutes_1 :  qq_term ;; π _ = π _ ;; f.
Proof.
  assert (XT:= Yo_of_qq_commutes_1).
  rewrite <- Yo_qq_term_Yo_of_qq in XT.
  do 2 rewrite <- functor_comp in XT.
  apply (invmaponpathsweq (make_weq _ (yoneda_fully_faithful _ _ _ ))).
  apply @pathsinv0, XT.
Qed.

Definition isPullback_qq : isPullback (!qq_commutes_1).
Proof.
  use (isPullback_preimage_square _ _ _ Yo).
  - apply homset_property.
  - apply yoneda_fully_faithful.
  - assert (XT:= isPullback_Yo_of_qq).
    match goal with |[|- isPullback ?HHH] => generalize HHH end.
    rewrite Yo_qq_term_Yo_of_qq.
    intro. assumption.
Qed.

End qq_from_term.

(** ** Assembly into a compatible _q_-morphism structure. *)

Definition qq_from_term_data : qq_morphism_data X.
Proof.
  use tpair.
  - intros. apply qq_term.
  - cbn. intros. simpl.
    exists (qq_commutes_1 _ _ _ _ ).
    apply isPullback_qq.
Defined.

Lemma is_split_qq_from_term : qq_morphism_axioms qq_from_term_data.
Proof.
  split.
  - intros Γ A. simpl.
    apply (invmaponpathsweq (make_weq _ (yoneda_fully_faithful _ _ _ ))).
    etrans; [ apply (homotweqinvweq (make_weq _ (yoneda_fully_faithful _ _ _ ))) | idtac ].    
    apply pathsinv0.
    unfold Yo_of_qq.
    apply PullbackArrowUnique. 
    + etrans. apply maponpaths. cbn. apply idpath. 
      rewrite <- functor_comp.
      etrans. eapply pathsinv0. use (functor_comp Yo).
      apply maponpaths.
      etrans. { apply comp_ext_compare_π. }
      apply pathsinv0, id_right.
    + etrans. apply maponpaths. cbn. apply idpath.
      apply comp_ext_compare_Q.
  - intros.
    apply (invmaponpathsweq (make_weq _ (yoneda_fully_faithful _ _ _ ))).
    etrans; [ apply (homotweqinvweq (make_weq _ (yoneda_fully_faithful _ _ _ ))) | idtac ].    
    sym. apply PullbackArrowUnique.
    + etrans. apply maponpaths. cbn. apply idpath.
      rewrite <- functor_comp.
      etrans. eapply pathsinv0. use (functor_comp Yo).
      apply maponpaths.
      rewrite <- assoc. rewrite qq_commutes_1 .
      repeat rewrite assoc.
      rewrite assoc4.
      etrans. apply maponpaths_2. apply maponpaths. eapply qq_commutes_1 .
      apply maponpaths_2.
      repeat rewrite assoc.
      apply maponpaths_2.
      apply comp_ext_compare_π.
    + etrans. apply maponpaths. cbn. apply idpath.
      etrans. apply maponpaths_2. apply functor_comp.
      rewrite <- assoc.
      rewrite Yo_qq_term_Yo_of_qq.
      rewrite  Yo_of_qq_commutes_2 .
      etrans. apply maponpaths_2. apply functor_comp.
      rewrite <- assoc.
      etrans. apply maponpaths. apply maponpaths_2. apply Yo_qq_term_Yo_of_qq.
      etrans. apply maponpaths. apply Yo_of_qq_commutes_2 .
      apply comp_ext_compare_Q.
Qed.

Definition qq_from_term
  : qq_morphism_structure X.
Proof.
  exists qq_from_term_data.
  apply is_split_qq_from_term.
Defined.

Lemma iscompatible'_qq_from_term : iscompatible'_term_qq Y qq_from_term.
Proof.
  intros Γ Γ' A f.
  assert (XR:= Yo_of_qq_commutes_2).
  apply pathsinv0.
  rewrite Yo_qq_term_Yo_of_qq.
  apply XR.
Qed.

Lemma iscompatible_qq_from_term : iscompatible_term_qq Y qq_from_term.
Proof.
  apply (pr2 (iscompatible_iscompatible' _ _)).
  apply iscompatible'_qq_from_term.
Qed.

Definition compatible_qq_from_term : compatible_qq_morphism_structure Y
  := (qq_from_term,, iscompatible_qq_from_term).
    
End compatible_comp_structure_from_term.

End Fix_Base_Category.

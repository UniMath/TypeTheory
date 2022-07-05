(**
  [TypeTheory.RelUniv.RelativeUniverses]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**

Contents:

- Definition of universe structure on a map, relative to a functor: [fcomprehension]
- [fcomprehension] is a proposition under saturation assumptions: [isaprop_fcomprehension]
- Definition of a relative universe: [relative_universe] (due to Vladimir Voevodsky)
- Transfer of a relative universe from one functor to another: [transfer_of_rel_univ_with_ess_surj]

*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheory.
Require Import TypeTheory.Auxiliary.Pullbacks.
Require Import TypeTheory.Auxiliary.TypeOfMorphisms.

(** * Relative universe structures *)

(** Given a map [ p : Ũ —> U ] in a category [D], 
    and a functor [ F : C —> D ], _a comprehension structure for [p] 
    relative to [F]_ is an operation providing all pullbacks of [p] 
    along morphisms from objects of the form [F X]. *)

Section Relative_Comprehension.

Context {C D : category} (J : functor C D).
Context {U tU : D} (p : D ⟦tU, U⟧).

Definition fpullback_data {X : C} (f : D ⟦J X, U⟧) : UU 
  := ∑ Xf : C, C⟦Xf, X⟧ × D⟦J Xf, tU⟧.

Definition fpb_ob  {X : C} {f : D⟦J X, U⟧} (T : fpullback_data f) : C := pr1 T.
Definition fp {X : C} {f : D⟦J X, U⟧} (T : fpullback_data f)
  : C⟦fpb_ob T, X⟧ := pr1 (pr2 T).
Definition fq {X : C} {f : D⟦J X, U⟧} (T : fpullback_data f)
  : D⟦ J (fpb_ob T), tU⟧ := pr2 (pr2 T).

Definition fpullback_prop {X : C} {f : D ⟦J X, U⟧} (T : fpullback_data f) : UU
:= commutes_and_is_pullback f p (#J (fp T)) (fq T).

Definition fpullback {X : C} (f : D ⟦J X, U⟧)
:= ∑ T : fpullback_data f, fpullback_prop T.

Coercion fpullback_data_from_fpullback
  {X : C} {f : D ⟦J X, U⟧} (T : fpullback f) : fpullback_data f
:= pr1 T.

Definition isPullback_fpullback
           {X : C} {f : D ⟦J X, U⟧ } (Y : fpullback f)
  : isPullback _ := pr2 (pr2 Y).

Definition rel_universe_structure := ∏ X (f : D⟦J X, U⟧), fpullback f.

Definition is_universe_relative_to : UU
  := ∏ (X : C) (f : D⟦J X, _ ⟧), ∥ fpullback f ∥ .

(* NOTE: [rel_universe_structure_data] never uses [p], only [U] and [tU]; so when section variables are generalised, it doesn’t depend on [p], even though conceptually perhaps it should. *)
Definition rel_universe_structure_data
  := ∏ X (f : D⟦ J X, U⟧), fpullback_data f.

Definition rel_universe_structure_prop (Y : rel_universe_structure_data)
  := ∏ X f, fpullback_prop (Y X f). 

(**  An equivalent form of [rel_universe_structure], separating its data and properties by interchanging ∑ and ∏ *)
Definition weq_rel_universe_structure_ :
   rel_universe_structure
     ≃ ∑ Y : rel_universe_structure_data, rel_universe_structure_prop Y.
Proof.
  eapply weqcomp.
  2: {
    set (XR:=@weqforalltototal (ob C)).
    specialize (XR (fun X => ∏ f : D⟦ J X, U⟧, fpullback_data f)). simpl in XR.
    specialize (XR (fun X pX => ∏ A, fpullback_prop  (pX  A))).
    apply XR.
  }
  apply weqonsecfibers.
  intro X.
  apply weqforalltototal.
Defined.

End Relative_Comprehension.

Arguments fpb_ob [_ _ _ _ _ _ _] _.
Arguments fp [_ _ _ _ _ _ _] _.
Arguments fq [_ _ _ _ _ _ _] _.
Arguments rel_universe_structure_data [_ _] _ _ _.
Arguments isPullback_fpullback [_ _ _ _ _ _ _ _] Y.

(** * Uniqueness of relative universe structures under some assumptions *)

Section Relative_Comprehension_Lemmas.

Context {C : category} {D : category} (J : functor C D).
Context {U tU : D} (pp : D ⟦tU, U⟧).

Lemma isaprop_fpullback_prop {X : C} {f : D ⟦J X, U⟧} (T : fpullback_data J f)
  : isaprop (fpullback_prop J pp T).
Proof.
  apply isofhleveltotal2.
  - apply homset_property.
  - intros. apply isaprop_isPullback.
Qed.

Lemma isaprop_fpullback {X : C} (f : D ⟦J X, U⟧) 
      (is_c : is_univalent C)
      (HJ : fully_faithful J) (* NOTE: the weaker assumption “ff on isos” might be enough. *)
  : isaprop (fpullback J pp f).
Proof.
  apply invproofirrelevance.
  intros x x'. apply subtypePath.
  - intro t. apply isaprop_fpullback_prop.
  - unfold fpullback_data in *.
    use total2_paths_f; simpl.
    + apply isotoid. { assumption. }
      apply (invmap (weq_ff_functor_on_z_iso HJ _ _)).
      refine (z_iso_from_Pullback_to_Pullback
                (make_Pullback _ (isPullback_fpullback _))
                (make_Pullback _ (isPullback_fpullback _))).
    + etrans. { apply (transportf_dirprod'
                         (λ a', C ⟦ a', _ ⟧) (λ a', D ⟦ J a', _ ⟧)). }
      apply pathsdirprod.
      * rewrite transportf_isotoid.
        cbn.
        unfold from_Pullback_to_Pullback.
        apply (invmaponpathsweq (weq_from_fully_faithful HJ _ _ )).
        cbn. rewrite functor_comp.
        etrans. { apply maponpaths_2,
                    (homotweqinvweq (weq_from_fully_faithful HJ _ _)). }
        apply (PullbackArrow_PullbackPr1 (make_Pullback _ _)).
      * etrans. { apply (transportf_isotoid_functor). }
        cbn.
        etrans. { apply maponpaths_2,
                    (homotweqinvweq (weq_from_fully_faithful HJ _ _)). }
        apply (PullbackArrow_PullbackPr2 (make_Pullback _ _)).
Qed.

Lemma isaprop_rel_universe_structure  (is_c : is_univalent C) 
    (HJ : fully_faithful J) : isaprop (rel_universe_structure J pp).
Proof.
  do 2 (apply impred; intro).
  apply isaprop_fpullback; assumption.
Qed.

End Relative_Comprehension_Lemmas.



(**  Relative universes *)

(** A _universe relative to a functor_ is just a map in the target category, 
    equipped with a relative comprehension structure. *)

Definition relative_universe {C D : category} (J : functor C D) : UU
  := ∑ X : mor_total D, rel_universe_structure J X.

Definition weak_relative_universe {C D : category} (J : functor C D) : UU
  := ∑ X : mor_total D, is_universe_relative_to J X.

(** ** Forgetful function from relative universes to relative weak universes *)

Definition weak_from_relative_universe {C D : category} (J : functor C D) 
  : relative_universe J → weak_relative_universe J.
Proof.
  use bandfmap.
  - apply idfun.
  - cbn. intros p H Γ f.
    apply hinhpr. apply H.
Defined.

Lemma weq_relative_universe_weak_relative_universe
    {C D : category} (J : functor C D)
    (Ccat : is_univalent C) (J_ff : fully_faithful J)
  : relative_universe J ≃ weak_relative_universe J.
Proof.
  apply weqfibtototal.
  intro p.
  apply weqonsecfibers. intro Γ.
  apply weqonsecfibers. intro f.
  apply truncation_weq.
  apply (isaprop_fpullback J _ _ Ccat J_ff).
Defined.

Goal ∏ (C D : category) (J : functor C D) 
     (Ccat : is_univalent C) (J_ff : fully_faithful J)
     (X : relative_universe J),
  weak_from_relative_universe _ X = 
  weq_relative_universe_weak_relative_universe _ Ccat J_ff X.
intros; apply idpath.
Qed.    


(* Access functions for relative universes *)
Section Relative_Universe_Accessors.

Context {C D : category} {J : functor C D}.

(* NOTE: it would be nice to have at least [base] as a coercion, and perhaps also [mor].  But when one declarest them as such and tries to use them, they are not found (presumably since they don’t satisfy the “uniform inheritance condition”, according to a warning given at declaration time). *)

Definition mor (U : relative_universe J) : mor_total D := pr1 U.

Definition base (U : relative_universe J) : D
  := target (mor U).

Definition total (U : relative_universe J) : D
  := source (mor U).
(* TODO: would it work more cleanly to have the total come via an object of the slice over the base? *)

Definition relative_universe_fpullback (U : relative_universe J)
  : forall (X:C) (f : J X --> base U), fpullback J (mor U) f
:= pr2 U.
Coercion relative_universe_fpullback : relative_universe >-> Funclass.

End Relative_Universe_Accessors.

Section Extension_Functoriality.
(* In case J : C —> D is fully faithful, the J-pullback operation a relative universe on J is automatically functorial, and the structure morphisms are natural with respect to that.

  For general J, these data+conditions should probably be added to the definition of a relative universe.  However, for fully faithful J, they exist uniquely. *)

(* TODO: 

- define a type [rel_universe_functoriality], given as the sigma-type of the four following lemmas;
- show (by the four following lemmas, plus a little more work) that this type is contractible for fully faithful [J].
- possibly rename the current definition of relative universe to eg [simple_relative_universe], and redefine [relative_universe] to include the functoriality. 
*)

Context {C D : category} {J : C ⟶ D}
  (U : relative_universe J).

Definition fpullback_mor_type : UU
  := forall (X : C) (f : J X --> base U)
            (X' : C) (f' : J X' --> base U)
            (g : X --> X') (e : # J g ;; f' = f)
  , fpb_ob (U X f) --> fpb_ob (U X' f').

Section fpb_mor_section.

Variable fpb_mor : fpullback_mor_type.
Arguments fpb_mor [ _ _ _ _ ] _ _ .


Definition id_fpb_mor_type : UU :=
  forall {X : C} (f : J X --> base U),
  let e := maponpaths_2 _ (functor_id _ _) _ @ id_left _
  in
   fpb_mor (identity X) e
  = identity (fpb_ob (U X f)).

Lemma isaprop_id_fpb_mor_type : isaprop id_fpb_mor_type.
Proof.
  do 2 (apply impred; intro).
  apply (homset_property C).
Qed.

Definition comp_fpb_mor_type : UU :=
  forall {X : C} {f : J X --> base U}
         {X' : C} {f' : J X' --> base U}
         {X'' : C} {f'' : J X'' --> base U}
         (g : X --> X') (e : # J g ;; f' = f)
         (g' : X' --> X'') (e' : # J g' ;; f'' = f'),
    let e'' := (maponpaths_2 _ (functor_comp _ _ _) _)
            @ !(assoc _ _ _) @ (maponpaths _ e') @ e in
    fpb_mor (g ;; g') e''
     = fpb_mor g e ;; fpb_mor g' e'.

Lemma isaprop_comp_fpb_mor_type : isaprop comp_fpb_mor_type.
Proof.
  do 10 (apply impred; intro).
  apply (homset_property C).
Qed.

Definition fp_nat_fpb_mor_type : UU :=
  forall {X : C} {f : J X --> base U}
         {X' : C} {f' : J X' --> base U}
         (g : X --> X') (e : # J g ;; f' = f),
    fpb_mor g e ;; fp _ = fp _ ;; g.

Lemma isaprop_fp_nat_fpb_mor_type : isaprop fp_nat_fpb_mor_type.
Proof.
  do 6 (apply impred; intro).
  apply (homset_property C).
Qed.
  

Definition fq_nat_fpb_mor_type : UU :=
  forall {X : C} {f : J X --> base U}
         {X' : C} {f' : J X' --> base U}
         (g : X --> X') (e : # J g ;; f' = f),
    # J (fpb_mor g e) ;; fq _ = fq _.

Lemma isaprop_fq_nat_fpb_mor_type : isaprop fq_nat_fpb_mor_type.
Proof.
  do 6 (apply impred; intro).
  apply (homset_property D).
Qed.

End fpb_mor_section.

Definition functorial_structure_relu : UU
  := ∑ fpb_mor : fpullback_mor_type,
                 
                 id_fpb_mor_type fpb_mor
                                 × comp_fpb_mor_type fpb_mor
                                 × fp_nat_fpb_mor_type fpb_mor
                                 × fq_nat_fpb_mor_type fpb_mor.

Definition fpb_mor (Y : functorial_structure_relu)
           {X : C} {f : J X --> base U}
           {X' : C} {f' : J X' --> base U}
           (g : X --> X') (e : # J g ;; f' = f)
  : fpb_ob (U X f) --> fpb_ob (U X' f')
  := pr1 Y _ _ _ _ g e.

Definition id_fpb_mor (Y : functorial_structure_relu)
  : id_fpb_mor_type (@fpb_mor Y)
  := pr1 (pr2 Y).

Definition comp_fpb_mor (Y : functorial_structure_relu)
  : comp_fpb_mor_type (@fpb_mor Y)
  := pr1 (pr2 (pr2 Y)).

Definition fp_nat_fpb_mor (Y : functorial_structure_relu)
  : fp_nat_fpb_mor_type (@fpb_mor Y)
  := pr1 (pr2 (pr2 (pr2 Y))).

Definition fq_nat_fpb_mor (Y : functorial_structure_relu)
  : fq_nat_fpb_mor_type (@fpb_mor Y)
  := pr2 (pr2 (pr2 (pr2 Y))).


Definition make_functorial_structure_relu
           (fpb_mor : fpullback_mor_type)
  : id_fpb_mor_type fpb_mor
    -> comp_fpb_mor_type fpb_mor
    -> fp_nat_fpb_mor_type fpb_mor
    -> fq_nat_fpb_mor_type fpb_mor
    -> functorial_structure_relu.
Proof.
  intros.
  exists fpb_mor.
  repeat split; assumption.
Defined.

Section functorial_structure_from_ff.

Context (HJ : fully_faithful J).

Definition rel_universe_fpullback_mor
    {X : C} {f : J X --> base U}
    {X' : C} {f' : J X' --> base U}
    (g : X --> X') (e : # J g ;; f' = f)
  : fpb_ob (U X f) --> fpb_ob (U X' f').
Proof.
  apply (fully_faithful_inv_hom HJ).
  use (map_into_Pb (pr2 (pr2 (U _ _)))).
  - apply (# J). exact (fp _ ;; g). 
  - apply fq.
  - refine (_ @ _). { apply maponpaths_2. apply functor_comp. }
    refine (_ @ _). { apply pathsinv0, assoc. }
    refine (_ @ _). { apply maponpaths, e. }
    exact (pr1 (pr2 (U X f))).
Defined.

Definition rel_universe_fpullback_mor_id
    {X : C} (f : J X --> base U)
    (e := maponpaths_2 _ (functor_id _ _) _ @ id_left _)
  : rel_universe_fpullback_mor (identity X) e
  = identity (fpb_ob (U X f)).
Proof.
  refine (_ @ _). 2: { apply fully_faithful_inv_identity. }
  apply (maponpaths (fully_faithful_inv_hom _ _ _)). 
  apply (map_into_Pb_unique (pr2 (pr2 (U _ _)))).
  - refine (_ @ _). { apply Pb_map_commutes_1. }
    refine (_ @ _). { apply maponpaths, id_right. }
    apply pathsinv0, id_left.
  - refine (_ @ _). { apply Pb_map_commutes_2. }
    apply pathsinv0, id_left.
Qed.
    
Definition rel_universe_fpullback_mor_comp
    {X : C} {f : J X --> base U}
    {X' : C} {f' : J X' --> base U}
    {X'' : C} {f'' : J X'' --> base U}
    (g : X --> X') (e : # J g ;; f' = f)
    (g' : X' --> X'') (e' : # J g' ;; f'' = f')
    (e'' := (maponpaths_2 _ (functor_comp _ _ _) _)
            @ !(assoc _ _ _) @ (maponpaths _ e') @ e)
  : rel_universe_fpullback_mor (g ;; g') e''
    = rel_universe_fpullback_mor g e
    ;; rel_universe_fpullback_mor g' e'.
Proof.
  refine (_ @ _). 2: { apply fully_faithful_inv_comp. }
  apply (maponpaths (fully_faithful_inv_hom _ _ _)).
  apply (map_into_Pb_unique (pr2 (pr2 (U _ _)))).
  - refine (_ @ _). { apply Pb_map_commutes_1. }
    refine (_ @ _).
    2: { apply pathsinv0.
      refine (_ @ _). { apply pathsinv0, assoc. } 
      refine (_ @ _). { apply maponpaths, Pb_map_commutes_1. }
      refine (_ @ _). { apply maponpaths, functor_comp. }
      refine (_ @ _). { apply assoc. }
      apply maponpaths_2, Pb_map_commutes_1.
    }
    refine (_ @ _). { apply maponpaths, assoc. }
    apply functor_comp.
  - refine (_ @ _). { apply Pb_map_commutes_2. }
    apply pathsinv0.
    refine (_ @ _). { apply pathsinv0, assoc. } 
    refine (_ @ _). { apply maponpaths, Pb_map_commutes_2. }
    apply Pb_map_commutes_2.    
Qed.

Definition rel_universe_fp_nat
    {X : C} {f : J X --> base U}
    {X' : C} {f' : J X' --> base U}
    (g : X --> X') (e : # J g ;; f' = f)
  : rel_universe_fpullback_mor g e ;; fp _ = fp _ ;; g.
Proof.
  apply (invmaponpathsweq (weq_from_fully_faithful HJ _ _)). 
  refine (_ @ _). { apply functor_comp. }
  refine (_ @ _).
    { apply maponpaths_2, (homotweqinvweq (weq_from_fully_faithful _ _ _)). }
  apply Pb_map_commutes_1.
Qed.

Definition rel_universe_fq_nat
    {X : C} {f : J X --> base U}
    {X' : C} {f' : J X' --> base U}
    (g : X --> X') (e : # J g ;; f' = f)
  : # J (rel_universe_fpullback_mor g e) ;; fq _ = fq _.
Proof.
  refine (_ @ _).
    { apply maponpaths_2, (homotweqinvweq (weq_from_fully_faithful _ _ _)). }
  apply Pb_map_commutes_2.
Qed.

Definition ff_functorial_structure_relu : functorial_structure_relu.
Proof.
  use make_functorial_structure_relu.
  - exact @rel_universe_fpullback_mor.
  - exact @rel_universe_fpullback_mor_id.
  - exact @rel_universe_fpullback_mor_comp.
  - exact @rel_universe_fp_nat.
  - exact @rel_universe_fq_nat.
Defined.

End functorial_structure_from_ff.

Lemma isaprop_functorial_structure_relu (HJ : faithful J)
  : isaprop functorial_structure_relu.
Proof.
  apply invproofirrelevance.
  intros xf xf'.
  apply subtypePath.
  { intro x. repeat (apply isapropdirprod).
    - apply isaprop_id_fpb_mor_type.
    - apply isaprop_comp_fpb_mor_type.
    - apply isaprop_fp_nat_fpb_mor_type.
    - apply isaprop_fq_nat_fpb_mor_type. }
  apply funextsec; intro X.
  apply funextsec; intro f.
  apply funextsec; intro X'.
  apply funextsec; intro f'.
  apply funextsec; intro g.
  apply funextsec; intro e.
  apply (isweqonpathsincl _ (HJ _ _ )).
  set (UXf' := U X' f').
  set (P:= isPullback_fpullback UXf').
  use (map_into_Pb_unique P).
  - destruct xf as [F [H1 [H2 [H3 H4]]]].
    destruct xf' as [F' [H1' [H2' [H3' H4']]]].
    cbn.
    etrans.
    {
      etrans. { apply pathsinv0. apply functor_comp. }
              apply maponpaths. apply H3. }
    apply pathsinv0.
    etrans. { apply pathsinv0. apply functor_comp. }
            apply maponpaths. apply H3'.
  - destruct xf as [F [H1 [H2 [H3 H4]]]].
    destruct xf' as [F' [H1' [H2' [H3' H4']]]].
    cbn.
    etrans. apply H4. apply pathsinv0. apply H4'.
Qed.

Lemma iscontr_functorial_structure_relu (HJ : fully_faithful J)
  : iscontr functorial_structure_relu.
Proof.
  apply iscontraprop1.
  - apply isaprop_functorial_structure_relu.
    apply (pr2 (fully_faithful_implies_full_and_faithful _ _ _ HJ)).
  - apply ff_functorial_structure_relu. apply HJ.
Defined.

End Extension_Functoriality.


(** * Transfer of relative universes *)

Section Rel_Univ_Structure_Transfer.

(** We give two sets of conditions under which a relative universe for one functor 
    can be transferred to one for another functor. 
    In each case, we start by assuming a commutative (up to iso) square of functors, 
    in which the right-hand functor _S_ preserves pullbacks. *)

Context
   {C : category} {D : category}
   (J : functor C D)
   (RUJ : relative_universe J)

   {C' : category} {D' : category}
   (J' : functor C' D')

   (R : functor C C') (S : functor D D')

   (α : [C, D'] ⟦functor_composite J S , functor_composite R J'⟧)
   (is_iso_α : is_z_isomorphism α)

   (S_pb : maps_pb_squares_to_pb_squares _ _ S).

(** On top of this, we then assume either 
   - the assumptions that [R] is split essentially surjective and [S] split full; or else 
   - that [R] is essentially surjective and [S] full, plus that [J] is fully faithful 
     and [C'] saturated.  
     These last two assumptions imply uniqueness of the new comprehension structure, 
     and hence allow getting chosen inverses out of the (non-split) 
     surjectivity assumptions. 
*)

Let αiso := α,, is_iso_α.
Let α' := inv_from_z_iso αiso. 
Let α'_α := nat_trans_eq_pointwise (z_iso_after_z_iso_inv αiso).
Let α_α' := nat_trans_eq_pointwise (z_iso_inv_after_z_iso αiso).

Local Definition α_iso : forall X, is_z_isomorphism (pr1 α X).
Proof.
  intros.
  apply is_functor_z_iso_pointwise_if_z_iso.
  assumption.
Qed.

Local Definition α'_iso : forall X, is_z_isomorphism (pr1 α' X).
Proof.
  intros.
  apply is_functor_z_iso_pointwise_if_z_iso.
  apply is_z_iso_inv_from_z_iso.
Qed.

Local Notation tU := (source (pr1 RUJ)).
Local Notation U :=  (target (pr1 RUJ)).
Local Notation pp := (morphism_from_total (pr1 RUJ)).

(** ** Transfer along split and split-full functors *)

Definition rel_universe_structure_induced_with_ess_split
    (R_es : split_ess_surj R)
    (S_sf : split_full S)
  :  rel_universe_structure J' (# S (pr1 RUJ)).
Proof.
  cbn in α, α', α'_α.
  intros X' g.
  set (Xi := R_es X'); destruct Xi as [X i]; clear R_es.
  set (f' := (α X ;; #J' i ;; g) : D' ⟦ S (J X), S U ⟧).
  destruct (S_sf _ _ f') as [f e_Sf_f']; clear S_sf.
  set (Xf :=  (pr2 RUJ) _ f); clearbody Xf.
  destruct Xf as [H A].
  destruct H as [Xf [p q]].
  destruct A as [e isPb]. cbn in e, isPb.
  assert (Sfp := S_pb _ _ _ _ _ _ _ _ _ isPb); clear S_pb.
  set (HSfp := functor_on_square D D' S e) in *; clearbody HSfp.
  use tpair.
  { exists (R Xf); split.
    - exact (#R p ;; i).
    - refine (α' Xf ;; #S q).
  }
  cbn. unfold fpullback_prop.
  use (commutes_and_is_pullback_transfer_z_iso _ _ _ _ _ Sfp).
  - apply identity_z_iso.
  - refine (z_iso_comp _ (functor_on_z_iso J' i)).
    exists (α _); apply α_iso.
  - apply identity_z_iso.
  - cbn. exists (α _); apply α_iso.
  - cbn. rewrite id_right.
    apply e_Sf_f'.
  - rewrite id_left. apply id_right.
  - cbn. rewrite functor_comp.
    repeat rewrite assoc. apply maponpaths_2, (nat_trans_ax α).
  - cbn. rewrite id_right. apply pathsinv0.
    rewrite assoc. eapply @pathscomp0. apply maponpaths_2, α_α'.
    apply id_left.
Qed.

Definition transfer_of_rel_univ_with_ess_split 
    (R_es : split_ess_surj R)
    (S_sf : split_full S)
  : relative_universe J'.
Proof.
  exists (morphism_as_total (#S pp)).
  apply rel_universe_structure_induced_with_ess_split; assumption.
Defined.

(** ** Transfer along surjective functors *)

Definition fpullback_induced_with_ess_surj
           (R_es : essentially_surjective R)
           (C'_sat : is_univalent C')
           (J'_ff : fully_faithful J')
           (* TODO: only “ff on isos” might suffice; see note at [isaprop_fpullback]. *)
           (S_full : full S)
           (X' : C')
           (g : D' ⟦ J' X', S U ⟧)
: fpullback J' (# S (pr1 RUJ)) g.
Proof.
  cbn in α, α', α'_α.
  unsquash from (R_es X') as [X i]; clear R_es.
  { apply isaprop_fpullback; assumption. }
  set (f' := (α X ;; #J' i ;; g) : D' ⟦ S (J X), S U ⟧).
  unsquash from (S_full _ _ f') as [f e_Sf_f']; clear S_full.
  { apply (isaprop_fpullback J'); assumption. }
  set (Xf :=  (pr2 RUJ) _ f); clearbody Xf.
  destruct Xf as [H A].
  destruct H as [Xf [p q]].
  destruct A as [e isPb]. cbn in e, isPb.
  assert (Sfp := S_pb _ _ _ _ _ _ _ _ _ isPb); clear S_pb.
  set (HSfp := functor_on_square D D' S e) in *; clearbody HSfp.
  use tpair.
  { exists (R Xf); split.
    - exact (#R p ;; i).
    - refine (α' Xf ;; #S q).
  }
  cbn. unfold fpullback_prop.
  use (commutes_and_is_pullback_transfer_z_iso _ _ _ _ _ Sfp).
  - apply identity_z_iso.
  - refine (z_iso_comp _ (functor_on_z_iso J' i)).
    exists (α _); apply α_iso.
  - apply identity_z_iso.
  - cbn. exists (α _); apply α_iso.
  - cbn. rewrite id_right.
    apply e_Sf_f'.
  - rewrite id_left. apply id_right.
  - cbn. rewrite functor_comp.
    repeat rewrite assoc. apply maponpaths_2, (nat_trans_ax α).
  - cbn. rewrite id_right. apply pathsinv0.
    rewrite assoc. eapply @pathscomp0. apply maponpaths_2, α_α'.
    apply id_left.
Defined.

Definition rel_universe_structure_induced_with_ess_surj
   (R_es : essentially_surjective R)
   (C'_sat : is_univalent C')
   (J'_ff : fully_faithful J')
     (* TODO: only “ff on isos” might suffice; see note at [isaprop_fpullback]. *)
   (S_full : full S)
  :  rel_universe_structure J' (# S (pr1 RUJ)).
Proof.
  cbn in α, α', α'_α.
  intros X' g.
  apply fpullback_induced_with_ess_surj; assumption.
Defined.

Definition transfer_of_rel_univ_with_ess_surj
    (R_es : essentially_surjective R)
    (C'_sat : is_univalent C')
    (J'_ff : fully_faithful J')
     (* TODO: only “ff on isos” might suffice; see note at [isaprop_fpullback]. *)
    (S_full : full S)
  : relative_universe J'.
Proof.
  exists (morphism_as_total (#S pp)).
  apply rel_universe_structure_induced_with_ess_surj; assumption.
Defined.

End Rel_Univ_Structure_Transfer.

Arguments transfer_of_rel_univ_with_ess_surj
  {_ _ J} u {_ _ _ _ _ _} α_is_iso S_pb R_es C'_univ J'_ff S_full : rename.
 
(** ** Transfer of weak relative universes *)

(** The next section literally copies a proof from the
    preceding section, with the exception of a truncation elimination
    in the middle of the proof.
    TODO: see if one can factor out a common lemma between the
          truncated lemma below and the untruncated lemma above.
*)
    

Section Is_universe_relative_to_Transfer.

Context
   {C : category} {D : category}
   (J : functor C D)

   {C' : category} {D' : category}
   (J' : functor C' D')

   (R : functor C C') (S : functor D D')

   (α : [C, D'] ⟦functor_composite J S , functor_composite R J'⟧)
   (is_iso_α : is_z_isomorphism α)

   (S_pb : maps_pb_squares_to_pb_squares _ _ S).

Let αiso := α,, is_iso_α.
Let α' := inv_from_z_iso αiso. 
Let α'_α := nat_trans_eq_pointwise (z_iso_after_z_iso_inv αiso).
Let α_α' := nat_trans_eq_pointwise (z_iso_inv_after_z_iso αiso).


Context
  (R_es : essentially_surjective R)
  (C'_sat : is_univalent C')
  (J'_ff : fully_faithful J')
  (* TODO: only “ff on isos” might suffice; see note at [isaprop_fpullback]. *)
  (S_full : full S).

Section fix_a_morphism.

Variables (U tU : D) (pp : tU --> U).

Section map_on_is_universe_relativ_to.

Hypothesis is : is_universe_relative_to J pp.


Lemma mere_fpullback_transfer {X' : C'} (g : D' ⟦ J' X', S U ⟧)
  : ∥ fpullback J' (# S pp) g ∥.
Proof.
  cbn in α, α', α'_α.
  unsquash from (R_es X') as [X i]; clear R_es.
  set (f' := (α X ;; #J' i ;; g) : D' ⟦ S (J X), S U ⟧).
  unsquash from (S_full _ _ f') as [f e_Sf_f']; clear S_full.
  unsquash from (is _ f) as [[Xf [p q]] [e isPb]].
  assert (Sfp := S_pb _ _ _ _ _ _ _ _ _ isPb); clear S_pb.
  set (HSfp := functor_on_square D D' S e) in *; clearbody HSfp.
  apply hinhpr.
  use tpair.
  { exists (R Xf); split.
    - exact (#R p ;; i).
    - refine (α' Xf ;; #S q).
  }
  cbn. unfold fpullback_prop.
  use (commutes_and_is_pullback_transfer_z_iso _ _ _ _ _ Sfp).
  - apply identity_z_iso.
  - refine (z_iso_comp _ (functor_on_z_iso J' i)).
    exists (α _). apply α_iso. apply is_iso_α.
  - apply identity_z_iso.
  - cbn. exists (α _). apply α_iso. apply is_iso_α.
  - cbn. rewrite id_right.
    apply e_Sf_f'.
  - rewrite id_left. apply id_right.
  - cbn. rewrite functor_comp.
    repeat rewrite assoc. apply maponpaths_2, (nat_trans_ax α).
  - cbn. rewrite id_right. apply pathsinv0.
    rewrite assoc. eapply @pathscomp0. apply maponpaths_2, α_α'.
    apply id_left.
Defined.


Lemma is_universe_transfer : is_universe_relative_to J' (#S pp).
Proof.
  intros X' g.
  apply (mere_fpullback_transfer g).
Defined.

End map_on_is_universe_relativ_to.

Definition αpwiso X : z_iso (S (J X)) (J' (R X))
  := functor_z_iso_pointwise_if_z_iso _ _ _ _ _ α is_iso_α X.


Definition isweq_is_universe_transfer 
           (R_full : full R) 
           (S_faithful : faithful S)
  : isweq is_universe_transfer.
Proof.
  set (S_ff
    := full_and_faithful_implies_fully_faithful _ _ S (S_full,,S_faithful)).
  use (gradth _ _ _ _ ).
  - intro H.
    intros X f.
    set (f' := (α' : nat_trans _ _ ) X ;; #S f).
    unsquash from (H (R X) f') as [[X' [p' q']] [H1 H2]]. 
    cbn in H1, H2.
    
    unsquash from (R_es X') as [Xf i].
    
    (* get a preimage of [i · 'p] *)
    unsquash from (R_full _ _ (i · p')) as [ip' Hip'].
    apply hinhpr.
    repeat (use tpair).
    + apply Xf.
    + exact ip'.
    + set (hi := (α : nat_trans _ _ ) Xf). cbn in hi.
      set (XR := hi ;; functor_on_z_iso J' i ;; q'). 
      exact (invmap (weq_from_fully_faithful S_ff _ _ ) XR).
    + cbn. apply (invmaponpathsweq (weq_from_fully_faithful S_ff _ _ )).
      cbn. apply pathsinv0.
      etrans. rewrite functor_comp. apply maponpaths_2.
              apply (homotweqinvweq (weq_from_fully_faithful S_ff _ _ )).
      unfold f' in H1. unfold f' in H2. clear f'.
      etrans. eapply pathsinv0. repeat rewrite <- assoc.
              apply maponpaths. apply maponpaths. apply H1.
      rewrite functor_comp.
      repeat rewrite assoc. apply maponpaths_2.
      apply pathsinv0. rewrite <- assoc. rewrite <- assoc.
      apply (z_iso_inv_to_left (C:=D') _ _ _ (αpwiso Xf )).
      cbn.
      etrans. { apply pathsinv0, (nat_trans_ax α'). }
      cbn.
      etrans. { apply maponpaths_2, maponpaths, Hip'. }
      rewrite functor_comp.
      apply pathsinv0, assoc.
    + cbn. 
      match goal with |[|- isPullback (?HH)] => generalize HH end.
      intro HH.
      use (isPullback_preimage_square _ _ _ _ S_ff). 
      { apply homset_property. }
      match goal with |[|- isPullback (?HH)] => generalize HH end.
      assert (XR := homotweqinvweq (weq_from_fully_faithful S_ff (J Xf) tU )).
      simpl in XR. rewrite XR.
      clear HH XR.
      intro HH.
      use (isPullback_transfer_z_iso _ _ _ _ _ _ H2).
      * exact (identity_z_iso _ ).
      * exact (z_iso_inv_from_z_iso (αpwiso _ )).
      * exact (identity_z_iso _ ).
      * apply (z_iso_comp (functor_on_z_iso J' (z_iso_inv_from_z_iso i)) 
                        (z_iso_inv_from_z_iso (αpwiso _ ))).
      * cbn. rewrite id_right. 
        unfold f'. apply idpath.
      * rewrite id_left. rewrite id_right. apply idpath.
      * cbn.
        etrans. 2: { apply assoc. }
        etrans. 2: { apply maponpaths, (nat_trans_ax α'). }
        rewrite assoc.
        apply maponpaths_2. cbn.
        rewrite <- functor_comp. 
        apply maponpaths.
        apply pathsinv0.
        etrans. { apply maponpaths, Hip'. }
        rewrite assoc.
        rewrite z_iso_after_z_iso_inv.
        apply id_left.
      * cbn. rewrite id_right.
        apply pathsinv0.
        do 2 rewrite assoc.
        etrans. { apply maponpaths_2, assoc4. }
        etrans. { apply maponpaths_2, maponpaths_2, maponpaths, α'_α. }
        rewrite id_right.
        rewrite <- functor_comp.
        rewrite z_iso_after_z_iso_inv.
        rewrite functor_id.
        apply id_left.
  - intros.
    do 2 (apply impred_isaprop; intro); apply propproperty.
  - intros.
    do 2 (apply impred_isaprop; intro); apply propproperty.
Defined.

End fix_a_morphism.

Definition weak_relative_universe_transfer : 
  weak_relative_universe J -> weak_relative_universe J'.
Proof.
  use bandfmap.
  - apply (functor_on_mor_total S).
  - intro pp. cbn.
    apply is_universe_transfer.
Defined.


Definition isweq_weak_relative_universe_transfer 
           (R_full : full R)
           (isD : is_univalent D) (isD' : is_univalent D')
           (T : functor D' D)
           (eta : z_iso (C:=[D, D]) (functor_identity D) (S ∙ T))
           (eps : z_iso (C:=[D', D']) (T ∙ S) (functor_identity D'))
           (S_faithful : faithful S) 
  : isweq weak_relative_universe_transfer.
Proof.
  apply isweqbandfmap_var.
  - use isweq_equivalence_on_mor_total.
    + apply isD.
    + apply isD'.
    + apply T.
    + apply eta.
    + apply eps.
  - intro pp.
    apply isweq_is_universe_transfer.
    + apply R_full.
    + apply S_faithful.
Defined.

Definition weq_weak_relative_universe_transfer
           (R_full : full R)
           (isD : is_univalent D) (isD' : is_univalent D')
           (T : functor D' D)
           (eta : z_iso (C:=[D, D]) (functor_identity D) (S ∙ T))
           (eps : z_iso (C:=[D', D']) (T ∙ S) (functor_identity D'))
           (S_ff : fully_faithful S)
  : weak_relative_universe J ≃ weak_relative_universe J'
:= make_weq _
     (isweq_weak_relative_universe_transfer R_full isD isD' T eta eps S_ff).

Section Weak_RelU_Comm_Square.

  Definition weak_relu_comm_square
  : ∏ (u : relative_universe J),
    weak_from_relative_universe J' (transfer_of_rel_univ_with_ess_surj u
                                      is_iso_α S_pb R_es C'_sat J'_ff S_full)
    = weak_relative_universe_transfer (weak_from_relative_universe J u).
  Proof.
    intros u.
    use total2_paths_f.
    - apply idpath.
    - do 2 (apply impred_isaprop; intro); apply propproperty.
  Defined.

End Weak_RelU_Comm_Square.


End Is_universe_relative_to_Transfer.


(* *)

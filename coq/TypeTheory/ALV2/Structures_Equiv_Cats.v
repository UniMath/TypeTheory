
(**

 Ahrens, Lumsdaine, Voevodsky, 2015 - 2016

*)

Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.equivalences.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.
Require Import TypeTheory.Displayed_Cats.Auxiliary.
Require Import TypeTheory.Displayed_Cats.Core.
Require Import TypeTheory.Displayed_Cats.Constructions.
Require Import TypeTheory.Displayed_Cats.Equivalences.
Require Import TypeTheory.ALV1.Structures.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Maps.
Require Import TypeTheory.ALV2.Structures_Cats.

Local Set Automatic Introduction.
(* only needed since imports globally unset it *)

(* TODO: globalise upstream? *)
Notation "# F" := (functor_over_on_morphisms F)
  (at level 3) : mor_disp_scope.

(* TODO: as ever, upstream when possible. *)
Section Auxiliary.

(* The following definition takes unfair advantage of the fact that  [functor_composite (functor_identity _) (functor_identity _)]
  is judgementally(!) equal to [functor_identity _]. *)
Definition functor_over_id_composite
  {C : Precategory}
  {CC DD EE : disp_precat C}
  (FF : functor_over (functor_identity _) CC DD)
  (GG : functor_over (functor_identity _) DD EE)
: functor_over (functor_identity _) CC EE
:= functor_over_composite FF GG.

End Auxiliary.

Section Fix_Context.

Context {C : Precategory}.

Local Notation hsC := (homset_property C).

Local Notation "'Yo'" := (yoneda C hsC).
Local Notation "'Yo^-1'" :=  (invweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ ))).

Local Notation "Γ ◂ A" := (comp_ext _ Γ A) (at level 30).
Local Notation "'Ty'" := (fun X Γ => (TY X : functor _ _) Γ : hSet) (at level 10).

Local Notation Δ := comp_ext_compare.
Local Notation φ := obj_ext_mor_φ.

Section Compatible_Disp_Cat.

(* TODO: rename [strucs_compat_FOO] to [strucs_iscompat_FOO] throughout, to disambiguate these from the sigma’d displayed-precat [compat_structures]. *)

Definition strucs_compat_ob_mor
  : disp_precat_ob_mor (total_precat
      (families_disp_precat C × qq_structure_disp_precat C)).
Proof.
  use tpair.
  - intros XYZ. exact (iscompatible_fam_qq (pr1 (pr2 XYZ)) (pr2 (pr2 XYZ))).
  - simpl; intros; exact unit.
    (* For a given map of object-extension structures, a lifting to a map of either families-structures or _q_-morphism structues is essentially unique; so there is no extra compatibility condition required here on maps. *)
Defined.

Definition strucs_compat_id_comp
  : disp_precat_id_comp _ strucs_compat_ob_mor.
Proof.
  split; intros; exact tt.
Qed.

Definition strucs_compat_data : disp_precat_data _
  := ( _ ,, strucs_compat_id_comp).

Definition strucs_compat_axioms : disp_precat_axioms _ strucs_compat_data.
Proof.
  repeat apply tpair; intros; try apply isasetaprop; apply isapropunit.
Qed.

Definition strucs_compat_disp_precat
  : disp_precat (total_precat
      (families_disp_precat C × qq_structure_disp_precat C))
:= ( _ ,, strucs_compat_axioms).

Definition compat_structures_disp_precat
  := sigma_disp_precat strucs_compat_disp_precat.

Definition compat_structures_pr1_disp_functor
  : functor_over (functor_identity _)
      compat_structures_disp_precat (families_disp_precat C)
:= functor_over_id_composite
     (sigmapr1_disp_functor _) (dirprodpr1_disp_functor _ _).

Definition compat_structures_pr2_disp_functor
  : functor_over (functor_identity _)
      compat_structures_disp_precat (qq_structure_disp_precat C)
:= functor_over_id_composite
     (sigmapr1_disp_functor _) (dirprodpr2_disp_functor _ _).

(* TODO: once the equivalence has been redone at the displayed level, the following are probably redundant/obsolete and should be removed. *)
Definition compat_structures_precat
  := total_precat (strucs_compat_disp_precat).

Definition compat_structures_pr1_functor
  : functor compat_structures_precat (families_structure_precat C)
:= functor_composite
     (pr1_precat _)
     (total_functor (dirprodpr1_disp_functor _ _)).

Definition compat_structures_pr2_functor
  : functor compat_structures_precat (qq_structure_precat C)
:= functor_composite
     (pr1_precat _)
     (total_functor (dirprodpr2_disp_functor _ _)).

End Compatible_Disp_Cat.

(** * Lemmas towards an equivalence *)

(** In the following two sections, we prove lemmas which should amount to the fact that the two projections from [compat_structures_disp_precat C] to [families_disp_precat C] and [qq_structure_precat C] are each equivalences (of displayed categories).

We don’t yet have the infrastructure on displayed categories to put it together as that fact; for now we put it together just as equivalences of _total_ precategories. *)
 
Section Unique_QQ_From_Fam.

Lemma qq_from_fam_ob {X : obj_ext_precat} (Y : families_disp_precat C X)
  : Σ (Z : qq_structure_disp_precat C X), strucs_compat_disp_precat (X ,, (Y ,, Z)).
Proof.
  exists (qq_from_fam Y).
  apply iscompatible_qq_from_fam.
Defined.

Lemma qq_from_fam_mor {X X' : obj_ext_precat} {F : X --> X'}
  {Y : families_disp_precat C X} {Y'} (FY : Y -->[F] Y')
  {Z : qq_structure_disp_precat C X} {Z'}
  (W : strucs_compat_disp_precat (X,,(Y,,Z)))
  (W' : strucs_compat_disp_precat (X',,(Y',,Z')))
  : Σ (FZ : Z -->[F] Z'), W -->[(F,,(FY,,FZ))] W'.
Proof.
  refine (_,, tt).
  intros Γ' Γ f A.
  cbn in W, W', FY. unfold iscompatible_fam_qq in *. 
  unfold families_mor in FY.
  apply (Q_pp_Pb_unique Y'); simpl; unfold yoneda_morphisms_data.
  - etrans. apply @pathsinv0, assoc.
    etrans. apply maponpaths, obj_ext_mor_ax.
      (* TODO: name of [obj_ext_mor_ax] unmemorable.  Rename more like [qq_π]? *)
    etrans. apply @pathsinv0, qq_π.
      (* TODO: name of [qq_π] misleading, suggests opposite direction. *)
    apply pathsinv0.
    etrans. apply @pathsinv0, assoc.
    etrans. apply maponpaths, @pathsinv0, qq_π.
    etrans. apply assoc. apply cancel_postcomposition.
    etrans. apply @pathsinv0, assoc.
    etrans. apply maponpaths. apply comp_ext_compare_π.
    apply obj_ext_mor_ax.
  (* Maybe worth abstracting the following pointwise application of [W],
   [families_mor_Q], etc. as lemmas? *)
  - etrans.
      exact (!toforallpaths _ _ _
        (nat_trans_eq_pointwise (families_mor_Q FY _) _) _).
    etrans. apply maponpaths, @pathsinv0, id_left.
    etrans. cbn. apply maponpaths.
      exact (!toforallpaths _ _ _
        (nat_trans_eq_pointwise (W _ _ _ _) _) _).
    apply pathsinv0.
    etrans.
      exact (!toforallpaths _ _ _
        (nat_trans_eq_pointwise (W' _ _ _ _) _) _).
    etrans. apply Q_comp_ext_compare.
    etrans. apply maponpaths, @pathsinv0, id_left.
    exact (!toforallpaths _ _ _
      (nat_trans_eq_pointwise (families_mor_Q FY _) _) _).
Time Qed.

Lemma qq_from_fam_mor_unique {X X' : obj_ext_precat} {F : X --> X'}
  {Y : families_disp_precat C X} {Y'} (FY : Y -->[F] Y')
  {Z : qq_structure_disp_precat C X} {Z'}
  (W : strucs_compat_disp_precat (X,,(Y,,Z)))
  (W' : strucs_compat_disp_precat (X',,(Y',,Z')))
  : isaprop (Σ (FZ : Z -->[F] Z'), W -->[(F,,(FY,,FZ))] W').
Proof.
  apply isofhleveltotal2.
  - simpl. repeat (apply impred_isaprop; intro). apply hsC.
  - intros; simpl. apply isapropunit.
Qed.

End Unique_QQ_From_Fam.

Section Unique_Fam_From_QQ.

Lemma fam_from_qq_ob {X : obj_ext_precat} (Z : qq_structure_disp_precat C X)
  : Σ (Y : families_disp_precat C X), strucs_compat_disp_precat (X ,, (Y ,, Z)).
Proof.
  exists (fam_from_qq Z).
  apply iscompatible_fam_from_qq.
Defined.

(** The next main goal is the following statement.  However, the construction of the morphism of families structures is rather large; so we break out the first component (the map of term presheaves) into several independent lemmas, before returning to this in [fam_from_qq_mor] below. *)
Lemma fam_from_qq_mor {X X' : obj_ext_precat} {F : X --> X'}
  {Z : qq_structure_disp_precat C X} {Z'} (FZ : Z -->[F] Z')
  {Y : families_disp_precat C X} {Y'}
  (W : strucs_compat_disp_precat (X,,(Y,,Z)))
  (W' : strucs_compat_disp_precat (X',,(Y',,Z')))
  : Σ (FY : Y -->[F] Y'), W -->[(F,,(FY,,FZ))] W'.
Abort.

Lemma fam_from_qq_mor_TM_data {X X' : obj_ext_precat} {F : X --> X'}
  {Z : qq_structure_disp_precat C X} {Z'} (FZ : Z -->[F] Z')
  {Y : families_disp_precat C X} {Y'}
  (W : strucs_compat_disp_precat (X,,(Y,,Z)))
  (W' : strucs_compat_disp_precat (X',,(Y',,Z')))
  : Π Γ,
    ((TM (Y : families_structure _ _) : functor _ _) Γ : hSet)
    -> ((TM (Y' : families_structure _ _) : functor _ _) Γ : hSet).
Proof.
  intros Γ t; simpl in Γ.
  exact ((Q _ _ : nat_trans _ _) _ (pr1 (term_to_section t) ;; φ F _)).
Defined.

Lemma fam_from_qq_mor_TM_naturality {X X' : obj_ext_precat} {F : X --> X'}
  {Z : qq_structure_disp_precat C X} {Z'} (FZ : Z -->[F] Z')
  {Y : families_disp_precat C X} {Y'}
  (W : strucs_compat_disp_precat (X,,(Y,,Z)))
  (W' : strucs_compat_disp_precat (X',,(Y',,Z')))
  : is_nat_trans (TM _ : functor _ _) _ (fam_from_qq_mor_TM_data FZ W W').
Proof.
  simpl in Y, Y'.
  intros Γ' Γ f; apply funextsec; intros t.
  (* Part 1: naturality of the section-to-term map back to [Tm Y']. *)
  etrans. Focus 2. exact (toforallpaths _ _ _ (nat_trans_ax (Q Y' _) _ _ _) _).
  cbn. simpl in W, W'; unfold iscompatible_fam_qq in W, W'.
  (* We want to apply [W'] on the lhs, so we need to munge the type argument
  of [Q] to a form with the [f] action outermost.  Naturality will show that
  the type is equal to such a form; [Q_comp_ext_compare] pushes that type
  equality through [Q]. *)
  etrans. 
    apply @pathsinv0.
    simple refine (Q_comp_ext_compare _ _); simpl.
    Focus 2. etrans. apply maponpaths.
      exact (toforallpaths _ _ _ (nat_trans_ax (pp Y) _ _ _) _).
    exact (toforallpaths _ _ _ (nat_trans_ax (obj_ext_mor_TY F) _ _ _) _).
  etrans.
    exact (toforallpaths _ _ _ (nat_trans_eq_pointwise (W' _ _ _ _) _) _).
  apply (maponpaths ((Q _ _ : nat_trans _ _ ) Γ)).
  simpl. unfold yoneda_morphisms_data.
  (* Part 2: naturality of the transfer along [F]. *)
  etrans. apply @pathsinv0, assoc.
  etrans. apply @pathsinv0, assoc.
  etrans. apply maponpaths.
    etrans. apply assoc. 
    etrans. apply cancel_postcomposition. Focus 2.
      apply @pathsinv0. 
      etrans. Focus 2. apply assoc. 
      apply maponpaths, FZ.
    etrans. Focus 2. apply @pathsinv0, assoc.
    etrans. Focus 2. apply cancel_postcomposition.
      apply @pathsinv0, Δ_φ.
    etrans. Focus 2. apply assoc.
    apply maponpaths, comp_ext_compare_comp.
  etrans. apply assoc.
  etrans. apply assoc.
  etrans. Focus 2. apply @pathsinv0, assoc.
  apply cancel_postcomposition.
  (* Part 3: naturality in [Γ] of the term-to-section construction from [Tm Y]. *)
  apply (Q_pp_Pb_unique Y).
  + unfold yoneda_morphisms_data. 
    apply @pathscomp0 with f.
    * etrans. apply @pathsinv0, assoc.
      etrans. apply maponpaths, @pathsinv0, qq_π.
      etrans. apply assoc.
      etrans. Focus 2. apply id_left.
      apply cancel_postcomposition.
      etrans. apply @pathsinv0, assoc.
      etrans. apply maponpaths, comp_ext_compare_π.
      exact (pr2 (term_to_section _)).
    * etrans. apply @pathsinv0, id_right.
      etrans. Focus 2. apply assoc.
      apply maponpaths, pathsinv0.
      exact (pr2 (term_to_section _)).
  + etrans. Focus 2.
      exact (toforallpaths _ _ _ (!nat_trans_ax (Q _ _) _ _ _) _).
    etrans. Focus 2. cbn.
      apply maponpaths, @pathsinv0, term_to_section_recover.
    etrans.
      exact (!toforallpaths _ _ _ (nat_trans_eq_pointwise (W _ _ _ _) _) _).
    etrans. apply Q_comp_ext_compare.
    apply term_to_section_recover.
Time Qed.

Definition fam_from_qq_mor_TM {X X' : obj_ext_precat} {F : X --> X'}
    {Z : qq_structure_disp_precat C X} {Z'} (FZ : Z -->[F] Z')
    {Y : families_disp_precat C X} {Y'}
    (W : strucs_compat_disp_precat (X,,(Y,,Z)))
    (W' : strucs_compat_disp_precat (X',,(Y',,Z')))
  : TM (Y : families_structure _ _) --> TM (Y' : families_structure _ _)
:= (fam_from_qq_mor_TM_data _ _ _,, fam_from_qq_mor_TM_naturality FZ W W').

Lemma fam_from_qq_mor {X X' : obj_ext_precat} {F : X --> X'}
  {Z : qq_structure_disp_precat C X} {Z'} (FZ : Z -->[F] Z')
  {Y : families_disp_precat C X} {Y'}
  (W : strucs_compat_disp_precat (X,,(Y,,Z)))
  (W' : strucs_compat_disp_precat (X',,(Y',,Z')))
  : Σ (FY : Y -->[F] Y'), W -->[(F,,(FY,,FZ))] W'.
Proof.
  simpl in W, W'; unfold iscompatible_fam_qq in W, W'. (* Readability *)
  simpl in Y, Y'.  (* To avoid needing casts [Y : families_structure _]. *)
  refine (_,,tt). simpl; unfold families_mor.
  exists (fam_from_qq_mor_TM FZ W W').
  apply dirprodpair; try intros Γ A; apply nat_trans_eq; cbn.
  - apply has_homsets_HSET.
  - simpl. intros Γ; apply funextsec; intros t.
    etrans. refine (!toforallpaths _ _ _ (nat_trans_eq_pointwise (Q_pp _ _) _) _).
    simpl. unfold yoneda_morphisms_data; cbn.
    etrans. refine (toforallpaths _ _ _(!nat_trans_ax (obj_ext_mor_TY _) _ _ _) _).
    cbn; apply maponpaths.
    etrans.
      refine (toforallpaths _ _ _ _ ((pp Y : nat_trans _ _) Γ t)).
      apply maponpaths.
      etrans. apply @pathsinv0, assoc.
      etrans. apply maponpaths, obj_ext_mor_ax.
      exact (pr2 (term_to_section _)).
    exact (toforallpaths _ _ _ (functor_id (TY _) _) _).
  - apply has_homsets_HSET.
  - intros Γ'. unfold yoneda_morphisms_data, yoneda_objects_ob; cbn.
    apply funextsec; intros f.
    etrans.
      (* TODO: consider changing direction of [Q_comp_ext_compare]?*)
      apply @pathsinv0. simple refine (Q_comp_ext_compare _ _); simpl.
        exact ((obj_ext_mor_TY F : nat_trans _ _) _ 
                 (# (TY _ : functor _ _) (f ;; π _) A)). 
      apply maponpaths.
      refine (!toforallpaths _ _ _ (nat_trans_eq_pointwise (Q_pp _ _) _) _).
    cbn.
    Arguments Δ [_ _ _ _ _ _]. idtac.
    etrans. apply maponpaths.
      etrans. apply @pathsinv0, assoc.
      etrans. apply maponpaths, @pathsinv0, Δ_φ.
      apply assoc.
    etrans. 
      apply @pathsinv0. simple refine (Q_comp_ext_compare _ _); simpl.
        exact (# (TY _ : functor _ _) (f ;; π _)
                 ((obj_ext_mor_TY F : nat_trans _ _) _ A)).
      exact (toforallpaths _ _ _ (nat_trans_ax (obj_ext_mor_TY F) _ _ _) _).
    cbn.
    etrans. exact (toforallpaths _ _ _ (nat_trans_eq_pointwise (W' _ _ _ _) _) _).
    simpl; unfold yoneda_morphisms_data; cbn.  apply maponpaths.
    etrans. apply @pathsinv0, assoc.
    etrans. apply @pathsinv0, assoc.
    etrans. apply maponpaths.
      etrans. apply assoc.
      apply @pathsinv0, FZ.
    etrans. apply assoc.
    apply cancel_postcomposition.
  apply (map_from_term_recover W).
Time Qed.

Lemma fam_from_qq_mor_unique {X X' : obj_ext_precat} {F : X --> X'}
  {Z : qq_structure_disp_precat C X} {Z'} (FZ : Z -->[F] Z')
  {Y : families_disp_precat C X} {Y'}
  (W : strucs_compat_disp_precat (X,,(Y,,Z)))
  (W' : strucs_compat_disp_precat (X',,(Y',,Z')))
  : isaprop (Σ (FY : Y -->[F] Y'), W -->[(F,,(FY,,FZ))] W').
Proof.
  apply isofhleveltotal2.
  - simpl. apply isaprop_families_mor.
  - intros; simpl. apply isapropunit.
Defined.

End Unique_Fam_From_QQ.

(** We show, in this section, that the (non-displayed) projection functors from the (total) precategory of compatible-pairs-of-structures on C to the precategories of qq-structures and of families-structures are each equivalences. 

TODO: scrap this section, and recover it from the displayed version. *) 
Section Strucs_Equiv_Precats.

(* TODO: could strengthen to “explicitly essentially surjective” *)
Lemma compat_structures_pr1_ess_surj
  : essentially_surjective (compat_structures_pr1_functor).
Proof.
  unfold essentially_surjective.
  intros XY; destruct XY as [X Y]; apply hinhpr.
  exists ((X,,(Y,, qq_from_fam Y)),,iscompatible_qq_from_fam Y).
  apply identity_iso.
Qed.

Lemma compat_structures_pr1_fully_faithful
  : fully_faithful (compat_structures_pr1_functor).
Proof.
  intros XYZW XYZW'.
  destruct XYZW as [ [X [Y Z] ] W].
  destruct XYZW' as [ [X' [Y' Z'] ] W'].
  unfold compat_structures_pr1_functor; simpl.
  assert (structural_lemma :
    Π A (B C : A -> UU) (D : Π a, B a -> C a -> UU)
      (H : Π a b, iscontr (Σ c, D a b c)),
    isweq (fun abcd : Σ (abc : Σ a, (B a × C a)),
                        D (pr1 abc) (pr1 (pr2 abc)) (pr2 (pr2 abc))
            => (pr1 (pr1 abcd),, pr1 (pr2 (pr1 abcd))))).
    clear C X Y Z W X' Y' Z' W'.
  { intros A B C D H.
    use gradth.
    + intros ab.
      set (cd := iscontrpr1 (H (pr1 ab) (pr2 ab))). 
        exact ((pr1 ab,, (pr2 ab,, pr1 cd)),, pr2 cd).
    + intros abcd; destruct abcd as [ [a [b c] ] d]; simpl.
      refine (@maponpaths _ _ 
        (fun cd : Σ c' : C a, (D a b c') => (a,, b,, (pr1 cd)),, (pr2 cd))
        _ (_,, _) _).
      apply proofirrelevancecontr, H.
    + intros ab; destruct ab as [a b]. apply idpath. }
  simple refine (structural_lemma _ _ _ _ _).
  - intros FX FY FZ.
      exists (W -->[FX,,(FY,,FZ)] W').
  - intros FX FY. apply iscontraprop1.
    exact (qq_from_fam_mor_unique FY W W').
    exact (qq_from_fam_mor FY W W').
Qed.

(* TODO: could strengthen to “explicitly essentially surjective” *)
Lemma compat_structures_pr2_ess_surj
  : essentially_surjective (compat_structures_pr2_functor).
Proof.
  unfold essentially_surjective.
  intros XZ; destruct XZ as [X Z]; apply hinhpr.
  exists ((X,,(fam_from_qq Z,, Z)),,iscompatible_fam_from_qq Z).
  apply identity_iso.
Qed.

Lemma compat_structures_pr2_fully_faithful
  : fully_faithful (compat_structures_pr2_functor).
Proof.
  intros XYZW XYZW';
  destruct XYZW as [ [X [Y Z] ] W];
  destruct XYZW' as [ [X' [Y' Z'] ] W'].
  unfold compat_structures_pr2_functor; simpl.
  assert (structural_lemma :
    Π A (B C : A -> UU) (D : Π a, B a -> C a -> UU)
      (H : Π a c, iscontr (Σ b, D a b c)),
    isweq (fun abcd : Σ (abc : Σ a, (B a × C a)),
                        D (pr1 abc) (pr1 (pr2 abc)) (pr2 (pr2 abc))
            => (pr1 (pr1 abcd),, pr2 (pr2 (pr1 abcd))))).
    clear C X Y Z W X' Y' Z' W'.
  { intros A B C D H.
    use gradth.
    + intros ac.
      set (bd := iscontrpr1 (H (pr1 ac) (pr2 ac))). 
        exact ((pr1 ac,, (pr1 bd,, pr2 ac)),, pr2 bd).
    + intros abcd; destruct abcd as [ [a [b c] ] d]; simpl.
      refine (@maponpaths _ _ 
        (fun bd : Σ b' : B a, (D a b' c) => (a,, (pr1 bd),, c),, (pr2 bd))
        _ (_,, _) _).
      apply proofirrelevancecontr, H.
    + intros ac; destruct ac as [a c]. apply idpath. }
  simple refine (structural_lemma _ _ _ _ _).
  - intros FX FY FZ.
      exists (W -->[FX,,(FY,,FZ)] W').
  - intros FX FY. apply iscontraprop1.
    exact (fam_from_qq_mor_unique FY W W').
    exact (fam_from_qq_mor FY W W').
Qed.

End Strucs_Equiv_Precats.

Section Strucs_Disp_Equiv.

Lemma compat_structures_pr1_ess_split
  : functor_over_disp_ess_split_surj (compat_structures_pr1_disp_functor).
Proof.
  unfold functor_over_disp_ess_split_surj.
  intros X Y.
  exists ((Y,, qq_from_fam Y),,iscompatible_qq_from_fam Y).
  apply identity_iso_disp.
Defined.

Lemma compat_structures_pr1_ff
  : functor_over_ff (compat_structures_pr1_disp_functor).
Proof.
  intros X X' YZW YZW'.
  destruct YZW as [ [Y Z] W].
  destruct YZW' as [ [Y' Z'] W'].
  unfold compat_structures_pr1_functor; simpl.
  intros FX.
  assert (structural_lemma :
    Π (B C : UU) (D : B -> C -> UU)
      (H : Π b, iscontr (Σ c, D b c)),
    isweq (fun bcd : Σ (bc : B × C), D (pr1 bc) (pr2 bc)
            => pr1 (pr1 bcd))).
    clear C X Y Z W X' Y' Z' W' FX.
  { intros B C D H.
    use gradth.
    + intros b.
      set (cd := iscontrpr1 (H b)). 
        exact ((b,,pr1 cd),, pr2 cd).
    + intros bcd; destruct bcd as [ [b c] d]; simpl.
      refine (@maponpaths _ _ 
        (fun cd : Σ c', (D b c') => (b,, (pr1 cd)),, (pr2 cd))
        _ (_,, _) _).
      apply proofirrelevancecontr, H.
    + intros b; apply idpath. }
  simple refine (structural_lemma _ _ _ _).
  - intros FY FZ.
      exists (W -->[FX,,(FY,,FZ)] W').
  - intros FY. apply iscontraprop1.
    exact (qq_from_fam_mor_unique FY W W').
    exact (qq_from_fam_mor FY W W').
Qed.

Lemma compat_structures_pr1_is_equiv_over_id
  : is_equiv_over_id (compat_structures_pr1_disp_functor).
Proof.
  apply is_equiv_from_ff_ess_over_id.
  - apply compat_structures_pr1_ess_split.
  - apply compat_structures_pr1_ff.
Defined.

Definition compat_structures_pr1_equiv_over_id
  : equiv_over_id _ _
:= compat_structures_pr1_is_equiv_over_id.

Definition compat_structures_pr1_inverse_over_id
     : equiv_over_id
         (families_disp_precat C) compat_structures_disp_precat.
Proof.
  exact (equiv_inv _ (compat_structures_pr1_is_equiv_over_id)).
Defined.

Lemma compat_structures_pr2_ess_split
  : functor_over_disp_ess_split_surj (compat_structures_pr2_disp_functor).
Proof.
  unfold functor_over_disp_ess_split_surj.
  intros X Z.
  exists ((fam_from_qq Z,, Z),,iscompatible_fam_from_qq Z).
  apply identity_iso_disp.
Defined.

Lemma compat_structures_pr2_ff
  : functor_over_ff (compat_structures_pr2_disp_functor).
Proof.
  intros X X' YZW YZW'.
  destruct YZW as [ [Y Z] W].
  destruct YZW' as [ [Y' Z'] W'].
  unfold compat_structures_pr1_functor; simpl.
  intros FX.
  assert (structural_lemma :
    Π (B C : UU) (D : B -> C -> UU)
      (H : Π c, iscontr (Σ b, D b c)),
    isweq (fun bcd : Σ (bc : B × C), D (pr1 bc) (pr2 bc)
            => pr2 (pr1 bcd))).
    clear C X Y Z W X' Y' Z' W' FX.
  { intros B C D H.
    use gradth.
    + intros c.
      set (bd := iscontrpr1 (H c)). 
        exact ((pr1 bd,,c),, pr2 bd).
    + intros bcd; destruct bcd as [ [b c] d]; simpl.
      refine (@maponpaths _ _ 
        (fun bd : Σ b', (D b' c) => ((pr1 bd),, c),, (pr2 bd))
        _ (_,, _) _).
      apply proofirrelevancecontr, H.
    + intros c; apply idpath. }
  simple refine (structural_lemma _ _ _ _).
  - intros FY FZ.
      exists (W -->[FX,,(FY,,FZ)] W').
  - intros FY. apply iscontraprop1.
    exact (fam_from_qq_mor_unique FY W W').
    exact (fam_from_qq_mor FY W W').
Qed.

Lemma compat_structures_pr2_is_equiv_over_id
  : is_equiv_over_id (compat_structures_pr2_disp_functor).
Proof.
  apply is_equiv_from_ff_ess_over_id.
  - apply compat_structures_pr2_ess_split.
  - apply compat_structures_pr2_ff.
Defined.

Definition compat_structures_pr2_equiv_over_id
  : equiv_over_id _ _
:= compat_structures_pr2_is_equiv_over_id.

Definition compat_structures_pr2_inverse_over_id
     : equiv_over_id
         (qq_structure_disp_precat C) compat_structures_disp_precat.
Proof.
  exact (equiv_inv _ (compat_structures_pr2_is_equiv_over_id)).
Defined.

End Strucs_Disp_Equiv.

Section Strucs_Fiber_Equiv.

Context (X : obj_ext_Precat C).

Definition fam_struc_to_qq_struc_fibre_functor
  : functor
      (fibre_precategory (families_disp_precat C) X)
      (fibre_precategory (qq_structure_disp_precat C) X).
Proof.
  eapply functor_composite.
  - eapply fibre_functor.
    exact compat_structures_pr1_inverse_over_id.
    (* TODO: make lemma [fibre_functor_over_id] *)
  - exact (fibre_functor compat_structures_pr2_equiv_over_id X).
Defined.

Definition fam_struc_to_qq_struc_is_equiv
  : adj_equivalence_of_precats
      fam_struc_to_qq_struc_fibre_functor.
Proof.
  eapply comp_adj_equivalence_of_precats.
  - apply fibre_equiv.
    apply is_equiv_of_equiv_over_id.
  - apply fibre_equiv.
    apply is_equiv_of_equiv_over_id.
  (* TODO: WTF with all the shelving!? *)
  Unshelve. 
(* TODO: define [fibre_precategory] as a [Precategory], so we can just use [homset_property] here. *)
  apply has_homsets_fibre. apply has_homsets_fibre. apply has_homsets_fibre.
Defined.

End Strucs_Fiber_Equiv.




End Fix_Context.
(**
  [TypeTheory.CwF_TypeCat.CwF_SplitTypeCat_Equiv_Cats]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Equivalences.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheory.
Require Import TypeTheory.Auxiliary.SetsAndPresheaves.
Require Import TypeTheory.Auxiliary.DisplayedCategories.

Require Import TypeTheory.CwF_TypeCat.CwF_SplitTypeCat_Defs.
Require Import TypeTheory.CwF_TypeCat.CwF_SplitTypeCat_Maps.
Require Import TypeTheory.CwF_TypeCat.CwF_SplitTypeCat_Cats.
Require Import TypeTheory.CwF_TypeCat.CwF_SplitTypeCat_Equivalence. (* TODO: needed for some natural transformations. *)

Section Fix_Context.

Context {C : category}.

Local Notation "Γ ◂ A" := (comp_ext _ Γ A) (at level 30).
Local Notation "'Ty'" := (fun X Γ => TY X $p Γ) (at level 10).

Local Notation Δ := comp_ext_compare.
Local Notation φ := obj_ext_mor_φ.

Section Compatible_Disp_Cat.

(* TODO: rename [strucs_compat_FOO] to [strucs_iscompat_FOO] throughout, to disambiguate these from the sigma’d displayed-precat [compat_structures]. *)

Definition strucs_compat_ob_mor
  : disp_cat_ob_mor (total_category
      (term_fun_disp_cat C × qq_structure_disp_cat C)).
Proof.
  use tpair.
  - intros XYZ. exact (iscompatible_term_qq (pr1 (pr2 XYZ)) (pr2 (pr2 XYZ))).
  - simpl; intros; exact unit.
    (* For a given map of object-extension structures, a lifting to a map of either term-structures or _q_-morphism structues is essentially unique; so there is no extra compatibility condition required here on maps. *)
Defined.

Definition strucs_compat_id_comp
  : disp_cat_id_comp _ strucs_compat_ob_mor.
Proof.
  split; intros; exact tt.
Qed.

Definition strucs_compat_data : disp_cat_data _
  := ( _ ,, strucs_compat_id_comp).

Definition strucs_compat_axioms : disp_cat_axioms _ strucs_compat_data.
Proof.
  repeat apply tpair; intros; try apply isasetaprop; apply isapropunit.
Qed.

Definition strucs_compat_disp_cat
  : disp_cat (total_category
      (term_fun_disp_cat C × qq_structure_disp_cat C))
:= ( _ ,, strucs_compat_axioms).

Definition compat_structures_disp_cat
  := sigma_disp_cat strucs_compat_disp_cat.

Definition compat_structures_pr1_disp_functor
  : disp_functor (functor_identity _)
      compat_structures_disp_cat (term_fun_disp_cat C)
:= disp_functor_id_composite
     (sigmapr1_disp_functor _) (dirprodpr1_disp_functor _ _).

Definition compat_structures_pr2_disp_functor
  : disp_functor (functor_identity _)
      compat_structures_disp_cat (qq_structure_disp_cat C)
:= disp_functor_id_composite
     (sigmapr1_disp_functor _) (dirprodpr2_disp_functor _ _).

Definition compat_structures_precat
  := total_category (strucs_compat_disp_cat).

Definition compat_structures_pr1_functor
  : functor compat_structures_precat (cwf'_structure_precat C)
:= functor_composite
     (pr1_category _)
     (total_functor (dirprodpr1_disp_functor _ _)).

Definition compat_structures_pr2_functor
  : functor compat_structures_precat (sty'_structure_precat C)
:= functor_composite
     (pr1_category _)
     (total_functor (dirprodpr2_disp_functor _ _)).

End Compatible_Disp_Cat.

(** * Lemmas towards an equivalence *)

(** In the following two sections, we prove lemmas which should amount to the fact that the two projections from [compat_structures_disp_cat C] to [cwf'_precat C] and [sty'_structure_precat C] are each equivalences (of displayed categories).

We don’t yet have the infrastructure on displayed categories to put it together as that fact; for now we put it together just as equivalences of _total_ precategories. *)
 
Section Unique_QQ_From_Term.

Lemma qq_from_term_ob {X : obj_ext_cat C} (Y : term_fun_disp_cat C X)
  : ∑ (Z : qq_structure_disp_cat C X), strucs_compat_disp_cat (X ,, (Y ,, Z)).
Proof.
  exists (qq_from_term Y).
  apply iscompatible_qq_from_term.
Defined.

(* TODO: upstream *)
Lemma comp_ext_compare_te
    {X : obj_ext_structure C}
    {Y : term_fun_structure C X}
    {Γ:C} {A A' : Ty X Γ} (e : A = A')
  : #p (TM Y) (Δ e) (te Y A') = te Y A.
Proof.
  destruct e; cbn.
  apply functor_id_pshf.
Qed.

Lemma qq_from_term_mor {X X' : obj_ext_cat C} {F : X --> X'}
  {Y : term_fun_disp_cat C X} {Y'} (FY : Y -->[F] Y')
  {Z : qq_structure_disp_cat C X} {Z'}
  (W : strucs_compat_disp_cat (X,,(Y,,Z)))
  (W' : strucs_compat_disp_cat (X',,(Y',,Z')))
  : ∑ (FZ : Z -->[F] Z'), W -->[(F,,(FY,,FZ))] W'.
Proof.
  use (_,, tt).
  intros Γ' Γ f A.
  cbn in W, W', FY. unfold iscompatible_term_qq in *. 
  unfold term_fun_mor in FY.
  apply (Q_pp_Pb_unique Y'); simpl; unfold yoneda_morphisms_data.
  - etrans. apply @pathsinv0, assoc.
    etrans. apply maponpaths, obj_ext_mor_ax.
      (* TODO: name of [obj_ext_mor_ax] unmemorable.  Rename more like [qq_π]? *)
    etrans. apply qq_π.
    apply pathsinv0.
    etrans. apply @pathsinv0, assoc.
    etrans. apply maponpaths, qq_π.
    etrans. apply assoc. apply maponpaths_2.
    etrans. apply @pathsinv0, assoc.
    etrans. apply maponpaths. apply comp_ext_compare_π.
    apply obj_ext_mor_ax.
  - etrans. apply functor_comp_pshf.
    etrans. cbn. apply maponpaths, @pathsinv0, (term_fun_mor_te FY).
    etrans. apply pathsinv0, nat_trans_ax_pshf.
    etrans. cbn. apply maponpaths, @pathsinv0, W.
    etrans. apply term_fun_mor_te.
    apply pathsinv0.
    etrans. apply functor_comp_pshf.
    etrans. cbn. apply maponpaths, @pathsinv0, W'.
    etrans. apply functor_comp_pshf.
    apply maponpaths. 
    apply comp_ext_compare_te.
Time Qed.

Lemma qq_from_term_mor_unique {X X' : obj_ext_cat C} {F : X --> X'}
  {Y : term_fun_disp_cat C X} {Y'} (FY : Y -->[F] Y')
  {Z : qq_structure_disp_cat C X} {Z'}
  (W : strucs_compat_disp_cat (X,,(Y,,Z)))
  (W' : strucs_compat_disp_cat (X',,(Y',,Z')))
  : isaprop (∑ (FZ : Z -->[F] Z'), W -->[(F,,(FY,,FZ))] W').
Proof.
  apply isofhleveltotal2.
  - simpl. repeat (apply impred_isaprop; intro). apply homset_property.
  - intros; simpl. apply isapropunit.
Qed.

End Unique_QQ_From_Term.

Section Unique_Term_From_QQ.

Lemma term_from_qq_ob {X : obj_ext_cat C} (Z : qq_structure_disp_cat C X)
  : ∑ (Y : term_fun_disp_cat C X), strucs_compat_disp_cat (X ,, (Y ,, Z)).
Proof.
  exists (term_from_qq Z).
  apply iscompatible_term_from_qq.
Defined.

(** The next main goal is the following statement.  However, the construction of the morphism of term structures is rather large; so we factor the first component (the map of term presheaves) into several steps, going explicitly via the canonical term-structure constructed from sections [term_fun_from_qq], before returning to this in [term_from_qq_mor] below. *)
Lemma term_from_qq_mor {X X' : obj_ext_cat C} {F : X --> X'}
  {Z : qq_structure_disp_cat C X} {Z'} (FZ : Z -->[F] Z')
  {Y : term_fun_disp_cat C X} {Y'}
  (W : strucs_compat_disp_cat (X,,(Y,,Z)))
  (W' : strucs_compat_disp_cat (X',,(Y',,Z')))
  : ∑ (FY : Y -->[F] Y'), W -->[(F,,(FY,,FZ))] W'.
Abort.

(* We start by showing that a map of _q_-morphism structures induces a map of term-structures between their canonical term-structures of sections. *)


(* TODO: rename and upstream this section! *)
Section Rename_me.

(* TODO: naming conventions in this section clash rather with those of [CwF_TypeCat.CwF_SplitTypeCat_Equivalence]. Consider! *)
Lemma tm_from_qq_mor_data {X X' : obj_ext_cat C} {F : X --> X'}
    {Z : qq_structure_disp_cat C X} {Z'} (FZ : Z -->[F] Z')
  : nat_trans_data (tm_from_qq Z) (tm_from_qq Z').
Proof.
  intros Γ Ase.
  exists (obj_ext_mor_TY F $nt (pr1 Ase)).
  exists (pr1 (pr2 Ase) ;; φ F _).
  etrans. apply @pathsinv0, assoc.
  etrans. apply maponpaths, obj_ext_mor_ax.
  apply (pr2 (pr2 Ase)).
Defined.

Lemma tm_from_qq_mor_naturality {X X' : obj_ext_cat C} {F : X --> X'}
    {Z : qq_structure_disp_cat C X} {Z'} (FZ : Z -->[F] Z')
  : is_nat_trans (tm_from_qq Z) (tm_from_qq Z') (tm_from_qq_mor_data FZ).
Proof.
  intros Γ Γ' f; cbn in Γ, Γ', f.
  apply funextsec; intros [A [s e]].
  use tm_from_qq_eq.
  - cbn. apply nat_trans_ax_pshf.
  - cbn. apply PullbackArrowUnique. 
    + etrans. cbn. apply @pathsinv0, assoc.
      etrans. apply maponpaths, comp_ext_compare_π.
      etrans. apply @pathsinv0, assoc.
      etrans. apply maponpaths, obj_ext_mor_ax.
      use (PullbackArrow_PullbackPr1
                (make_Pullback _ (qq_π_Pb _ f A))).
    + cbn in FZ; cbn.
      etrans. apply maponpaths_2, @pathsinv0, assoc.
      etrans. apply @pathsinv0, assoc.
      etrans. apply maponpaths, @pathsinv0, FZ.
      etrans. apply assoc.
      etrans. apply maponpaths_2.
        apply (PullbackArrow_PullbackPr2 (make_Pullback _ _)). 
      apply pathsinv0, assoc.
Time Qed.

Lemma tm_from_qq_mor_TM {X X' : obj_ext_cat C} {F : X --> X'}
    {Z : qq_structure_disp_cat C X} {Z'} (FZ : Z -->[F] Z')
  : nat_trans (tm_from_qq Z) (tm_from_qq Z').
Proof.
  exists (tm_from_qq_mor_data FZ).
  apply tm_from_qq_mor_naturality.
Defined.

Lemma tm_from_qq_mor_pp {X X' : obj_ext_cat C} {F : X --> X'}
    {Z : qq_structure_disp_cat C X} {Z'} (FZ : Z -->[F] Z')
  : (tm_from_qq_mor_TM FZ : preShv C ⟦ _ , _ ⟧) ;; pp_from_qq Z'
  = pp_from_qq Z;; obj_ext_mor_TY F.
Proof.
  apply nat_trans_eq. apply homset_property.
  intros Γ. apply idpath.
Qed.

Lemma tm_from_qq_mor_te {X X' : obj_ext_cat C} {F : X --> X'}
    {Z : qq_structure_disp_cat C X} {Z'} (FZ : Z -->[F] Z')
    {Γ} (A : Ty X Γ)
  : tm_from_qq_mor_TM FZ _ (te_from_qq Z A)
  = # (tm_from_qq Z') (φ F A)
      (te_from_qq Z' (obj_ext_mor_TY F $nt A)).
Proof.
  cbn.
  use tm_from_qq_eq_reindex.
  - cbn.
  (* Putting these equalities under [abstract] shaves a couple of seconds off the overall Qed time, but makes the proof script rather less readable. *) 
    etrans. 2: { apply functor_comp_pshf. }
    etrans. 2: { cbn. apply maponpaths_2, @pathsinv0, obj_ext_mor_ax. }
    apply nat_trans_ax_pshf.
  - etrans. 2: { apply @pathsinv0, 
        (postCompWithPullbackArrow _ _ _ _ (make_Pullback _ _)). }
    apply PullbackArrowUnique.
    + cbn.
      etrans. apply @pathsinv0, assoc.
      etrans. apply maponpaths, qq_π.
      etrans. apply assoc.
      etrans. 2: { apply @pathsinv0, id_right. }
      etrans. 2: { apply id_left. }
      apply maponpaths_2.
      etrans. apply @pathsinv0, assoc.
      etrans. apply maponpaths, comp_ext_compare_π.
      etrans. apply @pathsinv0, assoc.
      etrans. apply maponpaths, obj_ext_mor_ax.
      apply (PullbackArrow_PullbackPr1 (make_Pullback _ _)).
    + etrans. 2: { apply @pathsinv0, id_right. }
      etrans. cbn. apply maponpaths_2, maponpaths_2, maponpaths.
        etrans. apply comp_ext_compare_comp.
        apply maponpaths_2, comp_ext_compare_comp.
      etrans. apply @pathsinv0, assoc.
      etrans. apply maponpaths_2, assoc.
      etrans. apply @pathsinv0, assoc.
      etrans. apply maponpaths. 
        etrans. apply assoc.
        apply @pathsinv0, @qq_comp.
      etrans. apply maponpaths_2, assoc.
      etrans. apply @pathsinv0, assoc.
      etrans. apply maponpaths, comp_ext_compare_qq.
      etrans. apply maponpaths_2, @pathsinv0, assoc.
      etrans. apply @pathsinv0, assoc.
      etrans. apply maponpaths, @pathsinv0. use FZ.
        (* TODO: give access function [qq_structure_mor_ax]! *)
      etrans. apply assoc.
      etrans. apply maponpaths_2.
        apply (PullbackArrow_PullbackPr2 (make_Pullback _ _)).
      apply id_left.
Time Qed.

End Rename_me.

Definition term_from_qq_mor_TM {X X' : obj_ext_cat C} {F : X --> X'}
    {Z : qq_structure_disp_cat C X} {Z'} (FZ : Z -->[F] Z')
    {Y : term_fun_disp_cat C X} {Y'}
    (W : strucs_compat_disp_cat (X,,(Y,,Z)))
    (W' : strucs_compat_disp_cat (X',,(Y',,Z')))
  : TM (Y : term_fun_structure _ _) --> TM (Y' : term_fun_structure _ _).
Proof.
  use ( _ ;; (tm_from_qq_mor_TM FZ : preShv C ⟦ _ , _ ⟧) ;; _).
  - exact (given_TM_to_canonical _ _ (Y,,W)).
  - exact (canonical_TM_to_given _ _ (Y',,W')).
Defined.
(* TODO: better, construct these three parts as maps of qq-morphism structures, and put them together directly as that. *)

Lemma term_from_qq_mor {X X' : obj_ext_cat C} {F : X --> X'}
  {Z : qq_structure_disp_cat C X} {Z'} (FZ : Z -->[F] Z')
  {Y : term_fun_disp_cat C X} {Y'}
  (W : strucs_compat_disp_cat (X,,(Y,,Z)))
  (W' : strucs_compat_disp_cat (X',,(Y',,Z')))
  : ∑ (FY : Y -->[F] Y'), W -->[(F,,(FY,,FZ))] W'.
Proof.
  simpl in W, W'; unfold iscompatible_term_qq in W, W'. (* Readability *)
  simpl in Y, Y'.  (* To avoid needing casts [Y : term_fun_structure _]. *)
  use (_,,tt). simpl; unfold term_fun_mor.
  exists (term_from_qq_mor_TM FZ W W').
  apply make_dirprod; try intros Γ A.
  - etrans. apply @pathsinv0, assoc.
    etrans. apply maponpaths, (pp_canonical_TM_to_given _ _ (_,,_)).
    etrans. apply @pathsinv0, assoc.
    etrans. apply maponpaths, tm_from_qq_mor_pp.
    etrans. apply assoc.
    apply maponpaths_2, (pp_given_TM_to_canonical _ _ (_,,_)).
  - unfold term_from_qq_mor_TM. 
    etrans. 2: { eapply maponpaths, (canonical_TM_to_given_te _ _ (_,,_)). }
    etrans. 2: { apply nat_trans_ax_pshf. }
    etrans. 2: { apply maponpaths, (tm_from_qq_mor_te FZ). }
    cbn. apply maponpaths, maponpaths, given_TM_to_canonical_te.
Defined.

Lemma term_from_qq_mor_unique {X X' : obj_ext_cat C} {F : X --> X'}
  {Z : qq_structure_disp_cat C X} {Z'} (FZ : Z -->[F] Z')
  {Y : term_fun_disp_cat C X} {Y'}
  (W : strucs_compat_disp_cat (X,,(Y,,Z)))
  (W' : strucs_compat_disp_cat (X',,(Y',,Z')))
  : isaprop (∑ (FY : Y -->[F] Y'), W -->[(F,,(FY,,FZ))] W').
Proof.
  apply isofhleveltotal2.
  - simpl. apply isaprop_term_fun_mor.
  - intros; simpl. apply isapropunit.
Defined.

End Unique_Term_From_QQ.

(** We show, in this section, that the (non-displayed) projection functors from the (total) precategory of compatible-pairs-of-structures on C to the precategories of _q_-morphism structures and of term-structures are each equivalences. 

TODO: scrap this section, and recover it from the displayed version. *) 
Section Strucs_Equiv_Precats.

(* TODO: strengthen to “split essentially surjective” *)
Lemma compat_structures_pr1_ess_surj
  : essentially_surjective (compat_structures_pr1_functor).
Proof.
  unfold essentially_surjective.
  intros XY; destruct XY as [X Y]; apply hinhpr.
  exists ((X,,(Y,, qq_from_term Y)),,iscompatible_qq_from_term Y).
  apply identity_z_iso.
Qed.

Lemma compat_structures_pr1_fully_faithful
  : fully_faithful (compat_structures_pr1_functor).
Proof.
  intros XYZW XYZW'.
  destruct XYZW as [ [X [Y Z] ] W].
  destruct XYZW' as [ [X' [Y' Z'] ] W'].
  unfold compat_structures_pr1_functor; simpl.
  assert (structural_lemma :
    ∏ (A : UU) (B C : A -> UU) (D : ∏ a, B a -> C a -> UU)
      (H : ∏ a b, iscontr (∑ c, D a b c)),
    isweq (fun abcd : ∑ (abc : ∑ a, (B a × C a)),
                        D (pr1 abc) (pr1 (pr2 abc)) (pr2 (pr2 abc))
            => (pr1 (pr1 abcd),, pr1 (pr2 (pr1 abcd))))).
  { clear C X Y Z W X' Y' Z' W'.
    intros A B C D H.
    use gradth.
    + intros ab.
      set (cd := iscontrpr1 (H (pr1 ab) (pr2 ab))). 
        exact ((pr1 ab,, (pr2 ab,, pr1 cd)),, pr2 cd).
    + intros abcd; destruct abcd as [ [a [b c] ] d]; simpl.
      use (@maponpaths _ _ 
        (fun cd : ∑ c' : C a, (D a b c') => (a,, b,, (pr1 cd)),, (pr2 cd))
        _ (_,, _)).
      apply proofirrelevancecontr, H.
    + intros ab; destruct ab as [a b]. apply idpath. }
  use (structural_lemma _ _ _ (fun _ _ _ => unit)).
(* these are all the arguments to structural_lemma 
         (obj_ext_mor X X') 
                        (fun f' => term_fun_mor Y Y' f') 
                        (fun f' => ∏ (Γ' Γ : C) (f0 : C ⟦ Γ', Γ ⟧) 
                                     (A : pr1 (pr1 (TY X) Γ)),
                                   qq (pr1 Z) f0 A ;; φ f' A =
                  φ f' (# (pr1 (TY X)) f0 A) ;; Δ
                                           (toforallpaths
                                              (λ _ : pr1 (pr1 (TY X) Γ), pr1 (pr1 (TY X') Γ'))
                                              (λ x : pr1 (pr1 (TY X) Γ),
                                               (pr1 (obj_ext_mor_TY f')) Γ'
                                                 (# (pr1 (TY X)) f0 x))
                                              (λ x : pr1 ((pr1 (TY X)) Γ),
                                               # (pr1 (TY X')) f0
                                                 ((pr1 (obj_ext_mor_TY f')) Γ x))
                                              (nat_trans_ax
                                                 (obj_ext_mor_TY f') Γ Γ' f0)
                                              A) ;; 
                  qq (pr1 Z') f0 ((pr1 (obj_ext_mor_TY f')) Γ A))
                        (fun _ _ _ => unit) ).
*)
  intros FX FY. apply iscontraprop1.
  - exact (qq_from_term_mor_unique FY W W').
  - exact (qq_from_term_mor FY W W').
Qed.

(* TODO: could strengthen to “explicitly essentially surjective” *)
Lemma compat_structures_pr2_ess_surj
  : essentially_surjective (compat_structures_pr2_functor).
Proof.
  unfold essentially_surjective.
  intros XZ; destruct XZ as [X Z]; apply hinhpr.
  exists ((X,,(term_from_qq Z,, Z)),,iscompatible_term_from_qq Z).
  apply identity_z_iso.
Qed.

Lemma compat_structures_pr2_fully_faithful
  : fully_faithful (compat_structures_pr2_functor).
Proof.
  intros XYZW XYZW';
  destruct XYZW as [ [X [Y Z] ] W];
  destruct XYZW' as [ [X' [Y' Z'] ] W'].
  unfold compat_structures_pr2_functor; simpl.
  assert (structural_lemma :
    ∏ A (B C : A -> UU) (D : ∏ a, B a -> C a -> UU)
      (H : ∏ a c, iscontr (∑ b, D a b c)),
    isweq (fun abcd : ∑ (abc : ∑ a, (B a × C a)),
                        D (pr1 abc) (pr1 (pr2 abc)) (pr2 (pr2 abc))
            => (pr1 (pr1 abcd),, pr2 (pr2 (pr1 abcd))))).
  { clear C X Y Z W X' Y' Z' W'.
    intros A B C D H.
    use gradth.
    + intros ac.
      set (bd := iscontrpr1 (H (pr1 ac) (pr2 ac))). 
        exact ((pr1 ac,, (pr1 bd,, pr2 ac)),, pr2 bd).
    + intros abcd; destruct abcd as [ [a [b c] ] d]; simpl.
      use (@maponpaths _ _ 
        (fun bd : ∑ b' : B a, (D a b' c) => (a,, (pr1 bd),, c),, (pr2 bd))
        _ (_,, _)).
      apply proofirrelevancecontr, H.
    + intros ac; destruct ac as [a c]. apply idpath. }
  use (structural_lemma _ _ _ (fun _ _ _ => unit)).
  intros FX FY. apply iscontraprop1.
  - exact (term_from_qq_mor_unique FY W W').
  - exact (term_from_qq_mor FY W W').
Qed.

End Strucs_Equiv_Precats.

Section Strucs_Disp_Equiv.

Lemma compat_structures_pr1_ess_split
  : disp_functor_disp_ess_split_surj (compat_structures_pr1_disp_functor).
Proof.
  unfold disp_functor_disp_ess_split_surj.
  intros X Y.
  exists ((Y,, qq_from_term Y),,iscompatible_qq_from_term Y).
  apply identity_z_iso_disp.
Defined.

Lemma compat_structures_pr1_ff
  : disp_functor_ff (compat_structures_pr1_disp_functor).
Proof.
  intros X X' YZW YZW'.
  destruct YZW as [ [Y Z] W].
  destruct YZW' as [ [Y' Z'] W'].
  unfold compat_structures_pr1_functor; simpl.
  intros FX.
  assert (structural_lemma :
    ∏ (B C : UU) (D : B -> C -> UU)
      (H : ∏ b, iscontr (∑ c, D b c)),
    isweq (fun bcd : ∑ (bc : B × C), D (pr1 bc) (pr2 bc)
            => pr1 (pr1 bcd))).
    clear C X Y Z W X' Y' Z' W' FX.
  { intros B C D H.
    use gradth.
    + intros b.
      set (cd := iscontrpr1 (H b)). 
        exact ((b,,pr1 cd),, pr2 cd).
    + intros bcd; destruct bcd as [ [b c] d]; simpl.
      use (@maponpaths _ _ 
        (fun cd : ∑ c', (D b c') => (b,, (pr1 cd)),, (pr2 cd))
        _ (_,, _)).
      apply proofirrelevancecontr, H.
    + intros b; apply idpath. }
  use (structural_lemma _ _ (fun _ _  => unit)).
  intros FY. apply iscontraprop1.
  - exact (qq_from_term_mor_unique FY W W').
  - exact (qq_from_term_mor FY W W').
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
         (term_fun_disp_cat C) compat_structures_disp_cat.
Proof.
  exact (equiv_inv _ (compat_structures_pr1_is_equiv_over_id)).
Defined.

Lemma compat_structures_pr2_ess_split
  : disp_functor_disp_ess_split_surj (compat_structures_pr2_disp_functor).
Proof.
  unfold disp_functor_disp_ess_split_surj.
  intros X Z.
  exists ((term_from_qq Z,, Z),,iscompatible_term_from_qq Z).
  apply identity_z_iso_disp.
Defined.

Lemma compat_structures_pr2_ff
  : disp_functor_ff (compat_structures_pr2_disp_functor).
Proof.
  intros X X' YZW YZW'.
  destruct YZW as [ [Y Z] W].
  destruct YZW' as [ [Y' Z'] W'].
  unfold compat_structures_pr1_functor; simpl.
  intros FX.
  assert (structural_lemma :
    ∏ (B C : UU) (D : B -> C -> UU)
      (H : ∏ c, iscontr (∑ b, D b c)),
    isweq (fun bcd : ∑ (bc : B × C), D (pr1 bc) (pr2 bc)
            => pr2 (pr1 bcd))).
    clear C X Y Z W X' Y' Z' W' FX.
  { intros B C D H.
    use gradth.
    + intros c.
      set (bd := iscontrpr1 (H c)). 
        exact ((pr1 bd,,c),, pr2 bd).
    + intros bcd; destruct bcd as [ [b c] d]; simpl.
      use (@maponpaths _ _ 
        (fun bd : ∑ b', (D b' c) => ((pr1 bd),, c),, (pr2 bd))
        _ (_,, _)).
      apply proofirrelevancecontr, H.
    + intros c; apply idpath. }
  use (structural_lemma _ _ (fun _ _ => unit)).
  intros FY. apply iscontraprop1.
  - exact (term_from_qq_mor_unique FY W W').
  - exact (term_from_qq_mor FY W W').
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
         (qq_structure_disp_cat C) compat_structures_disp_cat.
Proof.
  exact (equiv_inv _ (compat_structures_pr2_is_equiv_over_id)).
Defined.

End Strucs_Disp_Equiv.

Section Strucs_Fiber_Equiv.

Context (X : obj_ext_cat C).

Definition term_struc_to_qq_struc_fiber_functor
  : functor
      (fiber_category (term_fun_disp_cat C) X)
      (fiber_category (qq_structure_disp_cat C) X).
Proof.
  eapply functor_composite.
  - eapply fiber_functor.
    exact compat_structures_pr1_inverse_over_id.
    (* TODO: make lemma [fiber_disp_functor_id] *)
  - exact (fiber_functor compat_structures_pr2_equiv_over_id X).
Defined.

Definition term_struc_to_qq_struc_is_equiv
  : adj_equivalence_of_cats
      term_struc_to_qq_struc_fiber_functor.
Proof.
  use comp_adj_equivalence_of_cats.
  - apply fiber_equiv.
    apply is_equiv_of_equiv_over_id.
  - apply fiber_equiv.
    apply is_equiv_of_equiv_over_id.
Defined.

End Strucs_Fiber_Equiv.


Section Strucs_Total_Equiv.

Definition cwf'_struc_to_sty'_struc_is_equiv
  : adj_equiv
      (cwf'_structure_precat C)
      (sty'_structure_precat C).
Proof.
  eapply compose_adj_equiv.
  - eapply inv_adj_equiv, total_equiv_over_id.
    apply compat_structures_pr1_equiv_over_id.
  - eapply total_equiv_over_id.
    apply compat_structures_pr2_equiv_over_id.
Defined.

End Strucs_Total_Equiv.

End Fix_Context.

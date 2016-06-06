(**

 Ahrens, Lumsdaine, Voevodsky, 2015 - 2016

*)

Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.CategoryTheory.UnicodeNotations.

Require Import Systems.Auxiliary.
Require Import Systems.UnicodeNotations.
Require Import Systems.Bicats.Auxiliary.
Require Import Systems.Bicats.Displayed_Precats.
Require Import Systems.Structures.
Require Import Systems.Structures_Cats.
Require Import Systems.Structures_Equiv_Cats.

Local Set Automatic Introduction.
(* only needed since imports globally unset it *)

Undelimit Scope transport.

Section Fix_Context.

Context {C : Precategory}.

Local Notation hsC := (homset_property C).

Local Notation "'Yo'" := (yoneda C hsC).
Local Notation "'Yo^-1'" :=  (invweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ ))).

Local Notation "Γ ◂ A" := (comp_ext _ Γ A) (at level 30).
Local Notation "'Ty'" := (fun X Γ => (TY X : functor _ _) Γ : hSet) (at level 10).

Local Notation Δ := comp_ext_compare.
Local Notation φ := obj_ext_mor_φ.

Theorem is_category_obj_ext
  : is_category (obj_ext_Precat C).
Proof.
  split. Focus 2. apply homset_property.
  intros a b. simpl in *. unfold obj_ext_structure in a, b.
  admit.
  (* Probably the hardest *)
Admitted.

(* TODO: move *) 
Lemma isaprop_whatever
  (x : obj_ext_Precat C)
  (d d' : (families_disp_precat C) x)
  : isaprop (iso_disp (identity_iso x) d d').
Proof.
  apply isofhleveltotal2.
  - apply isaprop_families_mor.
  - intro. apply isaprop_is_iso_disp.
Qed.

(* TODO: move *) 
Definition pr1_transportf_prime :
 ∀ (A : UU) (a a' : A) (e : a = a') (B : A → UU) (P : ∀ a : A, B a → UU) 
        (xs : Σ b : B a, P a b),
       pr1 (transportf (λ x : A, Σ b : B x, P x b) e xs) =
       transportf (λ x : A, B x) e (pr1 xs).
Proof.
  intros.
  apply pr1_transportf.
Defined.

(* TODO: move *) 
Lemma transportf_const (A B : UU) (a a' : A) (e : a = a') (b : B) :
   transportf (fun _ => B) e b = b.
Proof.
  induction e.
  apply idpath.
Qed.

(* TODO: write access functions for [iso_disp], [is_iso_disp].  Maybe make [pr1] from [iso_disp] a coercion. *)

(* TODO: move! *)
Lemma transportf_families_mor_TM
  {X X' : obj_ext_Precat C} {F F' : X ⇒ X'} (e : F = F')
  {Y : families_disp_precat C X} {Y'} (FY : Y ⇒[F] Y')
  : families_mor_TM (transportf _ e FY) = families_mor_TM FY.
Proof.
  destruct e; apply idpath.
Qed.

Definition iso_disp_to_TM_eq
  (X : obj_ext_Precat C)
  (Y Y' : (families_disp_precat C) X)
  : iso_disp (identity_iso X) Y Y'
  -> TM (Y : families_structure _ X) = TM (Y' : families_structure _ X).
Proof.
  intro i.
  use isotoid.
  - apply (is_category_functor_category _ _ is_category_HSET).
  - exists (families_mor_TM (pr1 i)).
    apply is_iso_from_is_z_iso.
    exists (families_mor_TM (pr1 (pr2 i))).
    split.
    + set (XR' := maponpaths families_mor_TM (pr2 (pr2 (pr2 i)))).
      etrans. apply XR'. clear XR'.
      apply transportf_families_mor_TM.
    + set (XR' := maponpaths families_mor_TM (pr1 (pr2 (pr2 i)))).
      etrans. apply XR'. clear XR'.
      apply transportf_families_mor_TM.
Defined.

(* TODO: check more thoroughly if this is provided in the library; if so, use the library version, otherwise move this upstream.  Cf. also https://github.com/UniMath/UniMath/issues/279 *)
Lemma inv_from_iso_from_is_z_iso {D: precategory} {a b : D}
  (f: a --> b) (g : b --> a) (H : is_inverse_in_precat f g)
: inv_from_iso (f ,, (is_iso_from_is_z_iso _ (g ,, H))) 
  = g.
Proof.
  cbn. apply id_right.
Qed.

(* Left-handed counterpart to [transportf_isotoid], which could be called [prewhisker_isotoid] analogously — neither of these is a fully general transport lemma, they’re about specific cases.

  TODO: look for dupes in library; move; consider naming conventions; rename D to C. *)
Lemma postwhisker_isotoid {D : precategory} (H : is_category D)
    {a b b' : D} (f : a --> b) (p : iso b b')
  : transportf (fun b0 => a --> b0) (isotoid _ H p) f
  = f ;; p.
Proof.
  rewrite <- idtoiso_postcompose.
  apply maponpaths, maponpaths, idtoiso_isotoid.
Qed.

Lemma prewhisker_iso_disp_to_TM_eq 
  {X} {Y Y' : families_disp_precat C X}
  (FG : iso_disp (identity_iso X) Y Y')
  {P : preShv C} (α : TM (Y : families_structure _ X) ⇒ P)
: transportf (λ P' : preShv C, P' ⇒ P) (iso_disp_to_TM_eq _ _ _ FG) α
  = families_mor_TM (pr1 (pr2 FG)) ;; α.
Proof.
  etrans. apply transportf_isotoid.
  apply maponpaths_2.
  apply inv_from_iso_from_is_z_iso.
Qed.

Lemma postwhisker_iso_disp_to_TM_eq 
  {X} {Y Y' : families_disp_precat C X}
  (FG : iso_disp (identity_iso X) Y Y')
  {P : preShv C} (α : P ⇒ TM (Y : families_structure _ X))
: transportf (λ P' : preShv C, P ⇒ P') (iso_disp_to_TM_eq _ _ _ FG) α
  = α ;; families_mor_TM (pr1 FG).
Proof.
  apply postwhisker_isotoid.
Qed.

Definition iso_to_id__families_disp_precat
  (X : obj_ext_Precat C)
  (Y Y' : families_disp_precat C X)
  : iso_disp (identity_iso _) Y Y' -> Y = Y'.
Proof.
  intros i.
  apply subtypeEquality. { intro. apply isaprop_families_structure_axioms. }
  apply total2_paths with (iso_disp_to_TM_eq _ _ _ i).
  etrans. refine (transportf_dirprod _ _ _ _ _ _).
  apply dirprodeq; simpl.
  - etrans. apply prewhisker_iso_disp_to_TM_eq.
    etrans. apply families_mor_pp.
    exact (id_right (pp _)).
  - etrans. refine (transportf_forall _ _ _).
    apply funextsec; intros Γ.
    etrans. refine (transportf_forall _ _ _).
    apply funextsec; intros A.
    etrans. refine (postwhisker_iso_disp_to_TM_eq i (Q _ _)).
    etrans. apply families_mor_Q.
    etrans. Focus 2. exact (id_left (Q _ A)).
    apply maponpaths_2. apply functor_id.
Qed.

Theorem is_category_families_structure
  : is_category_disp (families_disp_precat C).
Proof.
  apply is_category_disp_from_fibers.
  intros x d d'.
  match goal with [|- @isweq ?XX ?YY ?ff ] =>
      set (X:=XX); set (Y := YY); set (f := ff) end.
  admit.
  (* Probably also not easy; [isaprop_families_mor] should be helpful. *)
Admitted.


Lemma isaset_qq_morphism_structure (x : obj_ext_structure C) 
  : isaset (qq_morphism_structure x).
Proof.
  apply (isofhleveltotal2 2).
  - apply (isofhleveltotal2 2).
    + do 4 (apply impred; intro).
      apply Precategories.homset_property.
    + intros. do 4 (apply impred; intro).
      apply (isofhleveltotal2 2).
      * apply hlevelntosn.
        apply Precategories.homset_property.
      * intro. apply hlevelntosn.
        apply pullbacks.isaprop_isPullback.
  - intro d. unfold qq_morphism_axioms.
    apply isofhleveldirprod.
    + do 2 (apply impred; intro).
      apply hlevelntosn.
      apply Precategories.homset_property.
    + do 6 (apply impred; intro).
      apply hlevelntosn.
      apply Precategories.homset_property.
Qed. 

Lemma isaprop_iso_disp_qq_morphism_structure 
  (x : obj_ext_Precat C)
  (d d' : (qq_structure_disp_precat C) x)
  : isaprop (iso_disp (identity_iso x) d d').
Proof.
  apply (isofhleveltotal2 1).
  - do 4 (apply impred; intro).
    apply Precategories.homset_property.
  - intro. apply isaprop_is_iso_disp.
Qed.

Lemma qq_structure_eq 
  (x : obj_ext_Precat C)
  (d d' : qq_morphism_structure x)
  (H : ∀ (Γ Γ' : C) (f : Γ' ⇒ Γ) (A : (TY x : functor _ _ ) Γ : hSet), 
           qq d f A = qq d' f A)
  : d = d'.
Proof.
  apply subtypeEquality.
  { intro. apply (@isaprop_qq_morphism_axioms _  (Precategories.homset_property _ )). }
  apply subtypeEquality.
  { intro. do 4 (apply impred; intro). 
           apply isofhleveltotal2.
     + apply Precategories.homset_property.
     + intro. apply pullbacks.isaprop_isPullback.
  } 
  do 4 (apply funextsec; intro).
  apply H.
Defined.

Definition qq_structure_iso_disp_to_id
  (x : obj_ext_Precat C)
  (d d' : (qq_structure_disp_precat C) x)
  : iso_disp (identity_iso x) d d' → d = d'.
Proof.
  intro H. 
  apply qq_structure_eq.
  intros Γ Γ' f A.
  assert (XR := pr1 H); clear H.
  specialize (XR _ _ f A).
  rewrite id_right in XR.
  rewrite id_left in XR.
  etrans. apply XR.
  match goal with [|- Δ ?ee ;; _ = _ ] => set (e := ee) end.  
  simpl in e; unfold identity in e; simpl in e.
  assert (X : e = idpath _ ).
  { apply setproperty. }
  rewrite X. apply id_left.
Defined.  
  
Theorem is_category_qq_morphism
  : is_category_disp (qq_structure_disp_precat C).
Proof.
  apply is_category_disp_from_fibers.
  intros x d d'. 
  use isweqimplimpl. 
  - apply qq_structure_iso_disp_to_id.
  - apply isaset_qq_morphism_structure.
  - apply isaprop_iso_disp_qq_morphism_structure.
Defined.


Lemma isaprop_iso_disp_strucs_compat_disp_precat
  (x : total_precat (families_disp_precat C × qq_structure_disp_precat C))
  (d d' : strucs_compat_disp_precat x)
  : isaprop (iso_disp (identity_iso x) d d').
Proof.
  unfold iso_disp.
  apply isofhleveltotal2.
  - apply hlevelntosn.
    apply iscontrunit.
  - intro.
    apply isaprop_is_iso_disp.
Qed.


Definition  strucs_compat_iso_disp_to_id
  (x : total_precat (families_disp_precat C × qq_structure_disp_precat C))
  (d d' : strucs_compat_disp_precat x)
  : iso_disp (identity_iso x) d d' → d = d'.
Proof.
  intro H.
  do 4 (apply funextsec; intro).
  apply functor_category_has_homsets.
Defined.

Theorem is_category_strucs_compat
  : is_category_disp (@strucs_compat_disp_precat C).
Proof.
  apply is_category_disp_from_fibers.
  intros x d d'.
  use isweqimplimpl.
  - apply strucs_compat_iso_disp_to_id.
  - apply hlevelntosn.
    apply CwF_SplitTypeCat_Maps.isaprop_iscompatible_fam_qq.
  - apply isaprop_iso_disp_strucs_compat_disp_precat.
Defined.

End Fix_Context.
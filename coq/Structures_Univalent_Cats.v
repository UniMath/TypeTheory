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

Section move_upstream.


Definition isweqpathscomp0l {X : UU} {x x' : X} (x'' : X) (e: x = x') :
   isweq (fun (e' : x' = x'') => e @ e').
Proof.
  intros.
  apply (gradth _ (fun e'' => !e @ e'')).
  - intro p. rewrite path_assoc. rewrite pathsinv0l.
    apply idpath.
  - intro p. rewrite path_assoc. rewrite pathsinv0r.
    apply idpath.
Defined.

  
Definition rewrite_in_equivalence (A X : UU) (a a' b : A) :
  a = a' → (a' = b) ≃ X → (a = b) ≃ X.
Proof.
  intros.
  set  (H:= weqpair _ (isweqpathscomp0l b (!X0))).
  eapply weqcomp. apply H.
  apply X1.
Defined.

Definition transportf_forall_var :
  Π (A : UU) (B : A -> UU) (C : UU)
    (a1 a2 : A) (e : a1 = a2)
(f : B a1 -> C),
transportf (λ x : A, Π y : B x, C) e f =
(λ y : B a2 ,  f (transportb B e y)).
Proof.
  intros A B D a1 a2 e f.
  induction e.
  apply idpath.
Defined.

(* transportf_forall *)

Definition transportf_forall_var2 :
  Π (A : UU) (B C : A -> UU) 
    (a1 a2 : A) (e : a1 = a2)
    (f : B a1 -> C a1),
transportf (λ x : A, Π y : B x, C x) e f =  
(λ y : B a2 , transportf _ e (f (transportb B e y))).
Proof.
  intros A B D a1 a2 e f.
  induction e.
  apply idpath.
Defined.

(* TODO: check more thoroughly if this is provided in the library; if so, use the library version, otherwise move this upstream.  Cf. also https://github.com/UniMath/UniMath/issues/279 *)
Lemma inv_from_iso_from_is_z_iso {D: precategory} {a b : D}
  (f: a --> b) (g : b --> a) (H : is_inverse_in_precat f g)
: inv_from_iso (f ,, (is_iso_from_is_z_iso _ (g ,, H))) 
  = g.
Proof.
  cbn. apply id_right.
Qed.


(* A slightly surprising but very useful lemma for characterising identity types.

Concisely: to show that a family of functions [w : forall a b, a = b -> P a b] are equivalences, it’s enough to show they have a retraction; the retraction is then automatically a quasi-inverse, because of the fact that the coconut is contractible.
 
Often one can save a bit of work with this (since the other direction of inverseness may not be so obvious in individual cases).

TODO: move; consider naming; see if this can be used to simplify other proofs of [is_category] and similar? *)
Lemma eq_equiv_from_retraction {A} {P : A -> A -> UU} 
    (w : forall a b, a = b -> P a b)
    (v : forall a b, P a b -> a = b)
  : (forall a b (p : P a b), w _ _ (v _ _ p) = p)
  -> forall a b, isweq (w a b).
Proof.
  intros wv a.
  apply isweqtotaltofib. (* first of the two key steps *)
  use gradth.
  - intros bp. exists (pr1 bp). apply v, (pr2 bp).
  - intros be; apply connectedcoconusfromt. (* the second key step *)
  - intros bp. use total2_paths. apply idpath. apply wv.
Qed.

End move_upstream.


Section Fix_Context.

Context {C : Precategory}.

Local Notation hsC := (homset_property C).

Local Notation "'Yo'" := (yoneda C hsC).
Local Notation "'Yo^-1'" :=  (invweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ ))).

Local Notation "Γ ◂ A" := (comp_ext _ Γ A) (at level 30).
Local Notation "'Ty'" := (fun X Γ => (TY X : functor _ _) Γ : hSet) (at level 10).

Local Notation Δ := comp_ext_compare.
Local Notation φ := obj_ext_mor_φ.

(* does not line up with identity 
Definition obj_ext_iso_alt (X X' : obj_ext_Precat C) : UU :=
  Σ F_TY : iso (TY X) (TY X'),
        Π {Γ:C} {A : Ty X Γ},
         Σ φ : iso (Γ ◂ A) (Γ ◂ ((pr1 F_TY : nat_trans _ _) _ A)),
           φ ;; π _ = π A.
 *)

Definition obj_ext_iso_alt (X X' : obj_ext_Precat C) : UU :=
  Σ F_TY : iso (TY X) (TY X'),
        Π {Γ:C} {A' : Ty X' Γ},
         Σ φ : iso (Γ ◂ ((inv_from_iso F_TY) : nat_trans _ _ ) _ A') (Γ ◂  A'),
           φ ;; π _ = π _ .

Search (is_category _ ).

Definition is_saturated_preShv (F G : preShv C) : F = G ≃ iso F G.
Proof.
  apply (weqpair idtoiso (pr1
                            (is_category_functor_category _ _ is_category_HSET) _ _ )).
Defined.  





Definition weq_eq_obj_ext_iso_alt (X X' : obj_ext_Precat C) :
  (X = X') ≃ obj_ext_iso_alt X X'.
Proof.
  eapply weqcomp. apply total2_paths_equiv.
  
  set (H := is_saturated_preShv (TY X) (TY X')).
  use (weqbandf H).
  intro F. simpl.
(*  rewrite transportf_forall. (* do better *) *)
  Search ( ( _ = _ ) ≃ (Π _ ,  _ )).
  eapply weqcomp. apply weqtoforallpaths.
  Search ( (forall _ , _ ) ≃ (forall _ , _ )).
  apply weqonsecfibers.
  intro Γ.
  eapply weqcomp. apply weqtoforallpaths. simpl.
  apply weqonsecfibers.
  intro A'.
  eapply weqcomp. apply total2_paths_equiv.
  simpl.
(*  rewrite transportf_forall. *)
  use weqbandf. simpl.
  - 
    set (RX := @transportf_forall).
    specialize (RX (preShv C) C).
    specialize (RX (fun F Γ' => ((F:functor _ _ ) Γ' : hSet) → Σ ΓA : C, ΓA ⇒ Γ')).
    simpl in RX.
    specialize (RX _ _ F).
    rewrite RX.
    simpl.
    clear RX.
    rewrite transportf_forall_var.

    simpl. cbn.
 
  admit.
Admitted.

(* TODO: above here and below here are two mostly separate approaches to [is_category_obj_ext].  Once one is complete, most of the other can probably be pruned *)

(* TODO: move*)
Definition obj_ext_to_preShv_functor_data
  : functor_data (obj_ext_Precat C) (preShv C).
Proof.
  use tpair.
  apply pr1.
  simpl; intros X X'; apply pr1.
Defined.

(* TODO: move *)
Definition obj_ext_to_preShv_functor_axioms
  : is_functor obj_ext_to_preShv_functor_data.
Proof.
  split; intro; intros; apply idpath.
Qed.

(* TODO: move; rename to [obj_ext_TY_functor]? *)
Definition obj_ext_to_preShv_functor
  : functor (obj_ext_Precat C) (preShv C)
:= (_ ,, obj_ext_to_preShv_functor_axioms).



Definition transportf_obj_ext
  {T T' : preShv C} (e : T = T')
  (extn : Π Γ : C, ((T : functor _ _) Γ : hSet) → Σ ΓA : C, ΓA ⇒ Γ) 
: transportf _ e extn
  = fun Γ A => extn Γ ((inv_from_iso (idtoiso e) : nat_trans _ _) Γ A).
Proof.
  destruct e; cbn. apply idpath.
Defined.

Lemma obj_ext_mor_TY_eq {X X' : obj_ext_Precat C}
  {F F' : X ⇒ X'} (E : F = F')
  {Γ} (A : Ty X Γ)
: (obj_ext_mor_TY F : nat_trans _ _) _ A
  = (obj_ext_mor_TY F' : nat_trans _ _) _ A.
Proof.
  destruct E; apply idpath.
Qed.

Lemma obj_ext_mor_φ_eq {X X' : obj_ext_Precat C}
  {F F' : X ⇒ X'} (E : F = F')
  {Γ} (A : Ty X Γ)
: φ F A ;; Δ (obj_ext_mor_TY_eq E A)
  = φ F' A.
Proof.
  destruct E.
  etrans. apply maponpaths, comp_ext_compare_id_general.
  apply id_right.
Qed.

Definition iso_to_obj_ext_eq (H : is_category C)
  {X X' : obj_ext_Precat C}
: (iso X X') -> (X = X').
Proof.
  intros F.
  apply (total2_paths (isotoid _
    (is_category_functor_category _ _ is_category_HSET)
    (functor_on_iso obj_ext_to_preShv_functor F))).
  etrans. apply transportf_obj_ext.
  apply funextsec; intro Γ; apply funextsec; intro A.
  rewrite idtoiso_isotoid.
  etrans.
  { apply maponpaths.
    refine (toforallpaths _ _ _ _ A).
    refine (toforallpaths _ _ _ _ Γ).
    eapply pathsinv0, maponpaths.
    refine (maponpaths pr1 (functor_on_iso_inv _ _ obj_ext_to_preShv_functor _ _ _)).
  }
  set (F' := inv_from_iso F).
  set (FF' := iso_after_iso_inv F).
  set (F'F := iso_inv_after_iso F).
  simpl.
  (* Now we break out a proof-irrelevant subproof needed later.  By breaking it out _before_ [use total2_paths], we ensure that this large subterm only occurs once in the proof term; this saves c.30s at the [Defined.] 

  For reading: skip this subproof block for now, then imagine it inlined at [exact H'] below. *)
  assert (H' : is_inverse_in_precat
     (φ _ ((obj_ext_mor_TY (inv_from_iso F) : nat_trans _ _) Γ A)
       ;; Δ (obj_ext_mor_TY_eq FF' A))
     (φ (inv_from_iso F) A)).
  { split.
    * etrans. eapply pathsinv0, assoc.
      etrans. apply maponpaths, Δ_φ.
      etrans. apply assoc.
      etrans. Focus 2. apply (obj_ext_mor_φ_eq F'F).
      cbn. apply maponpaths.
      apply maponpaths, setproperty.
    * etrans. apply assoc.
      apply (obj_ext_mor_φ_eq FF').
  }
  use total2_paths.
  use isotoid. assumption.
  exists (φ (F : _ ⇒ _) _ ;; Δ (obj_ext_mor_TY_eq FF' _)).
  + simpl. apply is_iso_from_is_z_iso.
    exists (φ _ _). exact H'.
  + etrans. apply transportf_isotoid.
    etrans. apply maponpaths_2. 
      apply inv_from_iso_from_is_z_iso.
    apply obj_ext_mor_ax.
Defined.

(* TODO: inline *)
Lemma foo {X X' : obj_ext_Precat C} (e : X = X')
  {Γ} (A : Ty X Γ)
: comp_ext X Γ A
  ⇒ comp_ext X' Γ ((obj_ext_mor_TY (idtoiso e : X ⇒ X') : nat_trans _ _) _ A).
Proof.
  Unset Printing Notations.
  revert Γ A.
  set (e' := (fiber_paths e)). simpl in e'.
  assert (H : (fun Γ (A : Ty X' Γ)
                => pr2 X Γ (transportb (fun (T : functor C^op hset_precategory) => T Γ : hSet) (base_paths X X' e) A))
              = pr2 X').
  { etrans. Focus 2. apply e'.
    apply pathsinv0.
    etrans. refine (transportf_forall _ _ _). simpl.
    apply funextsec; intros Γ.
    apply (transportf_forall_var _
     (fun (T : functor C^op hset_precategory) => T Γ : hSet)).
  }
  intros Γ A; simpl in A. 
  refine (_ ;; _).
    Focus 2. eapply idtoiso.
    refine (maponpaths pr1 (toforallpaths _ _ _
              (toforallpaths _ _ _ H Γ) _)).
  apply Δ. destruct e; apply idpath.
  Set Printing Notations.
Defined.

Lemma funextsec_idpath (T : UU) (P : T -> UU) (f : forall t, P t)
  : funextsec P f f (fun t => idpath _) = idpath _.
Proof.
  (* equal since they become equal after applying [toforallpaths], which is an equivalence and hence injective *)
Admitted.

(* TODO: name *)
Lemma foo2 {X X' : obj_ext_Precat C} (e : X = X')
  {Γ} (A : Ty X Γ)
: φ (idtoiso e : _ ⇒ _) A = foo e A.
Proof.
  (* should be trivial once [foo] is defined correctly: *)
  destruct e. cbn. apply pathsinv0.
  unfold foo. cbn. 
  etrans. apply id_left. 
  rewrite funextsec_idpath; apply idpath.
Qed.

Theorem is_category_obj_ext (H : is_category C)
  : is_category (obj_ext_Precat C).
Proof.
  split. Focus 2. apply homset_property.
  apply (eq_equiv_from_retraction _ (@iso_to_obj_ext_eq H)). 
  intros X X' F.
  apply eq_iso.
  apply obj_ext_mor_eq'.
  - intros Γ; apply toforallpaths; revert Γ; apply toforallpaths.
    apply maponpaths.
    refine (@maponpaths _ _ pr1
      (functor_on_iso (obj_ext_to_preShv_functor) _)
      (functor_on_iso _ _) _).
    etrans. apply @pathsinv0, maponpaths_idtoiso.
    etrans. apply maponpaths, base_total2_paths.
    apply (idtoiso_isotoid _ _ _ _ _).
  - intros e_TY Γ A.
    etrans. apply maponpaths_2. apply foo2. unfold foo.
    etrans. apply maponpaths_2. apply maponpaths.
    eapply (maponpaths pr1).
    (* lemma foo2 above: [φ] of an [idtoiso] is… what? *) 
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
 Π (A : UU) (a a' : A) (e : a = a') (B : A → UU) (P : Π a : A, B a → UU) 
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
  {X : obj_ext_Precat C}
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
  intros X.
  apply eq_equiv_from_retraction with iso_to_id__families_disp_precat.
  - intros. apply eq_iso_disp, isaprop_families_mor.
Qed.

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
  (H : Π (Γ Γ' : C) (f : Γ' ⇒ Γ) (A : (TY x : functor _ _ ) Γ : hSet), 
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
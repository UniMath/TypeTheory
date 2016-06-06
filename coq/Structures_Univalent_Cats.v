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
  ∀ (A : UU) (B : A -> UU) (C : UU)
    (a1 a2 : A) (e : a1 = a2)
(f : B a1 -> C),
transportf (λ x : A, ∀ y : B x, C) e f =
(λ y : B a2 ,  f (transportb B e y)).
Proof.
  intros A B D a1 a2 e f.
  induction e.
  apply idpath.
Defined.

(* transportf_forall *)

Definition transportf_forall_var2 :
  ∀ (A : UU) (B C : A -> UU) 
    (a1 a2 : A) (e : a1 = a2)
    (f : B a1 -> C a1),
transportf (λ x : A, ∀ y : B x, C x) e f =  
(λ y : B a2 , transportf _ e (f (transportb B e y))).
Proof.
  intros A B D a1 a2 e f.
  induction e.
  apply idpath.
Defined.

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
        ∀ {Γ:C} {A : Ty X Γ},
         Σ φ : iso (Γ ◂ A) (Γ ◂ ((pr1 F_TY : nat_trans _ _) _ A)),
           φ ;; π _ = π A.
 *)

Definition obj_ext_iso_alt (X X' : obj_ext_Precat C) : UU :=
  Σ F_TY : iso (TY X) (TY X'),
        ∀ {Γ:C} {A' : Ty X' Γ},
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
  Search ( ( _ = _ ) ≃ (∀ _ ,  _ )).
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
  

Theorem is_category_obj_ext
  : is_category (obj_ext_Precat C).
Proof.
  split. Focus 2. apply homset_property.
  intros a b. simpl in *. unfold obj_ext_structure in a, b.
  admit.
  (* Probably the hardest *)
Admitted.


Lemma isaprop_whatever
  (x : obj_ext_Precat C)
  (d d' : (families_disp_precat C) x)
  : isaprop (iso_disp (identity_iso x) d d').
Proof.
  apply isofhleveltotal2.
  - apply isaprop_families_mor.
  - intro. apply isaprop_is_iso_disp.
Qed.

Definition pr1_transportf_prime :
 ∀ (A : UU) (a a' : A) (e : a = a') (B : A → UU) (P : ∀ a : A, B a → UU) 
        (xs : Σ b : B a, P a b),
       pr1 (transportf (λ x : A, Σ b : B x, P x b) e xs) =
       transportf (λ x : A, B x) e (pr1 xs).
Proof.
  intros.
  apply pr1_transportf.
Defined.

Lemma transportf_const (A B : UU) (a a' : A) (e : a = a') (b : B) :
   transportf (fun _ => B) e b = b.
Proof.
  induction e.
  apply idpath.
Qed.

Definition iso_disp_to_TM_eq
  (x : obj_ext_Precat C)
  (d d' : (families_disp_precat C) x)
  : iso_disp (identity_iso x) d d' -> TM (d : families_structure _ x) = TM (d' : families_structure _ x) .
Proof.
  intro i.
  use isotoid.
  - apply (is_category_functor_category _ _ is_category_HSET).
  - exists (pr1 (pr1 i)).
    apply is_iso_from_is_z_iso.
    exists (pr1 (pr1 (pr2 i))).
    split.
    + set (XR' := maponpaths pr1 (pr2 (pr2 (pr2 i)))).
      etrans. apply XR'. clear XR'.
      simpl.  unfold transportb.     
      match goal with |[|- pr1 (transportf ?PP ?HH ?ee) = _ ] => 
           set (P := PP); set (eq := HH); set (e := ee) end.
      etrans.
      set (XR:= pr1_transportf_prime _ _ _ eq). simpl in *.
      set (XR' := mor_disp (d : (families_disp_precat C) x) d).
      specialize (XR (λ f : obj_ext_mor x x, TM d ⇒ TM d)). simpl in XR.
      specialize (XR (fun (f :  obj_ext_mor x x) (tm : (TM d) ⇒ (TM d)) 
                        =>
                          tm ;; pp d = pp d ;; obj_ext_mor_TY f
         × (∀ (Γ : C) (A : (TY x : functor _ _ ) Γ : hSet),
            Q d A ;; tm =
            # (yoneda C hsC) (φ f A) ;; Q d ((obj_ext_mor_TY f : nat_trans _ _ ) Γ A)))).
      apply XR.
      apply transportf_const.
    + set (XR' := maponpaths pr1 (pr1 (pr2 (pr2 i)))).
      etrans. apply XR'.
      clear XR'.
      unfold transportb.     
      match goal with |[|- pr1 (transportf ?PP ?HH ?ee) = _ ] => 
           set (P := PP); set (eq := HH); set (e := ee) end.
      etrans.
      set (XR:= pr1_transportf_prime _ _ _ eq).
      set (XR' := mor_disp (d' : (families_disp_precat C) x) d').
      simpl in d'.
      specialize (XR (λ f : obj_ext_mor x x, TM (d' : families_structure _ x) ⇒ TM (d' : families_structure _ _ ))). 
      specialize (XR (fun (f :  obj_ext_mor x x) (tm : (TM d') ⇒ (TM d')) 
                        =>
                          tm ;; pp d' = pp d' ;; obj_ext_mor_TY f
         × (∀ (Γ : C) (A : (TY x : functor _ _ ) Γ : hSet),
            Q d' A ;; tm =
            # (yoneda C hsC) (φ f A) ;; Q d' ((obj_ext_mor_TY f : nat_trans _ _ ) Γ A)))).
      apply XR.
      apply transportf_const.
Defined.

    
    

Definition iso_to_id__families_disp_precat
  (x : obj_ext_Precat C)
  (d d' : (families_disp_precat C) x)
  : iso_disp (identity_iso x) d d' -> d = d'.
Proof.
  intro i.
  apply subtypeEquality.
  { intro. apply isaprop_families_structure_axioms. }
  use total2_paths.
  - apply (iso_disp_to_TM_eq _ _ _ i).
  - etrans.
    set (XR:= transportf_dirprod).
    specialize (XR (preShv C)).
    specialize (XR (fun x0 => x0 ⇒ TY x)).
    apply XR.
(* not necessary, found automatically
  specialize (XR (fun x0 =>
           (∀ (Γ : C^op) (A : (TY x : functor _ _ ) Γ : hSet),
                 (yoneda C hsC) (comp_ext x Γ  A) ⇒ x0))).
*)
    apply dirprodeq.
    +  (* rewrite <- idtoiso_precompose. *)
      simpl.
Abort.  

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
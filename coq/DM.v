
(**

  Ahrens, Lumsdaine, Voevodsky, 2015

  Contents:

    - Definition of a (pre)category with display maps

  The definition is based on, well, what PLL told me

*)

Require Export Systems.Auxiliary.
Require Export Systems.UnicodeNotations.
Require Export UniMath.Foundations.Sets.
Require Export UniMath.CategoryTheory.precategories.
Require Export UniMath.CategoryTheory.limits.pullbacks.

Require Import UniMath.Foundations.FunctionalExtensionality.


(** * A "preview" of the definition *)

Module Record_Preview.

Reserved Notation "γ ⋆ f" (at level 25).



(** these are approximations of the access functions implemented at the end of the file 

  one difference is that actually DM is defined as the sigma type of another type

*)


Record CwDM := {
  C : precategory ;
  DM : ∀ {Δ Γ : C}, Δ ⇒ Γ → hProp ;
  pb : ∀ {Δ Γ : C} (γ : Σ f : Δ ⇒ Γ, DM f) {Γ'} (f : Γ' ⇒ Γ), C  where "γ ⋆ f" := (pb γ f) ;
  pb_DM_of_DM : ∀  {Δ Γ} (γ : Σ f : Δ ⇒ Γ, DM f) {Γ'} (f : Γ' ⇒ Γ),  Σ f : (γ⋆f) ⇒ Γ', DM f ;
  pb_arrow_of_arrow : ∀ {Δ Γ} (γ : Σ f : Δ ⇒ Γ, DM f) {Γ'} (f : Γ' ⇒ Γ),  γ⋆f ⇒ Δ ;
  sqr_comm_of_DM : ∀ {Δ Γ} (γ : Σ f : Δ ⇒ Γ, DM f) {Γ'} (f : Γ' ⇒ Γ),
                      pb_arrow_of_arrow _ _  ;; pr1 γ = pr1 (pb_DM_of_DM γ f)  ;; f ;

  isPullback_of_DM : ∀ {Δ Γ} (γ : Σ f : Δ ⇒ Γ, DM f) {Γ'} (f : Γ' ⇒ Γ),
                       isPullback  _ _ _ _ _ (sqr_comm_of_DM γ f)

}.

End Record_Preview.


(** * Definition of Display Map structure on a (pre)category *)

(** ** Predicate selecting the display maps among the arrows *)

Definition dm_sub_struct (CC : precategory)
  : UU
  := ∀ {Δ Γ : CC} , Δ ⇒ Γ → UU.

Definition DM_type {C : precategory} (H : dm_sub_struct C) {Δ Γ} (γ : Δ ⇒ Γ)
           := H Δ Γ γ.

Definition DM {C : precategory}(H : dm_sub_struct C) (Δ Γ : C) : UU :=
  Σ f : Δ ⇒ Γ, DM_type H f.

Definition DM_over {C : precategory}(H : dm_sub_struct C) (Γ : C) : UU :=
  Σ (Δf : Σ Δ, Δ ⇒ Γ), DM_type H (pr2 Δf).

Definition ob_from_DM_over {C : precategory} {H : dm_sub_struct C} {Γ : C}
           (X : DM_over H Γ) : C := pr1 (pr1 X).

Definition DM_from_DM_over {C : precategory} {H : dm_sub_struct C} {Γ : C}
  (X : DM_over H Γ) : DM H (ob_from_DM_over  X) Γ.
Proof.
  exists (pr2 (pr1 X)).
  exact (pr2 X).
Defined.

Coercion arrow_from_DM {C : precategory} (H : dm_sub_struct C)(Δ Γ : C) (δ : DM H Δ Γ) : Δ ⇒ Γ := pr1 δ.

(** ** Display maps are closed under iso *)
(** Here, isomorphism means isomorphism in the slice category of the target object.
    Alternatively and equivalently, one could consider isomorphism in the arrow category?
*)

Definition dm_sub_closed_under_iso {CC : precategory} (C : dm_sub_struct CC)
  : UU
  := ∀ Δ Γ (γ : DM C Δ Γ),
                          ∀ Δ' (δ : Δ' ⇒ Γ), 
                          ∀ (h : iso Δ Δ'), h ;; δ = γ → DM_type C δ.


(** ** Display maps are closed under pullback *)
(**  i.e., the pullback of a display map
       exists and is again a display map
*)
(**

[[
  __________Γ
 |          |
 |          | γ ∈ DM
 |____f_____|Γ'
 Δ         

]]

*)


Definition pb_of_DM_struct {CC : precategory} (H : dm_sub_struct CC)
: UU
  := ∀ Δ Γ (γ : DM H Δ Γ), ∀ Γ' (f : Γ' ⇒ Γ),
       Σ P : Pullback _ γ f, DM_type H (PullbackPr1 _ P).

(*
Definition pb_type_of_DM {CC : precategory} (H : dm_sub_struct CC)
           {Δ Γ} (γ : DM H Δ Γ) {Γ'} (f : Γ' ⇒ Γ)
  : UU
  := 
    Σ (pfg : Σ Δ' : CC, Δ' ⇒ Δ × DM H Δ' Γ') (H : pr1 (pr2 pfg);; γ = pr2 (pr2 pfg);; f),
           isPullback _ _ _  (pr1 (pr2 pfg)) (pr2 (pr2 pfg)) H .
 *)

(*
Definition Pullback_of_pb_type {CC : precategory} (sat : is_category CC) (H : dm_sub_struct CC)
      {Δ Γ} (γ : DM H Δ Γ) {Γ'} (f : Γ' ⇒ Γ)
:  pb_type_of_DM _ γ f → Pullback _ γ f.
Proof.
  intros [[P [f' g]] p]; simpl in *.
  refine (tpair _ _ _ ).
  - exists P.
    exists f'.
    exact g.
  - simpl. exact p.
Defined.  
*)
(*
Search (isofhlevel _ _ -> isofhlevel _ _ ).
*)

(*
Definition pb_type_of_DM_weq_Pb {CC : precategory} (sat : is_category CC) (H : dm_sub_struct CC)
      {Δ Γ} (γ : DM H Δ Γ) {Γ'} (f : Γ' ⇒ Γ)
:  (∀ Γ Γ' (γ : Γ ⇒ Γ'), isaprop (DM_type H γ)) →
   isaprop (pb_type_of_DM _ γ f).
Proof.
  intros.
  apply invproofirrelevance.
  intros Pb Pb'.
  apply total2_paths_isaprop.
  - intro; apply isofhleveltotal2.
    + apply (pr2 sat).
    + intros; apply isaprop_isPullback.
  - apply (total2_paths (isotoid _ sat (iso_from_Pullback_to_Pullback _ Pb Pb' ))).
    rewrite transportf_dirprod, transportf_isotoid.
    rewrite inv_from_iso_iso_from_Pullback.
    rewrite transportf_isotoid.
    rewrite inv_from_iso_iso_from_Pullback.
    destruct Pb as [Cone bla];
    destruct Pb' as [Cone' bla'];
    simpl in ×.
    destruct Cone as [p [h k]];
    destruct Cone' as [p' [h' k']];
    simpl in ×.
    unfold from_Pullback_to_Pullback;
    rewrite PullbackArrow_PullbackPr2, PullbackArrow_PullbackPr1.
    apply idpath.
 *)

(*
Definition pb_type_of_DM_weq_Pb {CC : precategory} (sat : is_category CC) (H : dm_sub_struct CC)
      {Δ Γ} (γ : DM H Δ Γ) {Γ'} (f : Γ' ⇒ Γ)
:  (∀ Γ Γ' (γ : Γ ⇒ Γ'), isaprop (DM_type H γ)) →
   isaprop (pb_type_of_DM _ γ f).
Proof.
  intros.
  intros a b.
  apply (isofhlevelsninclb _ (Pullback_of_pb_type sat H γ f)).
  unfold isincl.
  unfold isofhlevelf.
  intro x.
  unfold hfiber.
  apply invproofirrelevance.
  intros P P'.
  apply total2_paths_second_isaprop.
  + apply isapropifcontr. apply isaprop_Pullback. assumption.
  + destruct P as [P PX]; destruct P' as [P' PX']. simpl in *.
    apply total2_paths_second_isaprop.
    * apply (isofhleveltotal2). apply (pr2 sat).
      intros. apply isaprop_isPullback.
    *  assert (A :  Pullback_of_pb_type sat H γ f P =  Pullback_of_pb_type sat H γ f P').
       { etrans. apply PX. sym. apply PX'. }
       clear PX. clear PX'.
       assert (T := maponpaths (pr1) A).
       clear X. clear x. clear A.
       simpl in *.
      destruct P as [P1 X1 ]. simpl.
      destruct P' as [P1' X1']. simpl in *.  
      refine (total2_paths _ _  ).
      apply (maponpaths).
      refine (total2_paths _ _ ).
      revert T.
      destruct P1 as [P1 P2].
      destruct P1' as [P1' P2']. simpl in *.
      apply (maponpaths _ T) .
      clear X1.
      clear PX. clear PX'.
  destruct P as [
  intros.
  intro H'.
  apply invproofirrelevance.
  intros Pb Pb'.
  apply total2_paths_isaprop.
  - intro; apply isofhleveltotal2.
    + apply (pr2 sat). 
    + intros; apply isaprop_isPullback.
  - apply (total2_paths (isotoid _ sat (iso_from_Pullback_to_Pullback _   Pb Pb' ))).
    rewrite transportf_dirprod, transportf_isotoid.
    rewrite inv_from_iso_iso_from_Pullback.
    rewrite transportf_isotoid.
    rewrite inv_from_iso_iso_from_Pullback.
    destruct Pb as [Cone bla];
    destruct Pb' as [Cone' bla'];
    simpl in ×.
    destruct Cone as [p [h k]];
    destruct Cone' as [p' [h' k']];
    simpl in ×.
    unfold from_Pullback_to_Pullback;
    rewrite PullbackArrow_PullbackPr2, PullbackArrow_PullbackPr1.
    apply idpath.
Qed.
   pb_type_of_DM _ γ f ≃ Pullback _ γ f.
Proof.
  intro H'.
  unfold pb_type_of_DM, Pullback.
  refine (weqbandf _ _ _ _ ).
  - apply weqfibtototal.
    intro Δ'.
    apply weqfibtototal.
    intro.
    exists (pr1).
    Search (isweq pr1).
    apply isweqpr1.
    
  - 
  simpl.
  eapply weqcomp.
*)
(*
Definition pb_of_DM_struct {CC : precategory} (H : dm_sub_struct CC)
: UU
  := ∀ Δ Γ (γ : DM H Δ Γ) Γ' (f : Γ' ⇒ Γ), pb_type_of_DM H γ f.
*)
(*
    Σ (pfg : Σ Δ' : CC, Δ' ⇒ Δ × DM H Δ' Γ') (H : pr1 (pr2 pfg);; γ = pr2 (pr2 pfg);; f),
           isPullback _ _ _  (pr1 (pr2 pfg)) (pr2 (pr2 pfg)) H .
 *)

Definition dm_sub_pb (CC : precategory) : UU :=
  Σ DM : dm_sub_struct CC, pb_of_DM_struct DM.

Coercion dm_sub_of_dm_sub_pb {CC : precategory} (C : dm_sub_pb CC) : dm_sub_struct CC := pr1 C.
Coercion pb_of_dm_sub_pb {CC : precategory} (C : dm_sub_pb CC) : pb_of_DM_struct C := pr2 C.


Definition pb_ob_of_DM {CC : precategory} {C : dm_sub_pb CC}
           {Δ Γ} (γ : DM C Δ Γ) {Γ'} (f : Γ' ⇒ Γ)
: CC
  := pr1 (pr1 (pr1 (pr2 C _ _ γ _  f))).

Notation "γ ⋆ f" := (pb_ob_of_DM γ f) (at level 45, format "γ ⋆ f").
(* written "\st" in Agda input mode *)
                        
Definition pb_mor_of_DM {CC : precategory} {C : dm_sub_pb CC}
           {Δ Γ} (γ : DM C Δ Γ) {Γ'} (f : Γ' ⇒ Γ)
  :  (γ⋆f) ⇒  Γ'.
Proof.
  apply (PullbackPr2 _ (pr1 (pr2 C _ _ γ _ f))).
Defined.
(*  :=  pr2 (pr2 (pr1 (pr1 (pr2 C _ _ γ _ f)))). *)

Definition pb_mor_of_mor {CC : precategory} {C : dm_sub_pb CC}
           {Δ Γ} (γ : DM C Δ Γ) {Γ'} (f : Γ' ⇒ Γ)
: γ⋆f ⇒ Δ.
Proof.
  apply (PullbackPr1 _ (pr1 (pr2 C _ _ γ _ f))).
Defined.
(* := pr1 (pr2 (pr1 (pr1 (pr2 C _ _ γ _ f)))). *)

Definition sqr_comm_of_dm_sub_pb {CC : precategory} {C : dm_sub_pb CC}
           {Δ Γ} (γ : DM C Δ Γ) {Γ'} (f : Γ' ⇒ Γ)
: _ ;; _ = _ ;; _ 
:= PullbackSqrCommutes _ (pr1 (pr2 C _ _ γ _ f )).

Definition isPullback_of_dm_sub_pb {CC : precategory} {C : dm_sub_pb CC}
           {Δ Γ} (γ : DM C Δ Γ) {Γ'} (f : Γ' ⇒ Γ)
: isPullback _ _ _ _ _ _
:=  pr2 (pr2 (pr1 (pr2 C _ _ γ _ f ))).

(*
Definition dm_closed_under_pb {CC : precategory} (C : dm_sub_pb CC)
: UU
    := ∀ Δ Γ (γ : DM C Δ Γ) Γ' (f : Γ' ⇒ Γ), DM_type C (pb_mor_of_DM γ f).
*)

(** ** DM structure: putting the pieces together *)

Definition DM_structure (CC : precategory) : UU
  := Σ C : dm_sub_pb CC,
   (*        dm_closed_under_pb C *)
          dm_sub_closed_under_iso C
        ×  ∀ Γ Γ' (γ : Γ ⇒ Γ'), isaprop (DM_type C γ).

(** ** Some access functions *)
(** Names are chosen as for the preview above *)

Coercion dm_sub_pb_from_DM_structure CC (C : DM_structure CC) : dm_sub_pb CC := pr1 C.


Definition pb_DM_of_DM {CC} {C : DM_structure CC}  {Δ Γ} (γ : DM C Δ Γ) {Γ'} (f : Γ' ⇒ Γ)
: DM C (γ⋆f) Γ'.
Proof.
  exists (pb_mor_of_DM γ f).
  apply ( pr2 (pr2 (pr1 C) _ _ γ _ f)). 
Defined.


Definition pb_arrow_of_arrow {CC} {C : DM_structure CC}  {Δ Γ} (γ : DM C Δ Γ) {Γ'} (f : Γ' ⇒ Γ)
: γ⋆f ⇒ Δ.
Proof.
  apply pb_mor_of_mor.
Defined.

Definition sqr_comm_of_DM {CC} {C : DM_structure CC}  {Δ Γ} (γ : DM C Δ Γ) {Γ'} (f : Γ' ⇒ Γ)
:  pb_arrow_of_arrow _ _  ;; γ = pb_DM_of_DM γ f  ;; f.
Proof. 
  apply sqr_comm_of_dm_sub_pb.
Defined.

Definition isPullback_of_DM {CC} {C : DM_structure CC} {Δ Γ} (γ : DM C Δ Γ) {Γ'} (f : Γ' ⇒ Γ)
: isPullback CC _ _ _ _ (sqr_comm_of_DM γ f).
Proof.
  apply isPullback_of_dm_sub_pb.
Defined.


Section lemmas.

  Definition DM_equal {CC} (H : is_category CC) (D D' : DM_structure CC)
             (X : ∀ Δ Γ (f : Δ ⇒ Γ), DM_type D f → DM_type D' f)
             (X' : ∀ Δ Γ (f : Δ ⇒ Γ), DM_type D' f → DM_type D f)
  : D = D'.
  Proof.
    apply total2_paths_second_isaprop.
    - simpl.
      apply isofhleveltotal2.
      + unfold dm_sub_closed_under_iso.
        repeat (apply impred; intro).
        apply (pr2 (pr2 D')).
      + intro.
        repeat (apply impred; intro).
        apply isapropiscontr.
    - simpl.
      destruct D as [D Dh];
        destruct D' as [D' Dh']; simpl in *.
      apply total2_paths_second_isaprop.
      + unfold pb_of_DM_struct.
        repeat (apply impred; intro).
        apply isofhleveltotal2.
        * apply isaprop_Pullback. exact H.
        * intro. apply (pr2 Dh').
      + destruct D as [D Da];
        destruct D' as [D' Da'];
        simpl in *.
        unfold dm_sub_struct in D.
        apply funextsec; intro.
        apply funextsec; intro.
        apply funextsec; intro f.
        apply univalenceaxiom.
        exists (X _ _ _).
        apply isweqimplimpl.
        * apply X'.
        * apply (pr2 Dh).
        * apply (pr2 Dh').
Defined.

End lemmas.

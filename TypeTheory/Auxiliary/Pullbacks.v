Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.All.
(* a few libraries need to be reloaded after “All”,
   to claim precedence on overloaded names *)
Require Import UniMath.CategoryTheory.limits.pullbacks.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheory.

(** * Basic pullback utility functions *)

Section Pullback_Basics.

Definition map_into_Pb
    {C : precategory} {a b c d : C}
    {f : a --> b} {g : a --> c} {k : b --> d} {h : c --> d}
    {sqr_comm : f ;; k = g ;; h}
    (Pb : isPullback sqr_comm)
    {e : C} (x : e --> b) (y : e --> c) (H : x ;; k = y ;; h)
  :  e --> a.
Proof.
  eapply (PullbackArrow (make_Pullback _ Pb)).
  apply H.
Defined.

Definition Pb_map_commutes_1
    {C : precategory} {a b c d : C}
    {f : a --> b} {g : a --> c} {k : b --> d} {h : c --> d}
    {sqr_comm : f ;; k = g ;; h}
    (Pb : isPullback sqr_comm)
    {e : C} (x : e --> b) (y : e --> c) H
  : map_into_Pb Pb x y H ;; f = x.
Proof.
  apply (PullbackArrow_PullbackPr1 (make_Pullback _ _)).
Qed.

Definition Pb_map_commutes_2
    {C : precategory} {a b c d : C}
    {f : a --> b} {g : a --> c} {k : b --> d} {h : c --> d}
    {sqr_comm : f ;; k = g ;; h}
    (Pb : isPullback sqr_comm)
    {e : C} (x : e --> b) (y : e --> c) H
  : map_into_Pb Pb x y H ;; g = y.
Proof.
  apply (PullbackArrow_PullbackPr2 (make_Pullback _ _)).
Qed.

Lemma map_into_Pb_unique
    {C : precategory} {a b c d : C}
    {f : a --> b} {g : a --> c} {k : b --> d} {h : c --> d}
    {sqr_comm : f ;; k = g ;; h}
    (Pb : isPullback sqr_comm)
    {e : C} {x y : e --> a}
    (e_f : x ;; f = y ;; f) (e_g : x ;; g = y ;; g)
  : x = y.
Proof.
  etrans.
  { use (PullbackArrowUnique _ Pb); try eassumption.
    repeat rewrite <- assoc. apply maponpaths; assumption. }
  apply pathsinv0, (PullbackArrowUnique _ Pb); apply idpath.
Qed.

(* In fact this is trivial, since the equality doesn’t appear in the type of the pullback. However, it’s convenient for proof scripts. *)
Lemma isPullback_indepdent_of_path
    {C : precategory} {a b c d : C}
    {f : a --> b} {g : a --> c} {k : b --> d} {h : c --> d}
    {sqr_comm : f ;; k = g ;; h}
    (Pb : isPullback sqr_comm)
    (sqr_comm' :  f ;; k = g ;; h)
  : isPullback (sqr_comm').
Proof.
  exact Pb.
Defined.

(* Duplicate of [is_symmetric_isPullback] from UniMath, but without the un-needed [has_homsets]/[category] assumption *)
Lemma is_symmetric_isPullback
    {C : precategory}
    {a b c d : C} {f : b --> a} {g : c --> a}
    {p1 : d --> b} {p2 : d --> c} {H : p1 · f = p2 · g}
    (pb : isPullback H)
  : isPullback (! H).
Proof.
  use make_isPullback.
  intros e h k H'.
  use (iscontrweqf _ (pb e k h (! H'))).
  use (weqtotal2 (idweq _)).
  intros ?. apply weqdirprodcomm.
Defined.

(* Variant of [is_symmetric_isPullback], more convenient for applying when reasoning bottom-up. *)
Lemma is_symmetric'_isPullback
    {C : precategory}
    {a b c d : C} {f : b --> a} {g : c --> a}
    {p1 : d --> b} {p2 : d --> c} {H : p1 · f = p2 · g}
    (pb : isPullback (! H))
  : isPullback H.
Proof.
  eapply transportf. 2: { eapply is_symmetric_isPullback, pb. }
  apply pathsinv0inv0.
Defined.

End Pullback_Basics.

(** * Pullback transfer lemmas *)

Section Pullback_transfers.
(* Various results, generally showing that perturbing a pullback squares by equalities and/or isos is still a pullback. *)

Lemma square_morphism_equal
    {C : precategory} {a b c d : C}
    {f : a --> b} {g : a --> c} {k : b --> d} {h : c --> d}
    (sqr_comm : f ;; k = g ;; h)
    {k'} (e : k' = k)
  : f ;; k' = g ;; h.
Proof.
  rewrite e. assumption.
Defined.

Lemma isPb_morphism_equal
    {C : precategory} {a b c d : C}
    {f : a --> b} {g : a --> c} {k : b --> d} {h : c --> d}
    (sqr_comm : f ;; k = g ;; h)
    (Pb : isPullback sqr_comm)
    {k'} (e : k' = k)
  : isPullback (square_morphism_equal sqr_comm e).
Proof.
  match goal with |[|- isPullback ?HH] => generalize HH end.
  rewrite e.
  intro.
  apply Pb.
Defined.

Definition commutes_and_is_pullback {C : category} {a b c d : C}
    (f : b --> a) (g : c --> a) (p1 : d --> b) (p2 : d --> c)
  : UU
:= ∑ (H : p1 ;; f = p2 ;; g), isPullback H.

(* Note: should have a dual version where [i_a], instead of [i_d], is assumed iso (and using [post_comp_with_iso_is_inj] in the proof). *)
Lemma commuting_square_transfer_z_iso {C : precategory}
      {a b c d : C}
      {f : b --> a} {g : c --> a} {p1 : d --> b} {p2 : d --> c}
      {a' b' c' d' : C}
      {f' : b' --> a'} {g' : c' --> a'} {p1' : d' --> b'} {p2' : d' --> c'}
      {i_a : a --> a'} {i_b : b --> b'} {i_c : c --> c'} {i_d : z_iso d d'}
      (i_f : f ;; i_a = i_b ;; f') (i_g : g ;; i_a = i_c ;; g')
      (i_p1 : p1 ;; i_b = i_d ;; p1') (i_p2 : p2 ;; i_c = i_d ;; p2')
   : p1 ;; f = p2;; g
   -> p1' ;; f' = p2' ;; g'.
Proof.
  intro H.
  refine (pre_comp_with_z_iso_is_inj i_d _ _ _).
  rewrite 2 assoc.
  rewrite <- i_p1, <- i_p2.
  rewrite <- 2 assoc.
  rewrite <- i_f, <- i_g.
  rewrite 2 assoc.
  apply maponpaths_2, H.
Qed.

(* Generalisation of [isPulback_iso_of_morphisms].
TODO: This probably should work in an arbitrary precategory, i.e. not requiring the hom-sets assumption.  Try upgrading proof to show that? *)
Lemma isPullback_transfer_z_iso {C : category}
      {a b c d : C}
      {f : b --> a} {g : c --> a} {p1 : d --> b} {p2 : d --> c}
      (H : p1 ;; f = p2;; g)
      {a' b' c' d' : C}
      {f' : b' --> a'} {g' : c' --> a'} {p1' : d' --> b'} {p2' : d' --> c'}
      (H' : p1' ;; f' = p2' ;; g')
      {i_a : z_iso a a'} {i_b : z_iso b b'} {i_c : z_iso c c'} {i_d : z_iso d d'}
      (i_f : f ;; i_a = i_b ;; f') (i_g : g ;; i_a = i_c ;; g')
      (i_p1 : p1 ;; i_b = i_d ;; p1') (i_p2 : p2 ;; i_c = i_d ;; p2')
   : isPullback H
   -> isPullback H'.
Proof.
  intros Hpb.
  apply (make_isPullback _ ).    
  intros X h k H''.
  simple refine (tpair _ _ _ ).
  - simple refine (tpair _ _ _ ).
    { refine ( _ ;; i_d ).
      simple refine (PullbackArrow (make_Pullback _ Hpb) _ _ _ _).
      + exact (h ;; z_iso_inv_from_z_iso i_b).
      + exact (k ;; z_iso_inv_from_z_iso i_c).
      + abstract (
          apply (post_comp_with_z_iso_is_inj i_a _);
          repeat rewrite <- assoc;
          rewrite i_f, i_g;
          eapply @pathscomp0;
          [ apply maponpaths; rewrite assoc;
            apply maponpaths_2, z_iso_after_z_iso_inv
          | eapply @pathsinv0, @pathscomp0;
          [ apply maponpaths; rewrite assoc;
            apply maponpaths_2, z_iso_after_z_iso_inv
          | rewrite 2 id_left; apply @pathsinv0, H''
          ]]
        ).
    }
    cbn; split;
    abstract (
      rewrite <- assoc;
      eapply @pathscomp0;
      [ apply maponpaths, @pathsinv0;
        try apply i_p2; try apply i_p1
      | rewrite assoc;
      eapply @pathscomp0;
      [ apply maponpaths_2;
        try apply (PullbackArrow_PullbackPr2 (make_Pullback _ _));
        try apply (PullbackArrow_PullbackPr1 (make_Pullback _ _))
      | rewrite <- assoc, z_iso_after_z_iso_inv; apply id_right]] ).
  - intros hk'.
    apply subtypePath.
      intro; apply isapropdirprod; apply homset_property.
    cbn.
    apply (post_comp_with_z_iso_is_inj (z_iso_inv_from_z_iso i_d)).
    eapply @pathscomp0.
    2: { rewrite <- assoc. cbn. rewrite z_iso_inv_after_z_iso.
         eapply pathsinv0, id_right. }
    apply PullbackArrowUnique; cbn.
    + apply (post_comp_with_z_iso_is_inj i_b).
      repeat rewrite <- assoc.
      rewrite i_p1, z_iso_after_z_iso_inv, id_right.
      eapply @pathscomp0.
        apply maponpaths. rewrite assoc, z_iso_after_z_iso_inv. apply id_left.
      apply (pr1 (pr2 hk')).
    + apply (post_comp_with_z_iso_is_inj i_c).
      repeat rewrite <- assoc.
      rewrite i_p2, z_iso_after_z_iso_inv, id_right.
      eapply @pathscomp0.
        apply maponpaths. rewrite assoc, z_iso_after_z_iso_inv. apply id_left.
      apply (pr2 (pr2 hk')).
  Qed.

(* Generalisation of [isPulback_iso_of_morphisms]. *)
Lemma commutes_and_is_pullback_transfer_z_iso {C : category}
      {a b c d : C}
      {f : b --> a} {g : c --> a} {p1 : d --> b} {p2 : d --> c}
      {a' b' c' d' : C}
      {f' : b' --> a'} {g' : c' --> a'} {p1' : d' --> b'} {p2' : d' --> c'}
      {i_a : z_iso a a'} {i_b : z_iso b b'} {i_c : z_iso c c'} {i_d : z_iso d d'}
      (i_f : f ;; i_a = i_b ;; f') (i_g : g ;; i_a = i_c ;; g')
      (i_p1 : p1 ;; i_b = i_d ;; p1') (i_p2 : p2 ;; i_c = i_d ;; p2')
      (H : p1 ;; f = p2 ;; g) (P : isPullback H)
   : commutes_and_is_pullback f' g' p1' p2'.
Proof.
  exists (commuting_square_transfer_z_iso i_f i_g i_p1 i_p2 H).
  exact (isPullback_transfer_z_iso _ _ i_f i_g i_p1 i_p2 P).
Qed.

Lemma postcomp_commutes_and_is_pb_with_z_iso
    {C : category} {a b c d : C}
    {f : a --> b} {g : a --> c} {k : b --> d} {h : c --> d}
    (sqr_comm : f ;; k = g ;; h)
    (Pb : isPullback sqr_comm)
    {y : C} (r : y --> d) (i : z_iso b y) (Hi : i ;; r = k)
  : ∑ H : f ;; i ;; r = g ;; h, isPullback H.
Proof.
  simple refine (commutes_and_is_pullback_transfer_z_iso _ _ _ _ _ Pb);
    try apply identity_z_iso;
    try rewrite id_left;
    try rewrite id_right;
    try apply idpath.
  apply pathsinv0, Hi.
Qed.

Definition postcomp_pb_with_z_iso
    {C : category} {a b c d : C}
    {f : a --> b} {g : a --> c} {k : b --> d} {h : c --> d}
    (sqr_comm : f ;; k = g ;; h)
    (Pb : isPullback sqr_comm)
    {y : C} (r : y --> d) (i : z_iso b y) (Hi : i ;; r = k)
  : isPullback _
:= pr2 (postcomp_commutes_and_is_pb_with_z_iso _ Pb _ i Hi).

End Pullback_transfers.

(** * Uniqueness of pullbacks *)

Definition isaprop_Pullback (C : category) (H : is_univalent C)
           (a b c : C) (f : b --> a) (g : c --> a)
: isaprop (Pullback f g).
Proof.
  unfold Pullback.
  apply invproofirrelevance.
  unfold Pullback.
  intros Pb Pb'.
  apply subtypePath.
  - intro; apply isofhleveltotal2.
    + apply homset_property.
    + intros; apply isaprop_isPullback.
  - apply (total2_paths_f (isotoid _ H (z_iso_from_Pullback_to_Pullback _ _))).
    rewrite transportf_dirprod, transportf_isotoid.
    rewrite inv_from_z_iso_z_iso_from_Pullback.
    rewrite transportf_isotoid.
    rewrite inv_from_z_iso_z_iso_from_Pullback.
    destruct Pb as [Cone bla];
    destruct Pb' as [Cone' bla'];
    simpl in *.
    destruct Cone as [p [h k]];
    destruct Cone' as [p' [h' k']];
    simpl in *. 
    unfold from_Pullback_to_Pullback;
    rewrite PullbackArrow_PullbackPr2, PullbackArrow_PullbackPr1.
    apply idpath.
Qed.

(* TODO: check for results of the following section upstream *)
Section Pullback_Unique_Up_To_Iso.

(*   a'   b'
      f  /h
   a----b  b'
   |    |
 g |    | k
   |    |
   c----d
     j 

   and pb square a' b' c d, and h iso
    
   task: construct iso from a to a'

 *)
  
  Variable CC : category.
  Variables A B C D A' B' : CC.
  Variables (f : A --> B) (g : A --> C) (k : B --> D) (j : C --> D)
            (H : f ;; k = g ;; j) (pb : isPullback H).
  Variables (f' : A' --> B') (g' : A' --> C) (r : B' --> D) (h : z_iso B B').
  Variable (H' : f' ;; r = g' ;; j).
  Variable (pb' : isPullback H').
  Variable (T : h ;; r = k).

  Definition map_to_2nd_pb : A --> A'.
  Proof.
    use (map_into_Pb pb').
    - exact (f ;; h).
    - exact g.
    - eapply pathscomp0. 2: { apply H. }
      eapply pathscomp0. apply (!assoc _ _ _ ).
      apply maponpaths. apply T.
  Defined.

  Definition map_to_1st_pb : A' --> A.
  Proof.
    use (map_into_Pb pb).
    - exact (f';; inv_from_z_iso h).
    - exact g'.
    - eapply pathscomp0; [| apply H'].
      eapply pathscomp0; [ apply (!assoc _ _ _ ) |].
      apply maponpaths. apply z_iso_inv_on_right.
      apply (!T).
  Defined.

  Lemma inv1 : map_to_2nd_pb ;; map_to_1st_pb = identity _ .
  Proof.
    apply (map_into_Pb_unique pb).
    - rewrite id_left.
      rewrite <- assoc.
      unfold map_to_1st_pb.
      rewrite Pb_map_commutes_1.
      rewrite assoc.
      apply pathsinv0.
      apply z_iso_inv_on_left.
      unfold map_to_2nd_pb.
      use Pb_map_commutes_1.
    - rewrite id_left.
      rewrite <- assoc.
      unfold map_to_1st_pb.
      rewrite Pb_map_commutes_2.
      unfold map_to_2nd_pb.
      apply Pb_map_commutes_2.
  Qed.

  Lemma inv2 : map_to_1st_pb ;; map_to_2nd_pb = identity _ .
  Proof.
    apply (map_into_Pb_unique pb').
    - rewrite id_left.
      rewrite <- assoc.
      unfold map_to_2nd_pb.
      rewrite Pb_map_commutes_1.
      rewrite assoc.
      unfold map_to_1st_pb.
      rewrite Pb_map_commutes_1.
      rewrite <- assoc.
      rewrite z_iso_after_z_iso_inv.
      apply id_right.
    - rewrite id_left.
      rewrite <- assoc.
      unfold map_to_2nd_pb.
      rewrite Pb_map_commutes_2.
      unfold map_to_1st_pb.
      apply Pb_map_commutes_2.
  Qed.

  Definition z_iso_to_second_pb : z_iso A A'.
  Proof.
    exists map_to_2nd_pb.
    exists map_to_1st_pb.
    split.
    - apply inv1.
    - apply inv2.
  Defined.

End Pullback_Unique_Up_To_Iso.


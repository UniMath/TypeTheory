
(** 

 Ahrens, Lumsdaine, Voevodsky 2015

Auxiliary background lemmas for the Ahrens/Lumsdaine/Voevodsky “Systems” project.  
Possibly some should be upstreamed to “UniMath” eventually.

*)


Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.limits.limits.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.yoneda.

Require Import Systems.UnicodeNotations.

(** Redeclare this notation, along with a new scope. *)
Notation "ff ;; gg" := (compose ff gg)
  (at level 50, left associativity, format "ff  ;;  gg")
  : mor_scope.
Delimit Scope mor_scope with mor.
Bind Scope mor_scope with precategory_morphisms.
Open Scope mor_scope.

(** * Lemmas about identity etc *)

Lemma pr1_transportf (A : UU) (B : A -> UU) (P : ∀ a, B a -> UU)
   (a a' : A) (e : a = a') (xs : Σ b : B a, P _ b):
   pr1 (transportf (fun x => Σ b : B x, P _ b) e xs) = 
     transportf (fun x => B x) e (pr1 xs).
Proof.
  induction e.
  apply idpath.
Defined.

Lemma maponpaths_eq_idpath : ∀ (T1 T2 : UU) (f : T1 -> T2) (t1 : T1) (e : t1 = t1)
          (H : e = idpath _ ), 
                                 maponpaths f e = idpath _ .
Proof.
  intros.
  rewrite H.
  apply idpath.
Defined.

(** Useful lemma for binary functions, generalising e.g. [cancel_postcomposition]. 

TODO: look carefully for this in the library *)
Definition maponpaths_2 {X Y Z : Type} (f : X -> Y -> Z) {x x'} (e : x = x') y
  : f x y = f x' y
:= maponpaths (fun x => f x y) e.

(* TODO: SURELY this is in the library!? *)
Lemma pathscomp0_assoc {A : UU} {a b c d : A}(e : a = b) (e' : b = c) (e'' : c = d) 
  : (e @ e') @ e'' = e @ (e' @ e'').
Proof.
  destruct e.
  apply idpath.
Defined.
  

Lemma transportf_comp_lemma (X : UU) (B : X -> UU) {A A' A'': X} (e : A = A'') (e' : A' = A'')
  (x : B A) (x' : B A')
  : transportf _ (e @ !e') x = x'
  -> transportf _ e x = transportf _ e' x'.
Proof.
  intro H.
  eapply pathscomp0. Focus 2.
    apply maponpaths. exact H.
  eapply pathscomp0. Focus 2.
    symmetry. apply transport_f_f.
  apply (maponpaths (fun p => transportf _ p x)).
  apply pathsinv0.
  eapply pathscomp0.
  - apply pathscomp0_assoc. 
  - eapply pathscomp0. 
    apply maponpaths.
    apply pathsinv0l.
    apply pathscomp0rid.
Qed.

Lemma transportf_comp_lemma_hset (X : UU) (B : X -> UU) (A : X) (e : A = A)
  {x x' : B A} (hs : isaset X)
  : x = x'
  -> transportf _ e x = x'.
Proof.
  intros ex.
  apply @pathscomp0 with (transportf _ (idpath _) x).
    apply (maponpaths (fun p => transportf _ p x)).
    apply hs.
  exact ex.
Qed.

Lemma transportf_ext (X : UU) (B : X -> UU) (A A' : X) (e e' : A = A') p :
  e = e' -> transportf _ e p = transportf B e' p.
Proof.
  intro H; induction H; apply idpath.
Defined.



(** * Lemmas/definitions on (pre)categories *)

Definition preShv C := functor_precategory C^op HSET (pr2 is_category_HSET).

(* TODO: perhaps rename e.g. [yoneda_eq]? *)
Definition yy {C : precategory} {hsC : has_homsets C}
  {F : preShv C} {c : C} : ((F : functor _ _) c : hSet) ≃ _ ⟦ yoneda _ hsC c, F⟧.
Proof.
  apply invweq.
  apply yoneda_weq.
Defined.

Arguments yy {_ _ _ _}.

Lemma yy_natural {C : precategory} {hsC : has_homsets C}
  (F : preShv C) (c : C) (A : (F:functor _ _) c : hSet) 
                  c' (f : C⟦c', c⟧) :
        yy (# (F : functor _ _) f A) = # (yoneda _ hsC) f ;; yy A.
Proof.
  assert (XTT := is_natural_yoneda_iso_inv _ hsC F _ _ f).
  apply (toforallpaths _ _ _ XTT).
Qed.

Lemma idtoiso_concat_pr (C : precategory) (a a' a'' : ob C)
  (p : a = a') (q : a' = a'') :
  idtoiso p ;; idtoiso q = idtoiso (p @ q).
Proof.
  apply pathsinv0.
  apply (base_paths _ _ (idtoiso_concat _ _ _ _ _ _ )).
Defined.

Lemma idtoiso_eq_idpath (C : precategory) (a : C) (e : a = a)
    (H : e = idpath _ )
  : identity a = idtoiso e.
Proof.
  rewrite H.
  apply idpath.
Qed.

Lemma cancel_postcomposition {C : precategory} {a b c : C} (f f' : a ⇒ b) (g : b ⇒ c)
: f = f' -> f ;; g = f' ;; g.
Proof.
  intro H. apply (maponpaths (fun f => f ;; g) H).
Defined.

Lemma idtoiso_postcompose_idtoiso_pre {C : precategory} {a b c : C} (g : a ⇒ b) (f : a ⇒ c)
              (p : b = c) :
  g = f ;; idtoiso (!p) -> g ;; idtoiso p = f.
Proof.
  induction p. simpl.
  rewrite id_right.
  induction 1.
  apply id_right.
Qed.


(** ** Lemmas on pullbacks *)

Section on_pullbacks.

  Variable C : precategory.
  Variable hs : has_homsets C.
  Variables a b c d : C.
  Variables (f : a ⇒ b) (g : a ⇒ c) (k : b ⇒ d) (h : c ⇒ d).

(*
      f
   a----b
 g |    | k
   |    |
   c----d
     h 
    
 *)

  Variable sqr_comm : f ;; k = g ;; h.
  Variable Pb : isPullback _ _ _ _ sqr_comm.

  Local Definition Pbb : Pullback k h.
  Proof.
    unshelve refine (mk_Pullback _ _ _ _ _ _ _ ).
      - apply a.
      - apply f.
      - apply g.
      - apply sqr_comm.
      - apply Pb.
  Defined.
  
  Definition map_into_Pb {e : C} (x : e ⇒ b) (y : e ⇒ c)
  :  x ;; k = y ;; h → e ⇒ a.
  Proof.
    intro H.
    unshelve refine (PullbackArrow Pbb _ _ _ _ ).
    - apply x.
    - apply y.
    - apply H.
  Defined.
      
  Definition Pb_map_commutes_1 {e : C} (x : e ⇒ b) (y : e ⇒ c) H
  : map_into_Pb x y H ;; f = x.
  Proof.
    assert (P:=PullbackArrow_PullbackPr1 Pbb).
    apply P.
  Qed.

  Definition Pb_map_commutes_2 {e : C} (x : e ⇒ b) (y : e ⇒ c) H
  : map_into_Pb x y H ;; g = y.
  Proof.
    assert (P:=PullbackArrow_PullbackPr2 Pbb).
    apply P.
  Qed.

  Lemma map_into_Pb_unique (e : C) (x y : e ⇒ a)
  : x ;; f = y ;; f → x ;; g = y ;; g → x = y.
  Proof.
    intros H H'.
    set (T:=@map_into_Pb _ (x ;; f)(y ;; g)).
    assert  (TH : x ;; f ;; k = y ;; g ;; h).
    { rewrite H. repeat rewrite <- assoc. rewrite sqr_comm. apply idpath. }
    pathvia (T TH).
    apply PullbackArrowUnique. apply idpath. assumption.
    apply pathsinv0. apply PullbackArrowUnique. apply pathsinv0; assumption.
    apply idpath.
  Qed.

  Lemma postcomp_pb_with_iso (y : C) (r : y ⇒ d) (i : iso b y) (Hi : i ;; r = k) :
    Σ H : f ;; i ;; r = g ;; h, isPullback _ _ _ _ H.
  Proof.
    unshelve refine (tpair _ _ _ ).
    { eapply pathscomp0 ; [|apply sqr_comm].
      eapply pathscomp0. eapply pathsinv0; apply assoc.
      apply maponpaths. apply Hi.
    }
    apply (mk_isPullback _ ).    
    intros e s t HH.
    unshelve refine (tpair _ _ _ ).
    - unshelve refine (tpair _ _ _ ).
      set (T:= @map_into_Pb e).
      set (T':= T (s ;; inv_from_iso i) t).
      apply T'. { rewrite <- HH. rewrite <- assoc. apply maponpaths.
                  apply iso_inv_on_right. apply pathsinv0; assumption. }
                simpl.
      split.
      + assert (T1:= @Pb_map_commutes_1).
        eapply pathscomp0. apply assoc.
        rewrite T1.
        rewrite <- assoc.
        rewrite iso_after_iso_inv.
        apply id_right.
      + apply Pb_map_commutes_2.
    - intro t0.
      apply subtypeEquality.
      + intro. apply isapropdirprod; apply hs.
      + simpl.
        destruct t0 as [w [Ht1 Ht2]]; simpl in *.
        apply PullbackArrowUnique.
        * apply iso_inv_on_left.
          rewrite <- Ht1. apply assoc.
        * assumption.
Defined.    
 
End on_pullbacks.

Arguments map_into_Pb {_ _ _ _ _ _ _ _ _ } _ _ {_} _ _ _ .
Arguments map_into_Pb_unique {_ _ _ _ _ _ _ _ _} _ _ {_} _ _ _ _   .

Section Pullback_HSET.

(* TODO: does this already exist?

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

End Pullback_HSET.

(**
will be an instance of a general lemma to be proved
   in UniMath
*)
Definition isaprop_Pullback (C : precategory) (H : is_category C)
           (a b c : C) (f : b ⇒ a) (g : c ⇒ a)
: isaprop (Pullback f g).
Proof.
  unfold Pullback.
  apply invproofirrelevance.
  unfold Pullback.
  intros Pb Pb'.
  apply subtypeEquality.
  - intro; apply isofhleveltotal2.
    + destruct H as [H1 H2]. apply H2.
    + intros; apply isaprop_isPullback.
  - apply (total2_paths  (isotoid _ H (iso_from_Pullback_to_Pullback Pb Pb' ))). 
    rewrite transportf_dirprod, transportf_isotoid.
    rewrite inv_from_iso_iso_from_Pullback.
    rewrite transportf_isotoid.
    rewrite inv_from_iso_iso_from_Pullback.
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


Section bla.


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
  
  Variable CC : precategory.
  Variables A B C D A' B' : CC.
  Variables (f : A ⇒ B) (g : A ⇒ C) (k : B ⇒ D) (j : C ⇒ D) (H : f ;; k = g ;; j)
            (pb : isPullback _ _ _ _ H).
  Variables (f' : A' ⇒ B') (g' : A' ⇒ C) (r : B' ⇒ D) (h : iso B B').
  Variable (H' : f' ;; r = g' ;; j).
  Variable (pb' : isPullback _ _ _ _ H').
  Variable (T : h ;; r = k).

  Definition map_to_2nd_pb : A ⇒ A'.
  Proof.
    unshelve refine (map_into_Pb H' pb' _ _ _  ).
    - exact (f ;; h).
    - exact g.
    - eapply pathscomp0. Focus 2. apply H.
      eapply pathscomp0. apply (!assoc _ _ _ _ _ _ _ _ ).
      apply maponpaths. apply T.
  Defined.

  Definition map_to_1st_pb : A' ⇒ A.
  Proof.
    unshelve refine (map_into_Pb H pb _ _ _ ).
    - exact (f';; inv_from_iso h).
    - exact g'.
    - eapply pathscomp0; [| apply H'].
      eapply pathscomp0; [ apply (!assoc _ _ _ _ _ _ _ _) |].
      apply maponpaths. apply iso_inv_on_right.
      apply (!T).
  Defined.

  Lemma inv1 : map_to_2nd_pb ;; map_to_1st_pb = identity _ .
  Proof.
    apply (map_into_Pb_unique  H pb).
    - rewrite id_left.
      rewrite <- assoc.
      unfold map_to_1st_pb.
      rewrite Pb_map_commutes_1.
      rewrite assoc.
      apply pathsinv0.
      apply iso_inv_on_left.
      unfold map_to_2nd_pb.
      match goal with |[ |- map_into_Pb ?H1 ?pb1 ?x1 ?y1 ?R1 ;; _ = _ ] => assert
           (T1:=@Pb_map_commutes_1 _ _ _ _ _ _ _ _ _ H' pb' _ x1 y1 R1) end.
      apply T1.
    - rewrite id_left.
      rewrite <- assoc.
      unfold map_to_1st_pb.
      rewrite Pb_map_commutes_2.
      unfold map_to_2nd_pb.
      apply Pb_map_commutes_2.
Qed.

   Lemma inv2 : map_to_1st_pb ;; map_to_2nd_pb = identity _ .
  Proof.
    apply (map_into_Pb_unique  H' pb').
    - rewrite id_left.
      rewrite <- assoc.
      unfold map_to_2nd_pb.
      rewrite Pb_map_commutes_1.
      rewrite assoc.
      unfold map_to_1st_pb.
      rewrite Pb_map_commutes_1.
      rewrite <- assoc.
      rewrite iso_after_iso_inv.
      apply id_right.
    - rewrite id_left.
      rewrite <- assoc.
      unfold map_to_2nd_pb.
      rewrite Pb_map_commutes_2.
      unfold map_to_1st_pb.
      apply Pb_map_commutes_2.
Qed.

Definition iso_to_second_pb : iso A A'.
Proof.
  exists map_to_2nd_pb.
  simple refine (is_iso_qinv _ map_to_1st_pb _ ).
  split.
  - apply inv1.
  - apply inv2.
Defined.

End bla.
  

Arguments map_into_Pb {_ _ _ _ _} _ _ _ _ _ _ {_} _ _ _ .
Arguments Pb_map_commutes_1 {_ _ _ _ _} _ _ _ _ _ _ {_} _ _ _ .
Arguments Pb_map_commutes_2 {_ _ _ _ _} _ _ _ _ _ _ {_} _ _ _ .

(** * Some tactics *)

Tactic Notation "etrans" := eapply pathscomp0.
Tactic Notation "rew_trans_@" := repeat (etrans ; [ apply transport_f_f |]).
Tactic Notation "sym" := apply pathsinv0.
Tactic Notation "assoc" := apply pathscomp0_assoc.
Tactic Notation "cancel_postcomposition" := apply cancel_postcomposition.

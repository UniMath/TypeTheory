(** * Systems.Auxiliary *)
(** Auxiliary background lemmas for the Ahrens/Lumsdaine/Voevodsky “Systems” project.  Possibly some should be upstreamed to “UniMath” eventually.
*)

Require Import UniMath.Foundations.Generalities.uu0.
Require Import UniMath.RezkCompletion.precategories.
Require Import Systems.UnicodeNotations.
Require Import UniMath.RezkCompletion.limits.pullbacks.

Lemma maponpaths_eq_idpath : ∀ (T1 T2 : UU) (f : T1 → T2) (t1 : T1) (e : t1 = t1)
          (H : e = idpath _ ), 
                                 maponpaths f e = idpath _ .
Proof.
  intros.
  rewrite H.
  apply idpath.
Defined.

Lemma idtoiso_concat_pr (C : precategory) (hs: has_homsets C) (a a' a'' : ob C)
  (p : a = a') (q : a' = a'') :
  idtoiso p ;; idtoiso q = idtoiso (p @ q).
Proof.
  apply pathsinv0.
  apply (base_paths _ _ (idtoiso_concat _ hs _ _ _ _ _ )).
Defined.

Lemma idtoiso_eq_idpath (C : precategory) (a : C) (e : a = a)
    (H : e = idpath _ )
  : identity a = idtoiso e.
Proof.
  rewrite H.
  apply idpath.
Qed.

Section on_pullbacks.

  Variable C : precategory.
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
  Variable Pb : isPullback _ _ _ _ _ sqr_comm.

  Definition map_into_Pb {e : C} (x : e ⇒ b) (y : e ⇒ c)
      :  x ;; k = y ;; h → e ⇒ a
    := fun H => pr1 (pr1 (Pb _ x y H)).

  Definition Pb_map_commutes_1 {e : C} (x : e ⇒ b) (y : e ⇒ c) H
  : map_into_Pb x y H ;; f = x
    := (pr1 (pr2 (pr1 (Pb _ x y H)))).
  

  Definition Pb_map_commutes_2 {e : C} (x : e ⇒ b) (y : e ⇒ c) H
  : map_into_Pb x y H ;; g = y
    := (pr2 (pr2 (pr1 (Pb _ x y H)))).

End on_pullbacks.

Arguments map_into_Pb {_ _ _ _ _} _ _ _ _ _ _ {_} _ _ _ .
Arguments Pb_map_commutes_1 {_ _ _ _ _} _ _ _ _ _ _ {_} _ _ _ .
Arguments Pb_map_commutes_2 {_ _ _ _ _} _ _ _ _ _ _ {_} _ _ _ .

(* (Surprised there’s no library function for this!) *)
Lemma transportf_pathscomp0 {A} {B} {a a' a'' : A} (e : a = a') (e' : a' = a'') (b : B a)
  : transportf B e' (transportf B e b) = transportf B (pathscomp0 e e') b.
Proof.
  destruct e; apply idpath.
Defined.

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
    symmetry. apply transportf_pathscomp0.
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


Lemma cancel_postcomposition {C : precategory} {a b c : C} (f f' : a ⇒ b) (g : b ⇒ c)
: f = f' -> f ;; g = f' ;; g.
Proof.
  intro H. apply (maponpaths (fun f => f ;; g) H).
Defined.


Tactic Notation "etrans" := eapply pathscomp0.
Tactic Notation "rew_trans_@" := repeat (etrans ; [ apply transportf_pathscomp0 |]).
Tactic Notation "sym" := apply pathsinv0.
Tactic Notation "assoc" := apply pathscomp0_assoc.
Tactic Notation "cancel_postcomposition" := apply cancel_postcomposition.
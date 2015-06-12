(** * Systems.Auxiliary *)
(** Auxiliary background lemmas for the Ahrens/Lumsdaine/Voevodsky “Systems” project.  Possibly some should be upstreamed to “UniMath” eventually.
*)

Require Import UniMath.Foundations.Generalities.uu0.

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

Tactic Notation "etrans" := eapply pathscomp0.
Tactic Notation "rew_trans_@" := repeat (etrans ; [ apply transportf_pathscomp0 |]).
Tactic Notation "sym" := apply pathsinv0.
Tactic Notation "assoc" := apply pathscomp0_assoc.

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

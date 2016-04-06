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
  admit.
  (* Probably the hardest *)
Admitted.

Theorem is_category_families_structure
  : is_category_disp (families_disp_precat C).
Proof.
  apply is_category_disp_from_fibers.
  admit.
  (* Probably also not easy; [isaprop_families_mor] should be helpful. *)
Admitted.

Theorem is_category_qq_morphism
  : is_category_disp (qq_structure_disp_precat C).
Proof.
  apply is_category_disp_from_fibers.
  admit.
  (* Hopefully easier, since both sides of this equivalence are obviously hprops. *)
Admitted.

Theorem is_category_strucs_compat
  : is_category_disp (@strucs_compat_disp_precat C).
Proof.
  apply is_category_disp_from_fibers.
  admit.
  (* Should be very easy. *)
Admitted.

End Fix_Context.
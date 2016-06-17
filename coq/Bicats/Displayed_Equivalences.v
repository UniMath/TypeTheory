(**
A module for “displayed precategories”, based over UniMath’s [CategoryTheory] library.

Roughly, a “displayed category _D_ over a precategory _C_” is analogous to “a family of types _Y_ indexed over a type _X_”.  A displayed category has a “total category” Σ _C_ _D_, with a functor to _D_; and indeed displayed categories should be equivalent to categories over _D_, by taking fibres.

In a little more detail: if [D] is a displayed precategory over [C], then [D] has a type of objects indexed over [ob C], and for each [x y : C, f : x ⇒ y, xx : D x, yy : D y], a type of “morphisms over [f] from [xx] to [yy]”.  The identity and composition (and axioms) for [D] all overlie the corresponding structure on [C].

Two major motivations for displayed categories:

- Pragmatically, they give a convenient tool for building categories of “structured objects”, and functors into such categories, encapsulating a lot of frequently-used contstructions.
- More conceptually, they give a setting for defining Grothendieck fibrations and isofibrations without mentioning equality of objects.

** Contents:

- Displayed precategories: [disp_precat C]
- Total precategories (and their forgetful functors)
  - [total_precat D]
  - [pr1_precat D]
- Functors between precategories, over functors between their bases
  - [functor_lifting], [lifted_functor]
  - [functor_over], [total_functor]
- Direct products of displayed precategories (and their projections)
  - [dirprod_precat D1 D2]
  - [dirprodpr1_functor], [dirprodpr2_functor]
- Examples

*)

Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.

Require UniMath.Ktheory.Utilities.

Require Import Systems.Auxiliary.
Require Import Systems.UnicodeNotations.
Require Import Systems.Bicats.Auxiliary.
Require Import Systems.Bicats.Displayed_Precats.
Require Import Systems.Bicats.Displayed_Precats_bis.

Local Set Automatic Introduction.
(* only needed since imports globally unset it *)

Local Open Scope type_scope.

Undelimit Scope transport.

Notation "# F" := (functor_over_on_morphisms F)
  (at level 3) : mor_disp_scope.

Local Open Scope mor_disp_scope.


Lemma functor_over_transportf {C' C : Precategory}
  {D' : disp_precat C'} {D : disp_precat C}
  (F : functor C' C) (FF : functor_over F D' D)
  (x' x : C') (f' f : x' ⇒ x) (p : f' = f)
  (xx' : D' x') (xx : D' x)
  (ff : xx' ⇒[ f' ] xx) 
  :
  # FF (transportf (mor_disp _ _ ) p ff)
  = 
  transportf _ (maponpaths (#F)%mor p) (#FF ff) .
Proof.
  induction p.
  apply idpath.
Defined.

(** Composition of displayed functors *)

Section bla.

Variables C'' C' C : Precategory.
Variable D'' : disp_precat C''.
Variable D' : disp_precat C'.
Variable D : disp_precat C.
Variable F' : functor C'' C'.
Variable F : functor C' C.

Variable FF' : functor_over F' D'' D'.
Variable FF : functor_over F D' D.


(** TODO : split this for opacification *)
Definition functor_composite_over : functor_over (functor_composite F' F) D'' D.
Proof.
  mkpair.
  - mkpair.
    + intros x'' xx''. apply (FF _ (FF' _ xx'')).
    + intros. apply (# FF  (# FF' X )).
  - split; simpl.
    + intros x'' xx''.
      etrans. apply maponpaths. apply functor_over_id.
      etrans. apply functor_over_transportf.
      etrans. apply maponpaths. apply functor_over_id.
      etrans. apply transport_f_f.
      apply transportf_ext. apply (pr2 C).
    + intros.
      etrans. apply maponpaths. apply functor_over_comp.
      etrans. apply functor_over_transportf.
      etrans. apply maponpaths. apply functor_over_comp.
      etrans. apply transport_f_f.
      apply transportf_ext. apply (pr2 C).
Defined.      

Definition functor_identity_over : functor_over (functor_identity _ ) D D.
Proof.
  mkpair.
  - mkpair. 
    + intros; assumption.
    + intros; assumption.
  - split; simpl.      
    + intros; apply idpath.
    + intros; apply idpath.
Defined.
      
End bla.

Arguments functor_composite_over {_ _ _ _ _ _ _ _ } _ _.
Arguments functor_identity_over {_ }_ .
(** definition of displayed quasi-equivalence *)
(** for now a specialized version for displayed precats over
    the same base cat
*)

Section foo.

Variable C : Precategory.
Variables D' D : disp_precat C.

Definition quasi_equiv_disp (F : functor_over (functor_identity _ ) D' D) : UU
  :=
  Σ G : functor_over (functor_identity _ ) D D', 
        nat_trans_over (nat_trans_id _ ) 
                (functor_composite_over F G)  (functor_identity_over _ )
     × nat_trans_over (nat_trans_id _ ) (functor_composite_over G F) (functor_identity_over _ ).

End foo.







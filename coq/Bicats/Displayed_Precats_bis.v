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

Local Set Automatic Introduction.
(* only needed since imports globally unset it *)

Local Open Scope type_scope.

Undelimit Scope transport.

Notation "# F" := (functor_over_on_morphisms F)
  (at level 3) : mor_disp_scope.

Local Open Scope mor_disp_scope.

Section move_elsewhere.

Definition assoc_disp_var {C} {D : disp_precat C}
  {x y z w} {f} {g} {h} {xx : D x} {yy : D y} {zz : D z} {ww : D w}
  {ff : xx ⇒[f] yy} {gg : yy ⇒[g] zz} {hh : zz ⇒[h] ww}
: (ff ;; gg) ;; hh = transportf _ (assoc _ _ _) (ff ;; (gg ;; hh)).
Proof.
  apply pathsinv0, Utilities.transportf_pathsinv0.
  apply pathsinv0, assoc_disp.
Defined.

End move_elsewhere.


Definition nat_trans_over_data
  {C' C : precategory_data} 
  {F' F : functor_data C' C}
  (a : forall x, F' x ⇒ F x)
  {D' : disp_precat_data C'}
  {D : disp_precat_data C}
  (R' : functor_over_data F' D' D)
  (R : functor_over_data F D' D) :=
forall (x : C')  (xx : D' x), 
      R' x  xx ⇒[ a x ] R x xx .
(*
Check @nat_trans_ax.

@nat_trans_ax
     : ∀ (C C' : precategory_data) (F F' : functor_data C C')
       (a : nat_trans F F') (x x' : C) (f : x ⇒ x'),
       (# F f ;; a x')%mor = (a x ;; # F' f)%mor
*)

Definition nat_trans_over_axioms
  {C' C : precategory_data} 
  {F' F : functor_data C' C}
  {a : nat_trans F' F}
  {D' : disp_precat_data C'}
  {D : disp_precat_data C}
  {R' : functor_over_data F' D' D}
  {R : functor_over_data F D' D}
  (b : nat_trans_over_data a R' R) : UU
 := 
   forall (x' x : C') (f : x' ⇒ x)
          (xx' : D' x') (xx : D' x) 
          (ff : xx' ⇒[ f ] xx), 
     # R'  ff ;; b _ xx = 
     transportb _ (nat_trans_ax a _ _ f ) (b _ xx' ;; # R ff).

Lemma isaprop_nat_trans_over_axioms
  {C' C : Precategory} 
  {F' F : functor_data C' C}
  (a : nat_trans F' F)
  {D' : disp_precat_data C'}
  {D : disp_precat C}
  {R' : functor_over_data F' D' D}
  {R : functor_over_data F D' D}
  (b : nat_trans_over_data a R' R) 
  : 
    isaprop (nat_trans_over_axioms b).
Proof.
  repeat (apply impred; intro).
  apply homsets_disp.
Qed.

Definition nat_trans_over
  {C' C : precategory_data} 
  {F' F : functor_data C' C}
  (a : nat_trans F' F)
  {D' : disp_precat_data C'}
  {D : disp_precat_data C}
  (R' : functor_over_data F' D' D)
  (R : functor_over_data F D' D) : UU :=
  Σ b : nat_trans_over_data a R' R,
    nat_trans_over_axioms b.

Definition nat_trans_over_pr1 
  {C' C : precategory_data} 
  {F' F : functor_data C' C}
  {a : nat_trans F' F}
  {D' : disp_precat_data C'}
  {D : disp_precat_data C}
  {R' : functor_over_data F' D' D}
  {R : functor_over_data F D' D}
  (b : nat_trans_over a R' R) 
  {x : C'}  (xx : D' x):
    R' x  xx ⇒[ a x ] R x xx
  := pr1 b x xx.

Coercion nat_trans_over_pr1 : nat_trans_over >-> Funclass.

Definition nat_trans_over_ax
  {C' C : precategory_data} 
  {F' F : functor_data C' C}
  {a : nat_trans F' F}
  {D' : disp_precat_data C'}
  {D : disp_precat_data C}
  {R' : functor_over_data F' D' D}
  {R : functor_over_data F D' D}
  (b : nat_trans_over a R' R)
  {x' x : C'} 
  {f : x' ⇒ x}
  {xx' : D' x'} 
  {xx : D' x}
  (ff : xx' ⇒[ f ] xx):
  # R'  ff ;; b _ xx = 
  transportb _ (nat_trans_ax a _ _ f ) (b _ xx' ;; # R ff)
  := 
  pr2 b _ _ f _ _ ff.

Lemma nat_trans_over_ax_var
  {C' C : precategory_data} 
  {F' F : functor_data C' C}
  {a : nat_trans F' F}
  {D' : disp_precat_data C'}
  {D : disp_precat_data C}
  {R' : functor_over_data F' D' D}
  {R : functor_over_data F D' D}
  (b : nat_trans_over a R' R)
  {x' x : C'} 
  {f : x' ⇒ x}
  {xx' : D' x'} 
  {xx : D' x}
  (ff : xx' ⇒[ f ] xx):
  b _ xx' ;; # R ff =
  transportf _ (nat_trans_ax a _ _ f) (# R'  ff ;; b _ xx).
Proof.
  apply pathsinv0, Utilities.transportf_pathsinv0.
  apply pathsinv0, nat_trans_over_ax.
Defined.


(** identity nat_trans_over *)

Definition nat_trans_over_id
  {C' C : Precategory} 
  {F': functor_data C' C}
  {D' : disp_precat_data C'}
  {D : disp_precat C}
  (R' : functor_over_data F' D' D)
  : nat_trans_over (nat_trans_id F') R' R'.
Proof.
  mkpair.
  - intros x xx.
    apply id_disp.
  - abstract (
    intros x' x f xx' xx ff;
    etrans; [ apply id_right_disp |];
    apply transportf_comp_lemma;
    apply pathsinv0;
    etrans; [apply id_left_disp |];
    apply transportf_ext;
    apply (pr2 C) ).
Defined.    
    

(** composition of nat_trans_over *)



Definition nat_trans_over_comp
  {C' C : Precategory} 
  {F'' F' F : functor_data C' C}
  (a' : nat_trans F'' F')
  (a : nat_trans F' F)
  {D' : disp_precat_data C'}
  {D : disp_precat C}
  (R'' : functor_over_data F'' D' D)
  (R' : functor_over_data F' D' D)
  (R : functor_over_data F D' D)
  (b' : nat_trans_over a' R'' R')
  (b : nat_trans_over a R' R)
  : nat_trans_over (nat_trans_comp _ _ _ a' a) R'' R.
Proof.
  mkpair.
  - intros x xx.
    apply (comp_disp (b' _ _ )  (b _ _ )).
  - abstract ( 
    intros x' x f xx' xx ff;
    etrans; [ apply assoc_disp |];
    apply transportf_comp_lemma;
    apply Utilities.transportf_pathsinv0; apply pathsinv0;
    rewrite (nat_trans_over_ax b');
    etrans; [ apply compl_disp_transp |];
    apply transportf_comp_lemma;
    apply pathsinv0;
    etrans; [ apply assoc_disp_var |];
    apply pathsinv0;
    apply transportf_comp_lemma;
    apply pathsinv0;
    rewrite (nat_trans_over_ax_var b);
    rewrite mor_disp_transportf_prewhisker;
    apply transportf_comp_lemma;
    apply pathsinv0;
    etrans; [ apply assoc_disp_var |];
    apply transportf_comp_lemma;
    apply transportf_comp_lemma_hset;
     [ apply (pr2 C) | apply idpath]
   ).
Defined.


(** Displayed precategory of displayed functors and 
    displayed natural transformations 
    
*)


Section displayed_functor_precategory.

Variables C' C : Precategory.
Variable D' : disp_precat C'.
Variable D : disp_precat C.

Search (_  -> Precategory).

Let FunctorsC'C := Precategories.functorPrecategory C' C.

Lemma foo
  (F' F : functor C' C)
  (a' a : nat_trans F' F)
  (p : a' = a )
  (FF' : functor_over F' D' D)
  (FF : functor_over F D' D)
  (b : nat_trans_over a' FF' FF)
  (c' : C')
  (xx' : D' c')
  :
  pr1 (transportf (fun x => nat_trans_over x FF' FF) p b) c' xx' =
      transportf (mor_disp (FF' c' xx') (FF c' xx')) 
           (nat_trans_eq_pointwise p _ )  (b c' xx'). 
Proof.
  induction p.
  simpl. cbn. simpl.
  cbn.
  unfold idfun.
  assert (XR : nat_trans_eq_pointwise (idpath a') c' = idpath _ ).
  { apply (pr2 C). }
  rewrite XR.
  apply idpath.
Qed.

Definition disp_functor_precat : 
  disp_precat (FunctorsC'C).
Proof.
  mkpair.
  - mkpair.
    + mkpair.
      * intro F.
        apply (functor_over F D' D).
      * simpl. intros F' F FF' FF a.
        apply (nat_trans_over a FF' FF).
    + mkpair.
      * intros x xx.
        apply nat_trans_over_id.
      * intros. apply (nat_trans_over_comp _ _ _ _ _ X X0).
  - repeat split.
    + (* TODO : find suitable lemmas to make this less painful *)
      simpl.
      intros F' F a FF' FF b.
      apply subtypeEquality.
      { intro. apply isaprop_nat_trans_over_axioms. }
      apply funextsec; intro c'.
      apply funextsec; intro xx'.
      apply pathsinv0. 
      etrans. 
        assert (XR := foo).
        specialize (XR F' F a _ (! (id_left (a : FunctorsC'C ⟦ _ , _ ⟧)))).
        apply XR; clear XR.
      apply pathsinv0.
      etrans. apply id_left_disp.
      apply transportf_ext. apply (pr2 C).
    + simpl.
      intros F' F a FF' FF b.
      apply subtypeEquality.
      { intro. apply isaprop_nat_trans_over_axioms. }
      apply funextsec; intro c'.
      apply funextsec; intro xx'.
      apply pathsinv0. 
      etrans. 
        assert (XR := foo).
        specialize (XR F' F a _ (! (id_right (a : FunctorsC'C ⟦ _ , _ ⟧)))).
        apply XR; clear XR.
      apply pathsinv0.
      etrans. apply id_right_disp.
      apply transportf_ext. apply (pr2 C).
    + simpl.
      admit.
    + simpl.
      intros.
      apply (isofhleveltotal2 2).
      * do 2 (apply impred; intro).
        apply homsets_disp.
      * intro d. 
        do 6 (apply impred; intro).
        apply hlevelntosn. apply homsets_disp.
Abort.
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
Require Import Systems.Displayed_Cats.Auxiliary.
Require Import Systems.Displayed_Cats.Displayed_Precats.

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


Lemma iso_disp_precomp {C : Precategory} {D : disp_precat C}
    {x y : C} (f : iso x y) 
    {xx : D x} {yy} (ff : iso_disp f xx yy)
  : forall (y' : C) (f' : y ⇒ y') (yy' : D y'), 
          isweq (fun ff' : yy ⇒[ f' ] yy' => pr1 ff ;; ff').
Proof.
  intros y' f' yy'.
  use gradth.
  + intro X.
    set (XR := (pr1 (pr2 ff)) ;; X).
    set (XR' := transportf _ (assoc _ _ _   ) XR).
(*    Search (inv_from_iso _  ). *)
    set (XRRT := transportf _ 
           (maponpaths (fun xyz => (xyz ;; f')%mor) (iso_after_iso_inv f)) 
           XR').
    set (XRRT' := transportf _ (id_left _ )                   
           XRRT).
    apply XRRT'.
  + intros. simpl.
    etrans. apply transport_f_f.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply assoc_disp.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply maponpaths_2. apply (pr2 (pr2 ff)). 
    etrans. apply maponpaths. apply mor_disp_transportf_postwhisker.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply id_left_disp.
    etrans. apply transport_f_f.
    apply transportf_comp_lemma_hset.
    apply (pr2 C). apply idpath.
  + intros; simpl.
    etrans. apply maponpaths. apply transport_f_f.
    etrans. apply mor_disp_transportf_prewhisker.
    etrans. apply maponpaths. apply mor_disp_transportf_prewhisker.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply assoc_disp.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply maponpaths_2. 
    assert (XR := pr2 (pr2 (pr2 ff))). simpl in XR. apply XR.
    etrans. apply maponpaths. apply mor_disp_transportf_postwhisker.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply id_left_disp.
    etrans. apply transport_f_f.
    apply transportf_comp_lemma_hset.
    apply (pr2 C). apply idpath.
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
     : Π (C C' : precategory_data) (F F' : functor_data C C')
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
  {a' : nat_trans F'' F'}
  {a : nat_trans F' F}
  {D' : disp_precat_data C'}
  {D : disp_precat C}
  {R'' : functor_over_data F'' D' D}
  {R' : functor_over_data F' D' D}
  {R : functor_over_data F D' D}
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
  assert (XR : nat_trans_eq_pointwise (idpath a') c' = idpath _ ).
  { apply (pr2 C). }
  rewrite XR.
  apply idpath.
Qed.

Lemma nat_trans_over_id_left
  (F' F : functor C' C)
  (a : nat_trans F' F)
  (FF' : functor_over F' D' D)
  (FF : functor_over F D' D)
  (b : nat_trans_over a FF' FF)
  :
   nat_trans_over_comp (nat_trans_over_id FF') b =
   transportb (λ f : nat_trans F' F, nat_trans_over f FF' FF) 
              (id_left (a : FunctorsC'C ⟦ _ , _ ⟧)) 
              b.
Proof.
  apply subtypeEquality.
  { intro. apply isaprop_nat_trans_over_axioms. }
  apply funextsec; intro c'.
  apply funextsec; intro xx'.
  apply pathsinv0. 
  etrans. apply foo.
  apply pathsinv0.
  etrans. apply id_left_disp.
  apply transportf_ext. apply (pr2 C).
Qed.

Lemma nat_trans_over_id_right
  (F' F : functor C' C)
  (a : nat_trans F' F)
  (FF' : functor_over F' D' D)
  (FF : functor_over F D' D)
  (b : nat_trans_over a FF' FF)
  :
   nat_trans_over_comp b (nat_trans_over_id FF) =
   transportb (λ f : nat_trans F' F, nat_trans_over f FF' FF) 
              (id_right (a : FunctorsC'C ⟦ _ , _ ⟧)) 
              b.
Proof.
  apply subtypeEquality.
  { intro. apply isaprop_nat_trans_over_axioms. }
  apply funextsec; intro c'.
  apply funextsec; intro xx'.
  apply pathsinv0. 
  etrans. apply foo.
  apply pathsinv0.
  etrans. apply id_right_disp.
  apply transportf_ext. apply (pr2 C).
Qed.

Lemma nat_trans_over_assoc
  (x y z w : functor C' C)
  (f : nat_trans x y)
  (g : nat_trans y z)
  (h : nat_trans z w)
  (xx : functor_over x D' D)
  (yy : functor_over y D' D)
  (zz : functor_over z D' D)
  (ww : functor_over w D' D)
  (ff : nat_trans_over f xx yy)
  (gg : nat_trans_over g yy zz)
  (hh : nat_trans_over h zz ww)
  :
   nat_trans_over_comp ff (nat_trans_over_comp gg hh) =
   transportb (λ f0 : nat_trans x w, nat_trans_over f0 xx ww) 
     (assoc (f : FunctorsC'C⟦_,_⟧) g h) 
     (nat_trans_over_comp (nat_trans_over_comp ff gg) hh).
Proof.
  apply subtypeEquality.
  { intro. apply isaprop_nat_trans_over_axioms. }
  apply funextsec; intro c'.
  apply funextsec; intro xx'.
  apply pathsinv0.
  etrans. apply foo.
  apply pathsinv0.
  etrans. apply assoc_disp.
  apply transportf_ext.
  apply (pr2 C).
Qed.

Lemma isaset_nat_trans_over
  (x y : functor C' C)
  (f : nat_trans x y)
  (xx : functor_over x D' D)
  (yy : functor_over y D' D)
  :
   isaset (nat_trans_over f xx yy).
Proof.
  intros. simpl in *.
  apply (isofhleveltotal2 2).
  * do 2 (apply impred; intro).
    apply homsets_disp.
  * intro d. 
    do 6 (apply impred; intro).
    apply hlevelntosn. apply homsets_disp.
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
      * intros ? ? ? ? ? ? ? ? X X0. apply (nat_trans_over_comp X X0 ).
  - repeat split.
    + apply nat_trans_over_id_left.
    + apply nat_trans_over_id_right.
    + apply nat_trans_over_assoc.
    + apply isaset_nat_trans_over.      
Defined.

(** TODO : characterize isos in the displayed functor precat *)

Definition pointwise_iso_from_nat_iso {A X : precategory} {hsX : has_homsets X}
  {F G : functor_precategory A X hsX}
  (b : iso F G) (a : A) : iso (pr1 F a) (pr1 G a)
  :=
  functor_iso_pointwise_if_iso _ _ _ _ _ b (pr2 b)_ .


Definition pointwise_inv_is_inv_on {A X : precategory} {hsX : has_homsets X}
  {F G : functor_precategory A X hsX}
  (b : iso F G) (a : A) : 
  
  inv_from_iso (pointwise_iso_from_nat_iso b a) =
                                       pr1 (inv_from_iso b) a. 
Proof.
  apply id_right.
Defined.



(** 
    It seems to be better to work on 
    https://github.com/UniMath/UniMath/issues/362
    first
*)

(** TODO : write a few lemmas about isos in 
    the disp functor precat, 
    to make the following sane
*)

Definition is_pointwise_iso_if_is_disp_functor_precat_iso
  (x y : FunctorsC'C)
  (f : iso x y)
  (xx : disp_functor_precat x)
  (yy : disp_functor_precat y)
  (FF : xx ⇒[ f ] yy)
  (H : is_iso_disp f FF)
  :
  forall x' (xx' : D' x') , is_iso_disp (pointwise_iso_from_nat_iso f _ )
                          (pr1 FF _ xx' ).
Proof.
  intros x' xx'.
  mkpair.
  - set (X:= pr1 H). simpl in X.
    apply (transportb _ (pointwise_inv_is_inv_on f _ ) (X x' xx')).
  - simpl. repeat split.
    + etrans. apply compl_disp_transp.
      apply pathsinv0.
      apply transportf_comp_lemma.
      assert (XR:= pr1 (pr2 H)).
      assert (XRT :=  (maponpaths pr1 XR)). 
      assert (XRT' :=  toforallpaths _ _ _  (toforallpaths _ _ _ XRT x')).
      apply pathsinv0.
      etrans. apply XRT'. 
      clear XRT' XRT XR.
      assert (XR := foo). 
      specialize (XR _ _ _ _ (! iso_after_iso_inv f)).
      etrans. apply XR.
      apply transportf_comp_lemma.
(*      Search (transportf _ _ ?x = ?y). *)
      apply transportf_comp_lemma_hset.
      apply (pr2 C).
      apply idpath.
    + etrans. apply mor_disp_transportf_prewhisker.      
      apply pathsinv0.
      apply transportf_comp_lemma.
      assert (XR:= pr2 (pr2 H)).
      assert (XRT :=  (maponpaths pr1 XR)). 
      assert (XRT' :=  toforallpaths _ _ _  (toforallpaths _ _ _ XRT x')).
      apply pathsinv0.
      etrans. apply XRT'. 
      clear XRT' XRT XR.
      assert (XR := foo). 
      specialize (XR _ _ _ _ (! iso_inv_after_iso f)).
      etrans. apply XR.
      apply transportf_comp_lemma.
(*      Search (transportf _ _ ?x = ?y). *)
      apply transportf_comp_lemma_hset.
      apply (pr2 C).
      apply idpath.
Defined.

Lemma is_nat_trans_over_pointwise_inv
  (x y : FunctorsC'C)
  (f : iso x y)
  (xx : disp_functor_precat x)
  (yy : disp_functor_precat y)
  (FF : xx ⇒[ f] yy)
  (H : Π (x' : C') (xx' : D' x'),
      is_iso_disp (pointwise_iso_from_nat_iso f x') (pr1 FF x' xx'))
  (x' x0 : C')
  (f0 : x' ⇒ x0)
  (xx' : D' x')
  (xx0 : D' x0)
  (ff : xx' ⇒[ f0] xx0)
  :
   # (yy : functor_over _ _ _)  ff ;; (let RT := pr1 (H x0 xx0) in
               transportf (mor_disp (pr1 yy x0 xx0) (pr1 xx x0 xx0))
                 (id_right (pr1 (inv_from_iso f) x0)) RT) =
   transportb (mor_disp (pr1 yy x' xx') (pr1 xx x0 xx0))
     (nat_trans_ax (inv_from_iso f) x' x0 f0)
     ((let RT := pr1 (H x' xx') in
       transportf (mor_disp (pr1 yy x' xx') (pr1 xx x' xx'))
         (id_right (pr1 (inv_from_iso f) x')) RT) ;; 
      # (xx : functor_over _ _ _) ff).
Proof.
 etrans. apply mor_disp_transportf_prewhisker.
    apply pathsinv0.
    etrans. apply maponpaths. apply mor_disp_transportf_postwhisker.
(*    Search (transportf _ _ _ = transportf _ _ _ ). *)
(*    Search (?e = ?e' -> ?w = ?w' -> _ ?e ?w = _ ?e' ?w'). *)
    etrans. apply transport_f_f.
(*    Search (transportf _ _ _ = transportf _ _ _ ). *)
    apply transportf_comp_lemma.
    set (Hx := H x' xx').
    assert (Hx1 := pr2 (pr2 Hx)).
    set (XR:= iso_disp_precomp (pointwise_iso_from_nat_iso f x' ) (_ ,,Hx)).
(*    Check (# (pr1 yy) ff ;; pr1 (H x0 xx0)). *)
    specialize (XR _  
       (
        ((# (y : functor _ _ ))%mor f0 ;; inv_from_iso (pointwise_iso_from_nat_iso f x0))
          %mor
         ) 
       ).
    specialize (XR ((xx : functor_over _ _ _  ) x0 xx0)).
    set (Xweq := weqpair _ XR).
    apply (invmaponpathsweq Xweq).
    unfold Xweq. clear Xweq.
    etrans.  apply mor_disp_transportf_prewhisker.
    etrans. apply maponpaths. apply assoc_disp.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply maponpaths_2. apply Hx1.
    etrans. apply maponpaths. apply mor_disp_transportf_postwhisker.
    etrans. apply transport_f_f.
    apply pathsinv0.
    etrans. apply assoc_disp.
    assert (XRO := @nat_trans_over_ax _ _ _ _ _ _ _ _ _ FF).
    specialize (XRO _ _ _ xx'  _ ff).
    assert (XR' := ! (Utilities.transportf_pathsinv0 _ _ _ _  (!XRO))).
    clear XRO.
    clear XR. clear Hx1.
    etrans. apply maponpaths. apply maponpaths_2.
            apply XR'.
    etrans. apply maponpaths.  apply mor_disp_transportf_postwhisker. 
    etrans. apply transport_f_f.
    apply pathsinv0. 
    etrans. apply maponpaths. apply id_left_disp.
    etrans. apply transport_f_f.
    apply pathsinv0.
    
    etrans. apply maponpaths. 
            apply assoc_disp_var.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply maponpaths.
            apply (pr2 (pr2 (H _ _ ))).
    etrans. apply maponpaths. apply mor_disp_transportf_prewhisker. 
    etrans. apply maponpaths. apply maponpaths.
            apply id_right_disp.
    etrans. apply transport_f_f.
    etrans. apply transport_f_f.
    apply transportf_ext. apply (pr2 C).
Qed.

Definition inv_disp_from_pointwise_iso 
  (x y : FunctorsC'C)
  (f : iso x y)
  (xx : disp_functor_precat x)
  (yy : disp_functor_precat y)
  (FF : xx ⇒[ f ] yy)
  (H : forall x' (xx' : D' x') , is_iso_disp (pointwise_iso_from_nat_iso f _ )
                          (pr1 FF _ xx' ))
  :     
       yy ⇒[ inv_from_iso f] xx.
Proof.
  mkpair.
  + intros x' xx'.
    simpl in xx. simpl in yy.
    assert (XR : inv_from_iso (pointwise_iso_from_nat_iso f x') =
                                       pr1 (inv_from_iso f) x').
    { apply id_right. }
    set (RT := pr1 (H x' xx')).
    apply (transportf _ XR RT).
  + intros x' x0 f0 xx' xx0 ff.
    apply is_nat_trans_over_pointwise_inv.
Defined.
    
    

Definition is_disp_functor_precat_iso_if_pointwise_iso 
  (x y : FunctorsC'C)
  (f : iso x y)
  (xx : disp_functor_precat x)
  (yy : disp_functor_precat y)
  (FF : xx ⇒[ f ] yy)
  (H : forall x' (xx' : D' x') , is_iso_disp (pointwise_iso_from_nat_iso f _ )
                          (pr1 FF _ xx' ))
  : is_iso_disp f FF.
Proof.  
  mkpair.
  - apply (inv_disp_from_pointwise_iso _ _ _ _ _ FF H).
  - split.
    + apply subtypeEquality.
      { intro. apply isaprop_nat_trans_over_axioms. }
      apply funextsec; intro c'.
      apply funextsec; intro xx'.
      apply pathsinv0.
      etrans. apply foo.
      cbn.
      apply pathsinv0.
      etrans. apply mor_disp_transportf_postwhisker.
      etrans. apply maponpaths. apply (pr1 (pr2 (H c' xx'))).
      etrans. apply transport_f_f.
      apply transportf_ext. apply (pr2 C).
    + apply subtypeEquality.
      { intro. apply isaprop_nat_trans_over_axioms. }
      apply funextsec; intro c'.
      apply funextsec; intro xx'.
      apply pathsinv0.
      etrans. apply foo.
      cbn.
      apply pathsinv0.
      etrans. apply mor_disp_transportf_prewhisker.
      etrans. apply maponpaths. apply (pr2 (pr2 (H c' xx'))).
      etrans. apply transport_f_f.
      apply transportf_ext. apply (pr2 C).
Defined.      


End displayed_functor_precategory.
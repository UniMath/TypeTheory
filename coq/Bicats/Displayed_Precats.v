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

Local Set Automatic Introduction.
(* only needed since imports globally unset it *)

Local Open Scope type_scope.



(** * Displayed precategories *)

Module Record_Preview.

  Record disp_precat (C : Precategory) : Type :=
    { ob_disp : C -> Type
    ; mor_disp {x y : C} : (x ⇒ y) -> ob_disp x -> ob_disp y -> Type
    ; id_disp {x : C} (xx : ob_disp x) : mor_disp (identity x) xx xx
    ; comp_disp {x y z : C} {f : x ⇒ y} {g : y ⇒ z}
                   {xx : ob_disp x} {yy : ob_disp y} {zz : ob_disp z}
        : mor_disp f xx yy -> mor_disp g yy zz -> mor_disp (f ;; g) xx zz
    ; id_left_disp {x y} {f : x ⇒ y} {xx} {yy} (ff : mor_disp f xx yy)
        : comp_disp (id_disp xx) ff
          = transportb (fun g => mor_disp g xx yy) (id_left _) ff
    ; id_right_disp {x y} {f : x ⇒ y} {xx} {yy} (ff : mor_disp f xx yy)
        : comp_disp ff (id_disp yy)
          = transportb (fun g => mor_disp g xx yy) (id_right _) ff
    ; assoc_disp {x y z w} {f : x ⇒ y} {g : y ⇒ z} {h : z ⇒ w}
        {xx} {yy} {zz} {ww}
        (ff : mor_disp f xx yy) (gg : mor_disp g yy zz) (hh : mor_disp h zz ww)
        : comp_disp ff (comp_disp gg hh)
          = transportb (fun k => mor_disp k _ _) (assoc _ _ _)
            (comp_disp (comp_disp ff gg) hh)
    ; homsets_disp {x y} {f : x ⇒ y} {xx} {yy} : isaset (mor_disp f xx yy) 
    }.

End Record_Preview.

(** The actual definition is structured analogously to [precategory], as an iterated Σ-type:

- [disp_precat]
  - [disp_precat_data]
    - [disp_precat_ob_mor]
      - [ob_disp]
      - [mod_disp]
    - [disp_precat_id_comp]
      - [id_disp]
      - [comp_disp]
  - [disp_precat_axioms]
    - [id_left_disp]
    - [id_right_disp]
    - [assoc_disp]
    - [homsets_disp]

*)

Section Disp_Precat.

Definition disp_precat_ob_mor (C : precategory_ob_mor)
  := Σ (obd : C -> Type), (∀ x y:C, obd x -> obd y -> (x ⇒ y) -> Type).

Definition ob_disp {C} (D : disp_precat_ob_mor C) : C -> UU := pr1 D.
Coercion ob_disp : disp_precat_ob_mor >-> Funclass.

Definition mor_disp {C} {D : disp_precat_ob_mor C}
  {x y} xx yy (f : x ⇒ y)
:= pr2 D x y xx yy f : Type. 

Local Notation "xx ⇒[ f ] yy" := (mor_disp xx yy f) (at level 50, yy at next level).

Definition disp_precat_id_comp (C : precategory_data)
  (D : disp_precat_ob_mor C)
  : Type
:= (forall (x:C) (xx : D x), xx ⇒[identity x] xx)
  × (forall (x y z : C) (f : x ⇒ y) (g : y ⇒ z) (xx:D x) (yy:D y) (zz:D z),
           (xx ⇒[f] yy) -> (yy ⇒[g] zz) -> (xx ⇒[f ;; g] zz)).

Definition disp_precat_data C := total2 (disp_precat_id_comp C).

Definition disp_precat_ob_mor_from_disp_precat_data {C}
  (D : disp_precat_data C)
  : disp_precat_ob_mor C
:= pr1 D.

Coercion disp_precat_ob_mor_from_disp_precat_data : 
 disp_precat_data >-> disp_precat_ob_mor.

Definition id_disp {C} {D : disp_precat_data C} {x:C} (xx : D x)
  : xx ⇒[identity x] xx
:= pr1 (pr2 D) x xx.

Definition comp_disp {C} {D : disp_precat_data C}
  {x y z : C} {f : x ⇒ y} {g : y ⇒ z}
  {xx : D x} {yy} {zz} (ff : xx ⇒[f] yy) (gg : yy ⇒[g] zz)
  : xx ⇒[f;;g] zz
:= pr2 (pr2 D) _ _ _ _ _ _ _ _ ff gg.

Local Notation "ff ;; gg" := (comp_disp ff gg)
  (at level 50, left associativity, format "ff  ;;  gg")
  : mor_disp_scope.
Delimit Scope mor_disp_scope with mor_disp.
Bind Scope mor_disp_scope with mor_disp.
Local Open Scope mor_disp_scope.

Definition disp_precat_axioms (C : Precategory) (D : disp_precat_data C)
  : Type
:= (∀ x y (f : x ⇒ y) (xx : D x) yy (ff : xx ⇒[f] yy),
     id_disp _ ;; ff
     = transportb _ (id_left _) ff)
   × (∀ x y (f : x ⇒ y) (xx : D x) yy (ff : xx ⇒[f] yy),
     ff ;; id_disp _
     = transportb _ (id_right _) ff)
   × (∀ x y z w f g h (xx : D x) (yy : D y) (zz : D z) (ww : D w)
        (ff : xx ⇒[f] yy) (gg : yy ⇒[g] zz) (hh : zz ⇒[h] ww),
     ff ;; (gg ;; hh)
     = transportb _ (assoc _ _ _) ((ff ;; gg) ;; hh))
   × (∀ x y f (xx : D x) (yy : D y), isaset (xx ⇒[f] yy)).

Definition disp_precat (C : Precategory) := total2 (disp_precat_axioms C).

Definition disp_precat_data_from_disp_precat {C} (D : disp_precat C)
 := pr1 D : disp_precat_data C.
Coercion disp_precat_data_from_disp_precat : disp_precat >-> disp_precat_data.

Definition id_left_disp {C} {D : disp_precat C} 
  {x y} {f : x ⇒ y} {xx : D x} {yy} {ff : xx ⇒[f] yy}
: id_disp _ ;; ff = transportb _ (id_left _) ff
:= pr1 (pr2 D) _ _ _ _ _ _.

Definition id_right_disp {C} {D : disp_precat C} 
  {x y} {f : x ⇒ y} {xx : D x} {yy} {ff : xx ⇒[f] yy}
  : ff ;; id_disp _ = transportb _ (id_right _) ff
:= pr1 (pr2 (pr2 D)) _ _ _ _ _ _.

Definition assoc_disp {C} {D : disp_precat C}
  {x y z w} {f} {g} {h} {xx : D x} {yy : D y} {zz : D z} {ww : D w}
  {ff : xx ⇒[f] yy} {gg : yy ⇒[g] zz} {hh : zz ⇒[h] ww}
: ff ;; (gg ;; hh) = transportb _ (assoc _ _ _) ((ff ;; gg) ;; hh)
:= pr1 (pr2 (pr2 (pr2 D))) _ _ _ _ _ _ _ _ _ _ _ _ _ _.

Definition homsets_disp {C} {D :disp_precat C} {x y} {f} {xx : D x} {yy : D y}
  : isaset (xx ⇒[f] yy)
:= pr2 (pr2 (pr2 (pr2 D))) _ _ _ _ _.

(** ** Some utility lemmas *)
Section Lemmas.

Lemma isaprop_disp_precat_axioms (C : Precategory) (D : disp_precat_data C)
  : isaprop (disp_precat_axioms C D).
Proof.
  apply isofhlevelsn.
  intro X.
  set (XR := ( _ ,, X) : disp_precat C).
  apply isofhleveltotal2.
  - repeat (apply impred; intro).
    apply (@homsets_disp _ XR).
  - intros x.
    repeat (apply isofhleveldirprod); repeat (apply impred; intro).
    + apply (@homsets_disp _ XR).
    + apply (@homsets_disp _ XR).
    + apply isapropiscontr.
Qed.
      
Lemma compl_disp_transp {C : Precategory} {D : disp_precat_data C}
    {x y z : C} {f f' : x ⇒ y} (ef : f = f') {g : y ⇒ z}
    {xx : D x} {yy} {zz} (ff : xx ⇒[f] yy) (gg : yy ⇒[g] zz)
  : (transportf _ ef ff) ;; gg
  = transportf _ (maponpaths (fun k => k ;; _)%mor ef) (ff ;; gg).
Proof.
  destruct ef. apply idpath.
Qed.

(* TODO: consider naming of following few transport lemmas *)
Lemma mor_disp_transportf_postwhisker
    {C : precategory} {D : disp_precat_data C}
    {x y z : C} {f f' : x ⇒ y} (ef : f = f') {g : y ⇒ z}
    {xx : D x} {yy} {zz} (ff : xx ⇒[f] yy) (gg : yy ⇒[g] zz)
  : (transportf _ ef ff) ;; gg
  = transportf _ (cancel_postcomposition _ _ g ef) (ff ;; gg).
Proof.
  destruct ef; apply idpath.
Qed.

Lemma mor_disp_transportf_prewhisker
    {C : precategory} {D : disp_precat_data C}
    {x y z : C} {f : x ⇒ y} {g g' : y ⇒ z} (eg : g = g')
    {xx : D x} {yy} {zz} (ff : xx ⇒[f] yy) (gg : yy ⇒[g] zz)
  : ff ;; (transportf _ eg gg)
  = transportf _ (maponpaths (compose f) eg) (ff ;; gg).
Proof.
  destruct eg; apply idpath.
Qed.

(* TODO: unify with [mor_disp_transportf_prewhisker] *)
Lemma compr_disp_transp {C : Precategory} {D : disp_precat_data C}
    {x y z : C} {f : x ⇒ y} {g g' : y ⇒ z} (eg : g = g')
    {xx : D x} {yy} {zz} (ff : xx ⇒[f] yy) (gg : yy ⇒[g] zz)
  : ff ;; (transportf _ eg gg)
  = transportf _ (maponpaths (fun k => _ ;; k)%mor eg) (ff ;; gg).
Proof.
  apply mor_disp_transportf_prewhisker.
Qed.

End Lemmas.

End Disp_Precat.

(** Redeclare sectional notations globally. *)
Notation "xx ⇒[ f ] yy" := (mor_disp xx yy f) (at level 50, yy at next level).

Notation "ff ;; gg" := (comp_disp ff gg)
  (at level 50, left associativity, format "ff  ;;  gg")
  : mor_disp_scope.
Delimit Scope mor_disp_scope with mor_disp.
Bind Scope mor_disp_scope with mor_disp.
Local Open Scope mor_disp_scope.

(** * Isomorphisms and (saturated) categories *)

Section Isos.

Definition is_iso_disp {C : Precategory} {D : disp_precat_data C}
    {x y : C} (f : iso x y) {xx : D x} {yy} (ff : xx ⇒[f] yy)
  : Type
:= Σ (gg : yy ⇒[inv_from_iso f] xx),
     gg ;; ff = transportb _ (iso_after_iso_inv _) (id_disp _)
     × ff ;; gg = transportb _ (iso_inv_after_iso _) (id_disp _).

Definition iso_disp {C : Precategory} {D : disp_precat_data C}
    {x y : C} (f : iso x y) (xx : D x) (yy : D y)
  := Σ ff : xx ⇒[f] yy, is_iso_disp f ff.

Definition mor_disp_from_iso {C : Precategory} {D : disp_precat_data C}
    {x y : C} {f : iso x y}{xx : D x} {yy : D y} 
    (i : iso_disp f xx yy) : _ ⇒[ _ ] _ := pr1 i.
Coercion mor_disp_from_iso : iso_disp >-> mor_disp.

Definition inv_mor_disp_from_iso {C : Precategory} {D : disp_precat_data C}
    {x y : C} {f : iso x y}{xx : D x} {yy : D y} 
    (i : iso_disp f xx yy) : _ ⇒[ _ ] _ := pr1 (pr2 i).

Definition iso_disp_after_inv_mor {C : Precategory} {D : disp_precat_data C}
    {x y : C} {f : iso x y}{xx : D x} {yy : D y} 
    (i : iso_disp f xx yy) 
    : 
    inv_mor_disp_from_iso i ;; i = transportb _ (iso_after_iso_inv _) (id_disp _).
Proof.
  apply (pr2 (pr2 i)).
Qed.
Definition inv_mor_after_iso_disp {C : Precategory} {D : disp_precat_data C}
    {x y : C} {f : iso x y}{xx : D x} {yy : D y} 
    (i : iso_disp f xx yy) 
    : 
    i ;; inv_mor_disp_from_iso i = transportb _ (iso_inv_after_iso _) (id_disp _).
Proof.
  apply (pr2 (pr2 (pr2 i))).
Qed.


Lemma isaprop_is_iso_disp {C : Precategory} {D : disp_precat C}
    {x y : C} (f : iso x y) {xx : D x} {yy} (ff : xx ⇒[f] yy)
  : isaprop (is_iso_disp f ff).
Proof.
  apply invproofirrelevance; intros i i'.
  apply subtypeEquality.
  - intros gg. apply isapropdirprod; apply homsets_disp.
  (* uniqueness of inverses *)
  (* TODO: think about better lemmas for this sort of calculation?
  e.g. all that repeated application of [transport_f_f], etc. *)
  - destruct i as [gg [gf fg]], i' as [gg' [gf' fg']]; simpl.
    etrans. eapply pathsinv0, Utilities.transportfbinv.
    etrans. apply maponpaths, @pathsinv0, id_right_disp.
    etrans. apply maponpaths, maponpaths.
      etrans. eapply pathsinv0, Utilities.transportfbinv.
      apply maponpaths, @pathsinv0, fg'.
    etrans. apply maponpaths, mor_disp_transportf_prewhisker.
    etrans. apply transport_f_f.
    etrans. apply maponpaths, assoc_disp.
    etrans. apply transport_f_f.
    etrans. apply maponpaths, maponpaths_2, gf.
    etrans. apply maponpaths, mor_disp_transportf_postwhisker.
    etrans. apply transport_f_f.
    etrans. apply maponpaths, id_left_disp.
    etrans. apply transport_f_f.
    refine (@maponpaths_2 _ _ _ (transportf _) _ (idpath _) _ _).
    apply homset_property.
Qed.

Lemma eq_iso_disp {C : Precategory} {D : disp_precat C}
    {x y : C} (f : iso x y) 
    {xx : D x} {yy} (ff ff' : iso_disp f xx yy)
  : pr1 ff = pr1 ff' -> ff = ff'.
Proof.
  apply subtypeEquality; intro; apply isaprop_is_iso_disp.
Qed.

Definition id_is_iso_disp {C} {D : disp_precat C} {x : C} (xx : D x)
  : is_iso_disp (identity_iso x) (id_disp xx).
Proof.
  exists (id_disp _); split.
  - etrans. apply id_left_disp.
    apply maponpaths_2, homset_property.
  - etrans. apply id_left_disp.
    apply maponpaths_2, homset_property.
Defined.

Definition identity_iso_disp {C} {D : disp_precat C} {x : C} (xx : D x)
  : iso_disp (identity_iso x) xx xx
:= (_ ,, id_is_iso_disp _).

Lemma idtoiso_disp {C} {D : disp_precat C}
    {x x' : C} (e : x = x')
    {xx : D x} {xx' : D x'} (ee : transportf _ e xx = xx')
  : iso_disp (idtoiso e) xx xx'.
Proof.
  destruct e, ee; apply identity_iso_disp.
Defined.

Lemma idtoiso_fiber_disp {C} {D : disp_precat C} {x : C}
    {xx xx' : D x} (ee : xx = xx')
  : iso_disp (identity_iso x) xx xx'.
Proof.
  exact (idtoiso_disp (idpath _) ee).
Defined.

(** TODO: define isofibrations
whenever you have an iso φ : c =~ c' in C, and an object d in D c,
there’s some object d' in D c', and an iso φbar : d =~ d' over φ
*)

Definition iso_fibration {C : Precategory} (D : disp_precat C) : UU
  := 
  forall (c c' : C) (i : iso c c') (d : D c),
          Σ d' : D c', iso_disp i d d'.


End Isos.

Section Categories.

(** The current [is_category_disp] is certainly the correct definition in the case where the base precategory [C] is a category.

When [C] is a general precategory, it’s not quite clear if this definition is correct, or if some other definition might be better. *)

Definition is_category_disp {C} (D : disp_precat C)
  := forall x x' (e : x = x') {xx : D x} {xx' : D x'},
       isweq (λ ee, @idtoiso_disp _ _ _ _ e xx xx' ee).


Lemma is_category_disp_from_fibers {C} {D : disp_precat C}
  : (∀ x (xx xx' : D x), isweq (fun e : xx = xx' => idtoiso_fiber_disp e))
  -> is_category_disp D.
Proof.
  intros H x x' e. destruct e. apply H.
Qed.

Definition disp_category {C}
  := Σ D : disp_precat C, is_category_disp D.

End Categories.


(** * Total category *)

(* Any displayed precategory has a total precategory, with a forgetful functor to the base category. *)
Section Total_Precat.

Context {C : Precategory} (D : disp_precat C).

Definition total_precat_ob_mor : precategory_ob_mor.
Proof.
  exists (Σ x:C, D x).
  intros xx yy.
  (* note: we use projections rather than destructing, so that [ xx ⇒ yy ] 
  can β-reduce without [xx] and [yy] needing to be in whnf *) 
  exact (Σ (f : pr1 xx ⇒ pr1 yy), pr2 xx ⇒[f] pr2 yy).
Defined.

Definition total_precat_id_comp : precategory_id_comp (total_precat_ob_mor).
Proof.
  apply tpair; simpl.
  - intros. exists (identity _). apply id_disp.
  - intros xx yy zz ff gg.
    exists (pr1 ff ;; pr1 gg)%mor.
    exact (pr2 ff ;; pr2 gg).
Defined.

Definition total_precat_data : precategory_data
  := (total_precat_ob_mor ,, total_precat_id_comp).

(* TODO: make notations [( ,, )] and [ ;; ] different levels?  ;; should bind tighter, perhaps, and ,, looser? *)
Lemma total_precat_is_precat : is_precategory (total_precat_data).
Proof.
  repeat apply tpair; simpl.
  - intros xx yy ff; cbn.
    use total2_paths; simpl.
    apply id_left.
    eapply pathscomp0.
      apply maponpaths, id_left_disp.
  (* Note: [transportbfinv] is from [UniMath.Ktheory.Utilities].
  We currently can’t import that, due to notation clashes. *)
    apply Utilities.transportfbinv. 
  - intros xx yy ff; cbn.
    use total2_paths; simpl.
    apply id_right.
    eapply pathscomp0.
      apply maponpaths, id_right_disp.
    apply Utilities.transportfbinv. 
  - intros xx yy zz ww ff gg hh.
    use total2_paths; simpl.
    apply assoc.
    eapply pathscomp0.
      apply maponpaths, assoc_disp.
    apply Utilities.transportfbinv. 
Qed.

(* The “pre-pre-category” version, without homsets *)
Definition total_precat_pre : precategory
  := (total_precat_data ,, total_precat_is_precat).

Lemma total_precat_has_homsets : has_homsets (total_precat_data).
Proof.
  intros xx yy; simpl. apply isaset_total2. apply homset_property.
  intros; apply homsets_disp.
Qed.

Definition total_precat : Precategory
  := (total_precat_pre ,, total_precat_has_homsets).

(** ** Forgetful functor *)

Definition pr1_precat_data : functor_data total_precat C.
Proof.
  exists pr1.
  intros a b; exact pr1.
Defined.

Lemma pr1_precat_is_functor : is_functor pr1_precat_data.
Proof.
  apply tpair.
  - intros x; apply idpath.
  - intros x y z f g; apply idpath.
Qed.  

Definition pr1_precat : functor total_precat C
  := (pr1_precat_data ,, pr1_precat_is_functor).

(** ** Isomorphisms and saturation in the total category *)

(* TODO: define, and sub in, [inv_from_iso_disp], and other access functions. *)

Definition is_iso_total {xx yy : total_precat} (ff : xx ⇒ yy)
  (i : is_iso (pr1 ff))
  (fi := isopair (pr1 ff) i)
  (ii : is_iso_disp fi (pr2 ff))
  : is_iso ff.
Proof.
  apply (@is_iso_qinv total_precat xx yy _ 
           (inv_from_iso fi,, pr1 ii)).
  split.
  - use total2_paths.
    apply (iso_inv_after_iso fi).
    etrans. apply maponpaths. apply (pr2 (pr2 ii)).
    apply Utilities.transportfbinv.
  - use total2_paths.
    apply (iso_after_iso_inv fi).
    etrans. apply maponpaths. apply (pr1 (pr2 ii)).
    apply Utilities.transportfbinv.
Qed.

Definition is_iso_base_from_total {xx yy : total_precat} {ff : xx ⇒ yy} (i : is_iso ff)
  : is_iso (pr1 ff).
Proof.  
  set (ffi := isopair ff i).
  apply (is_iso_qinv _ (pr1 (inv_from_iso ffi))).
  split.
  - exact (maponpaths pr1 (iso_inv_after_iso ffi)).
  - exact (maponpaths pr1 (iso_after_iso_inv ffi)).
Qed.

Definition iso_base_from_total {xx yy : total_precat} (ffi : iso xx yy)
  : iso (pr1 xx) (pr1 yy)
:= isopair _ (is_iso_base_from_total (pr2 ffi)).

Definition inv_iso_base_from_total {xx yy : total_precat} (ffi : iso xx yy)
  : inv_from_iso (iso_base_from_total ffi) = pr1 (inv_from_iso ffi).
Proof.
  apply pathsinv0, inv_iso_unique'. unfold precomp_with.
  exact (maponpaths pr1 (iso_inv_after_iso ffi)).
Qed.

Definition is_iso_disp_from_total {xx yy : total_precat}
    {ff : xx ⇒ yy} (i : is_iso ff)
    (ffi := isopair ff i)
  : is_iso_disp (iso_base_from_total (ff,,i)) (pr2 ff).
Proof.  
  mkpair; [ | split].
  - eapply transportb. apply inv_iso_base_from_total.
    exact (pr2 (inv_from_iso ffi)).
  - etrans. apply mor_disp_transportf_postwhisker.
    etrans. apply maponpaths, @pathsinv0.
      exact (fiber_paths (!iso_after_iso_inv ffi)).
    etrans. apply transport_f_f.
    refine (toforallpaths _ _ _ _ (id_disp _)).
    unfold transportb; apply maponpaths, homset_property.
  - etrans. apply mor_disp_transportf_prewhisker.
    etrans. apply maponpaths, @pathsinv0.
      exact (fiber_paths (!iso_inv_after_iso ffi)).
    etrans. apply transport_f_f.
    refine (toforallpaths _ _ _ _ (id_disp _)).
    unfold transportb; apply maponpaths, homset_property.
Qed.

Definition iso_disp_from_total {xx yy : total_precat}
    (ff : iso xx yy)
  : iso_disp (iso_base_from_total ff) (pr2 xx) (pr2 yy). 
Proof.
  exact (_,, is_iso_disp_from_total (pr2 ff)).
Defined.

Definition total_iso {xx yy : total_precat}
  (f : iso (pr1 xx) (pr1 yy)) (ff : iso_disp f (pr2 xx) (pr2 yy))
  : iso xx yy.
Proof.
  exists (pr1 f,, pr1 ff).
  apply (is_iso_total (pr1 f,, pr1 ff) (pr2 f) (pr2 ff)).
Defined.

Definition total_iso_equiv_map {xx yy : total_precat}
  : (Σ f : iso (pr1 xx) (pr1 yy), iso_disp f (pr2 xx) (pr2 yy))
  -> iso xx yy
:= fun ff => total_iso (pr1 ff) (pr2 ff).

(* TODO: make an uncurried version of this above, as [transportf_iso_disp]? *)
Lemma transportf_iso_disp' {xx yy : total_precat} 
    {f f' : iso (pr1 xx) (pr1 yy)} (e : f = f')
    (ff : iso_disp f (pr2 xx) (pr2 yy))
  : pr1 (transportf (fun g => iso_disp g _ _) e ff)
  = transportf _ (base_paths _ _ e) (pr1 ff).
Proof.
  destruct e; apply idpath.
Qed.

Definition total_iso_isweq (xx yy : total_precat)
  : isweq (@total_iso_equiv_map xx yy).
Proof.
  use gradth.
  - intros ff. exists (iso_base_from_total ff). apply iso_disp_from_total.
  - intros [f ff]. use total2_paths.
    + apply eq_iso, idpath.
    + apply eq_iso_disp.
      etrans. apply transportf_iso_disp'.
      simpl pr2. simpl (pr1 (iso_disp_from_total _)).
      refine (@maponpaths_2 _ _ _ (transportf _) _ (idpath _) _ _). 
      apply homset_property.
  - intros f. apply eq_iso; simpl.
    destruct f as [[f ff] w]; apply idpath.
Qed.

Definition total_iso_equiv (xx yy : total_precat)
  : (Σ f : iso (pr1 xx) (pr1 yy), iso_disp f (pr2 xx) (pr2 yy))
  ≃ iso xx yy
:= weqpair _ (total_iso_isweq xx yy).

Lemma is_category_total_category (CC : is_category C) (DD : is_category_disp D)
  : is_category (total_precat).
Proof.
  split. Focus 2. apply homset_property.
  intros xs ys.
  set (x := pr1 xs). set (xx := pr2 xs).  
  set (y := pr1 ys). set (yy := pr2 ys). 
  assert (lemma : 
   ∀ (A B : Type) (f : A -> B) (w : A ≃ B) (H : w ~ f), isweq f).
  {
    intros A B f w H. apply isweqhomot with w. apply H. apply weqproperty.
  }
  use lemma.
  apply (@weqcomp _ (Σ e : x = y, transportf _ e xx = yy) _).
    apply total2_paths_equiv.
  apply (@weqcomp _ (Σ e : x = y, iso_disp (idtoiso e) xx yy) _).
    apply weqfibtototal. 
    intros e. exists (fun ee => idtoiso_disp e ee). 
    apply DD.
  apply (@weqcomp _ (Σ f : iso x y, iso_disp f xx yy) _).
    refine (weqfp (weqpair _ _) _). apply CC.
  apply total_iso_equiv.
  intros e; destruct e; apply eq_iso; cbn.
    apply idpath.
Qed.

End Total_Precat.

Arguments pr1_precat [C] D.

(** * Functors 

- Reindexing of displayed precats along functors
- Functors into displayed precategories *)

(** ** Reindexing *)

Section Reindexing.

Context {C' C : Precategory} (F : functor C' C) (D : disp_precat C).

Definition reindex_disp_precat_ob_mor : disp_precat_ob_mor C'.
Proof.
  exists (fun c => D (F c)).
  intros x y xx yy f. exact (xx ⇒[# F f] yy).
Defined.

Definition reindex_disp_precat_id_comp : disp_precat_id_comp C' reindex_disp_precat_ob_mor.
Proof.
  apply tpair.
  - simpl; intros x xx.
    refine (transportb _ _ _).
    apply functor_id. apply id_disp.
  - simpl; intros x y z f g xx yy zz ff gg.
    refine (transportb _ _ _).
    apply functor_comp. exact (ff ;; gg).    
Defined.

Definition reindex_disp_precat_data : disp_precat_data C'
  := (_ ,, reindex_disp_precat_id_comp).

Definition reindex_disp_precat_axioms : disp_precat_axioms C' reindex_disp_precat_data.
Proof.
  repeat apply tpair; cbn.
  - intros x y f xx yy ff. 
    eapply pathscomp0. apply maponpaths, compl_disp_transp.
    eapply pathscomp0. apply transport_b_f.
    eapply pathscomp0. apply maponpaths, id_left_disp.
    eapply pathscomp0. apply transport_f_b.
    eapply pathscomp0. Focus 2. apply @pathsinv0, (functtransportb (# F)).
    unfold transportb; apply maponpaths_2, homset_property.
  - intros x y f xx yy ff. 
    eapply pathscomp0. apply maponpaths, compr_disp_transp.
    eapply pathscomp0. apply transport_b_f.
    eapply pathscomp0. apply maponpaths, id_right_disp.
    eapply pathscomp0. apply transport_f_b.
    eapply pathscomp0. Focus 2. apply @pathsinv0, (functtransportb (# F)).
    unfold transportb; apply maponpaths_2, homset_property.
  - intros x y z w f g h xx yy zz ww ff gg hh.
    eapply pathscomp0. apply maponpaths, compr_disp_transp.
    eapply pathscomp0. apply transport_b_f.
    eapply pathscomp0. apply maponpaths, assoc_disp.
    eapply pathscomp0. apply transport_f_b.
    apply pathsinv0.
    eapply pathscomp0. apply (functtransportb (# F)).
    eapply pathscomp0. apply transport_b_b.
    eapply pathscomp0. apply maponpaths, compl_disp_transp.
    eapply pathscomp0. apply transport_b_f.
    unfold transportb; apply maponpaths_2, homset_property.
  - intros; apply homsets_disp.
Qed.

Definition reindex_disp_precat : disp_precat C'
  := (_ ,, reindex_disp_precat_axioms).

End Reindexing.

(** ** Functors into displayed categories *)

(** Just like how context morphisms in a CwA can be built up out of terms, similarly, the basic building-block for functors into (total cats of) displayed precategories will be analogous to a term. 

We call it a _section_ (though we define it intrinsically, not as a section in a (bi)category), since it corresponds to a section of the forgetful functor. *)

Section Sections.

Definition section_disp_data {C} (D : disp_precat C) : Type
  := Σ (Fob : forall x:C, D x),
       (forall (x y:C) (f:x ⇒ y), Fob x ⇒[f] Fob y).

Definition section_disp_on_objects {C} {D : disp_precat C}
  (F : section_disp_data D) (x : C)
:= pr1 F x : D x.

Coercion section_disp_on_objects : section_disp_data >-> Funclass.

Definition section_disp_on_morphisms {C} {D : disp_precat C}
  (F : section_disp_data D) {x y : C} (f : x ⇒ y)
:= pr2 F _ _ f : F x ⇒[f] F y.

Notation "# F" := (section_disp_on_morphisms F)
  (at level 3) : mor_disp_scope.

Definition section_disp_axioms {C} {D : disp_precat C}
  (F : section_disp_data D) : Type
:= ((forall x:C, # F (identity x) = id_disp (F x))
  × (forall (x y z : C) (f : x ⇒ y) (g : y ⇒ z),
      # F (f ;; g)%mor = (# F f) ;; (# F g))).

Definition section_disp {C} (D : disp_precat C) : Type
  := total2 (@section_disp_axioms C D).

Definition section_disp_data_from_section_disp {C} {D : disp_precat C}
  (F : section_disp D) := pr1 F.

Coercion section_disp_data_from_section_disp
  : section_disp >-> section_disp_data.

Definition section_disp_id {C} {D : disp_precat C} (F : section_disp D)
  := pr1 (pr2 F).

Definition section_disp_comp {C} {D : disp_precat C} (F : section_disp D)
  := pr2 (pr2 F).

End Sections.

(** With sections defined, we can now define _lifts_ to a displayed precategory of a functor into the base. *)
Section Functor_Lifting.

Notation "# F" := (section_disp_on_morphisms F)
  (at level 3) : mor_disp_scope.

Definition functor_lifting
  {C C' : Precategory} (D : disp_precat C) (F : functor C' C) 
  := section_disp (reindex_disp_precat F D).

Identity Coercion section_from_functor_lifting
  : functor_lifting >-> section_disp.

(** Note: perhaps it would be better to define [functor_lifting] directly? 
  Reindexed displayed-precats are a bit confusing to work in, since a term like [id_disp xx] is ambiguous: it can mean both the identity in the original displayed category, or the identity in the reindexing, which is nearly but not quite the same.  This shows up already in the proofs of [lifted_functor_axioms] below. *)

Definition lifted_functor_data {C C' : Precategory} {D : disp_precat C}
  {F : functor C' C} (FF : functor_lifting D F)
  : functor_data C' (total_precat D).
Proof.
  exists (fun x => (F x ,, FF x)). 
  intros x y f. exists (# F f)%mor. exact (# FF f).
Defined.

Definition lifted_functor_axioms {C C' : Precategory} {D : disp_precat C}
  {F : functor C' C} (FF : functor_lifting D F)
  : is_functor (lifted_functor_data FF).
Proof.
  split.
  - intros x. use total2_paths; simpl.
    apply functor_id.
    eapply pathscomp0. apply maponpaths, (section_disp_id FF).
    cbn. apply Utilities.transportfbinv.
  - intros x y z f g. use total2_paths; simpl.
    apply functor_comp.
    eapply pathscomp0. apply maponpaths, (section_disp_comp FF).
    cbn. apply Utilities.transportfbinv.
Qed.

Definition lifted_functor {C C' : Precategory} {D : disp_precat C}
  {F : functor C' C} (FF : functor_lifting D F)
  : functor C' (total_precat D)
:= (_ ,, lifted_functor_axioms FF).

End Functor_Lifting.

(** ** Functors over functors between bases *)

(** One could define these in terms of functor-liftings, as:

[[
Definition functor_over {C C' : Precategory} (F : functor C C')
    (D : disp_precat C) (D' : disp_precat C')
  := functor_lifting D' (functor_composite (pr1_precat D) F). 
]]

However, it seems like it may probably be cleaner to define these independently.

TODO: reassess this design decision after some experience using it! *)

Section Functor_Over.

Definition functor_over_data {C' C : precategory_data} (F : functor_data C' C)
  (D' : disp_precat_data C') (D : disp_precat_data C)
:= Σ (Fob : ∀ x, D' x -> D (F x)),
     ∀ x y (xx : D' x) (yy : D' y) (f : x ⇒ y),
       (xx ⇒[f] yy) -> (Fob _ xx ⇒[ # F f ] Fob _ yy).

Definition functor_over_on_objects {C' C : precategory_data} {F : functor_data C' C}
    {D' : disp_precat_data C'} {D : disp_precat_data C}
    (FF : functor_over_data F D' D) {x : C'} (xx : D' x)
  : D (F x)
:= pr1 FF x xx.

Coercion functor_over_on_objects : functor_over_data >-> Funclass.

(** Unfortunately, the coercion loses implicitness of the {x:C'} argument:
  we have to write [ FF _ xx ] instead of just [ FF xx ].

  If anyone knows a way to avoid this, we would be happy to hear it! *)

Definition functor_over_on_morphisms {C' C : precategory_data} {F : functor_data C' C}
    {D' : disp_precat_data C'} {D : disp_precat_data C}
    (FF : functor_over_data F D' D)
    {x y : C'} {xx : D' x} {yy} {f : x ⇒ y} (ff : xx ⇒[f] yy)
  : (FF _ xx) ⇒[ # F f ] (FF _ yy)
:= pr2 FF x y xx yy f ff.

Notation "# F" := (functor_over_on_morphisms F)
  (at level 3) : mor_disp_scope.

Definition functor_over_axioms {C' C : Precategory} {F : functor C' C}
  {D' : disp_precat C'} {D : disp_precat C} (FF : functor_over_data F D' D)
:=  (∀ x (xx : D' x),
      # FF (id_disp xx) = transportb _ (functor_id F x) (id_disp (FF _ xx)))
  × (∀ x y z (xx : D' x) yy zz (f : x ⇒ y) (g : y ⇒ z)
        (ff : xx ⇒[f] yy) (gg : yy ⇒[g] zz),
      # FF (ff ;; gg)
      = transportb _ (functor_comp F _ _ _ f g) (# FF ff ;; # FF gg)).

Definition functor_over {C' C : Precategory} (F : functor C' C)
  (D' : disp_precat C') (D : disp_precat C)
:= Σ FF : functor_over_data F D' D, functor_over_axioms FF.

Definition functor_over_data_from_functor_over
    {C' C} {F} {D' : disp_precat C'} {D : disp_precat C}
    (FF : functor_over F D' D)
  : functor_over_data F D' D
:= pr1 FF.

Coercion functor_over_data_from_functor_over
  : functor_over >-> functor_over_data.

Definition functor_over_id {C' C} {F} {D' : disp_precat C'} {D : disp_precat C}
    (FF : functor_over F D' D)
    {x} (xx : D' x)
  : # FF (id_disp xx) = transportb _ (functor_id F x) (id_disp (FF _ xx))
:= pr1 (pr2 FF) x xx.

Definition functor_over_comp {C' C} {F} {D' : disp_precat C'} {D : disp_precat C}
    (FF : functor_over F D' D)
    {x y z} {xx : D' x} {yy} {zz} {f : x ⇒ y} {g : y ⇒ z}
    (ff : xx ⇒[f] yy) (gg : yy ⇒[g] zz)
  : # FF (ff ;; gg)
    = transportb _ (functor_comp F _ _ _ f g) (# FF ff ;; # FF gg)
:= pr2 (pr2 FF) _ _ _ _ _ _ _ _ ff gg.

Definition functor_over_comp_var {C' C} {F} {D' : disp_precat C'} {D : disp_precat C}
    (FF : functor_over F D' D)
    {x y z} {xx : D' x} {yy} {zz} {f : x ⇒ y} {g : y ⇒ z}
    (ff : xx ⇒[f] yy) (gg : yy ⇒[g] zz)
  : transportf _ (functor_comp F _ _ _ f g) (# FF (ff ;; gg)) 
     = # FF ff ;; # FF gg.
Proof.
  apply Utilities.transportf_pathsinv0.
  apply pathsinv0, functor_over_comp.
Defined.


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

(** Let's see how [functor_over]s behave on [iso_disp]s *)
(** TODO: opacify *)
Undelimit Scope transport.
Definition functor_over_iso_disp_is_iso {C' C} {F} 
    {D' : disp_precat C'} {D : disp_precat C}
    (FF : functor_over F D' D)
    {x y} {xx : D' x} {yy} {f : iso x y} 
    (ff : iso_disp f xx  yy)
    : is_iso_disp (functor_on_iso F f) (# FF ff).
Proof.
  mkpair.
  - set (XR := #FF (inv_mor_disp_from_iso ff)).
(*    Search (_ (inv_from_iso _ ) = inv_from_iso _ ). *)
    apply (transportf _ (functor_on_inv_from_iso _ _ F _ _ f) XR).
  - split.
    + cbn. 
      etrans. apply mor_disp_transportf_postwhisker.
      etrans. apply maponpaths. eapply pathsinv0. 
      apply functor_over_comp_var.
      etrans. apply transport_f_f.
      etrans. apply maponpaths. apply maponpaths. 
              apply iso_disp_after_inv_mor.
      etrans. apply maponpaths. apply functor_over_transportf.
      etrans. apply transport_f_f.
      etrans. apply maponpaths. apply functor_over_id.
      etrans. apply transport_f_f.
      
      apply transportf_comp_lemma.
      apply transportf_comp_lemma_hset.
      apply homset_property. apply idpath.
    +       etrans. apply mor_disp_transportf_prewhisker.
      etrans. apply maponpaths. eapply pathsinv0. 
      apply functor_over_comp_var.
      etrans. apply transport_f_f.
      etrans. apply maponpaths. apply maponpaths. 
              apply inv_mor_after_iso_disp.
      etrans. apply maponpaths. apply functor_over_transportf.
      etrans. apply transport_f_f.
      etrans. apply maponpaths. apply functor_over_id.
      etrans. apply transport_f_f.
      
      apply transportf_comp_lemma.
      apply transportf_comp_lemma_hset.
      apply homset_property. apply idpath.
Defined.



(* not needed, let's remove it *)
Definition functor_over_identity_ff {C} 
  {D' D: disp_precat C} (FF : functor_over (functor_identity _ ) D' D) : UU
  :=
    forall (x' x : C) (xx' : D' x') (xx : D' x) (f : x' ⇒ x),
           isweq (fun ff : xx' ⇒[f] xx => # FF ff).

Definition functor_over_ff {C' C} {F} {D' : disp_precat C'} {D : disp_precat C}
    (FF : functor_over F D' D)
    :=
      ∀ {x y} {xx : D' x} {yy : D' y} {f : x ⇒ y},
           isweq (fun ff : xx ⇒[f] yy => # FF ff).


(* 
F : C' —> C
and FF : D' —> D' over it
then FF is essentially surjective (relative to F)
if for any c' in C'
and d in D (F c')
there’s some dbar in D' c
and an iso FF (dbar) =~ d in D' (F c), over the identity?
alternatively,
actually I guess this is probably better,
given the same inputs,
there’s some c' in C',
an iso φ : c' =~ c in C',
some dbar in D' c',
and an iso FF dbar =~ d
over F φ.
*)

Definition functor_over_ess_split_surj {C' C : Precategory} (F : functor C' C)
  {D' : disp_precat C'} {D : disp_precat C} 
  (FF : functor_over F D' D) : UU
  :=
    forall (c' : C') (d : D (F c')),
      Σ c'' : C', 
      Σ i : iso c'' c', 
      Σ dbar : D' c'',
      iso_disp (functor_on_iso F i) (FF _ dbar) d.

Definition total_functor_data {C' C} {F}
    {D' : disp_precat C'} {D : disp_precat C} (FF : functor_over F D' D)
  : functor_data (total_precat D') (total_precat D).
Proof.
  mkpair.
  - intros xx. exists (F (pr1 xx)). exact (FF _ (pr2 xx)).
  - intros xx yy ff. exists (# F (pr1 ff))%mor. exact (# FF (pr2 ff)).
Defined.

Definition total_functor_axioms {C' C} {F}
    {D' : disp_precat C'} {D : disp_precat C} (FF : functor_over F D' D)
  : is_functor (total_functor_data FF).
Proof.
  split.
  - intros xx; use total2_paths.
      apply functor_id.
    etrans. apply maponpaths, functor_over_id.
    apply Utilities.transportfbinv.
  - intros xx yy zz ff gg; use total2_paths; simpl.
      apply functor_comp.
    etrans. apply maponpaths, functor_over_comp.
    apply Utilities.transportfbinv.
Qed.

Definition total_functor {C' C} {F}
    {D' : disp_precat C'} {D : disp_precat C} (FF : functor_over F D' D)
  : functor (total_precat D') (total_precat D)
:= (total_functor_data FF,, total_functor_axioms FF).

End Functor_Over.

(** * Products of displayed (pre)categories 

We directly define direct products of displayed categories over a base.

An alternative would be to define the direct product as the “Sigma-precategory” of the pullback to either factor.  *)
Section Dirprod.

Context {C : Precategory} (D1 D2 : disp_precat C).

Definition dirprod_disp_precat_ob_mor : disp_precat_ob_mor C.
Proof.
  exists (fun c => (D1 c × D2 c)).
  intros x y xx yy f.
  exact (pr1 xx ⇒[f] pr1 yy × pr2 xx ⇒[f] pr2 yy).
Defined.

Definition dirprod_disp_precat_id_comp
  : disp_precat_id_comp _ dirprod_disp_precat_ob_mor.
Proof.
  apply tpair.
  - intros x xx. exact (id_disp _,, id_disp _).
  - intros x y z f g xx yy zz ff gg.
    exact ((pr1 ff ;; pr1 gg),, (pr2 ff ;; pr2 gg)).
Defined.

Definition dirprod_disp_precat_data : disp_precat_data C
  := (_ ,, dirprod_disp_precat_id_comp).

(* TODO: move!  Also consider implicit args of pr1_transportf?? *)
Lemma pr2_transportf {A} {B1 B2 : A → Type} 
    {a a' : A} (e : a = a') (xs : B1 a × B2 a)
  : pr2 (transportf (fun a => B1 a × B2 a) e xs) = transportf _ e (pr2 xs).
Proof.
  destruct e. apply idpath.
Defined.

Definition dirprod_disp_precat_axioms
  : disp_precat_axioms _ dirprod_disp_precat_data.
Proof.
  repeat apply tpair.
  - intros. apply dirprod_paths; refine (id_left_disp @ !_).
    + refine (pr1_transportf _ _ _ _ _ _ _).
    + apply pr2_transportf.
  - intros. apply dirprod_paths; refine (id_right_disp @ !_).
    + refine (pr1_transportf _ _ _ _ _ _ _).
    + apply pr2_transportf.
  - intros. apply dirprod_paths; refine (assoc_disp @ !_).
    + refine (pr1_transportf _ _ _ _ _ _ _).
    + apply pr2_transportf.
  - intros. apply isaset_dirprod; apply homsets_disp.
Qed.

Definition dirprod_disp_precat : disp_precat C
  := (_ ,, dirprod_disp_precat_axioms).

Definition dirprodpr1_disp_functor_data
  : functor_over_data (functor_identity C) dirprod_disp_precat (D1).
Proof.
  mkpair.
  - intros x xx; exact (pr1 xx).
  - intros x y xx yy f ff; exact (pr1 ff).
Defined.

Definition dirprodpr1_disp_functor_axioms
  : functor_over_axioms dirprodpr1_disp_functor_data.
Proof.
  split. 
  - intros; apply idpath.
  - intros; apply idpath.
Qed.

Definition dirprodpr1_disp_functor
  : functor_over (functor_identity C) dirprod_disp_precat (D1)
:= (dirprodpr1_disp_functor_data,, dirprodpr1_disp_functor_axioms).


Definition dirprodpr2_disp_functor_data
  : functor_over_data (functor_identity C) dirprod_disp_precat (D2).
Proof.
  mkpair.
  - intros x xx; exact (pr2 xx).
  - intros x y xx yy f ff; exact (pr2 ff).
Defined.

Definition dirprodpr2_disp_functor_axioms
  : functor_over_axioms dirprodpr2_disp_functor_data.
Proof.
  split. 
  - intros; apply idpath.
  - intros; apply idpath.
Qed.

Definition dirprodpr2_disp_functor
  : functor_over (functor_identity C) dirprod_disp_precat (D2)
:= (dirprodpr2_disp_functor_data,, dirprodpr2_disp_functor_axioms).

End Dirprod.

Notation "D1 × D2" := (dirprod_disp_precat D1 D2) : disp_precat_scope.
Delimit Scope disp_precat_scope with disp_precat.
Bind Scope disp_precat_scope with disp_precat.

(** * Examples 

A typical use for displayed categories is for constructing categories of structured objects, over a given (specific or general) category. We give a few examples here:

- arrow precategories
- objects with N-actions
- elements, over hSet

*)

(** ** The displayed arrow category 

A very fertile example: many others can be obtained from it by reindexing. *)
Section Arrow_Disp.

Context (C:Precategory).

Definition arrow_disp_ob_mor : disp_precat_ob_mor (C × C).
Proof.
  exists (fun xy : (C × C) => (pr1 xy) ⇒ (pr2 xy)).
  simpl; intros xx' yy' g h ff'. 
    exact (pr1 ff' ;; h = g ;; pr2 ff')%mor.
Defined.

Definition arrow_id_comp : disp_precat_id_comp _ arrow_disp_ob_mor.
Proof.
  split.
  - simpl; intros.
    eapply pathscomp0. apply id_left. apply pathsinv0, id_right.
  - simpl; intros x y z f g xx yy zz ff gg.
    eapply pathscomp0. apply @pathsinv0, assoc.
    eapply pathscomp0. apply maponpaths, gg.
    eapply pathscomp0. apply assoc.
    eapply pathscomp0. apply cancel_postcomposition, ff.
    apply pathsinv0, assoc.
Qed.

Definition arrow_data : disp_precat_data _
  := (arrow_disp_ob_mor ,, arrow_id_comp).

Lemma arrow_axioms : disp_precat_axioms (C × C) arrow_data.
Proof.
  repeat apply tpair; intros; try apply homset_property.
  apply isasetaprop, homset_property. 
Qed.

Definition arrow_disp : disp_precat (C × C)
  := (arrow_data ,, arrow_axioms).

End Arrow_Disp.

(** ** Objects with N-action

For any category C, “C-objects equipped with an N-action” (or more elementarily, with an endomorphism) form a displayed category over C 
Section ZAct. 

Once we have pullbacks of displayed precategories, this can be obtained as a pullback of the previous example. *)

Section NAction.

Context (C:Precategory).

Definition NAction_disp_ob_mor : disp_precat_ob_mor C.
Proof.
  exists (fun c => c ⇒ c).
  intros x y xx yy f. exact (f ;; yy = xx ;; f)%mor.
Defined.

Definition NAction_id_comp : disp_precat_id_comp C NAction_disp_ob_mor.
Proof.
  split.
  - simpl; intros.
    eapply pathscomp0. apply id_left. apply pathsinv0, id_right.
  - simpl; intros x y z f g xx yy zz ff gg.
    eapply pathscomp0. apply @pathsinv0, assoc.
    eapply pathscomp0. apply maponpaths, gg.
    eapply pathscomp0. apply assoc.
    eapply pathscomp0. apply cancel_postcomposition, ff.
    apply pathsinv0, assoc.
Qed.

Definition NAction_data : disp_precat_data C
  := (NAction_disp_ob_mor ,, NAction_id_comp).

Lemma NAction_axioms : disp_precat_axioms C NAction_data.
Proof.
  repeat apply tpair; intros; try apply homset_property.
  apply isasetaprop, homset_property. 
Qed.

Definition NAction_disp : disp_precat C
  := (NAction_data ,, NAction_axioms).

End NAction.

(** ** Elements of sets

A presheaf on a (pre)category can be viewed as a fibrewise discrete displayed (pre)category. In fact, the universal example of this is the case corresponding to the identity functor on [SET].  So, having given the displayed category for this case, one obtains it for arbitrary presheaves by reindexing. *)

(* TODO: move? ponder? *)
Local Notation SET := Precategories.SET.

Section Elements_Disp.

Definition elements_ob_mor : disp_precat_ob_mor SET.
Proof.
  use tpair.
  - simpl. exact (fun X => X).
  - simpl. intros X Y x y f. exact (f x = y).
Defined.

Lemma elements_id_comp : disp_precat_id_comp SET elements_ob_mor.
Proof.
  apply tpair; simpl.
  - intros X x. apply idpath.
  - intros X Y Z f g x y z e_fx_y e_gy_z. cbn.
    eapply pathscomp0. apply maponpaths, e_fx_y. apply e_gy_z.
Qed.

Definition elements_data : disp_precat_data SET
  := (_ ,, elements_id_comp).

Lemma elements_axioms : disp_precat_axioms SET elements_data.
Proof.
  repeat split; intros; try apply setproperty.
  apply isasetaprop; apply setproperty.
Qed.

Definition elements_universal : disp_precat SET
  := (_ ,, elements_axioms).

Definition disp_precat_of_elements {C : Precategory} (P : functor C SET)
  := reindex_disp_precat P elements_universal.

(* TODO: compare to other definitions of this in the library! *)
Definition precat_of_elements {C : Precategory} (P : functor C SET)
  := total_precat (disp_precat_of_elements P).

End Elements_Disp.

(** TODOs:

- add definitions of fibrations/isofibrations
- add lemmas connecting with products of precats (as required for displayed bicats)
- add more applications of the displayed arrow category: slices; equalisers, inserters; hence groups etc.

*)
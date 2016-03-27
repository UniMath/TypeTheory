(**
A module for “displayed precategories”, based over UniMath’s [CategoryTheory] library.

Roughly, a “displayed category _D_ over a precategory _C_” is analogous to “a family of types _Y_ indexed over a type _X_”.  A displayed category has a “total category” Σ _C_ _D_, with a functor to _D_; and indeed displayed categories should be equivalent to categories over _D_, by taking fibres.

In a little more detail: if [D] is a displayed precategory over [C], then [D] has a type of objects indexed over [ob C], and for each [x y : C, f : x ⇒ y, xx : D x, yy : D y], a type of “morphisms over [f] from [xx] to [yy]”.  The identity and composition (and axioms) for [D] all overlie the corresponding structure on [C].

Two major motivations for displayed categories:

- Pragmatically, they give a technical tool for building categories of “structured objects”, and functors into such categories, encapsulating a lot of frequently-used contstructions.
- More conceptually, they give a setting for developing the theory of Grothendieck fibrations and isofibrations, without mentioning equality of objects.

*)

Require Import UniMath.CategoryTheory.UnicodeNotations.

Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.

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
  := Σ (obd : C -> Type), (∀ x y:C, (x ⇒ y) -> obd x -> obd y -> Type).

Definition ob_disp {C} (D : disp_precat_ob_mor C) := pr1 D.
Coercion ob_disp : disp_precat_ob_mor >-> Funclass.

Definition mor_disp {C} {D : disp_precat_ob_mor C}
  {x y} (f : x ⇒ y) xx yy
:= pr2 D x y f xx yy : Type. 

Local Notation "xx ⇒[ f ] yy" := (mor_disp f xx yy) (at level 50, yy at next level).

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

Definition disp_precat_axioms (C : Precategory) (D : disp_precat_data C)
  : Type
:= (∀ x y (f : x ⇒ y) (xx : D x) yy (ff : xx ⇒[f] yy),
     id_disp _ ;; ff
     = transportb (fun k => mor_disp k _ _) (id_left _) ff)%mor_disp
   × (∀ x y (f : x ⇒ y) (xx : D x) yy (ff : xx ⇒[f] yy),
     ff ;; id_disp _
     = transportb (fun k => mor_disp k _ _) (id_right _) ff)%mor_disp
   × (∀ x y z w f g h (xx : D x) (yy : D y) (zz : D z) (ww : D w)
        (ff : xx ⇒[f] yy) (gg : yy ⇒[g] zz) (hh : zz ⇒[h] ww),
     ff ;; (gg ;; hh)
     = transportb (fun k => mor_disp k _ _) (assoc _ _ _)
       ((ff ;; gg) ;; hh))%mor_disp
   × (∀ x y f (xx : D x) (yy : D y), isaset (xx ⇒[f] yy)).

Definition disp_precat (C : Precategory) := total2 (disp_precat_axioms C).

Definition disp_precat_data_from_disp_precat {C} (D : disp_precat C)
 := pr1 D : disp_precat_data C.
Coercion disp_precat_data_from_disp_precat : disp_precat >-> disp_precat_data.

Definition id_left_disp {C} {D : disp_precat C} 
  {x y} {f : x ⇒ y} {xx : D x} {yy} {ff : xx ⇒[f] yy}
: (id_disp _ ;; ff
  = transportb (fun k => mor_disp k _ _) (id_left _) ff)%mor_disp
:= pr1 (pr2 D) _ _ _ _ _ _.

Definition id_right_disp {C} {D : disp_precat C} 
  {x y} {f : x ⇒ y} {xx : D x} {yy} {ff : xx ⇒[f] yy}
  : (ff ;; id_disp _
    = transportb (fun k => mor_disp k _ _) (id_right _) ff)%mor_disp
:= pr1 (pr2 (pr2 D)) _ _ _ _ _ _.

Definition assoc_disp {C} {D : disp_precat C}
  {x y z w} {f} {g} {h} {xx : D x} {yy : D y} {zz : D z} {ww : D w}
  {ff : xx ⇒[f] yy} {gg : yy ⇒[g] zz} {hh : zz ⇒[h] ww}
: (ff ;; (gg ;; hh)
  = transportb (fun k => mor_disp k _ _) (assoc _ _ _)
      ((ff ;; gg) ;; hh))%mor_disp
:= pr1 (pr2 (pr2 (pr2 D))) _ _ _ _ _ _ _ _ _ _ _ _ _ _.

Definition homsets_disp {C} {D :disp_precat C} {x y} {f} {xx : D x} {yy : D y}
  : isaset (xx ⇒[f] yy)
:= pr2 (pr2 (pr2 (pr2 D))) _ _ _ _ _.

(** TODO: prove this lemma!  (Probably not often needed, but would be nice to know.) *)
Lemma isaprop_disp_precat_axioms (C : Precategory) (D : disp_precat_data C)
  : isaprop (disp_precat_axioms C D).
Abort.

End Disp_Precat.

(** Redeclare sectional notations globally. *)
Notation "xx ⇒[ f ] yy" := (mor_disp f xx yy) (at level 50, yy at next level).

Notation "ff ;; gg" := (comp_disp ff gg)
  (at level 50, left associativity, format "ff  ;;  gg")
  : mor_disp_scope.
Delimit Scope mor_disp_scope with mor_disp.
Bind Scope mor_disp_scope with mor_disp.

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
    exists (pr1 ff ;; pr1 gg).
    exact (pr2 ff ;; pr2 gg)%mor_disp.
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
  (* Note: [transportbfinv] is from [UniMath.Ktheory.Utilities.
  We currently can’t import that, due to notation clashes. *)
    exact (Utilities.transportfbinv _ _ (pr2 ff)).
  - intros xx yy ff; cbn.
    use total2_paths; simpl.
    apply id_right.
    eapply pathscomp0.
      apply maponpaths, id_right_disp.
    exact (Utilities.transportfbinv _ _ (pr2 ff)).
  - intros xx yy zz ww ff gg hh.
    use total2_paths; simpl.
    apply assoc.
    eapply pathscomp0.
      apply maponpaths, assoc_disp.
    exact (Utilities.transportfbinv (fun k => _ ⇒[k] _) _ _).
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

(** ** Forgetful functor from the total precategory *)

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

End Total_Precat.

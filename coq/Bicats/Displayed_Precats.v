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
  - [pr1_functor]
- Examples

*)

Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.

Require UniMath.Ktheory.Utilities.

Require Import Systems.Auxiliary.
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

(** ** Some utility lemmas *)
Section Lemmas.

(** TODO: prove this lemma!  Probably not needed, but would be nice to know. *)
Lemma isaprop_disp_precat_axioms (C : Precategory) (D : disp_precat_data C)
  : isaprop (disp_precat_axioms C D).
Abort.

Lemma compl_disp_transp {C : Precategory} {D : disp_precat_data C}
    {x y z : C} {f f' : x ⇒ y} (ef : f = f') {g : y ⇒ z}
    {xx : D x} {yy} {zz} (ff : xx ⇒[f] yy) (gg : yy ⇒[g] zz)
  : ((transportf (fun k => _ ⇒[k] _) ef ff) ;; gg
  = transportf (fun k => _ ⇒[k] _)
    (maponpaths (fun k => k ;; _)%mor ef) (ff ;; gg))%mor_disp.
Proof.
  destruct ef. apply idpath.
Qed.

Lemma compr_disp_transp {C : Precategory} {D : disp_precat_data C}
    {x y z : C} {f : x ⇒ y} {g g' : y ⇒ z} (eg : g = g')
    {xx : D x} {yy} {zz} (ff : xx ⇒[f] yy) (gg : yy ⇒[g] zz)
  : (ff ;; (transportf (fun k => _ ⇒[k] _) eg gg)
  = transportf (fun k => _ ⇒[k] _)
    (maponpaths (fun k => _ ;; k)%mor eg) (ff ;; gg))%mor_disp.
Proof.
  destruct eg. apply idpath.
Qed.

End Lemmas.

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

End Total_Precat.

Arguments pr1_precat [C D].

(** * Functors 

- Reindexing of displayed precats along functors
- Functors into displayed precategories *)

(** ** Reindexing *)

Section Reindexing.

Context {C' C : Precategory} (F : functor C' C) (D : disp_precat C).

(* TODO: search/replace [disp_precat] to [disp_precat] once done *)
Definition reindex_disp_precat_ob_mor : disp_precat_ob_mor C'.
Proof.
  exists (fun c => D (F c)).
  intros x y f xx yy. exact (xx ⇒[# F f] yy).
Defined.

Definition reindex_disp_precat_id_comp : disp_precat_id_comp C' reindex_disp_precat_ob_mor.
Proof.
  apply tpair.
  - simpl; intros x xx.
    refine (transportb (fun g => _ ⇒[g] _) _ _).
    apply functor_id. apply id_disp.
  - simpl; intros x y z f g xx yy zz ff gg.
    refine (transportb (fun g => _ ⇒[g] _) _ _).
    apply functor_comp. exact (ff ;; gg)%mor_disp.    
Defined.

Definition reindex_disp_precat_data : disp_precat_data C'
  := (_ ,, reindex_disp_precat_id_comp).

Definition reindex_disp_precat_axioms : disp_precat_axioms C' reindex_disp_precat_data.
Proof.
  repeat apply tpair; cbn.
  - intros x y f xx yy ff. 
    eapply pathscomp0. apply maponpaths, compl_disp_transp.
    eapply pathscomp0. refine (transport_b_f (fun g => _ ⇒[g] _) _ _ _).
    eapply pathscomp0. apply maponpaths, id_left_disp.
    eapply pathscomp0. refine (transport_f_b (fun g => _ ⇒[g] _) _ _ _).
    eapply pathscomp0. Focus 2. eapply pathsinv0.
      refine (functtransportb (# F) (fun g => _ ⇒[g] _) _ _).
    refine (toforallpaths _ _ _ _ ff). unfold transportb; apply maponpaths.
    apply homset_property.
  - intros x y f xx yy ff. 
    eapply pathscomp0. apply maponpaths, compr_disp_transp.
    eapply pathscomp0. refine (transport_b_f (fun g => _ ⇒[g] _) _ _ _).
    eapply pathscomp0. apply maponpaths, id_right_disp.
    eapply pathscomp0. refine (transport_f_b (fun g => _ ⇒[g] _) _ _ _).
    eapply pathscomp0. Focus 2. eapply pathsinv0.
      refine (functtransportb (# F) (fun g => _ ⇒[g] _) _ _).
    refine (toforallpaths _ _ _ _ ff). unfold transportb; apply maponpaths.
    apply homset_property.
  - intros x y z w f g h xx yy zz ww ff gg hh.
    eapply pathscomp0. apply maponpaths, compr_disp_transp.
    eapply pathscomp0. refine (transport_b_f (fun g => _ ⇒[g] _) _ _ _).
    eapply pathscomp0. apply maponpaths, assoc_disp.
    eapply pathscomp0. refine (transport_f_b (fun g => _ ⇒[g] _) _ _ _).
    apply pathsinv0.
    eapply pathscomp0.
      refine (functtransportb (# F) (fun g => _ ⇒[g] _) _ _).
    eapply pathscomp0. refine (transport_b_b (fun g => _ ⇒[g] _) _ _ _).
    eapply pathscomp0. apply maponpaths, compl_disp_transp.
    eapply pathscomp0. refine (transport_b_f (fun g => _ ⇒[g] _) _ _ _).
    refine (toforallpaths _ _ _ _ (ff ;; gg ;; hh)%mor_disp).
    unfold transportb; apply maponpaths.
    apply homset_property.
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

Notation "## F" := (section_disp_on_morphisms F)
  (at level 3) : mor_disp_scope.

Definition section_disp_axioms {C} {D : disp_precat C}
  (F : section_disp_data D) : Type
:= ((forall x:C, ## F (identity x) = id_disp (F x))
  × (forall (x y z : C) (f : x ⇒ y) (g : y ⇒ z),
      ## F (f ;; g)%mor = (## F f) ;; (## F g)))%mor_disp.

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

Notation "## F" := (section_disp_on_morphisms F)
  (at level 3) : mor_disp_scope.

(** With sections defined, we can now define _lifts_ to a displayed precategory of a functor into the base. *)
Section Functor_Disp.

Definition functor_disp
  {C C' : Precategory} (D : disp_precat C) (F : functor C' C) 
  := section_disp (reindex_disp_precat F D).

Identity Coercion section_from_functor_disp
  : functor_disp >-> section_disp.

(** Note: perhaps it would be better to define [functor_disp] directly? 
  Reindexed displayed-precats are a bit confusing to work in, since a term like [id_disp xx] is ambiguous: it can mean both the identity in the original displayed category, or the identity in the reindexing, which is nealry but not quite the same.  This shows up already in the proofs of [total_functor_axioms] below. *)

Definition total_functor_data {C C' : Precategory} {D : disp_precat C}
  {F : functor C' C} (FF : functor_disp D F)
  : functor_data C' (total_precat D).
Proof.
  exists (fun x => (F x ,, FF x)). 
  intros x y f. exists (# F f). exact (## FF f)%mor_disp.
Defined.

Definition total_functor_axioms {C C' : Precategory} {D : disp_precat C}
  {F : functor C' C} (FF : functor_disp D F)
  : is_functor (total_functor_data FF).
Proof.
  split.
  - intros x. use total2_paths; simpl.
    apply functor_id.
    eapply pathscomp0. apply maponpaths, (section_disp_id FF).
    cbn.
    refine (Utilities.transportfbinv (fun (g : F _ ⇒ F _) => _ ⇒[g] _) _ _).
  - intros x y z f g. use total2_paths; simpl.
    apply functor_comp.
    eapply pathscomp0. apply maponpaths, (section_disp_comp FF).
    cbn.
    refine (Utilities.transportfbinv (fun (g : F _ ⇒ F _) => _ ⇒[g] _) _ _).
Qed.

Definition total_functor {C C' : Precategory} {D : disp_precat C}
  {F : functor C' C} (FF : functor_disp D F)
  : functor C' (total_precat D)
:= (_ ,, total_functor_axioms FF).

End Functor_Disp.

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
  simpl; intros xx' yy' ff' g h. 
    exact (pr1 ff' ;; h = g ;; pr2 ff').
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
    eapply pathscomp0. eapply (maponpaths (fun f' => f' ;; _)), ff.
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
  intros x y f xx yy. exact (f ;; yy = xx ;; f).
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
    eapply pathscomp0. eapply (maponpaths (fun f' => f' ;; g)), ff.
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
  - simpl. intros X Y f x y. exact (f x = y).
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

(* TODOs:

- add definitions of fibrations/isofibrations
- add lemmas connecting with products of precats (as required for displayed bicats)
- add more applications of the displayed arrow category: slices; equalisers, inserters; hence groups etc.

*)
(**
  [TypeTheory.ALV2.RelUniv_Cat]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(** 
Main definitions:

  TODO: list!
*)

Require Import UniMath.Foundations.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.limits.pullbacks.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.RelativeUniverses.

Local Set Automatic Introduction.
(* only needed since imports globally unset it *)

Section RelUniv_Cat.

  Context (C D : category).

  Context (J : functor C D).

  Local Definition Ũ (u : relative_universe J) := source (pr1 u).
  Local Definition U  (u : relative_universe J) := target (pr1 u).
  Local Definition Xf (u : relative_universe J)
        (X : C) (f : J X --> U u) : C
    := pr1 (pr1 (pr2 u X f)).
  Local Definition π (u : relative_universe J)
        (X : C) (f : J X --> U u) : C ⟦ Xf u X f, X ⟧
    := pr1 (pr2 (pr1 (pr2 u X f))).
  Local Definition Q (u : relative_universe J)
        (X : C) (f : J X --> U u) : D ⟦ J (Xf u X f), Ũ u ⟧
    := pr2 (pr2 (pr1 (pr2 u X f))).
  Local Definition u_commutes (u : relative_universe J)
        (X : C) (f : J X --> U u)
    : # J (fp (pr1 (pr2 u X f)));; f = fq (pr1 (pr2 u X f));; pr1 u
    := pr1 (pr2 (pr2 u X f)).
  Local Definition u_isPullback (u : relative_universe J)
        (X : C) (f : J X --> U u)
    : isPullback f (pr1 u) (# J (fp (pr1 (pr2 u X f))))
                 (fq (pr1 (pr2 u X f))) (pr1 (pr2 (pr2 u X f)))
    := pr2 (pr2 (pr2 u X f)).

  Definition relative_universe_mor_data
             (u1 u2 : relative_universe J)
    : UU
    := (Ũ u1 --> Ũ u2) × (U u1 --> U u2).

  Local Definition F_Ũ
        {u1 u2 : relative_universe J}
        (mor : relative_universe_mor_data u1 u2)
    : Ũ u1 --> Ũ u2
    := pr1 mor.
  Local Definition F_U
        {u1 u2 : relative_universe J}
        (mor : relative_universe_mor_data u1 u2)
    : U u1 --> U u2
    := pr2 mor.

  Definition is_relative_universe_mor
             {u1 u2 : relative_universe J}
             (mor : relative_universe_mor_data u1 u2)
    : UU
    := F_Ũ mor ;; pr1 u2 = pr1 u1 ;; F_U mor.

  Definition relative_universe_mor
             (u1 u2 : relative_universe J)
    : UU
    := ∑ (mor : relative_universe_mor_data u1 u2),
       is_relative_universe_mor mor.

  Coercion relative_universe_mor_to_data
           (u1 u2 : relative_universe J)
           (mor : relative_universe_mor u1 u2)
    : relative_universe_mor_data u1 u2
    := pr1 mor.

  Definition relative_universe_mor_J_F_Xf
             {u1 u2 : relative_universe J}
             (mor : relative_universe_mor u1 u2)
    : ∏ (X : C) (f : J X --> U u1),
      J (Xf u1 X f) --> J (Xf u2 X (f ;; F_U mor)).
  Proof.
    intros X f.
    apply (u_isPullback u2 X (f ;; F_U mor)
                        _ (# J (π u1 X f)) (Q u1 X f ;; F_Ũ mor)).
    etrans. apply assoc.
    etrans. apply maponpaths_2, (u_commutes u1 X f).
    etrans. apply assoc'.
    apply pathsinv0.
    etrans. apply assoc'.
    apply maponpaths.
    apply (pr2 mor).
  Defined.

  Definition relative_universe_mor_F_Xf
             {u1 u2 : relative_universe J}
             (mor : relative_universe_mor u1 u2)
             (ff_J : fully_faithful J)
    : ∏ (X : C) (f : J X --> U u1),
      Xf u1 X f --> Xf u2 X (f ;; F_U mor).
  Proof.
    intros X f.
    apply ff_J.
    apply relative_universe_mor_J_F_Xf.
  Defined.

  Definition relative_universe_mor_axiom_F_Xf_π
             (u1 u2 : relative_universe J)
             (mor : relative_universe_mor u1 u2)
             (ff_J : fully_faithful J)
    : ∏ (X : C) (f : J X --> U u1),
      relative_universe_mor_F_Xf mor ff_J X f ;; π u2 X (F_U mor ∘ f)
      = π u1 X f.
  Proof.
    intros X f.
    apply (invmaponpathsweq (# J ,, ff_J _ _)).
    etrans. apply functor_comp.
    etrans. apply (maponpaths (λ k, k ;; _)
                              (homotweqinvweq (# J ,, ff_J _ _) _)).
    simpl.
    set (u2_Pullback
         := make_Pullback
              _ _ _ _ _ _
              (u_isPullback u2 X (f ;; F_U mor))).
    apply (PullbackArrow_PullbackPr1 u2_Pullback).
  Defined.

  Definition relative_universe_mor_axiom_F_Xf_Q
             (u1 u2 : relative_universe J)
             (mor : relative_universe_mor u1 u2)
    : ∏ (X : C) (f : J X --> U u1),
      relative_universe_mor_J_F_Xf mor X f ;; Q u2 X (F_U mor ∘ f)
      = Q u1 X f ;; F_Ũ mor.
  Proof.
    intros X f.
    set (u2_Pullback
         := make_Pullback
              _ _ _ _ _ _
              (u_isPullback u2 X (f ;; F_U mor))).
    apply (PullbackArrow_PullbackPr2 u2_Pullback).
  Defined.

  Definition isaprop_is_relative_universe_mor
             {u1 u2 : relative_universe J}
             (mor : relative_universe_mor_data u1 u2)
    : isaprop (is_relative_universe_mor mor).
  Proof.
    apply homset_property.
  Defined.

  Definition relative_universe_mor_eq
             (u1 u2 : relative_universe J)
             (g h : relative_universe_mor u1 u2)
             (e_Ũ : F_Ũ g = F_Ũ h)
             (e_U : F_U g = F_U h)
    : g = h.
  Proof.
    use total2_paths_f.
    - use dirprod_paths.
      + apply e_Ũ.
      + apply e_U.
    - apply isaprop_is_relative_universe_mor.
  Defined.
  
  Definition relative_universe_mor_id
             (u : relative_universe J)
    : relative_universe_mor u u.
  Proof.
    use tpair.
    - exists (identity _).
      apply identity.
    - unfold is_relative_universe_mor. simpl.
      etrans. apply id_left.
      apply pathsinv0, id_right.
  Defined.

  Definition relative_universe_mor_comp
             (a b c : relative_universe J)
             (g : relative_universe_mor a b)
             (h : relative_universe_mor b c)
    : relative_universe_mor a c.
  Proof.
    use tpair.
    - exists (F_Ũ g ;; F_Ũ h).
      exact (F_U g ;; F_U h).
    - unfold is_relative_universe_mor. simpl.
      etrans. apply assoc'.
      etrans. apply maponpaths, (pr2 h).
      etrans. apply assoc.
      etrans. apply maponpaths_2, (pr2 g).
      apply assoc'.
  Defined.

  Definition reluniv_precat_ob_mor : precategory_ob_mor
    := (relative_universe J ,, relative_universe_mor).

  Definition reluniv_precat_id_comp
    : precategory_id_comp reluniv_precat_ob_mor
    := (relative_universe_mor_id ,, relative_universe_mor_comp).

  Definition reluniv_precat_data : precategory_data
    := (reluniv_precat_ob_mor ,, reluniv_precat_id_comp).

  Definition reluniv_is_precategory : is_precategory reluniv_precat_data.
  Proof.
    use make_is_precategory_one_assoc.
    - intros a b g.
      use relative_universe_mor_eq.
      * apply id_left.
      * apply id_left.
    - intros a b g.
      use relative_universe_mor_eq.
      * apply id_right.
      * apply id_right.
    - intros a b c d g h k.
      use relative_universe_mor_eq.
      * apply assoc.
      * apply assoc.
  Defined.

  Definition reluniv_precat : precategory
    := ( reluniv_precat_data ,, reluniv_is_precategory ).

  Definition isaset_relative_universe_mor
             (u1 u2 : relative_universe J)
    : isaset (relative_universe_mor u1 u2).
  Proof.
    apply isaset_total2.
    - apply isaset_dirprod.
      + apply homset_property.
      + apply homset_property.
    - intros mor.
      apply isasetaprop.
      apply isaprop_is_relative_universe_mor.
  Defined.

  Definition reluniv_has_homsets : has_homsets reluniv_precat.
  Proof.
    unfold has_homsets.
    intros a b.
    apply isaset_relative_universe_mor.
  Defined.

  Definition reluniv_cat : category
    := ( reluniv_precat ,, reluniv_has_homsets ).

End RelUniv_Cat.

(** * Functors of relative universe categories *)

(** ** Lax commutative squares *)

Section Comm_Squares.
(* TODO: perhaps it would be better to unify this with the displayed arrow category. *)

Context {C : precategory}.
  
Definition comm_square
      {c c' : C} (f : c --> c')
      {d d' : C} (g : d --> d')
  := ∑ (hk : c --> d × c' --> d'), (pr1 hk ;; g = f ;; pr2 hk). 

Definition dom_comm_square
      {c c' : C} {f : c --> c'}
      {d d' : C} {g : d --> d'}
    : comm_square f g -> c --> d
  := (@funcomp _ _ (fun _ => _) pr1 pr1).

Definition cod_comm_square
      {c c' : C} {f : c --> c'}
      {d d' : C} {g : d --> d'}
    : comm_square f g -> c' --> d'
  := (@funcomp _ _ _ pr1 (@pr2 _ (fun _ => _))).

Definition commutes_comm_square
      {c c' : C} {f : c --> c'}
      {d d' : C} {g : d --> d'}
    (hk : comm_square f g)
  : dom_comm_square hk ;; g = f ;; cod_comm_square hk
:= pr2 hk.

End Comm_Squares.

Section Functor_Squares.

(* Start by defining “pre-functor-squares”, with no commutativity,
  so that we can have a single pair of access functions [dom_functor], 
  [cod_functor] which can (via coercions) be used for lax-, colax-, and
  pseudo-commutative squares alike. *)

Definition pre_functor_square 
    {C D : precategory} (J : C ⟶ D)
    {C' D' : precategory} (J' : C' ⟶ D')
  : UU
:= (functor C C' × functor D D').

Definition dom_functor 
    {C D : precategory} {J : C ⟶ D}
    {C' D' : precategory} {J' : C' ⟶ D'}
  : pre_functor_square J J' -> C ⟶ C'
:= pr1.

Definition cod_functor 
    {C D : precategory} {J : C ⟶ D}
    {C' D' : precategory} {J' : C' ⟶ D'}
  : pre_functor_square J J' -> D ⟶ D'
:= pr2.

Definition lax_functor_square
    {C D : precategory} (J : functor C D)
    {C' D' : precategory} (J' : functor C' D')
  : UU
:= ∑ (FG : pre_functor_square J J'),
     nat_trans ((dom_functor FG) ∙ J')
               (J ∙ (cod_functor FG)).

Coercion pre_functor_square_of_lax_functor_square
    {C D : precategory} {J : functor C D}
    {C' D' : precategory} {J' : functor C' D'}
  : lax_functor_square J J' -> pre_functor_square J J'
:= pr1.

Definition make_lax_functor_square
    {C D : precategory} {J : C ⟶ D}
    {C' D' : precategory} {J' : C' ⟶ D'}
    (F : C ⟶ C') (G : D ⟶ D') (α : nat_trans (F ∙ J') (J ∙ G))
  : lax_functor_square J J'
:= ((F,G) ,, α).

Definition commutes_lax_functor_square
    {C D : precategory} {J : C ⟶ D}
    {C' D' : precategory} {J' : C' ⟶ D'}
    (FG : lax_functor_square J J')
  : nat_trans _ _
:= pr2 FG.

End Functor_Squares.

Section Relative_Universe_Functor.

Context {C D : precategory} {J : functor C D} (U : relative_universe J)
        {C' D' : precategory} {J' : functor C' D'} (U' : relative_universe J')
        (FGα : lax_functor_square J J').

Definition relative_universe_functor : UU.
Proof.
  set (F := dom_functor FGα).
  set (G := cod_functor FGα).
  set (α := commutes_lax_functor_square FGα).
  simple refine ((∑ (t : _) (ϕ : _), _ × _) × _).
  - (* t : comparison square between the universes *)
    exact (comm_square (# G (mor U)) (mor U')).
  - (* ϕ : comparison maps between “context extensions” *)
    refine (forall (X:C) (f : J X --> base U), F _ --> _).
    + exact (fpb_ob (U X f)).
    + refine (fpb_ob (U' (F X) _)).
      refine (_ ;; cod_comm_square t).
      refine (_ ;; # G f).
      exact (α _).
  - refine (forall (X:C) (f : J X --> base U), _ × _).
    + (* ϕ is over the base *)
      exact (ϕ X f ;; fp _ = # F (fp _)).
    + (* ϕ commutes with the canonical pullback morphism *)
      exact (#J' (ϕ X f) ;; (fq _)
             = α (fpb_ob (U X f)) ;; #G (fq _) ;; dom_comm_square t).
  - (* ϕ is natural *)
    (* TODO: give this, once we have added the missing functoriality condition in the definition of relative universes. *)
    exact unit.
  - (* G preserves the canonical pullbacks *)
    refine (forall (X:C) (f : J X --> base U),
                isPullback _ _ _ _ (functor_on_square _ _ G _)).
    exact (pr1 (pr2 (U X f))). (* TODO: access functions for [commutes_and_is_pullback] and [fpullback] ! *)
Defined.

End Relative_Universe_Functor.
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

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.RelativeUniverses.

Local Set Automatic Introduction.
(* only needed since imports globally unset it *)

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

Definition mk_lax_functor_square
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
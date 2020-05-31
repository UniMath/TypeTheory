(* TODO: module documentation *)

Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.Foundations.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV2.FullyFaithfulDispFunctor.
Require Import TypeTheory.ALV1.TypeCat.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.ComprehensionC.

Section T.

  Definition discrete_comprehension_cat_structure (C : category) : UU
    := ∑ (D : disp_cat C) (H : is_discrete_fibration D)
         (F : disp_functor (functor_identity _ ) D (disp_codomain C)),
       is_cartesian_disp_functor F.

  Search isaset.

  Definition split_type_cat_structure' (C : category) : UU
    := ∑ (Ty : C → UU)
         (ext : ∏ Γ : C, Ty Γ → C)
         (reind : ∏ Γ : C, Ty Γ → ∏ Γ' : C, C ⟦ Γ', Γ ⟧ → Ty Γ')
         (dpr : ∏ (Γ : C) (A : Ty Γ), C ⟦ ext Γ A, Γ ⟧)
         (q : ∏ (Γ : C) (A : Ty Γ) (Γ' : C) (f : C ⟦ Γ', Γ ⟧),
              C ⟦ ext Γ' (reind _ A _ f), ext Γ A ⟧)
         (dpr_q : ∏ (Γ : C) (A : Ty Γ) (Γ' : C) (f : C ⟦ Γ', Γ ⟧),
                  q _ A _ f ;; dpr Γ A = dpr Γ' (reind _ A _ f) ;; f)
         (pb : ∏ (Γ : C) (A : Ty Γ) (Γ' : C) (f : C ⟦ Γ', Γ ⟧),
               isPullback _ _ _ _ (! dpr_q Γ A Γ' f)),
       (* isaset_Ty : *) (∏ (Γ : C), isaset (Ty Γ)) ×
       (* idax : *) (∑ (reind_id : ∏ (Γ : C) (A : Ty Γ), reind _ A _ (identity Γ) = A),
                     ∏ (Γ : C) (A : Ty Γ),
                     q _ A _ (identity Γ) =
                     idtoiso (maponpaths (λ B : Ty Γ, ext Γ B) (reind_id Γ A))) ×
       (* compax : *) (∑ (reind_comp : ∏ (Γ : C) (A : Ty Γ) (Γ' : C) (f : C ⟦ Γ', Γ ⟧)
                                         (Γ'' : C) (g : C ⟦ Γ'', Γ' ⟧),
                                       reind _ A _ (g ;; f) = reind _ (reind _ A _ f) _ g),
                       ∏ (Γ : C) (A : Ty Γ) (Γ' : C) (f : C ⟦ Γ', Γ ⟧)
                         (Γ'' : C) (g : C ⟦ Γ'', Γ' ⟧),
                       q _ A _ (g ;; f) =
                       idtoiso (maponpaths (λ B, ext Γ'' B) (reind_comp _ A _ f _ g)) ;;
                       q _ (reind _ A _ f) _ g ;; q _ A _ f).


  Search disp_codomain.
  
  Definition discrete_comprehension_cat_structure' (C : category) : UU
    := ∑ (ob_disp : C -> UU)
         (mor_disp : ∏ {x y : C}, (x --> y) -> ob_disp x -> ob_disp y -> UU)
         (id_disp : ∏ {x : C} (xx : ob_disp x), mor_disp (identity x) xx xx)
         (comp_disp : ∏ {x y z : C} {f : x --> y} {g : y --> z}
                        {xx : ob_disp x} {yy : ob_disp y} {zz : ob_disp z},
                      mor_disp f xx yy -> mor_disp g yy zz -> mor_disp (f ;; g) xx zz)
         (id_left_disp : ∏ {x y} {f : x --> y} {xx} {yy} (ff : mor_disp f xx yy),
                         comp_disp (id_disp xx) ff
                         = transportb (λ g, mor_disp g xx yy) (id_left _) ff)
         (id_right_disp : ∏ {x y} {f : x --> y} {xx} {yy} (ff : mor_disp f xx yy),
                          comp_disp ff (id_disp yy)
                          = transportb (λ g, mor_disp g xx yy) (id_right _) ff)
         (assoc_disp : ∏ {x y z w} {f : x --> y} {g : y --> z} {h : z --> w}
                         {xx} {yy} {zz} {ww}
                         (ff : mor_disp f xx yy) (gg : mor_disp g yy zz) (hh : mor_disp h zz ww),
                       comp_disp ff (comp_disp gg hh)
                       = transportb (λ k, mor_disp k _ _) (assoc _ _ _)
                                    (comp_disp (comp_disp ff gg) hh))
         (homsets_disp : ∏ {x y} {f : x --> y} {xx} {yy}, isaset (mor_disp f xx yy))
         (is_disc_fib : (forall (c c' : C) (f : c' --> c) (d : ob_disp c),
                            ∃! d' : ob_disp c', mor_disp f d' d)
                          ×
                          (forall c, isaset (ob_disp c)))

         (Fob : ∏ x, ob_disp x -> disp_codomain C x)
         (Fmor : ∏ x y (xx : ob_disp x) (yy : ob_disp y) (f : x --> y),
                 (mor_disp f xx yy) -> (Fob _ xx -->[ f ] Fob _ yy))
         (Faxioms :
            (∏ x (xx : ob_disp x),
             Fmor _ _ _ _ _ (id_disp xx) = transportb _ (functor_id (functor_identity _) x) (Core.id_disp (Fob _ xx)))
              × (∏ x y z (xx : ob_disp x) yy zz (f : x --> y) (g : y --> z)
                   (ff : mor_disp f xx yy) (gg : mor_disp g yy zz),
                 Fmor _ _ _ _ _ (comp_disp ff gg)
                 = transportb _ (functor_comp (functor_identity _) f g) (Core.comp_disp (Fmor _ _ _ _ _ ff) (Fmor _ _ _ _ _ gg))))

         
       , unit.

End T.

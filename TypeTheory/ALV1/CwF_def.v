(**
  [TypeTheory.ALV1.CwF_RelUnivYoneda]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**
Contents:

- Main result: an equivalence [weq_RelUnivYo_CwF]
  between CwF-structures on a precategory [C]
  and relative universes for [ Yo : C -> preShv C ].
*)

Require Import UniMath.Foundations.Basics.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.
Require Import TypeTheory.ALV1.RelativeUniverses.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Defs.

Set Automatic Introduction.

Section Fix_Category.

Variable C : Precategory.


Local Definition Ty (pp : mor_total (preShv C)) : functor _ _ := target pp.
Local Definition Tm (pp : mor_total (preShv C)) : functor _ _ := source pp.

(** ** Main intermediate structures: [comp], [icwf_structure] *)


Definition cwf'_structure (pp : mor_total (preShv C)) : UU
  := Π Γ (A : Ty pp Γ : hSet),
       Σ (ΓA : C) (π_A : C ⟦ΓA, Γ⟧) (v : Tm pp ΓA : hSet)
         (e : #Yo π_A ;; yy A = yy v ;; pp), isPullback _ _ _ _ e .
       
Definition ext' {pp : mor_total (preShv C)} (Y : cwf'_structure pp) {Γ} A 
  : C 
  := pr1 (Y Γ A).

Definition π' {pp : mor_total (preShv C)} (Y : cwf'_structure pp) {Γ} A 
  : C ⟦ext' Y A, Γ⟧ 
  := pr1 (pr2 (Y Γ A)).

Definition QQ' {pp : mor_total (preShv C)} (Y : cwf'_structure pp) {Γ} A 
  : _ ⟦Yo (ext' Y A) , Tm pp⟧ 
  := yy (pr1 (pr2 (pr2 (Y Γ A)))).


Definition to_construct (pp : mor_total (preShv C)) : UU :=
   fcomprehension Yo pp ≃ cwf'_structure pp.

(** to construct this equivalence, maybe parts of the proofs of
    CwF_RelUnivYoneda can be reused
*)

Lemma foo pp : to_construct pp.
Proof.
  unfold to_construct.
  apply weqonsecfibers.
  intro Γ.  
  Check (weqonsecbase _ (@yy _ _ _ _ )).
Abort.

End Fix_Category.
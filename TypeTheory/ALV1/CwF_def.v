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


Section fix_stuff.

Context (pp : mor_total (preShv C))
        {Γ : C}
        (A : Ty pp Γ : hSet).

Definition cwf_ext : UU := Σ (ΓA : C), C ⟦ΓA, Γ⟧.

Definition cwf_tm (r : cwf_ext) : UU := 
  let ΓA := pr1 r in
  let π := pr2 r in
  Σ v : (Tm pp ΓA : hSet), (pr2 pp : nat_trans _ _ ) _ v = #(Ty pp) π A.

Section fix_more_stuff.

Context (ext : cwf_ext)
        (tm : cwf_tm ext).

Let ΓA : C := pr1 ext.
Let π : C ⟦ ΓA , Γ ⟧ := pr2 ext.
Let v : (Tm pp ΓA : hSet) := pr1 tm.
Let e : (pr2 pp : nat_trans _ _ ) _ v = #(Ty pp) π A := pr2 tm.

Lemma cwf_square_comm 
  : #Yo π ;; yy A = yy v ;; pp.
Proof.
  apply pathsinv0.
  etrans. Focus 2. apply yy_natural.
  rewrite <- e.
  apply yy_comp_nat_trans.
Qed.

End fix_more_stuff.

Definition cwf_struct_pw : UU
  := Σ (ΓAπ : cwf_ext), 
     (Σ (ve : cwf_tm ΓAπ), isPullback _ _ _ _ (cwf_square_comm ΓAπ ve)).

End fix_stuff.

Definition rep_structure (pp : mor_total (preShv C)) : UU 
  :=
            Π Γ (A : Ty pp Γ : hSet), cwf_struct_pw pp A.


Definition to_construct (pp : mor_total (preShv C)): UU := 
  fcomprehension Yo pp ≃ rep_structure pp.

Lemma foo pp : to_construct pp.
Proof.
  unfold to_construct.
  apply weqonsecfibers.
  intro Γ.  
  eapply weqcomp.
  apply (weqonsecbase _ (@yy _ _ _ _ )).
  apply weqonsecfibers. intro tm.
Abort.

End Fix_Category.
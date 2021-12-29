(**
  [TypeTheory.ALV1.CwF_Defs_Equiv]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**
  The main result of this file is an equivalence [weq_cwf'_cwf_structure]
  between the canonical definition of CwF-structures on a precategory [C] 
  and the regrouped definition based on object-extension structures.

  A [cwf'_structure] on _C_ is
  - a triple (Ty, (◂ + π)) (the object-extension structure)
  - a triple (Tm, pp, Q) where
    - Tm is a presheaf,
    - pp is a morphism of presheaves Tm -> Ty
    - te is a term, for any Γ : C and A : Ty(Γ),
        te A : Tm (Γ◂A)
  - such (te A) has the desired type, and square are pbs

  Parentheses are
    ( (Ty, (◂ + π)), ( (Tm,(pp,Q)), props) )

  Meanwhile, a [cwf_structure] on _C_ consists of a morphism pp : Ty --> Tm of presheaves together with, for each Γ:C and A : Ty Γ, a _representation_ of the fiber of Tm over A, which we will inspect in more detail below.

  So the three differences, in the order we will tackle them, are:

  - ordering: moving the morphism _pp_ to the front;
  - distributing ∏ over ∑: a single quantification over Γ, A on the outside, vs. quantifying within each component;
  - re-association of the components within the fiber-representation

*)

Require Import UniMath.Foundations.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheory.
Require Import TypeTheory.Auxiliary.SetsAndPresheaves.
Require Import TypeTheory.Auxiliary.TypeOfMorphisms.

Require Import TypeTheory.ALV1.CwF_def.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Defs.

Section Fix_Category.

Context {C : category}.

(** * Definition of an intermediate structure

  We start by reordering the components of [cwf'_structure],
  so that like [cwf_structure], the morphism of presheaves comes first:
   ( (Ty, Tm, pp), ( ((◂ + π) , Q), props ) )

  We name the intermediate structure produced as follows:

  - the type of triples (Ty,Tm,pp) is just [mor_total (preShv C)];
  - the type of triples (◂ + π, Q) is called [rep1_data];
  - the axioms are called [rep1_axioms].

  A pair [rep1_data, rep1_axioms] is called [rep1], and we define
  [cwf1_structure] as the type of pairs of a [mor_total] and a [rep1] on it.

  The equivalence
     [weq_cwf'_cwf1_structure : cwf'_structure C ≃ cwf1_structure C]
  is given just (!) by shuffling components.

  It remains then to give an equivalence [cwf1_structure C ≃ cwf_structure C].
  Since [pp] is at the front in both of these, it suffices to give, for each
  [ (Ty,Tm,pp) : mor_total (preShv C) ], an equivalence between the remaining
  structure, [ weq_rep1_representation : rep1 pp ≃ cwf_representation pp ].

*)

Definition rep1_data (pp : mor_total (preShv C)) : UU
  := 
   ∑ (dpr : ∏ (Γ : C) (A : Ty pp Γ : hSet ), ∑ (ΓA : C), C⟦ΓA, Γ⟧),
     ∏ Γ (A : Ty pp Γ : hSet), Tm pp (pr1 (dpr Γ A)) : hSet.

Definition ext {pp : mor_total (preShv C)} (Y : rep1_data pp) Γ A 
  : C 
  := pr1 (pr1 Y Γ A).

Definition dpr {pp : mor_total (preShv C)} (Y : rep1_data pp) {Γ} A 
  : C⟦ext Y Γ A, Γ⟧ 
  := pr2 (pr1 Y Γ A).

Definition te {pp : mor_total (preShv C)} (Y : rep1_data pp) {Γ:C} A 
  : Tm pp (ext Y Γ A) : hSet
  := pr2 Y Γ A.

Definition rep1_fiber_axioms {pp : mor_total (preShv C)}
  {Γ} (A : Ty pp Γ : hSet) 
  {ΓA : C} (π : ΓA --> Γ) (te : Tm pp ΓA : hSet) : UU
:=
  ∑ (e : ((pp : _ --> _) : nat_trans _ _ ) _ te
         = (# (Ty pp) π A)),
    isPullback (cwf_square_comm e).

Definition rep1_axioms {pp : mor_total (preShv C)} (Y : rep1_data pp) : UU :=
  ∏ Γ (A : Ty pp Γ : hSet), rep1_fiber_axioms A (dpr Y A) (te Y A).

Definition rep1 (pp : mor_total (preShv C)) : UU 
  := ∑ (Y : rep1_data pp), rep1_axioms Y.

Definition cwf1_structure := ∑ (pp : mor_total (preShv C)), rep1 pp.

(** * Equivalence between [cwf'_structure] and intermediate [cwf1_structure] *)

(* Note: the next lemma might be proved more easily with the specialized lemmas
    [weqtotal2dirprodassoc] and [weqtotal2dirprodassoc']
*)

Definition weq_rep1_cwf'_data : 
 (∑ X : obj_ext_structure C, term_fun_structure_data C X)
   ≃ 
 ∑ pp : mor_total (preShv C), rep1_data pp.
Proof.
  eapply weqcomp.
    unfold obj_ext_structure.
    apply weqtotal2asstor. simpl.
  eapply weqcomp. 2: { apply weqtotal2asstol. }
  simpl. eapply weqcomp. 
  2: { eapply invweq, weqtotal2dirprodassoc. }
  simpl.
  apply weqfibtototal.
  intro Ty.
  eapply weqcomp.
    apply weqfibtototal; intro depr.
    apply weqtotal2asstol'.
  eapply weqcomp.
    apply weqtotal2asstol'.
  eapply weqcomp. cbn. use weqtotal2dirprodcomm.
  eapply weqcomp; apply weqtotal2asstor.
Defined.

Definition weq_cwf'_cwf1_structure : cwf'_structure C ≃ cwf1_structure.
Proof.
  eapply weqcomp. 2: { apply weqtotal2asstor'. }
  eapply weqcomp. apply weqtotal2asstol'.
  use weqbandf.
  - apply weq_rep1_cwf'_data.
  - intro.
    apply weqonsecfibers.
    intro. 
    exact (idweq _ ).
Defined.

(** * Equivalence between [cwf_structure] and intermediate *)

(** As per the outline above, it now remains to construct,
  for a given morphism [ pp : Tm --> Ty ] in [ preShv pp ],
  an equivalence [ rep1 pp ≃ cwf_representation pp ]. Recall:

  a [rep1 pp] consists of:
   - [rep1_data], a triple [(◂ + π, Q)] as in a CwF, so
     - [◂ + π] : for each [Γ:C] and [A : Ty Γ],
        an object [ Γ ◂ A : C ], and projection [ π : Γ ◂ A -> Γ ]
     - [Q] : for each [Γ], [A], a tm [ te : Tm (Γ ◂ A) ]
   - some axioms, [rep1_axioms].

  a representation of [pp] is a function giving,
  for each [Γ : C] and [f : Yo Γ -> Ty],
    - an object and map [ f^*Γ -> Γ in C ];
    - a term of appropriate type;
    - such that the induced square of presheaves is a pullback.


  The equivalence between these goes in two steps, essentially:
 
  - distributing the quantification over Γ, A to the outside;
  - reassociating the sigma-types.

  For distributing the quantification, we go via an intermediate defind
  notion [rep2_data].
*)

Definition rep2_data (pp : mor_total (preShv C)) : UU
  := ∏ (Γ : C) (A : Ty pp Γ : hSet),
           (∑ ΓAπ : ∑ ΓA : C, ΓA --> Γ, Tm pp (pr1 ΓAπ) : hSet).

Definition weq_rep2_rep1_data (pp : mor_total (preShv C))
  : rep2_data pp ≃ rep1_data pp.
Proof.
  unfold rep1_data, rep2_data.
  eapply weqcomp. apply weqonsecfibers; intro; apply weqforalltototal.
  use weqforalltototal.
Defined.

Definition rep2 (pp : mor_total (preShv C)) : UU 
  := ∑ (Y : rep2_data pp), rep1_axioms (weq_rep2_rep1_data _ Y).

Definition weq_rep1_representation (pp : mor_total (preShv C))
  : rep1 pp ≃ cwf_representation pp.
Proof.
  use weqcomp. { exact (rep2 pp). }
    eapply invweq, weqfp.
  unfold rep2, cwf_representation.
  eapply weqcomp. 
    unfold rep2_data, rep1_axioms.
    use (@weqtotaltoforall C (fun Γ => (Ty pp Γ : hSet) -> _)
      (fun Γ Y => forall A, rep1_fiber_axioms A (pr2 (pr1 (Y A))) (pr2 (Y A)))).
  apply weqonsecfibers; intro Γ.
  eapply weqcomp.
  { exact (weqtotaltoforall
           _
           (fun A ΓAπt => @rep1_fiber_axioms pp Γ _ (pr1 (pr1 ΓAπt)) 
                                             (pr2 (pr1 ΓAπt)) (pr2 ΓAπt))). }
  apply weqonsecfibers; intro A.
  unfold cwf_fiber_representation.
  (* reassociation:
     ((ΓAπ,t),(e,pb))
  ~> (ΓAπ,(t,(e,pb)))
  ~> (ΓAπ,((t,e),pb))
  *)
  eapply weqcomp.
    unfold rep1_fiber_axioms.
    use weqtotal2asstor.
  apply weqfibtototal; intros ΓAπ.
  use weqtotal2asstol.
Defined.

(** * Main result: equivalence between [cwf_structure C] and [cwf'_structure C] *)

Definition weq_cwf_cwf'_structure : cwf_structure C ≃ cwf'_structure C.
Proof.
  apply invweq.
  eapply weqcomp.
  apply weq_cwf'_cwf1_structure.
  apply weqfibtototal; intro pp.
  apply weq_rep1_representation.
Defined.

End Fix_Category.

Arguments weq_cwf'_cwf1_structure _ : clear implicits.
Arguments weq_cwf_cwf'_structure _ : clear implicits.

(**
  [TypeTheory.ALV1.CwF_def]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**
Contents:

- the canonical standalone definition of a (Fiore-style) CwF
- equivalence between this and two related ones occurring in the ALV1 paper
*)

Require Import UniMath.Foundations.Basics.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.
Require Import TypeTheory.ALV1.RelativeUniverses.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Defs.

Set Automatic Introduction.

Section Auxiliary.

(* Needed temporarily for [weq_total2_assoc]. *)
Lemma transparent_admit {A} : A.
Admitted.

(** Associativity of Σ. *)
(* TODO: seek in library; if not found, upstream! *)
(* Not sure if it’s best to give this with [C] typed as 
[Π a, B a -> Type] or [(Σ a, B a) -> Type].  See how it works out in practice. The latter is more general, but it may be useful to have the former explicitly since if its arguments can be inferred more easily. *)
Definition weq_total2_assoc {A} {B : A -> Type} (C : (Σ x, B x) -> Type)
  : (Σ (xy : Σ x, B x), C xy) ≃ (Σ x y, C (x,, y)).
Proof.
  mkpair.
    intros [[x y] z]. exact (x,,(y,,z)).
  intros [x [y z]].
  mkpair.
    mkpair.
      exact ((x,,y),,z).
    apply idpath.
  intros t. apply transparent_admit.
  (* Can’t just [admit.] since we need computational behaviour of this lemma below. *)
Defined.

Definition weq_total2_assoc' {A} {B : A -> Type} (C : Π a, B a -> Type)
  : (Σ (xy : Σ x, B x), C _ (pr2 xy)) ≃ (Σ x y, C x y).
Proof.
  apply (weq_total2_assoc (fun xy => C (pr1 xy) (pr2 xy))).
Defined.

End Auxiliary.

(** * Definition of a CwF 

A (Fiore-style) CwF consists of:

- a base category C;
- a morphism Tm —p—> Ty of presheaves on C;
- a _representation_ of p.

*)

Section Fix_Category.

Variable C : Precategory.

Local Definition Ty (pp : mor_total (preShv C)) : functor _ _ := target pp.
Local Definition Tm (pp : mor_total (preShv C)) : functor _ _ := source pp.

(** ** Representations of maps of presheaves 

A *representation* of a map Tm —p—> Ty of presheaves consists of data exhibiting, for each (A : Ty Γ), the fiber of p over A as represented by some object Γ.A over Γ. *)

Section Representation.

Section Fiber_Representation.

Context (pp : mor_total (preShv C))
        {Γ : C}
        (A : Ty pp Γ : hSet).

Definition cwf_ext : UU := Σ (ΓA : C), C ⟦ΓA, Γ⟧.

Definition cwf_tm (r : cwf_ext) : UU := 
  let ΓA := pr1 r in
  let π := pr2 r in
  Σ v : (Tm pp ΓA : hSet), (morphism_from_total pp : nat_trans _ _ ) _ v = #(Ty pp) π A.

(* Lemma: convert the equality of elements of presheaves into the commutativity of a square involving representables. *)
Lemma cwf_square_comm
  (ext : cwf_ext) (ΓA := pr1 ext) (π := pr2 ext)
  (tm : cwf_tm ext) (v := pr1 tm) (e := pr2 tm)
  : #Yo π ;; yy A = yy v ;; pp.
Proof.
  apply pathsinv0.
  etrans. Focus 2. apply yy_natural.
  etrans. apply yy_comp_nat_trans.
  apply maponpaths, e.
Qed.

Definition cwf_fiber_representation : UU
  := Σ (ΓAπ : cwf_ext), 
     (Σ (ve : cwf_tm ΓAπ), isPullback _ _ _ _ (cwf_square_comm ΓAπ ve)).

End Fiber_Representation.

Definition cwf_representation (pp : mor_total (preShv C)) : UU 
  := Π Γ (A : Ty pp Γ : hSet), cwf_fiber_representation pp A.

End Representation.

(** ** Definition of CwF structure *)

Definition cwf_structure : UU := Σ pp, (cwf_representation pp).


(** ** Equivalence with relative universe structures on Yoneda *)


Lemma wev_cwf_representation_fcomprehension (pp : mor_total (preShv C))
  : cwf_representation pp ≃ fcomprehension Yo pp.
Proof.
  apply weqonsecfibers. intro Γ.
  (* convert the type argument under [yy] *) 
  eapply weqcomp.
    Focus 2. eapply invweq. 
    refine (weqonsecbase _ _). apply yy.
  apply weqonsecfibers. intro A.
  unfold cwf_fiber_representation, fpullback.
  (* reassociate the RHS to match the LHS:
       ((ΓA,(π,v)),(e,p))
    -> (((ΓA,π),v),(e,p))
    -> ((ΓA,π),(v,(e,p)))
    -> ((ΓA,π),((v,e),p))
  *)
  eapply weqcomp. Focus 2.
    refine (weqfp _ _).
    apply weq_total2_assoc'.
  eapply weqcomp. Focus 2.
    eapply invweq, weq_total2_assoc.
  eapply weqcomp. Focus 2.
    refine (weqfibtototal _ _ _).
    intro. apply weq_total2_assoc'.
  (* convert the term argument under [yy] *)
  apply weqfibtototal. intros [ΓA π]; simpl.
  simple refine (weqbandf _ _ _ _).
    simple refine (weqbandf _ _ _ _).
      apply yy.
  (* show the two forms of the equality axiom are equivalent *)
  - intros v; simpl.
    apply weqimplimpl.
    (* TODO: abstract the following, as bidirectional version of [cwf_square_comm]. *)
    + intros e. 
      refine (cwf_square_comm _ _ (_,,_) (_,,e)).
    + intros ey. 
      assert (ey' := nat_trans_eq_pointwise ey ΓA); clear ey; cbn in ey'.
      assert (ey'' := toforallpaths _ _ _ ey' (identity _)); clear ey';
      cbn in ey''.
      etrans. etrans. Focus 2. apply @pathsinv0, ey''.
      * apply maponpaths, @pathsinv0.
        apply (toforallpaths _ _ _ (functor_id (Tm pp) _)).
      * unfold yoneda_morphisms_data.
        apply maponpaths_2, id_left.
    + apply setproperty.
    + refine (homset_property (preShv C) _ _ _
        (fq _
          (ΓA,, π,, invmap (yoneda_weq C (homset_property C) ΓA (Tm pp)) v)
        ;; _)).
    (* Why does so much need to be given explicitly there? *)
  - intros [v e]; cbn.
    apply idweq.
Time Defined.

End Fix_Category.
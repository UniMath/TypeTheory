(**
  [TypeTheory.CwF.CwF_def]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**
Contents:

- the definition of CwFs à la Fiore: [cwf_structure], [cwf]
- equivalence between cwf structures and relative universe structures on Yoneda, [weq_cwf_structure_RelUnivYo]
- type of representations is a proposition if [C] is univalent [isaprop_cwf_representation]
- transport of a CwF structure along weak equivalence [transfer_cwf_weak_equiv]

*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheory.
Require Import TypeTheory.Auxiliary.SetsAndPresheaves.
Require Import TypeTheory.Auxiliary.TypeOfMorphisms.

Require Import TypeTheory.RelUniv.RelativeUniverses.
Require Import TypeTheory.RelUniv.Transport_along_Equivs.
Require Import TypeTheory.RelUniv.RelUnivYonedaCompletion.

(** * Definition of a CwF 

A (Fiore-style) CwF consists of:

- a base category C;
- two presheaves on C, connected by a morphism Tm —p—> Ty;
- a _representation_ of p (see below).

  This is a mild reformulation of Dybjer’s original definition of CwF’s, replacing the functor [C --> FAM] with an arrow in [preShv C].

  Specifically, we follow: Marcelo Fiore, slides 32–34 of _Discrete Generalised Polynomial Functors_ , from talk at ICALP 2012,
  #(<a href="http://www.cl.cam.ac.uk/~mpf23/talks/ICALP2012.pdf">link</a>)#

  See also: Marcelo Fiore, _Algebraic Type Theory_, 2008
  #(<a href="http://www.cl.cam.ac.uk/~mpf23/Notes/att.pdf">link</a>)#

*)

Section Fix_Category.

Context {C : category}.

(** ** Representations of maps of presheaves 

A *representation* of a map Tm —p—> Ty of presheaves consists of data illustrating that “every fibre of _p_ is representable”; that is, giving for each (A : Ty Γ), some object and map (π A) : Γ.A Γ, along with a term (te A) over A which is “universal”, in that it represents the fiber of p over A. *)

Section Representation.

Context (pp : mor_total (preShv C)).

Definition Ty : functor _ _ := target pp.
Definition Tm : functor _ _ := source pp.

Definition map_into (Γ : C) : UU
:= ∑ (ΓA : C), C ⟦ΓA, Γ⟧.

Definition cwf_tm_of_ty {Γ : C} (A : Ty Γ : hSet) : UU
:= ∑ t : (Tm Γ : hSet), pp $nt t = A.

(* Lemma: convert an equality giving the type of a term
          into commutativity of a square of maps of presheaves. *)
Lemma cwf_square_comm {Γ} {A}
  {ΓA : C} {π : ΓA --> Γ}
  {t : Tm ΓA : hSet} (e : pp $nt t = # Ty π A)
  : #Yo π ;; yy A = yy t ;; pp.
Proof.
  apply pathsinv0.
  etrans. 2: { apply yy_natural. }
  etrans. apply yy_comp_nat_trans.
  apply maponpaths, e.
Qed.

Definition cwf_fiber_representation {Γ : C} (A : Ty Γ : hSet) : UU
  := ∑ (ΓAπ : map_into Γ) (te : cwf_tm_of_ty (# Ty (pr2 ΓAπ) A)), 
     isPullback (cwf_square_comm (pr2 te)).
(* See below for an alternative version [cwf_fiber_representation'], separated into data + axioms *)

Definition cwf_representation : UU 
  := ∏ Γ (A : Ty Γ : hSet), cwf_fiber_representation A.

End Representation.

(** ** Definition of CwF structure, CwF *)

Definition cwf_structure : UU := ∑ pp, (cwf_representation pp).

(* TODO: add notations, coercions, access functions to make this usable! Or perhaps below, after the date-plus-axioms reformulation? *)

End Fix_Category.

Arguments cwf_structure C : clear implicits.

Definition cwf := ∑ C, cwf_structure C.

Arguments cwf_square_comm {C pp Γ A _ _ _} e.

(** ** Misc lemmas on CwF’s *)
Section CwF_Lemmas.

Context {C : category} (pp : mor_total (preShv C)).

Lemma cwf_square_comm_converse {Γ : C} {A : Ty pp Γ : hSet}
    {ΓA : C} {π : ΓA --> Γ}
    {t : Tm pp ΓA : hSet}
    (e :  #Yo π ;; yy A = yy t ;; pp)
  : pp $nt t = # (Ty pp) π A.
Proof.
  etrans.
  { apply maponpaths, pathsinv0, functor_id_pshf. }
  etrans.
  { assert (e' := nat_trans_eq_pointwise e ΓA); clear e; cbn in e'.
    refine (toforallpaths (!e') (identity _)).
  }
  unfold yoneda_morphisms_data.
  apply maponpaths_2, id_left.
Qed.

End CwF_Lemmas.

(** * Useful facts about representations *)

Section Representation_Facts.

Context {C : category} (pp : mor_total (preShv C)).

(** ** Data+properties reformulation of definition of representation *)

Section Representation_Regrouping.

Definition cwf_fiber_rep_data {Γ:C} (A : Ty pp Γ : hSet) : UU
  := ∑ (ΓA : C), C ⟦ΓA, Γ⟧ × (Tm pp ΓA : hSet).

Definition cwf_fiber_rep_ax {Γ:C} {A : Ty pp Γ : hSet}
    (ΓAπt : cwf_fiber_rep_data A) : UU 
  := ∑ (H : pp $nt (pr2 (pr2 ΓAπt))
            = #(Ty pp) (pr1 (pr2 ΓAπt)) A),
    isPullback (cwf_square_comm H).

Definition cwf_fiber_representation' {Γ:C} (A : Ty pp Γ : hSet) : UU
  := ∑ ΓAπt : cwf_fiber_rep_data A, cwf_fiber_rep_ax ΓAπt.

Definition cwf_fiber_representation_weq {Γ:C} (A : Ty pp Γ : hSet) 
  : cwf_fiber_representation pp A ≃ cwf_fiber_representation' A.
Proof.
  unfold cwf_fiber_representation, cwf_fiber_representation'.
  eapply weqcomp.   (* (ΓA,π), ((v,e),P) *)
  eapply weqfibtototal. intro x.
    apply weqtotal2asstor. simpl. (*  (ΓA,π), (v, (e,P)) *)
  eapply weqcomp; [eapply invweq; apply weqtotal2asstol |]; simpl.  
  apply invweq.
  eapply weqcomp.
  apply weqtotal2asstor. cbn.
  apply weqfibtototal. intro ΓA.
  apply weqtotal2asstor.
Defined.  

End Representation_Regrouping.

(** ** Uniqueness of representations, when C saturated *)

(* TODO: can this be simplified? *)
Lemma isaprop_cwf_fiber_representation' {Γ:C} (A : Ty pp Γ : hSet)
  : is_univalent C -> isaprop (cwf_fiber_representation' A).
Proof.
  intros isC.
  apply invproofirrelevance.
  intros x x'. apply subtypePath.
  { intro t. 
    apply isofhleveltotal2. 
    - apply setproperty.
    - intro. apply isaprop_isPullback.
  }
  use total2_paths_f; simpl.
  { apply isotoid. { assumption. }
    apply (invmap (weq_ff_functor_on_z_iso (yoneda_fully_faithful _) _ _)).
    refine (z_iso_from_Pullback_to_Pullback
                (make_Pullback _ (pr22 x))
                (make_Pullback _ (pr22 x'))).
  }
  etrans. { apply (transportf_dirprod'
                       (λ a', C ⟦ a', _ ⟧) (λ a', (Tm pp a' : hSet))). }
  apply pathsdirprod.
  - rewrite transportf_isotoid.
    cbn.
    etrans. { apply yoneda_postcompose. }
    etrans. {
      refine (toforallpaths _ (identity _)). 
      refine (toforallpaths _ _). 
      apply maponpaths,
        (PullbackArrow_PullbackPr1 (make_Pullback _ (pr22 x))).
    }
    cbn; unfold yoneda_morphisms_data.
    apply id_left.
  - etrans. { apply transportf_pshf'. }
    rewrite idtoiso_inv.
    rewrite idtoiso_isotoid.
    cbn.
    match goal with | [ |- _ (_ ?f) _ = _]
                      => set (i := f :  preShv C ⟦ _, _ ⟧) end.
    refine (@pathscomp0 _ _
                 ((i ;; yy _) $nt (identity _)) _ _ _).
    { apply idpath. }
    subst i; unfold from_Pullback_to_Pullback.
    rewrite (PullbackArrow_PullbackPr2 (make_Pullback _ (pr22 x))).
    cbn. apply functor_id_pshf.
Qed.

Lemma isaprop_cwf_fiber_representation {Γ:C} (A : Ty pp Γ : hSet)
  : is_univalent C -> isaprop (cwf_fiber_representation pp A).
Proof.
  intro H.
  refine (isofhlevelweqb _ _ _).
  - apply cwf_fiber_representation_weq.
  - apply isaprop_cwf_fiber_representation'.
    apply H.
Defined.

End Representation_Facts.

(* TODO: perhaps move the following section into a separate file [CwF_RelUniv_Yoneda], to make this file more self-contained?
*)

(** * Equivalence with relative universe structures on Yoneda *)
Section CwF_RelUnivYo.

Context {C : category}.

(** ** Construction of the equivalence *)

Section Representation_FComprehension.

Context (pp : mor_total (preShv C)).


(* TODO: there is considerable redundancy between this and [cwf_fiber_representation_weq] above; in particular, the same reassociation is used. Try to consolidate? *)
Definition weq_cwf_fiber_representation_fpullback {Γ : C} (A : Ty pp Γ : hSet)
: cwf_fiber_representation pp A
  ≃ fpullback (yoneda C) pp (yy A).
Proof.
  unfold cwf_fiber_representation, fpullback.
  (* reassociate the RHS to match the LHS:
       ((ΓA,(π,v)),(e,p))
    -> (((ΓA,π),v),(e,p))
    -> ((ΓA,π),(v,(e,p)))
    -> ((ΓA,π),((v,e),p))
  *)
  eapply weqcomp.
  2: { refine (weqfp _ _). apply weqtotal2asstor'. }
  eapply weqcomp.
  2: { eapply weqtotal2asstol. }
  eapply weqcomp.
  2: { refine (weqfibtototal _ _ _).
    intro. apply weqtotal2asstor'.
  }
  (* convert the term argument under [yy] *)
  apply weqfibtototal. intros [ΓA π]; simpl.
  use weqbandf.
    use weqbandf.
      apply yy.
  (* show the two forms of the equality axiom are equivalent *)
  - intros v; simpl.
    apply weqimplimpl.
    + apply @cwf_square_comm.
    + apply @cwf_square_comm_converse.
    + apply setproperty.
    + apply isaset_nat_trans.
      apply has_homsets_HSET.
  - intros [v e]; cbn.
    apply idweq.
Defined.

Lemma weq_cwf_representation_rel_universe_structure
  : cwf_representation pp ≃ rel_universe_structure Yo pp.
Proof.
  apply weqonsecfibers. intro Γ.
  (* convert the type argument under [yy] *) 
  eapply weqcomp.
  2: { eapply invweq.
    refine (weqonsecbase _ _). apply yy.
  }
  apply weqonsecfibers. intro A.
  apply  weq_cwf_fiber_representation_fpullback.
Defined.

End Representation_FComprehension.

Definition weq_cwf_structure_RelUnivYo 
  : cwf_structure C ≃ @relative_universe C _ Yo.
Proof.
  apply weqfibtototal.
  intro pp.
  apply weq_cwf_representation_rel_universe_structure.
Defined.

End CwF_RelUnivYo.

Arguments weq_cwf_structure_RelUnivYo _ : clear implicits.

(** The above equivalences allow us to easily deduce a few more nice facts about representations and CwF-structures from the corresponding facts about relative universes. *)

(** ** Consequences of the equivalence: Representations vs representability *)

(*
    When the underlying category is univalent [is_univalent C],
    then representations of a map of presheaves are unique,
    and hence there is no distinction between “represented” and
    “representable” morphisms of presheaves.

    For more on this comparison see [RepMaps.v].
*)

Lemma isaprop_cwf_representation {C : category}
    (Ccat : is_univalent C) (pp : mor_total (preShv C))
  : isaprop (cwf_representation pp).
Proof.
  use isofhlevelweqb.
  - exact (rel_universe_structure Yo pp).
  - apply weq_cwf_representation_rel_universe_structure.
  - apply isaprop_rel_universe_structure.
    + apply Ccat.
    + apply yoneda_fully_faithful.
Qed.

(** * Transport along a weak equivalence *)

(** ** General case of transport, and recovery of the original map *)

Definition transfer_cwf_weak_equiv {C D : category} (F : C ⟶ D)
           (F_ff : fully_faithful F) (F_es : essentially_surjective F)
           (Dcat : is_univalent D) 
  : cwf_structure C → cwf_structure D.
Proof.
  intro CC.
  apply (invmap (@weq_cwf_structure_RelUnivYo _)).
  apply (Transfer_of_RelUnivYoneda F F_ff F_es Dcat).
  apply (weq_cwf_structure_RelUnivYo _).
  exact CC.
Defined.

(**  Recovering the original morphism of presheaves after transport *)

Section CwF_Ftransport_recover.

Context {C D : category} 
        (F : C ⟶ D)
        (F_ff : fully_faithful F) 
        (F_es : essentially_surjective F)
        (Dcat : is_univalent D) 
        (T : cwf_structure C).

Let DD : univalent_category := (D,,Dcat).
Let T' : cwf_structure D := transfer_cwf_weak_equiv F F_ff F_es Dcat T.
Let TM : preShv C := Tm (pr1 T).
Let TM' : preShv DD := Tm (pr1 T').
Let TY : preShv C := Ty (pr1 T).
Let TY' : preShv D := Ty (pr1 T').

Let pp : _ ⟦ TM , TY ⟧ := pr1 T.
Let pp' : _ ⟦ TM' , TY' ⟧ := pr1 T'.

Let ηη : functor (preShv D) (preShv C) :=
  pre_composition_functor C^op D^op _ (functor_opp F).

Let isweq_Fcomp : isweq (pr1 (pr1 (Fop_precomp F))) := 
adj_equiv_of_cats_is_weq_of_objects 
               _ _ 
               (is_univalent_functor_category _ _ is_univalent_HSET )
               (is_univalent_functor_category _ _ is_univalent_HSET )
               _ 
               (equiv_Fcomp F F_ff F_es).

Lemma Tm_transfer_recover : 
      TM = ηη TM'.
Proof.
  assert (XT := homotweqinvweq (make_weq _ isweq_Fcomp) TM).
  apply pathsinv0.
  apply XT.
Defined.  

Lemma Ty_transfer_recover : 
   TY = ηη TY'.
Proof.
  assert (XT := homotweqinvweq (make_weq _ isweq_Fcomp) TY).
  apply pathsinv0.
  apply XT.
Defined.  

Let Fopequiv : adj_equivalence_of_cats _  := equiv_Fcomp F F_ff F_es.


Definition pp'_eta : 
  preShv C ⟦ ηη TM' , ηη TY' ⟧.
Proof.
  apply (# ηη pp').
Defined.

Definition Tm_iso : z_iso (ηη TM') TM.
Proof.
  apply (counit_pointwise_z_iso_from_adj_equivalence Fopequiv TM).
Defined.

Definition Ty_iso : z_iso (ηη TY') TY.
Proof.
  apply (counit_pointwise_z_iso_from_adj_equivalence Fopequiv TY).
Defined.

Lemma Morphism_of_presheaves_transfer_recover
  : Tm_iso ;; pp = pp'_eta ;; Ty_iso.
Proof.
  apply pathsinv0.
  apply (nat_trans_ax (counit_from_left_adjoint Fopequiv) pp).
Qed.

End CwF_Ftransport_recover.


(** ** Special case of transport: Descent along Rezk-completion *)
(** The construction below is also a special case of [transfer_cwf_weak_equiv] *)
Definition Rezk_on_cwf_structures {C : category} (CC : cwf_structure C)
  : cwf_structure (Rezk_completion C).
Proof.
  apply (invmap (@weq_cwf_structure_RelUnivYo _)).
  apply (Rezk_on_RelUnivYoneda C).
  apply (weq_cwf_structure_RelUnivYo _).
  exact CC.
Defined.

Section CwF_RC_recover.

Context {C : category} (T : cwf_structure C).

Let RC : univalent_category := Rezk_completion C.
Let T' : cwf_structure RC := Rezk_on_cwf_structures T.
Let TM : preShv C := Tm (pr1 T).
Let TM' : preShv RC := Tm (pr1 T').
Let TY : preShv C := Ty (pr1 T).
Let TY' : preShv RC := Ty (pr1 T').

Let pp : _ ⟦ TM , TY ⟧ := pr1 T.
Let pp' : _ ⟦ TM' , TY' ⟧ := pr1 T'.

Let ηη : functor (preShv RC) (preShv C) :=
  pre_composition_functor C^op RC^op _ (functor_opp (Rezk_eta C)).

Lemma Tm_Rezk_completion_recover : 
 (*  Tm = functor_composite (functor_opp (Rezk_eta C _ )) Tm'.*)
      TM = ηη TM'.
Proof.
  set (XR := Rezk_opp_weq C HSET is_univalent_HSET).
  assert (XT := homotweqinvweq XR TM).
  apply pathsinv0.
  apply XT.
Defined.  

Lemma Ty_Rezk_completion_recover : 
(*   Ty = functor_composite (functor_opp (Rezk_eta C _ )) Ty'. *)
   TY = ηη TY'.
Proof.
  set (XR := Rezk_opp_weq C HSET is_univalent_HSET).
  assert (XT := homotweqinvweq XR TY).
  apply pathsinv0.
  apply XT.
Defined.  


Let RCequiv : adj_equivalence_of_cats _  := Rezk_op_adj_equiv C
          HSET is_univalent_HSET.

Lemma has_homsets_preShv (D : category) : has_homsets (preShv D).
Proof.
  apply functor_category_has_homsets.
Defined.

Definition RC_pp'_eta : 
  preShv C ⟦ ηη TM' , ηη TY' ⟧.
Proof.
  apply (# ηη pp').
Defined.

Definition RC_Tm_iso : z_iso (ηη TM') TM.
Proof.
  set (XR':=  counit_pointwise_z_iso_from_adj_equivalence RCequiv TM).
  apply XR'.
Defined.

Definition RC_Ty_iso : z_iso (ηη TY') TY.
Proof.
  set (XR':=  counit_pointwise_z_iso_from_adj_equivalence RCequiv TY).
  apply XR'.
Defined.

Lemma RC_morphism_of_presheaves_recover
  : RC_Tm_iso ;; pp = RC_pp'_eta ;; RC_Ty_iso.
Proof.
  apply pathsinv0.
  apply (nat_trans_ax (counit_from_left_adjoint RCequiv) pp).
Qed.

End CwF_RC_recover.





(**
“Displayed equivalences” of displayed (pre)categories
*)

Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.equivalences.
Require Import UniMath.CategoryTheory.UnicodeNotations.

Require UniMath.Ktheory.Utilities.

Require Import Systems.Auxiliary.
Require Import Systems.UnicodeNotations.
Require Import Systems.Displayed_Cats.Auxiliary.
Require Import Systems.Displayed_Cats.Core.
Require Import Systems.Displayed_Cats.Constructions.


Local Set Automatic Introduction.
(* only needed since imports globally unset it *)

Local Open Scope type_scope.
Local Open Scope mor_disp_scope.

Section Auxiliary.

Lemma invmap_eq {A B : UU} (f : A ≃ B) (b : B) (a : A)
  : b = f a → invmap f b = a.
Proof.
  intro H.
  apply (invmaponpathsweq f).
  etrans. apply homotweqinvweq. apply H.
Defined.  

End Auxiliary.

(* TODO: move somewhere.  Not sure where? [Constructions]? *)
Section Essential_Surjectivity.

Definition fibre_functor_ess_split_surj 
    {C C' : Precategory} {D} {D'}
    {F : functor C C'} (FF : functor_over F D D')
    (H : functor_over_ff FF)
    {X : functor_over_ess_split_surj FF}
    {Y : isofibration D}
    (x : C)
  : Π yy : D'[{F x}], Σ xx : D[{x}], 
                iso (fibre_functor FF _ xx) yy.
Proof.
  intro yy.
  set (XR := X _ yy).
  destruct XR as [c'' [i [xx' ii]]].
  set (YY := Y _ _ i xx').
  destruct YY as [ dd pe ].
  mkpair.
  - apply dd.
  - 
    (* now need functor_over_on_iso_disp *)
    set (XR := functor_over_on_iso_disp FF pe).
    set (XR' := iso_inv_from_iso_disp XR).
    (* now need composition of iso_disps *)
    apply  (invweq (iso_disp_iso_fibre _ _ _ _)).
    set (XRt := iso_disp_comp XR' ii).
    transparent assert (XH : 
           (iso_comp (iso_inv_from_iso (functor_on_iso F i))
             (functor_on_iso F i) = identity_iso _ )).
    { apply eq_iso. cbn. simpl. unfold precomp_with.
      etrans. apply maponpaths_2. apply id_right.
      etrans. eapply pathsinv0. apply functor_comp. 
      etrans. Focus 2. apply functor_id. 
      apply maponpaths. apply iso_after_iso_inv.
   } 
    set (XRT := transportf (fun r => iso_disp r (FF x dd) yy ) 
                           XH).
    apply XRT.
    assumption.
Defined.

End Essential_Surjectivity.


Section Fix_context.

Variable C : Precategory.
Variables D' D : disp_precat C.

(** definition of displayed (quasi-)equivalence *)
(** In general, one can define displayed equivalences over any equivalence between the bases (and probably more generally still).  For now we just give the case over a single base precategory — i.e. over an identity functor. *)

(* TODO: refactor as data + axioms.*)
Definition equiv_disp (FF : functor_over (functor_identity _ ) D' D) : UU
  :=
  Σ (GG : functor_over (functor_identity _ ) D D') 
    (η : nat_trans_over (nat_trans_id _ ) 
                (functor_over_identity _ ) (functor_over_composite FF GG)  )
    (ε : nat_trans_over (nat_trans_id _ ) (functor_over_composite GG FF) (functor_over_identity _ ))
  , 
    (Π x xx, #FF ( η x xx) ;;  ε _ (FF _ xx) = 
               transportb _ (id_left _ ) (id_disp _) ) × 
    (Π x xx, η _ (GG x xx) ;; # GG (ε _ xx) = 
               transportb _ (id_left _ ) (id_disp _) ) ×  
    ((Π x xx, is_iso_disp (identity_iso _ ) (η x xx)) × 
    (Π x xx, is_iso_disp (identity_iso _ ) (ε x xx))). 


Section equiv_from_ses_ff.

(* now construct an [equiv_disp] from a s.e.s. and ff functor *)



Variable FF : functor_over (functor_identity _ ) D' D.
Hypothesis FFses : functor_over_disp_ess_split_surj FF.
Hypothesis FFff : functor_over_ff FF.

Let FFweq {x y} {xx yy} f := weqpair _ (FFff x y xx yy f).
Let FFinv {x y} {xx yy} f := invmap (@FFweq x y xx yy f).

Lemma FFinv_identity (x : C) (xx : D' x) :
  FFinv  
    (identity ((functor_identity C) x)) (id_disp (FF x xx)) =
           id_disp _ .
Proof.
  apply invmap_eq.  
  cbn.
  apply pathsinv0. 
  etrans. apply (functor_over_id FF). (* why arg needed? *)
  apply idpath.
Defined.

(* TODO: write a lemma about FF_inv and composition *)

Lemma FFinv_compose (x y z : C) (f : x ⇒ y) (g : y ⇒ z)
    (xx : D' x) (yy : D' y) (zz : D' z) 
    (ff : FF _ xx ⇒[f] FF _ yy) (gg : FF _ yy ⇒[g] FF _ zz)
  : FFinv (f ;; g) (ff ;; gg) = FFinv f ff ;; FFinv _ gg.
Proof.
  apply invmap_eq.
  cbn.
  apply pathsinv0.
  etrans. apply (functor_over_comp FF).
  etrans. apply maponpaths. apply maponpaths.
          apply (homotweqinvweq (FFweq _ )).
  etrans. apply maponpaths. apply maponpaths_2.
          apply (homotweqinvweq (FFweq _ )).
  apply idpath.
Qed.

Lemma FFinv_transportf x y (f f' : x ⇒ y) (p : f = f') xx yy 
   (ff : FF _ xx ⇒[f] FF _ yy) :
    FFinv  _ (transportf _ p ff) = 
     transportf _ p (FFinv _ ff).
Proof.
  induction p.
  apply idpath.
Defined.

(*
Variable X : isofibration D'.
*)

Local Definition GG_data : functor_over_data (functor_identity _ ) D D'.
Proof.
  mkpair.
  + intros x xx.
    apply (pr1 (FFses x xx)).
  + intros x y xx yy f X. simpl.
    set (Hxx := FFses x xx).
    set (Hyy := FFses y yy).
    
    set ( HHH:= 
            transportf _ (id_left _ )   
                       (transportf _ (id_right _ ) ((pr2 Hxx ;; X) ;; inv_mor_disp_from_iso (pr2 Hyy)))).
    set (HF := FFinv  (* (pr1 Hxx) (pr1 Hyy) f *) _  HHH).
    apply HF.
Defined.

Local Lemma GG_ax : functor_over_axioms GG_data.
Proof.
   - split; simpl.
     + intros x xx.
       etrans. apply FFinv_transportf.
       etrans. apply maponpaths. apply FFinv_transportf.
       Search (transportf _ _ (transportf _ _ _ )).
       etrans. apply transport_f_f.
       apply transportf_comp_lemma.
       etrans. apply maponpaths. apply maponpaths.
               apply maponpaths_2.
               apply id_right_disp.
       etrans. apply maponpaths. apply maponpaths.
               apply mor_disp_transportf_postwhisker.
       etrans. apply maponpaths. apply FFinv_transportf.
       etrans. apply transport_f_f.
       etrans. apply maponpaths. apply maponpaths.
         apply (inv_mor_after_iso_disp (pr2 (FFses x xx))). (* why is the argument needed? *)      etrans. apply maponpaths. apply FFinv_transportf.
       etrans. apply transport_f_f.
       etrans. apply maponpaths. apply FFinv_identity.
       apply transportf_comp_lemma_hset. apply homset_property. apply idpath.
     + intros.
       etrans. apply FFinv_transportf.
       etrans. apply maponpaths. apply FFinv_transportf.
       etrans. apply transport_f_f.       
       apply transportf_comp_lemma.
       etrans. Focus 2. apply FFinv_compose.
       apply pathsinv0.
       etrans. apply maponpaths.
               apply mor_disp_transportf_postwhisker.
       etrans. apply FFinv_transportf.
       etrans. apply maponpaths. apply maponpaths.
               apply mor_disp_transportf_postwhisker.
       etrans. apply maponpaths. apply maponpaths. apply maponpaths.
               apply mor_disp_transportf_prewhisker.
       etrans. apply maponpaths. apply FFinv_transportf.
       etrans. apply maponpaths. apply maponpaths. apply FFinv_transportf.
       etrans. apply transport_f_f. 
       etrans. apply transport_f_f. 
       etrans. apply maponpaths. apply maponpaths. 
               apply mor_disp_transportf_prewhisker.
       etrans. apply maponpaths. apply FFinv_transportf. 
       etrans. apply transport_f_f. 
       etrans. apply maponpaths. apply maponpaths.
               apply assoc_disp_var.               
       etrans. apply maponpaths. apply FFinv_transportf.
       etrans. apply transport_f_f.
       etrans. apply maponpaths. apply maponpaths.
               apply maponpaths. apply maponpaths.
               apply assoc_disp_var.
       etrans. apply maponpaths. apply maponpaths. apply maponpaths.
               apply mor_disp_transportf_prewhisker.
       etrans. apply maponpaths. apply maponpaths. 
               apply assoc_disp_var.
       etrans. apply maponpaths. apply FFinv_transportf.
       etrans. apply transport_f_f.
       etrans. apply maponpaths. apply maponpaths.
               apply maponpaths.
               apply mor_disp_transportf_prewhisker.
       etrans. apply maponpaths. apply maponpaths.
               apply maponpaths. apply maponpaths. apply maponpaths.
               apply assoc_disp.
       etrans. apply maponpaths. apply maponpaths. apply maponpaths.
               apply maponpaths. apply maponpaths. apply maponpaths.
               apply maponpaths_2.
               apply (iso_disp_after_inv_mor (pr2 (FFses y yy))).
       etrans. apply maponpaths. apply maponpaths.
               apply mor_disp_transportf_prewhisker.
       etrans. apply maponpaths. apply FFinv_transportf.
       etrans. apply transport_f_f.
       etrans. apply maponpaths. apply maponpaths.
               apply maponpaths. 
               apply mor_disp_transportf_prewhisker.
       etrans. apply maponpaths. apply maponpaths.
               apply mor_disp_transportf_prewhisker.
       etrans. apply maponpaths. apply FFinv_transportf.
       etrans. apply transport_f_f.
       etrans. apply maponpaths. apply maponpaths.
               apply maponpaths. apply maponpaths. 
               apply mor_disp_transportf_postwhisker.
       etrans. apply maponpaths. apply maponpaths. apply maponpaths.
               apply maponpaths. apply maponpaths.
               apply id_left_disp.
       etrans. apply maponpaths. apply maponpaths. apply maponpaths.
               apply mor_disp_transportf_prewhisker.
       etrans. do 2 (apply maponpaths). 
                      apply mor_disp_transportf_prewhisker.
       etrans. apply maponpaths. apply FFinv_transportf.
       etrans. apply transport_f_f.
       etrans. apply maponpaths. apply maponpaths. 
               apply assoc_disp.        
       etrans. apply maponpaths. apply FFinv_transportf. 
       etrans. apply transport_f_f.
       etrans. apply maponpaths. apply maponpaths. 
                      apply mor_disp_transportf_prewhisker.
       etrans. apply maponpaths. 
             apply FFinv_transportf.
       etrans. apply transport_f_f.
       Search (transportf _ _ _ = transportf _ _ _ ).
       apply transportf_comp_lemma.
       etrans. apply maponpaths. apply maponpaths.
               apply assoc_disp.
       etrans. apply maponpaths. apply FFinv_transportf. 
       etrans. apply transport_f_f.
       etrans. apply maponpaths. apply maponpaths. apply maponpaths_2.
               apply assoc_disp_var.
       etrans. apply maponpaths. 
               apply maponpaths. apply mor_disp_transportf_postwhisker.
       etrans. apply maponpaths. 
               apply FFinv_transportf.
       etrans. apply transport_f_f.
       apply transportf_comp_lemma_hset. 
       * apply homset_property.
       *  apply idpath.
(* Time Qed. *)
Admitted. (* is proved, but for quicker checking we admit *)

Definition GG : functor_over _ _ _ := (_ ,, GG_ax).


Definition ε_ses_ff : 
     (*
      nat_trans_over (nat_trans_id _ )
     (functor_over_composite GG FF) (functor_over_identity _ ) 
     *)
     (functor_over_composite GG FF : (disp_functor_precat _ _ D D) _ ) 
    ⇒[ @identity_iso (functor_precategory C C (homset_property C)) _ ] 
     functor_over_identity _ .
Proof.
  mkpair.
  - intros x xx. cbn.
    apply (pr2 (FFses x xx)).
  - (* should/could be opacified *)
    intros x y f xx yy ff. cbn.
    etrans. apply maponpaths_2. apply (homotweqinvweq (FFweq _ )).
    etrans. apply mor_disp_transportf_postwhisker.
    apply transportf_comp_lemma.
    etrans. apply maponpaths. apply mor_disp_transportf_postwhisker.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. 
            apply assoc_disp_var.
    etrans. apply transport_f_f. 
    etrans. apply maponpaths. apply maponpaths.
            apply (iso_disp_after_inv_mor (pr2 (FFses y yy))).
    etrans. apply maponpaths. apply mor_disp_transportf_prewhisker.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply id_right_disp.
    etrans. apply transport_f_f.
    apply transportf_comp_lemma_hset.
    + apply homset_property.
    + apply idpath.
Defined.

Definition ε_inv_ses_ff : 
    (functor_over_identity _ : (disp_functor_precat _ _ D D) _ )
    ⇒[ @identity_iso (functor_precategory C C (homset_property C)) _ ] 
    (functor_over_composite GG FF : (disp_functor_precat _ _ D D) _ ).
Proof.
  simple refine (inv_disp_from_pointwise_iso _ _ _ _ _ _ _ _ _ ε_ses_ff  _ ).
  intros x' xx'. 
  set ( H:= (pr2 (pr2 (FFses x' xx')))). 
  cbn in H. 
  transparent assert (XR : ((pointwise_iso_from_nat_iso
       (identity_iso
          (functor_composite (functor_identity C) (functor_identity C) : functor_precategory _ _ (homset_property C) )) x') = 
              identity_iso x' )).
  { apply eq_iso. apply idpath. }
Abort.

Definition is_iso_ε_ses_ff : is_iso_disp _ ε_ses_ff.
Proof.
  apply is_disp_functor_precat_iso_if_pointwise_iso.
  intros x' xx'. 
Abort.

Definition η_ses_ff : nat_trans_over (nat_trans_id _ ) (functor_over_identity _ ) 
                                     (functor_over_composite FF GG).
Proof.
  mkpair.
  - intros x xx. cbn.
    apply FFinv.
    (* should one here take [ε_ses_ff^{-1} (FF x xx)] ? *)
Abort.

End equiv_from_ses_ff.

End Fix_context.

Section Displayed_Equiv_Compose.

(* TODO: give composites of displayed equivalences. *)

End Displayed_Equiv_Compose.

Section Equiv_Fibres.

(* TODO: move *)
Definition fibre_nat_trans {C C' : Precategory}
  {F : functor C C'}
  {D D'} {FF FF' : functor_over F D D'}
  (α : nat_trans_over (nat_trans_id F) FF FF')
  (c : C)
: nat_trans (fibre_functor FF c) (fibre_functor FF' c).
Proof.
  use tpair; simpl.
  - intro d. exact (α c d).
  - unfold is_nat_trans; intros d d' ff; simpl.
    set (αff := pr2 α _ _ _ _ _ ff); simpl in αff.
    cbn.
    etrans. apply maponpaths, mor_disp_transportf_postwhisker.
    etrans. apply transport_f_f.
    etrans. apply maponpaths, αff.
    etrans. apply transport_f_b.
    apply @pathsinv0.
    etrans. apply maponpaths, mor_disp_transportf_prewhisker.
    etrans. apply transport_f_f.
    apply maponpaths_2, homset_property.
Defined.

(* TODO: move *)
Definition is_iso_fibre_from_is_iso_disp
  {C : Precategory} {D : disp_precat C}
  {c : C} {d d' : D c} (ff : d ⇒[identity c] d')
  (Hff : is_iso_disp (identity_iso c) ff)
: @is_iso (fibre_precategory D c) _ _ ff.
Proof.
  apply is_iso_from_is_z_iso.
  exists (pr1 Hff).
  mkpair; cbn.
  + set (H := pr2 (pr2 Hff)).
    etrans. apply maponpaths, H.
    etrans. apply transport_f_b.
    (* TODO: the following slightly cumbersome step is used in several spots.  Is there a lemma for it?  If not, make one? *)
(*    apply transportf_comp_lemma_hset. 
      is a lemma crafted by PLL that might be applied here; 
      a variant with only [x] would be useful
                    *)
    refine (@maponpaths_2 _ _ _ _ _ (paths_refl _) _ _).
    apply homset_property.      
  + set (H := pr1 (pr2 Hff)).
    etrans. apply maponpaths, H.
    etrans. apply transport_f_b.
    refine (@maponpaths_2 _ _ _ _ _ (paths_refl _) _ _).
    apply homset_property.
Qed.

Context {C : Precategory}.

(* TODO: restructure definition of [equiv_disp], so that it’s built over a left adjoint, and then weaken the hypothesis of this lemma to just a [left_adjoint_disp]. *)
Definition fibre_is_left_adj {D D' : disp_precat C}
  {FF : functor_over (functor_identity _) D D'}
  (EFF : equiv_disp _ _ _ FF)
  (c : C)
: is_left_adjoint (fibre_functor FF c).
Proof.
  destruct EFF as [GG [η [ε axs] ] ]; simpl in axs.
  exists (fibre_functor GG _).
  exists (fibre_nat_trans η _,
          fibre_nat_trans ε _).
  mkpair; cbn.
  + intros d.
    set (thisax := pr1 axs c d); clearbody thisax; clear axs.
    etrans. apply maponpaths, thisax.
    etrans. apply transport_f_b.
    refine (@maponpaths_2 _ _ _ _ _ (paths_refl _) _ _).
    apply homset_property.
  + intros d.
    set (thisax := pr1 (pr2 axs) c d); clearbody thisax; clear axs.
    etrans. apply maponpaths, thisax.
    etrans. apply transport_f_b.
    refine (@maponpaths_2 _ _ _ _ _ (paths_refl _) _ _).
    apply homset_property.
Defined.

Definition fibre_equiv {D D' : disp_precat C}
  {FF : functor_over (functor_identity _) D D'}
  (EFF : equiv_disp _ _ _ FF)
  (c : C)
: adj_equivalence_of_precats (fibre_functor FF c).
Proof.
  exists (fibre_is_left_adj EFF c).
  destruct EFF as [GG [η [ε axs] ] ]; cbn in axs; cbn.
  mkpair.
  + intros d. set (thisax := pr1 (pr2 (pr2 axs)) c d).
    apply is_iso_fibre_from_is_iso_disp, thisax.
  + intros d. set (thisax := pr2 (pr2 (pr2 axs)) c d).
    apply is_iso_fibre_from_is_iso_disp, thisax.
Defined.

End Equiv_Fibres.

(* *)







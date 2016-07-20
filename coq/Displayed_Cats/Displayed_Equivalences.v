(**
“Displayed equivalences” of displayed (pre)categories
*)

Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.

Require UniMath.Ktheory.Utilities.

Require Import Systems.Auxiliary.
Require Import Systems.UnicodeNotations.
Require Import Systems.Displayed_Cats.Auxiliary.
Require Import Systems.Displayed_Cats.Displayed_Precats.
Require Import Systems.Displayed_Cats.Displayed_Precats_bis.


Local Set Automatic Introduction.
(* only needed since imports globally unset it *)

Local Open Scope type_scope.

Undelimit Scope transport.

Notation "# F" := (functor_over_on_morphisms F)
  (at level 3) : mor_disp_scope.

Local Open Scope mor_disp_scope.



Section move_upstream.

Lemma transportf_pathsinv0_var :
Π {X : UU} {P : X → UU} {x y : X} {p : x = y} {u : P x} 
{v : P y}, transportf P p u = v → transportf P (!p) v = u.
Proof.
  intros. induction p. apply (!X0).
Defined.

End move_upstream.

(*

we have F : C -> C',
and FF : D -> D' over F,
then dses says:
for any c:C and d : D' (F c),
there’s some “lift” [ dbar : D c ]
and some iso [ d <~> d' ] over [ id (F c) ].
*)

(* TODO: consider changing this identifier, since “SES” is such a well-established abbreviation for “short exact sequence”. *)
Definition ses_disp {C' C : Precategory}
  {D' : disp_precat C'} {D : disp_precat C}
  {F : functor C' C} (FF : functor_over F D' D) : UU
  := 
  Π (c' : C') (d' : D (F c')),
   Σ (dbar : D' c'), iso_disp (identity_iso _ ) (FF _ dbar) d'.



Lemma functor_over_transportf {C' C : Precategory}
  {D' : disp_precat C'} {D : disp_precat C}
  (F : functor C' C) (FF : functor_over F D' D)
  (x' x : C') (f' f : x' ⇒ x) (p : f' = f)
  (xx' : D' x') (xx : D' x)
  (ff : xx' ⇒[ f' ] xx) 
  :
  # FF (transportf (mor_disp _ _ ) p ff)
  = 
  transportf _ (maponpaths (#F)%mor p) (#FF ff) .
Proof.
  induction p.
  apply idpath.
Defined.

(** Fibre precategory *)

Section fibre_precategory.

Variable C : Precategory.
Variable D : disp_precat C.
Variable c : C.

Definition fibre_precategory_data : precategory_data.
Proof.
  mkpair.
  - mkpair.
    + apply (ob_disp D c).
    + intros xx xx'. apply (mor_disp xx xx' (identity c)).
  - mkpair.
    + intros. apply id_disp.
    + intros. apply (transportf _ (id_right _ ) (comp_disp X X0)).
Defined.

Lemma fibre_is_precategory : is_precategory fibre_precategory_data.
Proof.
  repeat split; intros; cbn.
  - etrans. apply maponpaths. apply id_left_disp.
    etrans. apply transport_f_f. apply transportf_comp_lemma_hset. 
    apply (homset_property). apply idpath.
  - etrans. apply maponpaths. apply id_right_disp.
    etrans. apply transport_f_f. apply transportf_comp_lemma_hset. 
    apply (homset_property). apply idpath.
  - etrans. apply maponpaths. apply mor_disp_transportf_prewhisker.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply assoc_disp.
    etrans. apply transport_f_f.
    apply pathsinv0. 
    etrans. apply maponpaths.  apply mor_disp_transportf_postwhisker.
    etrans. apply transport_f_f.
    apply transportf_ext. apply homset_property.
Qed.

Definition fibre_precategory : precategory := ( _ ,, fibre_is_precategory).

Lemma has_homsets_fibre : has_homsets fibre_precategory.
Proof.
  intros x y. apply homsets_disp.
Qed.



Definition iso_disp_from_iso_fibre (a b : fibre_precategory) :
  iso a b -> iso_disp (identity_iso c) a b.
Proof.
 intro i.
 mkpair.
 + apply (pr1 i).
 + cbn. 
   mkpair. 
   * apply (inv_from_iso i).
   * abstract (  split;
       [ assert (XR := iso_after_iso_inv i);
        cbn in *;
        assert (XR' := transportf_pathsinv0_var XR);
        etrans; [ apply (!XR') |];
        apply transportf_ext; apply homset_property
       |assert (XR := iso_inv_after_iso i);
        cbn in *;
        assert (XR' := transportf_pathsinv0_var XR);
        etrans; [ apply (!XR') | ];
        apply transportf_ext; apply homset_property ] ).
Defined.

Definition iso_fibre_from_iso_disp (a b : fibre_precategory) :
  iso a b <- iso_disp (identity_iso c) a b.
Proof.
  intro i.
  mkpair.
  + apply (pr1 i).
  + cbn in *. 
    apply (@is_iso_from_is_z_iso fibre_precategory).
    mkpair.
    apply (inv_mor_disp_from_iso i).
    abstract (split; cbn;
              [
                assert (XR := inv_mor_after_iso_disp i);
                etrans; [ apply maponpaths , XR |];
                etrans; [ apply transport_f_f |];
                apply transportf_comp_lemma_hset;
                  try apply homset_property; apply idpath
              | assert (XR := iso_disp_after_inv_mor i);
                etrans; [ apply maponpaths , XR |] ;
                etrans; [ apply transport_f_f |];
                apply transportf_comp_lemma_hset;
                try apply homset_property; apply idpath
              ]). 
Defined.

Lemma iso_disp_iso_fibre (a b : fibre_precategory) :
  iso a b ≃ iso_disp (identity_iso c) a b.
Proof.
  exists (iso_disp_from_iso_fibre a b).
  use (gradth _ (iso_fibre_from_iso_disp _ _ )).
  - intro. apply eq_iso. apply idpath.
  - intro. apply eq_iso_disp. apply idpath.
Defined.
    

Variable H : is_category_disp D.

Let idto1 (a b : fibre_precategory) : a = b ≃ iso_disp (identity_iso c) a b 
  := 
  weqpair (@idtoiso_fiber_disp _ _ _ a b) (H _ _ (idpath _ ) a b).

Let idto2 (a b : fibre_precategory) : a = b -> iso_disp (identity_iso c) a b 
  := 
  funcomp (λ p : a = b, idtoiso p) (iso_disp_iso_fibre a b).

Lemma eq_idto1_idto2 (a b : fibre_precategory) 
  : Π p : a = b, idto1 _ _ p = idto2 _ _ p.
Proof.
  intro p. induction p.
  apply eq_iso_disp.
  apply idpath.
Qed.

Lemma is_univalent_fibre_precat 
  (a b : fibre_precategory)
  :
  isweq (λ p : a = b, idtoiso p).
Proof.
  use (twooutof3a _ (iso_disp_iso_fibre a b)). 
  - use (isweqhomot (idto1 a b)).
    + intro p.
      apply eq_idto1_idto2.
    + apply weqproperty.
  - apply weqproperty.
Defined.    


Lemma is_category_fibre : is_category fibre_precategory.
Proof.
  split.
  - apply is_univalent_fibre_precat.
  - apply has_homsets_fibre.
Defined.

End fibre_precategory.

Arguments fibre_precategory {_} _ _ .

(* TODO: this notation interferes with the parsing of elim patterns,
  e.g. [ destruct XYZ as [[X Y] Z] ].  Perhaps find alternative notation. *)
Notation "D [[ x ]]" := (fibre_precategory D x)(at level 3,format "D [[ x ]]").

Section fibre_functor.

Variables C' C : Precategory.
Variable F : functor C' C.
Variable D' : disp_precat C'.
Variable D : disp_precat C.
Variable FF : functor_over F D' D.

Variable x' : C'.

Definition fibre_functor_data : functor_data D'[[x']] D[[F x']].
Proof.
  mkpair.
  - apply (fun xx' => FF xx').
  - intros xx' xx ff.
    apply (transportf _ (functor_id _ _ ) (# FF ff)).
Defined.

Lemma is_functor_fibre : is_functor fibre_functor_data.
Proof.
  split; unfold functor_idax, functor_compax; cbn.
  - intros.
    apply Utilities.transportf_pathsinv0.
    apply pathsinv0. apply functor_over_id.
  - intros.
    etrans. apply maponpaths. apply functor_over_transportf.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply functor_over_comp.
    etrans. apply transport_f_f.
    apply pathsinv0.
    etrans. apply maponpaths. apply mor_disp_transportf_prewhisker.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply mor_disp_transportf_postwhisker.
    etrans. apply transport_f_f.
    apply transportf_comp_lemma.
    apply transportf_comp_lemma_hset.
    + apply homset_property.
    + apply idpath.
Qed.

Definition fibre_functor : functor _ _ := ( _ ,, is_functor_fibre).

End fibre_functor.

Section fibre_functor_identity_ff.

Variables C : Precategory.
Variables D' D : disp_precat C.
Variable FF : functor_over (functor_identity _ ) D' D.
Hypothesis H : functor_over_identity_ff FF.

Lemma fibre_functor_identity_ff (x : C) : fully_faithful (fibre_functor _ _ _ _ _ FF x).
Proof.
  intros xx yy. apply H.
Defined.

End fibre_functor_identity_ff.

Section fibre_functor_ff.
Variables C' C : Precategory.
Variable F : functor C' C.
Variable D' : disp_precat C'.
Variable D : disp_precat C.
Variable FF : functor_over F D' D.

Hypothesis H : functor_over_ff FF.

Lemma fibre_functor_ff (x : C') : fully_faithful (fibre_functor _ _ _ _ _ FF x).
Proof.
  intros xx yy; cbn.
  set (XR := H _ _ xx yy (identity _ )).
  apply twooutof3c.
  - apply XR.
  - apply isweqtransportf.
Defined.

Variable X : functor_over_ess_split_surj _ FF.
Variable Y : iso_fibration D'.

Definition fibre_functor_ess_split_surj (x' : C') : 
   forall yy : D[[F x']], Σ xx : D'[[x']], 
                iso (fibre_functor _ _ _ _ _ FF x' xx) yy.
Proof.
  intro yy.
  set (XR := X _ yy).
  destruct XR as [c'' [i [xx' ii] ] ].
  set (YY := Y _ _ i xx').
  destruct YY as [ dd pe ].
  mkpair.
  - apply dd.
  - 
    (* now need functor_over_on_iso_disp *)
    set (XR := functor_over_on_iso_disp FF pe).
    set (XR' := iso_inv_from_iso_disp XR).
    (* now need composition of iso_disps *)
    apply  (invweq (iso_disp_iso_fibre _ _ _ _ _ )).
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
    set (XRT := transportf (fun r => iso_disp r (FF x' dd) yy ) 
                           XH).
    apply XRT.
    assumption.
Defined.

End fibre_functor_ff.

(** Composite and  identity displayed functors *)

Section bla.

Variables C'' C' C : Precategory.
Variable D'' : disp_precat C''.
Variable D' : disp_precat C'.
Variable D : disp_precat C.
Variable F' : functor C'' C'.
Variable F : functor C' C.

Variable FF' : functor_over F' D'' D'.
Variable FF : functor_over F D' D.


Definition functor_over_composite_data : functor_over_data (functor_composite F' F) D'' D.
Proof.
  mkpair.
    + intros x'' xx''. apply (FF _ (FF' _ xx'')).
    + intros. apply (# FF  (# FF' X )).
Defined.
Lemma functor_over_composite_axioms :  functor_over_axioms functor_over_composite_data.
Proof.
  split; simpl.
    + intros x'' xx''.
      etrans. apply maponpaths. apply functor_over_id.
      etrans. apply functor_over_transportf.
      etrans. apply maponpaths. apply functor_over_id.
      etrans. apply transport_f_f.
      apply transportf_ext. apply (pr2 C).
    + intros.
      etrans. apply maponpaths. apply functor_over_comp.
      etrans. apply functor_over_transportf.
      etrans. apply maponpaths. apply functor_over_comp.
      etrans. apply transport_f_f.
      apply transportf_ext. apply (pr2 C).
Qed.      

(** TODO : split this for opacification *)
Definition functor_composite_over : functor_over (functor_composite F' F) D'' D.
Proof.
  mkpair.
  - apply functor_over_composite_data.
  - apply functor_over_composite_axioms.
Defined.

Definition functor_identity_over : functor_over (functor_identity _ ) D D.
Proof.
  mkpair.
  - mkpair. 
    + intros; assumption.
    + intros; assumption.
  - split; simpl.      
    + intros; apply idpath.
    + intros; apply idpath.
Defined.
      
End bla.

Arguments functor_composite_over {_ _ _ _ _ _ _ _ } _ _.
Arguments functor_identity_over {_ }_ .
(** definition of displayed quasi-equivalence *)
(** for now a specialized version for displayed precats over
    the same base cat
*)

Section foo.

Variable C : Precategory.
Variables D' D : disp_precat C.


Definition equiv_disp (FF : functor_over (functor_identity _ ) D' D) : UU
  :=
  Σ (GG : functor_over (functor_identity _ ) D D') 
    (η : nat_trans_over (nat_trans_id _ ) 
                (functor_identity_over _ ) (functor_composite_over FF GG)  )
    (ε : nat_trans_over (nat_trans_id _ ) (functor_composite_over GG FF) (functor_identity_over _ ))
  , 
    (Π x xx, #FF ( η x xx) ;;  ε _ (FF _ xx) = 
               transportb _ (id_left _ ) (id_disp _) ) × 
    (Π x xx, η _ (GG x xx) ;; # GG (ε _ xx) = 
               transportb _ (id_left _ ) (id_disp _) ) ×  
    (Π x xx, is_iso_disp (identity_iso _ ) (η x xx) × 
    (Π x xx, is_iso_disp (identity_iso _ ) (ε x xx))). 


Section equiv_from_ses_ff.

(* now construct an [equiv_disp] from a s.e.s. and ff functor *)



Variable FF : functor_over (functor_identity _ ) D' D.
Hypothesis FFses : ses_disp FF.
Hypothesis FFff : functor_over_ff FF.

Let FFinv {x y} xx yy f := invmap (weqpair _ (FFff x y xx yy f)).

Lemma FFinv_transportf x y (f f' : x ⇒ y) (p : f = f') xx yy 
   (ff : FF _ xx ⇒[f] FF _ yy) :
    FFinv _ _ _ (transportf _ p ff) = 
     transportf _ p (FFinv _ _ _ ff).
Proof.
  induction p.
  apply idpath.
Defined.

(*
Variable X : iso_fibration D'.
*)

Local Definition GG : functor_over (functor_identity _ ) D D'.
Proof.
  mkpair.
  - mkpair.
    + intros x xx.
      apply (pr1 (FFses x xx)).
    + intros x y xx yy f X. simpl.
      set (Hxx := FFses x xx).
      set (Hyy := FFses y yy).

      set ( HHH:= 
        transportf _ (id_left _ )   
                   (transportf _ (id_right _ ) ((pr2 Hxx ;; X) ;; inv_mor_disp_from_iso (pr2 Hyy)))).
      set (HF := FFinv  (* (pr1 Hxx) (pr1 Hyy) f *) _ _ _  HHH).
      apply HF.
   - split; simpl.
     + intros x xx.
       etrans. apply FFinv_transportf.
       etrans. apply maponpaths. apply FFinv_transportf.
       Search (transportf _ _ (transportf _ _ _ )).
       etrans. apply transport_f_f.
       apply transportf_comp_lemma.
       admit.
     + intros.
Abort.


End equiv_from_ses_ff.

End foo.


(* *)







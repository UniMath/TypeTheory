
(** Some important constructions on displayed categories

Partial contents:

- Direct products of displayed precategories (and their projections)
  - [dirprod_precat D1 D2]
  - [dirprodpr1_functor], [dirprodpr2_functor]
- Sigmas of displayed precategories
- Displayed functor precat
*)

Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.

Require Import Systems.Auxiliary.
Require Import Systems.UnicodeNotations.

Require Import Systems.Displayed_Cats.Auxiliary.
Require Import Systems.Displayed_Cats.Core.

Local Open Scope mor_disp_scope.

Local Set Automatic Introduction.
(* only needed since imports globally unset it *)

Section Auxiliary.

(** Compare [total2_paths2], [total2_paths_b]. *)
(* TODO: perhaps upstream. *)
Lemma total2_paths2_b {A : UU} {B : A → UU} 
    {a1 : A} {b1 : B a1} {a2 : A} {b2 : B a2}
    (p : a1 = a2) (q : b1 = transportb B p b2)
  : (a1,,b1) = (a2,,b2).
Proof.
  exact (@total2_paths_b _ _ (_,,_) (_,,_) p q).
Defined.

(* TODO: perhaps upstream; consider name *)
Lemma total2_reassoc_paths {A} {B : A → Type} {C : (Σ a, B a) -> Type}
    (BC : A -> Type := fun a => Σ b, C (a,,b))
    {a1 a2 : A} (bc1 : BC a1) (bc2 : BC a2)
    (ea : a1 = a2)
    (eb : transportf _ ea (pr1 bc1) = pr1 bc2)
    (ec : transportf C (total2_paths2 ea eb) (pr2 bc1) = pr2 bc2)
  : transportf _ ea bc1 = bc2.
Proof.
  destruct ea, bc1 as [b1 c1], bc2 as [b2 c2].
  cbn in *; destruct eb, ec.
  apply idpath.
Defined.

(* TODO: as for non-primed version above *)
Lemma total2_reassoc_paths' {A} {B : A → Type} {C : (Σ a, B a) -> Type}
    (BC : A -> Type := fun a => Σ b, C (a,,b))
    {a1 a2 : A} (bc1 : BC a1) (bc2 : BC a2)
    (ea : a1 = a2)
    (eb : pr1 bc1 = transportb _ ea (pr1 bc2))
    (ec : pr2 bc1 = transportb C (total2_paths2_b ea eb) (pr2 bc2))
  : bc1 = transportb _ ea bc2.
Proof.
  destruct ea, bc1 as [b1 c1], bc2 as [b2 c2].
  cbn in eb; destruct eb; cbn in ec; destruct ec.
  apply idpath.
Defined.

End Auxiliary.


(** * Products of displayed (pre)categories 

We directly define direct products of displayed categories over a base.

An alternative would be to define the direct product as the “Sigma-precategory” of the pullback to either factor.  *)
Section Dirprod.

Context {C : Precategory} (D1 D2 : disp_precat C).

Definition dirprod_disp_precat_ob_mor : disp_precat_ob_mor C.
Proof.
  exists (fun c => (D1 c × D2 c)).
  intros x y xx yy f.
  exact (pr1 xx ⇒[f] pr1 yy × pr2 xx ⇒[f] pr2 yy).
Defined.

Definition dirprod_disp_precat_id_comp
  : disp_precat_id_comp _ dirprod_disp_precat_ob_mor.
Proof.
  apply tpair.
  - intros x xx. exact (id_disp _,, id_disp _).
  - intros x y z f g xx yy zz ff gg.
    exact ((pr1 ff ;; pr1 gg),, (pr2 ff ;; pr2 gg)).
Defined.

Definition dirprod_disp_precat_data : disp_precat_data C
  := (_ ,, dirprod_disp_precat_id_comp).

Definition dirprod_disp_precat_axioms
  : disp_precat_axioms _ dirprod_disp_precat_data.
Proof.
  repeat apply tpair.
  - intros. apply dirprod_paths; refine (id_left_disp @ !_).
    + refine (pr1_transportf _ _ _ _ _ _ _).
    + apply pr2_transportf.
  - intros. apply dirprod_paths; refine (id_right_disp @ !_).
    + refine (pr1_transportf _ _ _ _ _ _ _).
    + apply pr2_transportf.
  - intros. apply dirprod_paths; refine (assoc_disp @ !_).
    + refine (pr1_transportf _ _ _ _ _ _ _).
    + apply pr2_transportf.
  - intros. apply isaset_dirprod; apply homsets_disp.
Qed.

Definition dirprod_disp_precat : disp_precat C
  := (_ ,, dirprod_disp_precat_axioms).

Definition dirprodpr1_disp_functor_data
  : functor_over_data (functor_identity C) dirprod_disp_precat (D1).
Proof.
  mkpair.
  - intros x xx; exact (pr1 xx).
  - intros x y xx yy f ff; exact (pr1 ff).
Defined.

Definition dirprodpr1_disp_functor_axioms
  : functor_over_axioms dirprodpr1_disp_functor_data.
Proof.
  split. 
  - intros; apply idpath.
  - intros; apply idpath.
Qed.

Definition dirprodpr1_disp_functor
  : functor_over (functor_identity C) dirprod_disp_precat (D1)
:= (dirprodpr1_disp_functor_data,, dirprodpr1_disp_functor_axioms).


Definition dirprodpr2_disp_functor_data
  : functor_over_data (functor_identity C) dirprod_disp_precat (D2).
Proof.
  mkpair.
  - intros x xx; exact (pr2 xx).
  - intros x y xx yy f ff; exact (pr2 ff).
Defined.

Definition dirprodpr2_disp_functor_axioms
  : functor_over_axioms dirprodpr2_disp_functor_data.
Proof.
  split. 
  - intros; apply idpath.
  - intros; apply idpath.
Qed.

Definition dirprodpr2_disp_functor
  : functor_over (functor_identity C) dirprod_disp_precat (D2)
:= (dirprodpr2_disp_functor_data,, dirprodpr2_disp_functor_axioms).

End Dirprod.

Notation "D1 × D2" := (dirprod_disp_precat D1 D2) : disp_precat_scope.
Delimit Scope disp_precat_scope with disp_precat.
Bind Scope disp_precat_scope with disp_precat.

(** * Sigmas of displayed (pre)categories *)
Section Sigma.

Context {C : Precategory}
        {D : disp_precat C}
        (E : disp_precat (total_precat D)).

Definition sigma_disp_precat_ob_mor : disp_precat_ob_mor C.
Proof.
  exists (fun c => Σ (d : D c), (E (c,,d))).
  intros x y xx yy f.
  exact (Σ (fD : pr1 xx ⇒[f] pr1 yy), 
                (pr2 xx ⇒[f,,fD] pr2 yy)).
Defined.

Definition sigma_disp_precat_id_comp
  : disp_precat_id_comp _ sigma_disp_precat_ob_mor.
Proof.
  apply tpair.
  - intros x xx.
    exists (id_disp _). exact (id_disp (pr2 xx)).
  - intros x y z f g xx yy zz ff gg.
    exists (pr1 ff ;; pr1 gg). exact (pr2 ff ;; pr2 gg).
Defined.

Definition sigma_disp_precat_data : disp_precat_data C
  := (_ ,, sigma_disp_precat_id_comp).


Definition sigma_disp_precat_axioms
  : disp_precat_axioms _ sigma_disp_precat_data.
Proof.
  repeat apply tpair.
  - intros. use total2_reassoc_paths'.
    + apply id_left_disp.
    + etrans. exact (@id_left_disp _ _ _ _ _ _ _ (pr2 ff)).
    (* TODO: why doesn’t [apply homsets_disp] work here,
       and in the other parts of this proof? *)
      apply maponpaths_2, homset_property.
  - intros. use total2_reassoc_paths'.
    + apply id_right_disp.
    + etrans. exact (@id_right_disp _ _ _ _ _ _ _ (pr2 ff)).
      apply maponpaths_2, homset_property.
  - intros. use total2_reassoc_paths'.
    + apply assoc_disp.
    + etrans. 
        exact (@assoc_disp _ _ 
                 _ _ _ _  _ _ _ 
                 _ _ _ _ (pr2 ff) (pr2 gg) (pr2 hh)).
      apply maponpaths_2, homset_property.
  - intros. apply isaset_total2; intros; apply homsets_disp.
Qed.

Definition sigma_disp_precat : disp_precat C
  := (_ ,, sigma_disp_precat_axioms).

Definition sigmapr1_disp_functor_data
  : functor_over_data (functor_identity C) sigma_disp_precat D.
Proof.
  mkpair.
  - intros x xx; exact (pr1 xx).
  - intros x y xx yy f ff; exact (pr1 ff).
Defined.

Definition sigmapr1_disp_functor_axioms
  : functor_over_axioms sigmapr1_disp_functor_data.
Proof.
  split. 
  - intros; apply idpath.
  - intros; apply idpath.
Qed.

Definition sigmapr1_disp_functor
  : functor_over (functor_identity C) sigma_disp_precat D
:= (sigmapr1_disp_functor_data,, sigmapr1_disp_functor_axioms).

(* TODO: complete [sigmapr2_disp]; will be a [functor_lifting], not a [functor_over]. *)

End Sigma.

(** * Displayed functor precategory

Displayed functors and natural transformations form a displayed precategory over the ordinary functor precategory between the bases. *)

Section Functor.
(* TODO: clean up this section a bit. *)

Variables C' C : Precategory.
Variable D' : disp_precat C'.
Variable D : disp_precat C.

Let FunctorsC'C := Precategories.functorPrecategory C' C.

Lemma foo
  (F' F : functor C' C)
  (a' a : nat_trans F' F)
  (p : a' = a )
  (FF' : functor_over F' D' D)
  (FF : functor_over F D' D)
  (b : nat_trans_over a' FF' FF)
  (c' : C')
  (xx' : D' c')
  :
  pr1 (transportf (fun x => nat_trans_over x FF' FF) p b) c' xx' =
      transportf (mor_disp (FF' c' xx') (FF c' xx')) 
           (nat_trans_eq_pointwise p _ )  (b c' xx'). 
Proof.
  induction p.
  assert (XR : nat_trans_eq_pointwise (idpath a') c' = idpath _ ).
  { apply (pr2 C). }
  rewrite XR.
  apply idpath.
Qed.

Lemma nat_trans_over_id_left
  (F' F : functor C' C)
  (a : nat_trans F' F)
  (FF' : functor_over F' D' D)
  (FF : functor_over F D' D)
  (b : nat_trans_over a FF' FF)
  :
   nat_trans_over_comp (nat_trans_over_id FF') b =
   transportb (λ f : nat_trans F' F, nat_trans_over f FF' FF) 
              (id_left (a : FunctorsC'C ⟦ _ , _ ⟧)) 
              b.
Proof.
  apply subtypeEquality.
  { intro. apply isaprop_nat_trans_over_axioms. }
  apply funextsec; intro c'.
  apply funextsec; intro xx'.
  apply pathsinv0. 
  etrans. apply foo.
  apply pathsinv0.
  etrans. apply id_left_disp.
  apply transportf_ext. apply (pr2 C).
Qed.

Lemma nat_trans_over_id_right
  (F' F : functor C' C)
  (a : nat_trans F' F)
  (FF' : functor_over F' D' D)
  (FF : functor_over F D' D)
  (b : nat_trans_over a FF' FF)
  :
   nat_trans_over_comp b (nat_trans_over_id FF) =
   transportb (λ f : nat_trans F' F, nat_trans_over f FF' FF) 
              (id_right (a : FunctorsC'C ⟦ _ , _ ⟧)) 
              b.
Proof.
  apply subtypeEquality.
  { intro. apply isaprop_nat_trans_over_axioms. }
  apply funextsec; intro c'.
  apply funextsec; intro xx'.
  apply pathsinv0. 
  etrans. apply foo.
  apply pathsinv0.
  etrans. apply id_right_disp.
  apply transportf_ext. apply (pr2 C).
Qed.

Lemma nat_trans_over_assoc
  (x y z w : functor C' C)
  (f : nat_trans x y)
  (g : nat_trans y z)
  (h : nat_trans z w)
  (xx : functor_over x D' D)
  (yy : functor_over y D' D)
  (zz : functor_over z D' D)
  (ww : functor_over w D' D)
  (ff : nat_trans_over f xx yy)
  (gg : nat_trans_over g yy zz)
  (hh : nat_trans_over h zz ww)
  :
   nat_trans_over_comp ff (nat_trans_over_comp gg hh) =
   transportb (λ f0 : nat_trans x w, nat_trans_over f0 xx ww) 
     (assoc (f : FunctorsC'C⟦_,_⟧) g h) 
     (nat_trans_over_comp (nat_trans_over_comp ff gg) hh).
Proof.
  apply subtypeEquality.
  { intro. apply isaprop_nat_trans_over_axioms. }
  apply funextsec; intro c'.
  apply funextsec; intro xx'.
  apply pathsinv0.
  etrans. apply foo.
  apply pathsinv0.
  etrans. apply assoc_disp.
  apply transportf_ext.
  apply (pr2 C).
Qed.

Lemma isaset_nat_trans_over
  (x y : functor C' C)
  (f : nat_trans x y)
  (xx : functor_over x D' D)
  (yy : functor_over y D' D)
  :
   isaset (nat_trans_over f xx yy).
Proof.
  intros. simpl in *.
  apply (isofhleveltotal2 2).
  * do 2 (apply impred; intro).
    apply homsets_disp.
  * intro d. 
    do 6 (apply impred; intro).
    apply hlevelntosn. apply homsets_disp.
Qed.

Definition disp_functor_precat : 
  disp_precat (FunctorsC'C).
Proof.
  mkpair.
  - mkpair.
    + mkpair.
      * intro F.
        apply (functor_over F D' D).
      * simpl. intros F' F FF' FF a.
        apply (nat_trans_over a FF' FF).
    + mkpair.
      * intros x xx.
        apply nat_trans_over_id.
      * intros ? ? ? ? ? ? ? ? X X0. apply (nat_trans_over_comp X X0 ).
  - repeat split.
    + apply nat_trans_over_id_left.
    + apply nat_trans_over_id_right.
    + apply nat_trans_over_assoc.
    + apply isaset_nat_trans_over.      
Defined.

(** TODO : characterize isos in the displayed functor precat *)

Definition pointwise_iso_from_nat_iso {A X : precategory} {hsX : has_homsets X}
  {F G : functor_precategory A X hsX}
  (b : iso F G) (a : A) : iso (pr1 F a) (pr1 G a)
  :=
  functor_iso_pointwise_if_iso _ _ _ _ _ b (pr2 b)_ .


Definition pointwise_inv_is_inv_on {A X : precategory} {hsX : has_homsets X}
  {F G : functor_precategory A X hsX}
  (b : iso F G) (a : A) : 
  
  inv_from_iso (pointwise_iso_from_nat_iso b a) =
                                       pr1 (inv_from_iso b) a. 
Proof.
  apply id_right.
Defined.

(** TODO : write a few lemmas about isos in 
    the disp functor precat, 
    to make the following sane

    However: it seems to be better to work on 
    https://github.com/UniMath/UniMath/issues/362
    first.
*)

Definition is_pointwise_iso_if_is_disp_functor_precat_iso
  (x y : FunctorsC'C)
  (f : iso x y)
  (xx : disp_functor_precat x)
  (yy : disp_functor_precat y)
  (FF : xx ⇒[ f ] yy)
  (H : is_iso_disp f FF)
  :
  forall x' (xx' : D' x') , is_iso_disp (pointwise_iso_from_nat_iso f _ )
                          (pr1 FF _ xx' ).
Proof.
  intros x' xx'.
  mkpair.
  - set (X:= pr1 H). simpl in X.
    apply (transportb _ (pointwise_inv_is_inv_on f _ ) (X x' xx')).
  - simpl. repeat split.
    + etrans. apply compl_disp_transp.
      apply pathsinv0.
      apply transportf_comp_lemma.
      assert (XR:= pr1 (pr2 H)).
      assert (XRT :=  (maponpaths pr1 XR)). 
      assert (XRT' :=  toforallpaths _ _ _  (toforallpaths _ _ _ XRT x')).
      apply pathsinv0.
      etrans. apply XRT'. 
      clear XRT' XRT XR.
      assert (XR := foo). 
      specialize (XR _ _ _ _ (! iso_after_iso_inv f)).
      etrans. apply XR.
      apply transportf_comp_lemma.
(*      Search (transportf _ _ ?x = ?y). *)
      apply transportf_comp_lemma_hset.
      apply (pr2 C).
      apply idpath.
    + etrans. apply mor_disp_transportf_prewhisker.      
      apply pathsinv0.
      apply transportf_comp_lemma.
      assert (XR:= pr2 (pr2 H)).
      assert (XRT :=  (maponpaths pr1 XR)). 
      assert (XRT' :=  toforallpaths _ _ _  (toforallpaths _ _ _ XRT x')).
      apply pathsinv0.
      etrans. apply XRT'. 
      clear XRT' XRT XR.
      assert (XR := foo). 
      specialize (XR _ _ _ _ (! iso_inv_after_iso f)).
      etrans. apply XR.
      apply transportf_comp_lemma.
(*      Search (transportf _ _ ?x = ?y). *)
      apply transportf_comp_lemma_hset.
      apply (pr2 C).
      apply idpath.
Defined.

Lemma is_nat_trans_over_pointwise_inv
  (x y : FunctorsC'C)
  (f : iso x y)
  (xx : disp_functor_precat x)
  (yy : disp_functor_precat y)
  (FF : xx ⇒[ f] yy)
  (H : Π (x' : C') (xx' : D' x'),
      is_iso_disp (pointwise_iso_from_nat_iso f x') (pr1 FF x' xx'))
  (x' x0 : C')
  (f0 : x' ⇒ x0)
  (xx' : D' x')
  (xx0 : D' x0)
  (ff : xx' ⇒[ f0] xx0)
  :
   # (yy : functor_over _ _ _)  ff ;; (let RT := pr1 (H x0 xx0) in
               transportf (mor_disp (pr1 yy x0 xx0) (pr1 xx x0 xx0))
                 (id_right (pr1 (inv_from_iso f) x0)) RT) =
   transportb (mor_disp (pr1 yy x' xx') (pr1 xx x0 xx0))
     (nat_trans_ax (inv_from_iso f) x' x0 f0)
     ((let RT := pr1 (H x' xx') in
       transportf (mor_disp (pr1 yy x' xx') (pr1 xx x' xx'))
         (id_right (pr1 (inv_from_iso f) x')) RT) ;; 
      # (xx : functor_over _ _ _) ff).
Proof.
 etrans. apply mor_disp_transportf_prewhisker.
    apply pathsinv0.
    etrans. apply maponpaths. apply mor_disp_transportf_postwhisker.
(*    Search (transportf _ _ _ = transportf _ _ _ ). *)
(*    Search (?e = ?e' -> ?w = ?w' -> _ ?e ?w = _ ?e' ?w'). *)
    etrans. apply transport_f_f.
(*    Search (transportf _ _ _ = transportf _ _ _ ). *)
    apply transportf_comp_lemma.
    set (Hx := H x' xx').
    assert (Hx1 := pr2 (pr2 Hx)).
    set (XR:= iso_disp_precomp (pointwise_iso_from_nat_iso f x' ) (_ ,,Hx)).
(*    Check (# (pr1 yy) ff ;; pr1 (H x0 xx0)). *)
    specialize (XR _  
       (
        ((# (y : functor _ _ ))%mor f0 ;; inv_from_iso (pointwise_iso_from_nat_iso f x0))
          %mor
         ) 
       ).
    specialize (XR ((xx : functor_over _ _ _  ) x0 xx0)).
    set (Xweq := weqpair _ XR).
    apply (invmaponpathsweq Xweq).
    unfold Xweq. clear Xweq.
    etrans.  apply mor_disp_transportf_prewhisker.
    etrans. apply maponpaths. apply assoc_disp.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply maponpaths_2. apply Hx1.
    etrans. apply maponpaths. apply mor_disp_transportf_postwhisker.
    etrans. apply transport_f_f.
    apply pathsinv0.
    etrans. apply assoc_disp.
    assert (XRO := @nat_trans_over_ax _ _ _ _ _ _ _ _ _ FF).
    specialize (XRO _ _ _ xx'  _ ff).
    assert (XR' := ! (Utilities.transportf_pathsinv0 _ _ _ _  (!XRO))).
    clear XRO.
    clear XR. clear Hx1.
    etrans. apply maponpaths. apply maponpaths_2.
            apply XR'.
    etrans. apply maponpaths.  apply mor_disp_transportf_postwhisker. 
    etrans. apply transport_f_f.
    apply pathsinv0. 
    etrans. apply maponpaths. apply id_left_disp.
    etrans. apply transport_f_f.
    apply pathsinv0.
    
    etrans. apply maponpaths. 
            apply assoc_disp_var.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply maponpaths.
            apply (pr2 (pr2 (H _ _ ))).
    etrans. apply maponpaths. apply mor_disp_transportf_prewhisker. 
    etrans. apply maponpaths. apply maponpaths.
            apply id_right_disp.
    etrans. apply transport_f_f.
    etrans. apply transport_f_f.
    apply transportf_ext. apply (pr2 C).
Qed.

Definition inv_disp_from_pointwise_iso 
  (x y : FunctorsC'C)
  (f : iso x y)
  (xx : disp_functor_precat x)
  (yy : disp_functor_precat y)
  (FF : xx ⇒[ f ] yy)
  (H : forall x' (xx' : D' x') , is_iso_disp (pointwise_iso_from_nat_iso f _ )
                          (pr1 FF _ xx' ))
  :     
       yy ⇒[ inv_from_iso f] xx.
Proof.
  mkpair.
  + intros x' xx'.
    simpl in xx. simpl in yy.
    assert (XR : inv_from_iso (pointwise_iso_from_nat_iso f x') =
                                       pr1 (inv_from_iso f) x').
    { apply id_right. }
    set (RT := pr1 (H x' xx')).
    apply (transportf _ XR RT).
  + intros x' x0 f0 xx' xx0 ff.
    apply is_nat_trans_over_pointwise_inv.
Defined.
    
    

Definition is_disp_functor_precat_iso_if_pointwise_iso 
  (x y : FunctorsC'C)
  (f : iso x y)
  (xx : disp_functor_precat x)
  (yy : disp_functor_precat y)
  (FF : xx ⇒[ f ] yy)
  (H : forall x' (xx' : D' x') , is_iso_disp (pointwise_iso_from_nat_iso f _ )
                          (pr1 FF _ xx' ))
  : is_iso_disp f FF.
Proof.  
  mkpair.
  - apply (inv_disp_from_pointwise_iso _ _ _ _ _ FF H).
  - split.
    + apply subtypeEquality.
      { intro. apply isaprop_nat_trans_over_axioms. }
      apply funextsec; intro c'.
      apply funextsec; intro xx'.
      apply pathsinv0.
      etrans. apply foo.
      cbn.
      apply pathsinv0.
      etrans. apply mor_disp_transportf_postwhisker.
      etrans. apply maponpaths. apply (pr1 (pr2 (H c' xx'))).
      etrans. apply transport_f_f.
      apply transportf_ext. apply (pr2 C).
    + apply subtypeEquality.
      { intro. apply isaprop_nat_trans_over_axioms. }
      apply funextsec; intro c'.
      apply funextsec; intro xx'.
      apply pathsinv0.
      etrans. apply foo.
      cbn.
      apply pathsinv0.
      etrans. apply mor_disp_transportf_prewhisker.
      etrans. apply maponpaths. apply (pr2 (pr2 (H c' xx'))).
      etrans. apply transport_f_f.
      apply transportf_ext. apply (pr2 C).
Defined.      

End Functor.


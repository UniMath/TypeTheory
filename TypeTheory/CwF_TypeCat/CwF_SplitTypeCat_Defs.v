(**
  [TypeTheory.CwF_TypeCat.CwF_SplitTypeCat_Defs]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**

In this file, we give the definitions of _split type-categories_ (originally due to Cartmell, here following a version given by Pitts) and _categories with families_ (originally due to Dybjer, here following a formulation given by Fiore).

To facilitate comparing them afterwards, we split up their definitions in a slightly unusual way, starting with the part they share.  The key definitions of this file are therefore (all over a fixed base category [C]):

- _object-extension structures_, [obj_ext_structure], the common core of CwF’s and split type-categories;
- (_functional) term structures_, [term_fun_structure], the rest of the structure of a CwF on [C];
- _cwf-structures_, [cwf_structure], the full structure of a CwF on a category [C];
- _CwF’s_, [cwf]; 
- _q-morphism structures_, [qq_morphism_structure], for rest of the structure of a split type-category on [C];
- _split type-cat structures_, [split_typecat_structure], the full structure of a split type-category on [C].
- _split type-categories_, [split_typecat].

NB: we follow UniMath’s convention that _category_ does not assume saturation/univalence, i.e. means what is sometimes called _precategory_ in the literature.
*)



Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.All. (* TODO: work out what’s actually needed and move into [CategoryTheoryImports]. *)
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheory.
Require Import TypeTheory.Auxiliary.SetsAndPresheaves.

(** * Object-extension structures 

We start by fixing the common core of families structures and split type-category structures: an _object-extension structure_, a presheaf of “types” together with “extension” and “dependent projection” operations, as in the following definition: *)

(* Not intended for external use; provided just for readability. *)
Local Definition obj_ext_structure_explicit (C : category) : UU
  := ∑ Ty : preShv C,
       ∏ (Γ : C) (A : Ty $p Γ ),
         ∑ (ΓA : C), ΓA --> Γ.

(** In order to facilitate working with the category of these structures later, we define them not directly, but as the objects of the total category of a displayed category over [preShv C]. *)

(* TODO: consistentise with notations used in other files *)

Section Obj_Ext_Structures_Disp_Cat_Data.

  Context {C : category}.

  Definition obj_ext_ob_mor : disp_cat_ob_mor (preShv C).
  Proof.
    use tpair.
    - intros Ty.
      exact (∏ (Γ:C) (A : Ty $p Γ), ∑ (ΓA : C), ΓA --> Γ).
    - intros Ty Ty' ext_π ext'_π' F_TY.
      exact (∏ (Γ:C) (A : Ty $p Γ),
             ∑ φ : pr1 (ext_π Γ A) --> pr1 (ext'_π' Γ (F_TY $nt A)),
                 φ ;; pr2 (ext'_π' _ _) = pr2 (ext_π _ _)).
  Defined.

  (* accessor functions: [comp_ext_disp], [obj_ext_disp_π], [obj_ext_disp_φ] *)

  Definition comp_ext_disp {Ty} (X : obj_ext_ob_mor Ty) Γ A : C
  := pr1 (X Γ A).

  Definition obj_ext_disp_π {Ty} (X : obj_ext_ob_mor Ty) {Γ} A
    : comp_ext_disp X Γ A --> Γ
  := pr2 (X Γ A).

  Local Notation π := obj_ext_disp_π.

  Definition obj_ext_mor_disp_φ
      {Ty Ty' : preShv C } {F : Ty --> Ty'}
      {X : obj_ext_ob_mor Ty} {X'} (FF : X -->[F] X')
      {Γ:C} (A : Ty $p Γ)
    : comp_ext_disp X Γ A --> comp_ext_disp X' Γ (F $nt A)
  := pr1 (FF _ _).

  Local Notation φ := obj_ext_mor_disp_φ.

  Definition obj_ext_mor_disp_ax
      {Ty Ty' : preShv C } (F : Ty --> Ty')
      {X : obj_ext_ob_mor Ty} {X'} (FF : X -->[F] X')
      {Γ:C} (A : Ty $p Γ)
    : φ FF A ;; π X' _ = π X A
  := pr2 (FF _ _).

  Definition obj_ext_id_comp : disp_cat_id_comp _ obj_ext_ob_mor.
  Proof.
    use tpair.
    - intros Ty X Γ A. exists (identity _). apply id_left.
    - intros Ty Ty' Ty'' F G X X' X'' FF GG.
      intros Γ A.
      exists ( φ FF A ;; φ GG _ ); cbn.
      etrans. apply @pathsinv0, assoc. 
      etrans. apply maponpaths, obj_ext_mor_disp_ax.
      apply obj_ext_mor_disp_ax.
  Defined.

  Definition obj_ext_data : disp_cat_data (preShv C).
  Proof.
    use tpair.
    - exact obj_ext_ob_mor.
    - exact obj_ext_id_comp.
  Defined.

End Obj_Ext_Structures_Disp_Cat_Data.

(* repeating section notations for file *)
Local Notation φ := obj_ext_mor_disp_φ.

(** Before proving the displayed category axioms, we need some utility lemmas for reasoning with morphisms.

These fall into two main groups:

- [comp_ext_compare] and lemmas. One frequently needs to deal with isomorphisms between context extensions [Γ ◂ A ≃ Γ ◂ A'] induced by type equalities [e : A = A']; so we collect lemmas for them, and notate as [comp_ext_compare e], or concisely just [Δ e]. 

- equality/transport lemmas for displayed morphisms of object-extension structures, over equalities of natrual transformations. 
*)

Section Obj_Ext_Structures_Disp_Utility_Lemmas.

  Context {C : category}.

  Definition comp_ext_compare_iso
      {Ty} {X : obj_ext_ob_mor Ty}
      {Γ : C} {A A' : Ty $p Γ} (e : A = A')
    : z_iso (comp_ext_disp X Γ A) (comp_ext_disp X Γ A')
  := idtoiso (maponpaths _ e).

  Definition comp_ext_compare
      {Ty} {X : obj_ext_ob_mor Ty}
      {Γ : C} {A A' : Ty $p Γ} (e : A = A')
    : comp_ext_disp X Γ A --> comp_ext_disp X Γ A'
  := comp_ext_compare_iso e.

  Local Notation Δ := comp_ext_compare.

  Lemma comp_ext_compare_id 
     {Ty : PreShv C} {X : obj_ext_ob_mor Ty}
     {Γ : C} {A : Ty $p Γ}
    : Δ (idpath A) = identity (comp_ext_disp X Γ A).
  Proof.
    apply idpath.
  Qed.

  Lemma comp_ext_compare_id_general
     {Ty : PreShv C} {X : obj_ext_ob_mor Ty}
     {Γ : C} {A : Ty $p Γ} (e : A = A)
    : Δ e = identity (comp_ext_disp X Γ A).
  Proof.
      assert (e = idpath _) as H. { apply setproperty. }
      refine (maponpaths Δ H).
  Qed.
  
  Lemma comp_ext_compare_comp
     {Ty : PreShv C} {X : obj_ext_ob_mor Ty}
     {Γ : C} {A A' A'' : Ty $p Γ} (e : A = A') (e' : A' = A'')
    : @comp_ext_compare _ X _ _ _ (e @ e') = Δ e ;; Δ e'.
  Proof.
    etrans. 2: { apply idtoiso_concat_pr. }
    apply (maponpaths pr1), (maponpaths idtoiso), maponpathscomp0.
  Qed.
  
  Lemma comp_ext_compare_comp_general
     {Ty : PreShv C} {X : obj_ext_ob_mor Ty}
     {Γ : C} {A A' A'' : Ty $p Γ} (e : A = A') (e' : A' = A'') (e'' : A = A'')
    : @comp_ext_compare _ X _ _ _ e'' = Δ e ;; Δ e'.
  Proof.
    refine (_ @ comp_ext_compare_comp _ _).
    apply maponpaths, setproperty.
  Qed.
  
  Lemma comp_ext_compare_inv
      {Ty : PreShv C} {X : obj_ext_ob_mor Ty}
      {Γ : C} {A A' : Ty $p Γ} (e : A = A')
    : Δ (!e) = inv_from_z_iso (@comp_ext_compare_iso _ X _ _ _ e).
  Proof.
    destruct e; apply idpath.
  Defined.
  
  Lemma comp_ext_compare_π
      {Ty : PreShv C} {X : obj_ext_ob_mor Ty}
      {Γ : C} {A A' : Ty $p Γ} (e : A = A')
    : Δ e ;; obj_ext_disp_π X A' = obj_ext_disp_π X A.
  Proof.
    destruct e; apply id_left.
  Qed.
  
  Lemma obj_ext_mor_disp_eq
      {Ty Ty' : preShv C } (F : Ty --> Ty')
      {X : obj_ext_ob_mor Ty} {X'} (FF GG : X -->[F] X')
      (e : ∏  Γ (A : Ty $p Γ), φ FF A = φ GG A)
    : FF = GG.
  Proof.
    apply funextsec; intros Γ; apply funextsec; intros A.
    use total2_paths_f. 2: { apply homset_property. }
    apply e.
  Defined.

  Lemma obj_ext_mor_disp_transportf
      {Ty Ty' : preShv C } (F F' : Ty --> Ty') (e_F : F = F')
      {X : obj_ext_ob_mor Ty} {X'} (FF: X -->[F] X')
      {Γ} {A : Ty $p Γ}
      (e_FA := maponpaths (fun G => G $nt A) e_F)
    : φ (transportf _ e_F FF) A = φ FF A ;; Δ e_FA.
  Proof.
    etrans.
    { unfold φ. apply maponpaths.
      refine (toforallpaths _ _).
      etrans.
      { refine (toforallpaths _ _); refine (transportf_forall _ _ _). }
      simpl. refine (transportf_forall _ _ _).
    } 
    etrans. { use (pr1_transportf (nat_trans _ _)). }
    etrans. { use (@functtransportf (nat_trans _ _)). }
    etrans. { apply @pathsinv0, idtoiso_postcompose. }
    apply maponpaths, (maponpaths pr1), (maponpaths idtoiso), pathsinv0.
    apply (maponpathscomp (fun G => _) (fun A' => comp_ext_disp X' Γ A')).
  Qed.

  Lemma obj_ext_mor_disp_transportf_gen
      {Ty Ty' : preShv C } {F F' : Ty --> Ty'} (e_F : F = F')
      {X : obj_ext_ob_mor Ty} {X'} (FF: X -->[F] X')
      {Γ} {A : Ty $p Γ} (e_FA : _)
    : φ (transportf _ e_F FF) A = φ FF A ;; Δ e_FA.
  Proof.
    etrans. { apply obj_ext_mor_disp_transportf. }
    apply maponpaths, maponpaths, setproperty.
  Qed.

  Lemma obj_ext_mor_disp_transportb
      {Ty Ty' : preShv C } (F F' : Ty --> Ty') (e_F : F' = F)
      {X : obj_ext_ob_mor Ty} {X'} (FF: X -->[F] X')
      {Γ} {A : Ty $p Γ}
      (e_FA := ! maponpaths (fun G => G $nt A) e_F)
    : φ (transportb _ e_F FF) A = φ FF A ;; Δ e_FA.
  Proof.
    unfold transportb.
    etrans. { apply obj_ext_mor_disp_transportf. }
    apply maponpaths, maponpaths.
    exact (maponpathsinv0 _ e_F).
  Defined.

  Lemma obj_ext_mor_disp_transportb_gen
      {Ty Ty' : preShv C } {F F' : Ty --> Ty'} (e_F : F' = F)
      {X : obj_ext_ob_mor Ty} {X'} (FF: X -->[F] X')
      {Γ} {A : Ty $p Γ} (e_FA : _)
    : φ (transportb _ e_F FF) A = φ FF A ;; Δ (! e_FA).
  Proof.
    etrans. { apply obj_ext_mor_disp_transportb. }
    apply maponpaths, maponpaths, setproperty.
  Qed.

  Lemma obj_ext_mor_disp_transportf_eq
      {Ty Ty' : preShv C } {F G : Ty --> Ty'} (e_F : F = G)
      {X : obj_ext_ob_mor Ty} {X'} {FF : X -->[F] X'} {GG : X -->[G] X'}
      (e : ∏ Γ (A : Ty $p Γ),
         φ FF A ;; Δ (maponpaths (λ F, F $nt A) e_F) = φ GG A)
    : transportf _ e_F FF = GG.
  Proof.
    apply obj_ext_mor_disp_eq.
    intros Γ A.
    etrans. { apply obj_ext_mor_disp_transportf. }
    apply e.
  Qed.

  Lemma obj_ext_mor_disp_transportf_eq_gen
      {Ty Ty' : preShv C } {F G : Ty --> Ty'} (e_F : F = G)
      {X : obj_ext_ob_mor Ty} {X'} {FF : X -->[F] X'} {GG : X -->[G] X'}
      (e_FA : ∏ Γ (A : Ty $p Γ), F $nt A = G $nt A)
      (e : ∏ Γ (A : Ty $p Γ),
         φ FF A ;; Δ (e_FA Γ A) = φ GG A)
    : transportf _ e_F FF = GG.
  Proof.
    apply obj_ext_mor_disp_eq.
    intros Γ A.
    etrans. { apply obj_ext_mor_disp_transportf. }
    etrans. 2: { apply e. }
    apply maponpaths, maponpaths, setproperty.
  Qed.

  Lemma obj_ext_mor_disp_transportb_eq
      {Ty Ty' : preShv C } {F G : Ty --> Ty'} (e_F : F = G)
      {X : obj_ext_ob_mor Ty} {X'} {FF : X -->[F] X'} {GG : X -->[G] X'}
      (e : ∏ Γ (A : Ty $p Γ),
         φ FF A ;; Δ (maponpaths (λ (F:Ty-->Ty'), F $nt A) e_F) = φ GG A)
    : FF = transportb _ e_F GG.
  Proof.
    apply transportb_transpose_right, obj_ext_mor_disp_transportf_eq, e.
  Qed.

  Lemma obj_ext_mor_disp_transportb_eq_gen
      {Ty Ty' : preShv C } {F G : Ty --> Ty'} (e_F : F = G)
      {X : obj_ext_ob_mor Ty} {X'} {FF : X -->[F] X'} {GG : X -->[G] X'}
      (e_FA : ∏ Γ (A : Ty $p Γ), F $nt A = G $nt A)
      (e : ∏ Γ (A : Ty $p Γ),
         φ FF A ;; Δ (e_FA Γ A) = φ GG A)
    : FF = transportb _ e_F GG.
  Proof.
    eapply transportb_transpose_right,
      obj_ext_mor_disp_transportf_eq_gen, e.
  Qed.

End Obj_Ext_Structures_Disp_Utility_Lemmas.

Arguments comp_ext_compare {_ _ _ _ _ _} _.
Local Notation Δ := comp_ext_compare.

Section Obj_Ext_Structures.

  Context {C : category}.

  Definition obj_ext_axioms : disp_cat_axioms _ (@obj_ext_data C).
  Proof.
    repeat use tpair.
    - intros Ty Ty' F X X' FF. 
      use obj_ext_mor_disp_transportb_eq_gen. { intros; apply idpath. }
      intros Γ A; cbn.
      etrans. { apply id_right. }
      apply id_left.
    - intros Ty Ty' F X X' FF.
      use obj_ext_mor_disp_transportb_eq_gen. { intros; apply idpath. }
      intros Γ A; cbn.
      etrans. { apply id_right. }
      apply id_right.
    - intros Ty0 Ty1 Ty2 Ty3 F G H
             X0 X1 X2 X3 FF GG HH.
      use obj_ext_mor_disp_transportb_eq_gen. { intros; apply idpath. }
      intros Γ A; cbn.
      etrans. { apply id_right. }
      apply assoc.
    - intros ? ? ? ? ?.
      apply impred_isaset; intros ?; apply impred_isaset; intros ?.
      apply isaset_total2. { apply homset_property. }
      intros ?; apply isasetaprop, homset_property.
  Qed.

  Definition obj_ext_disp : disp_cat (preShv C).
  Proof.
    use tpair.
    - exact obj_ext_data.
    - exact obj_ext_axioms.
  Defined.

  Definition obj_ext_structure : UU
  := ob (total_category_ob_mor (@obj_ext_data C)).

  Local Definition obj_ext_structure_explicit_correct
    : obj_ext_structure = obj_ext_structure_explicit C.
  Proof.
    reflexivity.
  Qed.

  Definition TY (X : obj_ext_structure) : preShv _ := pr1 X.
  Local Notation "'Ty'" := (fun X Γ => (TY X $p Γ)) (at level 10).
  
  Definition comp_ext (X : obj_ext_structure) Γ A : C
    := comp_ext_disp (pr2 X) Γ A.
  Local Notation "Γ ◂ A" := (comp_ext _ Γ A) (at level 30).
  
  Definition π {X : obj_ext_structure} {Γ} A
    : Γ ◂ A --> Γ
  := obj_ext_disp_π (pr2 X) A.

End Obj_Ext_Structures.

Arguments obj_ext_structure _ : clear implicits.

Local Notation "Γ ◂ A" := (comp_ext _ Γ A) (at level 30).
Local Notation "'Ty'" := (fun X Γ => (TY X $p Γ)) (at level 10).

(** The definitions of term structures and split type-category structures will all be relative to a fixed base category and object-extension structure. *)

Section Families_Structures.

Context {C : category} {X : obj_ext_structure C}.

(** * Families structures 

We now define the extra structure, over an object-extension structure, which constitutes a _category with families_ in the sense of Fiore a reformulation of Dybjer’s original definition, replacing the functor [C --> FAM] with an arrow in [preShv C].

We call this _term structure_, or a _functional_ term structure [term_fun] when necessary to disambiguate from Dybjer-style _familial_ term structures.

Components of [Y : term_fun_structure X]:

- [TM Y : preShv C] 
- [pp Y : TM Y --> TY X]
- [Q Y A :  Yo (Γ ◂ A) --> TM Y]
- [Q_pp Y A : #Yo (π A) ;; yy A = Q Y A ;; pp Y]
- [isPullback_Q_pp Y A : isPullback (Q_pp Y A)]

 See: Marcelo Fiore, slides 32–34 of _Discrete Generalised Polynomial Functors_ , from talk at ICALP 2012,
  #(<a href="http://www.cl.cam.ac.uk/~mpf23/talks/ICALP2012.pdf">link</a>)#
  and comments in file [CwF_def].

*)

Local Notation "A [ f ]" := (#p (TY X) f A) (at level 4).

Definition term_fun_structure_data : UU
  := ∑ TM : preShv C, 
        (TM --> TY X)
        × (∏ (Γ : C) (A : Ty X Γ), TM $p (Γ ◂ A)).

Definition TM (Y : term_fun_structure_data) : preShv C := pr1 Y.
Local Notation "'Tm'" := (fun Y Γ => TM Y $p Γ) (at level 10).

Definition pp Y : TM Y --> TY X := pr1 (pr2 Y).

Definition te Y {Γ:C} A : Tm Y (Γ ◂ A)
  := pr2 (pr2 Y) Γ A.

Definition Q Y {Γ:C} (A:Ty X Γ) : Yo (Γ ◂ A) --> TM Y
  := yy (te Y A).

Lemma comp_ext_compare_Q Y Γ (A A' : Ty X Γ) (e : A = A') : 
  #Yo (Δ e) ;; Q Y A' = Q Y A . 
Proof.
  induction e. 
  etrans. apply maponpaths_2, functor_id.
  apply id_left.
Qed.

(* Note: essentially a duplicate of [TypeTheory.CwF.CwF_def.cwf_square_comm].
  However, using that here would add [CwF_def] as a dependency for this and all subsequent files, which is otherwise not needed; so we repeat the (short) proof to avoid the dependency.  *)
Lemma term_fun_str_square_comm {Y : term_fun_structure_data}
    {Γ : C} {A : Ty X Γ}
    (e : (pp Y) $nt (te Y A) = A [ π A ])
  : #Yo (π A) ;; yy A = Q Y A ;; pp Y.
Proof.
  apply pathsinv0.
  etrans. 2: { apply yy_natural. }
  etrans. apply yy_comp_nat_trans.
  apply maponpaths, e.
Qed.

Definition term_fun_structure_axioms (Y : term_fun_structure_data) :=
  ∏ Γ (A : Ty X Γ), 
        ∑ (e : (pp Y) $nt (te Y A) = A [ π A ]),
          isPullback (term_fun_str_square_comm e).

Lemma isaprop_term_fun_structure_axioms Y
  : isaprop (term_fun_structure_axioms Y).
Proof.
  do 2 (apply impred; intro).
  apply isofhleveltotal2.
  - apply setproperty.
  - intro. apply isaprop_isPullback.
Qed.

Definition term_fun_structure : UU :=
  ∑ Y : term_fun_structure_data, term_fun_structure_axioms Y.
Coercion term_fun_data_from_term_fun (Y : term_fun_structure) : _ := pr1 Y.


Definition pp_te (Y : term_fun_structure) {Γ} (A : Ty X Γ)
  : (pp Y) $nt (te Y A)
    = A [ π A ]
:= pr1 (pr2 Y _ A).

Definition Q_pp (Y : term_fun_structure) {Γ} (A : Ty X Γ) 
  : #Yo (π A) ;; yy A = Q Y A ;; pp Y
:= term_fun_str_square_comm (pp_te Y A).

(* TODO: rename this to [Q_pp_Pb], or [qq_π_Pb] to [isPullback_qq_π]? *)
Definition isPullback_Q_pp (Y : term_fun_structure) {Γ} (A : Ty X Γ)
  : isPullback (Q_pp Y A)
:= pr2 (pr2 Y _ _ ).

(* TODO: look for places these three lemmas can be used to simplify proofs *) 
Definition Q_pp_Pb_pointwise (Y : term_fun_structure) (Γ' Γ : C) (A : Ty X Γ)
  := isPullback_preShv_to_pointwise (isPullback_Q_pp Y A) Γ'.

Definition Q_pp_Pb_univprop (Y : term_fun_structure) (Γ' Γ : C) (A : Ty X Γ)
  := pullback_HSET_univprop_elements _ (Q_pp_Pb_pointwise Y Γ' Γ A).

Definition Q_pp_Pb_unique (Y : term_fun_structure) (Γ' Γ : C) (A : Ty X Γ)
  := pullback_HSET_elements_unique (Q_pp_Pb_pointwise Y Γ' Γ A).

(** ** Terms as sections *)

(* In any term structure, “terms” correspond to sections of dependent projections.  For now, we do not need this full isomorphism, but we construct the beginning of the correspondence. *)
  
Lemma term_to_section_aux {Y : term_fun_structure} {Γ:C} (t : Tm Y Γ) 
  (A := pp Y $nt t)
  : iscontr
    (∑ (f : Γ --> Γ ◂ A), 
         f ;; π _ = identity Γ
       × Q Y A $nt f = t).
Proof.
  set (Pb := isPullback_preShv_to_pointwise (isPullback_Q_pp Y A) Γ).
  simpl in Pb.
  apply (pullback_HSET_univprop_elements _ Pb).
  apply functor_id_pshf.
Qed.

Lemma term_to_section {Y : term_fun_structure} {Γ:C} (t : Tm Y Γ) 
  (A := pp Y $nt t)
  : ∑ (f : Γ --> Γ ◂ A), (f ;; π _ = identity Γ).
Proof.
  set (sectionplus := iscontrpr1 (term_to_section_aux t)).
  exists (pr1 sectionplus).
  exact (pr1 (pr2 sectionplus)).
Defined.

(* TODO: unify with lemmas following [bar] in […_Equivalence]? *)
Lemma term_to_section_recover {Y : term_fun_structure}
  {Γ:C} (t : Tm Y Γ) (A := pp Y $nt t)
  : Q Y A $nt (pr1 (term_to_section t)) = t.
Proof.
  exact (pr2 (pr2 (iscontrpr1 (term_to_section_aux t)))).
Qed.

Lemma Q_comp_ext_compare {Y : term_fun_structure}
    {Γ Γ':C} {A A' : Ty X Γ} (e : A = A') (t : Γ' --> Γ ◂ A)
  : Q Y A' $nt (t ;; Δ e)
  = Q Y A $nt t.
Proof.
  destruct e. apply maponpaths, id_right.
Qed.

End Families_Structures.

Section qq_Morphism_Structures.

(* NOTE: most of this section does not require the [homset_property] for [C]. If the few lemmas that do require it were moved out of the section, e.g. [isaprop_qq_morphism_axioms], then would could take [C] as just a [precategory] here. Perhaps worth doing so? Would mainly be relevant if we wanted to generalise to bicategories. *)

Context {C : category} {X : obj_ext_structure C}.

(** * q-morphism structures, split type-categories

On the other hand, a _q-morphism structure_ (over an object-extension structure) is what is required to constitute a _split type-category_.

Up to ordering/groupoing of the components, these are essentially the _type-categories_ of Andy Pitts, _Categorical Logic_, 2000, Def. 6.3.3 #(<a href="http://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-367.html">link</a>)# (which in turn were a reformulation of Cartmell’s _categories with attributes_).

Our terminology follows van den Berg and Garner, _Topological and simplicial models_, Def 2.2.1 #(<a href="http://arxiv.org/abs/1007.4638">arXiv</a>)# 
in calling this notion a _split_ type-category, and reserving _type-category_ (unqualified) for the weaker version without hSet/splitness assumptions.  We formalise non-split type-categories elsewhere, since they do not extend object-extension structures.

Beyond the object extension structure, the only further data in a split type-category is the morphisms customarily denoted [qq f A : Γ ◂ A --> Γ] (satisfying certain axioms).  We therefore call this data a _q_-morphism structure.

Components of [Z : qq_morphism_structure X]:

- [qq Z f A : Γ' ◂ A[f] --> Γ ◂ A]
- [qq_π Z f A : qq Z f A ;; π A = π _ ;; f]
- [qq_π_Pb Z f A : isPullback (!qq_π Z f A)]
- [qq_id], [qq_comp]: functoriality for [qq]
*)

Local Notation "A [ f ]" := (#p (TY X) f A) (at level 4).

Definition qq_morphism_data : UU :=
  ∑ q : ∏ {Γ Γ'} (f : C⟦Γ', Γ⟧) (A : TY X $p Γ), 
           C ⟦Γ' ◂ A [ f ], Γ ◂ A⟧, 
    (∏ Γ Γ' (f : C⟦Γ', Γ⟧) (A : TY X $p Γ), 
        ∑ e : q f A ;; π _ = π _ ;; f , isPullback (!e)).

Definition qq (Z : qq_morphism_data) {Γ Γ'} (f : C ⟦Γ', Γ⟧)
              (A : TY X $p Γ) 
  : C ⟦Γ' ◂ A [ f ], Γ ◂ A⟧
:= pr1 Z _ _ f A.

(* TODO: consider changing the direction of this equality? *)
Lemma qq_π (Z : qq_morphism_data) {Γ Γ'} (f : Γ' --> Γ) (A : _ )
  : qq Z f A ;; π A = π _ ;; f.
Proof.
  exact (pr1 (pr2 Z _ _ f A)).
Qed.

Lemma qq_π_Pb (Z : qq_morphism_data) {Γ Γ'} (f : Γ' --> Γ) (A : _ )
  : isPullback (!qq_π Z f A).
Proof.
  exact (pr2 (pr2 Z _ _ f A)).
Qed.

Lemma comp_ext_compare_qq (Z : qq_morphism_data)
  {Γ Γ'} {f f' : C ⟦Γ', Γ⟧} (e : f = f') (A : Ty X Γ) 
  : Δ (maponpaths (λ k : C⟦Γ', Γ⟧, A [k]) e) ;; qq Z f' A
  = qq Z f A.
Proof.
  induction e.
  apply id_left.
Qed.

Lemma comp_ext_compare_qq_general (Z : qq_morphism_data)
  {Γ Γ' : C} {f f' : Γ' --> Γ} (e : f = f')
  {A : Ty X Γ} (eA : A[f] = A[f']) 
  : Δ eA ;; qq Z f' A
  = qq Z f A.
Proof.
  use (_ @ comp_ext_compare_qq _ e A).
  apply maponpaths_2, maponpaths, setproperty.
Qed.

Definition qq_morphism_axioms (Z : qq_morphism_data) : UU
  := 
    (∏ Γ A,
    qq Z (identity Γ) A
    = Δ (functor_id_pshf A))
  ×
    (∏ Γ Γ' Γ'' (f : C⟦Γ', Γ⟧) (g : C⟦Γ'', Γ'⟧) (A : TY X $p Γ),
    qq Z (g ;; f) A
    = Δ (functor_comp_pshf A _ _)
      ;; qq Z g (A [f]) 
      ;; qq Z f A).

Definition qq_morphism_structure : UU
  := ∑ Z : qq_morphism_data,
           qq_morphism_axioms Z.

Definition qq_morphism_data_from_structure :
   qq_morphism_structure -> qq_morphism_data := pr1.
Coercion qq_morphism_data_from_structure :
   qq_morphism_structure >-> qq_morphism_data.

Definition qq_id (Z : qq_morphism_structure)
    {Γ} (A : Ty X Γ)
  : qq Z (identity Γ) A
  = Δ (functor_id_pshf A)
:= pr1 (pr2 Z) _ _.

Definition qq_comp (Z : qq_morphism_structure)
    {Γ Γ' Γ'' : C}
    (f : C ⟦ Γ', Γ ⟧) (g : C ⟦ Γ'', Γ' ⟧) (A : Ty X Γ)
  : qq Z (g ;; f) A
  = Δ (functor_comp_pshf A _ _)
    ;; qq Z g (A [f]) ;; qq Z f A
:= pr2 (pr2 Z) _ _ _ _ _ _.

Lemma isaprop_qq_morphism_axioms (Z : qq_morphism_data)
  : isaprop (qq_morphism_axioms Z).
Proof.
  apply isofhleveldirprod.
  - do 2 (apply impred; intro).
    apply homset_property.
  - do 6 (apply impred; intro).
    apply homset_property.    
Qed.

(* Since [Ty X] is always an hset, the splitness properties hold with any path in place of the canonical ones. This is sometimes handy, as one may want to opacify the canonical equalities in examples. *)
Lemma qq_comp_general (Z : qq_morphism_structure)
  {Γ Γ' Γ'' : C}
  {f : C ⟦ Γ', Γ ⟧} {g : C ⟦ Γ'', Γ' ⟧} {A : Ty X Γ}
  (p : A [g ;; f]
       = #p (TY X) g (#p (TY X) f A)) 
: qq Z (g ;; f) A
  = Δ p ;; qq Z g (A [f]) ;; qq Z f A.
Proof.
  eapply pathscomp0. apply qq_comp.
  repeat apply (maponpaths (fun h => h ;; _)).
  repeat apply maponpaths. apply uip. apply setproperty.
Qed.

End qq_Morphism_Structures.

Arguments term_fun_structure_data _ _ : clear implicits.
Arguments term_fun_structure_axioms _ _ _ : clear implicits.
Arguments term_fun_structure _ _ : clear implicits.
Arguments qq_morphism_data [_] _ .
Arguments qq_morphism_structure [_] _ .

(** * CwF’s, split type-categories *)

(** Here, we assemble the components above (object-extension structures, term-structures, and _q_-morphism structures) into versions of the definitions of CwF’s and split type-categories.

These are reassociated compared to the canonical definitions; equivalences between these and the canonical ones are provided in [CwF_Defs_Equiv.v] and [TypeCat_Reassoc.v] respectively. *)
(* TODO: rename one of those files, for consistency (and make sure README up-to-date on filenames). *)

Definition cwf'_structure (C : category) : UU 
:= ∑ X : obj_ext_structure C, term_fun_structure C X.

Coercion obj_ext_structure_of_cwf'_structure {C : category}
:= pr1 : cwf'_structure C -> obj_ext_structure C.

Coercion term_fun_structure_of_cwf'_structure {C : category}
:= pr2 : forall XY : cwf'_structure C, term_fun_structure C XY.

Definition cwf' : UU
:= ∑ C : category, cwf'_structure C.

Coercion precategory_of_cwf' := pr1 : cwf' -> category.

Coercion cwf'_structure_of_cwf' := pr2 : forall C : cwf', cwf'_structure C.

Definition split_typecat'_structure (C : category) : UU 
:= ∑ X : obj_ext_structure C, qq_morphism_structure X.

Coercion obj_ext_structure_of_split_typecat'_structure {C : category}
:= pr1 : split_typecat'_structure C -> obj_ext_structure C.

Coercion qq_morphism_structure_of_split_typecat'_structure {C : category}
:= pr2 : forall XY : split_typecat'_structure C, qq_morphism_structure XY.

Definition split_typecat' : UU
  := ∑ C : category, split_typecat'_structure C.

Coercion precategory_of_split_typecat'
:= pr1 : split_typecat' -> category.

Coercion split_typecat'_structure_of_split_typecat'
:= pr2 : forall C : split_typecat', split_typecat'_structure C.


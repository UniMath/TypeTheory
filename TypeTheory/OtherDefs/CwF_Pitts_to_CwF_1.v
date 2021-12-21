
(**

 Ahrens, Lumsdaine, Voevodsky, 2015

  Contents:

    - Definition of a precategory with families
    - Proof that reindexing forms a pullback

  The definition is based on Pitts, *Nominal Presentations of the Cubical Sets
  Model of Type Theory*, Def. 3.1: 
  http://www.cl.cam.ac.uk/~amp12/papers/nompcs/nompcs.pdf (page=9)
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.limits.pullbacks.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.OtherDefs.CwF_Pitts.
Require Import TypeTheory.OtherDefs.CwF_1.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op").


Section fix_a_precategory.
  
  Variable C : category.

  Section CwF_1_from_CwF.
  
  Variable CC : CwF_Pitts.cwf_struct C.

  Definition type_functor : functor C^op HSET.
  Proof.
    use tpair.
    - exists (fun Γ => make_hSet
                         (CwF_Pitts.type CC Γ)
                         (CwF_Pitts.cwf_types_isaset CC Γ)).
      simpl.
      intros a b f A.
      apply (CwF_Pitts.rtype A f).
    -  split; intros; simpl.
       + intro Γ; simpl;
         apply funextsec; intro A;
         apply CwF_Pitts.reindx_type_id;
         apply CwF_Pitts.reindx_laws_from_cwf_struct.
       + intros Γ Γ' Γ'' γ γ';
         apply funextsec; intro A;
         apply CwF_Pitts.reindx_type_comp;
         apply CwF_Pitts.reindx_laws_from_cwf_struct.
  Defined.

  Definition CwF_1_data_from_CwF : CwF_1.tt_reindx_type_struct C.
  Proof.    
    use tpair; [use tpair; [use tpair; [use tpair|]|]|].
    - apply type_functor.
    - simpl. intros Γ A. apply (CwF_Pitts.term CC Γ A).
    - intros Γ Γ' A a γ. simpl in *.
      apply (CwF_Pitts.rterm a γ).
    - intros Γ A. simpl in *.
      exists (CwF_Pitts.comp_obj Γ A).
      exact (CwF_Pitts.proj_mor A).
    - simpl.
      intros Γ A; simpl in *.
      refine (make_dirprod _ _ ).
      + apply (CwF_Pitts.gen_elem  _ ).
      + intros Γ' γ a.
        apply (CwF_Pitts.pairing γ a ).
  Defined.

  Definition CwF_1_laws_from_CwF : CwF_1.cwf_laws CwF_1_data_from_CwF.
  Proof.
    split. 2: { apply CwF_Pitts.cwf_terms_isaset. }
    use tpair; [use tpair|].
    - simpl; intros Γ A a.
      eapply pathscomp0. { apply CwF_Pitts.reindx_term_id. }
      apply maponpaths_2.
      apply maponpaths.
      apply pathsinv0.
      unfold functor_id. simpl.
      rewrite toforallpaths_funextsec.
      apply idpath.
    - simpl.
      intros.
      eapply pathscomp0. { apply CwF_Pitts.reindx_term_comp. }
      apply maponpaths_2.
      apply maponpaths.
      apply pathsinv0.
      unfold functor_comp; simpl.
      rewrite toforallpaths_funextsec.
      apply idpath.
    - repeat split; simpl.
      * intros Γ A Γ' γ a.
        simpl in *; use tpair.
        { apply CwF_Pitts.cwf_law_1. }
        simpl in *.
        eapply pathscomp0. 2: apply CwF_Pitts.cwf_law_2.
        apply maponpaths.
        apply maponpaths_2.
        apply maponpaths.
        unfold reindx_type_comp. simpl.
        unfold functor_comp. simpl.
        rewrite toforallpaths_funextsec.
        apply idpath.
      * intros ? ? ? ? ? ? ? .
        simpl in *.
        eapply pathscomp0. { apply CwF_Pitts.cwf_law_3. }
        apply maponpaths.
        apply maponpaths_2.
        apply CwF_Pitts.cwf_types_isaset.
      * intros ? ? .
        simpl in *.
        apply CwF_Pitts.cwf_law_4.
  Defined.
     
  Definition CwF_1_from_CwF : CwF_1.cwf_struct C.
  Proof.
    exists CwF_1_data_from_CwF.
    apply CwF_1_laws_from_CwF.
  Defined.

  End CwF_1_from_CwF.

  Section CwF_from_CwF_1.

    Variable CC : CwF_1.cwf_struct C.

    Definition CwF_data_from_CwF_1 : CwF_Pitts.tt_reindx_type_struct C.
    Proof.
      use tpair; [use tpair; [use tpair; [use tpair|]|]|].
      - intro Γ.
        apply (CwF_1.type CC Γ).
      - simpl.
        intros Γ A.
        apply (CwF_1.term CC Γ A).
      - simpl.
        use tpair.
        + simpl.
          intros Γ Γ' A γ.
          apply (rtype A γ).
        + simpl.
          intros Γ Γ' A a γ.
          apply (rterm a γ).
      - intros Γ A.
        exists (comp_obj Γ A).
        exact (proj_mor A).
      - intros Γ A; simpl in Γ, A |- *. split.
        * apply gen_elem.
        * intros Γ' γ a.
          exact (pairing γ a).
    Defined.

    Definition CwF_laws_from_CwF_1 : CwF_Pitts.cwf_laws CwF_data_from_CwF_1.
    Proof.
      split; simpl.
      2: { split.
           - intro. apply setproperty.
           - intros Γ A. apply CwF_1.cwf_terms_isaset.
      }
      use tpair; [use tpair|].
      - unfold reindx_laws_type.
        split; simpl.
        + intros Γ A.
          apply CwF_1.reindx_type_id.
        + intros.
          apply CwF_1.reindx_type_comp.
      - split.
        + simpl.
          intros Γ A a.
          apply CwF_1.reindx_term_id, CC.
        + simpl.
          intros.
          apply CwF_1.reindx_term_comp, CC.
      - simpl. split; [|split].
        + intros ? ? ? ? ? .
          simpl in * |-.
          use tpair.
          * apply CwF_1.cwf_law_1.
          * apply CwF_1.cwf_law_2.
        + intros ? ? ? ? ? ? ? .
          simpl in *|-.
          apply CwF_1.cwf_law_3.
        + intros ? ? .
          simpl in A.
          apply CwF_1.cwf_law_4.
    Defined.
    
    Definition CwF_from_CwF_1 : CwF_Pitts.cwf_struct C.
    Proof.
      exists CwF_data_from_CwF_1.
      apply CwF_laws_from_CwF_1.
    Defined.

  End CwF_from_CwF_1.

  
  Lemma CwF_1_to_CwF_to_CwF_1 (CC : CwF_1.cwf_struct C)
    : CwF_1_from_CwF (CwF_from_CwF_1 CC) = CC.
  Proof.
    apply (subtypePath).
    { apply (isPredicate_cwf_laws). }
    destruct CC as [CC_data CC_laws ].
    destruct CC_data as [ [CC_tt_reindx CC_comp_1] CC_comp_2].
    destruct CC_tt_reindx as [ [C_ty C_tm] C_reindx].
    destruct C_ty as [ [C_ty C_q] C_ty_laws ].
    simpl in *.
    simpl. use total2_paths_f.
    simpl. use total2_paths_f.
    simpl. use total2_paths_f.
    simpl. use total2_paths_f.
    simpl. use total2_paths_f.
    - apply idpath.
    - apply isaprop_is_functor, (homset_property HSET).
    (* Hard to see how to do this from here.
       Probably needs some careful thought in the structuring + transport
     lemmas involved. *)
    - admit.
    - admit.
    - admit.
    - admit.
    Abort.

End fix_a_precategory.

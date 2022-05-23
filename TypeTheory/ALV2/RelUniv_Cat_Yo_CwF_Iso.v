(**
  [TypeTheory.ALV2.RelUniv_Cat_Yo_CwF_Iso]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**
An isomorphism between a (simple) category of CwF structures and
(simple) category of relative universe structures over the Yoneda embedding functor.

The proof is "too easy" since all the components are arranged in the same order.

Main definitions:
- [cwf_to_reluniv_functor] and [cwf_to_reluniv_is_catiso].

*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.CategoryTheory.
Require Import TypeTheory.Auxiliary.SetsAndPresheaves.

Require Import TypeTheory.CwF.CwF_def.
Require Import TypeTheory.ALV1.RelativeUniverses.
Require Import TypeTheory.ALV2.CwF_Cats_Simple.
Require Import TypeTheory.ALV2.RelUniv_Cat_Simple.
Require Import TypeTheory.ALV2.RelUniv_Cat.
Require Import UniMath.CategoryTheory.catiso.

Section Cat_Equiv.

  Context (C : category).

  Definition weq_cwf_reluniv_mor
             (X Y : cwf_structure C)
    : cwf_structure_mor X Y ≃
        relative_universe_mor _
        (weq_cwf_structure_RelUnivYo _ X)
        (weq_cwf_structure_RelUnivYo _ Y)
      := idweq _.

  (* CwF to CwF (simple) functor *)

  Definition cwf_to_reluniv_functor_data
    : functor_data (@cwf_structure_cat C)
                   (@reluniv_cat C _ Yo).
  Proof.
    use make_functor_data.
    - apply weq_cwf_structure_RelUnivYo.
    - intros X Y. apply weq_cwf_reluniv_mor.
  Defined.

  Definition cwf_to_reluniv_functor_idax
    : functor_idax cwf_to_reluniv_functor_data.
  Proof.
    intros c. 
    use total2_paths_f.
    + apply idpath.
    + apply homset_property.
  Defined.

  Definition cwf_to_reluniv_functor_compax
    : functor_compax cwf_to_reluniv_functor_data.
  Proof.
    intros a b c.
    intros f g.

    use total2_paths_f.
    + apply idpath.
    + apply homset_property.
  Defined.

  Definition cwf_to_reluniv_is_functor
    : is_functor cwf_to_reluniv_functor_data
    := (cwf_to_reluniv_functor_idax ,, cwf_to_reluniv_functor_compax).
  
  Definition cwf_to_reluniv_functor
    : functor (@cwf_structure_cat C)
              (@reluniv_cat C _ Yo).
  Proof.
    use (make_functor cwf_to_reluniv_functor_data).
    apply cwf_to_reluniv_is_functor.
  Defined.

  Definition cwf_to_reluniv_is_catiso : is_catiso cwf_to_reluniv_functor.
  Proof.
    use tpair.
    - unfold fully_faithful.
      intros X Y.
      apply (pr2 (weq_cwf_reluniv_mor _ _)).
    - apply (pr2 (weq_cwf_structure_RelUnivYo _)).
  Defined.

End Cat_Equiv.

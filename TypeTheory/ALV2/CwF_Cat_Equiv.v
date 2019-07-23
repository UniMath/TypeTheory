(**
  [TypeTheory.ALV1.CwF_Cats]
  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**
Contents:
- 
*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.CwF_def.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Defs.

Require Import TypeTheory.ALV2.CwF_Cats.
Require Import TypeTheory.ALV2.CwF_SplitTypeCat_Cats.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Equivalences.



Set Automatic Introduction.

Section CwF_Cat_Equiv.

  Context (C : category).

  (* Mapping of objects: cwf_structure → obj_ext_structure *)
  Definition cwf_structure_to_obj_ext_structure
             (X : cwf_structure C)
    : obj_ext_structure C.
  Proof.
    exists (TY X).
    intros Γ A.
    exists (cwf_extended_context X Γ A).
    apply cwf_projection.
  Defined.

  (* Mapping of objects: cwf_structure → term_fun_structure *)
  Definition cwf_structure_to_term_fun_structure
             (X : cwf_structure C)
    : ∑ (ext : obj_ext_structure C), term_fun_structure C ext.
  Proof.
    use tpair.
    - apply (cwf_structure_to_obj_ext_structure X).
    - cbn. unfold term_fun_structure.
      use tpair.
      + unfold term_fun_structure_data. cbn.
        exists (TM X).
        use make_dirprod.
        * exact (pr2 (pr1 X)).
        * intros Γ A.
          apply cwf_extended_context_term.
      + unfold term_fun_structure_axioms. cbn.
        intros Γ A.
        set (ΓAπ := pr1 (pr2 X Γ A)).
        set (te := pr1 (pr2 (pr2 X Γ A))).
        set (pullback := pr2 (pr2 (pr2 X Γ A))).
        exists (pr2 te).
        exact pullback.
  Defined.

  (* Mapping of morphisms: cwf_structure_mor → obj_ext_mor *)
  Definition cwf_structure_mor_to_obj_ext_mor
             (X Y : cwf_structure C)
             (f : cwf_structure_mor X Y)
    : obj_ext_mor
        (pr1 (cwf_structure_to_term_fun_structure X))
        (pr1 (cwf_structure_to_term_fun_structure Y)).
  Proof.
    unfold obj_ext_mor.
    destruct f as [[F_TM [F_TY ϕ]] f_is_cwf_structure_mor].
    exists F_TY.
    intros Γ A.
    exists (ϕ Γ A).
    exact (pr1 f_is_cwf_structure_mor Γ A).
  Defined.

  (* Mapping of morphisms: cwf_structure_mor → term_fun_structure_mor *)
  Definition cwf_structure_mor_to_term_fun_structure_mor
             (X Y : cwf_structure C)
             (f : cwf_structure_mor X Y)
    : ∑ (ext : obj_ext_mor
                 (cwf_structure_to_obj_ext_structure X)
                 (cwf_structure_to_obj_ext_structure Y)
        ), term_fun_mor
             (pr2 (cwf_structure_to_term_fun_structure X))
             (pr2 (cwf_structure_to_term_fun_structure Y))
             ext.
  Proof.
    exists (cwf_structure_mor_to_obj_ext_mor _ _ f).
    unfold term_fun_mor.
    destruct f as [[F_TM [F_TY ϕ]] [axiom1 [axiom2 axiom3]]].
    exists F_TM.
    exists axiom2.
    exact axiom3.
  Defined.

  Definition cwf_structure_to_term_fun_structure_functor_data
    : functor_data
        (@cwf_structure_precat C)
        (term_fun_structure_precat C).
  Proof.
    exists cwf_structure_to_term_fun_structure.
    intros X Y f.
    apply (cwf_structure_mor_to_term_fun_structure_mor _ _ f).
  Defined.
 
  Definition cwf_structure_mor_to_term_fun_structure_is_functor
    : is_functor cwf_structure_to_term_fun_structure_functor_data.
  Proof.
    use make_dirprod.
    - unfold functor_idax.
      intros X.
      use total2_paths_f.
      + simpl. use obj_ext_mor_eq.
        * intros Γ A. apply idpath.
        * intros Γ A. cbn. apply id_left.
      + apply term_fun_mor_eq.
        intros Γ t.
        (* STUCK here: too much transportf *)
        apply term_fun_mor_transportf.
  Defined.

  Definition cwf_structure_to_term_struc_functor
  : functor
      (@cwf_structure_precat C) (* Why C is implicit? *)
      (term_fun_structure_precat C).
  Proof.
    exists cwf_structure_to_term_fun_structure_functor_data.
  Defined.

End CwF_Cat_Equiv.

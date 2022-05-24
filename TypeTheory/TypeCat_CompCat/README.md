Package *TypeCat_CompCat*
===================================================

Authors: Benedikt Ahrens, Peter LeFanu Lumsdaine, Vladimir Voevodsky

Contents
--------

The files of this package provide:

- [CwF_SplitTypeCat_Cats.v](CwF_SplitTypeCat_Cats.v)

  - Definition of displayed categories of term structures and *q*-morphism structures; and of CwF’s and split type-categories, as defined via these.

    Main definitions:

    - `obj_ext_cat`
    - `term_fun_disp_cat`, `cwf'n_structure_precat`
    - `qq_structure_disp_cat`, `sty'_structure_precat`

- [CwF_SplitTypeCat_Equiv_Cats.v](CwF_SplitTypeCat_Equiv_Cats.v)

  - Construction of an equivalence of displayed categories between term structures and *q*-morphism structures.

- [CwF_SplitTypeCat_Univalent_Cats.v](CwF_SplitTypeCat_Univalent_Cats.v)

  - Proof that the above displayed categories are univalent.

- [CwF_SplitTypeCat_Equiv_Comparison.v](CwF_SplitTypeCat_Equiv_Comparison.v)

  - Comparison of the two equivalences constructed between the types of term structures
    and _q_-morphism structures over a given object-extension structure:

    - one given directly, in [`TypeTheory.CwF_TypeCat.CwF_SplitTypeCat_Equivalence`](/TypeTheory/CwF_TypeCat.CwF_SplitTypeCat_Equivalence.v);
    - one deduced from an equivalence of categories, in [`CwF_SplitTypeCat_Equiv_Cats`](CwF_SplitTypeCat_Equiv_Cats.v)

    Main result: [`compare_term_qq_equivs`][compare_term_qq_equivs].

TypeTheory: the mathematical study of type theories, in univalent foundations
==========

Code  on C-systems, D-systems, categories with families, comprehension categories, saturation, and the like.

Compilation
------------

### Prerequisites

The Coq code depends on the UniMath library, available from http://github.com/UniMath/UniMath.
To compile UniMath, follow the installation instructions given there.
Afterwards, make sure to install UniMath and to add the underlying Coq binaries to your path, by calling, from within the UniMath toplevel directory,
```
$ make install 
$ PATH=$PATH:`pwd`/sub/coq/bin/
```
The second step can be made persistent by modifying your shell configuration file.

### Compilation of UniMath/TypeTheory

If you have UniMath’s Coq in your path (as per the above extension of PATH), then our library can be built just with `make` from within the toplevel directory.

Otherwise, you need to pass the location of the UniMath `coqc` binary by hand, as e.g. `make COQBIN="~/src/UniMath/sub/coq/bin/"`.

Similarly, to use these files in Proof General, you must make sure the correct `coqtop` is called.  This may be either permanently set in the option `coq-prog-name`, or prompted for at each invocation by setting `proof-prog-name-ask`.

Contents
--------

The contents of this library are split into several "packages" (subdirectories).
We give an overview of the packages and refer to each package's README for details.

* *Auxiliary/*
  * General background definitions and results that might be upstreamed into UniMath/UniMath
  * Notations for the library
* *Categories/*
  * Background constructions and results on categories; might be upstreamed to UniMath/CategoryTheory
* *ALV1/*
  * Definition of CwF’s (a la Fiore) and Split Type-Categories
  * Construction of an equivalence of types between families structures and split type structures
  * Construction of an equivalence of categories between families structures and split type structures
  * Definition of relative universe structures
  * Construction of an equivalence between families structures and relative universe structures on Yoneda
  * Construction of a function from families structures on a category to families structures on its Rezk completion
* *Displayed_Cats/*
  * Library on displayed categories: a toolbox for constructing and working with categories of multi-component structures
* *ALV2/*
  * Construction of equivalences of categories between families structures and split type structures, using
    displayed categories
* *OtherDefs/*
  * Various other categorical structures used in the study of type theory
  * WARNING: many files in this subdirectory are in a very rough state; use at your own risk.

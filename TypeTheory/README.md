Mathematics of type theory in univalent foundations
===================================================


Installation
------------

Requires installed [UniMath](https://github.com/UniMath/UniMath/).
Make sure to use 
```
$ make install
```
on UniMath, and to have the directory `UniMath/sub/coq/bin` in your PATH.


Contents
--------

The contents of this library are split into several "packages" (subdirectories).
We give an overview of the packages and refer to each package's README for details.

* *Auxiliary/*
  * Some complementary definitions and results that might be upstreamed into UniMath/UniMath
  * Some notations
* *Categories/*
  * Definition of some categories that might be of use
* *ALV1/*
  * Construction of an equivalence of types between families structures and split type structures
  * Definition of relative universe structures
  * Construction of an equivalence between families structures and relative universe structures on Yoneda
  * Construction of a function from families structures on a category to families structures on its Rezk completion
* *Displayed_Cats/*
  * Theory of displayed categories
* *ALV2/*
  * Construction of an equivalence of categories between families structures and split type structures using
    displayed categories
* *OtherDefs/*
  * Some categorical structures used in the study of type theory


TypeTheory: the mathematical study of type theories, in univalent foundations
==========

Code  on C-systems, D-systems, categories with families, comprehension categories, saturation, and the like.

Compilation
------------

### Prerequisites

The Coq code depends on the UniMath library, available from http://github.com/UniMath/UniMath.
To compile UniMath, follow the installation instructions given there.

You will also need to make UniMath’s coq binaries available for compiling this library.  The simplest way is to install them as the default Coq on your system, by calling, from within the UniMath toplevel directory,
```
$ make install 
```
and then adding them to your `$PATH`, either temporarily by running
```
$ PATH=$PATH:`pwd`/sub/coq/bin/
```
or permanently by modifying your shell configuration file (usually `~/.bash_profile` or similar):
```
echo "export PATH=\"`pwd`/sub/coq/bin/:\$PATH\"" >> ~/.bash_profile
```

Alternatively, if you do not want to make UniMath’s Coq your default, you can add an alias for its directory to your shell config file by calling (from within the UniMath toplevel directory)
```
echo "export UNIBIN=\"`pwd`/sub/coq/bin/\"" >> ~/.bash_profile
```
and then give the option `COQBIN=$UNIBIN` when compiling this library.

### Compilation of UniMath/TypeTheory

If you have UniMath’s Coq in your path (as per the first suggestion above), then our library can be built just with `make` from within the toplevel directory.

Otherwise, you need to pass the location of the UniMath `coqc` binary by hand, as e.g. `make COQBIN="~/src/UniMath/sub/coq/bin/"` or `make COQBIN=$UNIBIN`.

Similarly, to use these files in Proof General, you must make sure the correct `coqtop` is called.  This may be either permanently set in the option `coq-prog-name`, or prompted for at each invocation by setting `proof-prog-name-ask`.

Contents
--------

The contents of this library are split into several "packages" (subdirectories).
We give an overview of the packages and refer to each package's README for details.

NOTE: this table of contents is not automatically updated, and may often be out of sync with the development.

- *Auxiliary/*
  - General background definitions and results, that could be upstreamed into UniMath/UniMath
- *RelUniv/*
  - Definition and basic development of *relative universe structures*
- *CompCats/*
  - Basic development of *comprehension categories* (though UniMath itself contains the basic definition)
- *TypeCat/*
  - Definition and basic development of *type-categories*, including splitness, the (2-)category of type-categories, and extra logical structure on them
- *CwF/*
  - Definition and basic development of *categories with families*, using the Fiore–Aowdey approach with representable (more precisely, *represented*) maps
  - An equivalence between families structures and relative universe structures on Yoneda
  - Construction of a function from families structures on a category to families structures on its Rezk completion
- *CwF_TypeCat/*
  - Comparisons between CwF’s and split type-categories; specifically:
    - equivalence of types between families structures and split type structures, as presented in Ahrens–Lumsdaine–Voevodsky 2017
	- equivalence of categories between families structures and split type structures
- *OtherDefs/*
  - Various other categorical structures used in the study of type theory, not yet developed here enough to warrant separate packages
- *Categories/*
  - Background constructions and results on categories; might be upstreamed to UniMath/CategoryTheory
- *Instances/*
  - concrete examples of the categorical structures considered
  - so far, only the result that presheaves form a type-category
- *Csystems/*
  * the implementation of Vladimir Voevodsky's notion of C system
- *Bsystems/*
  * the implementation of Vladimir Voevodsky's notion of B system
- *Cubical/*
  - To be documented
- *Initiality/*
  - the interpretation from the syntax of a small type theory into suitably-structured CwA’s
  - (incomplete) the syntactic CwA of the type theory, and its initiality
- *TypeConstructions/*
  - To be documented
- *Articles/*
  - files corresponding to articles whose content is formalised here, linking results named in the articles to their formalisation in this development

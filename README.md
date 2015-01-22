ahrens-lumsdaine-voevodsky
==========================

Paper on C-systems, D-systems, categories with families, comprehension categories, saturation, and the like.

## Usage of the Coq code

The Coq code depends on the UniMath library, available from http://github.com/UniMath/UniMath.

If you have UniMath’s coq installed globally, then our library can be built just with `make` from within the `coq` subdirectory.

Otherwise, you need to pass the location of the UniMath `coqc` binary by hand, as e.g. `make COQC="~/src/UniMath/sub/coq/bib/coqc"`.

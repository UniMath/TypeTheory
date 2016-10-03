TypeTheory
==========

Mathematics of type theory, formalized on top of [UniMath](https://github.com/UniMath/UniMath)

Code on C-systems, D-systems, categories with families, comprehension categories, saturation, and the like.

## Usage of the Coq code

The Coq code depends on the UniMath library, available from http://github.com/UniMath/UniMath.

If you have UniMath’s coq installed globally, then our library can be built just with `make` from within the toplevel directory.

Otherwise, you need to pass the location of the UniMath `coqc` binary by hand, as e.g. `make COQBIN="~/src/UniMath/sub/coq/bin/"`.

Similarly, to use these files in Proof General, you must make sure the correct `coqtop` is called.  This may be either permanently set in the option `coq-prog-name`, or prompted for at each invocation by setting `proof-prog-name-ask`.

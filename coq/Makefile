# X-systems project makefile.
# Benedikt Ahrens, Vladimir Voevodsky, Peter LeFanu Lumsdaine, Oct 2014 onwards.

# Quick usage: “make” to build core of library, “make all” to build all files.
# If you do not have Unimath installed globally, then invoke as e.g.
# make COQC="~/src/UniMath/sub/coq/bib/coqc"
# (or wherever you keep your UniMath coq).

# Modules to be compiled by default, in plain “make”.
# Includes everything that compiles in reasonable time, and all dependencies.
MODULES-CORE := Auxiliary UnicodeNotations \
	CompCats cwf CwF_to_CompCat \
	ess_alg_categories ess_and_gen_alg_cats

# Remaining modules, included only in “make all”.
# Useful for leaves that are slow to recompile.
MODULES-EXTRA := 

VS-CORE  := $(MODULES-CORE:%=%.v)
VS-EXTRA := $(MODULES-EXTRA:%=%.v)

COQDOC := coqdoc

.PHONY: core all clean

core: Makefile.coq
	$(MAKE) -f Makefile.coq 

all: Makefile_all.coq
	$(MAKE) -f Makefile_all.coq 

Makefile.coq: Makefile $(VS-CORE)
	coq_makefile -R . "Systems" $(VS-CORE) -o Makefile.coq

Makefile_all.coq: Makefile $(VS-CORE) $(VS-EXTRA)
	coq_makefile -R . "Systems" $(VS-CORE) $(VS-EXTRA) -o Makefile_all.coq

clean:: Makefile_all.coq
	$(MAKE) -f Makefile_all.coq clean
	rm -f Makefile_all.coq
	rm -f html

html: all
	mkdir -p html
	$(COQDOC) -toc $(COQDOCFLAGS) -utf8 -html $(COQDOCLIBS) -d html $(VS-CORE) $(VS-EXTRA)
	
# Makefile based on example from Adam Chlipala, “Theorem Proving in the Large”,
# section “Build Patterns”. http://adam.chlipala.net/cpdt/html/Large.html

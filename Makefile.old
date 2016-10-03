# X-systems project makefile.
# Benedikt Ahrens, Vladimir Voevodsky, Peter LeFanu Lumsdaine, Oct 2014 onwards.

# Quick usage: “make” to build core of library, “make all” to build all files.
# If you do not have Unimath installed globally, then invoke as e.g.
#   make COQBIN="~/src/UniMath/sub/coq/bin/"
# (or wherever you keep your UniMath coq).  It can be convenient to have an
# environment variable $UNIBIN exported by your shell profile, and then call
#   make COQBIN=$UNIBIN

# Modules to be compiled by default, in plain “make”.
# Includes everything that compiles in reasonable time, and all dependencies.


MODULES-CORE := \
	Auxiliary \
	UnicodeNotations \
	Displayed_Cats/Auxiliary \
	Displayed_Cats/Core \
	Displayed_Cats/Constructions \
	Displayed_Cats/Equivalences \
	Displayed_Cats/Examples \
	Structures \
	CwF_SplitTypeCat_Maps \
	CwF_SplitTypeCat_Equivalence \
	Structures_Cats \
	Structures_Equiv_Cats \
	Structures_Univalent_Cats \
	Structures_Equiv_Types \
	RelUnivStructure \
	CwF_RelUnivYoneda \
	RelUnivYonedaCompletion \
	Bicats/Bicats \
	Bicats/Displayed_Bicats \
	Categories/category_of_elements \
	Categories/category_FAM \
	OtherDefs/CwF_Pitts \
	OtherDefs/TypeCat \
	OtherDefs/DM \
	OtherDefs/CwF_Pitts_to_TypeCat \
	OtherDefs/TypeCat_to_CwF_Pitts \
	OtherDefs/DM_to_TypeCat \
	OtherDefs/CwF_Pitts_to_DM \
	OtherDefs/TypeCat_to_DM \
	OtherDefs/CwF_Pitts_to_TypeCat_to_DM \
	OtherDefs/CwF_1 \
	EquivCats_Q_q

MODULES-BICATS := \
	Bicats/Bicats \
	Bicats/Displayed_Bicats

MODULES-UNIVALENT := \
	Auxiliary \
	UnicodeNotations \
	Structures \
	CwF_SplitTypeCat_Maps \
	CwF_SplitTypeCat_Equivalence \
	EquivCats_Q_q

MODULES-RELUNIV := \
	Auxiliary \
	RelUnivStructure \
	CwF_RelUnivYoneda \
	RelUnivYonedaCompletion

# Remaining modules, included only in “make all”.
# Useful for leaves that are slow to recompile.
MODULES-EXTRA := \
	OtherDefs/CwF_Pitts_completion \
	OtherDefs/DM_to_TypeCat_to_DM \
	Test

# Modules that have gone out-of-date with upstream changes,
# and don’t currently compile.
MODULES-ROTTEN := \
	OtherDefs/DM_truncated \
	OtherDefs/CwF_Pitts_to_CwF_1 \
	OtherDefs/CwF_Dybjer \
	OtherDefs/CwF_Pitts_natural \

VS-CORE  := $(MODULES-CORE:%=%.v)
VS-EXTRA := $(MODULES-EXTRA:%=%.v)
VS-UNIVALENT := $(MODULES-UNIVALENT:%=%.v)
VS-RELUNIV := $(MODULES-RELUNIV:%=%.v)
VS-ALV1 := $(VS-UNIVALENT) $(VS-RELUNIV)

COQBIN ?= 
COQDOC ?= $(COQBIN)coqdoc
COQMAKEFILE ?= $(COQBIN)coq_makefile

COQOPTIONS := -type-in-type

.PHONY: core all clean

core: Makefile.coq
	$(MAKE) -f Makefile.coq 

all: Makefile_all.coq
	$(MAKE) -f Makefile_all.coq 

univalent: Makefile_univalent.coq
	$(MAKE) -f Makefile_univalent.coq

alv1: $(VS-RELUNIV) $(VS-UNIVALENT)
	$(COQMAKEFILE) -R . "Systems" $(VS-RELUNIV) $(VS-UNIVALENT) Test.v -arg $(COQOPTIONS) -o Makefile_alv1.coq
	$(MAKE) -f Makefile_alv1.coq

coqwc-alv1:  ## counts Auxiliary twice, hence delivers wrong result
	coqwc $(VS-ALV1) 

coqwc-all:
	coqwc $(VS-CORE) $(VS-EXTRA)

Makefile.coq: Makefile $(VS-CORE)
	$(COQMAKEFILE) -R . "Systems" $(VS-CORE) -arg $(COQOPTIONS) -o Makefile.coq

Makefile_all.coq: Makefile $(VS-CORE) $(VS-EXTRA)
	$(COQMAKEFILE) -R . "Systems" $(VS-CORE) $(VS-EXTRA) -arg $(COQOPTIONS) -o Makefile_all.coq

Makefile_univalent.coq: Makefile $(VS-UNIVALENT)
	$(COQMAKEFILE) -R . "Systems" $(VS-UNIVALENT) -arg $(COQOPTIONS) -o Makefile_univalent.coq

coqwc-univ:
	coqwc $(VS-UNIVALENT)

install: all
	$(MAKE) -f Makefile_all.coq install

install_core: core
	$(MAKE) -f Makefile.coq install

clean:: Makefile_all.coq
	$(MAKE) -f Makefile_all.coq clean
	rm -f Makefile_all.coq
	rm -f html

html: all
	mkdir -p html
	$(COQDOC) -R . "Systems" -toc -interpolate $(COQDOCFLAGS) -utf8 -html $(COQDOCLIBS) -d html $(VS-CORE) $(VS-EXTRA)

html_core: core
	mkdir -p html
	$(COQDOC) -R . "Systems" -toc -interpolate $(COQDOCFLAGS) -utf8 -html $(COQDOCLIBS) -d html $(VS-CORE)

# Makefile based on example from Adam Chlipala, “Theorem Proving in the Large”,
# section “Build Patterns”. http://adam.chlipala.net/cpdt/html/Large.html

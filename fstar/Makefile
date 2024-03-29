.PHONY: verify-all basic_clean test test.kremlin test.ocaml
################################################################################
# Customize these variables for your project
################################################################################
FSTAR ?= $(FSTAR_HOME)/bin/fstar.exe --z3rlimit_factor 32

# The root files of your project, from which to begin scanning dependences
FSTAR_FILES ?= Hpke.fst

# The paths to related files which to include for scanning
#   -- No need to add FSTAR_HOME/ulib; it is included by default
INCLUDE_PATHS ?= $(HACL_HOME)/lib

# The executable file you want to produce
PROGRAM ?= specs.exe

# A driver in ML to call into your program
TOP_LEVEL_FILE ?=

# A place to put all the emitted .ml files
OUTPUT_DIRECTORY ?= _output

################################################################################
MY_FSTAR=$(FSTAR) \
	--cache_checked_modules $(addprefix --include , $(INCLUDE_PATHS)) \
	--odir $(OUTPUT_DIRECTORY)
ML_FILES=$(addprefix $(OUTPUT_DIRECTORY)/,$(addsuffix .ml,$(subst .,_, $(subst .fst,,$(FSTAR_FILES)))))
OCAML_EXE=$(PROGRAM).ocaml.exe
KREMLIN_EXE=$(PROGRAM).exe

# a.fst.checked is the binary, checked version of a.fst
%.fst.checked: %.fst
	$(MY_FSTAR) $*.fst
	touch -c $@

# a.fsti.checked is the binary, checked version of a.fsti
%.fsti.checked: %.fsti
	$(MY_FSTAR) $*.fsti
	touch -c $@

%.fst.checked.lax: %.fst
	$(MY_FSTAR) --lax $*.fst
	touch -c $@

# The _tags file is a directive to ocamlbuild
# The extracted ML files are precious, because you may want to examine them,
#     e.g., to see how type signatures were transformed from F*
.PRECIOUS: _tags $(ML_FILES) $(addsuffix .checked,$(FSTAR_FILES)) $(OUTPUT_DIRECTORY)/out.krml

_tags:
	echo "<ml>: traverse" > $@
	echo "<$(OUTPUT_DIRECTORY)>: traverse\n" >> $@
	echo "<$(OUTPUT_DIRECTORY)/c>: -traverse\n" >> $@

# To extract an A.ml ML file from an A.fst, we just reload its A.fst.checked file
# and then with the --codegen OCaml option, emit an A.ml
# Note, by default F* will extract all files in the dependency graph
# With the --extract_module, we instruct it to just extract A.ml
$(OUTPUT_DIRECTORY)/%.ml:
	$(MY_FSTAR) $(subst .checked,,$<) --codegen OCaml --extract_module $(subst .fst.checked,,$<)

$(OCAML_EXE): _tags $(ML_FILES) $(TOP_LEVEL_FILE) $(FSTAR_HOME)/bin/fstarlib/fstarlib.cmxa
	OCAMLPATH="$(FSTAR_HOME)/bin" ocamlbuild -I $(OUTPUT_DIRECTORY) -use-ocamlfind -pkg fstarlib $(subst .ml,.native,$(TOP_LEVEL_FILE))
	mv _build/$(subst .ml,.native,$(TOP_LEVEL_FILE)) $@

test.ocaml: $(OCAML_EXE)
	./$< hello

$(OUTPUT_DIRECTORY)/c/out.krml: $(addsuffix .checked,$(FSTAR_FILES))
	krml -fsopts --cache_checked_modules -tmpdir $(OUTPUT_DIRECTORY)/c -skip-translation $(FSTAR_FILES)

$(KREMLIN_EXE): $(OUTPUT_DIRECTORY)/c/out.krml
	krml $< -tmpdir $(OUTPUT_DIRECTORY)/c -no-prefix A -o $@

test.kremlin: $(KREMLIN_EXE)
	./$< hello

test: test.kremlin test.ocaml

$(FSTAR_HOME)/bin/fstarlib/fstarlib.cmxa:
	+$(MAKE) -C $(FSTAR_HOME)/ulib/ml

basic_clean:
	rm -rf _build $(OUTPUT_DIRECTORY) *~ *.checked $(OCAML_EXE) $(KREMLIN_EXE) .depend

.depend: $(FSTAR_FILES)
	$(MY_FSTAR) --dep full $(addprefix --include , $(INCLUDE_PATHS)) $(FSTAR_FILES) > .depend

depend: .depend

include .depend

# The default target is to verify all files, without extracting anything
# It needs to be here, because it reads the variable ALL_FST_FILES in .depend
verify-all: $(addsuffix .checked, $(ALL_FST_FILES))

lax-all: $(addsuffix .checked.lax, $(ALL_FST_FILES))

%.fst-in %.fsti-in:
	@echo --cache_checked_modules $(addprefix --include , $(INCLUDE_PATHS))

%.fst-formatted: %.fst
	$(FSTAR) --print_in_place $*.fst

format: $(subst .fst,.fst-formatted,$(FSTAR_FILES))

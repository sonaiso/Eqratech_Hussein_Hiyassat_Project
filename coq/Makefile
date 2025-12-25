# Makefile for Arabic Kernel Coq Formalization

# Coq compiler
COQC = coqc
COQDEP = coqdep
COQ_MAKEFILE = coq_makefile

# Directories
THEORIES_DIR = theories/ArabicKernel

# Source files
VFILES = $(THEORIES_DIR)/FractalCore.v \
         $(THEORIES_DIR)/Roles.v \
         $(THEORIES_DIR)/SlotsTable.v \
         $(THEORIES_DIR)/All.v

# Build using coq_makefile
.PHONY: all clean

all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject $(VFILES)
	$(COQ_MAKEFILE) -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf

# Alternative: direct compilation
.PHONY: direct
direct:
	$(COQC) -Q theories ArabicKernel $(THEORIES_DIR)/FractalCore.v
	$(COQC) -Q theories ArabicKernel $(THEORIES_DIR)/Roles.v
	$(COQC) -Q theories ArabicKernel $(THEORIES_DIR)/SlotsTable.v
	$(COQC) -Q theories ArabicKernel $(THEORIES_DIR)/All.v

# Help
.PHONY: help
help:
	@echo "Available targets:"
	@echo "  all     - Build all Coq files using coq_makefile"
	@echo "  direct  - Build Coq files directly with coqc"
	@echo "  clean   - Remove build artifacts"
	@echo "  help    - Show this help message"

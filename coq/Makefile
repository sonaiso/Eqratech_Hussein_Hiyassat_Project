# FractalHub Coq Formalization Makefile

.PHONY: all clean theories extraction ocaml-build ocaml-test python-test verify help

# Default target
all: theories

# Build all theories
theories:
	@echo "Building Coq theories..."
	coq_makefile -f _CoqProject -o Makefile.coq
	$(MAKE) -f Makefile.coq

# Extract to OCaml
extraction: theories
	@echo "Extracting to OCaml..."
	coqc -R theories FractalHub theories/Extraction.v
	@echo "Extracted code available in fractalhub_kernel.ml"
	@echo "Building OCaml project..."
	cd extraction && dune build

# Build OCaml extracted code
ocaml-build: extraction
	@echo "OCaml build complete"

# Test OCaml extracted code
ocaml-test: ocaml-build
	@echo "Running OCaml test suite..."
	cd extraction && dune exec ./test_extraction.exe

# Test Python integration
python-test: ocaml-build
	@echo "Running Python integration tests..."
	cd .. && pytest tests/test_verified_bridge.py -v

# Full verification chain: Coq → OCaml → Python → Tests
verify-full: theories ocaml-test python-test
	@echo "========================================="
	@echo "✅ Full verification chain complete!"
	@echo "   Coq proofs ✓"
	@echo "   OCaml extraction ✓"
	@echo "   Python integration ✓"
	@echo "========================================="

# Clean build artifacts
clean:
	@echo "Cleaning..."
	-$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf
	rm -f theories/*.vo theories/*.vok theories/*.vos theories/*.glob theories/*.aux
	rm -f *.ml *.mli
	rm -f .*.aux
	cd extraction && dune clean

# Verify all proofs
verify: theories
	@echo "All proofs verified ✓"

# Help
help:
	@echo "FractalHub Coq Formalization"
	@echo ""
	@echo "Targets:"
	@echo "  all          - Build all Coq theories (default)"
	@echo "  theories     - Build all Coq theories"
	@echo "  extraction   - Extract to OCaml and build"
	@echo "  ocaml-build  - Build OCaml extracted code"
	@echo "  ocaml-test   - Run OCaml test suite"
	@echo "  python-test  - Run Python integration tests"
	@echo "  verify-full  - Full verification chain (Coq → OCaml → Python)"
	@echo "  verify       - Verify all proofs"
	@echo "  clean        - Remove build artifacts"
	@echo "  help         - Show this help"

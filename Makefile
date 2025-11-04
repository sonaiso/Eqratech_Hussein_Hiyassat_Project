SHELL := /bin/bash

VENV ?= .venv
TRAIN_CONFIG ?= configs/transformer_quran_colab.yaml

ifeq ($(OS),Windows_NT)
	PYTHON ?= py -3
	VENV_BIN := $(VENV)/Scripts
else
	PYTHON ?= python3
	VENV_BIN := $(VENV)/bin
endif

PIP := $(VENV_BIN)/pip
PY := $(VENV_BIN)/python
PYTEST := $(VENV_BIN)/pytest
RUFF := $(VENV_BIN)/ruff

.PHONY: help install lint test reveng train clean distclean

help:
	@printf "Available targets:\n"
	@printf "  make install   # create $(VENV) and install requirements-dev\n"
	@printf "  make lint      # run ruff static analysis\n"
	@printf "  make test      # execute pytest suite\n"
	@printf "  make reveng    # rebuild Excel export via Main_engine.py\n"
	@printf "  make train     # launch transformer fine-tuning (configurable)\n"
	@printf "  make clean     # remove __pycache__ artifacts\n"
	@printf "  make distclean # clean + remove $(VENV)\n"

$(VENV):
	$(PYTHON) -m venv $(VENV)

install: $(VENV)
	$(PIP) install --upgrade pip
	$(PIP) install -r requirements-dev.txt

lint: $(VENV)
	@if [ ! -x "$(RUFF)" ]; then \
		echo "ruff not installed in $(VENV); run 'make install'"; \
		exit 1; \
	fi
	$(RUFF) check .

test: $(VENV)
	@if [ ! -x "$(PYTEST)" ]; then \
		echo "pytest not installed in $(VENV); run 'make install'"; \
		exit 1; \
	fi
	$(PYTEST)

reveng: $(VENV)
	@if [ ! -x "$(PY)" ]; then \
		echo "Python binary missing from $(VENV); run 'make install'"; \
		exit 1; \
	fi
	$(PY) Main_engine.py

train: $(VENV)
	@if [ ! -x "$(PY)" ]; then \
		echo "Python binary missing from $(VENV); run 'make install'"; \
		exit 1; \
	fi
	@if [ ! -f "$(TRAIN_CONFIG)" ]; then \
		echo "TRAIN_CONFIG not found: $(TRAIN_CONFIG)"; \
		echo "Set TRAIN_CONFIG=/path/to/config.yaml before running make train"; \
		exit 1; \
	fi
	$(PY) scripts/train_transformer_quran.py --config "$(TRAIN_CONFIG)"

clean:
	$(PYTHON) -c "import os, shutil; \
for root, dirs, files in os.walk('.', topdown=False): \
	for name in files: \
		if name.endswith('.pyc'): \
			try: \
				os.remove(os.path.join(root, name)) \
			except FileNotFoundError: \
				pass; \
	for name in dirs: \
		if name == '__pycache__': \
			shutil.rmtree(os.path.join(root, name), ignore_errors=True)"

distclean: clean
	rm -rf $(VENV)

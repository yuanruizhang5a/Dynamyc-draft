# SPDX-License-Identifier: GPL-3.0-only
# Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root.
.DEFAULT_GOAL := all
PDFLATEX ?= pdflatex
LATEXMK ?= latexmk
PYTHON ?= python3
SOURCES := $(wildcard *.tex *.sty)
FLAGS := -interaction=nonstopmode -halt-on-error -file-line-error -no-shell-escape

.PHONY: all check refresh check-rocq latexmk loop
all: check asm.pdf

check:
	$(PYTHON) check_manual.py

# Refresh only after reviewing the code and evidence against the manual.
refresh:
	$(PYTHON) check_manual.py --refresh

asm.pdf: $(SOURCES) sources.json
	mkdir -p build
	$(PDFLATEX) $(FLAGS) -output-directory=build asm.tex > build/compile.log 2>&1 || { tail -60 build/compile.log; exit 1; }
	$(PDFLATEX) $(FLAGS) -output-directory=build asm.tex >> build/compile.log 2>&1 || { tail -60 build/compile.log; exit 1; }
	$(PDFLATEX) $(FLAGS) -output-directory=build asm.tex >> build/compile.log 2>&1 || { tail -60 build/compile.log; exit 1; }
	cp build/asm.pdf asm.pdf
	@echo "Built asm.pdf; compiler output is in build/compile.log"

# Optional multi-pass engine, with all bookkeeping retained in build/.
latexmk: check
	mkdir -p build
	$(LATEXMK) -pdf -outdir=build -pdflatex='$(PDFLATEX) $(FLAGS) %O %S' asm.tex > build/latexmk.log 2>&1 || { tail -60 build/latexmk.log; exit 1; }
	cp build/asm.pdf asm.pdf

loop: check
	$(LATEXMK) -pdf -pvc -outdir=build -pdflatex='$(PDFLATEX) $(FLAGS) %O %S' asm.tex

check-rocq:
	$(MAKE) -C ../../.. lpl-asm-common
	mkdir -p build
	timeout --signal=KILL 600s rocq compile -Q ../../.. CyclistRocq quickstart.v > build/quickstart.log 2>&1 || { cat build/quickstart.log; exit 1; }
	@echo "Quickstart compiled; Rocq output is in build/quickstart.log"

# Deliberately no deleting clean target: project policy preserves files.

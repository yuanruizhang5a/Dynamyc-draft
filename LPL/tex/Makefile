# SPDX-License-Identifier: GPL-3.0-only
# Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root.
.DEFAULT_GOAL := all
PDFLATEX ?= pdflatex
PYTHON ?= python3
SOURCES := $(wildcard *.tex *.sty)
FLAGS := -interaction=nonstopmode -halt-on-error -file-line-error -no-shell-escape

.PHONY: all check refresh loop
all: check lpl.pdf

check:
	$(PYTHON) check_manual.py

# Refresh only after reviewing changes in the theory against the manual.
refresh:
	$(PYTHON) check_manual.py --refresh

lpl.pdf: $(SOURCES) sources.json
	mkdir -p build
	$(PDFLATEX) $(FLAGS) -output-directory=build lpl.tex > build/compile.log 2>&1 || { tail -60 build/compile.log; exit 1; }
	$(PDFLATEX) $(FLAGS) -output-directory=build lpl.tex >> build/compile.log 2>&1 || { tail -60 build/compile.log; exit 1; }
	$(PDFLATEX) $(FLAGS) -output-directory=build lpl.tex >> build/compile.log 2>&1 || { tail -60 build/compile.log; exit 1; }
	cp build/lpl.pdf lpl.pdf
	@echo "Built lpl.pdf; compiler output is in build/compile.log"

# Optional Iris-style continuous preview if latexmk is installed.
loop: check
	latexmk -pdf -pvc -pdflatex='$(PDFLATEX) %O %S' lpl.tex

# Deliberately no deleting clean target: project policy preserves files.

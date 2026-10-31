# SPDX-License-Identifier: GPL-3.0-only
.DEFAULT_GOAL := all
ROCQ ?= rocq
SOURCES := $(shell find Cyclic LPL -name '*.v')
CORE := $(wildcard Cyclic/*.v LPL/*.v)
ASM := $(wildcard LPL/ASM/*.v LPL/ASM/Cases/*.v)
.PHONY: all proofs manuals lpl lpl-common lpl-asm lpl-asm-common lpl-asm-unfold-common lpl-asm-unfold lpl-benchmarks lpl-asm-benchmarks lpl-asm-unfold-benchmarks kernel-check
all: proofs manuals
Makefile.rocq: _CoqProject
	$(ROCQ) makefile -f _CoqProject -o $@
proofs: Makefile.rocq
	$(MAKE) -f Makefile.rocq all
lpl: proofs
lpl-common: Makefile.rocq
	$(MAKE) -f Makefile.rocq $(CORE:.v=.vo)
lpl-asm-common lpl-asm-unfold-common: Makefile.rocq
	$(MAKE) -f Makefile.rocq $(CORE:.v=.vo) $(ASM:.v=.vo) LPL/ASM/Benchmarks/Support.vo
lpl-asm lpl-asm-unfold: proofs
manuals:
	$(MAKE) -C LPL/tex
	$(MAKE) -C LPL/ASM/tex
lpl-benchmarks:
	python3 LPL/run_benchmarks.py
lpl-asm-benchmarks lpl-asm-unfold-benchmarks:
	python3 LPL/ASM/run_unfold_benchmarks.py --kernel-check
kernel-check: proofs
	$(ROCQ) check -Q . CyclistRocq $(patsubst %.v,CyclistRocq.%,$(subst /,.,$(SOURCES)))

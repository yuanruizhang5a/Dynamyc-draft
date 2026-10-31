<!-- SPDX-License-Identifier: GPL-3.0-only
Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root. -->
In current benchmarks (ASM/Benchmarks), it uses the approach that compile the ASM into a regular LPL program, then prove properties of that program. 

Create another set of benchmarks that use the exactly same cases as in ASM/Benchmarks, but conduct proofs without the need to firstly compile the whole ASM into a regular LPL program, but only use unfold_at: the proof tactic is that firstly unfold the current continuation into a regular-program form (perhaps that still contain continuation in it), then dissolve this form using the rules in LPL for regular programs, then continue unfold_at the rest continuation in each branch... Continue this process until proof closes or a cyclic proof structure is formed. 

Test this benchmark until everything works. 

If having any questions, stop and interact with the user. 
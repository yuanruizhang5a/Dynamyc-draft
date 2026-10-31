<!-- SPDX-License-Identifier: GPL-3.0-only
Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root. -->
Build an abstract state machine layer in LPL (`Rocq-copy/LPL/ASM`).

Current requirements are specified by [revise-2.md](revise-2.md), superseding
this file's original compiler-based design.

- A finite machine declares control states, transitions and an initial state.
- Each state description contains only a finite set of propositions.
- Transition instructions use existing LPL programs and may update variables.
- `unfold_at` opens one outgoing layer with caller-supplied continuations.
- Deductions use local unfolding, regular-program contract rules and checked
  continuation backlinks. Do not compile the entire graph to a regular program.
- Interpret all programs using existing LPL semantics, without another ASM
  execution relation.
- Build and prove the five local-unfolding benchmarks, with a 600-second
  maximum compilation time for each. See [README.md](README.md) for commands.
- Removed files must be moved to `~/Garbage`; if this session cannot do so,
  provide runnable commands in a `.txt` file as requested in `revise-2.md`.

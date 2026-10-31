(* SPDX-License-Identifier: GPL-3.0-only
   Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root. *)
(** Nondeterministic assignments and complementary conditional transitions. *)
From Stdlib Require Import List ZArith Lia.
From CyclistRocq.LPL.ASM Require Import Support.
Import ListNotations.
Inductive control := Choose | LeftEnd | RightEnd.
Definition control_eq_dec : forall s t : control, {s=t}+{s<>t}.
Proof. decide equality. Defined.
Definition describe q := StateDescription
  (match q with Choose => [] | LeftEnd => [Equal x zero] | RightEnd => [Equal x one] end).
Definition machine_with (conditional_edges : bool) : ASM.
Proof.
  refine (Machine control control_eq_dec [Choose;LeftEnd;RightEnd] _ _ describe
    (if conditional_edges then
       [conditional Choose LeftEnd iszero (Assign 0 zero);
        conditional Choose RightEnd (Neg iszero) (Assign 0 one)]
     else [unconditional Choose LeftEnd (vname 0) zero;
           unconditional Choose RightEnd (vname 0) one]) Choose).
  - intros []; cbn; auto.
  - repeat constructor; cbn; intuition discriminate.
Defined.

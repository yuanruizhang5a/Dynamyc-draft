(* SPDX-License-Identifier: GPL-3.0-only
   Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root. *)
(** A cyclic, guarded countdown: arbitrary finite input, exit, and safety. *)
From Stdlib Require Import List ZArith Lia.
From CyclistRocq.LPL.ASM Require Import Support.
Import ListNotations.
Inductive control := Loop | Halt.
Definition control_eq_dec : forall s t : control, {s=t}+{s<>t}.
Proof. decide equality. Defined.
Definition positive := Pred 2 [zero;x].
Definition describe q := StateDescription
  (match q with Loop => [nonnegative] | Halt => [iszero] end).
Definition machine : ASM.
Proof.
  refine (Machine control control_eq_dec [Loop;Halt] _ _ describe
    [conditional Loop Loop positive (Assign 0 (dec x));
     guarded Loop Halt iszero] Loop).
  - intros []; cbn; auto.
  - repeat constructor; cbn; intuition discriminate.
Defined.

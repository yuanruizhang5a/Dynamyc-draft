(* SPDX-License-Identifier: GPL-3.0-only
   Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root. *)
(** A closed two-state cycle: no terminal states, finite prefixes execute. *)
From Stdlib Require Import List ZArith Lia.
From CyclistRocq.LPL.ASM Require Import Support.
Import ListNotations.
Inductive control := Tick | Tock.
Definition control_eq_dec : forall s t : control, {s=t}+{s<>t}.
Proof. decide equality. Defined.
Definition describe q := StateDescription
  [Equal x (match q with Tick => zero | Tock => one end)].
Definition machine : ASM.
Proof.
  refine (Machine control control_eq_dec [Tick;Tock] _ _ describe
    [unconditional Tick Tock (vname 0) one;
     unconditional Tock Tick (vname 0) zero] Tick).
  - intros []; cbn; auto.
  - repeat constructor; cbn; intuition discriminate.
Defined.

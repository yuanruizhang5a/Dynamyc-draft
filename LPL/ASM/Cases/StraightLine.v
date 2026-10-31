(* SPDX-License-Identifier: GPL-3.0-only
   Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root. *)
(** Two assignments with state propositions, including equality assertions. *)
From Stdlib Require Import List ZArith Lia.
From CyclistRocq.LPL.ASM Require Import Support.
Import ListNotations.
Inductive control := Start | Middle | Done.
Definition control_eq_dec : forall s t : control, {s=t}+{s<>t}.
Proof. decide equality. Defined.
Definition describe q := match q with
  | Start => StateDescription [iszero; Equal x zero]
  | Middle => StateDescription [nonnegative; Equal x one]
  | Done => StateDescription [Equal x (inc one)] end.
Definition machine : ASM.
Proof.
  refine (Machine control control_eq_dec [Start;Middle;Done] _ _ describe
    [unconditional Start Middle (vname 0) one;
     unconditional Middle Done (vname 0) (inc x)] Start).
  - intros []; cbn; auto.
  - repeat constructor; cbn; intuition discriminate.
Defined.

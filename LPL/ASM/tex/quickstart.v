(* SPDX-License-Identifier: GPL-3.0-only
   Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root. *)
(** Executable version of the example in usage.tex. *)
From Stdlib Require Import List.
From CyclistRocq.LPL.ASM Require Import Support.
Import ListNotations.

Inductive control := Begin | Finish.
Definition control_eq_dec : forall q r : control, {q = r} + {q <> r}.
Proof. decide equality. Defined.

Definition describe q := StateDescription
  (match q with
   | Begin => []
   | Finish => [Equal x one]
   end).

Definition tiny : ASM.
Proof.
  refine (Machine control control_eq_dec [Begin;Finish]
    _ _ describe
    [unconditional Begin Finish (vname 0) one] Begin).
  - intros []; cbn; auto.
  - repeat constructor; cbn; intuition discriminate.
Defined.

Example tiny_checked : asm_wfb tiny = true.
Proof. vm_compute; reflexivity. Qed.

Example tiny_layer_checked :
  program_wfb (unfold_at tiny (observe tiny) Begin) = true.
Proof. apply unfold_at_wf; [exact tiny_checked|intro q; now apply observe_wf]. Qed.

Example tiny_layer_shape : unfold_at tiny (observe tiny) Begin =
  Seq (Test Truth) (Seq (Assign 0 one) (Test (Conj (Equal x one) Truth))).
Proof. reflexivity. Qed.

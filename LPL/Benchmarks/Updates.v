(* SPDX-License-Identifier: GPL-3.0-only
   Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root. *)
(** * Update evaluation and retained intermediate states

    Updates describe individual states and evaluate inside out. These small
    computations show dependent assignments and preservation of other
    variables; explicit label components then retain the intermediate states.
    The final atomic leaf proof is valid in every label environment. *)
From Stdlib Require Import List ZArith.
From CyclistRocq.LPL.Benchmarks Require Import Support.
Import ListNotations Generation Cert.
Definition w := constant_world 0.
Definition first_update := AssignUpdate 0 (inc x) u0.
Definition second_update := AssignUpdate 0 (inc x) first_update.
Definition dependent_update := AssignUpdate 1 (plus x one) first_update.
Example identity_assignment : eval_state M w (AssignUpdate 0 x u0) 0 tt = 0%Z.
Proof. reflexivity. Qed.
Example assignment_changes_value : eval_state M w first_update 0 tt = 1%Z.
Proof. reflexivity. Qed.
Example reads_previous_update : eval_state M w second_update 0 tt = 2%Z.
Proof. reflexivity. Qed.
Example dependent_assignments : eval_state M w dependent_update 1 tt = 2%Z.
Proof. reflexivity. Qed.
Example other_variable_unchanged : eval_state M w dependent_update 0 tt = 1%Z.
Proof. reflexivity. Qed.
Example every_intermediate_state_retained :
  map (fun s : state M => s 0 tt) (eval_label M w (Join (Join l0 (StateLabel first_update)) (StateLabel
    second_update))) = [0%Z;1%Z;2%Z].
Proof. reflexivity. Qed.
(** Unlike the computations at [w], this goal makes no assumption on its
    base state: the last update overwrites [x] with one. [close_atoms] requires
    the shallow proof explicitly before the one-node certificate is built. *)
Definition grounded := Jdg [] [assertion (StateLabel (AssignUpdate 0 one (AssignUpdate 0 zero u0))) (Equal x
  one)].
Definition grounded_ax : Cyclic.axiom_instance.
Proof.
  refine (close_atoms grounded eq_refl eq_refl _); intros world Hleft.
  exists (assertion (StateLabel (AssignUpdate 0 one (AssignUpdate 0 zero u0))) (Equal x one));
    split; [now left|]; split; [discriminate|reflexivity].
Defined.
Theorem dependent_update_terminal_valid : Cyclic.Valid grounded.
Proof. exact (raw_check_sound (axiom_graph grounded_ax) empty_trace_witness (axiom_graph_raw_check
  grounded_ax)). Qed.
Example nonvacuity : exists world, admissible M grounded world.
Proof. apply root_nonvacuous; reflexivity. Qed.

Print Assumptions dependent_update_terminal_valid.

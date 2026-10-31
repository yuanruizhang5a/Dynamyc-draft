(* SPDX-License-Identifier: GPL-3.0-only
   Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root. *)
(** * Snapshot updates, explicit rewrites, and a generated conversion proof *)
From Stdlib Require Import List Bool ZArith String.
From CyclistRocq.LPL.Benchmarks Require Import Support.
Import ListNotations Generation Cert.
Open Scope string_scope.
Definition input := write M (constant_state 1) 1 (zvalue 2).
Definition swap := Parallel [(vname 0,y);(vname 1,x)].
Definition sequential := Then (Put 0 y) (Put 1 x).
Example parallel_swap : apply_update M swap input 0 tt = 2%Z /\ apply_update M swap input 1 tt = 1%Z.
Proof. split; reflexivity. Qed.
Example sequential_reads_changed_state : apply_update M sequential input 0 tt = 2%Z /\ apply_update M
  sequential input 1 tt = 2%Z.
Proof. split; reflexivity. Qed.
Example last_duplicate_wins : apply_update M (Parallel [(vname 0,zero);(vname 0,one)]) input 0 tt = 1%Z.
Proof. reflexivity. Qed.
Example empty_parallel : apply_update M (Parallel []) input = input.
Proof. reflexivity. Qed.
Example other_variable_preserved : apply_update M swap input 2 tt = input 2 tt.
Proof. reflexivity. Qed.
Example nested_updates : apply_update M (Then swap (Put 0 (inc x))) input 0 tt = 3%Z.
Proof. reflexivity. Qed.
Definition root := Jdg [] [traced (Join Empty (StateLabel (Apply Skip u0))) (Box (Test Truth) Truth) 0].
Definition rewrite_rule := requested root (RewriteUpdate OnRight 0 [true] 0 UpdateSkip) ltac:(vm_compute;
  reflexivity).
Definition after_rewrite := premise_at rewrite_rule 0.
Definition test_rule := requested after_rewrite (Local OnRight 0 "B.Test.R") ltac:(vm_compute; reflexivity).
Definition ax := generated_axiom (premise_at test_rule 0) ltac:(vm_compute; reflexivity).
Definition build := Cyclic.run_script root [Cyclic.ApplyRule 0 rewrite_rule;Cyclic.ApplyRule 1
  test_rule;Cyclic.CloseWith 2 ax].
Example accepted : Cyclic.raw_check build.(Cyclic.built_graph) empty_trace_witness = true.
Proof. vm_compute; reflexivity. Qed.
Theorem explicit_update_rewrite_valid : Cyclic.Valid root.
Proof. exact (raw_check_sound _ _ accepted). Qed.
Example retained_tag :
  match rewrite_rule.(Cyclic.rule_premises) with [p] => p.(Cyclic.premise_edge).(Cyclic.edge_valid) | _ =>
    [] end = [(0,0)].
Proof. vm_compute; reflexivity. Qed.
Example no_artificial_progress :
  match rewrite_rule.(Cyclic.rule_premises) with [p] => p.(Cyclic.premise_edge).(Cyclic.edge_progress) | _
    => [(0,0)] end = [].
Proof. vm_compute; reflexivity. Qed.
Example bad_path_rejected : someb (generate_requested root (RewriteUpdate OnRight 0 [false] 0 UpdateSkip)) =
  false.
Proof. vm_compute; reflexivity. Qed.
Example bad_law_rejected : someb (generate_requested root (RewriteUpdate OnRight 0 [true] 0 UpdateSequence))
  = false.
Proof. vm_compute; reflexivity. Qed.
Example bad_position_rejected : someb (generate_requested root (RewriteUpdate OnRight 1 [] 0 UpdateSkip)) =
  false.
Proof. vm_compute; reflexivity. Qed.
Example sequence_expansion : rewrite_state 0 UpdateSequence (Apply sequential u0) = Some (Apply (Put 1 x)
  (Apply (Put 0 y) u0)).
Proof. reflexivity. Qed.
Example inner_depth : rewrite_state 1 UpdateSkip (Apply swap (Apply Skip u0)) = Some (Apply swap u0).
Proof. reflexivity. Qed.
Example singleton_parallel : rewrite_state 0 UpdateParallelSingleton (Apply (Parallel [(vname 0,one)]) u0) =
  Some (AssignUpdate 0 one u0).
Proof. reflexivity. Qed.
Example empty_parallel_expansion : rewrite_state 0 UpdateParallelEmpty (Apply (Parallel []) u0) = Some u0.
Proof. reflexivity. Qed.
Example nonvacuity : exists w, admissible M root w.
Proof. apply root_nonvacuous; reflexivity. Qed.
Print Assumptions explicit_update_rewrite_valid.
Print Assumptions rewrite_update_right.

Definition left_goal := Jdg [assertion (StateLabel (Apply (Parallel []) u0)) Truth] [assertion l0 Truth].
Example left_update_request : someb (generate_requested left_goal (RewriteUpdate OnLeft 0 [] 0
  UpdateParallelEmpty)) = true.
Proof. vm_compute; reflexivity. Qed.
Example bad_depth_rejected : someb (generate_requested root (RewriteUpdate OnRight 0 [true] 1 UpdateSkip)) =
  false.
Proof. vm_compute; reflexivity. Qed.
Definition sequence_goal := Jdg [] [assertion (StateLabel (Apply sequential u0)) Truth].
Example sequence_request : someb (generate_requested sequence_goal (RewriteUpdate OnRight 0 [] 0
  UpdateSequence)) = true.
Proof. vm_compute; reflexivity. Qed.
Definition singleton_goal := Jdg [] [assertion (StateLabel (Apply (Parallel [(vname 0,one)]) u0)) Truth].
Example singleton_request : someb (generate_requested singleton_goal (RewriteUpdate OnRight 0 [] 0
  UpdateParallelSingleton)) = true.
Proof. vm_compute; reflexivity. Qed.

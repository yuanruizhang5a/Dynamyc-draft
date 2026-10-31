(* SPDX-License-Identifier: GPL-3.0-only
   Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root. *)
From Stdlib Require Import List ZArith Lia.
From CyclistRocq.LPL.ASM.Benchmarks Require Import Support.
From CyclistRocq.LPL.ASM.Cases Require Import Validation Cycle.
Import ListNotations.
Module Case := CyclistRocq.LPL.ASM.Cases.Validation.
Module StoppedSpec <: Engine.SPEC.
  Definition machine := import_machine (Case.stopped).
  Definition ends := terminal_states machine.
  Definition invariant (_ : state M) := True.
  Lemma checked_machine : asm_wfb machine = true. Proof. vm_compute; reflexivity. Qed.
  Lemma instructions_safe e : In e (transitions machine) -> safe invariant (instruction e).
  Proof. cbn; tauto. Qed.
End StoppedSpec.
Module P := Engine.ForSpec StoppedSpec.
Definition graph := P.Graph.built_graph (P.build 100 P.Contract tt).
Example checked : P.Graph.raw_check graph (P.witness graph) = true. Proof. check_graph. Qed.
Example exact_terminal_stutter s : program_holds M (P.approx 0 tt) [s;s].
Proof. change (program_holds M (Test Truth) [s;s]); exists s; split; [reflexivity|exact I]. Qed.
Example no_singleton s : ~ program_holds M (P.approx 0 tt) [s].
Proof. change (~ program_holds M (Test Truth) [s]); intros [t [H _]]; discriminate. Qed.
Example wrong_arity_rejected : asm_wfb (import_machine Case.invalid_term) = false. Proof. check_graph. Qed.
Example impure_description_rejected : asm_wfb (import_machine Case.impure_description) = false. Proof. check_graph. Qed.
Example cross_sort_proposition_rejected : Case.TypedModel.A.asm_wfb
  (Case.TypedModel.machine false false) = false. Proof. check_graph. Qed.
Example cross_sort_assignment_rejected : Case.TypedModel.A.asm_wfb
  (Case.TypedModel.machine true true) = false. Proof. check_graph. Qed.
Example correct_sort_accepted : Case.TypedModel.A.asm_wfb
  (Case.TypedModel.machine true false) = true. Proof. check_graph. Qed.
Example many_sorted_local_unfold_checked : Case.TypedModel.A.Syn.program_wfb
  (Case.TypedModel.A.unfold_at (Case.TypedModel.machine true false)
    (fun _ => Case.TypedModel.A.Syn.Test Case.TypedModel.A.Syn.Truth) tt) = true.
Proof. check_graph. Qed.
Example exhausted_builder_is_rejected :
  let g := P.Graph.built_graph (P.build 0 P.Contract tt) in
  P.Graph.raw_check g (P.witness g) = false.
Proof. check_graph. Qed.

(** A syntactically valid pair of backlinks with NO unfolding/progress is
    rejected. Matching judgments alone do not justify cyclic reasoning. *)
Definition stalled_root := (P.Contract,P.Call tt).
Definition stalled : P.Graph.graph :=
  {| P.Graph.graph_root := stalled_root;
     P.Graph.graph_nodes :=
       [{| P.Graph.node_judgment := stalled_root;
           P.Graph.node_payload := P.Graph.BacklinkNode (P.backlink_rule stalled_root) 1 |};
        {| P.Graph.node_judgment := stalled_root;
           P.Graph.node_payload := P.Graph.BacklinkNode (P.backlink_rule stalled_root) 0 |}] |}.
Example stalled_is_structurally_valid : P.Graph.structural_check stalled = true.
Proof. check_graph. Qed.
Example stalled_cycle_is_rejected : P.Graph.raw_check stalled (P.witness stalled) = false.
Proof. check_graph. Qed.

Module ContradictorySpec <: Engine.SPEC.
  Definition machine := import_machine (Case.contradictory).
  Definition ends := terminal_states machine.
  Definition invariant (_ : state M) := True.
  Lemma checked_machine : asm_wfb machine = true. Proof. vm_compute; reflexivity. Qed.
  Lemma instructions_safe e : In e (transitions machine) -> safe invariant (instruction e).
  Proof. cbn; tauto. Qed.
End ContradictorySpec.
Module C := Engine.ForSpec ContradictorySpec.
Definition cg := C.Graph.built_graph (C.build 100 C.Contract tt).
Example contradictory_checked : C.Graph.raw_check cg (C.witness cg) = true. Proof. check_graph. Qed.
Theorem contradictory_state_cannot_execute depth s tail :
  ~ program_holds M (C.approx depth tt) (s::tail).
Proof.
  intro H; pose proof (C.accepted_post cg tt eq_refl contradictory_checked depth s tail H I) as Hp.
  change (exists q, In q [tt] /\ observed ContradictorySpec.machine q (last (s::tail) default_state)) in Hp.
  destruct Hp as [q [[<-|[]] Hp]]; destruct Hp as [Hfalse _]; exact (Hfalse I).
Qed.
Module DisconnectedSpec <: Engine.SPEC.
  Definition machine := import_machine (Case.disconnected).
  Definition ends := [true].
  Definition invariant (_ : state M) := True.
  Lemma checked_machine : asm_wfb machine = true. Proof. vm_compute; reflexivity. Qed.
  Lemma instructions_safe e : In e (transitions machine) -> safe invariant (instruction e).
  Proof. cbn; tauto. Qed.
End DisconnectedSpec.
Module D := Engine.ForSpec DisconnectedSpec.
Definition dg := D.Graph.built_graph (D.build 100 D.Contract false).
Example disconnected_checked : D.Graph.raw_check dg (D.witness dg) = true. Proof. check_graph. Qed.
Theorem absent_edges_do_not_become_skip depth tr : ~ program_holds M (D.approx depth false) tr.
Proof.
  destruct depth.
  - change (~ program_holds M (Test Falsity) tr); intros [s [Heq Hfalse]]; apply Hfalse; exact I.
  - change (~ program_holds M (Seq (Test Truth) (Test Falsity)) tr).
    intros [a [b [Ha [[s [Heq Hfalse]] Ho]]]]; apply Hfalse; exact I.
Qed.
Print Assumptions contradictory_state_cannot_execute.

Goal True.
  let nodes := eval vm_compute in (List.length (P.Graph.graph_nodes graph)) in
  let links := eval vm_compute in (P.backlink_count graph) in
  idtac "GRAPH Stopped" nodes links; exact I.
Qed.
Goal True.
  let nodes := eval vm_compute in (List.length (C.Graph.graph_nodes cg)) in
  let links := eval vm_compute in (C.backlink_count cg) in
  idtac "GRAPH Contradictory" nodes links; exact I.
Qed.
Goal True.
  let nodes := eval vm_compute in (List.length (D.Graph.graph_nodes dg)) in
  let links := eval vm_compute in (D.backlink_count dg) in
  idtac "GRAPH Disconnected" nodes links; exact I.
Qed.
